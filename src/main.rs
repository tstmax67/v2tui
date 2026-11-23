#![allow(deprecated)]

use std::{
    collections::{HashMap, VecDeque},
    fs,
    io::{self, Read, Write},
    net::{TcpStream, ToSocketAddrs},
    os::unix::{fs::OpenOptionsExt, process::CommandExt},
    path::{Path, PathBuf},
    process::{Child, Command, Stdio},
    sync::{
        atomic::{AtomicBool, Ordering},
        mpsc::{self, Receiver, Sender},
        Arc, Mutex,
    },
    thread,
    time::{Duration, Instant, SystemTime, UNIX_EPOCH},
};

use base64::{engine::general_purpose, Engine as _};
use chrono::{Local, TimeZone};
use percent_encoding::percent_decode_str;
use ratatui::{
    crossterm::{
        cursor::{Hide, Show},
        event::{self, Event as CEvent, KeyCode, KeyEvent, KeyEventKind, KeyModifiers},
        execute,
        terminal::{disable_raw_mode, enable_raw_mode, EnterAlternateScreen, LeaveAlternateScreen},
    },
    layout::{Alignment, Constraint, Layout, Rect},
    style::{Color, Modifier, Style},
    text::{Line, Span, Text},
    widgets::{Block, BorderType, Cell, Clear, Padding, Paragraph, Row, Table, TableState, Wrap},
    DefaultTerminal, Frame,
};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};

const SOCKS_PORT: u16 = 10808;
const HTTP_PORT: u16 = 10809;
const PING_WORKERS: usize = 32;
/// Exit-IP checks start one xray process each, so far fewer run at once than TCP pings.
const EXIT_WORKERS: usize = 16;
/// One exit-IP lookup (connect + SOCKS5 handshake + reply) must finish within this time.
const EXIT_HTTP_TIMEOUT_MS: u64 = 10000;
/// Per-subscription results (pings, exit IPs, selection) for every file ever opened.
const CACHE_FILE: &str = "cache.json";
/// Keep at most this many subscription files in the cache (the most recently used ones) ...
const CACHE_MAX_FILES: usize = 10;
/// ... and forget files that were not opened for this long.
const CACHE_MAX_AGE_SECS: u64 = 90 * 24 * 3600;
const PING_TIMEOUT_MS: u64 = 2500;
/// The layout is designed for at least this many columns and rows.
const MIN_W: u16 = 130;
const MIN_H: u16 = 32;
/// Ping results are called stale once the last "ping all" is older than this. With live
/// pinging switched on (l), "ping all" is repeated automatically at this interval.
const PING_STALE_SECS: u64 = 5 * 60;
/// Name of the TUN interface created in VPN mode.
const TUN_NAME: &str = "v2tui0";
/// How the two connection modes are described in the Connection box.
const MODE_PROXY_URL: &str = "Proxy URL (SOCKS5 / HTTP URL for your apps)";
const MODE_VPN: &str = "System VPN (all traffic, no proxy URL)";

// ───────────────────────────── data model ─────────────────────────────

#[derive(Clone, Copy, PartialEq)]
enum Ping {
    Unknown,
    Testing,
    Ms(u128),
    Fail,
}

impl Ping {
    fn sort_key(self) -> u128 {
        match self {
            Ping::Ms(m) => m,
            Ping::Unknown | Ping::Testing => u128::MAX - 1,
            Ping::Fail => u128::MAX,
        }
    }
}

/// Where a node's traffic really comes out, found by sending a request through it.
#[derive(Clone, PartialEq)]
enum ExitState {
    Unknown,
    Testing,
    Ok { ip: String, code: String, name: String },
    Fail,
}

/// (exit IP, country code, country name) as found through a node.
type ExitRes = Option<(String, String, String)>;

#[derive(Clone)]
struct Node {
    /// Stable identity used by the cache (no credentials in it).
    key: String,
    proto: String,
    name: String,
    code: String,
    country: String,
    host: String,
    port: u16,
    net: String,
    sec: String,
    sni: String,
    outbound: Value,
    ping: Ping,
    exit: ExitState,
    /// A node that is not in the opened file: the still-running connection of an earlier
    /// file, restored from state.json. It is dropped from the list once disconnected.
    external: bool,
}

/// "UK" is how some subscriptions write "GB".
fn same_country(a: &str, b: &str) -> bool {
    let norm = |c: &str| if c == "UK" { "GB".to_string() } else { c.to_string() };
    norm(a) == norm(b)
}

impl Node {
    /// What the `/` filter searches: the Country, Exit, Type, Address, Port, Net and Name
    /// columns, as they appear in the table.
    fn haystack(&self) -> String {
        format!(
            "{} {} {} {} {} {} {}",
            self.country,
            self.exit_country(),
            self.proto,
            self.host,
            self.port,
            self.net,
            self.name
        )
        .to_lowercase()
    }

    /// What the Exit column shows: the country of the real exit IP, "unavailable" when the
    /// exit check failed, and blank until the node has been checked.
    fn exit_country(&self) -> String {
        match &self.exit {
            ExitState::Ok { code, name, .. } if code != "??" => name.clone(),
            ExitState::Fail => "unavailable".to_string(),
            _ => String::new(),
        }
    }

    /// True when the exit IP is in a different country than the node's name claims.
    fn exit_differs(&self) -> bool {
        match &self.exit {
            ExitState::Ok { code, .. } => {
                self.code != "??" && code != "??" && !same_country(&self.code, code)
            }
            _ => false,
        }
    }
}

#[derive(Clone, Copy, PartialEq)]
enum Sort {
    File,
    Ping,
    Country,
    Proto,
}

impl Sort {
    fn next(self) -> Self {
        match self {
            Sort::File => Sort::Ping,
            Sort::Ping => Sort::Country,
            Sort::Country => Sort::Proto,
            Sort::Proto => Sort::File,
        }
    }
    fn id(self) -> &'static str {
        match self {
            Sort::File => "file",
            Sort::Ping => "ping",
            Sort::Country => "country",
            Sort::Proto => "proto",
        }
    }
    fn from_id(s: &str) -> Self {
        match s {
            "ping" => Sort::Ping,
            "country" => Sort::Country,
            "proto" => Sort::Proto,
            _ => Sort::File,
        }
    }
    fn label(self) -> &'static str {
        match self {
            Sort::File => "file order",
            Sort::Ping => "ping",
            Sort::Country => "country",
            Sort::Proto => "type",
        }
    }
}

enum Msg {
    Ping(usize, Ping),
    /// Exit IP check through the running connection (node index, result).
    Exit(usize, ExitRes),
    /// Exit IP check through a temporary xray started just for that node.
    Probe(usize, ExitRes),
}

/// Temporary xray processes started for exit-IP checks, so they can be stopped on quit.
#[derive(Clone, Default)]
struct Probes {
    live: Arc<Mutex<Vec<(u32, PathBuf)>>>,
    stop: Arc<AtomicBool>,
}

impl Probes {
    fn stopped(&self) -> bool {
        self.stop.load(Ordering::Relaxed)
    }
    fn add(&self, pid: u32, cfg: PathBuf) {
        self.live.lock().unwrap().push((pid, cfg));
    }
    fn remove(&self, pid: u32) {
        self.live.lock().unwrap().retain(|(p, _)| *p != pid);
    }
    /// Stop handing out work and kill every probe still running (and delete its config).
    fn kill_all(&self) {
        self.stop.store(true, Ordering::Relaxed);
        let live: Vec<(u32, PathBuf)> = self.live.lock().unwrap().clone();
        for (pid, cfg) in live {
            let _ = Command::new("kill")
                .args(["-KILL", &pid.to_string()])
                .stdout(Stdio::null())
                .stderr(Stdio::null())
                .status();
            let _ = fs::remove_file(cfg);
        }
    }
}

struct Active {
    node: usize,
    /// Pid of the core (in VPN mode: of the `sudo` wrapper, or of the core if sudo exec'd it).
    pid: u32,
    /// Some when this session started the core, None when we re-attached to one
    /// that an earlier v2tui session left running.
    child: Option<Child>,
    /// True for VPN (TUN) mode, where the core runs as root.
    vpn: bool,
    /// Content hash of the subscription file the node comes from. Differs from the opened
    /// file's hash for an `external` node; empty when unknown (older state.json).
    origin: String,
}

// ───────────────────────────── link parsing ─────────────────────────────

fn b64(s: &str) -> Option<Vec<u8>> {
    let t = s.trim().trim_end_matches('=');
    general_purpose::STANDARD_NO_PAD
        .decode(t)
        .ok()
        .or_else(|| general_purpose::URL_SAFE_NO_PAD.decode(t).ok())
}

fn dec(s: &str) -> String {
    percent_decode_str(s).decode_utf8_lossy().into_owned()
}

fn jstr(v: &Value, k: &str) -> String {
    match v.get(k) {
        Some(Value::String(s)) => s.clone(),
        Some(Value::Number(n)) => n.to_string(),
        _ => String::new(),
    }
}

fn country_name(code: &str) -> &'static str {
    match code {
        "US" => "United States",
        "GB" | "UK" => "United Kingdom",
        "DE" => "Germany",
        "FR" => "France",
        "NL" => "Netherlands",
        "CA" => "Canada",
        "JP" => "Japan",
        "SG" => "Singapore",
        "HK" => "Hong Kong",
        "TW" => "Taiwan",
        "KR" => "South Korea",
        "IN" => "India",
        "BD" => "Bangladesh",
        "RU" => "Russia",
        "TR" => "Turkey",
        "IR" => "Iran",
        "AE" => "UAE",
        "SA" => "Saudi Arabia",
        "IL" => "Israel",
        "AU" => "Australia",
        "BR" => "Brazil",
        "AR" => "Argentina",
        "MX" => "Mexico",
        "ZA" => "South Africa",
        "SE" => "Sweden",
        "FI" => "Finland",
        "NO" => "Norway",
        "DK" => "Denmark",
        "PL" => "Poland",
        "IT" => "Italy",
        "ES" => "Spain",
        "PT" => "Portugal",
        "CH" => "Switzerland",
        "AT" => "Austria",
        "BE" => "Belgium",
        "IE" => "Ireland",
        "CZ" => "Czechia",
        "HU" => "Hungary",
        "RO" => "Romania",
        "BG" => "Bulgaria",
        "UA" => "Ukraine",
        "LT" => "Lithuania",
        "LV" => "Latvia",
        "EE" => "Estonia",
        "KZ" => "Kazakhstan",
        "AM" => "Armenia",
        "GE" => "Georgia",
        "CY" => "Cyprus",
        "CN" => "China",
        "ID" => "Indonesia",
        "MY" => "Malaysia",
        "TH" => "Thailand",
        "VN" => "Vietnam",
        "PH" => "Philippines",
        "??" => "Unknown",
        _ => "Other",
    }
}

/// Country code from a flag emoji (regional indicators) or a leading "US"-style token.
fn detect_country(name: &str) -> (String, String) {
    let mut ri: Vec<char> = Vec::new();
    for c in name.chars() {
        if ('\u{1F1E6}'..='\u{1F1FF}').contains(&c) {
            ri.push(c);
            if ri.len() == 2 {
                break;
            }
        } else if !ri.is_empty() {
            ri.clear();
        }
    }
    let code = if ri.len() == 2 {
        ri.iter()
            .map(|c| (b'A' + (*c as u32 - 0x1F1E6) as u8) as char)
            .collect::<String>()
    } else {
        let first: String = name
            .trim()
            .chars()
            .take_while(|c| c.is_ascii_alphabetic())
            .collect();
        if first.len() == 2 && first.chars().all(|c| c.is_ascii_uppercase()) {
            first
        } else {
            "??".to_string()
        }
    };
    let cname = country_name(&code).to_string();
    (code, cname)
}

/// Remove flag emoji (they break column alignment) and collapse whitespace.
fn clean_name(name: &str) -> String {
    name.chars()
        .filter(|c| !('\u{1F1E6}'..='\u{1F1FF}').contains(c))
        .collect::<String>()
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
}

fn stream_settings(p: &HashMap<String, String>, addr: &str) -> Value {
    let get = |k: &str| p.get(k).cloned().unwrap_or_default();
    let net = if get("type").is_empty() { "tcp".to_string() } else { get("type") };
    let sec = if get("security").is_empty() { "none".to_string() } else { get("security") };
    let sni = [get("sni"), get("host"), addr.to_string()]
        .into_iter()
        .find(|s| !s.is_empty())
        .unwrap_or_default();
    let fp = get("fp");
    let path = if get("path").is_empty() { "/".to_string() } else { get("path") };
    let host = get("host");
    let mut s = json!({ "network": net, "security": sec });

    if sec == "tls" {
        let mut t = json!({ "serverName": sni });
        if !fp.is_empty() {
            t["fingerprint"] = json!(fp);
        }
        let alpn = get("alpn");
        if !alpn.is_empty() {
            t["alpn"] = json!(alpn.split(',').collect::<Vec<_>>());
        }
        s["tlsSettings"] = t;
    } else if sec == "reality" {
        let fp = if fp.is_empty() { "chrome".to_string() } else { fp };
        s["realitySettings"] = json!({
            "serverName": sni,
            "fingerprint": fp,
            "publicKey": get("pbk"),
            "shortId": get("sid"),
            "spiderX": get("spx"),
        });
    }
    match net.as_str() {
        "ws" => {
            s["wsSettings"] = json!({ "path": path, "headers": { "Host": host } });
        }
        "grpc" => {
            s["grpcSettings"] = json!({ "serviceName": get("serviceName") });
        }
        _ => {}
    }
    s
}

fn finish(
    proto: &str,
    name: String,
    host: String,
    port: u16,
    p: &HashMap<String, String>,
    outbound: Value,
) -> Node {
    let get = |k: &str| p.get(k).cloned().unwrap_or_default();
    let net = if get("type").is_empty() { "tcp".to_string() } else { get("type") };
    let sec = if get("security").is_empty() { "none".to_string() } else { get("security") };
    let (code, country) = detect_country(&name);
    Node {
        key: format!("{}|{}|{}|{}", proto, host, port, clean_name(&name)),
        proto: proto.to_string(),
        name: clean_name(&name),
        code,
        country,
        host,
        port,
        net,
        sec,
        sni: get("sni"),
        outbound,
        ping: Ping::Unknown,
        exit: ExitState::Unknown,
        external: false,
    }
}

fn parse_vmess(rest: &str) -> Option<Node> {
    let v: Value = serde_json::from_slice(&b64(rest)?).ok()?;
    let host = jstr(&v, "add");
    let port: u16 = jstr(&v, "port").parse().ok()?;
    let id = jstr(&v, "id");
    let mut name = jstr(&v, "ps");
    if name.is_empty() {
        name = jstr(&v, "name");
    }
    let aid: u32 = jstr(&v, "aid").parse().unwrap_or(0);
    let scy = {
        let s = jstr(&v, "scy");
        if s.is_empty() { "auto".to_string() } else { s }
    };

    let mut p: HashMap<String, String> = HashMap::new();
    p.insert("type".into(), jstr(&v, "net"));
    p.insert(
        "security".into(),
        if jstr(&v, "tls") == "tls" { "tls".into() } else { "none".into() },
    );
    for (dst, src) in [("sni", "sni"), ("host", "host"), ("path", "path"), ("alpn", "alpn"), ("fp", "fp")] {
        p.insert(dst.into(), jstr(&v, src));
    }

    let outbound = json!({
        "protocol": "vmess",
        "settings": { "vnext": [{
            "address": host, "port": port,
            "users": [{ "id": id, "alterId": aid, "security": scy }]
        }]},
        "streamSettings": stream_settings(&p, &host),
    });
    Some(finish("vmess", name, host, port, &p, outbound))
}

struct Parsed {
    user: String,
    host: String,
    port: u16,
    q: HashMap<String, String>,
    frag: String,
}

fn parse_urlish(rest: &str) -> Option<Parsed> {
    let (rest, frag) = match rest.split_once('#') {
        Some((a, b)) => (a, dec(b)),
        None => (rest, String::new()),
    };
    let (rest, query) = rest.split_once('?').unwrap_or((rest, ""));
    let rest = rest.trim_end_matches('/');
    let (user, hostport) = rest.rsplit_once('@')?;
    let (host, port) = hostport.rsplit_once(':')?;
    let q = query
        .split('&')
        .filter_map(|kv| kv.split_once('='))
        .map(|(k, v)| (k.to_string(), dec(v)))
        .collect();
    Some(Parsed {
        user: dec(user),
        host: host.trim_matches(|c| c == '[' || c == ']').to_string(),
        port: port.parse().ok()?,
        q,
        frag,
    })
}

fn parse_vless(rest: &str) -> Option<Node> {
    let u = parse_urlish(rest)?;
    let mut p = u.q.clone();
    p.entry("security".into()).or_insert_with(|| "none".into());
    let flow = p.get("flow").cloned().unwrap_or_default();
    let enc = p.get("encryption").cloned().unwrap_or_else(|| "none".into());
    let outbound = json!({
        "protocol": "vless",
        "settings": { "vnext": [{
            "address": u.host, "port": u.port,
            "users": [{ "id": u.user, "encryption": enc, "flow": flow }]
        }]},
        "streamSettings": stream_settings(&p, &u.host),
    });
    Some(finish("vless", u.frag, u.host, u.port, &p, outbound))
}

fn parse_trojan(rest: &str) -> Option<Node> {
    let u = parse_urlish(rest)?;
    let mut p = u.q.clone();
    p.entry("security".into()).or_insert_with(|| "tls".into());
    let outbound = json!({
        "protocol": "trojan",
        "settings": { "servers": [{ "address": u.host, "port": u.port, "password": u.user }]},
        "streamSettings": stream_settings(&p, &u.host),
    });
    Some(finish("trojan", u.frag, u.host, u.port, &p, outbound))
}

fn parse_ss(rest: &str) -> Option<Node> {
    let (body, frag) = match rest.split_once('#') {
        Some((a, b)) => (a, dec(b)),
        None => (rest, String::new()),
    };
    let body = body.split('?').next()?.trim_end_matches('/');

    let (method, password, hostport) = if let Some((ui, hp)) = body.rsplit_once('@') {
        let ui = dec(ui);
        let creds = b64(&ui)
            .and_then(|b| String::from_utf8(b).ok())
            .filter(|s| s.contains(':'))
            .unwrap_or(ui);
        let (m, pw) = creds.split_once(':')?;
        (m.to_string(), pw.to_string(), hp.to_string())
    } else {
        let s = String::from_utf8(b64(body)?).ok()?;
        let (creds, hp) = s.rsplit_once('@')?;
        let (m, pw) = creds.split_once(':')?;
        (m.to_string(), pw.to_string(), hp.to_string())
    };
    let (host, port) = hostport.rsplit_once(':')?;
    let port: u16 = port.parse().ok()?;
    let host = host.trim_matches(|c| c == '[' || c == ']').to_string();

    let mut p = HashMap::new();
    p.insert("type".to_string(), "tcp".to_string());
    p.insert("security".to_string(), "-".to_string());
    let outbound = json!({
        "protocol": "shadowsocks",
        "settings": { "servers": [{
            "address": host, "port": port, "method": method, "password": password
        }]},
    });
    Some(finish("ss", frag, host, port, &p, outbound))
}

fn parse_link(line: &str) -> Option<Node> {
    let line = line.trim();
    let (scheme, rest) = line.split_once("://")?;
    match scheme {
        "vmess" => parse_vmess(rest),
        "vless" => parse_vless(rest),
        "trojan" => parse_trojan(rest),
        "ss" => parse_ss(rest),
        _ => None,
    }
}

fn load_nodes(text: &str) -> Vec<Node> {
    let mut text = text.to_string();
    // Whole file may still be a base64 subscription blob.
    if !text.contains("://") {
        let squashed: String = text.split_whitespace().collect();
        if let Some(s) = b64(&squashed).and_then(|d| String::from_utf8(d).ok()) {
            text = s;
        }
    }
    text.lines()
        .filter(|l| !l.trim_start().starts_with('#'))
        .filter_map(parse_link)
        .collect()
}

// ───────────────────────────── pinging ─────────────────────────────

fn tcp_ping(host: &str, port: u16) -> Ping {
    let addrs = match (host, port).to_socket_addrs() {
        Ok(a) => a,
        Err(_) => return Ping::Fail,
    };
    for addr in addrs {
        let t = Instant::now();
        if TcpStream::connect_timeout(&addr, Duration::from_millis(PING_TIMEOUT_MS)).is_ok() {
            return Ping::Ms(t.elapsed().as_millis());
        }
    }
    Ping::Fail
}

fn spawn_pings(jobs: Vec<(usize, String, u16)>, tx: Sender<Msg>) {
    let queue = Arc::new(Mutex::new(jobs.into_iter().collect::<VecDeque<_>>()));
    for _ in 0..PING_WORKERS {
        let q = Arc::clone(&queue);
        let tx = tx.clone();
        thread::spawn(move || loop {
            let job = q.lock().unwrap().pop_front();
            let Some((i, host, port)) = job else { break };
            if tx.send(Msg::Ping(i, tcp_ping(&host, port))).is_err() {
                break;
            }
        });
    }
}

/// Give the next read only the time that is left of the overall deadline (None = none left).
fn arm_read(s: &TcpStream, deadline: Instant) -> Option<()> {
    let left = deadline.saturating_duration_since(Instant::now());
    if left.is_zero() {
        return None;
    }
    s.set_read_timeout(Some(left)).ok()
}

/// SOCKS5 handshake (no authentication) asking the proxy to connect to `host:port`.
/// The name is resolved by the proxy, so DNS lookups also go through the node.
/// The whole handshake must finish before `deadline`.
fn socks5_connect(s: &mut TcpStream, host: &str, port: u16, deadline: Instant) -> Option<()> {
    s.write_all(&[5, 1, 0]).ok()?; // version 5, one method: none
    let mut r = [0u8; 2];
    arm_read(s, deadline)?;
    s.read_exact(&mut r).ok()?;
    if r != [5, 0] {
        return None;
    }
    let h = host.as_bytes();
    if h.len() > 255 {
        return None;
    }
    let mut req = vec![5u8, 1, 0, 3, h.len() as u8];
    req.extend_from_slice(h);
    req.extend_from_slice(&port.to_be_bytes());
    s.write_all(&req).ok()?;
    let mut head = [0u8; 4];
    arm_read(s, deadline)?;
    s.read_exact(&mut head).ok()?;
    if head[0] != 5 || head[1] != 0 {
        return None;
    }
    // Skip the bound address in the reply.
    let addr_len = match head[3] {
        1 => 4,
        4 => 16,
        3 => {
            let mut l = [0u8; 1];
            arm_read(s, deadline)?;
            s.read_exact(&mut l).ok()?;
            l[0] as usize
        }
        _ => return None,
    };
    let mut rest = vec![0u8; addr_len + 2];
    arm_read(s, deadline)?;
    s.read_exact(&mut rest).ok()?;
    Some(())
}

/// Decode an HTTP "chunked" body.
fn dechunk(mut b: &[u8]) -> Option<Vec<u8>> {
    let mut out = Vec::new();
    loop {
        let eol = b.windows(2).position(|w| w == b"\r\n")?;
        let size_text = std::str::from_utf8(&b[..eol]).ok()?;
        let size = usize::from_str_radix(size_text.split(';').next()?.trim(), 16).ok()?;
        b = &b[eol + 2..];
        if size == 0 {
            return Some(out);
        }
        if b.len() < size + 2 {
            return None;
        }
        out.extend_from_slice(&b[..size]);
        b = &b[size + 2..];
    }
}

/// Minimal plain-HTTP GET using only the standard library: straight out, or through a SOCKS5
/// proxy (`host:port`). One deadline (EXIT_HTTP_TIMEOUT_MS) covers connecting, the SOCKS5
/// handshake and reading the reply. Returns the body of a 200 reply.
fn http_get(host: &str, path: &str, proxy: Option<&str>) -> Option<Vec<u8>> {
    let deadline = Instant::now() + Duration::from_millis(EXIT_HTTP_TIMEOUT_MS);
    let left = || deadline.saturating_duration_since(Instant::now());
    let mut stream = match proxy {
        Some(p) => {
            let addr = p.to_socket_addrs().ok()?.next()?;
            let mut s = TcpStream::connect_timeout(&addr, left()).ok()?;
            s.set_write_timeout(Some(left())).ok()?;
            socks5_connect(&mut s, host, 80, deadline)?;
            s
        }
        None => {
            let addr = (host, 80u16).to_socket_addrs().ok()?.next()?;
            TcpStream::connect_timeout(&addr, left()).ok()?
        }
    };
    stream.set_write_timeout(Some(left())).ok()?;
    let req = format!(
        "GET {path} HTTP/1.0\r\nHost: {host}\r\nUser-Agent: v2tui\r\nAccept: */*\r\nConnection: close\r\n\r\n"
    );
    stream.write_all(req.as_bytes()).ok()?;

    let mut buf: Vec<u8> = Vec::new();
    let mut chunk = [0u8; 4096];
    loop {
        let left = deadline.saturating_duration_since(Instant::now());
        if left.is_zero() {
            return None;
        }
        stream.set_read_timeout(Some(left)).ok()?;
        match stream.read(&mut chunk) {
            Ok(0) => break,
            Ok(n) => {
                buf.extend_from_slice(&chunk[..n]);
                if buf.len() > 64 * 1024 {
                    break;
                }
            }
            Err(_) => return None,
        }
    }

    let end = buf.windows(4).position(|w| w == b"\r\n\r\n")?;
    let head = String::from_utf8_lossy(&buf[..end]).to_lowercase();
    let ok = head
        .lines()
        .next()
        .map_or(false, |l| l.split_whitespace().nth(1) == Some("200"));
    if !ok {
        return None;
    }
    let body = &buf[end + 4..];
    if head.contains("transfer-encoding: chunked") {
        dechunk(body)
    } else {
        Some(body.to_vec())
    }
}

/// Ask a web service where traffic really comes out. With `proxy` (host:port) the request
/// goes through that SOCKS5 proxy, otherwise straight out (used in VPN mode).
fn probe_exit(proxy: Option<&str>) -> ExitRes {
    // Both services are asked at the same time and the first usable answer wins, so a slow
    // or blocked service no longer delays the other one.
    let (tx, rx) = mpsc::channel::<ExitRes>();
    let lookups: [fn(Option<&str>) -> ExitRes; 2] = [lookup_ip_api, lookup_ipinfo];
    for lookup in lookups {
        let tx = tx.clone();
        let proxy = proxy.map(String::from);
        thread::spawn(move || {
            let _ = tx.send(lookup(proxy.as_deref()));
        });
    }
    drop(tx);
    // Ends at the first Some, or when both lookups are done and failed.
    rx.iter().flatten().next()
}

/// Names we already know are used as-is, so both country columns spell them the same way.
fn exit_result(ip: String, code: String, api_name: String) -> ExitRes {
    let code = code.to_uppercase();
    if ip.is_empty() || code.len() != 2 {
        return None;
    }
    let known = country_name(&code);
    let name = if known != "Other" || api_name.is_empty() {
        known.to_string()
    } else {
        api_name
    };
    Some((ip, code, name))
}

fn fetch_json(host: &str, path: &str, proxy: Option<&str>) -> Option<Value> {
    serde_json::from_slice(&http_get(host, path, proxy)?).ok()
}

fn lookup_ip_api(proxy: Option<&str>) -> ExitRes {
    let v = fetch_json("ip-api.com", "/json/?fields=status,country,countryCode,query", proxy)?;
    if v.get("status").and_then(|x| x.as_str()) != Some("success") {
        return None;
    }
    exit_result(jstr(&v, "query"), jstr(&v, "countryCode"), jstr(&v, "country"))
}

fn lookup_ipinfo(proxy: Option<&str>) -> ExitRes {
    let v = fetch_json("ipinfo.io", "/json", proxy)?;
    exit_result(jstr(&v, "ip"), jstr(&v, "country"), String::new())
}

fn free_port() -> Option<u16> {
    let l = std::net::TcpListener::bind("127.0.0.1:0").ok()?;
    l.local_addr().ok().map(|a| a.port())
}

fn apply_insecure(outbound: &mut Value, insecure: bool) {
    if insecure {
        if let Some(t) = outbound.pointer_mut("/streamSettings/tlsSettings") {
            t["allowInsecure"] = json!(true);
        }
    }
}

/// Start a throw-away xray with only this node on a free local SOCKS port, look up the exit
/// IP through it, then stop it again.
fn exit_probe(core: &Path, dir: &Path, id: usize, outbound: Value, probes: &Probes) -> ExitRes {
    let path = dir.join(format!("v2tui-probe-{id}.json"));
    for _ in 0..2 {
        if probes.stopped() {
            return None;
        }
        let port = free_port()?;
        let cfg = json!({
            "log": { "loglevel": "none" },
            "inbounds": [{
                "listen": "127.0.0.1", "port": port, "protocol": "socks",
                "settings": { "udp": false }
            }],
            "outbounds": [ outbound.clone() ]
        });
        write_private(&path, &serde_json::to_string(&cfg).ok()?).ok()?;
        let spawned = Command::new(core)
            .arg("run")
            .arg("-c")
            .arg(&path)
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .spawn();
        let Ok(mut child) = spawned else {
            let _ = fs::remove_file(&path);
            return None;
        };
        let pid = child.id();
        probes.add(pid, path.clone());

        // Wait (up to 5 s) for the SOCKS port to accept connections.
        let addr: std::net::SocketAddr = ([127, 0, 0, 1], port).into();
        let mut ready = false;
        let mut died = false;
        for _ in 0..50 {
            if probes.stopped() {
                break;
            }
            if matches!(child.try_wait(), Ok(Some(_))) {
                died = true;
                break;
            }
            if TcpStream::connect_timeout(&addr, Duration::from_millis(200)).is_ok() {
                ready = true;
                break;
            }
            thread::sleep(Duration::from_millis(100));
        }
        let res = if ready {
            probe_exit(Some(&format!("127.0.0.1:{port}")))
        } else {
            None
        };
        let _ = child.kill();
        let _ = child.wait();
        probes.remove(pid);
        let _ = fs::remove_file(&path);
        // If xray died at once the port was probably taken by someone else: try a new one.
        if !died {
            return res;
        }
    }
    None
}

fn spawn_exit_probes(
    jobs: Vec<(usize, Value)>,
    core: PathBuf,
    dir: PathBuf,
    probes: Probes,
    tx: Sender<Msg>,
) {
    if jobs.is_empty() {
        return;
    }
    let workers = EXIT_WORKERS.min(jobs.len());
    let queue = Arc::new(Mutex::new(jobs.into_iter().collect::<VecDeque<_>>()));
    for _ in 0..workers {
        let q = Arc::clone(&queue);
        let tx = tx.clone();
        let core = core.clone();
        let dir = dir.clone();
        let probes = probes.clone();
        thread::spawn(move || loop {
            if probes.stopped() {
                break;
            }
            let job = q.lock().unwrap().pop_front();
            let Some((i, outbound)) = job else { break };
            let res = exit_probe(&core, &dir, i, outbound, &probes);
            if tx.send(Msg::Probe(i, res)).is_err() {
                break;
            }
        });
    }
}

fn which(bin: &str) -> Option<PathBuf> {
    let path = std::env::var_os("PATH")?;
    std::env::split_paths(&path)
        .map(|d| d.join(bin))
        .find(|p| p.is_file())
}

fn now_unix() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
}

/// Local wall-clock time, "04:31:12".
fn clock(ts: u64) -> String {
    Local
        .timestamp_opt(ts as i64, 0)
        .single()
        .map(|d| d.format("%H:%M:%S").to_string())
        .unwrap_or_else(|| "?".to_string())
}

fn truncate_chars(s: &str, max: usize) -> String {
    if s.chars().count() <= max {
        return s.to_string();
    }
    let mut t: String = s.chars().take(max.saturating_sub(1)).collect();
    t.push('…');
    t
}

/// SHA-256 (hex) of the nodes a subscription file contains. Identifies the file in cache.json
/// whatever it is called, wherever it lives, or how it is encoded: a base64 subscription and
/// its decoded copy (or one with different line endings, comments or blank lines) parse to
/// the same nodes and so share one cache entry.
fn content_hash(nodes: &[Node]) -> String {
    let mut h = Sha256::new();
    for n in nodes {
        h.update(n.key.as_bytes());
        h.update(b"\n");
    }
    format!("{:x}", h.finalize())
}

fn ping_to_i64(p: Ping) -> Option<i64> {
    match p {
        Ping::Ms(m) => Some(m as i64),
        Ping::Fail => Some(-1),
        Ping::Unknown | Ping::Testing => None,
    }
}

fn ping_from_i64(p: i64) -> Ping {
    if p < 0 {
        Ping::Fail
    } else {
        Ping::Ms(p as u128)
    }
}

fn exit_to_json(e: &ExitState) -> Option<Value> {
    match e {
        ExitState::Ok { ip, code, name } => Some(json!({ "ip": ip, "code": code, "name": name })),
        // A failed exit check is remembered too, so it is shown again next time.
        ExitState::Fail => Some(json!({ "unavailable": true })),
        _ => None,
    }
}

fn exit_from_json(v: &Value) -> Option<ExitState> {
    if v.get("unavailable").and_then(|x| x.as_bool()) == Some(true) {
        return Some(ExitState::Fail);
    }
    let ip = jstr(v, "ip");
    let code = jstr(v, "code");
    let name = jstr(v, "name");
    if ip.is_empty() || code.is_empty() {
        None
    } else {
        Some(ExitState::Ok { ip, code, name })
    }
}

/// Everything about a node that is needed to show it and manage its connection.
fn node_to_json(n: &Node) -> Value {
    json!({
        "key": n.key, "proto": n.proto, "name": n.name, "code": n.code, "country": n.country,
        "host": n.host, "port": n.port, "net": n.net, "sec": n.sec, "sni": n.sni,
        "outbound": n.outbound,
        "ping": ping_to_i64(n.ping),
        "exit": exit_to_json(&n.exit),
    })
}

/// Rebuild a node saved by node_to_json (always flagged `external`).
fn node_from_json(v: &Value) -> Option<Node> {
    let key = jstr(v, "key");
    let host = jstr(v, "host");
    let outbound = v.get("outbound")?.clone();
    if key.is_empty() || host.is_empty() || !outbound.is_object() {
        return None;
    }
    let port = v.get("port")?.as_u64()? as u16;
    Some(Node {
        key,
        proto: jstr(v, "proto"),
        name: jstr(v, "name"),
        code: jstr(v, "code"),
        country: jstr(v, "country"),
        host,
        port,
        net: jstr(v, "net"),
        sec: jstr(v, "sec"),
        sni: jstr(v, "sni"),
        outbound,
        ping: v
            .get("ping")
            .and_then(|x| x.as_i64())
            .map(ping_from_i64)
            .unwrap_or(Ping::Unknown),
        exit: v.get("exit").and_then(exit_from_json).unwrap_or(ExitState::Unknown),
        external: true,
    })
}

/// The "files" map of cache.json: content hash -> what v2tui learned about that file.
fn read_cache(dir: &Path) -> serde_json::Map<String, Value> {
    fs::read_to_string(dir.join(CACHE_FILE))
        .ok()
        .and_then(|t| serde_json::from_str::<Value>(&t).ok())
        .and_then(|v| v.get("files").and_then(|f| f.as_object().cloned()))
        .unwrap_or_default()
}

/// Version 1 of state.json kept one file's pings/exits/selection inside it. Turn that into a
/// cache entry, so the results of the last session are not lost when upgrading.
fn legacy_entry(v: &Value) -> Option<Value> {
    let pings = v.get("pings")?.as_object()?;
    let mut nodes = serde_json::Map::new();
    for (k, p) in pings {
        nodes.entry(k.clone()).or_insert_with(|| json!({}))["ping"] = p.clone();
    }
    if let Some(ex) = v.get("exits").and_then(|x| x.as_object()) {
        for (k, e) in ex {
            nodes.entry(k.clone()).or_insert_with(|| json!({}))["exit"] = e.clone();
        }
    }
    Some(json!({
        "ping_all_at": v.get("ping_all_at"),
        "selected": v.get("selected"),
        "nodes": nodes,
    }))
}

/// Where the cursor was in a file the last time it was open.
#[derive(Default)]
struct SavedView {
    selected: Option<String>,
    row: Option<usize>,
    offset: usize,
}

/// ~/.cache/v2tui (or $XDG_CACHE_HOME/v2tui): settings, per-file cache, core config and core
/// log live here.
fn cache_dir() -> PathBuf {
    let base = std::env::var_os("XDG_CACHE_HOME")
        .filter(|v| !v.is_empty())
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|h| PathBuf::from(h).join(".cache")))
        .unwrap_or_else(std::env::temp_dir);
    let dir = base.join("v2tui");
    let _ = fs::create_dir_all(&dir);
    dir
}

fn write_private(path: &Path, data: &str) -> io::Result<()> {
    let tmp = path.with_extension("tmp");
    fs::OpenOptions::new()
        .write(true)
        .create(true)
        .truncate(true)
        .mode(0o600)
        .open(&tmp)
        .and_then(|mut f| f.write_all(data.as_bytes()))?;
    fs::rename(&tmp, path)
}

/// True if `pid` is a live core that v2tui started (Linux: checks /proc, which also
/// guards against a reused pid and ignores zombies).
fn core_alive(pid: u32) -> bool {
    fs::read(format!("/proc/{pid}/cmdline"))
        .map(|b| String::from_utf8_lossy(&b).contains("v2tui-config.json"))
        .unwrap_or(false)
}

/// True when sudo will run a command right now without asking for a password.
fn sudo_cached() -> bool {
    Command::new("sudo")
        .args(["-n", "true"])
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .map(|s| s.success())
        .unwrap_or(false)
}

/// Stop a root-owned core (VPN mode): SIGTERM first, SIGKILL if it hangs.
/// Kills the pid's children first (xray under the sudo wrapper), then the pid itself.
fn stop_root_core(pid: u32) {
    for sig in ["-TERM", "-KILL"] {
        let _ = Command::new("sudo")
            .args(["-n", "sh", "-c", "pkill \"$1\" -P \"$2\"; kill \"$1\" \"$2\"", "sh", sig])
            .arg(pid.to_string())
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status();
        for _ in 0..40 {
            if !core_alive(pid) {
                return;
            }
            thread::sleep(Duration::from_millis(100));
        }
    }
}

/// In VPN mode xray must not resolve the server's name through the tunnel it is about to
/// create (that would deadlock), so resolve it now and connect by IP. The original name
/// stays in TLS serverName, and is copied into the WebSocket Host header when that is empty.
fn pin_server_ip(outbound: &mut Value) {
    let ptr = if outbound.pointer("/settings/vnext/0/address").is_some() {
        "/settings/vnext/0/address"
    } else {
        "/settings/servers/0/address"
    };
    let Some(host) = outbound.pointer(ptr).and_then(|v| v.as_str()).map(String::from) else {
        return;
    };
    if host.parse::<std::net::IpAddr>().is_ok() {
        return;
    }
    let Some(ip) = (host.as_str(), 443u16)
        .to_socket_addrs()
        .ok()
        .and_then(|mut a| a.next())
        .map(|a| a.ip().to_string())
    else {
        return;
    };
    if let Some(v) = outbound.pointer_mut(ptr) {
        *v = json!(ip);
    }
    if let Some(h) = outbound.pointer_mut("/streamSettings/wsSettings/headers") {
        let empty = h.get("Host").and_then(|x| x.as_str()).map_or(true, |s| s.is_empty());
        if empty {
            h["Host"] = json!(host);
        }
    }
}

fn kill_pid(pid: u32) {
    let _ = Command::new("kill")
        .arg(pid.to_string())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status();
    for _ in 0..30 {
        if !core_alive(pid) {
            break;
        }
        thread::sleep(Duration::from_millis(100));
    }
}

// ───────────────────────────── app state ─────────────────────────────

struct App {
    nodes: Vec<Node>,
    view: Vec<usize>,
    state: TableState,
    filter: String,
    filtering: bool,
    sort: Sort,
    hide_dead: bool,
    insecure: bool,
    active: Option<Active>,
    exit_ip: String,
    status: String,
    core: Option<PathBuf>,
    tx: Sender<Msg>,
    rx: Receiver<Msg>,
    quit: bool,
    show_help: bool,
    /// The field guide popup (what every column / field means).
    show_guide: bool,
    too_small: bool,
    /// Set after the terminal was handed to sudo, so the next frame redraws everything.
    force_redraw: bool,
    /// What Enter does: false = local SOCKS/HTTP proxy, true = system-wide VPN (TUN).
    vpn_mode: bool,
    /// Live pinging (toggle with l): re-test every node every PING_STALE_SECS. Off by default.
    live_ping: bool,
    /// Unix time the last "ping all nodes" was started.
    ping_all_at: Option<u64>,
    status_seen: String,
    status_since: Instant,
    dir: PathBuf,
    last_save: Instant,
    state_dirty: bool,
    /// Temporary xray processes used for exit-IP checks.
    probes: Probes,
    /// SHA-256 of the opened file's content, and where it was opened from.
    file_hash: String,
    file_path: String,
    /// cache.json: what is known about every subscription file seen so far, by hash.
    cache: serde_json::Map<String, Value>,
}

impl App {
    fn new(nodes: Vec<Node>, file_hash: String, file_path: String) -> Self {
        let (tx, rx) = mpsc::channel();
        let core = which("xray");
        let dir = cache_dir();
        let cache = read_cache(&dir);
        let status = String::new(); // the "Core" line in the status box covers a missing core
        let mut app = App {
            nodes,
            view: Vec::new(),
            state: TableState::default(),
            filter: String::new(),
            filtering: false,
            sort: Sort::File,
            hide_dead: false,
            insecure: false,
            active: None,
            exit_ip: String::new(),
            status,
            core,
            tx,
            rx,
            quit: false,
            show_help: false,
            show_guide: false,
            too_small: false,
            force_redraw: false,
            vpn_mode: false,
            live_ping: false,
            ping_all_at: None,
            status_seen: String::new(),
            status_since: Instant::now(),
            dir,
            last_save: Instant::now(),
            state_dirty: false,
            probes: Probes::default(),
            file_hash,
            file_path,
            cache,
        };
        let legacy = app.load_global();
        let saved = app.load_file_cache(legacy);
        app.rebuild();

        // Jump to the running connection's row, else to where you were last time in this file.
        let target = app.active.as_ref().map(|a| a.node).or_else(|| {
            saved
                .selected
                .as_ref()
                .and_then(|k| app.nodes.iter().position(|n| &n.key == k))
        });
        match target.and_then(|t| app.view.iter().position(|&i| i == t)) {
            Some(pos) => app.state.select(Some(pos)),
            None => {
                if let Some(row) = saved.row {
                    if !app.view.is_empty() {
                        app.state.select(Some(row.min(app.view.len() - 1)));
                    }
                }
            }
        }
        *app.state.offset_mut() = saved.offset;
        if app.active.is_some() {
            // No exit-IP request on startup: show what was found last time, if anything.
            // (Press e to check it again.)
            let cached = app.active.as_ref().and_then(|a| match &app.nodes[a.node].exit {
                ExitState::Ok { ip, .. } => Some(ip.clone()),
                _ => None,
            });
            if let Some(ip) = cached {
                app.exit_ip = ip;
            }
        }
        app
    }

    /// state.json: what belongs to you rather than to one subscription file. It stays the
    /// same when you open another file: sort order, mode, toggles and the running connection
    /// (with the node's full data, so it can still be managed if it is not in this file).
    /// Returns the old per-file data when this is a version-1 state.json.
    fn load_global(&mut self) -> Option<Value> {
        let text = fs::read_to_string(self.dir.join("state.json")).ok()?;
        let v: Value = serde_json::from_str(&text).ok()?;
        if let Some(s) = v.get("sort").and_then(|x| x.as_str()) {
            self.sort = Sort::from_id(s);
        }
        self.hide_dead = v.get("hide_dead").and_then(|x| x.as_bool()).unwrap_or(false);
        self.insecure = v.get("insecure").and_then(|x| x.as_bool()).unwrap_or(false);
        self.vpn_mode = v.get("vpn_mode").and_then(|x| x.as_bool()).unwrap_or(false);
        self.live_ping = v.get("live_ping").and_then(|x| x.as_bool()).unwrap_or(false);
        if let Some(a) = v.get("active").filter(|a| a.is_object()) {
            let pid = a.get("pid").and_then(|x| x.as_u64()).unwrap_or(0) as u32;
            let vpn = a.get("vpn").and_then(|x| x.as_bool()).unwrap_or(false);
            let saved_node = a.get("node").and_then(node_from_json);
            let key = a
                .get("key")
                .and_then(|x| x.as_str())
                .map(String::from)
                .or_else(|| saved_node.as_ref().map(|n| n.key.clone()))
                .unwrap_or_default();
            if pid != 0 && core_alive(pid) {
                if let Some(i) = self.nodes.iter().position(|n| n.key == key) {
                    let origin = self.file_hash.clone();
                    self.active = Some(Active { node: i, pid, child: None, vpn, origin });
                } else if let Some(n) = saved_node {
                    // Not in this file (it was changed or replaced): keep the node as saved.
                    let origin = a
                        .get("file_hash")
                        .and_then(|x| x.as_str())
                        .unwrap_or_default()
                        .to_string();
                    self.nodes.push(n);
                    let node = self.nodes.len() - 1;
                    self.active = Some(Active { node, pid, child: None, vpn, origin });
                } else {
                    let how = if vpn { "sudo kill" } else { "kill" };
                    self.status = format!(
                        "a core (pid {pid}) is running but its node is not in this file; stop it with: {how} {pid}"
                    )
                }
            }
        }
        if v.get("version").and_then(|x| x.as_u64()) == Some(1) {
            legacy_entry(&v)
        } else {
            None
        }
    }

    /// This file's entry in cache.json (found by content hash): pings, exit IPs, when "ping
    /// all" last ran, and where the cursor was.
    fn load_file_cache(&mut self, legacy: Option<Value>) -> SavedView {
        let entry = self.cache.get(&self.file_hash).cloned().or(legacy);
        let Some(e) = entry else { return SavedView::default() };
        if let Some(m) = e.get("nodes").and_then(|x| x.as_object()) {
            for n in self.nodes.iter_mut().filter(|n| !n.external) {
                if let Some(d) = m.get(&n.key) {
                    if let Some(p) = d.get("ping").and_then(|x| x.as_i64()) {
                        n.ping = ping_from_i64(p);
                    }
                    if let Some(x) = d.get("exit").and_then(exit_from_json) {
                        n.exit = x;
                    }
                }
            }
        }
        self.ping_all_at = e.get("ping_all_at").and_then(|x| x.as_u64());
        SavedView {
            selected: e.get("selected").and_then(|x| x.as_str()).map(String::from),
            row: e.get("row").and_then(|x| x.as_u64()).map(|x| x as usize),
            offset: e.get("offset").and_then(|x| x.as_u64()).unwrap_or(0) as usize,
        }
    }

    fn save_state(&mut self) {
        self.save_global();
        self.save_cache();
        self.last_save = Instant::now();
        self.state_dirty = false;
    }

    fn save_global(&self) {
        let active = self.active.as_ref().map(|a| {
            let n = &self.nodes[a.node];
            json!({
                "pid": a.pid, "vpn": a.vpn, "key": n.key, "file_hash": a.origin,
                "node": node_to_json(n)
            })
        });
        let state = json!({
            "version": 2,
            "sort": self.sort.id(),
            "hide_dead": self.hide_dead,
            "insecure": self.insecure,
            "vpn_mode": self.vpn_mode,
            "live_ping": self.live_ping,
            "active": active,
        });
        let _ = write_private(
            &self.dir.join("state.json"),
            &serde_json::to_string(&state).unwrap_or_default(),
        );
    }

    /// Update this file's entry in cache.json (other files' entries are kept as they are),
    /// and forget files that are old or beyond the CACHE_MAX_FILES most recent ones.
    fn save_cache(&mut self) {
        let mut nodes = serde_json::Map::new();
        for n in self.nodes.iter().filter(|n| !n.external) {
            let mut d = serde_json::Map::new();
            if let Some(p) = ping_to_i64(n.ping) {
                d.insert("ping".to_string(), json!(p));
            }
            if let Some(x) = exit_to_json(&n.exit) {
                d.insert("exit".to_string(), x);
            }
            if !d.is_empty() {
                nodes.insert(n.key.clone(), Value::Object(d));
            }
        }
        let selected = self
            .selected_node()
            .filter(|&i| !self.nodes[i].external)
            .map(|i| self.nodes[i].key.clone());
        let now = now_unix();
        let entry = json!({
            "path": self.file_path,
            "last_used": now,
            "node_count": self.nodes.iter().filter(|n| !n.external).count(),
            "ping_all_at": self.ping_all_at,
            "selected": selected,
            "row": self.state.selected(),
            "offset": self.state.offset(),
            "nodes": nodes,
        });
        self.cache.insert(self.file_hash.clone(), entry);

        let used = |e: &Value| e.get("last_used").and_then(|x| x.as_u64()).unwrap_or(0);
        self.cache.retain(|_, e| now.saturating_sub(used(&*e)) <= CACHE_MAX_AGE_SECS);
        if self.cache.len() > CACHE_MAX_FILES {
            let mut by_age: Vec<(u64, String)> =
                self.cache.iter().map(|(k, e)| (used(e), k.clone())).collect();
            by_age.sort_unstable_by(|a, b| b.0.cmp(&a.0)); // newest first
            for (_, k) in by_age.into_iter().skip(CACHE_MAX_FILES) {
                self.cache.remove(&k);
            }
        }

        let doc = json!({ "version": 1, "files": self.cache });
        let _ = write_private(
            &self.dir.join(CACHE_FILE),
            &serde_json::to_string(&doc).unwrap_or_default(),
        );
    }

    /// The connected node came from another subscription file (`external`): write its exit
    /// result into that file's entry in cache.json, so it is there when that file is opened.
    /// Nodes of the opened file are saved by save_cache() instead.
    fn store_external_exit(&mut self, i: usize) {
        if !self.nodes[i].external {
            return;
        }
        let Some(origin) = self
            .active
            .as_ref()
            .filter(|a| a.node == i)
            .map(|a| a.origin.clone())
        else {
            return;
        };
        if origin.is_empty() || origin == self.file_hash {
            return; // origin unknown (older state.json)
        }
        let Some(exit) = exit_to_json(&self.nodes[i].exit) else { return };
        let key = self.nodes[i].key.clone();
        let Some(entry) = self.cache.get_mut(&origin).and_then(|e| e.as_object_mut()) else {
            return; // that file's cache entry was forgotten (old or beyond the newest files)
        };
        let nodes = entry.entry("nodes").or_insert_with(|| json!({}));
        let Some(nodes) = nodes.as_object_mut() else { return };
        let node = nodes.entry(key).or_insert_with(|| json!({}));
        if let Some(node) = node.as_object_mut() {
            node.insert("exit".to_string(), exit);
            self.state_dirty = true;
        }
    }

    /// Drop the restored node of an earlier file once it is no longer the connected one.
    fn prune_external(&mut self) {
        let Some(last) = self.nodes.len().checked_sub(1) else { return };
        if self.nodes[last].external && self.active.as_ref().map(|a| a.node) != Some(last) {
            self.nodes.pop();
            self.rebuild();
        }
    }

    fn selected_node(&self) -> Option<usize> {
        self.state.selected().and_then(|p| self.view.get(p).copied())
    }

    fn rebuild(&mut self) {
        let keep = self.selected_node();
        let f = self.filter.to_lowercase();
        let active_node = self.active.as_ref().map(|a| a.node);
        let mut v: Vec<usize> = (0..self.nodes.len())
            .filter(|&i| {
                // The still-running connection of another file is not listed here.
                if self.nodes[i].external {
                    return false;
                }
                // The connected node is always listed, whatever the filters say.
                if Some(i) == active_node {
                    return true;
                }
                let n = &self.nodes[i];
                if self.hide_dead && n.ping == Ping::Fail {
                    return false;
                }
                f.is_empty() || n.haystack().contains(&f)
            })
            .collect();
        match self.sort {
            Sort::File => {}
            Sort::Ping => v.sort_by_key(|&i| self.nodes[i].ping.sort_key()),
            Sort::Country => v.sort_by(|&a, &b| {
                self.nodes[a].country.cmp(&self.nodes[b].country)
            }),
            Sort::Proto => v.sort_by(|&a, &b| self.nodes[a].proto.cmp(&self.nodes[b].proto)),
        }
        self.view = v;
        let pos = keep
            .and_then(|k| self.view.iter().position(|&i| i == k))
            .or_else(|| {
                if self.view.is_empty() {
                    None
                } else {
                    Some(self.state.selected().unwrap_or(0).min(self.view.len() - 1))
                }
            });
        self.state.select(pos);
    }

    fn test(&mut self, idxs: Vec<usize>) {
        let mut jobs: Vec<(usize, String, u16)> = Vec::with_capacity(idxs.len());
        for i in idxs {
            self.nodes[i].ping = Ping::Testing;
            jobs.push((i, self.nodes[i].host.clone(), self.nodes[i].port));
        }
        spawn_pings(jobs, self.tx.clone());
    }

    /// Re-test every node quietly: results replace the old ones as they arrive, without
    /// the "..." state, so rows do not jump around every 5 minutes.
    fn auto_ping_all(&mut self) {
        self.ping_all_at = Some(now_unix());
        self.state_dirty = true;
        let jobs: Vec<(usize, String, u16)> = self
            .nodes
            .iter()
            .enumerate()
            .map(|(i, n)| (i, n.host.clone(), n.port))
            .collect();
        spawn_pings(jobs, self.tx.clone());
    }

    /// Find the real exit IP (and its country) of the given nodes. The connected node is
    /// checked through the running connection; every other node gets a temporary xray.
    fn test_exit(&mut self, idxs: Vec<usize>) {
        let Some(core) = self.core.clone() else {
            self.status = "xray not found in PATH".into();
            return;
        };
        let active = self.active.as_ref().map(|a| a.node);
        let mut jobs: Vec<(usize, Value)> = Vec::new();
        let mut check_active = false;
        for i in idxs {
            if self.nodes[i].exit == ExitState::Testing {
                continue;
            }
            self.nodes[i].exit = ExitState::Testing;
            if Some(i) == active {
                check_active = true;
            } else {
                let mut outbound = self.nodes[i].outbound.clone();
                apply_insecure(&mut outbound, self.insecure);
                jobs.push((i, outbound));
            }
        }
        if check_active {
            self.check_exit_after(false);
        }
        spawn_exit_probes(jobs, core, self.dir.clone(), self.probes.clone(), self.tx.clone());
    }

    fn check_exit(&mut self) {
        self.check_exit_after(true);
    }

    /// Exit IP of the running connection. `wait` gives a freshly started core time to come up.
    fn check_exit_after(&mut self, wait: bool) {
        let Some((node, vpn)) = self.active.as_ref().map(|a| (a.node, a.vpn)) else { return };
        self.exit_ip = "checking...".into();
        let tx = self.tx.clone();
        thread::spawn(move || {
            if wait {
                // The tunnel takes a little longer to come up than a local proxy.
                thread::sleep(Duration::from_millis(if vpn { 2500 } else { 1500 }));
            }
            let proxy = format!("127.0.0.1:{SOCKS_PORT}");
            let mut res = probe_exit(if vpn { None } else { Some(proxy.as_str()) });
            if wait && res.is_none() {
                // Right after connecting the core may still be starting: try once more.
                thread::sleep(Duration::from_millis(1000));
                res = probe_exit(if vpn { None } else { Some(proxy.as_str()) });
            }
            let _ = tx.send(Msg::Exit(node, res));
        });
    }

    fn connect(&mut self) {
        let Some(i) = self.selected_node() else { return };
        self.connect_node(i);
    }

    /// Stop whatever is running and bring node `i` up in the current mode.
    fn connect_node(&mut self, i: usize) {
        let Some(core) = self.core.clone() else {
            self.status = "xray not found in PATH".into();
            return;
        };
        let vpn = self.vpn_mode;
        // Which subscription file the node belongs to. Reconnecting a restored node of an
        // earlier file (mode switch) keeps that file as its origin.
        let origin = if self.nodes[i].external {
            self.active.as_ref().map(|a| a.origin.clone()).unwrap_or_default()
        } else {
            self.file_hash.clone()
        };
        if vpn && !self.ensure_sudo() {
            self.status = "VPN not started: sudo failed or was cancelled".into();
            return;
        }
        self.disconnect();
        if self.active.is_some() {
            return; // the previous connection could not be stopped; disconnect() said why
        }

        let mut outbound = self.nodes[i].outbound.clone();
        apply_insecure(&mut outbound, self.insecure);

        let cfg = if vpn {
            // System-wide: one TUN inbound, no local proxy ports. Xray adds the default
            // routes itself and keeps its own outbound traffic on the real interface.
            pin_server_ip(&mut outbound);
            json!({
                "log": { "loglevel": "warning" },
                "inbounds": [{
                    "tag": "tun",
                    "protocol": "tun",
                    "settings": {
                        "name": TUN_NAME,
                        "mtu": 1500,
                        "gateway": ["198.18.0.1/16", "fdfe:dcba:9876::1/64"],
                        "autoSystemRoutingTable": ["0.0.0.0/0", "::/0"],
                        "autoOutboundsInterface": "auto"
                    }
                }],
                "outbounds": [ outbound, { "protocol": "freedom", "tag": "direct" } ]
            })
        } else {
            json!({
                "log": { "loglevel": "warning" },
                "inbounds": [
                    { "tag": "socks", "listen": "127.0.0.1", "port": SOCKS_PORT, "protocol": "socks",
                      "settings": { "udp": true },
                      "sniffing": { "enabled": true, "destOverride": ["http", "tls"] } },
                    { "tag": "http", "listen": "127.0.0.1", "port": HTTP_PORT, "protocol": "http" }
                ],
                "outbounds": [ outbound, { "protocol": "freedom", "tag": "direct" } ]
            })
        };

        let path = self.dir.join("v2tui-config.json");
        let cfg_text = serde_json::to_string_pretty(&cfg).unwrap_or_default();
        if let Err(e) = write_private(&path, &cfg_text) {
            self.status = format!("cannot write config: {e}");
            return;
        }

        // Keep the core's output so a failure can be explained.
        let log = fs::OpenOptions::new()
            .write(true)
            .create(true)
            .truncate(true)
            .mode(0o600)
            .open(self.dir.join("v2tui-core.log"));
        let (out, err) = match log.and_then(|f| f.try_clone().map(|g| (f, g))) {
            Ok((a, b)) => (Stdio::from(a), Stdio::from(b)),
            Err(_) => (Stdio::null(), Stdio::null()),
        };

        // VPN mode needs root (tunnel device + routes), so the core runs under `sudo -n`.
        // sudo's password was already cached by ensure_sudo().
        let mut cmd = if vpn {
            let mut c = Command::new("sudo");
            c.arg("-n").arg("--").arg(&core);
            c
        } else {
            Command::new(&core)
        };

        // Own process group, so Ctrl-C or quitting v2tui does not take the core down.
        match cmd
            .arg("run")
            .arg("-c")
            .arg(&path)
            .stdin(Stdio::null())
            .stdout(out)
            .stderr(err)
            .process_group(0)
            .spawn()
        {
            Ok(child) => {
                let pid = child.id();
                self.status = if vpn {
                    format!("started VPN via {} (pid {pid}); whole system now uses this node", core.display())
                } else {
                    format!("started {} (pid {pid}); it keeps running after you quit", core.display())
                };
                self.active = Some(Active { node: i, pid, child: Some(child), vpn, origin });

                // No known exit IP yet (or the last check failed) -> show "checking..." in
                // Selected node -> Exit IP until the new check answers.
                if !matches!(self.nodes[i].exit, ExitState::Ok { .. }) {
                    self.nodes[i].exit = ExitState::Testing;
                }

                self.check_exit();
                self.prune_external();
                self.save_state();
            }
            Err(e) => self.status = format!("failed to start {}: {e}", core.display()),
        }
    }

    /// Hand the terminal to `sudo -v` for a moment if a password is needed, then take it back.
    fn ensure_sudo(&mut self) -> bool {
        if sudo_cached() {
            return true;
        }
        let mut out = io::stdout();
        let _ = execute!(out, LeaveAlternateScreen, Show);
        let _ = disable_raw_mode();
        println!("\nv2tui: VPN mode needs root to create the tunnel and set routes.");
        let ok = Command::new("sudo")
            .arg("-v")
            .status()
            .map(|s| s.success())
            .unwrap_or(false);
        let _ = enable_raw_mode();
        let _ = execute!(out, EnterAlternateScreen, Hide);
        self.force_redraw = true;
        ok
    }

    fn disconnect(&mut self) {
        let Some(vpn) = self.active.as_ref().map(|a| a.vpn) else { return };
        if vpn && !self.ensure_sudo() {
            let pid = self.active.as_ref().map(|a| a.pid).unwrap_or(0);
            self.status = format!("cannot stop the VPN without sudo; run: sudo kill {pid}");
            return;
        }
        let Some(mut a) = self.active.take() else { return };
        if a.vpn {
            stop_root_core(a.pid);
            if let Some(c) = a.child.as_mut() {
                for _ in 0..20 {
                    if matches!(c.try_wait(), Ok(Some(_))) {
                        break;
                    }
                    thread::sleep(Duration::from_millis(100));
                }
            }
        } else {
            match a.child.as_mut() {
                Some(c) => {
                    let _ = c.kill();
                    let _ = c.wait();
                }
                None => kill_pid(a.pid),
            }
        }
        self.status = "disconnected".into();
        self.exit_ip.clear();
        self.save_state();
    }

    fn tick(&mut self) {
        let mut dirty = false;
        let mut exit_changed = false;

        // Live ping (only when switched on with l): test every node again whenever the last
        // "ping all" is 5 minutes old, or there has not been one yet.
        if self.live_ping {
            let due = match self.ping_all_at {
                None => true,
                Some(t) => now_unix().saturating_sub(t) >= PING_STALE_SECS,
            };
            if due && !self.nodes.iter().any(|n| n.ping == Ping::Testing) {
                self.auto_ping_all();
            }
        }
        if self.status != self.status_seen {
            self.status_seen = self.status.clone();
            self.status_since = Instant::now();
        }
        while let Ok(msg) = self.rx.try_recv() {
            match msg {
                Msg::Ping(i, p) => {
                    if i < self.nodes.len() {
                        self.nodes[i].ping = p;
                        dirty = true;
                    }
                }
                Msg::Exit(i, res) => {
                    if i >= self.nodes.len() {
                        continue; // the node was dropped (see prune_external)
                    }
                    if self.active.as_ref().map(|a| a.node) == Some(i) {
                        match res {
                            Some((ip, code, name)) => {
                                self.exit_ip = ip.clone();
                                self.nodes[i].exit = ExitState::Ok { ip, code, name };
                            }
                            None => {
                                // Unavailable: remembered (cache) and shown in red, also when
                                // an earlier check had found an address.
                                self.exit_ip.clear();
                                self.nodes[i].exit = ExitState::Fail;
                            }
                        }
                        // A restored node of another file is not saved with this file's
                        // cache, so put the result into the cache of its own file.
                        self.store_external_exit(i);
                        dirty = true;
                        exit_changed = true;
                    } else if self.nodes[i].exit == ExitState::Testing {
                        // The connection changed while the check was running.
                        self.nodes[i].exit = ExitState::Unknown;
                    }
                }
                Msg::Probe(i, res) => {
                    if i < self.nodes.len() {
                        self.nodes[i].exit = match res {
                            Some((ip, code, name)) => ExitState::Ok { ip, code, name },
                            None => ExitState::Fail,
                        };
                        dirty = true;
                        exit_changed = true;
                    }
                }
            }
        }
        if dirty {
            self.state_dirty = true;
        }
        if exit_changed && !self.filter.is_empty() {
            self.rebuild(); // the filter also searches the exit country
        }
        if dirty && (self.sort == Sort::Ping || self.hide_dead) {
            self.rebuild();
        }

        // Has the core died? (Either our own child, or one we re-attached to.)
        let exited: Option<String> = match self.active.as_mut() {
            Some(a) => match a.child.as_mut() {
                Some(c) => c.try_wait().ok().flatten().map(|st| st.to_string()),
                None => {
                    if core_alive(a.pid) {
                        None
                    } else {
                        Some("process ended".to_string())
                    }
                }
            },
            None => None,
        };
        if let Some(st) = exited {
            let log_path = self.dir.join("v2tui-core.log");
            let tail = fs::read_to_string(&log_path)
                .ok()
                .and_then(|s| {
                    s.lines()
                        .rev()
                        .find(|l| !l.trim().is_empty())
                        .map(|l| l.trim().to_string())
                })
                .unwrap_or_else(|| format!("no output (see {})", log_path.display()));
            self.status = format!("core exited ({st}): {tail}");
            self.active = None;
            self.exit_ip.clear();
            self.prune_external();
            self.save_state();
        }

        // Autosave so the cache survives a closed terminal or a crash.
        if self.state_dirty && self.last_save.elapsed() > Duration::from_secs(3) {
            self.save_state();
        }
    }

    fn move_sel(&mut self, delta: isize) {
        if self.view.is_empty() {
            return;
        }
        let cur = self.state.selected().unwrap_or(0) as isize;
        let n = (cur + delta).clamp(0, self.view.len() as isize - 1) as usize;
        self.state.select(Some(n));
    }

    fn on_key(&mut self, k: KeyEvent) {
        if self.show_help {
            if k.modifiers.contains(KeyModifiers::CONTROL) && k.code == KeyCode::Char('c') {
                self.quit = true;
            } else if matches!(
                k.code,
                KeyCode::Esc | KeyCode::Enter | KeyCode::Char('?') | KeyCode::Char('q')
            ) {
                self.show_help = false;
            }
            return;
        }
        if self.show_guide {
            if k.modifiers.contains(KeyModifiers::CONTROL) && k.code == KeyCode::Char('c') {
                self.quit = true;
            } else if matches!(
                k.code,
                KeyCode::Esc | KeyCode::Enter | KeyCode::Char('f') | KeyCode::Char('q')
            ) {
                self.show_guide = false;
            }
            return;
        }
        if self.filtering {
            match k.code {
                KeyCode::Enter | KeyCode::Esc => self.filtering = false,
                KeyCode::Backspace => {
                    self.filter.pop();
                    self.rebuild();
                }
                KeyCode::Char(c) => {
                    self.filter.push(c);
                    self.rebuild();
                }
                _ => {}
            }
            return;
        }
        if k.modifiers.contains(KeyModifiers::CONTROL) && k.code == KeyCode::Char('c') {
            self.quit = true;
            return;
        }
        match k.code {
            KeyCode::Char('q') => self.quit = true, // leaves the connection running
            KeyCode::Char('Q') => {
                self.disconnect();
                // If a VPN could not be stopped (no sudo), stay open so the reason is visible.
                if self.active.is_none() {
                    self.quit = true;
                }
            }
            KeyCode::Char('m') => {
                let old_mode = self.vpn_mode;
                let running = self.active.as_ref().map(|a| a.node);
                self.vpn_mode = !old_mode;
                self.state_dirty = true;
                match running {
                    // Connected: drop the current connection and bring the same node
                    // back up in the new mode.
                    Some(node) => {
                        self.connect_node(node);
                        // If the old connection could not be replaced (for example sudo was
                        // refused) it is still running in the old mode, so keep the mode
                        // shown in step with what is really running.
                        if self.active.as_ref().is_some_and(|a| a.vpn != self.vpn_mode) {
                            self.vpn_mode = old_mode;
                        }
                    }
                    None => {
                        self.status = if self.vpn_mode {
                            "mode: system VPN - Enter sends all system traffic through the node, no proxy URL (asks for sudo)".into()
                        } else {
                            format!("mode: proxy URL - Enter gives you socks5h://127.0.0.1:{SOCKS_PORT} and http://127.0.0.1:{HTTP_PORT} to use in apps")
                        };
                    }
                }
            }
            KeyCode::Esc => {
                if !self.filter.is_empty() {
                    self.filter.clear();
                    self.rebuild();
                }
            }
            KeyCode::Down | KeyCode::Char('j') => self.move_sel(1),
            KeyCode::Up | KeyCode::Char('k') => self.move_sel(-1),
            KeyCode::PageDown => self.move_sel(10),
            KeyCode::PageUp => self.move_sel(-10),
            KeyCode::Home | KeyCode::Char('g') => self.state.select(if self.view.is_empty() { None } else { Some(0) }),
            KeyCode::End | KeyCode::Char('G') => {
                self.state.select(self.view.len().checked_sub(1))
            }
            KeyCode::Char('c') => match self.active.as_ref().map(|a| a.node) {
                Some(node) => {
                    if let Some(pos) = self.view.iter().position(|&i| i == node) {
                        self.state.select(Some(pos));
                    }
                }
                None => self.status = "not connected".into(),
            },
            KeyCode::Enter => self.connect(),
            KeyCode::Char('x') => {
                self.disconnect();
                self.prune_external();
            }
            KeyCode::Char('e') => self.check_exit(),
            KeyCode::Char('i') => {
                self.insecure = !self.insecure;
                self.state_dirty = true;
                self.status = if self.insecure {
                    "insecure TLS ON: certificates are not verified (applies on next connect)".into()
                } else {
                    "insecure TLS off: certificates are verified (applies on next connect)".into()
                };
            }
            KeyCode::Char('t') => {
                if let Some(i) = self.selected_node() {
                    self.test(vec![i]);
                }
            }
            KeyCode::Char('T') => {
                if let Some(i) = self.selected_node() {
                    self.status = "checking the exit IP of the selected node...".into();
                    self.test_exit(vec![i]);
                }
            }
            KeyCode::Char('P') => {
                let all: Vec<usize> = (0..self.nodes.len()).collect();
                self.status = format!(
                    "checking the exit IP of {} nodes ({EXIT_WORKERS} at a time, one xray each)...",
                    all.len()
                );
                self.test_exit(all);
            }
            KeyCode::Char('l') => {
                self.live_ping = !self.live_ping;
                self.state_dirty = true;
                self.status = if self.live_ping {
                    "live ping ON: all nodes are re-tested every 5 minutes".into()
                } else {
                    "live ping off: press p to test all nodes".into()
                };
            }
            KeyCode::Char('p') => {
                // "Ping all" means every node, not just the rows a filter leaves visible,
                // so the "last ping-all" time in the status box stays truthful.
                let all: Vec<usize> = (0..self.nodes.len()).collect();
                self.ping_all_at = Some(now_unix());
                self.state_dirty = true;
                self.test(all);
            }
            KeyCode::Char('s') => {
                self.sort = self.sort.next();
                self.state_dirty = true;
                self.rebuild();
            }
            KeyCode::Char('a') => {
                self.hide_dead = !self.hide_dead;
                self.state_dirty = true;
                self.rebuild();
            }
            KeyCode::Char('/') => self.filtering = true,
            KeyCode::Char('?') => self.show_help = true,
            KeyCode::Char('f') => self.show_guide = true,
            _ => {}
        }
    }
}

// ───────────────────────────── rendering ─────────────────────────────

fn dim() -> Style {
    Style::default().fg(Color::DarkGray)
}

fn block(title: &str) -> Block<'static> {
    Block::bordered()
        .border_type(BorderType::Rounded)
        .border_style(Style::default().fg(Color::Rgb(90, 100, 140)))
        .title(format!(" {title} "))
}

fn ping_cell(p: Ping) -> (String, Style) {
    match p {
        Ping::Unknown => ("-".into(), dim()),
        Ping::Testing => ("...".into(), Style::default().fg(Color::Yellow)),
        Ping::Ms(m) => {
            let c = if m < 120 {
                Color::Green
            } else if m < 300 {
                Color::Yellow
            } else {
                Color::Red
            };
            (format!("{m} ms"), Style::default().fg(c))
        }
        Ping::Fail => ("timeout".into(), Style::default().fg(Color::Red)),
    }
}

fn proto_color(p: &str) -> Color {
    match p {
        "vmess" => Color::Cyan,
        "vless" => Color::Magenta,
        "trojan" => Color::Yellow,
        "ss" => Color::Green,
        _ => Color::White,
    }
}

fn kv(label: &str, value: String) -> Line<'static> {
    Line::from(vec![
        Span::styled(format!("{label:<11}"), dim()),
        Span::raw(value),
    ])
}

/// btop-style notice shown instead of the UI when the terminal is below MIN_W x MIN_H.
fn draw_too_small(f: &mut Frame, area: Rect) {
    let need = |have: u16, want: u16| {
        Style::default()
            .fg(if have >= want { Color::Green } else { Color::Red })
            .add_modifier(Modifier::BOLD)
    };
    let lines = vec![
        Line::from(Span::styled(
            "Error: Terminal size too small:",
            Style::default().fg(Color::Red).add_modifier(Modifier::BOLD),
        )),
        Line::from(vec![
            Span::raw("Width = "),
            Span::styled(area.width.to_string(), need(area.width, MIN_W)),
            Span::raw("  Height = "),
            Span::styled(area.height.to_string(), need(area.height, MIN_H)),
        ]),
        Line::from(""),
        Line::from("Needed for current config:"),
        Line::from(vec![
            Span::raw("Width = "),
            Span::styled(MIN_W.to_string(), Style::default().fg(Color::Green)),
            Span::raw("  Height = "),
            Span::styled(MIN_H.to_string(), Style::default().fg(Color::Green)),
        ]),
        Line::from(""),
        Line::from(Span::styled("Resize the window, or press q to quit", dim())),
    ];
    let h = (lines.len() as u16).min(area.height);
    let r = Rect {
        x: area.x,
        y: area.y + (area.height - h) / 2,
        width: area.width,
        height: h,
    };
    f.render_widget(Clear, area);
    f.render_widget(Paragraph::new(lines).alignment(Alignment::Center), r);
}

fn ui(f: &mut Frame, app: &mut App) {
    let area = f.area();
    app.too_small = area.width < MIN_W || area.height < MIN_H;
    if app.too_small {
        draw_too_small(f, area);
        return;
    }
    let rows = Layout::vertical([
        Constraint::Length(6), // status: counts + core / ping / log-or-message lines
        Constraint::Min(6),
        Constraint::Length(10),
        Constraint::Length(1),
    ])
    .split(f.area());
    draw_header(f, app, rows[0]);
    draw_table(f, app, rows[1]);
    draw_details(f, app, rows[2]);
    draw_footer(f, app, rows[3]);
    if app.show_help {
        draw_help(f);
    }
    if app.show_guide {
        draw_guide(f);
    }
}

fn draw_header(f: &mut Frame, app: &App, area: Rect) {
    // A restored connection from another file is not one of this file's nodes.
    let total = app.nodes.iter().filter(|n| !n.external).count();
    let ok = app.nodes.iter().filter(|n| !n.external && matches!(n.ping, Ping::Ms(_))).count();
    let dead = app.nodes.iter().filter(|n| !n.external && n.ping == Ping::Fail).count();
    let testing = app.nodes.iter().filter(|n| n.ping == Ping::Testing).count();
    let exit_testing = app.nodes.iter().filter(|n| n.exit == ExitState::Testing).count();
    let mut spans = vec![
        Span::raw(format!("{total} nodes  ")),
        Span::styled(format!("{ok} reachable  "), Style::default().fg(Color::Green)),
        Span::styled(format!("{dead} timeout  "), Style::default().fg(Color::Red)),
    ];
    if testing > 0 {
        spans.push(Span::styled(
            format!("{testing} testing...  "),
            Style::default().fg(Color::Yellow),
        ));
    }
    if exit_testing > 0 {
        spans.push(Span::styled(
            format!("{exit_testing} checking exit IP...  "),
            Style::default().fg(Color::Yellow),
        ));
    }
    spans.push(Span::styled("sort ", dim()));
    spans.push(Span::styled(
        app.sort.label(),
        Style::default().fg(Color::Rgb(125, 170, 255)).add_modifier(Modifier::BOLD),
    ));
    spans.push(Span::styled("  mode ", dim()));
    spans.push(if app.vpn_mode {
        Span::styled("system VPN", Style::default().fg(Color::Magenta).add_modifier(Modifier::BOLD))
    } else {
        Span::styled("proxy URL", Style::default().fg(Color::Cyan).add_modifier(Modifier::BOLD))
    });
    if app.hide_dead {
        spans.push(Span::styled("  [hiding timeouts]", dim()));
    }
    if app.live_ping {
        spans.push(Span::styled("  [live ping]", Style::default().fg(Color::Green)));
    }
    if app.insecure {
        spans.push(Span::styled("  [insecure TLS]", Style::default().fg(Color::Red)));
    }

    let outer = block("Status");
    let inner = outer.inner(area);
    f.render_widget(outer, area);

    // Fixed layout, nothing reserved on demand: counts, then exactly three lines.
    let rows = Layout::vertical([Constraint::Length(1); 4]).split(inner);
    f.render_widget(Paragraph::new(Line::from(spans)), rows[0]);

    // Every line is cut to the box width (<= 128 columns at the 130-column minimum).
    let width = inner.width as usize;
    let line = |label: &str, text: String, style: Style| -> Line<'static> {
        Line::from(vec![
            Span::styled(format!("{label:<6}"), dim()),
            Span::styled(truncate_chars(&text, width.saturating_sub(6)), style),
        ])
    };

    // i) Is a core installed?
    let core_line = match &app.core {
        Some(p) => {
            let name = p.file_name().map(|n| n.to_string_lossy().into_owned()).unwrap_or_default();
            line(
                "Core",
                format!("{name} installed ({})", p.display()),
                Style::default().fg(Color::Green),
            )
        }
        None => line(
            "Core",
            "xray not installed (not found in PATH)".into(),
            Style::default().fg(Color::Red),
        ),
    };
    f.render_widget(Paragraph::new(core_line), rows[1]);

    // ii) When "ping all" last ran; flips to a warning live once it is over 5 minutes old.
    let (ptxt, pstyle) = ping_status(app);
    f.render_widget(Paragraph::new(line("Ping", ptxt, pstyle)), rows[2]);

    // iii) Normally where the log lives; briefly (or, for errors, until replaced) a message.
    let show_msg = !app.status.is_empty()
        && (is_error(&app.status) || app.status_since.elapsed() < Duration::from_secs(8));
    let info_line = if show_msg {
        line("Msg", app.status.clone(), status_style(&app.status))
    } else {
        line(
            "Log",
            format!(
                "Xray output and any errors are saved in {}",
                app.dir.join("v2tui-core.log").display()
            ),
            Style::default(),
        )
    };
    f.render_widget(Paragraph::new(info_line), rows[3]);
}

/// Status of the "ping all nodes" cache, recomputed on every frame so it changes live.
fn ping_status(app: &App) -> (String, Style) {
    let testing = app.nodes.iter().filter(|n| n.ping == Ping::Testing).count();
    if testing > 0 {
        return (
            format!("testing nodes... {testing} left"),
            Style::default().fg(Color::Yellow),
        );
    }
    match app.ping_all_at {
        None => ("not tested yet - press p to test all nodes".into(), dim()),
        Some(t) if now_unix().saturating_sub(t) > PING_STALE_SECS => (
            format!(
                "OLD - all nodes last tested at {}, over 5 min ago - press p to refresh",
                clock(t)
            ),
            Style::default().fg(Color::Yellow),
        ),
        Some(t) => {
            let text = if app.live_ping {
                format!(
                    "fresh - all nodes tested at {}, live ping refreshes at {}",
                    clock(t),
                    clock(t + PING_STALE_SECS)
                )
            } else {
                format!("fresh - all nodes tested at {}", clock(t))
            };
            (text, Style::default().fg(Color::Green))
        }
    }
}

fn draw_table(f: &mut Frame, app: &mut App, area: Rect) {
    let active_node = app.active.as_ref().map(|a| a.node);
    let rows: Vec<Row> = app
        .view
        .iter()
        .map(|&i| {
            let n = &app.nodes[i];
            let (ptxt, pstyle) = ping_cell(n.ping);
            let is_active = active_node == Some(i);
            // Red when the exit check failed ("unavailable"); yellow when the real exit
            // country is not the one the node's name claims.
            let real_style = if n.exit == ExitState::Fail {
                Style::default().fg(Color::Red)
            } else if n.exit_differs() {
                Style::default().fg(Color::Yellow).add_modifier(Modifier::BOLD)
            } else {
                Style::default()
            };
            Row::new(vec![
                Cell::from(if is_active { "●" } else { " " })
                    .style(Style::default().fg(Color::Green)),
                Cell::from(if n.external { "  -".to_string() } else { format!("{:>3}", i + 1) })
                    .style(dim()),
                Cell::from(n.country.clone()),
                Cell::from(n.exit_country()).style(real_style),
                Cell::from(n.proto.to_uppercase())
                    .style(Style::default().fg(proto_color(&n.proto))),
                Cell::from(n.host.clone()),
                Cell::from(n.port.to_string()),
                Cell::from(n.net.clone()),
                Cell::from(n.sec.clone()),
                Cell::from(ptxt).style(pstyle),
                Cell::from(n.name.clone()).style(dim()),
            ])
        })
        .collect();

    let header = Row::new([
        "", "#", "Country", "Exit", "Type", "Address", "Port", "Net", "Sec", "Ping", "Name",
    ])
        .style(Style::default().fg(Color::Yellow).add_modifier(Modifier::BOLD));

    // Tuned for 130 columns: the fixed columns take ~106, the Name column gets the rest (~20).
    let widths = [
        Constraint::Length(1),  // active marker
        Constraint::Length(4),  // #
        Constraint::Length(16), // country (from the node's name)
        Constraint::Length(16), // exit: country of the real exit IP (blank until checked)
        Constraint::Length(6),  // type
        Constraint::Length(26), // address (domains can be long)
        Constraint::Length(6),  // port
        Constraint::Length(6),  // net
        Constraint::Length(7),  // sec
        Constraint::Length(8),  // ping
        Constraint::Min(12),    // name
    ];

    let shown = app.view.iter().filter(|&&i| !app.nodes[i].external).count();
    let title = format!(
        "Servers {}/{}",
        shown,
        app.nodes.iter().filter(|n| !n.external).count()
    );
    let table = Table::new(rows, widths)
        .header(header)
        .block(block(&title))
        .column_spacing(1)
        .highlight_style(
            Style::default()
                .bg(Color::Rgb(40, 44, 70))
                .add_modifier(Modifier::BOLD),
        )
        .highlight_symbol("▶ ");
    // The table scrolls by remembering its first visible row. When the list gets shorter (a
    // filter, hiding timeouts) that remembered row can lie past the new end, which left only
    // the selected row on screen. Pull it back so the last page is always full.
    let visible = area.height.saturating_sub(3) as usize; // 2 borders + the header row
    let max_offset = app.view.len().saturating_sub(visible);
    if app.state.offset() > max_offset {
        *app.state.offset_mut() = max_offset;
    }
    f.render_stateful_widget(table, area, &mut app.state);
}

fn draw_details(f: &mut Frame, app: &App, area: Rect) {
    let cols = Layout::horizontal([Constraint::Percentage(50), Constraint::Percentage(50)]).split(area);

    let left: Vec<Line> = match app.selected_node().map(|i| &app.nodes[i]) {
        Some(n) => {
            let (pt, ps) = ping_cell(n.ping);
            let exit_label = Span::styled(format!("{:<11}", "Exit IP"), dim());
            let exit_line = match &n.exit {
                ExitState::Unknown => Line::from(vec![
                    exit_label,
                    Span::styled("not checked - press T", dim()),
                ]),
                ExitState::Testing => Line::from(vec![
                    exit_label,
                    Span::styled("checking...", Style::default().fg(Color::Yellow)),
                ]),
                ExitState::Fail => Line::from(vec![
                    exit_label,
                    Span::styled("unavailable", Style::default().fg(Color::Red)),
                ]),
                ExitState::Ok { ip, name, .. } => {
                    let mut v = vec![exit_label, Span::raw(format!("{ip}  {name}"))];
                    if n.exit_differs() {
                        v.push(Span::styled("  (≠ listed)", Style::default().fg(Color::Yellow)));
                    }
                    Line::from(v)
                }
            };
            vec![
                kv("Country", n.country.clone()),
                kv("Protocol", n.proto.to_uppercase()),
                kv("Server", format!("{}:{}", n.host, n.port)),
                kv("Transport", format!("{} / {}", n.net, n.sec)),
                kv("SNI", if n.sni.is_empty() { "-".into() } else { n.sni.clone() }),
                Line::from(vec![
                    Span::styled(format!("{:<11}", "TCP ping"), dim()),
                    Span::styled(pt, ps),
                ]),
                exit_line,
                kv("Name", n.name.clone()),
            ]
        }
        None => vec![Line::from(Span::styled("No node selected", dim()))],
    };
    f.render_widget(Paragraph::new(left).block(block("Selected node")), cols[0]);

    let mut right: Vec<Line> = Vec::new();
    match &app.active {
        Some(a) => {
            let n = &app.nodes[a.node];
            right.push(Line::from(vec![
                Span::styled(format!("{:<11}", "Status"), dim()),
                Span::styled("● connected", Style::default().fg(Color::Green)),
            ]));
            right.push(kv("Node", format!("{} {} ({})", n.country, n.host, n.proto.to_uppercase())));
            if a.vpn {
                right.push(kv("Mode", MODE_VPN.into()));
                right.push(kv("Interface", TUN_NAME.into()));
                right.push(active_exit_line(app, a.node));
            } else {
                right.push(kv("Mode", MODE_PROXY_URL.into()));
                right.push(kv("SOCKS5 URL", format!("socks5h://127.0.0.1:{SOCKS_PORT}")));
                right.push(kv("HTTP URL", format!("http://127.0.0.1:{HTTP_PORT}")));
                right.push(active_exit_line(app, a.node));
            }
        }
        None => {
            right.push(Line::from(vec![
                Span::styled(format!("{:<11}", "Status"), dim()),
                Span::styled("○ disconnected", dim()),
            ]));
            right.push(kv(
                "Mode",
                if app.vpn_mode {
                    MODE_VPN.into()
                } else {
                    MODE_PROXY_URL.into()
                },
            ));
        }
    }
    f.render_widget(
        Paragraph::new(right)
            .wrap(Wrap { trim: true })
            .block(block("Connection")),
        cols[1],
    );
}

/// The "Exit IP" line of the Connection box: the address of the running connection with its
/// country once known, "checking..." while a check runs, red "unavailable" if it failed.
fn active_exit_line(app: &App, node: usize) -> Line<'static> {
    let n = &app.nodes[node];
    let (text, style) = if app.exit_ip == "checking..." || n.exit == ExitState::Testing {
        ("checking...".to_string(), Style::default().fg(Color::Yellow))
    } else {
        match &n.exit {
            ExitState::Ok { ip, code, name } if code != "??" => {
                (format!("{ip}  ({name})"), Style::default())
            }
            ExitState::Ok { ip, .. } => (ip.clone(), Style::default()),
            ExitState::Fail => ("unavailable".to_string(), Style::default().fg(Color::Red)),
            _ => ("not checked - press e".to_string(), dim()),
        }
    };
    Line::from(vec![
        Span::styled(format!("{:<11}", "Exit IP"), dim()),
        Span::styled(text, style),
    ])
}

/// Errors stay in the status box until something replaces them; other messages fade.
fn is_error(s: &str) -> bool {
    let l = s.to_lowercase();
    l.contains("exited") || l.contains("failed") || l.contains("cannot") || l.contains("not found")
}

fn status_style(s: &str) -> Style {
    let color = if is_error(s) {
        Color::Red
    } else if s.starts_with("started") {
        Color::Green
    } else {
        Color::Yellow
    };
    Style::default().fg(color)
}

fn centered_rect(w: u16, h: u16, area: Rect) -> Rect {
    let w = w.min(area.width);
    let h = h.min(area.height);
    Rect {
        x: area.x + (area.width - w) / 2,
        y: area.y + (area.height - h) / 2,
        width: w,
        height: h,
    }
}

/// One line of the help popup: a section heading, or a shortcut.
enum Help {
    Section(&'static str),
    /// Alternative keys for the same action, and what they do.
    Key(&'static [&'static str], &'static str),
}

/// Alternative keys for the *same* action are joined with a dim "or". Related actions
/// (such as pinging one node vs. all nodes) get their own rows under a shared heading.
fn key_cell(keys: &[&str]) -> Cell<'static> {
    let mut spans: Vec<Span<'static>> = Vec::new();
    for (n, k) in keys.iter().enumerate() {
        if n > 0 {
            spans.push(Span::styled(" or ", dim()));
        }
        spans.push(Span::styled(
            k.to_string(),
            Style::default().fg(Color::Cyan).add_modifier(Modifier::BOLD),
        ));
    }
    Cell::from(Line::from(spans))
}

fn help_rows(items: &[Help]) -> u16 {
    let sections = items.iter().filter(|i| matches!(i, Help::Section(_))).count();
    (items.len() + sections.saturating_sub(1)) as u16
}

fn help_table(items: &[Help]) -> Table<'static> {
    let mut rows: Vec<Row<'static>> = Vec::new();
    for (n, item) in items.iter().enumerate() {
        match item {
            Help::Section(title) => {
                if n > 0 {
                    rows.push(Row::new(vec![Cell::from(""), Cell::from("")]));
                }
                rows.push(Row::new(vec![
                    Cell::from(*title)
                        .style(Style::default().fg(Color::Yellow).add_modifier(Modifier::BOLD)),
                    Cell::from(""),
                ]));
            }
            Help::Key(keys, desc) => {
                rows.push(Row::new(vec![key_cell(keys), Cell::from(*desc)]));
            }
        }
    }
    Table::new(rows, [Constraint::Length(11), Constraint::Min(20)]).column_spacing(2)
}

fn draw_help(f: &mut Frame) {
    let left = [
        Help::Section("Navigation"),
        Help::Key(&["↑", "k"], "Move up"),
        Help::Key(&["↓", "j"], "Move down"),
        Help::Key(&["PgUp"], "Up 10 rows"),
        Help::Key(&["PgDn"], "Down 10 rows"),
        Help::Key(&["g", "Home"], "Jump to first"),
        Help::Key(&["G", "End"], "Jump to last"),
        Help::Key(&["c"], "Jump to the connected node"),
        Help::Section("View"),
        Help::Key(&["s"], "Cycle sort order"),
        Help::Key(&["a"], "Hide / show timeouts"),
        Help::Key(&["/"], "Filter the list"),
        Help::Key(&["Esc"], "Clear the filter"),
        Help::Key(&["f"], "Field guide: what every field means"),
    ];
    let right = [
        Help::Section("Connection"),
        Help::Key(&["Enter"], "Connect to selected node"),
        Help::Key(&["m"], "Switch proxy URL / VPN (reconnects)"),
        Help::Key(&["x"], "Stop the connection"),
        Help::Key(&["e"], "Re-check the exit IP"),
        Help::Key(&["i"], "Toggle insecure TLS"),
        Help::Section("Ping"),
        Help::Key(&["t"], "Ping the selected node"),
        Help::Key(&["p"], "Ping all nodes"),
        Help::Key(&["T"], "Check exit IP / country of selected node"),
        Help::Key(&["P"], "Check exit IP / country of all nodes"),
        Help::Key(&["l"], "Live pinging on / off (every 5 min)"),
        Help::Section("App"),
        Help::Key(&["q"], "Quit, connection keeps running"),
        Help::Key(&["Q"], "Quit and stop the connection"),
        Help::Key(&["?"], "Show / close this help"),
    ];

    // Rows + 2 border + 2 vertical padding.
    let height = help_rows(&left).max(help_rows(&right)) + 4;
    let area = centered_rect(112, height, f.area());
    f.render_widget(Clear, area);

    let outer = block("Keyboard shortcuts")
        .title_bottom(" Esc or ? to close ")
        .padding(Padding::new(3, 3, 1, 1));
    let inner = outer.inner(area);
    f.render_widget(outer, area);

    let cols = Layout::horizontal([
        Constraint::Fill(1),
        Constraint::Length(4),
        Constraint::Fill(1),
    ])
    .split(inner);
    f.render_widget(help_table(&left), cols[0]);
    f.render_widget(help_table(&right), cols[2]);
}

/// One line of the field guide: a section heading (with a hint where to find it), or a
/// field and what it means.
enum Guide {
    Section(&'static str, &'static str),
    Field(&'static str, &'static str),
}

const GUIDE_LABEL_W: u16 = 13;

/// Greedy word wrap to `width` columns (always returns at least one line).
fn wrap_words(s: &str, width: usize) -> Vec<String> {
    let mut lines: Vec<String> = Vec::new();
    let mut cur = String::new();
    for w in s.split_whitespace() {
        if !cur.is_empty() && cur.chars().count() + 1 + w.chars().count() > width {
            lines.push(std::mem::take(&mut cur));
        }
        if !cur.is_empty() {
            cur.push(' ');
        }
        cur.push_str(w);
    }
    if !cur.is_empty() || lines.is_empty() {
        lines.push(cur);
    }
    lines
}

/// The guide as a table, with descriptions wrapped to `desc_w` columns, and its height in rows.
fn guide_table(items: &[Guide], desc_w: usize) -> (Table<'static>, u16) {
    let mut rows: Vec<Row<'static>> = Vec::new();
    let mut height: u16 = 0;
    for (n, item) in items.iter().enumerate() {
        match item {
            Guide::Section(title, hint) => {
                if n > 0 {
                    rows.push(Row::new(vec![Cell::from(""), Cell::from("")]));
                    height += 1;
                }
                rows.push(Row::new(vec![
                    Cell::from(*title)
                        .style(Style::default().fg(Color::Yellow).add_modifier(Modifier::BOLD)),
                    Cell::from(*hint).style(dim()),
                ]));
                height += 1;
            }
            Guide::Field(name, desc) => {
                let lines = wrap_words(desc, desc_w);
                let h = lines.len() as u16;
                rows.push(
                    Row::new(vec![
                        Cell::from(*name)
                            .style(Style::default().fg(Color::Cyan).add_modifier(Modifier::BOLD)),
                        Cell::from(Text::from(lines.join("\n"))),
                    ])
                    .height(h),
                );
                height += h;
            }
        }
    }
    let table = Table::new(rows, [Constraint::Length(GUIDE_LABEL_W), Constraint::Min(10)])
        .column_spacing(1);
    (table, height)
}

fn draw_guide(f: &mut Frame) {
    let left = [
        Guide::Section("Servers", "the table: one column each"),
        Guide::Field("●", "The node you are connected to. It always stays in the list, whatever the filter says."),
        Guide::Field("#", "Position in your file. It does not change when you sort or filter. A - marks the still-connected node of an earlier file."),
        Guide::Field("Country", "Country named in the node's own label (flag or 2-letter code). Providers sometimes get it wrong."),
        Guide::Field("Exit", "Country where traffic really leaves (exit IP check, T or P). Blank until checked. Yellow: differs from Country. Red: unavailable."),
        Guide::Field("Type", "VMESS, VLESS, TROJAN or SS (Shadowsocks)."),
        Guide::Field("Address", "Host name or IP of the server v2tui connects to."),
        Guide::Field("Port", "Server port."),
        Guide::Field("Net", "Transport: tcp, ws (WebSocket), grpc and so on."),
        Guide::Field("Sec", "Security layer: tls, reality or none. SS shows - because it has its own cipher."),
        Guide::Field("Ping", "TCP connect time to the server, not a speed test. Green under 120 ms, yellow under 300, red above."),
        Guide::Field("Name", "The node's label from your file, without the flag emoji."),
    ];
    let right = [
        Guide::Section("Selected node", "the box under the table, left"),
        Guide::Field("Country", "Country named in the node's label."),
        Guide::Field("Protocol", "VMESS, VLESS, TROJAN or SS."),
        Guide::Field("Server", "Address and port that v2tui connects to."),
        Guide::Field("Transport", "Network type / security layer, for example ws / tls."),
        Guide::Field("SNI", "Server name sent in the TLS handshake. - means none was set."),
        Guide::Field("TCP ping", "Time to open a TCP connection to the server (t or p)."),
        Guide::Field("Exit IP", "Public IP and country seen through this node (T or P). (≠ listed) means it differs from Country. Red: unavailable."),
        Guide::Field("Name", "The node's label from your file."),
        Guide::Section("Connection", "the box under the table, right"),
        Guide::Field("Status", "Whether a connection is running."),
        Guide::Field("Node", "Country, host and protocol of the node in use."),
        Guide::Field("Mode", "Proxy URL: local SOCKS5/HTTP ports for your apps. System VPN: all traffic goes through the node, no proxy URL."),
        Guide::Field("SOCKS5 URL", "Local SOCKS5 proxy for your apps (proxy mode)."),
        Guide::Field("HTTP URL", "Local HTTP proxy for your apps (proxy mode)."),
        Guide::Field("Interface", "Name of the TUN network device (VPN mode)."),
        Guide::Field("Exit IP", "Public IP and country of the connection, as last checked (e). Red: unavailable."),
    ];

    let width = 128u16.min(f.area().width);
    // Borders 2 + padding 2*2, then two columns with a gap of 4.
    let col_w = (width.saturating_sub(6 + 4) / 2) as usize;
    let desc_w = col_w.saturating_sub(GUIDE_LABEL_W as usize + 1).max(10);
    let (lt, lh) = guide_table(&left, desc_w);
    let (rt, rh) = guide_table(&right, desc_w);

    // Rows + 2 border + 2 vertical padding.
    let area = centered_rect(width, lh.max(rh) + 4, f.area());
    f.render_widget(Clear, area);

    let outer = block("Field guide")
        .title_bottom(" Esc or f to close ")
        .padding(Padding::new(2, 2, 1, 1));
    let inner = outer.inner(area);
    f.render_widget(outer, area);

    let cols = Layout::horizontal([
        Constraint::Fill(1),
        Constraint::Length(4),
        Constraint::Fill(1),
    ])
    .split(inner);
    f.render_widget(lt, cols[0]);
    f.render_widget(rt, cols[2]);
}

fn draw_footer(f: &mut Frame, app: &App, area: Rect) {
    let line = if app.filtering {
        Line::from(vec![
            Span::styled(" filter: ", Style::default().fg(Color::Yellow)),
            Span::raw(app.filter.clone()),
            Span::styled("█", Style::default().fg(Color::Yellow)),
            Span::styled("   (Enter/Esc to finish)", dim()),
        ])
    } else {
        let keys = [("↑↓", "move"), ("Enter", "connect"), ("f", "field guide"), ("?", "help")];
        let mut spans = vec![Span::raw(" ")];
        for (k, d) in keys {
            spans.push(Span::styled(
                k,
                Style::default().fg(Color::Cyan).add_modifier(Modifier::BOLD),
            ));
            spans.push(Span::styled(format!(" {d}  "), dim()));
        }
        if !app.filter.is_empty() {
            spans.push(Span::styled(
                format!("[filter: {}]", app.filter),
                Style::default().fg(Color::Yellow),
            ));
        }
        Line::from(spans)
    };
    f.render_widget(Paragraph::new(line), area);
}

// ───────────────────────────── main ─────────────────────────────

fn run(term: &mut DefaultTerminal, app: &mut App) -> io::Result<()> {
    while !app.quit {
        app.tick();
        term.draw(|f| ui(f, app))?;
        if event::poll(Duration::from_millis(100))? {
            if let CEvent::Key(k) = event::read()? {
                if k.kind == KeyEventKind::Press {
                    if app.too_small {
                        // The UI is hidden, so only allow quitting (no blind connects).
                        let ctrl_c = k.modifiers.contains(KeyModifiers::CONTROL)
                            && k.code == KeyCode::Char('c');
                        if ctrl_c || k.code == KeyCode::Char('q') {
                            app.quit = true;
                        }
                    } else {
                        app.on_key(k);
                        if app.force_redraw {
                            term.clear()?; // the terminal was lent to sudo; repaint fully
                            app.force_redraw = false;
                        }
                    }
                }
            }
        }
    }
    app.save_state();
    Ok(())
}

fn print_help() {
    println!(
        "v2tui {version}
Terminal UI to browse, ping and connect to V2Ray/Xray subscription links

USAGE:
    v2tui <FILE>
    v2tui -h | --help

ARGS:
    <FILE>    Text file with one link per line (vmess://, vless://, trojan://, ss://),
              or a base64-encoded subscription file

OPTIONS:
    -h, --help    Print this help message

REQUIREMENTS:
    xray must be installed and in your PATH. System VPN mode also needs sudo.
    A terminal of at least {w}x{h} columns x rows.

CONNECTION MODES (press m in the TUI to switch):
    proxy URL     SOCKS5 127.0.0.1:{socks} and HTTP 127.0.0.1:{http} for your apps
    system VPN    all traffic goes through the node (TUN device {tun})

FILES:
    Everything is kept in $XDG_CACHE_HOME/v2tui (default ~/.cache/v2tui):
      state.json          settings and the running connection (shared by every file)
      cache.json          pings, exit IPs and cursor per subscription file, by content hash
      v2tui-config.json   config of the running core
      v2tui-core.log      output of the core

Press ? inside v2tui for the keyboard shortcuts, f for a guide to every field.",
        version = env!("CARGO_PKG_VERSION"),
        w = MIN_W,
        h = MIN_H,
        socks = SOCKS_PORT,
        http = HTTP_PORT,
        tun = TUN_NAME,
    );
}

fn main() -> io::Result<()> {
    if std::env::args().skip(1).any(|a| a == "-h" || a == "--help") {
        print_help();
        return Ok(());
    }
    let Some(path) = std::env::args().nth(1) else {
        eprintln!("usage: v2tui <configs.txt>   (decoded links, or a base64 subscription file)");
        eprintln!("try 'v2tui -h' for more information");
        std::process::exit(2);
    };
    let text = fs::read_to_string(&path).map_err(|e| {
        eprintln!("cannot read {path}: {e}");
        e
    })?;
    let nodes = load_nodes(&text);
    if nodes.is_empty() {
        eprintln!("no supported links (vmess/vless/trojan/ss) found in {path}");
        std::process::exit(1);
    }
    let file_hash = content_hash(&nodes);
    let file_path = fs::canonicalize(&path)
        .map(|p| p.display().to_string())
        .unwrap_or_else(|_| path.clone());
    let mut app = App::new(nodes, file_hash, file_path);
    let mut terminal = ratatui::init();
    let res = run(&mut terminal, &mut app);
    app.probes.kill_all(); // never leave exit-check xray processes behind
    ratatui::restore();
    if let Some(a) = &app.active {
        let n = &app.nodes[a.node];
        println!(
            "v2tui: connection still running -> {} {} (pid {}), SOCKS5 127.0.0.1:{SOCKS_PORT}, HTTP 127.0.0.1:{HTTP_PORT}",
            n.country, n.host, a.pid
        );
        println!("       run v2tui again to manage it, press Q inside to quit and stop it, or: kill {}", a.pid);
    }
    res
}
