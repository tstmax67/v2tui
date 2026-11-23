# v2tui

A fast, lightweight Terminal UI (TUI) for Linux to browse, ping, verify, and connect to V2Ray/Xray subscription links.

Built in Rust with [`ratatui`](https://github.com/ratatui/ratatui), `v2tui` manages `xray` processes cleanly in the background—allowing you to close the TUI while keeping your proxy or system-wide VPN active.

---

## Features

- **Protocol Support:** Parses `vmess://`, `vless://`, `trojan://`, and `ss://` (Shadowsocks) links, as well as raw base64-encoded subscription files.
- **Two Connection Modes (`m`):**
  - **Proxy URL Mode:** Exposes local `SOCKS5` (`127.0.0.1:10808`) and `HTTP` (`127.0.0.1:10809`) endpoints for your browser or terminal apps.
  - **System VPN Mode:** Creates a TUN interface (`v2tui0`) and routes all system traffic through the selected node via `xray` (uses `sudo`).
- **Background Persistence:** Quitting with `q` leaves `xray` running in its own process group. Re-opening `v2tui` automatically re-attaches to the running session.
- **Latency & Exit-IP Verification:**
  - Fast concurrent TCP pings (`t` for one, `p` for all, or `l` for automatic 5-minute live pinging).
  - Real exit-IP & geolocation probing (`T` for one, `P` for all, `e` for active connection) to detect when a node's actual exit country differs from its label.
- **Smart Filtering & Sorting:** Filter live by country, exit location, protocol, host, port, transport, or node name (`/`), hide dead nodes (`a`), and cycle sort orders (`s`).
- **Built-in Field Guide:** Press `f` anytime inside the app for an explanation of every column and status field.

---

## Requirements

- **OS:** Linux (relies on `/proc` for process tracking and Linux TUN interfaces for VPN mode).
- **Core:** [`xray`](https://github.com/XTLS/Xray-core) installed and available in your `$PATH`.
- **Privileges:** `sudo` access (only required if using System VPN mode).
- **Terminal Size:** Minimum **130 columns × 32 rows**.

---

## Installation

### Build from Source

Make sure you have the Rust toolchain (`cargo`) installed:

```bash
git clone https://github.com/yourusername/v2tui.git
cd v2tui
cargo build --release
```

The optimized binary will be created at `target/release/v2tui`. You can copy it to a directory in your `$PATH`:

```bash
sudo cp target/release/v2tui /usr/local/bin/
```

---

## Usage

Pass a text file containing one proxy link per line, or a raw base64-encoded subscription file:

```bash
v2tui /path/to/nodes.txt
```

To view CLI flags and defaults:

```bash
v2tui --help
```

### Example Input File (`nodes.txt`)

```text
# Lines starting with # are ignored
vless://uuid@example.com:443?security=reality&sni=www.example.com&fp=chrome&pbk=...&sid=...#🇩🇪 Germany-01
vmess://eyJhZGQiOi...
trojan://password@example.org:443#🇯🇵 Japan-02
ss://YWVzLTI1Ni1nY206cGFzc3dvcmQ=@192.0.2.1:8388#🇺🇸 US-03
```

---

## Keyboard Shortcuts

### Navigation & View
| Key | Action |
| :--- | :--- |
| `↑` / `k`, `↓` / `j` | Move selection up / down |
| `PgUp` / `PgDn` | Scroll up / down 10 rows |
| `g` / `Home`, `G` / `End` | Jump to first / last node |
| `c` | Jump to the currently connected node |
| `/` | Filter nodes (by country, exit, protocol, address, port, net, or name) |
| `Esc` | Clear active filter |
| `s` | Cycle sort order (`file order` → `ping` → `country` → `type`) |
| `a` | Toggle hiding timed-out nodes |
| `f` | Open the **Field Guide** (explains every column and detail box) |
| `?` | Open / close keyboard shortcuts help |

### Connection & Testing
| Key | Action |
| :--- | :--- |
| `Enter` | Connect to selected node |
| `m` | Toggle **Proxy URL** / **System VPN** mode (reconnects if active) |
| `x` | Disconnect active connection |
| `t` / `p` | TCP ping selected node / all nodes |
| `l` | Toggle live pinging (automatically re-pings all nodes every 5 minutes) |
| `T` / `P` | Probe real Exit IP & country of selected node / all nodes |
| `e` | Re-check Exit IP of the active connection |
| `i` | Toggle `allowInsecure` for TLS connections (applies on next connect) |

### Application
| Key | Action |
| :--- | :--- |
| `q` | Quit TUI (**keeps** the active connection running in the background) |
| `Q` | Quit TUI and **stop** the active connection |

---

## Cache & Logs

`v2tui` stores its runtime state, generated Xray configuration, and logs in `$XDG_CACHE_HOME/v2tui` (defaults to `~/.cache/v2tui`):

- `state.json` — Cached ping results, exit IPs, UI preferences, and active PID tracking.
- `v2tui-config.json` — Generated Xray configuration for the active session (`0600` permissions).
- `v2tui-core.log` — Standard output and error logs from `xray` (useful if a connection fails to start).

---

## License

See the [LICENSE](LICENSE) file in this repository for details.