# Local AI Stack — Single Path Setup (Windows)

This guide restores the original, simple setup:

- Tool server on port 8000 via `python my_assistant_tools.py`
- LiteLLM Vertex proxy on port 4001 (container name: `litellm-vertex`)
- Open WebUI configured to use both

Keep to this one configuration unless you intentionally change it.

## Prerequisites

- Windows with PowerShell
- Python 3.11+ available as `python`
- Docker Desktop running
- Files located at:
  - Tool server: `C:\\Users\\Moses\\api_setup\\my_assistant_tools.py`
  - LiteLLM config: `C:\\Users\\Moses\\api_setup\\config.yaml`

## 1) Start the tool server on port 8000

Run in a PowerShell terminal:

```powershell
# (Optional) free the port if in use
netstat -ano | findstr :8000 | ForEach-Object {
  $pid = ($_ -split '\s+')[-1]; if ($pid -match '^\d+$') { Stop-Process -Id $pid -Force -ErrorAction SilentlyContinue }
}

# Start the original Flask dev server on 8000
$env:PYTHONUNBUFFERED = "1"
python C:\\Users\\Moses\\api_setup\\my_assistant_tools.py
```


- The dev server warning is expected and safe for local use.
- Keep this terminal open while using the tools.

Health checks (new terminal):

```powershell
Invoke-WebRequest -Uri "http://localhost:8000/health" -UseBasicParsing
Invoke-WebRequest -Uri "http://localhost:8000/openapi.json" -UseBasicParsing
```

## 2) Start the LiteLLM Vertex proxy on port 4001

If the containers already exist from your previous setup:

```powershell
docker start litellm-db
docker start litellm-vertex
```

Verify:

```powershell
docker ps --format "table {{.Names}}\t{{.Ports}}\t{{.Status}}"
```

If `docker start` fails because the containers were removed, recreate using your existing image and `config.yaml`, or ask me for a one-liner based on your environment.

## 3) Configure Open WebUI (single path)

Do this inside Open WebUI (port 3000).

- Tools → Manage Tool Servers → Edit/Add
  - URL: `http://host.docker.internal:8000`
  - Toggle “This is a Base URL”: ON (WebUI will fetch `/openapi.json`)
  - Auth: None (or Session; the server ignores it)
  - Name: `Moses Local Tools`
  - Save → Test (expect OK)

- Settings → Web Search
  - Web Search Engine: `external`
  - External Web Search URL: `http://host.docker.internal:8000/webui/search`
  - External Web Search API Key: `abc-123` (server accepts/ignores)
  - Search Result Count: set as you like (e.g., 3)

- Providers (LLM)
  - Type: `OpenAI`
  - Base URL: `http://host.docker.internal:4001/v1`
  - API Key: any non-empty string (e.g., `vertex-proxy`)
  - Model: select the LiteLLM route you use (as configured in `config.yaml`)

## 4) Quick end-to-end test

- Open WebUI → Tools → click Test for `Moses Local Tools` → should list endpoints.
- Start a new chat, enable the tool (puzzle icon), and run a query that uses web search.
- If using the LiteLLM provider, open the model list; it should show your routed models.

## 5) Troubleshooting (fast)

- Tool server not reachable:
  - Ensure it’s running on 8000 in a terminal.
  - From Open WebUI (Docker), always use `http://host.docker.internal:8000` (not `localhost`).
  - Windows Firewall: allow inbound TCP 8000 if prompted.

- `GET /models 404` in tool server logs:
  - The tool server URL was accidentally added as an LLM Provider. Keep it only under Tools and/or external Web Search.

- LiteLLM proxy unreachable:
  - Check container is running: `docker ps`
  - From host: `curl http://localhost:4001/v1/models`

## 6) Stop/Start cheat sheet (Docker + host)

Use these exact names from Docker Desktop (see your screenshot) and PowerShell-friendly commands:

Stop individual containers (safe):

```powershell
# Open WebUI container
docker stop open-webui-fresh

# LiteLLM Postgres DB
docker stop litellm-db

# LiteLLM Vertex proxy (if present in your setup)
docker stop litellm-vertex

# Filesystem MCP demo container (shows as group "filesystem" with child "server-1")
docker stop server-1

# Any extra stack container shown in Docker Desktop (e.g., operatorkernelo6)
docker stop operatorkernelo6
```

Stop everything that is currently running (bulk):

```powershell
docker ps -q | ForEach-Object { docker stop $_ }
```

Remove a stopped container (optional cleanup):

```powershell
docker rm <container-name>
```

Free port 8000 on Windows (safe; only kills listeners, not your shell):

List who is listening on 8000 first:

```powershell
Get-NetTCPConnection -LocalPort 8000 -State Listen -ErrorAction SilentlyContinue |
  Select-Object LocalAddress, LocalPort, OwningProcess,
    @{ Name = 'ProcessName'; Expression = { (Get-Process -Id $_.OwningProcess -ErrorAction SilentlyContinue).ProcessName } }
```

If that looks right, stop only the listener PIDs (skips your current PowerShell):

```powershell
$port = 8000
$listenerPids = Get-NetTCPConnection -LocalPort $port -State Listen -ErrorAction SilentlyContinue |
  Select-Object -ExpandProperty OwningProcess -Unique

foreach ($pid in $listenerPids) {
  if ($pid -and $pid -ne $PID) {
    try {
      $proc = Get-Process -Id $pid -ErrorAction Stop
      Write-Host "Stopping $($proc.ProcessName) (PID $pid) listening on $port"
      Stop-Process -Id $pid -Force -ErrorAction Stop
    } catch {
      Write-Host ("Skip PID {0}: {1}" -f $pid, $_)
    }
  }
}
```

Fallback if Get-NetTCPConnection isn’t available: stop the container bound to 8000 (if running):

```powershell
docker stop server-1
```

Stop the Python tool server started in a terminal:

```powershell
# In the same terminal where it's running, press Ctrl+C
# Or, if detached, use the 8000 port-freeing snippet above
```

Important: The Filesystem MCP container (`server-1`) and the Python tool server both use host port 8000. Run only one at a time. If you want to use the original `python my_assistant_tools.py`, first stop `server-1`.

## 7) Architecture overview (how pieces connect)

The diagram below shows the single-path setup used in this guide. Open WebUI talks to two things: your local tool server on port 8000 and the LiteLLM Vertex proxy on port 4001. The tool server performs web searches and helper tasks; LiteLLM forwards model calls to Vertex AI.

```mermaid
flowchart TD
  user[You in Open WebUI] --> webui[Open WebUI\n(container: open-webui-fresh)\nHost 3001 → Ctnr 8080]

  subgraph Port8000[Port 8000 (choose one)]
    tools[Local Tool Server\n(python my_assistant_tools.py)\nHost 8000]
    fsMCP[Filesystem MCP\n(container: server-1)\nHost 8000 → Ctnr 8000]
  end

  litellm[LiteLLM Vertex Proxy\n(container: litellm-vertex)\nHost 4001 → Ctnr 4001]
  db[(Postgres\n(container: litellm-db))]
  vertex[(Google Vertex AI APIs)]
  web[(External Web Sites)]
  hostfs[(Host Filesystem C:\\Users\\Moses\\…)]

  webui -- Tools Base URL → tools
  tools -- Web Search → web
  webui -- OpenAI Provider Base URL → litellm
  litellm --> db
  litellm --> vertex

  %% Optional alternative: if you run the Filesystem MCP demo instead of the Python tools
  webui -. alternative tools .-> fsMCP
  fsMCP -. reads/writes .- hostfs

  classDef container fill:#e6f3ff,stroke:#0a66c2,stroke-width:1px;
  classDef external fill:#fff5d6,stroke:#d99000,stroke-width:1px;
  classDef db fill:#e9fbe9,stroke:#198754,stroke-width:1px;

  class webui,tools,fsMCP,litellm container;
  class vertex,web external;
  class db db;
```

Source file for the diagram (editable): `docs/diagrams/local_stack_overview.mmd`.

## 8) Notes

- The `servers` URL in `/openapi.json` is informational. Open WebUI will call the Base URL you set (port 8000).
- Avoid switching ports; this guide standardizes on 8000 (tools) and 4001 (LiteLLM).

---

Last verified: 2025-08-25
