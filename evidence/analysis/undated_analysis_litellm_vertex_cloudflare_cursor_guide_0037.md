# End-to-End Guide: LiteLLM ↔ Vertex AI (Claude + Gemini) ↔ Cloud Tunnel ↔ Cursor (Windows)

This is a zero-assumptions, copy-paste guide to get a local LiteLLM proxy talking to Google Vertex AI (Anthropic Claude + Gemini), publish it via a public tunnel, and wire Cursor to use it. Every step uses Windows PowerShell commands you can paste as-is.

If something fails, check the Troubleshooting section near the end. Follow the order exactly.


## What you’ll build

- A local LiteLLM server at http://localhost:4000/v1 that exposes OpenAI-compatible APIs and routes calls to Vertex AI models (Claude Opus/Sonnet and Gemini 2.5).
- An optional public HTTPS URL via Cloudflare (or ngrok) so Cursor’s cloud features (Agent/Edit) can reach your local server.
- Cursor configured to use your proxy.


## Quick glossary (plain English)

- Project: Your Google Cloud project (e.g., gen-lang-client-0376912995). All resources, quotas, and permissions live here.
- Service account (SA): A robot identity used by servers/CLIs. Has an email and optional key JSON.
- ADC (Application Default Credentials): The standard way Google clients find credentials (either a user login or a service account JSON) for API calls.
- Vertex AI User role: Grants the model prediction permission your proxy needs (includes aiplatform.endpoints.predict).
- Model Garden “Enable”: A one-time click per project/region to accept terms and allow Anthropic (Claude) models.


## Prerequisites

- Windows 10/11 with PowerShell (v5+).
- Google Cloud SDK (gcloud) installed and on PATH.
- Python 3.10+ with pip; LiteLLM installed (pip install litellm).
- curl.exe available (Windows 10/11 ships with it). We’ll call curl.exe explicitly to avoid PowerShell alias issues.

Optional but recommended:
- Cloudflare’s cloudflared (for free quick tunnel) or ngrok (account required for stable URLs).


## Part 0 — Set variables for this session

Paste this first. If your project or key path differ, edit only the quoted values on the right side.

```powershell
# === Session variables (edit if different) ===
$PROJ = "gen-lang-client-0376912995"           # Your Google Cloud project id
$KEY  = "C:\Users\Moses\.gcp\keys\gen-lang-client-0376912995-961cd086a470.json"  # Service account JSON path
$CFG  = "C:\Users\Moses\litellm-config\config.yaml"  # Where we’ll write the LiteLLM config

# Make sure the folder for the config exists
New-Item -ItemType Directory -Force -Path (Split-Path $CFG) | Out-Null
```


## Part 1 — Google Cloud: auth, APIs, and roles

We’ll log in, set the active project, enable required APIs, and ensure the caller can make predictions.

```powershell
# 1. Login (opens browser). Also writes/refreshes ADC for libraries.
gcloud auth login --update-adc

# 2. Select the target project for CLI operations
gcloud config set project $PROJ

# 3. Enable Vertex AI API (safe to re-run)
gcloud services enable aiplatform.googleapis.com --project=$PROJ

# 4. Extract the service account email from your JSON key
$SA = (Get-Content $KEY -Raw | ConvertFrom-Json).client_email
$SA

# 5. Grant the Vertex AI User role (includes prediction permission)
gcloud projects add-iam-policy-binding $PROJ `
  --member="serviceAccount:$SA" `
  --role="roles/aiplatform.user"
```

### Required one-time console step (Model Garden → “Enable”)

- In the Google Cloud Console, switch to project $PROJ (top blue bar).
- Go to Vertex AI → Model Garden → search “Claude Opus 4.1” (Anthropic) → open the card → click Enable.
- Optional: repeat for “Claude Sonnet 4”.

Notes:
- Anthropic on Vertex is available in region us-east5 and requires versioned model IDs like claude-opus-4-1@20250805.
- Some organizations require enabling marketplace/agreements APIs or extra roles to click Enable. If the Enable button is blocked or grayed out, ask a project owner to help.


## Part 2 — ADC and quota project

Your running LiteLLM process needs ADC (either user login or the service account JSON). We’ll use the service account JSON via env var, and align the quota project for clean billing/quota behavior.

```powershell
# 1) Tell Google libraries to use your service account JSON at runtime
$env:GOOGLE_APPLICATION_CREDENTIALS = $KEY

# 2) Set the quota project in the ADC file to avoid warnings
# (If prompted to re-login, first run: gcloud auth application-default login)
gcloud auth application-default set-quota-project $PROJ

# 3) Optional: verify the quota project set in the ADC file
$ADC = "$env:APPDATA\gcloud\application_default_credentials.json"
if (Test-Path $ADC) { (Get-Content $ADC -Raw | ConvertFrom-Json).quota_project_id } else { "ADC file not found: $ADC" }
```

Tip: “gcloud auth login” is for the CLI; “application-default” commands affect the JSON that libraries (like LiteLLM’s provider code) use.


## Part 3 — Write LiteLLM config.yaml (clean, ASCII-only)

We’ll write a minimal, working config with:
- Anthropic Claude Opus/Sonnet on Vertex (region us-east5, versioned IDs).
- Gemini 2.5 (pro/flash) on Vertex.
- Two aliases: gpt-5 (routes to Opus) and gpt-5-low (routes to Gemini flash).
- Parameter dropping enabled (to prevent UIs from sending unsupported fields).
- For Anthropic on Vertex: set anthropic-version as an HTTP header, not as request body.

Option A — direct write via PowerShell here-string (works in most shells):

```powershell
$cfgText = @"
model_list:
  # ---- Anthropic on Vertex (must use us-east5 and versioned IDs) ----
  - model_name: "claude-opus-4.1"
    litellm_params:
      model: "vertex_ai/claude-opus-4-1@20250805"
      vertex_project: "$PROJ"
      vertex_location: "us-east5"
      extra_headers:
        anthropic-version: "vertex-2023-10-16"

  - model_name: "claude-sonnet-4"
    litellm_params:
      model: "vertex_ai/claude-sonnet-4@20250514"
      vertex_project: "$PROJ"
      vertex_location: "us-east5"
      extra_headers:
        anthropic-version: "vertex-2023-10-16"

  # ---- Google Gemini on Vertex (uniformly use us-east5) ----
  - model_name: "gemini-2.5-pro"
    litellm_params:
      model: "vertex_ai/gemini-2.5-pro"
      vertex_project: "$PROJ"
      vertex_location: "us-east5"

  - model_name: "gemini-2.5-flash"
    litellm_params:
      model: "vertex_ai/gemini-2.5-flash"
      vertex_project: "$PROJ"
      vertex_location: "us-east5"

  # ---- Cursor’s “Auto → gpt-5*” trap, map to real models ----
  - model_name: "gpt-5"
    litellm_params:
      model: "vertex_ai/claude-opus-4-1@20250805"
      vertex_project: "$PROJ"
      vertex_location: "us-east5"
      extra_headers:
        anthropic-version: "vertex-2023-10-16"

  - model_name: "gpt-5-low"
    litellm_params:
      model: "vertex_ai/gemini-2.5-flash"
      vertex_project: "$PROJ"
      vertex_location: "us-east5"

  # ---- Optional: convenience aliases some UIs expect ----
  - model_name: "gemini-2.5-pro-max"
    litellm_params:
      model: "vertex_ai/gemini-2.5-pro"
      vertex_project: "$PROJ"
      vertex_location: "us-east5"
      max_tokens: 4096
      temperature: 0.7
      top_p: 0.9

  - model_name: "gemini-2.5-pro-max-context"
    litellm_params:
      model: "vertex_ai/gemini-2.5-pro"
      vertex_project: "$PROJ"
      vertex_location: "us-east5"
      max_tokens: 8192
      temperature: 0.5
      top_p: 0.9

litellm_settings:
  drop_params: true
"@
Set-Content -Path $CFG -Value $cfgText -Encoding ASCII
```

Option B — if your PowerShell has paste bugs (PSReadLine exceptions), write via Base64 (pre-encoded for the minimal set; edit the project id after writing if needed):

```powershell
$cfgB64 = @"
bW9kZWxfbGlzdDoKICAtIG1vZGVsX25hbWU6ICJjbGF1ZGUtb3B1cy00LjEiCiAgICBsaXRlbGxtX3BhcmFtczoKICAgICAgbW9kZWw6ICJ2ZXJ0ZXhfYWkvY2xhdWRlLW9wdXMtNC0xQDIwMjUwODA1IgogICAgICB2ZXJ0ZXhfcHJvamVjdDogImdlbi1sYW5nLWNsaWVudC0wMzc2OTEyOTk1IgogICAgICB2ZXJ0ZXhfbG9jYXRpb246ICJ1cy1lYXN0NSIKICAgICAgZXh0cmFfaGVhZGVyczoKICAgICAgICBhbnRocm9waWMtdmVyc2lvbjogInZlcnRleC0yMDIzLTEwLTE2IgoKICAtIG1vZGVsX25hbWU6ICJjbGF1ZGUtc29ubmV0LTQiCiAgICBsaXRlbGxtX3BhcmFtczoKICAgICAgbW9kZWw6ICJ2ZXJ0ZXhfYWkvY2xhdWRlLXNvbm5ldC00QDIwMjUwNTE0IgogICAgICB2ZXJ0ZXhfcHJvamVjdDogImdlbi1sYW5nLWNsaWVudC0wMzc2OTEyOTk1IgogICAgICB2ZXJ0ZXhfbG9jYXRpb246ICJ1cy1lYXN0NSIKICAgICAgZXh0cmFfaGVhZGVyczoKICAgICAgICBhbnRocm9waWMtdmVyc2lvbjogInZlcnRleC0yMDIzLTEwLTE2IgoKICAtIG1vZGVsX25hbWU6ICJnZW1pbmktMi41LXBybyIKICAgIGxpdGVsbG1fcGFyYW1zOgogICAgICBtb2RlbDogInZlcnRleF9haS9nZW1pbmktMi41LXBybyIKICAgICAgdmVydGV4X3Byb2plY3Q6ICJnZW4tbGFuZy1jbGllbnQtMDM3NjkxMjk5NSIKICAgICAgdmVydGV4X2xvY2F0aW9uOiAidXMtZWFzdDUiCgogIC0gbW9kZWxfbmFtZTogImdlbWluaS0yLjUtZmxhc2giCiAgICBsaXRlbGxtX3BhcmFtczoKICAgICAgbW9kZWw6ICJ2ZXJ0ZXhfYWkvZ2VtaW5pLTIuNS1mbGFzaCIKICAgICAgdmVydGV4X3Byb2plY3Q6ICJnZW4tbGFuZy1jbGllbnQtMDM3NjkxMjk5NSIKICAgICAgdmVydGV4X2xvY2F0aW9uOiAidXMtZWFzdDUiCgogIC0gbW9kZWxfbmFtZTogImdwdC01IgogICAgbGl0ZWxsbV9wYXJhbXM6CiAgICAgIG1vZGVsOiAidmVydGV4X2FpL2NsYXVkZS1vcHVzLTQtMUAyMDI1MDgwNSIKICAgICAgdmVydGV4X3Byb2plY3Q6ICJnZW4tbGFuZy1jbGllbnQtMDM3NjkxMjk5NSIKICAgICAgdmVydGV4X2xvY2F0aW9uOiAidXMtZWFzdDUiCiAgICAgIGV4dHJhX2hlYWRlcnM6CiAgICAgICAgYW50aHJvcGljLXZlcnNpb246ICJ2ZXJ0ZXgtMjAyMy0xMC0xNiIKCiAgLSBtb2RlbF9uYW1lOiAiZ3B0LTUtbG93IgogICAgbGl0ZWxsbV9wYXJhbXM6CiAgICAgIG1vZGVsOiAidmVydGV4X2FpL2dlbWluaS0yLjUtZmxhc2giCiAgICAgIHZlcnRleF9wcm9qZWN0OiAiZ2VuLWxhbmctY2xpZW50LTAzNzY5MTI5OTUiCiAgICAgIHZlcnRleF9sb2NhdGlvbjogInVzLWVhc3Q1IgoKbGl0ZWxsbV9zZXR0aW5nczoKICBkcm9wX3BhcmFtczogdHJ1ZQ==
"@
[IO.Directory]::CreateDirectory((Split-Path $CFG)) | Out-Null
[IO.File]::WriteAllBytes($CFG, [Convert]::FromBase64String(($cfgB64 -replace '\s','')))
```

Important:
- Do not include “thinking” blocks for Anthropic on Vertex in your config. Vertex rejects extra fields with 400/“extra_body: Extra inputs are not permitted”.
- Keep anthropic-version in headers for Anthropic calls.


## Part 4 — Start LiteLLM

```powershell
# Ensure this shell uses your service account JSON for ADC
$env:GOOGLE_APPLICATION_CREDENTIALS = $KEY

# Start LiteLLM (keep this window open)
litellm --config $CFG --port 4000 --host 0.0.0.0
```

You should see a startup banner and a list of models (claude-opus-4.1, gemini-2.5-pro, etc.).


## Part 5 — Local smoke tests

Use curl.exe (not PowerShell’s curl alias) or pure PowerShell.

```powershell
# List models
curl.exe -s http://localhost:4000/v1/models -H "Authorization: Bearer sk-local-test"

# Simple chat (curl.exe with JSON file to avoid quoting problems)
$json = @{ model = "claude-opus-4.1"; messages = @(@{ role = "user"; content = "Say OK" }) } | ConvertTo-Json -Depth 5
$req = "$env:TEMP\req.json"; Set-Content $req $json -Encoding ASCII

curl.exe -sS -X POST http://localhost:4000/v1/chat/completions `
  -H "Content-Type: application/json" `
  -H "Authorization: Bearer sk-local-test" `
  --data-binary "@$req"
```

Pure PowerShell version:

```powershell
$headers = @{ Authorization = "Bearer sk-local-test"; "Content-Type" = "application/json" }
$body    = @{ model = "claude-opus-4.1"; messages = @(@{ role = "user"; content = "Say OK" }) } | ConvertTo-Json -Depth 5
$r = Invoke-RestMethod -Uri "http://localhost:4000/v1/chat/completions" -Method Post -Headers $headers -Body $body -ContentType "application/json"
$r.choices[0].message.content
```

If you get a JSON response or the string “OK,” your proxy is working.


## Part 6 — Public tunnel (so Cursor Agent/Edit can reach you)

Cursor’s cloud features can’t reach http://localhost. Use a public HTTPS tunnel.

### Option A — Cloudflare (quick tunnel, no account required)

```powershell
# Install cloudflared
winget install --id Cloudflare.cloudflared -s winget

# If the command isn’t found, use the full path (adjust if needed):
&"C:\Program Files\Cloudflare\cloudflared\cloudflared.exe" --version

# Start a quick tunnel to your local server (HTTP/2 + IPv4 for stability)
&"C:\Program Files\Cloudflare\cloudflared\cloudflared.exe" tunnel --protocol http2 --edge-ip-version 4 --url http://localhost:4000
```

- The console will print a URL like: https://something.trycloudflare.com
- Your public base URL for clients is: https://something.trycloudflare.com/v1

Test via the tunnel from another PowerShell:

```powershell
$PUBLIC = "https://paste-your-trycloudflare-url-here"  # no /v1 at the end in this var
curl.exe -s "$PUBLIC/v1/models" -H "Authorization: Bearer sk-public-test"
```

Tip: The first request after a tunnel starts might 524 timeout. Retry once or twice.

### Option B — ngrok (requires account/token)

```powershell
winget install Ngrok.Ngrok
ngrok config add-authtoken YOUR_NGROK_TOKEN
ngrok http 4000
```

- Use the printed https://xxxxx.ngrok.app URL.


## Part 7 — Cursor setup

1) Open Cursor → Settings (gear) → Models.
2) OpenAI API Key: paste any dummy string (e.g., sk-local).
3) Toggle “Override OpenAI Base URL”:
   - For local use: http://localhost:4000/v1 → Verify.
   - For cloud Agent/Edit: use your public tunnel, e.g., https://something.trycloudflare.com/v1 → Verify.
4) Add model names exactly as in your config.yaml (press Enter after each):
   - claude-opus-4.1
   - claude-sonnet-4
   - gemini-2.5-pro
   - gemini-2.5-flash
   - gpt-5
   - gpt-5-low
   - (optional) gemini-2.5-pro-max, gemini-2.5-pro-max-context
5) In chats, select a model explicitly. Avoid “Auto” if it tries a name you didn’t map.

Notes:
- Agent/Edit features may still use Cursor’s hosted models unless you point them at a public URL; localhost is not reachable from Cursor’s servers.
- “Thinking” parameters for Anthropic on Vertex are not supported; keep them off to avoid 400 errors.


## Troubleshooting playbook (copy/paste fixes)

- PowerShell curl errors like “Cannot bind parameter 'Headers'”
  - You used PowerShell’s curl alias. Use curl.exe or Invoke-RestMethod with a headers hashtable.

- UnicodeDecodeError in Python/YAML
  - Re-write config.yaml with ASCII encoding (the steps above use Set-Content -Encoding ASCII).

- 401 “No api key passed in”
  - Always include an Authorization: Bearer header: -H "Authorization: Bearer any-string".

- 403 “aiplatform.endpoints.predict denied”
  - Grant roles/aiplatform.user to your caller (service account or user) on the same project you’re calling.
  - Click Enable on the Claude model card in Model Garden for this project (us-east5). This is required for Anthropic.

- 404 or model not found
  - Anthropic on Vertex must use us-east5 and versioned IDs, e.g., claude-opus-4-1@20250805.
  - Gemini uses IDs like gemini-2.5-pro, gemini-2.5-flash.

- Cloudflared not recognized
  - Use the full path: "C:\Program Files\Cloudflare\cloudflared\cloudflared.exe"
  - Or restart PowerShell after install so PATH updates.

- Cloudflare 524 on first request
  - Retry; add --protocol http2 --edge-ip-version 4; allow a few seconds after starting the tunnel.

- Cursor still says “model not supported in your current plan/api key”
  - This often means Cursor bypassed your proxy. Ensure Override OpenAI Base URL is set to your proxy or tunnel and Verify is green. Pick your mapped model name explicitly.

- “Extra inputs are not permitted” from Vertex Anthropic
  - Don’t send non-standard fields (e.g., “thinking”). Keep anthropic-version in headers.
  - Keep litellm_settings.drop_params: true to drop UI extras.

- ADC quota project warning
  - Run: gcloud auth application-default set-quota-project $PROJ

- Paste crashes with PSReadLine exceptions
  - Use the Base64 write method or paste into Notepad/VS Code and save the YAML file manually.


## Role explanations (what they do and why)

- roles/aiplatform.user: Grants Vertex AI user capabilities including aiplatform.endpoints.predict (needed to call models) and token counting. Assign to the service account (or user) your proxy runs as.
- roles/serviceusage.serviceUsageAdmin: Lets a principal enable/disable APIs (e.g., aiplatform.googleapis.com). Sometimes needed so you can run gcloud services enable …
- “Enable” in Model Garden (console action): Not a role but a procurement/terms step that unlocks Anthropic models in the selected project/region. Must be done once per project.


## Appendix A — Full minimal config.yaml (inline)

```yaml
model_list:
  - model_name: "claude-opus-4.1"
    litellm_params:
      model: "vertex_ai/claude-opus-4-1@20250805"
      vertex_project: "gen-lang-client-0376912995"
      vertex_location: "us-east5"
      extra_headers:
        anthropic-version: "vertex-2023-10-16"

  - model_name: "claude-sonnet-4"
    litellm_params:
      model: "vertex_ai/claude-sonnet-4@20250514"
      vertex_project: "gen-lang-client-0376912995"
      vertex_location: "us-east5"
      extra_headers:
        anthropic-version: "vertex-2023-10-16"

  - model_name: "gemini-2.5-pro"
    litellm_params:
      model: "vertex_ai/gemini-2.5-pro"
      vertex_project: "gen-lang-client-0376912995"
      vertex_location: "us-east5"

  - model_name: "gemini-2.5-flash"
    litellm_params:
      model: "vertex_ai/gemini-2.5-flash"
      vertex_project: "gen-lang-client-0376912995"
      vertex_location: "us-east5"

  - model_name: "gpt-5"
    litellm_params:
      model: "vertex_ai/claude-opus-4-1@20250805"
      vertex_project: "gen-lang-client-0376912995"
      vertex_location: "us-east5"
      extra_headers:
        anthropic-version: "vertex-2023-10-16"

  - model_name: "gpt-5-low"
    litellm_params:
      model: "vertex_ai/gemini-2.5-flash"
      vertex_project: "gen-lang-client-0376912995"
      vertex_location: "us-east5"

litellm_settings:
  drop_params: true
```

Adjust vertex_project if your project id differs.


## Appendix B — One-command quick test against Vertex (bypasses LiteLLM)

This proves your project, region, IAM, and Model Garden “Enable” are correct for Anthropic Opus 4.1.

```powershell
$TOKEN = gcloud auth application-default print-access-token
$headers = @{ Authorization = "Bearer $TOKEN"; "Content-Type" = "application/json; charset=utf-8" }
$body = @{ anthropic_version = "vertex-2023-10-16"; messages = @(@{ role="user"; content="Say OK" }); max_tokens = 32; stream = $false } | ConvertTo-Json -Depth 5
Invoke-WebRequest -Method POST -Headers $headers -ContentType "application/json; charset=utf-8" -Body $body -Uri "https://us-east5-aiplatform.googleapis.com/v1/projects/$PROJ/locations/us-east5/publishers/anthropic/models/claude-opus-4-1@20250805:streamRawPredict" | Select-Object -Expand Content
```

You should see a JSON with "OK" from the model. If this succeeds but LiteLLM fails, focus on your LiteLLM config and runtime ADC.


---

Got stuck on a specific error not covered here? Copy the exact error text and your last command, and test directly against Vertex (Appendix B). If the direct call works, your GCP side is correct and the issue is only proxy/UI wiring. If the direct call fails, it’s a project/region/IAM/Enable mismatch—fix those first.
