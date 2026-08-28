$ErrorActionPreference = 'Stop'

$pluginDir = $env:HELM_PLUGIN_DIR
if ([string]::IsNullOrEmpty($pluginDir)) {
    throw 'HELM_PLUGIN_DIR is not set'
}

$binary = Join-Path $pluginDir 'bin\helm-schema.exe'
if (Test-Path -Path $binary -PathType Leaf) {
    exit 0
}

if (-not (Get-Command go -ErrorAction SilentlyContinue)) {
    throw 'helm-schema source installation requires Go; install a packaged release or install Go and retry'
}

New-Item -ItemType Directory -Force -Path (Split-Path -Parent $binary) | Out-Null
Push-Location $pluginDir
try {
    & go build -buildvcs=false -trimpath -o $binary ./cmd/helm-schema
    if ($LASTEXITCODE -ne 0) {
        exit $LASTEXITCODE
    }
} finally {
    Pop-Location
}
