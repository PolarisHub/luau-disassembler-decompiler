$ErrorActionPreference = "Stop"

$root = Split-Path -Parent $MyInvocation.MyCommand.Path
$exe = Join-Path $root "bin\luau-server.exe"

if (-not (Test-Path -LiteralPath $exe)) {
    throw "Missing server executable: $exe"
}

$listener = [System.Net.Sockets.TcpListener]::new([System.Net.IPAddress]::Parse("127.0.0.1"), 0)
$listener.Start()
$port = $listener.LocalEndpoint.Port
$listener.Stop()

$baseUrl = "http://127.0.0.1:$port"
$process = Start-Process -FilePath $exe -ArgumentList "127.0.0.1:$port" -PassThru -WindowStyle Hidden

try {
    $deadline = (Get-Date).AddSeconds(5)
    do {
        try {
            $health = Invoke-RestMethod -Uri "$baseUrl/health" -Method Get
            if ($health.status -eq "ok" -and $health.service -eq "luau-server") {
                $health | ConvertTo-Json -Compress
                exit 0
            }
        } catch {
            Start-Sleep -Milliseconds 200
        }
    } while ((Get-Date) -lt $deadline)

    throw "Server did not answer /health before timeout."
} finally {
    if ($process -and -not $process.HasExited) {
        Stop-Process -Id $process.Id -Force
    }
}
