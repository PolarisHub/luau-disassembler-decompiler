$ErrorActionPreference = "Stop"

$root = Split-Path -Parent (Split-Path -Parent $MyInvocation.MyCommand.Path)
$release = Join-Path $root "release"
$bin = Join-Path $release "bin"
$exeSource = Join-Path $root "target\release\luau-server.exe"
$exeDest = Join-Path $bin "luau-server.exe"
$zip = Join-Path $release "luau-disassembler-v0.1.0-windows-x64.zip"
$hashFile = "$zip.sha256"

Push-Location $root
try {
    cargo build -p luau-server --release

    New-Item -ItemType Directory -Force -Path $bin | Out-Null
    Copy-Item -LiteralPath $exeSource -Destination $exeDest -Force

    if (Test-Path -LiteralPath $zip) {
        Remove-Item -LiteralPath $zip -Force
    }
    if (Test-Path -LiteralPath $hashFile) {
        Remove-Item -LiteralPath $hashFile -Force
    }

    Compress-Archive -Path `
        (Join-Path $release "bin"), `
        (Join-Path $release "example.luau"), `
        (Join-Path $release "README.md"), `
        (Join-Path $release "RELEASE_NOTES_v0.1.0.md"), `
        (Join-Path $release "smoke-test.ps1") `
        -DestinationPath $zip

    $hash = Get-FileHash -Algorithm SHA256 -LiteralPath $zip
    "$($hash.Hash.ToLowerInvariant())  $(Split-Path -Leaf $zip)" | Set-Content -NoNewline -Encoding ASCII -Path $hashFile

    Write-Host "Wrote $zip"
    Write-Host "Wrote $hashFile"
} finally {
    Pop-Location
}
