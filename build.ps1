param (
    [switch]$Deploy = $false
)

$ErrorActionPreference = "Stop"

Write-Host "==========================================================" -ForegroundColor Cyan
Write-Host "   GTA_crowd Simulation - Stage 1 Build Script            " -ForegroundColor Cyan
Write-Host "==========================================================" -ForegroundColor Cyan

# 1. Paths verification
$CscPath = "C:\Windows\Microsoft.NET\Framework64\v4.0.30319\csc.exe"
$GtaRoot = "D:\Games\Grand Theft Auto V Legacy"
$ScriptsDir = "$GtaRoot\scripts"
$ShvdnApi = "$GtaRoot\ScriptHookVDotNet3.dll"

$ProjectRoot = $PSScriptRoot
$SourceFile = Join-Path $ProjectRoot "src\CrowdSimMain.cs"
$BuildDir = Join-Path $ProjectRoot "build"
$OutputDll = Join-Path $BuildDir "CrowdSim.dll"

Write-Host "`n[1/4] Verifying prerequisite tools and references..." -ForegroundColor Yellow

if (-not (Test-Path $CscPath)) {
    Write-Error "C# compiler not found at '$CscPath'."
    exit 1
}
Write-Host "  [OK] Found csc.exe: $CscPath" -ForegroundColor Green

if (-not (Test-Path $ShvdnApi)) {
    Write-Error "ScriptHookVDotNet3.dll not found at '$ShvdnApi'."
    exit 1
}
Write-Host "  [OK] Found ScriptHookVDotNet3.dll: $ShvdnApi" -ForegroundColor Green

if (-not (Test-Path $SourceFile)) {
    Write-Error "Source file not found at '$SourceFile'."
    exit 1
}
Write-Host "  [OK] Found source file: $SourceFile" -ForegroundColor Green

# Ensure local build and logs directories exist
if (-not (Test-Path $BuildDir)) {
    New-Item -ItemType Directory -Path $BuildDir -Force | Out-Null
}
$LogsDir = Join-Path $ProjectRoot "logs"
if (-not (Test-Path $LogsDir)) {
    New-Item -ItemType Directory -Path $LogsDir -Force | Out-Null
}

# 2. Compilation
Write-Host "`n[2/4] Compiling CrowdSim.dll (Target: net48, Platform: x64)..." -ForegroundColor Yellow

$References = @(
    "`"$ShvdnApi`"",
    "System.dll",
    "System.Core.dll",
    "System.Drawing.dll",
    "System.Windows.Forms.dll"
)
$RefArgs = $References | ForEach-Object { "/reference:$_" }

$CompilerArgs = @(
    "/target:library",
    "/platform:x64",
    "/optimize+",
    "/nologo"
) + $RefArgs + @(
    "/out:`"$OutputDll`"",
    "`"$SourceFile`""
)

Write-Host "Executing compiler command:" -ForegroundColor DarkGray
Write-Host "$CscPath $($CompilerArgs -join ' ')" -ForegroundColor DarkGray

$process = Start-Process -FilePath $CscPath -ArgumentList $CompilerArgs -NoNewWindow -Wait -PassThru -RedirectStandardOutput "$BuildDir\csc_stdout.txt" -RedirectStandardError "$BuildDir\csc_stderr.txt"

$stdout = ""
if (Test-Path "$BuildDir\csc_stdout.txt") {
    $stdout = Get-Content "$BuildDir\csc_stdout.txt" -Raw
}
$stderr = ""
if (Test-Path "$BuildDir\csc_stderr.txt") {
    $stderr = Get-Content "$BuildDir\csc_stderr.txt" -Raw
}

if ($stdout) { Write-Host $stdout }
if ($stderr) { Write-Host $stderr -ForegroundColor Red }

if ($process.ExitCode -ne 0) {
    Write-Error "Compilation FAILED with exit code $($process.ExitCode)."
    exit $process.ExitCode
}

Write-Host "  [OK] Compilation succeeded with exit code 0." -ForegroundColor Green
$dllItem = Get-Item $OutputDll
Write-Host "  Output DLL: $($dllItem.FullName) ($($dllItem.Length) bytes)" -ForegroundColor Green

# 3. Deployment
if ($Deploy) {
    Write-Host "`n[3/4] Deploying to GTA V scripts folder..." -ForegroundColor Yellow
    if (-not (Test-Path $ScriptsDir)) {
        New-Item -ItemType Directory -Path $ScriptsDir -Force | Out-Null
    }
    Copy-Item -Path $OutputDll -Destination "$ScriptsDir\CrowdSim.dll" -Force
    Write-Host "  [OK] Successfully deployed CrowdSim.dll to $ScriptsDir\CrowdSim.dll" -ForegroundColor Green
} else {
    Write-Host "`n[3/4] Deployment skipped (local build only). Use -Deploy to copy to GTA V scripts folder." -ForegroundColor Cyan
}

Write-Host "`n[4/4] Build complete." -ForegroundColor Green
Write-Host "==========================================================" -ForegroundColor Cyan
