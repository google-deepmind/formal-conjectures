<#
.SYNOPSIS
  Convenience script to run the Erdos updates checker locally on Windows PowerShell.

.DESCRIPTION
  Creates a dedicated virtual environment, installs the required Python packages
  (if requested), and runs `.github/scripts/check_erdos_updates.py` in either
  dry-run mode (default) or full mode (writes files and updates `erdos_dates.json`).

.PARAMETER FullRun
  If set, performs a full run that writes `erdos_dates.json` and `updates.json`.
  Without this flag the script runs in `--dry-run` mode (no file writes).

.PARAMETER InstallDeps
  If set, (re)install Python dependencies into the venv.

.EXAMPLE
  # dry-run (default)
  .\scripts\run_erdos_check.ps1

  # full run (writes files)
  .\scripts\run_erdos_check.ps1 -FullRun

  # force (re)install dependencies and do dry-run
  .\scripts\run_erdos_check.ps1 -InstallDeps
#>

param(
  [switch]$FullRun,
  [switch]$InstallDeps
)

Set-StrictMode -Version Latest

$repoRoot = Split-Path -Parent $MyInvocation.MyCommand.Definition
Push-Location $repoRoot

$venvDir = Join-Path $repoRoot ".venv_erdos"
$requirements = ".github/erdos-updates/requirements.txt"
$script = ".github/scripts/check_erdos_updates.py"
$datesFile = ".github/erdos-updates/erdos_dates.json"
$outFile = ".github/erdos-updates/updates.json"

if (-not (Test-Path $script)) {
  Write-Error "Checker script not found: $script"
  Pop-Location
  exit 2
}

if (-not (Test-Path $venvDir)) {
  Write-Host "Creating virtual environment at $venvDir"
  python -m venv $venvDir
}

if ($InstallDeps) {
  Write-Host "(Re)installing Python dependencies..."
  & "$venvDir\Scripts\python.exe" -m pip install --upgrade pip
  & "$venvDir\Scripts\python.exe" -m pip install -r $requirements
}

Write-Host "Activating virtual environment..."
# Activation changes the shell state; instead call python directly from the venv
$py = "$venvDir\Scripts\python.exe"

if (-not (Test-Path $py)) {
  Write-Error "Python executable not found in venv: $py"
  Pop-Location
  exit 3
}

if ($FullRun) {
  Write-Host "Running full check (will write $datesFile and $outFile)..."
  & $py $script --problems-dir FormalConjectures/ErdosProblems --dates-file $datesFile --out $outFile
  $exit = $LASTEXITCODE
  if ($exit -eq 0) {
    Write-Host "Full run finished. Contents of $outFile:"
    if (Test-Path $outFile) { Get-Content $outFile -Raw } else { Write-Host "No updates file written." }
  }
  else { Write-Error "Checker script exited with code $exit" }
  Pop-Location
  exit $exit
}
else {
  Write-Host "Running dry-run (no files will be written)."
  & $py $script --problems-dir FormalConjectures/ErdosProblems --dates-file $datesFile --out $outFile --dry-run
  $exit = $LASTEXITCODE
  Pop-Location
  exit $exit
}
