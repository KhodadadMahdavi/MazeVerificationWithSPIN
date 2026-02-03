param(
  [int]$Seed = 42,
  [int]$W = 12,
  [int]$H = 12,
  [double]$WallProb = 0.25,

  # If your MSYS2 install is elsewhere, change this
  [string]$MsysBash = "C:\msys64\usr\bin\bash.exe"
)

$ErrorActionPreference = "Stop"

# Project root = parent of scripts folder
$ProjectRoot = (Resolve-Path (Join-Path $PSScriptRoot "..")).Path
Set-Location $ProjectRoot

Write-Host "ProjectRoot: $ProjectRoot"

if (-not (Test-Path $MsysBash)) {
  throw "MSYS2 bash not found at: $MsysBash`nEdit -MsysBash or install MSYS2 to C:\msys64."
}

# Convert Windows path to MSYS2 path (C:\Dev\maze-spin-repro -> /c/Dev/maze-spin-repro)
$drive = $ProjectRoot.Substring(0,1).ToLower()
$rest = $ProjectRoot.Substring(2) -replace "\\","/"
$MsysRoot = "/$drive$rest"
Write-Host "MSYS2 root: $MsysRoot"

# -------------------------
# Step 1) Generate level + PML (PowerShell / Windows Python)
# -------------------------
Write-Host "`n[1/4] Generate level (seed=$Seed, ${W}x${H}, wall_prob=$WallProb) ..."
python scripts\10_generate_level.py --w $W --h $H --wall_prob $WallProb --seed $Seed --out levels\level_01.txt

Write-Host "[1/4] Generate PROMELA ..."
python scripts\01_generate_pml.py --level levels\level_01.txt --out promela\maze.pml

# -------------------------
# Step 2) Run SPIN + build pan + run pan to create a trail (MSYS2)
# -------------------------
Write-Host "`n[2/4] Clean old trails (Windows side) ..."
Remove-Item -Force -ErrorAction SilentlyContinue *.trail
Remove-Item -Force -ErrorAction SilentlyContinue promela\*.trail
Remove-Item -Force -ErrorAction SilentlyContinue trails\*.trail

Write-Host "[2/4] Run SPIN/pan via MSYS2: scripts/02_run_spin_msys2.sh ..."
& $MsysBash -lc "cd '$MsysRoot' && bash scripts/02_run_spin_msys2.sh"



# -------------------------
# Step 3) Normalize trail name + replay via pan (MSYS2)
# -------------------------
Write-Host "`n[3/4] Replay trail via pan (MSYS2) ..."

# create a temp bash script file (avoids PowerShell here-string parsing issues)
$TempBash = Join-Path $ProjectRoot "scripts\_temp_replay_trail.sh"

@(
  '#!/usr/bin/env bash'
  'set -euo pipefail'
  "cd '$MsysRoot'"
  'mkdir -p trails'
  ''
  '# Ensure SPIN is on PATH too (optional but safe)'
  'export PATH="$PWD/tools/bin:/ucrt64/bin:/usr/bin:$PATH"'
  'export PATH="$PWD/tools/bin:$PATH"'
  ''
  '# Normalize trail naming: prefer maze.pml.trail if present'
  'if [ -f "maze.pml.trail" ]; then'
  '  cp -f "maze.pml.trail" "pan.trail"'
  'elif [ -f "trails/maze.pml.trail" ]; then'
  '  cp -f "trails/maze.pml.trail" "pan.trail"'
  'elif [ -f "trails/pan.trail" ]; then'
  '  cp -f "trails/pan.trail" "pan.trail"'
  'fi'
  ''
  'if [ ! -f "pan.trail" ]; then'
  '  echo "ERROR: no trail found (pan.trail / maze.pml.trail missing)."'
  '  echo "Root trails:"'
  '  ls -la *.trail 2>/dev/null || true'
  '  echo "Trails folder:"'
  '  ls -la trails/*.trail 2>/dev/null || true'
  '  echo "Also check: trails/pan_output.txt"'
  '  exit 2'
  'fi'
  ''
  '# Replay using pan'
  './pan -r pan.trail > trails/trail_replay.txt'
  ''
  'echo "Replay saved to trails/trail_replay.txt"'
  'grep -n "MOVE" trails/trail_replay.txt | head -n 10 || true'
) | Set-Content -Encoding ASCII $TempBash


# run it inside MSYS2
& $MsysBash -lc "bash '$MsysRoot/scripts/_temp_replay_trail.sh'"



# cleanup temp file (optional)
Remove-Item -Force -ErrorAction SilentlyContinue $TempBash

# -------------------------
# Step 4) Parse + replay validation (PowerShell / Windows Python)
# -------------------------
Write-Host "`n[4/4] Parse moves ..."
python scripts\03_parse_moves.py

Write-Host "[4/4] Replay moves and validate WIN ..."
python scripts\04_replay.py

Write-Host "[5/5] Visualize level + path ..."
python scripts\12_visualize_level_and_path.py

Write-Host "`nDONE ✅"
Write-Host "Outputs:"
Write-Host "  - levels/level_01.txt"
Write-Host "  - promela/maze.pml"
Write-Host "  - trails/pan_output.txt"
Write-Host "  - trails/trail_replay.txt"
Write-Host "  - moves/moves_01.txt"
Write-Host "  - replay/replay_log.txt"
