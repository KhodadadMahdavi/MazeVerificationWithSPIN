
# Maze Verification with SPIN — Reproduction Pipeline (Windows + MSYS2)

This repository generates random maze levels, converts them to a PROMELA model, uses **SPIN** (via `pan`) to **prove a win path exists** by finding a counterexample to `[](!win)`, then replays that counterexample into `U/D/L/R` moves and validates the moves in Python. Finally, it visualizes the maze and the extracted win path.

> [!NOTE] Core Idea
> We check the LTL property **“never win”**:
> 
> `ltl never_win { [](!win) }`
> 
> If SPIN finds a counterexample, that counterexample is a **witness** that the player can reach `E` from `A`.

## What you get per run

After running the pipeline you will have:

- `levels/level_01.txt` — generated maze (ASCII)
- `promela/maze.pml` — generated PROMELA model for that maze
- `pan.c` / `pan` — verifier source and binary created by SPIN
- `trails/pan_output.txt` — model checking output log
- `pan.trail` (or `maze.pml.trail`) — counterexample trail file
- `trails/trail_replay.txt` — replay output (contains `MOVE n` markers)
- `moves/moves_01.txt` — extracted path as `UDLR...`
- `replay/replay_log.txt` — validation result (`WIN at step X`)
- `replay/level.png` — maze visualization
- `replay/level_with_path.png` — maze + extracted path overlay

## Requirements

### 1) Python
- Windows Python 3.x available as `python`

Check:
```powershell
python --version
```

### 2) Pillow (for visualization)
```powershell
python -m pip install pillow
```

### 3) MSYS2 (for gcc + building the verifier)
You need MSYS2 installed in the default location (or you must adjust the pipeline script):
- `C:\msys64\usr\bin\bash.exe`

### 4) UCRT64 GCC toolchain

In an MSYS2 shell (UCRT64 recommended), install:
```bash
pacman -Syu
pacman -S --needed mingw-w64-ucrt-x86_64-gcc
```

Make sure gcc exists at:
- `C:\msys64\ucrt64\bin\gcc.exe`

### 5) SPIN

Place `spin.exe` at:
- `tools/bin/spin.exe`

The MSYS2 scripts will add `tools/bin` to PATH automatically.

## The pipeline (recommended)

### Run everything with one command

```powershell
cd C:\Dev\maze-spin-repro
powershell -ExecutionPolicy Bypass -File scripts\20_pipeline_one.ps1 -Seed 42 -W 12 -H 12 -WallProb 0.25
```

### Customize generation
- `-Seed` changes the random level
- `-W` changes maze width
- `-H` changes maze height
- `-WallProb` controls wall density (0.10 easier → 0.35 harder)


Examples:
```powershell
# Different seed
powershell -ExecutionPolicy Bypass -File scripts\20_pipeline_one.ps1 -Seed 100

# Bigger maze
powershell -ExecutionPolicy Bypass -File scripts\20_pipeline_one.ps1 -Seed 42 -W 20 -H 20 -WallProb 0.25

# Easier (fewer walls)
powershell -ExecutionPolicy Bypass -File scripts\20_pipeline_one.ps1 -Seed 42 -WallProb 0.15

# Harder (more walls)
powershell -ExecutionPolicy Bypass -File scripts\20_pipeline_one.ps1 -Seed 42 -WallProb 0.35
```

## How it works (end-to-end)

### Step 1 — Generate a level (Python)

Script: `scripts/10_generate_level.py`

- Generates an ASCII grid maze:
    - `#` wall
    - `.` empty
    - `A` start
    - `E` exit

Output:
- `levels/level_01.txt`

### Step 2 — Convert level → PROMELA (Python)

Script: `scripts/01_generate_pml.py`

- Encodes the maze as `wall[W*H]`
- Adds a `visited[W*H]` array to enforce a **no-revisit** (human-like) constraint
- Player chooses moves nondeterministically
- Marks win when `(x,y)` equals exit cell
- Prints `MOVE n` markers during execution:
    - `1=U`, `2=D`, `3=L`, `4=R`

Output:
- `promela/maze.pml`

### Step 3 — Model-check using SPIN/pan (MSYS2)

Script: `scripts/02_run_spin_msys2.sh`
- `spin -a promela/maze.pml` produces `pan.c`
- `gcc -O2 -o pan pan.c` compiles verifier
- `./pan -a -m200000` runs the check

Property checked:
```promela
ltl never_win { [](!win) }
```

If a win is possible, this property is violated and SPIN produces a **trail**.

Outputs:
- `trails/pan_output.txt`
- A trail file: typically `pan.trail` or sometimes `maze.pml.trail`

### Step 4 — Normalize trail name + replay via pan (MSYS2)

Pipeline behavior:
- If `maze.pml.trail` exists, it is copied to `pan.trail`
- Replay is performed using pan:
```bash
./pan -r pan.trail > trails/trail_replay.txt
```

Output:
- `trails/trail_replay.txt`

### Step 5 — Parse moves (Python)

Script: `scripts/03_parse_moves.py`
- Extracts `MOVE n` markers from `trails/trail_replay.txt`
- Writes the path as a compact string (`UDLR...`)

Output:
- `moves/moves_01.txt`

### Step 6 — Validate path (Python)

Script: `scripts/04_replay.py`
- Simulates the path on the grid
- Confirms it reaches `E`

Output:
- `replay/replay_log.txt` (e.g., `WIN at step 14`)

### Step 7 — Visualize (Python + Pillow)

Script: `scripts/12_visualize_level_and_path.py`

- Renders:
    - `replay/level.png`
    - `replay/level_with_path.png`

## Manual pipeline (debug-friendly)

This is the same sequence as the pipeline script, but run step-by-step.

### PowerShell
```powershell
python scripts\10_generate_level.py --w 12 --h 12 --wall_prob 0.25 --seed 42 --out levels\level_01.txt
python scripts\01_generate_pml.py --level levels\level_01.txt --out promela\maze.pml
```

### MSYS2
```bash
cd /c/Dev/maze-spin-repro
bash scripts/02_run_spin_msys2.sh

# If the trail is named maze.pml.trail:
cp -f maze.pml.trail pan.trail

./pan -r pan.trail > trails/trail_replay.txt
```

### PowerShell
```powershell
python scripts\03_parse_moves.py
python scripts\04_replay.py
python scripts\12_visualize_level_and_path.py
```

## Troubleshooting

### `spin: command not found`
- Confirm `tools/bin/spin.exe` exists.
- Confirm `scripts/02_run_spin_msys2.sh` exports PATH including `$ROOT/tools/bin`.

### `gcc: command not found`
- Install: `pacman -S --needed mingw-w64-ucrt-x86_64-gcc`
- Confirm `C:\msys64\ucrt64\bin\gcc.exe` exists.
- Confirm MSYS2 scripts export PATH including `/ucrt64/bin`.

### No trail produced
- Open `trails/pan_output.txt` and look for `errors: 0` vs `errors: 1`.
- Try:
    - lowering `WallProb` (e.g. 0.15)
    - changing `Seed`
    - increasing `MAX_STEPS` in `scripts/01_generate_pml.py`

### `moves_01.txt` empty
- Confirm `trails/trail_replay.txt` contains `MOVE` lines:

```bash
grep -n "MOVE" trails/trail_replay.txt | head
```

- Confirm PROMELA includes `printf("MOVE %d\n", last_move)`.

### Visualization not created

- Check Pillow:
```powershell
python -c "from PIL import Image; print('PIL OK')"
```

- Run manually:
```powershell
python scripts\12_visualize_level_and_path.py
```

## Notes on the “no-revisit” constraint

We enforce `visited[]` to prevent revisiting cells. This avoids extremely long looping counterexample trails and produces a clean, human-like path.

In grid mazes, if a solution exists, there is always a **simple path** that does not repeat cells, so this restriction does not remove solvable cases; it only removes looping behavior.
