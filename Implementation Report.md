# Implementation Report — Maze Verification with SPIN (Maze Demo Reproduction)

## 1. Goal and Scope

### 1.1 Goal

Implement a working, reproducible demo for the **Maze** example in the paper’s verification pipeline:

1. Generate a maze level
2. Translate the level into a **PROMELA** model
3. Use **SPIN / pan** to model-check an LTL property
4. Extract a **witness path** (counterexample trail) as a move sequence
5. Validate the move sequence on the original level
6. Visualize the level and the extracted solution path

### 1.2 Scope of this implementation

This implementation focuses on a **self-contained Maze demo project** that reproduces the core idea: _model checking yields a counterexample trail that acts as a solution witness_.

It does **not** reproduce every auxiliary component from the paper (e.g., re-animating solutions in a full VGDL runtime), and it currently uses a **custom level generator** rather than the paper’s exact cellular-automata generator.

## 2. Repository Structure

```
maze-spin-repro/
  levels/
    level_01.txt
  promela/
    maze.pml
  scripts/
    01_generate_pml.py
    02_run_spin_msys2.sh
    03_parse_moves.py
    04_replay.py
    10_generate_level.py
    12_visualize_level_and_path.py
    20_pipeline_one.ps1
  tools/
    bin/
      spin.exe
  trails/
    pan_output.txt
    trail_replay.txt
  moves/
    moves_01.txt
  replay/
    replay_log.txt
    level.png
    level_with_path.png
```

## 3. Tooling and Environment

### 3.1 OS and Editor

- Windows 11
- VS Code

### 3.2 Required Tools

- **Python 3.x** (for level generation, PROMELA generation, parsing, replay validation, visualization)
- **MSYS2** (used as a POSIX toolchain environment on Windows)
- **GCC (UCRT64)** via MSYS2 (to compile `pan.c` produced by SPIN)
- **SPIN** (`spin.exe`) placed at `tools/bin/spin.exe`

### 3.3 Key Environment Detail (MSYS2 PATH)

A critical issue encountered was that calling MSYS2 from PowerShell often does not inherit the same PATH as an interactive UCRT64 session.

To make the run deterministic, the MSYS2 script explicitly sets:

- `tools/bin` (for `spin`)
- `/ucrt64/bin` (for `gcc`)

This ensures that both SPIN and GCC are available regardless of how the shell is launched.

## 4. Implementation Design

### 4.1 Level Representation

Levels are ASCII grids:

- `#` = wall
- `.` = walkable
- `A` = start
- `E` = exit

Example (small excerpt):
```
############
#A..#......#
#..##..#...#
#......#..E#
############
```

### 4.2 Level Generation

Script: `scripts/10_generate_level.py`

A new level is generated each run using parameters:
- width (`--w`)
- height (`--h`)
- wall probability (`--wall_prob`)
- seed (`--seed`)

The generator:
1. Starts with an open interior and walled borders
2. Carves a guaranteed path from start to exit (biased randomized walk)
3. Sprinkles additional walls with probability `wall_prob`
4. Writes `A` at `(1,1)` and `E` at `(w-2,h-2)`

This guarantees a solvable maze _under standard movement rules_.

### 4.3 PROMELA Model Generation

Script: `scripts/01_generate_pml.py`

The generated PROMELA model includes:
- Grid constants: `W`, `H`
- A `wall[W*H]` array (1=wall, 0=floor)
- Player position `(x,y)`
- A boolean `win`
- A step counter bounded by `MAX_STEPS`
- A `visited[W*H]` array implementing a **no-revisit constraint**

#### No-revisit rule (design choice)

To avoid long looping counterexample trails (which are valid but not human-readable), the model forbids moving into a previously visited cell:

- A move is enabled only if the destination is:
    1. within bounds
    2. not a wall
    3. not visited

This produces short, loop-free “human-like” solutions.

#### MOVE markers (for robust parsing)

Each successful move prints a marker:

- `MOVE 1` = Up
- `MOVE 2` = Down
- `MOVE 3` = Left
- `MOVE 4` = Right

These markers are used later for reliable extraction regardless of other pan/SPIN output content.

### 4.4 LTL Property

The model includes:

```
ltl never_win { [](!win) }
```

Meaning:

- We assert it is always true that `win` is never reached.
- If the level is solvable, SPIN finds a counterexample (a trace where `win` becomes true).
- That trace is the **witness** we extract as a solution path.

## 5. Verification and Witness Extraction

### 5.1 Running SPIN and pan

Script: `scripts/02_run_spin_msys2.sh`

Steps:
1. `spin -a promela/maze.pml` generates `pan.c`
2. `gcc -O2 -o pan pan.c` compiles the verifier
3. `./pan -a -m200000` runs the verifier
4. The output is saved to `trails/pan_output.txt`

If an error is found (counterexample exists), SPIN/pan generates a trail file.

### 5.2 Trail naming issues (pan.trail vs maze.pml.trail)

A major practical issue on Windows was **trail file naming differences** depending on SPIN/pan versions.

Observed outcomes:
- sometimes the trail is named `pan.trail`
- sometimes the trail is named `maze.pml.trail`

To normalize, the pipeline copies:
- `maze.pml.trail → pan.trail`

### 5.3 Replaying the trail

In this implementation the trail is replayed using pan:
```
./pan -r pan.trail > trails/trail_replay.txt
```

This produces a readable execution log that includes the `MOVE n` markers.

### 5.4 Parsing moves

Script: `scripts/03_parse_moves.py`

- Reads `trails/trail_replay.txt`
- Extracts all `MOVE n`
- Converts to `U/D/L/R`
- Writes to `moves/moves_01.txt`

## 6. Validation (Replay on the Original Level)

Script: `scripts/04_replay.py`

Steps:
1. Load the level
2. Load the move string from `moves/moves_01.txt`
3. Simulate movement step-by-step
4. Fail if:
    - a move hits a wall
    - a move goes out of bounds
    - the exit is not reached
5. Succeed if the exit is reached; write `WIN at step X`

Output:
- `replay/replay_log.txt`

## 7. Visualization

Script: `scripts/12_visualize_level_and_path.py`
- Renders the maze grid to `replay/level.png`
- Overlays the extracted path to `replay/level_with_path.png`

This provides an immediate artifact showing:
- maze structure
- start and exit positions
- the verified witness path

## 8. Automation: Pipeline One

Script: `scripts/20_pipeline_one.ps1`

The pipeline runs the whole process end-to-end from PowerShell:
1. Generate level (`10_generate_level.py`)
2. Generate PROMELA (`01_generate_pml.py`)
3. Run model-check (MSYS2: `02_run_spin_msys2.sh`)
4. Normalize trail name + replay trail using pan
5. Parse moves (`03_parse_moves.py`)
6. Validate moves (`04_replay.py`)
7. Visualize (`12_visualize_level_and_path.py`)

Parameters:
- `-Seed`, `-W`, `-H`, `-WallProb`


## 9. Problems Encountered and Fixes

### 9.1 Missing `make` vs `mingw32-make`
On MSYS2, GNU Make may be installed as `mingw32-make.exe` rather than `make`. This was identified during early toolchain checks.

### 9.2 `spin` not found in non-interactive shells
When `bash` was invoked from PowerShell (`bash -lc`), SPIN was not on PATH. Fixed by placing `spin.exe` in `tools/bin` and exporting PATH in MSYS2 scripts.

### 9.3 `gcc` not found in non-UCRT64 shells
The pipeline originally launched a shell without `/ucrt64/bin` on PATH, causing `gcc` to be missing. Fixed by explicitly exporting PATH inside `02_run_spin_msys2.sh`.

### 9.4 `spin: cannot find trail file`
Trail naming differed across builds and the replay step failed when the wrong trail name was assumed. Fixed by copying `maze.pml.trail` to `pan.trail`.

### 9.5 Long looping solution traces
SPIN may produce long cyclic counterexamples that still reach the exit. This was addressed by adding a `visited[]` no-revisit constraint to the model to obtain short, loop-free witness paths.

## 10. Deviations from the Paper (Important for Reporting)

This implementation is faithful to the **verification → counterexample → witness path** concept, but includes some differences that should be documented:

1. **Level generator**: uses a custom random generator rather than the paper’s exact cellular automata approach.
2. **No-revisit constraint(Game Design Change)**: the model forbids revisiting cells for human-readable solutions. (The paper discusses shortest traces via model-checker settings; here we enforced it at the model level.)
3. **Standalone Maze**: this repo focuses on the maze example rather than implementing all behavioral templates for all games.


## 11. How to Run (Reproduction Instructions)

### 11.1 Run the full pipeline

```powershell
cd C:\Dev\maze-spin-repro
powershell -ExecutionPolicy Bypass -File scripts\20_pipeline_one.ps1 -Seed 42 -W 12 -H 12 -WallProb 0.25
```

### 11.2 Expected outputs

- `trails/pan_output.txt` contains the verification results
- `trails/trail_replay.txt` contains `MOVE` lines
- `moves/moves_01.txt` is non-empty
- `replay/replay_log.txt` contains `WIN at step ...`
- `replay/level_with_path.png` shows the extracted path

## 12. Validation Evidence

Successful runs demonstrate:
- A counterexample trail is produced by SPIN/pan
- The extracted move sequence reaches `E`
- The visualization overlays the computed path correctly


## Appendix A — Manual Command Sequence

### PowerShell
```powershell
python scripts\10_generate_level.py --w 12 --h 12 --wall_prob 0.25 --seed 42 --out levels\level_01.txt
python scripts\01_generate_pml.py --level levels\level_01.txt --out promela\maze.pml
```

### MSYS2
```bash
cd /c/Dev/maze-spin-repro
bash scripts/02_run_spin_msys2.sh

# normalize trail name if needed
cp -f maze.pml.trail pan.trail

./pan -r pan.trail > trails/trail_replay.txt
```

### PowerShell
```powershell
python scripts\03_parse_moves.py
python scripts\04_replay.py
python scripts\12_visualize_level_and_path.py
```