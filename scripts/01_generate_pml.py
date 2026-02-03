from pathlib import Path
import argparse

MAX_STEPS = 2000  # safe bound

def read_level(path: Path):
    lines = [line.rstrip("\n") for line in path.read_text(encoding="utf-8").splitlines()]
    if not lines:
        raise ValueError("Empty level file.")
    w = len(lines[0])
    if any(len(row) != w for row in lines):
        raise ValueError("Level rows are not equal width.")

    grid = []
    ax = ay = ex = ey = None

    for y, row in enumerate(lines):
        for x, ch in enumerate(row):
            if ch == "A":
                ax, ay = x, y
                grid.append(".")
            elif ch == "E":
                ex, ey = x, y
                grid.append(".")
            elif ch in ["#", "."]:
                grid.append(ch)
            else:
                raise ValueError(f"Invalid char '{ch}' at ({x},{y}). Use only # . A E")

    if ax is None or ex is None:
        raise ValueError("Level must contain exactly one A and one E.")

    h = len(lines)
    return w, h, grid, ax, ay, ex, ey

def emit_promela(w, h, grid, ax, ay, ex, ey):
    walls = [1 if ch == "#" else 0 for ch in grid]

    pml = []
    pml.append("/* Auto-generated PROMELA model for Maze (no-revisit rule) */")
    pml.append(f"#define W {w}")
    pml.append(f"#define H {h}")
    pml.append(f"#define MAX_STEPS {MAX_STEPS}")
    pml.append("")
    pml.append("byte x;")
    pml.append("byte y;")
    pml.append("bool win = false;")
    pml.append("int steps = 0;")
    pml.append("byte last_move = 0; /* 1=U,2=D,3=L,4=R */")
    pml.append("")
    pml.append(f"byte wall[W*H] = {{ {', '.join(map(str, walls))} }};")
    pml.append("byte visited[W*H]; /* 0=not visited, 1=visited */")
    pml.append("")
    pml.append("inline update_win() {")
    pml.append("    if")
    pml.append(f"    :: (x == {ex} && y == {ey}) -> win = true")
    pml.append("    :: else -> skip")
    pml.append("    fi")
    pml.append("}")
    pml.append("")
    pml.append("active proctype Player() {")
    pml.append(f"    x = {ax}; y = {ay};")
    pml.append("    visited[(y*W + x)] = 1;")
    pml.append("    update_win();")
    pml.append("    do")
    pml.append("    :: (steps < MAX_STEPS && !win) ->")
    pml.append("        steps++;")
    pml.append("        if")
    pml.append(
        "        :: (y > 0 && wall[((y-1)*W + x)] == 0 && visited[((y-1)*W + x)] == 0) -> "
        "y = y-1; visited[(y*W + x)] = 1; last_move = 1; printf(\"MOVE %d\\n\", last_move)"
    )
    pml.append(
        "        :: (y+1 < H && wall[((y+1)*W + x)] == 0 && visited[((y+1)*W + x)] == 0) -> "
        "y = y+1; visited[(y*W + x)] = 1; last_move = 2; printf(\"MOVE %d\\n\", last_move)"
    )
    pml.append(
        "        :: (x > 0 && wall[(y*W + (x-1))] == 0 && visited[(y*W + (x-1))] == 0) -> "
        "x = x-1; visited[(y*W + x)] = 1; last_move = 3; printf(\"MOVE %d\\n\", last_move)"
    )
    pml.append(
        "        :: (x+1 < W && wall[(y*W + (x+1))] == 0 && visited[(y*W + (x+1))] == 0) -> "
        "x = x+1; visited[(y*W + x)] = 1; last_move = 4; printf(\"MOVE %d\\n\", last_move)"
    )
    pml.append("        fi;")
    pml.append("        update_win();")
    pml.append("    :: else -> break")
    pml.append("    od;")
    pml.append("}")
    pml.append("")
    pml.append("ltl never_win { [](!win) }")
    pml.append("")
    return "\n".join(pml)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--level", default="levels/level_01.txt", help="Input level file")
    ap.add_argument("--out", default="promela/maze.pml", help="Output pml file")
    args = ap.parse_args()

    level_path = Path(args.level)
    out_path = Path(args.out)

    w, h, grid, ax, ay, ex, ey = read_level(level_path)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(emit_promela(w, h, grid, ax, ay, ex, ey), encoding="utf-8")

    print(f"Wrote {out_path} (W={w}, H={h}, A=({ax},{ay}), E=({ex},{ey})) from {level_path}")

if __name__ == "__main__":
    main()
