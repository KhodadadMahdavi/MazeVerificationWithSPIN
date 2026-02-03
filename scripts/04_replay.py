from pathlib import Path

LEVEL_PATH = Path("levels/level_01.txt")
MOVES_PATH = Path("moves/moves_01.txt")
LOG_PATH = Path("replay/replay_log.txt")

DIRS = {"U": (0, -1), "D": (0, 1), "L": (-1, 0), "R": (1, 0)}

def load_level(path: Path):
    lines = [list(l.rstrip("\n")) for l in path.read_text(encoding="utf-8").splitlines()]
    h = len(lines)
    w = len(lines[0]) if h else 0

    ax = ay = ex = ey = None
    for y in range(h):
        for x in range(w):
            if lines[y][x] == "A":
                ax, ay = x, y
            elif lines[y][x] == "E":
                ex, ey = x, y

    if ax is None or ex is None:
        raise ValueError("Level must contain A and E.")
    return lines, w, h, ax, ay, ex, ey

def main():
    grid, w, h, x, y, ex, ey = load_level(LEVEL_PATH)
    moves = MOVES_PATH.read_text(encoding="utf-8").strip()

    def is_wall(nx, ny):
        return grid[ny][nx] == "#"

    reached = False
    step_reached = None
    for i, m in enumerate(moves, start=1):
        dx, dy = DIRS[m]
        nx, ny = x + dx, y + dy
        if not (0 <= nx < w and 0 <= ny < h):
            continue
        if is_wall(nx, ny):
            continue
        x, y = nx, ny
        if (x, y) == (ex, ey):
            reached = True
            step_reached = i
            break

    LOG_PATH.parent.mkdir(parents=True, exist_ok=True)
    if reached:
        LOG_PATH.write_text(f"WIN at step {step_reached}\n", encoding="utf-8")
        print(f"WIN at step {step_reached}")
    else:
        LOG_PATH.write_text("FAILED to reach exit\n", encoding="utf-8")
        raise SystemExit("FAILED: did not reach exit")

if __name__ == "__main__":
    main()
