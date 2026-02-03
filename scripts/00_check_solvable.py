from collections import deque
from pathlib import Path

LEVEL = Path("levels/level_01.txt")

def main():
    g = [list(l.rstrip("\n")) for l in LEVEL.read_text(encoding="utf-8").splitlines()]
    h, w = len(g), len(g[0])
    start = goal = None
    for y in range(h):
        for x in range(w):
            if g[y][x] == "A":
                start = (x, y)
            elif g[y][x] == "E":
                goal = (x, y)

    if start is None or goal is None:
        raise SystemExit("Level must contain A and E.")

    q = deque([start])
    seen = {start}
    dirs = [(1,0),(-1,0),(0,1),(0,-1)]
    while q:
        x, y = q.popleft()
        if (x, y) == goal:
            print("SOLVABLE")
            return
        for dx, dy in dirs:
            nx, ny = x + dx, y + dy
            if 0 <= nx < w and 0 <= ny < h and (nx, ny) not in seen:
                if g[ny][nx] != "#":
                    seen.add((nx, ny))
                    q.append((nx, ny))
    print("UNSOLVABLE")

if __name__ == "__main__":
    main()
