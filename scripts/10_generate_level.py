from pathlib import Path
import argparse
import random

def carve_path(grid, w, h, start, goal, rng):
    x, y = start
    gx, gy = goal
    grid[y][x] = "."
    # simple randomized “biased walk” to reach goal
    while (x, y) != (gx, gy):
        options = []
        if x < gx: options.append((x+1, y))
        if x > gx: options.append((x-1, y))
        if y < gy: options.append((x, y+1))
        if y > gy: options.append((x, y-1))
        # add a little randomness (side steps)
        if rng.random() < 0.35:
            for dx, dy in [(1,0),(-1,0),(0,1),(0,-1)]:
                nx, ny = x+dx, y+dy
                if 1 <= nx < w-1 and 1 <= ny < h-1:
                    options.append((nx, ny))
        x, y = rng.choice(options)
        grid[y][x] = "."
    return grid

def generate_level(w, h, wall_prob, seed):
    rng = random.Random(seed)
    grid = [["#" for _ in range(w)] for __ in range(h)]

    # borders remain walls, interior randomized later
    for y in range(1, h-1):
        for x in range(1, w-1):
            grid[y][x] = "."  # start open

    start = (1, 1)
    goal = (w-2, h-2)

    # carve guaranteed path
    carve_path(grid, w, h, start, goal, rng)

    # sprinkle walls, but keep start/goal/path cells open
    for y in range(1, h-1):
        for x in range(1, w-1):
            if (x, y) in [start, goal]:
                continue
            if grid[y][x] == ".":  # don't wall carved cells with high probability
                if rng.random() < wall_prob:
                    grid[y][x] = "#"

    # place A/E
    ax, ay = start
    gx, gy = goal
    grid[ay][ax] = "A"
    grid[gy][gx] = "E"

    return "\n".join("".join(row) for row in grid) + "\n"

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--w", type=int, default=12)
    ap.add_argument("--h", type=int, default=12)
    ap.add_argument("--wall_prob", type=float, default=0.25)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--out", default="levels/level_01.txt")
    args = ap.parse_args()

    text = generate_level(args.w, args.h, args.wall_prob, args.seed)
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(text, encoding="utf-8")
    print(f"Wrote {out_path} (seed={args.seed}, {args.w}x{args.h}, wall_prob={args.wall_prob})")

if __name__ == "__main__":
    main()
