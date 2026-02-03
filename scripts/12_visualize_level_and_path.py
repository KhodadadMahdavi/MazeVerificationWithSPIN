from pathlib import Path
from PIL import Image, ImageDraw

LEVEL_PATH = Path("levels/level_01.txt")
MOVES_PATH = Path("moves/moves_01.txt")

CELL = 32
PAD = 16

DIRS = {"U": (0, -1), "D": (0, 1), "L": (-1, 0), "R": (1, 0)}

def load_level():
    lines = [list(l.rstrip("\n")) for l in LEVEL_PATH.read_text(encoding="utf-8").splitlines()]
    h = len(lines)
    w = len(lines[0])
    ax = ay = ex = ey = None
    for y in range(h):
        for x in range(w):
            if lines[y][x] == "A": ax, ay = x, y
            if lines[y][x] == "E": ex, ey = x, y
    return lines, w, h, ax, ay, ex, ey

def main():
    grid, w, h, x, y, ex, ey = load_level()
    moves = MOVES_PATH.read_text(encoding="utf-8").strip()

    img_w = PAD*2 + w*CELL
    img_h = PAD*2 + h*CELL

    def draw_base():
        img = Image.new("RGB", (img_w, img_h), "white")
        dr = ImageDraw.Draw(img)
        for yy in range(h):
            for xx in range(w):
                ch = grid[yy][xx]
                x0 = PAD + xx*CELL
                y0 = PAD + yy*CELL
                x1 = x0 + CELL
                y1 = y0 + CELL
                if ch == "#":
                    dr.rectangle([x0, y0, x1, y1], fill=(40,40,40))
                else:
                    dr.rectangle([x0, y0, x1, y1], fill=(235,235,235))
                dr.rectangle([x0, y0, x1, y1], outline=(180,180,180))
        # start/end
        dr.rectangle([PAD + x*CELL, PAD + y*CELL, PAD+(x+1)*CELL, PAD+(y+1)*CELL], fill=(80,160,255))
        dr.rectangle([PAD + ex*CELL, PAD + ey*CELL, PAD+(ex+1)*CELL, PAD+(ey+1)*CELL], fill=(80,220,120))
        return img, dr

    # base image
    img, dr = draw_base()
    Path("replay").mkdir(parents=True, exist_ok=True)
    img.save("replay/level.png")

    # path overlay
    img2, dr2 = draw_base()
    px, py = x, y
    path_cells = [(px, py)]
    for m in moves:
        dx, dy = DIRS[m]
        nx, ny = px+dx, py+dy
        if 0 <= nx < w and 0 <= ny < h and grid[ny][nx] != "#":
            px, py = nx, ny
            path_cells.append((px, py))

    for (cx, cy) in path_cells:
        x0 = PAD + cx*CELL + CELL//4
        y0 = PAD + cy*CELL + CELL//4
        x1 = PAD + cx*CELL + 3*CELL//4
        y1 = PAD + cy*CELL + 3*CELL//4
        dr2.ellipse([x0, y0, x1, y1], fill=(255,120,80))

    img2.save("replay/level_with_path.png")
    print("Wrote replay/level.png and replay/level_with_path.png")

if __name__ == "__main__":
    main()

