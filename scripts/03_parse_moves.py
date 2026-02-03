from pathlib import Path

REPLAY_TXT = Path("trails/trail_replay.txt")
OUT = Path("moves/moves_01.txt")

MOVE_MAP = {
    "last_move = 1": "U",
    "last_move = 2": "D",
    "last_move = 3": "L",
    "last_move = 4": "R",
}

def main():
    if not REPLAY_TXT.exists():
        raise SystemExit("Missing trails/trail_replay.txt. Run MSYS2 replay step first.")

    text = REPLAY_TXT.read_text(encoding="utf-8", errors="replace")
    moves = []
    for line in text.splitlines():
        for k, v in MOVE_MAP.items():
            if k in line:
                moves.append(v)

    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text("".join(moves), encoding="utf-8")
    print(f"Wrote {OUT} ({len(moves)} moves)")

if __name__ == "__main__":
    main()
