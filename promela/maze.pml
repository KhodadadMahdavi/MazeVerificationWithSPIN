/* Auto-generated PROMELA model for Maze (no-revisit rule) */
#define W 15
#define H 15
#define MAX_STEPS 2000

byte x;
byte y;
bool win = false;
int steps = 0;
byte last_move = 0; /* 1=U,2=D,3=L,4=R */

byte wall[W*H] = { 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1 };
byte visited[W*H]; /* 0=not visited, 1=visited */

inline update_win() {
    if
    :: (x == 13 && y == 13) -> win = true
    :: else -> skip
    fi
}

active proctype Player() {
    x = 1; y = 1;
    visited[(y*W + x)] = 1;
    update_win();
    do
    :: (steps < MAX_STEPS && !win) ->
        steps++;
        if
        :: (y > 0 && wall[((y-1)*W + x)] == 0 && visited[((y-1)*W + x)] == 0) -> y = y-1; visited[(y*W + x)] = 1; last_move = 1; printf("MOVE %d\n", last_move)
        :: (y+1 < H && wall[((y+1)*W + x)] == 0 && visited[((y+1)*W + x)] == 0) -> y = y+1; visited[(y*W + x)] = 1; last_move = 2; printf("MOVE %d\n", last_move)
        :: (x > 0 && wall[(y*W + (x-1))] == 0 && visited[(y*W + (x-1))] == 0) -> x = x-1; visited[(y*W + x)] = 1; last_move = 3; printf("MOVE %d\n", last_move)
        :: (x+1 < W && wall[(y*W + (x+1))] == 0 && visited[(y*W + (x+1))] == 0) -> x = x+1; visited[(y*W + x)] = 1; last_move = 4; printf("MOVE %d\n", last_move)
        fi;
        update_win();
    :: else -> break
    od;
}

ltl never_win { [](!win) }
