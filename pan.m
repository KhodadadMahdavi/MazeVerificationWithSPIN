#define rand	pan_rand
#define pthread_equal(a,b)	((a)==(b))
#if defined(HAS_CODE) && defined(VERBOSE)
	#ifdef BFS_PAR
		bfs_printf("Pr: %d Tr: %d\n", II, t->forw);
	#else
		cpu_printf("Pr: %d Tr: %d\n", II, t->forw);
	#endif
#endif
	switch (t->forw) {
	default: Uerror("bad forward move");
	case 0:	/* if without executable clauses */
		continue;
	case 1: /* generic 'goto' or 'skip' */
		IfNotBlocked
		_m = 3; goto P999;
	case 2: /* generic 'else' */
		IfNotBlocked
		if (trpt->o_pm&1) continue;
		_m = 3; goto P999;

		 /* CLAIM never_win */
	case 3: // STATE 1 - _spin_nvr.tmp:3 - [(!(!(win)))] (6:0:0 - 1)
		
#if defined(VERI) && !defined(NP)
#if NCLAIMS>1
		{	static int reported1 = 0;
			if (verbose && !reported1)
			{	int nn = (int) ((Pclaim *)pptr(0))->_n;
				printf("depth %ld: Claim %s (%d), state %d (line %d)\n",
					depth, procname[spin_c_typ[nn]], nn, (int) ((Pclaim *)pptr(0))->_p, src_claim[ (int) ((Pclaim *)pptr(0))->_p ]);
				reported1 = 1;
				fflush(stdout);
		}	}
#else
		{	static int reported1 = 0;
			if (verbose && !reported1)
			{	printf("depth %d: Claim, state %d (line %d)\n",
					(int) depth, (int) ((Pclaim *)pptr(0))->_p, src_claim[ (int) ((Pclaim *)pptr(0))->_p ]);
				reported1 = 1;
				fflush(stdout);
		}	}
#endif
#endif
		reached[1][1] = 1;
		if (!( !( !(((int)now.win)))))
			continue;
		/* merge: assert(!(!(!(win))))(0, 2, 6) */
		reached[1][2] = 1;
		spin_assert( !( !( !(((int)now.win)))), " !( !( !(win)))", II, tt, t);
		/* merge: .(goto)(0, 7, 6) */
		reached[1][7] = 1;
		;
		_m = 3; goto P999; /* 2 */
	case 4: // STATE 10 - _spin_nvr.tmp:8 - [-end-] (0:0:0 - 1)
		
#if defined(VERI) && !defined(NP)
#if NCLAIMS>1
		{	static int reported10 = 0;
			if (verbose && !reported10)
			{	int nn = (int) ((Pclaim *)pptr(0))->_n;
				printf("depth %ld: Claim %s (%d), state %d (line %d)\n",
					depth, procname[spin_c_typ[nn]], nn, (int) ((Pclaim *)pptr(0))->_p, src_claim[ (int) ((Pclaim *)pptr(0))->_p ]);
				reported10 = 1;
				fflush(stdout);
		}	}
#else
		{	static int reported10 = 0;
			if (verbose && !reported10)
			{	printf("depth %d: Claim, state %d (line %d)\n",
					(int) depth, (int) ((Pclaim *)pptr(0))->_p, src_claim[ (int) ((Pclaim *)pptr(0))->_p ]);
				reported10 = 1;
				fflush(stdout);
		}	}
#endif
#endif
		reached[1][10] = 1;
		if (!delproc(1, II)) continue;
		_m = 3; goto P999; /* 0 */

		 /* PROC Player */
	case 5: // STATE 1 - promela/maze.pml:23 - [x = 1] (0:0:1 - 1)
		IfNotBlocked
		reached[0][1] = 1;
		(trpt+1)->bup.oval = ((int)now.x);
		now.x = 1;
#ifdef VAR_RANGES
		logval("x", ((int)now.x));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 6: // STATE 2 - promela/maze.pml:23 - [y = 1] (0:0:1 - 1)
		IfNotBlocked
		reached[0][2] = 1;
		(trpt+1)->bup.oval = ((int)now.y);
		now.y = 1;
#ifdef VAR_RANGES
		logval("y", ((int)now.y));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 7: // STATE 3 - promela/maze.pml:24 - [visited[((y*15)+x)] = 1] (0:0:1 - 1)
		IfNotBlocked
		reached[0][3] = 1;
		(trpt+1)->bup.oval = ((int)now.visited[ Index(((((int)now.y)*15)+((int)now.x)), 225) ]);
		now.visited[ Index(((now.y*15)+now.x), 225) ] = 1;
#ifdef VAR_RANGES
		logval("visited[((y*15)+x)]", ((int)now.visited[ Index(((((int)now.y)*15)+((int)now.x)), 225) ]));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 8: // STATE 4 - promela/maze.pml:17 - [(((x==13)&&(y==13)))] (0:0:0 - 1)
		IfNotBlocked
		reached[0][4] = 1;
		if (!(((((int)now.x)==13)&&(((int)now.y)==13))))
			continue;
		_m = 3; goto P999; /* 0 */
	case 9: // STATE 5 - promela/maze.pml:17 - [win = 1] (0:0:1 - 1)
		IfNotBlocked
		reached[0][5] = 1;
		(trpt+1)->bup.oval = ((int)now.win);
		now.win = 1;
#ifdef VAR_RANGES
		logval("win", ((int)now.win));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 10: // STATE 11 - promela/maze.pml:27 - [(((steps<2000)&&!(win)))] (0:0:0 - 1)
		IfNotBlocked
		reached[0][11] = 1;
		if (!(((now.steps<2000)&& !(((int)now.win)))))
			continue;
		_m = 3; goto P999; /* 0 */
	case 11: // STATE 12 - promela/maze.pml:28 - [steps = (steps+1)] (0:0:1 - 1)
		IfNotBlocked
		reached[0][12] = 1;
		(trpt+1)->bup.oval = now.steps;
		now.steps = (now.steps+1);
#ifdef VAR_RANGES
		logval("steps", now.steps);
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 12: // STATE 13 - promela/maze.pml:30 - [((((y>0)&&(wall[(((y-1)*15)+x)]==0))&&(visited[(((y-1)*15)+x)]==0)))] (0:0:0 - 1)
		IfNotBlocked
		reached[0][13] = 1;
		if (!((((((int)now.y)>0)&&(((int)now.wall[ Index((((((int)now.y)-1)*15)+((int)now.x)), 225) ])==0))&&(((int)now.visited[ Index((((((int)now.y)-1)*15)+((int)now.x)), 225) ])==0))))
			continue;
		_m = 3; goto P999; /* 0 */
	case 13: // STATE 14 - promela/maze.pml:30 - [y = (y-1)] (0:0:1 - 1)
		IfNotBlocked
		reached[0][14] = 1;
		(trpt+1)->bup.oval = ((int)now.y);
		now.y = (((int)now.y)-1);
#ifdef VAR_RANGES
		logval("y", ((int)now.y));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 14: // STATE 15 - promela/maze.pml:30 - [visited[((y*15)+x)] = 1] (0:0:1 - 1)
		IfNotBlocked
		reached[0][15] = 1;
		(trpt+1)->bup.oval = ((int)now.visited[ Index(((((int)now.y)*15)+((int)now.x)), 225) ]);
		now.visited[ Index(((now.y*15)+now.x), 225) ] = 1;
#ifdef VAR_RANGES
		logval("visited[((y*15)+x)]", ((int)now.visited[ Index(((((int)now.y)*15)+((int)now.x)), 225) ]));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 15: // STATE 16 - promela/maze.pml:30 - [last_move = 1] (0:0:1 - 1)
		IfNotBlocked
		reached[0][16] = 1;
		(trpt+1)->bup.oval = ((int)last_move);
		last_move = 1;
#ifdef VAR_RANGES
		logval("last_move", ((int)last_move));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 16: // STATE 17 - promela/maze.pml:30 - [printf('MOVE %d\\n',last_move)] (0:0:0 - 1)
		IfNotBlocked
		reached[0][17] = 1;
		Printf("MOVE %d\n", ((int)last_move));
		_m = 3; goto P999; /* 0 */
	case 17: // STATE 18 - promela/maze.pml:31 - [(((((y+1)<15)&&(wall[(((y+1)*15)+x)]==0))&&(visited[(((y+1)*15)+x)]==0)))] (0:0:0 - 1)
		IfNotBlocked
		reached[0][18] = 1;
		if (!(((((((int)now.y)+1)<15)&&(((int)now.wall[ Index((((((int)now.y)+1)*15)+((int)now.x)), 225) ])==0))&&(((int)now.visited[ Index((((((int)now.y)+1)*15)+((int)now.x)), 225) ])==0))))
			continue;
		_m = 3; goto P999; /* 0 */
	case 18: // STATE 19 - promela/maze.pml:31 - [y = (y+1)] (0:0:1 - 1)
		IfNotBlocked
		reached[0][19] = 1;
		(trpt+1)->bup.oval = ((int)now.y);
		now.y = (((int)now.y)+1);
#ifdef VAR_RANGES
		logval("y", ((int)now.y));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 19: // STATE 20 - promela/maze.pml:31 - [visited[((y*15)+x)] = 1] (0:0:1 - 1)
		IfNotBlocked
		reached[0][20] = 1;
		(trpt+1)->bup.oval = ((int)now.visited[ Index(((((int)now.y)*15)+((int)now.x)), 225) ]);
		now.visited[ Index(((now.y*15)+now.x), 225) ] = 1;
#ifdef VAR_RANGES
		logval("visited[((y*15)+x)]", ((int)now.visited[ Index(((((int)now.y)*15)+((int)now.x)), 225) ]));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 20: // STATE 21 - promela/maze.pml:31 - [last_move = 2] (0:0:1 - 1)
		IfNotBlocked
		reached[0][21] = 1;
		(trpt+1)->bup.oval = ((int)last_move);
		last_move = 2;
#ifdef VAR_RANGES
		logval("last_move", ((int)last_move));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 21: // STATE 22 - promela/maze.pml:31 - [printf('MOVE %d\\n',last_move)] (0:0:0 - 1)
		IfNotBlocked
		reached[0][22] = 1;
		Printf("MOVE %d\n", ((int)last_move));
		_m = 3; goto P999; /* 0 */
	case 22: // STATE 23 - promela/maze.pml:32 - [((((x>0)&&(wall[((y*15)+(x-1))]==0))&&(visited[((y*15)+(x-1))]==0)))] (0:0:0 - 1)
		IfNotBlocked
		reached[0][23] = 1;
		if (!((((((int)now.x)>0)&&(((int)now.wall[ Index(((((int)now.y)*15)+(((int)now.x)-1)), 225) ])==0))&&(((int)now.visited[ Index(((((int)now.y)*15)+(((int)now.x)-1)), 225) ])==0))))
			continue;
		_m = 3; goto P999; /* 0 */
	case 23: // STATE 24 - promela/maze.pml:32 - [x = (x-1)] (0:0:1 - 1)
		IfNotBlocked
		reached[0][24] = 1;
		(trpt+1)->bup.oval = ((int)now.x);
		now.x = (((int)now.x)-1);
#ifdef VAR_RANGES
		logval("x", ((int)now.x));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 24: // STATE 25 - promela/maze.pml:32 - [visited[((y*15)+x)] = 1] (0:0:1 - 1)
		IfNotBlocked
		reached[0][25] = 1;
		(trpt+1)->bup.oval = ((int)now.visited[ Index(((((int)now.y)*15)+((int)now.x)), 225) ]);
		now.visited[ Index(((now.y*15)+now.x), 225) ] = 1;
#ifdef VAR_RANGES
		logval("visited[((y*15)+x)]", ((int)now.visited[ Index(((((int)now.y)*15)+((int)now.x)), 225) ]));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 25: // STATE 26 - promela/maze.pml:32 - [last_move = 3] (0:0:1 - 1)
		IfNotBlocked
		reached[0][26] = 1;
		(trpt+1)->bup.oval = ((int)last_move);
		last_move = 3;
#ifdef VAR_RANGES
		logval("last_move", ((int)last_move));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 26: // STATE 27 - promela/maze.pml:32 - [printf('MOVE %d\\n',last_move)] (0:0:0 - 1)
		IfNotBlocked
		reached[0][27] = 1;
		Printf("MOVE %d\n", ((int)last_move));
		_m = 3; goto P999; /* 0 */
	case 27: // STATE 28 - promela/maze.pml:33 - [(((((x+1)<15)&&(wall[((y*15)+(x+1))]==0))&&(visited[((y*15)+(x+1))]==0)))] (0:0:0 - 1)
		IfNotBlocked
		reached[0][28] = 1;
		if (!(((((((int)now.x)+1)<15)&&(((int)now.wall[ Index(((((int)now.y)*15)+(((int)now.x)+1)), 225) ])==0))&&(((int)now.visited[ Index(((((int)now.y)*15)+(((int)now.x)+1)), 225) ])==0))))
			continue;
		_m = 3; goto P999; /* 0 */
	case 28: // STATE 29 - promela/maze.pml:33 - [x = (x+1)] (0:0:1 - 1)
		IfNotBlocked
		reached[0][29] = 1;
		(trpt+1)->bup.oval = ((int)now.x);
		now.x = (((int)now.x)+1);
#ifdef VAR_RANGES
		logval("x", ((int)now.x));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 29: // STATE 30 - promela/maze.pml:33 - [visited[((y*15)+x)] = 1] (0:0:1 - 1)
		IfNotBlocked
		reached[0][30] = 1;
		(trpt+1)->bup.oval = ((int)now.visited[ Index(((((int)now.y)*15)+((int)now.x)), 225) ]);
		now.visited[ Index(((now.y*15)+now.x), 225) ] = 1;
#ifdef VAR_RANGES
		logval("visited[((y*15)+x)]", ((int)now.visited[ Index(((((int)now.y)*15)+((int)now.x)), 225) ]));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 30: // STATE 31 - promela/maze.pml:33 - [last_move = 4] (0:0:1 - 1)
		IfNotBlocked
		reached[0][31] = 1;
		(trpt+1)->bup.oval = ((int)last_move);
		last_move = 4;
#ifdef VAR_RANGES
		logval("last_move", ((int)last_move));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 31: // STATE 32 - promela/maze.pml:33 - [printf('MOVE %d\\n',last_move)] (0:0:0 - 1)
		IfNotBlocked
		reached[0][32] = 1;
		Printf("MOVE %d\n", ((int)last_move));
		_m = 3; goto P999; /* 0 */
	case 32: // STATE 35 - promela/maze.pml:17 - [(((x==13)&&(y==13)))] (0:0:0 - 1)
		IfNotBlocked
		reached[0][35] = 1;
		if (!(((((int)now.x)==13)&&(((int)now.y)==13))))
			continue;
		_m = 3; goto P999; /* 0 */
	case 33: // STATE 36 - promela/maze.pml:17 - [win = 1] (0:0:1 - 1)
		IfNotBlocked
		reached[0][36] = 1;
		(trpt+1)->bup.oval = ((int)now.win);
		now.win = 1;
#ifdef VAR_RANGES
		logval("win", ((int)now.win));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 34: // STATE 47 - promela/maze.pml:38 - [-end-] (0:0:0 - 3)
		IfNotBlocked
		reached[0][47] = 1;
		if (!delproc(1, II)) continue;
		_m = 3; goto P999; /* 0 */
	case  _T5:	/* np_ */
		if (!((!(trpt->o_pm&4) && !(trpt->tau&128))))
			continue;
		/* else fall through */
	case  _T2:	/* true */
		_m = 3; goto P999;
#undef rand
	}

