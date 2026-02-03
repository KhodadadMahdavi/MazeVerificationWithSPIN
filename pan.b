	switch (t->back) {
	default: Uerror("bad return move");
	case  0: goto R999; /* nothing to undo */

		 /* CLAIM never_win */
;
		
	case 3: // STATE 1
		goto R999;

	case 4: // STATE 10
		;
		p_restor(II);
		;
		;
		goto R999;

		 /* PROC Player */

	case 5: // STATE 1
		;
		now.x = trpt->bup.oval;
		;
		goto R999;

	case 6: // STATE 2
		;
		now.y = trpt->bup.oval;
		;
		goto R999;

	case 7: // STATE 3
		;
		now.visited[ Index(((now.y*15)+now.x), 225) ] = trpt->bup.oval;
		;
		goto R999;
;
		;
		
	case 9: // STATE 5
		;
		now.win = trpt->bup.oval;
		;
		goto R999;
;
		;
		
	case 11: // STATE 12
		;
		now.steps = trpt->bup.oval;
		;
		goto R999;
;
		;
		
	case 13: // STATE 14
		;
		now.y = trpt->bup.oval;
		;
		goto R999;

	case 14: // STATE 15
		;
		now.visited[ Index(((now.y*15)+now.x), 225) ] = trpt->bup.oval;
		;
		goto R999;

	case 15: // STATE 16
		;
		last_move = trpt->bup.oval;
		;
		goto R999;
;
		;
		;
		;
		
	case 18: // STATE 19
		;
		now.y = trpt->bup.oval;
		;
		goto R999;

	case 19: // STATE 20
		;
		now.visited[ Index(((now.y*15)+now.x), 225) ] = trpt->bup.oval;
		;
		goto R999;

	case 20: // STATE 21
		;
		last_move = trpt->bup.oval;
		;
		goto R999;
;
		;
		;
		;
		
	case 23: // STATE 24
		;
		now.x = trpt->bup.oval;
		;
		goto R999;

	case 24: // STATE 25
		;
		now.visited[ Index(((now.y*15)+now.x), 225) ] = trpt->bup.oval;
		;
		goto R999;

	case 25: // STATE 26
		;
		last_move = trpt->bup.oval;
		;
		goto R999;
;
		;
		;
		;
		
	case 28: // STATE 29
		;
		now.x = trpt->bup.oval;
		;
		goto R999;

	case 29: // STATE 30
		;
		now.visited[ Index(((now.y*15)+now.x), 225) ] = trpt->bup.oval;
		;
		goto R999;

	case 30: // STATE 31
		;
		last_move = trpt->bup.oval;
		;
		goto R999;
;
		;
		;
		;
		
	case 33: // STATE 36
		;
		now.win = trpt->bup.oval;
		;
		goto R999;

	case 34: // STATE 47
		;
		p_restor(II);
		;
		;
		goto R999;
	}

