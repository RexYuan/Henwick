initscr => 	initscr();
cbreak => 	cbreak();
echo => 	noecho();
curs_set => 	curs_set(0);
halfdelay => 	halfdelay(0);
nodelay => 	nodelay(stdscr, TRUE);
keypad => 	keypad(stdscr, TRUE);
start_color => 		start_color();
has_colors => 		opts->color = has_colors();
init_pair => 			init_pair(pair, color[pair].foreground, color[pair].background);
timeout => 	timeout(opts->refr_time * 1000);
endwin => 	endwin();
nodelay => 	nodelay(stdscr, FALSE);
timeout => 	timeout(99999);
nodelay => 	nodelay(stdscr, TRUE);
timeout => 	timeout(opts->refr_time * 1000);
nodelay => 	nodelay(stdscr, FALSE);
napms => 		napms(1000);
nodelay => 	nodelay(stdscr, TRUE);
init_pair => 		init_pair(DEFAULT_COLOR, COLOR_BLACK, COLOR_WHITE);
init_pair => 		init_pair(DEFAULT_COLOR, COLOR_BLACK, COLOR_WHITE);