nodelay => 	nodelay(menu, TRUE);
keypad => 	keypad(menu, TRUE);
initscr => 	initscr();
echo => 	noecho();
nonl => 	nonl();
cbreak => 	cbreak();
curs_set => 	curs_set(0);
start_color => 	start_color();
init_pair => 	init_pair(CP_STANDARD,	COLOR_WHITE,	COLOR_BLACK);
init_pair => 	init_pair(CP_SCALEHI,	COLOR_RED,	COLOR_BLACK);
init_pair => 	init_pair(CP_SCALEMID,	COLOR_YELLOW,	COLOR_BLACK);
init_pair => 	init_pair(CP_SCALELOW,	COLOR_GREEN,	COLOR_BLACK);
init_pair => 	init_pair(CP_WTITLE,	COLOR_CYAN,	COLOR_BLACK);
init_pair => 	init_pair(CP_INACTIVE,	COLOR_CYAN,	COLOR_BLACK);
init_pair => 	init_pair(CP_ACTIVE,	COLOR_CYAN,	COLOR_BLUE);
init_pair => 	init_pair(CP_STATSIG,	  COLOR_GREEN,	COLOR_BLACK);
init_pair => 	init_pair(CP_STATNOISE,	  COLOR_RED,	COLOR_BLACK);
init_pair => 	init_pair(CP_STATSNR,	  COLOR_BLUE,	COLOR_BLUE);
init_pair => 	init_pair(CP_STATBKG,	  COLOR_BLUE,	COLOR_BLACK);
init_pair => 	init_pair(CP_STATSIG_S,	  COLOR_GREEN,	COLOR_BLUE);
init_pair => 	init_pair(CP_STATNOISE_S, COLOR_RED,	COLOR_BLUE);
init_pair => 	init_pair(CP_PREF_NORMAL, COLOR_WHITE,	COLOR_BLACK);
init_pair => 	init_pair(CP_PREF_SELECT, COLOR_WHITE,	COLOR_BLUE);
init_pair => 	init_pair(CP_PREF_ARROW,  COLOR_RED,	COLOR_BLACK);
init_pair => 	init_pair(CP_SCAN_CRYPT,  COLOR_RED,	COLOR_BLACK);
init_pair => 	init_pair(CP_SCAN_UNENC,  COLOR_GREEN,	COLOR_BLACK);
init_pair => 	init_pair(CP_SCAN_NON_AP, COLOR_YELLOW, COLOR_BLACK);
endwin => 	endwin();