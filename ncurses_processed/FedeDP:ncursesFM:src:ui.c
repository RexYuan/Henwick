initscr =>     initscr();
start_color =>     start_color();
init_pair =>     init_pair(1, COLOR_BLUE, -1);
init_pair =>     init_pair(2, COLOR_CYAN, -1);
init_pair =>     init_pair(3, COLOR_GREEN, -1);
init_pair =>     init_pair(4, COLOR_YELLOW, -1);
init_pair =>     init_pair(5, COLOR_RED, -1);
echo =>     noecho();
curs_set =>     curs_set(0);
raw =>     raw();
nodelay =>     nodelay(stdscr, TRUE);
keypad =>     keypad(info_win, TRUE);
nodelay =>     nodelay(info_win, TRUE);
endwin =>         endwin();
keypad =>     keypad(ps[win].mywin.fm, TRUE);
scrollok =>     scrollok(ps[win].mywin.fm, TRUE);
idlok =>     idlok(ps[win].mywin.fm, TRUE);
nodelay =>     nodelay(ps[win].mywin.fm, TRUE);
curs_set =>     curs_set(1);
curs_set =>             curs_set(1 + overtype_mode);
curs_set =>     curs_set(0);
