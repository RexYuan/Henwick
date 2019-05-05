initscr =>   if (!initscr())
keypad =>   keypad(stdscr, true);
cbreak =>   cbreak();
echo =>   noecho();
nonl =>   nonl();
typeahead =>   typeahead(-1); /* simulate smooth scrolling */
meta =>   meta(stdscr, true);
endwin =>     endwin();
