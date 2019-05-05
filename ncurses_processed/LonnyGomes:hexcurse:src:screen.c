cbreak =>     cbreak();						/* allow cbreak()     */
echo =>     noecho();						/* disable echoing    */
raw =>     raw();
idlok => 	idlok(win, TRUE);				/* enable scrolling   */
keypad =>         keypad(win, TRUE);				/* enable the keypad  */
endwin =>     endwin(); 						/* end curses screen  */
initscr =>     if ((initscr()) == NULL)				/*couldn't init screen*/
endwin =>     endwin();						/* end curses screeen */
endwin =>     endwin();
endwin =>         endwin();
scrollok =>     scrollok(windows->hex, TRUE);                       /* allow scrolling    */
scrollok =>     scrollok(windows->ascii, TRUE);
scrollok =>     scrollok(windows->address, TRUE);
scrollok =>     scrollok(windows->hex, FALSE);                      /*disable scrolling   */
scrollok =>     scrollok(windows->ascii, FALSE);
scrollok =>     scrollok(windows->address, FALSE);
keypad =>     keypad(tmpwin, TRUE);
