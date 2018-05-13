
import os

targets = {
    # initscr
    "initscr",
    "endwin",
    "isendwin",
    "newterm",
    "set_term",
    "delscreen",
    # inopts
    "cbreak",
    "nocbreak",
    "echo",
    "noecho",
    "halfdelay",
    "intrflush",
    "keypad",
    "meta",
    "nodelay",
    "raw",
    "noraw",
    "noqiflush",
    "qiflush",
    "notimeout",
    "timeout",
    "wtimeout",
    "typeahead",
    # outopts
    "clearok",
    "idlok",
    "idcok",
    "immedok",
    "leaveok",
    "setscrreg",
    "wsetscrreg",
    "scrollok",
    "nl",
    "nonl",
    # color
    "start_color",
    "has_colors",
    "can_change_color",
    "init_pair",
    "init_color",
    # kernel
    "def_prog_mode",
    "def_shell_mode",
    "reset_prog_mode",
    "reset_shell_mode",
    "resetty",
    "savetty",
    "getsyx",
    "setsyx",
    "ripoffline",
    "curs_set",
    "napms"
}

fs = os.listdir('ncurses')
for f in fs:
    if f == '.DS_Store':
        continue
    with open('ncurses_processed/'+f, 'w') as fp_processed:
        with open('ncurses/'+f, 'r') as fp:
            for line in fp:
                for t in targets:
                    if t+'(' in line:
                        fp_processed.write(t+' => '+line)
                        break
