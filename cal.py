from termcolor import cprint
from pprint import pprint

table = [[k * n**2 for k in range(1,21)] for n in range(1,21)]

for n in range(0,21):
    s = "{:>4}".format(str(n))
    print(s, end=' ')
print()
for n in range(0,20):
    s = "{:>4}".format(str(n+1))
    print(s, end=' ')
    for k in range(0,20):
        s = "{:>4}".format(str(table[n][k]))
        if table[n][k] > 300:
            cprint(s, 'red', 'on_cyan', end=' ')
        else:
            print(s, end=' ')
    print()
