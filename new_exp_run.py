import os

for i in range(1,127):
    os.system("python3 new\ exp\ batch/batch{}.py &".format(i))
