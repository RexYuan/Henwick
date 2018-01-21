import matplotlib.pyplot as plt
import numpy as np
from mpl_toolkits.mplot3d import Axes3D

with open('/Users/Rex/Desktop/result/timeout_log.txt') as fp:
    s = fp.read()
    stats = eval('['+s[:-1]+']')
'''
lins = list(map(lambda l:l[0], stats))
omega = list(map(lambda l:l[1], stats))
k = list(map(lambda l:l[2], stats))
d = list(map(lambda l:l[3], stats))
r = list(map(lambda l:l[4], stats))
'''
# lins = 50, 60, 80, 100
# omega = 5, 6, 8 10
record = {lins: {omega: 0 for omega in [5,6,8,10]} for lins in [50,60,80,100]}
for lins, omega, k, d, r in stats:
    record[lins][omega] += 1

'''
fig = plt.figure(figsize=(8, 8))
ax = fig.add_subplot(111, projection='3d')

coordinates = np.meshgrid(np.arange(10), np.arange(10))

x = coordinates[0].ravel()
y = coordinates[1].ravel()
z = np.zeros(100)

dx = np.ones(100)
dy = np.ones(100)
dz = np.arange(100)

ax.bar3d(x, y, z, dx, dy, dz, shade=True)

plt.show()
'''
