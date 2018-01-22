import matplotlib.pyplot as plt
import numpy as np
from mpl_toolkits.mplot3d import Axes3D

with open('exp result/timeout_log.txt') as fp:
    s = fp.read()
    stats = eval('['+s[:-1]+']')

lins_range = [30,40,50,60,80,100]
omega_range = [5,6,8,10]

record = {lins: {omega: 0 for omega in omega_range} for lins in lins_range}
for lins, omega, k, d, r in stats:
    record[lins][omega] += 1

print((" "*3 + "{:>3} " * len(omega_range)).format(*omega_range))
for lins, vals in record.items():
    print(("{:>3}" + "{:>3} " * len(vals)).format(lins, *vals.values()))

fig = plt.figure(figsize=(6, 6))
ax = fig.add_subplot(111, projection='3d')

coordinates = np.meshgrid(np.arange(len(omega_range)), np.arange(len(lins_range)))

x = coordinates[0].ravel()
y = coordinates[1].ravel()
z = np.zeros(len(omega_range) * len(lins_range))

dx = np.ones(len(omega_range) * len(lins_range))
dy = np.ones(len(omega_range) * len(lins_range))
dz = [v for vs in record.values() for v in vs.values()]

ax.bar3d(x, y, z, dx, dy, dz, shade=True, edgecolor='black', linewidth=1.5)

ax.set_title('Timeout(=15m) result out of 100 trials')
ax.set_xlabel('|omega|')
ax.set_ylabel('|lins|')
ax.set_zlabel('#timeout')

ax.set_xticks(range(len(omega_range)))
ax.set_yticks([i+0.5 for i in range(len(lins_range))])
ax.set_zticks(range(0,101,10))

ax.set_xticklabels(omega_range)
ax.set_yticklabels(lins_range)

ax.view_init(10, -140)

plt.savefig("bar3d.svg", format="svg")
#plt.show()
