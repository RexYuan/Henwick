import matplotlib.pyplot as plt
import numpy as np
from mpl_toolkits.mplot3d import Axes3D

with open('new_timeout_log.txt') as fp:
    s = fp.read()
    stats = eval('['+s[:-1]+']')

lins_range = [30,40,50,60,70,80,90,100]
omega_range = [5,6,7,8,9,10]
poset_range = set()
diameter_range = set()

record = {lins: {omega: 0 for omega in omega_range} for lins in lins_range}
for lins, omega, k, d, r in stats:
    record[lins][omega] += 1
    poset_range.add(k)
    diameter_range.add(d)

poset_range = sorted(list(poset_range))
diameter_range = sorted(list(diameter_range))
poset_omega_record = {poset: {omega: 0 for omega in omega_range} for poset in poset_range}
poset_diameter_record = {poset: {d: 0 for d in diameter_range} for poset in poset_range}
poset_lin_record = {poset: {l: 0 for l in lins_range} for poset in poset_range}
diameter_omega_record = {poset: {omega: 0 for omega in omega_range} for poset in diameter_range}
diameter_lin_record = {poset: {l: 0 for l in lins_range} for poset in diameter_range}

for lins, omega, k, d, r in stats:
    poset_omega_record[k][omega] += 1
    poset_diameter_record[k][d] += 1
    poset_lin_record[k][lins] += 1
    diameter_omega_record[d][omega] += 1
    diameter_lin_record[d][lins] += 1

#print((" "*3 + "{:>3} " * len(omega_range)).format(*omega_range))
#for lins, vals in record.items():
#    print(("{:>3}" + "{:>3} " * len(vals)).format(lins, *vals.values()))
#print((" "*3 + "{:>4} " * len(omega_range)).format(*omega_range))
#for lins, vals in poset_omega_record.items():
#    print(("{:>3}" + "{:>4} " * len(vals)).format(lins, *vals.values()))

#fig = plt.figure(figsize=(32, 36))
#ax = fig.add_subplot(321, projection='3d')
fig = plt.figure(figsize=(8, 8))
ax = fig.add_subplot(111, projection='3d')

coordinates = np.meshgrid(np.arange(len(omega_range)), np.arange(len(lins_range)))

x = coordinates[0].ravel()
y = coordinates[1].ravel()
z = np.zeros(len(omega_range) * len(lins_range))

dx = np.ones(len(omega_range) * len(lins_range))
dy = np.ones(len(omega_range) * len(lins_range))
dz = [v for vs in record.values() for v in vs.values()]

# specifying colors: https://matplotlib.org/examples/color/named_colors.html
ax.bar3d(x, y, z, dx, dy, dz, shade=True, edgecolor='black', linewidth=1.5, color='gainsboro')

#ax.set_title('#Timeout(=15m) result out of 100 trials')
ax.set_xlabel('universe size')
ax.set_ylabel('# of linearizations')
ax.set_zlabel('# of timeouts')

ax.set_xticks([i+0.5 for i in range(len(omega_range))])
ax.set_yticks([i+0.5 for i in range(len(lins_range))])
ax.set_zticks(range(0,101,10))

ax.set_xticklabels(omega_range)
ax.set_yticklabels(lins_range)

ax.view_init(8.75, -140)
'''
#####
ax = fig.add_subplot(322, projection='3d')

coordinates = np.meshgrid(np.arange(len(omega_range)), np.arange(len(poset_range)))

x = coordinates[0].ravel()
y = coordinates[1].ravel()
z = np.zeros(len(omega_range) * len(poset_range))

dx = np.ones(len(omega_range) * len(poset_range))
dy = np.ones(len(omega_range) * len(poset_range))
dz = [v for vs in poset_omega_record.values() for v in vs.values()]

ax.bar3d(x, y, z, dx, dy, dz, shade=True, edgecolor='black', linewidth=1.5)

ax.set_title('Timeout(=15m) result out of 100 trials')
ax.set_xlabel('universe size')
ax.set_ylabel('# of poset')
ax.set_zlabel('# of timeout')
ax.set_xlabel()
ax.set_ylabel('linearization size')
ax.set_zlabel('# of timeout')

ax.set_xticks([i+0.5 for i in range(len(omega_range))])
ax.set_yticks([i+0.5 for i in range(len(poset_range))])
ax.set_zticks(range(0,501,100))

ax.set_xticklabels(omega_range)
ax.set_yticklabels(poset_range)

ax.view_init(8.75, 140)

#####
ax = fig.add_subplot(323, projection='3d')

coordinates = np.meshgrid(np.arange(len(diameter_range)), np.arange(len(poset_range)))

x = coordinates[0].ravel()
y = coordinates[1].ravel()
z = np.zeros(len(diameter_range) * len(poset_range))

dx = np.ones(len(diameter_range) * len(poset_range))
dy = np.ones(len(diameter_range) * len(poset_range))
dz = [v for vs in poset_diameter_record.values() for v in vs.values()]

ax.bar3d(x, y, z, dx, dy, dz, shade=True, edgecolor='black', linewidth=1.5)

ax.set_title('Timeout(=15m) result out of 100 trials')
ax.set_xlabel('diameter(interval=4)')
ax.set_ylabel('#poset')
ax.set_zlabel('#timeout')

ax.set_xticks([i+0.5 for i in range(0,len(diameter_range),4)])
ax.set_yticks([i+0.5 for i in range(len(poset_range))])
ax.set_zticks(range(0,101,10))

ax.set_xticklabels(diameter_range)
ax.set_yticklabels(poset_range)

ax.view_init(8.75, 50)

#####
ax = fig.add_subplot(324, projection='3d')

coordinates = np.meshgrid(np.arange(len(lins_range)), np.arange(len(poset_range)))

x = coordinates[0].ravel()
y = coordinates[1].ravel()
z = np.zeros(len(lins_range) * len(poset_range))

dx = np.ones(len(lins_range) * len(poset_range))
dy = np.ones(len(lins_range) * len(poset_range))
dz = [v for vs in poset_lin_record.values() for v in vs.values()]

ax.bar3d(x, y, z, dx, dy, dz, shade=True, edgecolor='black', linewidth=1.5)

ax.set_title('Timeout(=15m) result out of 100 trials')
ax.set_xlabel('|lin|')
ax.set_ylabel('#poset')
ax.set_zlabel('#timeout')

ax.set_xticks([i+0.5 for i in range(len(lins_range))])
ax.set_yticks([i+0.5 for i in range(len(poset_range))])
ax.set_zticks(range(0,401,100))

ax.set_xticklabels(lins_range)
ax.set_yticklabels(poset_range)

ax.view_init(8.75, 140)

#####
ax = fig.add_subplot(325, projection='3d')

coordinates = np.meshgrid(np.arange(len(omega_range)), np.arange(len(diameter_range)))

x = coordinates[0].ravel()
y = coordinates[1].ravel()
z = np.zeros(len(omega_range) * len(diameter_range))

dx = np.ones(len(omega_range) * len(diameter_range))
dy = np.ones(len(omega_range) * len(diameter_range))
dz = [v for vs in diameter_omega_record.values() for v in vs.values()]

ax.bar3d(x, y, z, dx, dy, dz, shade=True, edgecolor='black', linewidth=1.5)

ax.set_title('Timeout(=15m) result out of 100 trials')
ax.set_xlabel('|omega|')
ax.set_ylabel('diameter(interval=4)')
ax.set_zlabel('#timeout')

ax.set_xticks([i+0.5 for i in range(len(omega_range))])
ax.set_yticks([i+0.5 for i in range(0,len(diameter_range),4)])
ax.set_zticks(range(0,151,50))

ax.set_xticklabels(omega_range)
ax.set_yticklabels(diameter_range)

ax.view_init(8.75, 50)

#####
ax = fig.add_subplot(326, projection='3d')

coordinates = np.meshgrid(np.arange(len(lins_range)), np.arange(len(diameter_range)))

x = coordinates[0].ravel()
y = coordinates[1].ravel()
z = np.zeros(len(lins_range) * len(diameter_range))

dx = np.ones(len(lins_range) * len(diameter_range))
dy = np.ones(len(lins_range) * len(diameter_range))
dz = [v for vs in diameter_lin_record.values() for v in vs.values()]

ax.bar3d(x, y, z, dx, dy, dz, shade=True, edgecolor='black', linewidth=1.5)

ax.set_title('Timeout(=15m) result out of 100 trials')
ax.set_xlabel('|lin|')
ax.set_ylabel('diameter(interval=4)')
ax.set_zlabel('#timeout')

ax.set_xticks([i+0.5 for i in range(len(lins_range))])
ax.set_yticks([i+0.5 for i in range(0,len(diameter_range),4)])
ax.set_zticks(range(0,51,10))

ax.set_xticklabels(lins_range)
ax.set_yticklabels(diameter_range)

ax.view_init(8.75, 140)
###

plt.savefig("paper_summary_bar3d.svg", format="svg")
#plt.show()
'''
plt.savefig("../papers/images/bar3d.svg", format="svg", transparent=True)
#plt.show()
