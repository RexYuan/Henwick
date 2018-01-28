

with open('batch template.py') as fp:
    rest = fp.read()

i = 1
for ele in [5,6,7,8,9,10]:
    for lin in [30,40,50,60,70,80,90,100]:
        config = "batch = {batch};ele_count = {ele_count};lin_count = {lin_count}\n".format(batch=i, ele_count=ele, lin_count=lin)
        with open("new exp batch/batch{}.py".format(i), 'w') as fp:
            fp.write(config+rest)
        i += 1
        config = "batch = {batch};ele_count = {ele_count};lin_count = {lin_count}\n".format(batch=i, ele_count=ele, lin_count=lin)
        with open("new exp batch/batch{}.py".format(i), 'w') as fp:
            fp.write(config+rest)
        i += 1
