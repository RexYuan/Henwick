
import poset_HnN, poset_partial

HNpc = poset_HnN.partial_cover
MYpc = poset_partial.partial_cover
tc = poset_HnN.trans_closure
rmtc = poset_partial.rm_trans_closure
ls = poset_partial.get_linearizations

def test(lins, target):
    rets = list(map(lambda x: rmtc(target,x), MYpc(lins, target)))
    for ret in rets:
        print(ret)
        #print(ls(target,tc(ret)))
    print()
    tmp = []
    x = HNpc(lins, target)
    while len(tmp) < len(rets):
        if x == False:
            print('e',end=' ')
        elif x[0] not in rets:
            print('n',end=' ')
        else:
            tmp.append(x[0])
        x = HNpc(lins, target)
    print()
    for t in tmp:
        print(t)
        #print(ls(target,tc(ret)))

# counter
lins1 = [
'afbced',
'afbecd',
'abfecd',
'bfaced',
'bafced',
'abfced',
'bacfed',
'abcfed',
'bacefd',
'abcefd'
]
print('test1')
test(lins1,'abfced')
print()

# cut
lins2 = [
'adbc',
'adcb',
'acdb',
'acbd',
'abcd'
]
print('test2')
test(lins2,'acdb')
print()

#long
lins3 = [
'abcdef',
'badcef',
'badcfe',
'abdcfe'
]
print('test3')
test(lins3,'badcfe')
print()

# many covers
lins4 = [
'abcdef',
'acbdef',
'acbdfe',
'acbfde',
'adcbef',
'acdbef',
'acdbfe',
'acdfbe'
]
print('test4')
test(lins4,'acbdef')
print()

# new way
lins5 = [
'abcdef',
'acbdfe',
'acbfde',
'acdbfe',
'acdfbe',
'adcbef'
]
print('test5')
test(lins5,'acbdfe')
print()

# paper
lins6 = [
'abcde',
'bacde',
'bcade',
'cbade',
'cabde',
'acbde',
'abced',
'baced',
'acbed',
'bcaed',
'cbaed'
]
print('test6')
test(lins6,'abced')
print()

# problem
lins7 = [
'adcb',
'acdb',
'acbd',
'abcd'
]
print('test7')
test(lins7,'acdb')
print()
