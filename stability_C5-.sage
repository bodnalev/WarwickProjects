from sage.algebras.flag_algebras import *

def test_identify(n, ftype_points, edges, C0, C1, C2):
    return colored_identify(2, [[0], [1, 2]], n, ftype_points, edges=edges, C0=C0, C1=C1, C2=C2)

def test_generate(n):
    return colored_generate(2, [[0], [1, 2]], n)

TT = CombinatorialTheory("12ColGraph", test_generate, test_identify, edges=2, C0=1, C1=1, C2=1)

# Exclude triangles 6.1.6 (1)
f = TT.generate_flags(3)
TT.exclude(f[-6:])

# Exclude disjoint edges 6.1.6 (3)
# The edges share a vertex
f = TT.generate_flags(3)
avoid = []
for ff in f:
    if len(ff.blocks()['edges']) != 2:
        continue
    yep = True
    for edge in ff.blocks()['edges']:
        for i in range(0, 3):
            if [edge[0]] in ff.blocks()['C'+str(i)] and [edge[1]] in ff.blocks()['C'+str(i)]:
                yep = False
    if not yep:
        continue
    if ff.blocks()['C0'] == [] or ff.blocks()['C1'] == [] or ff.blocks()['C2'] == []:
        continue
    avoid.append(ff)
TT.exclude(avoid)
# The edges are vertex disjoint
f = TT.generate_flags(4)
avoid = []
for ff in f:
    if len(ff.blocks()['edges']) != 2:
        continue
    yep = True
    for edge in ff.blocks()['edges']:
        for i in range(0, 3):
            if [edge[0]] in ff.blocks()['C'+str(i)] and [edge[1]] in ff.blocks()['C'+str(i)]:
                yep = False
    if not yep:
        continue
    if ff.blocks()['C0'] == [] or ff.blocks()['C1'] == [] or ff.blocks()['C2'] == []:
        continue
    if ff.blocks()['edges'] != [[0, 2], [1, 3]]:
        continue
    avoid.append(ff)
TT.exclude(avoid)

# Exclude special paths 6.1.6 (2)
f = TT.generate_flags(4)
avoid = []
for ff in f:
    if len(ff.blocks()['edges']) != 3:
        continue
    degree = [0, 0, 0, 0]
    for edge in ff.blocks()['edges']:
        for v in edge:
            degree[v] += 1
    if sorted(degree) != [1, 1, 2, 2]:
        continue
    if ff.blocks()['C0'] == [] or ff.blocks()['C1'] == [] or ff.blocks()['C2'] == []:
        continue
    avoid.append(ff)
TT.exclude(avoid)

# Assumptions
edge_12 = TT.generate_flags(2)[-1]
edge_01 = TT.generate_flags(2)[5]
positives = [edge_12 - edge_01]

# Missing edges (correct?)
M = 1 + edge_12 - 1

# Bad edges (correct?)
f = TT.generate_flags(2)[-4:-1]
B = 1
for ff in f:
    B += ff
B -= 1

# Optimize (correct?)
x = TT.optimize(B - M, 5, maximize=False, positives=positives)
print(x)
