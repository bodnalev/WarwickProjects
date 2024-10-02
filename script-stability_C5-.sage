from sage.algebras.flag_algebras import *

def test_identify(n, ftype_points, edges, C0, C1, C2):
    return colored_identify(2, [[0], [1, 2]], n, ftype_points, edges=edges, C0=C0, C1=C1, C2=C2)

def test_generate(n):
    return colored_generate(2, [[0], [1, 2]], n)

TT = CombinatorialTheory("12ColGraph", test_generate, test_identify, edges=2, C0=1, C1=1, C2=1)

# Exclude triangles 6.1.6 (1)
# f = TT.generate_flags(3)
# exclude = list(f[-6:])
exclude = []
exclude += [
    # TT(3, edges=[[0, 1], [0, 2], [1, 2]], C0=[[0], [1], [2]], C1=[], C2=[]),
    # TT(3, edges=[[0, 1], [0, 2], [1, 2]], C0=[[0], [1]], C1=[[2]], C2=[]),
    # TT(3, edges=[[0, 1], [0, 2], [1, 2]], C0=[[0]], C1=[[1], [2]], C2=[]),
    TT(3, edges=[[0, 1], [0, 2], [1, 2]], C0=[[0]], C1=[[1]], C2=[[2]]),
    # TT(3, edges=[[0, 1], [0, 2], [1, 2]], C0=[], C1=[[0], [1], [2]], C2=[]),
    # TT(3, edges=[[0, 1], [0, 2], [1, 2]], C0=[], C1=[[0], [1]], C2=[[2]])
]

# Exclude disjoint edges 6.1.6 (3)
# The edges share a vertex
exclude += [
    TT(3, edges=[[0, 2], [1, 2]], C0=[[0]], C1=[[1]], C2=[[2]]),
    TT(3, edges=[[0, 2], [1, 2]], C0=[[2]], C1=[[0]], C2=[[1]])
    ]
# The edges are vertex disjoint
exclude += [
    TT(4, edges=[[0, 2], [1, 3]], C0=[[0], [1]], C1=[[2]], C2=[[3]]),
    TT(4, edges=[[0, 2], [1, 3]], C0=[[0]], C1=[[1], [2]], C2=[[3]])
    ]
TT.exclude(exclude)

# Exclude special paths 6.1.6 (2)
f = TT.generate_flags(4)
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
    pas = True
    for i in range(4):
        for j in range(i + 1, 4):
            if degree[i] == degree[j] == 1 and (([i] in ff.blocks()['C0'] and [j] in ff.blocks()['C0']) or ([i] in ff.blocks()['C1'] and [j] in ff.blocks()['C1']) or ([i] in ff.blocks()['C2'] and [j] in ff.blocks()['C2'])):
                pas = False
    if not pas:
        continue
    # exclude.append(ff)
    # print(ff)
exclude += [
    TT(4, edges=[[0, 2], [0, 3], [1, 3]], C0=[[0], [3]], C1=[[1]], C2=[[2]]),
    TT(4, edges=[[0, 2], [0, 3], [1, 3], [0, 1], [3, 2]], C0=[[0], [3]], C1=[[1]], C2=[[2]]),
    TT(4, edges=[[0, 2], [0, 3], [1, 3], [0, 1]], C0=[[0], [3]], C1=[[1]], C2=[[2]]),
    TT(4, edges=[[0, 2], [0, 3], [1, 3], [3, 2]], C0=[[0], [3]], C1=[[1]], C2=[[2]]),
    
    TT(4, edges=[[0, 2], [0, 3], [1, 3]], C0=[[1]], C1=[[0], [3]], C2=[[2]]),
    TT(4, edges=[[0, 2], [0, 3], [1, 3], [0, 1], [3, 2]], C0=[[1]], C1=[[0], [3]], C2=[[2]]),
    TT(4, edges=[[0, 2], [0, 3], [1, 3], [0, 1]], C0=[[1]], C1=[[0], [3]], C2=[[2]]),
    TT(4, edges=[[0, 2], [0, 3], [1, 3], [3, 2]], C0=[[1]], C1=[[0], [3]], C2=[[2]]),
]
TT.exclude(exclude)

# Assumptions
edge_12 = TT(2, edges=[[0, 1]], C0=[], C1=[[0]], C2=[[1]])
edge_01 = TT(2, edges=[[0, 1]], C0=[[0]], C1=[[1]], C2=[])
pairs_12 = TT(2, edges=[[0, 1]], C0=[], C1=[[0]], C2=[[1]]) + TT(2, edges=[], C0=[], C1=[[0]], C2=[[1]])
point = TT(1, edges = [], C0 = [[0]], C1 = [], C2 = [])
point2 = TT(1, edges = [], C0 = [], C1 = [[0]], C2 = [])
positives = [edge_12 - 1/2*edge_01, point - 1/3, point2 - 2/3, pairs_12 - 2/9]

# Missing edges (correct?)
M = 1 + TT(2, edges=[], C0=[], C1=[[0]], C2=[[1]]) - 1

# Bad edges (correct?)
B = 1
B += TT(2, edges=[[0, 1]], C0=[[0]], C1=[[1]], C2=[])
B += TT(2, edges=[[0, 1]], C0=[], C1=[[0], [1]], C2=[])
B -= 1

# print(M + B)

# Optimize (correct?)
# cons = TT.blowup_construction(target_size = 5, pattern_size = 3, symmetric=False, edges = [[1, 2]], C0 = [[0]], C1 = [[1]], C2 = [[2]])
x = TT.optimize(B - M, 5, maximize=True, positives = positives)
print(x)
