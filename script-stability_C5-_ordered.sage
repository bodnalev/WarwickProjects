from sage.algebras.flag_algebras import *
import itertools

# Create the theory
def test_identify(n, ftype_points, edges, C0, C1, C2):
    return colored_identify(2, [[0], [1], [2]], n, ftype_points, edges=edges, C0=C0, C1=C1, C2=C2)

def test_generate(n):
    return colored_generate(2, [[0], [1], [2]], n)

TT = CombinatorialTheory("123graphs", test_generate, test_identify, edges=2, C0=1, C1=1, C2=1)

feasibles = []
for flag in TT.generate_flags(4):
    # Real edges
    edge_list = [sorted(x + [4]) for x in flag.blocks()['edges']]
    # Add rainbow edges
    for v1 in flag.blocks()['C0']:
        for v2 in flag.blocks()['C1']:
            for v3 in flag.blocks()['C2']:
                l = sorted([v1[0], v2[0], v3[0]])
                if l not in edge_list:
                    edge_list.append(l)
    # Look for C5-
    feasible = True
    for p in list(itertools.permutations([0, 1, 2, 3, 4])):
        if sorted([p[0], p[1], p[2]]) in edge_list and sorted([p[1], p[2], p[3]]) in edge_list and sorted([p[2], p[3], p[4]]) in edge_list and sorted([p[3], p[4], p[0]]) in edge_list:
            feasible = False
            break
    # Account for this flag
    if feasible:
        feasibles.append(flag)

print(len(feasibles))

exclude = [flag for flag in TT.generate_flags(4) if flag not in feasibles]

TT.exclude(exclude)

# Assumptions
edge_01 = TT(2, edges=[[0, 1]], C0=[[0]], C1=[[1]], C2=[])
edge_12 = TT(2, edges=[[0, 1]], C0=[], C1=[[0]], C2=[[1]])
edge_02 = TT(2, edges=[[0, 1]], C0=[[0]], C1=[], C2=[[1]])
point0 = TT(1, edges = [], C0 = [[0]], C1 = [], C2 = [])
point1 = TT(1, edges = [], C0 = [], C1 = [[0]], C2 = [])
point2 = TT(1, edges = [], C0 = [], C1 = [], C2 = [[0]])
positives = [edge_12 - edge_01, edge_12 - edge_02, point0 - 1/3, point1 - 1/3, point2 - 1/3]

# Missing edges
M = 1 + TT(2, edges=[], C0=[], C1=[[0]], C2=[[1]]) - 1

# Bad edges
B = 1
B += TT(2, edges=[[0, 1]], C0=[[0]], C1=[[1]], C2=[])
B += TT(2, edges=[[0, 1]], C0=[[0]], C1=[], C2=[[1]])
B += TT(2, edges=[[0, 1]], C0=[], C1=[[0], [1]], C2=[])
B += TT(2, edges=[[0, 1]], C0=[], C1=[], C2=[[0], [1]])
B -= 1

# Optimize
# const = TT.blowup_construction(5, 3, edges=[[1, 2]], C0=[[0]], C1=[[1]], C2=[[2]])
# x = TT.optimize(B - M, 5, maximize=True, positives = positives, exact=True, construction=const)
# print(x)

x = TT.optimize(B - M, 5, maximize=True, positives = positives)
print(x)
