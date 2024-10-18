from sage.algebras.flag_algebras import *
import itertools

# Create the theory
def test_identify(n, ftype_points, edges, C0, C1, C2):
    return colored_identify(2, [[0], [1], [2]], n, ftype_points, edges=edges, C0=C0, C1=C1, C2=C2)

def test_generate(n):
    return colored_generate(2, [[0], [1], [2]], n)

TT = CombinatorialTheory("123_graph_link_no_C5-", test_generate, test_identify, edges=2, C0=1, C1=1, C2=1)

def get_more_edges(n, edges):
    edge = edges.copy()
    for e in edge:
        e = sorted(e)
    gg = []
    for u, v in itertools.combinations([x for x in range(n)], 2):
        if sorted([u, v]) not in edge:
            gg.append([u, v])
    return gg

exclude = []
# Condition 2.1 (two disjoint edges)
for flag in TT.generate_flags(4):
    # Make sure it has 2 edges
    if len(flag.blocks()['edges']) != 2:
        continue
    # Make sure it intersects all three parts
    if flag.blocks()['C0'] == [] or flag.blocks()['C1'] == [] or flag.blocks()['C2'] == []:
        continue
    # Get the degree sequence and make sure it is 1, 1, 1, 1
    seq = [0, 0, 0, 0]
    for e in flag.blocks()['edges']:
        seq[e[0]] += 1
        seq[e[1]] += 1
    if sorted(seq) != [1, 1, 1, 1]:
        continue
    # Make sure the edges go across parts
    across = True
    for e in flag.blocks()['edges']:
        i, j = e
        if [i] in flag.blocks()['C0'] and [j] in flag.blocks()['C0']:
            across = False
        if [i] in flag.blocks()['C1'] and [j] in flag.blocks()['C1']:
            across = False
        if [i] in flag.blocks()['C2'] and [j] in flag.blocks()['C2']:
            across = False
    if not across:
        continue
    # print(flag)
    exclude.append(flag)
print(len(exclude), "non-induced subgraphs to exclude")

# Condition 2.2 (two intersecting edges)
for flag in TT.generate_flags(3):
    # Make sure it has 2 edges
    if len(flag.blocks()['edges']) != 2:
        continue
    # Make sure it intersects all three parts
    if flag.blocks()['C0'] == [] or flag.blocks()['C1'] == [] or flag.blocks()['C2'] == []:
        continue
    # Get the degree sequence and make sure it is 1, 1, 2
    seq = [0, 0, 0]
    for e in flag.blocks()['edges']:
        seq[e[0]] += 1
        seq[e[1]] += 1
    if sorted(seq) != [1, 1, 2]:
        continue
    # Make sure the edges go across parts
    across = True
    for e in flag.blocks()['edges']:
        i, j = e
        if [i] in flag.blocks()['C0'] and [j] in flag.blocks()['C0']:
            across = False
        if [i] in flag.blocks()['C1'] and [j] in flag.blocks()['C1']:
            across = False
        if [i] in flag.blocks()['C2'] and [j] in flag.blocks()['C2']:
            across = False
    if not across:
        continue
    # print(flag)
    exclude.append(flag)
print(len(exclude), "non-induced subgraphs to exclude")

# Condition 3 (two edges)
for flag in TT.generate_flags(3):
    # Make sure it has 2 edges
    if len(flag.blocks()['edges']) != 2:
        continue
    # Make sure exactly one of the parts is empty
    if not (flag.blocks()['C0'] == [] or flag.blocks()['C1'] == [] or flag.blocks()['C2'] == []):
        continue
    two_empty = False
    for i in range(3):
        for j in range(i + 1, 3):
            if flag.blocks()['C'+str(i)] == flag.blocks()['C'+str(j)] == []:
                two_empty = True
    if two_empty:
        continue
    # Get the degree sequence and make sure it is 1, 1, 2
    v = 0
    seq = [0, 0, 0]
    for e in flag.blocks()['edges']:
        seq[e[0]] += 1
        seq[e[1]] += 1
        if seq[e[0]] == 2:
            v = e[0]
        elif seq[e[1]] == 2:
            v = e[1]
    if sorted(seq) != [1, 1, 2]:
        continue
    # Make sure the degree 2 vertex is not the only in its part
    lonely = False
    for i in range(3):
        if flag.blocks()['C'+str(i)] == [[v]]:
            lonely = True
    if lonely:
        continue
    # print(flag)
    exclude.append(flag)
print(len(exclude), "non-induced subgraphs to exclude")

# Get complete list of induced graphs to exclude
complete_excluded_list = []
for flag in exclude:
    # print(flag)
    edges = flag.blocks()['edges']
    base = edges.copy()
    n = len(flag.blocks()['C0']) + len(flag.blocks()['C1']) + len(flag.blocks()['C2'])
    extra_edges = get_more_edges(n, edges=edges)
    # print(extra_edges)
    for L in range(len(extra_edges) + 1):
        for subset in itertools.combinations(extra_edges, L):
            # print(base + list(subset))
            complete_excluded_list.append(TT(n, edges=base + list(subset), C0=flag.blocks()['C0'], C1=flag.blocks()['C1'], C2=flag.blocks()['C2']))
print(len(complete_excluded_list), "induced subgraphs to exclude")

# Exclude induced
TT.exclude(complete_excluded_list)

# # Assumptions
edge_00 = TT(2, edges=[[0, 1]], C0=[[0], [1]], C1=[], C2=[])
edge_11 = TT(2, edges=[[0, 1]], C0=[], C1=[[0], [1]], C2=[])
edge_22 = TT(2, edges=[[0, 1]], C0=[], C1=[], C2=[[0], [1]])
edge_01 = TT(2, edges=[[0, 1]], C0=[[0]], C1=[[1]], C2=[])
edge_12 = TT(2, edges=[[0, 1]], C0=[], C1=[[0]], C2=[[1]])
edge_02 = TT(2, edges=[[0, 1]], C0=[[0]], C1=[], C2=[[1]])
point0 = TT(1, edges = [], C0 = [[0]], C1 = [], C2 = [])
point1 = TT(1, edges = [], C0 = [], C1 = [[0]], C2 = [])
point2 = TT(1, edges = [], C0 = [], C1 = [], C2 = [[0]])
positives = [edge_12 - edge_01, edge_12 - edge_02]
positives += [point0 - 1/4, point1 - 1/4, point2 - 1/4]
positives += [edge_01 + edge_02 + edge_12 - 1/8]

# # Missing edges
M = 1 + TT(2, edges=[], C0=[], C1=[[0]], C2=[[1]]) - 1

# # Bad edges
B = 1
B += TT(2, edges=[[0, 1]], C0=[[0]], C1=[[1]], C2=[])
B += TT(2, edges=[[0, 1]], C0=[[0]], C1=[], C2=[[1]])
B += TT(2, edges=[[0, 1]], C0=[], C1=[[0], [1]], C2=[])
B += TT(2, edges=[[0, 1]], C0=[], C1=[], C2=[[0], [1]])
B -= 1

# Optimize
TT.optimize(B - M*9/10, 5, maximize=True, positives = positives, exact=True)
