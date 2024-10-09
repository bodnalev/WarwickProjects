from sage.algebras.flag_algebras import *

def check_containment(smalls, larges):
    sis = [IncidenceStructure(ss.size(), ss.blocks()['edges']) for ss in smalls]
    lis = [IncidenceStructure(ss.size(), ss.blocks()['edges']) for ss in larges]
    res = []
    for ll in lis:
        good = True
        for ss in sis:
            for _ in ll.isomorphic_substructures_iterator(ss):
                good = False
                break
            if not good:
                break
        res.append(good)
    return res

TG = ThreeGraphTheory
TG.exclude()
C5m = TG(5, edges=[[0, 1, 2], [1, 2, 3], [2, 3, 4], [3, 4, 0]])
fl5 = TG.generate_flags(5)

gs = check_containment([C5m], fl5)
exls = [xx for ii, xx in enumerate(fl5) if not gs[ii]]
TG.exclude(exls)
#update graphs with size 5
fl5 = TG.generate_flags(5)

def _identifyCT(k, order_partition, n, ftype_points, **kwargs):
    is_graph = (k==2)
    color_number = sum(len(xx) for xx in order_partition)
    edges = kwargs["edges"]
    ftype_union = [jj for ff in ftype_points for jj in ff]
    Cs = [[cx[0] for cx in kwargs["C{}".format(ii)]] for ii in range(color_number)]
    g_parts = list(ftype_points) + \
              [[ii for ii in range(n) if ii not in ftype_union]]
    ppadd = 0 if is_graph else len(edges)
    g_verts = list(range(n+ppadd+color_number))
    g_parts.append(list(range(n, n+ppadd)))
    g_parts += [[n+ppadd+ii for ii in partition_j] for partition_j in order_partition]
    if is_graph:
        g_edges = list(edges)
        for ii in range(color_number):
            g_edges += [(xx, n+ii) for xx in Cs[ii]]
    else:
        g_edges = [(i+n,x) for i,b in enumerate(edges) for x in b]
        for ii in range(color_number):
            g_edges += [(xx, n+len(edges)+ii) for xx in Cs[ii]]
    g = Graph([g_verts, g_edges], format='vertices_and_edges')
    blocks = tuple(g.canonical_label(partition=g_parts).edges(labels=None, sort=True))
    return (n, tuple([len(xx) for xx in ftype_points]), blocks)

def _generateCT(base_theory, k, order_partition, n):
    color_number = sum(len(xx) for xx in order_partition)
    BT = base_theory
    for xx in BT.generate_flags(n):
        unique = []
        edges = xx.blocks()['edges']

        for yy in itertools.product(range(color_number), repeat=int(n)):
            yy = list(yy)
            Cs = {"C{}".format(cc):[[ii] for ii, oo in enumerate(yy) if oo==cc] for cc in range(color_number)}
            iden = _identifyCT(k==2, order_partition, n, [], edges=edges, **Cs)
            if iden not in unique:
                unique.append(iden)
                Cs["edges"] = edges
                yield Cs

# To make the default codes work for this specific case:
# The generator:
# Colors the elements of TGp (3-graphs without C5- and K4-), works on 3-uniform structures
# and the colors 0, 1, 2 are interchangeable (otherwise it would say [[0], [1], [2]]
GraphTheory.exclude()
def generate_colored(n):
    return _generateCT(TG, 3, [[0], [1], [2]], n)

# Same for the identifier. Colors are interchangeable.
def identify_colored(n, ftype_points, edges, C0, C1, C2):
    return _identifyCT(3, [[0], [1], [2]], n, ftype_points, edges=edges, C0=C0, C1=C1, C2=C2)

CTGp = CombinatorialTheory("ColoredNoC5mYesK4m", generate_colored, identify_colored, edges=3, C0=1, C1=1, C2=1)

CTGp.exclude(CTGp(3, edges=[], C0=[[0]], C1=[[1]], C2=[[2]]))

# Create the theory
def test_identify(n, ftype_points, edges, C0, C1, C2):
    return colored_identify(2, [[0], [1], [2]], n, ftype_points, edges=edges, C0=C0, C1=C1, C2=C2)

def test_generate(n):
    return colored_generate(2, [[0], [1], [2]], n)

TT = CombinatorialTheory("123ColLinkNoC5", test_generate, test_identify, edges=2, C0=1, C1=1, C2=1)
# TT.clear()
TT.exclude()

print(len(TT.generate_flags(4)))

# Generate all feasible graphs on 4 vertices
all_flags = CTGp.generate_flags(5)
feasible = []
for flag in all_flags:
    edges = flag.blocks()['edges']
    C0, C1, C2 = flag.blocks()['C0'], flag.blocks()['C1'], flag.blocks()['C2']
    for v in range(5):
        if [v] not in C0:
            continue
        # Find the link graph of v
        link_edges = []
        for e in edges:
            if v in e:
                link_edges.append([v if x == 4 else x for x in e if x != v])
        g = TT(4,
                 edges=link_edges,
                 C0=[[v] if x == [4] else x for x in C0 if x != [v]],
                 C1=[[v] if x == [4] else x for x in C1 if x != [v]],
                 C2=[[v] if x == [4] else x for x in C2 if x != [v]])
        if g not in feasible:
            feasible.append(g)

print(len(feasible))

exclude = [flag for flag in TT.generate_flags(4) if flag not in feasible]

print(len(exclude))
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

# # Optimize
const = TT.blowup_construction(5, 3, edges=[[1, 2]], C0=[[0]], C1=[[1]], C2=[[2]])
x = TT.optimize(B - M, 5, maximize=True, positives = positives, exact=True, construction=const)
print(x)

# x = TT.optimize(B - 0.99*M, 5, maximize=True, positives = positives)
# print(x)
