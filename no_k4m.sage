from sage.algebras.flag_algebras import *

# This is some hack to create the theory for 3-graphs without C5- and K4-
# up to size 7. It is easier to make them as extensions of 6 sized structures
# so this code does that.

def check_containment(smalls, larges):
    """
    Helper function to check is any of the smalls appears in each of the larges.

    INPUT:
    smalls - list of flags, must be from a theory with edges relation
    larges - list of flags, also must be from a theory with edges relation

    OUTPUT:
    list of booleans, i-th element represents if i-th large flag is free from all smalls
    """
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

# Reset three graphs, so nothing is excluded
TG = ThreeGraphTheory
# k4 and k4m (the two induced structures with size 4 excluded)
k4 = TG(4, edges=[[0, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 3]])
k4m = TG(4, edges=[[0, 1, 2], [0, 1, 3], [0, 2, 3]])
excls = [k4,k4m]
TG.exclude(excls)

# check the list of flags with size 5 and 6
fl5 = TG.generate_flags(5)
fl6 = TG.generate_flags(6)

# quick 3-graph identifier code. This will be the identifier for
# the theory of C5- free 3-graphs (any identifier working for 3-graphs can work here)
def _identify_hypergraph(n, ftype_points, edges):
    g = Graph([list(range(n+len(edges))), [(i+n,x) for i,b in enumerate(edges) for x in b]], 
              format='vertices_and_edges')
    ftype_union = [jj for ff in ftype_points for jj in ff]
    partt = list(ftype_points) + \
            [[ii for ii in range(n) if ii not in ftype_union]] + \
            [list(range(n,n+len(edges)))]
    blocks = tuple(g.canonical_label(partition=partt).edges(labels=None, sort=True))
    return (n, tuple([len(xx) for xx in ftype_points]), blocks)

# generator code. It should really just return TG, but for size 7 that takes too long
# so this hack just returns TG for size up to 6, and for 7 it generates all flags
# with this extension technique
def _gen(n):
    if n<=4:
        for xx in TG.generate_flags(n):
            yield xx.blocks()
    elif n==5:
        for xx in fl5:
            yield xx.blocks()
    elif n==6:
        for xx in fl6:
            yield xx.blocks()
    elif n==7:
        import itertools
        from tqdm import tqdm
        fl7_m = [[] for ii in range(35+1)]
        subs = list(itertools.combinations(range(6), int(2)))
        for xx in tqdm(fl6):
            xb = xx.blocks()['edges']
            for ii in range(15+1):
                for pps in itertools.combinations(subs, int(ii)):
                    xbp = [[pp[0], pp[1], 6] for pp in pps] + xb
                    flxp = TG(7, edges=xbp)
                    en = len(xbp)
                    if flxp not in fl7_m[en]:
                        if check_containment(excls, [flxp])[0]:
                            fl7_m[en].append(flxp)
        fl7 = [yy for xx in fl7_m for yy in xx]
        for xx in fl7:
            yield xx.blocks()
    else:
        #for n>=8 just return an empty list, this will not be called so doesn't 
        #really matter
        return []

# Create the theory based on this generator and identifier
TGp = CombinatorialTheory("NoK4m", _gen, _identify_hypergraph, edges=3)

# for sanity check, print the number of structures with size 5, 6, 7
# should be 11 106 8157
# print(len(TGp.generate_flags(5)), len(TGp.generate_flags(6)), len(TGp.generate_flags(7)))


#############################################################################################

tp = TGp(3, ftype=[0, 1, 2], edges=[[0, 1, 2]])
all_6 = TGp.generate_flags(6, tp)
F = 1

for f in all_6:
    # Re-label vertices to match type [0, 1, 2]
    roots = f.ftype_points()
    edges = f.blocks()['edges'].copy()
    isom = [-1 for i in range(6)]
    for i in range(3):
        isom[ roots[i] ] = i
    idx = 3
    for i in range(6):
        if isom[i] == -1:
            isom[i] = idx
            idx += 1
    for i in range(len(edges)):
        for j in range(len(edges[i])):
            edges[i][j] = isom[ edges[i][j] ]
        edges[i] = sorted(edges[i])
        
    # Re-labeled flag
    flag = TGp(6, ftype=[0, 1, 2], edges=edges)

    # Only preserve flags that contain edge [3, 4, 5]
    if [3, 4, 5] not in flag.blocks()['edges']:
        continue

    # Get pattern of the top vertices
    states = [[], [], []]
    for v in [3, 4, 5]:
        for e in edges:
            if v in e:
                t = [x for x in e if x <= 2]
                if len(t) > 1:
                    states[v - 3] += t
    for i in range(3):
        states[i] = list({0, 1, 2}.difference(set(states[i])))
        if len(states[i]) == 1:
            states[i] = states[i][0]
        elif len(states[i]) == 2:
            print("FATAL ERROR")
        else:
            states[i] = -1

    # Add flags with coefficients
    if (len(set(states)) == 2 and -1 not in states) or len(set(states)) == 3:
        continue
    if states.count(-1) in [3, 2]:
        F += flag / 9
    elif states.count(-1) == 1:
        F += flag / 3
    else:
        F += flag
    # print()
    # print(flag)
    # print(states)
F -= 1

# Optimise
degree = TGp(3, edges=[[0,1,2]], ftype=[0])
p2f4 = TGp.generate_flags(4, TGp(2, ftype=[0, 1]))
degree_difference = p2f4[2]-p2f4[3]+p2f4[5]-p2f4[6]
positives = [degree-2/7, degree_difference, -degree_difference]
ans = TGp.optimize_problem(F, 7, maximize=True, positives=positives)
print(ans)
