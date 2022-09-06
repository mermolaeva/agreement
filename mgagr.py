
import re
import itertools
from utils import *
from grammars import mg2mcfg, start_exp_fun, random_tree

str_type_chars = ''.join([re.escape(c) for c in type_chars])
re_li = r'(.*?) ?{} ?(.*);'.format(re.escape('::'))
re_eq = r'(.*) ?{} ?(.*);'.format(re.escape('=='))
re_sfeature = r'([{}]*)([^ \[\]{}]+)([{}]*)(?:(\[[^ \[\]{}]*\]))?(?: |$)'.format(str_type_chars, str_type_chars, str_type_chars, str_type_chars)
re_mfeature = r'(.*?):(.*?)(?:,|$)'
re_mor = r'([^\[\]]*)\[(.*)\] ?(?:\+|$)'


def get_syn_features(lis):
    return set(f.name for _, b in lis for f in b)


def get_sem_features(lis):
    mfeat_dict = {}
    for mbundle in [f.mfeats for _, b in lis for f in b if f.mfeats]:
        for mf in mbundle:
            mfeat_dict.setdefault(mf.name, set())
            mfeat_dict[mf.name].add(mf.value)
    return mfeat_dict


def get_morphemes(eqs):
    return set(m for morphemes in eqs.keys() for m in morphemes)


def unpack_sf(sf, sem_features):
    if sf.mfeats is None: # no agreement, return singleton list of original SFeature
        return [sf,]
    options = {f.name: [(f.value, f.is_lex, f.is_cin), None] for f in sf.mfeats}
    for key, val in sem_features.items():
        if not key in options:
            options[key] = [None,]
            for v in val:
                options[key].append((v, False, True))
                options[key].append((v, False, False))

    options_list = [[(key, v) for v in val] for key, val in options.items()]
    combinations = list(itertools.product(*options_list))
    sfeatures = [SFeature(sf.type, sf.name, MBundle(MFeature(t[0], *t[1]) for t in c if t[1] is not None)) for c in combinations]

    return sfeatures


def unpack_sb(sb, sem_features):
    options = [unpack_sf(f, sem_features) for f in sb]
    combinations = [SBundle(x) for x in itertools.product(*options)]
    return combinations


def is_consistent(sb):
    mdicts = [sf.mfeats.to_dict() for sf in reversed(sb) if sf.mfeats is not None]
    for i, mdict in enumerate(mdicts):
        for n, goal in mdict.items():
            if goal.is_cin is False and goal.is_lex is False:
                try:
                    probe = next(mdict2[n] for mdict2 in mdicts[i+1:])
                    assert probe.value == goal.value
                except (KeyError, StopIteration, AssertionError) as e: return False
    return True


def is_pronounceable(sem, sb, morphemes):
    mb = sb.mor().compatible()
    for morpheme in morphemes:
        # print()
        # print(sem, morpheme[0], morpheme[0] == sem)
        # print(set(mb), set(morpheme[1]), set(morpheme[1]).issubset(set(mb)), all(x in mb for x in morpheme[1]))
        if morpheme[0] == sem and set(morpheme[1]).issubset(set(mb)):
            return True
    return False


def is_exactly_pronounceable(sem, sb, morphemes):
    mb = sb.mor().compatible()
    # morpheme[1] has to be a subset of mb
    # but also mb.
    for morpheme in morphemes:
        # print()
        # print(sem, morpheme[0], morpheme[0] == sem)
        # print(set(mb), set(morpheme[1]), set(morpheme[1]).issubset(set(mb)), all(x in mb for x in morpheme[1]))
        if morpheme[0] == sem and morpheme[1] == mb:
            return True
    return False


def is_minimal(sem, sb, morphemes):
    # check whole mbundles: for each of them, all the smaller bundles are available in other LIs
    # for each received bundle:
    # is each received feature value emitted down the line?
    # if not, are all received features actually used to pronounce the LI?
    # PROBLEM: how do we know what is needed to pronounce the lI?
    # Can we assume that there is exactly one way to pronounce each morpheme?

    # mdicts = [sf.mfeats.to_dict() for sf in reversed(sb) if sf.mfeats is not None]
    # for i, mdict in enumerate(mdicts):
    #     for n, goal in mdict.items():
    #         if goal.is_cin is False and goal.is_lex is False:
    #             try:
    #                 probe = next(mdict2[n] for mdict2 in mdicts[i+1:])
    #                 assert probe.value == goal.value
    #             except (KeyError, StopIteration, AssertionError) as e: return False
    # return True
    pass


def is_good(sem, sb, morphemes):
    conditions = [
        is_consistent(sb),
        is_pronounceable(sem, sb, morphemes),
        # is_exactly_pronounceable(sem, sb, morphemes)
    ]
    return all(conditions)


# def unpack_li(li, ids):
#     options = [unpack_sf(f, li.sem) for f in li.sb]
#     combinations = [SBundle(x) for x in itertools.product(*options)]
#     new_lis = []
#     for c in combinations:
#         new_li, ids = make_li(li.sem, c, ids)
#         new_lis.append(new_li)
#     return new_lis, ids


# def make_li(sem, sb, ids):
#     next_id = len(ids)
#     li = LI(id, sem, sb)
#     ids[next_id] = (sem, sb.mor())
#     return li, ids


def file_to_mg(curr_name): # read grammar from a .mg file
    file = open('lexica/{}.mg'.format(curr_name), 'r')
    start = None
    mg, eqs, reps = [], {}, {}
    for line in file:
        line = line.strip().split('/', 1)[0]
        if line:
            if start == None:
                l = line.strip(';')
                if len(l) == 1: start = l # NOTE: assumes that the start category is a single symbol
                else: raise Exception('Cannot identify the start category')
            
            elif '::' in line: # parsing LIs
                (item_sem, item_syn) = re.findall(re_li, line)[0]
                features = []
                for (before, name, after, mor) in re.findall(re_sfeature, item_syn):
                    type = (before, after)
                    name = orig_int(name) if name.isdigit() else name # if the name is all digits: add a letter
                    if not mor:
                        mfeats = None
                    else:
                        mor = mor.strip('[]')
                        mfeats = MBundle([(MFeature(k, v, True, False)) for k, v in re.findall(re_mfeature, mor)])
                    features.append(SFeature(type, name, mfeats))
                mg.append((item_sem, SBundle(features)))

            elif '==' in line:
                (items_mor, item_phon) = re.findall(re_eq, line)[0]
                morphemes = []
                for (sem, mor) in re.findall(re_mor, items_mor):
                    mfeats = MBundle([(MFeature(k, v)) for k, v in re.findall(re_mfeature, mor)])
                    morphemes.append((sem, mfeats))
                eqs[tuple(morphemes)] = item_phon

            else: raise Exception(f'Cannot parse line: {line}')
        
    return start, mg, eqs


if __name__ == '__main__':
    start, mg, eqs = file_to_mg('eng')
    syn_features = get_syn_features(mg)
    sem_features = get_sem_features(mg)
    morphemes = get_morphemes(eqs)
    print(start)
    print(syn_features)
    print(list(sem_features.items()))
    print(morphemes)
    print()
    for (sem, sb) in mg: print(sem, sb.stripped())

    mg_stripped = {i:c.stripped() for i, (sem, c) in enumerate(mg)}
    mg_dict = {i:(sem, c) for i, (sem, c) in enumerate(mg)}
    cfg = mg2mcfg(mg_stripped, start_exp_fun(start), useful=True)
    pretty_cfg(cfg, show_usage=False)
    for k, v in mg_dict.items():
        print(k, v)
    
    print()
    t = random_tree(cfg, mg_dict)
    pprint_tree(t)
    print()
    print(t)
    print()
    tree = to_node(t)
    tree.pprint()
    print()
    for n in tree.fringe:
        print('Node:', n)
        n.outward()
        print('---------')



    # combs = [(sem, unpack_sb(sb, sem_features)) for (sem, sb) in mg]

    # for comb in combs:
    #     print(comb[0], len(comb[1]))

    # filtered = list(set((sem, sb) for (sem, sbs) in combs for sb in sbs if is_good(sem, sb, morphemes)))
    # new_mg_dict = {i:c.vanilla() for i, (sem, c) in enumerate(filtered)}
    # print(f'Done filtering: {len(filtered)}')

    # cfg = mg2mcfg(new_mg_dict, start_exp_fun(start), useful=True)
    # ids = [y[0] for x in cfg.values() for y in x.keys() if isinstance(y[0], int)]
    # print(sum(len(sbs) for _, sbs in combs), len(filtered), len(ids))
    
    # for sem, c in sorted([filtered[i] for i in ids]):
    #     print(f'{sem} :: {c.vanilla()}')

    # for key, val in eqs.items(): print (key, val)
    # print()
    # print(syn_features)
    # print(list(sem_features.items()))
    # print(morphemes)
