
import re
import itertools
from utils import *
from grammars import mg2mcfg, random_tree
import argparse

str_type_chars = ''.join([re.escape(c) for c in type_chars])
re_li = r'(.*?) ?{} ?(.*);'.format(re.escape('::'))
re_eq = r'(.*) ?{} ?(.*);'.format(re.escape('=='))
re_sfeature = r'([{}]*)([^ \[\]{}]+)([{}]*)(?:(\[[^ \[\]{}]*\]))?(?: |$)'.format(str_type_chars, str_type_chars, str_type_chars, str_type_chars)
re_mfeature = r'(.*?):(.*?)(?:,|$)'
re_mor = r'([^\[\]]*)\[(.*)\] ?(?:\+|$)'


def get_syn_features(lis):
    return set(f.name for _, b in lis for f in b)


def get_sem_features(lis): # collect all known mfeatures and their values
    mfeat_dict = {}
    for _, b in lis:
        for f in b:
            for mf in [*(f.cin if f.cin else tuple()), *(f.cout if f.cout else tuple())]:
                mfeat_dict.setdefault(mf.name, set())
                mfeat_dict[mf.name].add(mf.value)
    return mfeat_dict


def get_morphemes(eqs):
    return set(m for morphemes in eqs.keys() for m in morphemes)


def unpack_sf(sf, sem_features):
    if sf.cin is None: # no incoming agreement, return singleton list of original SFeature
        return [sf,]

    options = {f.name: [(f.value, f.is_lex), None] for f in sf.cin}
    for key, val in sem_features.items():
        if not key in options:
            options[key] = [None,]
            for v in val:
                options[key].append((v, False))

    options_list = [[(key, v) for v in val] for key, val in options.items()]
    combinations = list(itertools.product(*options_list))
    sfeatures = [SFeature(
        sf.type, 
        sf.name, 
        cin=MBundle(MFeature(t[0], *t[1]) for t in c if t[1] is not None),
        cout=MBundle(sf.cout)
        ) for c in combinations]

    return sfeatures


def unpack_cin(sb, sem_features): # received values: all combinations are viable
    options = [unpack_sf(f, sem_features) for f in sb]
    combinations = [SBundle(x) for x in itertools.product(*options)]
    return combinations


def unpack_cout(sb): # emitted values: fully determined by received and lexical
    consensus_sb = []
    consensus_dict = {} # consensus dictionary

    for i, sf in enumerate(sb): # first pass: collect mfeatures
        if sf.cin is not None: # if the receiving channel is present
            consensus_dict.update({mf.name:(mf, i) for mf in sf.cin}) # Lexical filter: ensure that the last received value wins
    
    for j, sf in enumerate(sb): # second pass: assign mfeatures to cout channels
        if sf.cout is not None: # if the emitting channel is present

            sf_mdict = {mf.name:mf for mf in sf.cout if mf.is_lex is True}
            for consensus_name, (consensus_feature, i) in consensus_dict.items():
                if i != j: # Valves: never emit a value along the same dependency you received it
                    sf_mdict.setdefault(consensus_name, consensus_feature) # keep lexically determined values

            sf_cout = MBundle(MFeature(v.name, v.value, False) for v in sf_mdict.values())
        else: sf_cout = sf.cout
        
        consensus_sb.append(SFeature(sf.type, sf.name, cin=sf.cin, cout=sf_cout))

    return SBundle(consensus_sb)


def unpack_sb(sb, sem_features):
    combs = unpack_cin(sb, sem_features)
    return [unpack_cout(comb) for comb in combs]


def is_pronounceable(sem, sb, morphemes):
    mb = sb.mor().compatible()
    for morpheme in morphemes:
        if morpheme[0] == sem and set(morpheme[1]).issubset(set(mb)):
            return True
    return False


def is_good(sem, sb, morphemes):
    conditions = [
        # is_consistent(sb),
        is_pronounceable(sem, sb, morphemes),
    ]
    return all(conditions)


def file_to_mg(curr_name): # read grammar from a .mg file
    file = open('lexica/{}.mg'.format(curr_name), 'r')
    start = None
    mg, eqs = [], {}
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
                        mfeats = MBundle([(MFeature(k, v, True)) for k, v in re.findall(re_mfeature, mor)])
                    features.append(SFeature(type, name, cout=mfeats, cin=None if mfeats is None else MBundle(())))
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
    parser = argparse.ArgumentParser()
    parser.add_argument('-g', '--grammar', action='store', type=str)
    parser.add_argument('-o', '--one_op', action='store_true', default=False)
    args = parser.parse_args()

    start, mg, eqs = file_to_mg(args.grammar)
    syn_features = get_syn_features(mg)
    sem_features = get_sem_features(mg)
    morphemes = get_morphemes(eqs)
    print(start)
    print(syn_features)
    print(list(sem_features.items()))
    print()
    for (sem, sb) in mg: print(sem, sb)
    print()

    unpacked_mg = []
    for sem, sb in mg:
        for new_sb in unpack_sb(sb, sem_features):
            # print(sem, '\t', new_sb)
            unpacked_mg.append((sem, new_sb))
    
    # print()

    # combs = [(sem, unpack_cin(sb, sem_features)) for (sem, sb) in mg]
    # unpacked_mg = list(set((sem, unpack_cout(sb)) for (sem, sbs) in combs for sb in sbs if is_good(sem, sb, morphemes)))
    
    new_mg_dict = {i:c for i, (sem, c) in enumerate(unpacked_mg)}
    print(f'Unpacked: {len(unpacked_mg)}\n')

    cfg = mg2mcfg(new_mg_dict, start, useful=True, one_op=args.one_op)
    ids = [y[0] for x in cfg.values() for y in x.keys() if isinstance(y[0], int)]

    # for k, v in cfg.items():
    #     print(k, v)
    
    for sem, c in sorted([unpacked_mg[i] for i in ids]):
        print(f'{sem} :: {c}')


    # mg_for_cfg = {i:c for i, (sem, c) in enumerate(mg)} # replace semantic features with indices
    # mg_dict = {i:sem for i, (sem, c) in enumerate(mg)} # record what each morpheme index (label) stands for
    # for k, v in mg_dict.items(): print(k, v)
    # print()


    # mg_for_cfg = {sem:c for i, (sem, c) in enumerate(mg)} # keep semantic features as they are
    # cfg = mg2mcfg(mg_for_cfg, start, useful=False)
    # pretty_cfg(cfg, show_usage=False)

    # tree = to_node(random_tree(cfg, None))
    # for n in tree.fringe:
    #     n.parent.data = n.data
    #     n.parent.children = None
    # tree.pprint()

    # print()
    # for n in tree.fringe:
    #     print('Node:', n)
    #     n.outward()
    #     print('---------')
