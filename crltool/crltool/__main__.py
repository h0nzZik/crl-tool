import argparse
import json
import logging
import time
import sys
import pprint
import cProfile

from pathlib import Path

from itertools import (
    chain
)

from typing import (
    Dict,
    Final,
    Optional,
    List,
    Tuple,
)

from pyk.kast.outer import (
    KFlatModuleList,
    KFlatModule,
    read_kast_definition,
    KClaim,
    KApply,
    KLabel,
    KSentence,
)

from pyk.kast.manip import (
    extract_cells,
    extract_lhs,
    extract_rhs,
    rename_generated_vars,
    bool_to_ml_pred,
)

from pyk.kore.syntax import (
    And,
    Pattern,
    Top,
    Not,
    Implies,
    App,
    EVar,
    SortApp,
)

from pyk.kore.parser import (
    KoreParser
)

from pyk.ktool.kprove import (
    KProve
)

from pyk.cterm import (
    CTerm,
    KInner,
)

from .crl import (
    LP,
    CLP,
    ECLP,
    Claim,
    Specification,
    RLCircularity,
)

from .kore_utils import (
     get_top_cell_initializer
)

from .ReachabilitySystem import ReachabilitySystem

from .frontend import (
    get_kprove_generated_json,
)

from .verify import (
    #UnsolvableGoal,
    VerifyGoal,
    EclpImpliesResult,
    eclp_impl_valid_trough_lists,
    VerifySettings,
    VerifyResult,
    VerifyEntry,
    VerifyQuestion,
    free_evars_of_pattern, # TODO this should be moved somewhere else
    verify,
    prepare_verifier,
)

_LOGGER: Final = logging.getLogger(__name__)

def create_argument_parser() -> argparse.ArgumentParser:
    argument_parser = argparse.ArgumentParser(
        prog="crl-tool",
        description="A Cartesian Reachability Logic tool"
    )
    argument_parser.add_argument('-d', '--definition', required=True)
    argument_parser.add_argument('--kore-rpc-args')
    argument_parser.add_argument('--connect-to-port', default=None)
    
    subparsers = argument_parser.add_subparsers(dest='command')
    
    subparser_check_implication = subparsers.add_parser('check-implication', help='Checks whether the specification holds trivially')
    subparser_check_implication.add_argument('--specification', required=True)
    subparser_check_implication.add_argument('--store-witness-to', type=str, default=None)

    subparser_prove = subparsers.add_parser('prove', help='Prove a specification')
    subparser_prove.add_argument('--specification', required=True)
    subparser_prove.add_argument('--depth', type=int, default=10)
    subparser_prove.add_argument('--from-json', action='store_true', default=False)
    subparser_prove.add_argument('--trusted-claim-blacklist', type=str, default="")
    subparser_prove.add_argument('--dont-filter-candidate-matches', action='store_true', default=False)

    subparser_load_frontend_spec = subparsers.add_parser('load-frontend-spec', help='Load a frontend-generated specification')
    subparser_load_frontend_spec.add_argument('--specification', required=True)
    subparser_load_frontend_spec.add_argument('--output-file', type=str)

    subparser_view_dump = subparsers.add_parser('view-dump', help='Views a dump generated by [prove]')
    subparser_view_dump.add_argument('--from', type=str, required=True)
    subparser_view_dump.add_argument('--target', nargs='+', default=None, required=True)

    subparser_simplify = subparsers.add_parser('simplify', help='Simplify a pattern')
    subparser_simplify.add_argument('--pattern', required=True)
    subparser_simplify.add_argument('--output-file', required=True)

    subparser_check_impl_direct = subparsers.add_parser('check-implication-directly', help='Simplify a pattern')
    subparser_check_impl_direct.add_argument('--hackit', type=bool, default=False)
    subparser_check_impl_direct.add_argument('--pattern', required=True)
    
    return argument_parser

def check_implication(rs: ReachabilitySystem, args) -> int:
    with open(args['specification'], 'r') as spec_f:
        claim = Claim.from_dict(json.loads(spec_f.read()))
        result : EclpImpliesResult = eclp_impl_valid_trough_lists(rs, claim.antecedent, claim.consequent)
        print(result.valid)
        if result.witness is not None:
            pretty_witness = rs.kprint.kore_to_pretty(result.witness)
            if args['store_witness_to'] is None:
                return 0
            with open(args['store_witness_to'], 'w') as fw:
                fw.write(pretty_witness)
        return 0
    return 1

def check_implication_directly(rs: ReachabilitySystem, args) -> int:
    with open(args['pattern'], 'r') as fr:
        pat = KoreParser(fr.read()).pattern()            
        print('Input')
        print(rs.kprint.kore_to_pretty(pat))
        match pat:
            case Implies(_, l, r):
                lhs, rhs = l, r
            case _:
                raise ValueError(f"Expected implication, but {pat} was given")
        impl_result = rs.kcs.client.implies(lhs, rhs)
        print('Simplified')
        print(rs.kprint.kore_to_pretty(impl_result.implication))
        #print(impl_result.implication.text)
        if (impl_result.satisfiable):
            print("Satisfiable")
        else:
            print("Unsatisfiable")
        if impl_result.substitution is not None:
            print("Substitution:")
            print(rs.kprint.kore_to_pretty(impl_result.substitution))
            #print(impl_result.substitution.text)
        if impl_result.predicate is not None:
            print("Predicate:")
            print(rs.kprint.kore_to_pretty(impl_result.predicate))
            #print(impl_result.predicate.text)
    return 0

def simplify(rs: ReachabilitySystem, args) -> int:
    with open(args['pattern'], 'r') as fr:
        pat = KoreParser(fr.read()).pattern()
        patsimpl0 : Pattern = rs.kcs.client.simplify(pat)[0]
        print(patsimpl0.text)
        with open(args['output_file'], 'w') as fw:
            fw.write(patsimpl0.text)
    return 0

def eclp_to_pretty(rs: ReachabilitySystem, eclp: ECLP):
    patterns = list(map(rs.kprint.kore_to_pretty, eclp.clp.lp.patterns))
    constraint = rs.kprint.kore_to_pretty(eclp.clp.constraint)
    return {'vars': eclp.vars, 'patterns': patterns, 'constraint': constraint}
    #return f'exists {eclp.vars} such that {patterns} /\ {constraint}'

def pprint_eclp(rs: ReachabilitySystem, eclp: ECLP):
    print("Existentially quantified variables")
    pprint.pprint(eclp.vars)
    patterns = list(map(lambda p: (rs.kprint.kore_to_pretty(p)), eclp.clp.lp.patterns))
    pprint.pprint(patterns)
    print('Constraint')
    pprint.pprint(rs.kprint.kore_to_pretty(eclp.clp.constraint))

def print_vquestion(rs: ReachabilitySystem, q: VerifyQuestion):
    for g0 in q.goals:
        #if not isinstance(g0, VerifyGoal):
        #    print('Unsolvable')
        #    continue
        g : VerifyGoal = g0
        print(f'Goal ID {g.goal_id}.')
        pprint_eclp(rs, g.antecedent)
        print('Flushed cutpoints')
        continue
    return

# TODO I think this should be removed.
def view_dump(rs: ReachabilitySystem, args) -> int:
    with open(args['from'], 'r') as fr:
        the_dump = json.load(fr)
        entries : List[VerifyEntry] = [VerifyEntry.from_dict(e) for e in the_dump ]
        tgt : List[int] = list(map(lambda s: int(s), args['target']))
        selected : List[VerifyQuestion] = [] # [e.question for e in entries if e.question is not None and e.question.depth == tgt ]
        # Usually, there should be at most one
        for q in selected:
            #print(f'Proof state {i} in depth {s.depth}, generated from {s.source_of_question}: ')
            print_vquestion(rs, q)
        #print(f"selected: {selected}")
        
    return 0

def claim_is_cartesian(claim: KClaim) -> bool:
    return ('cartesian' in claim.att.atts)

def claim_is_trusted(claim: KClaim) -> bool:
    return ('trusted' in claim.att.atts)

def prelude_list_to_metalist(term: KInner) -> List[KInner]:
    match term:
        case KApply(KLabel('_List_', _), (left,right)):
            return prelude_list_to_metalist(left) + prelude_list_to_metalist(right)
        case KApply(KLabel('ListItem', _), (value,)):
            return [value]
        # TODO: what about empty list (.List) ?
        case _:
            raise ValueError(f"Not a list: {term}")

def add_generated_stuff(phis : Tuple[Pattern, ...], counter_variable_name : str) -> Pattern:
    return App(
        symbol="Lbl'-LT-'generatedTop'-GT-'",
        sorts=(),
        args=tuple(
            list(phis) + [
            App(
                symbol="Lbl'-LT-'generatedCounter'-GT-'",
                sorts=(),
                args=(
                    EVar(
                        name=counter_variable_name,
                        sort=SortApp('SortInt', ())
                    ),
                )
            )
            ]
        ),
    )

def strip_inj(phi: Pattern) -> Tuple[Pattern,...]:
    match phi:
        case App('inj', _, subs):
            return subs
        case _:
            raise ValueError(f"Not an inj pattern: {phi.text}")

def extract_crl_claim(rs: ReachabilitySystem, claim: KClaim, claim_id: int) -> Claim:
    body = claim.body
    print(f'before:{body}')
    lhs = extract_lhs(body)
    rhs = extract_rhs(body)

    list_lhs = prelude_list_to_metalist(lhs)
    list_rhs = prelude_list_to_metalist(rhs)
    if (len(list_lhs) != len(list_rhs)):
        raise ValueError(f"CRL antecedent and consequent need to have the same arity: {len(list_lhs)} != {len(list_rhs)}")
    print(f"list_lhs={list_lhs}")
    list_lhs_kore = [rs.kprint.kast_to_kore(x) for x in list_lhs]
    list_rhs_kore = [rs.kprint.kast_to_kore(x) for x in list_rhs]
    evars = list(chain.from_iterable([free_evars_of_pattern(p) for p in list_rhs_kore]))
    list_lhs_kore2 = [strip_inj(p) for p in list_lhs_kore]
    list_rhs_kore2 = [strip_inj(p) for p in list_rhs_kore]
    
    lhs_generated_counters = [f"VARGENERATED{claim_id}COUNTER{i}" for i in range(len(list_lhs_kore))]
    rhs_generated_counters = [f"VARGENERATED{claim_id}COUNTERPRIME{i}" for i in range(len(list_rhs_kore))]
    list_lhs_kore_top = [add_generated_stuff(phis, name) for phis,name in zip(list_lhs_kore2,lhs_generated_counters)]
    list_rhs_kore_top = [add_generated_stuff(phis, name) for phis,name in zip(list_rhs_kore2,rhs_generated_counters)]

    question_mark_variables = [
        ev for ev in evars if ev.name.startswith("Var'Ques")
    ] + [
        EVar(name=name, sort=SortApp('SortInt', ()))  for name in rhs_generated_counters
    ]

    requires_constraint = strip_inj(rs.kprint.kast_to_kore(bool_to_ml_pred(claim.requires)))[0]
    ensures_constraint = strip_inj(rs.kprint.kast_to_kore(bool_to_ml_pred(claim.ensures)))[0]
    return Claim(
        antecedent=ECLP(
            vars=[],
            clp=CLP(
                lp=LP(
                    patterns=list_lhs_kore_top,
                ),
                constraint=requires_constraint
            ),
        ),
        consequent=ECLP(
            vars=question_mark_variables,
            clp=CLP(
                lp=LP(
                    patterns=list_rhs_kore_top,
                ),
                constraint=ensures_constraint,
            )
        )
    )


def extract_crl_spec_from_flat_module(
    rs: ReachabilitySystem,
    mod: KFlatModule,
    trusted_claim_blacklist : List[str]
) -> Specification:
    claims: Dict[str,Claim] = dict()
    trusted_claims: Dict[str,Claim] = dict()
    cutpoints: Dict[str,ECLP] = dict()
    rl_circularities : Dict[str,RLCircularity] = dict()
    for claim, claim_id in zip(mod.claims, range(len(mod.claims))):
        cart : bool = claim_is_cartesian(claim)
        trusted : bool = claim_is_trusted(claim)
        sen : KSentence = claim
        if cart:
            if trusted:
                if sen.label not in trusted_claim_blacklist:
                    trusted_claims[sen.label] = extract_crl_claim(rs, claim, claim_id=claim_id)
            else:
                claims[sen.label] = extract_crl_claim(rs, claim, claim_id=claim_id)
        else:
            _LOGGER.warning("Non-cartesian claims are not supported yet")
        # TODO extract cutpoints and circularities...
    return Specification(
        claims=claims,
        trusted_claims=trusted_claims,
        cutpoints=cutpoints,
        rl_circularities=rl_circularities
    )

def get_spec_from_file(rs: ReachabilitySystem, filename: Path, trusted_claim_blacklist: List[str]) -> Specification:
    jsspec = get_kprove_generated_json(rs=rs, specification=filename)
    ml = KFlatModuleList.from_dict(jsspec['term'])
    #print(ml)
    for mod in ml.modules:
        if mod.name == ml.main_module:
            spec = extract_crl_spec_from_flat_module(
                rs=rs,
                mod=mod,
                trusted_claim_blacklist=trusted_claim_blacklist
            )
            return spec
    raise ValueError("No main module found")

def load_frontend_spec(rs: ReachabilitySystem, args):
    spec : Specification = get_spec_from_file(
        rs=rs,
        filename=Path(args['specification']),
        trusted_claim_blacklist=[s.strip() for s in args['trusted_claim_blacklist'].split(",")]
    )
    spec_str = json.dumps(spec.dict, sort_keys=True, indent=True)
    if ('output_file' not in args) or (args['output_file'] is None):
        print(spec_str)
    else:
        with open(args['output_file'], 'w') as fw:
            fw.write(spec_str)
    return 0

def prove(rs: ReachabilitySystem, args) -> int:
    if args['from_json']:
        with open(args['specification'], 'r') as spec_f:
            spec : Specification = Specification.from_dict(json.loads(spec_f.read()))
    else:
        spec  = get_spec_from_file(
            rs=rs,
            filename=Path(args['specification']),
            trusted_claim_blacklist=[s.strip() for s in args['trusted_claim_blacklist'].split(",")],
        )

    settings = VerifySettings(
        check_eclp_impl_valid=eclp_impl_valid_trough_lists,
        max_depth=int(args['depth']),
        goal_as_cutpoint=True,
        filter_candidate_matches=not bool(args['dont_filter_candidate_matches']),
    )
    for claim_name,claim in spec.claims.items():
        _LOGGER.info(f"Going to verify claim {claim_name}")
        
        verifier = prepare_verifier(
            rs=rs, 
            settings=settings,
            user_cutpoints=spec.cutpoints,
            claim=claim,
            claim_name=claim_name,
            trusted_claims=spec.trusted_claims,
        )
        result : VerifyResult = verifier.verify()
        print(f'proved: {result.proved}')
        pprint.pprint(verifier.ps.dict)
        #pprint.pprint(verifier.sscache)

    return 0

def main_main() -> None:
    argument_parser = create_argument_parser()
    args = vars(argument_parser.parse_args())
    #logging.basicConfig(encoding='utf-8', level=logging.DEBUG, filename="crl-tool.log")
    logging.basicConfig(encoding='utf-8', level=logging.DEBUG)
    logging.getLogger('pyk.kore.rpc').disabled = True
    logging.getLogger('pyk.ktool.kprint').disabled = True
    logging.getLogger('pyk.konvert').disabled = True
    logging.getLogger('pyk.kast.inner').disabled = True # TODO check those debugging messages
    if (args['connect_to_port'] is not None) and (args['kore_rpc_args'] is not None):
        print("'--connect-to-port' and '--kore-rpc-args' are mutually exclusive")
        return
    kore_rpc_args : Tuple[str,...] = ()
    if args['kore_rpc_args'] is not None:
        kore_rpc_args = tuple(str.split(args['kore_rpc_args']))
    #print(args)
    with ReachabilitySystem(
        definition_dir=Path(args['definition']), 
        kore_rpc_args=kore_rpc_args, 
        connect_to_port=args['connect_to_port'],
        ) as rs:
        if args['command'] == 'check-implication':
            retval = check_implication(rs, args)
        elif args['command'] == 'prove':
            retval = prove(rs, args)
        elif args['command'] == 'load-frontend-spec':
            retval = load_frontend_spec(rs, args)
        elif args['command'] == 'check-implication-directly':
            retval = check_implication_directly(rs, args)
        elif args['command'] == 'simplify':
            retval = simplify(rs, args)
        elif args['command'] == 'view-dump':
            retval = view_dump(rs, args)
        else:
            retval = 1
                
    sys.exit(retval)

def main() -> None:
    cProfile.runctx('main_main()', globals(), locals(), sort='cumulative')