import argparse
import json
import logging
import time
import sys
import pprint

from pathlib import Path

from typing import (
    Final,
    Optional,
    List,
    Tuple,
)

from pyk.kore.syntax import (
    And,
    Pattern,
    Top,
    Not,
    Implies,
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
)

from .kore_utils import (
     get_top_cell_initializer
)

from .ReachabilitySystem import ReachabilitySystem

from .verify import (
    #UnsolvableGoal,
    VerifyGoal,
    EclpImpliesResult,
    eclp_impl_valid,
    eclp_impl_valid_trough_lists,
    VerifySettings,
    VerifyResult,
    VerifyEntry,
    VerifyQuestion,
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
    subparser_check_implication.add_argument('--iteratively', action='store_true', default=False)
    subparser_check_implication.add_argument('--store-witness-to', type=str, default=None)

    subparser_prove = subparsers.add_parser('prove', help='Prove a specification')
    subparser_prove.add_argument('--specification', required=True)
    subparser_prove.add_argument('--depth', type=int, default=10)
    subparser_prove.add_argument('--no-print', action='store_true')
    subparser_prove.add_argument('--target', nargs='+', default=None)
    subparser_prove.add_argument('--dump-on-failure', type=str, default=None)

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
        if args['iteratively']:
            result : EclpImpliesResult = eclp_impl_valid(rs, claim.antecedent, claim.consequent)    
        else:
            result = eclp_impl_valid_trough_lists(rs, claim.antecedent, claim.consequent)
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
        patsimpl0 : Pattern = rs.kcs.client.simplify(pat)
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
        print(f'Goal ID {g.goal_id}. Stuck: { g.stuck }')
        pprint_eclp(rs, g.antecedent)
        print('Flushed cutpoints')
        continue
    return

def view_dump(rs: ReachabilitySystem, args) -> int:
    with open(args['from'], 'r') as fr:
        the_dump = json.load(fr)
        entries : List[VerifyEntry] = [VerifyEntry.from_dict(e) for e in the_dump ]
        tgt : List[int] = list(map(lambda s: int(s), args['target']))
        selected : List[VerifyQuestion] = [e.question for e in entries if e.question is not None and e.question.depth == tgt ]
        # Usually, there should be at most one
        for q in selected:
            #print(f'Proof state {i} in depth {s.depth}, generated from {s.source_of_question}: ')
            print_vquestion(rs, q)
        #print(f"selected: {selected}")
        
    return 0

def prove(rs: ReachabilitySystem, args) -> int:
    with open(args['specification'], 'r') as spec_f:
        claim : Claim = Claim.from_dict(json.loads(spec_f.read()))
        tgt : Optional[List[int]] = None
        if args['target'] is not None:
            tgt = list(map(lambda s: int(s), args['target']))
        settings = VerifySettings(
            check_eclp_impl_valid=eclp_impl_valid_trough_lists,
            max_depth=int(args['depth']),
            goal_as_cutpoint=True,
            target=tgt
        )
        #_LOGGER.info("Going to call `verify`")
        verifier = prepare_verifier(
            rs=rs, 
            settings=settings,
            user_cutpoints=[],
            antecedent=claim.antecedent, 
            consequent=claim.consequent,
        )
        result : VerifyResult = verifier.verify()


        print(f'proved: {result.proved}')
        if (not result.proved) and (args['dump_on_failure'] is not None):
            with open(args['dump_on_failure'], 'w') as fw:
                fw.write(verifier.dump())

        print(f'Have {len(result.final_states)} remaining questions:')
        if (args['no_print']):
            print("(omitted).")
            return 0
        for s,i in zip(result.final_states, range(len(result.final_states))):
            print(f'Proof state {i} in depth {s.depth}, generated from {s.source_of_question}: ')
            for g0 in s.goals:
                if not isinstance(g0, VerifyGoal):
                    print('Unsolvable')
                    continue
                g : VerifyGoal = g0
                print(f'Goal ID {g.goal_id}')
                patterns = list(map(lambda p: (rs.kprint.kore_to_pretty(p)), g.antecedent.clp.lp.patterns))
                pprint.pprint(patterns)
                print('Constraint')
                pprint.pprint(rs.kprint.kore_to_pretty(g.antecedent.clp.constraint))

    return 0

def main() -> None:
    argument_parser = create_argument_parser()
    args = vars(argument_parser.parse_args())
    #logging.basicConfig(encoding='utf-8', level=logging.DEBUG, filename="crl-tool.log")
    logging.basicConfig(encoding='utf-8', level=logging.DEBUG)
    logging.getLogger('pyk.kore.rpc').disabled = True
    logging.getLogger('pyk.ktool.kprint').disabled = True
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
        elif args['command'] == 'check-implication-directly':
            retval = check_implication_directly(rs, args)
        elif args['command'] == 'simplify':
            retval = simplify(rs, args)
        elif args['command'] == 'view-dump':
            retval = view_dump(rs, args)
        else:
            retval = 1
                
    sys.exit(retval)
        