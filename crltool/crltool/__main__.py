import argparse
import json
import logging
import time

from pathlib import Path

from typing import (
    Final,
    Tuple,
)

from pyk.kore.syntax import (
    Pattern,
    Top,
    Not,
)

from pyk.kore.parser import (
    KoreParser
)

from pyk.ktool.kprint import (
    KPrint
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
    eclp_impl_to_pattern
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
    subparser_check_implication.add_argument('--query-file', required=True)
    subparser_check_implication.add_argument('--output-file', required=True)
    
    subparser_prove = subparsers.add_parser('prove', help='Prove a specification')
    subparser_prove.add_argument('--specification', required=True)

    subparser_simplify = subparsers.add_parser('simplify', help='Simplify a pattern')
    subparser_simplify.add_argument('--pattern', required=True)
    subparser_simplify.add_argument('--output-file', required=True)
    subparser_simplify.add_argument('--try-impl', type=bool, default=False)

    subparser_check_impl_direct = subparsers.add_parser('check-implication-directly', help='Simplify a pattern')
    subparser_check_impl_direct.add_argument('--hackit', type=bool, default=False)
    subparser_check_impl_direct.add_argument('--pattern', required=True)
    
    return argument_parser

def main() -> None:
    argument_parser = create_argument_parser()
    args = vars(argument_parser.parse_args())
    logging.basicConfig(filename='crl-tool.log', encoding='utf-8', level=logging.DEBUG)
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
            with open(args['specification'], 'r') as spec_f:
                claim = Claim.from_dict(json.loads(spec_f.read()))
            pat0 = eclp_impl_to_pattern(rs, claim.antecedent, claim.consequent)
            #pat = Not(rs.top_sort, pat0)
            pat = pat0
            print(pat)
            with open(args['query_file'], 'w') as fw:
                fw.write(pat.text)
            patsimpl : Pattern = rs.kcs.client.simplify(pat)
            print(patsimpl.text)
            with open(args['output_file'], 'w') as fw:
                fw.write(patsimpl.text)
            #impl_result = rs.kcs.client.implies(Top(rs.top_sort), pat)
            #print(impl_result)
        elif args['command'] == 'prove':
            print("Dummy proving...")
        elif args['command'] == 'check-implication-directly':
            with open(args['pattern'], 'r') as fr:
                pat = KoreParser(fr.read()).pattern()
            kp = KPrint(args['definition'])                
            print('Input')
            print(kp.kore_to_pretty(pat))
            if args['hackit']:
                kprove = KProve(definition_dir=args['definition'], port=3001, use_directory=Path("./mytemp"))
                src = CTerm(kp.kore_to_kast(pat.left))
                print(src)
                tgt = CTerm(kp.kore_to_kast(pat.right))
                print(tgt)
                result = kprove.prove_cterm(claim_id='my-claim', init_cterm=src, target_cterm=tgt, depth=0, allow_zero_step=True)
                print(result)
                pass
            else:
                impl_result = rs.kcs.client.implies(pat.left, pat.right)
                print('Simplified')
                print(kp.kore_to_pretty(impl_result.implication))
                #print(impl_result.implication.text)
                if (impl_result.satisfiable):
                    print("Satisfiable")
                else:
                    print("Unsatisfiable")
                if impl_result.substitution is not None:
                    print("Substitution:")
                    print(kp.kore_to_pretty(impl_result.substitution))
                    #print(impl_result.substitution.text)
                if impl_result.predicate is not None:
                    print("Predicate:")
                    print(kp.kore_to_pretty(impl_result.predicate))
                    #print(impl_result.predicate.text)
            
        elif args['command'] == 'simplify':
            with open(args['pattern'], 'r') as fr:
                pat = KoreParser(fr.read()).pattern()
            patsimpl0 : Pattern = rs.kcs.client.simplify(pat)
            print(patsimpl0.text)
            with open(args['output_file'], 'w') as fw:
                fw.write(patsimpl0.text)
            if args['try_impl']:
                impl_result = rs.kcs.client.implies(pat.left, pat.right)
                print(impl_result)
                

        