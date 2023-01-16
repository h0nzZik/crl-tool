import argparse
import json
import logging

from pathlib import Path

from typing import (
    Final,
)

from pyk.kore.syntax import (
    Pattern,
    Top,
    Not,
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
    subparsers = argument_parser.add_subparsers(dest='command')
    subparser_check_implication = subparsers.add_parser('check-implication', help='Checks whether the specification holds trivially')
    subparser_check_implication.add_argument('--specification', required=True)
    subparser_check_implication.add_argument('--query-file', required=True)
    subparser_check_implication.add_argument('--output-file', required=True)
    subparser_prove = subparsers.add_parser('prove', help='Prove a specification')
    subparser_prove.add_argument('--specification', required=True)
    return argument_parser

def main() -> None:
    argument_parser = create_argument_parser()
    args = vars(argument_parser.parse_args())
    #print(args)
    with ReachabilitySystem(definition_dir=Path(args['definition'])) as rs:
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
            return
        if args['command'] == 'prove':
            print("Dummy proving...")
    
    print("Other command")

        