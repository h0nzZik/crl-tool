import argparse
import json
import logging

from pathlib import Path

from typing import (
    Final,
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
    subparser_prove = subparsers.add_parser('prove', help='Prove a specification')
    subparser_prove.add_argument('--specification', required=True)
    return argument_parser

def main() -> None:
    argument_parser = create_argument_parser()
    args = vars(argument_parser.parse_args())
    if args['command'] == 'prove':
        with ReachabilitySystem(definition_dir=Path(args['definition'])) as rs:
            with open(args['specification'], 'r') as spec_f:
                claim = Claim.from_dict(json.loads(spec_f.read()))
            print(rs.top_sort)
            print(eclp_impl_to_pattern(rs, claim.antecedent, claim.consequent))
            #print(claim)
            #print(get_top_cell_initializer(rs.definition))
            pass
        return
    
    print("Other command")

        