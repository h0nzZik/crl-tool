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

from .ReachabilitySystem import ReachabilitySystem

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
    #print("Hello")
    argument_parser = create_argument_parser()
    args = vars(argument_parser.parse_args())
    #print(args)
    if args['command'] == 'prove':
        with ReachabilitySystem(definition_dir=Path(args['definition'])) as rs:
            #print(kcs)
            with open(args['specification'], 'r') as spec_f:
                claim = Claim.from_dict(json.loads(spec_f.read()))
            #print(kcs.client)
            print(claim)
            pass
        return
    
    print("Other command")

        