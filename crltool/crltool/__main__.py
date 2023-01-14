import argparse
import logging

from typing import (
    Final,
)

from pyk.ktool.kprove import KProve

from .kcommand import KORE_RPC_COMMAND

_LOGGER: Final = logging.getLogger(__name__)

def create_argument_parser() -> argparse.ArgumentParser:
    argument_parser = argparse.ArgumentParser(
        prog="crl-tool",
        description="A Cartesian Reachability Logic tool"
    )
    argument_parser.add_argument('-d', '--definition')
    subparser_prove = argument_parser.add_parser('prove', help='Prove a specification')
    subparser_prove.add_argument('--specification', required=True)
    return argument_parser

def main() -> None:
    #print("Hello")
    argument_parser = create_argument_parser()
    args = argument_parser.parse_args()
    #print(args)
    if args['command'] == 'prove':
        with KProve(definition_dir=args['definition']) as kprove:
            print(kprove)
            pass
        return
    
    print("Other command")

        