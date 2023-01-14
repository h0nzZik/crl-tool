import argparse
import logging
from pathlib import Path

from typing import (
    Any,
    Final,
)

from pyk.kore.rpc import (
    KoreServer,
    KoreClient
)

from .kcommands import KORE_RPC_COMMAND

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

class KoreClientServer:
    server: KoreServer
    client: KoreClient

    def __init__(self, definition_dir: Path):
        port = 3000
        with open(definition_dir / 'mainModule.txt', 'r') as mm:
            main_module = mm.read()
        self.server = KoreServer(kompiled_dir=definition_dir, module_name=main_module, command=KORE_RPC_COMMAND, port=port)
        self.client = KoreClient('localhost', port=port)
    
    def __enter__(self) -> 'KoreClientServer':
        return self

    def __exit__(self, *args: Any) -> None:
        self.client.close()
        self.server.close()

def main() -> None:
    #print("Hello")
    argument_parser = create_argument_parser()
    args = vars(argument_parser.parse_args())
    #print(args)
    if args['command'] == 'prove':
        with KoreClientServer(definition_dir= Path(args['definition'])) as kcs:
            print(kcs)
            with open(args['specification'], 'r') as spec_f:
                print(kcs.client)
                pass
        return
    
    print("Other command")

        