from pathlib import Path

from typing import (
    Any,
    Final,
)

from pyk.kore.rpc import (
    KoreServer,
    KoreClient
)

from pyk.kore.parser import (
    KoreParser
)

from pyk.kore.syntax import (
    Definition
)

from .kcommands import KORE_RPC_COMMAND

class KoreClientServer:
    server: KoreServer
    client: KoreClient

    def __init__(self, definition_dir: Path, main_module_name: str):
        port = 3000
        self.server = KoreServer(kompiled_dir=definition_dir, module_name=main_module_name, command=KORE_RPC_COMMAND, port=port)
        self.client = KoreClient('localhost', port=port)
    
    def __enter__(self) -> 'KoreClientServer':
        return self

    def __exit__(self, *args: Any) -> None:
        self.client.close()
        self.server.close()

class ReachabilitySystem:
    kcs: KoreClientServer
    definition: Definition
    main_module_name: str

    def __init__(self, definition_dir: Path):
        with open(definition_dir / 'mainModule.txt', 'r') as mm:
            self.main_module_name = mm.read()
        with open(definition_dir / 'definition.kore', 'r') as dc:
            d = dc.read()
        print(d)
        self.definition = KoreParser(d).definition()
        self.kcs = KoreClientServer(definition_dir=definition_dir, main_module_name=self.main_module_name)

    def __enter__(self) -> 'ReachabilitySystem':
        return self

    def __exit__(self, *args: Any) -> None:
        self.kcs.__exit__()