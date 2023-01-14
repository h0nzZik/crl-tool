import argparse

from typing import (
    Final,
)

from pyk.ktool import kprove

_LOGGER: Final = logging.getLogger(__name__)

def main() -> None:
    #print("Hello")
    argument_parser = argparse.ArgumentParser(
        prog="crl-tool",
        description="A Cartesian Reachability Logic tool"
    )
    argument_parser.add_argument('-d', '--definition')
    args = argument_parser.parse_args()
    print(args)