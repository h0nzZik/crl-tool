import json

from pathlib import Path
from tempfile import NamedTemporaryFile
from typing import (
    Any,
    Dict,
)


from pyk.utils import run_process

from .kcommands import KPROVE_COMMAND
from .ReachabilitySystem import ReachabilitySystem

def get_kprove_generated_json(rs: ReachabilitySystem, specification: Path) -> Dict[str, Any]:
    with NamedTemporaryFile() as f:
        command = [
            KPROVE_COMMAND,
            '--dont-prove',
            '--definition',
            str(rs.definition_dir),
            '--emit-json-spec',
            f.name,
            str(specification),

        ]
        rv = run_process(command)
        if rv.returncode != 0:
            raise RuntimeError(f"krove returned a nonzero value: {rv.returncode}")
        return json.loads(f.read())