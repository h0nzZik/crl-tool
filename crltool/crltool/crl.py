from dataclasses import dataclass

from pyk.kore.syntax import (
    EVar,
    Sort,
    Pattern,
)

from typing import (
    Tuple,
    final,
)

@final
@dataclass
class LP:
    patterns: Tuple[Pattern, ...]

@final
@dataclass
class CLP:
    lp: LP
    constraint: Pattern

@final
@dataclass
class ECLP:
    vars: Tuple[Tuple[Sort, EVar], ...]
    clp: CLP

@final
@dataclass
class Claim:
    antecedent: ECLP
    consequent: ECLP