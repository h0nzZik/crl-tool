from dataclasses import dataclass

from pyk.kore.syntax import (
    EVar,
    Sort,
    Pattern,
)

from typing import (
    Any,
    Dict,
    List,
    Mapping,
    Tuple,
    final,
)

@final
@dataclass
class LP:
    patterns: List[Pattern]

    @staticmethod
    def from_dict(dct: Mapping[str, Any]) -> 'LP':
        return LP(list(map(Pattern.from_dict, dct['patterns'])))

    @property
    def dict(self) -> Dict[str, Any]:
        return {'patterns': list(map(lambda p: p.dict, self.patterns))}


@final
@dataclass
class CLP:
    lp: LP
    constraint: Pattern
    
    @staticmethod
    def from_dict(dct: Mapping[str, Any]) -> 'CLP':
        return CLP(LP.from_dict(dct['lp']), Pattern.from_dict(dct['constraint']))
    
    @property
    def dict(self) -> Dict[str, Any]:
        return {'lp': self.lp.dict, 'constraint': self.constraint.dict}

@final
@dataclass
class ECLP:
    vars: List[EVar]
    clp: CLP

    @staticmethod
    def from_dict(dct: Mapping[str, Any]) -> 'ECLP':
        return ECLP(list(map(EVar.from_dict, dct['vars'])), CLP.from_dict(dct['clp']))
    
    @property
    def dict(self) -> Dict[str, Any]:
        return {'vars': list(map(lambda v: v.dict, self.vars)), 'clp': self.clp.dict}

@final
@dataclass
class Claim:
    antecedent: ECLP
    consequent: ECLP

    @staticmethod
    def from_dict(dct: Mapping[str, Any]) -> 'Claim':
        return Claim(ECLP.from_dict(dct['antecedent']), ECLP.from_dict(dct['consequent']))
    
    @property
    def dict(self) -> Dict[str, Any]:
        return {'antecedent': self.antecedent.dict, 'consequent': self.consequent.dict}
