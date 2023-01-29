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
    
    def copy(self):
        return LP(self.patterns.copy())


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
    
    def copy(self):
        return CLP(self.lp.copy(), self.constraint)

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
    
    def copy(self):
        return ECLP(self.vars.copy(), self.clp.copy())
    
    def with_no_vars(self):
        return ECLP([], self.clp.copy())

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


@final
@dataclass
class RLCircularity:
    antecedent: Pattern
    consequent: Pattern

    @staticmethod
    def from_dict(dct: Mapping[str, Any]) -> 'RLCircularity':
        return RLCircularity(Pattern.from_dict(dct['antecedent']), Pattern.from_dict(dct['consequent']))
    
    @property
    def dict(self) -> Dict[str, Any]:
        return {'antecedent': self.antecedent.dict, 'consequent': self.consequent.dict}


@final
@dataclass
class Specification:
    claims: List[Claim]
    cutpoints: List[CLP]
    rl_circularities : List[RLCircularity]

    @staticmethod
    def from_dict(dct: Mapping[str, Any]) -> 'Specification':
        return Specification(
            claims=list(map(lambda c: Claim.from_dict(c), dct['claims'])),
            cutpoints=list(map(lambda c: CLP.from_dict(c), dct['cutpoints'])),
            rl_circularities=list(map(lambda c: RLCircularity.from_dict(c), dct['rl_circularities'])),
        )
    
    @property
    def dict(self) -> Dict[str, Any]:
        return {
            'claims': list(map(lambda c: c.dict, self.claims)),
            'cutpoints': list(map(lambda c: c.dict, self.cutpoints)),
            'rl_circularities': list(map(lambda c: c.dict, self.rl_circularities))
        }