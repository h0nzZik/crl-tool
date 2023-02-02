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
        return LP([p for p in self.patterns])


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
        return ECLP([e.copy() for e in self.vars], self.clp.copy())
    
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
    claims: Dict[str, Claim]
    trusted_claims: Dict[str, Claim]
    cutpoints: Dict[str, ECLP] # TODO I am not sure if the existential variables are needed
    rl_circularities : Dict[str, RLCircularity]

    @staticmethod
    def from_dict(dct: Mapping[str, Any]) -> 'Specification':
        return Specification(
            claims={k: Claim.from_dict(v) for k,v in dct['claims'].items()},
            trusted_claims={k: Claim.from_dict(v) for k,v in dct['trusted_claims'].items()},
            cutpoints={k: ECLP.from_dict(v) for k,v in dct['cutpoints'].items()},
            rl_circularities={k : RLCircularity.from_dict(v) for k,v in dct['rl_circularities'].items()},
        )
    
    @property
    def dict(self) -> Dict[str, Any]:
        return {
            'claims': {k : v.dict for k,v in self.claims.items()},
            'trusted_claims': {k : v.dict for k,v in self.trusted_claims.items()},
            'cutpoints': {k : v.dict for k,v in self.cutpoints.items()},
            'rl_circularities': {k : v.dict for k,v in self.rl_circularities.items()}
        }