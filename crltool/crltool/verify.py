import logging

from itertools import (
    chain
)

from typing import (
    Any,
    Final,
    List,
    Optional,
)

from pyk.kore.rpc import (
    KoreClient
)

from pyk.kore.syntax import (
    And,
    App,
    Bottom,
    DV,
    Equals,
    EVar,
    Exists,
    Forall,
    Iff,
    Implies,
    In,
    Or,
    Not,
    Pattern,
    Sort,
    SortApp,
    String,
    SVar,
    Top,
)

from pyk.kore.manip import (
    free_occs
)

from .crl import (
    LP,
    CLP,
    ECLP,
    Claim,
)

from .kore_utils import (
    get_symbol_sort
)

from .ReachabilitySystem import (
    ReachabilitySystem
)

LOGGER: Final = logging.getLogger(__name__)

# But this will have a problem with predicate patterns
def to_FOL(rs: ReachabilitySystem, square_var : EVar, phi: Pattern) -> Pattern:
    match phi:
        # The main case
        case App(symbol_name, _, _):
            sort = get_symbol_sort(rs.definition, rs.main_module_name, symbol_name)
            if sort != square_var.sort:
                return phi
            return Equals(op_sort=SortApp('SortBool', ()),sort=sort, left=square_var, right=phi)
        # The recursive cases
        case Not(sort, pattern):
            return Not(sort, to_FOL(rs, square_var, pattern))
        case And(sort, left, right):
            return And(sort, to_FOL(rs, square_var, left), to_FOL(rs, square_var, right))
        case Or(sort, left, right):
            return Or(sort, to_FOL(rs, square_var, left), to_FOL(rs, square_var, right))
        case Implies(sort, left, right):
            return Implies(sort, to_FOL(rs, square_var, left), to_FOL(rs, square_var, right))
        case Iff(sort, left, right):
            return Iff(sort, to_FOL(rs, square_var, left), to_FOL(rs, square_var, right))
        case Exists(sort, var, pattern):
            return Exists(sort, var, to_FOL(rs, square_var, pattern))
        case Forall(sort, var, pattern):
            return Forall(sort, var, to_FOL(rs, square_var, pattern))
        # Base cases
        case Equals(_,_,_,_):
            return phi
        case In(_,_,_,_):
            return phi
        case DV(_,_):
            return phi
        case EVar(_, _):
            return phi
        case SVar(_, _):
            return phi
        case String(_):
            return phi
        case Top(_):
            return phi
        case Bottom(_):
            return phi
        case _:
            raise NotImplementedError()

def int_or_None(s: str) -> Optional[int]:
    try:
        return int(s)
    except:
        return None

def get_fresh_evars(avoid: List[EVar], sort: Sort, prefix="Fresh", length=1) -> List[EVar]:
    names_to_avoid = map(lambda ev: ev.name, avoid)
    names_with_prefix_to_avoid : List[str] = [name for name in names_to_avoid if name.startswith(prefix)]
    suffixes_to_avoid : List[str] = [name.removeprefix(prefix) for name in names_with_prefix_to_avoid]
    nums_to_avoid : List[int] = [ion for ion in map(int_or_None, suffixes_to_avoid) if ion is not None]
    n : int = max(nums_to_avoid) + 1
    nums = list(range(n, n + length))
    fresh_evars : List[EVar] = list(map(lambda n: EVar(name=prefix + str(n), sort=sort), nums))
    return fresh_evars


def lp_to_pattern(rs: ReachabilitySystem, lp: LP) -> Pattern:
    ll : List[List[EVar]] = list(map(lambda p: list(chain.from_iterable(free_occs(p).values())), lp.patterns))
    list_free_vars = chain.from_iterable(ll)
    free_vars = list(list_free_vars)

    fresh_vars = get_fresh_evars(free_vars, sort=None, prefix="Component", length=len(lp.patterns))
    map(lambda pvar: to_FOL(rs, pvar[1], pvar[0]), zip(lp.patterns, fresh_vars))
    raise NotImplementedError()

def clp_to_pattern(rs: ReachabilitySystem, clp: CLP) -> Pattern:
    raise NotImplementedError()

def claim_to_pattern(rs: ReachabilitySystem, claim: Claim) -> Pattern:
    raise NotImplementedError()

# Checks an implication between two ECLPs.
# Returns a substitution or a None
#def eclp_check_impl(kc: KoreClient, Phi: ECLP, Psi:ECLP):
#    pass

