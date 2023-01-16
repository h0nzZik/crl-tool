import logging

from functools import (
    reduce
)

from itertools import (
    chain
)

from typing import (
    Any,
    Final,
    List,
    Optional,
    Set,
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


def free_evars_of_pattern(p: Pattern) -> Set[EVar]:
    return set(chain.from_iterable(free_occs(p).values()))

def free_evars_of_lp(lp: LP) -> Set[EVar]:
    return set(chain.from_iterable(map(lambda p: free_evars_of_pattern(p), lp.patterns)))

def free_evars_of_clp(clp : CLP) -> Set[EVar]:
    return free_evars_of_lp(clp.lp).union(free_evars_of_pattern(clp.constraint))

# For the purposes of fresh variable generation we do not care that some evars are bound.
# In the worst case, we will generate variables that are fresher than necessary.
def approximate_free_evars_of_eclp(eclp : ECLP) -> Set[EVar]:
    return free_evars_of_clp(eclp.clp)

def eclp_impl_to_pattern(rs: ReachabilitySystem, antecedent : ECLP, consequent: ECLP) -> Pattern:
    # We can strip the quantifiers of antecedent.
    # The task is, roughly, to check that
    # |= (exists x. phi) -> (exists y. psi)
    # which is equivalent to
    # |= forall x. (phi -> (exists y. psi)
    # which is equivalent to
    # |= phi -> (exists y. psi)
    if (len(antecedent.clp.lp.patterns) != len(consequent.clp.lp.patterns)):
        raise ValueError("The antecedent and consequent have different arity.")
    arity = len(antecedent.clp.lp.patterns)
    vars_to_avoid = free_evars_of_clp(antecedent.clp).union(approximate_free_evars_of_eclp(consequent))
    fresh_vars = get_fresh_evars(list(vars_to_avoid), sort=rs.top_sort, prefix="Component", length=arity)
    ante_preds : List[Pattern] = list(map(lambda pvar: And(rs.top_sort, to_FOL(rs, pvar[1], pvar[0]), antecedent.clp.constraint), zip(antecedent.clp.lp.patterns, fresh_vars)))
    cons_preds : List[Pattern] = list(map(lambda pvar: And(rs.top_sort, to_FOL(rs, pvar[1], pvar[0]), consequent.clp.constraint), zip(consequent.clp.lp.patterns, fresh_vars)))
    implications : List[Pattern] = list(map(lambda t: Implies(rs.top_sort, t[0], t[1]), zip(ante_preds, cons_preds)))
    result = reduce(lambda a,b : And(rs.top_sort, a, b), implications)
    return result
    


def lp_to_pattern(rs: ReachabilitySystem, lp: LP) -> Pattern:
    ll : List[List[EVar]] = list(map(lambda p: list(chain.from_iterable(free_occs(p).values())), lp.patterns))
    free_vars : List[EVar] = list(chain.from_iterable(ll))

    fresh_vars = get_fresh_evars(free_vars, sort=None, prefix="Component", length=len(lp.patterns))
    fols : List[Pattern] = map(lambda pvar: to_FOL(rs, pvar[1], pvar[0]), zip(lp.patterns, fresh_vars))
    return reduce(lambda a, b: And(SortApp('SortBool', ()), a, b), fols)

def clp_to_pattern(rs: ReachabilitySystem, clp: CLP) -> Pattern:
    return And(SortApp('SortBool', ()), lp_to_pattern(rs, clp.lp), clp.constraint)

def eclp_to_pattern(rs: ReachabilitySystem, eclp: ECLP) -> Pattern:
    pat = clp_to_pattern(rs, eclp.clp)
    return reduce(lambda p, var: Exists(SortApp('SortBool', ()), var, p), eclp.vars, pat)

def claim_to_pattern(rs: ReachabilitySystem, claim: Claim) -> Pattern:
    ante_p = eclp_to_pattern(rs, claim.antecedent)
    cons_p = eclp_to_pattern(rs, claim.consequent)
    raise NotImplementedError()

# Checks an implication between two ECLPs.
# Returns a substitution or a None
#def eclp_check_impl(kc: KoreClient, Phi: ECLP, Psi:ECLP):
#    pass

