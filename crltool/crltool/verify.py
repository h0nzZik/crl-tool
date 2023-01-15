import logging

from typing import (
    Any,
    Final,
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
    SortApp,
    String,
    SVar,
    Top,
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


# Checks an implication between two ECLPs.
# Returns a substitution or a None
#def eclp_check_impl(kc: KoreClient, Phi: ECLP, Psi:ECLP):
#    pass

