import logging

from typing import (
    Any,
    Final,
)

from pyk.kore.rpc import (
    KoreClient
)

from pyk.kore.syntax import (
    App,
    EVar,
    Equals,
    Pattern,
    SortApp,
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
def to_FOL(rs: ReachabilitySystem, phi: Pattern, square_var : EVar) -> Pattern:
    def _app_to_equality(p: Pattern) -> Pattern:
        match p:
            case App(symbol_name, _, _):
                sort = get_symbol_sort(rs.definition, rs.main_module_name, symbol_name)
                if sort != square_var.sort:
                    return p
                return Equals(op_sort=SortApp('SortBool', ()),sort=sort, left=square_var, right=p)
            case _:
                return p
    return phi.bottom_up(_app_to_equality)


# Checks an implication between two ECLPs.
# Returns a substitution or a None
def eclp_check_impl(kc: KoreClient, Phi: ECLP, Psi:ECLP):
    pass

