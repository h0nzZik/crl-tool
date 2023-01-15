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

LOGGER: Final = logging.getLogger(__name__)

#def to_FOL(phi: Pattern) -> Pattern:
#    def _app_to_equality(p: Pattern) -> Pattern:
#        match p:
#            case App(symbol, sorts, args):
#                pass
#                #return Equals(op_sort=SortApp('SortBool', ()))


# Checks an implication between two ECLPs.
# Returns a substitution or a None
def eclp_check_impl(kc: KoreClient, Phi: ECLP, Psi:ECLP):
    pass

