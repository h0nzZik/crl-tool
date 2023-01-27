import logging
import json
import time
import pygtrie # type: ignore

from abc import (
    ABC,
    abstractmethod,
)

from collections.abc import Iterable

from dataclasses import dataclass

from functools import (
    reduce,
)

from itertools import (
    chain,
    product,
)

from typing import (
    Any,
    Callable,
    Dict,
    Final,
    List,
    Mapping,
    Optional,
    Set,
    Tuple,
    Union,
    final,
)

from pyk.kore.rpc import (
    ImpliesResult,
    KoreClient,
    ExecuteResult,
    StopReason,
    State
)

from pyk.kore.syntax import (
    And,
    App,
    Bottom,
    DV,
    Equals,
    EVar,
    Exists,
    Floor,
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

_LOGGER: Final = logging.getLogger(__name__)

# But this will have a problem with predicate patterns
def to_FOL(rs: ReachabilitySystem, square_var : EVar, phi: Pattern) -> Pattern:
    match phi:
        # The main case
        case App(symbol_name, _, _):
            sort = get_symbol_sort(rs.definition, rs.main_module_name, symbol_name)
            #if sort != square_var.sort:
            if sort != rs.top_sort:
                return phi
            return Equals(op_sort=rs.top_sort,sort=sort, left=square_var, right=phi)
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
    if len(list(nums_to_avoid)) >= 1:
        n = max(nums_to_avoid) + 1
    else:
        n = 0
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
    # which is (assuming x \not\in FV(exists y, psi)) equivalent to
    # |= forall x. (phi -> (exists y. psi)
    # which is equivalent to
    # |= phi -> (exists y. psi)
    ## which (assuming y \not\in FV(phi)) is equivalent to
    ## |= exists y. ( phi -> psi)
    arity = len(antecedent.clp.lp.patterns)
    if (arity != len(consequent.clp.lp.patterns)):
        raise ValueError("The antecedent and consequent have different arity.")
    antecedent_fv = free_evars_of_clp(antecedent.clp)
    #intersecting_vars = antecedent_fv.intersection(consequent.vars)
    #if len(list(intersecting_vars)) >= 1:
    #    raise NotImplementedError(f"The antecedent contains variables {intersecting_vars} which are existentially quantified in the consequent; this is not supported yet")

    vars_to_avoid = antecedent_fv.union(approximate_free_evars_of_eclp(consequent))
    fresh_vars = get_fresh_evars(list(vars_to_avoid), sort=rs.top_sort, prefix="Component", length=arity)
    #ante_preds : List[Pattern] = list(map(lambda pvar: And(rs.top_sort, to_FOL(rs, pvar[1], pvar[0]), antecedent.clp.constraint), zip(antecedent.clp.lp.patterns, fresh_vars)))
    #cons_preds : List[Pattern] = list(map(lambda pvar: And(rs.top_sort, to_FOL(rs, pvar[1], pvar[0]), consequent.clp.constraint), zip(consequent.clp.lp.patterns, fresh_vars)))
    ante_preds : List[Pattern] = list(map(lambda pvar: to_FOL(rs, pvar[1], pvar[0]), zip(antecedent.clp.lp.patterns, fresh_vars)))
    cons_preds : List[Pattern] = list(map(lambda pvar: to_FOL(rs, pvar[1], pvar[0]), zip(consequent.clp.lp.patterns, fresh_vars)))
    ante_conj : Pattern = And(rs.top_sort, reduce(lambda a,b : And(rs.top_sort, a, b), ante_preds), antecedent.clp.constraint)
    cons_conj : Pattern = And(rs.top_sort, reduce(lambda a,b : And(rs.top_sort, a, b), cons_preds), consequent.clp.constraint)
    cons_ex : Pattern = reduce(lambda p, var: Exists(rs.top_sort, var, p), consequent.vars, cons_conj)
    #implications : List[Pattern] = list(map(lambda t: Implies(rs.top_sort, t[0], t[1]), zip(ante_preds, cons_preds)))
    #impl = reduce(lambda a,b : And(rs.top_sort, a, b), implications)
    impl : Pattern = Implies(rs.top_sort, ante_conj, cons_ex)
    return impl
    #result = reduce(lambda p, var: Exists(rs.top_sort, var, p), consequent.vars, impl)
    #return result



def extract_equalities_from_witness(expected_vars : Set[EVar], witness : Pattern) -> Dict[EVar, Pattern]:
    result : Dict[EVar, Pattern] = dict()
    def go(w : Pattern):
        match w:
            case And(_, l, r):
                go(l)
                go(r)
                return
            case Equals(_, _, l, r):
                if type(l) is EVar and l in expected_vars:
                    result[l] = r
                    return
                if type(r) is EVar and r in expected_vars:
                    result[r] = l
                    return
                raise ValueError(f"Unexpected equality '{l} = {r}' in the witness {witness}")
            case _:
                return

    go(witness)
    return result

def equalities_to_pattern(rs: ReachabilitySystem, eqls : Dict[EVar, Pattern]) -> Pattern:
    pairs : List[Tuple[EVar, Pattern]] = [(k, eqls[k]) for k in eqls]
    list_of_equalities : List[Pattern] = list(map(lambda p: Equals(rs.top_sort, p[0].sort, p[0], p[1]), pairs))
    initial : Pattern = Top(rs.top_sort)
    conj : Pattern = reduce(lambda a,b : And(rs.top_sort, a, b), list_of_equalities, initial)
    return conj

@final
@dataclass(frozen=True)
class EclpImpliesResult:
    valid: bool
    witness: Optional[Pattern]

# Assumes (A1) that antecedent does not contain (free or bound) variables from consequent.vars.
# This is wlog, since one can alpha-rename the bound variables of the consequent.
#
# If the return value is [True], then antecedent ---> consequent.
# More precisely, then:
# forall (cfgs : Vec{Cfg, k}) (rho : Valuation),
#   (rho |= antecedent.clp.constraint /\ forall i in range(0, k), (cfgs[i], rho) |= antecedent.clp.lp.patterns[i]) ->
#   exists (rho2 : Valuation), (rho2 is the same as rho except on consequent.vars) /\
#   (rho2 |= consequent.clp.constraint /\ forall i in range(0, k), (cfgs[i], rho2) |= consequent.clp.lp.patterns[i]).
def eclp_impl_valid(rs: ReachabilitySystem, antecedent : ECLP, consequent: ECLP) -> EclpImpliesResult:
    arity = len(antecedent.clp.lp.patterns)
    if (arity != len(consequent.clp.lp.patterns)):
        raise ValueError("The antecedent and consequent have different arity.")
    
    witness : Pattern = Top(rs.top_sort)
    for i in range(0, arity):
        # Inv1:
        # ```
        # forall (cfgs : Vec{Cfg, k}) (rho : Valuation),
        #   (rho |= antecedent.clp.constraint /\ forall j in range(0, i), (cfgs[j], rho) |= antecedent.clp.lp.patterns[j]) ->
        #   exists (rho2 : Valuation), (rho2 is the same as rho except on consequent.vars) /\
        #   (rho2 |= consequent.clp.constraint /\ forall j in range(0, i), (cfgs[j], rho2) |= consequent.clp.lp.patterns[j]).
        # ```
        # Inv2:
        # ```
        # forall (j : range(0, i)) (rho : Valuation) (cfg : Cfg),
        #   (rho |= witness) ->
        #   ((cfg, rho) |= antecedent.clp.lp.patterns[j]) ->
        #   ((cfg, rho) |= consequent.clp.lp.patterns[j]) .
        # ```
        lhs : Pattern = And(rs.top_sort, antecedent.clp.lp.patterns[i], antecedent.clp.constraint)
        free_evars_of_lhs : Set[EVar] = free_evars_of_pattern(lhs)
        equalities : Dict[EVar, Pattern] = extract_equalities_from_witness(set(consequent.vars), witness)
        #print(f"Equalities: {equalities}")
        filtered_equalities : Dict[EVar, Pattern] = {k : equalities[k] for k in equalities if free_evars_of_pattern(equalities[k]).issubset(set(consequent.vars).union(free_evars_of_lhs))} 
        #print(f"Filtered equalities: {filtered_equalities}")
        ## @ghost_variable
        #unfiltered_equalities : Dict[EVar, Pattern] = {k : equalities[k] for k in equalities if free_evars_of_pattern(equalities[k]).issubset(set(consequent.vars).union(free_evars_of_lhs))} 
        #print(f"Unfiltered equalities: {unfiltered_equalities}")
        filtered_witness : Pattern = equalities_to_pattern(rs, filtered_equalities)
        ## @ghost_variable
        #unfiltered_witness = equalities_to_pattern(rs, unfiltered_equalities)
        # Now we asume (Hwitfwitunfwit)
        # |= witness <-> filtered_witness /\ unfiltered_witness

        rhs_body : Pattern = And(rs.top_sort, consequent.clp.lp.patterns[i], And(rs.top_sort, consequent.clp.constraint, filtered_witness))
        rhs : Pattern = reduce(lambda p, var: Exists(rs.top_sort, var, p), consequent.vars, rhs_body)
        try:
            result : ImpliesResult = rs.kcs.client.implies(lhs, rhs)
        except:
            _LOGGER.error(f"Implication check failed on the position {i}, with lhs={lhs} and rhs={rhs}")
            raise
        if result.satisfiable != True:
            return EclpImpliesResult(False, None)
        if (result.substitution is None):
            raise RuntimeError("Satisfable, but no witness was given")
        new_witness : Pattern = result.substitution
        #print(f"new_witness: {new_witness}")
        # Furthermore, (Inv1) still holds, and in addition, we have (2) (from the would-be contract of `implies`) saying that:
        # ```
        # |= antecedent.clp.lp.patterns[i] ---> exists \vec{consequent.vars}, (consequent.clp.lp.patterns[i] /\ consequent.clp.constraint /\ filtered_witness) /\ new_witness
        # ```
        # And I believe that the semantics of the witness guarantees something in addition (3), saying that
        # ```
        # |= antecedent.clp.lp.patterns[i] ---> forall \vec{consequent.vars}, (new_witness --> (consequent.clp.lp.patterns[i] /\ consequent.clp.constraint /\ filtered_witness))
        # ```

        # We want to show that we preserve Inv2.
        # In other words, we have to show that at this point, it holds (Inv2') that
        # ```
        # forall (j : range(0, i+1)) (rho : Valuation) (cfg : Cfg),
        #   (rho |= witness /\ new_witness) ->
        #   ((cfg, rho) |= antecedent.clp.lp.patterns[j]) ->
        #   ((cfg, rho) |= consequent.clp.lp.patterns[j]) .
        # ```
        # This is equivalent to showing
        # ```
        # forall (j : range(0, i)) (rho : Valuation) (cfg : Cfg),
        #   (rho |= witness /\ new_witness) ->
        #   ((cfg, rho) |= antecedent.clp.lp.patterns[j]) ->
        #   ((cfg, rho) |= consequent.clp.lp.patterns[j]) .
        # ```
        # and
        # ```
        # forall (rho : Valuation) (cfg : Cfg),
        #   (rho |= witness /\ new_witness) ->
        #   ((cfg, rho) |= antecedent.clp.lp.patterns[i]) ->
        #   ((cfg, rho) |= consequent.clp.lp.patterns[i]) .
        # ```
        # Inv2 still holds, since we haven't modified any variables, only added new ones.
        # The first goal holds because (rho |= witness /\ new_witness) -> (rho |= witness), and we can use Inv2.
        # For the second goal, let us have
        #   rho : Valuation
        #   cfg : Cfg
        #   H1: rho |= witness /\ new_witness
        #   H2: (cfg, rho) |= antecedent.clp.lp.patterns[i]
        # and goal
        #   (cfg, rho) |= consequent.clp.lp.patterns[i] .
        # which follows directly from (3) by the semantics of matching logic.

        # We also want to show that we preserve Inv1.
        # At this point, we need to prove the folowing:
        # ```
        # forall (cfgs : Vec{Cfg, k}) (rho : Valuation),
        #   (rho |= antecedent.clp.constraint /\ forall j in range(0, i+1), (cfgs[j], rho) |= antecedent.clp.lp.patterns[j]) ->
        #   exists (rho2 : Valuation), (rho2 is the same as rho except on consequent.vars) /\
        #   (rho2 |= consequent.clp.constraint /\ forall j in range(0, i+1), (cfgs[j], rho2) |= consequent.clp.lp.patterns[j]).
        # ```
        # which is equivalent to:
        # ```
        # forall (cfgs : Vec{Cfg, k}) (rho : Valuation),
        #   (rho |= antecedent.clp.constraint
        #    /\ (cfgs[i], rho) |= antecedent.clp.lp.patterns[i]
        #    /\ (forall j in range(0, i), (cfgs[j], rho) |= antecedent.clp.lp.patterns[j])
        #   ) ->
        #   exists (rho2 : Valuation),
        #     (rho2 is the same as rho except on consequent.vars)
        #     /\ (rho2 |= consequent.clp.constraint
        #     /\ (cfgs[i], rho2) |= consequent.clp.lp.patterns[i])
        #     /\ (forall j in range(0, i), (cfgs[j], rho2) |= consequent.clp.lp.patterns[j])).
        # ```
        # Ok, let us have
        #   cfgs : Vec{Cfg, k}
        #   rho : Valuation
        # arbitrary, and in addition
        #   H1: rho |= antecedent.clp.constraint
        #   H2: (cfgs[i], rho) |= antecedent.clp.lp.patterns[i]
        #   H3: (forall j in range(0, i), (cfgs[j], rho) |= antecedent.clp.lp.patterns[j])
        # ; we have to prove that
        # ```
        #   exists (rho2 : Valuation),
        #     (rho2 is the same as rho except on consequent.vars)
        #     /\ (rho2 |= consequent.clp.constraint
        #     /\ (cfgs[i], rho2) |= consequent.clp.lp.patterns[i])
        #     /\ (forall j in range(0, i), (cfgs[j], rho2) |= consequent.clp.lp.patterns[j])).
        # ```
        # We first use `((Inv1), cfgs, rho. H1, H3` to obtain
        # ```
        #   rho2: Valuation
        #   Hrho2rho: rho2 is the same as rho except on consequent.vars
        #   Hrho2constr: rho2 |= consequent.clp.constraint
        #   Hrho2i: forall j in range(0, i), (cfgs[j], rho2) |= consequent.clp.lp.patterns[j]
        # ```
        # Now, if we tried to let `rho2 := rho2`, we would have troubles proving
        # that `(cfgs[i], rho2) |= consequent.clp.lp.patterns[i])`.
        # So we postpone instantiating rho2 until we know better.
        # We still have (2).
        # Using (2) together with H2, we obtain
        #   H2': (cfgs[i], rho) |= exists \vec{consequent.vars}, (consequent.clp.lp.patterns[i] /\ consequent.clp.constraint /\ filtered_witness) /\ new_witness
        # In other words, by semantics of the logic, we obtain some
        #   rho': Valuation
        #   Hrho'rho: rho' is the same as rho except on consequent.vars
        #   Hrho'i: (cfgs[i], rho') |= consequent.clp.lp.patterns[i]
        #   Hrho'c: (cfgs[i], rho') |= consequent.clp.constraint
        #   Hrho'w: (cfgs[i], rho') |= filtered_witness
        #   Hrho'nw: (cfgs[i], rho') |= new_witness
        #
        # Note that in general, we do not have (cfgs[i], rho') |= unfiltered_witness.
        # But surely there exists a valuation rho'' such that
        #   Hrho''uf: (cfgs[i], rho'') |= unfiltered_witness
        #   Hrho''i: (cfgs[i], rho'') |= consequent.clp.lp.patterns[i]
        #   Hrho''c: (cfgs[i], rho'') |= consequent.clp.constraint
        #   Hrho''fw: (cfgs[i], rho'') |= filtered_witness
        # - just define rho''(V) = rho'(p) whenever `unfiltered_equalities[V] == p``,
        #           and rho''(V) = rho'(V) whenever `not V in unfiltered_equalities`,
        #   and note that free variables of consequent.clp.lp.patterns[i], consequent.clp.constraint, and filtered_witness
        #   are either those bound in the RHS (that is, the ones from consequent.vars),
        #   or those that are present in consequent.clp.lp.patterns[i],
        #   and therefore rho'' and rho' behaves the same on these patterns.
        # 
        # Then we also get
        #   Hrho''fw: (cfgs[i], rho'') |= witness
        # We also want to prove that
        #   rho'' is the same as rho except on consequent.vars
        # which, by the definition of rho'' and the hypothesis Hrho'rho, reduces to
        # ```
        #   on the variables from `unfiltered_equalities`, rho'' is the same as rho
        # ```
        # Let `V` be such variable; we want to show that
        # ```
        #   rho''(V) = rho(V)
        # ```
        # 
        # . Since `rho |= witness`, by Hwitfwitunfwit
        # we also have `rho |= unfiltered_witness`, which implies that
        # ```
        #   rho(V) = rho(unfiltered_equalities[v])
        # ```
        # Therefore, the goal is equivalent (using also the definition of rho'') to
        # ```
        #   rho'(unfiltered_equalities[V]) = rho(unfiltered_equalities[V])
        # ```
        # which holds assuming that rho and rho' are the same for FV(unfiltered_equalities[V]).
        # This requires an auxilliary invariant about `witness` which I am not going to formally state
        # and prove there, but the invariant boils down to the assumption
        ########################################################################################
        ########################################################################################
        #                   BIG RED ASSUMPTION HERE
        # The witness returned by the implies procedure has to property that all its equalities,
        # if oriented properly, map the quantified variables of the RHS to patterns
        # **whose set of free variables is subset of the set of free variables of the LHS.
        ########################################################################################
        ########################################################################################
        #
        # Now we have
        #   Hrho''rho: rho'' is the same as rho except on consequent.vars
        #
        # Now, in the goal we let (rho2 := rho'').
        # The first three subgoals are proven by Hrho''rho, Hrho'c, and Hrho'i, respectively.
        # It remains to prove
        # ```
        # forall j in range(0, i), (cfgs[j], rho'') |= consequent.clp.lp.patterns[j]
        # ```
        # which we can reduce using Inv2, Hrho''w to something like
        # ```
        # forall j in range(0, i), (cfgs[j], rho'') |= antecedent.clp.lp.patterns[j]
        # ```
        # That is almost the same as
        #   H3: forall j in range(0, i), (cfgs[j], rho) |= antecedent.clp.lp.patterns[j]
        # the only difference being that rho' and rho differs on consequent.vars
        # But by the assumption A1, antecedent does not contain variables from consequent.vars,
        # and therefore H3 implies the goal.
        # We are done [].
        witness = And(rs.top_sort, witness, new_witness)
        # Now we just change Inv2' into Inv2'', applying the standard Hoare-logic rule for variable assignment.
        # ```
        # forall (j : range(0, i+1)) (rho : Valuation) (cfg : Cfg),
        #   rho |= witness ->
        #   ((cfg, rho) |= antecedent.clp.lp.patterns[j]) ->
        #   ((cfg, rho) |= consequent.clp.lp.patterns[j]) .
        # ```
        continue # just to be explicit

    #lhs2 : Pattern = antecedent.clp.constraint
    #rhs2 : Pattern = reduce(lambda p, var: Exists(rs.top_sort, var, p), consequent.vars, And(rs.top_sort, consequent.clp.constraint, witnesses))
    #result2 : ImpliesResult = rs.kcs.client.implies(lhs2, rhs2)
    #if result2.satisfiable != True:
    #    return False
    
    return EclpImpliesResult(True, witness)

def clp_to_list(rs : ReachabilitySystem, clp : CLP) -> Pattern:
    sortList = SortApp('SortList', (rs.top_sort,))
    list_items : List[Pattern] = list(map(lambda p: App('LblListItem', (), (App('inj', (rs.top_sort, SortApp('SortKItem', ())), (p,)),)), clp.lp.patterns))
    resulting_list : Pattern = reduce(lambda p, q: App("Lbl'Unds'List'Unds'", (), (p, q)), list_items, App("Lbl'Stop'List", ()))
    constrained = And(SortApp('SortList', ()), resulting_list, Floor(rs.top_sort, SortApp('SortList', ()), clp.constraint))
    return constrained


def eclp_impl_valid_trough_lists(rs: ReachabilitySystem, antecedent : ECLP, consequent: ECLP) -> EclpImpliesResult:
    antecedent_list : Pattern = clp_to_list(rs, antecedent.clp)
    consequent_list : Pattern = clp_to_list(rs, consequent.clp)
    ex_consequent_list : Pattern = reduce(lambda p, var: Exists(SortApp('SortList', ()), var, p), consequent.vars, consequent_list)
    #print(f'from {antecedent_list}')
    #print(f'to {ex_consequent_list}')

    try:
        result : ImpliesResult = rs.kcs.client.implies(antecedent_list, ex_consequent_list)
    except:
        _LOGGER.error(f"Implication failed: {antecedent_list} -> {ex_consequent_list}")
        raise
    return EclpImpliesResult(result.satisfiable, result.substitution)

#def eclp_impl_component_valid(rs: ReachabilitySystem, antecedent: ECLP, consequent: ECLP, j: int) -> bool:
#    antec_j = antecedent.clp.lp.patterns[j]
#    conseq_j = consequent.clp.lp.patterns[j]
#    ex_conseq_j : Pattern = reduce(lambda p, var: Exists(rs.top_sort, var, p), consequent.vars, conseq_j)
#    _LOGGER.debug(f"conseq_j: {ex_conseq_j}")
#    valid = rs.kcs.client.implies(antec_j, ex_conseq_j).satisfiable
#    return valid


# But this will have a problem with predicate patterns
def rename_vars(renaming: Dict[str, str], phi: Pattern) -> Pattern:
    match phi:
        # The main case
        case EVar(name, sort):
            if name in renaming:
                return EVar(renaming[name], sort)
            return EVar(name, sort)

        # The recursive cases    
        case App(symbol_name, sorts, args):
            return App(symbol_name, sorts, tuple(map(lambda p: rename_vars(renaming, p), args)))
        case Not(sort, pattern):
            return Not(sort, rename_vars(renaming, pattern))
        case And(sort, left, right):
            return And(sort, rename_vars(renaming, left), rename_vars(renaming, right))
        case Or(sort, left, right):
            return Or(sort, rename_vars(renaming, left), rename_vars(renaming, right))
        case Implies(sort, left, right):
            return Implies(sort, rename_vars(renaming, left), rename_vars(renaming, right))
        case Iff(sort, left, right):
            return Iff(sort, rename_vars(renaming, left), rename_vars(renaming, right))
        case Exists(sort, var, pattern):
            new_dict = dict(renaming)
            new_dict.update({var.name : var.name})
            return Exists(sort, var, rename_vars(new_dict, pattern))
        case Forall(sort, var, pattern):
            new_dict = dict(renaming)
            new_dict.update({var.name : var.name})
            return Forall(sort, var, rename_vars(new_dict, pattern))
        # Base cases
        case Equals(op_sort, sort, left, right):
            return Equals(op_sort, sort, rename_vars(renaming, left), rename_vars(renaming, right))
        case In(op_sort, sort, left, right):
            return In(op_sort, sort, rename_vars(renaming, left), rename_vars(renaming, right))
        case DV(_,_):
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
    raise NotImplementedError()
        

@final
@dataclass
class VerifySettings:
    check_eclp_impl_valid : Callable[[ReachabilitySystem, ECLP, ECLP], EclpImpliesResult]
    goal_as_cutpoint : bool
    max_depth : int
    target : Optional[List[int]]

@dataclass
class VerifyGoal:
    goal_id : int
    antecedent : ECLP
    instantiated_cutpoints : Dict[str,ECLP]
    flushed_cutpoints : Dict[str,ECLP]
    user_cutpoint_blacklist : List[str]
    stuck : List[bool]
    total_steps : List[int]
    #max_depth : List[int]
    component_matches_something : List[bool]
    try_stepping : bool
    was_processed_by_advance_general : bool = False
    

    @staticmethod
    def from_dict(dct: Mapping[str, Any]) -> 'VerifyGoal':
        return VerifyGoal(
            goal_id=int(dct['goal_id']),
            antecedent=ECLP.from_dict(dct['antecedent']),
            instantiated_cutpoints={k : ECLP.from_dict(dct['instantiated_cutpoints'][k]) for k in dct['instantiated_cutpoints']},
            flushed_cutpoints={k : ECLP.from_dict(dct['flushed_cutpoints'][k]) for k in dct['flushed_cutpoints']},
            user_cutpoint_blacklist=dct['user_cutpoint_blacklist'],
            stuck=list(map(lambda s: bool(s), dct['stuck'])),
            total_steps=dct['total_steps'],
            #max_depth=dct['max_depth'],
            was_processed_by_advance_general=dct['was_processed_by_advance_general'],
            component_matches_something=dct['component_matches_something'],
            try_stepping=dct['try_stepping'],
        )
    
    @property
    def dict(self) -> Dict[str, Any]:
        return {
            'goal_id' : self.goal_id,
            'antecedent' : self.antecedent.dict,
            'instantiated_cutpoints' : {k : self.instantiated_cutpoints[k].dict for k in self.instantiated_cutpoints},
            'flushed_cutpoints' : {k : self.flushed_cutpoints[k].dict for k in self.flushed_cutpoints},
            'user_cutpoint_blacklist' : self.user_cutpoint_blacklist,
            'stuck' : self.stuck,
            'total_steps' : self.total_steps,
            #'max_depth' : self.max_depth,
            'was_processed_by_advance_general' : self.was_processed_by_advance_general,
            'component_matches_something' : self.component_matches_something,
            'try_stepping' : self.try_stepping,
        }

    def is_fully_stuck(self) -> bool:
        return all(self.stuck)
    
#    def copy(self):
#        return VerifyGoal(
#            goal_id=self.goal_id,
#            antecedent=self.antecedent.copy(), self.instantiated_cutpoints.copy(),)

#@dataclass
#class UnsolvableGoal:
#    reason : str
#    pass

@dataclass
class VerifyQuestion:
    # None means impossible / failed branch / a goal with no solution.
    # We store such value because one entry in the hypercube can be reached from multiple sides,
    # and we do not want to 
    goals : List[VerifyGoal]
    depth : List[int]
    #source_of_question : Optional[List[int]] # index, or nothing for initial


    @staticmethod
    def from_dict(dct: Mapping[str, Any]) -> 'VerifyQuestion':
        return VerifyQuestion(
            goals=list(map(VerifyGoal.from_dict, dct['goals'])),
            depth=dct['depth'],
        )
    
    @property
    def dict(self) -> Dict[str, Any]:
        return {
            'goals' : list(map(lambda g: g.dict, self.goals)),
            'depth' : self.depth,
        }

    #def is_worth_trying(self) -> bool:
    #    return all(map(lambda g: g is not UnsolvableGoal, self.goals))

@dataclass
class VerifyEntry:
    question : VerifyQuestion
    index : Optional[List[int]]
    processed : bool


    @staticmethod
    def from_dict(dct: Mapping[str, Any]) -> 'VerifyEntry':
        q0 = dct['question']
        q1 = VerifyQuestion.from_dict(q0)
        return VerifyEntry(
            question = q1,
            index = dct['index'],
            processed= dct['processed']
        )
    
    @property
    def dict(self) -> Dict[str, Any]:
        return {
            'question' : self.question.dict,
            'index' : self.index,
            'processed' : self.processed,
        }

@final
@dataclass
class VerifyResult:
    proved : bool
    final_states : List[VerifyQuestion]

@dataclass
class PerfCounter:
    total_count : int = 0
    total_time : float = 0.0

    @property
    def dict(self) -> Dict[str, Any]:
        return {
            'total_count' : self.total_count,
            'total_time' : self.total_time
        }

    def add(self, time_diff : float) -> None:
        self.total_count = self.total_count + 1
        self.total_time = self.total_time + time_diff

def index_zero() -> List[Any]:
    return []

def index_append_steps(idx : List[Any], steps: List[int]) -> List[Any]:
    return idx + [('steps', steps)]

def index_append_cutpoint(idx : List[Any], cutpoint_name) -> List[Any]:
    return idx + [('cutpoint', cutpoint_name)]    

def index_depth_in_direction(idx: List[Any], j: int) -> int:
    return sum([ele[1][j] for ele in idx if ele[0] == 'steps'])

def index_depth(idx: List[Any]) -> int:
    return sum([sum(ele[1]) for ele in idx if ele[0] == 'steps'])

def add_on_position(l: List[int], j: int, m: int) -> List[int]:
    l2 = l.copy()
    l2[j] += m
    return l2

@dataclass
class Projection:
    pattern : Pattern
    depth : int
    stuck : bool
    matches : bool
    instantiated_cutpoints : List[ECLP]
    flushed_cutpoints : List[ECLP]
    user_cutpoint_blacklist : List[ECLP]
    projected_from : VerifyGoal


@dataclass
class CutElement:
    phi : Pattern
    matches : bool
    depth : int
    stuck : bool
    progress_from_initial : bool

@dataclass
class ExeCut:
    ces : List[CutElement]

@dataclass
class PreGoal:
    patterns: List[Pattern]
    absolute_depths: List[int]
    progress_from_initial: List[bool]

# Combines execution tree cuts from different executions
def combine_exe_cuts(ecuts: List[ExeCut]) -> List[PreGoal]:
    ecutelements : List[List[CutElement]] = [ec.ces for ec in ecuts]
    combined : List[List[CutElement]] = [list(e) for e in product(*ecutelements)]
    pregoals : List[PreGoal] = [
        PreGoal(
            patterns = [ce.phi for ce in comb],
            absolute_depths = [ce.depth for ce in comb],
            progress_from_initial = [ce.progress_from_initial for ce in comb],
        )
        for comb in combined
    ]

    return pregoals


class Strategy(ABC):
    @abstractmethod
    def combine(self, streams: List[Iterable[ExeCut]]) -> Iterable[PreGoal]:
        ...

# This strategy assumes that all the streams are finite
class StupidStrategy(Strategy):
    def combine(self, streams: List[Iterable[ExeCut]]) -> Iterable[PreGoal]:
        # arity == len(streams)
        lists : List[List[ExeCut]] = [ list(s) for s in streams ]
        # arity == len(lists)
        combinations : List[List[ExeCut]] = [list(e) for e in product(*lists)]
        # for any c in combinations, arity == len(c)
        pgsl : List[List[PreGoal]] = [combine_exe_cuts(combination) for combination in combinations]
        pgs = chain(*pgsl)
        return pgs

def filter_out_pregoals_with_no_progress(pregoals: Iterable[PreGoal]) -> Iterable[PreGoal]:
    for pg in pregoals:
        if any(pg.progress_from_initial):
            yield pg
    return

class Verifier:
    settings: VerifySettings
    strategy : Strategy
    user_cutpoints : Dict[str, ECLP]
    rs: ReachabilitySystem
    arity : int
    consequent : ECLP
    last_goal_id : int
    
    trie : pygtrie.Trie
    # invariant: if a key matching `prefix + [('steps', l)]` is in `self.trie`,
    # then for any j in range(self.arity), the key `prefix + [('steps', add_on_position(l, j, -1))]`
    # is also (if valid; i.e., positive in all components) in `self.trie`

    failed_attempts : List[VerifyEntry] = []

    @dataclass
    class PerformanceStatistics:
        big_impl = PerfCounter()
        small_impl = PerfCounter()
        stepping = PerfCounter()

        @property
        def dict(self) -> Dict[str, Any]:
            return {
                'big_impl' : self.big_impl.dict,
                'small_impl' : self.small_impl.dict,
                'stepping' : self.stepping.dict,
            }

    ps = PerformanceStatistics()

    def __init__(self,
        settings: VerifySettings,
        strategy: Strategy,
        user_cutpoints : Dict[str, ECLP],
        rs: ReachabilitySystem,
        arity: int,
        antecedent : ECLP,
        consequent: ECLP
    ):
        self.settings = settings
        self.strategy = strategy
        self.rs = rs
        self.arity = arity
        self.consequent = consequent
        self.user_cutpoints = user_cutpoints
        self.last_goal_id = 1
        self.trie = pygtrie.Trie()
        
        self.trie[index_zero()] = VerifyEntry(
            question=VerifyQuestion(
                goals=[VerifyGoal(
                    goal_id = 0,
                    antecedent=antecedent,
                    instantiated_cutpoints=dict(),
                    flushed_cutpoints=dict(),
                    user_cutpoint_blacklist=[],
                    stuck=[False for _ in range(arity)],
                    #max_depth = [self.settings.max_depth for _ in range(arity)],
                    component_matches_something=[False for _ in range(arity)],
                    total_steps=index_zero(),
                    try_stepping=True,
                )],
                depth=index_zero(),
            ),
            index = index_zero(),
            processed=False,
        )


    #def dump(self) -> str:
    #    return json.dumps(list(map(lambda e: e.dict, self.entries)), sort_keys=True, indent=4)

    def fresh_goal_id(self) -> int:
        self.last_goal_id = self.last_goal_id + 1
        return self.last_goal_id

    def get_range(self):
        if self.settings.target is None:
            return vecrange(self.arity, self.settings.max_depth)
        else:
            return targeted_range(self.settings.target)


    def verify(self) -> VerifyResult:
        while len(self.trie) > 0:
            item = self.trie.shortest_prefix(index_zero())
            if self.advance_proof(item.key):
                return VerifyResult(proved=True, final_states=[])
            self.trie.pop(item.key)
            continue
        return VerifyResult(proved=False, final_states=[e.question for e in self.failed_attempts if e.question is not None])
    
    
    # Takes an index of a proof state in the hypercube
    # and tries to advance the proof state, possibly generating more entries in the hypercube
    def advance_proof(self, idx: Any) -> bool:
        _LOGGER.info(f"Advance_proof on {idx}. Total unprocessed: {len(self.trie)}")
        e : VerifyEntry = self.trie[idx]
        #e.index = idx

        _LOGGER.debug(f"Steps on goals: {list(map(lambda g: g.total_steps, e.question.goals))}")
        apgresult = self.advance_proof_general(idx=idx, q=e.question)
        if isinstance(apgresult, bool):
            if apgresult == True:
                _LOGGER.info("Succeeded (advance_proof_general returned True).")
                return True
    
            if not e.question.try_stepping:
                return False
            
            for goal in e.question.goals:
                cuts_in_j : Iterable[ExeCut]= [
                    self.advance_to_limit(
                        phi=goal.antecedent.clp.lp.patterns[j],
                        depth=goal.total_steps[j],
                        j=j,
                        instantiated_cutpoints=goal.instantiated_cutpoints,
                        flushed_cutpoints=goal.flushed_cutpoints,
                        user_cutpoint_blacklist=goal.user_cutpoint_blacklist,
                    )
                    for j in range(0, self.arity)
                ]
                # TODO what now?
                continue
            e.processed = True
            return False
            pass
        else:
            (cutpoint_name, new_entry) = apgresult
            new_index = index_append_cutpoint(idx, cutpoint_name)
            assert new_index not in self.trie
            self.trie[new_index] = new_entry
            return False

    def list_of_cut_elements_to_goal(self, goal: VerifyGoal, cut_elements: List[CutElement]) -> VerifyGoal:
        assert(len(cut_elements) == self.arity)
        goal_id = self.fresh_goal_id()
        antecedent = ECLP(
            vars = [],
            clp = CLP(
                constraint = goal.antecedent.clp.constraint,
                lp = LP (
                    patterns = list(map(lambda ce: ce.phi, cut_elements))
                )
            )
        )
        
        progress : bool = any([ce.progress_from_initial for ce in cut_elements])
        flushed_cutpoints : Dict[str,ECLP] = self.new_flushed_cutpoints(
            instantiated_cutpoints=goal.instantiated_cutpoints,
            flushed_cutpoints=goal.flushed_cutpoints,
            progress=progress,
        )
        instantiated_cutpoints : Dict[str,ECLP] = self.new_instantiated_cutpoints(
            instantiated_cutpoints=goal.instantiated_cutpoints,
            flushed_cutpoints=goal.flushed_cutpoints,
            progress=progress,
        )
        user_cutpoint_blacklist : List[str] = goal.user_cutpoint_blacklist
        stuck : List[bool] = [ce.stuck for ce in cut_elements]
        total_steps : List[int] = [ce.depth for ce in cut_elements]
        component_matches_something : List[bool] = [ce.matches for ce in cut_elements]

        return VerifyGoal(
            goal_id=goal_id,
            antecedent=antecedent,
            flushed_cutpoints=flushed_cutpoints,
            instantiated_cutpoints=instantiated_cutpoints,
            user_cutpoint_blacklist=user_cutpoint_blacklist,
            stuck=stuck,
            total_steps=total_steps,
            component_matches_something=component_matches_something,
        )

    def combine_cuts(self, goal: VerifyGoal, cuts: List[List[CutElement]]) -> None:
        combined : List[VerifyGoal] = []
        # Those are the obvious ones.
        combinations = list(product(*cuts))
        # TODO maybe we have to filter out those where there was no progress_from_initial?
        # But we also have to explore the ones for which some, but not all, components remain the same.
        # (The 'all components are the same' is the current situation, and we have already checked that
        #  using `advance_proof_general`.)
        non_obvious_combinations = []

        # `j` is the index that we keep constant, as in the 'goal'
        for j in range(self.arity):
            # But only if it is worth it
            if not goal.component_matches_something[j]:
                continue
            for combination in combinations:
                # `jprime` is the index that we update
                for jprime in range(self.arity):
                    if jprime == j:
                        continue
                

        pass


    def check_eclp_impl_valid(self, antecedent: ECLP, consequent: ECLP) -> EclpImpliesResult:
        old = time.perf_counter()
        r = self.settings.check_eclp_impl_valid(self.rs, antecedent, consequent)
        new = time.perf_counter()
        self.ps.big_impl.add(new - old)
        return r

    def advance_proof_general(self, idx: List[int], q: VerifyQuestion) -> List[VerifyGoal]:
        _LOGGER.info(f"Question {idx} in general. Goals: {len(q.goals)}")
        new_goals : List[VerifyGoal] = []
        for goal in q.goals:

            if goal.was_processed_by_advance_general:
                new_goals.append(goal)
                continue
            goal.was_processed_by_advance_general = True

            _LOGGER.info(f"Question {idx}, goal ID {goal.goal_id}, directions {len([True for b in goal.stuck if not b])}, flushed cutpoints {len(goal.flushed_cutpoints)}")
            
            implies_result = self.check_eclp_impl_valid(goal.antecedent, self.consequent)
            if implies_result.valid:
                # we can build a proof object using subst, Conseq, Reflexivity
                _LOGGER.info(f'Question {idx}, goal ID {goal.goal_id}: solved (antecedent implies consequent)')
                continue 

            #_LOGGER.info(f"Antecedent vars: {goal.antecedent.vars}") # most often should be empty
            # For each flushed cutpoint we compute a substitution which specialize it to the current 'state', if possible.
            flushed_cutpoints_with_subst : List[Tuple[ECLP, EclpImpliesResult]] = [
                (antecedentC, self.settings.check_eclp_impl_valid(self.rs, goal.antecedent, antecedentC))
                for antecedentC in goal.flushed_cutpoints.values()
            ]
            # Is there some flushed cutpoint / axiom which matches our current state? If so, we are done.
            usable_flushed_cutpoints : List[Tuple[ECLP, EclpImpliesResult]] = [
                (antecedentC, result)
                for (antecedentC, result) in flushed_cutpoints_with_subst
                if result.valid
            ]
            if (len(usable_flushed_cutpoints) > 0):
                # Conseq, Axiom
                _LOGGER.info(f'Question {idx}, goal ID {goal.goal_id}: solved (using flushed cutpoint)')
                continue

            # For each user cutpoint we compute a substitution which specialize it to the current 'state', if possible.
            user_cutpoints_with_subst : List[Tuple[str, EclpImpliesResult]] = [
                (antecedentCname, self.settings.check_eclp_impl_valid(self.rs, goal.antecedent, self.user_cutpoints[antecedentCname]))
                for antecedentCname in self.user_cutpoints
                if not antecedentCname in goal.user_cutpoint_blacklist
            ]
            # The list of cutpoints matching the current 'state'
            usable_cutpoints : List[Tuple[str, EclpImpliesResult]] = [
                (antecedentC, subst)
                for (antecedentC, subst) in user_cutpoints_with_subst
                if subst is not None
            ]

            if (len(usable_cutpoints) > 1):
                _LOGGER.warning(f"Question {idx}, goal ID {goal.goal_id}: multiple usable cutpoints; choosing one arbitrarily")
                _LOGGER.debug(f"(The usable cutpoints are: {[name for name,_ in usable_cutpoints]})")
            
            if (len(usable_cutpoints) > 0):
                new_goal_id = self.fresh_goal_id()
                _LOGGER.info(f'Question {idx}, goal ID {goal.goal_id}: using a cutpoint to create goal with ID {new_goal_id}')
                # apply Conseq (using [subst]) to change the goal to [antecedentC]
                # apply Circularity
                # We filter [user_cutpoints] to prevent infinite loops
                antecedentCname : str = usable_cutpoints[0][0]
                antecedentC = self.user_cutpoints[antecedentCname]
                antecedentCrenamed = rename_vars_eclp_to_fresh(list(free_evars_of_clp(antecedentC.clp).union(free_evars_of_clp(goal.antecedent.clp))), antecedentC)
                #_LOGGER.debug(f'New cutpoint: {antecedentCrenamed}')
                ucp = goal.user_cutpoint_blacklist + list(map(lambda cp: cp[0], usable_cutpoints))
                ic = goal.instantiated_cutpoints.copy()
                ic[antecedentCname] = antecedentCrenamed
                new_goals.append(VerifyGoal(
                    goal_id=new_goal_id,
                    antecedent=antecedentC.with_no_vars(),
                    instantiated_cutpoints=ic,
                    flushed_cutpoints=goal.flushed_cutpoints,
                    user_cutpoint_blacklist=ucp,
                    stuck=goal.stuck.copy(),
                    total_steps=goal.total_steps.copy(),
                    # FIXME Well, it matches the current usable cutpoint, right? And other usable cutpoints.
                    # So this is not really true. TODO think about it more
                    component_matches_something = [False for _ in range(self.arity)]
                ))
                continue
            new_goals.append(goal)
            continue
        return new_goals

    def implies_small(self, antecedent: Pattern, consequent: Pattern) -> bool:
        old = time.perf_counter()
        r = self.rs.kcs.client.implies(antecedent, consequent).satisfiable
        new = time.perf_counter()
        self.ps.small_impl.add(new - old)
        return r

    def approx_implies_something(self,
        pattern_j : Pattern,
        j: int,
        flushed_cutpoints : Dict[str,ECLP],
        user_cutpoint_blacklist : List[str]
    ) -> bool:
        usable_user_cutpoints : List[ECLP] = [self.user_cutpoints[name] for name in self.user_cutpoints if name not in user_cutpoint_blacklist]
        what = usable_user_cutpoints + list(flushed_cutpoints.values()) + [self.consequent]
        for eclp in what:
            phi = reduce(lambda p, var: Exists(self.rs.top_sort, var, p), eclp.vars, eclp.clp.lp.patterns[j])
            try:
                if self.implies_small(pattern_j, phi):
                    return True
            except:
                _LOGGER.error("Implies exception. LHS, RHS follows.")
                _LOGGER.error(self.rs.kprint.kore_to_pretty(pattern_j))
                _LOGGER.error(self.rs.kprint.kore_to_pretty(phi))
                raise
        return False


    sscache : Dict[int, int] = dict()

    def symbolic_step(self, pattern : Pattern) -> ExecuteResult:
        old = time.perf_counter()
        step_result = self.rs.kcs.client.execute(pattern=pattern, max_depth=1)
        new = time.perf_counter()
        self.ps.stepping.add(new - old)
        if pattern.__hash__() in self.sscache:
            self.sscache[pattern.__hash__()] = self.sscache[pattern.__hash__()] + 1
        else:
            self.sscache[pattern.__hash__()] = 1
        return step_result



    def new_flushed_cutpoints(
        self,
        instantiated_cutpoints : Dict[str, ECLP],
        flushed_cutpoints : Dict[str, ECLP],
        progress: bool
    ) -> Dict[str, ECLP]:
        if progress:
            tmp = instantiated_cutpoints.copy()
            tmp.update(flushed_cutpoints)
            return tmp
        else:
            return flushed_cutpoints

    def new_instantiated_cutpoints(
        self,
        instantiated_cutpoints : Dict[str, ECLP],
        flushed_cutpoints : Dict[str, ECLP],
        progress: bool
    ) -> Dict[str, ECLP]:
        if progress:
            return dict()
        else:
            return instantiated_cutpoints

    def advance_to_limit(
        self,
        phi: Pattern,
        depth: int,
        j: int,
        instantiated_cutpoints : Dict[str, ECLP],
        flushed_cutpoints : Dict[str, ECLP],
        user_cutpoint_blacklist : List[str],
    ) -> Iterable[ExeCut]:
        
        # This is the initial cut
        elements_to_explore_next : ExeCut = ExeCut(ces=[
            CutElement(phi=phi, matches=False,depth=depth,stuck=False,progress_from_initial=False)
        ])
        while len(elements_to_explore_next) > 0:
            elements_to_explore_now : List[CutElement] = elements_to_explore_next.ces
            elements_to_explore_next.ces = []
            curr_cut = ExeCut(ces=[])
            while len(elements_to_explore_now) > 0:
                ce : CutElement = elements_to_explore.pop()
                assert(not ce.matches)
                assert(not ce.stuck)
                _LOGGER.info(f"Exploring element in depth {ce.depth}")

                if ce.depth >= self.settings.max_depth:
                    _LOGGER.info(f"Maximal depth reached")
                    curr_cut.ces.append(ce)
                    # We are NOT adding ce into `elements_to_explore_next`
                    continue

                step_result : ExecuteResult = self.symbolic_step(ce.phi)
                if step_result.reason == StopReason.BRANCHING:
                    assert(step_result.next_states is not None)
                    assert(len(step_result.next_states) > 1)
                    _LOGGER.info(f"Branching in depth {ce.depth}")
                    bs = list(map(lambda s: s.kore, step_result.next_states))
                    for b in bs:
                        matches : bool = self.approx_implies_something(
                            pattern_j=b,
                            j=j,
                            flushed_cutpoints=self.new_flushed_cutpoints(
                                instantiated_cutpoints=instantiated_cutpoints,
                                flushed_cutpoints=flushed_cutpoints,
                                progress=ce.progress_from_initial, # TODO or True?
                            ),
                            user_cutpoint_blacklist=user_cutpoint_blacklist
                        )
                        new_ce1 : CutElement = CutElement(
                            phi=b,
                            depth=ce.depth+1,
                            stuck=False,
                            matches=matches,
                            progress_from_initial=ce.progress_from_initial # TODO: or True?
                        )

                        if matches:
                            curr_cut.ces.append(new_ce1)
                        elements_to_explore_next.ces.append(new_ce1)
                        continue
                    continue
                if step_result.reason == StopReason.DEPTH_BOUND:
                    _LOGGER.info(f"Progress in depth {ce.depth}")
                    p : Pattern = step_result.state.kore
                    matches1 : bool = self.approx_implies_something(
                        pattern_j=p,
                        j=j,
                        flushed_cutpoints=self.new_flushed_cutpoints(
                            instantiated_cutpoints=instantiated_cutpoints,
                            flushed_cutpoints=flushed_cutpoints,
                            progress=True
                        ),
                        user_cutpoint_blacklist=user_cutpoint_blacklist
                    )
                    new_ce : CutElement = CutElement(
                        phi=p,
                        depth=ce.depth+1,
                        stuck=False,
                    matches=matches1,
                        progress_from_initial=True
                    )
                    if matches:
                        curr_cut.ces.append(new_ce)
                    # We are NOT adding this element to `elements_to_explore_next` to be explored next
                    continue
                continue

                if step_result.reason == StopReason.STUCK:
                    _LOGGER.info(f"Stuck in depth {ce.depth}")
                    #ce.stuck = True
                    #final_elements.append(ce)
                    continue
                _LOGGER.error(f"Weird step_result: reason={step_result.reason}")
                raise RuntimeError()
            yield curr_cut
            continue
        return


def rename_vars_lp(renaming: Dict[str, str], lp: LP):
    return LP(list(map(lambda p: rename_vars(renaming, p), lp.patterns)))

def rename_vars_clp(renaming: Dict[str, str], clp: CLP):
    return CLP(lp=rename_vars_lp(renaming, clp.lp), constraint=rename_vars(renaming, clp.constraint))

def rename_vars_eclp(renaming: Dict[str, str], eclp: ECLP):
    new_vars0 : List[Pattern] = list(map(lambda ev: rename_vars(renaming, ev), eclp.vars))
    new_vars : List[EVar] = new_vars0 # type: ignore
    return ECLP(vars=new_vars, clp=rename_vars_clp(renaming, eclp.clp))

def get_fresh_evars_with_sorts(avoid: List[EVar], sorts: List[Sort], prefix="Fresh") -> List[EVar]:
    names_to_avoid = map(lambda ev: ev.name, avoid)
    names_with_prefix_to_avoid : List[str] = [name for name in names_to_avoid if name.startswith(prefix)]
    suffixes_to_avoid : List[str] = [name.removeprefix(prefix) for name in names_with_prefix_to_avoid]
    nums_to_avoid : List[int] = [ion for ion in map(int_or_None, suffixes_to_avoid) if ion is not None]
    if len(list(nums_to_avoid)) >= 1:
        n = max(nums_to_avoid) + 1
    else:
        n = 0
    nums = list(range(n, n + len(sorts)))
    fresh_evars : List[EVar] = list(map(lambda m: EVar(name=prefix + str(m), sort=sorts[m - n]), nums))
    return fresh_evars

def rename_vars_eclp_to_fresh(vars_to_avoid : List[EVar], eclp: ECLP) -> ECLP:
    eclp2 = eclp.copy()
    new_vars = get_fresh_evars_with_sorts(avoid=list(vars_to_avoid), sorts=list(map(lambda ev: ev.sort, eclp2.vars)))
    renaming = dict(zip(map(lambda e: e.name, eclp2.vars), map(lambda e: e.name, new_vars)))
    return rename_vars_eclp(renaming, eclp2)

# Phi - CLP (constrained list pattern)
# Psi - ECLP (existentially-quantified CLP)
# user_cutpoints - List of "lockstep invariants" / "circularities" provided by user;
#   each one is an ECLP. Note that they have not been proved to be valid;
#   it is our task to verify them if we need to use them.
def prepare_verifier(settings: VerifySettings, user_cutpoints : Dict[str,ECLP], rs: ReachabilitySystem, antecedent : ECLP, consequent) -> Verifier:
    user_cutpoints_2 = user_cutpoints.copy()
    if settings.goal_as_cutpoint:
        new_cutpoint = rename_vars_eclp_to_fresh(list(free_evars_of_clp(antecedent.clp)), antecedent)
        user_cutpoints_2['default']=new_cutpoint
        
    verifier = Verifier(
        settings=settings,
        strategy=StupidStrategy(),
        user_cutpoints=user_cutpoints_2,
        rs=rs,
        arity=len(antecedent.clp.lp.patterns),
        antecedent=antecedent.with_no_vars(),
        consequent=consequent,
    )
    return verifier

def verify(settings: VerifySettings, user_cutpoints : Dict[str,ECLP], rs: ReachabilitySystem, antecedent : ECLP, consequent) -> VerifyResult:
    verifier = prepare_verifier(settings, user_cutpoints, rs, antecedent, consequent)
    return verifier.verify()