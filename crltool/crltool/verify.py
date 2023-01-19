import logging

from dataclasses import dataclass

from functools import (
    reduce
)

from itertools import (
    chain
)

from typing import (
    Any,
    Callable,
    Dict,
    Final,
    List,
    Optional,
    Set,
    Tuple,
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

    result : ImpliesResult = rs.kcs.client.implies(antecedent_list, ex_consequent_list)
    return EclpImpliesResult(result.satisfiable, result.substitution)

@final
@dataclass
class VerifySettings:
    check_eclp_impl_valid : Callable[[ReachabilitySystem, ECLP, ECLP], EclpImpliesResult]
    user_cutpoints : List[ECLP]
    max_depth : int

@final
@dataclass
class VerifyResult:
    proved : bool
    final_states : List[ECLP] # nonempty implies .proved == False
    depth : int


# Phi - CLP (constrained list pattern)
# Psi - ECLP (existentially-quantified CLP)
# user_cutpoints - List of "lockstep invariants" / "circularities" provided by user;
#   each one is a CLP. Note that they have not been proved to be valid;
#   it is our task to verify them if we need to use them.
# instantiated_cutpoints
# flushed_cutpoints
def verify(settings: VerifySettings, rs: ReachabilitySystem, antecedent : ECLP, consequent, instantiated_cutpoints = [], flushed_cutpoints = [], user_cutpoint_blacklist : Set[ECLP] =set(), depth : int = 0) -> VerifyResult:
    arity : Final[int] = len(antecedent.clp.lp.patterns)
    if (arity != len(consequent.clp.lp.patterns)):
        raise ValueError("The antecedent and consequent have different arity.")

    implies_result = settings.check_eclp_impl_valid(rs, antecedent, consequent)
    if implies_result.valid:
        return VerifyResult(True, [], depth) # build a proof object using subst, Conseq, Reflexivity
    
    # For each flushed cutpoint we compute a substitution which specialize it to the current 'state', if possible.
    flushed_cutpoints_with_subst : List[Tuple[ECLP, EclpImpliesResult]] = [(antecedentC, settings.check_eclp_impl_valid(rs, antecedent, antecedentC)) for antecedentC in flushed_cutpoints]
    # Is there some flushed cutpoint / axiom which matches our current state? If so, we are done.
    usable_flushed_cutpoints : List[Tuple[ECLP, EclpImpliesResult]] = [(antecedentC, result) for (antecedentC, result) in flushed_cutpoints_with_subst if result.valid]
    if (len(list(usable_flushed_cutpoints)) > 0):
        return VerifyResult(True, [], depth) # Conseq, Axiom

    if (depth >= settings.max_depth):
        return VerifyResult(False, [antecedent], depth)

    # For each user cutpoint we compute a substitution which specialize it to the current 'state', if possible.
    user_cutpoints_with_subst : List[Tuple[ECLP, EclpImpliesResult]] = [(antecedentC, settings.check_eclp_impl_valid(rs, antecedent, antecedentC)) for antecedentC in settings.user_cutpoints if not antecedentC in user_cutpoint_blacklist]
    # The list of cutpoints matching the current 'state'
    usable_cutpoints : List[Tuple[ECLP, EclpImpliesResult]] = [(antecedentC, subst) for (antecedentC, subst) in user_cutpoints_with_subst if subst is not None]
    # If at least on succeeds, it is good.
    for (antecedentC, subst) in usable_cutpoints:
        # apply Conseq (using [subst]) to change the goal to [antecedentC]
        # apply Circularity
        # We filter [user_cutpoints] to prevent infinite loops
        result = verify(
            settings=settings,
            rs=rs,
            antecedent=antecedentC,
            consequent=consequent,
            instantiated_cutpoints=(instantiated_cutpoints + [antecedentC]),
            flushed_cutpoints=flushed_cutpoints,
            user_cutpoint_blacklist=user_cutpoint_blacklist.union((antecedentC,)),
            depth=depth+1,
        )
        if result.proved:
            return result
    
    for j in range(0, arity):
        # TODO We can execute a component [j] until it partially matches the corresponding component of some circularity/axiom
        step_result : ExecuteResult = rs.kcs.client.execute(pattern=antecedent.clp.lp.patterns[j], max_depth=1)
        # Cannot rewrite the j'th component anymore
        if step_result.reason == StopReason.STUCK:
            continue

        if step_result.next_states is None:
            continue

        nss : Tuple[State,...] = step_result.next_states
        verify_result : VerifyResult = VerifyResult(True, [], depth)

        for ns in nss:
            b = ns.kore
            newantecedent : ECLP = antecedent
            tmp = list(newantecedent.clp.lp.patterns)
            tmp[j] = b
            newantecedent.clp.lp.patterns = tuple(tmp)
            # TODO:
            # (1) prune inconsistent branches (since we have the toplevel constraint in antecedent/newantecedent)
            # (2) propagate the constraints as locally as possible
            #if not consistent(newantecedent):
            #    continue

            intermediate_result : VerifyResult = verify(
                settings=settings,
                rs=rs,
                antecedent=newantecedent,
                consequent=consequent,
                instantiated_cutpoints=[],
                flushed_cutpoints=instantiated_cutpoints+flushed_cutpoints,
                user_cutpoint_blacklist=user_cutpoint_blacklist,
                depth=depth+1,
            )
            verify_result.proved = verify_result.proved and intermediate_result.proved
            verify_result.final_states = verify_result.final_states + intermediate_result.final_states
        if verify_result.proved == False:
            return verify_result
    # TODO we should do something here
    return VerifyResult(False, [antecedent], depth)
