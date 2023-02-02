import logging
import json
import time
import pprint

from abc import (
    ABC,
    abstractmethod,
)

from collections.abc import Iterable

from dataclasses import dataclass

from enum import Enum

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

def clp_to_list(rs : ReachabilitySystem, clp : CLP) -> Pattern:
    sortList = SortApp('SortList', (rs.top_sort,))
    list_items : List[Pattern] = list(map(lambda p: App('LblListItem', (), (App('inj', (rs.top_sort, SortApp('SortKItem', ())), (p,)),)), clp.lp.patterns))
    resulting_list : Pattern = reduce(lambda p, q: App("Lbl'Unds'List'Unds'", (), (p, q)), list_items, App("Lbl'Stop'List", ()))
    constrained = And(SortApp('SortList', ()), resulting_list, Floor(rs.top_sort, SortApp('SortList', ()), clp.constraint))
    return constrained

def eclp_to_list(rs: ReachabilitySystem, eclp: ECLP) -> Pattern:
    l : Pattern = clp_to_list(rs, eclp.clp)
    ex_l : Pattern = reduce(lambda p, var: Exists(SortApp('SortList', ()), var, p), eclp.vars, l)
    return ex_l

def eclp_impl_valid_trough_lists(rs: ReachabilitySystem, antecedent : ECLP, consequent: ECLP) -> EclpImpliesResult:
    antecedent_list : Pattern = clp_to_list(rs, antecedent.clp)
    ex_consequent_list : Pattern = eclp_to_list(rs, consequent)
    #print(f'from {rs.kprint.kore_to_pretty(antecedent_list)}')
    #print(f'to {rs.kprint.kore_to_pretty(ex_consequent_list)}')

    try:
        result : ImpliesResult = rs.kcs.client.implies(antecedent_list, ex_consequent_list)
    except:
        _LOGGER.error(f"Implication failed: Antecedent -> Consequent")
        _LOGGER.error(f"Antecedent: {rs.kprint.kore_to_pretty(antecedent_list)}")
        _LOGGER.error(f"Consequent: {rs.kprint.kore_to_pretty(ex_consequent_list)}")
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
        

CandidateType = Enum('CandidateType', [
    'Consequent',
    'Axiom',
    'CandidateCircularity',
    'FlushedCircularity',
    'Stuck',
    'Branching'])
Candidate = Tuple[CandidateType, str]

@final
@dataclass
class VerifySettings:
    check_eclp_impl_valid : Callable[[ReachabilitySystem, ECLP, ECLP], EclpImpliesResult]
    goal_as_cutpoint : bool
    max_depth : int
    cut_on_branch : bool
    filter_candidate_matches : bool

@dataclass
class VerifyGoal:
    goal_id : int
    antecedent : ECLP
    instantiated_cutpoints : Dict[str,ECLP]
    flushed_cutpoints : Dict[str,ECLP]
    user_cutpoint_blacklist : List[str]
    #stuck : List[bool]
    total_steps : List[int]
    candidate_matches : List[List[Candidate]]
    #max_depth : List[int]
    #component_matches_something : List[bool]
    #try_stepping : bool
    was_processed_by_advance_general : bool = False
    
    # TODO we need to serialize and de-serialize 'candidate_matches' somehow
    @staticmethod
    def from_dict(dct: Mapping[str, Any]) -> 'VerifyGoal':
        return VerifyGoal(
            goal_id=int(dct['goal_id']),
            antecedent=ECLP.from_dict(dct['antecedent']),
            instantiated_cutpoints={k : ECLP.from_dict(dct['instantiated_cutpoints'][k]) for k in dct['instantiated_cutpoints']},
            flushed_cutpoints={k : ECLP.from_dict(dct['flushed_cutpoints'][k]) for k in dct['flushed_cutpoints']},
            user_cutpoint_blacklist=dct['user_cutpoint_blacklist'],
            #stuck=list(map(lambda s: bool(s), dct['stuck'])),
            total_steps=dct['total_steps'],
            #max_depth=dct['max_depth'],
            was_processed_by_advance_general=dct['was_processed_by_advance_general'],
            candidate_matches=dct['candidate_matches'],
            #component_matches_something=dct['component_matches_something'],
            #try_stepping=dct['try_stepping'],
        )
    
    @property
    def dict(self) -> Dict[str, Any]:
        return {
            'goal_id' : self.goal_id,
            'antecedent' : self.antecedent.dict,
            'instantiated_cutpoints' : {k : self.instantiated_cutpoints[k].dict for k in self.instantiated_cutpoints},
            'flushed_cutpoints' : {k : self.flushed_cutpoints[k].dict for k in self.flushed_cutpoints},
            'user_cutpoint_blacklist' : self.user_cutpoint_blacklist,
            #'stuck' : self.stuck,
            'total_steps' : self.total_steps,
            #'max_depth' : self.max_depth,
            'was_processed_by_advance_general' : self.was_processed_by_advance_general,
            'candidate_matches' : self.candidate_matches
            #'component_matches_something' : self.component_matches_something,
            #'try_stepping' : self.try_stepping,
        }

    #def is_fully_stuck(self) -> bool:
    #    return all(self.stuck)
    
#    def copy(self):
#        return VerifyGoal(
#            goal_id=self.goal_id,
#            antecedent=self.antecedent.copy(), self.instantiated_cutpoints.copy(),)

#@dataclass
#class UnsolvableGoal:
#    reason : str
#    pass

@dataclass
class GoalConjunction:
    goals : Iterable[VerifyGoal]
    can_make_steps : bool

@dataclass
class VerifyQuestion: 
    goals : Iterable[VerifyGoal]
    #depth : List[int]
    #source_of_question : Optional[List[int]] # index, or nothing for initial


    @staticmethod
    def from_dict(dct: Mapping[str, Any]) -> 'VerifyQuestion':
        return VerifyQuestion(
            goals=list(map(VerifyGoal.from_dict, dct['goals'])),
            #depth=dct['depth'],
        )
    
    @property
    def dict(self) -> Dict[str, Any]:
        return {
            'goals' : list(map(lambda g: g.dict, self.goals)),
            #'depth' : self.depth,
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
class CutElement:
    phi : Pattern
    matches : List[Candidate]
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
    candidate_matches: List[List[Candidate]]

# Represents a bunch of pre-goals which all have to be valid at the same time
# if they are to represent a proof
@dataclass
class PreGoalConjunction:
    pregoals: List[PreGoal]

def combine_candidate_matches(l: List[List[Candidate]]) -> List[Candidate]:
    result = list(set.intersection(*[set(x) for x in l]))
    _LOGGER.info(f"Combining {l} into {result}")
    return result

# Combines execution tree cuts from different executions
def combine_exe_cuts(rs: ReachabilitySystem, ecuts: List[ExeCut]) -> List[PreGoal]:
    ecutelements : List[List[CutElement]] = [ec.ces for ec in ecuts]
    combined : List[List[CutElement]] = [list(e) for e in product(*ecutelements)]
    pregoals : List[PreGoal] = [
        PreGoal(
            patterns = [ce.phi for ce in comb],
            absolute_depths = [ce.depth for ce in comb],
            progress_from_initial = [ce.progress_from_initial for ce in comb],
            candidate_matches = [ce.matches for ce in comb] # combine_candidate_matches(comb)
        )
        for comb in combined
    ]

    return pregoals


class ExplorationStrategy(ABC):
    # Exploration strategy for a particular question.
    # Here we have a stream of execution cuts for every dimension,
    # and the strategy is combining them into bunches pre-goals.
    # The order of the generated pregoals really depends on the strategy.
    # For example, we might have a DFS-like strategy going deeply into one dimension,
    # or a BFS-like strategy which tries to stay on the same depth in all dimensions;
    # or a lockstep strategy which goes like (0,0),(1,1),(2,2) and ignores the rest.
    # The strategy does not necessarily have to generate all combinations of the ExeCuts,
    # but then the risk is that the verifier will not find a proof even if there exists one.
    # However, every yielded PreGoalConjunction has to be exhaustive.
    # Such can be generated from an ExeCut for each direction by `combine_exe_cuts`.
    @abstractmethod
    def combine(self, rs: ReachabilitySystem, streams: List[Iterable[ExeCut]]) -> Iterable[PreGoalConjunction]:
        ...

# This exploration_strategy assumes that all the streams are finite
class StupidExplorationStrategy(ExplorationStrategy):
    def combine(self, rs: ReachabilitySystem, streams: List[Iterable[ExeCut]]) -> Iterable[PreGoalConjunction]:
        # arity == len(streams)
        lists : List[List[ExeCut]] = [ list(s) for s in streams ]
        # arity == len(lists)
        combinations : List[List[ExeCut]] = [list(e) for e in product(*lists)]
        # for any c in combinations, arity == len(c)
        pgcs : List[PreGoalConjunction] = [
            PreGoalConjunction(pregoals=combine_exe_cuts(rs, combination))
            for combination in combinations
        ]
        return pgcs

def filter_out_pregoals_with_no_progress(pregoals: Iterable[PreGoalConjunction]) -> Iterable[PreGoalConjunction]:
    for pgc in pregoals:
        if len(pgc.pregoals) == 0:
            _LOGGER.warning(f"Filtering an empty conjunction: {pgc}")
            continue
        if len(pgc.pregoals) == 1:
            if not any(pgc.pregoals[0].progress_from_initial):
                continue
        yield pgc
    return

# We have a bunch of conjunctions of goals, and we want to prove at least one conjunction of those.
# This class manages the conjunctions
class GoalConjunctionChooserStrategy(ABC):
    # Returns one conjunction and removes it from the internal store.
    # None means that there are no remaining conjunctions
    @abstractmethod
    def pick_some(self) -> Optional[GoalConjunction]:
        ...
    
    @abstractmethod
    def insert_conjunctions(self, conjs: Iterable[GoalConjunction]) -> None:
        ...
    

# A minimal, stack-based conjunction chooser strategy.    
class StackGoalConjunctionChooserStrategy(GoalConjunctionChooserStrategy):
    _stack : List[GoalConjunction] = []

    def pick_some(self) -> Optional[GoalConjunction]:
        if (len(self._stack) >= 1):
            return self._stack.pop()
        return None
    
    def insert_conjunctions(self, gcs: Iterable[GoalConjunction]) -> None:
        # Evaluate it so that we can debug print it
        l = [GoalConjunction(goals=list(gc.goals), can_make_steps=gc.can_make_steps)  for gc in gcs]
        # We can do len(list(...)) only because it actually is a list, see the line above
        _LOGGER.info(f"Inserting goal conjunctions: {[(len(list(x.goals)), x.can_make_steps) for x in l]}")
        pprint.pprint([[g.candidate_matches for g in x.goals] for x in l])
        self._stack.extend(l)
        return

@dataclass
class APGResult:
    new_goal: Optional[VerifyGoal]
    proved: bool
    # invariant: proved == True ---> new_goal = None

class Verifier:
    settings: VerifySettings
    exploration_strategy : ExplorationStrategy
    user_cutpoints : Dict[str, ECLP]
    trusted_axioms : Dict[str, ECLP]
    rs: ReachabilitySystem
    arity : int
    consequent : ECLP
    last_goal_id : int
    
    goal_conj_chooser_strategy : GoalConjunctionChooserStrategy

    failed_attempts : List[GoalConjunction] = []

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
        exploration_strategy: ExplorationStrategy,
        goal_conj_chooser_strategy : GoalConjunctionChooserStrategy,
        user_cutpoints : Dict[str, ECLP],
        trusted_axioms : Dict[str, ECLP],
        rs: ReachabilitySystem,
        arity: int,
        antecedent : ECLP,
        consequent: ECLP
    ):
        self.settings = settings
        self.exploration_strategy = exploration_strategy
        self.goal_conj_chooser_strategy = goal_conj_chooser_strategy
        self.rs = rs
        self.arity = arity
        self.consequent = consequent
        self.user_cutpoints = user_cutpoints
        self.trusted_axioms = trusted_axioms
        self.last_goal_id = 1
        
        goal = VerifyGoal(
            goal_id = 0,
            antecedent=antecedent,
            instantiated_cutpoints=dict(),
            flushed_cutpoints=dict(),
            user_cutpoint_blacklist=[],
            candidate_matches=[[(CandidateType.CandidateCircularity, "default")]],
            #stuck=[False for _ in range(arity)],
            #max_depth = [self.settings.max_depth for _ in range(arity)],
            #component_matches_something=[False for _ in range(arity)],
            total_steps=[0 for _ in range(arity)],
            #try_stepping=True,
        )
        self.goal_conj_chooser_strategy.insert_conjunctions([GoalConjunction(goals = [goal], can_make_steps = True)])
        return

    #def dump(self) -> str:
    #    return json.dumps(list(map(lambda e: e.dict, self.entries)), sort_keys=True, indent=4)

    def fresh_goal_id(self) -> int:
        self.last_goal_id = self.last_goal_id + 1
        return self.last_goal_id


    def verify(self) -> VerifyResult:
        while(True):
            conj = self.goal_conj_chooser_strategy.pick_some()
            if conj is None:
                return VerifyResult(proved=False, final_states=[]) # TODO
            if self.advance_proof(conj):
                return VerifyResult(proved=True, final_states=[])
            continue
        raise RuntimeError("Unreachable")


    def advance_proof(self, conj: GoalConjunction) -> bool:
        _LOGGER.info(f"Advance_proof on conjunction.")

        # We need to make progress on all the goals from the conjunction.
        # If one goal cannot make progress, we discard the whole conjunction as unprovable.
        # However, if all of them make progress - that is, are proved or can be generalized,
        # we have to combine all the generalizations into a ....
        apgresults = [
            (goal, self.advance_proof_general(goal))
            for goal in conj.goals
        ]
        if all([apgr.proved for _,apgr in apgresults]):
            _LOGGER.info(f"All goals ({len(apgresults)}) of the conjunction were proved")
            pprint.pprint({ g.goal_id : g.candidate_matches for g in conj.goals})
            return True
        
        if not conj.can_make_steps:
            _LOGGER.info("Some goals of the conjunction were NOT proved, and we are NOT allowed to make steps")
            return False
        
        not_proved_and_not_generalized = [
            apgr.new_goal
            for _,apgr in apgresults
            if (not apgr.proved) and (apgr.new_goal is None)
        ]
        if len(not_proved_and_not_generalized) > 0:
            _LOGGER.info("Some goals of the conjunction were NOT proved and NOT generalized")
            return False
        
        _LOGGER.info("All the goals of the conjunction that were NOT proved WERE generalized")

        # Ok, so now we make steps, because we can.
        goals_after_generalization : List[VerifyGoal] = [
            apgr.new_goal
            for _, apgr in apgresults
            if (not apgr.proved) and (apgr.new_goal is not None)
        ]
        _LOGGER.info(f"Going to make steps on {len(goals_after_generalization)} goals")
        new_goals_pre_conj : List[Iterable[GoalConjunction]] = []
        # All of these have to hold
        for goal in goals_after_generalization:
            _LOGGER.info(f"Making steps on goal {goal.goal_id}")
            cuts_in_j : List[Iterable[ExeCut]] = [
                self.advance_to_limit(
                    phi=goal.antecedent.clp.lp.patterns[j],
                    depth=goal.total_steps[j],
                    j=j,
                    instantiated_cutpoints=goal.instantiated_cutpoints,
                    flushed_cutpoints=goal.flushed_cutpoints,
                    user_cutpoint_blacklist=goal.user_cutpoint_blacklist,
                    progress_from_initial=False,
                )
                for j in range(0, self.arity)
            ]
            # Each of the elements of 'combined' is a way of making 'goal' hold.
            combined : Iterable[PreGoalConjunction] = self.exploration_strategy.combine(self.rs, cuts_in_j.copy())
            combined_filtered : Iterable[PreGoalConjunction] = filter_out_pregoals_with_no_progress(combined)
            # Each of the elements of 'new_gcjs' is a way of making 'goal' hold.
            new_gcjs : Iterable[GoalConjunction] = list(map( # TODO remove the list
                lambda pgc: (
                    GoalConjunction(
                        goals=list(map( #TODO is the list() needed?
                            lambda pg: self.pregoal_to_goal(goal, pg),
                            pgc.pregoals.copy()
                        )),
                        can_make_steps=True,
                    )
                ),
                #combined_filtered
                list(combined_filtered)
            ))
            # Ok, so at least one of the new goals have to hold for the old goal to be verified.
            # But: the task was to prove all the goals from the conjunction
            new_goals_pre_conj.append(new_gcjs)
            #continue

        # We now have to convert what is effectively a conjunction of disjunctions
        # into a disjunction of conjunctions.
        disj_of_conj : Iterable[Tuple[GoalConjunction,...]] = product(*new_goals_pre_conj)
        disj_of_conj_2 : Iterable[List[GoalConjunction]] = map(lambda t: list(t), disj_of_conj)
        disj_of_conj_3 : Iterable[List[Iterable[VerifyGoal]]] = map(lambda l: list(map(lambda g: g.goals, l)), disj_of_conj_2)
        def filter_out_empty(l : List[Iterable[VerifyGoal]]) -> bool:
            if len(l) == 0:
                print("Filtering out an empty List[Iterable[VerifyGoal]]")
                return False
            return True
        disj_of_conj_4 : Iterable[List[Iterable[VerifyGoal]]] = filter(filter_out_empty, disj_of_conj_3)
        #disj_of_conj_4 : Iterable[List[Iterable[VerifyGoal]]] = filter(lambda l: len(l) > 0, disj_of_conj_3)
        # Now we just flatten the list of conjunctions.
        disj_of_conj_flattened : Iterable[GoalConjunction] = (map(
            lambda lgc: GoalConjunction(
                goals = chain(*lgc),
                can_make_steps = True,
            ),
            disj_of_conj_4
        ))
        if self.settings.filter_candidate_matches:
            disj_of_conj_flattened = self.filter_out_goals_with_empty_candidate_matches(disj_of_conj_flattened)
        self.goal_conj_chooser_strategy.insert_conjunctions(disj_of_conj_flattened)
        return False

    def pregoal_to_goal(self, goal: VerifyGoal, pregoal: PreGoal) -> VerifyGoal:
        assert(len(pregoal.patterns) == self.arity)
        goal_id = self.fresh_goal_id()
        antecedent = ECLP(
            vars = [],
            clp = CLP(
                constraint = goal.antecedent.clp.constraint,
                lp = LP (
                    patterns = pregoal.patterns.copy()
                )
            )
        )
        
        progress : bool = any(pregoal.progress_from_initial)
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
        #stuck : List[bool] = [ce.stuck for ce in cut_elements]
        #component_matches_something : List[bool] = [ce.matches for ce in cut_elements]

        return VerifyGoal(
            goal_id=goal_id,
            antecedent=antecedent,
            flushed_cutpoints=flushed_cutpoints,
            instantiated_cutpoints=instantiated_cutpoints,
            user_cutpoint_blacklist=user_cutpoint_blacklist,
            #stuck=stuck,
            total_steps=pregoal.absolute_depths,
            candidate_matches=pregoal.candidate_matches.copy(),
            #component_matches_something=component_matches_something,
        )

    def is_contradiction(self, eclp: ECLP) -> bool:
        return self.check_eclp_impl_valid(
            eclp,
            ECLP(
                vars=[],
                clp=CLP(
                    lp=LP(
                        patterns=[Bottom(self.rs.top_sort) for _ in range(len(eclp.clp.lp.patterns))]
                    ),
                    constraint=Bottom(self.rs.top_sort),
                )
            )
        ).valid
    
    def transform_goals(self, goals: List[VerifyGoal]) -> Optional[List[VerifyGoal]]:
        new_goals : List[VerifyGoal] = []
        for goal in goals:
            if len(combine_candidate_matches(goal.candidate_matches)) >= 1:
                new_goals.append(goal)
                continue
            if self.is_contradiction(goal.antecedent):
                continue
            return None
        return new_goals

    def filter_out_goals_with_empty_candidate_matches(self, gcs: Iterable[GoalConjunction]) -> Iterable[GoalConjunction]:
        for gc in gcs:
            new_goals = self.transform_goals(list(gc.goals))
            if new_goals is not None:
                yield GoalConjunction(goals=new_goals, can_make_steps=gc.can_make_steps)    
        return



    def check_eclp_impl_valid(self, antecedent: ECLP, consequent: ECLP) -> EclpImpliesResult:
        _LOGGER.debug("Checking a large implication")
        old = time.perf_counter()
        r = self.settings.check_eclp_impl_valid(self.rs, antecedent, consequent)
        new = time.perf_counter()
        self.ps.big_impl.add(new - old)
        return r

    def check_eclp_impl_valid_alpha(self, antecedent: ECLP, consequent: ECLP) -> EclpImpliesResult:
        vars_to_rename = list(free_evars_of_clp(antecedent.clp))
        vars_to_avoid = vars_to_rename + list(free_evars_of_clp(consequent.clp))
        new_vars = get_fresh_evars_with_sorts(avoid=list(vars_to_avoid), sorts=list(map(lambda ev: ev.sort, vars_to_rename)))
        vars_fr : List[str] = list(map(lambda e: e.name, vars_to_rename))
        vars_to : List[str] = list(map(lambda e: e.name, new_vars))
        renaming = dict(zip(vars_fr, vars_to))
        #print(f"Reanimg: {renaming}")
        consequent_renamed = ECLP(
            vars=[EVar(name=renaming[v.name] if v.name in renaming else v.name, sort=v.sort) for v in consequent.vars],
            clp=rename_vars_clp(renaming, consequent.clp)
        )
        return self.check_eclp_impl_valid(antecedent, consequent_renamed)
 
    def eclp_to_pretty(self, eclp: ECLP) -> str:
        return self.rs.kprint.kore_to_pretty(eclp_to_list(self.rs, eclp))

    def advance_proof_general(self, goal: VerifyGoal) -> APGResult:
        _LOGGER.info(f"APG goal {goal.goal_id}")
        _LOGGER.info(f"Flushed cutpoints {len(goal.flushed_cutpoints)}")
        #print(self.eclp_to_pretty(goal.antecedent))

        # FIXME According to the proof system, we can do this only if we do not have any unflushed circularity
        implies_result = self.check_eclp_impl_valid(goal.antecedent, self.consequent)
        if implies_result.valid:
            # we can build a proof object using subst, Conseq, Reflexivity
            _LOGGER.info(f'Solved (antecedent implies consequent)')
            return APGResult(new_goal=None, proved=True)

        # For each flushed cutpoint we compute a substitution which specialize it to the current 'state', if possible.
        flushed_cutpoints_with_subst : List[Tuple[ECLP, EclpImpliesResult]] = [
            (antecedentC, self.check_eclp_impl_valid(goal.antecedent, antecedentC))
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
            _LOGGER.info(f'Solved (using flushed cutpoint)')
            return APGResult(new_goal=None, proved=True)


        # For each axiom cutpoint we compute a substitution which specialize it to the current 'state', if possible.
        axioms_with_subst : List[Tuple[ECLP, EclpImpliesResult]] = [
            (axiom, self.check_eclp_impl_valid_alpha(goal.antecedent, axiom))
            for axiom in self.trusted_axioms.values()
        ]
        # Is there some flushed cutpoint / axiom which matches our current state? If so, we are done.
        usable_axioms : List[Tuple[ECLP, EclpImpliesResult]] = [
            (antecedentC, result)
            for (antecedentC, result) in axioms_with_subst
            if result.valid
        ]
        if (len(usable_axioms) > 0):
            # Conseq, Axiom/Admit
            _LOGGER.info(f'Solved (using trusted axiom)')
            return APGResult(new_goal=None, proved=True)

        # For each user cutpoint we compute a substitution which specialize it to the current 'state', if possible.
        user_cutpoints_with_subst : List[Tuple[str, EclpImpliesResult]] = [
            (antecedentCname, self.check_eclp_impl_valid(goal.antecedent, self.user_cutpoints[antecedentCname]))
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
            _LOGGER.warning(f"Multiple usable cutpoints; choosing one arbitrarily")
            _LOGGER.debug(f"(The usable cutpoints are: {[name for name,_ in usable_cutpoints]})")
            
        if (len(usable_cutpoints) > 0):
            new_goal_id = self.fresh_goal_id()
            _LOGGER.info(f'Using a cutpoint to create goal with ID {new_goal_id}')
            # apply Conseq (using [subst]) to change the goal to [antecedentC]
            # apply Circularity
            # We filter [user_cutpoints] to prevent infinite loops
            antecedentCname : str = usable_cutpoints[0][0]
            antecedentC = self.user_cutpoints[antecedentCname]
            consequent_vars = free_evars_of_clp(self.consequent.clp)
            # We want to generalize on all variables of the candidate circularity.
            # TODO: What if some variables `v:s` of the candidate circularity is present in the consequent?
            #vars_to_generalize = [ev for ev in free_evars_of_clp(antecedentC.clp) if ev not in consequent_vars]
            vars_to_generalize = [ev for ev in free_evars_of_clp(antecedentC.clp)]
            antecedentCrenamed = rename_and_generalize_vars_eclp_to_fresh(
                vars_to_avoid=list(
                    free_evars_of_clp(antecedentC.clp).union(free_evars_of_clp(goal.antecedent.clp)).union(consequent_vars)
                ),
                vars_to_rename=vars_to_generalize,
                eclp=antecedentC,
            )
            ucp = goal.user_cutpoint_blacklist + list(map(lambda cp: cp[0], usable_cutpoints))
            ic = goal.instantiated_cutpoints.copy()
            ic[antecedentCname] = antecedentCrenamed
            #_LOGGER.debug(f'New goal: {self.eclp_to_pretty(antecedentC.with_no_vars())}')
            #_LOGGER.debug(f'Added circularity: {self.eclp_to_pretty(antecedentCrenamed)}')
            ng = VerifyGoal(
                goal_id=new_goal_id,
                antecedent=antecedentC.with_no_vars(),
                instantiated_cutpoints=ic,
                flushed_cutpoints=goal.flushed_cutpoints,
                user_cutpoint_blacklist=ucp,
                candidate_matches=[[(CandidateType.CandidateCircularity, antecedentCname)]],
                #stuck=goal.stuck.copy(),
                total_steps=goal.total_steps.copy(),
                # FIXME Well, it matches the current usable cutpoint, right? And other usable cutpoints.
                # So this is not really true. TODO think about it more
                #component_matches_something = [False for _ in range(self.arity)]
            )
            return APGResult(new_goal=ng, proved=False)
        _LOGGER.info(f'Not proved, no generalization applicable.')
        return APGResult(new_goal=None, proved=False)

    def implies_small(self, antecedent: Pattern, consequent: Pattern) -> bool:
        old = time.perf_counter()
        r = self.rs.kcs.client.implies(antecedent, consequent).satisfiable
        new = time.perf_counter()
        self.ps.small_impl.add(new - old)
        return r
    
    def implies_small_alpha(self, antecedent: Pattern, consequent: Pattern, eqvars) -> bool:
        vars_to_rename = list(free_evars_of_pattern(antecedent))
        vars_to_avoid = vars_to_rename + list(free_evars_of_pattern(consequent))
        new_vars = get_fresh_evars_with_sorts(avoid=list(vars_to_avoid), sorts=list(map(lambda ev: ev.sort, vars_to_rename)))
        vars_fr : List[str] = list(map(lambda e: e.name, vars_to_rename))
        vars_to : List[str] = list(map(lambda e: e.name, new_vars))
        renaming = dict(zip(vars_fr, vars_to))
        consequent_renamed = rename_vars(renaming, consequent)
        vars_renamed = [EVar(name=renaming[v.name] if v.name in renaming else v.name, sort=v.sort)
            for v in eqvars
        ]
        consequent_ex = reduce(lambda p, var: Exists(self.rs.top_sort, var, p), vars_renamed, consequent_renamed)
        return self.implies_small(antecedent, consequent_ex)

    def approx_implies_something(self,
        pattern_j : Pattern,
        j: int,
        flushed_cutpoints : Dict[str,ECLP],
        user_cutpoint_blacklist : List[str]
    ) -> List[Candidate]:
        Candidate
        usable_user_cutpoints : List[Tuple[ECLP, Candidate]] = [
            (self.user_cutpoints[name], (CandidateType.CandidateCircularity, name))
            for name in self.user_cutpoints
            if name not in user_cutpoint_blacklist
        ]
        fcv : List[Tuple[ECLP, Candidate]] = [
            (eclp, (CandidateType.FlushedCircularity, name))
            for name,eclp in flushed_cutpoints.items()
        ]
        
        usable : List[Candidate] = []
        what : List[Tuple[ECLP, Candidate]] = usable_user_cutpoints + fcv + [(self.consequent, (CandidateType.Consequent, ""))]
        #_LOGGER.debug(f"Implication checking: usable user cutpoints: {len(usable_user_cutpoints)}, flushed cutpoints: {len(fcv)}")
        for eclp, candidate in what:
            phi = reduce(lambda p, var: Exists(self.rs.top_sort, var, p), eclp.vars, eclp.clp.lp.patterns[j])
            
            if self.implies_small(pattern_j, phi):
                _LOGGER.debug(f"Implies {self.rs.kprint.kore_to_pretty(phi)}")
                usable.append(candidate)
            
        for name, eclp in self.trusted_axioms.items():
            if self.implies_small_alpha(pattern_j, eclp.clp.lp.patterns[j], eclp.vars):
                _LOGGER.debug(f"Trusted axiom '{name}' matches on component {j}")
                usable.append((CandidateType.Axiom, name))

        return usable


    sscache : Dict[int, int] = dict()

    def symbolic_step(self, pattern : Pattern) -> ExecuteResult:
        old = time.perf_counter()
        step_result = self.rs.kcs.client.execute(
            pattern=pattern,
            max_depth=1,
            terminal_rules=["IMP.halt"], # TODO abstract this away
        )
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

    def conjunct_exe_cuts(self, ecuts: List[ExeCut]) -> ExeCut:
        ces: List[CutElement] = []
        for ecut in ecuts:
            ces = ces + ecut.ces
        _LOGGER.debug(f"Combining a list of cuts of length {len(ecuts)} into a cut of length {len(ces)}")
        return ExeCut(ces=ces)

    def combine_exe_cuts_0(self, ecuts: List[Iterable[ExeCut]]) -> Iterable[ExeCut]:
        _LOGGER.debug(f"Combining a List[Iterable[ExeCut]] from various branches, of length {len(ecuts)}")
        prod : Iterable[Tuple[ExeCut,...]] = product(*ecuts)
        return map(lambda p: self.conjunct_exe_cuts(list(p)), prod)
        #return list(map(lambda p: self.conjunct_exe_cuts(list(p)), prod))

    def advance_to_limit(
        self,
        phi: Pattern,
        depth: int,
        j: int,
        instantiated_cutpoints : Dict[str, ECLP],
        flushed_cutpoints : Dict[str, ECLP],
        user_cutpoint_blacklist : List[str],
        progress_from_initial : bool,
        branching : bool = False,
    ) -> Iterable[ExeCut]:
        _LOGGER.info(f"advance_to_limit a pattern in depth {depth}, in direction {j}")

        matches00 : List[Candidate] = self.approx_implies_something(
            pattern_j=phi,
            j=j,
            flushed_cutpoints=self.new_flushed_cutpoints(
                instantiated_cutpoints=instantiated_cutpoints,
                flushed_cutpoints=flushed_cutpoints,
                progress=progress_from_initial,
            ),
            user_cutpoint_blacklist=user_cutpoint_blacklist
        )
        if branching and self.settings.cut_on_branch:
            matches00.append((CandidateType.Branching, ""))

        if len(matches00) >= 1 or (depth >= self.settings.max_depth):
            if len(matches00) < 1 and (depth >= self.settings.max_depth):
                _LOGGER.warning("Emiting a cut which does not match.")
             # This is the initial cut
            yield ExeCut(ces=[
                CutElement(phi=phi, matches=matches00.copy(),depth=depth,stuck=False,progress_from_initial=progress_from_initial)
            ])
        
        while depth < self.settings.max_depth:
            step_result : ExecuteResult = self.symbolic_step(phi)
            if step_result.reason == StopReason.BRANCHING:
                assert(step_result.next_states is not None)
                assert(len(step_result.next_states) > 1)
                bs = list(map(lambda s: s.kore, step_result.next_states))
                _LOGGER.info(f"Branching in depth {depth} with {len(bs)} successors")
                its : List[Iterable[ExeCut]] = []
                for b in bs:
                    its.append(self.advance_to_limit(
                        phi=b,
                        depth=depth+1,
                        j=j,
                        instantiated_cutpoints=instantiated_cutpoints,
                        flushed_cutpoints=flushed_cutpoints,
                        progress_from_initial=progress_from_initial,
                        user_cutpoint_blacklist=user_cutpoint_blacklist,
                        branching=True,
                    ))
                yield from self.combine_exe_cuts_0(its)
                #combined0 = self.combine_exe_cuts_0(its)
                #for c in combined0:
                #    yield c
                return

            if step_result.reason == StopReason.DEPTH_BOUND:
                _LOGGER.info(f"Progress in depth {depth}")
                p : Pattern = step_result.state.kore
                matches1 : List[Candidate] = self.approx_implies_something(
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
                    depth=depth+1,
                    stuck=False,
                    matches=matches1.copy(),
                    progress_from_initial=True
                )
                if len(matches1) >= 1:
                    _LOGGER.info(f"The configuration matches something; yielding.")
                    yield ExeCut(ces=[new_ce])
                phi = p
                depth = depth + 1
                matches00 = matches1
                progress_from_initial = True
                continue
                
            if (step_result.reason == StopReason.STUCK) or (step_result.reason == StopReason.TERMINAL_RULE):
                _LOGGER.info(f"Stuck (or terminal rule) in depth {depth}")
                #return # An optimization
                break
            _LOGGER.error(f"Weird step_result: reason={step_result.reason}")
            raise RuntimeError()

        #if len(matches00) < 1:
        #    _LOGGER.warning("Emiting a cut which does not match (point 2)")

        new_ce0 : CutElement = CutElement(
            phi=phi,
            depth=depth,
            stuck=True,
            matches=matches00.copy(), #[(CandidateType.Stuck, "")],
            progress_from_initial=progress_from_initial
        )
        if len(matches00) >= 1:
            yield ExeCut(ces=[new_ce])
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

def rename_and_generalize_vars_eclp_to_fresh(vars_to_avoid : List[EVar], vars_to_rename : List[EVar], eclp: ECLP) -> ECLP:
    new_vars = get_fresh_evars_with_sorts(avoid=list(vars_to_avoid), sorts=list(map(lambda ev: ev.sort, vars_to_rename)))
    fr : List[str] = list(map(lambda e: e.name, vars_to_rename))
    to : List[str] = list(map(lambda e: e.name, new_vars))
    renaming = dict(zip(fr, to))
    clp = rename_vars_clp(renaming, eclp.clp)
    return ECLP(vars=new_vars, clp=clp)

def axiom_from_trusted_claim(rs: ReachabilitySystem, claim: Claim, trusted_claim: Claim, vars_to_avoid: List[EVar]) -> Optional[ECLP]:
    # First I want to rename all the variables of the axiom.
    vars_to_rename = list(free_evars_of_clp(trusted_claim.antecedent.clp).union(free_evars_of_clp(trusted_claim.consequent.clp)))
    new_vars = get_fresh_evars_with_sorts(avoid=list(vars_to_avoid), sorts=list(map(lambda ev: ev.sort, vars_to_rename)))
    vars_fr : List[str] = list(map(lambda e: e.name, vars_to_rename))
    vars_to : List[str] = list(map(lambda e: e.name, new_vars))
    renaming = dict(zip(vars_fr, vars_to))
    trusted_claim_consequent_renamed = ECLP(
        vars=[EVar(name=renaming[v.name], sort=v.sort) for v in trusted_claim.consequent.vars],
        clp=rename_vars_clp(renaming, trusted_claim.consequent.clp)
    )

    # Then I want to check whether the consequent of my axiom implies the consequent of the claim/goal.
    r : EclpImpliesResult = eclp_impl_valid_trough_lists(rs, trusted_claim_consequent_renamed, claim.consequent)
    if (not r.valid) or (r.witness is None):
        return None

    return ECLP(
        vars=list(free_evars_of_clp(trusted_claim.antecedent.clp)),
        clp=trusted_claim.antecedent.clp,
    )

# Phi - CLP (constrained list pattern)
# Psi - ECLP (existentially-quantified CLP)
# user_cutpoints - List of "lockstep invariants" / "circularities" provided by user;
#   each one is an ECLP. Note that they have not been proved to be valid;
#   it is our task to verify them if we need to use them.
def prepare_verifier(
    settings: VerifySettings,
    user_cutpoints : Dict[str,ECLP],
    rs: ReachabilitySystem,
    claim: Claim,
    claim_name : str,
    trusted_claims: Dict[str, Claim],
) -> Verifier:
    antecedent = claim.antecedent
    consequent = claim.consequent
    user_cutpoints_2 = user_cutpoints.copy()
    antecedent_vars = free_evars_of_clp(antecedent.clp)
    consequent_vars = free_evars_of_clp(consequent.clp)
    vars_to_avoid : List[EVar] = list(antecedent_vars.union(consequent_vars))
    if settings.goal_as_cutpoint:
        vars_to_generalize = [ev for ev in free_evars_of_clp(antecedent.clp) if ev not in consequent_vars]
        new_cutpoint = rename_and_generalize_vars_eclp_to_fresh(
            vars_to_avoid=vars_to_avoid,
            vars_to_rename=vars_to_generalize, 
            eclp=antecedent,
        )
        user_cutpoints_2['default']=new_cutpoint

    trusted_axioms: Dict[str, ECLP] = dict()    
    for n,tc in trusted_claims.items():
        tcprime = axiom_from_trusted_claim(rs, claim, tc, vars_to_avoid=vars_to_avoid)
        if tcprime is not None:
            trusted_axioms[n] = tcprime

    verifier = Verifier(
        settings=settings,
        exploration_strategy=StupidExplorationStrategy(),
        goal_conj_chooser_strategy=StackGoalConjunctionChooserStrategy(),
        user_cutpoints=user_cutpoints_2,
        trusted_axioms=trusted_axioms,
        rs=rs,
        arity=len(antecedent.clp.lp.patterns),
        antecedent=antecedent.with_no_vars(),
        consequent=consequent,
    )
    return verifier

def verify(settings: VerifySettings, user_cutpoints : Dict[str,ECLP], rs: ReachabilitySystem, claim: Claim, claim_name : str) -> VerifyResult:
    verifier = prepare_verifier(settings, user_cutpoints, rs, claim, claim_name, trusted_claims=dict())
    return verifier.verify()