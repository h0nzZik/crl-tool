# Checks an implication between two ECLPs.
# Returns a substitution or a None
def eclp_check_impl(Phi, Psi):
    pass

# Phi - CLP (constrained list pattern)
# Psi - ECLP (existentially-quantified CLP)
# user_cutpoints - List of "lockstep invariants" / "circularities" provided by user;
#   each one is a CLP. Note that they have not been proved to be valid;
#   it is our task to verify them if we need to use them.
# instantiated_cutpoints
# flushed_cutpoints
def verify(S, Phi, Psi, user_cutpoints, instantiated_cutpoints = [], flushed_cutpoints = []):
    if (subst := eclp_check_impl(Phi, Psi)) is not None:
        return True # build a proof object using subst, Conseq, Reflexivity
    
    # For each flushed cutpoint we compute a substitution which specialize it to the current 'state', if possible.
    flushed_cutpoints_with_subst = [(PhiC, eclp_check_impl(Phi, PhiC)) for PhiC in flushed_cutpoints]
    # Is there some flushed cutpoint / axiom which matches our current state? If so, we are done.
    usable_flushed_cutpoints = [(PhiC, subst) for (PhiC, subst) in flushed_cutpoints_with_subst if subst is not None]
    if (len(list(usable_flushed_cutpoints)) > 0):
        return True # Conseq, Axiom

    # For each user cutpoint we compute a substitution which specialize it to the current 'state', if possible.
    user_cutpoints_with_subst = [(PhiC, eclp_check_impl(Phi, PhiC)) for PhiC in user_cutpoints]
    # The list of cutpoints matching the current 'state'
    usable_cutpoints = [(PhiC, subst) for (PhiC, subst) in user_cutpoints_with_subst if subst is not None]
    # If at least on succeeds, it is good.
    for (PhiC, subst) in usable_cutpoints:
        # apply Conseq (using [subst]) to change the goal to [PhiC]
        # apply Circularity
        # We filter [user_cutpoints] to prevent infinite loops
        if verify(S, PhiC, Psi,
            #user_cutpoints=[x for x in user_cutpoints if check_impl(x, PhiC) is None],
            user_cutpoints=[x for x in user_cutpoints if x != PhiC],
            instantiated_cutpoints=(instantiated_cutpoints + [PhiC]),
            flushed_cutpoints=flushed_cutpoints
        ):
            return True
    
    for j in range(0, arity_of(Phi)):
        # TODO We can execute a component [j] until it partially matches the corresponding component of some circularity/axiom
        step_result = make_step(Phi.component[j], steps=1)
        # Cannot rewrite the j'th component anymore
        if noRewriteStepHappened(step_result):
            continue
        # Assuming that a rewrite step happened
        for (b in branches_of(step_result)):
            newPhi = Phi.with_component(j, b)
            # prune inconsistent branches (since we have the toplevel constraint in Phi/newPhi)
            if not consistent(newPhi):
                continue
            if verify(S, newPhi,
                user_cutpoints=user_cutpoints,
                instantiated_cutpoints=[],
                flushed_cutpoints=instantiated_cutpoints+flushed_cutpoints) is False:
                return False
        return True
    
    return False
