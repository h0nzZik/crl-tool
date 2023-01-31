module NEED_CONTRADICTION-SPEC
  imports DOMAINS-SYNTAX
  imports IMP


  // verification IDs
  syntax Id ::= "x"     [token]


  /*
    The idea behind this claim is that the program in the first component cannot go into the `else` branch,
    because the ordering on integers is transitive - that is, (X0 <=Int X1) andBool (X1 <=Int 3) implies (X0 <=Int 3).
    After branching, the prover should realize that the `else` branch is infeasible when considered together with the
    global condition, and should prune it.

    There are two caveats, though.
    1) Currently, the second component holds an empty/stuck program. In future we want to also call the normal RL solver
       in situations when we have only one component 'live'. When we have that, we need to adapt this example
       because it would be discharged by this feature and not test the feature that it is intended to test.
    2) Maybe we will need to be able to localize some side conditions? For example, if the side condition says
       that `X0 ==Int 10`, we may want to plug the value `10` into the configuration, otherwise.. i am not sure,
       but maybe pruning infeasible branches is not enough? Not sure.
   */
  claim [my-crl-claim]:
      (ListItem(<T><k>if (x <= 3 ) { x = 10; } else { x = 20; } ~> halt() </k><state>x |-> X0::Int</state></T>) 
       ListItem(<T><k>halt() ~> .K</k><state>x |-> X1::Int</state></T>))
       =>
       (ListItem(<T><k>halt() ~> .K</k><state>x |-> ?X0'</state></T>)
        ListItem(<T><k>halt() ~> .K</k><state>x |-> ?X1'</state></T>)
      )
    requires (X0 <=Int X1) andBool (X1 <=Int 3)
    ensures (?X0' ==Int 10)
   [cartesian, one-path]


endmodule