module COUNT_MONOTONIC-SPEC
  imports DOMAINS-SYNTAX
  imports IMP


  // verification IDs
  syntax Id ::= "x"     [token]
              | "y"     [token]


  claim [my-crl-claim]:
      (ListItem(<T><k>while(1 <= x) { x = x + (-1); y = y + 1; } ~> halt() </k><state>(x |-> X0::Int) (y |-> Y0::Int)</state></T>) 
       ListItem(<T><k>while(1 <= x) { x = x + (-1); y = y + 1; } ~> halt() </k><state>(x |-> X1::Int) (y |-> Y1::Int)</state></T>))
       =>
       (ListItem(<T><k>halt() ~> .K</k><state>(x |-> ?_X0':Int) (y |-> ?Y0':Int)</state></T>)
        ListItem(<T><k>halt() ~> .K</k><state>(x |-> ?_X1':Int) (y |-> ?Y1':Int)</state></T>)
      )
    requires (X0 <=Int X1) andBool (Y0 <=Int Y1)
    ensures (?Y0' <=Int ?Y1')
   [cartesian, one-path]


    /*
      Consider the above claim [my-crl-claim].
      When the first component finishes its execution, the second one may still continue looping, because
      its initial value of `x` is higher. So we get one case like the lhs of this axiom.
      We then use this axiom to discharge the proof obligation.
      In future, the obligation should be discharged by a call to a normal reachability logic prover.
     */
   claim [my-axiom]:
       (ListItem(<T><k>halt() ~> .K </k><state>(x |-> _:Int) (y |-> Y0t:Int)</state></T>) 
       ListItem(<T><k>while(1 <= x) { x = x + (-1); y = y + 1; } ~> halt() </k><state>(x |-> _:Int) (y |-> Y1:Int)</state></T>))
       =>
       (ListItem(<T><k>halt() ~> .K</k><state>(x |-> ?_:Int) (y |-> Y0t:Int)</state></T>)
        ListItem(<T><k>halt() ~> .K</k><state>(x |-> ?_:Int) (y |-> ?YY1':Int)</state></T>)
      )
    requires (Y0t <=Int Y1)
    ensures (Y0t <=Int ?YY1')
   [cartesian, one-path, trusted]

endmodule