module INCR_MONOTONIC-SPEC
  imports DOMAINS-SYNTAX
  imports IMP

  // verification IDs
  syntax Id ::= "x"     [token]


  claim [my-crl-claim]:
      (ListItem(<T><k>x = x + 1; ~> halt()</k><state>x |-> X0::Int</state></T>) 
       ListItem(<T><k>x = x + 1; ~> halt()</k><state>x |-> X1::Int</state></T>))
       =>
       (ListItem(<T><k>halt() ~> .K</k><state>x |-> ?X0'</state></T>)
        ListItem(<T><k>halt() ~> .K</k><state>x |-> ?X1'</state></T>)
      )
    requires X0 <=Int X1
    ensures ?X0' <=Int ?X1'
    // ensures (1 +Int ?X0') <=Int ?X1' // cannot be proven. TODO create a negative test
   [cartesian, one-path]

/*
claim [my-crl-claim]:
      (ListItem(<T><k>x = x + 1; ~> halt()</k><state>x |-> X0::Int</state></T>) 
       ListItem(<T><k>x = x + 1; ~> halt()</k><state>x |-> X1::Int</state></T>))
       =>
       (ListItem(<T><k>halt() ~> .K</k><state> ?ST0' </state></T>)
        ListItem(<T><k>halt() ~> .K</k><state> ?ST1' </state></T>)
      )
      requires X0 <=Int X1
      //ensures (x in_keys(?ST0')) andBool (x in_keys(?ST1'))
      [cartesian, one-path]
    //requires X0 <=Int X1
    //ensures ?X0' <=Int ?X1'
  */

endmodule
