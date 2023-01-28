module INCR_MONOTONIC-SPEC
  imports DOMAINS-SYNTAX
  imports IMP

  // verification IDs
  syntax Id ::= "x"     [token]

  claim [my-crl-claim]:
      (ListItem(<T><k>x = x + 1;</k><state>x |-> X0::Int</state></T>) 
       ListItem(<T><k>x = x + 1;</k><state>x |-> X1::Int</state></T>))
       =>
       (ListItem(<T><k>.K</k><state>x |-> ?X0'</state></T>)
        ListItem(<T><k>.K</k><state>x |-> ?X1'</state></T>)
      )
    requires X0 <=Int X1
    ensures ?X0' <=Int ?X1'
   [cartesian, one-path]


endmodule
