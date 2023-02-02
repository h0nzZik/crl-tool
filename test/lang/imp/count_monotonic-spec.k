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
       (ListItem(<T><k>halt() ~> .K</k><state>(x |-> ?X0':Int) (y |-> ?Y0':Int)</state></T>)
        ListItem(<T><k>halt() ~> .K</k><state>(x |-> ?X1':Int) (y |-> ?Y1':Int)</state></T>)
      )
    requires (X0 <=Int X1) andBool (Y0 <=Int Y1)
    ensures (?Y0' <=Int ?Y1')
    //ensures (?X0' ==Int 10)
   [cartesian, one-path]


endmodule