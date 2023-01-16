// Taken from https://github.com/runtimeverification/k/blob/3c5e1c329dc69085ac3878583985d52cfc420a9c/k-distribution/pl-tutorial/1_k/2_imp/lesson_4/imp.k
// We replaced 'seqstrict' with 'seqstrict' for performance reasons
// Copyright (c) 2014-2019 K Team. All Rights Reserved.

module IMP-SYNTAX
  imports DOMAINS-SYNTAX
  syntax AExp  ::= Int | Id
                 | "-" Int
                 | AExp "/" AExp              [left, seqstrict]
                 | "(" AExp ")"               [bracket]
                 > AExp "+" AExp              [left, seqstrict]
  syntax BExp  ::= Bool
                 | AExp "<=" AExp             [seqstrict, latex({#1}\leq{#2})]
                 | "!" BExp                   [seqstrict]
                 | "(" BExp ")"               [bracket]
                 > BExp "&&" BExp             [left, seqstrict(1)]
  syntax Block ::= "{" "}"
                 | "{" Stmt "}"
  syntax Stmt  ::= Block
                 | Id "=" AExp ";"            [seqstrict(2)]
                 | "if" "(" BExp ")"
                   Block "else" Block         [seqstrict(1)]
                 | "while" "(" BExp ")" Block
                 > Stmt Stmt                  [left]
  syntax Pgm ::= "int" Ids ";" Stmt
  syntax Ids ::= List{Id,","}
endmodule


module IMP
  imports IMP-SYNTAX
  
  //imports DOMAINS
  imports INT-COMMON
  imports BOOL-COMMON
  imports BASIC-K

  syntax KResult ::= Int | Bool

  configuration <T color="yellow">
                  <k color="green"> $PGM:Pgm </k>
                  <state color="red"> .Map </state>
                </T>

// AExp
  rule <k> X:Id => I ...</k> <state>... X |-> I ...</state>
  rule I1 / I2 => I1 /Int I2  requires I2 =/=Int 0
  rule I1 + I2 => I1 +Int I2
  rule - I1 => 0 -Int I1
// BExp
  rule I1 <= I2 => I1 <=Int I2
  rule ! T => notBool T
  rule true && B => B
  rule false && _ => false
// Block
  rule {} => .   [structural]
  rule {S} => S  [structural]
// Stmt
  rule <k> X = I:Int; => . ...</k> <state>... X |-> (_ => I) ...</state>
  rule S1:Stmt S2:Stmt => S1 ~> S2  [structural]
  rule if (true)  S else _ => S
  rule if (false) _ else S => S
  rule while (B) S => if (B) {S while (B) S} else {}  [structural]
// Pgm
  rule <k> int (X,Xs => Xs);_ </k> <state> Rho:Map (.Map => X|->0) </state>
    requires notBool (X in_keys(Rho))
  rule int .Ids; S => S  [structural]

// verification ids
  syntax Id ::= "n"     [token]
              | "sum"   [token]
endmodule
