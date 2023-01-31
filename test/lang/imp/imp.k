// Taken from https://github.com/runtimeverification/k/blob/3c5e1c329dc69085ac3878583985d52cfc420a9c/k-distribution/pl-tutorial/1_k/2_imp/lesson_4/imp.k
// We replaced 'seqstrict' with 'seqstrict' for performance reasons.
// Also, we added `halt()`
// Copyright (c) 2014-2019 K Team. All Rights Reserved.

requires "my-prelude.md"

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
                 | "halt" "(" ")"
  syntax Pgm ::= "int" Ids ";" Stmt
  syntax Ids ::= List{Id,","}
endmodule

module IMP
  imports IMP-SYNTAX
  
  imports DOMAINS

  syntax KResult ::= Int | Bool

  configuration <T color="yellow">
                  <k color="green"> $PGM:Pgm </k>
                  <state color="red"> .Map </state>
                </T>


  rule <k> X:Id => STATE[X] ... </k> <state> STATE </state> requires X in_keys(STATE)

  rule <k> I1 / I2 => I1 /Int I2 ... </k>  requires I2 =/=Int 0
  rule <k> I1 + I2 => I1 +Int I2 ... </k>

  rule <k> I1 <= I2   => I1 <=Int I2 ... </k>
  rule <k> ! T        => notBool T   ... </k>
  rule <k> true && B  => B           ... </k>
  rule <k> false && _ => false       ... </k>

  rule <k> {}  => . ... </k>
  rule <k> {S} => S ... </k>

  rule <k> X = I:Int; => . ... </k> <state> STATE => STATE [ X <- I ] </state>

  rule <k> S1:Stmt S2:Stmt => S1 ~> S2 ... </k>

  rule <k> if (true)  S else _ => S ... </k>
  rule <k> if (false) _ else S => S ... </k>

  rule <k> while (B) S => if (B) {S while (B) S} else {} ... </k>

  rule <k> int (X , Xs => Xs) ; _ ... </k> <state> STATE => STATE [ X <- 0 ] </state>
    requires notBool (X in keys(STATE))

  rule <k> int .Ids ; S => S ... </k>


  rule [halt]: <k> halt() => . ... </k>

// verification ids
  syntax Id ::= "n"     [token]
              | "sum"   [token]
endmodule
