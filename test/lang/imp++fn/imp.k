// Copyright (c) K Team. All Rights Reserved.

module IMP-SYNTAX
  imports DOMAINS-SYNTAX
  syntax Val ::= Int | String
  syntax AExp  ::= Val | Id
                 | "++" Id
                 | Id "(" AExps ")"           [strict(2)]
                 | "-" Int
                 | "(" AExp ")"               [bracket]
                 > AExp "/" AExp              [left, strict, division]
                 > AExp "+" AExp              [left, strict]
  syntax BExp  ::= Bool
                 | AExp "<=" AExp             [seqstrict, latex({#1}\leq{#2})]
                 | "!" BExp                   [strict]
                 | "(" BExp ")"               [bracket]
                 > BExp "&&" BExp             [left, strict(1)]
  syntax Block ::= "{" "}"
                 | "{" Stmt "}"
  syntax Stmt  ::= Block
                 | AExp ";"                   [strict]
                 | Id "=" AExp ";"            [strict(2)]
                 | "if" "(" BExp ")"
                   Block "else" Block         [strict(1)]
                 | "while" "(" BExp ")" Block
                 | "int" Ids ";"
                 | "return" AExp ";"          [strict]
                 > Stmt Stmt                  [left]
    
  syntax Function ::= "function" Id "("Ids")" Block
  syntax Pgm ::= Function | Pgm Pgm           [left]

  syntax Ids  ::= List{Id,","}           [klabel(Exps)]
  syntax AExps ::= List{AExp,","}          [klabel(Exps), strict]  // automatically hybrid now
  syntax AExps ::= Ids
endmodule


module IMP
  imports IMP-SYNTAX
  imports DOMAINS
  syntax KResult ::= Bool | Val | Vals
  syntax Vals  ::= List{Val,","}              [klabel(Exps)]
  syntax AExps ::= Vals
  syntax Bottom
  syntax Bottoms ::= List{Bottom,","}    [klabel(Exps)]
  syntax Ids ::= Bottoms
  syntax Vals ::= Bottoms

  syntax Id ::= "main" [token]

  configuration <T color="yellow">
                  <functions color="grey"> .Map </functions>
                  <k color="green"> $PGM:Pgm ~> main(.Vals) </k>
                  <env color="LightSkyBlue"> .Map </env>
                  <stack> .List </stack>
                  <store color="red"> .Map </store>
                </T>

// AExp
  rule <k> X:Id => I ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> I ...</store>  [lookup]
  rule <k> ++X => I +Int 1 ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> (I => I +Int 1) ...</store>  [increment]
  rule I1 / I2 => I1 /Int I2  when I2 =/=Int 0
  rule I1 + I2 => I1 +Int I2
  rule - I => 0 -Int I
// BExp
  rule I1 <= I2 => I1 <=Int I2
  rule ! T => notBool T
  rule true && B => B
  rule false && _ => false
// Block
  rule {} => .   [structural]
  rule {S} => S  [structural]
// Stmt
  rule <k> X = I:Int; => . ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> (_ => I) ...</store>
  rule S1:Stmt S2:Stmt => S1 ~> S2  [structural]
  rule if (true)  S else _ => S
  rule if (false) _ else S => S
  rule while (B) S => if (B) {S while (B) S} else {}  [structural]

  rule <k> int (X:Id,Xs:Ids => Xs); ...</k>
       <env> Rho => Rho[X <- !N:Int] </env>
       <store>... .Map => !N |-> 0 ...</store>
  rule int .Ids; => .  [structural]

  rule S1:Pgm S2:Pgm => S1 ~> S2  [structural]
  rule <k> function X:Id (Xs:Ids) Bl:Block => .K ...</k>
       <functions> Fns => Fns[X <- function X:Id (Xs:Ids) Bl] </functions>

  syntax Frame ::= frame(K, Map)

  rule <k> X:Id(Vs:Vals) ~> K => bind(Xs,Vs) ~> Bl ~> return 0 ; </k>
       <env> Env => .Map </env>
       <stack> .List => ListItem(frame (K, Env)) ...</stack>
       <functions>... X |-> function X(Xs) Bl ...</functions>
  
  rule <k> return V:Val ; ~> _ => V ~> K </k>
       <env> _ => Env </env>
       <stack> ListItem (frame (K:K, Env:Map)) => .List ...</stack>
  
  syntax KItem ::= bind(Ids, Vals)
  rule bind(.Ids, .Vals) => .K
  rule <k> bind((X:Id, Xs:Ids => Xs), (V:Val, Vs:Vals => Vs)) ...</k>
       <env> Rho => Rho[X <- !N:Int] </env>
       <store>... .Map => !N |-> V ...</store>
endmodule
