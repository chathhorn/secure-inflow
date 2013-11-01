require "sif-syntax.k"

module SIF-TYPING
     imports SIF-SYNTAX

     configuration
          <k> $PGM:K </k>
          //<store> .Map </store> // Loc |-> Value (H)
          <types> .Map </types> // Loc |-> Type (Sigma)
          <levels> .Map </levels> // Loc |-> SecLvl
          <env> .Map </env> // Id |-> Type (Gamma)

     syntax KResult ::= Type
     syntax Term ::= Type
     syntax Exp ::= Type

     syntax Type ::= Type "@" SecLvlSub

     // *** Terms ***

     // Values.
     rule true => bool
     rule false => bool

     rule <k> L:Loc => ref(Lvl) T ...</k>
          <levels>... L |-> Lvl ...</levels>
          <types>... L |-> T ...</types>

     rule <k> X:Id => T ...</k>
          <env>... X |-> T:Type ...</env>

     // Conditional.
     context if _ then HOLE else _
     context if _ then _ else HOLE
     rule if bool then A:Type else A => A

     // Lambda.
     syntax K ::= fun(Type, Term, Map) [strict(2)]

     // Could probably just substitute the Id for its type.
     rule <k> lambda X:Id : A:Type . E:Term => fun(A, E, Env) ...</k>
          <env> Env:Map => Env[A / X] </env>
     rule <k> fun(A:Type, B:Type, Env:Map) => A -> B ...</k>
          <env> _ => Env </env>

     // Application.
     rule (A:Type -> B:Type) A => B

     // Val.
     context val HOLE
     rule val (A:Type @ Lvl:SecLvlSub) => O Lvl A

     // *** Exps ***

     rule [ A:Type ] => A @ (bot, top)

     rule ref(Lvl:SecLvl) (A:Type : A) => (ref(Lvl) A) @ (bot, top)

     rule ! (refr(RLvl:SecLvl) A:Type) => A @ (RLvl, top)

     rule (refw(WLvl:SecLvl) A:Type) := A => () @ (bot, WLvl)

     syntax K ::= letexp(SecLvlSub, Exp, Map) [strict(2)]

     rule <k> let val X:Id = (O Lvl:SecLvlSub A:Type) in E:Exp 
          => letexp(Lvl, E, Env) ...</k>
          <env> Env:Map => Env[A / X] </env>

     rule <k> letexp(Lvl:SecLvlSub, A:Type @ Lvl, Env:Map) => A @ Lvl </k>
          <env> _ => Env </env>

endmodule
