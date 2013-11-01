require "modules/substitution.k"
require "sif-syntax.k"

module SIF
     imports SIF-SYNTAX
     imports SUBSTITUTION

     configuration 
          <k> $PGM:K </k>
          <store> .Map </store> // Loc |-> Value (H)
          <types> .Map </types> // Loc |-> Type (Sigma)
          <levels> .Map </levels> // Loc |-> SecLvlSub

     syntax KResult ::= Value

     // *** Terms ***

     // Lambda.
     rule (lambda X:Id : _ . E:Term) V:Term => E[V / X]

     // Assignment.
     rule <k> L:Loc := V:Value => [()] ...</k>
          <store> Sto:Map => Sto[V / L] </store>

     // Bang.
     rule <k> ! L:Loc => [V] ...</k>
          <store>... L |-> V:Value ...</store>

     // Conditional.
     rule if true then E:Term else _ => E
     rule if false then _ else E:Term => E

     // *** Exps ***

     // Letval.
     rule let val X:Id = val M:Exp in N:Exp 
          => M ~> let val X = val HOLE in N
          [heat]
     rule M:Exp ~> let val X:Id = val HOLE in N:Exp
          => let val X = val M in N
          [cool]
     rule let val X:Id = (val [V:Value]) in E:Exp => E[V / X]

     // Ref.
     rule <k> ref(Lvl:SecLvl) ( V:Value : A:Type ) => [L] ...</k>
          <store> Sto:Map => Sto[V / L] </store>
          <types> Types:Map => Types[A / L] </types>
          <levels> Lvls:Map => Lvls[Lvl / L] </levels>
          when fresh(L:Loc)
     

endmodule
