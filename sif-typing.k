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

     syntax Type ::= Type "@" OpLvl

     // *** Informativeness ***

     syntax Bool ::= Type "/^" SecLvl [function]
                   | Type "/^'" SecLvl [function]

     // This is instead of 10 & 11.
     rule A:Type /^ bot => (A /^' bot) orElseBool (A /^' top)
     rule A:Type /^ top => (A /^' top) ==K true

     // 1.
     rule _ /^' bot => true

     // 2.
     rule () /^' _ => true

     // 3.
     rule (_ -> B:Type) /^' Lvl:SecLvl => B /^ Lvl

     // 4. Simplified by the total ordering on security levels.
     rule O (_, WLvl:SecLvl) A:Type /^' Lvl:SecLvl 
          => (A /^ Lvl) orBool (A /^ WLvl)
          
     // 5.
     rule ref(Lvl:SecLvl) _ /^' Lvl => true

     // 6.
     rule ref(_) A:Type /^' Lvl:SecLvl => true
          when A /^ Lvl

     // 7.
     rule refr(_) A:Type /^' Lvl:SecLvl => true
          when A /^ Lvl

     // 8.
     rule refr(Lvl:SecLvl) _ /^' Lvl => true

     // 9.
     rule refw(Lvl:SecLvl) _ /^' Lvl => true

     // 10 & 11. Made redundant by the trivial lattice of security levels.

     // *** Partial order on types ***

     syntax Bool ::= Type "<=Type" Type [function]
                   | Type "<=Type'" Type [function]

     rule A:Type <=Type B:Type => (A <=Type' B) ==K true

     // 12.
     rule A:Type <=Type' A => true

     // 13.
     rule A':Type -> B':Type  <=Type' A:Type -> B:Type => true
          when (A <=Type A') andBool (B <=Type B')

     // 14.
     rule O Lvl:OpLvl A:Type <=Type O Lvl':OpLvl B => true
          when (A <=Type B) andBool (Lvl <=OpLvl Lvl')

     // 15.
     rule ref(Lvl:SecLvl) A:Type <=Type refr(Lvl':SecLvl) B:Type => true
          when (A <=Type B) andBool (Lvl <=SecLvl Lvl')

     // 16.
     rule ref(Lvl:SecLvl) A:Type <=Type refw(Lvl':SecLvl) B:Type => true
          when (B <=Type A) andBool (Lvl' <=SecLvl Lvl)

     // 17.
     rule refr(Lvl:SecLvl) A:Type <=Type refr(Lvl':SecLvl) B:Type => true
          when (A <=Type B) andBool (Lvl <=SecLvl Lvl')

     // 18.
     rule refw(Lvl:SecLvl) A:Type <=Type refw(Lvl':SecLvl) B:Type => true
          when (B <=Type A) andBool (Lvl' <=SecLvl Lvl)

     // *** Partial order on operation levels ***

     syntax Bool ::= OpLvl "<=OpLvl" OpLvl [function]
                   | OpLvl "<=OpLvl'" OpLvl [function]

     rule A:OpLvl <=OpLvl B:OpLvl => (A <=OpLvl' B) ==K true

     rule (L:SecLvl, M:SecLvl) <=OpLvl' (L':SecLvl, M':SecLvl) => true
          when (L <=SecLvl L') andBool (M' <=SecLvl M)

     // *** (Total) order on security levels ***

     syntax Bool ::= SecLvl "<=SecLvl" SecLvl [function]
                   | SecLvl "<=SecLvl''" SecLvl [function]

     rule A:SecLvl <=SecLvl B:SecLvl => (A <=SecLvl' B) ==K true

     // We actually only have two security levels right now, so this is
     // pretty trivial.
     rule A:SecLvl <=SecLvl' A => true
     rule bot <=SecLvl' _ => true
     rule _ <=SecLvl' top => true

     // *** Terms ***

     // 19.
     rule <k> X:Id => T ...</k>
          <env>... X |-> T:Type ...</env>

     // 20.
     rule <k> L:Loc => ref(Lvl) T ...</k>
          <levels>... L |-> Lvl ...</levels>
          <types>... L |-> T ...</types>

     // 21--23. Values.
     rule true => bool
     rule false => bool

     // 24. Conditional.
     context if _ then HOLE else _
     context if _ then _ else HOLE
     rule if bool then A:Type else A => A

     // 25. Lambda.
     syntax K ::= fun(Type, Term, Map) [strict(2)]

     // Could probably just substitute the Id for its type.
     rule <k> lambda X:Id : A:Type . E:Term => fun(A, E, Env) ...</k>
          <env> Env:Map => Env[A / X] </env>
     rule <k> fun(A:Type, B:Type, Env:Map) => A -> B ...</k>
          <env> _ => Env </env>

     // 26. Application.
     rule (A:Type -> B:Type) A => B

     // 27. Val.
     context val HOLE
     rule val (A:Type @ Lvl:OpLvl) => O Lvl A

     // 28. TODO (subtyping/weakening)

     // *** Exps ***

     // 29. 
     rule [ A:Type ] => A @ (bot, top)

     // 30.
     syntax K ::= letexp(OpLvl, Exp, Map) [strict(2)]

     rule <k> let val X:Id = (O Lvl:OpLvl A:Type) in E:Exp 
          => letexp(Lvl, E, Env) ...</k>
          <env> Env:Map => Env[A / X] </env>

     rule <k> letexp(Lvl:OpLvl, A:Type @ Lvl, Env:Map) => A @ Lvl </k>
          <env> _ => Env </env>

     // 31.
     rule ref(Lvl:SecLvl) (A:Type : A) => (ref(Lvl) A) @ (bot, top)

     // 32.
     rule ! (refr(RLvl:SecLvl) A:Type) => A @ (RLvl, top)

     // 33.
     rule (refw(WLvl:SecLvl) A:Type) := A => () @ (bot, WLvl)

     // 34--36.
     // rule ref(Lvl:SecLevl) A:Type := B:Type
     //      => 



endmodule
