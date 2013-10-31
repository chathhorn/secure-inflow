require "modules/substitution.k"

// From Crary, Kliger, and Pfenning.
module SIF-SYNTAX

     syntax Id ::= Token{[a-zA-Z]+} [onlyLabel]

     syntax SecLvl ::= "Hi" | "Lo" | Int

     syntax SecLvlSub ::= "(" SecLvl "," SecLvl ")"

     syntax Loc ::= "null"

     syntax Type ::= "1" 
                   | "bool" 
                   > "ref" SecLvlSub Type
                   | "refr" SecLvlSub Type
                   | "refw" SecLvlSub Type
                   | "O" SecLvlSub Type
                   > Type "->" Type

     syntax Term ::= "(" Term ")" [bracket]
                   | Id
                   | "*"
                   | "veritum" | "falsum"
                   | Loc
                   > "val" Term
                   > Term Term
                   > "lambda" Id "is" Type "." Term [binder]
                   > "if" Term "then" Term "else" Term

     syntax Exp ::= "[" Term "]"
                  | "!" Term
                  | Term ":=" Term
                  | "ref" SecLvlSub "(" Term "," Type ")"
                  > "let" "val" Id "=" Term "in" Exp [binder]

     syntax Term ::= "true"

endmodule

module SIF
     imports SIF-SYNTAX
     imports SUBSTITUTION

     configuration <k> $PGM:K </k>

     rule (lambda X:Id is _ . E:Term) V:Term => E[V / X]

endmodule
