
// From Crary, Kliger, and Pfenning.
module SIF-SYNTAX

     syntax Id ::= Token{[a-zA-Z]+} [onlyLabel]

     syntax SecLvl ::= "top" | "bot"

     syntax OpLvl ::= "(" SecLvl "," SecLvl ")"

     syntax Loc ::= "null"

     syntax One ::= "()" // Single-element type (and its single element).

     syntax Type ::= "(" Type ")" [bracket]
                   | One
                   | "bool" 
                   > "ref" "(" SecLvl ")" Type
                   | "refr" "(" SecLvl ")" Type
                   | "refw" "(" SecLvl ")" Type
                   | "O" OpLvl Type
                   > Type "->" Type

     syntax Value ::= Id | One | Bool | Loc

     syntax Term ::= "(" Term ")" [bracket]
                   | Value
                   > "val" Exp
                   > Term Term [seqstrict]
                   > "lambda" Id ":" Type "." Term [binder]
                   > "if" Term "then" Term "else" Term [strict(1)]

     syntax Exp ::= "[" Term "]" [strict]
                  | "!" Term [strict]
                  | Term ":=" Term [strict]
                  | "ref" "(" SecLvl ")" "(" Term ":" Type ")" [strict(2)]
                  > "let" "val" Id "=" Term "in" Exp [binder, strict(2)]

endmodule

