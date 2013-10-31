
// From Crary, Kliger, and Pfenning.
module SIF-SYNTAX

     syntax Id ::= Token{[a-zA-Z]+} [onlyLabel]

     syntax SecLvl ::= "top" | "bot"

     syntax SecLvlSub ::= "(" SecLvl "," SecLvl ")"

     syntax Loc ::= "null"

     syntax Type ::= "(" Type ")" [bracket]
                   | "un" 
                   | "bool" 
                   > "ref" SecLvlSub Type
                   | "refr" "(" SecLvl ")" Type
                   | "refw" "(" SecLvl ")" Type
                   | "O" SecLvlSub Type
                   > Type "->" Type

     syntax Value ::= Id | "*" | Bool | Loc

     syntax Term ::= "(" Term ")" [bracket]
                   | Value
                   > "val" Exp
                   > Term Term [seqstrict]
                   > "lambda" Id ":" Type "." Term [binder]
                   > "if" Term "then" Term "else" Term [strict(1)]

     syntax Exp ::= "[" Term "]" [strict]
                  | "!" Term [strict]
                  | Term ":=" Term [strict]
                  | "ref" SecLvlSub "(" Term ":" Type ")" [strict(2)]
                  > "let" "val" Id "=" Term "in" Exp [binder, strict(2)]

endmodule

