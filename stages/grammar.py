import lark

grammar = lark.Lark('''
?start: statements
statements: statement*

?statement: assign
           | assert
           | unreachable
           | fn
           | return

assign: CNAME "=" expr

assert: "assert" expr

unreachable: "unreachable"

fn: "fn" CNAME "(" args ")" "->" type "{" statements "}"
args: argcomma* arg?

return: "return" expr


?argcomma: arg ","

arg: CNAME ":" type

?type: Z
      | B
      | range
      | tuple
      | array
      | vec
      | union
      | "(" type ")"

range: "range" expr
tuple: "tuple" "[" typecomma* type? "]"
array: "array" type
vec: "vec" type expr
union: "union" "[" typecomma* type? "]"

?typecomma: type ","

?expr: aexpr
     | eq
     | lt
     | le
     | gt
     | ge
     | ne

eq: aexpr "==" aexpr
lt: aexpr "<" aexpr
le: aexpr "<=" aexpr
gt: aexpr ">" aexpr
ge: aexpr ">=" aexpr
ne: aexpr "!=" aexpr

?aexpr: mexpr
      | add
      | sub

add: aexpr "+" mexpr
sub: aexpr "-" mexpr

?mexpr: lexpr
        | mul

mul: lexpr "*" mexpr

?lexpr: term
      | lookup

lookup: term "[" expr "]"

?term: INT
     | TRUE
     | FALSE
     | len
     | call
     | CNAME
     | "(" expr ")"
     | listing
     | neg

len: "len" lexpr
call: CNAME "(" exprcomma* expr? ")"
?exprcomma: expr ","

listing: "[" exprcomma* expr? "]"
neg: "-" term

TRUE: "true"
FALSE: "false"
Z: "int"
B: "bool"


%import common.CNAME
%import common.INT
%import common.WS

%ignore WS
''')


