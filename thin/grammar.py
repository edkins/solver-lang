import lark

grammar = lark.Lark(r'''
?start: reset
        | model
        | decl
        | bare_expr

model: "model"
reset: "reset"
decl: type CNAME

?type: inttype
       | booltype
inttype: "int"
booltype: "bool"

bare_expr: expr
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
      | append
      | add
      | sub

append: aexpr "++" mexpr
add: aexpr "+" mexpr
sub: aexpr "-" mexpr

?mexpr: lexpr
        | mul

mul: lexpr "*" mexpr

?lexpr: term
      | lookup

lookup: term "[" expr "]"

?term: int
     | true
     | false
     | len
     | arr
     | call
     | var
     | "(" expr ")"
     | listing
     | neg

len: /len\b/ lexpr
arr: /arr\b/ lexpr
call: CNAME "(" exprcomma* expr? ")"
?exprcomma: expr ","

listing: "[" exprcomma* expr? "]"
neg: "-" term

var: CNAME
int: INT
true: "true"
false: "false"

%import common.CNAME
%import common.INT
%import common.WS

%ignore WS
''')
