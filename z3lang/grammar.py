import lark

grammar = lark.Lark('''
?start: assignment
           | assertion
           | unreachable
           | pushfn
           | pop
           | return
           | env
           | sample

assignment: CNAME "=" expr

assertion: "assert" expr

unreachable: "unreachable"

pushfn: "fn" CNAME "(" argcomma* arg? ")" "->" type "{"

pop: "}"

return: "return" expr

env: "env"

sample: expr


?argcomma: arg ","

arg: CNAME ":" type

?type: Z
      | B
      | range
      | tuple
      | array
      | vec
      | "(" type ")"

range: "range" expr
tuple: "tuple" "[" typecomma* type? "]"
array: "array" type
vec: "vec" type expr

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

?mexpr: term
        | mul

mul: term "*" mexpr

?term: INT
     | TRUE
     | FALSE
     | call
     | CNAME
     | "(" expr ")"
     | listing
     | neg

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


