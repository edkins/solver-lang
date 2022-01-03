import lark

grammar = lark.Lark(r'''
?start: assign
        | assert
        | unreachable
        | pushfn
        | pop
        | return
        | sample

assign: CNAME "=" expr
assert: "assert" expr
unreachable: "unreachable"
pushfn: "fn" CNAME "(" argcomma* arg? ")" "->" type "{"
pop: "}"
return: "return" expr
sample: expr


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

?term: INT
     | TRUE
     | FALSE
     | len
     | arr
     | call
     | CNAME
     | "(" expr ")"
     | listing
     | neg

len: /len\b/ lexpr
arr: /arr\b/ lexpr
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


