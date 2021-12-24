import lark

grammar = lark.Lark('''
?start: assignment
           | assertion
           | pushfn
           | pop
           | return
           | env
           | sample

assignment: CNAME "=" expr

assertion: "assert" expr

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

range: "range" expr


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
     | neg

call: CNAME "(" exprcomma* expr? ")"
?exprcomma: expr ","

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


