import lark

grammar = lark.Lark(r'''
start: statement*

?statement: def
        | introduce
        | bare_expr

def: DEF nametypes OPEN NEWLINE inner_statements CLOSE NEWLINE
introduce: "introduce" nametypes OPEN inner_statements CLOSE
nametypes: (nametype ",")* nametype?
nametype: CNAME COLON type

DEF: "def"
OPEN: "{"
CLOSE: "}"
COLON: ":"

inner_statements: inner_statement*
?inner_statement: bare_expr
                | blank
blank: NEWLINE

?type: inttype
       | booltype
inttype: "int"
booltype: "bool"

bare_expr: expr NEWLINE
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

%import common.CNAME
%import common.INT
%import common.NEWLINE

%ignore /[ ]/+
''', parser='lalr')
