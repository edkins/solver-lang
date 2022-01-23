import lark

grammar = lark.Lark(r'''
start: statement*

?statement: def_eq
        | def
        | introduce
        | fn
        | bare_expr

def_eq: DEF CNAME EQ expr NEWLINE
def: DEF nametypes OPEN NEWLINE inner_statements CLOSE NEWLINE
introduce: INTRODUCE nametypes OPEN NEWLINE inner_statements CLOSE NEWLINE
nametypes: (nametype ",")* nametype?
nametype: CNAME COLON type

fn: FN CNAME OPEN_PAREN nametypes CLOSE_PAREN EQ expr NEWLINE

DEF: "def"
INTRODUCE: "introduce"
FN: "fn"
OPEN: "{"
CLOSE: "}"
COLON: ":"
EQ: "="

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

eq: aexpr "=" aexpr
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
     | paren
     | listing
     | neg

paren: OPEN_PAREN expr CLOSE_PAREN
OPEN_PAREN: "("
CLOSE_PAREN: ")"

len: /len\b/ lexpr
arr: /arr\b/ lexpr
call: CNAME OPEN_PAREN exprcommas CLOSE_PAREN
exprcommas: exprcomma* expr?
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
