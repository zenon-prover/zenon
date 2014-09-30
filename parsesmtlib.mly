%{
open Smtlib_syntax;;

type pos = int;;
type pd = pos * extradata;;

let line = ref 1;;
let cur_pd () = (!line, ());;

let parse_error s =
    print_string s;
    print_string " on line ";
    print_int !line;
    print_string "\n";;

%}

%start main

%token EOF AS ASSERT CHECKSAT DECLAREFUN DECLARESORT DEFINEFUN DEFINESORT EXCLIMATIONPT EXISTS EXIT FORALL GETASSERT GETASSIGN GETINFO GETOPTION GETPROOF GETUNSATCORE GETVALUE LET LPAREN POP PUSH RPAREN SETINFO SETLOGIC SETOPTION UNDERSCORE
%token <string> ASCIIWOR BINARY DECIMAL HEXADECIMAL KEYWORD NUMERAL STRINGLIT SYMBOL

%type <Smtlib_syntax.commands option> main
%type <Smtlib_syntax.an_option> an_option
%type <Smtlib_syntax.attribute> attribute
%type <Smtlib_syntax.attributevalsexpr_attributevalue_sexpr5> attributevalsexpr_attributevalue_sexpr5
%type <Smtlib_syntax.attributevalue> attributevalue
%type <Smtlib_syntax.command> command
%type <Smtlib_syntax.commanddeclarefun_command_sort13> commanddeclarefun_command_sort13
%type <Smtlib_syntax.commanddefinefun_command_sortedvar15> commanddefinefun_command_sortedvar15
%type <Smtlib_syntax.commanddefinesort_command_symbol11> commanddefinesort_command_symbol11
%type <Smtlib_syntax.commandgetvalue_command_term24> commandgetvalue_command_term24
%type <Smtlib_syntax.commands> commands
%type <Smtlib_syntax.commands_commands_command30> commands_commands_command30
%type <Smtlib_syntax.identifier> identifier
%type <Smtlib_syntax.idunderscoresymnum_identifier_numeral33> idunderscoresymnum_identifier_numeral33
%type <Smtlib_syntax.infoflag> infoflag
%type <Smtlib_syntax.qualidentifier> qualidentifier
%type <Smtlib_syntax.sexpr> sexpr
%type <Smtlib_syntax.sexprinparen_sexpr_sexpr41> sexprinparen_sexpr_sexpr41
%type <Smtlib_syntax.sort> sort
%type <Smtlib_syntax.sortedvar> sortedvar
%type <Smtlib_syntax.sortidsortmulti_sort_sort44> sortidsortmulti_sort_sort44
%type <Smtlib_syntax.specconstant> specconstant
%type <Smtlib_syntax.symbol> symbol
%type <Smtlib_syntax.term> term
%type <Smtlib_syntax.termexclimationpt_term_attribute64> termexclimationpt_term_attribute64
%type <Smtlib_syntax.termexiststerm_term_sortedvar62> termexiststerm_term_sortedvar62
%type <Smtlib_syntax.termforallterm_term_sortedvar60> termforallterm_term_sortedvar60
%type <Smtlib_syntax.termletterm_term_varbinding58> termletterm_term_varbinding58
%type <Smtlib_syntax.termqualidterm_term_term56> termqualidterm_term_term56
%type <Smtlib_syntax.varbinding> varbinding
%type <pd> cur_position

%%

main:
    | commands      { Some($1) }
    | EOF           { None }

cur_position:
    | { cur_pd () }

an_option:
    | attribute     { AnOptionAttribute(pd_attribute $1, $1) }

attribute:
    | cur_position KEYWORD
                    { AttributeKeyword($1, $2) }
    | cur_position KEYWORD attributevalue
                    { AttributeKeywordValue($1, $2, $3) }

attributevalue:
    | specconstant  { AttributeValSpecConst(pd_specconstant $1, $1) }
    | symbol        { AttributeValSymbol(pd_symbol $1, $1) }
    | cur_position LPAREN attributevalsexpr_attributevalue_sexpr5 RPAREN
                    { AttributeValSexpr($1, $3) }

command:
    | cur_position LPAREN SETLOGIC symbol RPAREN
                    { CommandSetLogic($1, $4) }
    | cur_position LPAREN SETOPTION an_option RPAREN
                    { CommandSetOption($1, $4) }
    | cur_position LPAREN SETINFO attribute RPAREN
                    { CommandSetInfo($1, $4) }
    | cur_position LPAREN DECLARESORT symbol NUMERAL RPAREN
                    { CommandDeclareSort($1, $4, $5) }
    | cur_position LPAREN DEFINESORT symbol LPAREN commanddefinesort_command_symbol11 RPAREN sort RPAREN
                    { CommandDefineSort($1, $4, $6, $8) }
    | cur_position LPAREN DECLAREFUN symbol LPAREN commanddeclarefun_command_sort13 RPAREN sort RPAREN
                    { CommandDeclareFun($1, $4, $6, $8) }
    | cur_position LPAREN DEFINEFUN symbol LPAREN commanddefinefun_command_sortedvar15 RPAREN sort term RPAREN
                    { CommandDefineFun($1, $4, $6, $8, $9) }
    | cur_position LPAREN PUSH NUMERAL RPAREN
                    { CommandPush($1, $4) }
    | cur_position LPAREN POP NUMERAL RPAREN
                    { CommandPop($1, $4) }
    | cur_position LPAREN ASSERT term RPAREN
                    { CommandAssert($1, $4) }
    | cur_position LPAREN CHECKSAT RPAREN
                    { CommandCheckSat($1) }
    | cur_position LPAREN GETASSERT RPAREN
                    { CommandGetAssert($1) }
    | cur_position LPAREN GETPROOF RPAREN
                    { CommandGetProof($1) }
    | cur_position LPAREN GETUNSATCORE RPAREN
                    { CommandGetUnsatCore($1) }
    | cur_position LPAREN GETVALUE LPAREN commandgetvalue_command_term24 RPAREN RPAREN
                    { CommandGetValue($1, $5) }
    | cur_position LPAREN GETASSIGN RPAREN
                    { CommandGetAssign($1) }
    | cur_position LPAREN GETOPTION KEYWORD RPAREN
                    { CommandGetOption($1, $4) }
    | cur_position LPAREN GETINFO infoflag RPAREN
                    { CommandGetInfo($1, $4) }
    | cur_position LPAREN EXIT RPAREN
                    { CommandExit($1) }

commands:
    | commands_commands_command30
                    { Commands(pd_commands_commands_command30 $1, $1) }

identifier:
| symbol { IdSymbol(pd_symbol $1, $1) }

identifier:
| cur_position LPAREN UNDERSCORE symbol idunderscoresymnum_identifier_numeral33 RPAREN { IdUnderscoreSymNum($1, $4, $5) }

infoflag:
| cur_position KEYWORD { InfoFlagKeyword($1, $2) }

qualidentifier:
| identifier { QualIdentifierId(pd_identifier $1, $1) }

qualidentifier:
| cur_position LPAREN AS identifier sort RPAREN { QualIdentifierAs($1, $4, $5) }

sexpr:
| specconstant { SexprSpecConst(pd_specconstant $1, $1) }

sexpr:
| symbol { SexprSymbol(pd_symbol $1, $1) }

sexpr:
| cur_position KEYWORD { SexprKeyword($1, $2) }

sexpr:
| cur_position LPAREN sexprinparen_sexpr_sexpr41 RPAREN { SexprInParen($1, $3) }

sort:
| identifier { SortIdentifier(pd_identifier $1, $1) }

sort:
| cur_position LPAREN identifier sortidsortmulti_sort_sort44 RPAREN { SortIdSortMulti($1, $3, $4) }

sortedvar:
| cur_position LPAREN symbol sort RPAREN { SortedVarSymSort($1, $3, $4) }

specconstant:
| cur_position DECIMAL { SpecConstsDec($1, $2) }

specconstant:
| cur_position NUMERAL { SpecConstNum($1, $2) }

specconstant:
| cur_position STRINGLIT { SpecConstString($1, $2) }

specconstant:
| cur_position HEXADECIMAL { SpecConstsHex($1, $2) }

specconstant:
| cur_position BINARY { SpecConstsBinary($1, $2) }

symbol:
| cur_position SYMBOL { Symbol($1, $2) }

symbol:
| cur_position ASCIIWOR { SymbolWithOr($1, $2) }

term:
| specconstant { TermSpecConst(pd_specconstant $1, $1) }

term:
| qualidentifier { TermQualIdentifier(pd_qualidentifier $1, $1) }

term:
| cur_position LPAREN qualidentifier termqualidterm_term_term56 RPAREN { TermQualIdTerm($1, $3, $4) }

term:
| cur_position LPAREN LET LPAREN termletterm_term_varbinding58 RPAREN term RPAREN { TermLetTerm($1, $5, $7) }

term:
| cur_position LPAREN FORALL LPAREN termforallterm_term_sortedvar60 RPAREN term RPAREN { TermForAllTerm($1, $5, $7) }

term:
| cur_position LPAREN EXISTS LPAREN termexiststerm_term_sortedvar62 RPAREN term RPAREN { TermExistsTerm($1, $5, $7) }

term:
| cur_position LPAREN EXCLIMATIONPT term termexclimationpt_term_attribute64 RPAREN { TermExclimationPt($1, $4, $5) }

varbinding:
| cur_position LPAREN symbol term RPAREN { VarBindingSymTerm($1, $3, $4) }

termexclimationpt_term_attribute64:
| attribute { (pd_attribute $1, ($1)::[]) }

termexclimationpt_term_attribute64:
| attribute termexclimationpt_term_attribute64 { let (p, ( l1 )) = $2 in (pd_attribute $1, ($1)::(l1)) }

termexiststerm_term_sortedvar62:
| sortedvar { (pd_sortedvar $1, ($1)::[]) }

termexiststerm_term_sortedvar62:
| sortedvar termexiststerm_term_sortedvar62 { let (p, ( l1 )) = $2 in (pd_sortedvar $1, ($1)::(l1)) }

termforallterm_term_sortedvar60:
| sortedvar { (pd_sortedvar $1, ($1)::[]) }

termforallterm_term_sortedvar60:
| sortedvar termforallterm_term_sortedvar60 { let (p, ( l1 )) = $2 in (pd_sortedvar $1, ($1)::(l1)) }

termletterm_term_varbinding58:
| varbinding { (pd_varbinding $1, ($1)::[]) }

termletterm_term_varbinding58:
| varbinding termletterm_term_varbinding58 { let (p, ( l1 )) = $2 in (pd_varbinding $1, ($1)::(l1)) }

termqualidterm_term_term56:
| term { (pd_term $1, ($1)::[]) }

termqualidterm_term_term56:
| term termqualidterm_term_term56 { let (p, ( l1 )) = $2 in (pd_term $1, ($1)::(l1)) }

sortidsortmulti_sort_sort44:
| sort { (pd_sort $1, ($1)::[]) }

sortidsortmulti_sort_sort44:
| sort sortidsortmulti_sort_sort44 { let (p, ( l1 )) = $2 in (pd_sort $1, ($1)::(l1)) }

sexprinparen_sexpr_sexpr41:
| cur_position { ($1, []) }

sexprinparen_sexpr_sexpr41:
| sexpr sexprinparen_sexpr_sexpr41 { let (p, ( l1 )) = $2 in (pd_sexpr $1, ($1)::(l1)) }

idunderscoresymnum_identifier_numeral33:
| cur_position NUMERAL { ($1, ($2)::[]) }

idunderscoresymnum_identifier_numeral33:
| cur_position NUMERAL idunderscoresymnum_identifier_numeral33 { let (p, ( l1 )) = $3 in ($1, ($2)::(l1)) }

commands_commands_command30:
| cur_position { ($1, []) }

commands_commands_command30:
| command commands_commands_command30 { let (p, ( l1 )) = $2 in (pd_command $1, ($1)::(l1)) }

commandgetvalue_command_term24:
| term { (pd_term $1, ($1)::[]) }

commandgetvalue_command_term24:
| term commandgetvalue_command_term24 { let (p, ( l1 )) = $2 in (pd_term $1, ($1)::(l1)) }

commanddefinefun_command_sortedvar15:
| cur_position { ($1, []) }

commanddefinefun_command_sortedvar15:
| sortedvar commanddefinefun_command_sortedvar15 { let (p, ( l1 )) = $2 in (pd_sortedvar $1, ($1)::(l1)) }

commanddeclarefun_command_sort13:
| cur_position { ($1, []) }

commanddeclarefun_command_sort13:
| sort commanddeclarefun_command_sort13 { let (p, ( l1 )) = $2 in (pd_sort $1, ($1)::(l1)) }

commanddefinesort_command_symbol11:
| cur_position { ($1, []) }

commanddefinesort_command_symbol11:
| symbol commanddefinesort_command_symbol11 { let (p, ( l1 )) = $2 in (pd_symbol $1, ($1)::(l1)) }

attributevalsexpr_attributevalue_sexpr5:
| cur_position { ($1, []) }

attributevalsexpr_attributevalue_sexpr5:
| sexpr attributevalsexpr_attributevalue_sexpr5 { let (p, ( l1 )) = $2 in (pd_sexpr $1, ($1)::(l1)) }
