%{
open CILsyntax

let read_path str =
    if str = "*" then ["any-node"] else
    if (String.get str 0) = '.' 
        then String.split_on_char '.' ("#" ^ str)
    else
        String.split_on_char '.' str
%}
%token <string> NAME
%token TYPE BLOCK IN COMMON CLASSCOMMON CLASS CLASSPERMISSION CLASSPERMISSIONSET CLASSMAP CLASSMAPPING 
%token BLOCKABSTRACT IN TYPEALIAS TYPEALIASACTUAL BLOCKINHERIT MACRO CALL
%token ALLOW SELF ATTRIBUTE ATTRIBUTESET ALL ANOT AND OR XOR LPAREN RPAREN STRING
%token EOF 
%start main             /* the entry point */
%type <CILsyntax.statement list> main
/*%type <string list> names  XXX attenzione, visto che ignoriamo gli spazi (a.b.c d.e.f) potrebbe essere letto a.b.c.d.e.f */
%%
main:
    stmnts EOF  { $1 }
stmnts:
    stmnt         { (match $1 with | None -> [] | Some e -> [e]) }
  | stmnt stmnts  { (match $1 with | None -> $2 | Some e -> e :: $2) }
;
stmnt:
  LPAREN stmnt RPAREN                { $2 }
;
stmnt:
    TYPE name                                                              { Some (CILTYPE $2) }
  | TYPEALIAS name                                                         { Some (CILTYPEALIAS $2) }
  | TYPEALIASACTUAL name name                                              { Some (CILTYPEALIASACTUAL($2, read_path($3))) }
  | COMMON name LPAREN names RPAREN                                        { Some (CILCOMMON($2, $4)) }
  | COMMON name LPAREN RPAREN                                              { Some (CILCOMMON($2, [])) }
  | CLASSCOMMON name name                                                  { Some (CILCLASSCOMMON(read_path($2), read_path($3))) }
  | CLASS name LPAREN names RPAREN                                         { Some (CILCLASS($2, $4)) }
  | CLASS name LPAREN RPAREN                                               { Some (CILCLASS($2, [])) }
  | CLASSPERMISSION name                                                   { Some (CILCLASSPERMISSION $2) }
  | CLASSPERMISSIONSET name LPAREN name LPAREN names RPAREN RPAREN         { Some (CILCLASSPERMISSIONSET(read_path($2), read_path($4), (Permissions $6))) }
  | CLASSPERMISSIONSET name LPAREN name attributeexp RPAREN                { Some (CILCLASSPERMISSIONSET(read_path($2), read_path($4), (Expression $5))) }
  | CLASSMAP name LPAREN names RPAREN                                      { Some (CILCLASSMAP($2, $4)) }
  | CLASSMAPPING name name LPAREN name LPAREN names RPAREN RPAREN          { Some (CILCLASSMAPPING(read_path($2), read_path($3), (Anonym(read_path($5), (Permissions $7))))) }
  | CLASSMAPPING name name LPAREN name attributeexp RPAREN                 { Some (CILCLASSMAPPING(read_path($2), read_path($3), (Anonym(read_path($5), (Expression $6))))) }
  | CLASSMAPPING name name name                                            { Some (CILCLASSMAPPING(read_path($2), read_path($3), (Name (read_path($4))))) }
  | ATTRIBUTE name                                                         { Some (CILATTRIBUTE $2) }
  | ATTRIBUTESET name attributeexp                                         { Some (CILATTRIBUTESET(read_path($2), $3)) }
  | BLOCK name stmnts                                                      { Some (CILBLOCK($2, $3)) }
  | BLOCK name                                                             { Some (CILBLOCK($2, [])) }
  | BLOCKINHERIT name                                                      { Some (CILBLOCKINHERIT(read_path($2))) }
  | BLOCKABSTRACT name                                                     { Some (CILBLOCKABSTRACT) }
  | IN NAME stmnts                                                         { Some (CILIN(read_path($2), $3)) }
  | MACRO name LPAREN formparams RPAREN stmnts                             { Some (CILMACRO($2, $4, $6)) }
  | MACRO name LPAREN RPAREN stmnts                                        { Some (CILMACRO($2, [], $5)) }
  | CALL name LPAREN names RPAREN                                          { Some (CILCALL(read_path($2), (List.map (fun str -> read_path str) $4))) }
  | CALL name                                                              { Some (CILCALL(read_path($2), [])) }
  | ALLOW name name LPAREN name LPAREN names RPAREN RPAREN                 { Some (CILALLOW(read_path($2), read_path($3), Anonym(read_path($5), (Permissions $7)))) }
  | ALLOW name name LPAREN name attributeexp RPAREN                        { Some (CILALLOW(read_path($2), read_path($3), Anonym(read_path($5), (Expression $6)))) }
  | ALLOW name name name                                                   { Some (CILALLOW(read_path($2), read_path($3), Name(read_path($4)))) }
  | ALLOW name SELF LPAREN name LPAREN names RPAREN RPAREN                 { Some (CILALLOW(read_path($2), read_path($2), Anonym(read_path($5), (Permissions $7)))) }
  | ALLOW name SELF LPAREN name attributeexp RPAREN                        { Some (CILALLOW(read_path($2), read_path($2), Anonym(read_path($5), (Expression $6)))) }
  | ALLOW name SELF name                                                   { Some (CILALLOW(read_path($2), read_path($2), Name(read_path($4)))) }
  | NAME                                                                   { None }
  | NAME everys                                                            { None }
;
attributeexp:
    LPAREN ALL RPAREN                            { A_NAME ["all"] }
  | LPAREN NAME RPAREN                           { A_NAME (read_path($2)) }
  | LPAREN NAME names RPAREN                     { (List.fold_right
                                                      (fun n e -> A_OR(A_NAME (read_path n), e))
                                                      $3
                                                      (A_NAME (read_path($2)))) }
  | LPAREN ANOT attributeexp RPAREN              { A_NOT $3 }
  | LPAREN AND attributeexp attributeexp RPAREN  { A_AND($3, $4) }
  | LPAREN OR attributeexp attributeexp RPAREN   { A_OR($3, $4) }
  | LPAREN XOR attributeexp attributeexp RPAREN  { A_XOR($3, $4) }
  | NAME                                         { A_NAME (read_path($1)) }
;
everys:
    IN                    { } 
  | COMMON                { } 
  | CLASSCOMMON           { } 
  | CLASS                 { }
  | CLASSPERMISSION       { }
  | CLASSPERMISSIONSET    { }
  | CLASSMAP              { }
  | CLASSMAPPING          { }
  | BLOCKABSTRACT         { }
  | BLOCK                 { }
  | TYPE                  { }
  | TYPEALIAS             { }
  | TYPEALIASACTUAL       { }
  | BLOCKINHERIT          { }
  | MACRO                 { }
  | CALL                  { }
  | ALLOW                 { }
  | SELF                  { }
  | ATTRIBUTE             { }
  | ATTRIBUTESET          { }
  | ALL                   { }
  | ANOT                  { }
  | AND                   { }
  | OR                    { }
  | XOR                   { }
  | NAME                  { }
  | LPAREN RPAREN         { }
  | everys everys         { }
  | LPAREN everys RPAREN  { }
;
name:
    IN                    { "in" } 
  | COMMON                { "common" } 
  | CLASSCOMMON           { "classcommon" } 
  | CLASS                 { "class" }
  | CLASSPERMISSION       { "classpermission" }
  | CLASSPERMISSIONSET    { "classpermissionset" }
  | CLASSMAP              { "classmap" }
  | CLASSMAPPING          { "classmapping" }
  | BLOCK                 { "block" }
  | BLOCKABSTRACT         { "blockabstract" }
  | TYPE                  { "type" }
  | TYPEALIAS             { "typealias" }
  | TYPEALIASACTUAL       { "typealiasactual" }
  | BLOCKINHERIT          { "blockinherit" }
  | MACRO                 { "macro" }
  | CALL                  { "call" }
  | ALLOW                 { "allow" }
  | ATTRIBUTE             { "attribute" }
  | ATTRIBUTESET          { "attributeset" }
  | ALL                   { "all" }
  | NAME                  { $1 }
;
names:
    name        { [$1] }
  | name names  { $1 :: $2 }
;
formparams:
    LPAREN TYPE NAME RPAREN                        { [(PARTYPE, $3)] }
  | LPAREN CLASS NAME RPAREN                       { [(PARCLASS, $3)] }
  | LPAREN TYPEALIAS NAME RPAREN                   { [(PARTYPEALIAS, $3)] }
  | LPAREN CLASSPERMISSION NAME RPAREN             { [(PARCLASSPERMISSION, $3)] }
  | LPAREN CLASSMAP NAME RPAREN                    { [(PARCLASSMAP, $3)] }
  | LPAREN NAME NAME RPAREN                        { [(PARIGNORE, $3)] }
  | LPAREN TYPE NAME RPAREN formparams             { (PARTYPE, $3) :: $5 }
  | LPAREN CLASS NAME RPAREN formparams            { (PARCLASS, $3) :: $5 }
  | LPAREN TYPEALIAS NAME RPAREN formparams        { (PARTYPEALIAS, $3) :: $5  }
  | LPAREN CLASSPERMISSION NAME RPAREN formparams  { (PARCLASSPERMISSION, $3) :: $5  }
  | LPAREN CLASSMAP NAME RPAREN formparams         { (PARCLASSMAP, $3) :: $5  }
  | LPAREN NAME NAME RPAREN formparams             { (PARIGNORE, $3) :: $5 }
%%