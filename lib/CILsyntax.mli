type parametertype = 
    PARTYPE 
  | PARCLASS 
  | PARTYPEALIAS
  | PARCLASSPERMISSION
  (* classpermission(named or anonymous), 
   block, name (a string), *)
  | PARCLASSMAP
  | PARIGNORE

type dn = string
type qn = dn list
type ns = dn list

type attributeexp = 
    A_NAME of string list
  | A_OR of attributeexp * attributeexp
  | A_AND of attributeexp * attributeexp
  | A_XOR of attributeexp * attributeexp
  | A_NOT of attributeexp

type classpermissionsetcon =
  | Permissions of string list
  | Expression of attributeexp

type classpermission =
  | Name of string list
  | Anonym of qn * classpermissionsetcon

type statement = 
    CILTYPE of string
  | CILTYPEALIAS of string
  | CILTYPEALIASACTUAL of string * qn
  | CILATTRIBUTE of string
  | CILATTRIBUTESET of qn * attributeexp
  | CILBLOCK of string * (statement list)
  | CILBLOCKINHERIT of qn 
  | CILBLOCKABSTRACT
  | CILCALL of qn * (qn list) 
  | CILMACRO of string * ((parametertype * string) list) * (statement list)
  | CILALLOW of qn * qn * classpermission
  | CILIN of qn * (statement list)
  | CILCOMMON of string * string list
  | CILCLASSCOMMON of qn * qn
  | CILCLASS of string * string list
  | CILCLASSPERMISSION of string
  | CILCLASSPERMISSIONSET of qn * qn * classpermissionsetcon
  | CILCLASSMAP of string * string list
  | CILCLASSMAPPING of qn * qn * classpermission


  
val removeIN : statement list -> statement list

val qn_tostring : qn -> string
val print : statement list -> unit
val conf_to_string : statement list -> string
