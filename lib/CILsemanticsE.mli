open CILsyntax
open Utils

type semantics =
  {
    nodes: qn list;
    allows: (qn * SS.t *qn) list;
    ta: (qn * attributeexp) list
  }

val get_semantics : statement list -> semantics
