open CILsyntax

type csi

type ns = dn list
type sigma = ns list


type tval = qn
type aval = qn
type mval = qn * ((parametertype * string) list) * (statement list) * csi * sigma
type bval = qn * (statement list)

type rho

val union : rho -> rho -> rho

val enterblock : qn -> dn -> qn

val print : rho -> unit

val sem_initialrhoR : statement list -> ns -> rho

val eval_tora_bar : qn -> rho -> sigma -> qn option
val eval_t_bar : qn -> rho -> sigma -> tval option
val eval_a_bar : qn -> rho -> sigma -> aval option
val eval_m_bar : qn -> rho -> sigma -> mval option
val eval_b_bar : qn -> rho -> sigma -> bval option
val eval_pars_bar : qn list -> ((parametertype * dn) list) -> rho -> sigma -> qn list option

val rho_plus_rho : ns -> ns -> rho -> rho -> rho
(* rhoplus ns ns' rho rho' returns rho[ns + rho'(ns')] *)

val rho_plus_rho_m : ns -> ns -> rho -> rho -> rho
(* like rho_plus_rho, but only copy the macro definitions *)

val rhoinherit : qn -> qn -> rho -> rho

val cdm : qn -> rho -> sigma -> csi

val rho_plus_csi : rho -> qn -> csi -> rho
val rho_minus_csi : rho -> ns -> csi -> rho
val rho_intersec_csi : rho -> ns -> csi -> rho

val fake_fr_rho : rho -> ns -> csi -> rho
(* fake_fr_rho rho mgn ns csi returns rho[mgn |-> {(dn, rho(ns)(dn)) | dn in csi}] *)

val fresh : string
