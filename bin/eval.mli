open Types
open Util

val matches : value -> value -> bool
val invert : iso -> iso
val subst : from:string -> into:term -> what:term -> term
val subst_iso : from:string -> into:iso -> what:iso -> iso
val subst_iso_in_expr : from:string -> into:iso -> what:expr -> expr
val subst_iso_in_term : from:string -> into:iso -> what:term -> term
val value_of_term : term -> value myresult
val match_pair : (value * expr) list -> value -> (value * expr) option
val unify_value : value -> value -> (string * value) list myresult
val subst_in_idem : from:string -> into:term -> what:idem -> idem
val subst_iso_in_idem : from:string -> into:iso -> what:idem -> idem
val subst_gamma_in_idem : from:string -> into:idem -> what:idem -> idem
val subst_gamma_in_term : from:string -> into:idem -> what:term -> term
val eval : term -> term myresult
val eval_idem : idem -> idem
val eval_iso : iso -> iso
