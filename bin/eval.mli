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
val subst_in_gamma : from:string -> into:term -> what:gamma -> gamma
val subst_iso_in_gamma : from:string -> into:iso -> what:gamma -> gamma
val subst_gamma_in_gamma : from:string -> into:gamma -> what:gamma -> gamma
val subst_gamma_in_term : from:string -> into:gamma -> what:term -> term
val eval : term -> term myresult
val eval_gamma : gamma -> gamma
val eval_iso : iso -> iso
