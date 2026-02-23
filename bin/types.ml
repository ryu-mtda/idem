open Util

type base_type =
  | Unit
  | Product of base_type list
  | Named of string
  | Var of string
  | Ctor of base_type list * string
  | FunType of { a : base_type; b : base_type }

type iso_type =
  | BiArrow of { a : base_type; b : base_type }
  | Arrow of { t_1 : iso_type; t_2 : iso_type }
  | Var of string

type value =
  | Unit
  | Var of string
  | Ctor of string
  | Cted of { c : string; v : value }
  | Tuple of value list

type expr =
  | Value of value
  | Let of { p_1 : value; omega : iso; p_2 : value; e : expr }
  | LetVal of { p : value; v : value; e : expr }

and iso =
  | Pairs of (value * expr) list
  | Fix of { phi : string; omega : iso }
  | Lambda of { psi : string; omega : iso }
  | Var of string
  | App of { omega_1 : iso; omega_2 : iso }
  | Invert of iso

type gamma =
  | Direct of { params : value; body : term }
  | Composed of { omega : iso; gamma : gamma }
  | Var of string

and term =
  | Unit
  | Var of string
  | Ctor of string
  | Cted of { c : string; t : term }
  | Tuple of term list
  | App of { omega : iso; t : term }
  | Let of { p : value; t_1 : term; t_2 : term }
  | LetIso of { phi : string; omega : iso; t : term }
  | AppGamma of { gamma : gamma; t : term }
  | LetIdem of { phi : string; gamma : gamma; t : term }
  | Fun of { x : string; body : term }
  | AppFun of { f : term; t : term }

type expr_intermediate =
  | IValue of term
  | ILet of { p_1 : value; p_2 : term; e : expr_intermediate }

type variant = Value of string | Iso of { c : string; a : base_type }
type typedef = { vars : string list; t : string; vs : variant list }
type program = { ts : typedef list; t : term }
type generator = { mutable i : int }

let char_ctor_map =
  let chars =
    "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz \
     !\"#$%&'()*+,-./:;<=>?@[\\]^_`{|}~"
  in
  let ctors =
    [
      "Char0";
      "Char1";
      "Char2";
      "Char3";
      "Char4";
      "Char5";
      "Char6";
      "Char7";
      "Char8";
      "Char9";
      "CharA";
      "CharB";
      "CharC";
      "CharD";
      "CharE";
      "CharF";
      "CharG";
      "CharH";
      "CharI";
      "CharJ";
      "CharK";
      "CharL";
      "CharM";
      "CharN";
      "CharO";
      "CharP";
      "CharQ";
      "CharR";
      "CharS";
      "CharT";
      "CharU";
      "CharV";
      "CharW";
      "CharX";
      "CharY";
      "CharZ";
      "CharLowerA";
      "CharLowerB";
      "CharLowerC";
      "CharLowerD";
      "CharLowerE";
      "CharLowerF";
      "CharLowerG";
      "CharLowerH";
      "CharLowerI";
      "CharLowerJ";
      "CharLowerK";
      "CharLowerL";
      "CharLowerM";
      "CharLowerN";
      "CharLowerO";
      "CharLowerP";
      "CharLowerQ";
      "CharLowerR";
      "CharLowerS";
      "CharLowerT";
      "CharLowerU";
      "CharLowerV";
      "CharLowerW";
      "CharLowerX";
      "CharLowerY";
      "CharLowerZ";
      "CharSpace";
      "CharExclamation";
      "CharQuote";
      "CharHash";
      "CharDollar";
      "CharPercent";
      "CharAmpersand";
      "CharApostrophe";
      "CharParenLeft";
      "CharParenRight";
      "CharAsterisk";
      "CharPlus";
      "CharComma";
      "CharMinus";
      "CharDot";
      "CharSlash";
      "CharColon";
      "CharSemicolon";
      "CharLessThan";
      "CharEqual";
      "CharGreaterThan";
      "CharQuestion";
      "CharAt";
      "CharBracketLeft";
      "CharBackslash";
      "CharBracketRight";
      "CharCaret";
      "CharUnderscore";
      "CharBackquote";
      "CharBraceLeft";
      "CharBar";
      "CharBraceRight";
      "CharTilde";
    ]
  in
  let explode_string s = List.init (String.length s) (fun n -> String.get s n |> String.make 1) in
  List.fold_left2 (fun m c ctor -> StrMap.add c ctor m) StrMap.empty (explode_string chars) ctors

let rec term_of_value : value -> term = function
  | Unit -> Unit
  | Var x -> Var x
  | Ctor x -> Ctor x
  | Cted { c; v } -> Cted { c; t = term_of_value v }
  | Tuple l -> Tuple (List.map term_of_value l)

let rec term_of_expr : expr -> term = function
  | Value v -> term_of_value v
  | Let { p_1; omega; p_2; e } ->
      Let
        {
          p = p_1;
          t_1 = App { omega; t = term_of_value p_2 };
          t_2 = term_of_expr e;
        }
  | LetVal { p; v; e } -> Let { p; t_1 = term_of_value v; t_2 = term_of_expr e }

let rec value_of_expr : expr -> value = function
  | Value v -> v
  | Let { e; _ } -> value_of_expr e
  | LetVal { e; _ } -> value_of_expr e

let rec contains_value (what : string) : value -> bool = function
  | Unit -> false
  | Var x -> x = what
  | Ctor _ -> false
  | Cted { v; _ } -> contains_value what v
  | Tuple l -> List.exists (contains_value what) l

let contains_pairs (what : string) (pairs : (value * expr) list) : bool =
  List.exists (fun (v, _) -> contains_value what v) pairs

let rec lambdas_of_params : string list -> iso -> iso = function
  | [] -> fun omega -> omega
  | psi :: tl -> fun omega -> Lambda { psi; omega = lambdas_of_params tl omega }

let rec funs_of_params : string list -> term -> term = function
  | [] -> fun body -> body
  | x :: tl -> fun body -> Fun { x; body = funs_of_params tl body }

let rec is_list_value : value -> bool = function
  | Cted { c = "Cons"; v = Tuple [ _; v ] } -> is_list_value v
  | Ctor "Nil" -> true
  | _ -> false

let rec is_list_term : term -> bool = function
  | Cted { c = "Cons"; t = Tuple [ _; t ] } -> is_list_term t
  | Ctor "Nil" -> true
  | _ -> false

let rec is_int_value : value -> bool = function
  | Cted { c = "S"; v } -> is_int_value v
  | Ctor "Z" -> true
  | _ -> false

let rec is_int_term : term -> bool = function
  | Cted { c = "S"; t } -> is_int_term t
  | Ctor "Z" -> true
  | _ -> false

let is_char_value : value -> bool = function
  | Ctor ctor -> List.exists (fun c -> c = ctor) (StrMap.bindings char_ctor_map |> List.map snd)
  | _ -> false

let is_char_term : term -> bool = function
  | Ctor ctor -> List.exists (fun c -> c = ctor) (StrMap.bindings char_ctor_map |> List.map snd)
  | _ -> false

let is_string_value (v : value) : bool =
  let rec aux: value -> bool = function
    | Ctor "Nil" -> true
    | Cted { c = "Cons"; v = Tuple [ head; tail ] } ->
        is_char_value head && aux tail
    | _ -> false
  in
  aux v

let is_string_term (t : term) : bool =
  let rec aux: term -> bool = function
    | Ctor "Nil" -> true
    | Cted { c = "Cons"; t = Tuple [ head; tail ] } ->
        is_char_term head && aux tail
    | _ -> false
  in
  aux t

let rec show_base_type : base_type -> string = function
  | Unit -> "unit"
  | Product l ->
      let lmao = function
        | Product l -> "(" ^ show_base_type (Product l) ^ ")"
        | FunType _ as f -> "(" ^ show_base_type f ^ ")"
        | otherwise -> show_base_type otherwise
      in
      show_listlike lmao ~left:"" ~delim:" * " ~right:"" l
  | Named x | Var x -> x
  | Ctor ([], _) -> "unreachable (type constructor with Z arity)"
  | Ctor ([ (Product _ as x) ], a) -> "(" ^ show_base_type x ^ ") " ^ a
  | Ctor ([ x ], a) -> show_base_type x ^ " " ^ a
  | Ctor (l, a) -> show_tuple show_base_type l ^ " " ^ a
  | FunType { a; b } ->
      let lhs = match a with
        | Product _ | FunType _ -> "(" ^ show_base_type a ^ ")"
        | _ -> show_base_type a
      in
      lhs ^ " -> " ^ show_base_type b

let rec show_iso_type : iso_type -> string = function
  | BiArrow { a; b } -> show_base_type a ^ " <-> " ^ show_base_type b
  | Arrow { t_1 = Var _ as t_1; t_2 = BiArrow _ as t_2 } ->
      show_iso_type t_1 ^ " -> (" ^ show_iso_type t_2 ^ ")"
  | Arrow { t_1 = Var _ as t_1; t_2 } ->
      show_iso_type t_1 ^ " -> " ^ show_iso_type t_2
  | Arrow { t_1; t_2 = BiArrow _ as t_2 } ->
      "(" ^ show_iso_type t_1 ^ ") -> (" ^ show_iso_type t_2 ^ ")"
  | Arrow { t_1; t_2 } -> "(" ^ show_iso_type t_1 ^ ") -> " ^ show_iso_type t_2
  | Var x -> x

let rec show_value : value -> string = function
  | Unit -> "()"
  | Ctor "Z" -> "0"
  | Ctor "Nil" -> "[]"
  | what when is_char_value what -> begin
      let rec lmao : value -> char = function
        | Ctor ctor ->
            let s = StrMap.bindings char_ctor_map
              |> List.find (fun (_, c) -> c = ctor)
              |> fst in
            String.get s 0
        | Cted { v; _ } -> lmao v
        | _ -> failwith "impossible: non-character value that satisfies is_char_value"
      in
      String.make 1 (lmao what)
    end
  | Ctor x | Var x -> x
  | what when is_int_value what -> begin
      let rec lmao acc : value -> int = function
        | Cted { v; _ } -> lmao (acc + 1) v
        | _ -> acc
      in
      lmao 0 what |> string_of_int
    end
  | Cted { c = "Cons"; v = Tuple [ v_1; v_2 ] } as v ->
      if is_string_value v then
        let rec lmao : value -> string = function
          | Cted { c = "Cons"; v = Tuple [ v_1; v_2 ] } ->
            show_value v_1 ^ lmao v_2
          | Ctor "Nil" -> ""
          | otherwise -> show_value otherwise
        in
        "\"" ^ lmao v ^ "\""
      else if is_list_value v then
        let rec lmao : value -> string = function
          | Cted { c = "Cons"; v = Tuple [ v_1; v_2 ] } ->
              "; " ^ show_value v_1 ^ lmao v_2
          | Ctor "Nil" -> ""
          | otherwise -> "; " ^ show_value otherwise
        in
        "[" ^ show_value v_1 ^ lmao v_2 ^ "]"
      else
        let rec lmao : value -> string = function
          | Cted { c = "Cons"; v = Tuple [ v_1; v_2 ] } ->
              " :: " ^ show_value v_1 ^ lmao v_2
          | otherwise -> " :: " ^ show_value otherwise
        in
        show_value v_1 ^ lmao v_2
  | Tuple l -> show_tuple show_value l
  | Cted { c; v = Cted _ as v } when is_int_value v || is_list_value v ->
      c ^ " " ^ show_value v
  | Cted { c; v = Cted _ as v } -> c ^ " (" ^ show_value v ^ ")"
  | Cted { c; v } -> c ^ " " ^ show_value v

let rec show_expr : expr -> string = function
  | Value v -> show_value v
  | Let
      {
        p_1;
        omega = (Pairs _ | Fix _ | Lambda _) as omega;
        p_2 = Cted _ as p_2;
        e;
      }
    when is_int_value p_2 || is_list_value p_2 ->
      "let " ^ show_value p_1 ^ " = {" ^ show_iso omega ^ "} " ^ show_value p_2
      ^ " in\n  " ^ show_expr e
  | Let
      {
        p_1;
        omega = (Pairs _ | Fix _ | Lambda _) as omega;
        p_2 = Cted _ as p_2;
        e;
      } ->
      "let " ^ show_value p_1 ^ " = {" ^ show_iso omega ^ "} (" ^ show_value p_2
      ^ ") in\n  " ^ show_expr e
  | Let { p_1; omega = (Pairs _ | Fix _ | Lambda _) as omega; p_2; e } ->
      "let " ^ show_value p_1 ^ " = {" ^ show_iso omega ^ "} " ^ show_value p_2
      ^ " in\n  " ^ show_expr e
  | Let { p_1; omega; p_2 = Cted _ as p_2; e }
    when is_int_value p_2 || is_list_value p_2 ->
      "let " ^ show_value p_1 ^ " = " ^ show_iso omega ^ " " ^ show_value p_2
      ^ " in\n  " ^ show_expr e
  | Let { p_1; omega; p_2 = Cted _ as p_2; e } ->
      "let " ^ show_value p_1 ^ " = " ^ show_iso omega ^ " (" ^ show_value p_2
      ^ ") in\n  " ^ show_expr e
  | Let { p_1; omega; p_2; e } ->
      "let " ^ show_value p_1 ^ " = " ^ show_iso omega ^ " " ^ show_value p_2
      ^ " in\n  " ^ show_expr e
  | LetVal { p; v; e } ->
      "let " ^ show_value p ^ " = " ^ show_value v ^ " in\n  " ^ show_expr e

and show_pairs (pairs : (value * expr) list) : string =
  List.fold_left
    (fun acc (v, e) -> acc ^ "\n  | " ^ show_value v ^ " <-> " ^ show_expr e)
    "case" pairs

and show_iso : iso -> string = function
  | Pairs p -> show_pairs p
  | Fix { phi; omega; _ } -> "fix " ^ phi ^ ". " ^ show_iso omega
  | Lambda { psi; omega; _ } -> "fun " ^ psi ^ " -> " ^ show_iso omega
  | Var omega -> omega
  | App { omega_1; omega_2 = Var _ as omega_2 } ->
      show_iso omega_1 ^ " " ^ show_iso omega_2
  | App { omega_1; omega_2 } -> show_iso omega_1 ^ " {" ^ show_iso omega_2 ^ "}"
  | Invert (Var _ as omega) -> "inv " ^ show_iso omega
  | Invert omega -> "inv {" ^ show_iso omega ^ "}"

let show_pairs_lhs (v : value) (pairs : (value * expr) list) : string =
  let init = "match " ^ show_value v ^ " with" in
  List.fold_left
    (fun acc (v, _) -> acc ^ "\n  | " ^ show_value v ^ " <-> ...")
    init pairs

let rec show_gamma : gamma -> string = function
  | Direct { params; body } ->
      show_value params ^ " -> " ^ show_term body
  | Composed { omega; gamma } ->
      show_iso omega ^ " with " ^ show_gamma gamma
  | Var x -> x

and show_term : term -> string = function
  | Unit -> "()"
  | Ctor "Z" -> "0"
  | Ctor "Nil" -> "[]"
  | what when is_char_term what -> begin
      let rec lmao : term -> char = function
        | Ctor ctor ->
            let s = StrMap.bindings char_ctor_map
              |> List.find (fun (_, c) -> c = ctor)
              |> fst in
            String.get s 0
        | Cted { t; _ } -> lmao t
        | _ -> failwith "impossible: non-character term that satisfies is_char_term"
      in
      String.make 1 (lmao what)
    end
  | Var x | Ctor x -> x
  | Tuple l -> show_tuple show_term l
  | what when is_int_term what -> begin
      let rec lmao acc = function
        | Cted { t; _ } -> lmao (acc + 1) t
        | _ -> acc
      in
      lmao 0 what |> string_of_int
    end
  | Cted { c = "Cons"; t = Tuple [ t_1; t_2 ] } as t ->
      if is_string_term t then
        let rec lmao = function
          | Cted { c = "Cons"; t = Tuple [ t_1; t_2 ] } ->
            show_term t_1 ^ lmao t_2
          | Ctor "Nil" -> ""
          | otherwise -> show_term otherwise
        in
        "\"" ^ lmao t ^ "\""
       else if is_list_term t then
        let rec lmao = function
          | Cted { c = "Cons"; t = Tuple [ t_1; t_2 ] } ->
              "; " ^ show_term t_1 ^ lmao t_2
          | Ctor "Nil" -> ""
          | otherwise -> "; " ^ show_term otherwise
        in
        "[" ^ show_term t_1 ^ lmao t_2 ^ "]"
      else
        let rec lmao = function
          | Cted { c = "Cons"; t = Tuple [ t_1; t_2 ] } ->
              " :: " ^ show_term t_1 ^ lmao t_2
          | otherwise -> " :: " ^ show_term otherwise
        in
        show_term t_1 ^ lmao t_2
  | Cted { c; t } when is_int_term t || is_list_term t -> c ^ " " ^ show_term t
  | Cted { c; t = (Cted _ | App _ | Let _ | LetIso _ | AppGamma _ | LetIdem _ | Fun _ | AppFun _) as t } ->
      c ^ " (" ^ show_term t ^ ")"
  | Cted { c; t } -> c ^ " " ^ show_term t
  | App { omega = (Pairs _ | Fix _ | Lambda _) as omega; t }
    when is_int_term t || is_list_term t ->
      "{" ^ show_iso omega ^ "} " ^ show_term t
  | App
      {
        omega = (Pairs _ | Fix _ | Lambda _) as omega;
        t = (Cted _ | App _ | Let _ | LetIso _ | AppGamma _ | LetIdem _ | Fun _ | AppFun _) as t;
      } ->
      "{" ^ show_iso omega ^ "} (" ^ show_term t ^ ")"
  | App { omega = (Pairs _ | Fix _ | Lambda _) as omega; t } ->
      "{" ^ show_iso omega ^ "} " ^ show_term t
  | App { omega; t } when is_int_term t || is_list_term t ->
      show_iso omega ^ " " ^ show_term t
  | App { omega; t = (Cted _ | App _ | Let _ | LetIso _ | AppGamma _ | LetIdem _ | Fun _ | AppFun _) as t } ->
      show_iso omega ^ " (" ^ show_term t ^ ")"
  | App { omega; t } -> show_iso omega ^ " " ^ show_term t
  | Let { p; t_1; t_2 } ->
      "let " ^ show_value p ^ " = " ^ show_term t_1 ^ "\nin\n\n" ^ show_term t_2
  | LetIso { phi; omega; t } ->
      "let iso " ^ phi ^ " = " ^ show_iso omega ^ "\nin\n\n" ^ show_term t
  | AppGamma { gamma; t = (Cted _ | App _ | Let _ | LetIso _ | AppGamma _ | LetIdem _ | Fun _ | AppFun _) as t } ->
      "{" ^ show_gamma gamma ^ "} (" ^ show_term t ^ ")"
  | AppGamma { gamma; t } ->
      "{" ^ show_gamma gamma ^ "} " ^ show_term t
  | LetIdem { phi; gamma; t } ->
      "let idem " ^ phi ^ " = " ^ show_gamma gamma ^ "\nin\n\n" ^ show_term t
  | Fun { x; body } ->
      "fun " ^ x ^ " -> " ^ show_term body
  | AppFun { f; t } ->
      show_term f ^ " " ^ show_term t

let rec nat_of_int (n : int) : value =
  if n < 1 then Ctor "Z" else Cted { c = "S"; v = nat_of_int (n - 1) }

let char_to_char_ctor (c : char) : string =
  try StrMap.find (String.make 1 c) char_ctor_map
  with Not_found -> failwith ("unsupported character: " ^ String.make 1 c)

let char_literal_to_value (c : char) : value =
  Ctor (char_to_char_ctor c)

let string_literal_to_value : string -> value =
  let rec chars_to_list idx (s: string): value =
    if idx >= String.length s then Ctor "Nil"
    else
      let ctor = char_to_char_ctor s.[idx] in
      Cted { c = "Cons"; v = Tuple [Ctor ctor; chars_to_list (idx + 1) s] }
  in
  fun s -> chars_to_list 0 s

let rec build_storage (default : 'a) : value -> 'a option StrMap.t = function
  | Unit -> StrMap.empty
  | Var x -> StrMap.singleton x None
  | Ctor _ -> StrMap.empty
  | Cted { v; _ } -> build_storage default v
  | Tuple l ->
      List.map (build_storage default) l
      |> List.fold_left
           (StrMap.union (fun _ _ _ -> Some (Some default)))
           StrMap.empty

let collect_vars (v : value) : string list =
  let rec collect : value -> string list = function
    | Unit -> []
    | Var x -> [ x ]
    | Ctor _ -> []
    | Cted { v; _ } -> collect v
    | Tuple l -> List.map collect l |> List.flatten
  in
  collect v |> List.sort_uniq compare

let rec free_vars_term : term -> StrSet.t = function
  | Unit | Ctor _ -> StrSet.empty
  | Var x -> StrSet.singleton x
  | Cted { t; _ } -> free_vars_term t
  | Tuple ts ->
      List.fold_left (fun acc t -> StrSet.union acc (free_vars_term t)) StrSet.empty ts
  | App { t; _ } -> free_vars_term t
  | Let { p; t_1; t_2 } ->
      let bound = collect_vars p |> StrSet.of_list in
      StrSet.union (free_vars_term t_1) (StrSet.diff (free_vars_term t_2) bound)
  | LetIso { t; _ } -> free_vars_term t
  | AppGamma { gamma; t } ->
      StrSet.union (free_vars_in_gamma gamma) (free_vars_term t)
  | LetIdem { gamma; t; _ } ->
      StrSet.union (free_vars_in_gamma gamma) (free_vars_term t)
  | Fun { x; body } ->
      StrSet.remove x (free_vars_term body)
  | AppFun { f; t } ->
      StrSet.union (free_vars_term f) (free_vars_term t)

and free_vars_in_gamma : gamma -> StrSet.t = function
  | Direct { params; body } ->
      let bound = collect_vars params |> StrSet.of_list in
      StrSet.diff (free_vars_term body) bound
  | Composed { gamma; _ } -> free_vars_in_gamma gamma
  | Var _ -> StrSet.empty

let new_generator () : generator = { i = 0 }

let fresh (gen : generator) : int =
  let i = gen.i in
  gen.i <- i + 1;
  i

let rec expand (gen : generator) :
    term -> ((value * iso * value) list * value) myresult = function
  | Unit -> Ok ([], Unit)
  | Var x -> Ok ([], Var x)
  | Ctor x -> Ok ([], Ctor x)
  | Tuple t ->
      let++ l = List.map (expand gen) t |> bind_all in
      let l, t = List.fold_left_map (fun l (l', v) -> (l @ l', v)) [] l in
      let tuple : value = Tuple t in
      (l, tuple)
  | Cted { c; t } ->
      let++ l, v = expand gen t in
      let silly : value = Cted { c; v } in
      (l, silly)
  | App { omega; t } ->
      let++ l, v = expand gen t in
      let name : value = Var ("_" ^ chars_of_int (fresh gen)) in
      ((name, omega, v) :: l, name)
  | Let _ -> Error "nested let is not supported (yet)"
  | LetIso _ -> Error "nested iso binding is not supported (yet)"
  | AppGamma _ -> Error "nested idem application is not supported (yet)"
  | LetIdem _ -> Error "nested idem binding is not supported (yet)"
  | Fun _ -> Error "function in iso body is not supported"
  | AppFun _ -> Error "function application in iso body is not supported"

let rec expand_expr (gen : generator) : expr_intermediate -> expr myresult =
  function
  | IValue t ->
      let++ l, v = expand gen t in
      let init : expr = Value v in
      List.fold_left
        (fun e (p_1, omega, p_2) : expr -> Let { p_1; omega; p_2; e })
        init l
  | ILet { p_1; p_2; e } ->
      let** l, v = expand gen p_2 in
      let++ e = expand_expr gen e in
      let init = LetVal { p = p_1; v; e } in
      List.fold_left
        (fun e (p_1, omega, p_2) : expr -> Let { p_1; omega; p_2; e })
        init l

let rec rewrite_app_to_appgamma (phi : string) (t : term) : term =
  match t with
  | App { omega = Var x; t = arg } when x = phi ->
      AppGamma { gamma = Var x; t = rewrite_app_to_appgamma phi arg }
  | App { omega; t = arg } ->
      App { omega; t = rewrite_app_to_appgamma phi arg }
  | Let { p; t_1; t_2 } ->
      Let { p; t_1 = rewrite_app_to_appgamma phi t_1;
            t_2 = rewrite_app_to_appgamma phi t_2 }
  | LetIso { phi = phi2; omega; t } ->
      if phi2 = phi then LetIso { phi = phi2; omega; t }
      else LetIso { phi = phi2; omega; t = rewrite_app_to_appgamma phi t }
  | LetIdem { phi = phi2; gamma; t } ->
      let gamma' = rewrite_app_to_appgamma_in_gamma phi gamma in
      if phi2 = phi then LetIdem { phi = phi2; gamma = gamma'; t }
      else LetIdem { phi = phi2; gamma = gamma';
                     t = rewrite_app_to_appgamma phi t }
  | Tuple ts -> Tuple (List.map (rewrite_app_to_appgamma phi) ts)
  | Cted { c; t = arg } -> Cted { c; t = rewrite_app_to_appgamma phi arg }
  | AppGamma { gamma; t = arg } ->
      AppGamma { gamma = rewrite_app_to_appgamma_in_gamma phi gamma;
                 t = rewrite_app_to_appgamma phi arg }
  | Fun { x; body } ->
      Fun { x; body = rewrite_app_to_appgamma phi body }
  | AppFun { f; t = arg } ->
      AppFun { f = rewrite_app_to_appgamma phi f;
               t = rewrite_app_to_appgamma phi arg }
  | Unit | Var _ | Ctor _ -> t

and rewrite_app_to_appgamma_in_gamma (phi : string) (g : gamma) : gamma =
  match g with
  | Direct { params; body } ->
      Direct { params; body = rewrite_app_to_appgamma phi body }
  | Composed { omega; gamma } ->
      Composed { omega; gamma = rewrite_app_to_appgamma_in_gamma phi gamma }
  | Var _ -> g

let rec rewrite_app_to_appfun (name : string) (t : term) : term =
  match t with
  | App { omega = Var x; t = arg } when x = name ->
      AppFun { f = Var x; t = rewrite_app_to_appfun name arg }
  | App { omega; t = arg } ->
      App { omega; t = rewrite_app_to_appfun name arg }
  | Let { p; t_1; t_2 } ->
      let t_1' = rewrite_app_to_appfun name t_1 in
      let shadowed = contains_value name p in
      Let { p; t_1 = t_1';
            t_2 = if shadowed then t_2 else rewrite_app_to_appfun name t_2 }
  | LetIso { phi; omega; t } ->
      if phi = name then LetIso { phi; omega; t }
      else LetIso { phi; omega; t = rewrite_app_to_appfun name t }
  | LetIdem { phi; gamma; t } ->
      let gamma' = rewrite_app_to_appfun_in_gamma name gamma in
      if phi = name then LetIdem { phi; gamma = gamma'; t }
      else LetIdem { phi; gamma = gamma';
                     t = rewrite_app_to_appfun name t }
  | Tuple ts -> Tuple (List.map (rewrite_app_to_appfun name) ts)
  | Cted { c; t = arg } -> Cted { c; t = rewrite_app_to_appfun name arg }
  | AppGamma { gamma; t = arg } ->
      AppGamma { gamma = rewrite_app_to_appfun_in_gamma name gamma;
                 t = rewrite_app_to_appfun name arg }
  | Fun { x; body } ->
      if x = name then Fun { x; body }
      else Fun { x; body = rewrite_app_to_appfun name body }
  | AppFun { f; t = arg } ->
      AppFun { f = rewrite_app_to_appfun name f;
               t = rewrite_app_to_appfun name arg }
  | Unit | Var _ | Ctor _ -> t

and rewrite_app_to_appfun_in_gamma (name : string) (g : gamma) : gamma =
  match g with
  | Direct { params; body } ->
      Direct { params; body = rewrite_app_to_appfun name body }
  | Composed { omega; gamma } ->
      Composed { omega; gamma = rewrite_app_to_appfun_in_gamma name gamma }
  | Var _ -> g
