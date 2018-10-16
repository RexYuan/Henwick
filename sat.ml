
module type Formula_interface =
sig
  exception UncaughtFormula
  exception InvalidClause

  type variable = string
  type formula =
      Var of variable
    | Neg of formula
    | And of formula * formula
    | Or  of formula * formula
    | Imp of formula * formula
    | Iff of formula * formula
  type dimacs_clause
  type dimacs_cnf = dimacs_clause list

  val string_of_formula : formula -> string
  val to_cnf : formula -> formula
end

module Formula : Formula_interface =
struct
  exception UncaughtFormula
  type variable = string
  type formula =
      Var of variable
    | Neg of formula
    | And of formula * formula
    | Or  of formula * formula
    | Imp of formula * formula
    | Iff of formula * formula

  let rec string_of_formula f =
    match f with
      Var str  -> str
    | Neg subf -> "-" ^ string_of_formula subf
    | And (subfl, subfr) -> "(" ^ string_of_formula subfl ^ " & " ^ string_of_formula subfr ^ ")"
    | Or  (subfl, subfr) -> "(" ^ string_of_formula subfl ^ " | " ^ string_of_formula subfr ^ ")"
    | Imp (subfl, subfr) -> "(" ^ string_of_formula subfl ^ " > " ^ string_of_formula subfr ^ ")"
    | _ -> raise UncaughtFormula

  let tseitin f i =
    let fresh_var  = Var ("!" ^ (string_of_int i)) in
    let fresh_var1 = Var ("!" ^ (string_of_int (i*2))) in
    let fresh_var2 = Var ("!" ^ (string_of_int (i*2+1))) in
    match f with
      Var str  -> Var str
    (* new <=> -sth = (new | --sth) & (-new | -sth) = (new | sth) & (-new | -sth) *)
    | Neg (Var s) -> And (
        Or (fresh_var, Var s),
        Or (Neg fresh_var, Neg (Var s))
      )
    | Neg _ -> And (
        Or (fresh_var, fresh_var1),
        Or (Neg fresh_var, Neg fresh_var1)
      )
    (* new <=> sthr & sthl = (new | -(sthr & sthl)) & (-new | (sthr & sthl)) = (new | (-sthr | -sthl)) & ((-new | sthl) & (-new | sthr)) *)
    | And (Var l, Var r) -> And (
        Or (fresh_var, Or (Neg (Var l), Neg (Var r))),
        And (
          Or (Neg fresh_var, Var l),
          Or (Neg fresh_var, Var r)
        )
      )
    | And (Var l, _) -> And (
        Or (fresh_var, Or (Neg (Var l), Neg fresh_var1)),
        And (
          Or (Neg fresh_var, Var l),
          Or (Neg fresh_var, fresh_var1)
        )
      )
    | And (_, Var r) -> And (
        Or (fresh_var, Or (Neg fresh_var1, Neg (Var r))),
        And (
          Or (Neg fresh_var, fresh_var1),
          Or (Neg fresh_var, Var r)
        )
      )
    | And (_, _) -> And (
        Or (fresh_var, Or (Neg fresh_var1, Neg fresh_var2)),
        And (
          Or (Neg fresh_var, fresh_var1),
          Or (Neg fresh_var, fresh_var2)
        )
      )
    (* new <=> sthr | sthl = (new | -(sthr | sthl)) & (-new | (sthr | sthl)) = ((new | -sthl) & (new | -sthr)) & (-new | (sthl | sthr)) *)
    | Or (Var l, Var r) -> And (
        And (
          Or (fresh_var, Neg (Var l)),
          Or (fresh_var, Neg (Var r))
        ),
        Or (Neg fresh_var, Or (Var l, Var r))
      )
    | Or (Var l, _) -> And (
        And (
          Or (fresh_var, Neg (Var l)),
          Or (fresh_var, Neg fresh_var1)
        ),
        Or (Neg fresh_var, Or (Var l, fresh_var1))
      )
    | Or (_, Var r) -> And (
        And (
          Or (fresh_var, Neg fresh_var1),
          Or (fresh_var, Neg (Var r))
        ),
        Or (Neg fresh_var, Or (fresh_var1, Var r))
      )
    | Or (_, _) -> And (
        And (
          Or (fresh_var, Neg fresh_var1),
          Or (fresh_var, Neg fresh_var2)
        ),
        Or (Neg fresh_var, Or (fresh_var1, fresh_var2))
      )
    (* new <=> sthr > sthl = (new | -(sthr > sthl)) & (-new | (sthr > sthl)) = (-new | (-sthl | sthr)) & ((new | sthl) & (new | -sthr)) *)
    | Imp (Var l, Var r) -> And (
        Or (Neg fresh_var, Or (Neg (Var l), Var r)),
        And (
          Or (fresh_var, Var l),
          Or (fresh_var, Neg (Var r))
        )
      )
    | Imp (Var l, _) -> And (
        Or (Neg fresh_var, Or (Neg (Var l), fresh_var1)),
        And (
          Or (fresh_var, Var l),
          Or (fresh_var, Neg fresh_var1)
        )
      )
    | Imp (_, Var r) -> And (
        Or (Neg fresh_var, Or (Neg fresh_var1, Var r)),
        And (
          Or (fresh_var, fresh_var1),
          Or (fresh_var, Neg (Var r))
        )
      )
    | Imp (_, _) -> And (
        Or (Neg fresh_var, Or (Neg fresh_var1, fresh_var2)),
        And (
          Or (fresh_var, fresh_var1),
          Or (fresh_var, Neg fresh_var2)
        )
      )
    | _ -> raise UncaughtFormula

  let to_cnf f =
    let rec walk f i =
      let (next_i1, next_i2) = (i*2, i*2+1) in
      match f with
        Var s -> Var s
      | Neg (Var _) -> tseitin f i
      | Neg subf -> And (tseitin f i, walk subf next_i1)
      (*| _ (subfl, subfr) -> And (tseitin f, And (walk subfl, walk subfr))*)
      | And (Var _, Var _) -> tseitin f i
      | And (Var _, subfr) -> And (tseitin f i, walk subfr next_i1)
      | And (subfl, Var _) -> And (tseitin f i, walk subfl next_i1)
      | And (subfl, subfr) -> And (tseitin f i, And (walk subfl next_i1, walk subfr next_i2))
      | Or (Var _, Var _)  -> tseitin f i
      | Or (Var _, subfr)  -> And (tseitin f i, walk subfr next_i1)
      | Or (subfl, Var _)  -> And (tseitin f i, walk subfl next_i1)
      | Or (subfl, subfr)  -> And (tseitin f i, And (walk subfl next_i1, walk subfr next_i2))
      | Imp (Var _, Var _) -> tseitin f i
      | Imp (Var _, subfr) -> And (tseitin f i, walk subfr next_i1)
      | Imp (subfl, Var _) -> And (tseitin f i, walk subfl next_i1)
      | Imp (subfl, subfr) -> And (tseitin f i, And (walk subfl next_i1, walk subfr next_i2))
      | _ -> raise UncaughtFormula
    in And (Var "!1", walk f 1)

  exception InvalidClause
  type dimacs_clause = int list
  type dimacs_cnf = dimacs_clause list

  let print_dimacs_clause (c : dimacs_clause) = List.iter (fun x -> print_int x; print_string " ") c
  let print_dimacs_cnf (cnf : dimacs_cnf) = List.iter (fun x -> print_dimacs_clause x; print_string "\n") cnf

  exception VariableNotFound
  type numbering_dict = (variable * int) list

  let build_dict (vs : variable list) : numbering_dict =
    let rec helper vs i =
      match vs with
        [] -> []
      | v::vs' -> (v, i) :: helper vs' (i+1)
    in helper vs 1
  let rec translate (vs : numbering_dict) (v : variable) : int =
    match vs with
      [] -> raise VariableNotFound
    | (v',i)::vs' when v=v' -> i
    | _::vs' -> translate vs' v

  let dimacs_tseitin (translate : variable -> int) (f : formula) (i : int) (t : int) : dimacs_cnf =
    let (fresh_var, fresh_var1, fresh_var2)  = (t+i, t+i*2, t+i*2+1) in
    match f with
      Var str  -> [ [translate str] ]
    (* new <=> -sth = (new | --sth) & (-new | -sth) = (new | sth) & (-new | -sth) *)
    | Neg (Var s) -> [ [fresh_var; translate s] ; [-fresh_var; -(translate s)] ]
    | Neg _       -> [ [fresh_var; fresh_var1]  ; [-fresh_var; -fresh_var1] ]
    (* new <=> sthr & sthl = (new | -(sthr & sthl)) & (-new | (sthr & sthl)) = (new | (-sthr | -sthl)) & ((-new | sthl) & (-new | sthr)) *)
    | And (Var l, Var r) -> [ [fresh_var; -(translate l); -(translate r)] ; [-fresh_var; translate l] ; [-fresh_var; translate r] ]
    | And (Var l, _)     -> [ [fresh_var; -(translate l); -fresh_var1]    ; [-fresh_var; translate l] ; [-fresh_var; fresh_var1] ]
    | And (_, Var r)     -> [ [fresh_var; -fresh_var1; -(translate r)]    ; [-fresh_var; fresh_var1]  ; [-fresh_var; translate r] ]
    | And (_, _)         -> [ [fresh_var; -fresh_var1; -fresh_var2]       ; [-fresh_var; fresh_var1]  ; [-fresh_var; fresh_var2] ]
    (* new <=> sthr | sthl = (new | -(sthr | sthl)) & (-new | (sthr | sthl)) = ((new | -sthl) & (new | -sthr)) & (-new | (sthl | sthr)) *)
    | Or (Var l, Var r) -> [ [fresh_var; -(translate l)] ; [fresh_var; -(translate r)] ; [-fresh_var; translate l; translate r] ]
    | Or (Var l, _)     -> [ [fresh_var; -(translate l)] ; [fresh_var; -fresh_var1]    ; [-fresh_var; translate l; fresh_var1] ]
    | Or (_, Var r)     -> [ [fresh_var; -fresh_var1]    ; [fresh_var; -(translate r)] ; [-fresh_var; fresh_var1; translate r] ]
    | Or (_, _)         -> [ [fresh_var; -fresh_var1]    ; [fresh_var; -fresh_var2]    ; [-fresh_var; fresh_var1; fresh_var2] ]
    (* new <=> sthr > sthl = (new | -(sthr > sthl)) & (-new | (sthr > sthl)) = (-new | (-sthl | sthr)) & ((new | sthl) & (new | -sthr)) *)
    | Imp (Var l, Var r) -> [ [-fresh_var; -(translate l); translate r] ; [fresh_var; translate l] ; [fresh_var; -(translate r)] ]
    | Imp (Var l, _)     -> [ [-fresh_var; -(translate l); fresh_var1]  ; [fresh_var; translate l] ; [fresh_var; -fresh_var1] ]
    | Imp (_, Var r)     -> [ [-fresh_var; -fresh_var1; translate r]    ; [fresh_var; fresh_var1]  ; [fresh_var; -(translate r)] ]
    | Imp (_, _)         -> [ [-fresh_var; -fresh_var1; fresh_var2]     ; [fresh_var; fresh_var1]  ; [fresh_var; -fresh_var2] ]
    | _ -> raise UncaughtFormula
end

(*let cnf = [[4;1]; [4;-2]; [-4;-1;5]; [-5;2]; [-5;3]; [5; -2; -3]]
  let _ = ignore (print_dimacs_cnf cnf)*)
open Formula
let f = Imp (Var "x1", And (Var "x2", Var "x3"))
let _ = ignore (Printf.printf "%s\n" (string_of_formula (to_cnf f)))
let f = Or (Neg (Var "x1"), And (Var "x2", Var "x3"))
let _ = ignore (Printf.printf "%s\n" (string_of_formula (to_cnf f)))
