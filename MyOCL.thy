theory MyOCL
  imports Main
begin

type_synonym var = string
datatype att = AGE | EMAIL | ID
(*
type_synonym assoc = string
*)
(*
datatype OCLCol = Assoc var assoc
*)
datatype OCLexp = Int int 
  | Var var 
  | Eq OCLexp OCLexp
  | Att var att
(*
  | OCLCol 
  | ITER OCLCol var OCLexp
*)

(* self = caller *)
value "Eq (Var self) (Var caller)"

(* self.age = 30 *)
value "Eq (Att self age) (MyOCL.Int 30)"

(*
(* self.students\<rightarrow>exists(s|s = caller) *)
value "ITER (Assoc self students) s (Eq (Var s) (Var caller))"
*)
end