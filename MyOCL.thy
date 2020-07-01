theory MyOCL
  imports Main
begin

type_synonym var = string
type_synonym att = string
datatype OCLexp = Int int 
  | Var var 
  | Eq OCLexp OCLexp
  | Att var att

(* self = caller *)
value "Eq (Var self) (Var caller)"

(* self.age = 30 *)
value "Eq (Att self age) (MyOCL.Int 30)"

end