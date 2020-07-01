theory MySQL
  imports Main
begin

type_synonym var = string

type_synonym table = string
type_synonym column = string

datatype exp = Int int 
  | Var var 
  | Eq exp exp
  | Col column

datatype fromItem = FROM table

datatype whereClause = WHERE exp

datatype SQLstm = Select exp
  | SelectFrom exp fromItem
  | SelectFromWhere exp fromItem whereClause

(* SELECT self = caller *)
value "Select (Eq (Var self) (Var caller))"

(* SELECT age FROM Lecturer *)
value "SelectFrom (Att age) (FROM Lecturer)"

(* SELECT age = 30 FROM Lecturer WHERE lid = self *)
value "SelectFromWhere (Eq (Att age) (MySQL.Int 30))
(FROM Lecturer) (WHERE (Eq (Att lid) (Var self)))"

end