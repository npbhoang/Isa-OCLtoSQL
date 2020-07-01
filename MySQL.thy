theory MySQL
  imports Main
begin

type_synonym var = string

type_synonym table = string
datatype col = ATT string | ID table

datatype exp = Int int 
  | Var var 
  | Eq exp exp
  | Col col

datatype fromItem = FROM table

datatype whereClause = WHERE exp

datatype SQLstm = Select exp
  | SelectFrom exp fromItem
  | SelectFromWhere exp fromItem whereClause

fun isID :: "col \<Rightarrow> table \<Rightarrow> bool" where
"isID (ID t1) t = (t1 = t)" |
"isID _ _ = False"

fun equalCol :: "col \<Rightarrow> col \<Rightarrow> bool" where 
"equalCol (ATT s1) (ATT s2) = (s1 = s2)" |
"equalCol (ID i1) (ID i2) = (i1 = i2)" |
"equalCol _ _ = False"

(* SELECT self = caller *)
value "Select (Eq (Var self) (Var caller))"

(* SELECT age FROM Lecturer *)
value "SelectFrom (Att age) (FROM Lecturer)"

(* SELECT age = 30 FROM Lecturer WHERE lid = self *)
value "SelectFromWhere (Eq (Att age) (MySQL.Int 30))
(FROM Lecturer) (WHERE (Eq (Att lid) (Var self)))"

end