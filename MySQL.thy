theory MySQL
  imports Main
begin

type_synonym var = string

type_synonym table = string
datatype col = AGE  | EMAIL | ID


datatype exp = Int int 
  | Var var 
  | Eq exp exp
  | Col col


datatype whereClause = WHERE exp

datatype SQLstm = Select exp 
  | SelectFrom exp fromItem
  | SelectFromWhere exp fromItem whereClause 
and  fromItem = FROM table |  Subselect SQLstm

fun isID :: "col \<Rightarrow> table \<Rightarrow> bool" where
"isID (ID) t = True " |
"isID _ _ = False"

end