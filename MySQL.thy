theory MySQL
  imports Main ObjectModel
begin

type_synonym var = string

datatype table = PERSON | ENROLLMENT
datatype col = AGE | EMAIL | ID | LECTURERS | STUDENTS

datatype exp = Int int 
  | Var var 
  | Eq exp exp
  | Col col
  | Count col

datatype whereClause = WHERE exp

datatype SQLstm = Select exp 
  | SelectFrom exp fromItem
| SelectFromWhere exp fromItem whereClause 
and fromItem = Table table | Subselect SQLstm

fun isID :: "col \<Rightarrow> table \<Rightarrow> bool" where
"isID ID PERSON = True " |
"isID _ _ = False"

fun execFrom :: "fromItem \<Rightarrow> persons \<Rightarrow> val" where
"execFrom (Table _) ps  = mapPersonsToVList ps" |
"execFrom (Subselect _) ps = VNULL"

fun sat :: "val \<Rightarrow> exp \<Rightarrow> bool" where
"sat v e = True"

fun proj :: "exp \<Rightarrow> val \<Rightarrow> val" where 
"proj (Col AGE) (VPerson (P pid page pemail pstudents plecturers)) 
= VInt page" |
"proj (Col EMAIL) (VPerson (P pid page pemail pstudents plecturers)) 
= VString pemail" |
"proj (Col ID) (VPerson (P pid page pemail pstudents plecturers)) 
= VString pid" |
"proj (Col STUDENTS) (VPerson (P pid page pemail pstudents plecturers)) 
= mapPersonsToVList pstudents" |
"proj (Col LECTURERS) (VPerson (P pid page pemail pstudents plecturers)) 
= mapPersonsToVList plecturers" |
"proj (MySQL.Int i) v = VInt i" |
"proj (Var var) v = VString var" |
"proj (Eq e1 e2) v = VBool (equalVal (proj e1 v) (proj e2 v))" |
"proj _ _ = VNULL"

fun isIdPerson :: "var \<Rightarrow> Person \<Rightarrow> bool" where
"isIdPerson v (P pid page pemail pstudents plecturers) 
= (v = pid)"

fun ext :: "var \<Rightarrow> col \<Rightarrow> persons \<Rightarrow> val" where
"ext v col Nil = VNULL" |
"ext v col (p#ps) = 
(if (isIdPerson v p) then (proj (Col col) (VPerson p)) 
else (ext v col ps))"

fun extElement :: "var \<Rightarrow> persons \<Rightarrow> val" where
"extElement v Nil = VNULL" |
"extElement v (Cons p ps) =
(if (isIdPerson v p) then (VPerson p)
else extElement v ps)"

fun filterWhere :: "val \<Rightarrow> whereClause \<Rightarrow> val" where
"filterWhere (VList Nil) (WHERE e) = VList Nil" |
"filterWhere (VList (Cons v vs)) (WHERE e)
= (if sat v e 
then (appendList v (filterWhere (VList vs) (WHERE e)))   
else filterWhere (VList vs) (WHERE e))" |
"filterWhere v e = v"

fun select :: "val \<Rightarrow> exp \<Rightarrow> val" where
"select VNULL (MySQL.Int i) = VList [VInt i]" |
"select VNULL (MySQL.Var var) = VList [VString var]" |
"select VNULL (MySQL.Eq e1 e2) = 
VList [VBool (equalVal (select VNULL e1) (select VNULL e2))]" |
"select VNULL COUNT = VList [VInt 0]" |

"select (VList Nil) exp = VList Nil" |
"select (VList (v#vs)) exp = 
appendList (proj exp v) (select (VList vs) exp)"

fun exec :: "SQLstm \<Rightarrow> persons \<Rightarrow> val" where
"exec (Select selitems) ps  = select VNULL selitems" |
"exec (SelectFrom selitems fromItem) ps 
= select (execFrom fromItem ps) selitems" |
"exec (SelectFromWhere selitems fromItem whereExp) ps
= select (filterWhere (execFrom fromItem ps) whereExp) selitems"

end