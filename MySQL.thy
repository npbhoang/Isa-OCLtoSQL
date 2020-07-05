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

datatype whereClause = WHERE exp

datatype SQLstm = Select exp 
  | SelectFrom exp fromItem
  | SelectFromWhere exp fromItem whereClause 
and  fromItem = FROM table |  Subselect SQLstm

fun isID :: "col \<Rightarrow> table \<Rightarrow> bool" where
"isID (ID) t = True " |
"isID _ _ = False"

(* temp: This only takes a column, should also take a table 
or a col has info of a table*)
fun proj :: "col \<Rightarrow> Person \<Rightarrow> val" where
"proj (AGE) (P pid page pemail pstudents plecturers) = VInt page" |
"proj (EMAIL) (P pid page pemail pstudents plecturers) = VString pemail" |
"proj (ID) (P pid page pemail pstudents plecturers) = VString pid" |
"proj (STUDENTS) (P pid page pemail pstudents plecturers) = mapList pstudents" |
"proj (LECTURERS) (P pid page pemail pstudents plecturers) = mapList plecturers"

fun ext :: "var \<Rightarrow> col \<Rightarrow> persons \<Rightarrow> val" where
"ext v col Nil = VString ''null''" |
"ext v col (Cons (P pid page pemail pstudents plecturers) ps) = 
(if (v = pid) then (proj col (P pid page pemail pstudents plecturers))  
else (ext v col ps))"

function (sequential) exec :: "SQLstm \<Rightarrow> persons \<Rightarrow> val" where
"exec (Select (MySQL.Int i)) ps  = VInt i" |
"exec (Select (MySQL.Var v)) ps = VString v" |
"exec (Select (MySQL.Col _)) ps = VString ''null''" |
"exec (Select (MySQL.Eq (MySQL.Var v1) (MySQL.Var v2))) ps = 
VBool (v1 = v2)" |
"exec (Select (MySQL.Eq (MySQL.Int i1) (MySQL.Int i2))) ps = 
VBool (i1 = i2)" |
"exec (Select (MySQL.Eq (MySQL.Col c1) (MySQL.Col c2))) ps = 
VBool (c1 = c2)" |
"exec (Select (MySQL.Eq _ _)) ps = VBool False" |
(* TBC: partial definition *)
"exec (SelectFrom _ _) ps = VBool False" |
(* FROM_WHERE *)
"exec (SelectFromWhere (MySQL.Col col) (FROM table1) 
(WHERE (MySQL.Eq (MySQL.Col col2) (MySQL.Var v)))) ps
= (if isID col2 table1 
then (ext v col ps) 
else VBool False)" |

"exec (SelectFromWhere (MySQL.Eq (MySQL.Col col1) (MySQL.Int i)) 
(FROM table) 
(WHERE (MySQL.Eq (MySQL.Col col2) (MySQL.Var v)))) ps
= VBool (equalVal (exec (SelectFromWhere (MySQL.Col col1) (FROM table) 
(WHERE (MySQL.Eq (MySQL.Col col2) (MySQL.Var v)))) ps ) (VInt i))" |

"exec _ ps = VBool False"
by pat_completeness auto
termination by size_change

end