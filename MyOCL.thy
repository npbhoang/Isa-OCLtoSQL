theory MyOCL
  imports Main ObjectModel MySQL
begin

type_synonym var = string
datatype att = AGE | EMAIL | ID
datatype as = LECTURERS | STUDENTS

datatype OCLexp = Int int 
  | Var var 
  | Eq OCLexp OCLexp
  | Att var att
  | As var as
  | Size OCLexp
  | IsEmpty OCLexp

fun transAtt :: "MyOCL.att \<Rightarrow> MySQL.col" where
"transAtt MyOCL.AGE = MySQL.AGE" |
"transAtt MyOCL.EMAIL = MySQL.EMAIL" |
"transAtt MyOCL.ID = MySQL.ID" 

fun transAs :: "MyOCL.as \<Rightarrow> MySQL.col" where
"transAs MyOCL.STUDENTS = MySQL.STUDENTS" |
"transAs MyOCL.LECTURERS = MySQL.LECTURERS"

fun eval :: "OCLexp \<Rightarrow> persons \<Rightarrow> val" where
"eval (MyOCL.Int i) ps = VList [VInt i]" |
"eval (MyOCL.Var x) ps = VList [VString x]" |
"eval (MyOCL.Eq e1 e2) ps = 
VList [VBool (equalVal (eval e1 ps) (eval e2 ps))]" |
"eval (MyOCL.Att v att) ps 
= VList [ext v (transAtt att) ps]" |
"eval (MyOCL.As v as) ps 
= ext v (transAs as) ps" |
"eval (Size exp) ps 
= VList [VInt (countVList (eval exp ps))]" |
"eval (IsEmpty exp) ps 
= VList [VBool (isEmptyVList (eval exp ps))]"

end