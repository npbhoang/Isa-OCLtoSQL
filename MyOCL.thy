theory MyOCL
  imports Main ObjectModel MySQL
begin

type_synonym var = string
datatype att = AGE | EMAIL | ID
datatype as = LECTURERS | STUDENTS

datatype OCLexp = Int nat 
  | Var var 
  | Eq OCLexp OCLexp
  | Att var att
  | As var as
  | Size OCLexp

fun transAtt :: "MyOCL.att \<Rightarrow> MySQL.col" where
"transAtt MyOCL.AGE = MySQL.AGE" |
"transAtt MyOCL.EMAIL = MySQL.EMAIL" |
"transAtt MyOCL.ID = MySQL.ID" 

fun transAs :: "MyOCL.as \<Rightarrow> MySQL.col" where
"transAs MyOCL.STUDENTS = MySQL.STUDENTS" |
"transAs MyOCL.LECTURERS = MySQL.LECTURERS"

fun eval :: "OCLexp \<Rightarrow> Objectmodel \<Rightarrow> val" where
"eval (MyOCL.Int i) om = VList [VInt i]"
| "eval (MyOCL.Var x) om = VList [VString x]"
| "eval (MyOCL.Eq e1 e2) om = 
VList [VBool (equalVal (eval e1 om) (eval e2 om))]" 
| "eval (MyOCL.Att v att) om 
= VList [ext v (transAtt att) (getPersonList om)]"
| "eval (MyOCL.As v as) om 
= VList (extCol v (transAs as) (getEnrollmentList om))"
| "eval (MyOCL.Size exp) om 
= VList [VInt (sizeValList (eval exp om))]"

end