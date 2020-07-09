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
  | IsEmpty OCLexp
  | Exists OCLexp var OCLexp

fun transAtt :: "MyOCL.att \<Rightarrow> MySQL.col" where
"transAtt MyOCL.AGE = MySQL.AGE" |
"transAtt MyOCL.EMAIL = MySQL.EMAIL" |
"transAtt MyOCL.ID = MySQL.ID" 

fun transAs :: "MyOCL.as \<Rightarrow> MySQL.col" where
"transAs MyOCL.STUDENTS = MySQL.STUDENTS" |
"transAs MyOCL.LECTURERS = MySQL.LECTURERS"

fun evalWithCtx :: "OCLexp \<Rightarrow> Objectmodel \<Rightarrow> var \<Rightarrow> val \<Rightarrow> val" where
"evalWithCtx (MyOCL.Int i) om var val = VList [VInt i]"
| "evalWithCtx (MyOCL.Var x) om var val = (if (x = var) then (VList[val]) else (VList[VString x]))"
| "evalWithCtx (MyOCL.Eq e1 e2) om var val = 
VList [VBool (equalVal (evalWithCtx e1 om var val) (evalWithCtx e2 om var val))]" 
| "evalWithCtx (MyOCL.Att v att) om var val
= (if (v=var) then (projList (Col (transAtt att)) val) else (VList [ext v (transAtt att) (getPersonList om)]))"
| "evalWithCtx (MyOCL.As v as) om var val
= (if (v=var) then (projList (Col (transAs as)) val) else (VList (extCol v (transAs as) (getEnrollmentList om))))"
| "evalWithCtx (MyOCL.Size exp) om var val
= VList [VInt (sizeVal (evalWithCtx exp om var val))]"
| "evalWithCtx (MyOCL.IsEmpty exp) om var val
= VList [VBool (isEmptyVal (evalWithCtx exp om var val))]"
| "evalWithCtx (MyOCL.Exists src v body) om var val
= (evalWithCtx src om var val)"

fun filterWithBody :: "val \<Rightarrow> var \<Rightarrow> OCLexp \<Rightarrow> Objectmodel \<Rightarrow> val" where
"filterWithBody (VList Nil) var (exp) om = VList Nil" 
  | "filterWithBody (VList (Cons val vs)) var exp om = (if (isTrue (evalWithCtx exp om var val)) 
    then (appendList val (filterWithBody (VList vs) var exp om))   
    else filterWithBody (VList vs) var exp om)"

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
= VList [VInt (sizeVal (eval exp om))]"
| "eval (MyOCL.IsEmpty exp) om
= VList [VBool (isEmptyVal (eval exp om))]"
| "eval (MyOCL.Exists src v body) om
= VList [VBool (\<not> isEmptyVal (filterWithBody (eval src om) v body om))]"
                      
end