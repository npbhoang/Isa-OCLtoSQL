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
"evalWithCtx (MyOCL.Int i) om var val = VInt i"
| "evalWithCtx (MyOCL.Var x) om var val = (if (x = var) then val else (VString x))"
| "evalWithCtx (MyOCL.Eq e1 e2) om var val = 
VBool (equalVal (evalWithCtx e1 om var val) (evalWithCtx e2 om var val))" 
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

fun filterWithBody :: "val list \<Rightarrow> var \<Rightarrow> OCLexp \<Rightarrow> Objectmodel \<Rightarrow> val list" where
"filterWithBody Nil var (exp) om = Nil" 
| "filterWithBody (Cons val vs) var exp om = (if (isTrueVal (evalWithCtx exp om var val)) 
    then (val#(filterWithBody vs var exp om))   
    else filterWithBody vs var exp om)"

fun eval :: "OCLexp \<Rightarrow> Objectmodel \<Rightarrow> val list" where
"eval (MyOCL.Int i) om = [VInt i]"
| "eval (MyOCL.Var x) om = [VString x]"
| "eval (MyOCL.Eq e1 e2) om = [VBool (equalValList (eval e1 om) (eval e2 om))]" 
| "eval (MyOCL.Att v att) om = [ext v (transAtt att) (getPersonList om)]"
| "eval (MyOCL.As v as) om = (extCol v (transAs as) (getEnrollmentList om))"
| "eval (MyOCL.Size exp) om = [VInt (sizeValList (eval exp om))]"
| "eval (MyOCL.IsEmpty exp) om = [VBool (isEmptyValList (eval exp om))]"
| "eval (MyOCL.Exists src v body) om = [VBool (\<not> isEmptyValList (filterWithBody (eval src om) v body om))]"
                      
end