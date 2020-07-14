theory MyOCL
  imports Main ObjectModel MySQL
begin

type_synonym var = string
type_synonym ivar = string
datatype att = AGE | EMAIL | ID
datatype as = LECTURERS | STUDENTS



datatype OCLexp = Int nat 
  | Var var 
  | Eq OCLexp OCLexp
  | IVar ivar
  | Att OCLexp att
  | As OCLexp as
  | Size OCLexp
  | IsEmpty OCLexp
  | Exists OCLexp OCLexp OCLexp

fun transAtt :: "MyOCL.att \<Rightarrow> MySQL.col" where
"transAtt MyOCL.AGE = MySQL.AGE" |
"transAtt MyOCL.EMAIL = MySQL.EMAIL" |
"transAtt MyOCL.ID = MySQL.ID" 

fun transAs :: "MyOCL.as \<Rightarrow> MySQL.col" where
"transAs MyOCL.STUDENTS = MySQL.STUDENTS" |
"transAs MyOCL.LECTURERS = MySQL.LECTURERS"

fun evalWithCtx :: "OCLexp \<Rightarrow> Objectmodel \<Rightarrow> OCLexp \<Rightarrow> val \<Rightarrow> val" where
"evalWithCtx (MyOCL.Int i) om var val = VInt i"
(* For the time being *)
| "evalWithCtx (MyOCL.Var x) om (MyOCL.IVar i) val = (VString x)"
| "evalWithCtx (MyOCL.IVar x) om (MyOCL.IVar i) val = val"
(* *)
| "evalWithCtx (MyOCL.Eq e1 e2) om var val = 
VBool (equalVal (evalWithCtx e1 om var val) (evalWithCtx e2 om var val))" 
| "evalWithCtx (MyOCL.Att (Var v) att) om (MyOCL.IVar i) val
= (if (v=i) then (projVal (Col (transAtt att)) val) 
else (VList (projValList (Col (transAtt att)) [extPerson v (getPersonList om)])))"
| "evalWithCtx (MyOCL.As (Var v) as) om (MyOCL.IVar i) val
= (if (v=i) then (projVal (Col (transAs as)) val) 
else (VList (extCol v (transAs as) (getEnrollmentList om))))"
| "evalWithCtx (MyOCL.Size exp) om var val
= VList [VInt (sizeVal (evalWithCtx exp om var val))]"
| "evalWithCtx (MyOCL.IsEmpty exp) om var val
= VList [VBool (isEmptyVal (evalWithCtx exp om var val))]"
| "evalWithCtx (MyOCL.Exists src v body) om var val
= (evalWithCtx src om var val)"

fun filterWithBody :: "val list \<Rightarrow> OCLexp \<Rightarrow> OCLexp \<Rightarrow> Objectmodel \<Rightarrow> val list" where
"filterWithBody Nil var (exp) om = Nil" 
| "filterWithBody (Cons val vs) var exp om = (if (isTrueVal (evalWithCtx exp om var val)) 
    then (val#(filterWithBody vs var exp om))   
    else filterWithBody vs var exp om)"

fun eval :: "OCLexp \<Rightarrow> Objectmodel \<Rightarrow> val list" where
"eval (MyOCL.Int i) om = [VInt i]"
| "eval (MyOCL.Var x) om = [VString x]"
| "eval (MyOCL.Eq e1 e2) om = [VBool (equalValList (eval e1 om) (eval e2 om))]" 
(*| "eval (MyOCL.Att (Var v) att) om = projValList (Col (transAtt att)) [extPerson v (getPersonList om)]"*)
(*| "eval (MyOCL.As (Var v) as) om = extCol v (transAs as) (getEnrollmentList om)"*)
| "eval (MyOCL.Size exp) om = [VInt (sizeValList (eval exp om))]"
| "eval (MyOCL.IsEmpty exp) om = [VBool (isEmptyValList (eval exp om))]"
| "eval (MyOCL.Exists src v body) om = [VBool (\<not> isEmptyValList (filterWithBody (eval src om) v body om))]"
                      
end