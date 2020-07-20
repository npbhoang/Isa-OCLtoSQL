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
  | PE OCLexp Objectmodel
  | AllInstances table

fun transAtt :: "MyOCL.att \<Rightarrow> MySQL.col" where
"transAtt MyOCL.AGE = MySQL.AGE" |
"transAtt MyOCL.EMAIL = MySQL.EMAIL" |
"transAtt MyOCL.ID = MySQL.ID" 

fun transAs :: "MyOCL.as \<Rightarrow> MySQL.col" where
"transAs MyOCL.STUDENTS = MySQL.STUDENTS" |
"transAs MyOCL.LECTURERS = MySQL.LECTURERS"

fun evalWithCtx :: "OCLexp \<Rightarrow> OCLexp \<Rightarrow> val \<Rightarrow> val" where
"evalWithCtx (MyOCL.Int i) var val = VInt i"
(* For the time being *)
| "evalWithCtx (MyOCL.Var x) (MyOCL.IVar i) val = (VObj x)" 
| "evalWithCtx (MyOCL.IVar x) (MyOCL.IVar i) val = val"
(* *)
| "evalWithCtx (MyOCL.Eq e1 e2) var val = 
VBool (equalVal (evalWithCtx e1 var val) (evalWithCtx e2 var val))" 


| "evalWithCtx (PE (MyOCL.Att (Var v) att) om) (MyOCL.IVar i) val
= projVal (Col (transAtt att)) (VObj v)"

| "evalWithCtx (PE (MyOCL.Att (IVar v) att) om) (MyOCL.IVar i) val
= projVal (Col (transAtt att)) val"


| "evalWithCtx (PE (MyOCL.As (Var v) as) om) (MyOCL.IVar i) val
= VList (extCol (MySQL.Var v) (transAs as) (getEnrollmentList om))"
(*
| "evalWithCtx (PE (MyOCL.As (IVar v) as) om) (MyOCL.IVar i) val
= VList (extCol (MySQL.IVar v) (transAs as) (getEnrollmentList om))"

| "evalWithCtx (MyOCL.Size exp) var val
= VList [VInt (sizeVal (evalWithCtx exp var val))]"
| "evalWithCtx (MyOCL.IsEmpty exp) var val
= VList [VBool (isEmptyVal (evalWithCtx exp var val))]"
| "evalWithCtx (MyOCL.Exists src v body) var val
= (evalWithCtx src var val)"
*)

fun filterWithBody :: "val list \<Rightarrow> OCLexp \<Rightarrow> OCLexp \<Rightarrow> val list" where
"filterWithBody Nil var (exp) = Nil" 
| "filterWithBody (Cons val vs) var exp = (if (isTrueVal (evalWithCtx exp var val)) 
    then (val#(filterWithBody vs var exp))   
    else filterWithBody vs var exp)"

fun partialEval :: "OCLexp \<Rightarrow> Objectmodel \<Rightarrow> OCLexp" where
"partialEval (MyOCL.Int i) om = (MyOCL.Int i)"
| "partialEval (MyOCL.Var x) om = (MyOCL.Var x)"
| "partialEval (MyOCL.IVar i) om = (MyOCL.IVar i)"
| "partialEval (MyOCL.Eq e1 e2) om = MyOCL.Eq (partialEval e1 om) (partialEval e2 om)" 
| "partialEval (MyOCL.Att (Var v) att) om = (PE (MyOCL.Att (Var v) att) om)"
| "partialEval (MyOCL.Att (IVar v) att) om = (PE (MyOCL.Att (IVar v) att) om)"
| "partialEval (MyOCL.As (Var v) as) om = (PE (MyOCL.As (Var v) as) om)"
| "partialEval (MyOCL.As (IVar v) as) om = (PE (MyOCL.As (IVar v) as) om)"

fun eval :: "OCLexp \<Rightarrow> Objectmodel \<Rightarrow> val list" where
"eval (MyOCL.Int i) om = [VInt i]"
| "eval (MyOCL.Var x) om = [VObj x]"
| "eval (MyOCL.Eq e1 e2) om = [VBool (equalValList (eval e1 om) (eval e2 om))]" 
| "eval (MyOCL.Att (Var v) att) om = projValList (Col (transAtt att)) [VObj v]"
| "eval (MyOCL.As (Var v) as) om = extCol (MySQL.Var v) (transAs as) (getEnrollmentList om)"
| "eval (MyOCL.Size exp) om = [VInt (sizeValList (eval exp om))]"
| "eval (MyOCL.IsEmpty exp) om = [VBool (isEmptyValList (eval exp om))]"
| "eval (MyOCL.Exists src v body) om = [VBool (\<not> isEmptyValList (filterWithBody (eval src om) v (partialEval body om)))]"
| "eval (MyOCL.AllInstances PERSON) om = mapPersonListToValList (getPersonList om)"

fun translate :: "OCLexp \<Rightarrow> MySQL.exp" where
"translate (MyOCL.Int i) = MySQL.Int i" |
"translate (Att (IVar p) att) = MySQL.Col (transAtt att)"

end