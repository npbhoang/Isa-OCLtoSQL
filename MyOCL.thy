theory MyOCL
  imports Main ObjectModel MySQL
begin

type_synonym var = string
type_synonym ivar = string
datatype att = AGE | EMAIL
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
  | Collect OCLexp OCLexp OCLexp
  (* collect with the body returns a collect-type, then flatten afterwards*)
  | CollectPlus OCLexp OCLexp OCLexp 
  | PEAtt OCLexp
  | PEAs OCLexp "Enrollment list"
  | AllInstances table

fun transAtt :: "MyOCL.att \<Rightarrow> MySQL.col" where
"transAtt MyOCL.AGE = MySQL.AGE" |
"transAtt MyOCL.EMAIL = MySQL.EMAIL"

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

| "evalWithCtx (PEAtt (MyOCL.Att (Var v) att)) (MyOCL.IVar i) val
= projVal (Col (transAtt att)) (VObj v)"

| "evalWithCtx (PEAtt (MyOCL.Att (IVar v) att)) (MyOCL.IVar i) val
= projVal (Col (transAtt att)) val"

| "evalWithCtx (PEAs (MyOCL.As (Var v) as) es) (MyOCL.IVar i) val
= VList (extCol (VObj v) (transAs as) es)"

| "evalWithCtx (PEAs (MyOCL.As (IVar v) as) es) (MyOCL.IVar i) val
= VList (extCol val (transAs as) es)"
(*
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
| "partialEval (MyOCL.Att (Var v) att) om = (PEAtt (MyOCL.Att (Var v) att))"
| "partialEval (MyOCL.Att (IVar v) att) om = (PEAtt (MyOCL.Att (IVar v) att))"
| "partialEval (MyOCL.As (Var v) as) om = (PEAs (MyOCL.As (Var v) as) (getEnrollmentList om))"
| "partialEval (MyOCL.As (IVar v) as) om = (PEAs (MyOCL.As (IVar v) as) (getEnrollmentList om))"

fun flatten :: "val list \<Rightarrow> val list" where
"flatten [] = []" |
"flatten ((VList vs)#vss) = vs@(flatten vss)"

fun collect :: "val list \<Rightarrow> OCLexp \<Rightarrow> OCLexp \<Rightarrow> val list" where
"collect [] ivar exp = []"           
| "collect (val#vs) ivar exp = (evalWithCtx exp ivar val)#(collect vs ivar exp)"

fun eval :: "OCLexp \<Rightarrow> Objectmodel \<Rightarrow> val list" where
"eval (MyOCL.Int i) om = [VInt i]"
| "eval (MyOCL.Var x) om = [VObj x]"
| "eval (MyOCL.Eq e1 e2) om = [VBool (equalValList (eval e1 om) (eval e2 om))]" 
| "eval (MyOCL.Att (Var v) att) om = projValList (Col (transAtt att)) [VObj v]"
| "eval (MyOCL.As (Var v) as) om = extCol (VObj v) (transAs as) (getEnrollmentList om)"
| "eval (MyOCL.Size exp) om = [VInt (sizeValList (eval exp om))]"
| "eval (MyOCL.IsEmpty exp) om = [VBool (isEmptyValList (eval exp om))]"
| "eval (MyOCL.Exists src v body) om = [VBool (\<not> isEmptyValList (filterWithBody (eval src om) v (partialEval body om)))]"
| "eval (MyOCL.AllInstances PERSON) om = mapPersonListToValList (getPersonList om)"
| "eval (MyOCL.Collect src v body) om = collect (eval src om) v (partialEval body om)"
| "eval (MyOCL.CollectPlus src v body) om = flatten (collect (eval src om) v (partialEval body om))"

fun translate :: "OCLexp \<Rightarrow> MySQL.exp" where
"translate (MyOCL.Int i) = MySQL.Int i" |
"translate (Att (IVar p) att) = MySQL.Col (transAtt att)"

end