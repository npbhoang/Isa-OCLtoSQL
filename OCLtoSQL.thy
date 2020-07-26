theory OCLtoSQL
imports Main MySQL MyOCL
begin

fun transAtt :: "MyOCL.att \<Rightarrow> MySQL.col" where
"transAtt MyOCL.AGE = MySQL.AGE" |
"transAtt MyOCL.EMAIL = MySQL.EMAIL"

fun transAs :: "MyOCL.as \<Rightarrow> MySQL.col" where
"transAs MyOCL.STUDENTS = MySQL.STUDENTS" |
"transAs MyOCL.LECTURERS = MySQL.LECTURERS"

fun evalWithCtx :: "OCLexp \<Rightarrow> OCLexp \<Rightarrow> val \<Rightarrow> val" where
"evalWithCtx (MyOCL.Int x) (MyOCL.IVar i) val = VInt x"
(* For the time being *)
| "evalWithCtx (MyOCL.Var x) (MyOCL.IVar i) val = (VObj x)" 
(*| "evalWithCtx (MyOCL.IVar x) (MyOCL.IVar i) val = val"*)
| "evalWithCtx (MyOCL.Eq e1 e2) (MyOCL.IVar i) val = 
VBool (equalVal (evalWithCtx e1 (MyOCL.IVar i) val) (evalWithCtx e2 (MyOCL.IVar i) val))" 
(*
  by pat_completeness auto
termination evalWithCtx
  apply (relation  "(\<lambda>p. size (fst p)) <*mlex*> {}")
  sorry
*)
(*
| "evalWithCtx (PEAtt (MyOCL.Att (Var v) MyOCL.EMAIL)) (MyOCL.IVar i) val
= projVal (Col  MySQL.EMAIL) (VObj v)"
| "evalWithCtx (PEAs (MyOCL.As (Var v)  MyOCL.STUDENTS) es) (MyOCL.IVar i) val
= VList (extCol (VObj v) MySQL.STUDENTS es)"
| "evalWithCtx (PEAs (MyOCL.As (Var v)  MyOCL.LECTURERS) es) (MyOCL.IVar i) val
= VList (extCol (VObj v) MySQL.LECTURERS es)"
| "evalWithCtx (PEAtt (MyOCL.Att (IVar v)  MyOCL.AGE)) (MyOCL.IVar i) val
= projVal (Col  MySQL.AGE) val"
| "evalWithCtx (PEAtt (MyOCL.Att (IVar v)  MyOCL.EMAIL)) (MyOCL.IVar i) val
= projVal (Col  MySQL.EMAIL) val"
| "evalWithCtx (PEAs (MyOCL.As (IVar v)  MyOCL.STUDENTS) es) (MyOCL.IVar i) val
= VList (extCol val  MySQL.STUDENTS es)"
| "evalWithCtx (PEAs (MyOCL.As (IVar v)  MyOCL.LECTURERS) es) (MyOCL.IVar i) val
= VList (extCol val  MySQL.LECTURERS es)"
*)
(*
| "evalWithCtx (MyOCL.Size exp) var val
= VList [VInt (sizeVal (evalWithCtx exp var val))]"
| "evalWithCtx (MyOCL.IsEmpty exp) var val
= VList [VBool (isEmptyVal (evalWithCtx exp var val))]"
| "evalWithCtx (MyOCL.Exists src v body) var val
= (evalWithCtx src var val)"
*)
(* FACT --- Due to the performance, the definition is put as lemma *)
lemma [simp]: "evalWithCtx (PEAtt (MyOCL.Att (IVar v) att)) (MyOCL.IVar i) val
= projVal (Col (transAtt att)) val"
sorry
(* FACT --- Due to the performance, the definition is put as lemma *)
lemma [simp]: "evalWithCtx (PEAs (MyOCL.As (IVar v) as) es) (MyOCL.IVar i) val
= VList (extCol val (transAs as) es)"
sorry

fun filterWithBody :: "val list \<Rightarrow> OCLexp \<Rightarrow> OCLexp \<Rightarrow> val list" where
"filterWithBody Nil var (exp) = Nil" 
| "filterWithBody (Cons val vs) var exp = (if (isTrueVal (evalWithCtx exp var val)) 
    then (val#(filterWithBody vs var exp))   
    else filterWithBody vs var exp)"

fun collect :: "val list \<Rightarrow> OCLexp \<Rightarrow> OCLexp \<Rightarrow> val list" where
"collect [] ivar exp = []"           
| "collect (val#vs) ivar exp = (evalWithCtx exp ivar val)#(collect vs ivar exp)"
(* FACT --- perform a collect operator from a list 
appended by two lists is same of perform a collect opeartor on them individually *)                    
lemma [simp]: "collect (xs@ys) ivar exp = (collect xs ivar exp)@(collect ys ivar exp)"
proof (induct xs)
case Nil
then show ?case by simp
next
case (Cons a xs)
then show ?case by simp
qed

fun collectPlus :: "val list \<Rightarrow> OCLexp \<Rightarrow> OCLexp \<Rightarrow> val list" where
"collectPlus [] ivar exp = []"           
| "collectPlus (val#vs) ivar exp = 
(flatten (evalWithCtx exp ivar val))@ (collectPlus vs ivar exp)"
(* FACT --- perform a collect operator from a list 
appended by two lists is same of perform a collect opeartor on them individually *)    
lemma [simp] : "collectPlus valList (IVar p) (PEAs (As (IVar p) as) []) = []"
proof (induct valList)
case Nil
then show ?case by simp
next
case (Cons a valList)
then show ?case by simp
qed


(*
fun collectAux :: "val list \<Rightarrow> OCLexp \<Rightarrow> Enrollment \<Rightarrow> val list" where
"collectAux []  (As (IVar p) as.LECTURERS) en = []"
| "collectAux (v#vs)  (As (IVar p) col) e = 
(extCol v (transAs col) [e])
@(collectAux vs  (As (IVar p) col) e)"
*)

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
| "eval (MyOCL.CollectPlus src v body) om = collectPlus (eval src om) v (partialEval body om)"

fun translate :: "OCLexp \<Rightarrow> MySQL.exp" where
"translate (MyOCL.Int i) = MySQL.Int i" |
"translate (Att (IVar p) att) = MySQL.Col (transAtt att)"

end