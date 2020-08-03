theory OCLtoSQL
imports Main MySQL MyOCL
begin

fun transAtt :: "MyOCL.att \<Rightarrow> MySQL.col" where
"transAtt MyOCL.AGE = MySQL.AGE" |
"transAtt MyOCL.EMAIL = MySQL.EMAIL"

fun transAs :: "MyOCL.as \<Rightarrow> MySQL.col" where
"transAs MyOCL.STUDENTS = MySQL.STUDENTS" |
"transAs MyOCL.LECTURERS = MySQL.LECTURERS"
(* COMMENT
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

*)

fun getPersonFromVal :: "val \<Rightarrow> Person" where
"getPersonFromVal (VPerson p) = p"

fun getPersonListFromValList :: "val list \<Rightarrow> Person list" where
"getPersonListFromValList [] = []"
| "getPersonListFromValList (v#vs) = (getPersonFromVal v)#(getPersonListFromValList vs)"

(*projValAs as (VPerson (getAssignedPerson v (getPersonList om))) (getEnrollmentList om)*)

fun addValIntoVList :: "val \<Rightarrow> val \<Rightarrow> val" where
"addValIntoVList v (VList vs) = VList (v#vs)"

fun evalForValue :: "Person \<Rightarrow> OCLexp \<Rightarrow> val" where
"evalForValue p (IVar l) = (VPerson p)"
| "evalForValue p (PEVar var ps) = (VPerson (getAssignedPerson var ps))"
| "evalForValue p (PEAtt (Att l att.AGE)) = 
VInt (getAgePerson (getPersonFromVal (evalForValue p l)))"
| "evalForValue p (OCLexp.Int i) = (VInt i)"
| "evalForValue p (PEAs (As l as) es)
= VList (projValAs as (evalForValue p l) es)"

(*
lemma lem2: "evalForValue p (PEAs (As l as.LECTURERS) (e#es))
= (if ((getAssociationEnd as.STUDENTS e) = p) 
then (addValIntoVList (VPerson (getAssociationEnd as.LECTURERS e)) (evalForValue p (PEAs (As l as.LECTURERS) es))) 
else (evalForValue p (PEAs (As l as.LECTURERS) es)))"
sorry
*)

fun isUnique :: "Person \<Rightarrow> Person list \<Rightarrow> bool" where
"isUnique v [] = True"
| "isUnique v (v1#vs) = (\<not>(v=v1) \<and> (isUnique v vs))"

fun validPersonList :: "Person list \<Rightarrow> bool" where
"validPersonList [] = True"
| "validPersonList (v#vs) = ((isUnique v vs) \<and> (validPersonList vs))"

fun isPersonInPersonList :: "Person \<Rightarrow> Person list => bool" where
"isPersonInPersonList p [] = False"
| "isPersonInPersonList v (v1#vs) =  (if (v = v1) then True else (isPersonInPersonList v vs))"



fun isEnrollmentInPersonList :: "Enrollment \<Rightarrow> Person list \<Rightarrow> bool" where
"isEnrollmentInPersonList e ps = 
((isPersonInPersonList (getAssociationEnd as.STUDENTS e) ps) \<and>
(isPersonInPersonList (getAssociationEnd as.LECTURERS e) ps))"


fun validEnrollmentList :: "Enrollment list \<Rightarrow> Person list \<Rightarrow> bool" where
"validEnrollmentList [] ps = True"
| "validEnrollmentList (e#es) ps = ((isEnrollmentInPersonList e ps) \<and> (validEnrollmentList es ps))"


fun collectAuxMin :: "val \<Rightarrow> as \<Rightarrow> Enrollment list \<Rightarrow> val list" where
"collectAuxMin v as.LECTURERS [] = []"
| "collectAuxMin v as.LECTURERS (e#es) =
(if (getAssociationEnd as.STUDENTS e) = (getPersonFromVal v)
then [(VPerson (getAssociationEnd as.LECTURERS e))]
else (collectAuxMin v as.LECTURERS es))"

fun collectAux :: "val \<Rightarrow> OCLexp \<Rightarrow> val list" where
"collectAux v (PEAs (As (IVar p) as.LECTURERS) es) = collectAuxMin v as.LECTURERS es"

(*"collectAux v  (PEAs (As (IVar p) as.LECTURERS) []) = []"
| "collectAux v  (PEAs (As (IVar p) as.LECTURERS) (e#es))
= collectAuxMin v e as.LECTURERS @ (collectAux v  (PEAs (As (IVar p) as.LECTURERS) es))"
*)
(* "collectAux v ivar (PEAs (As (IVar p) as.LECTURERS) [e]) =
(if ((getAssociationEnd as.STUDENTS e) = (getPersonFromVal v)) then 
[(VPerson (getAssociationEnd as.LECTURERS e))]
else [])"
*)

fun collectPlus :: "val list \<Rightarrow> OCLexp \<Rightarrow> OCLexp \<Rightarrow> val list" where
"collectPlus [] ivar exp = []"           
| "collectPlus (val#vs) ivar exp = (collectAux val exp)@(collectPlus vs ivar exp)"

(*
(flatten (evalForValue (getPersonFromVal val) exp)) @ (collectPlus vs ivar exp) "
*)
(*
lemma [simp]: "OCLtoSQL.isUnique p (getPersonListFromValList source) \<Longrightarrow>
    getAssociationEnd as.STUDENTS e = p \<Longrightarrow> 
collectAux source ivar (PEAs (As (IVar i) as.LECTURERS) [e]) = []"
  sorry
*)

(*
lemma lemaaux: "collectPlus source ivar (PEAs (As (IVar p) as.LECTURERS) (e#es))
= (collectPlus source ivar (PEAs (As (IVar p) as.LECTURERS) es))@(collectAux source ivar (PEAs (As (IVar p) as.LECTURERS) [e]))"
  proof (induct source)
    case Nil
    then show ?case by simp
  next
    case (Cons a source)
    then show ?case 
      sorry
  qed
*)

fun isVPersonSatisfied :: "Person \<Rightarrow> OCLexp \<Rightarrow> bool" where
"isVPersonSatisfied p (OCLexp.Eq l r)
= ((evalForValue p l) = (evalForValue p r))" 

fun isValSatisfied :: "val \<Rightarrow> OCLexp \<Rightarrow> bool" where
"isValSatisfied (VPerson p) exp = isVPersonSatisfied p exp"

fun filterSourceWithBody :: "val list \<Rightarrow> OCLexp \<Rightarrow> OCLexp \<Rightarrow> val list" where
"filterSourceWithBody [] (IVar l) (bodyExp) = []"
| "filterSourceWithBody (v#vs) (IVar l) exp = 
(if (isValSatisfied v exp) 
then (v#(filterSourceWithBody vs (IVar l) exp)) 
else (filterSourceWithBody vs (IVar l) exp))"

fun mapPersonToVal :: "Person \<Rightarrow> val" where
"mapPersonToVal p = VPerson p"

fun mapPersonListToValList :: "Person list \<Rightarrow> val list" where
"mapPersonListToValList [] = []"
| "mapPersonListToValList (p#ps) = (mapPersonToVal p)#(mapPersonListToValList ps)"

fun collectAuxButReturnVal :: "val \<Rightarrow> OCLexp \<Rightarrow> val" where
"collectAuxButReturnVal VNULL oclexp = VNULL"

fun collect :: "val list \<Rightarrow> OCLexp \<Rightarrow> OCLexp \<Rightarrow> val list" where
"collect [] ivar exp = []"           
| "collect (val#vs) ivar exp = (collectAuxButReturnVal val exp)#(collect vs ivar exp)"

lemma [simp]: "collect (xs@ys) ivar exp = (collect xs ivar exp) @ (collect ys ivar exp)"
proof (induct xs)
case Nil
then show ?case by simp
next
case (Cons a xs)
then show ?case by simp
qed

fun eval :: "OCLexp \<Rightarrow> Objectmodel \<Rightarrow> val list" where
"eval (MyOCL.Int i) om = [VInt i]"
| "eval (MyOCL.Var x) om = [VObj x]"
| "eval (MyOCL.Eq e1 e2) om = [VBool (equalValList (eval e1 om) (eval e2 om))]" 
| "eval (MyOCL.Att (Var v) att) om = [(projValAtt att (VPerson (getAssignedPerson v (getPersonList om))))]"
| "eval (MyOCL.As (Var v) as) om = projValAs as (VPerson (getAssignedPerson v (getPersonList om))) (getEnrollmentList om)"
| "eval (MyOCL.Size exp) om = [VInt (size (eval exp om))]"
| "eval (MyOCL.IsEmpty exp) om = [VBool ((size (eval exp om)) = 0)]"
| "eval (MyOCL.Exists src v body) om = [VBool ((sizeList (filterSourceWithBody (eval src om) v (partialEval body om))) > 0)]"
| "eval (MyOCL.AllInstances PERSON) om = mapPersonListToValList (getPersonList om)"
| "eval (MyOCL.CollectPlus src v body) om = collectPlus (eval src om) v (partialEval body om)"
| "eval (MyOCL.Collect src v body) om = collect (eval src om) v (partialEval body om)"

end