theory OCLtoSQL
imports Main MySQL MyOCL
begin

fun transAtt :: "MyOCL.att \<Rightarrow> MySQL.col" where
"transAtt MyOCL.AGE = MySQL.AGE" |
"transAtt MyOCL.EMAIL = MySQL.EMAIL"

fun transAs :: "MyOCL.as \<Rightarrow> MySQL.col" where
"transAs MyOCL.STUDENTS = MySQL.STUDENTS" |
"transAs MyOCL.LECTURERS = MySQL.LECTURERS"

fun getPersonFromVal :: "val \<Rightarrow> Person" where
"getPersonFromVal (VPerson p) = p"

fun getPersonListFromValList :: "val list \<Rightarrow> Person list" where
"getPersonListFromValList [] = []"
| "getPersonListFromValList (v#vs) = (getPersonFromVal v)#(getPersonListFromValList vs)"

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

end