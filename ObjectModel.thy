theory ObjectModel
imports Main
begin

(* Person (age, email) *)
datatype Person = P string nat string
  | PNULL (* An invalid Person *)
  
(* Enrollment (students, lecturers) *)
datatype Enrollment = E Person Person

datatype Objectmodel = OM "Person list" "Enrollment list"

datatype val =  VNULL 
  | VID Person
  | VInt nat 
  | VString string 
  | VBool bool 
  | VPerson Person 
  | VEnrollment Enrollment 
  | VList "val list"
  | TPerson Objectmodel
  | TEnrollment Objectmodel
  | VObj string
  | VIVar string
  | VJoin "val list"


fun getPersonList :: "Objectmodel \<Rightarrow> Person list" where
"getPersonList (OM ps es) = ps"

fun getEnrollmentList :: "Objectmodel \<Rightarrow> Enrollment list" where
"getEnrollmentList (OM ps es) = es"

(*
fun mapEnrollmentToValList :: "Enrollment list \<Rightarrow> val list" where
"mapEnrollmentToValList [] = []" |
"mapEnrollmentToValList (e#es) = (VEnrollment e)#(mapEnrollmentToValList es)"


*)

fun equalVal :: "val \<Rightarrow> val \<Rightarrow> bool" where
"equalVal v1 v2 = (v1 = v2)"


fun equalValList :: "val list \<Rightarrow> val list \<Rightarrow> bool"
where
"equalValList Nil Nil = True"
| "equalValList Nil e2 = False"
| "equalValList e1 Nil = False"
| "equalValList (e1#e1s) (e2#e2s) = ((equalVal e1 e2) \<and> (equalValList e1s e2s))"


fun getIdPerson :: "Person \<Rightarrow> string" where
"getIdPerson (P pid page pemail) = pid"
| "getIdPerson PNULL = undefined"

fun getAgePerson :: "Person \<Rightarrow> nat" where
"getAgePerson (P pid age email) = age"
| "getAgePerson PNULL = undefined"

fun getEmailPerson :: "Person \<Rightarrow> string" where
"getEmailPerson (P pid age email) = email"
| "getEmailPerson PNULL = undefined"

(*
fun greaterThanVal :: "val \<Rightarrow> val \<Rightarrow> bool" where
 "greaterThanVal (VInt i1) (VInt i2) = (i1 > i2)" 

fun greaterThanValList :: "val list \<Rightarrow> val list \<Rightarrow> bool"
where
"greaterThanValList Nil Nil = False"
| "greaterThanValList Nil e2 = False"
| "greaterThanValList e1 Nil = False"
| "greaterThanValList (e1#e1s) (e2#e2s) = 
(if (greaterThanVal e1 e2) 
then (greaterThanValList e1s e2s) else False)"

fun andVal :: "val \<Rightarrow> val \<Rightarrow> bool" where
"andVal (VBool b1) (VBool b2) = (b1 \<and> b2)"

fun andValList :: "val list \<Rightarrow> val list \<Rightarrow> bool" where
"andValList Nil Nil = False"
| "andValList Nil v2s = False"
| "andValList e1s Nil = False"
| "andValList (e1#e1s) (e2#e2s) = ((andVal e1 e2) \<and> (andValList e1s e2s))"

fun countValList :: "val list \<Rightarrow> int" where 
"countValList [] = 0" |
"countValList (v#vs) = 1 + countValList vs"

*)
fun sizeList :: "'a list \<Rightarrow> nat" where 
"sizeList [] = 0" |
"sizeList (v#vs) = Suc (sizeList vs)"
(*
fun sizeVal :: "val \<Rightarrow> nat" where
"sizeVal VNULL = 0" |
"sizeVal (VList vs) = sizeValList vs"

fun isEmptyValList :: "val list \<Rightarrow> bool" where
"isEmptyValList xs = ((sizeValList xs) = 0)"

fun isEmptyVal :: "val \<Rightarrow> bool" where
"isEmptyVal (VList []) = True"
| "isEmptyVal (VList (a#ls)) = False"

COMMENT *)

fun getAssignedPerson :: "string \<Rightarrow> Person list \<Rightarrow> Person" where
"getAssignedPerson s [] = Person.PNULL"
| "getAssignedPerson s (p#ps) = (if ((getIdPerson p) = s) then p else (getAssignedPerson s ps))"
end