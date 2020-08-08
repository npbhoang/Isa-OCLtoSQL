theory ObjectModel
imports Main
begin

datatype Person = P string nat string
  | PNULL
  
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

fun sizeList :: "'a list \<Rightarrow> nat" where 
"sizeList [] = 0" |
"sizeList (v#vs) = Suc (sizeList vs)"

fun getAssignedPerson :: "string \<Rightarrow> Person list \<Rightarrow> Person" where
"getAssignedPerson s [] = Person.PNULL"
| "getAssignedPerson s (p#ps) = (if ((getIdPerson p) = s) then p else (getAssignedPerson s ps))"
end