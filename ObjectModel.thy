theory ObjectModel
imports Main
begin

(* Person(age, email) *)
datatype Person = P nat string | PNULL

(* Enrollment (students, lecturers) *)
datatype Enrollment = E Person Person

datatype Objectmodel = OM "Person list" "Enrollment list"

datatype val =  VNULL 
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

fun mapPersonListToValList :: "Person list \<Rightarrow> val list" where
"mapPersonListToValList [] = []" |
"mapPersonListToValList (p#ps) = (VPerson p)#(mapPersonListToValList ps)"

fun mapEnrollmentToValList :: "Enrollment list \<Rightarrow> val list" where
"mapEnrollmentToValList [] = []" |
"mapEnrollmentToValList (e#es) = (VEnrollment e)#(mapEnrollmentToValList es)"

fun equalVal :: "val \<Rightarrow> val \<Rightarrow> bool" where
"equalVal v1 v2 = (v1 = v2)"

fun equalValList :: "val list \<Rightarrow> val list \<Rightarrow> bool"
where
"equalValList Nil Nil = True"
| "equalValList Nil e2 = False"
| "equalValList e1 Nil = False"
| "equalValList (e1#e1s) (e2#e2s) = ((equalVal e1 e2) \<and> (equalValList e1s e2s))"

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

fun sizeValList :: "val list\<Rightarrow> nat" where
"sizeValList [] = 0" |
"sizeValList (x#xs) = Suc (sizeValList xs)"

fun sizeVal :: "val \<Rightarrow> nat" where
"sizeVal VNULL = 0" |
"sizeVal (VList vs) = sizeValList vs"

fun isEmptyValList :: "val list \<Rightarrow> bool" where
"isEmptyValList xs = ((sizeValList xs) = 0)"

fun isEmptyVal :: "val \<Rightarrow> bool" where
"isEmptyVal (VList []) = True"
| "isEmptyVal (VList (a#ls)) = False"

fun isTrueVal :: "val \<Rightarrow> bool" where
"isTrueVal (VBool val) = val"

end