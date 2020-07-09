theory ObjectModel
imports Main
begin

(* Person(id, age, email, students, lecturers) *)
datatype Person = P string nat string | PNULL

(* Enrollment (students, lecturers) *)
datatype Enrollment = E string string

datatype Objectmodel = OM "Person list" "Enrollment list"

datatype val =  VNULL | VInt nat | VString string | VBool bool 
  | VPerson Person | VEnrollment Enrollment 
  | VList "val list"
  | TPerson Objectmodel
  | TEnrollment Objectmodel

fun isIdPerson :: "string \<Rightarrow> Person \<Rightarrow> bool" where
"isIdPerson v (P pid page pemail) = (v = pid)" |
"isIdPerson v PNULL = False"

fun getPersonFromId :: "string \<Rightarrow> Person list \<Rightarrow> Person" where
"getPersonFromId s [] = PNULL" |
"getPersonFromId s (p#ps) = (if isIdPerson s p then p else (getPersonFromId s ps))"

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
"equalVal (VInt i1) (VInt i2) = (i1 = i2)" |
"equalVal (VBool b1) (VBool b2) = (b1 \<longleftrightarrow> b2)" |
"equalVal (VString s1) (VString s2) = (s1 = s2)" |
"equalVal (VPerson p1) (VPerson p2) = (p1 = p2)" |
"equalVal (VList []) (VList []) = True" |
"equalVal (VList (v1#v1s)) (VList (v2#v2s)) = 
(if (equalVal v1 v2) then (equalVal (VList v1s) (VList v2s)) else False)"

fun greaterThanVal :: "val \<Rightarrow> val \<Rightarrow> bool" where
"greaterThanVal (VInt i1) (VInt i2) = (i1 > i2)" |
"greaterThanVal (VList []) (VList []) = True" |
"greaterThanVal (VList (v1#v1s)) (VList (v2#v2s)) = 
(if (greaterThanVal v1 v2) then (greaterThanVal (VList v1s) (VList v2s)) else False)"

fun andVal :: "val \<Rightarrow> val \<Rightarrow> bool" where
"andVal (VBool b1) (VBool b2) = (b1 \<and> b2)"
| "andVal (VList []) (VList []) = True" 
| "andVal (VList (v1#v1s)) (VList (v2#v2s)) = ((andVal v1 v2) \<and> (andVal (VList v1s) (VList v2s)))"

fun countValList :: "val list \<Rightarrow> int" where 
"countValList [] = 0" |
"countValList (v#vs) = 1 + countValList vs"

fun appendList :: "val \<Rightarrow> val \<Rightarrow> val" where
"appendList VNULL v = v" |
"appendList v VNULL = VList [v]" |
"appendList v (VList vs) = VList (v#vs)"

appendList VEnrollment vs = Cons Vernol (VList vs)
appendList (VList v) vs vs2 = cons (Vlist v) appendList (vs, vs2_)

fun sizeValList :: "val list\<Rightarrow> nat" where
"sizeValList [] = 0" |
"sizeValList (x#xs) = Suc (sizeValList xs)"

fun sizeVal :: "val \<Rightarrow> nat" where
"sizeVal VNULL = 0" |
"sizeVal (VList []) = 0" |
"sizeVal (VList (x#xs)) = Suc (sizeVal (VList xs))"

fun isEmptyVal :: "val \<Rightarrow> bool" where
"isEmptyVal v = (sizeVal v = 0)"

fun isTrue :: "val \<Rightarrow> bool" where
"isTrue (VList [VBool (True)]) = True"

end