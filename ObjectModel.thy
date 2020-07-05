theory ObjectModel
imports Main
begin

(* Person(id, age, email, students, lecturers) *)
datatype Person = P string int string "Person list" "Person list"
(* Enrollment(students, lecturers) *)
datatype Enrollment = E Person Person

type_synonym persons = "Person list" 

datatype val =  VInt int | VString string 
  |  VBool bool | VPerson Person | VList "val list"

fun appList :: "val \<Rightarrow> val \<Rightarrow> val" where
"appList v (VList vs) = VList (v#vs)"

fun mapList :: "Person list \<Rightarrow> val" where
"mapList Nil = VList []" |
"mapList (Cons p ps) = appList (VPerson p) (mapList ps)"

fun equalVal :: "val \<Rightarrow> val \<Rightarrow> bool" where
"equalVal (VInt i1) (VInt i2) = (i1 = i2)" |
"equalVal (VBool b1) (VBool b2) = (b1 \<longleftrightarrow> b2)" |
"equalVal (VString s1) (VString s2) = (s1 = s2)" |
"equalVal (VPerson p1) (VPerson p2) = (p1 = p2)" |
"equalVal (VList Nil) (VList Nil) = True" |
"equalVal (VList (Cons v1 v1s)) (VList (Cons v2 v2s)) = 
(if (equalVal v1 v2) then (equalVal (VList v1s) (VList v2s)) else False)" |
"equalVal _ _ = False" 

end