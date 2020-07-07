theory ObjectModel
imports Main
begin

(* Person(id, age, email, students, lecturers) *)
datatype Person = P string int string "Person list" "Person list"

type_synonym persons = "Person list" 

datatype val =  VNULL | VInt int | VString string 
  |  VBool bool | VPerson Person | VList "val list"

fun appendList :: "val \<Rightarrow> val \<Rightarrow> val" where
"appendList VNULL v = v" |
"appendList v VNULL = VNULL" |
"appendList v (VList vs) = VList (v#vs)" |
"appendList _ _ = VNULL"

fun mapPersonsToVList :: "persons \<Rightarrow> val" where
"mapPersonsToVList Nil = VList Nil" |
"mapPersonsToVList (p#ps) = appendList (VPerson p) (mapPersonsToVList ps)"

fun isEmptyVList :: "val \<Rightarrow> bool" where 
"isEmptyVList (VList Nil) = True" |
"isEmptyVList _ = False"

fun equalVal :: "val \<Rightarrow> val \<Rightarrow> bool" where
"equalVal (VInt i1) (VInt i2) = (i1 = i2)" |
"equalVal (VBool b1) (VBool b2) = (b1 \<longleftrightarrow> b2)" |
"equalVal (VString s1) (VString s2) = (s1 = s2)" |
"equalVal (VPerson p1) (VPerson p2) = (p1 = p2)" |
"equalVal (VList Nil) (VList Nil) = True" |
"equalVal (VList (Cons v1 v1s)) (VList (Cons v2 v2s)) = 
(if (equalVal v1 v2) then (equalVal (VList v1s) (VList v2s)) else False)" |
"equalVal _ _ = False" 

fun countVList :: "val \<Rightarrow> int" where 
"countVList (VList Nil) = 0" |
"countVList (VList (v#vs)) = 1 + countVList (VList vs)" |
"countVList _ = 0"

end