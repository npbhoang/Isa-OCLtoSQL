theory MySQL
  imports Main ObjectModel
begin

type_synonym var = string

datatype table = PERSON | ENROLLMENT
datatype col = AGE | EMAIL | ID | LECTURERS | STUDENTS

datatype exp = Int nat 
  | Var var 
  | Eq exp exp
  | Col col
  | Count col

datatype whereClause = WHERE exp

datatype SQLstm = Select exp 
  | SelectFrom exp fromItem
  | SelectFromWhere exp fromItem whereClause 
and fromItem = Table table 
  | Subselect SQLstm

fun isID :: "col \<Rightarrow> table \<Rightarrow> bool" where
"isID ID PERSON = True "
  | "isID _ _ = False"

fun execFrom :: "fromItem \<Rightarrow> Objectmodel \<Rightarrow> val" where
"execFrom (Table PERSON) om  = TPerson om"
  | "execFrom (Table ENROLLMENT) om = TEnrollment om" 
  | "execFrom (Subselect _) ps = VNULL"

fun sat :: "val \<Rightarrow> exp \<Rightarrow> bool" where
"sat v e = True"

fun getAssociationEnd :: "col \<Rightarrow> Enrollment \<Rightarrow> string" where
"getAssociationEnd STUDENTS (E students lecturers) = students"
  | "getAssociationEnd LECTURERS (E students lecturers) = lecturers"

fun proj :: "exp \<Rightarrow> val \<Rightarrow> val" where 
"proj (Col AGE) (VPerson (P pid page pemail)) = VInt page"
  | "proj (Col EMAIL) (VPerson (P pid page pemail)) = VString pemail"
  | "proj (Col ID) (VPerson (P pid page pemail)) = VString pid"
  | "proj (MySQL.Int i) v = VInt i"
  | "proj (MySQL.Col col) VNULL = VNULL"
  | "proj (Var var) v = VString var" 
  | "proj (Eq e1 e2) v = VBool (equalVal (proj e1 v) (proj e2 v))" 
  | "proj (Col STUDENTS) (VEnrollment v) = VString (getAssociationEnd STUDENTS v)" 
  | "proj (Col LECTURERS) (VEnrollment v) = VString (getAssociationEnd LECTURERS v)"

fun ext :: "var \<Rightarrow> col \<Rightarrow> Person list \<Rightarrow> val" where
"ext v col [] = VNULL"
  | "ext v col (p#ps) = (if (isIdPerson v p) 
    then (proj (Col col) (VPerson p)) 
    else (ext v col ps))"

fun extElement :: "var \<Rightarrow> Person list \<Rightarrow> val" where
"extElement v [] = VNULL"
  | "extElement v (p#ps) = (if (isIdPerson v p) 
    then (VPerson p)
    else extElement v ps)"

fun isAssociation :: "var \<Rightarrow> col \<Rightarrow> Enrollment \<Rightarrow> bool" where
"isAssociation v STUDENTS (E students lecturers) = (students = v)" 
  | "isAssociation v LECTURERS (E students lecturers) = (lecturers = v)" 
  | "isAssociation v col _ = False"

fun opposite :: "col \<Rightarrow> col" where
"opposite STUDENTS = LECTURERS"
  | "opposite LECTURERS = STUDENTS"

(* extCol returns VList of elements standing in column col such that
v stands in the column opposite to col *)
fun extCol :: "var \<Rightarrow> col \<Rightarrow> Enrollment list \<Rightarrow> val list" where
"extCol v col Nil = Nil" 
  | "extCol v col (e#es) = (if isAssociation v (opposite col) e 
    then (VString (getAssociationEnd col e))#(extCol v col es)
    else extCol v col es)"

(* extEnrollment returns VList of enrollments such that
v stands in the column col *)
fun extEnrollment :: "var \<Rightarrow> col \<Rightarrow> Enrollment list \<Rightarrow> val list" where
"extEnrollment v col Nil = Nil" 
  | "extEnrollment v col (e#es) = (if isAssociation v col e 
    then  (VEnrollment e)#(extEnrollment v col es) 
    else extEnrollment v col es)"

fun filterWhere :: "val \<Rightarrow> whereClause \<Rightarrow> val" where
"filterWhere (VList Nil) (WHERE e) = VList Nil" 
  | "filterWhere (VList (Cons v vs)) (WHERE e) = (if sat v e 
    then (appendList v (filterWhere (VList vs) (WHERE e)))   
    else filterWhere (VList vs) (WHERE e))"

fun select :: "val \<Rightarrow> exp \<Rightarrow> val list" where
"select VNULL (MySQL.Int i) = [VInt i]" 
  | "select VNULL (MySQL.Var var) = [VString var]" 
  | "select VNULL (MySQL.Eq e1 e2) = 
    [VBool (equalVal (VList (select VNULL e1)) (VList (select VNULL e2)))]" 
  | "select VNULL (Col col) = [VNULL]"
  | "select val (Count col) = [VInt (sizeValList val)]"
  | "select (VList Nil) exp = Nil" 
  | "select (VList (v#vs)) exp = 
    (proj exp v) # (select (VList vs) exp)"

fun exec :: "SQLstm \<Rightarrow> Objectmodel \<Rightarrow> val" where
"exec (Select selitems) ps  = VList (select VNULL selitems)"
  | "exec (SelectFrom (Count col) fromItem) ps
    = VList [VInt (sizeValList (VList (select (execFrom fromItem ps) (Col col))))]" 
  | "exec (SelectFrom exp fromItem) ps 
    = VList (select (execFrom fromItem ps) exp)" 
  | "exec (SelectFromWhere (Count col) fromItem whereExp) ps
    = VList [VInt (sizeValList (VList (select (filterWhere (execFrom fromItem ps) whereExp) (Col col))))]" 
  | "exec (SelectFromWhere exp fromItem whereExp) ps
    = VList (select (filterWhere (execFrom fromItem ps) whereExp) exp)"

end