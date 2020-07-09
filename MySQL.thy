theory MySQL
  imports Main ObjectModel
begin

type_synonym var = string

datatype table = PERSON | ENROLLMENT
datatype col = AGE | EMAIL | ID | LECTURERS | STUDENTS

datatype exp = Int nat 
  | Var var 
  | Eq exp exp
  | AggEq exp exp
  | GrtThan exp exp
  | AggGrtThan exp exp
  | And exp exp
  | Col col
  | Count col
  | CountAll

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

(* TBC *)
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

fun projList :: "exp \<Rightarrow> val \<Rightarrow> val" where
"projList exp (VList Nil) = (VList Nil)"
| "projList exp (VList (v#vs)) = appendList (proj exp v) (projList exp (VList vs))"
| "projList exp val = proj exp val"

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
    then (VEnrollment e)#(extEnrollment v col es) 
    else extEnrollment v col es)"

(* select takes a list of val [context] and for element
executes the expression *)
fun select :: "val \<Rightarrow> exp \<Rightarrow> val list" where
"select val (Col col) = [proj (Col col) val]"
  | "select val (Eq e1 e2) = [VBool (equalVal (VList (select val e1)) (VList (select val e2)))]"
  | "select val (And e1 e2) = [VBool (andVal (VList (select val e1)) (VList (select val e2)))]"

fun selectList :: "val \<Rightarrow> exp \<Rightarrow> val list" where
"selectList (VList vs) (Count col) = [VInt (sizeValList (VList (selectList (VList vs) (Col col))))]"
| "selectList (VList vs) CountAll = [VInt (sizeValList (VList vs))]"
| "selectList (VList vs) (AggEq (Count col) (MySQL.Int i)) 
= [VBool (equalVal (VList (selectList (VList vs) (Count col))) (VList [VInt i]))]"
| "selectList (VList vs) (AggEq (CountAll) (MySQL.Int i)) 
= [VBool (equalVal (VList (selectList (VList vs) (CountAll))) (VList [VInt i]))]"
| "selectList (VList Nil) exp = Nil"
| "selectList (VList (v#vs)) exp = (select v exp) @ (selectList (VList vs) exp)"

fun filterWhere :: "val \<Rightarrow> whereClause \<Rightarrow> val" where
"filterWhere (VList Nil) (WHERE (Eq e1 e2)) = VList Nil" 
| "filterWhere (VList (Cons v vs)) (WHERE e) = (if (isTrue (VList (select v e)))  
    then (appendList v (filterWhere (VList vs) (WHERE e)))   
    else filterWhere (VList vs) (WHERE e))"

fun exec :: "SQLstm \<Rightarrow> Objectmodel \<Rightarrow> val" where
"exec (Select selitems) om  = VList (select VNULL selitems)"
  | "exec (SelectFrom exp fromItem) om 
    = VList (select (execFrom fromItem om) exp)" 
  | "exec (SelectFromWhere (Count col) fromItem whereExp) om
    = VList [VInt (sizeValList (VList (select (filterWhere (execFrom fromItem om) whereExp) (Col col))))]" 
(* SelectFromWhere is simplified to select with the fromitem filtered out by where *)
  | "exec (SelectFromWhere exp fromItem whereExp) om
    = VList (selectList (filterWhere (execFrom fromItem om) whereExp) exp)"


end