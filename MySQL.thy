theory MySQL
  imports Main ObjectModel
begin

type_synonym var = string

datatype table = PERSON | ENROLLMENT
datatype col = AGE | EMAIL | ID | LECTURERS | STUDENTS

datatype exp = Int nat 
  | Var var 
  | Eq exp exp
  | GrtThan exp exp
  | And exp exp
  | Col col
  | Count col
  | CountAll

datatype whereClause = WHERE exp

datatype SQLstm = Select exp 
  | SelectFrom exp fromItem
  | SelectFromWhere exp fromItem whereClause 
and fromItem = Table table 

fun getAssociationEnd :: "col \<Rightarrow> Enrollment \<Rightarrow> string" where
"getAssociationEnd STUDENTS (E students lecturers) = students"
  | "getAssociationEnd LECTURERS (E students lecturers) = lecturers"

fun projVal :: "exp \<Rightarrow> val \<Rightarrow> val" where 
"projVal exp VNULL = VNULL"
| "projVal (Col AGE) (VPerson (P pid page pemail)) = VInt page"
| "projVal (Col EMAIL) (VPerson (P pid page pemail)) = VString pemail"
| "projVal (Col ID) (VPerson (P pid page pemail)) = VString pid"
| "projVal (Col STUDENTS) (VEnrollment v) = VString (getAssociationEnd STUDENTS v)" 
| "projVal (Col LECTURERS) (VEnrollment v) = VString (getAssociationEnd LECTURERS v)"

fun projValList :: "exp \<Rightarrow> val list \<Rightarrow> val list" where
"projValList exp Nil = Nil"
| "projValList exp (v#vs) = (projVal exp v)#(projValList exp vs)"

fun extPerson :: "var \<Rightarrow> Person list \<Rightarrow> val" where
"extPerson v [] = VNULL"
| "extPerson v (p#ps) = (if (isIdPerson v p) 
    then (VPerson p)
    else extPerson v ps)"

fun opposite :: "col \<Rightarrow> col" where
"opposite STUDENTS = LECTURERS"
  | "opposite LECTURERS = STUDENTS"

(* extCol returns VList of elements standing in column col such that
v stands in the column opposite to col *)
fun extCol :: "var \<Rightarrow> col \<Rightarrow> Enrollment list \<Rightarrow> val list" where
"extCol v col Nil = Nil" 
  | "extCol v col (e#es) = (if ((getAssociationEnd (opposite col) e) = v)
    then (VString (getAssociationEnd col e))#(extCol v col es)
    else extCol v col es)"

(* extEnrollment returns VList of enrollments such that
v stands in the column col *)
fun extEnrollments :: "var \<Rightarrow> col \<Rightarrow> Enrollment list \<Rightarrow> val list" where
"extEnrollments v col Nil = Nil" 
  | "extEnrollments v col (e#es) = (if ((getAssociationEnd col e) = v) 
    then (VEnrollment e)#(extEnrollments v col es) 
    else extEnrollments v col es)"

(* select takes a list of val [context] and for element
executes the expression *)
fun select :: "val \<Rightarrow> exp \<Rightarrow> val" where
"select val (MySQL.Int i) = VInt i"
| "select val (MySQL.Var v) = VString v"
| "select val (Col col) = projVal (Col col) val"
| "select val (Eq e1 e2) = VBool (equalVal (select val e1) (select val e2))"
| "select val (GrtThan e1 e2) = VBool (greaterThanVal (select val e1) (select val e2))"
| "select val (And e1 e2) = VBool (andVal (select val e1) (select val e2))"

fun filterEnrollments :: "exp \<Rightarrow> Enrollment list \<Rightarrow> val list" where
"filterEnrollments exp Nil = Nil"
| "filterEnrollments exp (e#es) = (if (isTrueVal (select (VEnrollment e) exp)) 
  then ((VEnrollment e)#(filterEnrollments exp es)) 
  else (filterEnrollments exp es))"

fun selectNoCtx :: "exp \<Rightarrow> val list" where
"selectNoCtx (MySQL.Int i) = [VInt i]"
| "selectNoCtx (MySQL.Var v) = [VString v]"
| "selectNoCtx (MySQL.Eq e1 e2) = [VBool (equalVal (VList (selectNoCtx e1)) (VList (selectNoCtx e2)))]"

fun selectList :: "val list \<Rightarrow> exp \<Rightarrow> val list" where
(* to be completed if needed: count and countAll is not the same in reality: null case *)
"selectList vs (Count col) = [VInt (sizeValList vs)]"
| "selectList vs (Eq (Count col) (MySQL.Int i)) = [VBool (equalVal (VInt (sizeValList vs)) (VInt i))]"
| "selectList vs (GrtThan (Count col) (MySQL.Int i)) = [VBool (greaterThanVal (VInt (sizeValList vs)) (VInt i))]"
| "selectList vs (CountAll) =  [VInt (sizeValList vs)]"
| "selectList vs (Eq (CountAll) (MySQL.Int i)) = [VBool (equalVal (VInt (sizeValList vs)) (VInt i))]"
| "selectList vs (GrtThan (CountAll) (MySQL.Int i)) = [VBool (greaterThanVal (VInt (sizeValList vs)) (VInt i))]"
| "selectList Nil (MySQL.Int i) = Nil"
| "selectList (v#vs) (MySQL.Int i) = (select v (MySQL.Int i)) # (selectList vs (MySQL.Int i))"
| "selectList Nil (MySQL.Var var) = Nil"
| "selectList (v#vs) (MySQL.Var var) = (select v (MySQL.Var var)) # (selectList vs (MySQL.Var var))"
| "selectList Nil (Eq e1 e2) = Nil"
| "selectList (v#vs) (Eq e1 e2) = (select v (Eq e1 e2)) # (selectList vs (Eq e1 e2))"
| "selectList Nil (GrtThan e1 e2) = Nil"
| "selectList (v#vs) (GrtThan e1 e2) = (select v (GrtThan e1 e2)) # (selectList vs (GrtThan e1 e2))"
| "selectList Nil (And e1 e2) = Nil"
| "selectList (v#vs) (And e1 e2) = (select v (And e1 e2)) # (selectList vs (And e1 e2))"
| "selectList Nil (Col col) = Nil"
| "selectList (v#vs) (Col col) = (select v (Col col)) # (selectList vs (Col col))"

(* for the time being, this filterWhere only takes 
either a "table Person" or a "table Enrollment" as an input *)
fun filterWhere :: "val list \<Rightarrow> whereClause \<Rightarrow> val list" where
"filterWhere Nil (WHERE (Eq e1 e2)) =  Nil"
| "filterWhere [TPerson om] (WHERE (Eq (Col ID) (Var var)))
= [extPerson var (getPersonList om)]"
| "filterWhere [TEnrollment om] (WHERE (Eq (Col col) (Var var)))
= extEnrollments var col (getEnrollmentList om)"
| "filterWhere [TEnrollment om] (WHERE (And e1 e2))
= filterEnrollments (And e1 e2) (getEnrollmentList om)"
(*
| "filterWhere (Cons v vs) (WHERE e) = (if (isTrueVal (select v e))  
    then (v#(filterWhere vs (WHERE e)))   
    else filterWhere vs (WHERE e))"
*)

fun execFrom :: "fromItem \<Rightarrow> Objectmodel \<Rightarrow> val list" where
"execFrom (Table PERSON) om  = [TPerson om]"
| "execFrom (Table ENROLLMENT) om = [TEnrollment om]" 

fun exec :: "SQLstm \<Rightarrow> Objectmodel \<Rightarrow> val list" where
"exec (Select selitems) om  = selectNoCtx selitems"
| "exec (SelectFrom exp fromItem) om 
    = selectList (execFrom fromItem om) exp"
| "exec (SelectFromWhere exp fromItem whereExp) om
    = selectList (filterWhere (execFrom fromItem om) whereExp) exp"

end