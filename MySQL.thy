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

fun isID :: "col \<Rightarrow> table \<Rightarrow> bool" where
"isID ID PERSON = True "
  | "isID _ _ = False"

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
"isAssociation v STUDENTS e = ((getAssociationEnd STUDENTS e) = v)" 
  | "isAssociation v LECTURERS e = ((getAssociationEnd LECTURERS e) = v)" 
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
fun extEnrollments :: "var \<Rightarrow> col \<Rightarrow> Enrollment list \<Rightarrow> val list" where
"extEnrollments v col Nil = Nil" 
  | "extEnrollments v col (e#es) = (if isAssociation v col e 
    then (VEnrollment e)#(extEnrollments v col es) 
    else extEnrollments v col es)"

(* select takes a list of val [context] and for element
executes the expression *)
fun select :: "val \<Rightarrow> exp \<Rightarrow> val" where
"select val (MySQL.Int i) = VInt i"
| "select val (MySQL.Var v) = VString v"
| "select val (Col col) = proj (Col col) val"
| "select val (Eq e1 e2) = VBool (equalVal (select val e1) (select val e2))"
| "select val (GrtThan e1 e2) = VBool (greaterThanVal (select val e1) (select val e2))"
| "select val (And e1 e2) = VBool (andVal (select val e1) (select val e2))"

fun selectNoCtx :: "exp \<Rightarrow> val list" where
"selectNoCtx (MySQL.Int i) = [VInt i]"
| "selectNoCtx (MySQL.Var v) = [VString v]"
| "selectNoCtx (MySQL.Eq e1 e2) = [VBool (equalVal (VList (selectNoCtx e1)) (VList (selectNoCtx e2)))]"

fun sucVal :: "val list \<Rightarrow> val list" where
"sucVal [VInt i] = [VInt (Suc i)]"

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
| "selectList Nil (Eq e1 e2) = [VBool (equalValList (selectList Nil e1) (selectList Nil e2))]"
| "selectList (v#vs) (Eq e1 e2) = (select v (Eq e1 e2)) # (selectList vs (Eq e1 e2))"
| "selectList Nil (GrtThan e1 e2) = [VBool (greaterThanValList (selectList Nil e1) (selectList Nil e2))]"
| "selectList (v#vs) (GrtThan e1 e2) = (select v (GrtThan e1 e2)) # (selectList vs (GrtThan e1 e2))"
| "selectList Nil (And e1 e2) = [VBool (andValList (selectList Nil e1) (selectList Nil e2))]"
| "selectList (v#vs) (And e1 e2) = (select v (And e1 e2)) # (selectList vs (And e1 e2))"
| "selectList Nil (Col col) = Nil"
| "selectList (v#vs) (Col col) = (select v (Col col)) # (selectList vs (Col col))"

fun filterWhere :: "val list \<Rightarrow> whereClause \<Rightarrow> val list" where
"filterWhere Nil (WHERE (Eq e1 e2)) =  Nil" 
| "filterWhere (Cons v vs) (WHERE e) = (if (isTrueVal (select v e))  
    then (v#(filterWhere vs (WHERE e)))   
    else filterWhere vs (WHERE e))"

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