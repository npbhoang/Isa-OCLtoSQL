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

datatype fromItem = Table table

datatype SQLstm = Select exp 
  | SelectFrom exp fromItem
  | SelectFromWhere exp fromItem whereClause 


fun opposite :: "col \<Rightarrow> col" where
"opposite STUDENTS = LECTURERS"
  | "opposite LECTURERS = STUDENTS"


fun getAssociationEnd :: "col \<Rightarrow> Enrollment \<Rightarrow> val" where
"getAssociationEnd STUDENTS (E students lecturers) = (VString students)"
  | "getAssociationEnd LECTURERS (E students lecturers) = (VString lecturers)"

(* projVal: given a column-expression and a row --either in person or enrollment table--,
it returns the corresonding value *)

fun projVal :: "exp \<Rightarrow> val \<Rightarrow> val" where 
"projVal exp VNULL = VNULL"
| "projVal (Col AGE) (VPerson (P pid page pemail)) = VInt page"
| "projVal (Col EMAIL) (VPerson (P pid page pemail)) = VString pemail"
| "projVal (Col ID) (VPerson (P pid page pemail)) = VString pid"
| "projVal (Col STUDENTS) (VEnrollment v) = getAssociationEnd STUDENTS v" 
| "projVal (Col LECTURERS) (VEnrollment v) = getAssociationEnd LECTURERS v"

(* projValList: given a  expression and a list of rows,
 it returns the list of values corresponding to calling projVal for each row in the given list *)

fun projValList :: "exp \<Rightarrow> val list \<Rightarrow> val list" where
"projValList exp Nil = Nil"
| "projValList exp (v#vs) = (projVal exp v)#(projValList exp vs)"


(* select: given a value --either a person or an enrollment--
and an expression, it returns the value that correspond to
evaluat the expression for exactly that value (the only relevant
cases are var and columns ---i.e., either attributes or association-ends) *)
fun select :: "val \<Rightarrow> exp \<Rightarrow> val" where
"select val (MySQL.Int i) = VInt i"
| "select val (MySQL.Var v) = VObj v"
| "select val (Col col) = projVal (Col col) val"
| "select val (Eq e1 e2) = VBool (equalVal (select val e1) (select val e2))"
| "select val (GrtThan e1 e2) = VBool (greaterThanVal (select val e1) (select val e2))"
| "select val (And e1 e2) = VBool (andVal (select val e1) (select val e2))"

(* filterEnrollments: given an expression and an enrollment list,
it filter out the enrollment list based on the result of the expression
for each enrollment *)

fun filterEnrollments :: "exp \<Rightarrow> Enrollment list \<Rightarrow> val list" where
"filterEnrollments exp Nil = Nil"
| "filterEnrollments exp (e#es) = (if (isTrueVal (select (VEnrollment e) exp)) 
  then ((VEnrollment e)#(filterEnrollments exp es)) 
  else (filterEnrollments exp es))"

(*
fun selectNoCtx :: "exp \<Rightarrow> val list" where
"selectNoCtx (MySQL.Int i) = [VInt i]"
| "selectNoCtx (MySQL.Var v) = [VObj v]"
| "selectNoCtx (MySQL.Eq e1 e2) = [VBool (equalVal (VList (selectNoCtx e1)) (VList (selectNoCtx e2)))]"
*)


(* extEnrollment: given a variable-expression and column
and a list of enrollments, it returns the list of enrollments such that
the unknown ---VObj v--- value of the variable-expression 
occupies the column position in the enrollment *)

fun extEnrollments :: "exp \<Rightarrow> col \<Rightarrow> Enrollment list \<Rightarrow> val list" where
"extEnrollments (Var v) col Nil = Nil" 
| "extEnrollments (Var v) col (e#es) = (if ((getAssociationEnd col e) = (VObj v)) 
    then (VEnrollment e)#(extEnrollments (Var v) col es) 
    else extEnrollments (Var v) col es)"

(* extCol: given a variable-expression and column
and a list of enrollments, it returns the list of values
that occupies the column position in the enrollments such that
the unknown ---VObj v--- value of the variable-expression 
occupies the opposite column position in the enrollment *)

fun extCol :: "exp \<Rightarrow> col \<Rightarrow> Enrollment list \<Rightarrow> val list" where
"extCol (Var v) col Nil = Nil" 
| "extCol (Var v) col (e#es) =  (if ((getAssociationEnd (opposite col) e) = (VObj v)) 
then (((getAssociationEnd col e))#(extCol (Var v) col es)) 
else (extCol (Var v) col es))"

fun naselectList :: "val list \<Rightarrow> exp \<Rightarrow> val list" where
 "naselectList Nil exp = Nil"
| "naselectList (v#vs) exp = (select v exp) # (naselectList vs exp)"

fun selectList :: "val list \<Rightarrow> exp \<Rightarrow> val list" where

(* agregator expressions *)
"selectList vs (Count col) = [VInt (sizeValList vs)]"
| "selectList vs (Eq (Count col) (MySQL.Int i)) = [VBool (equalVal (VInt (sizeValList vs)) (VInt i))]"
| "selectList vs (GrtThan (Count col) (MySQL.Int i)) = [VBool (greaterThanVal (VInt (sizeValList vs)) (VInt i))]"
| "selectList vs (CountAll) =  [VInt (sizeValList vs)]"
| "selectList vs (Eq (CountAll) (MySQL.Int i)) = [VBool (equalVal (VInt (sizeValList vs)) (VInt i))]"
| "selectList vs (GrtThan (CountAll) (MySQL.Int i)) = [VBool (greaterThanVal (VInt (sizeValList vs)) (VInt i))]"
(* no-agregator expressions *)
| "selectList vs exp = naselectList vs exp"


(*
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
*)

(* filterWhere: given a list of values --- currently, either the original Person table or
the original Enrollment table --- and a where-clause, it returns the values that satisfy 
(select equals to true) 
the where-clause 
*)
fun filterWhere :: "val list \<Rightarrow> whereClause \<Rightarrow> val list" where
"filterWhere Nil (WHERE (Eq e1 e2)) =  Nil"
| "filterWhere [TPerson om] (WHERE (Eq (Col ID) (Var var)))
= [VObj var]"
| "filterWhere [TEnrollment (OM ps es)] (WHERE (Eq (Col col) (Var var)))
= extEnrollments (Var var) col es"
| "filterWhere [TEnrollment  (OM ps es)] (WHERE (And e1 e2))
= filterEnrollments (And e1 e2) es"
(* This is to be discussed, completed later, when dealing with Subselect
| "filterWhere (Cons v vs) (WHERE e) = (if (isTrueVal (select v e))  
    then (v#(filterWhere vs (WHERE e)))   
    else filterWhere vs (WHERE e))"
*)



(* exec: this is the key function: given a SQL-expression and and object
model it returns a list of values. Notice that we keep the original
table-type-name to be sued in selectlist *)

fun exec :: "SQLstm \<Rightarrow> Objectmodel \<Rightarrow> val list" where
"exec (Select selitems) om  = [select VNULL selitems]"
| "exec (SelectFrom exp (Table PERSON)) om 
    = selectList ([TPerson om]) exp"
|  "exec (SelectFrom exp (Table ENROLLMENT)) om 
    = selectList ([TEnrollment om]) exp"
| "exec (SelectFromWhere exp (Table PERSON) whereExp) om
    = selectList (filterWhere ([TPerson om]) whereExp) exp"
| "exec (SelectFromWhere exp (Table ENROLLMENT) whereExp) om
    = selectList (filterWhere ([TEnrollment om]) whereExp) exp"

end