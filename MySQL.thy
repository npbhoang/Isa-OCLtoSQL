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

datatype joinClause = JOIN fromItem exp

datatype SQLstm = Select exp 
  | SelectFrom exp fromItem
  | SelectFromWhere exp fromItem whereClause 
  | SelectFromJoin exp fromItem joinClause


fun opposite :: "col \<Rightarrow> col" where
"opposite STUDENTS = LECTURERS"
  | "opposite LECTURERS = STUDENTS"


fun getAssociationEnd :: "col \<Rightarrow> Enrollment \<Rightarrow> Person" where
"getAssociationEnd STUDENTS (E students lecturers) = students"
  | "getAssociationEnd LECTURERS (E students lecturers) = lecturers"

(* projVal: given a column-expression and a row --either in person or enrollment table--,
it returns the corresonding value *)

fun projVal :: "exp \<Rightarrow> val \<Rightarrow> val" where 
"projVal (Col AGE) (VPerson (P page pemail)) = VInt page"
| "projVal (Col EMAIL) (VPerson (P page pemail)) = VString pemail"
| "projVal (Col STUDENTS) (VEnrollment (E p1 p2)) = VPerson p1" 
| "projVal (Col LECTURERS) (VEnrollment (E p1 p2)) = VPerson p2"
| "projVal (Col EMAIL) (VJoin [VEnrollment e, VPerson p]) = projVal (Col EMAIL) (VPerson p)"

lemma [simp]: "projVal (Col ID) (VPerson p) = VPerson p"
sorry

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

(* filterPersons: given an expression and a person list,
it filters out the person list based on the result of the expression
for each person *)

fun filterPersons :: "exp \<Rightarrow> Person list \<Rightarrow> val list" where
"filterPersons exp Nil = Nil"
| "filterPersons exp (p#ps) = (if (isTrueVal (select (VPerson p) exp)) 
  then ((VPerson p)#(filterPersons exp ps)) 
  else (filterPersons exp ps))"

(*
fun selectNoCtx :: "exp \<Rightarrow> val list" where
"selectNoCtx (MySQL.Int i) = [VInt i]"
| "selectNoCtx (MySQL.Var v) = [VObj v]"
| "selectNoCtx (MySQL.Eq e1 e2) = [VBool (equalVal (VList (selectNoCtx e1)) (VList (selectNoCtx e2)))]"
*)


(* extEnrollment: given an object ---currently, we consider VObj v--- and column
and a list of enrollments, it returns the list of enrollments such that
the unknown ---VObj v--- value of the variable-expression 
occupies the column position in the enrollment *)

fun extEnrollments :: "val \<Rightarrow> col \<Rightarrow> Enrollment list \<Rightarrow> val list" where
"extEnrollments (VObj v) col Nil = Nil" 
| "extEnrollments (VObj v) col (e#es) = (if ((VPerson (getAssociationEnd col e)) = (VObj v)) 
    then (VEnrollment e)#(extEnrollments (VObj v) col es) 
    else extEnrollments (VObj v) col es)"

(* extCol: given a val ---either a value of the variable-expression VObj v 
or a Person VPerson p--- and column
and a list of enrollments, it returns the list of values
that occupies the column position in the enrollments such that
the val ---VObj v or VPerson p---
occupies the opposite column position in the enrollment *)

fun extCol :: "val \<Rightarrow> col \<Rightarrow> Enrollment list \<Rightarrow> val list" where
"extCol val col [] = []" 
| "extCol val col (e#es) = (if (VPerson (getAssociationEnd (opposite col) e)) = val
then (((VPerson (getAssociationEnd col e)))#(extCol val col es))  
else (extCol val col es))" 


fun naselectList :: "val list \<Rightarrow> exp \<Rightarrow> val list" where
 "naselectList [] exp = []"
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

(* 
filterWhere: given a list of values --- currently, either the original Person table or
the original Enrollment table --- and a where-clause, it returns the values that satisfy 
(select equals to true) the where-clause 
*)
fun filterWhere :: "val list \<Rightarrow> whereClause \<Rightarrow> val list" where
"filterWhere [] exp =  []"
| "filterWhere ((VPerson p)#valps) (WHERE exp)
= (if (isTrueVal (select (VPerson p) exp)) 
  then ((VPerson p)#filterWhere valps (WHERE exp)) 
  else (filterWhere valps (WHERE exp)))"
(*
| "filterWhere [TEnrollment (OM ps es)] (WHERE (And e1 e2))
= filterEnrollments (And e1 e2) es"
*)
(* ASSUMPTION: Given the valid table Person, if the where-clause is of the form
---Person_id = var--- then it returns exactly one Person, which is the VObj var itself *)
lemma [simp]: "filterWhere [TPerson (OM ps es)] (WHERE (Eq (Col ID) (Var var))) = [VObj var]"
sorry
(* ASSUMPTION: Given the valid table Enrollment, if the where-clause is either of the form
---LECTURERS = var or STUDENTS = var--- then it returns exactly 
the list of Enrollments such that either the (VObj var) is the STUDENTS or the LECTURERS *)
lemma [simp]: "filterWhere [TEnrollment (OM ps es)] (WHERE (Eq (Col col) (Var var)))
= extEnrollments (VObj var) col es"
sorry


(* This is to be discussed, completed later, when dealing with Subselect
| "filterWhere (Cons v vs) (WHERE e) = (if (isTrueVal (select v e))  
    then (v#(filterWhere vs (WHERE e)))   
    else filterWhere vs (WHERE e))"
*)

lemma TPersonToValList: "[TPerson (OM ps es)] = mapPersonListToValList ps"
sorry

lemma TEnrollmentToValList: "[TEnrollment (OM ps es)] = mapEnrollmentToValList es"
sorry

(* 
getFromItem: given a from item --- currently, either the original Person table or
the original Enrollment table --- and an object model, it returns the val list indicates
the whole original Person table or the original Enrollment table under the val form.

Notice that TPerson and TEnrollment are special constructors which represents the notion
of the whole table, for the time being, we need to keep the object model within.

For additional usage which requires [TPerson om] of the actual list form (i.e. (VPerson p)#ps)
consider using lemma TPerson_ValList and TEnrollment_ValList.  
*)

(*
fun getFromItem :: "fromItem \<Rightarrow> Objectmodel \<Rightarrow>val list" where
"getFromItem (Table PERSON) om = [TPerson om]"
| "getFromItem (Table ENROLLMENT) om = [TEnrollment om]"
*)

(* 
checkOnCondition: given two values, each from each side of the join 
---currently, these values are assumed to be VPerson and VEnrollment as the join now 
is only between Person and Enrollment--- 
and an on-expression ---currently, it is an equality expression where the left-hand side 
is a column from the Person table and the right hand side is a column from the Enrollment table, 
it returns the 
boolean indicates that the two values return true when evaluated them on the on-expression.
*)

fun  checkOnCondition :: "val \<Rightarrow> val \<Rightarrow> exp \<Rightarrow> bool" where
"checkOnCondition val (VEnrollment e) (Eq (Col enrollmentCol) (Col personCol))
= equalVal (select val (Col personCol)) (select (VEnrollment e) (Col enrollmentCol))"





fun joinValWithValList :: "val \<Rightarrow> val list \<Rightarrow> exp \<Rightarrow> val list" where
"joinValWithValList val [] exp = []"
| "joinValWithValList val (val1#valList1) exp = 
(if (checkOnCondition val val1 exp) 
then ((VJoin [val,val1])#(joinValWithValList val valList1 exp))
else (joinValWithValList val valList1 exp))"


fun joinValListWithValList :: "val list \<Rightarrow> val list \<Rightarrow> exp \<Rightarrow> val list" where
"joinValListWithValList [] valList2 exp = []"
| "joinValListWithValList (val1#valList1) valList2 exp 
= (joinValWithValList val1 valList2 exp)
@(joinValListWithValList valList1 valList2 exp)"


(* exec: this is the key function: given a SQL-expression and and object
model it returns a list of values. Notice that we keep the original
table-type-name to be sued in selectlist *)

fun exec :: "SQLstm \<Rightarrow> Objectmodel \<Rightarrow> val list" where
"exec (Select selitems) om  = [select VNULL selitems]"
| "exec (SelectFrom exp (Table ENROLLMENT)) (OM ps es) 
    = selectList (mapEnrollmentToValList es) exp"
| "exec (SelectFrom exp (Table PERSON)) (OM ps es) 
    = selectList (mapPersonListToValList ps) exp"
| "exec (SelectFromWhere exp (Table ENROLLMENT) whereExp) (OM ps es)
    = selectList (filterWhere (mapEnrollmentToValList es) whereExp) exp"
| "exec (SelectFromWhere exp (Table PERSON) whereExp) (OM ps es)
    = selectList (filterWhere (mapPersonListToValList ps) whereExp) exp"
| "exec (SelectFromJoin exp (Table ENROLLMENT) (JOIN (Table PERSON) onExp)) (OM ps es)
= selectList (joinValListWithValList (mapEnrollmentToValList es) (mapPersonListToValList ps) onExp) exp"

end