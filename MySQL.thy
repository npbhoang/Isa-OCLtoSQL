theory MySQL
  imports Main ObjectModel
begin

type_synonym var = string

datatype pid = PID string | IDVar var

datatype SQLPerson = SQLP pid nat string | SQLPNULL
datatype SQLEnrollment = SQLE pid pid

datatype SQLObjectmodel = SQLOM "SQLPerson list" "SQLEnrollment list"

datatype column = RNULL
| RInt nat
| RString string
| RBool bool
| RID pid

datatype table = PERSON | ENROLLMENT
datatype col = AGE | EMAIL | ID | LECTURERS | STUDENTS | PINT | PBOOL | PSTRING | PNULL | PTOP

datatype row = RTuple "(col * column) list"

fun getSQLPersonList :: "SQLObjectmodel \<Rightarrow> SQLPerson list" where
"getSQLPersonList (SQLOM ps es) = ps"

fun getSQLEnrollmentList :: "SQLObjectmodel \<Rightarrow> SQLEnrollment list" where
"getSQLEnrollmentList (SQLOM ps es) = es"

fun getIdSQLPerson :: "SQLPerson \<Rightarrow> pid" where
"getIdSQLPerson (SQLP personid age email) = personid"
| "getIdSQLPerson SQLPNULL = PID undefined"

fun getAgeSQLPerson :: "SQLPerson \<Rightarrow> nat" where
"getAgeSQLPerson (SQLP personid age email) = age"
| "getAgeSQLPerson SQLPNULL = undefined"

fun getEmailSQLPerson :: "SQLPerson \<Rightarrow> string" where
"getEmailSQLPerson (SQLP personid age email) = email"
| "getEmailSQLPerson SQLPNULL = undefined"

fun mapSQLPersonToRow :: "SQLPerson \<Rightarrow> row" where
"mapSQLPersonToRow p = RTuple [
(Pair MySQL.ID (RID (getIdSQLPerson p))),
(Pair MySQL.AGE (RInt (getAgeSQLPerson p))),
(Pair MySQL.EMAIL (RString (getEmailSQLPerson p)))
]"

fun mapPersonListToRowList :: "SQLPerson list \<Rightarrow> row list" where
"mapPersonListToRowList [] = []" |
"mapPersonListToRowList (p#ps) = (mapSQLPersonToRow p)#(mapPersonListToRowList ps)"

fun getForeignKey :: "col \<Rightarrow> SQLEnrollment \<Rightarrow> pid" where
"getForeignKey STUDENTS (SQLE e1 e2) = e1"
| "getForeignKey LECTURERS (SQLE e1 e2) = e2"

fun mapEnrollmentToRow :: "SQLEnrollment \<Rightarrow> row" where
"mapEnrollmentToRow e = RTuple [(Pair MySQL.STUDENTS (RID (getForeignKey STUDENTS e))), 
(Pair MySQL.LECTURERS (RID (getForeignKey LECTURERS e)))]"

fun mapEnrollmentListToRowList :: "SQLEnrollment list \<Rightarrow> row list" where
"mapEnrollmentListToRowList [] = []" |
"mapEnrollmentListToRowList (e#es) 
= (mapEnrollmentToRow e)
#(mapEnrollmentListToRowList es)"

fun valToCol :: "val \<Rightarrow> column" where
"valToCol VNULL = RNULL"
| "valToCol (VInt i) = (RInt i)"
| "valToCol (VPerson p) = RID (PID (getIdPerson p))"
| "valToCol (VBool b) = (RBool b)"
| "valToCol (VObj var) = RID (IDVar var)"

fun typeToCol :: "val \<Rightarrow> col" where
"typeToCol (VInt i) = PINT"
| "typeToCol (VString s) = PSTRING"
| "typeToCol (VBool b) = PBOOL"
| "typeToCol (VPerson p) = PSTRING"
| "typeToCol (VObj var) = PSTRING"

fun OCL2PSQL :: "val list \<Rightarrow> row list" where
"OCL2PSQL [] = []" 
| "OCL2PSQL (val#list) = (RTuple [Pair (typeToCol val) (valToCol val)])#(OCL2PSQL list)"

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

  

(* COMMENT
fun opposite :: "col \<Rightarrow> col" where
"opposite STUDENTS = LECTURERS"
  | "opposite LECTURERS = STUDENTS"

(* projValList: given a  expression and a list of rows,
 it returns the list of values corresponding to calling projVal for each row in the given list *)

fun projValList :: "exp \<Rightarrow> val list \<Rightarrow> val list" where
"projValList exp Nil = Nil"
| "projValList exp (v#vs) = (projVal exp v)#(projValList exp vs)"

COMMENT *)

fun mapPersonToSQLPerson :: "Person \<Rightarrow> SQLPerson" where
"mapPersonToSQLPerson (P pid age email) = (SQLP (PID pid) age email)"
| "mapPersonToSQLPerson Person.PNULL = SQLPNULL"

fun mapEnrollmentToSQLEnrollment :: "Enrollment \<Rightarrow> SQLEnrollment" where
"mapEnrollmentToSQLEnrollment (E e1 e2) = (SQLE (PID (getIdPerson e1)) (PID (getIdPerson e2)))"

fun mapPersonListToSQLPersonList :: "Person list \<Rightarrow> SQLPerson list" where
"mapPersonListToSQLPersonList [] = []"
| "mapPersonListToSQLPersonList (p#ps) = (mapPersonToSQLPerson p)#(mapPersonListToSQLPersonList ps)"

fun mapEnrollmentListToSQLEnrollmentList :: "Enrollment list \<Rightarrow> SQLEnrollment list" where
"mapEnrollmentListToSQLEnrollmentList [] = []"
| "mapEnrollmentListToSQLEnrollmentList (e#es) = (mapEnrollmentToSQLEnrollment e)#(mapEnrollmentListToSQLEnrollmentList es)"

fun map :: "Objectmodel \<Rightarrow> SQLObjectmodel" where
"map (OM ps es) = SQLOM (mapPersonListToSQLPersonList ps) (mapEnrollmentListToSQLEnrollmentList es)"

(* select: given a value --either a person or an enrollment--
and an expression, it returns the value that correspond to
evaluat the expression for exactly that value (the only relevant
cases are var and columns ---i.e., either attributes or association-ends) *)

fun getType :: "col \<Rightarrow> col" where 
"getType col.AGE = PINT"
| "getType PINT = PINT"

fun equalCol :: "(col \<times> column) \<Rightarrow> (col \<times> column) \<Rightarrow> bool" where
"equalCol (Pair col1 i1) (Pair col2 i2) 
= (((getType col1) = (getType col2)) \<and> (i1 = i2))" 

fun equalColList :: "(col \<times> column) list \<Rightarrow> (col \<times> column) list \<Rightarrow> bool" where
"equalColList [] [] = True"
| "equalColList [] (c#cs) = False"
| "equalColList (c#cs) [] = False"
| "equalColList (c1#cs1) (c2#cs2) = 
((equalCol c1 c2) \<and> (equalColList cs1 cs2))"

fun equalRow ::  "row \<Rightarrow> row \<Rightarrow> bool" where
"equalRow (RTuple []) (RTuple []) = True"
| "equalRow (RTuple cs1) (RTuple cs2) = equalColList cs1 cs2"

fun getColumnInRow:: "col \<Rightarrow> (col \<times> column) list \<Rightarrow> (col \<times> column)" where
"getColumnInRow col [] = Pair (PNULL) (RNULL)"
| "getColumnInRow col (c#cs) = (if (col = fst c) 
then c else (getColumnInRow col cs))" 


fun getColumn :: "col \<Rightarrow> row \<Rightarrow> (col \<times> column)" where
"getColumn col (RTuple cs) = getColumnInRow col cs"

fun select :: "row \<Rightarrow> exp \<Rightarrow> row" where
"select row (MySQL.Int i) = RTuple [(Pair PINT (RInt i))]"
| "select row (MySQL.Var v) = RTuple [(Pair PSTRING (RID (IDVar v)))]"
| "select row (Eq e1 e2) = RTuple [(Pair PBOOL (RBool (equalRow (select row e1) (select row e2))))]"
| "select row (Col at) = RTuple [getColumn at row]"
(*
| "select val (GrtThan e1 e2) = VBool (greaterThanVal (select val e1) (select val e2))"
| "select val (And e1 e2) = VBool (andVal (select val e1) (select val e2))"
*)
(* filterEnrollments: given an expression and an enrollment list,
it filter out the enrollment list based on the result of the expression
for each enrollment *)

(* COMMENT
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
*)

fun naselectList :: "row list \<Rightarrow> exp \<Rightarrow> row list" where
"naselectList [] exp = []"
| "naselectList (row#rows) exp = (select row exp) # (naselectList rows exp)"

(* FACT --- select over a list appended by two lists is the same as selct them individually *)
lemma [simp]: "naselectList (xs@ys) exp = (naselectList xs exp) @ (naselectList ys exp)"
proof (induct xs)
case Nil
then show ?case by simp
next
case (Cons a xs)
then show ?case by simp
qed


fun selectList :: "row list \<Rightarrow> exp \<Rightarrow> row list" where
(*
(* agregator expressions *)
"selectList vs (Count col) = [VInt (sizeValList vs)]"
| "selectList vs (Eq (Count col) (MySQL.Int i)) = [VBool (equalVal (VInt (sizeValList vs)) (VInt i))]"
| "selectList vs (GrtThan (Count col) (MySQL.Int i)) = [VBool (greaterThanVal (VInt (sizeValList vs)) (VInt i))]"
| "selectList vs (CountAll) =  [VInt (sizeValList vs)]"
| "selectList vs (Eq (CountAll) (MySQL.Int i)) = [VBool (equalVal (VInt (sizeValList vs)) (VInt i))]"
| "selectList vs (GrtThan (CountAll) (MySQL.Int i)) = [VBool (greaterThanVal (VInt (sizeValList vs)) (VInt i))]"
*)
(* no-agregator expressions *)
"selectList vs exp = naselectList vs exp"
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

fun isEqualID :: "pid \<Rightarrow> pid \<Rightarrow> bool" where
"isEqualID (PID p1) (PID p2) = (p1 = p2)"
(*| "isEqualID (IDVar var1) (IDVar var2) = (var1 = var2)"
| "isEqualID (PID p1) (IDVar var) = (p1 = var)"
*)

fun isSatisfiedColumn :: "column \<Rightarrow> exp \<Rightarrow> bool" where
(*
"isSatisfiedColumn (RID pid) (Var self) = isEqualID pid (IDVar self)"
*)
"isSatisfiedColumn (RID (PID i)) (Var self) = (i = self)" 

fun isSatisfiedColColumnList :: "(col*column) list \<Rightarrow> exp \<Rightarrow> bool" where
"isSatisfiedColColumnList (c#cs) (Eq (Col col2) (Var self)) = 
(if (fst c) = col2
then (isSatisfiedColumn (snd c) (Var self))
else (isSatisfiedColColumnList cs (Eq (Col col2) (Var self))))"

fun isSatisfiedRow :: "row \<Rightarrow> exp \<Rightarrow> bool" where
"isSatisfiedRow (RTuple cs) (Eq (Col col2) (Var self)) = 
isSatisfiedColColumnList cs (Eq (Col col2) (Var self))"


(* 
filterWhere: given a list of values --- currently, either the original Person table or
the original Enrollment table --- and a where-clause, it returns the values that satisfy 
(select equals to true) the where-clause 
*)
(* This is a temporary hack: the special if-then-else only works for Person-table where
ID is a primary key
*)

fun filterWhere :: "row list \<Rightarrow> whereClause \<Rightarrow> row list" where
"filterWhere [] exp =  []"
| "filterWhere (r#rs) (WHERE (Eq (Col col2) (Var self)))
= (if isSatisfiedRow r (Eq (Col col2) (Var self)) 
  then (if (col2 = col.ID) then [r] else (r#filterWhere rs (WHERE (Eq (Col col2) (Var self)))))
  else (filterWhere rs (WHERE (Eq (Col col2) (Var self)))))"

(*
| "filterWhere [TEnrollment (OM ps es)] (WHERE (And e1 e2))
= filterEnrollments (And e1 e2) es"
*)


(* This is to be discussed, completed later, when dealing with Subselect
| "filterWhere (Cons v vs) (WHERE e) = (if (isTrueVal (select v e))  
    then (v#(filterWhere vs (WHERE e)))   
    else filterWhere vs (WHERE e))"
*)

(* COMMENT
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

COMMENT *)

(* exec: this is the key function: given a SQL-expression and and object
model it returns a list of values. Notice that we keep the original
table-type-name to be sued in selectlist *)
fun exec :: "SQLstm \<Rightarrow> SQLObjectmodel \<Rightarrow> row list" where
"exec (Select selitems) sqlom = [select (RTuple [(Pair PNULL RNULL)]) selitems]"
| "exec (SelectFromWhere exp (Table PERSON) whereExp) sqlom
    = selectList (filterWhere (mapPersonListToRowList (getSQLPersonList sqlom)) whereExp) exp"
| "exec (SelectFromWhere exp (Table ENROLLMENT) whereExp) sqlom
    = selectList (filterWhere (mapEnrollmentListToRowList (getSQLEnrollmentList sqlom)) whereExp) exp"    
(* COMMENT
| "exec (SelectFrom exp (Table ENROLLMENT)) (OM ps es) 
    = selectList (mapEnrollmentToValList es) exp"
| "exec (SelectFrom exp (Table PERSON)) (OM ps es) 
    = selectList (mapPersonListToValList ps) exp"
| "exec (SelectFromWhere exp (Table ENROLLMENT) whereExp) (OM ps es)
    = selectList (filterWhere (mapEnrollmentToValList es) whereExp) exp"

| "exec (SelectFromJoin exp (Table ENROLLMENT) (JOIN (Table PERSON) onExp)) (OM ps es)
= selectList (joinValListWithValList (mapEnrollmentToValList es) (mapPersonListToValList ps) onExp) exp"
COMMENT *)
end