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

lemma [simp]: "OCL2PSQL (xs@ys) = (OCL2PSQL xs)@(OCL2PSQL ys)"
proof(induct xs)
case Nil
then show ?case by simp
next
case (Cons a xs)
then show ?case by simp
qed


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
(* agregator expressions *)
"selectList vs (CountAll) =  [RTuple [Pair col.PINT (RInt (size vs))]]"
| "selectList vs (Eq (CountAll) (MySQL.Int i)) = [RTuple [Pair col.PBOOL (RBool ((size vs) = i))]]"
| "selectList vs (GrtThan (CountAll) (MySQL.Int i)) = [RTuple [Pair col.PBOOL (RBool ((sizeList vs) > i))]]"

(* no-agregator expressions *)
| "selectList vs exp = naselectList vs exp"

fun isEqualID :: "pid \<Rightarrow> pid \<Rightarrow> bool" where
"isEqualID (PID p1) (PID p2) = (p1 = p2)"

fun isSatisfiedColumn :: "column \<Rightarrow> exp \<Rightarrow> bool" where
"isSatisfiedColumn (RID (PID i)) (Var self) = (i = self)" 
| "isSatisfiedColumn (RInt i) (exp.Int l) = (i = l)" 

fun isSatisfiedColColumnList :: "(col*column) list \<Rightarrow> exp \<Rightarrow> bool" where
"isSatisfiedColColumnList (c#cs) (Eq (Col col2) exp) = 
(if (fst c) = col2
then (isSatisfiedColumn (snd c) exp)
else (isSatisfiedColColumnList cs (Eq (Col col2) exp)))"

fun isSatisfiedRow :: "row \<Rightarrow> exp \<Rightarrow> bool" where
"isSatisfiedRow (RTuple cs) (Eq (Col col2) exp) = 
isSatisfiedColColumnList cs (Eq (Col col2) exp)"
| "isSatisfiedRow (RTuple cs) (And e1 e2)
= ((isSatisfiedRow (RTuple cs) e1) \<and> (isSatisfiedRow (RTuple cs) e2))"

fun findIDCell :: "(col*column) list \<Rightarrow> column" where
"findIDCell [] = RNULL"
| "findIDCell (c#cs) = (if (fst c = MySQL.ID) 
then (snd c) else (findIDCell cs))"

fun isSameRow :: "row \<Rightarrow> row \<Rightarrow> bool" where
"isSameRow (RTuple cs1) (RTuple cs2) = ((findIDCell cs1) = (findIDCell cs2))"

fun isUnique :: "row \<Rightarrow> row list \<Rightarrow> bool" where
"isUnique r [] = True"
| "isUnique r (r1#rs) = (\<not>(isSameRow r r1) \<and> (isUnique r rs))"

fun isValid :: "row list \<Rightarrow> bool" where
"isValid [] = True"
| "isValid (v#vs) = ((isUnique v vs) \<and> (isValid vs))"

fun filterWhere :: "row list \<Rightarrow> whereClause \<Rightarrow> row list" where
"filterWhere [] exp =  []"
| "filterWhere (r#rs) (WHERE (Eq (Col col2) (Var self)))
= (if (isSatisfiedRow r (Eq (Col col2) (Var self))) 
then (if (col2 = col.ID \<and> isValid (r#rs)) then [r] else (r#filterWhere rs (WHERE (Eq (Col col2) (Var self)))))
else (filterWhere rs (WHERE (Eq (Col col2) (Var self)))))"
| "filterWhere (r#rs) (WHERE (Eq (Col col2) (MySQL.Int i)))
= (if isSatisfiedRow r (Eq (Col col2) (MySQL.Int i)) 
  then (r#filterWhere rs (WHERE (Eq (Col col2) (MySQL.Int i))))
  else (filterWhere rs (WHERE (Eq (Col col2) (MySQL.Int i)))))"
| "filterWhere (r#rs) (WHERE (And e1 e2))
= (if isSatisfiedRow r (And e1 e2)
then (r#filterWhere rs (WHERE (And e1 e2)))
else filterWhere rs (WHERE (And e1 e2)))"

fun getCell :: "(col*column) list \<Rightarrow> col \<Rightarrow> column" where
"getCell [] col = RNULL"
| "getCell (c#cs) col = (if (fst c) = col then snd c else (getCell cs col))"

fun checkOnCondition :: "row \<Rightarrow> row \<Rightarrow> exp \<Rightarrow> bool" where
"checkOnCondition (RTuple cs1) (RTuple cs2) (Eq (Col aRowFromCS1) (Col aRowFromCS2))
= ((getCell cs1 aRowFromCS1) = (getCell cs2 aRowFromCS2))"

fun joinRow :: "row \<Rightarrow> row \<Rightarrow> row" where
"joinRow (RTuple cs1) (RTuple cs2) = RTuple (cs1@cs2)"

fun joinValWithValList :: "row \<Rightarrow> row list \<Rightarrow> exp \<Rightarrow> row list" where
"joinValWithValList val [] exp = []"
| "joinValWithValList val (val1#valList1) exp =
(if (checkOnCondition val val1 exp) 
then (joinRow val val1) # (joinValWithValList val valList1 exp)
else (joinValWithValList val valList1 exp))"

fun joinValListWithValList :: "row list \<Rightarrow> row list \<Rightarrow> exp \<Rightarrow> row list" where
"joinValListWithValList [] valList2 exp = []"
| "joinValListWithValList (val1#valList1) valList2 exp 
= (joinValWithValList val1 valList2 exp)
@(joinValListWithValList valList1 valList2 exp)"

lemma [simp]: "joinValListWithValList aList [] exp = []"
proof (induct aList)
case Nil
then show ?case by simp
next
case (Cons a aList)
then show ?case by simp
qed

fun exec :: "SQLstm \<Rightarrow> SQLObjectmodel \<Rightarrow> row list" where
"exec (Select selitems) sqlom = [select (RTuple [(Pair PNULL RNULL)]) selitems]"
| "exec (SelectFrom exp (Table PERSON)) sqlom 
    = selectList (mapPersonListToRowList (getSQLPersonList sqlom)) exp"  
| "exec (SelectFrom exp (Table ENROLLMENT)) sqlom
    = selectList (mapEnrollmentListToRowList (getSQLEnrollmentList sqlom)) exp"
| "exec (SelectFromWhere exp (Table PERSON) whereExp) sqlom
    = selectList (filterWhere (mapPersonListToRowList (getSQLPersonList sqlom)) whereExp) exp"
| "exec (SelectFromWhere exp (Table ENROLLMENT) whereExp) sqlom
    = selectList (filterWhere (mapEnrollmentListToRowList (getSQLEnrollmentList sqlom)) whereExp) exp"
| "exec (SelectFromJoin exp (Table PERSON) (JOIN (Table ENROLLMENT) onExp)) sqlom
= selectList (joinValListWithValList (mapPersonListToRowList (getSQLPersonList sqlom)) 
(mapEnrollmentListToRowList (getSQLEnrollmentList sqlom)) onExp) exp"

end