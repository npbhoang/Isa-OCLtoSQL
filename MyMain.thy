theory MyMain
  imports Main MyOCL MySQL OCLtoSQL
  begin 

lemma (* 1 \<equiv> SELECT 1 *)
"OCL2PSQL (eval (MyOCL.Int i) om) = exec (Select (MySQL.Int i)) (map om)"
by simp

lemma (* self \<equiv> SELECT self *)
"OCL2PSQL (eval (MyOCL.Var self) om) = exec (Select (MySQL.Var self)) (map om)"
by simp

(* self = caller \<equiv> SELECT self = caller *)
theorem "OCL2PSQL (eval (MyOCL.Eq (MyOCL.Var self) (MyOCL.Var caller)) om) 
= exec (Select (MySQL.Eq (MySQL.Var self) (MySQL.Var caller))) (map om)"
proof -
  show ?thesis by simp      
qed    

fun getRowById :: "SQLPerson list \<Rightarrow> pid \<Rightarrow> row" where
"getRowById [] pid = (RTuple [(Pair MySQL.PNULL RNULL)])"
| "getRowById (p#ps) pid = (if (getIdSQLPerson p = pid) 
then (RTuple [(Pair MySQL.PSTRING (RID (getIdSQLPerson p)))
, (Pair MySQL.PINT (RInt (getAgeSQLPerson p)))
, (Pair MySQL.PSTRING (RString (getEmailSQLPerson p)))]) 
else (getRowById ps pid))"

(* Because ID is PRIMARY KEY. To prove it, the definition of filterWhere
needs to reflect this fact *)
lemma lem1: "filterWhere (mapPersonListToRowList (getSQLPersonList (MySQL.map om))) (WHERE (exp.Eq (Col col.ID) (exp.Var self))) 
= [(getRowById (getSQLPersonList (MySQL.map om)) (IDVar self))]"
sorry

fun stripAliasCell :: "(col*column) list \<Rightarrow> (col*column) list" where
"stripAliasCell [] = []"
| "stripAliasCell (c#cs) = (Pair PTOP (snd c))#(stripAliasCell cs)"

fun stripAliasRow :: "row \<Rightarrow> row" where
"stripAliasRow (RTuple as) = RTuple (stripAliasCell as)"

fun stripAlias :: "row list \<Rightarrow> row list" where
"stripAlias [] = []"
| "stripAlias (r#rs) = (stripAliasRow r)#(stripAlias rs)"

lemma remarkUno : "getRowById (getSQLPersonList (MySQL.map om)) (IDVar self)
= RTuple [
(Pair MySQL.ID (RID (IDVar self))),
(Pair MySQL.AGE (RInt (getAgePerson (PVObj self)))),
(Pair MySQL.EMAIL (RString (getEmailPerson (PVObj self))))
]"
sorry

theorem "stripAlias (OCL2PSQL (eval (MyOCL.Att (MyOCL.Var self) (MyOCL.AGE)) om))    
= stripAlias (exec (SelectFromWhere (MySQL.Col (MySQL.AGE)) (Table MySQL.PERSON) 
(WHERE (MySQL.Eq (MySQL.Col (MySQL.ID)) (MySQL.Var self)))) (map om))"
apply auto
apply (simp add: lem1 remarkUno)
done

fun getRowByAssociationEnd :: "col \<Rightarrow> SQLEnrollment list \<Rightarrow> pid \<Rightarrow> row list" where
"getRowByAssociationEnd col [] pid = []"
| "getRowByAssociationEnd col.STUDENTS (e#es) pid = (if ((getForeignKey col.STUDENTS e) = pid) 
then (RTuple [(Pair MySQL.PSTRING (RID (getForeignKey col.STUDENTS e))), 
(Pair MySQL.PSTRING (RID (getForeignKey col.LECTURERS e)))])#(getRowByAssociationEnd col.STUDENTS es pid) 
else (getRowByAssociationEnd col.STUDENTS es pid))"

(* Because ID is PRIMARY KEY. To prove it, the definition of filterWhere
needs to reflect this fact *)
lemma lem2: "filterWhere (mapEnrollmentListToRowList (getSQLEnrollmentList (MySQL.map om))) 
(WHERE (exp.Eq (Col col.STUDENTS) (exp.Var self)))
= (getRowByAssociationEnd col.STUDENTS (getSQLEnrollmentList (MySQL.map om)) (IDVar self))"
sorry


lemma lem3: "getForeignKey col.STUDENTS (mapAssociationLink e) = IDVar self
\<Longrightarrow> getAssociationEnd as.STUDENTS e = PVObj self"
sorry

lemma lem4: "getAssociationEnd as.STUDENTS e = PVObj self
\<Longrightarrow> getForeignKey col.STUDENTS (mapAssociationLink e) = IDVar self"
sorry

lemma remarkDos: "getForeignKey col.LECTURERS (mapAssociationLink e) =
PID (getAssociationEnd as.LECTURERS e)"
sorry

theorem "stripAlias (OCL2PSQL (eval (MyOCL.As (MyOCL.Var self) (MyOCL.LECTURERS)) om))    
= stripAlias (exec (SelectFromWhere (MySQL.Col (MySQL.LECTURERS)) (Table MySQL.ENROLLMENT) 
(WHERE (MySQL.Eq (MySQL.Col (MySQL.STUDENTS)) (MySQL.Var self)))) (map om))"
proof (induct om)
case (OM ps es)
then show ?case 
proof (induct es)
case Nil
then show ?case by simp
next
case (Cons e es)
then show ?case
  apply auto
  apply (simp add: lem2 remarkDos)
  apply (simp add: lem4)
  apply (simp add: lem3)
  done
qed
qed



(* COMMENT
(* self.age = 30 \<equiv> SELECT age = 30 FROM Person WHERE id = self *)
theorem "eval (MyOCL.Eq (MyOCL.Att (MyOCL.Var self) MyOCL.AGE) (MyOCL.Int 30)) om
= exec (SelectFromWhere (MySQL.Eq (MySQL.Col (MySQL.AGE)) (MySQL.Int 30))
(Table MySQL.PERSON)
(WHERE (MySQL.Eq (MySQL.Col (MySQL.ID)) (MySQL.Var self)))) om" 
proof (induct om)
case (OM ps es)
from this have "(mapPersonListToValList ps) = [TPerson (OM ps es)]" 
using TPersonToValList by simp
then show ?case by simp
qed  



(* self.lecturers \<equiv> SELECT lecturers FROM Enrollment WHERE students = self *)
theorem "eval (MyOCL.As (MyOCL.Var self) MyOCL.LECTURERS) om
= exec (SelectFromWhere (MySQL.Col MySQL.LECTURERS) 
(Table ENROLLMENT)
(WHERE (MySQL.Eq (MySQL.Col (MySQL.STUDENTS)) (MySQL.Var self)))) om"
proof (induct om)
case (OM ps es)
from this have "(mapEnrollmentToValList es) = [TEnrollment (OM ps es)]" 
using TEnrollmentToValList by simp
then show ?case
proof (induct es)
  case Nil
  then show ?case by simp
next
  case (Cons a es)
  then show ?case by simp
qed
qed

(* self.lecturers\<rightarrow>size() \<equiv> SELECT COUNT *  FROM Enrollment WHERE students = self *)
theorem "eval (MyOCL.Size (MyOCL.As (MyOCL.Var self) MyOCL.LECTURERS)) om
= exec (SelectFromWhere (MySQL.Count MySQL.LECTURERS) 
(Table ENROLLMENT)
(WHERE (MySQL.Eq (MySQL.Col (MySQL.STUDENTS)) (MySQL.Var self)))) om"
proof (induct om)
case (OM ps es)
from this have "(mapEnrollmentToValList es) = [TEnrollment (OM ps es)]" 
using TEnrollmentToValList by simp
then show ?case
proof (induct es)
  case Nil
  then show ?case by simp
next
  case (Cons a es)
  then show ?case by simp
qed
qed

(* self.lecturers\<rightarrow>isEmpty() \<equiv> SELECT COUNT * = 0 FROM Enrollment WHERE students = self *)
theorem "eval (MyOCL.IsEmpty (MyOCL.As (MyOCL.Var self) MyOCL.LECTURERS)) om
= exec (SelectFromWhere (MySQL.Eq (MySQL.CountAll) (MySQL.Int 0)) 
(Table ENROLLMENT)
(WHERE (MySQL.Eq (MySQL.Col (MySQL.STUDENTS)) (MySQL.Var self)))) om"
proof (induct om)
case (OM ps es)
from this have "(mapEnrollmentToValList es) = [TEnrollment (OM ps es)]" 
using TEnrollmentToValList by simp
then show ?case
proof (induct es)
  case Nil
  then show ?case by simp
next
  case (Cons a es)
  then show ?case by simp
qed
qed

(* self.lecturers→exists(l|l=caller)  = SELECT COUNT *  > 0 FROM Enrollment WHERE self = students
AND lecturers = caller *)
theorem  "eval (MyOCL.Exists (MyOCL.As (Var self) MyOCL.LECTURERS) (MyOCL.IVar l) 
(MyOCL.Eq (MyOCL.IVar l) (MyOCL.Var caller))) om
= exec ((SelectFromWhere (MySQL.GrtThan (CountAll) (MySQL.Int 0)) (Table ENROLLMENT) 
(WHERE (MySQL.And (MySQL.Eq (MySQL.Var self) (Col col.STUDENTS)) 
(MySQL.Eq (MySQL.Var caller) (Col col.LECTURERS)))))) om"
proof (induct om)
case (OM ps es)
from this have "(mapEnrollmentToValList es) = [TEnrollment (OM ps es)]" 
using TEnrollmentToValList by simp
then show ?case
 proof (induct es)
  case Nil
  then show ?case by simp
next
  case (Cons a es)
  then show ?case by simp
qed
qed

(* Person.allInstances() \<equiv> SELECT Person_id FROM Person *)
theorem "eval (MyOCL.AllInstances PERSON) om
= exec (SelectFrom (MySQL.Col MySQL.ID) (Table MySQL.PERSON)) om"
proof (induct om)
case (OM ps es)
then show ?case 
proof (induct ps)
  case Nil
  then show ?case by simp
  next
  case (Cons a ps)
  then show ?case by simp
qed
qed

(* Person.allInstances() \<rightarrow> exists(p|p.age = 30) 
\<equiv> SELECT COUNT * > 0 FROM Person WHERE age = 30*)
theorem "eval (MyOCL.Exists (MyOCL.AllInstances PERSON) (IVar p) (MyOCL.Eq (MyOCL.Att (MyOCL.IVar p) (MyOCL.AGE)) (MyOCL.Int 30))) om
= exec ((SelectFromWhere (MySQL.GrtThan (CountAll) (MySQL.Int 0)) (Table MySQL.PERSON) 
(WHERE (MySQL.Eq (Col col.AGE) (MySQL.Int 30))))) om"
proof (induct om)
case (OM ps es)
then show ?case
proof (induct ps)
case Nil
  then show ?case by simp
next
case (Cons a ps)
  then show ?case by simp
qed  
qed  

(* ASSUMPTION: Given a collect-then-flatten operator, if the source of this operator is the Person 
list from the Object model and the for each of the Enrollment in the Object model, return
the Person in the LECTURERS side *)       
lemma lem4: "collectPlus (mapPersonListToValList ps) (IVar p) (PEAs (As (IVar p) as.LECTURERS) (a # es))
=  VPerson (getAssociationEnd col.LECTURERS a) # (collectPlus (mapPersonListToValList ps) (IVar p) (PEAs (As (IVar p) as.LECTURERS) es))"
sorry

(* Person.allInstances()\<rightarrow>collect(p|p.lecturers)\<rightarrow>flatten()))
\<equiv> SELECT lecturers FROM Enrollment *)
lemma " eval (CollectPlus (AllInstances PERSON) (IVar p) (MyOCL.As (IVar p) (MyOCL.LECTURERS))) om
= exec (SelectFrom (Col MySQL.LECTURERS) (Table ENROLLMENT)) om"
proof (induct om)
case (OM ps es)
then show ?case
proof (induct es)
case Nil
then show ?case by simp
next
case (Cons a es)
then show ?case using lem4 by simp
qed
qed


(* ASSUMPTION: When join a single Enrollment object with the Person list 
from the Object Model under the on-expression col = ID then
return the tuple contains the Enrollment and the Person rightaway *)  
lemma lem5 : "joinValWithValList (VEnrollment a) (mapPersonListToValList ps) 
(exp.Eq (Col col.LECTURERS) (Col ID))
= [VJoin [VEnrollment a, (VPerson (getAssociationEnd col.LECTURERS a))]]"
sorry

(* Person.allInstances()\<rightarrow>collect(p|p.lecturers\<rightarrow>collect(l|l.email))
\<equiv> SELECT email FROM Person JOIN Enrollment ON Person_id = lecturers *)
lemma "eval (Collect (CollectPlus (AllInstances MyOCL.PERSON) (IVar p) (MyOCL.As (IVar p) (MyOCL.LECTURERS))) 
(IVar l) (MyOCL.Att (IVar l) (MyOCL.EMAIL))) om
= exec (SelectFromJoin (Col MySQL.EMAIL) (Table MySQL.ENROLLMENT) (JOIN (Table MySQL.PERSON) (MySQL.Eq (Col MySQL.LECTURERS) (Col MySQL.ID)))) om"
proof (induct om)
case (OM ps es)
then show ?case
proof (induct es)
case Nil
then show ?case by simp
next
case (Cons a es)
then show ?case using lem4 lem5 by simp
qed
qed
COMMENT *)
end

