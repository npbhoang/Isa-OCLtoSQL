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

fun stripAliasCell :: "(col*column) list \<Rightarrow> (col*column) list" where
"stripAliasCell [] = []"
| "stripAliasCell (c#cs) = (Pair PTOP (snd c))#(stripAliasCell cs)"

fun stripAliasRow :: "row \<Rightarrow> row" where
"stripAliasRow (RTuple as) = RTuple (stripAliasCell as)"

fun stripAlias :: "row list \<Rightarrow> row list" where
"stripAlias [] = []"
| "stripAlias (r#rs) = (stripAliasRow r)#(stripAlias rs)"

fun valid :: "string \<Rightarrow> Person list \<Rightarrow> bool" where
"valid s [] = False"
| "valid s (p#ps) = (if (s = (getIdPerson p)) then True else (valid s ps))"

lemma [simp]: "getIdSQLPerson (mapPersonToSQLPerson a) = PID (getIdPerson a)"
proof (induct a)
  case (P pid page pemail)
  then show ?case by simp
next
  case PNULL
  then show ?case by simp
qed

lemma [simp]: "getAgeSQLPerson (mapPersonToSQLPerson a) = getAgePerson a"
proof (induct a)
  case (P pid page pemail)
  then show ?case by simp
next
  case PNULL
  then show ?case by simp
qed 

theorem "(valid self (getPersonList om)) \<Longrightarrow> (stripAlias (OCL2PSQL (eval (MyOCL.Att (MyOCL.Var self) (MyOCL.AGE)) om))    
= stripAlias (exec (SelectFromWhere (MySQL.Col (MySQL.AGE)) (Table MySQL.PERSON) 
(WHERE (MySQL.Eq (MySQL.Col (MySQL.ID)) (MySQL.Var self)))) (map om)))"
proof (induct om)
  case (OM x1a x2a)
  then show ?case 
  proof (induct x1a)
    case Nil
    then show ?case by simp
  next
    case (Cons a x1a)
    then show ?case by simp
  qed
qed


(* KEY THEOREM FOR MAPPING-ASSOCIATIONS *)

lemma [simp] : "getForeignKey col.LECTURERS (mapEnrollmentToSQLEnrollment a) 
= PID (getIdPerson (getAssociationEnd as.LECTURERS a)) "
proof (induct a)
  case (E p1 p2)
  then show ?case by simp
qed

lemma [simp]: "getForeignKey col.STUDENTS (mapEnrollmentToSQLEnrollment a) = 
PID (getIdPerson (getAssociationEnd as.STUDENTS a)) "

proof (induct a)
  case (E p1 p2)
  then show ?case by simp
qed

(* ID IS UNIQUE *)
lemma [simp]: "getIdPerson a = getIdPerson p \<Longrightarrow> a = p"
  sorry

lemma [simp]: "getIdPerson a \<noteq> getIdPerson p \<Longrightarrow> a \<noteq> p"
  sorry

lemma [simp]: "valid i ps ⟹ getIdPerson (getAssignedPerson i ps) = i"
proof (induct ps)
  case Nil
  then show ?case by simp
next
  case (Cons a ps)
  then show ?case by simp
qed


lemma [simp]: "valid (getIdPerson p) ps ⟹ getAssignedPerson (getIdPerson p) ps = p"
proof (induct ps)
  case Nil
  then show ?case by simp
next
  case (Cons a ps)
  then show ?case by simp
qed

theorem "(valid self (getPersonList om)) \<Longrightarrow> (stripAlias (OCL2PSQL (eval (MyOCL.As (MyOCL.Var self) (MyOCL.LECTURERS)) om))    
= stripAlias (exec (SelectFromWhere (MySQL.Col (MySQL.LECTURERS)) (Table MySQL.ENROLLMENT) 
(WHERE (MySQL.Eq (MySQL.Col (MySQL.STUDENTS)) (MySQL.Var self)))) (map om)))"
proof (induct om)
  case (OM x1a x2a)
  then show ?case
  proof (induct x2a)
    case Nil
    then show ?case by simp
  next
    case (Cons a x2a)
    then show ?case by auto
  qed
qed


(* self.age = 30 \<equiv> SELECT age = 30 FROM Person WHERE id = self *)
theorem "(valid self (getPersonList om)) \<Longrightarrow> 
(stripAlias (OCL2PSQL (eval (MyOCL.Eq 
(MyOCL.Att (MyOCL.Var self) MyOCL.AGE) (MyOCL.Int 30)) om))
= stripAlias( exec (SelectFromWhere (MySQL.Eq (MySQL.Col (MySQL.AGE)) (MySQL.Int 30))
(Table MySQL.PERSON)
(WHERE (MySQL.Eq (MySQL.Col (MySQL.ID)) (MySQL.Var self)))) (map om)))" 
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

(* self.lecturers \<equiv> SELECT lecturers FROM Enrollment WHERE students = self *)
theorem "(valid self (getPersonList om)) \<Longrightarrow> (stripAlias(OCL2PSQL (eval (MyOCL.As (MyOCL.Var self) MyOCL.LECTURERS) om))
= stripAlias (exec (SelectFromWhere (MySQL.Col MySQL.LECTURERS) 
(Table ENROLLMENT)
(WHERE (MySQL.Eq (MySQL.Col (MySQL.STUDENTS)) (MySQL.Var self)))) (map om)))"
proof (induct om)
  case (OM ps es)
  then show ?case
  proof (induct es)
    case Nil
    then show ?case by simp
  next
    case (Cons a es)
    then show ?case by simp
  qed
qed

(* COMMENT
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

