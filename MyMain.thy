theory MyMain
  imports Main MyOCL MySQL OCLtoSQL
  begin 

(* self = caller \<equiv> SELECT self = caller *)
theorem "eval (MyOCL.Eq (MyOCL.Var self) (MyOCL.Var caller)) om 
= exec (Select (MySQL.Eq (MySQL.Var self) (MySQL.Var caller))) om"
proof -
  show ?thesis by simp      
qed     

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

end

