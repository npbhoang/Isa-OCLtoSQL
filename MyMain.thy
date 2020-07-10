theory MyMain
  imports Main MyOCL MySQL
begin

(* self = caller \<equiv> SELECT self = caller *)
lemma "eval (MyOCL.Eq (MyOCL.Var self) (MyOCL.Var caller)) om 
= exec (Select (MySQL.Eq (MySQL.Var self) (MySQL.Var caller))) om"
proof -
  show ?thesis by simp
qed

(* self.age = 30 \<equiv> SELECT age = 30 FROM Person WHERE id = self *)
lemma "eval (MyOCL.Eq (MyOCL.Att self MyOCL.AGE) (MyOCL.Int 30)) (OM ps es)
= exec (SelectFromWhere (MySQL.Eq (MySQL.Col (MySQL.AGE)) (MySQL.Int 30))
(Table PERSON)
(WHERE (MySQL.Eq (MySQL.Col (MySQL.ID)) (MySQL.Var self)))) (OM ps es)" 
proof -
  show ?thesis by simp
qed

(* self.lecturers \<equiv> SELECT lecturers FROM Enrollment WHERE students = self *)
lemma "eval (MyOCL.As self MyOCL.LECTURERS) (OM ps es)
= exec (SelectFromWhere (MySQL.Col MySQL.LECTURERS) 
(Table ENROLLMENT)
(WHERE (MySQL.Eq (MySQL.Col (MySQL.STUDENTS)) (MySQL.Var self)))) (OM ps es)"
proof (induct es)
  case Nil
  then show ?case by simp
next
  case (Cons a es)
  then show ?case by simp
qed

(* self.lecturers\<rightarrow>size() \<equiv> SELECT COUNT *  FROM Enrollment WHERE students = self *)
lemma "eval (MyOCL.Size (MyOCL.As self MyOCL.LECTURERS)) (OM ps es)
= exec (SelectFromWhere (MySQL.Count MySQL.LECTURERS) 
(Table ENROLLMENT)
(WHERE (MySQL.Eq (MySQL.Col (MySQL.STUDENTS)) (MySQL.Var self)))) (OM ps es)"
proof (induct es)
  case Nil
  then show ?case by simp
next
  case (Cons a es)
  then show ?case by simp
qed

(* self.lecturers\<rightarrow>isEmpty() \<equiv> SELECT COUNT * = 0 FROM Enrollment WHERE students = self *)
lemma "eval (MyOCL.IsEmpty (MyOCL.As self MyOCL.LECTURERS)) (OM ps es)
= exec (SelectFromWhere (MySQL.Eq (MySQL.CountAll) (MySQL.Int 0)) 
(Table ENROLLMENT)
(WHERE (MySQL.Eq (MySQL.Col (MySQL.STUDENTS)) (MySQL.Var self)))) (OM ps es)"
proof (induct es)
  case Nil
  then show ?case by simp
next
  case (Cons a es)
  then show ?case by simp
qed

(* self.lecturers\<rightarrow>exists(l|l=caller)  = SELECT COUNT *  > 0 FROM Enrollment WHERE self = students
AND lecturers = caller *)
lemma "eval (MyOCL.Exists (MyOCL.As self MyOCL.LECTURERS) (l) 
(MyOCL.Eq (MyOCL.Var l) (MyOCL.Var caller))) (OM ps es)
=
exec ((SelectFromWhere (MySQL.GrtThan (CountAll) (MySQL.Int 0)) (Table ENROLLMENT) 
(WHERE (MySQL.And (MySQL.Eq (MySQL.Var self) (Col col.STUDENTS)) 
(MySQL.Eq (MySQL.Var caller) (Col col.LECTURERS)))))) (OM ps es)"
  apply auto
  apply (induct es)
  sorry

end

  


