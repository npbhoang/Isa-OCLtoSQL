theory MyMain
  imports Main MyOCL MySQL
begin

lemma lem4 : "filterWhere (TEnrollment om) 
(WHERE (MySQL.Eq (Col col) (MySQL.Var var)))
= VList (extEnrollment var col (getEnrollmentList om))"
  sorry

lemma lem1 : "filterWhere (TPerson om) 
(WHERE (MySQL.Eq (Col MySQL.ID) (MySQL.Var var)))
= VList [extElement var (getPersonList om)]"
  sorry

lemma lem2 : "proj (Col col) (extElement v ps) 
= ext v col ps"
  apply (induct ps)
   apply simp_all
  done

(* self = caller \<equiv> SELECT self = caller *)
lemma "eval (MyOCL.Eq (MyOCL.Var self) (MyOCL.Var caller)) om 
= exec (Select (MySQL.Eq (MySQL.Var self) (MySQL.Var caller))) om"
  apply auto
  done

(* self.age = 30 \<equiv> SELECT age = 30 FROM Person WHERE id = self *)
lemma " eval (MyOCL.Eq (MyOCL.Att self MyOCL.AGE) (MyOCL.Int 30)) om
= exec (SelectFromWhere (MySQL.Eq (MySQL.Col (MySQL.AGE)) (MySQL.Int 30))
(Table PERSON)
(WHERE (MySQL.Eq (MySQL.Col (MySQL.ID)) (MySQL.Var self)))) om" 
  apply (auto)
   apply (simp_all add: lem1 lem2)
  done

(* self.lecturers \<equiv> SELECT lecturers FROM Enrollment WHERE students = self *)
lemma "eval (MyOCL.As self MyOCL.LECTURERS) (OM ps es)
= exec (SelectFromWhere (MySQL.Col MySQL.LECTURERS) 
(Table ENROLLMENT)
(WHERE (MySQL.Eq (MySQL.Col (MySQL.STUDENTS)) (MySQL.Var self)))) (OM ps es)"
    apply auto
    apply (simp add: lem4)
    apply (induct es)
   apply auto
  done

(* self.lecturers\<rightarrow>size() \<equiv> SELECT COUNT(lecturers) FROM Enrollment WHERE students = self *)
lemma "eval (MyOCL.Size (MyOCL.As self MyOCL.LECTURERS)) (OM ps es)
= exec (SelectFromWhere (MySQL.Count MySQL.LECTURERS) 
(Table ENROLLMENT)
(WHERE (MySQL.Eq (MySQL.Col (MySQL.STUDENTS)) (MySQL.Var self)))) (OM ps es)"
  apply auto
  apply(simp add: lem4)
  apply (induct es)
   apply auto
  done  

end

  


