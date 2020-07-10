theory MyMain
  imports Main MyOCL MySQL
begin

lemma filterEnrollmentsByAssocEnd : "filterWhere ([TEnrollment om]) 
(WHERE (MySQL.Eq (Col col) (MySQL.Var var)))
= (extEnrollments var col (getEnrollmentList om))"
  sorry

lemma filterPersonByID : "filterWhere ([TPerson om]) 
(WHERE (MySQL.Eq (Col MySQL.ID) (MySQL.Var var)))
=  [extElement var (getPersonList om)]"
  sorry

lemma proj_extElement_EQ_ext : "proj (Col col) (extElement v ps) 
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

lemma opp_opp: "opposite (opposite col) = col"
  sorry

lemma ass1 : "filterWhere (TEnrollment (OM ps [])) (WHERE exp) = (VList [])"
  sorry

lemma ass2 : "filterWhere (TEnrollment (OM ps (v#vs))) (WHERE exp) = (
if (isTrue (VList (select (VEnrollment v) exp)))  
    then (appendList (VEnrollment v) (filterWhere (VList (mapEnrollmentToValList vs)) (WHERE exp)))   
    else filterWhere (VList (mapEnrollmentToValList vs)) (WHERE exp))"
  sorry

lemma EqualSize_extEnrollment_extCol : "sizeVal (VList (extEnrollment var col enrollments)) 
= sizeVal (VList (extCol var (opposite col) enrollments))"
  apply(induct enrollments)
   apply(simp)
  apply(simp add: opp_opp)
  done


(* self.lecturers\<rightarrow>size() \<equiv> SELECT COUNT *  FROM Enrollment WHERE students = self *)
lemma "eval (MyOCL.Size (MyOCL.As self MyOCL.LECTURERS)) (OM ps es)
= exec (SelectFromWhere (MySQL.Count MySQL.LECTURERS) 
(Table ENROLLMENT)
(WHERE (MySQL.Eq (MySQL.Col (MySQL.STUDENTS)) (MySQL.Var self)))) (OM ps es)"
  apply auto
  apply(simp_all add: lem4)
  apply (induct es)
   apply auto
  done 


(* self.lecturers\<rightarrow>isEmpty() \<equiv> SELECT COUNT * = 0 FROM Enrollment WHERE students = self *)
lemma "eval (MyOCL.IsEmpty (MyOCL.As self MyOCL.LECTURERS)) (OM ps es)
= exec (SelectFromWhere (MySQL.Eq (MySQL.CountAll) (MySQL.Int 0)) 
(Table ENROLLMENT)
(WHERE (MySQL.Eq (MySQL.Col (MySQL.STUDENTS)) (MySQL.Var self)))) (OM ps es)"
  apply auto
  apply(simp_all add: lem4 EqualSize_extEnrollment_extCol)
  apply(induct es)
  apply auto
  done  

lemma sizeVal_appendList : "sizeVal (appendList (VString s) vs) = Suc (sizeVal vs)"
  apply(induct vs)
  apply(simp_all)
  sorry

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
   apply(simp add:ass1)
  apply auto
  apply (simp add: sizeVal_appendList ass2)
  sorry

end

  


