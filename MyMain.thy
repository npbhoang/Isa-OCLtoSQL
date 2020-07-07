theory MyMain
  imports Main MyOCL MySQL
begin

(* self = caller *)
lemma "\<forall> self caller om. eval (MyOCL.Eq (MyOCL.Var self) (MyOCL.Var caller)) om 
= exec (Select (MySQL.Eq (MySQL.Var self) (MySQL.Var caller))) om"
  apply auto
  done

lemma lem1 : "filterWhere (mapList persons) 
(WHERE (MySQL.Eq (Col MySQL.ID) (MySQL.Var var)))
= VList [extElement var persons]"
  sorry

lemma lem2 : "proj (Col col) (extElement v om) 
= ext v col om"
  apply (induct om)
   apply simp_all
  done
 
(* self.age = 30 *)
lemma "\<forall> om self. eval (MyOCL.Eq (MyOCL.Att self MyOCL.AGE) (MyOCL.Int 30)) om
= exec (SelectFromWhere (MySQL.Eq (MySQL.Col (MySQL.AGE)) (MySQL.Int 30))
(Table PERSON)
(WHERE (MySQL.Eq (MySQL.Col (MySQL.ID)) (MySQL.Var self)))) om" 
  apply auto
   apply (simp_all add: lem1 lem2)
  done

(* self.lecturers *)
lemma lem3 : "eval (MyOCL.As self MyOCL.LECTURERS) om
= exec (SelectFromWhere (MySQL.Col MySQL.LECTURERS) 
(Table ENROLLMENT)
(WHERE (MySQL.Eq (MySQL.Col (MySQL.STUDENTS)) (MySQL.Var self)))) om"
  sorry

(* self.lecturers\<rightarrow>size() *)
lemma "eval (MyOCL.Size (MyOCL.As self MyOCL.LECTURERS)) om
= exec (SelectFromWhere (MySQL.Count MySQL.LECTURERS) 
(Table ENROLLMENT)
(WHERE (MySQL.Eq (MySQL.Col (MySQL.STUDENTS)) (MySQL.Var self)))) om"
  sorry

end

  


