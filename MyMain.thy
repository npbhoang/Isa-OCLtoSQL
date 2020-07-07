theory MyMain
  imports Main MyOCL MySQL
begin

(* self = caller *)
lemma "\<forall> self caller om. eval (MyOCL.Eq (MyOCL.Var self) (MyOCL.Var caller)) om 
= exec (Select (MySQL.Eq (MySQL.Var self) (MySQL.Var caller))) om"
proof auto
qed


lemma lem1 : "filterWhere (mapList persons) 
(WHERE (MySQL.Eq (Col MySQL.ID) (MySQL.Var var)))
= VList [extElement var persons]"
  sorry



lemma lem2 : "proj (Col col) (extElement v om) 
= ext v col om"
proof (induct om)
  case Nil
  then show ?case 
    by simp
next
  case (Cons p ps)
then show ?case
  by simp
qed
 
(* self.age = 30 *)
lemma "\<forall> om self. eval (MyOCL.Eq (MyOCL.Att self MyOCL.AGE) (MyOCL.Int 30)) om
= exec (SelectFromWhere (MySQL.Eq (MySQL.Col (MySQL.AGE)) (MySQL.Int 30))
(Table PERSON)
(WHERE (MySQL.Eq (MySQL.Col (MySQL.ID)) (MySQL.Var self)))) om" 
  apply auto
   apply (simp_all add: lem1 lem2)
  done

lemma lem3 : "\<forall> persons var. filterWhere (mapList persons) 
(WHERE (MySQL.Eq (Col MySQL.STUDENTS) (MySQL.Var var)))
= VList [extElement var persons]"
  sorry

lemma singleVal : "val = VList [val]"
  sorry

(* self.lecturers *)
lemma "eval (MyOCL.As self MyOCL.LECTURERS) om
= exec (SelectFromWhere (MySQL.Col MySQL.LECTURERS) 
(Table ENROLLMENT)
(WHERE (MySQL.Eq (MySQL.Col (MySQL.STUDENTS)) (MySQL.Var self)))) om"
  apply auto
  apply(simp_all add: lem3 lem2 singleVal)
  done

(* self.lecturers\<rightarrow>size() *)
lemma "eval (MyOCL.Size (MyOCL.As self MyOCL.LECTURERS)) om
= exec (SelectFromWhere (MySQL.Count MySQL.LECTURERS) 
(Table ENROLLMENT)
(WHERE (MySQL.Eq (MySQL.Col (MySQL.STUDENTS)) (MySQL.Var self)))) om"
   apply auto
  apply(simp_all add: lem3 lem2)
  done



end

  


