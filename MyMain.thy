theory MyMain
  imports Main MyOCL MySQL
begin

(* self = caller *)
lemma "\<forall> self caller om. eval (MyOCL.Eq (MyOCL.Var self) (MyOCL.Var caller)) om 
= exec (Select (MySQL.Eq (MySQL.Var self) (MySQL.Var caller))) om"
proof auto
qed


lemma lem1 : "\<forall> persons var. filterWhere (mapList persons) 
(WHERE (MySQL.Eq (Col MySQL.ID) (MySQL.Var var)))
= VList [extElement var persons]"
  sorry

fun equalVar :: "var \<Rightarrow> Person \<Rightarrow> bool" where
"equalVar v (P pid page pemail pstudents plecturers) = (v = pid)"

lemma lemSQL1 : "equalVar v p \<Longrightarrow> 
extElement v (Cons p ps)
 = VPerson p"
  apply (induct p)
  apply (auto)
  done

lemma lemSQL2 : "\<not>equalVar v p \<Longrightarrow> 
extElement v (Cons p ps)
= extElement v ps"
  apply (induct p)
  apply (auto)
  done

lemma lemSQL3 : "equalVar v p \<Longrightarrow> 
ext v col (Cons p ps)
= proj (Col col) (VPerson p)"
  apply (induct p)
  apply auto
  done

lemma lemSQL4 : "\<not>equalVar v p \<Longrightarrow> 
ext v col (Cons p ps)
= ext v col ps"
apply (induct p)
  apply auto
  done

lemma lem2 : "\<forall> col v. proj (Col col) (extElement v om) 
= ext v col om"
proof (induct om)
  case Nil
  then show ?case 
    by simp
next
  case (Cons p ps)
  then show ?case
  proof (cases "equalVar v p")
    case True
    then show ?thesis 
      using lemSQL1 lemSQL2 lemSQL3 lemSQL4 by metis
  next
    case False
    then show ?thesis 
      using lemSQL1 lemSQL2 lemSQL3 lemSQL4 by metis
  qed
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

  


