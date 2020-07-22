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
(*
lemma "eval (MyOCL.Eq (MyOCL.Att (MyOCL.Var self) MyOCL.AGE) (MyOCL.Int 30)) om
= exec (SelectFromWhere (MySQL.Eq (MySQL.Col (MySQL.AGE)) (MySQL.Int 30))
(Table PERSON)
(WHERE (MySQL.Eq (MySQL.Col (MySQL.ID)) (MySQL.Var self)))) om" 
  apply auto
  done        
*)

(* self.lecturers \<equiv> SELECT lecturers FROM Enrollment WHERE students = self *)
lemma "eval (MyOCL.As (MyOCL.Var self) MyOCL.LECTURERS) om
= exec (SelectFromWhere (MySQL.Col MySQL.LECTURERS) 
(Table ENROLLMENT)
(WHERE (MySQL.Eq (MySQL.Col (MySQL.STUDENTS)) (MySQL.Var self)))) om"
proof (induct om)
  case (OM ps es)
  then show ?case
  proof (induct es)
    case Nil
    then show ?case by simp
  next
    case (Cons a es)
    then show ?case 
      apply auto
      done
  qed
qed

(* self.lecturers\<rightarrow>size() \<equiv> SELECT COUNT *  FROM Enrollment WHERE students = self *)
lemma "eval (MyOCL.Size (MyOCL.As (MyOCL.Var self) MyOCL.LECTURERS)) om
= exec (SelectFromWhere (MySQL.Count MySQL.LECTURERS) 
(Table ENROLLMENT)
(WHERE (MySQL.Eq (MySQL.Col (MySQL.STUDENTS)) (MySQL.Var self)))) om"
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

(* self.lecturers\<rightarrow>isEmpty() \<equiv> SELECT COUNT * = 0 FROM Enrollment WHERE students = self *)
lemma "eval (MyOCL.IsEmpty (MyOCL.As (MyOCL.Var self) MyOCL.LECTURERS)) om
= exec (SelectFromWhere (MySQL.Eq (MySQL.CountAll) (MySQL.Int 0)) 
(Table ENROLLMENT)
(WHERE (MySQL.Eq (MySQL.Col (MySQL.STUDENTS)) (MySQL.Var self)))) om"
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

lemma [simp]: "isTrueVal (VBool (e1 ∧ e2)) = (e1 \<and> e2)" 
proof (cases "e1")
  case True
  then have h1: "e1" by simp
  then show ?thesis 
  proof (cases "e2")
    case True
    then show ?thesis using h1 by simp
    next
      case False
      then show ?thesis by simp
    qed
next
  case False
  then show ?thesis by simp
qed



(* self.lecturers→exists(l|l=caller)  = SELECT COUNT *  > 0 FROM Enrollment WHERE self = students
AND lecturers = caller *)
lemma  "eval (MyOCL.Exists (MyOCL.As (Var self) MyOCL.LECTURERS) (MyOCL.IVar l) 
(MyOCL.Eq (MyOCL.IVar l) (MyOCL.Var caller))) (OM ps es)
= exec ((SelectFromWhere (MySQL.GrtThan (CountAll) (MySQL.Int 0)) (Table ENROLLMENT) 
(WHERE (MySQL.And (MySQL.Eq (MySQL.Var self) (Col col.STUDENTS)) 
(MySQL.Eq (MySQL.Var caller) (Col col.LECTURERS)))))) (OM ps es)"
 proof (induct es)
  case Nil
  then show ?case by simp
next
  case (Cons a list)
  then show ?case 
    by auto
qed

(* Person.allInstances() \<equiv> SELECT Person_id FROM Person *)
lemma "eval (MyOCL.AllInstances PERSON) (OM ps es)
= exec (SelectFrom (MySQL.Col MySQL.ID) (Table PERSON)) (OM ps es)"
apply auto
apply (simp add: TPerson_ValList)
done

lemma filterWithBody_Person_noNeed_Ctx: "filterWithBody (mapPersonListToValList list) (IVar p) (OCLexp.Eq (PEAtt (Att (IVar p) att.AGE)) (OCLexp.Int 30))
= filterWithBody (mapPersonListToValList list) (IVar p) (OCLexp.Eq (Att (IVar p) att.AGE) (OCLexp.Int 30))"
sorry

lemma filterWithBody_Person: "translate oclexp1 = sqlexp1 \<and>
translate oclexp2 = sqlexp2 \<Longrightarrow>
filterWithBody (mapPersonListToValList list) (IVar p) (OCLexp.Eq oclexp1 oclexp2)
= filterPersons (exp.Eq sqlexp1 sqlexp2) list"
sorry


(* Person.allInstances() \<rightarrow> exists(p|p.age = 30) 
\<equiv> SELECT COUNT * > 0 FROM Person WHERE age = 30*)
lemma "eval (MyOCL.Exists (MyOCL.AllInstances PERSON) (IVar p) (MyOCL.Eq (MyOCL.Att (MyOCL.IVar p) (MyOCL.AGE)) (MyOCL.Int 30))) (OM ps es)
= exec ((SelectFromWhere (MySQL.GrtThan (CountAll) (MySQL.Int 0)) (Table PERSON) 
(WHERE (MySQL.Eq (Col col.AGE) (MySQL.Int 30))))) (OM ps es)"
proof (cases ps)
case Nil
  then show ?thesis by auto
next
case (Cons a list)
  then show ?thesis using filterWithBody_Person_noNeed_Ctx filterWithBody_Person by auto
  qed

lemma collectPlus_on_Empty_Enrollment : "flatten (collect valList (IVar p) (PEAs (As (IVar p) as.LECTURERS) [])) = []"
apply(induct valList)
apply simp
apply auto
done

lemma [simp]: "naselectList (xs@ys) exp = (naselectList xs exp) @ (naselectList ys exp)"
apply(induct xs)
apply auto
done

lemma [simp]: "collect (xs@ys) ivar exp = (collect xs ivar exp)@(collect ys ivar exp)"
apply (induct xs)
apply auto
done

(* Person.allInstances()\<rightarrow>collect(p|p.lecturers\<rightarrow>collect(l|l.email))
\<equiv> SELECT email FROM Person JOIN Enrollment ON Person_id = lecturers *)
lemma "eval (Collect (CollectPlus (AllInstances PERSON) (IVar p) (MyOCL.As (IVar p) (MyOCL.LECTURERS))) 
(IVar l) (MyOCL.Att (IVar l) (MyOCL.EMAIL))) (OM ps es)
= exec (SelectFromJoin (Col MySQL.EMAIL) (Table ENROLLMENT) (JOIN (Table PERSON) (MySQL.Eq (Col MySQL.LECTURERS) (Col MySQL.ID)))) (OM ps es)"
apply (simp add: TPerson_ValList TEnrollment_ValList)
proof (induct ps)


qed
end

  


