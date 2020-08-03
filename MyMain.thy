theory MyMain
  imports Main MyOCL MySQL OCLtoSQL "~~/src/HOL/Library/Multiset"
begin 

(* ASSUMPTION: ID IS UNIQUE FOR PERSON *)
lemma [simp]: "(getIdPerson a = getIdPerson p) \<longleftrightarrow> (a = p)"
  sorry

(*
lemma [simp]: "getIdPerson a \<noteq> getIdPerson p \<Longrightarrow> a \<noteq> p"
  sorry
*)

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

lemma [simp]: "stripAlias (xs@ys) = (stripAlias xs) @ (stripAlias ys)"
proof (induct xs)
case Nil
then show ?case by simp
next
case (Cons a xs)
then show ?case by simp
qed

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

lemma [simp]: "MySQL.isUnique (RTuple
       [(ID, RID (PID (getIdPerson a))), (col.AGE, RInt (getAgePerson a)),
        (col.EMAIL, RString (getEmailSQLPerson (mapPersonToSQLPerson a)))]) 
(mapPersonListToRowList (mapPersonListToSQLPersonList x1a)) = OCLtoSQL.isUnique a x1a"
proof (induct x1a)
  case Nil
  then show ?case by simp
next
  case (Cons x x1a)
  then show ?case by simp
qed

lemma [simp]: "isValid (mapPersonListToRowList (mapPersonListToSQLPersonList x1a)) = validPersonList x1a"
proof (induct x1a)
  case Nil
  then show ?case by simp
next
  case (Cons a x1a)
  then show ?case by auto
qed

(*self.age \<equiv> SELECT age FROM Person WHERE Person_id = self *)
theorem "(valid self (getPersonList om)) \<and> (validPersonList (getPersonList om)) 
\<Longrightarrow> (stripAlias (OCL2PSQL (eval (MyOCL.Att (MyOCL.Var self) (MyOCL.AGE)) om))    
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
    then show ?case by auto
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
theorem "(valid self (getPersonList om)) \<and> (validPersonList (getPersonList om)) \<Longrightarrow> 
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
    then show ?case by auto
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
    then show ?case by auto
  qed
qed

(* self.lecturers\<rightarrow>size() \<equiv> SELECT COUNT *  FROM Enrollment WHERE students = self *)
theorem "(valid self (getPersonList om)) \<Longrightarrow> (stripAlias (OCL2PSQL (eval (MyOCL.Size (MyOCL.As (MyOCL.Var self) MyOCL.LECTURERS)) om))
= stripAlias (exec (SelectFromWhere (MySQL.CountAll) 
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
    then show ?case by auto
  qed
qed


(* self.lecturers\<rightarrow>isEmpty() \<equiv> SELECT COUNT * = 0 FROM Enrollment WHERE students = self *)
theorem "valid self (getPersonList om) \<Longrightarrow> (stripAlias (OCL2PSQL (eval (MyOCL.IsEmpty (MyOCL.As (MyOCL.Var self) MyOCL.LECTURERS)) om)))
= stripAlias (exec (SelectFromWhere (MySQL.Eq (MySQL.CountAll) (MySQL.Int 0)) 
(Table ENROLLMENT)
(WHERE (MySQL.Eq (MySQL.Col (MySQL.STUDENTS)) (MySQL.Var self)))) (map om))"
proof (induct om)
case (OM ps es)
then show ?case
  proof (induct es)
    case Nil
    then show ?case by simp
  next
    case (Cons a es)
    then show ?case by auto
  qed
qed

(* self.lecturers→exists(l|l=caller)  = SELECT COUNT *  > 0 FROM Enrollment WHERE self = students
AND lecturers = caller *)
theorem "valid self (getPersonList om) \<and> valid caller (getPersonList om) \<Longrightarrow> (stripAlias (OCL2PSQL (eval (MyOCL.Exists (MyOCL.As (Var self) MyOCL.LECTURERS) (MyOCL.IVar l) 
(MyOCL.Eq (MyOCL.IVar l) (MyOCL.Var caller))) om))
= stripAlias (exec ((SelectFromWhere (MySQL.GrtThan (CountAll) (MySQL.Int 0)) (Table ENROLLMENT) 
(WHERE (MySQL.And (MySQL.Eq (Col col.STUDENTS) (MySQL.Var self)) 
(MySQL.Eq (Col col.LECTURERS) (MySQL.Var caller)))))) (map om)))"
proof (induct om)
case (OM ps es)
then show ?case
 proof (induct es)
  case Nil
  then show ?case by simp
next
  case (Cons a es)
  then show ?case by auto
qed
qed

(* Person.allInstances() \<equiv> SELECT Person_id FROM Person *)
theorem "stripAlias (OCL2PSQL (eval (MyOCL.AllInstances PERSON) om))
= stripAlias (exec (SelectFrom (MySQL.Col MySQL.ID) (Table MySQL.PERSON)) (map om))"
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

theorem "stripAlias (OCL2PSQL (eval (MyOCL.Exists (MyOCL.AllInstances PERSON) (IVar p) (MyOCL.Eq
(MyOCL.Att (MyOCL.IVar p) (MyOCL.AGE)) (MyOCL.Int 30))) om))
= stripAlias (exec (SelectFromWhere (MySQL.GrtThan (CountAll) (MySQL.Int 0)) (Table MySQL.PERSON) 
(WHERE (MySQL.Eq (Col col.AGE) (MySQL.Int 30)))) (map om))"
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

lemma [simp]: "collectPlus source ivar (PEAs (As (IVar p) as.LECTURERS) []) = []"
proof (induct source)
  case Nil
  then show ?case by simp
next
  case (Cons a source)
  then show ?case by simp
qed


lemma [simp]: "getPersonListFromValList (mapPersonListToValList ps) = ps"
proof (induct ps)
  case Nil
  then show ?case by simp
next
  case (Cons a ps)
  then show ?case by simp
qed

(*
lemma [simp]: "validPersonList ps ⟹ 
isPersonInPersonList (getAssociationEnd as.STUDENTS a) ps ⟹
 collectAux (mapPersonListToValList ps) (IVar p) (PEAs (As (IVar p) as.LECTURERS) [a]) 
= [VPerson (getAssociationEnd as.LECTURERS a)]"
proof (induct ps)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  then show ?case by simp
qed
*)

(*
lemma [simp]: "(validPersonList ps) \<and> (isEnrollmentInPersonList a ps) \<Longrightarrow>
collectAux (mapPersonListToValList ps) (IVar p) (PEAs (As (IVar p) as.LECTURERS) [a])
= [VPerson (getAssociationEnd as.LECTURERS a)]"
proof (induct ps)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  then show ?case by simp
qed
*)

fun isValidOM :: "Objectmodel \<Rightarrow> bool" where
"isValidOM (OM ps es) = ((validPersonList ps) \<and> (validEnrollmentList es ps))"

fun listToBag :: "'a list \<Rightarrow> 'a multiset" where
"listToBag [] = {#}"
| "listToBag (v#vs) =  {# v #} + (listToBag vs)"

lemma [simp]: "listToBag (xs@ys) = (listToBag xs) + (listToBag ys)"
  sorry

lemma [simp]: "validPersonList ps ∧ 
isPersonInPersonList (getAssociationEnd as.STUDENTS a) ps \<and>
isPersonInPersonList (getAssociationEnd as.LECTURERS a) ps
\<Longrightarrow>
listToBag (collectPlus (mapPersonListToValList ps) (IVar p) (PEAs (As (IVar p) as.LECTURERS) (a # es)))
= listToBag ((VPerson (getAssociationEnd as.LECTURERS a))#(collectPlus (mapPersonListToValList ps) (IVar p)
(PEAs (As (IVar p) as.LECTURERS) es)))" 
proof (induct ps)
  case Nil
  then show ?case by simp
next
  case (Cons a ps)
  then show ?case sorry
qed


(* Person.allInstances() \<rightarrow> collect(p|p.lecturers)\<rightarrow>flatten()))
\<equiv> SELECT lecturers FROM Enrollment *)
theorem thm1: "(isValidOM om) \<Longrightarrow> (stripAlias 
(OCL2PSQL ( eval (CollectPlus (AllInstances PERSON) (IVar p) (MyOCL.As (IVar p) (MyOCL.LECTURERS))) om))
= stripAlias (exec (SelectFrom (Col MySQL.LECTURERS) (Table ENROLLMENT)) (map om)))"
proof (induct om)
case (OM ps es)
then show ?case
  proof (induct es)
    case Nil
    then show ?case by simp
  next
    case (Cons a es)
    then show ?case sorry
  qed
qed

(* Person.allInstances()\<rightarrow>collect(p|p.lecturers\<rightarrow>collect(l|l.email))
\<equiv> SELECT email FROM Person JOIN Enrollment ON Person_id = lecturers *)
theorem "(isValidOM om) \<Longrightarrow> (stripAlias (OCL2PSQL (eval (Collect (CollectPlus 
(AllInstances MyOCL.PERSON) (IVar p) (MyOCL.As (IVar p) (MyOCL.LECTURERS))) 
(IVar l) (MyOCL.Att (IVar l) (MyOCL.EMAIL))) om))
= stripAlias (exec (SelectFromJoin (Col MySQL.EMAIL) (Table MySQL.PERSON) 
(JOIN (Table MySQL.ENROLLMENT) (MySQL.Eq (Col MySQL.ID) (Col MySQL.LECTURERS)))) (map om)))"
proof (induct om)
case (OM ps es)
then show ?case
  proof (induct es)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  then show ?case sorry
  qed
qed

end

