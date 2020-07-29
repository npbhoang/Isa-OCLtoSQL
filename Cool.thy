theory Cool
imports Main ObjectModel MyOCL MySQL OCLtoSQL
begin

datatype CoolObjectmodel = CoolOM "row list * row list"

fun mapPersonToRow :: "Person \<Rightarrow> row" where
"mapPersonToRow p = 
RTuple [
(Pair MySQL.ID (RID (PID p))),
(Pair MySQL.AGE (RInt (getAgePerson p))),
(Pair MySQL.EMAIL (RString (getEmailPerson p)))
]"

fun mapPersonListToRowList :: "Person list \<Rightarrow> row list" where
"mapPersonListToRowList [] = []"
| "mapPersonListToRowList (p#ps) = (mapPersonToRow p)#(mapPersonListToRowList ps)"

fun mapEnrollmentListToRowList :: "Enrollment list \<Rightarrow> row list" where
"mapEnrollmentListToRowList es = []"

fun mapCool :: "Objectmodel \<Rightarrow> CoolObjectmodel" where
"mapCool (OM ps es) = CoolOM (Pair (mapPersonListToRowList ps) (mapEnrollmentListToRowList es))"

fun getPersonTable :: "CoolObjectmodel \<Rightarrow> row list" where
"getPersonTable (CoolOM pair) = fst pair"

value " isSatisfiedColColumnList [(ID, RID (PID p)), (col.AGE, RInt (getAgePerson p)), (col.EMAIL, RString (getEmailPerson p))]
 (exp.Eq (Col ID) (exp.Var self))"

lemma lem7: "filterWhere (getPersonTable (mapCool (OM ps es))) (WHERE (exp.Eq (Col col.ID) (exp.Var self)))
= ([RTuple [
(Pair MySQL.ID (RID (IDVar self))),
(Pair MySQL.AGE (RInt (getAgePerson (PVObj self)))),
(Pair MySQL.EMAIL (RString (getEmailPerson (PVObj self))))
]])"

  value " filterWhere (getPersonTable (mapCool (OM (a # ps) es))) (WHERE (exp.Eq (Col ID) (exp.Var self)))"

proof (induct ps)
  case Nil
  then show ?case sorry
next
  case (Cons a ps)
  then show ?case 
  proof (cases "isEqualID (PID a) (IDVar self)")
case True
then show ?thesis by simp
next
  case False
then show ?thesis sorry
qed
 

     
qed


end