theory MyOCL
  imports Main ObjectModel
begin

type_synonym var = string
type_synonym ivar = string
datatype att = AGE | EMAIL


datatype as = LECTURERS | STUDENTS
datatype entity = PERSON

datatype OCLexp = Int nat 
  | Var var 
  | Eq OCLexp OCLexp
  | IVar ivar
  | Att OCLexp att
  | As OCLexp as
  | Size OCLexp
  | IsEmpty OCLexp
  | Exists OCLexp OCLexp OCLexp
  | PEAtt OCLexp
  | PEAs OCLexp "Enrollment list"
  | PEVar var "Person list"
  | AllInstances entity

fun partialEval :: "OCLexp \<Rightarrow> Objectmodel \<Rightarrow> OCLexp" where
"partialEval (MyOCL.Int i) om = (MyOCL.Int i)"
| "partialEval (MyOCL.Eq e1 e2) om = MyOCL.Eq (partialEval e1 om) (partialEval e2 om)" 
| "partialEval (MyOCL.IVar i) om = (MyOCL.IVar i)"
| "partialEval (MyOCL.Var x) om = PEVar x (getPersonList om)"
| "partialEval (MyOCL.Att (IVar v) att) om = (PEAtt (MyOCL.Att (IVar v) att))"
| "partialEval (MyOCL.As (IVar v) as) om = (PEAs (MyOCL.As (IVar v) as) (getEnrollmentList om))"

fun projValAtt :: "att \<Rightarrow> val \<Rightarrow> val" where 
"projValAtt AGE (VPerson p) = VInt (getAgePerson p)"
| "projValAtt EMAIL (VPerson p) = VString (getEmailPerson p)"

fun getAssociationEnd :: "as \<Rightarrow> Enrollment \<Rightarrow> Person" where
"getAssociationEnd STUDENTS (E students lecturers) = students"
  | "getAssociationEnd LECTURERS (E students lecturers) = lecturers"

fun projValAs :: "as \<Rightarrow> val \<Rightarrow> Enrollment list \<Rightarrow> val list" where
"projValAs LECTURERS (VPerson p) [] = []"
| "projValAs LECTURERS (VPerson p) (e#es) = 
(if (getAssociationEnd STUDENTS e) = p
then ((VPerson (getAssociationEnd LECTURERS e))#(projValAs LECTURERS (VPerson p) es))
else (projValAs LECTURERS (VPerson p) es))"

end