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
  | Collect OCLexp OCLexp OCLexp
  (* collect with the body returns a collect-type, then flatten afterwards*)
  | CollectPlus OCLexp OCLexp OCLexp 
  | PEAtt OCLexp
  | PEAs OCLexp "Enrollment list"
  | AllInstances entity

(* COMMENT
fun partialEval :: "OCLexp \<Rightarrow> Objectmodel \<Rightarrow> OCLexp" where
"partialEval (MyOCL.Int i) om = (MyOCL.Int i)"
| "partialEval (MyOCL.Var x) om = (MyOCL.Var x)"
| "partialEval (MyOCL.IVar i) om = (MyOCL.IVar i)"
| "partialEval (MyOCL.Eq e1 e2) om = MyOCL.Eq (partialEval e1 om) (partialEval e2 om)" 
| "partialEval (MyOCL.Att (Var v) att) om = (PEAtt (MyOCL.Att (Var v) att))"
| "partialEval (MyOCL.Att (IVar v) att) om = (PEAtt (MyOCL.Att (IVar v) att))"
| "partialEval (MyOCL.As (Var v) as) om = (PEAs (MyOCL.As (Var v) as) (getEnrollmentList om))"
| "partialEval (MyOCL.As (IVar v) as) om = (PEAs (MyOCL.As (IVar v) as) (getEnrollmentList om))"

fun flatten :: "val \<Rightarrow> val list" where
"flatten (VList vs) = vs" 

COMMENT *)

(* projVal: given a column-expression and a row --either in person or enrollment table--,
it returns the corresonding value *)


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


(*
"projValAs LECTURERS (VPerson p) [] = []"
| "projValAs LECTURERS (VPerson p) (e#es) = 
(if (getAssociationEnd STUDENTS e) = p 
then ((VPerson (getAssociationEnd STUDENTS e))#(projValAs LECTURERS (VPerson p) es))
else (projValAs LECTURERS (VPerson p) es))"
*)
end