theory NewOCL
imports NewObjectModel Main "~~/src/HOL/Library/Multiset"
begin

datatype entity = PERSON | ENROLLMENT

datatype OCLCollectionTypeExp = OCLAllInstancesExp entity

datatype OCLLiteralExp = OCLNatLiteralExp nat
| OCLStringLiteralExp string
| OCLBoolLiteralExp bool
| OCLSizeExp OCLCollectionTypeExp
| OCLIsEmptyExp OCLCollectionTypeExp
| OCLIsNotEmptyExp OCLCollectionTypeExp

datatype OCLexp = SINGLETYPE OCLLiteralExp | COLLECTIONTYPE OCLCollectionTypeExp

datatype val =
ValNat nat
| ValString string
| ValBool bool
| ValPerson Person

fun getAllValPersons :: "Person list \<Rightarrow> val multiset" where
"getAllValPersons [] = {#}"
| "getAllValPersons (p#ps) = {#ValPerson p#} + getAllValPersons ps"

fun evalAllInstances :: "entity \<Rightarrow> ObjectModel \<Rightarrow> val multiset" where
"evalAllInstances PERSON om = getAllValPersons (getPersonList om)"

fun evalSingleType :: "OCLLiteralExp \<Rightarrow> ObjectModel \<Rightarrow> val multiset" 
and evalCollectionType :: "OCLCollectionTypeExp \<Rightarrow> ObjectModel \<Rightarrow> val multiset"
where
"evalSingleType (OCLNatLiteralExp i) om = {# ValNat i #}"
| "evalSingleType (OCLStringLiteralExp s) om = {# ValString s #}"
| "evalSingleType (OCLBoolLiteralExp b) om = {# ValBool b #}"
| "evalSingleType (OCLSizeExp exp) om = {# ValNat (size (evalCollectionType exp om)) #}"
| "evalSingleType (OCLIsEmptyExp exp) om = {# ValBool (size (evalCollectionType exp om) = 0) #}"
| "evalSingleType (OCLIsNotEmptyExp exp) om = {# ValBool (size (evalCollectionType exp om) \<noteq> 0) #}"
| "evalCollectionType (OCLAllInstancesExp entity) om = evalAllInstances entity om"

fun eval :: "OCLexp \<Rightarrow> ObjectModel \<Rightarrow> val multiset" where
"eval (SINGLETYPE exp) om = evalSingleType exp om"
| "eval (COLLECTIONTYPE exp) om = evalCollectionType exp om"


end