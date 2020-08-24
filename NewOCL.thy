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

datatype OCLexp = SINGLE OCLLiteralExp | COL OCLCollectionTypeExp

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

fun evalSingle :: "OCLLiteralExp \<Rightarrow> ObjectModel \<Rightarrow> val multiset" 
and evalCol :: "OCLCollectionTypeExp \<Rightarrow> ObjectModel \<Rightarrow> val multiset"
where
"evalSingle (OCLNatLiteralExp i) om = {# ValNat i #}"
| "evalSingle (OCLStringLiteralExp s) om = {# ValString s #}"
| "evalSingle (OCLBoolLiteralExp b) om = {# ValBool b #}"
| "evalSingle (OCLSizeExp exp) om = {# ValNat (size (evalCol exp om)) #}"
| "evalSingle (OCLIsEmptyExp exp) om = {# ValBool (size (evalCol exp om) = 0) #}"
| "evalSingle (OCLIsNotEmptyExp exp) om = {# ValBool (size (evalCol exp om) \<noteq> 0) #}"
| "evalCol (OCLAllInstancesExp entity) om = evalAllInstances entity om"

fun eval :: "OCLexp \<Rightarrow> ObjectModel \<Rightarrow> val multiset" where
"eval (SINGLE exp) om = evalSingle exp om"
| "eval (COL exp) om = evalCol exp om"


end