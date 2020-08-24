theory NewSQL
imports NewObjectModel Main "~~/src/HOL/Library/Multiset"
begin

datatype personColName = ID | AGE | EMAIL

datatype enrollmentColName = STUDENTS | LECTURERS

datatype col = PCol personColName | ECol enrollmentColName

datatype selitem = SQLNatSelItem nat 
| SQLStringSelItem string 
| SQLBoolSelItem bool
| SQLColSelItem col 
| SQLCount col 
| SQLEq selitem selitem
| SQLNotEq selitem selitem

datatype fromItem = PERSON | ENROLLMENT

datatype SQLstm = SELECT selitem
| SELECTFROM selitem fromItem

datatype row = RowNat nat | RowString string | RowBool bool

fun selectSelItemWithoutObjectModel :: "selitem \<Rightarrow> row" where
"selectSelItemWithoutObjectModel (SQLNatSelItem n) = RowNat n"
| "selectSelItemWithoutObjectModel (SQLStringSelItem s) = RowString s"
| "selectSelItemWithoutObjectModel (SQLBoolSelItem b) = RowBool b"

fun projPerson :: "personColName \<Rightarrow> Person \<Rightarrow> row" where
"projPerson ID p = RowString (getIdPerson p)"
|"projPerson AGE p = RowNat (getAgePerson p)"
|"projPerson EMAIL p = RowString (getEmailPerson p)"

fun selectSelItemWithPERSON :: "selitem \<Rightarrow> Person \<Rightarrow> row" where
"selectSelItemWithPERSON (SQLNatSelItem n) p = RowNat n"
| "selectSelItemWithPERSON (SQLStringSelItem s) p = RowString s"
| "selectSelItemWithPERSON (SQLBoolSelItem b) p = RowBool b"
| "selectSelItemWithPERSON (SQLColSelItem v) p = (case v of PCol col \<Rightarrow> projPerson col p)"

fun selectSelItemWithPERSONList :: "selitem \<Rightarrow> Person list \<Rightarrow> row multiset" where
"selectSelItemWithPERSONList selitem [] = {#}"
| "selectSelItemWithPERSONList selitem (p#ps) = {# selectSelItemWithPERSON selitem p #} + selectSelItemWithPERSONList selitem ps"

fun selectSelItemWithFromItem :: "selitem \<Rightarrow> fromItem \<Rightarrow> ObjectModel \<Rightarrow> row multiset" where
"selectSelItemWithFromItem selitem PERSON om = selectSelItemWithPERSONList selitem (getPersonList om)"

fun exec :: "SQLstm \<Rightarrow> ObjectModel \<Rightarrow> row multiset" where
"exec (SELECTFROM (SQLCount col) fromItem) om = {# RowNat (size (selectSelItemWithFromItem (SQLColSelItem (col)) fromItem om)) #}"
| "exec (SELECTFROM (SQLEq (SQLCount col) (SQLNatSelItem i)) fromItem) om = {# RowBool ((size (selectSelItemWithFromItem (SQLColSelItem (col)) fromItem om)) = i) #}"
| "exec (SELECTFROM (SQLNotEq (SQLCount col) (SQLNatSelItem i)) fromItem) om = {# RowBool ((size (selectSelItemWithFromItem (SQLColSelItem (col)) fromItem om)) \<noteq> i) #}"

| "exec (SELECT selitem) om = {# selectSelItemWithoutObjectModel selitem #}"
| "exec (SELECTFROM selitem fromItem) om = selectSelItemWithFromItem selitem fromItem om"

end