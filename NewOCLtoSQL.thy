theory NewOCLtoSQL
imports Main NewOCL NewSQL "~~/src/HOL/Library/Multiset"
begin

fun map :: "val \<Rightarrow> row" where
"map (ValNat n) = RowNat n"
| "map (ValString s) = RowString s"
| "map (ValBool b) = RowBool b"
| "map (ValPerson p) = RowString (getIdPerson p)"

fun OCL2PSQL :: "val multiset \<Rightarrow> row multiset" where
"OCL2PSQL vs = image_mset map vs"

end