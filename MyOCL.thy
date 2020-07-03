theory MyOCL
  imports Main
begin

type_synonym var = string
datatype att = AGE | EMAIL | ID

datatype OCLexp = Int int 
  | Var var 
  | Eq OCLexp OCLexp
  | Att var att
end