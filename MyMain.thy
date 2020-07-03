theory MyMain
  imports Main MyOCL MySQL
begin

(* Person(id, age, email) *)
datatype Person = P string int string
type_synonym persons = "Person list" 

datatype val =  VInt int | VString string 
  |  VBool bool |  VPerson Person | VList vlist
and vlist = VNil | VCons val vlist

fun proj :: "col \<Rightarrow> Person \<Rightarrow> val" where
"proj (AGE) (P pid page pemail) = VInt page" |
"proj (EMAIL) (P pid page pemail) = VString pemail" |
"proj (ID) (P pid page pemail) = VString pid" 

fun ext :: "var \<Rightarrow> col \<Rightarrow> persons \<Rightarrow> val" where
"ext v col Nil = VString ''null''" |
"ext v col (Cons (P pid page pemail) ps) 
  = 
(if (v = pid) then (proj col (P pid page pemail))  
else (ext v col ps))"

fun equalVal :: "val \<Rightarrow> val \<Rightarrow> bool" where
"equalVal (VInt i1) (VInt i2) = (i1 = i2)" |
"equalVal (VBool b1) (VBool b2) = (b1 \<longleftrightarrow> b2)" |
"equalVal (VString s1) (VString s2) = (s1 = s2)" |
"equalVal (VPerson p1) (VPerson p2) = (p1 = p2)" |
"equalVal (VList VNil) (VList VNil) = True" |
"equalVal (VList (VCons v1 v1s)) (VList (VCons v2 v2s)) = 
(if (equalVal v1 v2) then (equalVal (VList v1s) (VList v2s)) else False)" |
"equalVal _ _ = False" 

function (sequential) exec :: "SQLstm \<Rightarrow> persons \<Rightarrow> val" where
"exec (Select (MySQL.Int i)) ps  = VInt i" |
"exec (Select (MySQL.Var v)) ps = VString v" |
"exec (Select (MySQL.Col _)) ps = VString ''null''" |
"exec (Select (MySQL.Eq (MySQL.Var v1) (MySQL.Var v2))) ps = 
VBool (v1 = v2)" |
"exec (Select (MySQL.Eq (MySQL.Int i1) (MySQL.Int i2))) ps = 
VBool (i1 = i2)" |
"exec (Select (MySQL.Eq (MySQL.Col c1) (MySQL.Col c2))) ps = 
VBool (c1 = c2)" |
"exec (Select (MySQL.Eq _ _)) ps = VBool False" |
(* TBC: partial definition *)
"exec (SelectFrom _ _) ps = VBool False" |
(* FROM_WHERE *)
"exec (SelectFromWhere (MySQL.Col col) (FROM table1) 
(WHERE (MySQL.Eq (MySQL.Col col2) (MySQL.Var v)))) ps
= (if isID col2 table1 
then (ext v col ps) 
else VBool False)" |

"exec (SelectFromWhere (MySQL.Eq (MySQL.Col col1) (MySQL.Int i)) 
(FROM table) 
(WHERE (MySQL.Eq (MySQL.Col col2) (MySQL.Var v)))) ps
= VBool (equalVal (exec (SelectFromWhere (MySQL.Col col1) (FROM table) 
(WHERE (MySQL.Eq (MySQL.Col col2) (MySQL.Var v)))) ps ) (VInt i))" |

"exec _ ps = VBool False"
by pat_completeness auto
termination by size_change

fun trans :: "MyOCL.att \<Rightarrow> MySQL.col" where
"trans MyOCL.AGE = MySQL.AGE" |
"trans MyOCL.EMAIL = MySQL.EMAIL" |
"trans MyOCL.ID = MySQL.ID" 

fun eval :: "OCLexp \<Rightarrow> persons \<Rightarrow> val" where
"eval (MyOCL.Int i) ps = VInt i" |
"eval (MyOCL.Var x) ps = VString x" |
"eval (MyOCL.Eq e1 e2) ps = 
VBool (equalVal (eval e1 ps) (eval e2 ps))" |
"eval (MyOCL.Att v att) ps 
= ext v (trans att) ps"

(* self = caller *)
lemma "\<forall> self caller om. eval (MyOCL.Eq (MyOCL.Var self) (MyOCL.Var caller)) om 
= exec (Select (MySQL.Eq (MySQL.Var self) (MySQL.Var caller))) om"
proof auto
qed

(* self.age = 30 *)
lemma "\<forall> om self. eval (MyOCL.Eq (MyOCL.Att self MyOCL.AGE) (MyOCL.Int 30)) om
= exec (SelectFromWhere (MySQL.Eq (MySQL.Col (MySQL.AGE)) (MySQL.Int 30))
(FROM table)
(WHERE (MySQL.Eq (MySQL.Col (MySQL.ID)) (MySQL.Var self)))) om"
proof auto
qed

end
  


