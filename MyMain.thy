theory MyMain
  imports Main MyOCL MySQL
begin
datatype Person = P string

datatype val = VInt int | VString string 
  | VBool bool | VPerson Person | VList "val list"

datatype pair = Pair col "string \<Rightarrow> int"

datatype objectModel = OM "pair list"

fun doNothing :: "string \<Rightarrow> int" where
"doNothing s = 0"

function (sequential) findAtt :: "col \<Rightarrow> objectModel \<Rightarrow> (string \<Rightarrow> int)" where
"findAtt _ (OM Nil) = doNothing" |
"findAtt col (OM (Cons (Pair col1 f) xs)) = 
(if equalCol col col1 then f else findAtt col (OM xs))" 
  by pat_completeness auto

fun equalPerson :: "Person \<Rightarrow> Person \<Rightarrow> bool" where
"equalPerson (P s1) (P s2) = (s1 = s2)"

fun equalVal :: "val \<Rightarrow> val \<Rightarrow> bool" where
"equalVal (VInt i1) (VInt i2) = (i1 = i2)" |
"equalVal (VBool b1) (VBool b2) = (b1 \<longleftrightarrow> b2)" |
"equalVal (VString s1) (VString s2) = (s1 = s2)" |
"equalVal (VPerson p1) (VPerson p2) = (p1 = p2)" |
"equalVal (VList Nil) (VList Nil) = True" |
"equalVal (VList (Cons v1 v1s)) (VList (Cons v2 v2s)) = 
(if (equalVal v1 v2) then (equalVal (VList v1s) (VList v2s)) else False)" |
"equalVal _ _ = False" 

function (sequential) exec :: "SQLstm \<Rightarrow> objectModel \<Rightarrow> val" where
"exec (Select (MySQL.Int i)) om = VInt i" |

"exec (Select (MySQL.Var v)) om = VString v" |

"exec (Select (MySQL.Col _)) om = VString ''null''" |

"exec (Select (MySQL.Eq (MySQL.Var v1) (MySQL.Var v2))) om = 
VBool (v1 = v2)" |

"exec (Select (MySQL.Eq (MySQL.Int i1) (MySQL.Int i2))) om = 
VBool (i1 = i2)" |

"exec (Select (MySQL.Eq (MySQL.Col c1) (MySQL.Col c2))) om = 
VBool (c1 = c2)" |

"exec (Select (MySQL.Eq _ _)) om = VBool False" |

"exec (SelectFrom _ _) om = VBool False" |

"exec (SelectFromWhere (MySQL.Col col) (FROM table1) 
(WHERE (MySQL.Eq (MySQL.Col col2) (MySQL.Var v)))) om
= (if isID col2 table1 then VInt ((findAtt col om) v) else VBool False)" |

"exec (SelectFromWhere (MySQL.Eq (MySQL.Col col1) (MySQL.Int i)) 
(FROM table) 
(WHERE (MySQL.Eq (MySQL.Col col2) (MySQL.Var v)))) om
= VBool (equalVal (exec (SelectFromWhere (MySQL.Col col1) (FROM table) 
(WHERE (MySQL.Eq (MySQL.Col col2) (MySQL.Var v)))) om) (VInt i))" |

"exec _ om = VBool False"

  by pat_completeness auto
termination by size_change

fun eval :: "OCLexp \<Rightarrow> objectModel \<Rightarrow> val" where
"eval (MyOCL.Int i) om = VInt i" |
"eval (MyOCL.Var x) om = VString x" |
"eval (MyOCL.Eq e1 e2) om = VBool (equalVal (eval e1 om) (eval e2 om))" |
"eval (MyOCL.Att v col) om = VInt ((findAtt (ATT col) om) v)"

(* self = caller *)
lemma "\<forall> self caller om. eval (MyOCL.Eq (MyOCL.Var self) (MyOCL.Var caller)) om 
= exec (Select (MySQL.Eq (MySQL.Var self) (MySQL.Var caller))) om"
proof auto
qed

(* self.age = 30 *)
lemma "\<forall> om self. eval (MyOCL.Eq (MyOCL.Att self age) (MyOCL.Int 30)) om
= exec (SelectFromWhere (MySQL.Eq (MySQL.Col (ATT age)) (MySQL.Int 30))
(FROM table)
(WHERE (MySQL.Eq (MySQL.Col (ID table)) (MySQL.Var self)))) om"
proof auto
qed

end
  


