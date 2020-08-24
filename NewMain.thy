theory NewMain
imports Main NewOCL NewSQL NewOCLtoSQL
begin

theorem "OCL2PSQL (eval (SINGLETYPE (OCLNatLiteralExp i)) om) = exec (SELECT (SQLNatSelItem i)) om"
by auto

theorem "OCL2PSQL (eval (SINGLETYPE (OCLStringLiteralExp s)) om) = exec (SELECT (SQLStringSelItem s)) om"
by auto

theorem "OCL2PSQL (eval (SINGLETYPE (OCLBoolLiteralExp b)) om) = exec (SELECT (SQLBoolSelItem b)) om"
by auto

theorem "OCL2PSQL (eval (COLLECTIONTYPE (OCLAllInstancesExp NewOCL.PERSON)) om) = exec (SELECTFROM (SQLColSelItem (PCol ID)) (NewSQL.PERSON)) om"
proof (induct om)
case (OBJECTMODEL ps es)
then show ?case 
proof (induct ps)
  case Nil
  then show ?case by simp
next
  case (Cons a ps)
  then show ?case by simp
qed
qed

theorem "OCL2PSQL (eval (SINGLETYPE (OCLSizeExp (OCLAllInstancesExp NewOCL.PERSON))) om) = exec (SELECTFROM (SQLCount (PCol ID)) (NewSQL.PERSON)) om"
proof (induct om)
case (OBJECTMODEL ps es)
then show ?case 
proof (induct ps)
  case Nil
  then show ?case by simp
next
  case (Cons a ps)
  then show ?case by simp
qed
qed

theorem "OCL2PSQL (eval (SINGLETYPE (OCLIsEmptyExp (OCLAllInstancesExp NewOCL.PERSON))) om) = exec (SELECTFROM (SQLEq (SQLCount (PCol ID)) (SQLNatSelItem 0)) (NewSQL.PERSON)) om"
proof (induct om)
case (OBJECTMODEL ps es)
then show ?case 
proof (induct ps)
  case Nil
  then show ?case by simp
next
  case (Cons a ps)
  then show ?case by simp
qed
qed

theorem "OCL2PSQL (eval (SINGLETYPE (OCLIsNotEmptyExp (OCLAllInstancesExp NewOCL.PERSON))) om) = exec (SELECTFROM (SQLNotEq (SQLCount (PCol ID)) (SQLNatSelItem 0)) (NewSQL.PERSON)) om"
proof (induct om)
case (OBJECTMODEL ps es)
then show ?case 
proof (induct ps)
  case Nil
  then show ?case by simp
next
  case (Cons a ps)
  then show ?case by simp
qed
qed

end