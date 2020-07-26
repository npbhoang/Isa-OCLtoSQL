# Isabelle OCL2PSQL

The Object Constraint Language (OCL) is a textual, declarative language typically used as part of the UML standard for specifying constraints and queries on models. It is also a contextualized language: its expressions are written in a context provided by a model, called the contextual model.

The Structure Query Language (SQL) is a special-purpose programming language designed for managing data in relational database management systems.

In this project, we propose a formalization of evaluating an OCL expression, executing an SQL statement under our contextual model and prove the correctness of our mapping, using an automated proof assistant Isabelle/HOL.

Please note that this is an on-going project.

==================
## v1.0.2, 26th Jul, 2020

### The context
In this version, we assume the following contextual model:
- The model has a table Person with two attributes: age of type nat and email of type string. Then, the datatype Person has two constructors, the first one takes two arguments of attributes - representing an actual Person object while the second one takes no argument - representing an invalid Person.
We have decided to remove the identifier to make the contextual model definition more precise.
```ocaml
(* Person (ge, string) *) 
datatype Person = P nat string | PNULL
``` 
- There is an many-to-many association called Enrollment which specifies the relationship between persons with persons. Accordingly, we changed from having two foreign keys to having two actual Persons. This, of course, make the definition of contextual model more precise.
```ocaml
(* Enrollment (lectures, students) *)
datatype Enrollment = E Person Person
```
- Finally, the contextual instance model, also knows as Object model, including a list of Persons and a list of Enrollments. It is important to note that OCL and SQL in our case share the same contextual model.
```ocaml
datatype Objectmodel = OM "Person list" "Enrollment list"
```

### The SQL-select statement
We have decided to add one simple full inner JOIN for SQLstm. An SQL-select statement is of the form:
```ocaml
datatype SQLstm = Select exp (* SELECT-expression without context *)
  | SelectFrom exp fromItem (* SELECT-expression with a FROM-clause *)
  | SelectFromWhere exp fromItem whereClause (* SELECT-expression with a FROM-clause and a WHERE-clause *)
  | SelectFromJoin exp fromItem joinClause (* SELECT-expression with a JOIN-clause between two tables, for the time being, they are a Entity table and a related Associaiton table *)
datatype whereClause = WHERE exp
datatype fromItem = Table table
datatype table = PERSON | ENROLLMENT
```
where exp is of the form:
```ocaml
datatype exp = Int nat (* a natural number literal *)
  | Var var (* a variable *)
  | Eq exp exp (* an equality expression *)
  | GrtThan exp exp (* a greater than expression *)
  | And exp exp (* a logical and expression *)
  | Col col (* a column expression *)
  | Count col (* an aggregator COUNT with a column argument *) 
  | CountAll (* an aggregator COUNT *)
datatype col = AGE | EMAIL | ID | LECTURERS | STUDENTS
```
For example:
```ocaml
(* SELECT 1 *)
Select (Int 1)
(* SELECT COUNT (*) = 0 FROM Person *)
SelectFrom (IsEmpty (CountAll) (Int 0)) (Table PERSON)
(* SELECT email FROM Person WHERE age = 20 *)
SelectFromWhere (Col EMAIL) (Table PERSON) (WHERE (Eq (Col AGE) (Int 20))
```

### The OCL expression
An OCL expression is of the form:
```ocaml
datatype OCLexp = Int nat (* a natural number literal *)
  | Var var (* a variable *)
  | Eq OCLexp OCLexp (* an equality expression *)
  | IVar ivar (* a iterator *)
  | Att OCLexp att (* an attribute call expression *)
  | As OCLexp as (* an association call expression *)
  | Size OCLexp (* a size operator *)
  | IsEmpty OCLexp (* an isEmpty operator *)
  | Exists OCLexp OCLexp OCLexp (* an exists operator, it takes a source expression, an iterator and a body expression, respectively *)
  | PEAtt OCLexp (* partial evaluation expression, it takes an attribute expression to be partially evaluated *)
  | PEAs OCLexp "Enrollment list" (* partial evaluation expression, it takes an association expression to be partially evaluated and the Enrollment lsit from the Object Model*)
  | AllInstances table (* allInstances operator *)
  | Collect OCLexp OCLexp OCLexp (* collect operator *)
  | CollectPlus OCLexp OCLexp OCLexp (* collect with the body returns a collect-type, then flatten afterwards*)
```
where
```ocaml
type_synonym var = string
type_synonym ivar = string
datatype att = AGE | EMAIL | ID
datatype as = LECTURERS | STUDENTS
```
For example:
```ocaml
(* Person.allInstances() *)
AllInstances PERSON
(* Person.allInstances()->isEmpty() *)
IsEmpty (AllInstances PERSON)
(* Person.allInstances()->exists(l|l.age = 20) *)
Exists (AllInstances PERSON) (IVar l) (Eq (Att (IVar l) (AGE)) (Int 20))
```

### Structure
In general, our formalization is in five-fold:
- ObjectModel.thy: formalization of the contextual model and its instance.
- MySQL.thy: formalization of SQL-select statement.
- MyOCL.thy: formalization of OCL expression.
- OCLtoSQL.thy: formalization of the "bridge" between OCL and SQL.
- MyMain.thy: formalization of the mapping between SQL and OCL.

### Main idea 
Given the same contextual instance model O, given an OCL expression exp, the SQL select-statement q is said to be semantacially equivalent to exp
if and only if the execution of q on O is "equal" to the evaluation of exp on O. 
```ocaml
exec(q,O) = eval(exp,O)
```
In specific, the following functions are defined:
- In MyOCL.thy: The evaluation function takes an OCL expression, an object model and return a list of values.
```ocaml
fun eval :: "OCLexp => Objectmodel => val list"
```
- In MySQL.thy: The execution function takes an SQL select statement, an object model and return a list of values.
```ocaml
fun exec :: "SQLstm => Objectmodel => val list"
```

- For the datatype val (stands for value):
```ocaml
datatype val = VNULL  (* a null value *)
  | VInt nat (* a natural number value *)
  | VString string (* a string value *)
  | VBool bool (* a boolean value *)
  | VPerson Person (* a Person *)
  | VEnrollment Enrollment (* an Enrollment *)
  | VList "val list" (* a collection of values *)
  | TPerson Objectmodel (* all Persons in object model *)
  | TEnrollment Objectmodel (* all Enrollments in object model *)
  | VObj string (* an assignment value of a variable *)
  | VIVar string (* an assigment value of a iterator *)
```

### The proof
For example, here is the formal proof for ```{ocaml}self.lecturers->isEmpty() === SELECT COUNT (*) = 0 FROM Enrollment WHERE students = self```:
```ocaml
lemma "eval (MyOCL.IsEmpty (MyOCL.As (MyOCL.Var self) MyOCL.LECTURERS)) om 
= 
exec (SelectFromWhere 
(MySQL.Eq (MySQL.CountAll) (MySQL.Int 0)) 
(Table ENROLLMENT) 
(WHERE (MySQL.Eq (MySQL.Col (MySQL.STUDENTS)) (MySQL.Var self)))) om"

proof (induct om) (* apply structural induction on the object model *)
  case (OM ps es) (* there is only one case *)
  then show ?case
  proof (induct es) (* apply induction on es *)
    case Nil
    then show ?case by simp
  next
    case (Cons a es)
    then show ?case by simp
  qed
qed
```

So far, under our formulization, we have been able to prove the following properties:
```ocaml
(* self = caller === SELECT self = caller *)
(* self.age = 30 === SELECT age = 30 FROM Person WHERE id = self *)
(* self.lecturers === SELECT lecturers FROM Enrollment WHERE students = self *)
(* self.lecturers->size() === SELECT COUNT (*) FROM Enrollment WHERE students = self *)
(* self.lecturers->isEmpty() === SELECT COUNT (*) = 0 FROM Enrollment WHERE students = self *)
(* self.lecturers->exists(l|l=caller) === SELECT COUNT(*) > 0 FROM Enrollment WHERE self = students AND lecturers = caller *)
(* Person.allInstances()->exists(p|p.age = 30) === SELECT COUNT (*) > 0 FROM Person WHERE age = 30*)
(* Person.allInstances()->collect(p|p.lecturers)->flatten()))
=== SELECT lecturers FROM Enrollment *)
(* Person.allInstances()->collect(p|p.lecturers)->flatten()->collect(l|l.email)
=== SELECT email FROM Person JOIN Enrollment ON Person_id = lecturers *)
```
The proofs were carried out by Isar.
