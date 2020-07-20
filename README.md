# Isabelle OCL2PSQL

The Object Constraint Language (OCL) is a textual, declarative language typically used as part of the UML standard for specifying constraints and queries on models. It is also a contextualized language: its expressions are written in a context provided by a model, called the contextual model.

The Structure Query Language (SQL) is a special-purpose programming language designed for managing data in relational database management systems.

In this project, we propose a formalization of evaluating an OCL expression, executing an SQL statement under our contextual model and prove the correctness of our mapping, using an automated proof assistant Isabelle/HOL.

Please note that this is an on-going project.

==================
## 20th Jul, 2020

### The context
In this version, we assume the following contextual model:
- The model has 1 table Person with 2 attributes: age of type int and email of type string. Then, the datatype Person has 2 constructors, the first one takes three arguments of attributes - representing an actual Person object while the second one takes no argument - representing an invalid Person.
```ocaml
(* Person (Person_id, age, string) *) 
datatype Person = P string nat string | PNULL
``` 
- There is an many-to-many association called Enrollment which specifies the relationship between persons with persons. This datatype acts similar to the way SQL design association tables with the foreign keys refer to the primary keys
of the association end tables. 
```ocaml
(* Enrollment (lectures, students) *)
datatype Enrollment = E string string
```
- Finally, the contextual instance model, also knows as Object model, including a list of Persons and a list of Enrollments. It is important to note that OCL and SQL in our case share the same contextual model.
```ocaml
datatype Objectmodel = OM "Person list" "Enrollment list"
```

### Structure
In general, our formalization is in four-fold:
- ObjectModel.thy: formalization of the contextual model and its instance.
- MySQL.thy: formalization of SQL-select statement.
- MyOCL.thy: formalization of OCL expression.
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
So far, under our formulization, we have been able to prove the following properties:
```ocaml
(* self = caller === SELECT self = caller *)
(* self.age = 30 === SELECT age = 30 FROM Person WHERE id = self *)
(* self.lecturers === SELECT lecturers FROM Enrollment WHERE students = self *)
(* self.lecturers->size() === SELECT COUNT (*) FROM Enrollment WHERE students = self *)
(* self.lecturers->isEmpty() === SELECT COUNT (*) = 0 FROM Enrollment WHERE students = self *)
(* self.lecturers->exists(l|l=caller) === SELECT COUNT(*) > 0 FROM Enrollment WHERE self = students AND lecturers = caller *)
(* Person.allInstances()->exists(p|p.age = 30) 
=== SELECT COUNT (*) > 0 FROM Person WHERE age = 30*)
```
The proofs were carried out by Isar.
