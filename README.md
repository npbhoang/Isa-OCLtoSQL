# Isabelle OCL2PSQL

The Object Constraint Language (OCL) is a textual, declarative language typically used as part of the UML standard for specifying constraints and queries on models.

The Structure Query Language (SQL) is a special-purpose programming language designed for managing data in relational database management systems. Originally based
upon relational algebra and tuple relational calculus, its scope includes
data insert, query, update and delete, schema creation and modification,
and data access control.

OCL2PSQL represents a mapping from a large set of OCL expression to "pure" SQL select statement.

In this project, we (i) propose a formalization of evaluating an OCL expression, executing an SQL statement and (ii) prove the correctness of our mapping, using an automated proof assistant Isabelle/HOL.

Please note that this is an on-going project.

==================
## v1.0.1, 12th Jul, 2020

Here's what changed:

### The context
- The person datatype is still kept, although we changed the type of age from integer to natural numbers for convenient purpose.
```ocaml
datatype Person = P string nat string | PNULL
```
- More importantly, we added another constructor for Person which is PNULL (for Person null), the reason behind this was to return a null person
for the negative cases of any function that returns Person (for example: *searchPersonById*), but this is unstable and 
is the subject to change in the upcoming iterator.

- We added another datatype, called *Enrollment*, which specifies the relationship between persons with persons. 
This datatype acts similar to the way SQL design association tables with the foreign keys refer to the primary keys
of the association end tables. 
```ocaml
datatype Enrollment = E string string
```

- Note that we haved tried the NoSQL approach, but this way was inefficient because it messes up with the reasoning for SQL.
```ocaml
datatype Person = P string nat string "person list" "person list"
```

- The objectmodel is displayed as
```ocaml
datatype Objectmodel = OM "Person list" "Enrollment list"
```

### Structure
The "context" has been moved from the theories *MyOCL.thy* and *MySQL.thy to the seperated *ObjectModel.thy*.
In general, the dependency of the theories is as follows:
- ObjectModel.thy: formalization of the object model.
- MySQL.thy <-- ObjectModel.thy
- MyOCL.thy <-- ObjectModel.thy MySQL.thy
- MyMain.thy <-- ObjectModel.thy MySQL.thy MyOCL.thy

### Main idea 
(due to some limitation, the main idea was "refined" into a more archivable one :-))

For all context model O, given an OCL expression exp, the SQL select-statement q is said to be semantacially equivalent
if and only if the execution of q on O is "equal" to the evaluation of exp on O. Formally:
```ocaml
exec(exp,O) == eval(q,O)
```
Specifically:
```ocaml
fun eval :: "OCLexp => Objectmodel => val list"
fun exec :: "SQLstm => Objectmodel => val list"
```

### The proof
So far, under our formulization, we have been able to prove the following properties:
```ocaml
(* self = caller === SELECT self = caller *)
(* self.age = 30 === SELECT age = 30 FROM Person WHERE id = self *)
(* self.lecturers === SELECT lecturers FROM Enrollment WHERE students = self *)
(* self.lecturers->size() === SELECT COUNT *  FROM Enrollment WHERE students = self *)
(* self.lecturers->isEmpty() === SELECT COUNT * = 0 FROM Enrollment WHERE students = self *)
```
The proofs were carried out by Isar.

### There is no free lunch!
Some of the decisions are made during the formalization, for the time being, it is less general than what we expected.
The more we go with the prof, the better we understand and improve them. Notes:
- ObjectModel.thy: datatype Person: PNULL constructor
- ObjectModel.thy: datatype val: VNULL, TPerson, TEnrollment constructors.
- MySQL.thy: datatype col: The need of seperate table columns with association columns (normal columns with reference columns).
- MySQL.thy: fun selectNoCtx.
- MyOCL.thy: better link between fun eval with fun evalWithCtx and fun filterWithBody.

==================
## v1.0, 05th Jul, 2020

This tag is the first version of correctness proof for some specific cases of the mapping. 

In this version, we assume the following scenario:
- The datamodel has 1 table named Person with 3 attributes namely id, age and email of type string, int and string respectively.
- The OCL expression will be evaluated on the same object model as the SQL statement will be executed.

The following files are important:
- MyOCL.thy: formalization of OCL expression.
- MySQL.thy: formalization of SQL statement.
- MyMain.thy: formal proof of the mapping correctness.

In particular, the following lemmas are provided:
- (OCL) ($var1 = $var2)  === (SQL) (SELECT $var1 = $var2), in particular, under our scenario, (self = caller).
- (OCL) ($var1.$att1 = $int) === (SQL) (SELECT $att1 = $int FROM table($att1) WHERE table_id($att1) = $var1), in particular, under our scenario, (self.age = 30).