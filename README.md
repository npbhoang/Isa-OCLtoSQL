# Isabelle OCL2PSQL

The Object Constraint Language (OCL) is a textual, declarative language typically used as part of the UML standard for specifying constraints and queries on models.

The Structure Query Language (SQL) is a special-purpose programming language designed for managing data in relational database management systems. Originally based
upon relational algebra and tuple relational calculus, its scope includes
data insert, query, update and delete, schema creation and modification,
and data access control.

OCL2PSQL represents a mapping from a large set of OCL expression to "pure" SQL select statement.

In this project, we (i) propose a formalization of evaluating an OCL expression, executing an SQL statement and (ii) prove the correctness of our mapping, using an automated proof assistant Isabelle/HOL.

Please note that this is an on-going project.

## v1.0, Jul, 2020

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

