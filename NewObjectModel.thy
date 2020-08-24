theory NewObjectModel
imports Main
begin

type_synonym id = string
type_synonym age = nat
type_synonym email = string

datatype Person = PERSON id age email

fun getIdPerson :: "Person \<Rightarrow> id" where
"getIdPerson (PERSON pid age email) = pid"

fun getAgePerson :: "Person \<Rightarrow> age" where
"getAgePerson (PERSON pid age email) = age"

fun getEmailPerson :: "Person \<Rightarrow> email" where
"getEmailPerson (PERSON pid age email) = email"

type_synonym students = Person
type_synonym lecturers = Person

datatype Enrollment = ENROLLMENT students lecturers

type_synonym Persons = "Person list"
type_synonym Enrollments = "Enrollment list"

datatype ObjectModel = OBJECTMODEL Persons Enrollments

fun getPersonList :: "ObjectModel \<Rightarrow> Persons" where
"getPersonList (OBJECTMODEL ps es) = ps"

end