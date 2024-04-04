/* Signatures */
abstract sig Person {
	children: set Person,
	siblings: set Person
} 
sig Man, Woman extends Person {}
sig Married in Person {
	spouse: one Married 
}

/* Functions */
fun parents [] : Person -> Person { ~children }

/* Predicates */
pred BloodRelated [p1: Person, p2: Person] { some (p1.*parents & p2.*parents) }

/* Constraints */
fact {
	/* Constraint #1: No person can be their own ancestor */
	/* add your constraint code here */
	fact{
	all p; Person | p !in p.*parents
}
	/* Constraint #2: No person can be their own children */
	/* add your constraint code here */
	all p: Person | p !in p.children

	/* Constraint #3: No person can have more than one father or mother */
	/* add your constraint code here */
	all p : Person | #p.parents = 2

	/* Constraint #4: A person P's siblings are those people with the same parents as P (excluding P) */
	/* add your constraint code here */
	pred siblings [p : Person, s : Person] {
		s.parents = p.parents && p != s
	}
	/* Constraint #5: Each married man (woman) has a wife (husband) */
	/* add your constraint code here */
	all m : Married | m.spouse in Married

	/* Constratins #6: A person cannot be married to a blood relative */
	/* add your constraint code here */
	all m : Married | !BloodRelated[m,m.spouse]

	/* Constraint #7: A spouse cannot be a sibling */
	/* add your constraint code here */
	all m : Married | m.spouse !in m.siblings

	/* Constraint #8: A spouse cannot be their own parents */	
	/* add your constraint code here */
	all m : Married | m.spouse !in m.parents

	/* Constraint #9: A spouse cannot be their own children */	
	/* add your constraint code here */
	all m : Married | m.spouse !in m.children

	/* Constraint #10: Some married Man (Woman) can have no children */
	/* add your constraint code here */
	no m : Man, w : Woman | #m.children + #w.children > 0

}

----------------------------------------

/* Run Command to create an instance */
run {} for 3
