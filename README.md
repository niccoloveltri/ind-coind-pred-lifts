# Inductive and coinductive predicate liftings for effectful programs
## Niccolò Veltri and Niels Voorneveld

This is the Agda formalization for the paper submitted to FSCD 2021, with the same name.

We formulate a framework for describing behaviour of effectful higher-order recursive programs. Examples of effects we consider include: execution cost, nondeterminism, and interaction with a user, and are implemented using effect operations. The denotational semantics of a program is given by a coinductive tree in a cofree monad, which combines potential return values of the program in terms of effect operations. 
	
Using a simple test logic, we construct two sorts of predicate liftings, which lift predicates on a result type to predicates on computations that produce results of that type, capturing a facet of program behaviour. Firstly, we study inductive predicate liftings which can be used to describe effectful notions of total correctness. Secondly, we study coinductive predicate liftings, which describe effectful notions of partial correctness. The two constructions are dual in the sense that one can be used to disprove the other. 
	
The predicate liftings are used as a basis for an endogenous logic of behavioural properties for higher-order programs. The program logic has a derivable notion of negation, arising from the duality of the two sorts of predicate liftings, and it generates a program equivalence which subsumes a notion of bisimilarity. Appropriate definitions of inductive and coinductive predicate liftings are given for a multitude of effect examples.

The file [Everything.agda](https://github.com/niccoloveltri/ind-coind-pred-lifts/blob/main/Everything.agda) contains the whole Agda development.
The development uses Agda 2.6.1 with standard library 1.6-dev.
