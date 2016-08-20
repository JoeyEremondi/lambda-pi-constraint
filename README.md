The implementation accompanying the thesis "Improving Error Messages for Dependent Types with Constraint Based Unification", by Joseph Eremondi.

This code is a mismash of three existing projects:

* [LambdaPi](http://www.andres-loeh.de/LambdaPi/), whose files are in the `/src` directory
* [Gundry-McBride Unification](http://adam.gundry.co.uk/pub/pattern-unify/), whose files are in the `/src/PatternUnify` directory
* [Helium](https://hackage.haskell.org/package/Top), whose files are in the `src/Top` directory.

Notable modules include:

* `ConstraintBased`, a type-checking procedure generates constraints to be solved
* `Constraint`, where LambdaPi constraints and values are converted into Gundry-McBride form
* `PatternUnify.Tm`, where we define a value-form Lambda Calculus
* `PatternUnify.Context`, where we define the Gundry-McBride metacontext and operations on it
* `PatternUnify.Unify`, where the actual Gundry-McBride algorithm is implemented
* `Top.Implementation.TypeGraph.Standard`, the main type-graph implementation
* `Top.Implementation.TypeGraph.DefaultHeuristics`, where we implement a few heuristics used in error generation
