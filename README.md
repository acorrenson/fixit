# fixit

A collection of standard theorems and definitions
about greatest and least fixpoints in the monotone lattice of predicates.
Rocq's native support for induction/coinduction is not used in the development (expect implicitly in the definition of the logical connectives from the standard library).

## Content

+ `./theories/fix1.v`: theorems and definitions for unary predicates
+ `./theories/fix2.v`: theorems and definitions for binary predicates
+ `./theories/fix3.v`: theorems and definitions for ternary predicates


Each `fix[n].v` file provides the following definitions:

+ `union`, `inter`: predicate union/intersection
+ `opp`: predicate negation
+ `le`: predicate ordering
+ `lfp`, `gfp`: least and greatest fixpoints
+ `mono`: definition of monotone predicate transformers

Each `fix[n].v` file provides the following theorems:

+ `lfp_fold`, `lfp_unfold`, `gfp_fold`, `gfp_unfold`: folding and unfolding lemmas for fixpoints
+ `fixpoint_induction`, `fixpoint_coinduction`: Tarski-style induction and coinduction principles
+ `opp_lfp_intro`, `opp_gfp_intro`: exploiting satisfaction of an inductive predicate (resp. coinductive) to disprove satisfaction of a coinductive (resp. inductive) predicate.
+ `opp_lfp_elim`, `opp_gfp_elim`: exploiting violation of an inductive predicate (resp. coinductive) to prove satisfaction of a coinductive (resp. inductive) predicate.