# SymbolicEquivalence

This repo describes a generic, verified bisimulation-based equivalence algorithm over any symbolic alphabet.
By symbolic we mean that an alphabet is modelled by an effective Boolean algebra (EBA).

## Overview

* `EffectiveBooleanAlgebra` describes EBAs which model the underlying alphabet
* `TransitionTerm` describes transition terms, which are a symbolic representation of the transition function
* `SymbolicDerivativeSystem` is the interface that an instance provides (includes states, nullability and derivatives)
* `Checker` is the generic equivalence algorithm and its correctness proof
* `UnionFind` is the union-find structure that the checker uses to track equivalent states
* `UnionFold` folds a list into a union and shows that removing duplicates does not change it
* `SmartDedup`, `NeSubsets`, `UpTo` are list helpers used in the finiteness proofs
* `Ere` is an instance for Extended Regular Expressions
* `Ereq` is an instance for Extended Regular Expressions with Quantifiers and wMSO formulas (through a translation)
