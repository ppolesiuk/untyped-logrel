# Untyped Logical Relations at Work

This is the Coq formalization accompanying the "Untyped Logical Relations at
Work: Control Operators, Contextual Equivalence and Full Abstraction" paper. It
is tested under Coq version 8.20.0. It uses two third party libraries:

- IxFree, available at <https://github.com/ppolesiuk/IxFree>, heavily used for
  step indexing. Known to work with version 1.1.
- Binding [1], used for representation of variable binding. For convenience
  we include its source in our development.

## Structure of the Project

Here, we briefly describe how each part of the paper maps to the formalization.

### The calculus with call/cc and abort (beginning of Section 3)

The `callcc/Source` directory contains the definition of the calculus from
Section 3. Modules `Syntax` and `Reduction` contain the syntax and the
semantics, respectively. Some basic properties of the calculus can be found in
the `SyntaxProperties` and `ReductionProperties` modules. Finally, module
`CtxEquiv` contains the definition of contextual equivalence (Section 3.1).

### The logical relation from Section 3 (Section 3.2)

The definition of the logical relation is split into two subdirectories.
The `callcc/LogicalRelation` directory contains the definitions and proofs
that are shared with the logical relation from Section 3.4. In particular
it contains the main definition (module `Core`) without the Obs relation,
some basic properties (module `DefUnroll`) and the Fundamental Property
together with compatibility lemmas (module `Fundamental`).
The Obs relation and proofs of adequacy, soundness, and completeness can be
found in the `EquivLogicalRelation` directory.

### Example equivalences (Section 3.3)

Proofs of example equivalences can be found in the `callcc/Examples` directory.

### Alternative observation relation (Section 3.4)

The alternative Obs relation, together with its properties can be found
in `callcc/ApproxLogicalRelation`. The proof of Example 3.10 can be found
in the `CodeDup` module of the `callcc/Examples` directory.

### Full abstraction (Section 4)

The target language is defined in the `callcc/Target` directory, with its
structure similar to `callcc/Source`. The translation and its properties are
defined in the `callcc/Translation` directory, while the inter-language logical
relation can be found in `callcc/MixedLogicalRelation`. The main theorem is
proven in `FullAbstraction` module in the `callcc/Translation` directory.

## Bibliography

[1] P. Polesiuk and F. Sieczkowski. Functorial Syntax for All. CoqPL 2024.
