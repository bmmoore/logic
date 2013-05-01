logic
=====

A Haskell library for working with First-Order Logic.

Currently defines an AST, parser, and pretty-printer for formulas,

a few term orders for ground and non-ground terms,

and a clause generation step going through negation normal form,
skolemization, and a "structural transformation" step which
introduces predicates "defining" satisfaction of subformulas
to break up conjunctions that would otherwise make CNF coversion explode

The plan is to add definitions of signatures and theories,
and ordered resolution (with superposition) and inductive theorem provers.

Bibliography:
Yevgeny Kazakov "Framework of Refutational Theorem Proving for Saturation-Based Decision Procedures" Max Plack Institute research report

