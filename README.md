logic
=====

A Haskell library for working with First-Order Logic.

Currently defines

an AST, parser, pretty-printer for formulas,

a few term orders for ground and non-ground terms,

unification on terms

clause generation going from arbitrary first order formulas to CNF
by negation normal form, "structural transformation" step which
introduces predicates "defining" satisfaction of subformulas
to break up conjunctions that would otherwise make CNF coversion explode,
and a final Skolemization

Ordered resolution


Further work could add definitions of signatures and theories,
a more efficient term representation than String-labeled trees,
paramodulation/superposition handling of equality, and inductive theorem proving.

Bibliography:
Yevgeny Kazakov "Framework of Refutational Theorem Proving for Saturation-Based Decision Procedures" Max Plack Institute research report
