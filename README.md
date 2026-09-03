# parliament

An extensible, typed architecture for **valuation algebras** (Kohlas's
information-algebra framework; Shenoy–Shafer valuation-based systems) in
Common Lisp, using [Coalton](https://github.com/coalton-lang/coalton).

A valuation algebra unifies probability, possibility/fuzzy measures,
Dempster–Shafer belief functions, and other uncertainty calculi under two
operations — **combination** (`⊗`) and **marginalization** (`↓`) — over
valuations labeled with the variables they concern. Which calculus a
valuation belongs to is a **phantom type parameter**: combining a
probability potential with a possibility distribution without an explicit,
justified `lift` is a *compile-time type error*.

```lisp
(combine prob-val poss-val)          ; ✗ rejected by the type checker
(combine poss-val (lift prob-val))   ; ✓ explicit ratio-scale lift
```

## Layout

- `src/core.lisp` — variables/domains/configurations; the
  `ValuationAlgebra` and `Liftable` typeclasses; the shared phantom-tagged
  table representation and the `Calculus` (semiring) class with its blanket
  instance.
- `src/probability.lisp` — probability as arithmetic potentials
  `(ℚ≥0, +, ×)`.
- `src/possibility.lisp` — min-based possibility theory
  `([0,1]∩ℚ, max, min)`, and the probability→possibility lift.
- `tests/axioms.lisp` — the generic axiom suite: written once against the
  typeclass interface, instantiated per calculus by supplying a fleet of
  sample valuations. Exact rational arithmetic ⇒ exact-equality checks.
- `docs/THEORY.md` — the precise formalization implemented, per calculus.
- `docs/EXTENSION_PROTOCOL.md` — everything needed to add calculus #3
  without reading `core.lisp`.
- `NOTES.md` — running design notes; where the design bent to fit the
  axioms.

## Running the tests

Requires SBCL and Quicklisp (Coalton is fetched from the Quicklisp dist):

```sh
sbcl --non-interactive \
     --eval '(push #p"/path/to/parliament/" asdf:*central-registry*)' \
     --eval '(ql:quickload :parliament/tests :silent t)' \
     --eval '(parliament/tests:run-tests)'
```

Exits non-zero on any axiom failure.
