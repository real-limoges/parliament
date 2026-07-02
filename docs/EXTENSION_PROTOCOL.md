# EXTENSION PROTOCOL — adding calculus #3

This document is the complete contract for adding a new uncertainty
calculus to `parliament`. It is written so that you never need to read
`src/core.lisp`: every exported name you may use is specified here, with
its full type and semantics. If you find yourself needing something not
listed, that is a gap in this document — file it as such rather than
reaching into internals.

There are two routes:

- **Route A** (§3): your calculus is *pointwise* — a valuation is a table
  assigning a rational degree to each configuration, combination acts
  pointwise, and marginalization eliminates variables by folding a binary
  operation. Probability and possibility are both Route A. Cost: ~10 lines
  plus a smart constructor.
- **Route B** (§4): your valuations are not tables over configurations
  (Dempster–Shafer mass functions live on *subsets* of the frame; credal
  sets are sets of measures). You implement the `ValuationAlgebra` class
  directly on your own representation.

Either way, §6 (registering with the axiom suite) is mandatory: an
instance is not done until the generic suite passes on it unmodified.

## 1. The laws you are promising

Whatever the route, your instance must satisfy, with `d` = `domain`,
`⊗` = `combine`, `↓` = `marginalize` (statements and rationale in
docs/THEORY.md §2–3):

| # | Law |
|---|-----|
| A1 | `d(φ ⊗ ψ) = d(φ) ∪ d(ψ)` |
| A2 | `d(φ↓t) = d(φ) ∩ t` |
| A3 | `φ ⊗ ψ = ψ ⊗ φ` |
| A4 | `φ ⊗ (ψ ⊗ χ) = (φ ⊗ ψ) ⊗ χ` |
| A5 | `φ↓d(φ) = φ` |
| A6 | `(φ↓s)↓t = φ↓(s ∩ t)` for arbitrary `s`, `t` |
| A7 | `(φ ⊗ ψ)↓d(φ) = φ ⊗ (ψ↓d(φ))` |

Note A2 and A6: marginalization in `parliament` is **total** and projects
to the intersection `d(φ) ∩ t`. If your mental model of the operation is
the textbook partial one ("only defined for `t ⊆ d(φ)`"), implement the
intersection semantics — the suite tests the unconditional forms.

The suite compares valuations with `==`, so your valuation type needs an
`Eq` instance in which equal information is equal — for Route B, make sure
`Eq` is equality of the *represented* valuation (e.g. compare canonical
forms), not incidental structure.

## 2. The exported interface (`parliament/core`)

Package to `:use`: `#:parliament/core` (alongside `#:coalton`
`#:coalton-prelude`). Add
`(:shadowing-import-from #:parliament/core #:lift)` — the prelude also
exports a `lift`, and you want this one.

### Variables, domains, configurations

Domains are represented as `(List Variable)`, always kept **sorted by
variable name and duplicate-free**; every function below that returns a
domain returns it in that canonical form, and every function that takes one
accepts any order (it normalizes). A `Config` is `(List String)`:
frame values positionally aligned with the *canonical* (sorted) form of its
domain. The empty domain has exactly one configuration, `Nil`.

| Name | Type | Semantics |
|------|------|-----------|
| `Variable` | opaque type | A named variable with a finite frame. `Eq`/`Ord` by name-then-frame; two same-named variables with different frames are *different variables*, and merging domains containing both is a runtime error. |
| `make-variable` | `String → (List String) → Variable` | Smart constructor. Errors on an empty or duplicate-containing frame. |
| `variable-name` | `Variable → String` | |
| `variable-frame` | `Variable → (List String)` | Never empty. |
| `Config` | alias for `(List String)` | See above. |
| `domain-union` | `(List Variable) → (List Variable) → (List Variable)` | Sorted, deduplicated union. Errors on a frame conflict. |
| `domain-intersection` | `(List Variable) → (List Variable) → (List Variable)` | Sorted intersection. |
| `subdomain?` | `(List Variable) → (List Variable) → Boolean` | Is every variable of the first also in the second? |
| `enumerate-configs` | `(List Variable) → (List Config)` | All configurations of a (canonical-form) domain, lexicographic in frame order. For `Nil` it is `(Nil)` — one empty config. |
| `restrict-config` | `(List Variable) → Config → (List Variable) → Config` | `(restrict-config dom c target)`: the sub-configuration of `c` (a config of canonical `dom`) on the variables of `target`; `target` must be ⊆ `dom`. |

### The algebra classes

```
(define-class (ValuationAlgebra :v)
  (domain      (:v → (List Variable)))
  (combine     (:v → :v → :v))
  (marginalize (:v → (List Variable) → :v)))

(define-class (Liftable :from :to)
  (lift (:from → :to)))
```

`ValuationAlgebra` instances promise A1–A7. `Liftable` instances promise
the lift laws (§5). `marginalize` must implement intersection semantics
(§1). There is no method for "the domain argument in canonical form" —
`marginalize` must accept any order.

### The shared table representation (Route A machinery)

| Name | Type | Semantics |
|------|------|-----------|
| `Valuation` | `(Valuation :calc)`, opaque | A canonical domain plus a **total** table `Config → Fraction`. `:calc` is a phantom tag with no runtime content. Has `Eq` (domain and table equality). |
| `Calculus` | class over the tag, below | The semiring data of a pointwise calculus. |
| `tabulate` | `(List Variable) → (Config → Fraction) → (Valuation :calc)` | Build a valuation: your function is called once per configuration of the canonical form of the domain, values positionally aligned to it. |
| `valuation-entries` | `(Valuation :calc) → (List (Tuple Config Fraction))` | All (config, degree) pairs, canonical order. |
| `valuation-value` | `(Valuation :calc) → Config → (Optional Fraction)` | Degree at one configuration; `None` if the config isn't one of the domain's. |
| `transform-retag` | `(Fraction → Fraction) → (Valuation :a) → (Valuation :b)` | Map every degree AND reinterpret under a new tag. **The only exported door between tags.** Use it only inside a `Liftable` instance (or a same-tag transformation like `normalize`, where `:a = :b` by annotation). |

```
(define-class (Calculus :calc)
  (combine-op       ((Proxy :calc) → Fraction → Fraction → Fraction))
  (marginal-op      ((Proxy :calc) → Fraction → Fraction → Fraction))
  (marginal-neutral ((Proxy :calc) → Fraction)))
```

`Proxy` is `coalton-library/types:Proxy`; each method ignores its value and
dispatches on the tag. Given a `Calculus` instance, core's blanket instance
`(Calculus :c) => ValuationAlgebra (Valuation :c)` supplies `domain`,
`combine` (pointwise `combine-op` over the union domain) and `marginalize`
(fold of `marginal-op`, seeded with `marginal-neutral`, over eliminated
variables). You never implement those three yourself on `(Valuation :c)`.

## 3. Route A: a pointwise (semiring) calculus

**Obligation:** your degree set `E ⊆ ℚ` (as `Fraction`s) with
`(E, marginal-op, combine-op)` must be a **commutative semiring**:

1. `combine-op` associative and commutative on `E`; closed on `E`;
2. `marginal-op` associative and commutative on `E`; closed on `E`;
   `marginal-neutral` is its neutral element and belongs to your degree
   set's closure;
3. `combine-op` distributes over `marginal-op`:
   `a ⊙ (b ⊕ c) = (a ⊙ b) ⊕ (a ⊙ c)`.

That these three imply A1–A7 is a theorem (docs/THEORY.md §4) — but you
still run the suite (§6).

**Limitation to check first:** the neutral element must be an actual
`Fraction`. A calculus whose natural marginal operation is `min` over an
*unbounded* degree set (e.g. Spohn's kappa calculus, `(ℕ∪{∞}, min, +)`)
has neutral `+∞`, which `Fraction` cannot represent — such a calculus is
Route B (with its own degree type) or needs a documented finite cap. The
same applies if your calculus needs irrational degrees (e.g. entropies):
the shared table is exact-rational only.

**Worked example** — the max-product ("most probable explanation")
calculus, degrees in `[0,1] ∩ ℚ`, combination `×`, marginalization `max`
(a valid semiring: `×` distributes over `max` on non-negatives):

```lisp
(defpackage #:my/mpe
  (:use #:coalton #:coalton-prelude #:parliament/core)
  (:shadowing-import-from #:parliament/core #:lift)
  (:export #:Mpe #:mpe))
(in-package #:my/mpe)
(named-readtables:in-readtable coalton:coalton)

(coalton-toplevel
  ;; 1. The phantom tag. Uninhabited on purpose: it exists only to make
  ;;    (Valuation Mpe) a distinct type.
  (define-type Mpe)

  ;; 2. The semiring.
  (define-instance (Calculus Mpe)
    (define (combine-op _ a b) (* a b))
    (define (marginal-op _ a b) (max a b))
    (define (marginal-neutral _) 0))

  ;; 3. A smart constructor enforcing your degree set at the boundary.
  ;;    (The algebra preserves it: [0,1] is closed under × and max.)
  (declare mpe ((List Variable) -> (Config -> Fraction) -> (Valuation Mpe)))
  (define (mpe vars f)
    (tabulate vars
              (fn (c)
                (let ((x (f c)))
                  (if (or (< x 0) (> x 1))
                      (error "mpe: degrees must lie in [0,1]")
                      x))))))
```

That is the whole calculus. Do **not**:

- export `tabulate`-based constructors that bypass your degree-set check
  (export only the smart constructor and let `tabulate` stay a
  parliament/core import);
- renormalize (or otherwise post-process) inside anything that will be
  called per-`combine` — normalization does not commute with
  marginalization and will break A7 (see probability's treatment,
  docs/THEORY.md §4.1: normalization is a separate exported operation);
- reuse another calculus's tag "because the ops are the same shape" — the
  tag is the semantic identity of your calculus.

## 4. Route B: a direct `ValuationAlgebra` instance

Define your own representation and instantiate the class directly:

```lisp
(coalton-toplevel
  (define-type BeliefFn ...)          ; your representation

  (define-instance (Eq BeliefFn) ...) ; equality of represented information!

  (define-instance (ValuationAlgebra BeliefFn)
    (define (domain v) ...)           ; canonical (sorted, dedup) form
    (define (combine a b) ...)        ; A1, A3, A4, A7
    (define (marginalize v t) ...)))  ; A2, A5, A6 — INTERSECTION semantics
```

Requirements beyond the laws themselves:

- `domain` must return the canonical sorted/deduplicated form, built with
  `domain-union` / `domain-intersection` or sorted the same way (`Ord` on
  `Variable` is name-then-frame).
- `marginalize` must accept a target in any order and any relation to
  `d(φ)` (superset, overlap, disjoint — projecting to the intersection;
  disjoint target ⇒ result on the empty domain).
- `Eq` must be semantic: if your representation is non-canonical (e.g.
  unsorted focal sets), canonicalize before comparing, or the suite will
  report false failures of A3/A4 that are really representation noise.
- Coalton's **orphan-instance rule**: the instance must live in a package
  that defines a type mentioned in the instance head — in practice, define
  it in the same package as your representation type and this is
  automatic.

Route B valuations get no phantom-tag machinery and need none: the
representation type itself is the compile-time separation.

## 5. Lifts

Publish a `Liftable :from :to` instance **only** when there is a
literature-grade transformation whose information loss/injection you can
state. The laws (rationale and the impossibility of stronger ones:
docs/THEORY.md §5):

- **L1**: `d(lift φ) = d(φ)` — tested generically;
- **L2**: pointwise monotone — lifting never reorders configurations;
- **L3**: normalized in, normalized out (where both sides have a
  normalization notion).

Mechanics:

- Coalton's orphan rule again: the instance must be defined in a package
  owning one of the head types. Convention in this codebase: **a lift
  lives with the calculus it lifts into** (the Prob→Poss instance sits in
  `parliament/possibility`). For your calculus #3, both directions
  involving it belong in your package.
- For Route A calculi, build the lift from `valuation-entries` (to inspect
  the whole table, e.g. to find a normalization constant) plus
  `transform-retag` (to map degrees and change the tag). Degenerate inputs
  with no image in the target calculus (cf. the zero potential for
  Prob→Poss) should `error` with a message naming the precondition.
- Lifts are directional. Do not add the reverse direction for symmetry's
  sake; add it only if it is independently justified (the reverse of a
  lossy lift generally requires *choosing* information — say which choice
  and why, in your docstring).

## 6. Registering with the axiom suite (mandatory)

The suite (`tests/axioms.lisp`) is generic: every check is written against
`ValuationAlgebra` + `Eq` only. You bring a **fleet** — a `(List :v)` of
sample valuations — and one registration line.

1. **Build a fleet.** Aim at the axioms' weak spots:
   - at least two domains that *overlap without containment* (A7 is
     trivialized by nested or disjoint domains);
   - a three-way overlap for A4/A6 (e.g. `{a,b}`, `{b,c}`, `{a,c}`,
     `{a,b,c}`);
   - a single-variable and an **empty-domain** valuation (scalars exercise
     the unit-like edge cases);
   - degrees that are *not* normalized and not symmetric (symmetric tables
     can hide commutativity bugs);
   - only degrees in your calculus's degree set (the fleet must be built
     with your smart constructor, so the suite also witnesses that your
     constructor accepts sensible input).

   For Route A calculi with degrees in `(0,1]`, reuse the existing helper:
   `(tests::build-fleet my-constructor)` gives the standard 6-valuation
   fleet over `{a,b}`, `{b,c}`, `{a,c}`, `{a,b,c}`, `{b}`, `{}` with
   deterministic pseudo-random degrees `k/16 ∈ (0,1]`. If your degree set
   differs, write your own fleet in the same shape.

2. **Register it** in `all-results` in `tests/axioms.lisp`:

   ```lisp
   (append (run-axiom-suite "mpe" mpe-fleet) ...)
   ```

   and, if you published lifts, add lift-law checks next to
   `prob->poss-checks` (domain preservation via `lift-preserves-domain`,
   plus your L3 check).

3. **Run it**: `(asdf:test-system :parliament/tests)` or

   ```sh
   sbcl --non-interactive \
        --eval '(push #p"/path/to/parliament/" asdf:*central-registry*)' \
        --eval '(ql:quickload :parliament/tests)' \
        --eval '(parliament/tests:run-tests)'
   ```

   Exit status is non-zero on any failure; failures are printed as
   `calculus: axiom-name fleet-indices`, so `mpe: combination-axiom 0 3`
   means A7 failed for fleet elements 0 and 3 — a minimal reproduction is
   `(combination-axiom (index 0 fleet) (index 3 fleet))`.

If the suite fails, the fault is in the instance, not the suite: the
checks are direct transcriptions of A1–A7. The historically likely
culprits: a `combine-op`/`marginal-op` pair that doesn't distribute (A7), a
wrong `marginal-neutral` (A5/A6 on scalar cases), non-semantic `Eq`
(spurious A3/A4 failures), or normalization smuggled into `combine` (A7).
Weakening the test to pass is never the fix.

## 7. Checklist

- [ ] Tag type (Route A) or representation type + `Eq` (Route B) in your
      own package
- [ ] `Calculus` instance whose ops form a commutative semiring on your
      degree set (Route A) / `ValuationAlgebra` instance satisfying A1–A7
      with intersection-semantics marginalization (Route B)
- [ ] Smart constructor enforcing your degree set / representation
      invariants at the boundary; no law-relevant processing hidden in ops
- [ ] Optional `Liftable` instances, in your package, each with a stated
      justification and L1–L3
- [ ] Fleet + registration line in `tests/axioms.lisp`; suite passes with
      zero failures
- [ ] A short section in docs/THEORY.md naming your formalization and its
      semiring (or, for Route B, proving/citing A1–A7 for your ops)
