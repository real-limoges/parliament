# Design notes (running log)

Working notes kept while building the valuation-algebra architecture. Entries
are roughly chronological; the interesting ones are where the design had to
bend to fit the algebra's actual axioms.

## Environment

- SBCL 2.2.9 + Quicklisp + Coalton (quicklisp dist `coalton-20260101-git`).
- Repo was effectively empty at start (only `LICENSE` on both branches). The
  task description said `docs/THEORY.md` and `docs/EXTENSION_PROTOCOL.md`
  existed as skeletons — they did not, on any branch. Created from scratch.
- Current Coalton stdlib differs from older docs: the ordered map lives in
  `coalton-library/ordmap` (type `OrdMap`; `insert` upserts), and
  `coalton-library/classes` already exports a `lift` — our `Liftable` method
  shadows that symbol deliberately.

## Decision: degrees are `Fraction`, not floats

Combination for probability is multiplication and marginalization is
summation. Over floats, `(a*b)*c ≠ a*(b*c)` in general, so the associativity
axiom would only hold up to a tolerance, and the test suite would have to be
tolerance-based — which weakens exactly the guarantee the suite exists to
give. Coalton's `Fraction` (exact rational) makes every axiom an *exact*
equality, so the generic test suite can use `==` with no epsilon. The cost is
that calculi needing transcendental operations can't reuse the shared table
representation; that's documented as a limitation in EXTENSION_PROTOCOL.md.

## Decision: phantom tag on a shared table representation, plus an open class

Two layers:

1. `(Valuation :calc)` — one concrete representation (finite discrete
   variables, total table `Config -> Fraction`), where `:calc` is a phantom
   type tag (`Prob`, `Poss`, ...). The `Calculus` class supplies the semiring
   ops for a tag, and a single blanket instance
   `(Calculus :c) => ValuationAlgebra (Valuation :c)` derives the algebra.
   This is the standard "semiring-induced valuation algebra" construction
   (Kohlas ch. 6; see THEORY.md §4), and it means a new pointwise calculus
   is ~10 lines.
2. `ValuationAlgebra` itself is a plain single-parameter class over the
   valuation *type*, not the tag — so a calculus whose valuations are not
   pointwise tables over configurations (Dempster–Shafer mass functions over
   subsets, credal sets) can skip `(Valuation :calc)` entirely and implement
   the class directly on its own type. The axiom suite is written against
   `ValuationAlgebra` + `Eq` only, so it applies to either route.

Phantom safety: `combine :: :v -> :v -> :v` forces both arguments to the same
type, so `(combine prob-thing poss-thing)` is a compile-time unification
failure — no runtime calculus check exists or is needed.

## Bend #1: marginalization had to become "project to the intersection"

Kohlas states marginalization φ↓t as *partial*: defined only for t ⊆ d(φ).
Encoding that partiality in types would need type-level variable sets
(way beyond HM + classes), and returning `Optional` everywhere poisons the
algebra (combine of two Optionals, etc.). Instead `marginalize v t` is total
and projects to `d(v) ∩ t`.

This turned out to be a simplification, not a compromise:

- The **combination axiom** states cleanly with no side condition:
  `(φ ⊗ ψ)↓d(φ) = φ ⊗ (ψ↓d(φ))` — the RHS inner marginal is automatically
  ψ↓(d(φ)∩d(ψ)), which is exactly what the axiom requires.
- The **transitivity axiom** (φ↓s)↓t = φ↓t, normally guarded by t ⊆ s ⊆ d(φ),
  strengthens to the *unconditional* (φ↓s)↓t = φ↓(s∩t) for arbitrary s, t.
  The generic test suite tests this stronger unconditional form over all
  pairs of fleet domains, no subset bookkeeping needed.

## Bend #2: `Calculus` needs a neutral element for the marginal op

Marginalizing folds `marginal-op` over the group of configurations that
project to each target configuration. Groups are never empty (frames are
non-empty), but a fold still wants a seed, and demanding a two-sided neutral
(0 for +/max over [0,1], 1 would be it for a min-marginal) is exactly the
"commutative monoid" half of the semiring the construction requires anyway.
So the class carries `marginal-neutral`, and THEORY.md states the semiring
obligations explicitly rather than hiding them.

## Bend #3: `Liftable` cannot demand a homomorphism — and provably so

First instinct: law-wise, `lift` should commute with `combine` and
`marginalize`. It can't, in general: a probability→possibility map that
turned × into min and + into max would be a semiring homomorphism
(ℚ≥0,+,×) → ([0,1],max,min), and no informative one exists (max is
idempotent, + is not; any such map collapses almost everything — see
THEORY.md §5 for the two-element counterexample). The literature accordingly
treats probability↔possibility as *transformations* subject to consistency
principles, not algebra morphisms.

So `Liftable`'s laws are deliberately weaker (domain preservation,
pointwise monotonicity, normalization preservation), the class is
per-direction (`Liftable :from :to` — no symmetry or transitivity implied),
and the docs say loudly that a lift is an explicit, lossy, semantically
justified coercion — the type error you get without one is the feature.
The implemented instance is the ratio-scale (Dubois–Prade) transformation
π(x) = p(x)/max p, which satisfies Zadeh's consistency principle and is the
canonical choice on finite frames.

`lift (zero potential)` errors: there is no possibility distribution
consistent with "everything is impossible" under ratio scaling (0/0). Smart
constructors can't prevent it because the zero potential is a legitimate
probability *potential* (it arises from conditioning on contradictory
evidence); the precondition is documented on the instance.

## Bend #4: probability instance is over *potentials*, not normalized measures

The probability valuation algebra that actually satisfies the axioms is the
algebra of non-negative tables ("potentials", Lauritzen–Spiegelhalter style),
with combination = pointwise product. Normalized distributions are not closed
under combination (p·q doesn't sum to 1), so making normalization an
invariant of the type would break associativity-of-the-representation, or
force renormalization inside `combine` — which breaks the combination axiom
itself (the normalizing constants don't commute with marginalization).
`normalize` is therefore an explicit, separate operation, and the axiom
fleet deliberately contains unnormalized potentials.

Possibility has no such tension: [0,1] with min/max is closed, so its smart
constructor enforces degrees in [0,1] outright.

## Bend #5: Coalton's orphan-instance rule dictates where lifts live

First cut had a dedicated `src/lifts.lisp` in its own package. Coalton
rejected it: an instance must be defined in a package that defines the
class or one of the types in the instance head. `Liftable (Valuation Prob)
(Valuation Poss)` mentions types from core, probability, and possibility —
so a fourth package can't host it. Rather than fight this, it became the
convention (EXTENSION_PROTOCOL.md §5): a lift lives with the calculus it
lifts into; the Prob→Poss instance sits in `parliament/possibility`. Side
effect worth knowing: a third party cannot add a lift between two calculi
they don't own without editing one of the owning packages — an acceptable
(arguably healthy) restriction, since a lift is a semantic claim about
those calculi.

## Testing approach

- `tests/axioms.lisp` has a generic core: every check is a Coalton function
  constrained only by `(ValuationAlgebra :v) (Eq :v)` (lift checks add
  `Liftable`). A per-calculus driver is one call:
  `(axiom-report "name" fleet)` where `fleet :: List :v` is a list of sample
  valuations on overlapping domains.
- Fleets are generated deterministically (LCG over integers → fractions in
  (0,1]) so failures reproduce; exact arithmetic means zero flakiness.
- The suite iterates all pairs/triples from the fleet: commutativity,
  associativity, labeling (d(φ⊗ψ) = d(φ)∪d(ψ)), projection identity
  (φ↓d(φ) = φ), unconditional transitivity, combination axiom, plus scalar
  marginalization to the empty domain.

## Verification status

(Updated after each actual run — no claim here precedes a real run.)

- 2026-07-02, this session, `sbcl --non-interactive` loading
  `parliament/tests` and calling `run-tests`:
  `parliament axiom suite: 1176 checks, all passed.` (exit 0). Breakdown:
  per calculus 6 unary (projection identity) + 4·6² binary (commutativity,
  labeling, marginal labeling, combination axiom) + 2·6³ ternary
  (associativity, unconditional transitivity) = 582; ×2 calculi = 1164;
  plus 12 lift-law checks (domain preservation + normalized result over the
  6-element probability fleet).
- Suite *sensitivity* verified the same day: a deliberately lawless
  calculus (combine-op = subtraction) registered against the same generic
  suite produced **265 failures** — the suite can actually fail.
- Phantom-type enforcement verified: compiling `(combine p q)` with
  `p : Valuation Prob`, `q : Valuation Poss` fails with
  `Expected type '(VALUATION PROB)' but got '(VALUATION POSS)'`; the same
  composition through the explicit lift, `(combine q (lift p))`, compiles
  and evaluates correctly (checked by hand: p = (1/4, 3/4) lifts to
  (1/3, 1), min-combined with (1/2, 1/2) gives (1/3, 1/2)).
