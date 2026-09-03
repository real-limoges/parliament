# Design notes (running log)

Working notes I kept while building the valuation-algebra architecture.
Entries are roughly chronological.
The interesting ones are all in the same place: where the design had to bend to fit the algebra's actual axioms, not the ones I assumed it had.

## Environment

- SBCL 2.2.9 + Quicklisp + Coalton (quicklisp dist `coalton-20260101-git`).
- Repo was effectively empty at start (only `LICENSE` on both branches). The task description claimed `docs/THEORY.md` and `docs/EXTENSION_PROTOCOL.md` existed as skeletons. They did not, on any branch. Created both from scratch.
- Current Coalton stdlib differs from the older docs: the ordered map lives in `coalton-library/ordmap` (type `OrdMap`, where `insert` upserts), and `coalton-library/classes` already exports a `lift`, so our `Liftable` method shadows that symbol on purpose.

## Decision: degrees are `Fraction`, not floats

Combination for probability is multiplication, marginalization is summation.
Over floats `(a*b)*c ≠ a*(b*c)` in general.
So the associativity axiom would only hold up to a tolerance, and then the whole test suite has to be tolerance-based, which quietly weakens the exact guarantee the suite exists to give in the first place.
No thanks.
Coalton's `Fraction` (exact rational) makes every axiom an *exact* equality, so the generic suite gets to use `==` with no epsilon anywhere.
The cost: a calculus that needs transcendental ops can't reuse the shared table representation. That one is written up as a limitation in EXTENSION_PROTOCOL.md.

## Decision: phantom tag on a shared table representation, plus an open class

Two layers, and the split matters.

1. `(Valuation :calc)` is one concrete representation (finite discrete variables, a total table `Config -> Fraction`), where `:calc` is a phantom type tag (`Prob`, `Poss`, ...). The `Calculus` class supplies the semiring ops for a tag, and a single blanket instance `(Calculus :c) => ValuationAlgebra (Valuation :c)` derives the algebra. This is the standard "semiring-induced valuation algebra" construction (Kohlas ch. 6; see THEORY.md section 4), and it buys me a new pointwise calculus in about 10 lines.
2. `ValuationAlgebra` itself is a plain single-parameter class over the valuation *type*, not the tag. So a calculus whose valuations aren't pointwise tables over configurations (Dempster–Shafer mass functions over subsets, credal sets) can skip `(Valuation :calc)` entirely and implement the class straight on its own type. The suite is written against `ValuationAlgebra` + `Eq` only, so it doesn't care which route you took.

Phantom safety is the nice part.
`combine :: :v -> :v -> :v` forces both arguments to the same type, so `(combine prob-thing poss-thing)` is a compile-time unification failure.
No runtime calculus check exists, and none is needed.

## Bend #1: marginalization had to become "project to the intersection"

Kohlas states marginalization φ↓t as *partial*: defined only for t ⊆ d(φ).
Encoding that partiality in the types would need type-level variable sets, which is way beyond HM + classes, and returning `Optional` everywhere poisons the whole algebra (now combine takes two Optionals, and so on down the line).
So `marginalize v t` is total instead, and just projects to `d(v) ∩ t`.

I expected this to be a compromise. It turned out to be a straight simplification:

- The **combination axiom** states cleanly, no side condition: `(φ ⊗ ψ)↓d(φ) = φ ⊗ (ψ↓d(φ))`. The inner marginal on the right is automatically ψ↓(d(φ)∩d(ψ)), which is exactly what the axiom wanted anyway.
- The **transitivity axiom** (φ↓s)↓t = φ↓t, normally guarded by t ⊆ s ⊆ d(φ), strengthens to the *unconditional* (φ↓s)↓t = φ↓(s∩t) for arbitrary s, t. The suite tests that stronger unconditional form over all pairs of fleet domains, and there's no subset bookkeeping left to get wrong.

## Bend #2: `Calculus` needs a neutral element for the marginal op

Marginalizing folds `marginal-op` over the group of configurations that project to each target configuration.
The groups are never empty (frames are non-empty), but a fold still wants a seed.
And demanding a two-sided neutral (0 for +/max over [0,1]; 1 would be it for a min-marginal) is just the "commutative monoid" half of the semiring the construction already requires.
So the class carries `marginal-neutral`, and THEORY.md states the semiring obligations out loud instead of hiding them inside the fold.

## Bend #3: `Liftable` cannot demand a homomorphism, and provably so

First instinct: law-wise, `lift` should commute with `combine` and `marginalize`.
It can't. Not in general, and not for lack of trying.
A probability→possibility map that turned × into min and + into max would be a semiring homomorphism (ℚ≥0,+,×) → ([0,1],max,min), and no informative one exists.
max is idempotent, + is not, and any such map ends up collapsing almost everything (THEORY.md section 5 has the two-element counterexample).
So the literature treats probability↔possibility as *transformations* subject to consistency principles, not as algebra morphisms, and that is the right call.

So `Liftable`'s laws are deliberately weak (domain preservation, pointwise monotonicity, normalization preservation).
The class is per-direction: `Liftable :from :to` implies nothing about the other way, no symmetry, no transitivity.
And the docs say it loudly: a lift is an explicit, lossy, semantically justified coercion.
The type error you get when you *don't* have one is the whole feature, not an inconvenience.
The instance I actually ship is the ratio-scale (Dubois–Prade) transformation π(x) = p(x)/max p, which satisfies Zadeh's consistency principle and is the canonical choice on finite frames.

`lift (zero potential)` errors out: there's no possibility distribution consistent with "everything is impossible" under ratio scaling, it's literally 0/0.
Smart constructors can't head this off, because the zero potential is a legitimate probability *potential* (it comes from conditioning on contradictory evidence).
So the precondition lives on the instance instead.

## Bend #4: the probability instance is over *potentials*, not normalized measures

The probability valuation algebra that actually satisfies the axioms is the algebra of non-negative tables ("potentials", Lauritzen–Spiegelhalter style), with combination = pointwise product.
Normalized distributions are not closed under combination (p·q doesn't sum to 1).
So making normalization an invariant of the type would either break associativity of the representation, or force a renormalization inside `combine`, which breaks the combination axiom itself (the normalizing constants don't commute with marginalization).
Either way you lose. So `normalize` is an explicit, separate operation, and the axiom fleet deliberately carries unnormalized potentials so the tests can't quietly lean on normalization.

Possibility has none of this tension: [0,1] with min/max is closed, so its smart constructor just enforces degrees in [0,1] outright and moves on.

## Bend #5: Coalton's orphan-instance rule dictates where lifts live

First cut had a dedicated `src/lifts.lisp` in its own package.
Coalton rejected it flat out: an instance has to be defined in a package that defines the class or one of the types in the instance head.
`Liftable (Valuation Prob) (Valuation Poss)` mentions types from core, probability, and possibility, so a fourth package can't host it, full stop.
Rather than fight the compiler I turned it into the convention (EXTENSION_PROTOCOL.md section 5): a lift lives with the calculus it lifts *into*, so the Prob→Poss instance sits in `parliament/possibility`.
One side effect worth knowing: a third party can't add a lift between two calculi they don't own without editing one of the owning packages.
I think that is healthy, not a limitation. A lift is a semantic claim about those two calculi, so owning one of them is a fair price of admission.

## Testing approach

- `tests/axioms.lisp` has a generic core: every check is a Coalton function constrained only by `(ValuationAlgebra :v) (Eq :v)` (the lift checks add `Liftable`). A per-calculus driver is one call: `(run-axiom-suite "name" fleet)`, where `fleet :: List :v` is a list of sample valuations on overlapping domains.
- Fleets are generated deterministically (an LCG over integers → fractions in (0,1]) so failures reproduce, and exact arithmetic means zero flakiness. That combination is the point: a failing check is always a real failure, never a rounding ghost.
- The suite grinds through all pairs/triples from the fleet: commutativity, associativity, labeling (d(φ⊗ψ) = d(φ)∪d(ψ)), projection identity (φ↓d(φ) = φ), unconditional transitivity, the combination axiom, plus scalar marginalization to the empty domain.

## Verification status

(Updated after each actual run; no claim here precedes a real run.)

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
  suite produced **265 failures**, so the suite can actually fail.
- 2026-07-02, independent re-verification by a fresh-context subagent
  against the committed state (bcc0718): clean-image build + suite run
  reproduced `1176 checks, all passed` with exit 0; two injected mutants
  (non-commutative combine-op; wrong marginal-neutral with correct ops)
  produced 265 and 258 failures respectively; probability and possibility
  arithmetic matched its independent hand calculations exactly; the
  EXTENSION_PROTOCOL Route A example compiled verbatim from the doc and
  passed 582/582 through the generic suite. Two doc nits it found (a
  package-qualification typo in EXTENSION_PROTOCOL section 6, and an
  overstatement of `transform-retag` being the "only" retagging door,
  given `tabulate` is phantom-polymorphic) are fixed in the follow-up
  commit; wording now says the Liftable confinement is protocol, not
  typing.
- Phantom-type enforcement verified: compiling `(combine p q)` with
  `p : Valuation Prob`, `q : Valuation Poss` fails with
  `Expected type '(VALUATION PROB)' but got '(VALUATION POSS)'`; the same
  composition through the explicit lift, `(combine q (lift p))`, compiles
  and evaluates correctly (checked by hand: p = (1/4, 3/4) lifts to
  (1/3, 1), min-combined with (1/2, 1/2) gives (1/3, 1/2)).
