# THEORY — the formalization this code implements

This document states, precisely, the mathematical structure `parliament`
implements: the valuation-algebra axioms in the exact form the code and the
test suite use, the semiring construction the two shipped calculi are
instances of, and the theory of the lift between them. Section numbers are
referenced from docstrings in `src/`.

The framework is Kohlas's *information algebras* / labeled valuation
algebras (Kohlas, *Information Algebras: Generic Structures for Inference*,
Springer 2003), which axiomatizes the local-computation structure behind
Shenoy–Shafer valuation-based systems (Shenoy & Shafer, "Axioms for
probability and belief-function propagation", UAI 1990).

## 1. Setting

Fix a finite set of **variables**. Each variable `x` has a finite, non-empty
**frame** `Ω_x` of possible values. A **domain** is a finite set of
variables; for a domain `s`, a **configuration** of `s` is an element of the
product `Ω_s = ∏_{x∈s} Ω_x`. The empty domain has exactly one configuration,
the empty tuple — this is not a degenerate case but load-bearing: valuations
on the empty domain are the scalars of the algebra (§4).

In the code (`src/core.lisp`): a `Variable` is a name plus a frame of string
labels; a domain is a name-sorted, duplicate-free `(List Variable)`; a
`Config` is a list of frame values positionally aligned with its sorted
domain. Two variables with the same name and different frames are two
different variables, and merging domains containing both is a (runtime)
error — one model, one frame per name.

## 2. Labeled valuation algebras

A **valuation** is an atom of information about the values of a specific
domain of variables. A labeled valuation algebra is a set `Φ` of valuations
equipped with three operations

- **labeling** `d : Φ → domains`,
- **combination** `⊗ : Φ × Φ → Φ` (aggregation of information), and
- **marginalization** `↓ : Φ × domains → Φ` (focusing of information),

subject to the following axioms, which are exactly the laws of the
`ValuationAlgebra` typeclass and exactly what `tests/axioms.lisp` checks:

| # | Axiom | Statement |
|---|-------|-----------|
| A1 | Labeling | `d(φ ⊗ ψ) = d(φ) ∪ d(ψ)` |
| A2 | Marginal labeling | `d(φ↓t) = d(φ) ∩ t` |
| A3 | Commutativity | `φ ⊗ ψ = ψ ⊗ φ` |
| A4 | Associativity | `φ ⊗ (ψ ⊗ χ) = (φ ⊗ ψ) ⊗ χ` |
| A5 | Projection | `φ↓d(φ) = φ` |
| A6 | Transitivity | `(φ↓s)↓t = φ↓(s ∩ t)` for **arbitrary** `s`, `t` |
| A7 | Combination | `(φ ⊗ ψ)↓d(φ) = φ ⊗ (ψ↓d(φ))` |

A3+A4 make `(Φ, ⊗)` a commutative semigroup. A7 — the **combination
axiom**, the compatibility law between the two operations — is the entire
point of the structure: it says information about `d(φ)` contained in
`φ ⊗ ψ` can be computed by marginalizing `ψ` *first*, which is what makes
local computation (fusion / junction-tree propagation) sound. It is also the
axiom that actually constrains implementations; A1–A6 are bookkeeping by
comparison.

## 3. Totalized marginalization

Kohlas states marginalization as *partial*: `φ↓t` defined only when
`t ⊆ d(φ)`, with transitivity guarded by `t ⊆ s ⊆ d(φ)` and the combination
axiom's right side reading `ψ↓(d(φ) ∩ d(ψ))`. Partiality is hostile to a
typed interface — encoding `t ⊆ d(φ)` in types needs type-level sets, and
`Optional` results poison every downstream expression.

`parliament` instead makes marginalization **total** by projecting to the
intersection:

```
marginalize φ t   computes   φ↓(d(φ) ∩ t)
```

This is a conservative extension of the textbook operation:

- On the textbook's own turf (`t ⊆ d(φ)`) the two agree, since then
  `d(φ) ∩ t = t`.
- A2 becomes the general statement of marginal labeling.
- A6 in the unconditional form above is *equivalent* to guarded
  transitivity plus the definition: `(φ↓s)↓t = φ↓(d∩s)↓(d∩s∩t) = φ↓(s∩t)`
  by the guarded axiom, and conversely the guarded form is the special case
  `t ⊆ s ⊆ d(φ)`.
- A7 needs no side condition and no explicit intersection on the right:
  `marginalize ψ (d φ)` already means `ψ↓(d(φ) ∩ d(ψ))`.

The test suite tests the *unconditional* A6 over all pairs of fleet domains,
which is strictly more cases than the guarded form permits.

## 4. Semiring-induced valuation algebras

Both shipped calculi are instances of one classical construction (Kohlas
ch. 6; also Aji & McEliece's "generalized distributive law", IEEE Trans. IT
2000). Let `(E, ⊕, ⊙)` be a **commutative semiring**: `⊕` and `⊙`
associative and commutative, `⊕` with neutral element `e`, and `⊙`
distributing over `⊕`. Define valuations with domain `s` as *total tables*
`φ : Ω_s → E`, and:

- **combination**: `(φ ⊗ ψ)(c) = φ(c↓d(φ)) ⊙ ψ(c↓d(ψ))` for each
  configuration `c` of `d(φ) ∪ d(ψ)`, where `c↓s` restricts a configuration
  to the variables of `s`;
- **marginalization**: `(φ↓t)(c) = ⊕ { φ(c') : c' ∈ Ω_{d(φ)},
  c'↓(d(φ)∩t) = c }` — eliminate the variables outside `t` by `⊕`-ing over
  them.

**Theorem.** For any commutative semiring, these tables satisfy A1–A7.
*Proof sketch:* A1, A2, A5 are immediate from the definitions. A3, A4 are
pointwise commutativity/associativity of `⊙`. A6 is
associativity–commutativity of `⊕` (summing out in two stages equals
summing out in one). A7: fix a configuration `c` of `d(φ)`; the left side
is `⊕_{c'} [φ(c) ⊙ ψ(c'')]` over extensions `c'` of `c` to `d(φ) ∪ d(ψ)`,
and distributivity of `⊙` over `⊕` factors `φ(c)` out of the sum, giving
the right side. ∎

Both this construction and the theorem are what `src/core.lisp` encodes:
the `Calculus` typeclass *is* the semiring data (`combine-op` = `⊙`,
`marginal-op` = `⊕`, `marginal-neutral` = `e`) over a phantom calculus tag,
and the single blanket instance
`(Calculus :c) => ValuationAlgebra (Valuation :c)` is the construction. An
instance author's proof obligation is only "my ops form a commutative
semiring on my degree set"; the axiom suite then re-checks A1–A7
concretely.

Degrees are Coalton `Fraction`s — exact rationals — so the axioms hold *on
the nose* and are tested with exact equality, no epsilon. (Floats would
break associativity of `×` and `+`; see NOTES.md.)

Marginalizing to the empty domain yields a one-entry table on the empty
configuration: the "scalar content" of a valuation (total mass for
probability, height for possibility).

### 4.1 Probability

**Formalization:** the algebra of *arithmetic potentials* over the semiring
`(ℚ≥0, +, ×)` with `e = 0` — non-negative rational tables, combination by
pointwise product, marginalization by summing out. This is precisely the
algebra underlying Bayesian-network inference (Lauritzen & Spiegelhalter
1988; Shafer & Shenoy 1990): conditional probability tables are potentials,
`⊗` builds joint distributions, `↓` computes marginals.

`(ℚ≥0, +, ×)` is a commutative semiring (it is the non-negative part of a
semifield), so A1–A7 hold by the theorem.

**Normalization is deliberately not an invariant.** Normalized
distributions are not closed under `⊗` (`p·q` doesn't sum to 1), so a type
of "valuations that sum to 1" cannot support the algebra; and
renormalizing inside `combine` would break A7 itself, because the
normalization constant of `(φ⊗ψ)↓d(φ)` differs from that of
`φ ⊗ (ψ↓d(φ))` computed stepwise — the constants do not commute with
marginalization. So `parliament/probability` exposes potentials, plus
`normalize`, `total-mass`, and `normalized?` as explicit *semantic*
operations outside the algebra. The smart constructor `probability` rejects
negative degrees only. The zero potential (all mass 0) is a legitimate
element (it arises from conditioning on contradictory evidence); it is the
one potential `normalize` and the possibility lift reject.

### 4.2 Possibility / fuzzy measures

**Formalization:** min-based (qualitative) possibility theory on finite
frames (Zadeh, "Fuzzy sets as a basis for a theory of possibility", Fuzzy
Sets and Systems 1978; Dubois & Prade, *Possibility Theory*, Plenum 1988).
A possibility distribution on domain `s` is `π : Ω_s → [0,1]`;
`π(c)` is the degree to which configuration `c` is possible. The associated
fuzzy measure is `Π(A) = max_{c∈A} π(c)`, which is why marginalization is
maximization. The semiring is `([0,1] ∩ ℚ, max, min)` with `e = 0`:

- **combination = pointwise min**: Zadeh's conjunctive combination of
  non-interactive pieces of evidence — a configuration is possible to the
  degree the *most restrictive* source allows.
- **marginalization = max over eliminated variables**: a partial
  configuration is as possible as its best completion.

`([0,1], max, min)` is a bounded distributive lattice, hence a commutative
semiring (min distributes over max on any total order), so A1–A7 hold.
Unlike `+`, both operations are **idempotent**: `φ ⊗ φ = φ`. This is the
formal expression of possibility theory being qualitative — combining a
source with itself adds nothing, so double-counting evidence is harmless
here and harmful in probability. It is also the structural reason the two
calculi cannot be conflated (§5).

The smart constructor `possibility` enforces degrees in `[0,1]`
(min/max-closed, so the invariant survives the algebra, unlike
normalization for probability). A distribution is *normalized* when its
height (max degree) is 1 — `poss-normalized?`.

## 5. Lifts between calculi

### 5.1 Why `Liftable` demands so little

The first-instinct laws for a coercion `L` between calculi —
`L(φ ⊗ ψ) = L(φ) ⊗ L(ψ)` and `L(φ↓t) = L(φ)↓t` — are **unsatisfiable**
for probability → possibility, not merely hard. On single-variable domains
those laws force the degree map `h` to be a semiring morphism
`(ℚ≥0, +, ×) → ([0,1], max, min)` with `h(1) = 1`. Then
`h(n) = h(1+⋯+1) = max(h(1),…,h(1)) = 1` for every positive integer, and
from `1 = h(1) = h(n · 1/n) = min(h(n), h(1/n))` also `h(1/n) = 1`, hence
`h(p/q) = min(h(p), h(1/q)) = 1` for every positive rational: `h` collapses
all positive degrees to 1 and transports no information. The obstruction is
structural — `max` is idempotent and `+` is not.

This is why the framework treats cross-calculus movement as
*transformation*, not homomorphism (Dubois & Prade, "On several
representations of an uncertain body of evidence", 1982; Klir's
uncertainty-invariance program), and why `Liftable`'s laws are:

- **L1, domain preservation:** `d(lift φ) = d(φ)` — checked generically by
  the test suite;
- **L2, pointwise monotonicity:** `φ(c) ≤ φ(c') ⟹ (lift φ)(c) ≤ (lift φ)(c')`
  where degrees are ordered — a lift may forget magnitude but must not
  reorder configurations;
- **L3, normalization preservation:** where both calculi have a
  normalization notion, lifting a normalized valuation yields a normalized
  one.

A `Liftable` instance is a published semantic claim, made per direction
(`Liftable :from :to` implies nothing about `:to :from`), and the absence
of an instance is a feature: it is what makes an unconsidered mixture of
calculi a compile-time error instead of a silent category mistake.

### 5.2 The shipped lift: probability → possibility, ratio scale

`parliament` ships `Liftable (Valuation Prob) (Valuation Poss)` by the
**ratio-scale transformation** (Dubois & Prade 1982):

```
π(c) = p(c) / max_{c'} p(c')
```

Properties (on finite frames, exact under rational arithmetic):

- satisfies L1–L3; the result is always normalized (the modal configuration
  gets degree 1) — both facts are in the test suite;
- fully order-preserving in both directions
  (`p(c) ≤ p(c') ⟺ π(c) ≤ π(c')`);
- satisfies **Zadeh's consistency principle** — the possibility of any
  event bounds its probability from above after normalization of scale:
  what is probable must be possible.

Precondition: the zero potential has no possibilistic image (`0/0`); `lift`
rejects it at runtime. This cannot be excluded by the constructor because
the zero potential is a legitimate *probability* valuation (§4.1).

**Why no possibility → probability instance:** a possibility distribution
is a weaker piece of information than any single probability distribution —
it is equivalent to a *set* of probability measures
(`{P : P(A) ≤ Π(A) for all A}`). Choosing one member (e.g. by the pignistic
/ maximum-entropy transformation) injects information that was not present.
That can be a legitimate modeling decision, but it is not a canonical
coercion, so `parliament` does not publish it; a user who needs it should
define it in their own package (docs/EXTENSION_PROTOCOL.md §5) where the
choice is theirs to justify.

## 6. What the types do and do not enforce

Enforced at compile time:

- **Calculus separation.** `combine`/`marginalize` have types
  `:v → :v → :v` and `:v → domain → :v`; `(Valuation Prob)` and
  `(Valuation Poss)` are distinct types by the phantom tag, so any
  cross-calculus dataflow without an explicit `lift` fails unification.
- **Lift explicitness.** Every cross-calculus *dataflow* must pass through
  an explicit `lift` call resolved by a published `Liftable` instance, and
  Coalton's orphan-instance rule forces that instance to live in a package
  owning one of the endpoint types. (Cross-calculus *construction* — 
  rebuilding a table under a different tag via the phantom-polymorphic
  `tabulate` or `transform-retag` — is not type-preventable; the convention
  that it happens only inside `Liftable` instances is enforced by protocol,
  docs/EXTENSION_PROTOCOL.md §2/§5.)

Deliberately *not* type-enforced, with runtime checks or documented
preconditions instead:

- domain well-formedness across valuations (same variable name, different
  frames) — runtime error at `combine`/domain merge;
- degree-set membership (non-negativity, `[0,1]`) — enforced by smart
  constructors at the boundary, preserved by the ops;
- `t ⊆ d(φ)` for marginalization — dissolved by totalization (§3);
- normalization — a semantic property, explicitly outside the algebra
  (§4.1).

## 7. References

- J. Kohlas, *Information Algebras: Generic Structures for Inference*,
  Springer, 2003.
- P. P. Shenoy, G. Shafer, "Axioms for probability and belief-function
  propagation", *UAI* 4, 1990.
- S. L. Lauritzen, D. J. Spiegelhalter, "Local computations with
  probabilities on graphical structures…", *JRSS B* 50(2), 1988.
- S. M. Aji, R. J. McEliece, "The generalized distributive law", *IEEE
  Trans. Information Theory* 46(2), 2000.
- L. A. Zadeh, "Fuzzy sets as a basis for a theory of possibility", *Fuzzy
  Sets and Systems* 1, 1978.
- D. Dubois, H. Prade, *Possibility Theory: An Approach to Computerized
  Processing of Uncertainty*, Plenum, 1988.
- D. Dubois, H. Prade, "On several representations of an uncertain body of
  evidence", in *Fuzzy Information and Decision Processes*, 1982.
