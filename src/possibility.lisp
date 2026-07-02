;;;; possibility.lisp — the possibility (fuzzy-measure) calculus.
;;;;
;;;; Implements min-based possibility theory (docs/THEORY.md §4.2):
;;;; valuations are possibility distributions π : configs → [0,1],
;;;; combination is pointwise minimum (Zadeh's conjunctive combination),
;;;; marginalization is the maximum over eliminated variables. The degree
;;;; set [0,1] with (max, min) is a commutative semiring — in fact a
;;;; distributive lattice — so the blanket instance in core applies.

(defpackage #:parliament/possibility
  (:use #:coalton #:coalton-prelude #:parliament/core)
  (:shadowing-import-from #:parliament/core #:lift)
  (:import-from #:parliament/probability #:Prob)
  (:export
   #:Poss
   #:possibility
   #:possibility-height
   #:poss-normalized?))

(in-package #:parliament/possibility)

(named-readtables:in-readtable coalton:coalton)

(coalton-toplevel
  ;; The phantom tag for the possibility calculus. Uninhabited.
  (define-type Poss)

  ;; Degrees live in [0,1]; combination is min, marginalization is max.
  ;; min and max are associative, commutative, and mutually distributive on
  ;; a totally ordered set; 0 is neutral for max on [0,1]. Unlike
  ;; probability's +, min is idempotent: combining a distribution with
  ;; itself changes nothing (docs/THEORY.md §4.2).
  (define-instance (Calculus Poss)
    (define (combine-op _ a b) (min a b))
    (define (marginal-op _ a b) (max a b))
    (define (marginal-neutral _) 0))

  (declare possibility ((List Variable) -> (Config -> Fraction) -> (Valuation Poss)))
  (define (possibility vars f)
    "Build a possibility distribution over VARS from F, rejecting degrees
outside [0,1]. F receives configurations aligned with the name-sorted form
of VARS."
    (tabulate vars
              (fn (c)
                (let ((x (f c)))
                  (if (or (< x 0) (> x 1))
                      (error "parliament: possibility degrees must lie in [0,1]")
                      x)))))

  (declare possibility-height ((Valuation Poss) -> Fraction))
  (define (possibility-height v)
    "The height of V: its largest degree, i.e. its marginal to the empty
domain."
    (match (valuation-value (marginalize v Nil) Nil)
      ((Some x) x)
      ((None) (error "parliament: internal error: empty marginal has no value"))))

  (declare poss-normalized? ((Valuation Poss) -> Boolean))
  (define (poss-normalized? v)
    "A possibility distribution is normalized when some configuration is
fully possible (height 1)."
    (== (possibility-height v) 1)))

;;; ------------------------------------------------------------------
;;; Lifts INTO possibility.
;;;
;;; Coalton's orphan-instance rule requires a Liftable instance to be
;;; defined in a package that defines one of the types in its head, so
;;; cross-calculus lifts conventionally live with the calculus they lift
;;; into (docs/EXTENSION_PROTOCOL.md §5).
;;; ------------------------------------------------------------------

(coalton-toplevel
  ;; Probability → possibility by the ratio-scale (Dubois–Prade)
  ;; transformation π(c) = p(c) / max p: order-preserving, satisfies
  ;; Zadeh's consistency principle, and always yields a NORMALIZED
  ;; possibility distribution (the modal configuration gets degree 1).
  ;; See docs/THEORY.md §5 for why this direction is canonical, why the
  ;; reverse is not provided, and why no lift can be a full algebra
  ;; homomorphism.
  ;;
  ;; Precondition: V must not be the zero potential — "everything has mass
  ;; zero" has no possibilistic reading (0/0), and this errors on it.
  (define-instance (Liftable (Valuation Prob) (Valuation Poss))
    (define (lift v)
      (let ((m (fold (fn (acc entry) (max acc (snd entry)))
                     0
                     (valuation-entries v))))
        (if (== m 0)
            (error "parliament: cannot lift the zero potential to a possibility distribution")
            (transform-retag (fn (x) (/ x m)) v))))))
