;;;; probability.lisp -- the probability calculus.
;;;;
;;;; Implements the arithmetic-potential valuation algebra (docs/THEORY.md
;;;; section 4.1): valuations are non-negative rational tables ("potentials"),
;;;; combination is pointwise product, marginalization is summing out.
;;;; Normalized distributions are a semantic subclass, NOT an invariant of
;;;; the type: potentials are not closed under normalization-preserving
;;;; combination, so `normalize` is a separate explicit operation
;;;; (docs/THEORY.md section 4.1, NOTES.md "Bend #4").

(defpackage #:parliament/probability
  (:use #:coalton #:coalton-prelude #:parliament/core)
  (:shadowing-import-from #:parliament/core #:lift)
  (:export
   #:Prob
   #:probability
   #:total-mass
   #:normalize
   #:normalized?))

(in-package #:parliament/probability)

(named-readtables:in-readtable coalton:coalton)

(coalton-toplevel
  ;; The phantom tag for the probability calculus. Uninhabited: it exists
  ;; only at the type level.
  (define-type Prob)

  (define-instance (Calculus Prob)
    (define (combine-op _ a b) (* a b))
    (define (marginal-op _ a b) (+ a b))
    (define (marginal-neutral _) 0))

  (declare probability ((List Variable) -> (Config -> Fraction) -> (Valuation Prob)))
  (define (probability vars f)
    "Build a probability potential over VARS from F, rejecting negative
degrees. F receives configurations aligned with the name-sorted form of
VARS."
    (tabulate vars
              (fn (c)
                (let ((x (f c)))
                  (if (< x 0)
                      (error "parliament: probability potentials must be non-negative")
                      x)))))

  (declare total-mass ((Valuation Prob) -> Fraction))
  (define (total-mass v)
    "The sum of all degrees of V: the value of V marginalized to the empty
domain."
    (match (valuation-value (marginalize v Nil) Nil)
      ((Some x) x)
      ((None) (error "parliament: internal error: empty marginal has no value"))))

  (declare normalize ((Valuation Prob) -> (Valuation Prob)))
  (define (normalize v)
    "Scale V so its total mass is 1. Errors on the zero potential, which
normalizes to nothing."
    (let ((z (total-mass v)))
      (if (== z 0)
          (error "parliament: cannot normalize the zero potential")
          (transform-retag (fn (x) (/ x z)) v))))

  (declare normalized? ((Valuation Prob) -> Boolean))
  (define (normalized? v)
    (== (total-mass v) 1)))
