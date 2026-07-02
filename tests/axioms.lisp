;;;; axioms.lisp — the generic valuation-algebra axiom suite.
;;;;
;;;; Every check in §1 is written once, against the ValuationAlgebra (and,
;;;; for lifts, Liftable) typeclass interface only — constrained by
;;;; (ValuationAlgebra :v) (Eq :v) and nothing else. Because degrees are
;;;; exact rationals, every axiom is checked with exact equality: there is
;;;; no tolerance anywhere in this file.
;;;;
;;;; A calculus is hooked in by building a "fleet" — a list of sample
;;;; valuations on overlapping domains — and calling (run-axiom-suite name
;;;; fleet). The suite exercises every axiom over all pairs/triples drawn
;;;; from the fleet. To register a new calculus, see
;;;; docs/EXTENSION_PROTOCOL.md §6; it is one fleet definition and one line
;;;; in `all-results` below.

(defpackage #:parliament/tests
  (:use #:coalton #:coalton-prelude #:parliament/core)
  (:shadowing-import-from #:parliament/core #:lift)
  (:use #:parliament/probability #:parliament/possibility)
  (:local-nicknames (#:list #:coalton-library/list)
                    (#:math #:coalton-library/math)
                    (#:types #:coalton-library/types))
  (:export #:run-tests))

(in-package #:parliament/tests)

(named-readtables:in-readtable coalton:coalton)

;;; ------------------------------------------------------------------
;;; §1. Generic axiom checks — the only interface used is the typeclass.
;;; ------------------------------------------------------------------

(coalton-toplevel
  ;; One executed check: a description and whether it held.
  (define-type-alias CheckResult (Tuple String Boolean))

  (declare check (String -> Boolean -> CheckResult))
  (define (check description ok)
    (Tuple description ok))

  ;; Commutativity of combination: φ ⊗ ψ = ψ ⊗ φ.
  (declare commutativity ((ValuationAlgebra :v) (Eq :v) => :v -> :v -> Boolean))
  (define (commutativity a b)
    (== (combine a b) (combine b a)))

  ;; Associativity of combination: φ ⊗ (ψ ⊗ χ) = (φ ⊗ ψ) ⊗ χ.
  (declare associativity ((ValuationAlgebra :v) (Eq :v) => :v -> :v -> :v -> Boolean))
  (define (associativity a b c)
    (== (combine a (combine b c)) (combine (combine a b) c)))

  ;; Labeling: d(φ ⊗ ψ) = d(φ) ∪ d(ψ).
  (declare labeling ((ValuationAlgebra :v) (Eq :v) => :v -> :v -> Boolean))
  (define (labeling a b)
    (== (domain (combine a b)) (domain-union (domain a) (domain b))))

  ;; Marginal labeling: d(φ↓t) = d(φ) ∩ t.
  (declare marginal-labeling ((ValuationAlgebra :v) (Eq :v) => :v -> (List Variable) -> Boolean))
  (define (marginal-labeling a t)
    (== (domain (marginalize a t)) (domain-intersection (domain a) t)))

  ;; Projection identity: φ↓d(φ) = φ.
  (declare projection-identity ((ValuationAlgebra :v) (Eq :v) => :v -> Boolean))
  (define (projection-identity a)
    (== (marginalize a (domain a)) a))

  ;; Transitivity of marginalization, in the unconditional form valid for
  ;; total (project-to-intersection) marginalization: (φ↓s)↓t = φ↓(s ∩ t)
  ;; for ARBITRARY s and t. This implies the textbook form (φ↓s)↓t = φ↓t
  ;; for t ⊆ s ⊆ d(φ). See docs/THEORY.md §3.
  (declare transitivity ((ValuationAlgebra :v) (Eq :v) => :v -> (List Variable) -> (List Variable) -> Boolean))
  (define (transitivity a s t)
    (== (marginalize (marginalize a s) t)
        (marginalize a (domain-intersection s t))))

  ;; The combination axiom (compatibility of combination and
  ;; marginalization): (φ ⊗ ψ)↓d(φ) = φ ⊗ (ψ↓d(φ)). With total
  ;; marginalization the inner marginal is automatically ψ↓(d(φ) ∩ d(ψ)),
  ;; exactly as the axiom requires.
  (declare combination-axiom ((ValuationAlgebra :v) (Eq :v) => :v -> :v -> Boolean))
  (define (combination-axiom a b)
    (== (marginalize (combine a b) (domain a))
        (combine a (marginalize b (domain a)))))

  ;; Lift law: lifting preserves the domain.
  (declare lift-preserves-domain ((ValuationAlgebra :a) (ValuationAlgebra :b) (Liftable :a :b) => (types:Proxy :b) -> :a -> Boolean))
  (define (lift-preserves-domain p a)
    (== (domain (the-lifted p a)) (domain a)))

  (declare the-lifted ((Liftable :a :b) => (types:Proxy :b) -> :a -> :b))
  (define (the-lifted _ a) (lift a)))

;;; ------------------------------------------------------------------
;;; §2. The suite runner — still generic.
;;; ------------------------------------------------------------------

(coalton-toplevel
  (declare enumerate-from (Integer -> (List :a) -> (List (Tuple Integer :a))))
  (define (enumerate-from i xs)
    (match xs
      ((Nil) Nil)
      ((Cons x rest) (Cons (Tuple i x) (enumerate-from (+ i 1) rest)))))

  (declare enumerate ((List :a) -> (List (Tuple Integer :a))))
  (define (enumerate xs)
    (enumerate-from 0 xs))

  (declare fmt-ix (String -> (List Integer) -> String))
  (define (fmt-ix name ixs)
    (fold (fn (acc i) (<> acc (<> " " (into i))))
          name
          ixs))

  ;; Run every axiom over all pairs/triples drawn from FLEET, tagging each
  ;; check with CALC-NAME and the fleet indices involved so failures are
  ;; reproducible. Returns all executed checks.
  (declare run-axiom-suite ((ValuationAlgebra :v) (Eq :v) => String -> (List :v) -> (List CheckResult)))
  (define (run-axiom-suite calc-name fleet)
    (let ((ixed (enumerate fleet))
          (tag (fn (name ixs) (<> calc-name (<> ": " (fmt-ix name ixs)))))
          (unary
           (list:concatmap
            (fn (ia)
              (match ia
                ((Tuple i a)
                 (make-list
                  (check (tag "projection-identity" (make-list i))
                         (projection-identity a))))))
            ixed))
          (binary
           (list:concatmap
            (fn (ia)
              (match ia
                ((Tuple i a)
                 (list:concatmap
                  (fn (jb)
                    (match jb
                      ((Tuple j b)
                       (make-list
                        (check (tag "commutativity" (make-list i j))
                               (commutativity a b))
                        (check (tag "labeling" (make-list i j))
                               (labeling a b))
                        (check (tag "marginal-labeling" (make-list i j))
                               (marginal-labeling a (domain b)))
                        (check (tag "combination-axiom" (make-list i j))
                               (combination-axiom a b))))))
                  ixed))))
            ixed))
          (ternary
           (list:concatmap
            (fn (ia)
              (match ia
                ((Tuple i a)
                 (list:concatmap
                  (fn (jb)
                    (match jb
                      ((Tuple j b)
                       (list:concatmap
                        (fn (kc)
                          (match kc
                            ((Tuple k c)
                             (make-list
                              (check (tag "associativity" (make-list i j k))
                                     (associativity a b c))
                              (check (tag "transitivity" (make-list i j k))
                                     (transitivity a (domain b) (domain c)))))))
                        ixed))))
                  ixed))))
            ixed)))
      (append unary (append binary ternary)))))

;;; ------------------------------------------------------------------
;;; §3. Deterministic fleet generation.
;;; ------------------------------------------------------------------

(coalton-toplevel
  ;; A small LCG so fleets are pseudo-random but fully reproducible.
  (declare lcg-next (Integer -> Integer))
  (define (lcg-next seed)
    (mod (+ (* 1103515245 seed) 12345) 2147483648))

  ;; A degree in (0, 1]: (k+1)/16 for k in [0, 15]. Strictly positive so
  ;; both calculi accept it and the prob→poss lift is defined; in [0,1] so
  ;; the possibility constructor accepts it.
  (declare lcg-degrees (Integer -> UFix -> (List Fraction)))
  (define (lcg-degrees seed n)
    (if (== n 0)
        Nil
        (let ((next (lcg-next seed)))
          (Cons (math:exact/ (+ 1 (mod next 16)) 16)
                (lcg-degrees next (- n 1))))))

  ;; Build a valuation over VARS whose table is filled positionally from a
  ;; seeded degree stream.
  (declare seeded-valuation (Integer -> (List Variable) -> ((List Variable) -> (Config -> Fraction) -> :v) -> :v))
  (define (seeded-valuation seed vars constructor)
    (let ((configs (enumerate-configs vars))
          (degrees (lcg-degrees seed (length configs)))
          (table (list:zip configs degrees)))
      (constructor vars
                   (fn (c)
                     (match (list:find (fn (pr) (== (fst pr) c)) table)
                       ((Some pr) (snd pr))
                       ((None) (error "test fleet: configuration not found")))))))

  ;; Shared test variables. b's frame has three values so domains are not
  ;; all the same size; domains below overlap pairwise but none contains
  ;; another, which is where the combination axiom actually bites.
  (define var-a (make-variable "a" (make-list "0" "1")))
  (define var-b (make-variable "b" (make-list "lo" "mid" "hi")))
  (define var-c (make-variable "c" (make-list "x" "y")))

  (define fleet-domains
    (make-list
     (make-list var-a var-b)
     (make-list var-b var-c)
     (make-list var-a var-c)
     (make-list var-a var-b var-c)
     (make-list var-b)
     Nil))

  (declare build-fleet (((List Variable) -> (Config -> Fraction) -> :v) -> (List :v)))
  (define (build-fleet constructor)
    (map (fn (iv)
           (match iv
             ((Tuple i vars)
              (seeded-valuation (+ 7 (* 31 i)) vars constructor))))
         (enumerate fleet-domains)))

  (define prob-fleet (build-fleet probability))
  (define poss-fleet (build-fleet possibility)))

;;; ------------------------------------------------------------------
;;; §4. Instance registration + lift laws.
;;; ------------------------------------------------------------------

(coalton-toplevel
  ;; Lift laws for the Prob → Poss instance: domain preservation is the
  ;; generic Liftable law; that the result is a normalized possibility
  ;; distribution is specific to the ratio-scale transformation.
  (declare prob->poss-checks ((List (Valuation Prob)) -> (List CheckResult)))
  (define (prob->poss-checks fleet)
    (list:concatmap
     (fn (iv)
       (match iv
         ((Tuple i v)
          (let ((lifted (the (Valuation Poss) (lift v))))
            (make-list
             (check (<> "lift prob->poss: preserves-domain " (into i))
                    (lift-preserves-domain (types:proxy-of lifted) v))
             (check (<> "lift prob->poss: result-normalized " (into i))
                    (poss-normalized? lifted)))))))
     (enumerate fleet)))

  ;; Every registered calculus, in one place. Adding calculus #3 to the
  ;; suite means adding one run-axiom-suite line here with its fleet.
  (declare all-results (Unit -> (List CheckResult)))
  (define (all-results)
    (append (run-axiom-suite "probability" prob-fleet)
            (append (run-axiom-suite "possibility" poss-fleet)
                    (prob->poss-checks prob-fleet))))

  (declare failed-checks (Unit -> (List String)))
  (define (failed-checks)
    (map fst (list:filter (fn (r) (not (snd r))) (all-results))))

  (declare total-check-count (Unit -> UFix))
  (define (total-check-count)
    (length (all-results))))

;;; ------------------------------------------------------------------
;;; §5. Lisp-side driver: prints a report, errors (non-zero exit under
;;; --non-interactive) on any failure.
;;; ------------------------------------------------------------------

(cl:defun run-tests ()
  (cl:let ((failures (coalton (failed-checks)))
           (total (coalton (total-check-count))))
    (cl:cond
      ((cl:null failures)
       (cl:format cl:t "~&parliament axiom suite: ~a checks, all passed.~%" total)
       cl:t)
      (cl:t
       (cl:format cl:t "~&parliament axiom suite: ~a of ~a checks FAILED:~%"
                  (cl:length failures) total)
       (cl:dolist (f failures)
         (cl:format cl:t "  FAIL ~a~%" f))
       (cl:error "parliament axiom suite failed (~a failures)" (cl:length failures))))))
