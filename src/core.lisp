;;;; core.lisp — the calculus-independent core of the valuation-algebra
;;;; architecture.
;;;;
;;;; Three layers live here:
;;;;
;;;;   1. Domains: finite discrete variables with named frames, and
;;;;      configurations (assignments of frame values to a domain).
;;;;   2. The open typeclasses: ValuationAlgebra (combine/marginalize/domain)
;;;;      and Liftable (explicit cross-calculus coercion).
;;;;   3. A shared table representation (Valuation :calc) with a phantom
;;;;      calculus tag, and the Calculus class whose single blanket instance
;;;;      derives ValuationAlgebra for any semiring-style calculus.
;;;;
;;;; See docs/THEORY.md for the axioms this implements and
;;;; docs/EXTENSION_PROTOCOL.md for how to add a calculus without reading
;;;; this file.

(defpackage #:parliament/core
  (:use #:coalton #:coalton-prelude)
  (:shadow #:lift)
  (:local-nicknames (#:map #:coalton-library/ordmap)
                    (#:list #:coalton-library/list)
                    (#:iter #:coalton-library/iterator)
                    (#:types #:coalton-library/types))
  (:export
   ;; variables, domains, configurations
   #:Variable
   #:make-variable
   #:variable-name
   #:variable-frame
   #:Config
   #:domain-union
   #:domain-intersection
   #:subdomain?
   #:enumerate-configs
   #:restrict-config
   ;; the algebra classes
   #:ValuationAlgebra
   #:combine
   #:marginalize
   #:domain
   #:Liftable
   #:lift
   ;; the shared table representation and its calculus class
   #:Valuation
   #:Calculus
   #:combine-op
   #:marginal-op
   #:marginal-neutral
   #:tabulate
   #:valuation-entries
   #:valuation-value
   #:transform-retag))

(in-package #:parliament/core)

(named-readtables:in-readtable coalton:coalton)

;;; ------------------------------------------------------------------
;;; Variables, domains, configurations
;;; ------------------------------------------------------------------

(coalton-toplevel
  ;; A discrete variable: a name together with its finite, non-empty frame
  ;; of possible values. Two variables are the same variable iff they agree
  ;; on both name and frame; two variables sharing a name but not a frame
  ;; are ill-formed in one model and rejected when domains are merged.
  (define-type Variable
    (%Variable String (List String)))

  (declare make-variable (String -> (List String) -> Variable))
  (define (make-variable name frame)
    "Create a variable NAME whose finite frame of values is FRAME.
FRAME must be non-empty and duplicate-free."
    (match frame
      ((Nil) (error "parliament: variable frame must be non-empty"))
      (_ (if (== (length (list:remove-duplicates frame)) (length frame))
             (%Variable name frame)
             (error "parliament: variable frame contains duplicate values")))))

  (declare variable-name (Variable -> String))
  (define (variable-name v)
    (match v ((%Variable n _) n)))

  (declare variable-frame (Variable -> (List String)))
  (define (variable-frame v)
    (match v ((%Variable _ f) f)))

  (define-instance (Eq Variable)
    (define (== a b)
      (and (== (variable-name a) (variable-name b))
           (== (variable-frame a) (variable-frame b)))))

  (define-instance (Ord Variable)
    (define (<=> a b)
      (<=> (Tuple (variable-name a) (variable-frame a))
           (Tuple (variable-name b) (variable-frame b)))))

  ;; A configuration of a domain d = (x1 ... xn), where the domain is sorted
  ;; by variable name: a list (v1 ... vn) with vi drawn from xi's frame,
  ;; positionally aligned with the sorted domain.
  (define-type-alias Config (List String))

  ;; Domains are kept sorted by variable name with no duplicates. Sorting is
  ;; what makes a Config's positional encoding canonical.
  (declare check-adjacent-frames ((List Variable) -> (List Variable)))
  (define (check-adjacent-frames sorted)
    (match sorted
      ((Nil) Nil)
      ((Cons a (Nil)) (make-list a))
      ((Cons a (Cons b rest))
       (if (== a b)
           (check-adjacent-frames (Cons b rest))
           (if (== (variable-name a) (variable-name b))
               (error (<> "parliament: variable occurs with two different frames: "
                          (variable-name a)))
               (Cons a (check-adjacent-frames (Cons b rest))))))))

  (declare normalize-domain ((List Variable) -> (List Variable)))
  (define (normalize-domain vars)
    (check-adjacent-frames (list:sort vars)))

  (declare domain-union ((List Variable) -> (List Variable) -> (List Variable)))
  (define (domain-union a b)
    "The union of two domains, sorted and duplicate-free. Errors if the two
domains disagree on the frame of a shared variable name."
    (normalize-domain (append a b)))

  (declare domain-intersection ((List Variable) -> (List Variable) -> (List Variable)))
  (define (domain-intersection a b)
    "The intersection of two domains, sorted and duplicate-free."
    (normalize-domain (list:filter (fn (v) (list:member v b)) a)))

  (declare subdomain? ((List Variable) -> (List Variable) -> Boolean))
  (define (subdomain? a b)
    "Is every variable of A also in B?"
    (list:all (fn (v) (list:member v b)) a))

  (declare enumerate-configs ((List Variable) -> (List Config)))
  (define (enumerate-configs dom)
    "All configurations of DOM, in lexicographic frame order. The empty
domain has exactly one configuration: the empty one."
    (match dom
      ((Nil) (make-list Nil))
      ((Cons v rest)
       (let ((tails (enumerate-configs rest)))
         (list:concatmap
          (fn (val) (map (fn (tl) (Cons val tl)) tails))
          (variable-frame v))))))

  (declare restrict-config ((List Variable) -> Config -> (List Variable) -> Config))
  (define (restrict-config dom config target)
    "Restrict CONFIG (a configuration of DOM) to the variables of TARGET.
TARGET must be a subset of DOM; both must be normalized (sorted) domains."
    (map snd
         (list:filter (fn (pr) (list:member (fst pr) target))
                      (list:zip dom config)))))

;;; ------------------------------------------------------------------
;;; The algebra classes
;;; ------------------------------------------------------------------

(coalton-toplevel
  ;; A valuation algebra in the sense of Kohlas (docs/THEORY.md §2): a type
  ;; of valuations, each labeled with the domain (set of variables) it
  ;; carries information about, closed under combination and marginalization.
  ;;
  ;; Laws (checked generically by tests/axioms.lisp):
  ;;   labeling        d(combine φ ψ) = d(φ) ∪ d(ψ), d(marginalize φ t) = d(φ) ∩ t
  ;;   commutativity   combine φ ψ = combine ψ φ
  ;;   associativity   combine φ (combine ψ χ) = combine (combine φ ψ) χ
  ;;   projection      marginalize φ (d φ) = φ
  ;;   transitivity    marginalize (marginalize φ s) t = marginalize φ (s ∩ t)
  ;;   combination     marginalize (combine φ ψ) (d φ) = combine φ (marginalize ψ (d φ))
  ;;
  ;; Note that marginalization here is total: it projects to d(φ) ∩ t rather
  ;; than being partial on t ⊆ d(φ). See docs/THEORY.md §3 for why this is
  ;; equivalent to (and slightly stronger than) the textbook presentation.
  (define-class (ValuationAlgebra :v)
    (domain (:v -> (List Variable)))
    (combine (:v -> :v -> :v))
    (marginalize (:v -> (List Variable) -> :v)))

  ;; An explicit, semantically justified coercion from one calculus's
  ;; valuations to another's. There is deliberately NO blanket or implicit
  ;; instance: combining valuations of two calculi is a type error unless
  ;; someone has published (and justified — docs/THEORY.md §5) a Liftable
  ;; instance and the call site applies it explicitly.
  ;;
  ;; Laws (the first is checked generically by tests/axioms.lisp):
  ;;   domain preservation   d(lift φ) = d(φ)
  ;;   monotonicity          lift preserves the information ordering
  ;; A lift is NOT required (or in general able) to commute with combine and
  ;; marginalize; see docs/THEORY.md §5.
  (define-class (Liftable :from :to)
    (lift (:from -> :to))))

;;; ------------------------------------------------------------------
;;; The shared table representation and semiring-style calculi
;;; ------------------------------------------------------------------

(coalton-toplevel
  ;; One concrete valuation representation shared by all pointwise calculi:
  ;; a normalized domain together with a TOTAL table assigning a Fraction
  ;; degree to every configuration of that domain. The :calc parameter is a
  ;; phantom type — it has no runtime representation; its only job is to
  ;; make (Valuation Prob) and (Valuation Poss) distinct types so the
  ;; compiler rejects cross-calculus combination.
  (define-type (Valuation :calc)
    (%Valuation (List Variable) (map:OrdMap Config Fraction)))

  (define-instance (Eq (Valuation :calc))
    (define (== a b)
      (match (Tuple a b)
        ((Tuple (%Valuation da ta) (%Valuation db tb))
         (and (== da db) (== ta tb))))))

  ;; A pointwise calculus over exact rational degrees: the two semiring
  ;; operations and the neutral element of the marginal operation. The
  ;; obligations on an instance (docs/THEORY.md §4) are exactly that
  ;; (Fraction-degrees, marginal-op, combine-op) restricted to the calculus's
  ;; degree set forms a commutative semiring:
  ;;   - combine-op is associative and commutative
  ;;   - marginal-op is associative and commutative with neutral
  ;;     marginal-neutral
  ;;   - combine-op distributes over marginal-op
  ;; Under those obligations the blanket instance below is a lawful
  ;; ValuationAlgebra — that is a theorem (docs/THEORY.md §4), and
  ;; tests/axioms.lisp re-checks it concretely for every instance.
  ;;
  ;; Dispatch is by phantom tag, so each method takes a Proxy of the tag.
  (define-class (Calculus :calc)
    (combine-op ((types:Proxy :calc) -> Fraction -> Fraction -> Fraction))
    (marginal-op ((types:Proxy :calc) -> Fraction -> Fraction -> Fraction))
    (marginal-neutral ((types:Proxy :calc) -> Fraction)))

  (declare calc-proxy ((Valuation :calc) -> (types:Proxy :calc)))
  (define (calc-proxy _v) types:Proxy)

  (declare table-get ((map:OrdMap Config Fraction) -> Config -> Fraction))
  (define (table-get table config)
    (match (map:lookup table config)
      ((Some x) x)
      ((None) (error "parliament: internal error: valuation table is not total"))))

  (declare tabulate ((List Variable) -> (Config -> Fraction) -> (Valuation :calc)))
  (define (tabulate vars f)
    "Build a valuation over VARS whose degree at each configuration c is
(F c). Configurations are passed with values positionally aligned to the
name-sorted, deduplicated form of VARS (use `domain` on the result to see
that order)."
    (let ((dom (normalize-domain vars)))
      (%Valuation
       dom
       (map:collect!
        (iter:into-iter
         (map (fn (c) (Tuple c (f c)))
              (enumerate-configs dom)))))))

  (declare valuation-entries ((Valuation :calc) -> (List (Tuple Config Fraction))))
  (define (valuation-entries v)
    "All (configuration, degree) pairs of V, in the canonical (sorted-domain,
lexicographic-config) order."
    (match v
      ((%Valuation _ table) (iter:collect! (map:entries table)))))

  (declare valuation-value ((Valuation :calc) -> Config -> (Optional Fraction)))
  (define (valuation-value v config)
    "The degree V assigns to CONFIG (positionally aligned with (domain V)),
or None if CONFIG is not a configuration of V's domain."
    (match v
      ((%Valuation _ table) (map:lookup table config))))

  ;; The escape hatch Liftable instances are built from: transform every
  ;; degree and reinterpret the result under a different calculus tag. This
  ;; is the ONLY exported way to change a valuation's tag, so every
  ;; cross-calculus flow is forced through a deliberate use of it — normally
  ;; inside a Liftable instance, which is where the semantic justification
  ;; belongs.
  (declare transform-retag ((Fraction -> Fraction) -> (Valuation :a) -> (Valuation :b)))
  (define (transform-retag f v)
    (match v
      ((%Valuation dom table) (%Valuation dom (map f table)))))

  ;; The single blanket instance: any Calculus tag yields a ValuationAlgebra
  ;; on its tables. Extension authors adding a pointwise calculus never
  ;; write combine/marginalize themselves.
  (define-instance ((Calculus :calc) => ValuationAlgebra (Valuation :calc))
    (define (domain v)
      (match v ((%Valuation d _) d)))

    ;; (φ ⊗ ψ)(c) = combine-op φ(c↓d(φ)) ψ(c↓d(ψ)) for every configuration c
    ;; of d(φ) ∪ d(ψ).
    (define (combine a b)
      (match (Tuple a b)
        ((Tuple (%Valuation da ta) (%Valuation db tb))
         (let ((p (calc-proxy a))
               (dom (domain-union da db)))
           (%Valuation
            dom
            (map:collect!
             (iter:into-iter
              (map (fn (c)
                     (Tuple c (combine-op p
                                          (table-get ta (restrict-config dom c da))
                                          (table-get tb (restrict-config dom c db)))))
                   (enumerate-configs dom)))))))))

    ;; (φ↓t)(c) = marginal-op-fold over { φ(c') : c' a configuration of d(φ)
    ;; with c'↓(d(φ)∩t) = c }. Total: projects to d(φ) ∩ t.
    (define (marginalize v target)
      (match v
        ((%Valuation dom table)
         (let ((p (calc-proxy v))
               (tgt (domain-intersection dom (normalize-domain target)))
               (seed (fold (fn (acc c)
                             (map:insert acc c (marginal-neutral p)))
                           (the (map:OrdMap Config Fraction) map:empty)
                           (enumerate-configs tgt))))
           (%Valuation
            tgt
            (iter:fold! (fn (acc entry)
                          (match entry
                            ((Tuple c x)
                             (let ((c2 (restrict-config dom c tgt)))
                               (map:insert acc c2 (marginal-op p (table-get acc c2) x))))))
                        seed
                        (map:entries table)))))))))
