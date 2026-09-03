;;;; core.lisp -- the calculus-independent core
;;;;
;;;; The meat and potatoes are here:
;;;;
;;;;   1. Domains: finite discrete variables with named frames.
;;;;      These have configurations which assign frame values to
;;;;      a domain.
;;;;   2. The Open Typeclasses:
;;;;        - ValuationAlgebra (combine/marginalize/domain)
;;;;        - Liftable (explicit cross-calculus coercion).
;;;;   3. Calculus stuff. A shared table repr (Valuation :calc)
;;;;      It has a phantom calculus tag and a Calculus class which derives
;;;;      from ValuationAlgebra for any semiring-style calculus
;;;;      (God it sounds so deliciously dorky to say that)
;;;;
;;;; FYI:
;;;;  - See docs/THEORY.md for the axioms this implements
;;;;  - See docs/EXTENSION_PROTOCOL.md for the cookbook to create a calculus

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

;;; Variables, domains, configurations

(coalton-toplevel
  ;; A normal discrete variable with its finite, non-empty frame of possible
  ;; values. Two variables are the same variable if (and only iff) they agree
  ;; on the name and frame. If the two variables share a name but not a frame,
  ;; then that's illegal and the cops storm in (error).
  (define-type Variable
    (%Variable String (List String)))

  (declare make-variable (String -> (List String) -> Variable))
  (define (make-variable name frame)
    "Create a variable NAME whose finite frame of values is FRAME. FRAME must be non-empty and duplicate-free."
    (match frame
      ((Nil) (error "Parliament: Variable frame must be non-empty"))
      (_ (if (== (length (list:remove-duplicates frame)) (length frame))
             (%Variable name frame)
             (error "Parliament: Variable frame contains duplicate values")))))

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

  ;; A configuration of a domain d = (x1 ... xn). Its where the domain is sorted
  ;; by variable name: a list (v1 ... vn) with v_i drawn from x_i's frame.
  ;; This is positionally aligned with the sorted domain.
  (define-type-alias Config (List String))

  ;; Domains are kept sorted by variable name with no duplicates.;;
  ;; Sorting is what makes the Config's position encoding canonical.
  ;; (declare check-adjacent-frames ((List Variable) -> (List Variable)))
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
    "The union of two domains, sorted and duplicate-free.
     Errors if the two domains disagree on the frame of a shared variable name."
    (normalize-domain (append a b)))

  (declare domain-intersection ((List Variable) -> (List Variable) -> (List Variable)))
  (define (domain-intersection a b)
    "The intersection of two domains, sorted and duplicate-free."
    (normalize-domain (list:filter (fn (v) (list:member v b)) a)))

  (declare subdomain? ((List Variable) -> (List Variable) -> Boolean))
  (define (subdomain? a b)
    "Is all of A also in B?"
    (list:all (fn (v) (list:member v b)) a))

  (declare enumerate-configs ((List Variable) -> (List Config)))
  (define (enumerate-configs dom)
    "All configurations of DOM, in lexicographic frame order.
    The empty domain has exactly one configuration: the empty one."
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

;;; Algebra classes

(coalton-toplevel
  ;; A valuation algebra in the sense of Kohlas (docs/THEORY.md section 2): a
  ;; type of valuations, each labeled with the domain (set of variables) it
  ;; carries information about, closed under combination and marginalization.
  ;;
  ;; An instance must satisfy six laws: labeling, commutativity and
  ;; associativity of combine, projection, transitivity, and combination.
  ;; They are stated formally in docs/THEORY.md section 2 and checked
  ;; generically by tests/axioms.lisp.
  ;;
  ;; Marginalization here is total: it projects a valuation to the
  ;; intersection of its domain with the target, rather than being defined
  ;; only when the target is already a subdomain. See docs/THEORY.md section 3
  ;; for why this is equivalent to (and slightly stronger than) the textbook
  ;; presentation.
  (define-class (ValuationAlgebra :v)
    (domain (:v -> (List Variable)))
    (combine (:v -> :v -> :v))
    (marginalize (:v -> (List Variable) -> :v)))

  ;; An explicit, semantically justified coercion from one calculus's
  ;; valuations to another's. There is deliberately NO blanket or implicit
  ;; instance: combining valuations of two calculi is a type error unless
  ;; someone has published (and justified in docs/THEORY.md section 5) a
  ;; Liftable instance and the call site applies it explicitly.
  ;;
  ;; Two laws, stated in docs/THEORY.md section 5: a lift preserves the
  ;; domain, and it preserves the information ordering. The first is checked
  ;; generically by tests/axioms.lisp. A lift is NOT required (or in general
  ;; able) to commute with combine and marginalize.
  (define-class (Liftable :from :to)
    (lift (:from -> :to))))

;;; The shared table representation and semiring-style calculus

(coalton-toplevel
  ;; One concrete valuation representation shared by all pointwise calculi:
  ;; a normalized domain together with a TOTAL table assigning a Fraction
  ;; degree to every configuration of that domain. The :calc parameter is a
  ;; phantom type: it has no runtime representation; its only job is to
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
  ;; obligations on an instance (docs/THEORY.md section 4) are exactly that
  ;; (Fraction-degrees, marginal-op, combine-op) restricted to the calculus's
  ;; degree set forms a commutative semiring:
  ;;   - combine-op is associative and commutative
  ;;   - marginal-op is associative and commutative with neutral
  ;;     marginal-neutral
  ;;   - combine-op distributes over marginal-op
  ;; Under those obligations the blanket instance below is a lawful
  ;; ValuationAlgebra; that is a theorem (docs/THEORY.md section 4), and
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
  ;; degree and reinterpret the result under a different calculus tag.
  ;; Retagging is by convention confined to Liftable instances, which is
  ;; where the semantic justification belongs (tabulate is also
  ;; phantom-polymorphic, so the confinement is protocol, not typing;
  ;; see docs/EXTENSION_PROTOCOL.md section 2).
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

    ;; For each configuration c of the combined domain (the union of the two
    ;; input domains), the result degree at c is combine-op applied to each
    ;; input's degree at c restricted to that input's domain.
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

    ;; The result degree at each configuration c of the target is the
    ;; marginal-op fold of every input degree whose configuration restricts to
    ;; c. Total: projects to the intersection of the domain with the target.
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
