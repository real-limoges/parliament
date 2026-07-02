(asdf:defsystem #:parliament
  :description "An extensible typed architecture for valuation algebras in Coalton."
  :author "real-limoges"
  :license "See LICENSE"
  :depends-on (#:coalton)
  :serial t
  :components ((:module "src"
                :serial t
                :components ((:file "core")
                             (:file "probability")
                             (:file "possibility")))))

(asdf:defsystem #:parliament/tests
  :description "Generic axiom test suite for parliament valuation algebras."
  :depends-on (#:parliament)
  :serial t
  :components ((:module "tests"
                :components ((:file "axioms"))))
  :perform (asdf:test-op (o s)
             (uiop:symbol-call '#:parliament/tests '#:run-tests)))
