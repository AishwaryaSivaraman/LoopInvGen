(set-logic LIA)

(declare-primed-var conf_0 Int)
(declare-primed-var n Int)
(declare-primed-var x Int)

(declare-primed-var conf_0_0 Int)
(declare-primed-var conf_0_1 Int)
(declare-primed-var conf_0_2 Int)
(declare-primed-var n_0 Int)
(declare-primed-var x_0 Int)
(declare-primed-var x_1 Int)
(declare-primed-var x_2 Int)
(declare-primed-var x_3 Int)

(synth-inv inv-f ((conf_0 Int) (n Int) (x Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (n_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int)))

(define-fun pre-f ((conf_0 Int) (n Int) (x Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (n_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int)) Bool
  (and
    (= conf_0 conf_0_0)
    (= n n_0)
    (= x x_1)
    (= conf_0_0 1)
    (= x_1 n_0)
 )
)

(define-fun trans-f ((conf_0 Int) (n Int) (x Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (n_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int) (conf_0! Int) (n! Int) (x! Int) (conf_0_0! Int) (conf_0_1! Int) (conf_0_2! Int) (n_0! Int) (x_0! Int) (x_1! Int) (x_2! Int) (x_3! Int)) Bool
  (or
    (and
      (= conf_0_1 conf_0)
      (= x_2 x)
      (= conf_0_1 conf_0!)
      (= x_2 x!)
      (= conf_0 conf_0!)
      (= n n!)
   )
    (and
      (= conf_0_1 conf_0)
      (= x_2 x)
      (> x_2 0)
      (= x_3 (- x_2 1))
      (= conf_0_2 conf_0_1)
      (= conf_0_2 conf_0!)
      (= x_3 x!)
      (= n n_0)
      (= n! n_0)
   )
 )
)

(define-fun post-f ((conf_0 Int) (n Int) (x Int) (conf_0_0 Int) (conf_0_1 Int) (conf_0_2 Int) (n_0 Int) (x_0 Int) (x_1 Int) (x_2 Int) (x_3 Int)) Bool
  (or
    (not
      (and
        (= conf_0 conf_0_1)
        (= n n_0)
        (= x x_2)
     )
   )
    (not
      (and
        (not (> x_2 0))
        (not (= x_2 0))
        (not (< n_0 0))
     )
   )
 )
)

(inv-constraint inv-f pre-f trans-f post-f)
(check-synth)
