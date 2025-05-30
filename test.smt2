(set-logic HORN)
(set-option :produce-models true)

(declare-fun inv (Int Int) Bool)

(assert
    (forall ((n Int))
        (=> (<= 0 n)
            (inv 0 n))))

(assert
    (forall ((i Int) (n Int))
        (=> (and (< i n) (inv i n))
            (inv (+ i 1) n))))

(assert
    (forall ((i Int) (n Int))
        (=> (and (not (< i n)) (inv i n) (distinct i n))
            false)))

(check-sat)
(get-model)