 (declare-fun constr ((Array Int Int)(Array Int Int)) Bool)
    (declare-fun a ((Array (Array Int Int) Int)) (Array Int Int))
    (declare-const test (Array (Array Int Int) Int))
    (declare-fun b () (Array Int Int))
    (assert (constr (a test) b))
