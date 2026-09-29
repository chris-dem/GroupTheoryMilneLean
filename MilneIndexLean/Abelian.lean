import MilneIndexLean.Basic

universe u
variable  {G: Type u}

open MyGroup


  
class MyAbelianGroup (G : Type u) extends MyGroup G where
  op_comm:  ∀ x y :G, x * y = y * x

open MyAbelianGroup

instance [MyAbelianGroup G]: Add G where
  add x y := MyGroupOps.op x y

instance [MyAbelianGroup G]: HMul ℤ G G where
  hMul x y := power y x

instance [MyAbelianGroup G]: HMul ℕ G G where
  hMul x y := power y x

example [MyAbelianGroup G](a: G) (x y : ℤ):  (x * a) + (y * a) = (x+y) * a :=
    pow_distr a x y


theorem comm_mul_add [MyAbelianGroup G] (a: ℕ) : ∀ x y:G,  a*x +  a* y = a*(x+y)
  := by
    intro x y
    induction a  with
      | zero =>
        change (ε: G) * ε =  ε
        rw [op_id]
      | succ c ih =>
        change x^(c+1) * y^(c+1) = (x+y)^(c+1)
        change x^(c) * y^(c) = (x+y)^(c) at ih
        rw [power_succ_nat, power_succ_nat, op_comm x,
          op_assoc, op_comm x, op_comm y,  op_assoc, 
          ← op_assoc  (c:= y*x),ih, op_comm y]
        change (x*y)^c * (x*y) = (x*y)^(c+1)
        rw [op_comm, ← power_succ_nat]
