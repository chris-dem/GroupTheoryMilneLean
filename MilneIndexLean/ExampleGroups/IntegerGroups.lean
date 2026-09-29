import MilneIndexLean.Basic

def ZAddGroup := ℤ deriving Add, Neg, Sub, OfNat, DecidableEq


instance : MyGroupOps ZAddGroup where
  op x y:=  x +y
  inv x :=  - x



instance : MyGroup ZAddGroup where
  ε := 0

  op_assoc := Int.add_assoc
  op_id := Int.add_zero
  op_inv := Int.sub_self




