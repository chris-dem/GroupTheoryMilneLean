import MilneIndexLean.Basic
import MilneIndexLean.Morphisms.Homomorphism

universe u

variable  {G H: Type u} [MyGroup G] [MyGroup H]


section MyGroupIso

structure MyGroupIso (G H: Type u) [MyGroup G] [MyGroup H] 
  extends MyGroupSurjHom G H, MyGroupInjHom G H where

def MyGroupIsomorphic (G H : Type u)[MyGroup G] [MyGroup H]: Prop :=
  Nonempty (MyGroupIso G H)

infixl:25 " ≃ᵍ " => MyGroupIso
infix:25 " ≅ᵍ " => MyGroupIsomorphic
end MyGroupIso
