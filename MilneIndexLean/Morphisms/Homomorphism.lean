import MilneIndexLean.Basic

universe u

variable  {G H: Type u}


section MyGroupHom

structure MyGroupHom (G H: Type u) [MyGroup G] [MyGroup H] where
  toFun: G → H
  map_op : ∀ x y:G, toFun (x * y) = toFun x * toFun y

structure MyGroupInjHom (G H: Type u) [MyGroup G] [MyGroup H] extends MyGroupHom G H where
  injectivity: Function.Injective toFun

structure MyGroupSurjHom (G H: Type u) [MyGroup G] [MyGroup H] extends MyGroupHom G H where
  surjectivity: Function.Surjective toFun

infixr:25 " →ᵍ " => MyGroupHom
infixr:25 " ↪ᵍ " => MyGroupInjHom
infixr:25 " ↠ᵍ " => MyGroupSurjHom

  
end MyGroupHom
