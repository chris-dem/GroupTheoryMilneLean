import Mathlib.Logic.Function.Basic
import Mathlib.SetTheory.Cardinal.Basic 
import Mathlib.Data.Fintype.Pigeonhole


section MyGroup
universe u
variable  {G: Type u}


class MyGroupOps (G: Type u) where
  op : G → G → G
  inv : G → G

-- infixl:70 " * " => MyGroupOps.op  
postfix:max "⁻¹" => MyGroupOps.inv 


instance [MyGroupOps G]: Mul G where
  mul x y := MyGroupOps.op x y

class MyGroup (G: Type u) extends MyGroupOps G where
  ε  : G
  op_assoc :
    ∀ a b c: G, (a * b) * c = a * (b * c)
  
  op_id :
    ∀ a : G, a * ε = a

  op_inv :
    ∀ a : G, a * a⁻¹ = ε  

class MyFiniteGroup (G: Type u) extends MyGroup G , Fintype G where




open MyGroup

theorem op_right_cancel [MyGroup G] {a b c : G} (h : a * c= b*c) : a = b := by
  have h2 := congrArg (· * c⁻¹) h
  rw [op_assoc, op_assoc, op_inv, op_id, op_id] at h2
  exact h2
  
@[simp, grind =] theorem op_right_cancel_iff [MyGroup G] {a b c : G} : a * c = b * c ↔ a = b :=
  ⟨op_right_cancel, congrArg (· * c)⟩


@[simp, grind =] theorem id_op [MyGroup G] (x : G) :
    ε * x = x := by 
      apply (op_right_cancel_iff (a := ε*x) (b:= x) (c := x⁻¹)).mp
      rw [op_assoc, op_inv, op_id]

@[simp, grind =] theorem inv_mul[MyGroup G] (x : G) :
    x⁻¹ * x = ε := by 
      have h := MyGroup.op_inv x
      apply (op_right_cancel_iff (a := x⁻¹ * x) (b:= ε) (c := x⁻¹)).mp
      rw [op_assoc, op_inv, id_op, op_id]


theorem op_left_cancel [MyGroup G] {a b c : G} (h : c*a = c*b) : a = b := by
  have h2 := congrArg (c⁻¹ * ·) h
  rw [← op_assoc, ←op_assoc, inv_mul, id_op, id_op] at h2
  exact h2
  
@[simp, grind =] theorem op_left_cancel_iff [MyGroup G] {a b c : G} : c * a = c * b ↔ a = b :=
  ⟨op_left_cancel, congrArg  (c * ·)⟩

theorem unique_natural [MyGroup G] (x y :G) (h : x * y = x):  y = ε := by
  have heq := congrArg (x⁻¹ * ·) h
  rw [← op_assoc, inv_mul, id_op] at heq
  exact heq

theorem unique_inverse [MyGroup G] (x y : G) (h : x * y = ε):  y = x⁻¹ := by
  have heq := congrArg (x⁻¹ * ·) h
  rw [← op_assoc, inv_mul, id_op, op_id] at heq
  exact heq

theorem inverse_distributivity [MyGroup G] (x y : G):
    (x*y)⁻¹ = y⁻¹* x⁻¹ := by
    apply (op_right_cancel_iff (a := (x*y)⁻¹) (b:= y⁻¹ * x⁻¹) (c := (x*y))).mp
    rw [inv_mul, op_assoc, ← op_assoc (x⁻¹), inv_mul, id_op, inv_mul]


theorem left_mul_isomorphism [MyGroup G] (x : G):
      Function.Bijective (fun a : G => x * a) := by
        constructor
        · -- Injective
          rw [Function.Injective]
          intro a b
          simp only [op_left_cancel_iff, imp_self]
        · -- Surjective
          rw [Function.Surjective]
          intro b
          apply Exists.intro (x⁻¹*b)
          rw [←op_assoc, op_inv,id_op]


theorem right_mul_isomorphism [MyGroup G] (a : G):
      Function.Bijective (fun x : G =>  x*a) := by
        constructor
        · -- Injective
          rw [Function.Injective]
          intro a b
          simp only [op_right_cancel_iff, imp_self]
        · -- Surjective
          rw [Function.Surjective]
          intro b
          apply Exists.intro (b * a⁻¹)
          rw [op_assoc, inv_mul,op_id]

def groupOrder (G: Type u) [MyGroup G] : Cardinal := Cardinal.mk G

@[simp] def power' (a : G) [MyGroup G] : ℕ → G
  | .zero => ε
  | .succ n => a * power' a n
  
@[simp] def power (a : G) [MyGroup G] : ℤ→ G
  | .ofNat n => power' a n
  | .negSucc n => power' (a⁻¹) (n+1)

instance [MyGroup G]: Pow G Int where
  pow := fun g n => power g n

instance [MyGroup G]: Pow G Nat where
  pow g n := power g (Int.ofNat n)


theorem power'_zero [MyGroup G] (a : G) :
    power' a 0 = ε := rfl

theorem power'_succ [MyGroup G] (a : G) (n : ℕ) :
    power' a (n + 1) = a * power' a n := rfl

@[simp] theorem power_ofNat [MyGroup G] (a : G) (n : ℕ) :
    power a (.ofNat n) = power' a n := rfl

@[simp] theorem power_neg_nat [MyGroup G] (a : G) (n : ℕ) :
    power a (.negSucc n) = power' (a⁻¹) (n + 1) := rfl

@[simp] theorem power_neg_mul [MyGroup G] (a : G) (n : ℕ) :
    a * power a (.negSucc n) = power' (a⁻¹) n := by 
      induction n with
        | zero => 
          simp [op_id,op_inv]
        | succ x ih =>
          simp
          rw [←op_assoc, op_inv, id_op]

@[simp] theorem power_succ [MyGroup G] (a : G) (n : ℤ):
    a^(n+1) = a* a^n := by
      change power a (n+1) = a * power a n
      cases n with
        | ofNat x =>
          change power a (.ofNat (x+1)) = a * power a (Int.ofNat x)
          simp only [power, power']
        | negSucc n =>
          induction n with
            | zero =>
              simp only [power, Int.reduceNegSucc, neg_add_cancel, power', op_id, op_inv]
            | succ h ih =>
              rw [power_neg_nat] at ih
              rw [power, power', ←op_assoc,op_inv, id_op]
              apply op_left_cancel_iff (c := a).mp
              simp only [power, Int.negSucc_eq, Int.natCast_add, Int.cast_ofNat_Int, neg_add_rev,
                Int.reduceNeg, neg_add_cancel_comm, power', op_left_cancel_iff] 
              change power a (-1 + -h )  = power a (-(h+1))
              simp only [power, Int.reduceNeg, power', neg_add_rev]

@[simp] theorem power_succ_nat [MyGroup G] (a : G) (n : ℕ):
    a^(n+1) = a* a^n := power_succ a (Int.ofNat n)

@[simp] theorem power_pred [MyGroup G] (a : G) (n : ℤ):
    a^(n-1) = a⁻¹* a^n   := by
      change power a (n-1) = a⁻¹ * power a n
      cases n with
        | negSucc n =>
          change power a (.negSucc (n+1)) = a⁻¹ * power a (Int.negSucc n)
          simp only [power, power']
        | ofNat n =>
          cases n with
            | zero =>
              simp only [power, Int.ofNat_eq_natCast, Int.cast_ofNat_Int, zero_sub, Int.reduceNeg,
                power', op_id]
              change a⁻¹ * power' a⁻¹ 0 = a⁻¹ 
              rw [power', op_id]
            | succ h =>
              simp only [power, Int.ofNat_eq_natCast, Int.natCast_add, Int.cast_ofNat_Int,
                add_sub_cancel_right, power', ← op_assoc, inv_mul, id_op]
              
theorem pow_distr [MyGroup G] (a : G): ∀ n m : ℤ, a^n * a^m = a^(n+m) := by
  intro n m
  induction n with
    | zero =>
      change power a 0 * power a m = power a (0+m)
      simp
    | succ x ih =>
      rw [Int.add_right_comm, power_succ, power_succ, ←ih, op_assoc]
    | pred x ih =>
      rw [Int.sub_eq_add_neg, Int.add_right_comm
        ,← Int.sub_eq_add_neg (b := 1) ,← Int.sub_eq_add_neg (b := 1)
        , power_pred, power_pred, ←ih, op_assoc]

theorem pow_distr_nat [MyGroup G] (a : G): ∀ n m : ℕ, a^n * a^m = a^(n+m) := by
  intro n m
  exact pow_distr a (.ofNat n) (.ofNat m)

noncomputable def orderElem (a: G) [MyGroup G]  : ℕ :=by
  classical
  let A := {n : ℕ| n > 0 ∧ power a n = ε}
  exact if h: A.Nonempty then Nat.find h else 0

theorem power_one (a : G) [MyGroup G] : a^1 = a:= by
  change power' a 1 = a
  rw [power', power', op_id]
  

theorem fin_order_elem [MyFiniteGroup G] (a: G): ∃ n :ℕ, a^(n+1)  = ε := by
  by_contra h
  push Not at h
  let p := fun (n: ℕ) => a^(n+1)
  have hphp :=Finite.exists_ne_map_eq_of_infinite p
  obtain ⟨x,y,hne, heq⟩ := hphp
  wlog hmp : x < y generalizing x y with H
  · exact H y x hne.symm heq.symm (hne.lt_or_gt.resolve_left hmp)
  · -- Choose one of the two
    simp [p] at heq
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_lt hmp
    rw [hc, Nat.add_assoc, ← pow_distr_nat] at heq
    have h2 := congrArg ((a^x)⁻¹ * ·) heq
    rw [inv_mul (a^x), ←op_assoc, inv_mul, id_op] at h2
    symm at h2
    have hp' := h c
    exact hp' h2

def finOrderElem [MyFiniteGroup G] [DecidableEq G] (a: G): ℕ :=
  Nat.find (fin_order_elem a)
