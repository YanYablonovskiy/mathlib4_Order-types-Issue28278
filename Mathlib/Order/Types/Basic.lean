/-
Copyright (c) 2025 Yan Yablonovskiy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yan Yablonovskiy
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Types.Defs
public import Mathlib.Order.Interval.Set.Basic

/-!

## Main definitions

* `OrderType.card o`: the cardinality of an OrderType `o`.
* `o₁ + o₂`: the lexicographic sum of order types, which forms an `AddMonoid`.
* `o₁ * o₂`: the lexicographic product of order types, which forms a `MonoidWithZero`.

## Notation

The following are notations in the `OrderType` namespace:

* `η` is a notation for the order type of `ℚ` with its natural order.
* `θ` is a notation for the order type of `ℝ` with its natural order.

## References

* <https://en.wikipedia.org/wiki/Order_type>
* Dauben, J. W. Georg Cantor: His Mathematics and Philosophy of the Infinite. Princeton,
  NJ: Princeton University Press, 1990.
* Enderton, Herbert B. Elements of Set Theory. United Kingdom: Academic Press, 1977.

## Tags

order type, order isomorphism, linear order
-/

public noncomputable section

namespace OrderType

universe u v w w'

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type w'}

instance : ZeroLEOneClass OrderType :=
  ⟨OrderType.zero_le _⟩

instance : Add OrderType.{u} where
  add o₁ o₂ := OrderType.liftOn₂ o₁ o₂ (fun r _ s _ ↦ type (r ⊕ₗ s))
    fun _ _ _ _ _ _ _ _ ha hb ↦ OrderIso.sumLexCongr (Classical.choice <| type_eq_type.mp ha)
      (Classical.choice <| type_eq_type.mp hb) |> type_congr

instance : HAdd OrderType.{u} OrderType.{v} OrderType.{max u v} where
  hAdd o₁ o₂ := OrderType.liftOn₂ o₁ o₂ (fun r _ s _ ↦ type (r ⊕ₗ s))
    fun _ _ _ _ _ _ _ _ ha hb ↦ OrderIso.sumLexCongr (Classical.choice <| type_eq_type.mp ha)
      (Classical.choice <| type_eq_type.mp hb) |> type_congr

@[simp]
lemma type_lex_sum (α : Type u) (β : Type v) [LinearOrder α] [LinearOrder β] :
    type (α ⊕ₗ β) = type α + type β :=
     /- Get stuck on

        type (Lex (α ⊕ β)) = (type α).liftOn₂ (type β) (fun r x s x_1 ↦ type (Lex (r ⊕ s)))
        instHAdd._proof_1

        can't use old method due to exposed changes.
     -/
     sorry

instance : AddMonoid OrderType where
  add_assoc o₁ o₂ o₃ :=
    inductionOn₃ o₁ o₂ o₃ fun α _ β _ γ _ ↦ by
      simp only [← type_lex_sum, (OrderIso.sumLexAssoc α β γ).type_congr]
  zero_add o :=
    inductionOn o (fun α _ ↦ by
      simp only [show 0 = type PEmpty by rfl, ← type_lex_sum]
      exact (OrderIso.emptySumLex (β := PEmpty) (α := α)).type_congr)
  add_zero o :=
    inductionOn o (fun α _ ↦ by
      simp only [show 0 = type PEmpty by rfl, ← type_lex_sum]
      exact (OrderIso.sumLexEmpty (β := PEmpty) (α := α)).type_congr)
  nsmul := nsmulRec

instance : Mul OrderType where
  mul o₁ o₂ := OrderType.liftOn₂ o₁ o₂ (fun r _ s _ ↦ type (r ×ₗ s))
    fun _ _ _ _ _ _ _ _ ha hb ↦ Prod.Lex.prodLexCongr (Classical.choice <| type_eq_type.mp ha)
      (Classical.choice <| type_eq_type.mp hb) |> type_congr

instance : HMul OrderType.{u} OrderType.{v} OrderType.{max u v} where
  hMul o₁ o₂ :=  OrderType.liftOn₂ o₁ o₂ (fun r _ s _ ↦ type (r ×ₗ s))
    fun _ _ _ _ _ _ _ _ ha hb ↦ Prod.Lex.prodLexCongr (Classical.choice <| type_eq_type.mp ha)
      (Classical.choice <| type_eq_type.mp hb) |> type_congr

@[simp]
lemma type_lex_prod (α : Type u) (β : Type v) [LinearOrder α] [LinearOrder β] :
    type (α ×ₗ β) = type β * type α := sorry

instance : Monoid OrderType where
  mul_assoc o₁ o₂ o₃ :=
    inductionOn₃ o₁ o₂ o₃ fun α _ β _ γ _ ↦ by
      simp only [← type_lex_prod]
      exact (Prod.Lex.prodLexAssoc γ β α).symm.type_congr
  one_mul o :=
    inductionOn o (fun α _ ↦ by
      simp only [show 1 = type PUnit by rfl, ← type_lex_prod]
      exact (Prod.Lex.prodUnique α PUnit).type_congr)
  mul_one o :=
    inductionOn o (fun α _ ↦ by
      simp only [show 1 = type PUnit by rfl, ← type_lex_prod]
      exact (Prod.Lex.uniqueProd PUnit α).type_congr)

instance (n : Nat) : OfNat OrderType n where
 ofNat := Fin n |> type

instance : LeftDistribClass OrderType where
  left_distrib a b c := by
    refine inductionOn₃ a b c (fun _ _ _ _ _ _ ↦ ?_)
    simp only [← type_lex_prod,← type_lex_sum]
    exact (Prod.Lex.sumLexProdLexDistrib _ _ _).type_congr

/-- The order type of the rational numbers. -/
def eta : OrderType := type ℚ

/-- The order type of the real numbers. -/
def theta : OrderType := type ℝ

@[inherit_doc]
scoped notation "η" => OrderType.eta
recommended_spelling "eta" for "η" in [eta, «termη»]

@[inherit_doc]
scoped notation "θ" => OrderType.theta
recommended_spelling "theta" for "θ" in [theta, «termθ»]

section Cardinal

open Cardinal

/-- The cardinal of an `OrderType` is the cardinality of any type on which a relation
with that order type is defined. -/
@[expose]
def card : OrderType → Cardinal := sorry
  --Quotient.map _ fun _ _ ⟨e⟩ ↦ ⟨e.toEquiv⟩

@[simp]
theorem card_type [LinearOrder α] : card (type α) = #α :=
  sorry

@[gcongr]
theorem card_le_card {o₁ o₂ : OrderType} : o₁ ≤ o₂ → card o₁ ≤ card o₂ :=
  inductionOn o₁ fun _ ↦ inductionOn o₂ fun _ _ f ↦ by
    rw [type_le_type_iff] at f
    have := (Classical.choice f).toEmbedding-- ⟨f.toEmbedding⟩
    sorry

theorem card_mono : Monotone card := by
 rw [Monotone]; exact @card_le_card

@[simp]
theorem card_zero : card 0 = 0 := sorry --mk_eq_zero _

@[simp]
theorem card_one : card 1 = 1 := sorry --mk_eq_one _

end Cardinal

end OrderType
