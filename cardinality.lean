import data.nat data.set algebra.binary
open nat set quot binary function

definition injective [reducible] {T U : Type} (f : T → U) := ∀ (x y : T), f x = f y → x = y

private definition equiv (T1 T2 : Type) := ∃ (f : T1 → T2), bijective f
local infix ~ := equiv

private definition equiv.refl (T : Type) : T ~ T := sorry
private definition equiv.symm ⦃T1 T2 : Type⦄ : T1 ~ T2 → T2 ~ T1 := sorry
private definition equiv.trans ⦃T1 T2 T3 : Type⦄ : T1 ~ T2 → T2 ~ T3 → T1 ~ T3 := sorry

definition cardinality.bij_setoid [instance] : setoid Type :=
  setoid.mk equiv (mk_equivalence equiv equiv.refl equiv.symm equiv.trans)

definition cardinality : Type := quot cardinality.bij_setoid

namespace cardinality

definition aleph_zero := ⟦ ℕ ⟧

definition le [reducible] (C1 C2 : cardinality) : Prop := 
quot.lift_on₂ C1 C2 (λ T1 T2, ∃ (f : T1 → T2), injective f) sorry

infix `≤` := le

definition lt [reducible] (C1 C2 : cardinality) : Prop := C1 ≤ C2 ∧ C1 ≠ C2
infix `<` := lt

theorem cantor (T : Type) : ⟦T⟧ < ⟦T → bool⟧ := 
  assume (C : ⟦T⟧),
  quot.rec₂ 
  -- proof that there is an injection from T to T → bool
  -- proof that it doesn't matter which representatives you choose (rep1 → T → (T → bool) → rep2) using the given bijections

end cardinality
