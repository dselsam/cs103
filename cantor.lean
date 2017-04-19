import data.set data.bool classical
open bool set eq.ops

-- definition powertype [reducible] (T : Type) := T → bool
definition injective [reducible] {T U : Type} (f : T → U) := ∀ (x y : T), f x = f y → x = y
definition surjective [reducible] {T U : Type} (f : T → U) := ∀ (u : U), ∃ (x : T), f x = u

-- Misc lemmas
lemma case_analysis (b : bool) {c : Prop} : (b = tt → c) → (b = ff → c) → c := 
  take tt_c ff_c, or.elim (dichotomy b) ff_c tt_c

lemma bnot_of_false {b : bool} : b = bnot b → false := sorry
lemma not_of_false {P : Prop} : P = ¬ P → false := sorry
-- Cantor's theorem : 

section cantor

variables {T : Type} [T_dec : decidable_eq T]
include T_dec

-- On types
theorem cantor : ¬ ∃ (f : T → (T → bool)), surjective f :=
  assume exists_surjection : ∃ (f : T → (T → bool)), surjective f,
  obtain (f : T → (T → bool)) (f_surjective : surjective f), from exists_surjection,
  let D := λ x, bnot (f x x) in
  obtain (d : T) (fd_eq_D : f d = D), from f_surjective D,
  have fdd_eq_nfdd : f d d = bnot (f d d), from 
    calc f d d = D d : congr fd_eq_D rfl
         ... = bnot (f d d) : rfl,
  show false, from bnot_of_false fdd_eq_nfdd

-- On types with Prop
theorem cantor_prop : ¬ ∃ (f : T → (T → Prop)), surjective f :=
  assume exists_surjection : ∃ (f : T → (T → Prop)), surjective f,
  obtain (f : T → (T → Prop)) (f_surjective : surjective f), from exists_surjection,
  let D := λ x, ¬ f x x in
  obtain (d : T) (fd_eq_D : f d = D), from f_surjective D,
  have fdd_eq_nfdd : f d d = ¬ f d d, from 
    calc f d d = D d : congr fd_eq_D rfl
         ... = ¬ f d d : rfl,
  show false, from not_of_false fdd_eq_nfdd


-- On sets

/- TODO in progress

definition powerset (xs : set T) : set (set T) := λ ys, ys ⊆ xs
variables (S : set T)

lemma dneg {P : Prop} : ¬ ¬ P → P := sorry 

theorem cantor_set : ¬ ∃ (f : map S (powerset S)), surjective f :=
  assume exists_surjection : ∃ (f : map S (powerset S)), surjective f,
  obtain (f : map S (powerset S)) (f_surjective : surjective f), from exists_surjection,
  let D := { x ∈ S | x ∉ f x } in
  obtain (d : T) (fd_eq_D : f d = D), from f_surjective D,
  or.elim (em (d ∈ f d))
          (assume d_in_fd : d ∈ f d, 
           have d_in_D : d ∈ D, from fd_eq_D ▸ d_in_fd,
           -- the ands are unfortunate
           have d_nin_fd  : d ∉ f d, from and.right d_in_D,
           absurd d_in_fd d_nin_fd)
          (assume d_nin_fd : d ∉ f d, 
           have d_nin_D : d ∉ D, from fd_eq_D ▸ d_nin_fd,
           -- obnoxious, but we can make it cleaner
           have d_nnin_fd  : ¬ d ∉ f d, from sorry,
           have d_in_fd : d ∈ f d, from dneg d_nnin_fd,
           absurd d_in_fd d_nin_fd)

            
                 
           
                   



-/
end cantor
