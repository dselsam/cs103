import data.subtype

namespace set

constant set : Type.{1}

constant empty : set
constant pair : set → set → set
constant filter : set → (set → Prop) → set
constant bigunion : set → set
constant powerset : set → set
constant inf : set

definition function := { f : set → set → Prop | ∀ x y z, f x y = f x z → y = z }
constant map : function → set → set

constant mem : set → set → Prop

notation `∅` := empty
infix `∈` := mem
notation a ∉ b := ¬ mem a b

definition subset (s1 s2 : set) := ∀ {u}, u ∈ s1 → u ∈ s2
infix `⊆` := subset

definition singleton (s : set) := bigunion (pair s ∅)

definition intersection (s1 s2 : set) := filter s1 (λ x, x ∈ s2)
notation a ∩ b := intersection a b

definition intersect_in_both : ∀ {s1 s2 : set} {x : set}, x ∈ s1 ∩ s2 → x ∈ s1 ∧ x ∈ s2 := sorry

definition union (s1 s2 : set) := bigunion (pair s1 s2)
notation a ∪ b := union a b

-- Missing axiom
axiom axiom_emptyset : ∀ x, x ∉ ∅

-- 1. Axiom of Extensionality: If X and Y have the same elements, then X=Y.
axiom axiom_extensionality (X Y : set) : (∀ u, u ∈ X ↔ u ∈ Y) → X = Y

-- 2. Axiom of the Unordered Pair: For any a and b there exists a set {a,b} that contains exactly a and b. (also called Axiom of Pairing)
axiom axiom_pair : ∀ a b x, x ∈ pair a b ↔ (x = a ∨ x = b)

-- 3. Axiom of Subsets: If phi is a property (with parameter p), then for any  X and p there exists a set Y={u in X:phi(u,p)} that contains all those u in X that have the property phi. (also called Axiom of Separation or Axiom of Comprehension)
axiom axiom_filter (X : set) : ∀ φ u, (u ∈ filter X φ) ↔ (u ∈ X ∧ φ u)

-- 4. Axiom of the Sum Set: For any X there exists a set Y= union X, the union of all elements of X. (also called Axiom of Union)
axiom axiom_unions (X : set) : ∀ u, u ∈ bigunion X ↔ ∃ z, z ∈ X ∧ u ∈ z

-- 5. Axiom of the Power Set: For any X there exists a set Y=P(X), the set of all subsets of X.
axiom axiom_powerset (X : set) : ∀ u, u ∈ powerset X ↔ u ⊆ X

-- 6. Axiom of Infinity: There exists an infinite set.
axiom axiom_infinity : ∅ ∈ inf ∧ ∀ x, x ∈ inf → pair x (singleton x) ∈ inf

-- 7. Axiom of Replacement: If F is a function, then for any X there exists a set Y=F[X]={F(x):x in X}.
-- (Note: this is a type theory function, not a set function. Would just require coercion and choice to make it set-theoretic)
axiom axiom_replacement (X Y : set) : ∀ F y, y ∈ Y ↔ ∃ x, x ∈ X ∧ F x y

-- 8. Axiom of Foundation: Every nonempty set has an  in -minimal element. (also called Axiom of Regularity)
axiom axiom_foundation : ∀ S, S ≠ ∅ → ∃ x, x ∈ S ∧ x ∩ S = ∅

end set

namespace set_examples

open set

theorem subset_refl : ∀ A, A ⊆ A :=
  -- Proof. Let A be an arbitrary set, and let x be an arbitrary member of A. 
  assume A x `x ∈ A`,
  -- It is a tautology that x ∈ A → x ∈ A, so, by definition, A ⊆ A. 
  show x ∈ A, from `x ∈ A`

theorem subset_trans : ∀ (A B C : set), subset A B → subset B C → subset A C :=
  -- Proof. Let A, B, and C be arbitrary sets such that A ⊆ B and B ⊆ C. 
  assume A B C `A ⊆ B` `B ⊆ C`,
  -- Let x be an arbitrary member of A. 
  assume x `x ∈ A`,
  -- Then x ∈ B because A ⊆ B. 
  have x_in_B : x ∈ B, from `A ⊆ B` `x ∈ A`,
  -- But then x ∈ C since B ⊆ C. 
  have x_in_C : x ∈ C, from `B ⊆ C` `x ∈ B`,
  -- Therefore, x ∈ C for all x ∈ A, so, by definition, A ⊆ C.
  show x ∈ C, from x_in_C

theorem inter_subset : ∀ (A B : set), A ∩ B ⊆ A :=
  -- Proof. Let A and B be arbitrary sets. Let x be an arbitrary member of A ∩ B.
  assume A B x `x ∈ A ∩ B`,
  -- Then, by definition, x ∈ A and x ∈ B, 
  obtain `x ∈ A` `x ∈ B`, from intersect_in_both `x ∈ A ∩ B`,
  -- so, of course, x ∈ A. 
  -- So, we have x ∈ A ∩ B → x ∈ A, so, by definition, A ∩ B ⊆ A.
  show x ∈ A, from `x ∈ A`

theorem inter_sub_powerset : ∀ A B, A ∩ B ⊆ powerset A ∩ powerset B :=
  -- Proof. Let A and B be arbitrary sets. 
  assume A B,
  -- A ∩ B ⊆ A, so A ∩ B ∈ P(A) by the definition of powerset.
  have A ∩ B ∈ powerset A, from sorry, -- iff.elim_left (@axiom_powerset A (inter_subset A B)),
  -- Similarly, A ∩ B ∈ P(B). 
  have A ∩ B ∈ powerset B, from sorry, -- same but with commutativity
  -- Hence A ∩ B ⊆ P(A) ∩ P(B).
  sorry

lemma subset_eq : ∀ {A B}, A ⊆ B → B ⊆ A → A = B := sorry

theorem powerset_inter_splits : ∀ A B, powerset (A ∩ B) = powerset A ∩ powerset B :=
  -- Proof. Let A and B be arbitrary sets. 
  assume A B,
  -- We prove set inclusion in both directions.
  -- First, to see that P(A ∩ B) ⊆ P(A) ∩ P(B), let S be an arbitrary member of P(A ∩ B). 
  have H1 : powerset (A ∩ B) ⊆ powerset A ∩ powerset B, from
    assume S S_in_LHS,
    -- Then S ⊆ A ∩ B, 
    have H1a : S ⊆ A ∩ B, from sorry,
    have H1b : A ∩ B ⊆ A, from sorry,
    have H1c : S ⊆ A, from sorry,
    have H1d : S ∈ powerset A, from sorry,
    sorry,
  sorry
end set_examples

