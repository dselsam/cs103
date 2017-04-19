import data.set
open set

variables {T : Type}
variables {A B C : set T}

definition powerset (xs : set T) : set (set T) := λ ys, ys ⊆ xs

-- (All easy to prove)
lemma set_ext : A ⊆ B → B ⊆ A → A = B := sorry
lemma cap_ss_left (A B : set T) : A ∩ B ⊆ A := sorry
lemma cap_ss_right (A B : set T) : A ∩ B ⊆ B := sorry
lemma ss_trans : A ⊆ B → B ⊆ C → A ⊆ C := sorry
lemma ss_cap : A ⊆ B → A ⊆ C → A ⊆ B ∩ C := sorry


--Theorem. A ∩ B ⊆ P(A) ∩ P(B) for all sets A and B.
theorem inter_ss_P : A ∩ B ∈ powerset A ∩ powerset B :=
  -- Proof. Let A and B be arbitrary sets. 
  -- A ∩ B ⊆ A, so A ∩ B ∈ P(A) by the definition of powerset
  have AcapB_ss_P_A : A ∩ B ∈ powerset A, from cap_ss_left A B,
  -- Similarly, A ∩ B ∈ P(B). 
  have AcapB_ss_P_B : A ∩ B ∈ powerset B, from cap_ss_right A B,
  -- Hence A ∩ B ⊆ P(A) ∩ P(B).
  show A ∩ B ∈ powerset A ∩ powerset B, from and.intro AcapB_ss_P_A AcapB_ss_P_B

theorem powerset_inter : powerset (A ∩ B) = powerset A ∩ powerset B :=
  -- Proof. Let A and B be arbitrary sets. We prove set inclusion in both directions.
  set_ext
  (-- First, to see that P(A ∩ B) ⊆ P(A) ∩ P(B), 
   show powerset (A ∩ B) ⊆ powerset A ∩ powerset B, from
   -- let S be an arbitrary member of P(A ∩ B). 
     assume (S : set T) (S_in_P_AcapB : S ∈ powerset (A ∩ B)),
     -- Then S ⊆ A ∩ B, 
     have S_ss_AcapB : S ⊆ A ∩ B, from S_in_P_AcapB,
     -- but A ∩ B ⊆ A, 
     have AcapB_ss_A : A ∩ B ⊆ A, from cap_ss_left A B,
     -- so S ⊆ A.
     have S_ss_A : S ⊆ A, from ss_trans S_ss_AcapB AcapB_ss_A,
     -- and so, by the definition of powerset, S ∈ P(A). 
     have S_in_P_A : S ∈ powerset A, from S_ss_A,
     -- Similarly, S ∈ P(B), 
     have S_in_P_B : S ∈ powerset B, from ss_trans S_ss_AcapB (cap_ss_right A B),
     -- so S ∈ P(A) ∩ P(B).
     show S ∈ powerset A ∩ powerset B, from and.intro S_in_P_A S_in_P_B
     -- Hence, we have shown that S ∈ P(A ∩ B) → S ∈ P(A) ∩ P(B). 
     -- Since S was chosen arbitrarily, we have P(A ∩ B) ⊆ P(A) ∩ P(B)
  )    
  (-- Now, to see that P(A ∩ B) ⊇ P(A)∩P(B), 
   show powerset A ∩ powerset B ⊆ powerset (A ∩ B), from
   -- let S be an arbitrary member of P(A) ∩ P(B), 
   assume (S : set T) (S_in_PA_cap_PB : S ∈ powerset A ∩ powerset B),
   -- so S ∈ P(A) and S ∈ P(B). Then S ⊆ A and S ⊆ B.
   have S_ss_A : S ⊆ A, from and.left S_in_PA_cap_PB,
   have S_ss_B : S ⊆ B, from and.right S_in_PA_cap_PB,
  -- But then S ⊆ A ∩ B, so S ∈ P(A ∩ B).
   show S ∈ powerset (A ∩ B), from ss_cap S_ss_A S_ss_B)
