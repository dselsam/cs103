-- Keith
-- Chapter 2

import data.set algebra.binary algebra.group classical

open nat

-- I. Proofs about parity

--[KS] An integer x is called even if there is some integer k such that x = 2k.

definition even (x : nat) := ∃ k, x = 2 * k.

--[KS] An integer x is called odd if there is some integer k such that x = 2k + 1.

definition odd (x : nat) := ∃ k, x = 2 * k + 1.

notation x `²` := (x * x)

/- [KS]
Theorem: If x is even, then x^2 is even.
Proof: Let x be any even integer. Since x is even, there is some integer k such that x = 2k. This
means that x^2 = (2k)^2 = 4k = 2(2k)^2. Since (2k)^2 is an integer, this means that there is some integer m
(namely, (2k)^2) such that x^2 = 2m. Thus x^2 is even."
-/

theorem x_even_x2_even : ∀ (x : nat), even x → even (x²) :=
  -- Let x be an even integer
  take (x : nat),
  assume (even_x : even x),
  -- Since x is even, there is some integer k such that x = 2k.
  obtain (k : nat) (x_eq_2k : x = 2 * k), from even_x,
  -- This means that x^2 = (2k)^2 = 4k = 2(2k)^2
  have x2_eq_2m : x² = 2 * (2 * k²), from 
    calc x² = (2 * k)² : x_eq_2k
         ... = 4 * k² : sorry
         ... = 2 * (2 * k²) : sorry,
  -- this means that there is some integer m (namely, (2k)^2) such that x^2 = 2m. 
  have x2_div2 : ∃ m, x² = 2 * m, from exists.intro (2 * k²) x2_eq_2m,
  -- Thus x^2 is even.
  show even (x²), from x2_div2

/- [KS]
Theorem: If m is even and n is odd, then mn is even.
Proof: Let m be any even number and n be any odd number. Then m = 2r for some integer r, and
n = 2s + 1 for some integer s. This means that mn = (2r)(2s + 1) = 2(r(2s + 1)). This means that
mn = 2k for some integer k (namely, r(2s + 1)), so mn is even. 
-/

theorem even_mul_odd_even : ∀ (m n : nat), even m → odd n → even (m * n) :=
  -- Let m be any even number and n be any odd number.
  take (m n : nat),
  assume (even_m : even m) (odd_n : odd n),
  -- Then m = 2r for some integer r,
  obtain (r : nat) (m_eq_2r : m = 2 * r), from even_m,
  -- and n = 2s + 1 for some integer s.
  obtain (s : nat) (n_eq_2s_p1 : n = 2 * s + 1), from odd_n,
  -- This means that mn = (2r)(2s + 1) = 2(r(2s + 1)). 
  have mn_eq_2t : m * n = 2 * (r * (2 * s + 1)), from
  calc m * n = (2 * r) * (2 * s + 1) : sorry
       ... = 2 * (r * (2 * s + 1)) : sorry,
  -- This means that mn = 2k for some integer k (namely, r(2s + 1)), so mn is even. 
  show even (m * n), from exists.intro (r * (2 * s + 1)) mn_eq_2t

-- [KS] Two numbers have the same parity if they are both odd or both even

definition both {T : Type} (h : T → Prop) (x y : T) := h x ∧ h y
definition same_parity (x y : nat) := both even x y ∨ both odd x y
definition same_parity_odd1 {x y : nat} : same_parity x y → odd x → odd y := sorry
definition same_parity_odd2 {x y : nat} : same_parity x y → odd y → odd x := sorry

/- [KS]
Theorem: If m and n have the same parity, then m + n is even.
Proof: Let m and n be any two integers with the same parity. Then there are two cases to consider:
Case 1: m and n are even. Then m = 2r for some integer r and n = 2s for some integer s. Therefore,
m + n = 2r + 2s = 2(r + s). Thus m + n = 2k for some integer k (namely, r + s), so m + n is even.
Case 2: m and n are odd. Then m = 2r + 1 for some integer r and n = 2s + 1 for some integer s.
Therefore, m + n = 2r + 1 + 2s + 1 = 2r + 2s + 2 = 2(r + s + 1). Thus m + n = 2k for some integer k
(namely, r + s + 1), so m + n is even.
-/

theorem same_parity_add_even : ∀ {x y : nat}, same_parity x y → even (x + y) :=
  -- Let m and n be any two integers with the same parity.
  take (x y : nat),
  assume (sp_xy : same_parity x y),
  -- Then there are two cases to consider:
  have two_cases : (even x ∧ even y) ∨ (odd x ∧ odd y), from sp_xy,
  or.elim two_cases

(-- Case 1: m and n are even. 
           take (both_even : even x ∧ even y),
           have even_x : even x, from and.elim_left both_even,
           have even_y : even y, from and.elim_right both_even,
          -- Then m = 2r for some integer r and n = 2s for some integer s. 
           obtain (r : nat) (x_eq_2r : x = 2 * r), from even_x,
           obtain (s : nat) (y_eq_2s : y = 2 * s), from even_y,
          -- Therefore, m + n = 2r + 2s = 2(r + s).
           have xpy_eq_2t : x + y = 2 * (r + s), from
             calc x + y = 2 * r + 2 * s : sorry
                  ... = 2 * (r + s) : sorry,
         -- Thus m + n = 2k for some integer k (namely, r + s), so m + n is even.
           show even (x + y), from exists.intro (r + s) xpy_eq_2t)

          (-- Case 2: m and n are odd.
          take (both_odd : odd x ∧ odd y),
           have odd_x : odd x, from and.elim_left both_odd,
           have odd_y : odd y, from and.elim_right both_odd,
          -- Then m = 2r + 1 for some integer r and n = 2s + 1 for some integer s.
           obtain (r : nat) (x_eq_2r_p1 : x = 2 * r + 1), from odd_x,
           obtain (s : nat) (y_eq_2s_p1 : y = 2 * s + 1), from odd_y,
          -- Therefore, m + n = 2r + 1 + 2s + 1 = 2r + 2s + 2 = 2(r + s + 1).
           have xpy_eq_2t : x + y = 2 * (r + s + 1), from
             calc x + y = 2 * r + 1 + 2 * s + 1 : sorry
                  ... = 2 * r + 2 * s + 2 : sorry
                  ... = 2 * (r + s + 1) : sorry,
          --  Thus m + n = 2k for some integer k (namely, r + s + 1), so m + n is even.
           show even (x + y), from exists.intro (r + s + 1) xpy_eq_2t)

theorem even_or_odd : ∀ (n : nat), even n ∨ odd n := sorry
theorem not_even_and_odd : ∀ {n : nat}, even n → odd n → false := sorry


/- [KS]
Theorem: If n is even and m is an integer, then n + m has the same parity as m.
Proof: Consider any even integer n. Now, consider any integer m and the sum n + m. We consider
two possibilities for m:
Case 1: m is even. Then m and n have the same parity, so by our previous result (if m and n have the
same parity, then m + n is even) we know that m + n is even. Therefore m and m + n have the same
parity.
Case 2: m is odd. Since n is even, n = 2r for some integer r, and since m is odd, m = 2s + 1 for some
integer s. Then n + m = 2r + 2s + 1 = 2(r + s) + 1. This means that n + m = 2k + 1 for some k
(namely, r + s), so n + m is odd. Therefore m and m + n have the same parity.
-/

theorem even_add_sp : ∀ {n : nat}, even n → ∀ (m : nat), same_parity (n + m) m :=
  -- Consider any even integer n. 
  take (n : nat),
  assume (even_n : even n),
  -- Now, consider any integer m [and the sum n + m]. We consider two possibilities for m:
  take (m : nat),
  or.elim (even_or_odd m)
          (-- Case 1: m is even.
           assume (even_m : even m),
           -- Then m and n have the same parity,
           have sp_nm : same_parity n m, from or.inl (and.intro even_n even_m),
           -- so by our previous result (if m and n have the same parity, then m + n is even) we know that m + n is even.
           have even_mpn : even (n + m), from same_parity_add_even sp_nm,
           -- Therefore m and m + n have the same parity.
           show same_parity (n + m) m, from or.inl (and.intro even_mpn even_m))
          (-- Case 2: m is odd.
           assume (odd_m : odd m),
           -- Since n is even, n = 2r for some integer r,
           obtain (r : nat) (n_eq_2r : n = 2 * r), from even_n,
           --  and since m is odd, m = 2s + 1 for some integer s.
           obtain (s : nat) (m_eq_2s_p1 : m = 2 * s + 1), from odd_m,
           -- Then n + m = 2r + 2s + 1 = 2(r + s) + 1.
           have npm_eq_2t_p1 : n + m = 2 * (r + s) + 1, from
             calc n + m = 2 * r + 2 * s + 1 : sorry
                  ... = 2 * (r + s) + 1 : sorry,
           -- This means that n + m = 2k + 1 for some k (namely, r + s), so n + m is odd.
           have odd_npm : odd (n + m), from exists.intro (r + s) npm_eq_2t_p1,
           -- Therefore m and m + n have the same parity.
           show same_parity (n + m) m, from or.inr (and.intro odd_npm odd_m))
           

-- Keith, chapter 2
-- proofs about parity
open set binary

variable {T : Type}

/- [KS]
Theorem: For any sets A and B, A ∩ B ⊆ A.
Proof: Consider any sets A and B. We want to show that A ∩ B ⊆ A. By the definition of subset, this
means that we need to show that for any x ∈ A ∩ B, x ∈ A. So consider any x ∈ A ∩ B. By the definition
of intersection, x ∈ A ∩ B means that x ∈ A and x ∈ B. Therefore, if x ∈ A ∩ B, x ∈ A. Since our
choice of x was arbitrary, A ∩ B ⊆ A.
-/

theorem inter_sub : ∀ (A B : set T), A ∩ B ⊆ A :=
  -- Consider any sets A and B.
  take (A B : set T),
  -- We want to show that A ∩ B ⊆ A.
  show A ∩ B ⊆ A, from
  -- By the definition of subset, this means that we need to show that for any x ∈ A ∩ B, x ∈ A.
  show ∀ x, x ∈ A ∩ B → x ∈ A, from
  -- So consider any x ∈ A ∩ B.
  take (x : T),
  assume (x_in_inter : x ∈ A ∩ B),
  -- By the definition of intersection, x ∈ A ∩ B means that x ∈ A and x ∈ B. 
  have x_in_A : x ∈ A, from and.elim_left x_in_inter,
  have x_in_B : x ∈ B, from and.elim_right x_in_inter,
  -- Therefore, [if x ∈ A ∩ B], x ∈ A. 
  show x ∈ A, from x_in_A
  -- Since our choice of x was arbitrary, A ∩ B ⊆ A.

/- [KS]
Theorem: For any sets A and B, A ⊆ A ∪ B.
Proof: Consider any sets A and B. We want to show that A ⊆ A ∪ B. To do this, we show that for
any x ∈ A, that x ∈ A ∪ B as well. Note that by definition, x ∈ A ∪ B iff x ∈ A or x ∈ B.
Consider any x ∈ A. It is therefore true that x ∈ A or x ∈ B, since we know x ∈ A. Consequently,
x ∈ A ∪ B. Since our choice of x was arbitrary, this shows that any x ∈ A also satisfies x ∈ A ∪ B.
Consequently, A ⊆ A ∪ B, as required. 
-/

theorem union_sup : ∀ (A B : set T), A ⊆ A ∪ B :=
  -- Consider any sets A and B. 
  take (A B : set T),
  -- We want to show that A ⊆ A ∪ B.  
  show A ⊆ A ∪ B, from
  -- To do this, we show that for any x ∈ A, that x ∈ A ∪ B as well. 
  show ∀ x, x ∈ A → x ∈ A ∪ B, from
  -- [Note that by definition, x ∈ A ∪ B iff x ∈ A or x ∈ B.]
  -- Consider any x ∈ A.
  take (x : T),
  assume (x_in_A : x ∈ A),
  -- It is therefore true that x ∈ A or x ∈ B, since we know x ∈ A.
  have x_in_A_or_B : x ∈ A ∨ x ∈ B, from or.inl x_in_A,
  -- Consequently, x ∈ A ∪ B.
  show x ∈ A ∪ B, from x_in_A_or_B
  -- Since our choice of x was arbitrary, this shows that any x ∈ A also satisfies x ∈ A ∪ B. Consequently, A ⊆ A ∪ B, as required. 

definition set_minus [reducible] (A B : set T) := 
  λ x, x ∈ A ∧ ¬ x ∈ B

notation a - b := set_minus a b

-- probably in the 'classical' library

theorem prop_demorgan : ∀ {A B : Prop}, ¬ (A ∧ B) → ¬ A ∨ ¬ B :=
  take (A B : Prop),
  take notAandB : ¬ (A ∧ B),
  or.elim (em A)
          (take a : A,
           or.elim (em B)
                   (take b : B, absurd (and.intro a b) notAandB)
                   (take nb : ¬ B, or.inr nb))
          (take na : ¬ A, or.inl na)

/- [KS] 
Theorem: For any sets A, B, and C, we have C – (A ∩ B) ⊆ (C – A) ∪ (C – B)
Proof: Consider any sets A, B, and C. We will show C – (A ∩ B) ⊆ (C – A) ∪ (C – B). By definition,
this is true if for any x ∈ C – (A ∩ B), we also have x ∈ (C – A) ∪ (C – B). So consider any
x ∈ C – (A ∩ B). By the definition of set difference, this means that x ∈ C and x ∉ A ∩ B. Since
x ∉ A ∩ B, we know that it is not the case that both x ∈ A and x ∈ B. Consequently, it must be true
that either x ∉ A or x ∉ B. We consider these two cases individually:
Case 1: x ∉ A. Since we know that x ∈ C and x ∉ A, we know that x ∈ C – A. By our earlier result, we
therefore have that x ∈ (C – A) ∪ (C – B).
Case 2: x ∉ B. Since we know that x ∈ C and x ∉ B, we know that x ∈ C – B. By our earlier result, we
therefore have that x ∈ (C – A) ∪ (C – B).
In either case we have that x ∈ (C – A) ∪ (C – B). Since our choice of x was arbitrary, we have that
C – (A ∩ B) ⊆ (C – A) ∪ (C – B) as required. 
-/

theorem sm_inter_ss_union_sm : ∀ (A B C : set T), C - (A ∩ B) ⊆ (C - A) ∪ (C - B) :=
  -- Consider any sets A, B, and C. 
  take (A B C : set T),
  -- We will show C – (A ∩ B) ⊆ (C – A) ∪ (C – B). 
  show C - (A ∩ B) ⊆ (C - A) ∪ (C - B), from
  -- By definition, this is true if for any x ∈ C – (A ∩ B), we also have x ∈ (C – A) ∪ (C – B).
  show ∀ x, x ∈ C - (A ∩ B) → x ∈ (C - A) ∪ (C - B), from
  -- So consider any x ∈ C – (A ∩ B). 
  take (x : T),
  assume (x_in_lhs : x ∈ C - (A ∩ B)),
  -- By the definition of set difference, this means that x ∈ C and x ∉ A ∩ B.
  have x_in_C : x ∈ C, from and.elim_left x_in_lhs,
  have x_nin_AcapB : ¬ x ∈ A ∩ B, from and.elim_right x_in_lhs,
  -- Since x ∉ A ∩ B, we know that it is not the case that both x ∈ A and x ∈ B. 
  have x_nin_A_and_B : ¬ (x ∈ A ∩ B), from and.elim_right x_in_lhs,
  -- Consequently, it must be true that either x ∉ A or x ∉ B. 
  have two_cases : ¬ x ∈ A ∨ ¬ x ∈ B, from prop_demorgan x_nin_A_and_B,
  -- We consider these two cases individually:
  or.elim two_cases
          (-- Case 1: x ∉ A.
           assume (x_nin_A : ¬ x ∈ A),
           -- Since we know that x ∈ C and x ∉ A, we know that x ∈ C – A.
           have x_in_CmA : x ∈ C - A, from and.intro x_in_C x_nin_A,
           -- [By our earlier result], we therefore have that x ∈ (C – A) ∪ (C – B).
           show x ∈ (C - A) ∪ (C - B), from or.inl x_in_CmA)
          (-- Case 2: x ∉ B.
           assume (x_nin_B : ¬ x ∈ B),
           -- Since we know that x ∈ C and x ∉ B, we know that x ∈ C – B.
           have x_in_CmB : x ∈ C - B, from and.intro x_in_C x_nin_B,
           -- [By our earlier result], we therefore have that x ∈ (C – A) ∪ (C – B). [DHS: not without commutativity you don't]
           show x ∈ (C - A) ∪ (C - B), from or.inr (and.intro x_in_C x_nin_B))
  --In either case we have that x ∈ (C – A) ∪ (C – B). Since our choice of x was arbitrary, we have that C – (A ∩ B) ⊆ (C – A) ∪ (C – B) as required. 
           
/- [KS]
Lemma: For any sets A and B, A = B if and only if A ⊆ B and B ⊆ A.
Proof: We prove both directions of implication.
( ⇒ ) First, we show that, for any sets A and B, if A = B, then A ⊆ B and B ⊆ A. If A = B, consider
any x ∈ A. Since A = B, this means that x ∈ B. Since our choice of x was arbitrary, any x ∈ A satisfies
x ∈ B, so A ⊆ B. Similarly, consider any x ∈ B, then since A = B, x ∈ A as well. Since our choice of x
was arbitrary, any x ∈ B satisfies x ∈ A, so B ⊆ A.
( ⇐) Next, we prove that if A ⊆ B and B ⊆ A, then A = B. Consider any two sets A and B where
A ⊆ B and B ⊆ A. We need to prove that A = B. Since A ⊆ B, for any x ∈ A, x ∈ B as well. Since
B ⊆ A, for any x ∈ B, x ∈ A as well. Thus every element of A is in B and vice-versa, so the two sets
have the same elements. 
-/
  
lemma eqv_ss : ∀ {A B : set T}, A ∼ B ↔ A ⊆ B ∧ B ⊆ A :=
  -- We prove both directions of implication.
  take (A B : set T),
  iff.intro
    (-- ( ⇒ ) First, we show that, for any sets A and B, if A = B, then A ⊆ B and B ⊆ A.
     show A ∼ B → A ⊆ B ∧ B ⊆ A, from
    -- If A = B, 
     take A_eqv_B : A ∼ B,
    -- [DHS] states the goal later
     have A_ss_B : A ⊆ B, from
    -- consider any x ∈ A. 
     assume (x : T) (x_in_A : x ∈ A),
    -- Since A = B, this means that x ∈ B. 
     have x_in_B : x ∈ B, from iff.elim_left (A_eqv_B x) x_in_A,
    -- [Since our choice of x was arbitrary, any x ∈ A satisfies x ∈ B, so A ⊆ B.]
     show x ∈ B, from x_in_B,

    -- [DHS] states the goal later,
    have B_ss_A : B ⊆ A, from
    -- Similarly, consider any x ∈ B, 
     assume (x : T) (x_in_B : x ∈ B),
    -- then since A = B, x ∈ A as well. 
     have x_in_A : x ∈ A, from iff.elim_right (A_eqv_B x) x_in_B,
    -- [Since our choice of x was arbitrary, any x ∈ B satisfies x ∈ A, so B ⊆ A.]
     show x ∈ A, from x_in_A,

    and.intro A_ss_B B_ss_A)

  (-- ( ⇐) Next, we prove that if A ⊆ B and B ⊆ A, then A = B. 
    show A ⊆ B ∧ B ⊆ A → A ∼ B, from
    -- Consider any two sets A and B where A ⊆ B and B ⊆ A. 
    take H : A ⊆ B ∧ B ⊆ A,
    have A_ss_B : A ⊆ B, from and.elim_left H,
    have B_ss_A : B ⊆ A, from and.elim_right H,
    -- We need to prove that A = B. 
    show A ∼ B, from
    take x,   
    -- [DHS] states strategy afterwards
    iff.intro (-- Since A ⊆ B, for any x ∈ A, x ∈ B as well. 
                assume x_in_A : x ∈ A,
               show x ∈ B, from A_ss_B x x_in_A)
              (-- Since B ⊆ A, for any x ∈ B, x ∈ A as well. 
               assume x_in_B : x ∈ B,
               show x ∈ A, from B_ss_A x x_in_B)
    -- Thus every element of A is in B and vice-versa, so the two sets have the same elements.
    )   

definition sym_diff [reducible] (A B : set T) : set T := λ x, (x ∈ A ∧ ¬ x ∈ B) ∨ (x ∈ B ∧ ¬ x ∈ A)

infix `Δ`:101 := sym_diff

-- (taken implicitly as a lemma in Keith's notes)
lemma sym_diff_nocases : ∀ {A B : set T} (x : T), (x ∈ A ∨ x ∈ B) → (¬ x ∈ A ∨ ¬ x ∈ B) → x ∈ A Δ B :=
  take (A B : set T),
  take x : T,
  assume x_in_A_or_B : x ∈ A ∨ x ∈ B,
  assume x_nin_A_or_B : ¬ x ∈ A ∨ ¬ x ∈ B,
  or.elim x_in_A_or_B
          (take x_in_A : x ∈ A,
           or.elim x_nin_A_or_B
                   (take x_nin_A : ¬ x ∈ A, absurd x_in_A x_nin_A)
                   (take x_nin_B : ¬ x ∈ B, or.inl (and.intro x_in_A x_nin_B)))
          (take x_in_B : x ∈ B,
           or.elim x_nin_A_or_B
                   (take x_nin_A : ¬ x ∈ A, or.inr (and.intro x_in_B x_nin_A))
                   (take x_nin_B : ¬ x ∈ B, absurd x_in_B x_nin_B))

/- [KS]
Lemma 1: (A ∪ B) – (A ∩ B) ⊆ A Δ B.
Proof of Lemma 1: We will show that for any x ∈ (A ∪ B) – (A ∩ B), x ∈ A Δ B. So consider any
x ∈ (A ∪ B) – (A ∩ B). This means that x ∈ A ∪ B, but x ∉ A ∩ B. Since x ∈ A ∪ B, we know that
x ∈ A or x ∈ B. Since x ∉ A ∩ B, we know that x is not contained in both A and B. We thus have that
x is in at least one of A and B, but not both. Consequently, x ∈ A Δ B. Since our choice of x was arbitrary,
we therefore have that (A ∪ B) – (A ∩ B) ⊆ A Δ B.
-/

-- [DHS]#DESIGN Keith uses an unstated and unproved lemma, arguably

lemma sym_diff_alt_1 : ∀ {A B : set T}, (A ∪ B) - (A ∩ B) ⊆ A Δ B :=
  take (A B : set T),
  -- We will show that for any x ∈ (A ∪ B) – (A ∩ B), x ∈ A Δ B.
  show ∀ x, x ∈ (A ∪ B) - (A ∩ B) → x ∈ A Δ B, from
  -- So consider any x ∈ (A ∪ B) – (A ∩ B). 
  take (x : T),
  assume (x_in_lhs : x ∈ (A ∪ B) - (A ∩ B)),
  -- This means that x ∈ A ∪ B, 
  have x_in_A_cup_B : x ∈ A ∪ B, from and.elim_left x_in_lhs,
  -- but x ∉ A ∩ B.
  have x_nin_A_cap_B : ¬ x ∈ A ∩ B, from and.elim_right x_in_lhs,
  -- Since x ∈ A ∪ B, we know that x ∈ A or x ∈ B.
  have x_in_A_or_B : x ∈ A ∨ x ∈ B, from x_in_A_cup_B,
  -- Since x ∉ A ∩ B, we know that x is not contained in both A and B. We thus have that x is in at least one of A and B, but not both.
  have x_nin_A_or_x_nin_B : ¬ x ∈ A ∨ ¬ x ∈ B, from prop_demorgan x_nin_A_cap_B,
  -- Consequently, x ∈ A Δ B.
  show x ∈ A Δ B, from sym_diff_nocases x x_in_A_or_B x_nin_A_or_x_nin_B
  -- Since our choice of x was arbitrary, we therefore have that (A ∪ B) – (A ∩ B) ⊆ A Δ B.

/- [KS]
Lemma 2: A Δ B ⊆ (A ∪ B) – (A ∩ B)
Proof of Lemma 2: We will show that for any x ∈ A Δ B, x ∈ (A ∪ B) – (A ∩ B). Consider any
x ∈ A Δ B. Then either x ∈ A and x ∉ B, or x ∈ B and x ∉ A. We consider these cases separately:
Case 1: x ∈ A and x ∉ B. Since x ∈ A, x ∈ A ∪ B. Since x ∉ B, x ∉ A ∩ B. Consequently,
x ∈ (A ∪ B) – (A ∩ B).
Case 2: x ∈ B and x ∉ A. Since x ∈ B, x ∈ A ∪ B. Since x ∉ A, x ∉ A ∩ B. Consequently,
x ∈ (A ∪ B) – (A ∩ B).
In either case, x ∈ (A ∪ B) – (A ∩ B). Since our choice of x was arbitrary, we have that
A Δ B ⊆ (A ∪ B) – (A ∩ B).
-/

lemma sym_diff_alt_2 : ∀ {A B : set T}, A Δ B ⊆ (A ∪ B) - (A ∩ B) :=
  take (A B : set T),
  -- We will show that for any x ∈ A Δ B, x ∈ (A ∪ B) – (A ∩ B).
  show ∀ x, x ∈ A Δ B → x ∈ (A ∪ B) - (A ∩ B), from
  -- Consider any x ∈ A Δ B. 
  take (x : T),
  assume (x_in_sdAB : x ∈ A Δ B),
  -- Then either x ∈ A and x ∉ B, or x ∈ B and x ∉ A. We consider these cases separately:
  or.elim x_in_sdAB
          (-- Case 1: x ∈ A and x ∉ B.
           assume H : x ∈ A ∧ ¬ x ∈ B, 
           have x_in_A : x ∈ A, from and.elim_left H,
           have x_nin_B : ¬ x ∈ B, from and.elim_right H,
           -- Since x ∈ A, x ∈ A ∪ B.
           have x_in_AcupB : x ∈ A ∪ B, from or.inl x_in_A,
           -- Since x ∉ B, x ∉ A ∩ B.
           have x_nin_AcapB : ¬ x ∈ A ∩ B, from take x_in_AcapB, absurd (and.elim_right x_in_AcapB) x_nin_B,
           -- Consequently, x ∈ (A ∪ B) – (A ∩ B).
           show x ∈ (A ∪ B) - (A ∩ B), from and.intro x_in_AcupB x_nin_AcapB)
          (-- Case 2: x ∈ B and x ∉ A.  
           assume H : x ∈ B ∧ ¬ x ∈ A, 
           have x_in_B : x ∈ B, from and.elim_left H,
           have x_nin_A : ¬ x ∈ A, from and.elim_right H,
           -- Since x ∈ B, x ∈ A ∪ B.
           have x_in_AcupB : x ∈ A ∪ B, from or.inr x_in_B,
           -- Since x ∉ A, x ∉ A ∩ B. 
           have x_nin_AcapB : ¬ x ∈ A ∩ B, from take x_in_AcapB, absurd (and.elim_left x_in_AcapB) x_nin_A,
           -- Consequently, x ∈ (A ∪ B) – (A ∩ B).
           show x ∈ (A ∪ B) - (A ∩ B), from and.intro x_in_AcupB x_nin_AcapB)
-- In either case, x ∈ (A ∪ B) – (A ∩ B). Since our choice of x was arbitrary, we have that A Δ B ⊆ (A ∪ B) – (A ∩ B).

/-
Proof of Lemma 2: We will show that for any x ∈ A Δ B, x ∈ (A ∪ B) – (A ∩ B). Consider any
x ∈ A Δ B. Then either x ∈ A and x ∉ B, or x ∈ B and x ∉ A. Assume without loss of generality that
x ∈ A and x ∉ B. Since x ∈ A, x ∈ A ∪ B. Since x ∉ B, x ∉ A ∩ B, so x ∈ (A ∪ B) – (A ∩ B). Since our
choice of x was arbitrary, we have that A Δ B ⊆ (A ∪ B) – (A ∩ B).
-/

-- [DHS]#DESIGN w.l.o.g. actually quite subtle, since it depends on 2(!) commutativity lemmas

theorem union_com : commutative (@union T) := sorry
theorem inter_com : commutative (@inter T) := sorry

-- Here is the abstract lemma, that Keith does not show explicitly

lemma sym_diff_alt_2a : ∀ {A B : set T} {x : T}, x ∈ A - B → x ∈ (A ∪ B) - (A ∩ B) :=
  take (A B : set T) (x : T),
  -- Assume [without loss of generality] that x ∈ A and x ∉ B.
  assume (x_in_AmB : x ∈ A - B),
  have x_in_A : x ∈ A, from and.elim_left x_in_AmB,
  have x_nin_B : ¬ x ∈ B, from and.elim_right x_in_AmB,
  -- Since x ∈ A, x ∈ A ∪ B.
  have x_in_AcupB : x ∈ A ∪ B, from or.inl x_in_A,
  -- Since x ∉ B, x ∉ A ∩ B, 
  have x_nin_AcapB : ¬ x ∈ A ∩ B, from take x_in_AcapB, absurd (and.elim_right x_in_AcapB) x_nin_B,
  -- so x ∈ (A ∪ B) – (A ∩ B)
  show x ∈ (A ∪ B) - (A ∩ B), from and.intro x_in_AcupB x_nin_AcapB

open eq.ops

definition wlog (xy : A ∨ B) (b1 : A → C) : C := or.elim xy b1 b1

lemma sym_diff_alt_2b : ∀ {A B : set T}, A Δ B ⊆ (A ∪ B) - (A ∩ B) :=
  take (A B : set T),
  -- We will show that for any x ∈ A Δ B, x ∈ (A ∪ B) – (A ∩ B).
  show ∀ x, x ∈ A Δ B → x ∈ (A ∪ B) - (A ∩ B), from
  -- Consider any x ∈ A Δ B. 
  take x,
  assume (x_in_sdAB : x ∈ A Δ B), 
  -- Then either x ∈ A and x ∉ B, or x ∈ B and x ∉ A. 
  wlog x_in_sdAB (assume x_in_AmB : x ∈ A - B, sym_diff_alt_2a x_in_AmB)

/-  or.elim x_in_sdAB
          (assume x_in_AmB : x ∈ A - B, sym_diff_alt_2a x_in_AmB)
          (assume x_in_BmA : x ∈ B - A,
           (inter_com B A) ▸ (union_com B A) ▸ sym_diff_alt_2a x_in_BmA)
-/
/- [KS]
Theorem: For any sets A and B, (A ∪ B) – (A ∩ B) = A Δ B.
Proof of Theorem: By Lemma 1, (A ∪ B) – (A ∩ B) ⊆ A Δ B. By Lemma 2,
A Δ B ⊆ (A ∪ B) – (A ∩ B). Since each set is a subset of the other, by our earlier lemma we have that
(A ∪ B) – (A ∩ B) = A Δ B
-/
theorem sym_diff_alt : ∀ (A B : set T), (A ∪ B) - (A ∩ B) ∼ A Δ B :=
  take (A B : set T),
  -- By Lemma 1, (A ∪ B) – (A ∩ B) ⊆ A Δ B. 
  have l_to_r : (A ∪ B) - (A ∩ B) ⊆ A Δ B, from sym_diff_alt_1,
  -- By Lemma 2, A Δ B ⊆ (A ∪ B) – (A ∩ B).
  have r_to_l : A Δ B ⊆ (A ∪ B) - (A ∩ B), from sym_diff_alt_2,
  -- Since each set is a subset of the other, by our earlier lemma we have that (A ∪ B) – (A ∩ B) = A Δ B
  show (A ∪ B) - (A ∩ B) ∼ A Δ B, from iff.elim_right eqv_ss (and.intro sym_diff_alt_1 sym_diff_alt_2)

-- [DHS]
-- #DESGN
-- Issue #1: naming hypotheses
-- Issue #2: 'obvious' lemmas
-- Issue #3: w.l.o.g.

/- [KS]
Theorem: If m and n have opposite parity, m + n is odd.
Proof: Without loss of generality, assume that m is odd and n is even. Since m is odd, there exists an
integer r such that m = 2r + 1. Since n is even, there exists an integer s such that n = 2s. Then
m + n = 2r + 1 + 2s = 2(r + s) + 1. Consequently, m + n is odd. 
-/


definition opposite_parity (x y : nat) := (odd x ∧ even y) ∨ (odd y ∧ even x)

lemma add_comm : ∀ (x y : nat), x + y = y + x := sorry

set_option formatter.hide_full_terms false

/- [DHS]#DESIGN how is [suffices_to_show]? I think it is pretty reasonable. -/

definition suffices_to_show {Goal : Prop} (P : Prop) (H : P → Goal) (p : P) : Goal := H p

lemma opposite_parity_sum_odd : ∀ (m n : nat), opposite_parity m n → odd (m + n) :=

  -- Without loss of generality, assume that m is odd and n is even.
  suffices_to_show (∀ (m n : nat), odd m ∧ even n → odd (m + n))

    (assume (lem : ∀ (m n : nat), odd m ∧ even n → odd (m + n)) 
            (m n : nat) (opp_mn : opposite_parity m n),
      or.elim opp_mn (assume H : odd m ∧ even n, lem m n H) (assume H : odd n ∧ even m, (add_comm n m) ▸ (lem n m H)))

    (take (m n : nat),
    assume H : odd m ∧ even n,
  -- Since m is odd, there exists an integer r such that m = 2r + 1. 
    obtain r (m_eq_2r_p1 : m = 2 * r + 1), from and.elim_left H,
  -- Since n is even, there exists an integer s such that n = 2s. 
    obtain s (n_eq_2s : n = 2 * s), from and.elim_right H,
  -- Then m + n = 2r + 1 + 2s = 2(r + s) + 1. 
    have mpn_eq_2t_p1 : m + n = 2 * (r + s) + 1, from
      calc m + n = 2 * r + 1 + 2 * s : by rewrite [m_eq_2r_p1, n_eq_2s]
           ...= 2 * (r + s) + 1 : sorry,
  -- Consequently, m + n is odd. 
    show odd (m + n), from exists.intro (r + s) mpn_eq_2t_p1)

-- Proofs with vacuous truths
/- [KS]
Theorem: For any sets A and B, if A ⊆ B, then A – B = Ø.

Lemma 1: For any sets A and B, if A ⊆ B, then Ø ⊆ A – B.
Lemma 2: For any sets A and B, if A ⊆ B, then A – B ⊆ Ø.

Proof of Lemma 1: We need to show that every element x ∈ Ø also satisfies x ∈ A – B. But this is
vacuously true, as there are no x satisfying x ∈ Ø. 

Proof of Lemma 2: We need to show that any x ∈ A – B also satisfies x ∈ Ø. Consider any x ∈ A – B.
This means that x ∈ A and x ∉ B. Since A ⊆ B and since x ∈ A, we know that x ∈ B. But this means
simultaneously that x ∈ B and x ∉ B. Consequently, there are no x ∈ A – B, so the claim that any
x ∈ A – B also satisfies x ∈ Ø is vacuously true.

Proof of Theorem: Consider any sets A and B such that A ⊆ B. By Lemma 1, we have that
Ø ⊆ A – B. By Lemma 2, we have that A – B ⊆ Ø. Thus by our earlier lemma, A – B = Ø as required.
-/

lemma vacuous_set1a : ∀ {A B : set T}, A ⊆ B → ∅ ⊆ A - B :=
  take (A B : set T) (A_ss_B : A ⊆ B),
  -- We need to show that every element x ∈ Ø also satisfies x ∈ A – B.
  show ∀ x, x ∈ ∅ → x ∈ A - B, from
  -- But this is vacuously true, as there are no x satisfying x ∈ Ø. 
  assume x x_in_empty,
  false.rec _ x_in_empty

lemma vacuous_set1b : ∀ {A B : set T}, A ⊆ B → A - B ⊆ ∅ :=
  take (A B : set T) (A_ss_B : A ⊆ B),
  -- We need to show that any x ∈ A – B also satisfies x ∈ Ø.
  show ∀ x, x ∈ A - B → x ∈ ∅, from
  -- Consider any x ∈ A – B. 
  take x (x_in_AmB : x ∈ A - B), 
  -- This means that x ∈ A and x ∉ B. 
  have x_in_A : x ∈ A, from and.elim_left x_in_AmB,
  have x_nin_B : ¬ x ∈ B, from and.elim_right x_in_AmB,
  -- Since A ⊆ B and since x ∈ A, we know that x ∈ B. 
  have x_in_B : x ∈ B, from A_ss_B x x_in_A,
  -- But this means simultaneously that x ∈ B and x ∉ B. 
  -- Consequently, there are no x ∈ A – B, so the claim that any x ∈ A – B also satisfies x ∈ Ø is vacuously true.
  absurd x_in_B x_nin_B

theorem vacuous_set1 : ∀ {A B : set T}, A ⊆ B → A - B ∼ ∅ :=
  -- Consider any sets A and B such that A ⊆ B. 
  take (A B : set T) (A_ss_B : A ⊆ B),
  -- By Lemma 1, we have that Ø ⊆ A – B. 
  have empty_ss_lhs : ∅ ⊆ A - B, from vacuous_set1a A_ss_B,
  -- By Lemma 2, we have that A – B ⊆ Ø. 
  have lhs_ss_empty : A - B ⊆ ∅, from vacuous_set1b A_ss_B,
  -- Thus by our earlier lemma, A – B = Ø as required.
  show A - B ∼ ∅, from iff.elim_right eqv_ss (and.intro lhs_ss_empty empty_ss_lhs)

-- 2.3 Indirect Proofs

/- [KS]
Theorem: If n² is even, then n is even.
Proof: By contradiction; assume that n² is even but that n is odd. Since n is odd, n = 2k + 1 for some integer k. 
Therefore n² = (2k + 1)² = 4k² + 4k + 1 = 2(2k² + 2k) + 1. This means that n² is odd, contradicting
the fact that we know that n² is even. We have reached a contradiction, so our assumption must have been wrong. Therefore, if n² is even, n must be even. 
-/


theorem n2_even_n_even : ∀ (n:nat), even (n²) → even n :=
  -- By contradiction; assume that n² is even but that n is odd.
  assume n (even_n2 : even (n²)), 
  by_contradiction
  (take neven_n : ¬ even n,
   have odd_n : odd n, from or.elim (even_or_odd n) (take even_n, absurd even_n neven_n) (take odd_n, odd_n),
   -- Since n is odd, n = 2k + 1 for some integer k. 
   obtain k (n_eq_2k_p1 : n = 2 * k + 1), from odd_n,
   -- Therefore n² = (2k + 1)² = 4k² + 4k + 1 = 2(2k² + 2k) + 1.
   have n2_eq_2l_p1 : n² = 2 * (2 * k² + 2 * k) + 1, from
   calc n² = (2 * k + 1)² : n_eq_2k_p1
        ... = 4*k² + 4*k + 1 : sorry
        ... = 2 * (2 * k² + 2 * k) + 1 : sorry,
   -- This means that n² is odd, contradicting the fact that we know that n² is even. 
   have odd_n2 : odd (n²), from exists.intro _ n2_eq_2l_p1,
   not_even_and_odd even_n2 odd_n2)
  -- We have reached a contradiction, so our assumption must have been wrong. Therefore, if n² is even, n must be even. 




/- [KS]
You have 2,718 balls and five bins. Prove that you cannot distribute all of
the balls into the bins such that each bin contains an odd number of balls.

Proof: By contradiction; assume that there is a way to distribute all 2,718 balls into five bins such that
each bin has an odd number of balls in it. Consider any such way of distributing the balls, and let the
number of balls in the five bins be a, b, c, d, and e. Write the sum a + b + c + d + e as
((a + b) + (c + d)) + e. Since all five numbers have the same parity, both (a + b) and (c + d) are
even. Since (a + b) and (c + d) have the same parity, ((a + b) + (c + d)) must be even. Then, since
((a + b) + (c + d)) is even, the sum ((a + b) + (c + d)) + e must have the same parity as e. Since e is
odd, this means that sum of the number of balls in the five bins is odd, contradicting the fact that
there are an even number of balls distributed across the bins (2,718). We have reached a contradiction,
so our initial assumption must have been wrong and there is no way to distribute 2,718 balls into
five bins such that each bin has an odd number of balls. 
-/

/- [DHS]#DESIGN interesting challenge, since we really start with 5 of something, and only later provide variables for each individual -/

open list

definition list.sum (f : T → nat) (l : list T) : nat := list.foldr (λ x acc, f x + acc ) 0 l

lemma balls_in_bins_verbose : ∀ (a b c d e : nat), odd a → odd b → odd c → odd d → odd e → ¬ (a + b + c + d + e = 2718) :=
  -- By contradiction; assume that there is a way to distribute all 2,718 balls into five bins such that
  -- each bin has an odd number of balls in it.
  -- Consider any such way of distributing the balls, and let the number of balls in the five bins be a, b, c, d, and e.
  take a b c d e,
  assume odd_a odd_b odd_c odd_d odd_e,
  assume sum_2718 : a + b + c + d + e = 2718,
  have div2_2718 : 2718 = 2 * 1359, from rfl,
  have even_sum : even 2718, from exists.intro _ div2_2718,
  -- Write the sum a + b + c + d + e as ((a + b) + (c + d)) + e.
  have sum_parens : a + b + c + d + e = ((a + b) + (c + d)) + e, from sorry,
  -- Since all five numbers have the same parity, both (a + b) and (c + d) are even. 
  have even_ab : even (a + b), from same_parity_add_even (or.inr (and.intro odd_a odd_b)),
  have even_cd : even (c + d), from same_parity_add_even (or.inr (and.intro odd_c odd_d)),
  -- Since (a + b) and (c + d) have the same parity, ((a + b) + (c + d)) must be even. 
  have even_abcd : even ((a+b)+(c+d)), from same_parity_add_even (or.inl (and.intro even_ab even_cd)),
  -- Then, since ((a + b) + (c + d)) is even, the sum ((a + b) + (c + d)) + e must have the same parity as e.
  have sp_e : same_parity (((a + b) + (c + d)) + e) e, from even_add_sp even_abcd e,
  -- Since e is odd, this means that sum of the number of balls in the five bins is odd, 
  have odd_sum : odd (((a + b) + (c + d)) + e), from same_parity_odd2 sp_e odd_e,
  -- contradicting the fact that there are an even number of balls distributed across the bins (2,718). 
  not_even_and_odd even_sum (sum_2718 ▸ sum_parens⁻¹ ▸ odd_sum)
  -- We have reached a contradiction, so our initial assumption must have been wrong and there is no way to distribute 2,718 balls into five bins such that each bin has an odd number of balls. 

-- Proof by contrapositive
  
        
/- [KS]
Theorem: If not Q → not P, then P → Q.
Proof: By contradiction; assume that not Q → not P, but that P → Q is false. Since P → Q is false,
we know that P is true but Q is false. Since Q is false and not Q → not P, we have that P must be
false. But this contradicts the fact that we know that P is true. We have reached a contradiction, so
our initial assumption must have been false. Thus if not Q → not P, then P → Q. 
-/


definition neg_imp : ∀ {P Q : Prop}, ¬ (P → Q) → (P ∧ ¬ Q) :=
  take P Q,
  assume n_P_to_Q,
  or.elim (em Q)
          (take q : Q, absurd (λ p:P, q) n_P_to_Q)
          (take nq : ¬ Q, 
             (or.elim (em P)
             (take p : P, and.intro p nq)
             (take np : ¬ P, absurd (λ p, absurd p np) n_P_to_Q)))

theorem by_contrapositive : ∀ {P Q : Prop}, (¬ Q → ¬ P) → (P → Q) :=
  take P Q,
  -- By contradiction; assume that not Q → not P, but that P → Q is false. 
  assume nQ_to_nP : ¬ Q → ¬ P,
  by_contradiction
    (assume n_P_to_Q : ¬ (P → Q),
     -- Since P → Q is false, we know that P is true but Q is false. 
     have p : P, from and.elim_left (neg_imp n_P_to_Q),
     have nq : ¬ Q, from and.elim_right (neg_imp n_P_to_Q),
     -- Since Q is false and not Q → not P, we have that P must be false. 
     have np : ¬ P, from nQ_to_nP nq,
     -- But this contradicts the fact that we know that P is true. 
     absurd p np)
    -- We have reached a contradiction, so our initial assumption must have been false. Thus if not Q → not P, then P → Q. 

/- [KS]
Theorem: If n² is even, then n is even. 
Proof: By contrapositive; we prove that if n is odd, then n² is odd. Let n be any odd integer. Since n is odd, n = 2k + 1 for some integer k. 
Therefore, n² = (2k + 1)² = 4k² + 4k + 1 = 2(2k² + 2k) + 1. Thus n² is odd.
-/

lemma not_even_then_odd : ∀ {n : nat}, ¬ even n → odd n :=
  take n not_even_n, or.elim (even_or_odd n) (take even_n, absurd even_n not_even_n) (take odd_n, odd_n)

lemma not_odd_then_even : ∀ {n : nat}, ¬ odd n → even n :=
  take n not_odd_n, or.elim (even_or_odd n) (take even_n, even_n) (take odd_n, absurd odd_n not_odd_n)

lemma double_negation : ∀ {P : Prop}, ¬ ¬ P = P := sorry

lemma even_then_not_odd : ∀ {n : nat}, even n → ¬ odd n := sorry
lemma odd_then_not_even : ∀ {n : nat}, odd n → ¬ (even n) := sorry

theorem n2_even_n_even_by_contrapositive : ∀ (n:nat), even (n²) → even n :=
  take n,
  by_contrapositive
    (assume not_even_n : ¬ (even n),
     show ¬ even (n²), from
     have odd_n : odd n, from not_even_then_odd not_even_n,
     obtain k n_eq_2k_p1, from odd_n,
     have n2_eq_2l_p1 : n² = 2 * (2 * k² + 2 * k) + 1, from
       calc n² = (2 * k + 1)² : n_eq_2k_p1
            ... = 4 * k² + 4 * k + 1 : sorry
            ... = 2 * (2 * k² + 2 * k) + 1 : sorry,
     odd_then_not_even (exists.intro _ n2_eq_2l_p1))



     
-- Chapter 3. Induction

/- [KS]
Theorem: The sum of the first n positive natural numbers is n(n + 1) / 2.
Proof: By induction. Let P(n) be “the sum of the first n positive natural numbers is
n(n + 1) / 2.” We prove that P(n) is true for all n ∈ ℕ, from which the result immediately follows.
For our base case, we prove P(0), that the sum of the first 0 positive natural numbers is
0(0 + 1) / 2. The sum of zero numbers is 0, and 0 = 0(0 + 1)/2. Consequently, P(0) holds.
For the inductive step, assume that for some n ∈ ℕ that P(n) is true and the sum of the first n positive
natural numbers is n(n + 1) / 2. We will prove that P(n + 1) is true; that is, the sum of the first n + 1
positive natural numbers is (n + 1)(n + 2) / 2. Consider the sum of the first n + 1 positive natural
numbers. This is the sum of the first n positive natural numbers, plus n + 1. By our inductive hypothesis,
the sum of the first n positive natural numbers is n(n + 1) / 2. Thus the sum of the first
n + 1 positive natural numbers is
n(n+ 1)/2 + n+ 1
= n(n+ 1)/2 + 2(n+ 1)/2
= (n(n+ 1)+ 2 (n+ 1))/2
= (n+2)(n+ 1)/2
Thus P(n + 1) is true, completing the induction.
-/

definition sum_of_pos : nat → (nat → nat) → nat 
| zero f := 0
| (succ n) f := f (n+1) + sum_of_pos n f

theorem sum_of_pos_closed_form : ∀ (n : nat), 2 * sum_of_pos n (λn,n) = n * (n + 1) :=
  take n,
  -- By induction. Let P(n) be “the sum of the first n positive natural numbers is
  -- n(n + 1) / 2.” We prove that P(n) is true for all n ∈ ℕ, from which the result immediately follows.
  nat.induction_on n
                   (-- For our base case, we prove P(0), that the sum of the first 0 positive natural numbers is 0(0 + 1) / 2.
                    -- The sum of zero numbers is 0, and 0 = 0(0 + 1)/2. Consequently, P(0) holds.
                    show 2 * sum_of_pos 0 (λn,n) = 0 * (0 + 1), from sorry)
                  (-- For the inductive step, assume that for some n ∈ ℕ that P(n) is true and the sum of the first n positive natural numbers is n(n + 1) / 2. 
                   take n, 
                   assume IHn : 2 * sum_of_pos n (λn,n) = n * (n + 1),
                   -- We will prove that P(n + 1) is true; that is, the sum of the first n + 1 positive natural numbers is (n + 1)(n + 2) / 2.
                   show 2 * sum_of_pos (n + 1) (λn,n) = (n + 1) * (n + 2), from
                     -- Consider the sum of the first n + 1 positive natural numbers. This is the sum of the first n positive natural numbers, plus n + 1.
                     calc 2 * sum_of_pos (n + 1) (λn,n) = 2 * (n+1 + sum_of_pos n (λn,n)) : rfl
                          ... = 2 * (n+1) + 2 * sum_of_pos n (λn,n) : sorry
                          -- By our inductive hypothesis, the sum of the first n positive natural numbers is n(n + 1) / 2. 
                          ... = 2 * (n+1) + n * (n + 1) : IHn
                          -- [DHS] (Keith's calculations are more cumbersome due to the division)
                          ... = n*n + 3*n + 2 : sorry
                          ... = (n+1)*(n+2) : sorry
                     -- Thus P(n + 1) is true, completing the induction.
                     )

/- [KS]
Theorem: For any natural number n, ∑_{i=0}^{n-1} (2i + 1) = n²
Proof: By induction. Let P(n) be defined as
P(n)≡∑
i=0
n−1
(2i+ 1)=n
2
We prove that P(n) is true for all n ∈ ℕ by induction on n. As our base case, we prove P(0), that
∑_{i=0}^{-1} (2 i+ 1)=0².

The left-hand side of this equality is the empty sum, which is 0. The right-hand side of the equality
is also 0, so P(0) holds.

For the inductive step, assume that for some natural number n, P(n) holds, meaning that
∑_{i=0}^{n−1} (2 i+ 1) = n².

We will prove P(n + 1), meaning that
∑_{i=0}^{n} (2 i+ 1) = (n+1)².
To see this, note that
∑_{i=0}^{n} (2i+ 1)=(n+ 1)² 
= ∑_{i=0}^{n−1} (2i+ 1)+ 2 n+ 1
= n² + 2n+ 1
=(n+ 1)²

Thus P(n + 1) holds, completing the induction.
-/

theorem sum_odd_nats : ∀ (n:nat), sum_of_pos n (λ n, 2 * n + 1) = (n+1)² :=
  take n,
  nat.induction_on n
                   (show sum_of_pos 0 (λ n, 2 * n + 1) = (0+1)², from sorry)
                   (assume n (IHn : sum_of_pos n (λ n, 2*n+1) = (n+1)²),
                    show sum_of_pos (n+1) (λ n,2*n+1) = (n+2)², from
                      calc sum_of_pos (n+1) (λ n,2*n+1) = 2 * (n+1) + 1 + sum_of_pos n (λ n,2*n+1) : rfl
                           ... = 2 * (n+1) + 1 + (n+1)² : sorry
                           ... = n² + 4*n + 4 : sorry
                           ... = (n+2)² : sorry)


/- [KS]
Theorem: For any natural number n, ∑_{i=0}^{n−1} i = n.
Proof: <too many annoying symbols>
-/
definition constant_fn (i : nat) : nat → nat := λ n, i

theorem sum_constant : ∀ (n:nat), sum_of_pos n (constant_fn 1) = n :=
  take n,
  nat.induction_on n
                   (show sum_of_pos 0 (constant_fn 1) = 0, from rfl)
                   (assume n (IHn : sum_of_pos n (constant_fn 1) = n),
                    show sum_of_pos (n+1) (constant_fn 1) = n+1, from
                      calc sum_of_pos (n+1) (constant_fn 1) = 1 + sum_of_pos n (constant_fn 1) : rfl
                           ... = 1 + n : IHn
                           ... = n + 1 : add_comm)
-- Variants on Induction

/- [KS]
Theorem: Let P(n) be a property that applies to natural numbers and let k be a natural number. If
the following are true:
- P(k) is true
- For any n ∈ ℕ with n ≥ k, P(n) → P(n + 1)
Then for any n ∈ ℕ with n ≥ k, P(n) is true.

Proof: Consider any property P(n) of the natural numbers for which the above is true. Now, define
Q(n) ≡ P(n + k). This proof will work in two parts: first, we will prove, by induction, that Q(n) is
true for all n . Next, we will show that this implies that ∈ ℕ P(n) is true for all n where ∈ ℕ n ≥ k.
First, we prove that Q(n) is true for all n by induction. As our base case, we prove ∈ ℕ Q(0),
meaning that P(k) holds. By our choice of P, we know that this is true. Thus Q(0) holds.
For the inductive step, assume that for some n that ∈ ℕ Q(n) is true, meaning that P(n + k) holds.
We will prove that Q(n + 1) is true, meaning that P(n + k + 1) holds. Now, since n ∈ ℕ , we know
that n ≥ 0. Consequently, we know that n + k ≥ k. Thus by the properties of P, we know that
P(n + k) implies P(n + k + 1). Since Q(n + 1) ≡ P(n + k + 1), this proves that Q(n + 1) holds, completing
the induction. Thus Q(n) is true for all natural numbers n.
Now, we use this result to prove that P(n) is true for all natural numbers n ≥ k. Consider any arbitrary
natural number n ≥ k. Thus n – k ≥ 0, so n – k is a natural number. Therefore, Q(n – k) holds.
Since (n – k) + k = n, this means that P(n) holds. Since our choice of n was arbitrary, this shows
that P(n) is true for all natural numbers n ≥ k. 
-/

-- [DHS]#TODO tricky to avoid burdens, need the elaborator to kick-ass mod AC

open nat

definition shift (P : nat → Prop) (k : nat) : nat → Prop := λ m, P (m + k)

theorem nat.late_induction_on {P : nat → Prop} (k : nat) (base : P k) (step : ∀ (n:nat), n ≥ k → P n → P (n+1)) : ∀ (n:nat), n ≥ k → P n :=
  -- Consider any property P(n) of the natural numbers for which the above is true. 
  -- Now, define Q(n) ≡ P(n + k).
  let Q := shift P k in
  let Q := λ n, P (n + k) in
  -- This proof will work in two parts: first, we will prove, by induction, that Q(n) is true for all n. 
  -- Next, we will show that this implies that ∈ ℕ P(n) is true for all n where ∈ ℕ n ≥ k.

-- First, we prove that Q(n) is true for all n 
  have Q_holds : ∀ n, Q n, from
    take n,
  -- by induction.
    nat.induction_on n
                     (--  As our base case, we prove ∈ ℕ Q(0), meaning that P(k) holds. 
                     show Q 0, from
                     -- By our choice of P, we know that this is true. Thus Q(0) holds.
                     (zero_add k)⁻¹ ▸ base)
                     (-- For the inductive step, assume that for some n that ∈ ℕ Q(n) is true, 
                     (assume n (Qn : Q n),
                      -- meaning that P(n + k) holds.
                      have pnk : P (n + k), from Qn,
                      -- We will prove that Q(n + 1) is true, meaning that P(n + k + 1) holds.
                      show Q (n+1), from
                      -- Now, since n ∈ ℕ , we know that n ≥ 0. Consequently, we know that n + k ≥ k.
                      have npk_ge_k : n + k ≥ k, from le_add_left k n,
                      -- Thus by the properties of P, we know that P(n + k) implies P(n + k + 1).
                      have pnk_p1 : P (n + k + 1), from step (n+k) npk_ge_k Qn,
                      -- Since Q(n + 1) ≡ P(n + k + 1), this proves that Q(n + 1) holds, completing the induction. 
                      (add.right_comm n k 1) ▸ pnk_p1
                      -- Thus Q(n) is true for all natural numbers n.
                      )
  -- Now, we use this result to prove that P(n) is true for all natural numbers n ≥ k. 
  show ∀ (n : nat), n ≥ k → P n, from
  -- Consider any arbitrary natural number n ≥ k.
  take (n : nat) (n_ge_k : n ≥ k),
  -- Thus n – k ≥ 0, so n – k is a natural number.
  -- Therefore, Q(n – k) holds. Since (n – k) + k = n, this means that P(n) holds. 
  have n_mk_pk : (n - k) + k = n, from sub_add_cancel n_ge_k,
  have Q_nmk : Q (n - k), from Q_holds (n-k),
  n_mk_pk ▸ Q_nmk
  -- Since our choice of n was arbitrary, this shows that P(n) is true for all natural numbers n ≥ k. 


