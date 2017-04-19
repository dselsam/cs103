import data.set classical algebra.order data.nat
open set eq.ops

namespace relations

variable {T : Type}

/- [KS]
Given a set S, a partition of S is a set X ⊆ ℘(S) (that is, a set of subsets of S) with the following properties:
1. The union of all sets in X is equal to S.
2. For any S1, S2 ∈ X with S1 ≠ S2, we have that S1 ∩ S2 = Ø (S1 and S2 are disjoint)
3. Ø ∉ X.
-/

definition pairwise_disjoint (Xs : set (set T)) := ∀ ⦃ X1 X2 : set T ⦄, X1 ∈ Xs → X2 ∈ Xs → X1 ≠ X2 → X1 ∩ X2 = ∅

structure partition (Xs : set (set T)) :=
  mk :: (cover : T → set T)
        (cover_legal : ∀ x, cover x ∈ Xs)
        (cover_spans : ∀ x, x ∈ cover x)
        (pdisjoint : pairwise_disjoint Xs)
        (ncempty : ¬ ∅ ∈ Xs)

open partition



/- [KS]
Lemma: Let S be a set and X a partition of S. Then every element u ∈ S belongs to exactly one set
Y ∈ X.
Proof: Let S be a set and X a partition of S. We will show that every element u ∈ S belongs to at least
one set Y ∈ X and to at most one set Y ∈ X.
To see that every element u ∈ S belongs to at least one set Y ∈ X, note that since X is a partition of S,
the union of all the sets in S must be equal to S. Consequently, there must be at least one set Y ∈ X
such that u ∈ Y, since otherwise the union of all sets contained in X would not be equal to S.
To see that every element u ∈ S belongs to at most one set Y ∈ X, suppose for the sake of contradiction
that u belongs to two sets Y1, Y2 ∈ X with Y1 ≠ Y2. But then x ∈ Y1 ∩ Y2, meaning that
Y1 ∩ Y2 ≠ Ø, a contradiction. We have reached a contradiction, so our assumption must have been
wrong.
Thus every element u ∈ S belongs to at most one set Y ∈ X. ■
-/

/-
definition exists_unique {A : Type} (p : A → Prop) :=
∃x, p x ∧ ∀y, p y → y = x

notation `∃!` binders `,` r:(scoped P, exists_unique P) := r

theorem exists_unique.intro {A : Type} {p : A → Prop} (w : A) (H1 : p w) (H2 : ∀y, p y → y = w) :
  ∃!x, p x :=
exists.intro w (and.intro H1 H2)

theorem exists_unique.elim {A : Type} {p : A → Prop} {b : Prop}
    (H2 : ∃!x, p x) (H1 : ∀x, p x → (∀y, p y → y = x) → b) : b :=
obtain w Hw, from H2,
H1 w (and.elim_left Hw) (and.elim_right Hw)
-/

lemma unique_set : ∀ {Xs : set (set T)}, partition Xs → ∀ (u : T), ∃! (X : set T), X ∈ Xs ∧ u ∈ X :=
  assume (Xs : set (set T)) (pXs : partition Xs) (u : T),
  show ∃! (X : set T), X ∈ Xs ∧ u ∈ X, from
  show ∃ (X : set T), (X ∈ Xs ∧ u ∈ X) ∧ (∀ Y, Y ∈ Xs ∧ u ∈ Y → Y = X), from
  let X := cover pXs u in 
  have X_unique : (∀ Y, Y ∈ Xs ∧ u ∈ Y → Y = X), from
    assume (Y : set T) (Y_in_Xs_and_u_in_Y : Y ∈ Xs ∧ u ∈ Y),
    have Y_in_Xs : Y ∈ Xs, from and.left Y_in_Xs_and_u_in_Y,
    have u_in_Y : u ∈ Y, from and.right Y_in_Xs_and_u_in_Y,
    by_contradiction 
      (assume (Y_neq_X : Y ≠ X),
       show false, from
       -- But then x ∈ Y1 ∩ Y2, 
       have u_in_Y_cap_X : u ∈ Y ∩ X, from and.intro u_in_Y (cover_spans pXs u),
       -- meaning that Y1 ∩ Y2 ≠ Ø, 
       have Y_cap_X_neq_empty : Y ∩ X ≠ ∅, from 
         assume (cap_empty : Y ∩ X = ∅), 
         have u_in_empty : u ∈ ∅, from cap_empty ▸ u_in_Y_cap_X,
         show false, from u_in_empty,
       -- a contradiction. We have reached a contradiction, so our assumption must have been wrong.
       absurd (pdisjoint pXs Y_in_Xs (cover_legal pXs u) Y_neq_X) Y_cap_X_neq_empty),
  -- Thus every element u ∈ S belongs to at most one set Y ∈ X. ■
  exists_unique.intro X (and.intro (cover_legal pXs u) (cover_spans pXs u)) X_unique

definition P_equiv {Xs : set (set T)} (pXs : partition Xs) (x y : T) := cover pXs x = cover pXs y

/-
To see that ~X is reflexive, we need to prove that for any u ∈ S, that u ~X u. By definition, this means
that we need to show that [u]X = [u]X, which is true because = is reflexive.
To see that ~X is symmetric, we need to show that if u ~X v, then v ~X u. By definition, this means
that we need to show that if [u]X = [v]X, then [v]X = [u]X. This is true because = is symmetric.
To see that ~X is transitive, we need to show that if u ~X v and v ~X w, then u ~X w. By definition, this
means that we need to show that if [u]X = [v]X and [v]X = [w]X, then [u]X = [w]X. This is true because
= is transitive.
-/

print definition reflexive
check reflexive
-- TODO why won't this work??
set_option formatter.hide_full_terms false


lemma P_equiv_refl : ∀ {Xs : set (set T)} (pXs : partition Xs), reflexive (P_equiv pXs) := 
  assume (Xs : set (set T)) (pXs : partition Xs), 
  show reflexive (P_equiv pXs), from
  assume (u : T),
  show P_equiv pXs u u, from
  show cover pXs u = cover pXs u, from rfl

lemma P_equiv_symm : ∀ {Xs : set (set T)} (pXs : partition Xs), symmetric (P_equiv pXs) := 
  assume (Xs : set (set T)) (pXs : partition Xs), 
  show symmetric (P_equiv pXs), from
  assume (u v : T),
  show P_equiv pXs u v → P_equiv pXs v u, from
  assume (uRv : cover pXs u = cover pXs v),
  show cover pXs v = cover pXs u, from uRv⁻¹

lemma P_equiv_trans : ∀ {Xs : set (set T)} (pXs : partition Xs), transitive (P_equiv pXs) := 
  assume (Xs : set (set T)) (pXs : partition Xs), 
  show transitive (P_equiv pXs), from
  assume (u v w: T) (uRv : cover pXs u = cover pXs v) (vRw : cover pXs v = cover pXs w),
  show cover pXs u = cover pXs w, from vRw ▸ uRv


/- [KS]
Lemma: Let R be an equivalence relation over A, and X = { [x]R | x ∈ A }. Then ∪X = A.
Proof: Let R be an equivalence relation over A, and X = { [x]R | x ∈ A }. We will prove that ∪X ⊆ A
and A ⊆ ∪X, from which we can conclude that ∪X = A.
To show that ∪X ⊆ A, consider any x ∈ X. By definition of ∪X, since x ∈ X, this means that there is
some [y]R ∈ X such that x ∈ [y]R. By definition of [y]R, since x ∈ [y]R, this means that yRx. Since R is
a binary relation over A, this means that x ∈ A. Since our choice of x was arbitrary, this shows that if
x ∈ ∪X, then x ∈ A. Thus ∪X ⊆ A.
To show that A ⊆ ∪X, consider any x ∈ A. We will prove that x ∈ [x]R. If we can show this, then note
that since x ∈ [x]R and [x]R ∈ X, we have x ∈ X. Since our choice of x is arbitrary, this would mean
that any x ∈ A satisfies x ∈ ∪X, so A ⊆ ∪X.
So let's now prove that x ∈ [x]R. By definition, [x]R = { y ∈ A | xRy }. Since R is an equivalence relation,
R is reflexive, so xRx. Consequently, x ∈ [x]R, as required. ■ 
-/
print definition equivalence

definition set_of_sets (f : T → set T) : set (set T) := λ (s : set T), ∃ (u : T), s = f u
definition bigcup (Xs : set (set T)) : set T := λ (v: T), ∃ (X : set T), X ∈ Xs ∧ v ∈ X

lemma equiv_spans : ∀ {R : T → T → Prop}, equivalence R → ∀ v, v ∈ bigcup (set_of_sets R) :=
  assume (R : T → T → Prop) (R_equiv : equivalence R) (v : T),
  show ∃ (X : set T), X ∈ (set_of_sets R) ∧ v ∈ X, from
  let X := R v in
  have X_in_ssR : X ∈ set_of_sets R, from exists.intro v rfl,
  have v_in_X : v ∈ X, from and.left R_equiv v,
  exists.intro X (and.intro X_in_ssR v_in_X)

/- [KS]
Lemma: Let R be an equivalence relation over A, and X = { [x]R | x ∈ A }. Then Ø ∉ X.
Proof: Using the logic of our previous proof, we have that for any x ∈ A, that x ∈ [x]R. Consequently,
for any x ∈ A, we know [x]R ≠ Ø. Thus Ø ∉ X. ■
-/

lemma equiv_nonempty : ∀ {R : T → T → Prop}, equivalence R → ¬ ∅ ∈ set_of_sets R := 
  assume (R : T → T → Prop) (R_equiv : equivalence R) (equiv_empty : ∅ ∈ set_of_sets R),
  show false, from 
  have exists_u : ∃ (u : T), ∅ = R u, from equiv_empty,
  obtain (u : T) (u_empty : ∅ = R u), from exists_u,
  have Ruu : R u u, from and.left R_equiv u,
  show false, from (congr_fun u_empty⁻¹ u) ▸ Ruu


/- [KS]
Lemma: Let R be an equivalence relation over A, and X = { [x]R | x ∈ A }. Then for any two sets [x]R,
[y]R ∈ X, if [x]R ≠ [y]R, then [x]R ∩ [y]R = Ø.
Proof: Let R be an equivalence relation over A, and X = { [x]R | x ∈ A }. We proceed by contrapositive
and show that for any [x]R, [y]R ∈ X, that if [x]R ∩ [y]R ≠ Ø, then [x]R = [y]R.
Consider any [x]R, [y]R ∈ X such that [x]R ∩ [y]R ≠ Ø. Then there must be some element w such that
w ∈ [x]R and w ∈ [y]R. By definition, this means w ∈ { z ∈ A | xRz } and w ∈ { z ∈ A | yRz }. Consequently,
xRw and yRw. Since R is symmetric, this means that xRw and wRy. Since R is transitive,
this means that xRy. By symmetry, we also have that yRx.
We will now use this fact to show that [x]R ⊆ [y]R. Without loss of generality, we can use this same
argument to show that [y]R ⊆ [x]R, from which we can conclude that [x]R = [y]R, as required.
To show that [x]R ⊆ [y]R, consider any z ∈ [x]R. This means that xRz. Since yRx and xRz, by transitivity
we have that yRz. Consequently, z ∈ [y]R. Since our choice of z was arbitrary, we have that any
z ∈ [x]R satisfies z ∈ [y]R. Thus [x]R ⊆ [y]R, as required. ■
-/

-- proved elsewhere
axiom by_contrapositive : ∀ {P Q : Prop}, (¬ Q → ¬ P) → (P → Q)
lemma nonempty_choice : ∀ ⦃X : set T⦄, X ≠ ∅ → ∃ x, x ∈ X := sorry
lemma subset_eq : ∀ ⦃ X Y : set T ⦄, X ⊆ Y → Y ⊆ X → X = Y := sorry
lemma double_negation : ∀ {P : Prop}, ¬ ¬ P → P := sorry
lemma intro_double_negation : ∀ {P : Prop}, P → ¬¬ P := sorry

print definition equivalence

definition equiv_refl ⦃R : T → T → Prop⦄ (R_equiv : equivalence R) : reflexive R := and.left R_equiv
definition equiv_symm ⦃R : T → T → Prop⦄ (R_equiv : equivalence R) : symmetric R := and.left (and.right R_equiv)
definition equiv_trans ⦃R : T → T → Prop⦄ (R_equiv : equivalence R) : transitive R := and.right (and.right R_equiv)
print definition transitive

lemma equiv_pdisjoint : ∀ {R : T → T → Prop}, equivalence R → pairwise_disjoint (set_of_sets R) :=
  assume (R : T → T → Prop) (R_equiv : equivalence R),
  show pairwise_disjoint (set_of_sets R), from
  let Xs := set_of_sets R in
  show ∀ (X1 X2 : set T), X1 ∈ Xs → X2 ∈ Xs → X1 ≠ X2 → X1 ∩ X2 = ∅, from
  assume (X1 X2 : set T) (X1_in_Xs : X1 ∈ Xs) (X2_in_Xs : X2 ∈ Xs),
  show X1 ≠ X2 → X1 ∩ X2 = ∅, from
  by_contrapositive (
    assume (X1_meets_X2 : X1 ∩ X2 ≠ ∅),
    show ¬ X1 ≠ X2, from -- annoying double negation (how to apply and change the show?)
    have X1_eq_X2 : X1 = X2, from 
    obtain (x : T) (X1_x : X1 = R x), from X1_in_Xs,
    obtain (y : T) (X2_y : X2 = R y), from X2_in_Xs,
    have exists_w_in_both : ∃ w, w ∈ X1 ∧ w ∈ X2, from nonempty_choice X1_meets_X2,
    obtain (w : T) (w_in_both : w ∈ X1 ∧ w ∈ X2), from exists_w_in_both,
    have Rxw : R x w, from congr_fun X1_x w ▸ (and.left w_in_both),
    have Ryw : R y w, from congr_fun X2_y w ▸ (and.right w_in_both),
    have Rxy : R x y, from equiv_trans R_equiv Rxw (equiv_symm R_equiv Ryw),
    have X1_ss_X2 : X1 ⊆ X2, from
      assume (z : T) (z_in_X1 : z ∈ X1),
      show z ∈ X2, from
      have Rxz : R x z, from congr_fun X1_x z ▸ z_in_X1,
      have Ryz : R y z, from equiv_trans R_equiv (equiv_symm R_equiv Rxy) Rxz,
      congr_fun X2_y⁻¹ z ▸ Ryz,
    have X2_ss_X1 : X2 ⊆ X1, from
      assume (z : T) (z_in_X2 : z ∈ X2),
      show z ∈ X1, from
      have Ryz : R y z, from congr_fun X2_y z ▸ z_in_X2,
      have Rxz : R x z, from equiv_trans R_equiv Rxy Ryz,
      congr_fun X1_x⁻¹ z ▸ Rxz,
    subset_eq X1_ss_X2 X2_ss_X1,
    intro_double_negation X1_eq_X2
  )

/- [KS]
Theorem: Let R be an equivalence relation over A, and let X = { [x]R | x ∈ A }. Then X is a partition
of A.
-/

theorem equiv_partition : ∀ (R : T → T → Prop), equivalence R → partition (set_of_sets R) := 
  assume (R : T → T → Prop) (R_equiv : equivalence R),
  show partition (set_of_sets R), from
  have R_legal : ∀ x, R x ∈ set_of_sets R, from assume x, exists.intro x rfl,
  have R_spans : ∀ x, x ∈ R x, from assume x, equiv_refl R_equiv x,
  have R_pdisjoint : pairwise_disjoint (set_of_sets R), from equiv_pdisjoint R_equiv,
  have R_ncempty : ¬ ∅ ∈ set_of_sets R, from equiv_nonempty R_equiv,
  partition.mk R R_legal R_spans R_pdisjoint R_ncempty
  


definition asymmetric (R : T → T → Prop) := ∀ x y, R x y → ¬ R y x
definition antisymmetric (R : T → T → Prop) := ∀ x y, R x y → R y x → x = y

/- [KS]
A binary relation R over a set A is called a strict order iff R is irreflexive, asymmetric, and transitive.
-/

structure strict_order (R : T → T → Prop) :=
  mk :: (irrefl : irreflexive R)
        (asym : asymmetric R)
        (trans : transitive R)

/- [KS]
Theorem: The relation ⊂ over ℘(ℕ) is a strict order.
Proof: We show that ⊂ is irreflexive, asymmetric, and transitive.
To show that ⊂ is irreflexive, we must show that for any A ∈ ℘(ℕ) that A ⊂ A does not hold. To see
this, assume for the sake of contradiction that this is false and that there exists some A ∈ ℘(ℕ) such
that A ⊂ A. By definition of ⊂, this means that A ⊆ A and A ≠ A. But A ≠ A is impossible, since = is
reflexive. We have reached a contradiction, so our assumption must have been wrong. Thus ⊂ is irreflexive.
To show that ⊂ is asymmetric, we must show that for any A, B ∈ ℘(ℕ) that if A ⊂ B, then it is not the
case that B ⊂ A. We proceed by contradiction; assume that this statement is false and that there exist
some sets A, B ∈ ℘(ℕ) such that A ⊂ B and B ⊂ A. By definition of ⊂, this means that A ⊆ B, B ⊆ A,
but A ≠ B. Since A ⊆ B and B ⊆ A, we know that A = B, contradicting the fact that A ≠ B. We have
reached a contradiction, so our assumption must have been wrong. Thus ⊂ is asymmetric.
To show that ⊂ is transitive, we need to show that for any A, B, C ∈ ℘(ℕ), that if A ⊂ B and B ⊂ C,
then A ⊂ C. Consider any A, B, C ∈ ℘(ℕ) where A ⊂ B and B ⊂ C. By definition of ⊂, this means
that A ⊆ B, B ⊆ C, A ≠ B, and B ≠ C. We will show that A ⊂ C, meaning that A ⊆ C and A ≠ C.
Since A ⊆ B and B ⊆ C, we know that A ⊆ C. To show that A ≠ C, assume for the sake of contradiction
that A = C. Since B ⊂ C and C = A, this means that B ⊂ A. But this is impossible, because we
also know that A ⊂ B, and ⊂ is asymmetric. We have reached a contradiction, so our assumption
must have been wrong. Thus A ≠ C. Since A ⊆ C and A ≠ C, this means that A ⊂ C as required.
Since ⊂ is irreflexive, asymmetric, and transitive, it is a strict order over ℘(ℕ). ■
-/


definition strict_subset (X Y : set T) : Prop := X ⊆ Y ∧ X ≠ Y
infix `⊂`:50 := strict_subset

check strict_order
check strict_subset
theorem strict_subset_string_order : (@strict_order (set T)) (@strict_subset T) := 
  have ss_irrefl : irreflexive strict_subset, from 
    assume (X : set T) (X_lt_X : X ⊆ X ∧ X ≠ X),
    absurd rfl (and.right X_lt_X),
  have ss_asym : asymmetric strict_subset, from 
    assume (X Y : set T) (X_lt_Y : X ⊂ Y) (Y_lt_X : Y ⊂ X),
    have X_eq_Y : X = Y, from subset_eq (and.left X_lt_Y) (and.left Y_lt_X),
    absurd X_eq_Y (and.right X_lt_Y),
  have ss_trans : transitive strict_subset, from 
    assume (X Y Z : set T) (X_lt_Y : X ⊂ Y) (Y_lt_Z : Y ⊂ Z),
    show X ⊂ Z, from
      have X_ss_Z : X ⊆ Z, from assume (x : T) (x_in_X : x ∈ X), and.left Y_lt_Z x (and.left X_lt_Y x x_in_X),
      have X_neq_Z : X ≠ Z, from 
        assume (X_eq_Z : X = Z), 
        have Y_ss_X : Y ⊆ X, from X_eq_Z⁻¹ ▸ (and.left Y_lt_Z),
        have X_eq_Y : X = Y, from subset_eq (and.left X_lt_Y) Y_ss_X,
        absurd X_eq_Y (and.right X_lt_Y),
    and.intro X_ss_Z X_neq_Z,
  strict_order.mk ss_irrefl ss_asym ss_trans
  
open nat

structure partial_order (R : T → T → Prop) :=
  mk :: (refl : reflexive R)
        (antisym : antisymmetric R)
        (trans : transitive R)

definition divides (m n : nat) := ∃ q, n = m * q
infix `∣` := divides
check 2 ∣ 8
/- [KS]
Theorem: | is a partial order over ℕ.
Proof: We will show that | is reflexive, antisymmetric, and transitive. To see that | is reflexive, we will
prove that for any n ∈ ℕ, that n | n (that there exists some q ∈ ℕ such that n = nq). So let n be any
natural number, and take q = 1. Then nq = n · 1 = n, so n | n.
To see that | is antisymmetric, we will prove that for any m, n ∈ ℕ, that if m | n and n | m, that m = n.
Consider any m, n ∈ ℕ where m | n and n | m. This means that there exists q, r ∈ ℕ such that n = mq
and m = nr. Consequently:
m = nr = (mq)r = mqr
n = mq = (nr)q = nqr
We now consider two cases. First, if m = n = 0, then we are done, since m = n. Otherwise, at least
one of m or n is nonzero; without loss of generality, assume m ≠ 0. Then since m = mqr, we know
that 1 = qr. Since q, r ∈ ℕ, this is only possible if q = r = 1. Consequently, m = nr = n · 1 = n, so
m = n, as required.
To see that | is transitive, we will prove that for any m, n, p ∈ ℕ, that if m | n and n | p, then m | p.
Consider any m, n, p ∈ ℕ where m | n and n | p; then there must exist q, r ∈ ℕ such that n = qm and
p = rn. Consequently, p = rn = r(qm) = qrm = (qr)m. Since qr ∈ ℕ, this means that there is some
k ∈ ℕ (namely, qr) such that p = km. Thus m | p, as required.
Since | is reflexive, antisymmetric, and transitive over ℕ, | is a partial order over ℕ.
-/

print definition mul

lemma mul_cancel : ∀ ⦃m n : nat⦄, m ≠ 0 → m = m * n → n = 1 := sorry
lemma mul_cancel_one_right : ∀ ⦃ m n : nat ⦄, m * n = 1 → n = 1 := sorry

theorem divides_partial_order : partial_order divides := 
  have div_refl : reflexive divides, from 
    assume (n : ℕ),
    show n ∣ n, from exists.intro 1 (mul_one n)⁻¹,
  have div_antisym : antisymmetric divides, from 
    assume (m n : ℕ) (m_div_n : m ∣ n) (n_div_m : n ∣ m),
    show m = n, from 
      have m_neq_0 : m ≠ 0, from sorry, -- #FALSE need case analysis
      obtain (q1 : ℕ) (n_eq_mq1 : n = m * q1), from m_div_n,
      obtain (q2 : ℕ) (m_eq_nq2 : m = n * q2), from n_div_m,
      have m_eq_m_q12 : m = m * (q1 * q2), from (mul.assoc m q1 q2) ▸ n_eq_mq1 ▸ m_eq_nq2,
      have q1q2_eq_1 : q1 * q2 = 1, from mul_cancel m_neq_0 m_eq_m_q12,
      have q2_eq_1 : q2 = 1, from mul_cancel_one_right q1q2_eq_1,
      have m_eq_n1 : m = n * 1, from q2_eq_1 ▸ m_eq_nq2,
      (mul_one n) ▸ m_eq_n1,
  have div_trans : transitive divides, from 
    assume (m n p : ℕ) (m_div_n : m ∣ n) (n_div_p : n ∣ p),
    show m ∣ p, from 
      obtain (q1 : ℕ) (n_eq_mq1 : n = m * q1), from m_div_n,
      obtain (q2 : ℕ) (p_eq_nq2 : p = n * q2), from n_div_p,
      exists.intro (q1 * q2) (mul.assoc m q1 q2 ▸ n_eq_mq1 ▸ p_eq_nq2),
  partial_order.mk div_refl div_antisym div_trans
 
  
  














end relations
