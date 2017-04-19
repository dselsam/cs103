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

definition big_union (Xs : set (set T)) : set T := λ x, ∃ xs, xs ∈ Xs ∧ x ∈ xs
definition powerset (xs : set T) : set (set T) := λ ys, ys ⊆ xs

structure partition (xs : set T) (Xs : set (set T)) :=
  mk :: (in_powerset : Xs ⊆ powerset xs)
        (spans : big_union Xs = xs)
        (pdisjoint : pairwise_disjoint Xs)
        (ncempty : ¬ ∅ ∈ Xs)

open partition

-- Choice functions (not the end of the world)
-- (if we go down this road, we would hide the definitions from students, and just give them (1), (3) and (4))

definition cover {xs : set T} {Xs : set (set T)} (p : partition xs Xs) (x : T) : set T := epsilon (λ ys, ys ∈ Xs ∧ x ∈ ys)

definition cover_exists {xs : set T} {Xs : set (set T)} (p : partition xs Xs) (x : T) (x_in_xs : x ∈ xs) : ∃ ys, ys ∈ Xs ∧ x ∈ ys := 
  (spans p)⁻¹ ▸ x_in_xs

lemma x_in_cover_x {xs : set T} {Xs : set (set T)} (p : partition xs Xs) (x : T) (x_in_xs : x ∈ xs) : x ∈ cover p x := 
  and.right (epsilon_spec (cover_exists p x x_in_xs))

lemma cover_x_in_Xs {xs : set T} {Xs : set (set T)} (p : partition xs Xs) (x : T) (x_in_xs : x ∈ xs) : cover p x ∈ Xs := 
  and.left (epsilon_spec (cover_exists p x x_in_xs))

/- [KS]
Lemma: Let S be a set and X a partition of S. Then every element u ∈ S belongs to exactly one set
Y ∈ X
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

definition exactly_one [reducible] {T : Type} (P : T → Prop) := (∃ (u : T), P u) ∧ (∀ u v : T, P u → P v → u = v)

-- Lemma: Let S be a set and X a partition of S. Then every element u ∈ S belongs to exactly one set Y ∈ X.
definition unique_set : ∀ {S : set T} {X : set (set T)}, partition S X → ∀ (u : T), u ∈ S → exactly_one (λ (Y : set T), Y ∈ X ∧ u ∈ Y) :=
  -- Proof: Let S be a set and X a partition of S. 
  assume (S : set T) (X : set (set T)) (p : partition S X) (u : T) (u_in_S : u ∈ S),
  -- We will show that every element u ∈ S belongs to at least one set Y ∈ X and to at most one set Y ∈ X.
  show (∃ (Y : set T), Y ∈ X ∧ u ∈ Y) ∧ (∀ (Y1 Y2 : set T), (Y1 ∈ X ∧ u ∈ Y1) → (Y2 ∈ X ∧ u ∈ Y2) → Y1 = Y2), from
  -- To see that every element u ∈ S belongs to at least one set Y ∈ X, 
  have exists_Y : ∃ (Y : set T), Y ∈ X ∧ u ∈ Y, from
    -- note that since X is a partition of S, the union of all the sets in S must be equal to S. 
    -- Consequently, there must be at least one set Y ∈ X such that u ∈ Y, 
    -- since otherwise the union of all sets contained in X would not be equal to S.
    have u_in_bigX : u ∈ big_union X, from (spans p)⁻¹ ▸ u_in_S,
    u_in_bigX,
  -- To see that every element u ∈ S belongs to at most one set Y ∈ X, 
  have unique : (∀ (Y1 Y2 : set T), (Y1 ∈ X ∧ u ∈ Y1) → (Y2 ∈ X ∧ u ∈ Y2) → Y1 = Y2), from
    -- suppose for the sake of contradiction that u belongs to two sets Y1, Y2 ∈ X with Y1 ≠ Y2. 
    assume (Y1 Y2 : set T) (HY1 : Y1 ∈ X ∧ u ∈ Y1) (HY2 : Y2 ∈ X ∧ u ∈ Y2),
    by_contradiction
      (assume Y1_neq_Y2 : Y1 ≠ Y2, 
       show false, from
       -- But then u ∈ Y1 ∩ Y2,
       have u_in_Y1capY2 : u ∈ Y1 ∩ Y2, from and.intro (and.right HY1) (and.right HY2),
       -- meaning that Y1 ∩ Y2 ≠ Ø, a contradiction. 
       have Y1capY2_nempty : Y1 ∩ Y2 ≠ ∅, from 
         assume Y1capY2_empty : Y1 ∩ Y2 = ∅, 
         have u_in_emptyset : u ∈ ∅, from Y1capY2_empty ▸ u_in_Y1capY2,
         show false, from u_in_emptyset,
       -- We have reached a contradiction, so our assumption must have been wrong.
       absurd (pdisjoint p (and.left HY1) (and.left HY2) Y1_neq_Y2) Y1capY2_nempty),
  -- Thus every element u ∈ S belongs to at most one set Y ∈ X. 
  show exactly_one (λ (Y : set T), Y ∈ X ∧ u ∈ Y), from and.intro exists_Y unique
  -- ■

definition set_of_sets (f : T → set T) : set (set T) := λ (s : set T), ∃ (u : T), s = f u
definition bigcup (Xs : set (set T)) : set T := λ (v: T), ∃ (X : set T), X ∈ Xs ∧ v ∈ X

lemma equiv_spans : ∀ {R : T → T → Prop}, equivalence R → ∀ v, v ∈ bigcup (set_of_sets R) :=
  assume (R : T → T → Prop) (R_equiv : equivalence R) (v : T),
  show ∃ (X : set T), X ∈ (set_of_sets R) ∧ v ∈ X, from
  let X := R v in
  have X_in_ssR : X ∈ set_of_sets R, from exists.intro v rfl,
  have v_in_X : v ∈ X, from and.left R_equiv v,
  exists.intro X (and.intro X_in_ssR v_in_X)

end relations

