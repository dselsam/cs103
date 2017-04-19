import data.list data.subtype data.set classical
open subtype list prod prod.ops nat eq.ops

definition no_dup {V : Type} : list V → Prop
| [] := true
| (x :: xs) := ¬ x ∈ xs ∧ no_dup xs

definition last {V : Type} [V_inhabited : inhabited V] : list V → V
| [] := arbitrary V
| [x] := x
| (x :: xs) := last xs

definition all_but_last {V : Type} : list V → list V
| [] := []
| [x] := []
| (x :: xs) := x :: all_but_last xs

lemma all_but_last_concat {V : Type} (xs : list V) (x : V) : all_but_last (concat x xs) = xs := sorry
lemma last_concat {V : Type} [V_inhabited : inhabited V] (xs : list V) (x : V) : last (concat x xs) = x := sorry
lemma head_concat {V : Type} [V_inhabited : inhabited V] (xs : list V) (x : V) : xs ≠ [] → head (concat x xs) = head xs := sorry
lemma length_concat {V : Type} (xs : list V) (x : V) : length (concat x xs) = length xs + 1 := sorry

lemma concat_nnil {V : Type} (xs : list V) (x : V) : concat x xs ≠ nil := sorry
lemma concat_nnil_gt1 {V : Type} (xs : list V) (x : V) : xs ≠ nil → length (concat x xs) > 1 := sorry

theorem prop_demorgan : ∀ {A B : Prop}, ¬ (A ∧ B) → ¬ A ∨ ¬ B :=
  take (A B : Prop),
  take notAandB : ¬ (A ∧ B),
  or.elim (em A)
          (take a : A,
           or.elim (em B)
                   (take b : B, absurd (and.intro a b) notAandB)
                   (take nb : ¬ B, or.inr nb))
          (take na : ¬ A, or.inl na)

lemma reverse_last_head {V : Type} [V_inhabited : inhabited V] (xs : list V) : last (reverse xs) = head xs:= sorry
lemma reverse_head_last {V : Type} [V_inhabited : inhabited V] (xs : list V) : head (reverse xs) = last xs := sorry

definition edge (V : Type) := V × V
definition graph (V : Type) := edge V → Prop
definition undirected {V : Type} (g : graph V) := ∀ (u v : V), g (u,v) → g (v,u)

namespace path

variables {V : Type} [V_decidable_eq : decidable_eq V] [V_inhabited : inhabited V]
include V_decidable_eq V_inhabited

/- [KS]
A path in a graph G = (V, E) is a series of nodes (v1, v2, …, vn) where for any i ∈ ℕ with 1 ≤ i < n,
there is an edge from vi to vi+1.
-/

definition path_pred (g : graph V) (xs : list V) := ∀ (i : ℕ), i < pred (length xs) → g (nth xs i,nth xs (i + 1))
definition path (g : graph V) := { xs : list V | path_pred g xs }

/- [KS]
A simple path is a path with no repeated nodes.
-/

definition simple_path_pred (g : graph V) (xs : list V) := path_pred g xs ∧ no_dup xs
definition simple_path (g : graph V) := { xs : list V | simple_path_pred g xs }

/- [KS]
A cycle is a path that starts and ends at the same node.
#DHS his definitions are inconsistent at the null path
-/

definition cycle_pred (g : graph V) (xs : list V) := path_pred g xs ∧ head xs = last xs ∧ length xs > 1
definition cycle (g : graph V) := { xs : list V | cycle_pred g xs }

/- [KS]
A simple cycle is a cycle that does not contain any duplicate nodes (except for the very last node) or
duplicate edges.
-/

definition simple_cycle_pred (g : graph V) (xs : list V) := cycle_pred g xs ∧ no_dup (all_but_last xs)
definition simple_cycle (g : graph V) := { xs : list V | simple_cycle_pred g xs }

/- [KS]
Let G be an undirected graph. Two nodes u and v are called connected iff there is a path from u to v
in G. If u and v are connected, we denote this by writing u ↔ v. If u and v are not connected, we denote
this by writing u ↮ v.
-/

variables (g : graph V)

variables {g_symmetric : ∀ (u v : V), g (u,v) → g (v,u)}

definition connected (u v : V) := ∃ xs, path_pred g xs ∧ head xs = u ∧ last xs = v
lemma connected_simple {u v : V} : connected g u v → ∃ xs, simple_path_pred g xs ∧ head xs = u ∧ last xs = v := sorry

local notation u ↔ v := connected g u v

/- [KS]
Theorem: Let G = (V, E) be an undirected graph. Then:
(1) If v ∈ V, then v ↔ v.
(2) If u, v ∈ V and u ↔ v, then v ↔ u.
(3) If u, v, w ∈ V, then if u ↔ v and v ↔ w, then u ↔ w
Proof: We prove each part independently.
To prove (1), note that for any v ∈ V, the trivial path (v) is a path from v to itself. Thus v ↔ v.
To prove (2), consider any u, v ∈ V where u ↔ v. Then there must be some path (u, x1, x2, …, xn, v).
Since G is an undirected graph, this means v, xn, …, x1, u is a path from v to u. Thus v ↔ u.
To prove (3), consider any u, v, w ∈ V where u ↔ v and v ↔ w. Then there must be paths u, x1, x2,
…, xn, v and v, y1, y2, …, ym, w. Consequently, (u, x1, …, xn, v, y1, …, ym, w) is a path from u to w.
Thus u ↔ w. 
-/

lemma not_lt_zero : ∀ n, ¬ n < 0 := sorry
definition reverse_index (xs : list V) (i : ℕ) := length xs - 1 - i
lemma reverse_length : ∀ (xs : list V), length (reverse xs) = length xs := sorry
lemma reverse_index_lt (xs : list V) {i : ℕ} : reverse_index xs i < length xs → i < length xs := sorry
lemma index_lt_reverse (xs : list V) {i : ℕ} : i < length xs → reverse_index xs i < length xs := sorry
lemma reverse_index_succ (xs : list V) (i : ℕ) : reverse_index xs (i+1) + 1 = reverse_index xs i := sorry
lemma nth_reverse : ∀ (xs : list V) {i : ℕ}, i < length xs → nth (reverse xs) i = nth xs (reverse_index xs i) := sorry
lemma reverse_index_idempotent (xs : list V) (i : ℕ) : reverse_index xs (reverse_index xs i) = i := sorry

theorem connected_refl : ∀ (v : V), v ↔ v := 
  -- To prove (1), note that for any v ∈ V, 
  take v,
  -- the trivial path (v) is a path from v to itself. 
  have v_path_v : path_pred g [v], from 
    take (i : ℕ) (i_lt_0 : i < 0), 
    absurd i_lt_0 (not_lt_zero i),
  -- Thus v ↔ v.
  show v ↔ v, from exists.intro _ (and.intro v_path_v (and.intro rfl rfl))

-- [DHS] this proof is a textbook on what kinds of obviousness we need to support
theorem connected_symm : ∀ {u v : V}, u ↔ v → v ↔ u :=
  -- To prove (2), consider any u, v ∈ V where u ↔ v. 
  take u v,
  assume u_conn_v : u ↔ v,
  -- Then there must be some path (u, x1, x2, …, xn, v).
  obtain (xs : list V) (H : path_pred g xs ∧ head xs = u ∧ last xs = v), from u_conn_v,
  have path_xs : path_pred g xs, from and.elim_left H,
  have head_xs_u : head xs = u, from and.elim_left (and.elim_right H),
  have last_xs_v : last xs = v, from and.elim_right (and.elim_right H),
  -- Since G is an undirected graph, this means v, xn, …, x1, u is a path from v to u. 
  have path_reverse_xs : path_pred g (reverse xs), from 
    take (i : ℕ) (i_lt_length_m1 : i < length (reverse xs) - 1),
    show g (nth (reverse xs) i, nth (reverse xs) (i + 1)), from

    have r_Si_lt : reverse_index xs (i+1) < length xs, from sorry,
    have r_i_lt : reverse_index xs i < length xs, from sorry,
    have r_Si_lt_pred : reverse_index xs (i+1) < pred (length xs), from sorry,
    have g_fwd : g (nth xs (reverse_index xs (i+1)), nth xs (reverse_index xs i)), from 
      reverse_index_succ xs i ▸ path_xs (reverse_index xs (i+1)) r_Si_lt_pred,

    have nth_ident_i : nth xs (reverse_index xs i) = nth (reverse xs) i, from (nth_reverse xs (reverse_index_lt xs r_i_lt))⁻¹,
    have nth_ident_ip1 : nth xs (reverse_index xs (i+1)) = nth (reverse xs) (i+1), from (nth_reverse xs (reverse_index_lt xs r_Si_lt))⁻¹,

    have g_bwd : g (nth (reverse xs) (i+1), nth (reverse xs) i), from nth_ident_i ▸ nth_ident_ip1 ▸ g_fwd,
    g_symmetric _ _ g_bwd,
     -- Thus v ↔ u.
  show v ↔ u, from exists.intro (reverse xs) 
                                (and.intro path_reverse_xs 
                                  (and.intro ((reverse_head_last xs)⁻¹ ▸ last_xs_v) (!reverse_last_head⁻¹ ▸ head_xs_u)))


lemma nth_append_first (xs ys : list V) (i : ℕ) : i < length xs → nth (xs ++ ys) i = nth xs i := sorry
lemma nth_append_second (xs ys : list V) (i : ℕ) : i ≥ length xs → nth (xs ++ ys) i = nth ys (i - length xs) := sorry
lemma lt_or_ge (i j : ℕ) : i < j ∨ i ≥ j := sorry

lemma nth_concat_lt (xs : list V) (x : V) (i : ℕ) : i < length xs → nth (concat x xs) i = nth xs i := sorry
lemma nth_concat_eq (xs : list V) (x : V) (i : ℕ) : i = length xs → nth (concat x xs) i = x := sorry


theorem connected_trans : ∀ {u v w : V}, u ↔ v → v ↔ w → u ↔ w := 
  take (u v w : V),
  assume (u_conn_v : u ↔ v) (v_conn_w : v ↔ w),

  obtain (xs : list V) (Huv : path_pred g xs ∧ head xs = u ∧ last xs = v), from u_conn_v,
  have path_xs : path_pred g xs, from and.elim_left Huv,
  have head_xs_u : head xs = u, from and.elim_left (and.elim_right Huv),
  have last_xs_v : last xs = v, from and.elim_right (and.elim_right Huv),

  obtain (ys : list V) (Hvw : path_pred g ys ∧ head ys = v ∧ last ys = w), from v_conn_w,
  have path_ys : path_pred g ys, from and.elim_left Hvw,
  have head_ys_u : head ys = v, from and.elim_left (and.elim_right Hvw),
  have last_ys_v : last ys = w, from and.elim_right (and.elim_right Hvw),

  /- [DHS]
     Lots of tricky list-surgery here. 
     - If [i < pred (length xs)], then [g (i,i+1)] follows because of [xs].
     - If [i = pred (length xs)], then [g (i,i+1)] follows because of [ys], where we use that [xs ++ tail ys = (belast xs) ++ ys]
     - If [i > pred (length xs)], then [g (i,i+1)] follows because of [ys]
   -/
     
  -- this assertion needs that [head ys = last xs]
  have path_zs_forall : ∀ ys, path_pred g ys → path_pred g (xs ++ tail ys), from 
    list.rec
      (take (path_nil : path_pred g []) (i : ℕ) (i_lt_len_app : i < pred (length (xs ++ tail nil))), 
       have i_lt_len : i < pred (length xs), from (append_nil_right xs) ▸ i_lt_len_app,
       have g_xs : g (nth xs i, nth xs (i+1)), from path_xs i i_lt_len,
       show g (nth (xs ++ []) i, nth (xs ++ []) (i+1)), from (append_nil_right xs)⁻¹ ▸ g_xs)
      (take (y : V) (ys : list V) (IHys : path_pred g ys → path_pred g (xs ++ tail ys)),
       take (path_ys : path_pred g (y :: ys)) (i : ℕ) (i_lt_len_app : i < pred (length (xs ++ ys))),
       sorry),
  sorry

open set binary eq.ops

definition set_minus [reducible] {T : Type} (A B : set T) :=   λ x, x ∈ A ∧ ¬ x ∈ B
notation a - b := set_minus a b
theorem union_com : ∀ {T : Type}, commutative (@union T) := sorry
theorem inter_com : ∀ {T : Type}, commutative (@inter T) := sorry

definition connected_component (vs : set V) := ∀ ⦃u : V⦄, u ∈ vs → ∀ {v : V}, (v ∈ vs → u ↔ v) ∧ (¬ v ∈ vs → ¬ (u ↔ v))

/- [KS]
Theorem: Let G be an undirected graph and let C1 and C2 be connected components of G. If C1 ≠ C2,
then C1 ∩ C2 = Ø.
Proof: By contradiction. Suppose that C1 and C2 are connected components of some undirected
graph G, that C1 ≠ C2, but that C1 ∩ C2 ≠ Ø. Since C1 ∩ C2 ≠ Ø, there must be some node v such that
v ∈ C1 and v ∈ C2. Furthermore, since C1 ≠ C2, there must be some node u that either u ∈ C1 or
u ∈ C2, but not both. Without loss of generality, assume that u ∈ C1 and u ∉ C2.
By the definition of a connected component, since u ∈ C1 and v ∈ C1, we know u ↔ v. Similarly, by
the definition of a connected component, since v ∈ C2 and u ∉ C2, we know that u ↮ v, contradicting
our previous assertion. We have reached a contradiction, so our assumption must have been wrong.
Thus C1 ∩ C2 = Ø, as required. 
-/

-- #TODO need to handle unpacking/coercions here...tricky!


lemma inter_nonempty_imp_elem_in_both : ∀ {C1 C2 : set V}, C1 ∩ C2 ≠ ∅ → ∃ v, v ∈ C1 ∧ v ∈ C2 := sorry
lemma inter_empty_imp_not_elem_in_both : ∀ {C1 C2 : set V}, C1 ∩ C2 = ∅ → ∀ {u:V}, u ∈ C1 → ¬ u ∈ C2 := sorry

lemma connected_components_disjoint_helper : ∀ {C1 C2 : set V}, connected_component g C1 → connected_component g C2 → (C1 ∩ C2 ≠ ∅) → ¬ (∃ u:V, u ∈ C1 - C2) :=
  take (C1 C2 : set V),
  assume (CC1 : connected_component g C1) (CC2 : connected_component g C2) (C1_overlap_C2 : C1 ∩ C2 ≠ ∅) (exists_u_in_diff : ∃ u, u ∈ C1 - C2),
  obtain (u : V) (u_in_diff : u ∈ C1 - C2), from exists_u_in_diff,
  have exists_v_in_both : ∃ v, v ∈ C1 ∩ C2, from inter_nonempty_imp_elem_in_both C1_overlap_C2,
  obtain (v : V) (v_in_both : v ∈ C1 ∩ C2), from exists_v_in_both,
  have v_conn_u : v ↔ u, from and.elim_left (CC1 (and.elim_left v_in_both)) (and.elim_left u_in_diff),
  have v_nconn_u : ¬ (v ↔ u), from and.elim_right (CC2 (and.elim_right v_in_both)) (and.elim_right u_in_diff), 
  show false, from v_nconn_u v_conn_u

theorem connected_components_disjoint : ∀ {C1 C2 : set V}, connected_component g C1 → connected_component g C2 → C1 ≠ C2 → C1 ∩ C2 = ∅ := 
  take (C1 C2 : set V),
  assume (CC1 : connected_component g C1) (CC2 : connected_component g C2) (C1_neq_C2 : C1 ≠ C2),
  by_contradiction
  (assume C1_ndisj_C2 : C1 ∩ C2 ≠ ∅,
   show false, from
   have u_in_one : (∃ u:V, u ∈ C1 - C2) ∨ (∃ u:V, u ∈ C2 - C1), from sorry,
   or.elim u_in_one 
           (take (exists_u : ∃ u, u ∈ C1 - C2), connected_components_disjoint_helper g CC1 CC2 C1_ndisj_C2 exists_u)
           (take (exists_u : ∃ u, u ∈ C2 - C1), connected_components_disjoint_helper g CC2 CC1 ((inter_com C1 C2) ▸ C1_ndisj_C2) exists_u))



/- [DHS]#DESIGN
1. Troublesome WLOG
2. Lots of painful obviousness (e.g. inter_nonempty_imp_elem_in_both)
-/

/- [KS]
Theorem: Let G = (V, E) be an undirected graph. Then for any v ∈ V, there is a connected component
C such that v ∈ C.
Proof: Let G = (V, E) be any undirected graph and let v ∈ V be an arbitrary node in the graph. Consider
the set C = { u ∈ V | u ↔ v }. We will prove C is a connected component containing v.
First, we prove that v ∈ C. To see this, note that by construction, v ∈ C iff v ↔ v. As proven earlier,
v ↔ v is always true. Consequently, v ∈ C.
Next, we prove that C is a connected component. This proof proceeds in two steps: first, we prove
that for any u1, u2 ∈ C, that u1 ↔ u2; second, we prove that for any u1 ∈ C and u2 ∈ V – C, that u1 ↮ u2.
To prove that for any u1, u2 ∈ C, that u1 ↔ u2, consider any u1, u2 ∈ C. By construction, this means
that u1 ↔ v and u2 ↔ v. As proven earlier, since u2 ↔ v, we know that v ↔ u2. Also as proven earlier,
since u1 ↔ v and v ↔ u2, this means that u1 ↔ u2.
Finally, to prove that for any u1 ∈ C and u2 ∈ V – C, that u1 ↮ u2, consider any u1 ∈ C and u2 ∈ V – C.
Assume for the sake of contradiction that u1 ↔ u2. Since u1 ∈ C, we know that u1 ↔ v. Since u1↔ u2,
we know u2 ↔ u1. Therefore, since u2 ↔ u1 and u1 ↔ v, we have that u2 ↔ v. Thus by definition of
C, this means that u2 ∈ C, contradicting the fact that u2 ∈ V – C. We have reached a contradiction, so
our assumption must have been wrong. Thus u1 ↮ u2.
Thus C is a connected component containing v. Since our choice of v and G were arbitrary, any node
in any graph belongs to at least one connected component.
-/


-- Theorem: Let G = (V, E) be an undirected graph. Then for any v ∈ V, there is a connected component C such that v ∈ C.
theorem every_node_in_connected_component : ∀ (v : V), ∃ (C : set V), connected_component g C ∧ v ∈ C :=
  -- Proof: Let G = (V, E) be any undirected graph and let v ∈ V be an arbitrary node in the graph. 
  assume (v : V),
  -- Consider the set C = { u ∈ V | u ↔ v }. 
  let C := { u : V | u ↔ v} in
  -- We will prove C is a connected component containing v.
  show connected_component g C ∧ v ∈ C, from
  -- First, we prove that v ∈ C. 
  have v_in_C : v ∈ C, from 
    -- To see this, note that by construction, v ∈ C iff v ↔ v. 
    show v ↔ v, from 
    -- As proven earlier, v ↔ v is always true. Consequently, v ∈ C.
    connected_refl g v,
  -- Next, we prove that C is a connected component.
  have C_CC : connected_component g C, from
    -- This proof proceeds in two steps: first, we prove that for any u1, u2 ∈ C, that u1 ↔ u2; second, we prove that for any u1 ∈ C and u2 ∈ V – C, that u1 ↮ u2.
    show (∀ (u1 u2 : T), u1 ∈ C → u2 ∈ C → u1 ↔ u2) ∧ (∀ (u1 u2 : T), u1 ∈ C → ¬ u2 ∈ C → ¬ u1 ↔ u2), from
    -- To prove that for any u1, u2 ∈ C, that u1 ↔ u2, 
    have all_connected : ∀ (u1 u2 : T), u1 ∈ C → u2 ∈ C → u1 ↔ u2, from
      -- consider any u1, u2 ∈ C. 
      assume (u1 u2 : T) (u1_in_C : u1 ∈ C) (u2_in_C : u2 ∈ C),
      -- By construction, this means that u1 ↔ v and u2 ↔ v. 
      have u1_conn_v : u1 ↔ v, from u1_in_C,
      have u2_conn_v : u2 ↔ v, from u2_in_C,
       -- As proven earlier, since u2 ↔ v, we know that v ↔ u2. 
       have v_conn_u2 : v ↔ u2, from connected_symm g g_symmetric u2_conn_v,
       -- Also as proven earlier, since u1 ↔ v and v ↔ u2, this means that u1 ↔ u2.
       show u1 ↔ u2, from connected_trans g u1_conn_v v_conn_u2,
     -- Finally, to prove that for any u1 ∈ C and u2 ∈ V – C, that u1 ↮ u2,
     have otherwise_not_connected : ∀ (u1 u2 : T), u1 ∈ C → ¬ u2 ∈ C → ¬ u1 ↔ u2, from
       -- consider any u1 ∈ C and u2 ∈ V – C.
       assume (u1 u2 : T) (u1_in_C : u1 ∈ C) (u2_nin_C : ¬ u2 ∈ C),
       -- Assume for the sake of contradiction that u1 ↔ u2. 
       show ¬ (u1 ↔ u2), from 
       assume u1_conn_u2 : u1 ↔ u2,
       show false, from
       -- Since u1 ∈ C, we know that u1 ↔ v. 
       have u1_conn_v : u1 ↔ v, from u1_in_C,
       -- Since u1 ↔ u2, we know u2 ↔ u1. 
       have u2_conn_u1 : u2 ↔ u1, from connected_symm g g_symmetric u1_conn_u2,
       -- Therefore, since u2 ↔ u1 and u1 ↔ v, we have that u2 ↔ v. 
       have u2_conn_v : u2 ↔ v, from connected_trans g u2_conn_u1 u1_conn_v,
       -- Thus by definition of C, this means that u2 ∈ C, 
       have u2_in_C : u2 ∈ C, from u2_conn_v, 
       -- contradicting the fact that u2 ∈ V – C. 
       show false, from absurd u2_in_C u2_nin_C,
       -- We have reached a contradiction, so our assumption must have been wrong. Thus u1 ↮ u2.
    -- Thus C is a connected component containing v. Since our choice of v and G were arbitrary, any node
    -- in any graph belongs to at least one connected component.
    show ∃ (C : set V), connected_component g C ∧ v ∈ C, from exists.intro C (and.intro CC v_in_C)
  
  
/- [KS]
Theorem: Every node in an undirected graph belongs to exactly one connected component.
Proof: <no formal proof>
-/

theorem connected_components_cover : ∀ (v : V), ∃! (C : set V), connected_component g C ∧ v ∈ C :=
  take (v : V),
  exists.elim (@every_node_in_connected_component _ _ _ g g_symmetric v)
  (
    take (C : set V) (HC : connected_component g C ∧ v ∈ C),              
    have C_unique : ∀ (D : set V), connected_component g D ∧ v ∈ D → D = C, from
      take (D : set V) (HD : connected_component g D ∧ v ∈ D),
      by_contradiction
      (
        take D_neq_C : D ≠ C,
        have D_disj_C : D ∩ C = ∅, from connected_components_disjoint g (and.elim_left HD) (and.elim_left HC) D_neq_C,
        inter_empty_imp_not_elem_in_both D_disj_C (and.elim_right HD) (and.elim_right HC)
      ),
    exists_unique.intro _ HC C_unique
  )

-- k-connectivity

-- Trees

/- [KS]
An undirected graph G is called minimally connected iff G is connected, but the removal of any edge
from G leaves G disconnected.

A graph is called acyclic iff it contains no simple cycles.
-/

definition graph_connected := ∀ (u v : V), connected g u v

definition add_edge (e : edge V) : graph V := λ (f : edge V), if e.1 = f.1 ∧ e.2 = f.2 ∨ e.1 = f.2 ∧ e.2 = f.1 then true else g f
definition remove_edge (e : edge V) : graph V := λ (f : edge V), if e.1 = f.1 ∧ e.2 = f.2 ∨ e.1 = f.2 ∧ e.2 = f.1 then false else g f
definition remove_add (e : edge V) : remove_edge (add_edge g e) e = g := sorry

lemma add_edge_contains (e : edge V) : add_edge g e e := sorry
lemma add_edge_monotone {e : edge V} : g e → ∀ (f : edge V), (add_edge g f) e := sorry
lemma edge_imp_path {e : edge V} : g e → e.1 ↔ e.2 := sorry

definition minimally_connected := graph_connected g ∧ ∀ (e : edge V), g e → ¬ graph_connected (remove_edge g e)

definition acyclic := ¬ ∃ (xs : list V), simple_cycle_pred g xs
definition maximally_acyclic := acyclic g ∧ ∀ (e : edge V), ¬ g e → ∃ (xs : list V), simple_cycle_pred (add_edge g e) xs

lemma double_negation : ∀ {P : Prop}, ¬ ¬ P → P := sorry


definition get_edge (xs : list V) (i : ℕ) : edge V := (nth xs i, nth xs (i+1))
lemma path_edge_in_graph (xs : list V) : path_pred g xs → ∀ (i : ℕ), i < pred (length xs) → g (get_edge xs i) := sorry

/- [KS]
Theorem: Let G = (V, E) be any graph containing a simple cycle C. Let u, v ∈ V be nodes in G. If
u ↔ v, then after deleting any single edge in C from graph G, it is still the case that u ↔ v.
-/

theorem simple_cycle_not_fragile : 
  ∀ {xs : list V}, simple_cycle_pred g xs → 
    ∀ (u v : V), u ↔ v →
      ∀ {i : ℕ}, i < pred (length xs) → 
        connected (remove_edge g (get_edge xs i)) u v := sorry


lemma graph_connected_w_simple_cycle_imp_not_fragile : 
  graph_connected g → 
    ∀ {xs : list V}, simple_cycle_pred g xs → 
    ∀ {i : ℕ}, i < pred (length xs) → 
    graph_connected (remove_edge g (get_edge xs i)) := sorry

theorem minimally_connected_imp_connected_and_acyclic : minimally_connected g → graph_connected g ∧ acyclic g :=
  and.rec
    (assume (g_connected : graph_connected g) (g_fragile : ∀ (e : edge V), g e → ¬ graph_connected (remove_edge g e)),
    -- Proof: By contradiction; assume that G is minimally-connected, but that it is not connected or that it is not acyclic. 
    by_contradiction
      (assume not__connected_and_acyclic : ¬ (graph_connected g ∧ acyclic g),
       have not_connected_or_not_acyclic : ¬ graph_connected g ∨ ¬ acyclic g, from prop_demorgan not__connected_and_acyclic,
       -- It cannot be the case that G is not connected, since by definition any minimally-connected graph must be connected. 
       -- So we must have that G is not acyclic, meaning that it contains a simple cycle; call it C.
       or.elim not_connected_or_not_acyclic
         (assume g_not_connected : ¬ graph_connected g, absurd g_connected g_not_connected)
         (assume g_not_acyclic : ¬ acyclic g, 
          have g_has_simple_cycle : ∃ (xs : list V), simple_cycle_pred g xs, from double_negation g_not_acyclic,
          obtain (C : list V) (C_simple_cycle : simple_cycle_pred g C), from g_has_simple_cycle,
          -- By our previous corollary, since G is connected and C is a simple cycle, we can delete any edge e ∈ C from G without disconnecting G. 
          have can_delete_edge : ∀ (i : ℕ), i < pred (length C) → graph_connected (remove_edge g (get_edge C i)), from 
            take (i : ℕ) (i_lt_pred : i < pred (length C)), 
            graph_connected_w_simple_cycle_imp_not_fragile g g_connected C_simple_cycle i_lt_pred,
         -- This contradicts the fact that G is minimally-connected.
          have C_path : path_pred g C, from and.elim_left (and.elim_left C_simple_cycle),
          absurd (can_delete_edge 0 sorry) (g_fragile (get_edge C 0) (path_edge_in_graph g C C_path 0 sorry))
      )))
    -- We have reached a contradiction, so our assumption must have been wrong. Thus if G is minimally-connected, then it must be connected and acyclic. 


/- [KS]
Theorem: If an undirected graph G is connected and acyclic, then it is maximally acyclic.
Proof: Consider any undirected, connected, acyclic graph G = (V, E). Now, consider any pair of
nodes {u, v} such that {u, v} ∉ E. We will prove that adding the edge {u, v} introduces a simple cycle.
To see this, note that since G is connected, there must be a simple path (u, x1, x2, …, xn, v) from
u to v in G. Since this path is a simple path, none of the nodes x1, x2, …, xn can be equal to either u
or v. Now, consider the graph formed by adding {u, v} to G. We can then complete the previous
simple path into a simple cycle by following this new edge from v to u, giving the simple cycle (u, x1,
x2, …, xn, v, u). Since our choice of edge was arbitrary, this proves that adding any edge to G introduces
a simple cycle. Since G is acyclic, this proves that it is maximally acyclic
-/


theorem connected_and_acyclic_imp_maximally_acyclic : graph_connected g → acyclic g → maximally_acyclic g :=
  -- Proof: Consider any undirected, connected, acyclic graph G = (V, E). 
  assume (g_connected : graph_connected g) (g_acyclic : acyclic g),
  have cannot_add_edge : ∀ (e : edge V), ¬ g e → ∃ (xs : list V), simple_cycle_pred (add_edge g e) xs, from
    -- Now, consider any pair of nodes {u, v} such that {u, v} ∉ E. We will prove that adding the edge {u, v} introduces a simple cycle.
    take (e : edge V) (e_nin_g : ¬ g e),
    -- To see this, note that since G is connected, there must be a simple path (u, x1, x2, …, xn, v) from u to v in G.
    obtain (xs : list V) (Hxs : simple_path_pred g xs ∧ head xs = e.1 ∧ last xs = e.2), from connected_simple g (g_connected e.1 e.2),
    have path_g_xs : path_pred g xs, from and.elim_left (and.elim_left Hxs),
    -- Since this path is a simple path, none of the nodes x1, x2, …, xn can be equal to either u or v. 
    have no_dup_xs : no_dup xs, from and.elim_right (and.elim_left Hxs),
    -- Now, consider the graph formed by adding {u, v} to G.
    let h : graph V := add_edge g e,
        ys : list V := concat e.1 xs
    in
    -- We can then complete the previous simple path into a simple cycle by following this new edge from v to u, giving the simple cycle (u, x1, x2, …, xn, v, u). 
    have h_simple_cycle : simple_cycle_pred h ys, from
      have no_dup_all_but_last : no_dup (all_but_last ys), from (all_but_last_concat xs e.1)⁻¹ ▸ no_dup_xs,
      have path_concat : path_pred h ys, from
        take (i : ℕ) (i_lt_pred_ys : i < pred (length ys)),
        have i_cases : i < pred (length xs) ∨ i = pred (length xs), from sorry,
        or.elim i_cases
          -- TODO this is just bookkeeping, like in [connected_symm]
          -- (nth_concat_lt xs x i_lt_pred_xs) ▸ add_edge_monotone g (path_g_xs i i_lt_pred_xs) e)
          (take i_lt_pred_xs : i < pred (length xs), sorry) 
          -- TODO need to show that first node is last and last node is first
          (take i_eq_pred_length_xs : i = pred (length xs), sorry),
      have xs_nnil : xs ≠ [], from sorry, -- I guess [path_pred] needs this condition
      have head_eq_last : head ys = last ys, from 
        have head_eq_e1 : head ys = e.1, from (head_concat xs e.1 xs_nnil)⁻¹ ▸ and.elim_left (and.elim_right Hxs),
        have last_eq_e1 : last ys = e.1, from last_concat xs e.1,
        last_eq_e1⁻¹ ▸ head_eq_e1,
      and.intro (and.intro path_concat (and.intro head_eq_last (concat_nnil_gt1 xs e.1 xs_nnil))) no_dup_all_but_last,
    exists.intro _ h_simple_cycle,
  and.intro g_acyclic cannot_add_edge
  

/- [KS]
Lemma: If G is maximally acyclic, then G is connected.
Proof: By contradiction. Suppose that G = (V, E) is a maximally acyclic graph that is not connected.
Since G is not connected, it must consist of several connected components. Choose any two of these
connected components and call them CC1 and CC2.
Now, consider any nodes u ∈ CC1 and v ∈ CC2. Since u and v are in separate connected components,
note that u ↮ v and the edge {u, v} ∉ E. So consider what happens when we add the edge {u, v} to
the graph. Since G is maximally acyclic, this must introduce a simple cycle; call it C. Since G is
acyclic, this new cycle must use the edge {u, v}. Additionally, note that since {u, v} is an edge in the
new graph, we have that u ↔ v in this new graph.
By our earlier theorem, since in this new graph u ↔ v and C is a simple cycle, if we delete any single
edge from C, it will still be the case that u ↔ v still holds. In particular, this means that if we delete
{u, v} from the new graph (which yields the original graph G), we should have that u ↔ v. But this is
impossible, since we know that u ↮ v in the original graph.
We have reached a contradiction, so our assumption must have been wrong. Thus if G is maximally
acyclic, it must be connected.
-/
check maximally_acyclic
print definition maximally_acyclic
/-
lemma graph_connected_w_simple_cycle_imp_not_fragile : 
  graph_connected g → 
    ∀ {xs : list V}, simple_cycle_pred g xs → 
    ∀ {i : ℕ}, i < pred (length xs) → 
    graph_connected (remove_edge g (get_edge xs i)) := sorry
-/

lemma maximally_acyclic_imp_connected : maximally_acyclic g → graph_connected g := 
  -- Proof: By contradiction. Suppose that G = (V, E) is a maximally acyclic graph that is not connected.
  assume (g_maximally_acyclic : maximally_acyclic g),
  by_contradiction
  (
    assume g_not_connected : ¬ graph_connected g,
    -- Since G is not connected, it must consist of several connected components. Choose any two of these connected components and call them CC1 and CC2.
    have two_connected_components : ∃ (C1 C2 : set V), connected_component g C1 ∧ connected_component g C2 ∧ C1 ≠ C2, from sorry,
    obtain (C1 C2 : set V) (H_C1C2 : connected_component g C1 ∧ connected_component g C2 ∧ C1 ≠ C2), from two_connected_components,
    -- Now, consider any nodes u ∈ CC1 and v ∈ CC2. 
    -- [DHS] even given the previous axiom, we need to prove that they are non-empty as sets,
    have node_in_C1 : ∃ (u : V), u ∈ C1, from sorry,
    obtain (u : V) (u_in_C1 : u ∈ C1), from node_in_C1,
    have node_in_C2 : ∃ (v : V), v ∈ C2, from sorry,
    obtain (v : V) (v_in_C2 : v ∈ C2), from node_in_C2,
    -- Since u and v are in separate connected components, note that u ↮ v and the edge {u, v} ∉ E. 
    have u_nconn_v : ¬ (u ↔ v), from sorry,
    have u_nedge_v : ¬ g (u,v), from sorry,
    -- So consider what happens when we add the edge {u, v} to the graph. 
    let h : graph V := add_edge g (u,v) in
    -- Since G is maximally acyclic, this must introduce a simple cycle; call it C. 
    have simple_cycle : ∃ (xs : list V), simple_cycle_pred h xs, from and.elim_right g_maximally_acyclic (u,v) u_nedge_v,
    obtain (C : list V) (C_simple_cycle : simple_cycle_pred h C), from simple_cycle,
    -- Since G is acyclic, this new cycle must use the edge {u, v}. 
    -- [DHS] tricky...
    have exists_uv_in_C : ∃ (i : ℕ) (i_lt_pred : i < pred (length C)), get_edge C i = (u,v), from sorry,
    obtain (i : ℕ) (i_lt_pred : i < pred (length C)) (uv_in_C : get_edge C i = (u,v)), from exists_uv_in_C,
    -- Additionally, note that since {u, v} is an edge in the new graph, we have that u ↔ v in this new graph.
    have uv_in_h : h (u,v), from add_edge_contains g (u,v), 
    have u_conn_v_in_h : connected h u v, from edge_imp_path h uv_in_h,
    -- By our earlier theorem, since in this new graph u ↔ v and C is a simple cycle, if we delete any single edge from C, it will still be the case that u ↔ v still holds.
    have still_connected : connected (remove_edge h (get_edge C i)) u v, from simple_cycle_not_fragile h C_simple_cycle u v u_conn_v_in_h i_lt_pred,
    -- In particular, this means that if we delete {u, v} from the new graph (which yields the original graph G), we should have that u ↔ v. 
    have was_always_connected : connected g u v, from (remove_add g (u,v)) ▸ uv_in_C ▸ still_connected,
    -- But this is impossible, since we know that u ↮ v in the original graph.
    show false, from u_nconn_v was_always_connected
  )
  -- We have reached a contradiction, so our assumption must have been wrong. Thus if G is maximally acyclic, it must be connected.

/- [KS]
Theorem: If G is maximally acyclic, then it is minimally connected.
Proof: Let G = (V, E) be any maximally acyclic graph. By the previous lemma, G is connected. We
need to show that if we remove any edge e ∈ E from G, then G becomes disconnected. To do this, we
proceed by contradiction. Suppose that there is an edge {u, v} ∈ E such that if {u, v} is removed
from G, G remains connected. In that case, we must have that after removing {u, v} from G, there is
a simple path between u and v. This means that in the original graph G, there is a simple cycle –
namely, take the simple path from u to v, then follow the edge {u, v} from v back to u. But this is
impossible, since G is maximally acyclic and thus acyclic. We have reached a contradiction, so our
assumption must have been incorrect. Thus G is minimally connected. 
-/

theorem maximally_acyclic_imp_minimally_connected : maximally_acyclic g → minimally_connected g := 
  -- Proof: Let G = (V, E) be any maximally acyclic graph. 
  assume g_maximally_acyclic : maximally_acyclic g,
  -- By the previous lemma, G is connected. 
  have g_connected : graph_connected g, from maximally_acyclic_imp_connected g g_maximally_acyclic,
  -- We need to show that if we remove any edge e ∈ E from G, then G becomes disconnected. 
  have cannot_remove : ∀ (e : edge V), g e → ¬ graph_connected (remove_edge g e), from
  -- To do this, we proceed by contradiction. 
  by_contradiction 
  (
    -- Suppose that there is an edge {u, v} ∈ E such that if {u, v} is removed from G, G remains connected. 
    assume not_forall_H : ¬ ∀ (e : edge V), g e → ¬ graph_connected (remove_edge g e), 
    have exists_edge : ∃ (e : edge V), g e ∧ graph_connected (remove_edge g e), from sorry,
    obtain (e : edge V) (He : g e ∧ graph_connected (remove_edge g e)), from exists_edge,
    have remove_connected : graph_connected (remove_edge g e), from and.elim_right He,
    -- In that case, we must have that after removing {u, v} from G, there is a simple path between u and v. 
    let u := e.1, v := e.2 in
    have u_conn_v : ∃ (xs : list V), simple_path_pred g xs ∧ head xs = u ∧ last xs = v, from sorry, --connected_simple (remove_edge g e) (remove_connected u v),
    obtain (xs : list V) (Hxs : simple_path_pred g xs ∧ head xs = u ∧ last xs = v), from u_conn_v,
    -- This means that in the original graph G, there is a simple cycle – namely, take the simple path from u to v, then follow the edge {u, v} from v back to u. 
    let ys := concat u xs in
    have no_dup_all_but_last : no_dup (all_but_last ys), from (all_but_last_concat xs e.1)⁻¹ ▸ (and.elim_right (and.elim_left Hxs)),
    have ys_simple_cycle : simple_cycle_pred g ys, from sorry, -- TODO this step require a bunch of automatable reasoning
    -- But this is impossible, since G is maximally acyclic and thus acyclic. 
    sorry
  ),
  -- We have reached a contradiction, so our assumption must have been incorrect. Thus G is minimally connected. 
  show minimally_connected g, from and.intro g_connected cannot_remove
  
/- [KS]
Theorem: Let G be an undirected graph. The following are all equivalent:
1. G is minimally connected.
2. G is connected and acyclic.
3. G is maximally acyclic.
-/



  


end path

