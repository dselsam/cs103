import data.list data.set algebra.binary algebra.group classical
open nat list


definition no_dup {V : Type} : list V → Prop
| [] := true
| (x :: xs) := ¬ x ∈ xs ∧ no_dup xs

definition last {V : Type} [V_inhabited : inhabited V] : list V → V
| [] := arbitrary V
| [x] := x
| (x :: xs) := last xs

lemma reverse_last_head {V : Type} [V_inhabited : inhabited V] (xs : list V) : last (reverse xs) = head xs:= sorry
lemma reverse_head_last {V : Type} [V_inhabited : inhabited V] (xs : list V) : head (reverse xs) = last xs := sorry
lemma reverse_nil {V : Type} (xs :  list V) : xs = nil → reverse xs = nil := sorry
lemma reverse_nnil {V : Type} (xs :  list V) : xs ≠ nil → reverse xs ≠ nil := sorry

definition rcons {V : Type} : list V → V → list V 
| [] v := [v]
| (x :: xs) v := x :: (rcons xs v)

definition graph V := V → V → Prop

namespace path

section V

variables {V : Type} [V_inhabited : inhabited V]
include V_inhabited
variables (g : graph V)

/- [KS]
A path in a graph G = (V, E) is a series of nodes (v1, v2, …, vn) where for any i ∈ ℕ with 1 ≤ i < n,
there is an edge from vi to vi+1.
-/

-- this definition is not good enough
definition path (xs : list V) := ∀ i, i + 1 < length xs → g (nth xs i) (nth xs (i + 1))

/- [KS]
A simple path is a path with no repeated nodes.
-/

definition simple_path (xs : list V) := path g xs ∧ no_dup xs

/- [KS]
A cycle is a path that starts and ends at the same node.
-/

-- #DHS his definitions are inconsistent at the null path
definition cycle (xs : list V) := path g xs ∧ xs ≠ [] ∧ head xs = last xs

/- [KS]
A simple cycle is a cycle that does not contain any duplicate nodes (except for the very last node) or
duplicate edges.
-/

-- #DHS easier to exclude the first than the last
definition simple_cycle (xs : list V) := cycle g xs ∧ no_dup (tail xs)

-- 4.2 Graph Connectivity
-- 4.2.1 Connected Components

/- [KS]
Let G be an undirected graph. Two nodes u and v are called connected iff there is a path from u to v
in G. If u and v are connected, we denote this by writing u ↔ v. If u and v are not connected, we denote
this by writing u ↮ v.
-/

variables {g_symmetric : symmetric g}

-- #DHS this definition is terrible

definition path_btw (u v : V) (xs : list V) := path g xs ∧ xs ≠ nil ∧ head xs = u ∧ last xs = v
definition connected := ∀ (u v : V), ∃ xs, path_btw g u v xs

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

theorem connected_refl : ∀ (v : V), v ↔ v := 
  -- To prove (1), note that for any v ∈ V, 
  take v,
  -- the trivial path (v) is a path from v to itself. 
  have v_path_v : path_btw g v v [v], from sorry,
  -- Thus v ↔ v.
  show v ↔ v, from exists.intro _ v_path_v

theorem connected_symm : ∀ {u v : V}, u ↔ v → v ↔ u :=
  -- To prove (2), consider any u, v ∈ V where u ↔ v. 
  take u v,
  assume u_conn_v : u ↔ v,
  -- Then there must be some path (u, x1, x2, …, xn, v).
  obtain (xs : list V) (path_btw_u_v : path_btw g u v xs), from u_conn_v,
  -- Since G is an undirected graph, this means v, xn, …, x1, u is a path from v to u. 
  have g_holds : ∀ {i}, i + 1 < length xs → g (nth xs i) (nth xs (i + 1)), from and.elim_left path_btw_u_v,
  have g_holds_bwd : ∀ {i}, i + 1 < length xs → g (nth xs (i + 1)) (nth xs i), from take i i_in_bounds, g_symmetric (g_holds i_in_bounds),
  have g_holds_rev : ∀ {i}, i + 1 < length xs → g (nth (reverse xs) i) (nth (reverse xs) (i + 1)), from sorry,
  have path_btw_v_u : path_btw g v u (reverse xs), from sorry,
  -- Thus v ↔ u.
  show v ↔ u, from exists.intro _ path_btw_v_u

theorem connected_trans : ∀ {u v w : V}, u ↔ v → v ↔ w → u ↔ w :=
  -- To prove (3), consider any u, v, w ∈ V where u ↔ v and v ↔ w. 
  take u v w,
  assume (u_conn_v : u ↔ v) (v_conn_w : v ↔ w),
  -- Then there must be paths u, x1, x2, …, xn, v and v, y1, y2, …, ym, w. 
  obtain (xs : list V) (path_btw_u_v : path_btw g u v xs), from u_conn_v,
  obtain (ys : list V) (path_btw_v_w : path_btw g v w ys), from v_conn_w,
  -- Consequently, (u, x1, …, xn, v, y1, …, ym, w) is a path from u to w.
  have path_btw_u_w : path_btw g u w (xs ++ tail ys), from sorry,
  -- Thus u ↔ w. 
  show u ↔ w, from exists.intro _ path_btw_u_w
  
/- [KS]
An undirected graph G = (V, E) is called connected if for any u, v ∈ V, we have u ↔ v. If G is an
undirected graph that is not connected, we say that G is disconnected.
-/
  
definition graph_connected := ∀ (u v : V), u ↔ v
definition graph_disconnected := ¬ graph_connected g

/- [KS]
Let G = (V, E) be an undirected graph. A connected component of G is a nonempty set of nodes C
(that is, C ⊆ V), such that
(1) For any u, v ∈ C, we have u ↔ v.
(2) For any u ∈ C and v ∈ V – C, we have u ↮ v.
-/

-- #DHS could be a set, but doesn't need to be here

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

theorem every_node_in_connected_component : ∀ (v : V), ∃ (C : set V), connected_component g C ∧ v ∈ C :=
  -- Proof: Let G = (V, E) be any undirected graph and let v ∈ V be an arbitrary node in the graph. 
  take (v : V),
  -- Consider the set C = { u ∈ V | u ↔ v }. We will prove C is a connected component containing v.
  let C := (λ u, u ↔ v) in
  -- First, we prove that v ∈ C. 
  have v_in_C : v ∈ C, from 
    -- To see this, note that by construction, v ∈ C iff v ↔ v. As proven earlier, v ↔ v is always true. Consequently, v ∈ C.
    connected_refl g v,
  -- Next, we prove that C is a connected component.
  have CC : connected_component g C, from
    -- This proof proceeds in two steps: first, we prove that for any u1, u2 ∈ C, that u1 ↔ u2; second, we prove that for any u1 ∈ C and u2 ∈ V – C, that u1 ↮ u2.
    assume (u1 : V) (u1_in_C : u1 ∈ C) (u2 : V),
    and.intro 
      (-- To prove that for any u1, u2 ∈ C, that u1 ↔ u2, consider any u1, u2 ∈ C. 
       assume (u2_in_C : u2 ∈ C),
       -- By construction, this means that u1 ↔ v and u2 ↔ v. 
       have u1_conn_v : u1 ↔ v, from sorry,
       have u2_conn_v : u2 ↔ v, from sorry,
       -- As proven earlier, since u2 ↔ v, we know that v ↔ u2. 
       have v_conn_u2 : v ↔ u2, from @connected_symm _ _ g g_symmetric _ _ u2_conn_v,
       -- Also as proven earlier, since u1 ↔ v and v ↔ u2, this means that u1 ↔ u2.
       have u1_conn_u2 : u1 ↔ u2, from connected_trans g u1_conn_v v_conn_u2,
       show u1 ↔ u2, from u1_conn_u2)
      (-- Finally, to prove that for any u1 ∈ C and u2 ∈ V – C, that u1 ↮ u2, consider any u1 ∈ C and u2 ∈ V – C.
       assume (u2_nin_C : ¬ (u2 ∈ C)),
       -- Assume for the sake of contradiction that u1 ↔ u2. 
       show ¬ (u1 ↔ u2), from 
       assume u1_conn_u2 : u1 ↔ u2,
       -- Since u1 ∈ C, we know that u1 ↔ v. 
       have u1_conn_v : u1 ↔ v, from u1_in_C,
       -- Since u1 ↔ u2, we know u2 ↔ u1. 
       have u2_conn_u1 : u2 ↔ u1, from @connected_symm _ _ g g_symmetric _ _ u1_conn_u2,
       -- Therefore, since u2 ↔ u1 and u1 ↔ v, we have that u2 ↔ v. 
       have u2_conn_v : u2 ↔ v, from connected_trans g u2_conn_u1 u1_conn_v,
       -- Thus by definition of C, this means that u2 ∈ C, 
       have u2_in_C : u2 ∈ C, from u2_conn_v, 
       -- contradicting the fact that u2 ∈ V – C. 
       -- We have reached a contradiction, so our assumption must have been wrong. Thus u1 ↮ u2.
       absurd u2_in_C u2_nin_C),
  show ∃ (C : set V), connected_component g C ∧ v ∈ C, from exists.intro _ (and.intro CC v_in_C)
  
  
/- [KS]
Theorem: Every node in an undirected graph belongs to exactly one connected component.
Proof: <no formal proof>
-/
theorem connected_components_cover : ∀ (v : V), ∃! (C : set V), connected_component g C ∧ v ∈ C :=
  take (v : V),
  exists.elim (@every_node_in_connected_component _ _ g g_symmetric v)
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

/- [KS]
An undirected graph G is called minimally connected iff G is connected, but the removal of any edge
from G leaves G disconnected.

A graph is called acyclic iff it contains no simple cycles.
-/

definition remove_edge (u1 u2 : V) : graph V := 
  λ v1 v2, if u1 = v1 ∧ u2 = v2 ∨ u1 = v2 ∧ u2 = v1 then false else g v1 v2

definition minimally_connected := connected g ∧ ∀ u1 u2, ¬ connected (remove_edge g u1 u2)

definition acyclic := ¬ ∃ (xs : list V), simple_cycle g xs

/- [KS]
Theorem: If an undirected graph G is minimally-connected, then it is connected and acyclic.
Proof: By contradiction; assume that G is minimally-connected, but that it is not connected or that it
is not acyclic. It cannot be the case that G is not connected, since by definition any minimally-connected
graph must be connected. So we must have that G is not acyclic, meaning that it contains a
simple cycle; call it C. By our previous corollary, since G is connected and C is a simple cycle, we
can delete any edge e ∈ C from G without disconnecting G. This contradicts the fact that G is minimally-connected.
We have reached a contradiction, so our assumption must have been wrong. Thus
if G is minimally-connected, then it must be connected and acyclic. 
-/

lemma double_negation : ∀ {P : Prop}, ¬ ¬ P → P := sorry

-- TODO need notion of edge being in a path (This theorem is false!)
lemma connected_w_simple_cycle_imp_not_fragile : connected g → ∀ {xs : list V}, simple_cycle g xs → ∀ (u v : V), connected (remove_edge g u v) := sorry

theorem minimally_connected_imp_connected_and_acyclic : minimally_connected g → connected g ∧ acyclic g :=
  and.rec
    (assume (g_connected : connected g) (g_fragile : ∀ (u1 u2 : V), ¬ connected (remove_edge g u1 u2)),
    -- Proof: By contradiction; assume that G is minimally-connected, but that it is not connected or that it is not acyclic. 
    by_contradiction
      (assume not__connected_and_acyclic : ¬ (connected g ∧ acyclic g),
       have not_connected_or_not_acyclic : ¬ connected g ∨ ¬ acyclic g, from sorry,
       -- It cannot be the case that G is not connected, since by definition any minimally-connected graph must be connected. 
       -- So we must have that G is not acyclic, meaning that it contains a simple cycle; call it C.
       or.elim not_connected_or_not_acyclic
         (assume g_not_connected : ¬ connected g, absurd g_connected g_not_connected)
         (assume g_not_acyclic : ¬ acyclic g, 
          have g_has_simple_cycle : ∃ (xs : list V), simple_cycle g xs, from double_negation g_not_acyclic,
          obtain (C : list V) (C_simple_cycle : simple_cycle g C), from g_has_simple_cycle,
          -- By our previous corollary, since G is connected and C is a simple cycle, we can delete any edge e ∈ C from G without disconnecting G. 
          -- [DHS]TODO simple cycles contain edges
          -- [DHS]absurdity
          sorry)))
         -- This contradicts the fact that G is minimally-connected.
         -- We have reached a contradiction, so our assumption must have been wrong. Thus if G is minimally-connected, then it must be connected and acyclic. 


  
  



end V
end path
