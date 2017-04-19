import data.list data.subtype data.sigma
open subtype list prod prod.ops sigma.ops

definition edge (V : Type) := V × V
definition graph (V : Type) := edge V → Prop

definition undirected {V : Type} (g : graph V) := ∀ (u v : V), g (u,v) → g (v,u)

namespace path

variables {V : Type} [V_decidable_eq : decidable_eq V]
include V_decidable_eq

definition path : graph V → V → V → Prop := sorry
definition repeated_edges {g : graph V} {u v : V} (p : path g u v) : Prop := sorry

definition simple_path (g : graph V) (u v : V) := { p : path g u v | ¬ repeated_edges p }

definition path_contains_edge {g : graph V} {u v : V} : path g u v → edge V → Prop := sorry

lemma simple_path_nonempty (g : graph V) (u v : V) (spath : simple_path g u v) : ∃ e, g e ∧ path_contains_edge (spath.1) e

definition cycle (g : graph V) (u : V) := path g u u

definition simple_cycle (g : graph V) := Σ (u : V) (p : cycle g u), ¬ repeated_edges p

variables {g : graph V}

theorem path_refl (g : graph V) : ∀ (v : V), path g v v := sorry
theorem path_symm (g : graph V) : ∀ {u v : V}, path g u v → path g v u := sorry
theorem path_trans (g : graph V) : ∀ {u v w : V}, path g u v → path g v w → path g u w := sorry

definition graph_connected (g : graph V) := ∀ (u v : V), path g u v

definition remove_edge (g : graph V) (e : edge V) : graph V := λ (f : edge V), if f.1 = e.1 ∧ f.2 = e.2 ∨ f.1 = e.2 ∧ f.2 = e.1 then false else g f

-- An undirected graph G is called k-edge-connected iff G is connected, and there is no set of k – 1 edges that can be removed from G that disconnects it
definition two_edge_connected (g : graph V) := graph_connected g ∧ ¬ ∃ (e1 e2 : edge V), g e1 ∧ g e2 ∧ ¬ graph_connected (remove_edge (remove_edge g e1) e2)

-- A bridge in a connected, undirected graph G is an edge in G that, if removed, disconnects G.
definition has_bridge (g : graph V) : Prop := graph_connected g ∧ ∃ (e : edge V), g e ∧ ¬ graph_connected (remove_edge g e)

-- Theorem: An undirected graph G is 2-edge-connected iff it is connected and has no bridges.
theorem two_edge_connected_iff (g : graph V) : two_edge_connected g ↔ graph_connected g ∧ ¬ has_bridge g := sorry

/- [KS]
Theorem: Let G = (V, E) be any graph containing a simple cycle C. Let u, v ∈ V be nodes in G. If
u ↔ v, then after deleting any single edge in C from graph G, it is still the case that u ↔ v.

Proof: Consider any graph G = (V, E) with a simple cycle C = (x1, x2, …, xn, x1). Consider any u, v ∈
V such that u ↔ v. This means that there must be some simple path (u, y1, y2, …, ym, v) from u to v.

Now, suppose that we remove the edge {xi, xi+1} from G.  We need to show that u ↔ v in this modified
graph. We consider two cases. First, it might be the case that the edge {xi, xi+1} does not appear
on the path (u, y1, …, ym, v). In that case, the path (u, y1, …, ym, v) is a valid path from u to v in the
new graph, so u ↔ v still holds.

Second, it might be the case that the edge {xi, xi+1} appears somewhere in our original path (u, y1, …,
ym, v). Since the graph is undirected, the edge might appear as {xi, xi+1} or as {xi+1, xi} when it occurs
in the path. Assume without loss of generality that it appears as {xi, xi+1} (otherwise, we can just reverse
the ordering of the nodes in the original cycle so as to relabel the edges). This means that we
can split the original path into three smaller paths – a path from u to xi, then the edge {xi, xi+1}, and finally
a path from xi+1 to v. Thus u ↔ xi and xi+1 ↔ v. Now, since the edge {xi, xi+1} lies on the cycle
C, after deleting the edge from the cycle, there is still a path from xi to xi+1. Specifically, we can follow
the edges of the cycle in reverse from xi until we reach xi+1. In other words, in this new graph, we
must have that xi ↔ xi+1.

Since in this new graph u ↔ xi, xi ↔ xi+1, and xi+1 ↔ v, we thus have that u ↔ v in the new graph, as
required. 
-/

lemma path_imp_simple_path (g : graph V) : ∀ (u v : V), path g u v → simple_path g u v := sorry

theorem remove_edge_from_simple_cycle (g : graph V) (scycle : simple_cycle g) : ∀ (u v : V), path g u v → ∀ (e : edge V), g e → path (remove_edge g e) u v :=
  -- Proof: Consider any graph G = (V, E) with a simple cycle C = (x1, x2, …, xn, x1). 
  -- Consider any u, v ∈ V such that u ↔ v. 
  take (u v : V) (u_conn_v : path g u v),
  -- This means that there must be some simple path (u, y1, y2, …, ym, v) from u to v.
  have u_sconn_v : simple_path g u v, from path_imp_simple_path u_conn_v,
  -- Now, suppose that we remove the edge {xi, xi+1} from G.  
  let G' := remove_edge g in
  

/-We need to show that u ↔ v in this modified
graph. We consider two cases. First, it might be the case that the edge {xi, xi+1} does not appear
on the path (u, y1, …, ym, v). In that case, the path (u, y1, …, ym, v) is a valid path from u to v in the
new graph, so u ↔ v still holds.
-/


end path



