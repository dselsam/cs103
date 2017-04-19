-- Keith
-- Chapter 2

import data.fin data.list algebra.binary algebra.group classical

open nat fin list

definition no_dup {V : Type} : list V → Prop
| [] := true
| (x :: xs) := ¬ x ∈ xs ∧ no_dup xs

definition rcons {V : Type} : list V → V → list V 
| [] v := [v]
| (x :: xs) v := x :: (rcons xs v)

lemma rcons_reverse {V : Type} (u : V) (xs : list V) : reverse (u :: xs) = rcons (reverse xs) u := sorry

definition relation V := V → V → Prop
-- definition graph n := relation (fin n)

definition graph V := relation V -- for now, until we need finiteness
section V

variables {V : Type} (g : graph V)
variables [V_decidable : decidable_eq V]
variables [g_decidable : decidable_rel g]

include V_decidable g_decidable

inductive path : V → list V → V → Prop :=
| edge : ∀ {x y}, g x y → path x [] y
| trans : ∀ {x xs1 y xs2 z}, path x xs1 y → path y xs2 z → path x (xs1 ++ (y :: xs2)) z

-- There must be an easier way to do this!

/-
theorem decidable_path [instance] : ∀ (x_start : V) (xs : list V) (x_end : V), decidable (path g x_start xs x_end)
| x_start [] x_end := decidable.rec_on (prop_decidable (x_start = x_end)) (take yes, decidable.inl yes) (take no, decidable.inr no)
| x_start (x :: xs) x_end := decidable.rec_on (prop_decidable (g x_start x ∧ path g x xs x_end)) (take yes, decidable.inl yes) (take no, decidable.inr no)

definition simple {x_start : V} {xs : list V} {x_end : V} (p : path g x_start xs x_end) : Prop := 
  no_dup (x_start :: xs)

definition cycle {x_start : V} {xs : list V} {x_end : V} (p : path g x_start xs x_end) : Prop := 
  x_start = x_end

definition simple_cycle {x_start : V} {xs : list V} {x_end : V} (p : path g x_start xs x_end) : Prop := 
  (simple g p) ∧ (cycle g p)
-/

definition connected (u v : V) := u = v ∨ ∃ xs, path g u xs v

/- [KS]
Theorem: Let G = (V, E) be an undirected graph. Then:
(1) If v ∈ V, then v ↔ v.
(2) If u, v ∈ V and u ↔ v, then v ↔ u.
(3) If u, v, w ∈ V, then if u ↔ v and v ↔ w, then u ↔ w.
Proof: We prove each part independently.
To prove (1), note that for any v ∈ V, the trivial path (v) is a path from v to itself. Thus v ↔ v.
To prove (2), consider any u, v ∈ V where u ↔ v. Then there must be some path (u, x1, x2, …, xn, v).
Since G is an undirected graph, this means v, xn, …, x1, u is a path from v to u. Thus v ↔ u.
To prove (3), consider any u, v, w ∈ V where u ↔ v and v ↔ w. Then there must be paths u, x1, x2,
…, xn, v and v, y1, y2, …, ym, w. Consequently, (u, x1, …, xn, v, y1, …, ym, w) is a path from u to w.
Thus u ↔ w. 
-/

local notation a ↔ b := @connected V g V_decidable g_decidable a b
variable [g_undirected : symmetric g]
open eq.ops

theorem connected_refl : ∀ (v : V), v ↔ v := take v, or.inl rfl

lemma path_edge_inv : ∀ (u v : V), path g u [] v → g u v :=
  
check @path.edge
lemma path_reverse {xs : list V} : ∀ {u v : V}, path g u xs v → path g v (reverse xs) u :=
  list.induction_on 
    xs
    (show ∀ (u v : V), path g u [] v → path g v [] u, from 
     take (u v : V),
     assume (u_path_v : path g u [] v),
     path.cases_on u_path_v
                   _
                   _)
    sorry

/-
    (take (x : V) (xs : list V),
     assume (IHxs : ∀ {u v : V}, path g u xs v → path g v (reverse xs) u),
     show ∀ (u v : V), path g u (x :: xs) v → path g v (reverse (x :: xs)) u, from
     take (u v : V),
     assume (u_path_v : path g u (x :: xs) v),
     have g_u_x : g u x, from and.elim_left u_path_v,
     have x_path_v : path g x xs v, from and.elim_right u_path_v,
     have v_path_x : path g v (reverse xs) x, from IHxs x_path_v,
     have g_x_u : g x u, from g_undirected g_u_x,
     have x_path_u : path g x [] u, from 
     have v_path_u : path g v (reverse xs) x) u, from rcons_path g v_path_x g_x_u,
     show path g v (reverse (x :: xs)) u, from (rcons_reverse x xs)⁻¹ ▸ v_path_u)
-/

theorem connected_sym : ∀ (u v : V), u ↔ v → v ↔ u :=
  take u v,
  assume u_conn_v : u ↔ v,
  or.elim u_conn_v
          (take u_eq_v : u = v, or.inl u_eq_v⁻¹)
          (take H_uv : ∃ xs, path g u xs v,
           obtain xs (u_path_v : path g u xs v), from H_uv,
           have v_path_u : path g v (reverse xs) u, from @path_reverse V g V_decidable g_decidable g_undirected xs u v u_path_v,
           or.inr (exists.intro _ v_path_u))


lemma path_reverse_nil (u v : V) : ¬ path g u [] v := λ H,H
lemma path_reverse_one (x u v : V) (u_path_v : path g u [x] v) : path g v [x] u := iff.elim_left and.comm u_path_v



lemma path_reverse (xs : list V) : ∀ (u v : V), path g u xs v → path g v (reverse xs) u :=
  list.induction_on xs
                (take (u v : V),
                 assume (u_path_v : path g u [] v),
                 false.rec _ u_path_v)
                (take (x1 : V) (xs : list V),
                 assume (IHxs : ∀ (u v : V), path g u xs v → path g v (reverse xs) u),
                 show ∀ (u v : V), path g u (x1 :: xs) v → path g v (reverse (x1 :: xs)) u, from 
                 list.cases_on xs
                               (take (u v : V),
                                assume (u_path_v : path g u [x1] v),
                                show path g v [x1] u, from iff.elim_left and.comm u_path_v)
                               (take (x2 : V) (xs : list V),
                                take (u v : V),
                                list.cases_on xs 
                                  (assume u_path_v : path g u [x1,x2] v, show path g v [x2,x1] u, from sorry)
                                  (take (x3 : V) (xs : list V), 
                                   assume (u_path_v : path g u (x1 :: x2 :: x3 :: xs) v),
                                have H_u_path_v : u = x1 ∧ g x1 x2 ∧ path g x2 (x2 :: xs) v, from u_path_v,
                                have u_eq_x2 : u = x1, from and.elim_left H_u_path_v,
                                have g_x2_x1 : g x1 x2, from and.elim_left (and.elim_right H_u_path_v),
                                have g_x1_x2 : g x2 x1, from g_undirected g_x2_x1,
                                have x2_path_v : path g x2 (x2 :: x3 :: xs) v, from and.elim_right (and.elim_right H_u_path_v),

                                have v_path_x2 : path g v (reverse (x2 :: xs)) x2, from IHxs x2 v x2_path_v,
                                have v_path_x1 : path g v (rcons (reverse (x2 :: xs)) x1) x1, from rcons_path v_path_x2 g_x2_x1,
                                show path g v (reverse (x2 :: x1 :: xs)) u, from (rcons_reverse x2 (x1 :: xs))⁻¹ ▸ v_path_x2))


/-
                                    have x1_path_v : path g x1 (x1 :: xs) v, from and.elim_right (and.elim_right H_u_path_v),



                
-/

theorem graph_theorems1b_dep : ∀ (u v : V), u ↔ v → v ↔ u :=
  -- To prove (2), consider any u, v ∈ V where u ↔ v. 
  take u v,
  assume u_conn_v : u ↔ v,
  -- Then there must be some path (u, x1, x2, …, xn, v).
  obtain (xs : list V) (u_path_v : path g u xs v), from u_conn_v,
  -- Since G is an undirected graph, this means v, xn, …, x1, u is a path from v to u. 
  have v_conn_u : ∀ (u v : V), path g u xs v → path g v (reverse xs) u, from 
    list.induction_on xs
                      (take (u v : V),
                       assume (u_path_v : path g u [] v),
                       false.rec _ u_path_v)
                      (take (x : V) (xs : list V),
                       assume IHxs : ∀ (u v : V), path g u xs v → path g v (reverse xs) u,
                       take (u v : V),
                       assume u_path_v : path g u (x :: xs) v,
                       show path g v (reverse (x :: xs)) u, from sorry),

  -- Thus v ↔ u.
  show v ↔ u, from exists.intro _ (v_conn_u _ _ u_path_v)
  











end V
