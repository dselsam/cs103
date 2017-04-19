import data.nat data.set
open nat set

variable {T : Type}

/-
Lemma 2: A Δ B ⊆ (A ∪ B) – (A ∩ B)
Proof of Lemma 2: We will show that for any x ∈ A Δ B, x ∈ (A ∪ B) – (A ∩ B). Consider any
x ∈ A Δ B. Then either x ∈ A and x ∉ B, or x ∈ B and x ∉ A. Assume without loss of generality that
x ∈ A and x ∉ B. Since x ∈ A, x ∈ A ∪ B. Since x ∉ B, x ∉ A ∩ B, so x ∈ (A ∪ B) – (A ∩ B). Since our
choice of x was arbitrary, we have that A Δ B ⊆ (A ∪ B) – (A ∩ B). ■
-/

definition set_minus [reducible] (A B : set T) := 
  λ x, x ∈ A ∧ ¬ x ∈ B

notation a - b := set_minus a b

example : ∀ (A B : set T) (x : T), (x ∈ A ∧ x ∉ B) ∨ (x ∈ B ∧ x ∉ A) → x ∈ A ∪ B - A ∩ B := sorry

/-
Theorem: If m and n have opposite parity, m + n is odd
Proof: Without loss of generality, assume that m is odd and n is even. Since m is odd, there exists an
integer r such that m = 2r + 1. Since n is even, there exists an integer s such that n = 2s. Then
m + n = 2r + 1 + 2s = 2(r + s) + 1. Consequently, m + n is odd. ■
-/

definition even (x : nat) := ∃ k, x = 2 * k.
definition odd (x : nat) := ∃ k, x = 2 * k + 1.

example : ∀ (m n : nat), (odd m ∧ even n) ∨ (odd n ∧ even n) → odd (m + n) := sorry

/-
Theorem: Let G be an undirected graph and let C1 and C2 be connected components of G. If C1 ≠ C2,
then C1 ∩ C2 = Ø.
Proof: By contradiction. Suppose that C1 and C2 are connected components of some undirected
graph G, that C1 ≠ C2, but that C1 ∩ C2 ≠ Ø. Since C1 ∩ C2 ≠ Ø, there must be some node v such that
v ∈ C1 and v ∈ C2. Furthermore, since C1 ≠ C2, there must be some node u that either u ∈ C1 or
u ∈ C2, but not both. Without loss of generality, assume that u ∈ C1 and u ∉ C2.
By the definition of a connected component, since u ∈ C1 and v ∈ C1, we know u ↔ v. Similarly, by
the definition of a connected component, since v ∈ C2 and u ∉ C2, we know that u ↮ v, contradicting
our previous assertion. We have reached a contradiction, so our assumption must have been wrong.
Thus C1 ∩ C2 = Ø, as required. ■
-/

-- similar to the first one
example : ∀ (C1 C2 : set T) (u : T), (u ∈ C1 ∧ u ∉ C2) ∨ (u ∈ C2 ∧ u ∉ C1) → true := sorry

/-
Theorem: Let G = (V, E) be any graph containing a simple cycle C. Let u, v ∈ V be nodes in G. If
u ↔ v, then after deleting any single edge in C from graph G, it is still the case that u ↔ v.
Proof: Consider any graph G = (V, E) with a simple cycle C = (x1, x2, …, xn, x1). Consider any u, v ∈
V such that u ↔ v. This means that there must be some simple path (u, y1, y2, …, ym, v) from u to v.
*
Now, suppose that we remove the edge {xi, xi+1} from G.
†
 We need to show that u ↔ v in this modified
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
required. ■

* We have not formally proven that u ↔ v iff there is a simple path from u to v. It's a good exercise to try to prove this result. As a hint, try using
the well-ordering principle by considering the shortest path from u to v and proving that it must be a simple path.
† It might be the case that this edge is the last edge on the cycle, which goes from xn to x1. In proofs such as this one, it is typical to allow for a
slight abuse of notation by letting xi+1 mean “the next node on the cycle,” which might not necessarily have the next index.
-/

-- Not sure why he needs a directionality of the edge at all...weird

/-
Theorem: Let G be a tree with at least one edge. If any edge is removed from G, the resulting graph
consists of two connected components that are each trees over their respective nodes.
Proof: Let G = (V, E) be a tree with at least one edge, and let {u, v} ∈ E be an arbitrary edge of G.
By our lemma, if we remove {u, v} from G, we are left with two connected components; call them Cu
and Cv, with u ∈ Cu and v ∈ Cv. Since Cu and Cv are connected components, they are connected. Consequently,
if we can show that Cu and Cv are acyclic, then we can conclude that Cu and Cv are trees.
To show that Cu and Cv are acyclic, assume for the sake of contradiction that at least one of them is
not; without loss of generality, let it be Cu. This means that there is a simple cycle contained purely
within Cu. But since all of the edges in Cu are also present in G, this means that there is a simple cycle
in G, contradicting the fact that G is a tree. We have reached a contradiction, so our assumption
must have been wrong. Thus Cu and Cv must be acyclic, and therefore are trees. ■
-/

-- example acyclic Cu ∨ acyclic Cv → false

/-
Theorem: Let T = (V, E) be a tree. If |V| = 1, then V has exactly one leaf node. Otherwise, V has at
least two leaf nodes.
Proof: By induction. Let P(n) be “any tree with n nodes has exactly one leaf if n = 1 and at least two
leaves if n ≥ 2.” We prove P(n) is true for all n ∈ ℕ⁺ by induction on n.
Assume that for some n ∈ ℕ⁺, that for all n' ∈ ℕ⁺ with n' < n, that P(n') holds and any tree with n'
nodes either has one node and exactly one leaf, or has at least two nodes and at least two leaves. We
will prove that P(n) holds in this case.
First, if n = 1, then the only tree with n nodes is one with a single isolated node. This node has no
edges connected to it, so it is a leaf. Thus P(n) holds.
Otherwise, assume that n ≥ 2 and consider any tree T with n nodes. Choose any edge of T and remove
it; this splits T into two subtrees T1 and T2. We now consider three cases about the relative
sizes of T1 and T2.
Case 1: T1 and T2 each have one node. This means that the tree T has exactly two nodes, so it has exactly
one edge. Thus each of the nodes in T are leaves, since they are incident to just one edge each,
and so T has at least two leaves.
Case 2: Both T1 and T2 have at least two nodes. By the inductive hypothesis, this means that T1 and
T2 each have two leaf nodes, meaning that there are at least four nodes in the graph that have at most
one edge touching them. When we add back to T the initial edge that we deleted, this new edge can
be incident to at most two of these nodes. Consequently, the other two nodes must still have at most
one edge incident to them, and so they are still leaves in the overall graph T. Thus T has at least two
leaves.
Case 3: One of T1 and T2 has exactly one node, and the other has at least two. Without loss of generality,
assume that T1 has one node u, and that T2 has at least two. By the inductive hypothesis, T2 has
at least two leaves. Also by the inductive hypothesis, T1's sole node u must be a leaf, and moreover it
must have no edges incident to it, because any one-node graph must have no edges. When we add
back to T the initial edge that we deleted, this edge will be incident to u and incident to at most one
of the at least two leaves from T2. This means that there are now at least two leaves in T: first, the
node u, which now has exactly one edge incident to it, and second, one of the leaves from T2 that is
not incident to the new edge. Thus T has at least two leaves.
Thus in all three cases T has at least two leaves, so P(n) holds, completing the induction. ■ 
-/

-- Another simple binary disjunction, binary commutative relation one.

/-
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

-- This one is a bit more subtle. 

--Goal: (R x y → P x y) ∧ (R y x → P y x)
--no special knowledge of x and y
--wlog assume R x y
-- this is a weird one

/-
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

--standard case: 
--m = n vs n = m

------------------------------------

--Either: 
--have an OR (wlog, assume _)
--or want to show an AND (wlog, we'll show that _) -- this one is sketchier, I am okay ignoring it for now



example : ∀ (A B : set T) (x : T), (x ∈ A ∧ x ∉ B) ∨ (x ∈ B ∧ x ∉ A) → x ∈ A ∪ B - A ∩ B := 
  assume A B x x_or_and,
  wlog x_or_and
       (assume x_in_A_nin_B : x ∈ A ∧ x ∉ B,
        show x ∈ A ∪ B - A ∩ B, from sorry)

open prod.ops

example : ∀ (A B : set T) (x : T), 
  let R := λ UV, x ∈ UV.1 ∧ x ∉ UV.2 in
  let Goal := λ 
  let Pi := _ in -- permutations on pairs
  have can_assume_generic : R (A,B) ∨ R (B,A) ↔ ∀ (pi : Pi), R (pi (A,B)),
  have suffices : ∀ pi, Goal (pi (A,B)) → Goal (A,B),
  -- replace assumption,
  assume pi RpiAB,
  show Goal (pi (A,B)),
  show Goal (A,B)
  
  
-- Binary wlog
check @or.elim
check @bool.rec

-- or.elim : ∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
-- bool.rec : Π {C : bool → Type}, C bool.ff → C bool.tt → (Π (n : bool), C n)
-- or.rec : ∀ {a b C : Prop}, (a → C) → (b → C) → a ∨ b → C

-- wlog : Π (disj : ?A ∨ ?B) (?A → ?G) : ?G
-- wlog : Π (disj : ?A ∨ ?B) (a_to_G : @?F ?T ?A) {Aok : ?F ?A = G} {Bok : ?F ?B → G} :=
  or.elim disj (eq.rec a_to_G Aok)
               (Bok ?)

-- hmm...this is confusing
-- I provide a proof of (A → C), which we can "generalize" to a proof of (∀ {?T}, ?T → ?G)
-- and then `Aok` and `Bok` can handle the conversions.


       (assume x_in_A_nin_B : x ∈ A ∧ x ∉ B,
        show x ∈ A ∪ B - A ∩ B, from sorry)
wlog := or.elim disj (F 

definition wlog : ∀ {A B C : Prop} { MysteryType1 MysteryType2 : Type } { F : Π {M1 : MysteryType1}  (M2 : M1), M2 → C }
  (disj : A ∨ B) (pf1 : F A) : C :=
  or.rec pf1 (λ b, 
      @or.elim a b c disj (@
  C a → c :=

----------------
lemma opposite_parity_sum_odd : ∀ (m n : nat), opposite_parity m n → odd (m + n) :=
  assume m n : nat,

  -- Without loss of generality, assume that m is odd and n is even.
  suffices_to_show (∀ (m n : nat), odd m ∧ even n → odd (m + n))

    (assume (lem : ∀ (m n : nat), odd m ∧ even n → odd (m + n)) 
            (m n : nat) (opp_mn : opposite_parity m n),
      or.elim opp_mn (assume H : odd m ∧ even n, lem m n H) (assume H : odd n ∧ even m, (add_comm n m) ▸ (lem n m H)))

    (take (m n : nat),
