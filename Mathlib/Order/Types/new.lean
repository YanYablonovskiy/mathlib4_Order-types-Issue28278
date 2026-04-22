/-
Copyright (c) 2025 Yan Yablonovskiy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yan Yablonovskiy
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Combinatorics.SimpleGraph.Tutte
public import Mathlib.Combinatorics.SimpleGraph.Trails
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
/-!
# Petersen's 2-Factor Theorem

## Main definitions

* `SimpleGraph.IsBridgeless`: a connected graph with no bridge edges.
* `SimpleGraph.IsTwoFactor`: a spanning subgraph where every vertex has degree exactly 2.
* `SimpleGraph.IsKFactor`: a spanning subgraph where every vertex has degree exactly `k`.

## Main results

* `SimpleGraph.exists_twoFactor_of_isRegularOfDegree_even`: **Petersen's 2-Factor Theorem** —
  every 2k-regular graph (k ≥ 1) on a finite vertex set has a 2-factor.

## Overview of the proof

The classical proof proceeds by strong induction on `k`:

**Base case** (`k = 1`): A 2-regular graph is itself a 2-factor (it is a union of disjoint cycles).

**Inductive step** (`k ≥ 2`, assuming the result for `k - 1`):
Given a 2k-regular graph `G`:

1. **Euler circuit**: Since `G` is connected and every vertex has even degree, `G` has an Euler
   circuit `C`. (If `G` is disconnected, apply the argument to each connected component.)

2. **Orient the circuit**: Walk along `C` and orient each edge in the direction of traversal.
   This gives each vertex in-degree `k` and out-degree `k`.

3. **Construct a bipartite graph**: Create a bipartite graph `B` with two copies of the vertex
   set — "out-copies" `v⁺` and "in-copies" `v⁻`. For each edge `(u, v)` in the oriented circuit,
   add the edge `{u⁺, v⁻}` in `B`. Every `v⁺` has degree `k` and every `v⁻` has degree `k`,
   so `B` is `k`-regular bipartite.

4. **Perfect matching**: By König's theorem (or Hall's marriage theorem, since `B` is regular
   bipartite), `B` has a perfect matching `M`.

5. **Lift to 2-factor**: The matching `M` in `B` corresponds to a set of `|V|` edges in `G`
   (one outgoing edge per vertex, one incoming edge per vertex). This gives a spanning subgraph
   of `G` where every vertex has degree exactly 2 — a 2-factor `F`.

6. **Recurse**: The remaining graph `G - F` is `2(k-1)`-regular. By the induction hypothesis
   (for `k - 1`), `G - F` has a 2-factor. Together with `F`, this decomposes `G` into `k`
   edge-disjoint 2-factors.

## References

* [Petersen, J., "Die Theorie der regulären graphs", *Acta Math.* **15** (1891), 193–220]
* [Diestel, R., *Graph Theory*, 5th ed., Springer, 2017, Theorem 2.1.3]
* <https://en.wikipedia.org/wiki/2-factor_theorem>

## Tags

2-factor, Petersen, regular graph, Euler circuit, perfect matching, graph factorization
-/

open SimpleGraph Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]


/-! ### Bridgeless graphs -/

/-- A graph is *bridgeless* if it has no bridge edges. Equivalently, it is 2-edge-connected:
removing any single edge leaves the graph connected. -/
def IsBridgeless : Prop :=
  ∀⦃v1 v2 : V⦄, s(v1,v2) ∈ G.edgeSet → ¬G.IsBridge s(v1,v2)


-- SimpleGraph.connected_iff_exists_forall_reachable @ Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
-- {V : Type u} (G : SimpleGraph V) : G.Connected ↔ ∃ v, ∀ (w : V), G.Reachable v w

-- SimpleGraph.Connected.exists_isPath @ Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
-- {V : Type u} {G : SimpleGraph V} (h : G.Connected) (u v : V) : ∃ p, p.IsPath

-- SimpleGraph.isBridge_iff_mem_and_forall_cycle_notMem @ Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
-- {V : Type u} {G : SimpleGraph V}
-- {e : Sym2 V} : G.IsBridge e ↔ e ∈ G.edgeSet ∧ ∀ ⦃u : V⦄
-- (p : G.Walk u u), p.IsCycle → e ∉ p.edges

-- SimpleGraph.le_minDegree_of_forall_le_degree @ Mathlib.Combinatorics.SimpleGraph.Finite
-- {V : Type u_1} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] [Nonempty V] (k : ℕ)
-- (h : ∀ (v : V), k ≤ G.degree v) : k ≤ G.minDegree

-- SimpleGraph.degree_le_card_edgeFinset @ Mathlib.Combinatorics.SimpleGraph.Finite
-- {V : Type u_1} (G : SimpleGraph V) (v : V) [Fintype ↑(G.neighborSet v)] [Fintype ↑G.edgeSet] :
-- G.degree v ≤ G.edgeFinset.card


/-
SimpleGraph.Adj.toWalk @ Mathlib.Combinatorics.SimpleGraph.Walk.Basic
{V : Type u} {G : SimpleGraph V} {u v : V} (h : G.Adj u v) : G.Walk u v

SimpleGraph.mem_edgeSet @ Mathlib.Combinatorics.SimpleGraph.Basic
{V : Type u} (G : SimpleGraph V) {v w : V} : s(v, w) ∈ G.edgeSet ↔ G.Adj v w

-/

open SimpleGraph

#check SimpleGraph.minDegree
--exists_minimal_degree_vertex, minDegree_le_degree and le_minDegree_of_forall_le_degree.
#check exists_minimal_degree_vertex -- ∃ v, G.minDegree = G.degree v
#check minDegree_le_degree --G.minDegree ≤ G.degree v
#check le_minDegree_of_forall_le_degree -- (k : ℕ) (h : ∀ (v : V), k ≤ G.degree v) : k ≤ G.minDegree
#check commonNeighbors
#check SimpleGraph.neighborSet
#check SimpleGraph.isBridge_iff_adj_and_not_isEdgeConnected_two
#check Sym2

#check SimpleGraph.Walk.head_edges_eq_mk_start_snd

/-
Other way:
theorem isBridge_iff {u v : V} :
G.IsBridge s(u, v) ↔ G.Adj u v ∧ ¬(G.deleteEdges {s(u, v)}).Reachable u v := Iff.rfl

SimpleGraph.connected_iff_exists_forall_reachable @ Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
{V : Type u} (G : SimpleGraph V) : G.Connected ↔ ∃ v, ∀ (w : V), G.Reachable v w

SimpleGraph.Adj.reachable @ Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
{V : Type u} {G : SimpleGraph V} {u v : V} (h : G.Adj u v) : G.Reachable u v




Show (G.deleteEdges {s(u, v)}).Reachable u v from reachable u v3 and reachable v3 v ?
-/

/-
SimpleGraph.Walk.IsPath.of_append_left @ Mathlib.Combinatorics.SimpleGraph.Paths
{V : Type u} {G : SimpleGraph V} {u v w : V} {p : G.Walk u v} {q : G.Walk v w} : (p.append q).IsPath → p.IsPath

SimpleGraph.Walk.IsPath.of_append_right @ Mathlib.Combinatorics.SimpleGraph.Paths
{V : Type u} {G : SimpleGraph V} {u v w : V} {p : G.Walk u v} {q : G.Walk v w} (h : (p.append q).IsPath) : q.IsPath


-/
#check Nat.not_lt_of_ge
#check Nat.pos_iff_ne_zero
#check Nat.two_pos  -- 0 < 2
#check Nat.one_pos
#check Nat.one_lt_two
#check minDegree_le_degree --  2 ≤ G.degree inst.some
#check Walk.IsPath
#check Nat.lt_of_le_of_lt
#check G.isTree_iff.mpr

lemma nonempty_of_deg_ge_two (hdeg : 2 ≤ G.minDegree) : Nonempty V :=
  Classical.not_not.mp <| fun he ↦
    have := not_nonempty_iff.mp he
    Nat.not_lt_of_ge (Eq.subst (motive := fun n ↦ 2 ≤ n) G.minDegree_of_isEmpty hdeg) two_pos

lemma nontrivial_of_degree_ge_two (hdeg : 2 ≤ G.minDegree) : Nontrivial V :=
  G.nontrivial_of_degree_ne_zero (v := (G.nonempty_of_deg_ge_two hdeg).some)
    (by grind [hdeg.trans (G.minDegree_le_degree (G.nonempty_of_deg_ge_two hdeg).some)])

/-- A connected graph with minimum degree ≥ 2 is NOT acyclic. -/
lemma IsBridgeless.of_connected_minDegree_ge_two (hconn : G.Connected)
    (hdeg : 2 ≤ G.minDegree) : ¬G.IsAcyclic := fun hacyc ↦
  have := G.nontrivial_of_degree_ge_two hdeg;
  Nat.not_lt_of_ge (Eq.subst (motive := fun n ↦ 2 ≤ n)
    (G.isTree_iff.mpr ⟨hconn,hacyc⟩).minDegree_eq_one_of_nontrivial hdeg) Nat.one_lt_two


  -- intro v1 v2 he hbr
  -- --rw [SimpleGraph.isBridge_iff_mem_and_forall_cycle_notMem] at hbr

  -- obtain ⟨v3,hv3⟩ := Finset.exists_mem_ne (s := (G.neighborFinset v1)) (by have := hnb v1; grind) v2
  -- rw [mem_neighborFinset] at hv3
  -- let adj_walk_2 := @Walk.cons V G v1 v3 v3 hv3.1 .nil
  -- have adj_p := Walk.IsPath.of_adj hv3.1 --not linked to adj_walk_2 anymore?
  /-
  SimpleGraph.Connected.exists_isPath @ Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
  {V : Type u} {G : SimpleGraph V} (h : G.Connected) (u v : V) : ∃ p, p.IsPath

  SimpleGraph.card_neighborFinset_eq_degree @ Mathlib.Combinatorics.SimpleGraph.Finite
{V : Type u_1} (G : SimpleGraph V) (v : V) [Fintype ↑(G.neighborSet v)] : (G.neighborFinset v).card = G.degree v
  -/


  /-

  Finset.one_lt_card @ Mathlib.Data.Finset.Card
  {α : Type u_1} {s : Finset α} : 1 < s.card ↔ ∃ a ∈ s, ∃ b ∈ s, a ≠ b

  Finset.card_eq_two @ Mathlib.Data.Finset.Card
  {α : Type u_1} {s : Finset α} [DecidableEq α] : s.card = 2 ↔ ∃ x y, x ≠ y ∧ s = {x, y}
  Finset.exists_mem_ne @ Mathlib.Data.Finset.Card
  {α : Type u_1} {s : Finset α} (hs : 1 < s.card) (a : α) : ∃ b ∈ s, b ≠ a
  Finset.two_lt_card @ Mathlib.Data.Finset.Card
  {α : Type u_1} {s : Finset α} : 2 < s.card ↔ ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, a ≠ b ∧ a ≠ c ∧ b ≠ c
  -/
  -- obtain ⟨w3,hp⟩ := Connected.exists_isPath hconn v3 v2
  -- have final_path := adj_walk_2.append w3
  -- have hf : s(v1, v2) ∉ final_path.edges := sorry
  -- exact (hf ((isBridge_iff_adj_and_forall_walk_mem_edges.mp hbr).2 final_path)).elim
  -- A bridge `s(u, v)` forces all paths from `u` to `v` to use that edge.
  -- But `u` has degree ≥ 2, so there is another neighbor `w ≠ v` of `u`.
  -- Since `G` is connected, there is a path from `w` to `v` in `G`.
  -- That path together with `u—w` gives a walk from `u` to `v` not using `s(u, v)`.
  -- This contradicts the bridge property.

/-! ### k-factors and 2-factors -/

/-- A *k-factor* of `G` is a spanning subgraph in which every vertex has degree exactly `k`.

For `k = 1`, a 1-factor is a perfect matching.
For `k = 2`, a 2-factor is a union of vertex-disjoint cycles covering all vertices. -/
structure IsKFactor (H : Subgraph G) (k : ℕ) [∀ v, Fintype (H.neighborSet v)] : Prop where
  spanning : H.IsSpanning
  degree_eq : ∀ v : V, H.degree v = k

/-- A *2-factor* of `G` is a spanning subgraph in which every vertex has degree exactly 2. -/
abbrev IsTwoFactor (H : Subgraph G) [∀ v, Fintype (H.neighborSet v)] : Prop := G.IsKFactor H 2

/-- A 1-factor is the same as a perfect matching. -/
lemma isKFactor_one_iff_isPerfectMatching {H : Subgraph G} [∀ v, Fintype (H.neighborSet v)] :
    G.IsKFactor H 1 ↔ H.IsPerfectMatching := by
  constructor
  · intro ⟨hsp, hdeg⟩
    rw [Subgraph.isPerfectMatching_iff_forall_degree]
    exact fun v => hdeg v
  · intro hpm
    exact ⟨hpm.2, fun v => (Subgraph.isPerfectMatching_iff_forall_degree.mp hpm) v⟩

/-- The `spanningCoe` of a 2-factor satisfies `IsCycles`. -/
lemma IsTwoFactor.isCycles {H : Subgraph G} (hf : G.IsTwoFactor H) :
    H.spanningCoe.IsCycles := by
  intro v hv
  -- `IsCycles` says: if `v` has a neighbor, then `v` has exactly 2 neighbors.
  -- A 2-factor has every vertex with degree 2 in the subgraph.
  -- If `(neighborSet v).Nonempty` in `H.spanningCoe`, then `H.degree v = 2`,
  -- and this translates to `ncard (neighborSet v) = 2` in `H.spanningCoe`.
  sorry

/-! ### Even-degree connected graphs have Euler circuits -/

/-
SimpleGraph.Walk.fst_mem_support_of_mem_edges @ Mathlib.Combinatorics.SimpleGraph.Walk.Operations
{V : Type u} {G : SimpleGraph V} {t u v w : V} (p : G.Walk v w) (he : s(t, u) ∈ p.edges) :
 t ∈ p.support
-/

lemma SimpleGraph.Walk.not_mem_edges_of_not_fst_mem_support
   {V : Type*} {G : SimpleGraph V} {t u v w : V} (p : G.Walk v w) (hts : t ∉ p.support) :
   s(t, u) ∉ p.edges := by
   contrapose hts
   exact p.fst_mem_support_of_mem_edges hts

#check mem_support
lemma SimpleGraph.not_edge_of_not_support {G : SimpleGraph V} (u v : V): u ∉ G.support → s(u ,v) ∉ G.edgeSet := by
  intro hc
  simp
  rw [mem_support] at hc
  push Not at hc
  exact hc v



#check Set.diff_eq
lemma test_1 {G' : SimpleGraph V} [∀ u , Fintype ↑((G.deleteEdges G'.edgeSet).neighborSet u)]
    {u : V} (hni : u ∉ G'.support) :
    (G.deleteEdges G'.edgeSet).neighborFinset u = G.neighborFinset u  := by
  ext v
  rw [G.mem_neighborFinset]
  have (v : V) := @G.deleteEdges_adj _ u v (s := G'.edgeSet)
  constructor
  · intro hv
    rw [(G.deleteEdges G'.edgeSet).mem_neighborFinset] at hv
    exact (this v).mp hv |>.1
  · intro adj
    rw [(G.deleteEdges G'.edgeSet).mem_neighborFinset]
    --have := G'.degree_eq_zero_iff_notMem_support
    exact (this v).mpr ⟨adj, G'.not_edge_of_not_support u v hni⟩

#check SimpleGraph.degree_eq_zero

open Classical in
example {G' : SimpleGraph V} [∀ u , Fintype ↑((G.deleteEdges G'.edgeSet).neighborSet u)]
    {u : V} (hni : u ∉ G'.support) :
    (G.deleteEdges G'.edgeSet).neighborFinset u = G.neighborFinset u \ G'.neighborFinset u  := by
  ext v
  have (v : V) := @G.deleteEdges_adj _ u v (s := G'.edgeSet)
  constructor
  · intro hv
    rw [(G.deleteEdges G'.edgeSet).mem_neighborFinset] at hv
    have := (this v).mp hv |>.1
    rw [Finset.sdiff_eq_inter_compl]
    apply mem_inter_of_mem
    · simp [this]
    · have := G'.degree_eq_zero_iff_notMem_support u |>.mpr hni
      have := G'.degree_eq_zero u |>.mp this
      have := this.neighborFinset_eq_empty
      simp [this]
  · intro adj
    rw [(G.deleteEdges G'.edgeSet).mem_neighborFinset]
    rw [Finset.sdiff_eq_inter_compl] at adj

    --have := G'.degree_eq_zero_iff_notMem_support
    exact (this v).mpr ⟨sorry, G'.not_edge_of_not_support u v hni⟩

open Classical in
example {G' : SimpleGraph V} [∀ u , Fintype ↑((G.deleteEdges G'.edgeSet).neighborSet u)]
    {u : V} :
    (G.deleteEdges G'.edgeSet).neighborFinset u = G.neighborFinset u \ G'.neighborFinset u  := by
  -- ext v
  -- have (v : V) := @G.deleteEdges_adj _ u v (s := G'.edgeSet)
  by_cases hni : u ∉ G'.support
  · have := test_1 G hni
    rw [this]
    suffices he : G'.neighborFinset u = ∅ by simp [he]
    have := G'.degree_eq_zero_iff_notMem_support u |>.mpr hni
    have := G'.degree_eq_zero u |>.mp this
    have := this.neighborFinset_eq_empty
    exact this
  · push Not at hni
    rw [Finset.sdiff_eq_inter_compl]
    ext v
    have (v : V) := @G.deleteEdges_adj _ u v (s := G'.edgeSet)
    constructor
    · intro hv
      rw [(G.deleteEdges G'.edgeSet).mem_neighborFinset] at hv
      apply mem_inter_of_mem
      · simp [(this v).mp hv |>.1]
      · have t:= (this v).mp hv |>.2
        rw [mem_compl]
        simpa [t]
    ·




-- example {v : V} {W : G.Walk v v} (hW : W.IsCycle)
--     [∀ u , Fintype ↑((G.deleteEdges W.edgeSet).neighborSet u)] (u : V):
--     (G.deleteEdges W.edgeSet).degree u = if u ∈ W.support then
--     G.degree u - 2 else G.degree u := by
--   by_cases hs : u ∈ W.support
--   · simp [hs]
--     rw [SimpleGraph.degree,SimpleGraph.degree] at *

--   · have (v : V) := @G.deleteEdges_adj _ u v (s := W.edgeSet)
--     simp [hs]
--     rw [SimpleGraph.degree,SimpleGraph.degree] at *
--     have : (G.deleteEdges W.edgeSet).neighborFinset u = G.neighborFinset u := by
--       ext v
--       rw [G.mem_neighborFinset]
--       constructor
--       · intro hv
--         rw [(G.deleteEdges W.edgeSet).mem_neighborFinset] at hv
--         exact (this v).mp hv |>.1
--       · intro adj
--         rw [(G.deleteEdges W.edgeSet).mem_neighborFinset]
--         exact (this v).mpr ⟨adj, W.not_mem_edges_of_not_fst_mem_support hs⟩
--     rw [this]




#check SimpleGraph.induce

open Classical in
/-- Removing the edges of a closed trail from a graph preserves even-degree parity at every
vertex. More precisely, if every vertex of `G` has even degree and `W` is a circuit in `G`,
then every vertex of `G.deleteEdges W.edgeSet` has even degree. -/
lemma even_degree_deleteEdges_of_circuit
    {v : V} {W : G.Walk v v} (hW : W.IsCycle)
    (heven : ∀ u : V, Even (G.degree u)) :
    ∀ u : V, Even ((G.deleteEdges W.edgeSet).degree u) := by
  -- Each vertex u appears as an endpoint of edges in W an even number of times
  -- (since W is a closed trail, it enters and leaves u equally often).
  -- So degree_G(u) - degree_W(u) is even − even = even.
  sorry

/-- If `W` is a non-Eulerian closed trail in a connected graph `G` with all even degrees,
then there exists a vertex `u ∈ W.support` that is incident to an edge of `G` not in `W`.
This is because `G` is connected and `W` does not cover all edges. -/
lemma exists_support_adj_not_in_trail
    {v : V} {W : G.Walk v v} (hW : W.IsCircuit)
    (hconn : G.Connected) (hne : ¬W.IsEulerian) :
    ∃ u ∈ W.support, ∃ w : V,
      G.Adj u w ∧ s(u, w) ∉ W.edges := by
  -- Since W is not Eulerian, there exists an edge e ∈ G.edgeSet \ W.edgeSet.
  -- Since G is connected, there is a path from some vertex of W to an endpoint of e.
  -- Along this path, there must be a first edge not in W, incident to a vertex of W.
  sorry

/-- Given a circuit `W : G.Walk v v` and a circuit `W' : G'.Walk u u` in the graph
`G' = G.deleteEdges W.edgeSet` where `u ∈ W.support`, we can splice `W'` into `W`
at `u` to produce a strictly longer circuit in `G`. -/
lemma exists_longer_circuit_of_splice
    {v : V} {W : G.Walk v v} (hW : W.IsCircuit)
    {u : V} (hu : u ∈ W.support)
    {W' : (G.deleteEdges W.edgeSet).Walk u u} (hW' : W'.IsCircuit) :
    ∃ (w : V) (C : G.Walk w w), C.IsCircuit ∧
      W.length < C.length ∧ C.IsTrail := by
  -- Rotate W to start at u: W_rot = rotate W u hu.
  -- Map W' back to G via the inclusion G.deleteEdges _ ≤ G.
  -- The spliced walk is: W'_in_G ++ W_rot (as a walk u → u).
  -- This is a trail because W and W' have disjoint edge sets.
  -- Its length = W.length + W'.length > W.length since W' ≠ nil.
  sorry

/-- **Euler's Theorem**: In a connected graph where every vertex has even degree,
there exists an Eulerian circuit (a closed walk traversing every edge exactly once).

The proof proceeds by strong induction on the number of edges:

**Base case** (0 edges): The trivial walk `nil` at any vertex is vacuously Eulerian.

**Inductive step**: Among all closed trails in `G`, pick one of maximum length `W`.
We claim `W` is Eulerian. If not:
1. The residual graph `G' = G − E(W)` has all even degrees (removing a closed trail
   preserves degree parity).
2. Since `G` is connected and `W` is not Eulerian, some vertex `u ∈ W.support` is
   adjacent (in `G`) to an edge not in `W`.
3. The connected component of `G'` containing `u` is a smaller connected graph with
   all even degrees. By the inductive hypothesis, it has an Eulerian circuit `W'`.
4. Splicing `W'` into `W` at `u` produces a strictly longer closed trail in `G`,
   contradicting the maximality of `W`. -/
lemma exists_euler_circuit_of_connected_even_degree
    (hconn : G.Connected) [hne : Nonempty V]
    (heven : ∀ v : V, Even (G.degree v)) :
    ∃ (v : V) (w : G.Walk v v), w.IsEulerian := by
  -- We generalize and prove by strong induction on the number of edges.
  suffices key : ∀ (n : ℕ) (G' : SimpleGraph V) [DecidableRel G'.Adj],
      G'.Connected → (∀ v, Even (G'.degree v)) →
      #G'.edgeFinset = n →
      ∃ (v : V) (w : G'.Walk v v), w.IsEulerian from
    key _ G hconn heven rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro G' _ hconn' heven' hn
  -- ══════════════════════════════════════════════════════════════
  -- BASE CASE: n = 0 edges. The nil walk is vacuously Eulerian.
  -- ══════════════════════════════════════════════════════════════
  by_cases hedge : n = 0
  · subst hedge
    exact ⟨hne.some, Walk.nil, fun e he => by
      have := G'.mem_edgeFinset.mpr he
      simp [Finset.card_eq_zero.mp hn] at this⟩
  -- ══════════════════════════════════════════════════════════════
  -- INDUCTIVE STEP: n > 0 edges.
  -- ══════════════════════════════════════════════════════════════
  -- Step 1: A maximal-length closed trail exists.
  -- The set of closed-trail lengths is a finite subset of ℕ (bounded by #edgeFinset),
  -- so it has a maximum element.
  have hpos : 0 < n := Nat.pos_of_ne_zero hedge
  -- The set of achievable closed-trail lengths:
  let S : Set ℕ := { m | ∃ (v : V) (W : G'.Walk v v), W.IsTrail ∧ W.length = m }
  have hSfin : S.Finite :=
    Set.Finite.subset (Set.finite_le_nat (#G'.edgeFinset)) fun m ⟨v, W, hW, hm⟩ =>
      hm ▸ hn ▸ hW.length_le_card_edgeFinset
  have hSne : S.Nonempty := ⟨0, hne.some, Walk.nil, Walk.IsTrail.nil, rfl⟩
  obtain ⟨m, ⟨v₀, W, hWtrail, hWlen⟩, hWmax⟩ := hSfin.exists_maximal hSne
  -- W : G'.Walk v₀ v₀ is a closed trail of maximum length m.
  -- Step 2: Show W is Eulerian.
  -- If W is already Eulerian, we are done.
  by_cases hE : W.IsEulerian
  · exact ⟨v₀, W, hE⟩
  -- Otherwise, we derive a contradiction to the maximality of W.
  exfalso
  -- First establish that W has positive length (m > 0).
  -- If m = 0, G' would be a tree (connected + acyclic), but trees have
  -- min degree 1, contradicting all-even-degrees.
  have hm_pos : 0 < m := by
    by_contra hm0
    simp only [Nat.not_lt, Nat.le_zero] at hm0
    -- G' is not acyclic: connected + acyclic = tree, min degree 1, odd.
    have hnotacyc : ¬G'.IsAcyclic := by
      intro hacyc
      have htree := G'.isTree_iff.mpr ⟨hconn', hacyc⟩
      haveI : Nontrivial V := by
        obtain ⟨e, he⟩ := Finset.card_pos.mp (hn ▸ hpos)
        rw [mem_edgeFinset] at he; revert he
        exact Sym2.ind (fun a b he => ⟨⟨a, b, (G'.mem_edgeSet.mp he).ne⟩⟩) e
      have h1 := htree.minDegree_eq_one_of_nontrivial
      obtain ⟨v, hv⟩ := G'.exists_minimal_degree_vertex
      have hd : G'.degree v = 1 := by omega
      have hev := heven' v; rw [hd] at hev
      exact Nat.not_even_one hev
    -- Extract cycle from ¬IsAcyclic, contradicting m = 0 maximality
    simp only [IsAcyclic, not_forall, Classical.not_not] at hnotacyc
    obtain ⟨v, c, hc⟩ := hnotacyc
    have hclen := hc.three_le_length
    have := hWmax ⟨v, c, hc.isCircuit.isTrail, rfl⟩ (by omega)
    omega
  -- Step 3: Since W is a non-Eulerian trail, there exists an edge in G' not in W.
  rw [Walk.isEulerian_iff] at hE
  push Not at hE
  obtain ⟨e₀, he₀mem, he₀nin⟩ := hE hWtrail
  -- Step 4a: G'' = G'.deleteEdges W.edgeSet has all even degrees.
  -- Removing a closed trail preserves degree parity: a closed trail contributes
  -- an even number of incidences at each vertex (enters = exits), so
  -- deg_{G''}(v) = deg_{G'}(v) - (even number) = even.
  set G'' := G'.deleteEdges W.edgeSet with hG''def
  -- Ensure Lean can compute with G'':
  haveI : DecidablePred (· ∈ W.edgeSet) := fun e => decidable_of_iff
    (e ∈ W.edges) ⟨fun h => h, fun h => h⟩
  haveI : DecidableRel G''.Adj := inferInstance
  have heven'' : ∀ v, Even (G''.degree v) := by
    -- This follows because W is a closed trail: for each vertex v, the number of
    -- edges of W incident to v is even (the walk enters and exits v equally often).
    -- Therefore deg_{G''}(v) = deg_{G'}(v) - deg_W(v) is even - even = even.
    sorry
  -- Step 4b: By connectivity of G', there is a vertex u ∈ W.support that has
  -- an edge in G'' (i.e., an edge of G' not in W).
  have hexists_u : ∃ u ∈ W.support, 0 < G''.degree u := by
    -- Since G' is connected and e₀ ∈ G'.edgeSet \ W.edgeSet, and W is non-empty
    -- (as n > 0 and W is maximal), connectivity of G' ensures some vertex of W
    -- is incident to an edge not in W.
    sorry
  obtain ⟨u, hu_supp, hu_deg⟩ := hexists_u
  -- Step 4c: The connected component of G'' containing u has fewer edges than G',
  -- is connected, and has all even degrees. By the inductive hypothesis, it has
  -- an Eulerian circuit W'.
  -- (We work with the full G'' for simplicity; the argument applies to the component.)
  -- G'' has strictly fewer edges than G':
  have hG''_lt : #G''.edgeFinset < n := by
    -- G''.edgeFinset ⊂ G'.edgeFinset since W has ≥ 1 edge (m > 0).
    rw [hn]; apply Finset.card_lt_card
    refine ⟨edgeFinset_mono (deleteEdges_le W.edgeSet), fun hsub => ?_⟩
    -- Some edge of W is in G' but not in G'' → contradicts hsub
    have hWne : W.edges ≠ [] :=
      Walk.edges_eq_nil.not.mpr (Walk.not_nil_iff_lt_length.mpr (hWlen ▸ hm_pos))
    have he₁mem : W.edges.head hWne ∈ W.edges := List.head_mem hWne
    have he₁G' := (mem_edgeFinset G').mpr (W.edges_subset_edgeSet he₁mem)
    have he₁G'' := hsub he₁G'
    -- e₁ ∈ G''.edgeFinset, but e₁ ∈ W.edgeSet, contradicting deleteEdges
    rw [mem_edgeFinset] at he₁G''
    revert he₁mem he₁G''
    exact Sym2.ind (fun v w he₁mem he₁G'' => by
      rw [mem_edgeSet, hG''def, deleteEdges_adj] at he₁G''
      exact he₁G''.2 (Walk.mem_edgeSet.mpr he₁mem)) (W.edges.head hWne)
  -- Now we use the inductive hypothesis on the component of G'' containing u.
  -- The component is connected, has all even degrees, and fewer edges.
  -- For simplicity, we use G'' restricted to the component of u.
  -- (A full formalization would extract the connected component and apply ih.)
  -- The key point: we get a closed trail W' through u in G'' (or its component).
  have ⟨W'_start, W', hW'euler⟩ : ∃ (w : V) (W' : G''.Walk w w), W'.IsEulerian := by
    -- Apply ih to the connected component of G'' containing u.
    -- That component has < n edges and all even degrees.
    sorry
  -- Step 4d: Splice W' into W at u to get a strictly longer closed trail.
  -- Rotate W to start at u: W_rot : G'.Walk u u with W_rot.IsTrail and same length.
  let W_rot := W.rotate u hu_supp
  have hW_rot_trail : W_rot.IsTrail := hWtrail.rotate hu_supp
  -- Map W' from G'' to G' (since G'' ≤ G'):
  -- W'_in_G' : G'.Walk w w, same edges as W', all disjoint from W's edges.
  -- Rotate W' to start/end at u if W'_start ≠ u (or use the component circuit through u).
  -- The spliced walk: W_rot.append W'_lifted : G'.Walk u u
  -- This is a trail because W and W' have disjoint edge sets (W' lives in G'' = G' - E(W)).
  -- Its length = m + W'.length > m, contradicting maximality of m.
  -- (W'.length > 0 since W' is Eulerian in a component with edges through u.)
  have hsplice : ∃ (w : V) (C : G'.Walk w w), C.IsTrail ∧ m < C.length := by
    sorry
  obtain ⟨w, C, hCtrail, hClong⟩ := hsplice
  -- This contradicts the maximality of W: C is a closed trail of length > m.
  exact Nat.lt_irrefl m (lt_of_lt_of_le hClong
    (hWmax ⟨w, C, hCtrail, rfl⟩ (by omega)))

/-! ### Orienting an Euler circuit -/

/-- An *orientation* of a simple graph assigns a direction to each edge.
Represented as a function from edges to ordered pairs. -/
structure Orientation (G : SimpleGraph V) where
  /-- The head (target) of a directed edge from `v` to `w`. -/
  target : (e : Sym2 V) → e ∈ G.edgeSet → V
  /-- The tail (source) of a directed edge. -/
  source : (e : Sym2 V) → e ∈ G.edgeSet → V
  /-- Source and target are the two endpoints. -/
  endpoints : ∀ e (he : e ∈ G.edgeSet), s(source e he, target e he) = e
  /-- Source ≠ target (from irreflexivity). -/
  source_ne_target : ∀ e (he : e ∈ G.edgeSet), source e he ≠ target e he

/-- The in-degree of a vertex `v` in an orientation: the number of edges directed *into* `v`. -/
noncomputable def Orientation.inDegree (o : G.Orientation) (v : V) : ℕ :=
  (G.edgeFinset.filter (fun e => ∃ he : e ∈ G.edgeSet, o.target e he = v)).card

/-- The out-degree of a vertex `v` in an orientation: the number of edges directed *out of* `v`. -/
noncomputable def Orientation.outDegree (o : G.Orientation) (v : V) : ℕ :=
  (G.edgeFinset.filter (fun e => ∃ he : e ∈ G.edgeSet, o.source e he = v)).card

/-- In any orientation, `inDegree v + outDegree v = degree v` for every vertex `v`. -/
lemma Orientation.inDegree_add_outDegree (o : G.Orientation) (v : V) :
    o.inDegree G v + o.outDegree G v = G.degree v := by
  sorry

/-- An Euler circuit in a 2k-regular graph can be oriented so that every vertex has
in-degree `k` and out-degree `k`. This follows by walking along the circuit and directing
each edge in the traversal direction. -/
lemma exists_orientation_balanced_of_euler
    {k : ℕ} (hk : 0 < k) (hreg : G.IsRegularOfDegree (2 * k))
    (hconn : G.Connected)
    {v : V} {w : G.Walk v v} (hE : w.IsEulerian) :
    ∃ o : G.Orientation,
      (∀ u : V, o.inDegree G u = k) ∧ (∀ u : V, o.outDegree G u = k) := by
  sorry

/-! ### Bipartite double cover from an orientation -/

/-- Given a balanced orientation (in-degree = out-degree = k) of a 2k-regular graph, we
construct an auxiliary bipartite graph on `V ⊕ V` (left = out-copies, right = in-copies).

For each directed edge `u → w` in the orientation, we place the edge `{inl u, inr w}`. -/
noncomputable def bipartiteOfOrientation (o : G.Orientation) : SimpleGraph (V ⊕ V) where
  Adj x y := match x, y with
    | .inl u, .inr w =>
        ∃ e, (he : e ∈ G.edgeSet) →  o.source e he = u ∧ o.target e he = w
    | .inr w, .inl u =>
        ∃ e, (he : e ∈ G.edgeSet) →  o.source e he = u ∧ o.target e he = w
    | _, _ => False
  symm x y := by
    cases x <;> cases y <;> simp (config := { contextual := true })
  loopless := sorry


/-- The bipartite graph constructed from a balanced orientation is k-regular on both sides:
every out-copy has degree `k` and every in-copy has degree `k`. -/
lemma bipartiteOfOrientation_regular_left
    (o : G.Orientation)
    (hout : ∀ u : V, o.outDegree G u = k) :
    ∀ (u : V), (G.bipartiteOfOrientation o).degree (Sum.inl u) = k := by
  sorry

lemma bipartiteOfOrientation_regular_right
    (o : G.Orientation)
    (hin : ∀ u : V, o.inDegree G u = k) :
    ∀ (u : V), (G.bipartiteOfOrientation o).degree (Sum.inr u) = k := by
  sorry

/-! ### Regular bipartite graphs have perfect matchings -/

/-- **König's theorem for regular bipartite graphs**: every k-regular bipartite graph
(k ≥ 1) has a perfect matching.

This follows from Hall's marriage theorem: in a k-regular bipartite graph, every subset `S`
of the left part has `|N(S)| ≥ |S|`, because counting edges from `S` gives `k|S|` edges,
each right vertex absorbs at most `k`, so `|N(S)| ≥ |S|`. -/
lemma exists_isPerfectMatching_of_regular_bipartite
    {W : Type*} [Fintype W] [DecidableEq W]
    (B : SimpleGraph (W ⊕ W)) [DecidableRel B.Adj]
    (k : ℕ) (hk : 0 < k)
    (hreg : B.IsRegularOfDegree k) :
    ∃ M : Subgraph B, M.IsPerfectMatching := by
  -- Proof sketch:
  -- Hall's condition: for every S ⊆ left part,
  --   |N(S)| ≥ |S|
  -- because:
  --   edges from S = k * |S|  (each left vertex has degree k)
  --   edges into N(S) ≤ k * |N(S)|  (each right vertex has degree ≤ k)
  --   ∴ k * |S| ≤ k * |N(S)|  ⟹  |S| ≤ |N(S)|
  -- By Hall's marriage theorem, a matching saturating the left part exists.
  -- By symmetry (or repeating the argument), it saturates the right part too.
  -- Hence it is a perfect matching.
  sorry

/-! ### Lifting matchings from the bipartite graph back to 2-factors -/

/-- A perfect matching in the bipartite double cover `V ⊕ V` corresponds to a set of edges
in `G` forming a spanning subgraph where every vertex has degree exactly 2. -/
lemma matching_to_twoFactor
    (o : G.Orientation)
    {B : SimpleGraph (V ⊕ V)} [DecidableRel B.Adj]
    (M : Subgraph B) (hM : M.IsPerfectMatching) :
    ∃ H : Subgraph G, G.IsTwoFactor H := by
  -- Each left vertex `inl v` is matched to exactly one right vertex `inr w`,
  -- giving one outgoing edge `v → w` per vertex.
  -- Each right vertex `inr v` is matched to exactly one left vertex `inl u`,
  -- giving one incoming edge `u → v` per vertex.
  -- Thus every vertex `v` in `G` gains one "out-edge" and one "in-edge",
  -- yielding degree exactly 2 in the underlying undirected subgraph.
  sorry

/-! ### Subtraction lemma: removing a 2-factor from a 2k-regular graph -/

/-- If `G` is 2k-regular and `H` is a 2-factor of `G`, then the subgraph `G - H`
(edges of `G` not in `H`) is `2(k-1)`-regular. -/
lemma isRegularOfDegree_sub_twoFactor
    {k : ℕ} (hk : 1 ≤ k) (hreg : G.IsRegularOfDegree (2 * k))
    {H : Subgraph G} (hH : G.IsTwoFactor H) :
    ∃ G' : SimpleGraph V,
      G'.IsRegularOfDegree (2 * (k - 1)) ∧
      (∀ v w, G'.Adj v w → G.Adj v w) ∧
      (∀ v w, G.Adj v w → (G'.Adj v w ∨ H.Adj v w)) := by
  -- The edges of G partition into edges of H and edges of G'.
  -- H has degree 2 at every vertex, G has degree 2k,
  -- so G' has degree 2k - 2 = 2(k-1).
  sorry

/-! ### The main theorem -/

/-- **Petersen's 2-Factor Theorem**: Every 2k-regular graph (k ≥ 1) on a finite vertex set
has a 2-factor.

More precisely: if `G` is a simple graph on finitely many vertices and every vertex has
degree `2k` (with `k ≥ 1`), then `G` has a spanning subgraph `H` where every vertex has
degree exactly 2.

### Proof (induction on `k`)

**Base case** `k = 1`: `G` itself is 2-regular, so it is its own 2-factor.

**Inductive step** `k ≥ 2`: Apply the construction above:
1. Each connected component of `G` has all vertices of even degree, so it has an Euler circuit.
2. Orient the Euler circuit to get a balanced orientation (in-degree = out-degree = k).
3. Build the bipartite double cover and find a perfect matching (by Hall/König).
4. Lift the matching to a 2-factor `H` of `G`.
5. The remaining graph `G - H` is `2(k-1)`-regular; apply the induction hypothesis. -/
theorem exists_twoFactor_of_isRegularOfDegree_even
    {k : ℕ} (hk : 0 < k) (hreg : G.IsRegularOfDegree (2 * k)) :
    ∃ H : Subgraph G, G.IsTwoFactor H := by
  -- Induction on k
  induction k with
  | zero => omega
  | succ n ih =>
    by_cases hn : n = 0
    · -- Base case: k = 1, so G is 2-regular.
      -- G itself is a 2-factor.
      subst hn
      simp only [Nat.zero_add, mul_one] at hreg
      exact ⟨⊤, {
        spanning := fun v => Subgraph.mem_top v
        degree_eq := fun v => by
          -- Need: `(⊤ : Subgraph G).degree v = 2`
          -- The top subgraph of G has the same degree as G at every vertex.
          -- Since G is 2-regular, degree v = 2.
          sorry
      }⟩
    · -- Inductive step: k = n + 1 ≥ 2.
      -- Step 1: G has even degree at every vertex (degree = 2(n+1)).
      have heven : ∀ v : V, Even (G.degree v) := fun v => by
        rw [hreg v]; exact ⟨n + 1, by ring⟩
      -- Step 2: For each connected component, find an Euler circuit and orient it.
      -- We apply the construction component-by-component.
      -- Step 3: From the balanced orientation, build the bipartite double cover.
      -- Step 4: Find a perfect matching in the bipartite double cover.
      -- Step 5: Lift to a 2-factor H of G.
      obtain ⟨H, hH⟩ : ∃ H : Subgraph G, G.IsTwoFactor H := by
        -- Component-wise construction:
        -- Each component `C` of `G` is connected and `2(n+1)`-regular.
        -- By `exists_euler_circuit_of_connected_even_degree`, `C` has an Euler circuit.
        -- By `exists_orientation_balanced_of_euler`, orient it with in/out-degree `n+1`.
        -- By `exists_isPerfectMatching_of_regular_bipartite`, the bipartite cover has
        -- a perfect matching.
        -- By `matching_to_twoFactor`, this lifts to a 2-factor of `C`.
        -- The union of 2-factors of all components is a 2-factor of `G`.
        sorry
      exact ⟨H, hH⟩

/-- **Corollary**: A 2k-regular graph (k ≥ 1) can be decomposed into `k` edge-disjoint
2-factors. -/
theorem exists_twoFactor_decomposition
    {k : ℕ} (hk : 0 < k) (hreg : G.IsRegularOfDegree (2 * k)) :
    ∃ (factors : Fin k → Subgraph G),
      (∀ i, G.IsTwoFactor (factors i)) ∧
      -- The factors are pairwise edge-disjoint
      (∀ i j, i ≠ j → ∀ v w, ¬(factors i).Adj v w ∨ ¬(factors j).Adj v w) ∧
      -- Every edge of G is in some factor
      (∀ v w, G.Adj v w → ∃ i, (factors i).Adj v w) := by
  -- By induction on k, using `exists_twoFactor_of_isRegularOfDegree_even` and
  -- `isRegularOfDegree_sub_twoFactor`.
  sorry

/-! ### Special case: Petersen's original theorem for cubic graphs -/

/-- **Petersen's Theorem** (original form): Every bridgeless 3-regular (cubic) graph has a
perfect matching (1-factor).

Proof: A bridgeless cubic graph can be shown to satisfy Tutte's condition (no Tutte violators).
Alternatively, this follows from the 2-factor theorem applied to an appropriate construction:
the line graph of a cubic graph is 4-regular, and a 2-factor of the line graph corresponds
to a partition of the original graph's edges into paths and cycles of specific structure. -/
theorem exists_isPerfectMatching_of_cubic_bridgeless
    (hreg : G.IsRegularOfDegree 3) (hconn : G.Connected) (hbl : G.IsBridgeless) :
    ∃ M : Subgraph G, M.IsPerfectMatching := by
  -- Petersen's theorem via Tutte's theorem:
  -- We show that no set `S` is a Tutte violator.
  -- Let `S ⊆ V` and let `o(G - S)` denote the number of odd components of `G - S`.
  -- Counting argument:
  --   - Let the odd components be `C₁, ..., Cₜ`.
  --   - Each Cᵢ is connected to S by at least one edge (since G is connected).
  --   - In fact, since G is bridgeless and 3-regular, each Cᵢ sends at least 2 edges to S
  --     (if it sent exactly 1, that edge would be a bridge, since Cᵢ has odd order and
  --     each vertex has degree 3, the number of edges between Cᵢ and S has the same
  --     parity as ∑_{v ∈ Cᵢ} deg(v) - 2|E(Cᵢ)|, which is odd, so ≥ 3 edges to S,
  --     and since it's odd, ≥ 3).
  --   Actually the standard argument: 3|Cᵢ| = 2|E(Cᵢ)| + e(Cᵢ, S).
  --   Since |Cᵢ| is odd and 3|Cᵢ| is odd, e(Cᵢ, S) is odd, hence ≥ 1.
  --   But since G is bridgeless, e(Cᵢ, S) ≥ 2. Combined with odd, e(Cᵢ, S) ≥ 3.
  --   Total edges from odd components to S: ≥ 3t.
  --   Total edges at S: ≤ 3|S|.
  --   Hence 3t ≤ 3|S|, i.e., t ≤ |S|. So no Tutte violator exists.
  -- By Tutte's theorem (available as `SimpleGraph.tutte`), G has a perfect matching.
  sorry

end SimpleGraph
