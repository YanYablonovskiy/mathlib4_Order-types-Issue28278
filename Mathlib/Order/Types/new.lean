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

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]
 [∀G' : Subgraph G, Fintype ↑G'.verts] [∀G' : Subgraph G,∀x, DecidablePred fun v_1 ↦ v_1 ∈ G'.neighborSet x]

/-! ### Bridgeless graphs -/

/-- A graph is *bridgeless* if it has no bridge edges. Equivalently, it is 2-edge-connected:
removing any single edge leaves the graph connected. -/
def IsBridgeless : Prop :=
  ∀⦃v1 v2 : V⦄, s(v1,v2) ∈ G.edgeSet → ¬G.IsBridge s(v1,v2)


noncomputable local instance (G' : SimpleGraph V) (u : V) (S : Set (Sym2 V)) : Fintype ↑((G'.deleteEdges S).neighborSet u) :=
  Fintype.ofFinite ↑((G'.deleteEdges S).neighborSet u)

noncomputable local instance (G' : SimpleGraph V) (v w : V) (W : G'.Walk v w) (w : V) : Decidable (w ∈ W.toSubgraph.spanningCoe.support) := by
  exact Classical.propDecidable (w ∈ W.toSubgraph.spanningCoe.support)

noncomputable local instance (G' : SimpleGraph V) (v w : V) (W : G'.Walk v w) (u : V) : Fintype ↑(W.toSubgraph.spanningCoe.neighborSet u) := by
  exact Fintype.ofFinite ↑(W.toSubgraph.spanningCoe.neighborSet u)

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

-- #check SimpleGraph.minDegree
-- --exists_minimal_degree_vertex, minDegree_le_degree and le_minDegree_of_forall_le_degree.
-- #check exists_minimal_degree_vertex -- ∃ v, G.minDegree = G.degree v
-- #check minDegree_le_degree --G.minDegree ≤ G.degree v
-- #check le_minDegree_of_forall_le_degree -- (k : ℕ) (h : ∀ (v : V), k ≤ G.degree v) : k ≤ G.minDegree
-- #check commonNeighbors
-- #check SimpleGraph.neighborSet
-- #check SimpleGraph.isBridge_iff_adj_and_not_isEdgeConnected_two
-- #check Sym2

-- #check SimpleGraph.Walk.head_edges_eq_mk_start_snd

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
-- #check Nat.not_lt_of_ge
-- #check Nat.pos_iff_ne_zero
-- #check Nat.two_pos  -- 0 < 2
-- #check Nat.one_pos
-- #check Nat.one_lt_two
-- #check minDegree_le_degree --  2 ≤ G.degree inst.some
-- #check Walk.IsPath
-- #check Nat.lt_of_le_of_lt
-- #check G.isTree_iff.mpr


lemma nonempty_of_deg_ge_two (hdeg : 2 ≤ G.minDegree) : Nonempty V :=
  Classical.not_not.mp <| fun he ↦
    have := not_nonempty_iff.mp he
    Nat.not_lt_of_ge (Eq.subst (motive := fun n ↦ 2 ≤ n) G.minDegree_of_isEmpty hdeg) two_pos


lemma nontrivial_of_degree_ge_two (hdeg : 2 ≤ G.minDegree) : Nontrivial V :=
  letI v := (G.nonempty_of_deg_ge_two hdeg).some
  G.nontrivial_of_degree_ne_zero (v := v)
    (by grind [hdeg.trans (G.minDegree_le_degree v)])


/-- A connected graph with minimum degree ≥ 2 is NOT acyclic. -/
lemma IsAcyclic.not_of_connected_minDegree_ge_two (hconn : G.Connected)
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


lemma test_1 {G' : SimpleGraph V} [∀ u, ∀ S, Fintype ↑((G.deleteEdges S).neighborSet u)]
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


lemma test2 {G' : SimpleGraph V} [∀ u, ∀ S, Fintype ↑((G.deleteEdges S).neighborSet u)]
    {u : V} [∀ u, Fintype ↑(G'.neighborSet u)] :
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
    · intro hc
      rw [Finset.mem_inter] at hc
      obtain ⟨hc1 , hc2⟩ := hc
      rw [mem_neighborFinset,this v]
      constructor
      · rw [ ← mem_neighborFinset]
        exact hc1
      · rw [mem_compl] at hc2
        simp
        rw [ ← mem_neighborFinset]
        exact hc2

-- #check Finset.mem_inter



lemma test3 {G' : SimpleGraph V} [∀ u, ∀ S, Fintype ↑((G.deleteEdges S).neighborSet u)] [∀u , Fintype ↑(G'.neighborSet u)]
    (hSg : G'.edgeSet ≤ G.edgeSet) (u : V) [Decidable (u ∈ G'.support)] :
    (G.deleteEdges G'.edgeSet).degree u = if u ∈ G'.support then
    G.degree u - G'.degree u else G.degree u := by
  by_cases hs : u ∈ G'.support
  · simp [hs]
    rw [SimpleGraph.degree,SimpleGraph.degree,SimpleGraph.degree] at *
    rw [test2,Finset.card_sdiff_of_subset]
    intro x hs
    rw [mem_neighborFinset,← mem_edgeSet] at *
    exact hSg hs
  · have (v : V) := @G.deleteEdges_adj _ u v (s := G'.edgeSet)
    simp [hs]
    rw [SimpleGraph.degree, SimpleGraph.degree] at *
    rw [test_1 G hs]


-- #check G.neighborSet_subset_support



lemma del_deg_zero_iff {G' : SimpleGraph V} [∀ u, ∀ S, Fintype ↑((G.deleteEdges S).neighborSet u)] [∀u , Fintype ↑(G'.neighborSet u)]
    (hSg : G'.edgeSet ≤ G.edgeSet) (u : V) [Decidable (u ∈ G'.support)] :
    (G.deleteEdges G'.edgeSet).degree u = 0 ↔ ∀v, (G.Adj v u → G'.Adj v u) := by
  refine ⟨?_ , ?_⟩
  · intro hd0 v hadjv
    rw [SimpleGraph.degree,Finset.card_eq_zero] at hd0
    rw [test2,Finset.sdiff_eq_empty_iff_subset] at hd0
    rw [G.neighborFinset_def,G'.neighborFinset_def] at hd0
    rw [Set.toFinset_subset_toFinset] at hd0
    have t1: G.neighborSet u = {w | G.Adj u w} := by rfl
    rw [t1] at hd0
    have t2: G'.neighborSet u = {w | G'.Adj u w} := by rfl
    rw [t2] at hd0
    simp at hd0
    specialize hd0 v (G.adj_comm v u |>.mp hadjv)
    exact G'.adj_comm u v |>.mp hd0
  · intro hvfun
    rw [SimpleGraph.degree,Finset.card_eq_zero]
    rw [test2,Finset.sdiff_eq_empty_iff_subset]
    rw [G.neighborFinset_def,G'.neighborFinset_def]
    rw [Set.toFinset_subset_toFinset]
    have t1: G.neighborSet u = {w | G.Adj u w} := by rfl
    intro x hxu
    rw [t1] at hxu
    rw [Set.mem_setOf_eq] at hxu
    have t2: G'.neighborSet u = {w | G'.Adj u w} := by rfl
    rw [t2]
    specialize hvfun x (G.adj_comm u x |>.mp hxu)
    simp
    exact G'.adj_comm x u |>.mp hvfun

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

example {v : V} {W : G.Walk v v} : W.edgeSet ⊆ G.edgeSet := by
  intro x hxe
  exact W.edges_subset_edgeSet hxe

example {v : V} {W : G.Walk v v} :   W.toSubgraph.spanningCoe.edgeSet = W.edgeSet := by
  simp

-- #check SimpleGraph.induce

-- #check SimpleGraph.fromEdgeSet_edgeSet
-- #check Subgraph.neighborSet
-- #check Walk.recOn
-- #check Walk.brecOn
-- #check G.Subgraph

lemma t5 {u : V} {p : G.Walk u u} (ht : p.IsTrail)  (x : V)-- [∀ v w u, ∀ p : G.Walk v w,  Fintype ↑(p.toSubgraph.neighborSet u)]
    : haveI : Fintype ↑(p.toSubgraph.neighborSet x) :=
        SimpleGraph.Subgraph.instFintypeElemNeighborSetOfVertsOfDecidablePredMemSet p.toSubgraph x
    Even (p.toSubgraph.degree x) := by
  have t1 := ht.even_countP_edges_iff x |>.mpr (fun hc ↦ (hc (Eq.refl u)).elim)
  rw [Subgraph.degree]
  have : List.countP (fun e ↦ decide (x ∈ e)) p.edges = Fintype.card ↑(p.toSubgraph.neighborSet x) := by
    apply Walk.concatRec (motive := fun v w p ↦ (x : V) → p.IsTrail → (List.countP (fun e ↦ decide (x ∈ e)) p.edges = Fintype.card ↑(p.toSubgraph.neighborSet x)))
    · simp
    · intros u v w h p' p_ih k iht
      rw [h.edges_concat]
      simp
      rw [←Set.toFinset_card, h.concat_eq_append]
      rw! (castMode := .all) [h.toSubgraph_append,SimpleGraph.Subgraph.neighborSet_sup]
      rw [Set.toFinset_union , Finset.card_union]
      simp
      rw [←p_ih k]
      rw [Nat.add_sub_assoc]
      congr
      by_cases hex : k = v ∨ k = w
      · simp only [hex,decide_true,if_true]
        rcases hex with (hxu | hxv)
        · have := SimpleGraph.neighborSet_fst_subgraphOfAdj p'
          rw! [hxu]
          rw! (castMode := .all) [this]
          simp
          have : w ∉ h.toSubgraph.neighborSet v := by
            rw [h.concat_eq_append ] at iht
            by_contra hc
            simp at hc
            have e1: s(v , w) ∈ h.edges := by rw [h.adj_toSubgraph_iff_mem_edges] at hc; exact hc
            have e2: s(v , w) ∈ (Walk.cons p' Walk.nil).edges := by simp [SimpleGraph.Walk.edges_cons]
            rw [Walk.isTrail_def,h.edges_append,List.nodup_append] at iht
            exact iht.2.2 _ e1 _ e2 (Eq.refl s(v ,w))
              --have := h.toSubgraph.adj_sub hc
              --have := h.mem_support_of_adj_toSubgraph hc
          simp [this]
        · have := SimpleGraph.neighborSet_snd_subgraphOfAdj p'
          rw! [hxv]
          rw! (castMode := .all) [this]
          simp
          have : v ∉ h.toSubgraph.neighborSet w := by
            rw [h.concat_eq_append ] at iht
            by_contra hc
            simp at hc
            have e1: s(w , v) ∈ h.edges := by rw [h.adj_toSubgraph_iff_mem_edges] at hc; exact hc
            have e2: s(w , v) ∈ (Walk.cons p' Walk.nil).edges := by simp [SimpleGraph.Walk.edges_cons]
            rw [Walk.isTrail_def,h.edges_append,List.nodup_append] at iht
            exact iht.2.2 _ e1 _ e2 (Eq.refl s(w ,v))
          simp [this]

      . push Not at hex
        simp [hex]
      · rw [← Set.toFinset_card]
        apply Finset.card_le_card
        rw [inter_comm]
        exact Finset.inter_subset_left (α := V)

      · exact iht.of_append_left
    · exact ht
  rw [←this]
  exact t1













--     simp only [Subgraph.neighborSet_sup,Walk.toSubgraph]
--     rw [←Set.toFinset_card,Set.toFinset_union, Finset.card_union]
--     nth_rw 2 [Set.toFinset_card]
--     rw [←p_ih]
--     rw [SimpleGraph.neighborSet_fst_subgraphOfAdj h]
--     nth_rw 2 [add_comm]
--     rw [Nat.add_sub_assoc]
--     congr
--     by_cases hex : k = u ∨ k = v
--     · simp only [Sym2.mem_iff,hex,decide_true,if_true]
--       rcases hex with (hxu | hxv)
--       · have := SimpleGraph.neighborSet_fst_subgraphOfAdj h
--         rw! [hxu]
--         rw! (castMode := .all) [this]
--         simp

--         sorry

--       · sorry



--     · push Not at hex
--       simp [hex]
--     · apply Finset.card_le_card
--       simp

-- rw [←this]
-- exact t1

    --u v w h p p_ih





/-- Removing the edges of a closed trail from a graph preserves even-degree parity at every
vertex. More precisely, if every vertex of `G` has even degree and `W` is a circuit in `G`,
then every vertex of `G.deleteEdges W.edgeSet` has even degree. -/
lemma even_degree_deleteEdges_of_circuit
    {v : V} {W : G.Walk v v} (hW : W.IsCycle) [∀ u, ∀ S, Fintype ↑((G.deleteEdges S).neighborSet u)]
    (heven : ∀ u : V, Even (G.degree u)) :
    ∀ u : V, Even ((G.deleteEdges W.edgeSet).degree u) := by
  -- Each vertex u appears as an endpoint of edges in W an even number of times
  -- (since W is a closed trail, it enters and leaves u equally often).
  -- So degree_G(u) - degree_W(u) is even − even = even.
    classical
    intro w
    have := test3 (G' := W.toSubgraph.spanningCoe) G (by simp; exact fun x hxe ↦  W.edges_subset_edgeSet hxe
   )
    specialize this w
    rw  [←(by simp : @edgeSet V W.toSubgraph.spanningCoe = W.edgeSet)]
    by_cases hw : w ∈ W.toSubgraph.spanningCoe.support
    <;> simp [hw] at this
    · rw [this]
      rw [Nat.even_sub]
      · refine ⟨fun _ ↦ ?_ , fun _ ↦ heven w⟩
        rw [mem_support] at hw
        obtain ⟨w1,haw⟩ := hw

        have t1 := W.toSubgraph.spanningCoe_adj w w1
        rw [t1] at haw
        have := hW.ncard_neighborSet_toSubgraph_eq_two ( W.mem_support_of_adj_toSubgraph  haw)
        rw [Set.ncard_eq_toFinset_card', W.toSubgraph.finset_card_neighborSet_eq_degree ] at this
        rw [this]
        exact even_two
      · exact W.toSubgraph.degree_le w
      /-
      SimpleGraph.adj_of_mem_walk_support @ Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
      {V : Type u} {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (hp : ¬p.Nil) {x : V}
      (hx : x ∈ p.support) : ∃ y ∈ p.support, G.Adj x y
      -/

    · rw [this]
      exact heven w

#check SimpleGraph.neighborSetFintype
/-- Removing the edges of a closed trail from a graph preserves even-degree parity at every
vertex. More precisely, if every vertex of `G` has even degree and `W` is a circuit in `G`,
then every vertex of `G.deleteEdges W.edgeSet` has even degree. -/
lemma even_degree_deleteEdges_of_trail
    {v : V} {W : G.Walk v v} (hW : W.IsTrail) [∀ u, ∀ S, Fintype ↑((G.deleteEdges S).neighborSet u)]
    (heven : ∀ u : V, Even (G.degree u))
    [(w :V) → Decidable (w ∈ W.toSubgraph.spanningCoe.support)]
    [(u : V) → Fintype ↑(W.toSubgraph.spanningCoe.neighborSet u)] :
    ∀ u : V, Even ((G.deleteEdges W.edgeSet).degree u) := by
  -- Each vertex u appears as an endpoint of edges in W an even number of times
  -- (since W is a closed trail, it enters and leaves u equally often).
  -- So degree_G(u) - degree_W(u) is even − even = even.
    intro w
    have := test3 (G' := W.toSubgraph.spanningCoe) G (by simp; exact fun x hxe ↦  W.edges_subset_edgeSet hxe
   )
    specialize this w
    rw  [←(by simp : @edgeSet V W.toSubgraph.spanningCoe = W.edgeSet)]
    by_cases hw : w ∈ W.toSubgraph.spanningCoe.support
    <;> simp [hw] at this
    · rw [this]
      rw [Nat.even_sub]
      · refine ⟨fun _ ↦ ?_ , fun _ ↦ heven w⟩
        rw [mem_support] at hw
        obtain ⟨w1,haw⟩ := hw

        have t1 := W.toSubgraph.spanningCoe_adj w w1
        rw [t1] at haw
        exact t5 G hW w
      · exact W.toSubgraph.degree_le w
      /-
      SimpleGraph.adj_of_mem_walk_support @ Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
      {V : Type u} {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (hp : ¬p.Nil) {x : V}
      (hx : x ∈ p.support) : ∃ y ∈ p.support, G.Adj x y
      -/

    · rw [this]
      exact heven w







#check SimpleGraph.deleteEdges_eq_bot
-- ∀ u ∈ W.support, (G'.deleteEdges W.edgeSet).degree u
lemma SimpleGraph.Walk.deg_zero_of_del_Eulerian
    {v : V} {W : G.Walk v v} (hW : W.IsTrail) [∀ u, ∀ S, Fintype ↑((G.deleteEdges S).neighborSet u)]
    [(w :V) → Decidable (w ∈ W.toSubgraph.spanningCoe.support)]
    [(u : V) → Fintype ↑(W.toSubgraph.spanningCoe.neighborSet u)] :
    W.IsEulerian → (∀ u ∈ W.support, (G.deleteEdges W.edgeSet).degree u = 0) := by
  refine fun hEw ↦ ?_
  · rw [hW.isEulerian_iff] at hEw
    rw [hEw]
    have := G.deleteEdges_eq_bot (s := G.edgeSet ).mpr (subset_refl _)
    rw! (castMode := .all) [this]
    intro u huw
    convert bot_degree u
#check SimpleGraph.support
#check G.edgeFinset
#check maxOn_eq_if
lemma SimpleGraph.Walk.Eulerian_of_deg_zero
    {v : V} {W : G.Walk v v} (hW : W.IsTrail) [∀ u, ∀ S, Fintype ↑((G.deleteEdges S).neighborSet u)]
    [(w :V) → Decidable (w ∈ W.toSubgraph.spanningCoe.support)]
    [(u : V) → Fintype ↑(W.toSubgraph.spanningCoe.neighborSet u)]
    (hconn : G.Connected) :
    (∀ u ∈ W.support , (G.deleteEdges W.edgeSet).degree u = 0) → W.IsEulerian := by
  intro hwu
  rw [W.isEulerian_iff]
  refine ⟨hW, ?_⟩
  have aux (e : Sym2  V) (heG : e ∈ G.edgeSet) (x y : V) (hxye : s(x,y) = e):
      letI x' := minOn (G.dist v) x y
      x' ∈ W.support → s(x,y) ∈ W.edges := by
    intro heS
    set x' := minOn (G.dist v) x y with hx'
    have := del_deg_zero_iff G (G' := W.toSubgraph.spanningCoe) (by rw [W.toSubgraph.edgeSet_spanningCoe]; intro x hx; exact W.toSubgraph.edgeSet_subset hx )
    have hwu_x' := hwu x' heS
    rw [← W.edgeSet_toSubgraph, ← W.toSubgraph.edgeSet_spanningCoe] at hwu_x'
    have this_u := this x'
    rw [this_u] at hwu_x'
    have eq_or : x' = x ∨ x' = y := by
      simp [hx',minOn_eq_or]
    rcases eq_or with (hr | hr)
    · rw [← hr]
      rw [← hxye, ← hr, mem_edgeSet] at heG
      specialize hwu_x' y
      rw [← W.mem_edges_toSubgraph, ← W.toSubgraph.edgeSet_spanningCoe,mem_edgeSet]
      exact (hwu_x' heG.symm).symm
    · rw [← hr]
      rw [← hxye, ← hr, mem_edgeSet] at heG
      specialize hwu_x' x
      rw [← W.mem_edges_toSubgraph, ← W.toSubgraph.edgeSet_spanningCoe,mem_edgeSet]
      exact (hwu_x' heG)
  intro e heG
  refine e.rec (motive := fun e' ↦ (e' = e) → e' ∈ W.edges) ?_ (by simp) rfl
  intros
  intros
  rename_i x y hxye
  set x' := minOn (G.dist v) x y with hx'
  have := del_deg_zero_iff G (G' := W.toSubgraph.spanningCoe) (by rw [W.toSubgraph.edgeSet_spanningCoe]; intro x hx; exact W.toSubgraph.edgeSet_subset hx )
  suffices heS : x' ∈ W.support from aux e heG x y hxye heS
  have ⟨p, hp, hplen⟩  := hconn.exists_path_of_dist v x'
  refine Nat.recOn (motive :=
     fun n ↦ (x  : V) → (y : V) → (heG : s(x, y) ∈ G.edgeSet) →
     letI x' := minOn (G.dist v) x y; (p : G.Walk v x')
     → (p.length = n) → (G.dist v x' = p.length) → x' ∈ W.support) p.length ?_ ?_ x y (hxye ▸ heG) p rfl hplen.symm
  · intro a b e
    set b' := minOn (G.dist v) a b with hb'
    intro t h hd
    have h0 : G.dist v b' = 0 := by
      rw [hb']
      grind [G.dist_le t]
    have hdel := del_deg_zero_iff G (G' := W.toSubgraph.spanningCoe) (by rw [W.toSubgraph.edgeSet_spanningCoe]; intro x hx; exact W.toSubgraph.edgeSet_subset hx )
    have hvs : v ∈ W.support := by exact W.start_mem_support
    have hwu_v := hwu v hvs
    have hwu_v' := hwu v hvs
    have := hdel v
    rw [←W.edgeSet_toSubgraph,← W.toSubgraph.edgeSet_spanningCoe] at hwu_v
    rw [this] at hwu_v
    specialize hwu_v a
    --rw [← t.nil_iff_length_eq, t.nil_iff_support_eq] at h
    rw [hconn.dist_eq_zero_iff] at h0
    have eq_or : b' = a ∨ b' = b := by
      simp [hb',minOn_eq_or]
    rcases eq_or with (ha | ha)
    · rw [mem_edgeSet] at e
      rw [←W.edgeSet_toSubgraph,← W.toSubgraph.edgeSet_spanningCoe] at hwu_v'
      have := hdel v |>.mp hwu_v'
      have := this b
      rw! (castMode := .all) [h0.trans ha] at this
      specialize this e.symm
      simp at this
      rw [ha,W.mem_support_iff_exists_mem_edges]
      exact Or.inl <| ha.symm.trans h0.symm

    · rw [mem_edgeSet] at e
      rw [←W.edgeSet_toSubgraph,← W.toSubgraph.edgeSet_spanningCoe] at hwu_v'
      have := hdel v |>.mp hwu_v'
      have := this a
      rw! (castMode := .all) [h0.trans ha] at this
      specialize this e
      simp at this
      rw [W.mem_support_iff_exists_mem_edges]
      exact Or.inl h0.symm
  · intro n n_ih x_1 y_1 heG_1 p_1 h h_1
    have eq_or : minOn (G.dist v) x_1 y_1 = x_1 ∨ minOn (G.dist v) x_1 y_1 = y_1 := by
      simp [minOn_eq_or]
    rcases eq_or with (ha | ha)
    · rw [ha]
      set p_y : V := p_1.penultimate with hpy
      have hpnil : ¬p_1.Nil := by
        grind [p_1.nil_iff_length_eq]
      have hpath := p_1.isPath_of_length_eq_dist h_1.symm
      have hpath_d := hpath.drop 1
      -- have heq_d : p_1.drop (-1) = p_1.dropLast
      letI pmk (u : V) (hup : u ∈ p_1.support) := (p_1.reverse.dropUntil u (by simp [hup])).reverse
      have pmk_p (u : V) (hup : u ∈ p_1.support) : (pmk u hup).IsPath := by
        unfold pmk
        rw [(p_1.reverse.dropUntil u _).isPath_reverse_iff]
        apply (p_1.isPath_reverse_iff.mpr hpath).dropUntil (u := u)
          (by rw [p_1.support_reverse,p_1.support.mem_reverse]; exact hup )
      have hteq : (minOn (G.dist v) x_1 p_1.penultimate) = p_1.penultimate := by
        -- d v p_y ≤ d v x_1
        have : G.dist v p_1.penultimate < G.dist v x_1 := by
          nth_rw 1 [ha] at h_1
          rw [h_1]
          have := G.dist_le p_1.dropLast
          rw [p_1.length_dropLast] at this
          apply lt_of_le_of_lt this
          simp
          by_contra!
          simp at this
          exact hpnil ((propext p_1.nil_iff_length_eq) ▸ this)
        rw [minOn_eq_if]
        simp [this]
      set pmk' := pmk p_1.penultimate (by simp) with hpmk'
      have pmkt : pmk'.IsPath := by
        rw [hpmk']
        apply pmk_p p_1.penultimate
        rw [p_1.mem_support_iff_exists_mem_edges]
        have := p_1.mk_penultimate_end_mem_edges hpnil
        apply Or.inr
        use s(p_1.penultimate, minOn (G.dist v) x_1 y_1)
        simp [this]
      have n_ih2 := n_ih x_1 p_1.penultimate (by
        rw [mem_edgeSet, G.adj_comm]
        convert p_1.adj_penultimate hpnil
        exact ha.symm
        )
        (by
            -- have that (G.dist v) x_1 ≤ (G.dist v) y_1
            -- want (G.dist v) p_1.penultimate ≤ (G.dist v) x_1

            have := p_1.copy rfl ha

            have := hconn.dist_triangle (u := v) (w := p_1.penultimate) (v := x_1)
            nth_rw 3 [← ha] at this
            have hadj := p_1.adj_penultimate hpnil
            have hadj := G.adj_symm hadj
            rw [← G.dist_eq_one_iff_adj] at hadj
            rw [hadj] at this
            have := p_1.dropLast
            exact this.copy rfl hteq.symm







        )

        (by simp [p_1.length_dropLast,h])
        (by
            /-
           SimpleGraph.length_eq_dist_of_subwalk @ Mathlib.Combinatorics.SimpleGraph.Metric
           {V : Type u_1} {G : SimpleGraph V} {u v u' v' : V} {p₁ : G.Walk u v}
           {p₂ : G.Walk u' v'} (h₁ : p₁.length = G.dist u v)
           (h₂ : p₂.IsSubwalk p₁) : p₂.length = G.dist u' v'
            -/
           simp
           rw [hteq]
           have pmkt1 := pmkt.getVert_eq_end_iff (i := pmk'.length) (by simp)
           -- G.length_eq_dist_of_subwalk (p₁ := p_1) (u' := v) (v' := p_1.penultimate) h_1.symm (Walk.IsSubwalk.dropLast p_1)
           have : p_1.dropLast.IsSubwalk p_1 := by
             refine Walk.isSubwalk_iff_support_isInfix.mpr ?_
             rw [← p_1.support_dropLast_concat hpnil]
             exact List.infix_append_left
           have := G.length_eq_dist_of_subwalk (p₁ := p_1) (u' := v) (v' := p_1.penultimate) h_1.symm (this)
           rw [← this]
           exact Walk.length_dropLast p_1
        )
      have := aux (e := s(x_1,p_1.penultimate))
        (by
             nth_rw 1 [← ha]
             have := p_1.mk_penultimate_end_mem_edges hpnil
             apply p_1.edges_subset_edgeSet
             rwa [Sym2.eq_swap]
        ) x_1 p_1.penultimate rfl n_ih2
      rw [W.mem_support_iff_exists_mem_edges]
      apply Or.inr ⟨s(x_1, p_1.penultimate), this, by simp⟩
    · rw [ha]
      set p_y : V := p_1.penultimate with hpy
      have hpnil : ¬p_1.Nil := by
        grind [p_1.nil_iff_length_eq]
      have hpath := p_1.isPath_of_length_eq_dist h_1.symm
      have hpath_d := hpath.drop 1
      -- have heq_d : p_1.drop (-1) = p_1.dropLast
      letI pmk (u : V) (hup : u ∈ p_1.support) := (p_1.reverse.dropUntil u (by simp [hup])).reverse
      have pmk_p (u : V) (hup : u ∈ p_1.support) : (pmk u hup).IsPath := by
        unfold pmk
        rw [(p_1.reverse.dropUntil u _).isPath_reverse_iff]
        apply (p_1.isPath_reverse_iff.mpr hpath).dropUntil (u := u)
          (by rw [p_1.support_reverse,p_1.support.mem_reverse]; exact hup )
      have hteq : (minOn (G.dist v) y_1 p_1.penultimate) = p_1.penultimate := by
                -- d v p_y ≤ d v x_1
        have : G.dist v p_1.penultimate < G.dist v y_1 := by
          nth_rw 1 [ha] at h_1
          rw [h_1]
          have := G.dist_le p_1.dropLast
          rw [p_1.length_dropLast] at this
          apply lt_of_le_of_lt this
          simp
          by_contra!
          simp at this
          exact hpnil ((propext p_1.nil_iff_length_eq) ▸ this)
        rw [minOn_eq_if]
        simp [this]
      set pmk' := pmk p_1.penultimate (by simp) with hpmk'
      have pmkt : pmk'.IsPath := by
        rw [hpmk']
        apply pmk_p p_1.penultimate
        rw [p_1.mem_support_iff_exists_mem_edges]
        have := p_1.mk_penultimate_end_mem_edges hpnil
        apply Or.inr
        use s(p_1.penultimate, minOn (G.dist v) x_1 y_1)
        simp [this]
      have n_ih2 := n_ih y_1 p_1.penultimate (by
        rw [mem_edgeSet, G.adj_comm]
        convert p_1.adj_penultimate hpnil
        exact ha.symm
        )
        (by
            -- have that (G.dist v) x_1 ≤ (G.dist v) y_1
            -- want (G.dist v) p_1.penultimate ≤ (G.dist v) x_1

            have := p_1.copy rfl ha

            have := hconn.dist_triangle (u := v) (w := p_1.penultimate) (v := y_1)
            nth_rw 3 [← ha] at this
            have hadj := p_1.adj_penultimate hpnil
            have hadj := G.adj_symm hadj
            rw [← G.dist_eq_one_iff_adj] at hadj
            rw [hadj] at this
            have := p_1.dropLast
            exact this.copy rfl hteq.symm







        )

        (by simp [p_1.length_dropLast,h])
        (by
            /-
           SimpleGraph.length_eq_dist_of_subwalk @ Mathlib.Combinatorics.SimpleGraph.Metric
           {V : Type u_1} {G : SimpleGraph V} {u v u' v' : V} {p₁ : G.Walk u v}
           {p₂ : G.Walk u' v'} (h₁ : p₁.length = G.dist u v)
           (h₂ : p₂.IsSubwalk p₁) : p₂.length = G.dist u' v'
            -/
           simp
           rw [hteq]
           have pmkt1 := pmkt.getVert_eq_end_iff (i := pmk'.length) (by simp)
           -- G.length_eq_dist_of_subwalk (p₁ := p_1) (u' := v) (v' := p_1.penultimate) h_1.symm (Walk.IsSubwalk.dropLast p_1)
           have : p_1.dropLast.IsSubwalk p_1 := by
             refine Walk.isSubwalk_iff_support_isInfix.mpr ?_
             rw [← p_1.support_dropLast_concat hpnil]
             exact List.infix_append_left
           have := G.length_eq_dist_of_subwalk (p₁ := p_1) (u' := v) (v' := p_1.penultimate) h_1.symm (this)
           rw [← this]
           exact Walk.length_dropLast p_1
        )
      have := aux (e := s(y_1,p_1.penultimate))
        (by
             nth_rw 1 [← ha]
             have := p_1.mk_penultimate_end_mem_edges hpnil
             apply p_1.edges_subset_edgeSet
             rwa [Sym2.eq_swap]
        ) y_1 p_1.penultimate rfl n_ih2
      rw [W.mem_support_iff_exists_mem_edges]
      apply Or.inr ⟨s(y_1, p_1.penultimate), this, by simp⟩





lemma Eulerian_iff_deg_zero
    {v : V} {W : G.Walk v v} (hW : W.IsTrail) [∀ u, ∀ S, Fintype ↑((G.deleteEdges S).neighborSet u)]
    [(w :V) → Decidable (w ∈ W.toSubgraph.spanningCoe.support)]
    [(u : V) → Fintype ↑(W.toSubgraph.spanningCoe.neighborSet u)]
    (hconn : G.Connected) : (∀ u ∈ W.support , (G.deleteEdges W.edgeSet).degree u = 0) ↔ W.IsEulerian :=
  ⟨W.Eulerian_of_deg_zero G hW hconn, W.deg_zero_of_del_Eulerian G hW⟩



section
    --   haveI : Nontrivial V := by
    --     apply G.nontrivial_of_degree_ne_zero (v := x_1)
    --     rw [mem_edgeSet] at heG_1
    --     intro hc
    --     rw [G.degree_eq_zero,← G.neighborSet_eq_empty] at hc
    --     rw [Set.eq_empty_iff_forall_notMem] at hc
    --     specialize hc y_1
    --     rw [G.mem_neighborSet] at hc
    --     exact hc heG_1
    --   by_cases hx_1 : x_1 = p_y
    --   · rw [Sym2.eq_swap,hx_1]
    --     exact n_ih2
    -- · sorry


    -- have := hconn.preconnected
    -- have := this.exists_adj_of_nontrivial v



  -- have := del_deg_zero_iff G (G' := W.toSubgraph.spanningCoe) (by rw [W.toSubgraph.edgeSet_spanningCoe]; intro x hx; exact W.toSubgraph.edgeSet_subset hx )
  -- --first vertex in support
  -- have hvs : v ∈ W.support := by exact W.start_mem_support
  -- have hwu_v := hwu v hvs
  -- have := this v
  -- rw [←W.edgeSet_toSubgraph,← W.toSubgraph.edgeSet_spanningCoe] at hwu_v
  -- rw [this] at hwu_v
  --v is not isolated, either its only neighbour is on the og walk, which means
  --we are still on the og walk, or there are at least two neighbours and one of which
  --is in the y direction.

  --use hwu_v to conclude it is on the OG walk as well, repeat to get the edge x,y is in W?



end



section




  -- refine fun hEw ↦ ?_
  -- · rw [hW.isEulerian_iff, Set.ext_iff]
  --   intro x
  --   cases x
  --   expose_names
  --   refine ⟨W.edges_subset_edgeSet (e := s(x, y)) ,?_⟩
  --   intro hx
  --   have t1 := W.edgeSet_toSubgraph ▸ W.toSubgraph.edgeSet_spanningCoe
  --   have := del_deg_zero_iff G  (G' := W.toSubgraph.spanningCoe) (by rw [W.toSubgraph.edgeSet_spanningCoe];exact W.toSubgraph.edgeSet_subset )
  --   rw [←t1] at hEw
  --   specialize this x
  --   specialize hEw x
  --   rw [this] at hEw
  --   specialize hEw y
  --   rw [←t1]
  --   rw [G.mem_edgeSet] at hx
  --   specialize hEw (G.adj_comm x y |>.mp hx)
  --   rw [adj_comm,← mem_edgeSet] at hEw
  --   exact hEw


    /-

    Since x is not in the edge set, the connectedness of G means we can reach it from W

    Start a Walk `W'` from any vertex `u` to `x`.

    At every step, starting from u, the 0 degree ensures the vertex adjacent on the walk
    must be in W.

    This will lead to x being in W, a contradiction.


    -/
end

#check SimpleGraph.Walk.isCycle_def
#check SimpleGraph.Walk.IsCycle.ncard_neighborSet_toSubgraph_eq_two
/-- If `W` is a non-Eulerian closed trail in a connected graph `G` with all even degrees,
then there exists a vertex `u ∈ W.support` that is incident to an edge of `G` not in `W`.
This is because `G` is connected and `W` does not cover all edges. -/
lemma exists_support_adj_not_in_trail
    {v : V} {W : G.Walk v v} (hW : W.IsCycle)
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
    {u : V} (hu : u ∈ W.support) [∀ u, ∀ S, Fintype ↑((G.deleteEdges S).neighborSet u)]
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

theorem map_isTrail_iff_of_injective.{u',v} {V : Type u'} {V' : Type v} {G : SimpleGraph V}
  [DecidableEq V] [DecidableEq V'] {G' : SimpleGraph V'} {f : G →g G'} {u v : V} {p : G.Walk u v}
  (hinj : Function.Injective f) :
  (p.map f).IsTrail ↔ p.IsTrail := by
  induction p with
  | nil => simp only [Walk.map_nil, Walk.IsTrail.nil]
  | cons _ _ ih =>
    rw [Walk.map_cons, Walk.isTrail_cons, ih, Walk.isTrail_cons]
    apply and_congr_right'
    rw [← Sym2.map_mk, Walk.edges_map, ← List.mem_map_of_injective (Sym2.map.injective hinj)]

theorem map_isEulerian_iff_of_injective.{u',v} {V : Type u'} {V' : Type v} {G : SimpleGraph V}
  [DecidableEq V] [DecidableEq V'] {G' : SimpleGraph V'} {f : G →g G'} {u v : V} {p : G.Walk u v}
  (hinj : Function.Injective f) :
  (p.map f).IsEulerian ↔ p.IsEulerian := by
  simp only [Walk.isEulerian_iff]
  suffices h : (∀ e ∈ G'.edgeSet, e ∈ (Walk.map f p).edges) ↔ ∀ e ∈ G.edgeSet, e ∈ p.edges by
    simp only [map_isTrail_iff_of_injective hinj, h]
  induction p with
  | nil =>
      simp
      refine ⟨fun hne ↦ (fun e hne' ↦ hne (Sym2.map (⇑f) e) (f.map_mem_edgeSet hne')), fun hne ↦ ?_⟩
      · intro e hne'
        have : Hom.subset_preimage_edgeSet f
  | cons _ _ ih =>
    rw [Walk.map_cons, Walk.isTrail_cons, ih, Walk.isTrail_cons]
    apply and_congr_right'
    rw [← Sym2.map_mk, Walk.edges_map, ← List.mem_map_of_injective (Sym2.map.injective hinj)]


lemma exists_euler_circuit_of_connected_even_degree
    (hconn : G.Connected) [hne : Nonempty V]
    (heven : ∀ v : V, Even (G.degree v)) :
    ∃ (v : V) (w : G.Walk v v), w.IsEulerian := by
  -- We generalize and prove by strong induction on the number of edges.
  suffices key : ∀ (n : ℕ) {V : Type u} [Fintype V] [DecidableEq V] [hne : Nonempty V] (G' : SimpleGraph V) [∀G'' : Subgraph G', Fintype ↑G''.verts]
      [∀G'' : Subgraph G',∀x, DecidablePred fun v_1 ↦ v_1 ∈ G''.neighborSet x] [DecidableRel G'.Adj],
      G'.Connected → (∀ v, Even (G'.degree v)) →
      #G'.edgeFinset = n →
      ∃ (v : V) (w : G'.Walk v v), w.IsEulerian from
    key (V := V) _ _  hconn heven rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro V _ _ hne G' _ _ _ hconn' heven' hn
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
  have hE' : ¬W.IsEulerian := by simp [hE]
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
    intro v
    rw! (castMode := .all) [hG''def]
    convert even_degree_deleteEdges_of_trail G' hWtrail heven' v
  -- Step 4b: By connectivity of G', there is a vertex u ∈ W.support that has
  -- an edge in G'' (i.e., an edge of G' not in W).
  have hexists_u : ∃ u ∈ W.support, 0 < G''.degree u := by
    -- Since G' is connected and e₀ ∈ G'.edgeSet \ W.edgeSet, and W is non-empty
    -- (as n > 0 and W is maximal), connectivity of G' ensures some vertex of W
    -- is incident to an edge not in W.
    rw! (castMode := .all) [hG''def]
    by_contra! hc
    simp at hc
    rw [Eulerian_iff_deg_zero G' (v := v₀) (W := W) hWtrail hconn'] at hc
    exact hE' hc
    -- have : W.edgeSet = W.toSubgraph.spanningCoe.edgeSet := by simp
    -- rw [this] at hc
    -- simp at hc
    -- rw [Eulerian_iff_deg_zero G' (v := v₀) (W := W)] at hc
    -- conv =>
    --   rhs
    --   intro u
    --   rw [this u]
    -- use W.getVert 0
    -- simp
    -- have : W.getVert 0 ∈ W.toSubgraph.spanningCoe.support := by
    --   have := W.toSubgraph_adj_getVert (hWlen ▸ hm_pos)
    --   rw [← W.toSubgraph.spanningCoe_adj] at this
    --   rw [mem_support]
    --   use W.getVert (0 + 1)
    -- simp at this
    -- conv =>
    --   rhs
    --   simp [this]
    -- apply Nat.sub_pos_of_lt
  obtain ⟨u, hu_supp, hu_deg⟩ := hexists_u
  -- Step 4c: The connected component of G'' containing u has fewer edges than G',
  -- is connected, and has all even degrees. By the inductive hypothesis, it has
  -- an Eulerian circuit W'.
  -- (We work with the full G'' for simplicity; the argument applies to the component.)
  -- G'' has strictly fewer edges than G':
  have hG''_lt : #G''.edgeFinset < n := by
    -- G''.edgeFinset ⊂ G'.edgeFinset since W has ≥ 1 edge (m > 0).
    rw [←hn]; apply Finset.card_lt_card
    refine ⟨edgeFinset_mono (deleteEdges_le W.edgeSet), fun hsub => ?_⟩
    -- Some edge of W is in G' but not in G'' → contradicts hsub
    have hWne : W.edges ≠ [] :=
      Walk.edges_eq_nil.not.mpr (Walk.not_nil_iff_lt_length.mpr (hWlen ▸ hm_pos))
    have he₁mem : W.edges.head hWne ∈ W.edges := List.head_mem hWne
    have he₁G' := (G'.mem_edgeFinset (e := W.edges.head hWne)).mpr (W.edges_subset_edgeSet he₁mem)
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
    set uComp := ((G''.connectedComponentMk u).toSimpleGraph) with huc
    --via C.toSubgraph.coe = uComp , #edgeset  C.toSubgrph = C.tosubgraph.coe , and ≤
    have := (G''.connectedComponentMk u).coe_toSubgraph
    haveI : ∀ u,  Fintype ↥(G''.connectedComponentMk u) := by
      exact fun u ↦ Fintype.ofFinite ↥(G''.connectedComponentMk u)
    haveI :  DecidableRel uComp.Adj := by exact Classical.decRel uComp.Adj
    haveI : Fintype ↑uComp.edgeSet := by (expose_names; exact uComp.fintypeEdgeSet)

    haveI :  (G''_1 : uComp.Subgraph) → Fintype ↑G''_1.verts := fun G''_1 ↦
      Fintype.ofFinite ↑G''_1.verts
    haveI : (G''_1 : uComp.Subgraph) → (x : ↥(G''.connectedComponentMk u)) → DecidablePred fun v_1 ↦ v_1 ∈ G''_1.neighborSet x := by
      exact fun G''_1 x ↦ Classical.decPred fun v_1 ↦ v_1 ∈ G''_1.neighborSet x
    have := (G''.connectedComponentMk u).connected_toSimpleGraph
    haveI neucmp : ∀ u, Nonempty ↥(G''.connectedComponentMk u) := by
      #check G.adj_of_mem_walk_support
      #check this.exists_isPath ⟨u,ConnectedComponent.connectedComponentMk_mem⟩  ⟨v₀,by sorry⟩
      sorry
    have ih' := ih #uComp.edgeFinset ?_ uComp this sorry (by convert rfl)
    obtain ⟨v1,v2,hW⟩ := ih'
    use v1.val
    refine ⟨?_,?_⟩
    · exact v2.map (G''.connectedComponentMk u).toSimpleGraph_hom
    · have htp := v2.map_isTrail_of_injective
        (sorry : Function.Injective (G''.connectedComponentMk u).toSimpleGraph_hom) (hW.isTrail)
      have := v2.support_map (G''.connectedComponentMk u).toSimpleGraph_hom



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
