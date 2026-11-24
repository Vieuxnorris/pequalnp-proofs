import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_614

namespace PEqualNP.Research.Meta612

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def NoFourCycle {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a

def ComputesEdge {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) : Prop :=
  ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
    ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true

private lemma twoNeighbors {n : ℕ} {G : SimpleGraph (Fin n)} (v : Fin n)
    (h : 2 ≤ (G.neighborSet v).ncard) :
    ∃ a b, G.Adj v a ∧ G.Adj v b ∧ a ≠ b := by
  obtain ⟨a, ha, b, hb, hab⟩ := Set.one_lt_ncard_iff_nontrivial.mp h
  exact ⟨a, b, ha, hb, hab⟩

private lemma otherNeighbor {n : ℕ} {G : SimpleGraph (Fin n)} (v w : Fin n)
    (h : 2 ≤ (G.neighborSet v).ncard) :
    ∃ a, G.Adj v a ∧ a ≠ w := by
  obtain ⟨a, b, ha, hb, hab⟩ := twoNeighbors v h
  by_cases haw : a = w
  · exact ⟨b, hb, haw ▸ hab.symm⟩
  · exact ⟨a, ha, haw⟩

-- Cover of the edges whose endpoints both have at least two neighbors.
def InternalCover {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ u v, G.Adj u v → 2 ≤ (G.neighborSet u).ncard → 2 ≤ (G.neighborSet v).ncard →
    u ∈ S ∨ v ∈ S

-- The two separation hypotheses of L-meta-614 follow from absence of a four-cycle.
-- The second argument permits a triangle through the given edge.
theorem internalCoverLower {n k : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (h4 : NoFourCycle G) (hactive : ∀ v, ∃ w, G.Adj v w)
    (hex : ∃ S : Finset (Fin n), InternalCover G S ∧ S.card = k)
    (hmin : ∀ S : Finset (Fin n), InternalCover G S → k ≤ S.card)
    (hmono : Monotone2 C) (heval : ComputesEdge G C) :
    n + k ≤ C.size + 1 := by
  apply PEqualNP.Outside.L_meta_614 n k G C
  · exact hactive
  · intro v w hvw _ hv _
    by_contra! hall
    obtain ⟨a, b, hva, hvb, hab⟩ := twoNeighbors v hv
    have hwa := (hall a).mp hva
    have hwb := (hall b).mp hvb
    exact h4 v a w b hva.ne hvw hvb.ne hwa.ne.symm hab hwb.ne
      hva hwa.symm hwb hvb.symm
  · intro v w hvw hv hw
    obtain ⟨a, hva, haw⟩ := otherNeighbor v w hv
    obtain ⟨b, hwb, hbv⟩ := otherNeighbor w v hw
    refine ⟨a, b, hva, haw, hwb, hbv, ?_⟩
    by_cases hab : a = b
    · exact Or.inl hab
    · refine Or.inr (fun hadj => ?_)
      exact h4 v a b w hva.ne hbv.symm hvw.ne hab haw hwb.ne.symm
        hva hadj hwb.symm hvw.symm
  · exact hex
  · exact hmin
  · exact hmono
  · exact heval

theorem minDegreeTwoLower {n t : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (h4 : NoFourCycle G) (hdeg : ∀ v, 2 ≤ (G.neighborSet v).ncard)
    (hex : ∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧ S.card = t)
    (hmin : ∀ S : Finset (Fin n), CoverPromise.IsVertexCover G S → t ≤ S.card)
    (hmono : Monotone2 C) (heval : ComputesEdge G C) :
    n + t ≤ C.size + 1 := by
  apply internalCoverLower G C h4
  · intro v
    obtain ⟨a, _, ha, _, _⟩ := twoNeighbors v (hdeg v)
    exact ⟨a, ha⟩
  · obtain ⟨S, hS, hs⟩ := hex
    exact ⟨S, fun u v huv _ _ => hS u v huv, hs⟩
  · intro S hS
    exact hmin S (fun u v huv => hS u v huv (hdeg u) (hdeg v))
  · exact hmono
  · exact heval

-- On finite two-regular graphs the degree sum gives exactly one edge per vertex.
-- Thus the desired edge-count lower bound holds for this whole family.
theorem twoRegularEdgeCoverLower {n t : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (h4 : NoFourCycle G) (hdeg : ∀ v, (G.neighborSet v).ncard = 2)
    (hex : ∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧ S.card = t)
    (hmin : ∀ S : Finset (Fin n), CoverPromise.IsVertexCover G S → t ≤ S.card)
    (hmono : Monotone2 C) (heval : ComputesEdge G C) :
    G.edgeSet.ncard + t ≤ C.size + 1 := by
  classical
  have hd : ∀ v, G.degree v = 2 := fun v => by simpa using hdeg v
  have hsum := G.sum_degrees_eq_twice_card_edges
  simp [hd] at hsum
  have hcard : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← G.coe_edgeFinset, Set.ncard_coe_finset]
  have hl := minDegreeTwoLower G C h4 (fun v => (hdeg v).ge) hex hmin hmono heval
  omega

-- Choose one center per star. On the other side every vertex has degree one,
-- so counting degrees there counts all edges. There are no isolated inputs.
theorem starForestEdgeCoverLower {n t : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (centers : Finset (Fin n)) (h4 : NoFourCycle G)
    (hactive : ∀ v, ∃ w, G.Adj v w)
    (hbip : G.IsBipartiteWith (↑centers) (↑(centersᶜ)))
    (hleaf : ∀ v ∈ centersᶜ, (G.neighborSet v).ncard = 1)
    (hmin : ∀ S : Finset (Fin n), CoverPromise.IsVertexCover G S → t ≤ S.card)
    (hmono : Monotone2 C) (heval : ComputesEdge G C) :
    G.edgeSet.ncard + t ≤ C.size + 1 := by
  classical
  have emptyCover : InternalCover G ∅ := by
    intro u v huv hu hv
    rcases hbip.mem_of_adj huv with ⟨_, hv'⟩ | ⟨hu', _⟩
    · have := hleaf v hv'
      omega
    · have := hleaf u hu'
      omega
  have allInputs := internalCoverLower (k := 0) G C h4 hactive
    ⟨∅, emptyCover, rfl⟩ (fun _ _ => Nat.zero_le _) hmono heval
  have hcover : CoverPromise.IsVertexCover G centers := by
    intro u v huv
    rcases hbip.mem_of_adj huv with ⟨hu, _⟩ | ⟨_, hv⟩
    · exact Or.inl hu
    · exact Or.inr hv
  have ht := hmin centers hcover
  have hedge := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges' hbip
  have hsum : ∑ v ∈ centersᶜ, G.degree v = (centersᶜ).card := by
    calc
      _ = ∑ _v ∈ centersᶜ, 1 := by
        apply Finset.sum_congr rfl
        intro v hv
        simpa using hleaf v hv
      _ = _ := by simp
  have hcard : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← G.coe_edgeFinset, Set.ncard_coe_finset]
  have hn : (centersᶜ).card + centers.card = n := by
    simpa using Finset.card_compl_add_card centers
  omega

end PEqualNP.Research.Meta612
