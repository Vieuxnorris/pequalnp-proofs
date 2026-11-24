import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_105_aux

open PEqualNP.ProofComplexity

abbrev V := Fin 12 ⊕ (ℕ × ℕ)
abbrev xp (i : Fin 12) : Literal V := (Sum.inl i, true)
abbrev xn (i : Fin 12) : Literal V := (Sum.inl i, false)
abbrev sp (i j : ℕ) : Literal V := (Sum.inr (i, j), true)
abbrev sn (i j : ℕ) : Literal V := (Sum.inr (i, j), false)

-- The two sides occupy consecutive blocks of six vertices.
def edges : List (Fin 12 × Fin 12) := [(0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11)]

def formula : Set (Clause V) :=
  {C | ∃ e ∈ edges, C = {xp e.1, xp e.2}} ∪
  {C | ∃ i : Fin 12, i.val + 1 < 12 ∧ C = {xn i, sp i.val 0}} ∪
  {C | ∃ (i : Fin 12) (h j : ℕ), i.val = h + 1 ∧ i.val + 1 < 12 ∧ j < 5 ∧
    C = {sn h j, sp i.val j}} ∪
  {C | ∃ (i : Fin 12) (h g : ℕ), i.val = h + 1 ∧ i.val + 1 < 12 ∧ g + 1 < 5 ∧
    C = {xn i, sn h g, sp i.val (g + 1)}} ∪
  {C | ∃ (i : Fin 12) (h : ℕ), i.val = h + 1 ∧ C = {xn i, sn h 4}} ∪
  {C | ∃ j : ℕ, 1 ≤ j ∧ j < 5 ∧ C = {sn 0 j}}

lemma edgeAx (a b : Fin 12) (he : (a, b) ∈ edges) :
    ({xp a, xp b} : Clause V) ∈ formula :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨(a,b), he, rfl⟩))))

lemma startAx (i : Fin 12) (hi : i.val + 1 < 12) :
    ({xn i, sp i.val 0} : Clause V) ∈ formula :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨i, hi, rfl⟩))))

lemma incAx (i : Fin 12) (h g : ℕ) (hi : i.val = h + 1) (hb : i.val + 1 < 12)
    (hg : g + 1 < 5) : ({xn i, sn h g, sp i.val (g+1)} : Clause V) ∈ formula :=
  Or.inl (Or.inl (Or.inr ⟨i, h, g, hi, hb, hg, rfl⟩))

lemma stopAx (i : Fin 12) (h : ℕ) (hi : i.val = h + 1) :
    ({xn i, sn h 4} : Clause V) ∈ formula :=
  Or.inl (Or.inr ⟨i, h, hi, rfl⟩)

def Narrow (C : Clause V) : Prop :=
  ∃ π, IsDerivation formula π ∧ C ∈ π ∧ ∀ D ∈ π, D.card ≤ 3

lemma appendDeriv {p q : List (Clause V)} (hp : IsDerivation formula p)
    (hq : IsDerivation formula q) : IsDerivation formula (p ++ q) := by
  induction hp with
  | nil => exact hq
  | ax _ h ih => exact .ax ih h
  | res _ hC hD h ih =>
    exact .res ih (List.mem_append.mpr (Or.inl hC)) (List.mem_append.mpr (Or.inl hD)) h

lemma given {C : Clause V} (h : C ∈ formula) (hw : C.card ≤ 3) : Narrow C := by
  refine ⟨[C], .ax .nil h, by simp, ?_⟩
  simpa using hw

lemma resolve {C D R : Clause V} (hc : Narrow C) (hd : Narrow D)
    (hr : IsResolvent C D R) (hw : R.card ≤ 3) : Narrow R := by
  obtain ⟨p, hp, hC, wp⟩ := hc
  obtain ⟨q, hq, hD, wq⟩ := hd
  refine ⟨R :: (p ++ q), .res (appendDeriv hp hq) (List.mem_append.mpr (Or.inl hC))
    (List.mem_append.mpr (Or.inr hD)) hr, by simp, ?_⟩
  intro E hE
  rcases List.mem_cons.mp hE with rfl | h
  · exact hw
  rcases List.mem_append.mp h with h | h
  · exact wp _ h
  · exact wq _ h

set_option maxHeartbeats 2000000 in
lemma widthThree (Fs : Set (Clause V)) (hF : Fs = formula) :
    ∃ π, IsRefutation Fs π ∧ ∀ D ∈ π, D.card ≤ 3 := by
  subst Fs
  have h0 : Narrow {xp 0, xp 6} := given (edgeAx 0 6 (by decide)) (by decide)
  have h1 : Narrow {xp 0, xp 7} := given (edgeAx 0 7 (by decide)) (by decide)
  have h2 : Narrow {xp 0, xp 8} := given (edgeAx 0 8 (by decide)) (by decide)
  have h3 : Narrow {xp 0, xp 9} := given (edgeAx 0 9 (by decide)) (by decide)
  have h4 : Narrow {xp 0, xp 10} := given (edgeAx 0 10 (by decide)) (by decide)
  have h5 : Narrow {xp 0, xp 11} := given (edgeAx 0 11 (by decide)) (by decide)
  have h6 : Narrow {xn 6, sp 6 0} := given (startAx 6 (by decide)) (by decide)
  have h7 : Narrow {xp 0, sp 6 0} := resolve h0 h6
    ⟨(Sum.inl (6 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h8 : Narrow {xn 7, sn 6 0, sp 7 1} := given (incAx 7 6 0 (by decide) (by decide) (by decide)) (by decide)
  have h9 : Narrow {sn 6 0, xp 0, sp 7 1} := resolve h1 h8
    ⟨(Sum.inl (7 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h10 : Narrow {xp 0, sp 7 1} := resolve h7 h9
    ⟨(Sum.inr (6, 0) : V), by decide, by decide, by decide⟩ (by decide)
  have h11 : Narrow {xn 8, sn 7 1, sp 8 2} := given (incAx 8 7 1 (by decide) (by decide) (by decide)) (by decide)
  have h12 : Narrow {sn 7 1, xp 0, sp 8 2} := resolve h2 h11
    ⟨(Sum.inl (8 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h13 : Narrow {xp 0, sp 8 2} := resolve h10 h12
    ⟨(Sum.inr (7, 1) : V), by decide, by decide, by decide⟩ (by decide)
  have h14 : Narrow {xn 9, sn 8 2, sp 9 3} := given (incAx 9 8 2 (by decide) (by decide) (by decide)) (by decide)
  have h15 : Narrow {sn 8 2, xp 0, sp 9 3} := resolve h3 h14
    ⟨(Sum.inl (9 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h16 : Narrow {xp 0, sp 9 3} := resolve h13 h15
    ⟨(Sum.inr (8, 2) : V), by decide, by decide, by decide⟩ (by decide)
  have h17 : Narrow {xn 10, sn 9 3, sp 10 4} := given (incAx 10 9 3 (by decide) (by decide) (by decide)) (by decide)
  have h18 : Narrow {sn 9 3, xp 0, sp 10 4} := resolve h4 h17
    ⟨(Sum.inl (10 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h19 : Narrow {xp 0, sp 10 4} := resolve h16 h18
    ⟨(Sum.inr (9, 3) : V), by decide, by decide, by decide⟩ (by decide)
  have h20 : Narrow {xn 11, sn 10 4} := given (stopAx 11 10 (by decide)) (by decide)
  have h21 : Narrow {sn 10 4, xp 0} := resolve h5 h20
    ⟨(Sum.inl (11 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h22 : Narrow {xp 0} := resolve h19 h21
    ⟨(Sum.inr (10, 4) : V), by decide, by decide, by decide⟩ (by decide)
  have h23 : Narrow {xp 1, xp 6} := given (edgeAx 1 6 (by decide)) (by decide)
  have h24 : Narrow {xp 1, xp 7} := given (edgeAx 1 7 (by decide)) (by decide)
  have h25 : Narrow {xp 1, xp 8} := given (edgeAx 1 8 (by decide)) (by decide)
  have h26 : Narrow {xp 1, xp 9} := given (edgeAx 1 9 (by decide)) (by decide)
  have h27 : Narrow {xp 1, xp 10} := given (edgeAx 1 10 (by decide)) (by decide)
  have h28 : Narrow {xp 1, xp 11} := given (edgeAx 1 11 (by decide)) (by decide)
  have h30 : Narrow {xp 1, sp 6 0} := resolve h23 h6
    ⟨(Sum.inl (6 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h32 : Narrow {sn 6 0, xp 1, sp 7 1} := resolve h24 h8
    ⟨(Sum.inl (7 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h33 : Narrow {xp 1, sp 7 1} := resolve h30 h32
    ⟨(Sum.inr (6, 0) : V), by decide, by decide, by decide⟩ (by decide)
  have h35 : Narrow {sn 7 1, xp 1, sp 8 2} := resolve h25 h11
    ⟨(Sum.inl (8 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h36 : Narrow {xp 1, sp 8 2} := resolve h33 h35
    ⟨(Sum.inr (7, 1) : V), by decide, by decide, by decide⟩ (by decide)
  have h38 : Narrow {sn 8 2, xp 1, sp 9 3} := resolve h26 h14
    ⟨(Sum.inl (9 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h39 : Narrow {xp 1, sp 9 3} := resolve h36 h38
    ⟨(Sum.inr (8, 2) : V), by decide, by decide, by decide⟩ (by decide)
  have h41 : Narrow {sn 9 3, xp 1, sp 10 4} := resolve h27 h17
    ⟨(Sum.inl (10 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h42 : Narrow {xp 1, sp 10 4} := resolve h39 h41
    ⟨(Sum.inr (9, 3) : V), by decide, by decide, by decide⟩ (by decide)
  have h44 : Narrow {sn 10 4, xp 1} := resolve h28 h20
    ⟨(Sum.inl (11 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h45 : Narrow {xp 1} := resolve h42 h44
    ⟨(Sum.inr (10, 4) : V), by decide, by decide, by decide⟩ (by decide)
  have h46 : Narrow {xp 2, xp 6} := given (edgeAx 2 6 (by decide)) (by decide)
  have h47 : Narrow {xp 2, xp 7} := given (edgeAx 2 7 (by decide)) (by decide)
  have h48 : Narrow {xp 2, xp 8} := given (edgeAx 2 8 (by decide)) (by decide)
  have h49 : Narrow {xp 2, xp 9} := given (edgeAx 2 9 (by decide)) (by decide)
  have h50 : Narrow {xp 2, xp 10} := given (edgeAx 2 10 (by decide)) (by decide)
  have h51 : Narrow {xp 2, xp 11} := given (edgeAx 2 11 (by decide)) (by decide)
  have h53 : Narrow {xp 2, sp 6 0} := resolve h46 h6
    ⟨(Sum.inl (6 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h55 : Narrow {sn 6 0, xp 2, sp 7 1} := resolve h47 h8
    ⟨(Sum.inl (7 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h56 : Narrow {xp 2, sp 7 1} := resolve h53 h55
    ⟨(Sum.inr (6, 0) : V), by decide, by decide, by decide⟩ (by decide)
  have h58 : Narrow {sn 7 1, xp 2, sp 8 2} := resolve h48 h11
    ⟨(Sum.inl (8 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h59 : Narrow {xp 2, sp 8 2} := resolve h56 h58
    ⟨(Sum.inr (7, 1) : V), by decide, by decide, by decide⟩ (by decide)
  have h61 : Narrow {sn 8 2, xp 2, sp 9 3} := resolve h49 h14
    ⟨(Sum.inl (9 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h62 : Narrow {xp 2, sp 9 3} := resolve h59 h61
    ⟨(Sum.inr (8, 2) : V), by decide, by decide, by decide⟩ (by decide)
  have h64 : Narrow {sn 9 3, xp 2, sp 10 4} := resolve h50 h17
    ⟨(Sum.inl (10 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h65 : Narrow {xp 2, sp 10 4} := resolve h62 h64
    ⟨(Sum.inr (9, 3) : V), by decide, by decide, by decide⟩ (by decide)
  have h67 : Narrow {sn 10 4, xp 2} := resolve h51 h20
    ⟨(Sum.inl (11 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h68 : Narrow {xp 2} := resolve h65 h67
    ⟨(Sum.inr (10, 4) : V), by decide, by decide, by decide⟩ (by decide)
  have h69 : Narrow {xp 3, xp 6} := given (edgeAx 3 6 (by decide)) (by decide)
  have h70 : Narrow {xp 3, xp 7} := given (edgeAx 3 7 (by decide)) (by decide)
  have h71 : Narrow {xp 3, xp 8} := given (edgeAx 3 8 (by decide)) (by decide)
  have h72 : Narrow {xp 3, xp 9} := given (edgeAx 3 9 (by decide)) (by decide)
  have h73 : Narrow {xp 3, xp 10} := given (edgeAx 3 10 (by decide)) (by decide)
  have h74 : Narrow {xp 3, xp 11} := given (edgeAx 3 11 (by decide)) (by decide)
  have h76 : Narrow {xp 3, sp 6 0} := resolve h69 h6
    ⟨(Sum.inl (6 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h78 : Narrow {sn 6 0, xp 3, sp 7 1} := resolve h70 h8
    ⟨(Sum.inl (7 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h79 : Narrow {xp 3, sp 7 1} := resolve h76 h78
    ⟨(Sum.inr (6, 0) : V), by decide, by decide, by decide⟩ (by decide)
  have h81 : Narrow {sn 7 1, xp 3, sp 8 2} := resolve h71 h11
    ⟨(Sum.inl (8 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h82 : Narrow {xp 3, sp 8 2} := resolve h79 h81
    ⟨(Sum.inr (7, 1) : V), by decide, by decide, by decide⟩ (by decide)
  have h84 : Narrow {sn 8 2, xp 3, sp 9 3} := resolve h72 h14
    ⟨(Sum.inl (9 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h85 : Narrow {xp 3, sp 9 3} := resolve h82 h84
    ⟨(Sum.inr (8, 2) : V), by decide, by decide, by decide⟩ (by decide)
  have h87 : Narrow {sn 9 3, xp 3, sp 10 4} := resolve h73 h17
    ⟨(Sum.inl (10 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h88 : Narrow {xp 3, sp 10 4} := resolve h85 h87
    ⟨(Sum.inr (9, 3) : V), by decide, by decide, by decide⟩ (by decide)
  have h90 : Narrow {sn 10 4, xp 3} := resolve h74 h20
    ⟨(Sum.inl (11 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h91 : Narrow {xp 3} := resolve h88 h90
    ⟨(Sum.inr (10, 4) : V), by decide, by decide, by decide⟩ (by decide)
  have h92 : Narrow {xp 4, xp 6} := given (edgeAx 4 6 (by decide)) (by decide)
  have h93 : Narrow {xp 4, xp 7} := given (edgeAx 4 7 (by decide)) (by decide)
  have h94 : Narrow {xp 4, xp 8} := given (edgeAx 4 8 (by decide)) (by decide)
  have h95 : Narrow {xp 4, xp 9} := given (edgeAx 4 9 (by decide)) (by decide)
  have h96 : Narrow {xp 4, xp 10} := given (edgeAx 4 10 (by decide)) (by decide)
  have h97 : Narrow {xp 4, xp 11} := given (edgeAx 4 11 (by decide)) (by decide)
  have h99 : Narrow {xp 4, sp 6 0} := resolve h92 h6
    ⟨(Sum.inl (6 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h101 : Narrow {sn 6 0, xp 4, sp 7 1} := resolve h93 h8
    ⟨(Sum.inl (7 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h102 : Narrow {xp 4, sp 7 1} := resolve h99 h101
    ⟨(Sum.inr (6, 0) : V), by decide, by decide, by decide⟩ (by decide)
  have h104 : Narrow {sn 7 1, xp 4, sp 8 2} := resolve h94 h11
    ⟨(Sum.inl (8 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h105 : Narrow {xp 4, sp 8 2} := resolve h102 h104
    ⟨(Sum.inr (7, 1) : V), by decide, by decide, by decide⟩ (by decide)
  have h107 : Narrow {sn 8 2, xp 4, sp 9 3} := resolve h95 h14
    ⟨(Sum.inl (9 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h108 : Narrow {xp 4, sp 9 3} := resolve h105 h107
    ⟨(Sum.inr (8, 2) : V), by decide, by decide, by decide⟩ (by decide)
  have h110 : Narrow {sn 9 3, xp 4, sp 10 4} := resolve h96 h17
    ⟨(Sum.inl (10 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h111 : Narrow {xp 4, sp 10 4} := resolve h108 h110
    ⟨(Sum.inr (9, 3) : V), by decide, by decide, by decide⟩ (by decide)
  have h113 : Narrow {sn 10 4, xp 4} := resolve h97 h20
    ⟨(Sum.inl (11 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h114 : Narrow {xp 4} := resolve h111 h113
    ⟨(Sum.inr (10, 4) : V), by decide, by decide, by decide⟩ (by decide)
  have h115 : Narrow {xp 5, xp 6} := given (edgeAx 5 6 (by decide)) (by decide)
  have h116 : Narrow {xp 5, xp 7} := given (edgeAx 5 7 (by decide)) (by decide)
  have h117 : Narrow {xp 5, xp 8} := given (edgeAx 5 8 (by decide)) (by decide)
  have h118 : Narrow {xp 5, xp 9} := given (edgeAx 5 9 (by decide)) (by decide)
  have h119 : Narrow {xp 5, xp 10} := given (edgeAx 5 10 (by decide)) (by decide)
  have h120 : Narrow {xp 5, xp 11} := given (edgeAx 5 11 (by decide)) (by decide)
  have h122 : Narrow {xp 5, sp 6 0} := resolve h115 h6
    ⟨(Sum.inl (6 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h124 : Narrow {sn 6 0, xp 5, sp 7 1} := resolve h116 h8
    ⟨(Sum.inl (7 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h125 : Narrow {xp 5, sp 7 1} := resolve h122 h124
    ⟨(Sum.inr (6, 0) : V), by decide, by decide, by decide⟩ (by decide)
  have h127 : Narrow {sn 7 1, xp 5, sp 8 2} := resolve h117 h11
    ⟨(Sum.inl (8 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h128 : Narrow {xp 5, sp 8 2} := resolve h125 h127
    ⟨(Sum.inr (7, 1) : V), by decide, by decide, by decide⟩ (by decide)
  have h130 : Narrow {sn 8 2, xp 5, sp 9 3} := resolve h118 h14
    ⟨(Sum.inl (9 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h131 : Narrow {xp 5, sp 9 3} := resolve h128 h130
    ⟨(Sum.inr (8, 2) : V), by decide, by decide, by decide⟩ (by decide)
  have h133 : Narrow {sn 9 3, xp 5, sp 10 4} := resolve h119 h17
    ⟨(Sum.inl (10 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h134 : Narrow {xp 5, sp 10 4} := resolve h131 h133
    ⟨(Sum.inr (9, 3) : V), by decide, by decide, by decide⟩ (by decide)
  have h136 : Narrow {sn 10 4, xp 5} := resolve h120 h20
    ⟨(Sum.inl (11 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h137 : Narrow {xp 5} := resolve h134 h136
    ⟨(Sum.inr (10, 4) : V), by decide, by decide, by decide⟩ (by decide)
  have h138 : Narrow {xn 0, sp 0 0} := given (startAx 0 (by decide)) (by decide)
  have h139 : Narrow {sp 0 0} := resolve h22 h138
    ⟨(Sum.inl (0 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h140 : Narrow {xn 1, sn 0 0, sp 1 1} := given (incAx 1 0 0 (by decide) (by decide) (by decide)) (by decide)
  have h141 : Narrow {sn 0 0, sp 1 1} := resolve h45 h140
    ⟨(Sum.inl (1 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h142 : Narrow {sp 1 1} := resolve h139 h141
    ⟨(Sum.inr (0, 0) : V), by decide, by decide, by decide⟩ (by decide)
  have h143 : Narrow {xn 2, sn 1 1, sp 2 2} := given (incAx 2 1 1 (by decide) (by decide) (by decide)) (by decide)
  have h144 : Narrow {sn 1 1, sp 2 2} := resolve h68 h143
    ⟨(Sum.inl (2 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h145 : Narrow {sp 2 2} := resolve h142 h144
    ⟨(Sum.inr (1, 1) : V), by decide, by decide, by decide⟩ (by decide)
  have h146 : Narrow {xn 3, sn 2 2, sp 3 3} := given (incAx 3 2 2 (by decide) (by decide) (by decide)) (by decide)
  have h147 : Narrow {sn 2 2, sp 3 3} := resolve h91 h146
    ⟨(Sum.inl (3 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h148 : Narrow {sp 3 3} := resolve h145 h147
    ⟨(Sum.inr (2, 2) : V), by decide, by decide, by decide⟩ (by decide)
  have h149 : Narrow {xn 4, sn 3 3, sp 4 4} := given (incAx 4 3 3 (by decide) (by decide) (by decide)) (by decide)
  have h150 : Narrow {sn 3 3, sp 4 4} := resolve h114 h149
    ⟨(Sum.inl (4 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h151 : Narrow {sp 4 4} := resolve h148 h150
    ⟨(Sum.inr (3, 3) : V), by decide, by decide, by decide⟩ (by decide)
  have h152 : Narrow {xn 5, sn 4 4} := given (stopAx 5 4 (by decide)) (by decide)
  have h153 : Narrow {sn 4 4} := resolve h137 h152
    ⟨(Sum.inl (5 : Fin 12) : V), by decide, by decide, by decide⟩ (by decide)
  have h154 : Narrow ∅ := resolve h151 h153
    ⟨(Sum.inr (4, 4) : V), by decide, by decide, by decide⟩ (by decide)
  obtain ⟨π, hπ, hEmpty, hWidth⟩ := h154
  exact ⟨π, ⟨hπ, hEmpty⟩, hWidth⟩

end PEqualNP.Outside.L_pcx_105_aux



namespace PEqualNP.Outside.L_pcx_105_aux

open PEqualNP.ProofComplexity MvPolynomial

variable {W : Type} [DecidableEq W]

abbrev Poly (W : Type) := MvPolynomial W (ZMod 2)
abbrev Line (F : Set (Clause W)) (d : ℕ) (p : Poly W) := PCDerivable (cnfSystem F) d p

variable {F : Set (Clause W)} {k : ℕ}

noncomputable def factor (l : Literal W) : Poly W :=
  if l.2 = true then 1 + X l.1 else X l.1

lemma factorDegree (l : Literal W) : (factor l).totalDegree ≤ 1 := by
  obtain ⟨v, b⟩ := l
  cases b with
  | false => simp [factor]
  | true => exact (totalDegree_add 1 (X v : Poly W)).trans (by simp)

lemma clauseDegree (C : Clause W) : (clausePoly C).totalDegree ≤ C.card := by
  refine (totalDegree_finsetProd C factor).trans ?_
  simpa using (Finset.sum_le_sum (s := C) (fun l _ => factorDegree l))

lemma cpInsert (l : Literal W) (C : Clause W) (hl : l ∉ C) :
    clausePoly (insert l C) = factor l * clausePoly C := by
  unfold clausePoly factor
  rw [Finset.prod_insert hl]

lemma mulFactor (l : Literal W) {p : Poly W} (hp : Line F (k+1) p) (hd : p.totalDegree ≤ k) :
    Line F (k+1) (factor l * p) := by
  obtain ⟨v, b⟩ := l
  have hx : Line F (k+1) (X v * p) :=
    .mulX v hp ((totalDegree_mul _ _).trans (by rw [totalDegree_X]; omega))
  cases b with
  | false => exact hx
  | true => simpa [factor, add_mul] using (PCDerivable.add hp hx)

lemma pad (t : Literal W) (A B : Clause W) (ha : Line F (k+1) (factor t * clausePoly A))
    (hab : A ⊆ B) (hb : B.card ≤ k) : Line F (k+1) (factor t * clausePoly B) := by
  have grow (s : Clause W) : (A ∪ s).card ≤ k → Line F (k+1) (factor t * clausePoly (A ∪ s)) := by
    induction s using Finset.induction_on with
    | empty => simpa using fun _ : A.card ≤ k => ha
    | @insert l s _ ih =>
      intro bound
      have he : A ∪ insert l s = insert l (A ∪ s) := by ext e; simp
      rw [he] at bound ⊢
      by_cases hm : l ∈ A ∪ s
      · rw [Finset.insert_eq_of_mem hm] at bound ⊢
        exact ih bound
      · rw [Finset.card_insert_of_notMem hm] at bound
        have hdeg := (totalDegree_mul (factor t) (clausePoly (A ∪ s))).trans
          (add_le_add (factorDegree t) (clauseDegree (A ∪ s)))
        have h := mulFactor l (ih (by omega)) (by omega)
        simpa only [cpInsert l _ hm, mul_left_comm] using h
  have hu : A ∪ B = B := Finset.union_eq_right.mpr hab
  simpa only [hu] using grow B (by simpa only [hu] using hb)

lemma pcResolve {C D R : Clause W} (hc : Line F (k+1) (clausePoly C)) (hd : Line F (k+1) (clausePoly D))
    (hr : IsResolvent C D R) (hw : R.card ≤ k) : Line F (k+1) (clausePoly R) := by
  obtain ⟨v, hv, hv', rfl⟩ := hr
  have left : Line F (k+1) (factor (v, true) * clausePoly (C.erase (v, true))) := by
    rw [← cpInsert _ _ (Finset.notMem_erase _ _), Finset.insert_erase hv]
    exact hc
  have right : Line F (k+1) (factor (v, false) * clausePoly (D.erase (v, false))) := by
    rw [← cpInsert _ _ (Finset.notMem_erase _ _), Finset.insert_erase hv']
    exact hd
  have hp := pad _ _ _ left Finset.subset_union_left hw
  have hq := pad _ _ _ right Finset.subset_union_right hw
  have h := PCDerivable.add hp hq
  simpa [factor, add_mul, add_assoc, CharTwo.add_self_eq_zero] using h

lemma simulate {π : List (Clause W)} (hπ : IsDerivation F π) :
    (∀ D ∈ π, D.card ≤ k) → ∀ D ∈ π, Line F (k+1) (clausePoly D) := by
  induction hπ with
  | nil => simp
  | ax _ hC ih =>
    intro hw E he
    rcases List.mem_cons.mp he with rfl | he
    · exact .ax (Or.inr ⟨_, hC, rfl⟩) ((clauseDegree _).trans ((hw _ (by simp)).trans (Nat.le_succ _)))
    · exact ih (fun c h => hw c (List.mem_cons_of_mem _ h)) _ he
  | res _ hC hD hr ih =>
    intro hw E he
    have htail := ih (fun c h => hw c (List.mem_cons_of_mem _ h))
    rcases List.mem_cons.mp he with rfl | he
    · exact pcResolve (htail _ hC) (htail _ hD) hr (hw _ (by simp))
    · exact htail _ he

lemma degreeFour (Fs : Set (Clause V)) (hF : Fs = formula) : PCRefutable (cnfSystem Fs) 4 := by
  subst Fs
  obtain ⟨π, ⟨hπ, h0⟩, hw⟩ := widthThree formula rfl
  simpa [clausePoly, PCRefutable] using simulate hπ hw ∅ h0

end PEqualNP.Outside.L_pcx_105_aux



namespace PEqualNP.Outside.L_pcx_105_aux.Small

open PEqualNP.ProofComplexity

abbrev V := Fin 8 ⊕ (ℕ × ℕ)
abbrev xp (i : Fin 8) : Literal V := (Sum.inl i, true)
abbrev xn (i : Fin 8) : Literal V := (Sum.inl i, false)
abbrev sp (i j : ℕ) : Literal V := (Sum.inr (i, j), true)
abbrev sn (i j : ℕ) : Literal V := (Sum.inr (i, j), false)

-- In this order the four consecutive pairs give a perfect matching.
def edges : List (Fin 8 × Fin 8) := [(0, 1), (0, 3), (0, 5), (0, 7), (2, 1), (2, 3), (2, 5), (2, 7), (4, 1), (4, 3), (4, 5), (4, 7), (6, 1), (6, 3), (6, 5), (6, 7)]

def formula : Set (Clause V) :=
  {C | ∃ e ∈ edges, C = {xp e.1, xp e.2}} ∪
  {C | ∃ i : Fin 8, i.val + 1 < 8 ∧ C = {xn i, sp i.val 0}} ∪
  {C | ∃ (i : Fin 8) (h j : ℕ), i.val = h + 1 ∧ i.val + 1 < 8 ∧ j < 3 ∧
    C = {sn h j, sp i.val j}} ∪
  {C | ∃ (i : Fin 8) (h g : ℕ), i.val = h + 1 ∧ i.val + 1 < 8 ∧ g + 1 < 3 ∧
    C = {xn i, sn h g, sp i.val (g + 1)}} ∪
  {C | ∃ (i : Fin 8) (h : ℕ), i.val = h + 1 ∧ C = {xn i, sn h 2}} ∪
  {C | ∃ j : ℕ, 1 ≤ j ∧ j < 3 ∧ C = {sn 0 j}}

lemma edgeAx (a b : Fin 8) (he : (a, b) ∈ edges) :
    ({xp a, xp b} : Clause V) ∈ formula :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨(a,b), he, rfl⟩))))

lemma startAx (i : Fin 8) (hi : i.val + 1 < 8) :
    ({xn i, sp i.val 0} : Clause V) ∈ formula :=
  Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨i, hi, rfl⟩))))

lemma incAx (i : Fin 8) (h g : ℕ) (hi : i.val = h + 1) (hb : i.val + 1 < 8)
    (hg : g + 1 < 3) : ({xn i, sn h g, sp i.val (g+1)} : Clause V) ∈ formula :=
  Or.inl (Or.inl (Or.inr ⟨i, h, g, hi, hb, hg, rfl⟩))

lemma stopAx (i : Fin 8) (h : ℕ) (hi : i.val = h + 1) :
    ({xn i, sn h 2} : Clause V) ∈ formula :=
  Or.inl (Or.inr ⟨i, h, hi, rfl⟩)


lemma carryAx (i : Fin 8) (h j : ℕ) (hi : i.val = h + 1) (hb : i.val + 1 < 8)
    (hj : j < 3) : ({sn h j, sp i.val j} : Clause V) ∈ formula :=
  Or.inl (Or.inl (Or.inl (Or.inr ⟨i, h, j, hi, hb, hj, rfl⟩)))

abbrev Low (C : Clause V) := PEqualNP.Outside.L_pcx_105_aux.Line formula 3 (clausePoly C)

lemma base {C : Clause V} (h : C ∈ formula) (hw : C.card ≤ 3) : Low C :=
  .ax (Or.inr ⟨C, h, rfl⟩) ((PEqualNP.Outside.L_pcx_105_aux.clauseDegree C).trans hw)

lemma degreeThree (Fi : Set (Clause V)) (hF : Fi = formula) : PCRefutable (cnfSystem Fi) 3 := by
  subst Fi
  have h0 : Low {xp 0, xp 1} := base (edgeAx 0 1 (by decide)) (by decide)
  have h1 : Low {xn 0, sp 0 0} := base (startAx 0 (by decide)) (by decide)
  have h2 : Low {xn 1, sp 1 0} := base (startAx 1 (by decide)) (by decide)
  have h3 : Low {xp 1, sp 0 0} := pcResolve (k := 2) h0 h1
    ⟨(Sum.inl (0 : Fin 8) : V), by decide, by decide, by decide⟩ (by decide)
  have h4 : Low {sn 0 0, sp 1 0} := base (carryAx 1 0 0 (by decide) (by decide) (by decide)) (by decide)
  have h5 : Low {xp 1, sp 1 0} := pcResolve (k := 2) h3 h4
    ⟨(Sum.inr (0, 0) : V), by decide, by decide, by decide⟩ (by decide)
  have h6 : Low {sp 1 0} := pcResolve (k := 2) h5 h2
    ⟨(Sum.inl (1 : Fin 8) : V), by decide, by decide, by decide⟩ (by decide)
  have h7 : Low {xp 2, xp 3} := base (edgeAx 2 3 (by decide)) (by decide)
  have h8 : Low {xn 2, sn 1 0, sp 2 1} := base (incAx 2 1 0 (by decide) (by decide) (by decide)) (by decide)
  have h9 : Low {xn 2, sp 2 1} := pcResolve (k := 2) h6 h8
    ⟨(Sum.inr (1, 0) : V), by decide, by decide, by decide⟩ (by decide)
  have h10 : Low {sn 1 0, sp 2 0} := base (carryAx 2 1 0 (by decide) (by decide) (by decide)) (by decide)
  have h11 : Low {sp 2 0} := pcResolve (k := 2) h6 h10
    ⟨(Sum.inr (1, 0) : V), by decide, by decide, by decide⟩ (by decide)
  have h12 : Low {xn 3, sn 2 0, sp 3 1} := base (incAx 3 2 0 (by decide) (by decide) (by decide)) (by decide)
  have h13 : Low {xn 3, sp 3 1} := pcResolve (k := 2) h11 h12
    ⟨(Sum.inr (2, 0) : V), by decide, by decide, by decide⟩ (by decide)
  have h14 : Low {xp 3, sp 2 1} := pcResolve (k := 2) h7 h9
    ⟨(Sum.inl (2 : Fin 8) : V), by decide, by decide, by decide⟩ (by decide)
  have h15 : Low {sn 2 1, sp 3 1} := base (carryAx 3 2 1 (by decide) (by decide) (by decide)) (by decide)
  have h16 : Low {xp 3, sp 3 1} := pcResolve (k := 2) h14 h15
    ⟨(Sum.inr (2, 1) : V), by decide, by decide, by decide⟩ (by decide)
  have h17 : Low {sp 3 1} := pcResolve (k := 2) h16 h13
    ⟨(Sum.inl (3 : Fin 8) : V), by decide, by decide, by decide⟩ (by decide)
  have h18 : Low {xp 4, xp 5} := base (edgeAx 4 5 (by decide)) (by decide)
  have h19 : Low {xn 4, sn 3 1, sp 4 2} := base (incAx 4 3 1 (by decide) (by decide) (by decide)) (by decide)
  have h20 : Low {xn 4, sp 4 2} := pcResolve (k := 2) h17 h19
    ⟨(Sum.inr (3, 1) : V), by decide, by decide, by decide⟩ (by decide)
  have h21 : Low {sn 3 1, sp 4 1} := base (carryAx 4 3 1 (by decide) (by decide) (by decide)) (by decide)
  have h22 : Low {sp 4 1} := pcResolve (k := 2) h17 h21
    ⟨(Sum.inr (3, 1) : V), by decide, by decide, by decide⟩ (by decide)
  have h23 : Low {xn 5, sn 4 1, sp 5 2} := base (incAx 5 4 1 (by decide) (by decide) (by decide)) (by decide)
  have h24 : Low {xn 5, sp 5 2} := pcResolve (k := 2) h22 h23
    ⟨(Sum.inr (4, 1) : V), by decide, by decide, by decide⟩ (by decide)
  have h25 : Low {xp 5, sp 4 2} := pcResolve (k := 2) h18 h20
    ⟨(Sum.inl (4 : Fin 8) : V), by decide, by decide, by decide⟩ (by decide)
  have h26 : Low {sn 4 2, sp 5 2} := base (carryAx 5 4 2 (by decide) (by decide) (by decide)) (by decide)
  have h27 : Low {xp 5, sp 5 2} := pcResolve (k := 2) h25 h26
    ⟨(Sum.inr (4, 2) : V), by decide, by decide, by decide⟩ (by decide)
  have h28 : Low {sp 5 2} := pcResolve (k := 2) h27 h24
    ⟨(Sum.inl (5 : Fin 8) : V), by decide, by decide, by decide⟩ (by decide)
  have h29 : Low {xp 6, xp 7} := base (edgeAx 6 7 (by decide)) (by decide)
  have h30 : Low {xn 6, sn 5 2} := base (stopAx 6 5 (by decide)) (by decide)
  have h31 : Low {xn 6} := pcResolve (k := 2) h28 h30
    ⟨(Sum.inr (5, 2) : V), by decide, by decide, by decide⟩ (by decide)
  have h32 : Low {xp 7} := pcResolve (k := 2) h29 h31
    ⟨(Sum.inl (6 : Fin 8) : V), by decide, by decide, by decide⟩ (by decide)
  have h33 : Low {sn 5 2, sp 6 2} := base (carryAx 6 5 2 (by decide) (by decide) (by decide)) (by decide)
  have h34 : Low {sp 6 2} := pcResolve (k := 2) h28 h33
    ⟨(Sum.inr (5, 2) : V), by decide, by decide, by decide⟩ (by decide)
  have h35 : Low {xn 7, sn 6 2} := base (stopAx 7 6 (by decide)) (by decide)
  have h36 : Low {xn 7} := pcResolve (k := 2) h34 h35
    ⟨(Sum.inr (6, 2) : V), by decide, by decide, by decide⟩ (by decide)
  have h37 : Low ∅ := pcResolve (k := 2) h32 h36
    ⟨(Sum.inl (7 : Fin 8) : V), by decide, by decide, by decide⟩ (by decide)
  simpa [Low, clausePoly, PCRefutable] using h37

end PEqualNP.Outside.L_pcx_105_aux.Small



namespace PEqualNP.Outside.L_pcx_105_aux.Small

open PEqualNP.ProofComplexity MvPolynomial

lemma exactFactorDegree (l : Literal V) : (factor l).totalDegree = 1 := by
  obtain ⟨v,b⟩ := l
  cases b with
  | false => simp [factor]
  | true =>
    change (1 + (X v : Poly V)).totalDegree = 1
    rw [totalDegree_add_eq_right_of_totalDegree_lt (by simp), totalDegree_X]

lemma exactClauseDegree (C : Clause V) :
    clausePoly C ≠ 0 ∧ (clausePoly C).totalDegree = C.card := by
  induction C using Finset.induction_on with
  | empty => simp [clausePoly]
  | @insert l C hl ih =>
    have hf : factor l ≠ 0 := by
      intro h
      have hd := exactFactorDegree l
      simp [h] at hd
    rw [cpInsert l C hl]
    refine ⟨mul_ne_zero hf ih.1, ?_⟩
    rw [totalDegree_mul_of_isDomain hf ih.1, exactFactorDegree, ih.2, Finset.card_insert_of_notMem hl]
    omega

def point : V → ZMod 2
  | Sum.inl _ => 1
  | Sum.inr (_,j) => if j = 0 then 1 else 0

lemma zeroFromLiteral (C : Clause V) (l : Literal V) (hl : l ∈ C)
    (hz : eval point (factor l) = 0) : eval point (clausePoly C) = 0 := by
  change eval point (∏ l ∈ C, factor l) = 0
  rw [map_prod]
  exact Finset.prod_eq_zero hl hz

lemma axZero (p : Poly V) (hp : p ∈ cnfSystem formula) (hd : p.totalDegree ≤ 2) :
    eval point p = 0 := by
  rcases hp with ⟨v,rfl⟩ | ⟨C,hC,rfl⟩
  · rcases v with i | ⟨i,j⟩
    · simp [point, CharTwo.add_self_eq_zero]
    · by_cases h : j = 0 <;> simp [point, h, CharTwo.add_self_eq_zero]
  rcases hC with ((((he | ha) | hb) | hc) | hstop) | hzero
  · obtain ⟨e, _, rfl⟩ := he
    apply zeroFromLiteral _ (xp e.1) (by simp)
    simp [factor, xp, point, CharTwo.add_self_eq_zero]
  · obtain ⟨i, _, rfl⟩ := ha
    apply zeroFromLiteral _ (sp i.val 0) (by simp)
    simp [factor, sp, point, CharTwo.add_self_eq_zero]
  · obtain ⟨i, h, j, _, _, _, rfl⟩ := hb
    by_cases hj : j = 0
    · apply zeroFromLiteral _ (sp i.val j) (by simp)
      simp [factor, sp, point, hj, CharTwo.add_self_eq_zero]
    · apply zeroFromLiteral _ (sn h j) (by simp)
      simp [factor, sn, point, hj]
  · obtain ⟨i, h, g, _, _, _, rfl⟩ := hc
    rw [(exactClauseDegree _).2] at hd
    simp [xn, sn, sp] at hd
  · obtain ⟨i, h, _, rfl⟩ := hstop
    apply zeroFromLiteral _ (sn h 2) (by simp)
    simp [factor, sn, point]
  · obtain ⟨j, hj, _, rfl⟩ := hzero
    apply zeroFromLiteral _ (sn 0 j) (by simp)
    have h : j ≠ 0 := by omega
    simp [factor, sn, point, h]

lemma allLinesZero {p : Poly V} (hp : PCDerivable (cnfSystem formula) 2 p) :
    eval point p = 0 := by
  induction hp with
  | ax h hd => exact axZero _ h hd
  | zero => simp
  | add _ _ hi hj => simp [hi, hj]
  | mulX j _ _ hi => simp [hi]

lemma noDegreeTwo (Fi : Set (Clause V)) (hF : Fi = formula) :
    ¬ PCRefutable (cnfSystem Fi) 2 := by
  subst Fi
  intro h
  have := allLinesZero h
  simpa using this

end PEqualNP.Outside.L_pcx_105_aux.Small



namespace PEqualNP.Outside.L_pcx_105_aux.Lower
abbrev Tag := Fin 26
-- Coordinates of square-free monomials in a quotient of the degree-three space.
-- Each 27-bit entry stores up to three nonzero basis indices, offset by one.
def normalTable : Array Nat := #[
  0x20000003c000007000000d0000018000002c00000500000090000010000001c00000300000050000008000000c0000010000001,
  0x30080200000a0000011000001c0000042000006c00000d00000190000030000005c00000b00000150000028000004c0000090000011,
  0x480c02090100400001d0000030040140208020041003008200401000005e07028040e040081c0601038080206028040c04008180601,
  0x5810020b01804160200800004d000008a00000f00000190280a0105010020a018041402008000044000007600000c41205008240801,
  0x180000030000006000000c0000018000003000001580000000000046000007400002a800004e000008c00000f400001982c0a01,
  0x70180200000b40000020000025000000400000301a0b00834140106824020d040041a07008340c0100000580000010000012000001e,
  0x1e000003c000007800000f000001e00000000000148000026000003e0000034000006038160107028020e048041c08008380e01,
  0xc8000018800002e0000056000009e000011c00001f0000034000005c00000a8000013800002000000ca000018c000030800000f,
  0x1e1107004220d00800000c00000ba000015c0000280000048000007e000001822050084408010880c0211010040000078000066,
  0xce000000000000900000120000000000000000000000000000000000000000000001a8000012000002400000480000090000010,
  0x20000003c260e0084c1a010000018000017800002c00000510000092000001c00000304c0a0109810021301804260200800006c,
  0x5000000a0000000000000000000000000000000000000008000000d800000a0000014000002800000500000388000011,
  0xa83402000003000002f800005900000a4000002000000380000060a8140215020042a0300854040100000e800000480000368000068,
  0x250000041000006e000005800000b0000016000002c00001e00000098000072000002200000400000078541c01,
  0xc17028042e040085c06010b8080200001e800000a0000075000002400001b80000348000000000002c00000580000000000000,
  0xfa000005400003c800001300000e60000044000008000000f0b838021706804000006000006000000b400000240000040000007,
  0xde00001a8000000000001800000300000000000000000000000000a6000012c00002100000380000030000006000000c0000018,
  0x16c00002a000004c000008600000e400000c80000190000032000006400003f000001600000f6000005000003b0000012,
  0x10a0000204000040000001800000fe000005800003e000001400000ee0000048000038000006b0000000000006400000c8000000,
  0x17810022f018045e02008a00e011101c021c0380442070086c0e010d01c0228030044406008700c0110818021b03004340600800008e,
  0x13c3a028047404008e806011d0080230028046004008c0060118008022804004440800870100110820021b040043408008bc0a01,
  0x2200802000027c7605008ec08011d80c023b010046205008c408011880c02310100450090088812010e0240221048043609008681201,
  0x1e0080232028046404008c8060119008022805004440a00870140110828021b05004340a0080000bb000014e44028048804009100601,
  0x18600002b89a050093408012680c024d0100400005e00000a8228140245020048a0300914040100001403c028047804008f00601,
  0x1423d028047a04008f406011e8080233028046604008cc060119808022805804440b0087016011082c021b05804340b0080000d6,
  0x2a810025501804aa020080000d7000018800002bc9c050093808012700c024e0100400005e80000a9230140246020048c03009180401,
  0x3a00000ac0000000000023000003a000000000004880000880000000000000000000d00000ed00001ba00003240000599540a01,
  0x180000030000015800000000000460000074000006000000c00000560000000000011800001d000001800000ac0000000000023,
  0x180000030000006000002b0000000000008c00000e800000c00000180000030000006000002b0000000000008c00000e800000c,
  0x1601c0207020044807008780e01160180206020044806008780c0100000500000248000044800002100000360000208000006000000c,
  0x12028021e05004880d008ec1a0118834022c0480412040089012010f024023a06804600d008b01001040100224040043c08008bc1a01,
  0x3a55068049c0d009181a011e834023306804580b0082c08011202c021e058049a0d009141a011e034023206804580a008280801,
  0x30080200000a0000049800001c0000042000006c00000d000000c00000180000030000006000000c000001800000ac0000000000023,
  0x12824020901004740e008c01c01168200208020044a0800820040117838022d038040e04008940e0103808022d030040c04008940c01,
  0x58100225058041602009341c0122838023c07004640e008b41401050100225050041402009101c011d8380231070045a09008240801,
  0x180000030000006000000c00000180000030000015800000000000460000074aa0e009381c0123038023d07004660e008b41601,
  0x478000086000010600000301a0b00834140106824020d040041a07008340c0100000580000010000012000001e,
  0x1e000003c0000000000029000004c000007c00000780000000000052000009800000f80000000000052000009800000f8000000,
  0x3e000003c000007800000f000001e00000000000148000026000003e000003c000007800000f000000000000a4000013000001f,
  0xc2000018400003080000610000000000000000004a800008b000001e000003c000007800000f000001e00000000000148000026,
  0x52000026400000f800006100000c6000018c000031800006300000c6000018c0000000000029000012e00000780000308000061,
  0x1a08020000026c00004a000008a0000120000021c000042000006300000c20000194000032800006500000ca00001940000328000000,
  0x2789c204f1004000005f00000aa238b82047150408e270811c401000001443e170407c2a080f84e101f080203417040682a080d04e10,
  0x2e0a8205c13840b8200800000ee00001bc000032800005a1585c102b0a8205613840ac200800000d8000018a00002c09e2e0813c5410,
  0xc40000188000031000006200000c4000018800004e0000000000012c000023000007f00000f300001c4000033400005b1705c10,
  0x330d02000000b4000015000009a00000400000188c85c08190ac103213c206423840c83e081906810000013a00000a800004c000008d,
  0x1e000003c000007800000f000001e00000000000148000026000003e0000190000031198b81033158206627840cc47081987c10,
  0x1f80c023f010040c050081808010300c02060100450110088822010e044022108804361100868220100000ca000018c000030800000f,
  0x1b200003180000189400a0128010025001804a0020080000bf000006048028049004009200601240080200000bc7e05008fc0801,
  0x1e8000038c00006700000332e814025d02004ba0300974040100001de000037c00006580000322b814025702004ae030095c0401,
  0x6818022c0880422040089022010f044020000030000006000000c00000180000030000006000002b0000000000008c00000e80000ff,
  0x2e838025707004a00e009201c011f838020e030045a11008440801128440211010040000061741a012b834025006804900d008fc1a01,
  0x4000001940000318000061000001e000003c000007800000f000001e000003c0000000000029000004c000007c220d00800000c,
  0x240000048000009000000f00000cc0000190000031000005c00000ac000013c000023800003e000006800000b80000150000027,
  0xd400001a8000035000006a00000480000090000012,
  0x0,
  0x0,
  0x2400000000000000000000000000000000000000000000035000002400000480000090000012000000000000000000000000000,
  0x480000000000000000000000000000000000000000000006a00000480000090000012,
  0x3400000ce000019c0000338000067000000000000000000000000000000000000000000000000000000,
  0xd4000036000006c00000d800001b0000000000006700000ce00000000000000000000,
  0x38080206028040c040081806010300802280980444130087026011084c021b098043413008000067000000000001b00000360000000,
  0x7600000c4a2050094408012880c02510100400001d0000030248140249020049203009240401000005e07028040e040081c0601,
  0x1c800000f40000199780a012f010025e01804bc020080000f000001c000000f00000191600a012c010025801804b0020080000da,
  0x1604c021302004481300878260100000180000030000006000000c0000018000003000001580000000000046000007400008000000f5,
  0x2c038025107004920e008380e0107018022d09804260400894260109808020000030bc0d009601a01288340249068041a07008340c01,
  0xca000018c000030800000f000001e000003c000007800000f000001e00000000000148000026000003e13068040000061781c01,
  0x880c021101004000007800006600000c8000018800002e0000056000009e000011c00001f0000034000005c00000a80000138000020,
  0xe200001c40000388000010000001e1107004220d00800000c00000ba000015c0000280000048000007e00000182205008440801,
  0x28000005000000a000006c00000ce000000000003880000710000000000000000000000000000000000000000000001a8000071,
  0x14600001000000200000040000008000000d800001b0000036000006c000005000000a0000014,
  0x0,
  0x0,
  0x28000000000000000000000000000000000000002000000360000028000005000000a0000014000000000000000000000000000,
  0x500000000000000000000000000000000000000040000006c000005000000a0000014,
  0x6780000b700000d000001a00000340000068000000000000000000000000000000000000000000000000000000,
  0x7e00000d8000036800006d00000da00001b4000000000006800000d000000000000000000000,
  0x1a8000012000002400000480000090000068000000000001b40000368000000,
  0x10000001b000007400000e800001d000003a000006c00000ce00000000000090000012,
  0x30140206020040c030081804011405402220a8043815008842a010d854021a0a804000038800006d00000d0000000000003a0000074,
  0x625202804a404009480601290080200000e80000180200a0104010020801804100200800002f038140207020040e030081c0401,
  0x7a00000ccbe050097c08012f80c025f010040000788000045000007800000c8b2050096408012c80c025901004000022000003b,
  0xa81002240a8043c1500800000c00000180000030000006000000c000001800000ac0000000000023000003a000040400007b0000046,
  0x29038020e040041c07008380c01168540215020044a1500854040100000185f06804b20d009481a0106820020d038041a06008b02a01,
  0xc60000184000007800000f000001e000003c000007800000f000000000000a4000013000001f0a834020000030be0e009641c01,
  0x880802000003c000033000006400000c4000017000002b000004f000008e00000f800001a000002e0000054000009c0000100000065,
  0xe400001c8000008000000f08838021106804000006000005d00000ae0000140000024000003f000000c11028042204008440601,
  0x980c0213010040000360000067000000000001c80000390000000000000000000000000000000000000000000000d40000390000072,
  0xf000001c40000088000010000001e1307004260d00800000c00000bc00001600000288000049000000e000001826050084c0801,
  0xe400001b4000034000000000000f000001e00000000000000000000000000000000000000040000006c00001e000003c0000078,
  0x14800001040000208000041000008200000dc00001b8000037000006e000005800000b0000016000002c000005800000b0000074,
  0x6000000ab00000940000128000025000004a,
  0x0,
  0x1280000208000037000002c000005800000b0000016000000000000000000000000000000000000000000000000000000,
  0x580000000000000000000000000000000250000041000006e000005800000b0000016000002c00000000000000000000,
  0xd200001a40000348000069000000000000000000000000000000000000000000000000000000000000000000000000000000000,
  0x1a600000dc000037000006e00000dc00001b8000000000006900000d2000000000000000000000000000000039400006800000b8,
  0x1a8000012000002400000480000090000069000000000001b800003700000000000000000000000000000000e8,
  0x92000010400001b800007500000ea00001d400003a800006c00000ce00000000000090000012000000000000000000000000000,
  0x8000000d800000a000001400000280000050000038800006e00000d2000000000003a8000075000000000000000000000000000,
  0xf400001e800003d000007a00000e8000004800003680000680000000000005000000a0000000000000000000000000000000000,
  0xd05c0200001e000003a800007200000dc00001a4000000000007a00000f400000000000000000000000000000001280000208000037,
  0x400c02080100400001781c0a01038100207018040e02008180a01030100206018040c02008a02e011105c021c0b80442170086c2e01,
  0x645a02804b4040096806012d00802000011000001d8000031048140209020041203008240401000007400000c01005008200801,
  0x560000000000011800001d00002040000138000023000003d00000666002804c00400980060130008020000134000022800003c,
  0x30034025a068041a090083410010681c020d0300458170085c08011205c021e0b804000006000000c00000180000030000006000000c,
  0x52000009800000f85c1a0100000186007004b40e00838120107020020e038041c06008b42e010b81002250b8042e0200800000c,
  0x7c00000d0000017000002a000004e0000080000032800006300000c2000003c000007800000f000001e000003c0000078000000,
  0xa0000012000001f8000006088140211020042203008440401000001e0000198000032000006200000b800001580000278000047,
  0x6a00001cc000039800007300000e600000400000078441c010883402000003000002e8000057,
  0xb000001440000248000007000000c130280426040084c0601098080200001b0000033800000000000e600001cc0000000000000,
  0x20000003600000f200001e400003c800007900000e20000044000008000000f09838021306804000006000005e,
  0xe00000182a050085408010a80c02150100400003a000007300000da00001a0000000000007900000f200000000000000000000,
  0xfa00001f400003e8000078000002600001c80000088000010000001e15070042a0d00800000c00000be00001640000290000008,
  0xf200001d4000039800006e00000d2000000000003e800007d0000000000000000000000000000000094000010400001b800007d,
  0x14a00001080000210000042000008400000e000001c00000380000070000006000000c00000180000030000006000000c000007a,
  0xdb000018e00002c4000029800005300000a6000014c00006080000ac0000096000012c000025800004b,
  0x0,
  0xa6000012c00002100000380000030000006000000c0000018000000000000000000000000000000000000000000000000000000,
  0x6000000000000000000000000014c00002580000420000070000006000000c0000018000003000000000000000000000,
  0xd400001a8000035000006a000000000000000000000000000000000000000000000000000000000000000000000000000000000,
  0x1a800000e0000037800006f00000de00001bc000000000006a00000d40000000000000000000000001ee000039800006880000b9,
  0x1a800001200000240000048000009000006a000000000001bc00003780000000000000000000000007c80000e9,
  0x1d6000010800001c000007600000ec00001d800003b000006c00000ce00000000000090000012000000000000000000000000000,
  0x8000000d800000a000001400000280000050000038800006f00000d4000000000003b00000760000000000000000000000000fb,
  0xf600001ec00003d800007b00000e8000004800003680000680000000000005000000a0000000000000000000000000000000000,
  0x2c00001e000003b000007200000de00001a8000000000007b00000f60000000000000000000000000a4000012c0000210000038,
  0x2400001b80000348000000000002c00000580000000000000000000000000000000250000041000006e000005800000b0000016,
  0xfc00001f800000000000000000000000014c0000258000042000007000001f800003f000007e00000fc00001e800000a0000075,
  0x7200000e400000c80000190000032000006400000c800001900000fa00001ec00003c800007600000e600001bc0000350000000,
  0xa8000015000002a00000c2000015a0000130000026000004c0000098000029800002180000430000086000010c00001c8000039,
  0x1e4000038400006600000b500000b6000016c00002d800005b00001b800003200000590000054,
  0x3200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,
  0x8600000e400000c800001900000320000064000000000000000000b6000015000002600000430000072000006400000c8000019,
  0xc80000000000000000016c00002a000004c,
  0xd600001ac0000000000000000020600003e000007380000d2000017400001ac000035800006b00000d600000000000000000000,
  0xd6000000000003800000700000000000000000008200000fa00001d4000035400001c800007000000e000001c00000380000000,
  0xd8000019c0000000000012000002400000000000000000000000000000000000000000000035000002400000480000090000012,
  0xe000001ac000000000007700000ee0000000000000000010500001f800003b0000021800003900000ee00001dc00003b8000077,
  0xd0000000000000a00000140000000000000000000000000000000000000010000001b00000140000028000005000000a0000071,
  0xf800001f00000000000000000020c00003f40000260000043000007200001f000003e000007c00000f800001d0000009000006d,
  0x4a000008200000dc00000b0000016000002c000005800003c000007700000e400001c00000358000000,
  0x8600000e400003f800007f00000fe00001fc00003d000001400000ea000004800003700000690000000000005800000b0000000,
  0x3000001f400003e000007900000ee00001cc000038000006b000000000001fc00003f80000000000000000016800002a000004c,
  0x2400001bc00003500000000000030000006000000000000000000000000014c00002580000420000070000006000000c0000018,
  0x7e000002c00001ec00000a0000076]
-- Each column records the action of one variable on a basis element of degree at most two.
def colTable : Array Nat := #[
  0x20000003c000007000000d0000018000002c00000500000090000010000001c00000300000050000008000000c0000010000001,
  0x40000007c00000f000001d0000038000006c00000d00000190000030000005c00000b00000150000028000004c0000090000011,
  0x6000000bc000017000002d000005800000ac00001500000290000050000009c00001300000250000048000008c0000110000021,
  0x8000000fc00001f000003d000007800000ec00001d0000039000007000000dc00001b0000035000006800000cc0000190000031,
  0xa0000013c000027000004d0000098000012c00002500000490000090000011c00002300000450000088000010c0000210000041,
  0xc0000017c00002f000005d00000b8000016c00002d000005900000b0000015c00002b000005500000a8000014c0000290000051,
  0xe000001bc000037000006d00000d800001ac000035000006900000d0000019c000033000006500000c8000018c0000310000061,
  0x1fc00003f000007d00000f800001ec00003d000007900000f000001dc00003b000007500000e800001cc0000390000071,
  0x0,
  0x0,
  0x0,
  0x0,
  0x0,
  0x0,
  0x0,
  0x400000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,
  0x241101004000010000001f0000004000007800000e82c04010500802090100410020081c04010300802000007000000d800001a,
  0x1020000200000010000001f000003c000007400000e000001b0000034000006400000c05c0401000002c150100400000a04c0401,
  0x190080231010046002008bc0401000011400000700000448000088000010e0000218000042800008400001060000068000041000001a,
  0x8400001040000200fc04011f080203d010047802008ec04011d0080200000e400001c0000037000006c00000d46820080cc0401,
  0x29008025101004a0020093c401027008024d01004000026000004b0000094490100490020091c4010230080245010048802008000043,
  0x118000022cc0020097c04012f008025d01004b82008000005b2d008025901004b0020095c04012b08020550100400002a0000053,
  0xe400001c4000038000006f00000dc00001b4000036000006b00000d400001a400003400000670000040000007c000046800001e,
  0x60000068000001800007f00000fc00001f400003e000007b00000f400001e400003c000007700000ec00001d400003a0000073,
  0x980c0200000482203008000027000004c000009400001200000230580c020a0180412030082006010380c0206018040000110000021,
  0x46000008800001080000840000106000020800000d00000810000100000006800000c80000180b80c0200000582a03008000014,
  0x1980c0232018046203008c006011780c020000250000049800009200001220000240000047800008e000004e00000980000128000024,
  0x86000010800002080000401f80c023e138407a03008f006011d80c023a0180400001c8000038000006e00000d800001a8d04e10,
  0xa65201804a2030094006012789c204e018049a0300800004c0000096000012892030092006012389c2046018048a03009100601,
  0x12e000025800004a98006012f80c025e01804ba03009704e1000000b65a01804b2030096006012b80c025613840aa03008000054,
  0xe600001c8000038800007000000de00001b8000036800006c00000d600001a8000034800006800000ce000026800004c8000098,
  0x8000008400000d800000400000fe00001f800003e800007c00000f600001e800003c800007800000ee00001d800003a8000074,
  0x2813020040000090440801000005400000a4000002000000400000000b020041404008240801040100207020040c04008000028,
  0x4200000000000470000021000010e000021800000d8000000000010a000006c00004000000190000030170200400000b0540801,
  0x1a0a82033020046404008c4080118010022f0200400004d8000028000005000000000000150000029000005000002400000478000021,
  0x2201002000010c000021000004100000803f020047c2a080f408011e010023b020047404008000039000007000000dc00001b0000035,
  0xa8000014ca40400944080128010024f150409c040093408010000098000012c0000251240801240100247150408c04009140801,
  0x5400000a4000000000000030010025f02004bc040097408012e0a820000016cb4040096408012c010025702004ac2a081540801,
  0xe800001cc000039000007100000e000001bc000037000006d00000d800001ac000035000006900000d0000019c0000150000029,
  0xa00000a0000011000001c000000a00001fc00003f000007d00000f800001ec00003d000007900000f000001dc00003b0000075,
  0xa8140200000502605008000012088140200000b8000000000002d000005800000ac1605008280a01048140208028040e05008180a01,
  0x12600002480000488000022000011c00002280000000000089000011000000700000428000081000003200000602e05008000016,
  0x6a34170406605008c80a01188140230028045e0500800002e000005a00000b0000015800009b000000000000a000004a0000000,
  0x228140244028040000218000042000008200001007e05008f85c101e814023c028047605008e80a01000007200000e000001b8000036,
  0x2a8140200001500000299480a01288140250028049e2e081380a0126814020000130000025800004a248140248028048e2e081180a01,
  0x274000000000009c00000006002804be05009780a012e814025c1704000002d9680a012c814025802804ae05009585c10,
  0xea00001d0000039800007200000e200001c0000037800006e00000da00001b0000035800006a00000d200001a0000033800002d,
  0xc06028040c040081806010300802000001800003f800007e00000fa00001f000003d800007a00000f200001e000003b8000076,
  0x6e000001800001b0000006000006a000001800001a000000f07018020d030040000060000033000006400000c4000018000002f,
  0x4c2503004480600800002311018022103004682008000001f0f01802000007438060086c0c010d0180200000e400001c0000006,
  0x6c00000d400001a0000033000006400000c4000018000002f1a0b8202d03004580600800002b1a0a82000000a45006008d04e10,
  0x15200002a000005380000a6000014a0000290000051800002f00001440000284000050000009f000013c00000e400001c0000037,
  0x16800002cc00005900000b1000006200000c400001880000b0000015e00002b800005680000ac000015600000c000001800000aa,
  0x330d0200000194c83408000006300000c400001840000198000033000006600000cc00005b00000b5000006400000c80000190000032,
  0x7000000dc00001b0000035000006a00000d400001c8000038000006e00000d800001a80000ba000017200002e000005b8000034,
  0xe00000bc0e050081c08010380c0207010040000038000039000007000000dc00001c8000038000006e00000d800001b0000039,
  0xe00001040000038000040000000e000000000001f800003e000001e0e038041a0700800000c000007a00000f000001d800003a,
  0x1f09c2000000984a07008900e01000004622038044207008f84010000003e1e0380400000e8700e010d81c021a038040000218000042,
  0x148000028c00000000000a20000142000028000004f800009e000005e3e170405a07008b00e0100000563e150400000148a00e01,
  0x17c00002f400005e00000bb000008600001080000208000040000007e00000f800001e800003c000007600000e800005300000a5,
  0x196000032800006480000c8000018e00000ec00001d80000c6000018a000031000006180000c20000182000030000001d00000bf,
  0x661f0400000329907c1000000c60000188000030800003d000007a00000f400006700000cd000019800000f000001e000003c,
  0x86000010800002080000400000000000000000000000000d500001a8000034c00001f800000000001a4000034400006800000cf,
  0x1000000e80000180200a01040100208018041002008000008000008600001080000208000043000008400001040000200000040,
  0x9600000200000250000008000000000001240000000000048000008e000003c1c08008341001000001800001180000228000044,
  0x1402002471384000001309410011202002000008c44080088410012388020000007c3c0800800001d0e020021b04004340800800004c,
  0x15800002ac0000000000000000015400002a400005400000a7000006000002788e2e080b41001160200200000ac8e2a080000029,
  0x90000011c00002300000450000088000030800006080000c0000000000002fc00005f00000bd000017800002ec00001d00000ad,
  0x1c0000037c00006f00000dd00001b8000036c00002200000da00001b2000036000006b80000d60000098000012c0000250000049,
  0xcc470800000653211c20000018c0000310000061000008c000011800007200000e300001c400003840000228000045,
  0x3b0000075800004900000000000000000000000000000001d400003a400007400000000000000000039c00007300000e5,
  0x12000011000001d800003104814020902004120300824040100000120000130000025800004a0000098000012c0000250000000,
  0xa8000014c000004800000000000a40000000000028800000000000a0000013c000007838120106824020000030000027000004d,
  0x5228048049e2708000002612824022404804000011888120110824024f1004000000f8781201000003a1c048043609008681201,
  0x16400002c40000000000000000000000002c000005780000ae0000062000029c00004f93c5c1016824022c0480400001593c5410,
  0x1b4000036400006c00000d700001ac000011000006400000c70000000000000000006300000c50000188000030c00001d80000bb,
  0x1e200003c000007780000ee00001da0000150000029800005200000a20000140000027800004e000009a000037000006d8000000,
  0x1989e1000000ca6427840000031800006200000c2000013800007b00000f500001e800003cc000079000004d,
  0x7e00000fb000000000000000000000000000000000000003e800007c80000000000000000000000007c00000f7,
  0x140000134000022800003c00000640a0280414040082806010500802000002800002a0000053000000000003f40000290000000,
  0xd02802000016c000000000005a0000000000016400000000000580000000000015c00002b000000f07028020d050040000060000055,
  0x2b0a82000000a4500a009584e10000004c2505004480a00800002311028022105004ac2008000001f0f028020000074380a0086c1401,
  0x17800002d400000000000000000000000000000005a00000b3000006400002b800005400000a02b0b8202d05004580a00800002b,
  0x38000006f80000de00001ba000011400006b00000cc0000000000000000000000000cb0000194000032400001e00000c3,
  0xb4000016400002c000005700000ac0000154000079000000000001e200003c000007780000ee00001da00001340000708000000,
  0x33158200000194c85608000006300000c400001840000810000101000020000003fc00007f000005b,
  0x105000000000000000000000000000000000000000000000820000000000000000000000000000000103,
  0x1600001540000270000046000007a00000cc16050082c08010580c020b01004000005800005a000000000000000000830000000,
  0xd82c021a05804000000000000000000c0000000000002f800000000000bc000000000002e800005c000001e0e058041a0b00800000c,
  0x565c150400000148a016012e09c2000000984a0b00890160100000462205804420b009704010000003e1e0580400000e8701601,
  0x18800002f400000000000000000000000000000000000000b6000006600002cc00005780000a900001425c170405a0b008b01601,
  0x7200000e300001c4000011800006e80000d7000000000000000000000000000000019c000033400001e80000c9,
  0x408000080800010000001fe00003f800002a8000000000000000003d800007a80000f400001e600001380000768000000,
  0x662e040000032990b81000000c60000188000030800006000000be000017800002e800005c,
  0x0,
  0x180000030000006000000c00000180000030000006000002b0000000000008c00000e800000c000000000000000000000000000,
  0x110000000000000d000000000000000000030000000000000c00000000000030000000000000c00000c40000184000006000000c,
  0x5600000ac00000000000000000000000025800004a80000230000046000008c00004880000000000118000022c00000e800001d,
  0x180000030000006000000000000000000000000000000000000000c40000030000006000000c0000018000003000004e000002b,
  0xc00000180000188000006000000c00000180000000000000000000000000000000030000031000000c,
  0xc40000000000006000000c00000180000030000031000000c00000000000000000006000000c00000180000188000006000000c,
  0x31000006100000c40000184000031000006100000180000030000006000000c,
  0x0,
  0x1a00000301a0b00834140106824020d040041a07008340c0100000580000010000012000001e000001a00000000000000000000,
  0x3a000022400000d8000082000003200000602e0d0080000160a834020000050260d00800001208834020000190000031800000d,
  0x5800000b0000015800002a000005200000a000004c00000970000048000009000001180000920000042000023400000f000001e,
  0x1e834023c06804760d008e81a01000007200000e000001b8000036000006a641a040660d008c81a01188340230068045e0d00800009d,
  0x26834020000130000025800004a24834024806804c847081181a01228340244068040000218000042000008200001007e0d009907c10,
  0x2e83402642e04000002d9681a012c834025806804ae0d00990ac102a8340200001500000299481a0128834025006804c84f081381a01,
  0xda00001b0000035800006a00000d200001a0000033800006400000c60000190000031800006200000c26006804be0d009781a01,
  0xfa00001f000003d800007a00000f200001e000003b800007600000ea00001d0000039800007200000e200001c0000037800006e,
  0x1c0000034000006038160107028020e048041c08008380e01070180200000b400000200000250000004000003800003f800007e,
  0x3c000007400000e000001b0000034000006400000c05c1c01000002c150700400000a04c1c01000002411070040000330000065,
  0x5a00000b4000016000002b000005400000a4000014000009a00001320000094000012000002300001260000084000010000001f,
  0x330f8203d07004780e008ec1c011d0380200000e400001c0000037000006c00000d4cc34080cc1c0119038023107004600e008bc1c01,
  0x27038024d07004000026000004b00000944907004900e009988e1023038024507004880e008000043000008400001040000200fc1c01,
  0x2f038025d07004cc5c08000005b2d038025907004b00e0095c1c013315820550700400002a000005329038025107004a00e009989e10,
  0xdc00001b4000036000006b00000d400001a4000034000006700000cc0000194000032000006300000c40000184c00e0097c1c01,
  0xfc00001f400003e000007b00000f400001e400003c000007700000ec00001d400003a000007300000e400001c4000038000006f,
  0x1e00001940000318000061000001e000003c000007800000f000001e000003c0000000000029000004c000007c000007800007f,
  0x3e00000780000458000000000010c000020c0000000000000000001e00000000000078000000000001e0000000000007800000f,
  0x1e00000000000000000000000000000000a40000148000000000004c000009800004c8000097000012a0000000000047800001f,
  0x1e000003c000007800000f000001e000003c000000000000000000000000000000000000000f000001e000003c000007800000f,
  0x1e000003c000007800000000000000000000000007800000f000001e000003c000007800000f000000000000000000000000000,
  0x1e000003c000007800000f0000000000003c000007800000f000001e000003c00000780000000000000000003c000007800000f,
  0x194000032800006300000c60000184000030800000f,
  0x0,
  0x20000003c000033000006400000c4000017000002b000004f000008e00000f800001a000002e0000054000009c0000100000010,
  0x40000007c000046800008c0000114000021c000042000006b00000d40000040000034800001000000d000000400000338000010,
  0x1540000288000017000002d000013a000027000001500000290000136000009c000013000009a0000130000025800004a0000090,
  0x19e00000f800001f00000cd0000194000031400005f00000ba000017200002e000005b8000034000006800002d800005a00000b0,
  0x9e000013c00007980000ee00001ce00003980000728000047000008e000011c00007100000de00001b0000034800006880000d0,
  0xb8000017000002e000005c00000b8000040c00002b000005600000ac000015800002b00000fe00001f000003dc000027800004f,
  0xd600001a8000034800006800000ce00001ac000035000006900000d0000019c000033000006500000c8000018c0000310000061,
  0x2200001ac000035000006900000d600001a8000034800006800000d000001ac000035000006900000d0000019c0000338000067,
  0x2200000400000078441c010883402000003000002e800005700000a0000012000001f8000006088140211020042203008440401,
  0x1084402000008000000f8782201000003a1c08804361100868220100000e000001bc000008800006e000002200001b4000008800006c,
  0x6200000c0000017800002e16844022c08804000015800002a000005228088040000138000026128440224088040000118882201,
  0x1a600000fc00001f800003e000019c000032c00006300000bf000007200000e000001b8000036000006a00000d00000198000032,
  0xa0000014000002780000f400001de00003a800007480000e80000090000012000002380000e300001be000036400006a80000d4,
  0xc2000017400002e800005d00000ba0000170000082000005700000ae000015c00002b800005600001fe00003e800007c8000050,
  0xd800001c0000037800006e00000da00001b0000035800006a00000d200001a0000033800006600000ca00001900000318000062,
  0x240000048000038000006f00000dc00001c0000037800006e00000da00001b4000038000006f00000dc00001b4000036000006c,
  0x2400001b00000338000000000002400000480000000000000000000000000000000000000000000006a00000480000090000012,
  0x2400000480000338000000000002400000000000090000012000002400000480000090000073000002400001c80000090000071,
  0xce0000048000009000000000000ce00000000000090000067000000000000480000090000000,
  0xd400001a8000035000006a00000d400001a0000000,
  0x0,
  0x0,
  0xe400001c4000036000006c00000d800001b0000036000006700000ce000019c000033800006700000ce00000000000338000000,
  0x980c021301004000009800007300000e600001cc000039000007200000e400001cc000039000007100000e200001c40000388000073,
  0x2600001c40000088000010000001e1307004260d00800000c00000bc00001600000288000049000000e000001826050084c0801,
  0x4622098044213008000020000003e1e0980400000e87026010d84c021a0980400003b8000076000002600001d40000098000074,
  0x6600000c80000188000030000005e00000b85a13008b02601000005600000a80000148a02601000004e00000984a13008902601,
  0x8600001080000208000040000007e00000f800001e800003c000007600000e800001c8000038000006e00000d800001a8000034,
  0x1f600001440000288000050000009e00003d400007800000ec00001d600001240000248000048000008e000039000007000000da,
  0xc60000188000030800005e00000bc000017800002e800005c000020a000016000002c000005800000ae000015800008000000fc,
  0xe200001c4000038800007000000de00001b8000036800006c00000d600001a8000034800006800000ce00001980000328000064,
  0x28000005000000a000001400000ee00001d800003a800007700000ec00001d400003a000007400000ee00001d800003a8000074,
  0x2800001d0000009000006d00000d0000000000000a00000140000000000000000000000000000000000000010000001b0000014,
  0x28000000000000a000001400000d0000000000000a00000000000028000005000000a0000014000002800001e400000a0000078,
  0x16e000000000000000000000000000000028c0000340000014000002800000000000340000000000002800001a00000000000014,
  0x1000000200000040000008000000fc0000678000000000000000000000000000000036000006c00000d800001b0000035,
  0x0,
  0xd000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,
  0xe800001cc000039000007100000da00001b4000036800006d00000d800001a0000034000006800000d0000019c0000340000000,
  0xa8140215020042a03008540401000002a00001e400003c800007900000f000001e000003c000007900000f000001d000003a0000074,
  0x2a00001e00000098000072000002200000400000078541c010a83402000003000002f800005900000a400000200000038000006,
  0x1285402240a8040000118882a011085402000008000000f8782a01000003a1c0a8043615008682a0100000f800001ec00000a800007a,
  0x6a00000d00000198000032000006200000c0000017800002e16854022c0a804000015800002a0000052280a8040000138000026,
  0x8a000011000002180000420000082000010000001f800003e000007a00000f000001d800003a000007200000e000001b8000036,
  0x20200003f4000029000005200000a2000014000002780000f600001e20000130000025800004a000009200001200000238000046,
  0xca0000190000031800006200000c2000017c00002f800005e00000ba0000170000083000005900000b2000016000002b8000056,
  0xea00001d0000039000007200000e200001c0000037800006e00000da00001b0000035800006a00000d200001a00000338000066,
  0x6e000005800000b0000016000002c000005800003e000007b00000f400001f000003d800007a00000f000001e000003b8000076,
  0x2c00001e800000a0000075000002400001b80000348000000000002c00000580000000000000000000000000000000250000041,
  0x5800000b0000000000002c00000580000348000000000002c000000000000b0000016000002c000005800000b000007d,
  0x6c00000d400005c00000000000000000000000005580000a400000d2000005800000b000000000000d2000000000000b0000069,
  0x410000082000010400002000000d300001a000000000000000000000000018000000dc00001b8000037,
  0x25000004a0000094000012400007400000e5,
  0xd200000000000348000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,
  0xea00001d400003a000007300000e400001c4000037000006e00000dc00001b4000036000006900000d200001a40000340000067,
  0xe00000182e050085c08010b80c02170100400000b800007d00000fa00001f400003d000007a00000f400001e400003c0000075,
  0x2e00001f400000a8000079000002600001cc0000088000010000001e17070042e0d00800000c00000c000001680000048000008,
  0x4e00000984a17008902e010000046220b8044217008000020000003e1e0b80400000e8702e010d85c021a0b80400003f800007e,
  0x6e00000d800001a8000034000006600000c80000188000030000005e00000b85a17008b02e01000005600000a80000148a02e01,
  0x8e00001180000228000044000008600001080000208000040000007e00000f800001e800003c000007600000e800001c8000038,
  0xae0000158000081000005400000a600001480000288000050000009e0000138000026800004c000009600001280000248000048,
  0xce0000198000032800006400000c60000188000030800006000000be000017800002e800005c00000b4000016800002c8000058,
  0xee00001d800003a800007400000e600001c8000038800007000000de00001b8000036800006c00000d600001a80000348000068,
  0x96000010800001c00000180000030000006000000c000001800000fe00001f800003e800007c00000f600001e800003c8000078,
  0x3000001f800000b000007b000002800001d8000009000006f00000d4000000000000c0000018000000000000000000000000053,
  0x3000001a800000000000180000030000000000000c000001800000d4000000000000c00000000000030000006000000c0000018,
  0x7000000dc00001b00000350000172000000000000000000b1000015800002940000350000018000003000000000000350000000,
  0x1d20000398000000000000000001b6000010800002100000410000080000035000006880000000000000000031c0000608000038,
  0xa6000014c00002900000fb00001f200003dc00000000000000000096000012c00002500000eb,
  0xd0000019c000035000000000000d400000000000000000000000000000000000000000000000000000000000000000000000000,
  0xf000001d800003b000007500000e800001cc000039000007100000de00001bc000037000006d00000d800001a80000350000069,
  0xa8000013000002180000390000032000006400000c8000019000003200001f800003f000007d00000f600001ec00003d0000079,
  0x32000006000003f800001600000f8000005000003b800001200000e000001ac000000000001900000320000000000000000005b,
  0x640000358000000000003200000640000000000019000003200001ac00000000000190000000000006400000c8000019,
  0x7200000e000001b8000036000006a00002e800000000000b5000016400002b4000053000006b00000320000064000000000006b,
  0x1d800003a8000073800000000001c2000037000002180000420000082000010000006a80000d20000000000033000006400000c2,
  0x20c000041400008200001030000000000015000002980000fd00001f800003e800007c000000000001e40000130000025800004a,
  0xd200001a0000033800006b000000000001ac00000000000000000000000000000000000000000000000000000000002d800005a,
  0xf200001e000003b800007600000ea00001d0000039800007200000e200001c0000037800006e00000da00001b0000035800006a,
  0x3f800007e00000fa00001f000003d800007a]
def lookup (a : Array Nat) (i : Nat) : Nat :=
  ((a[i / 16]?.getD 0) >>> (27*(i % 16))) &&& 0x7ffffff
def entries (n : Nat) : List Nat :=
  if n = 0 then [] else if n < 512 then [n-1] else if n < 262144 then
    [(n &&& 511)-1, (n >>> 9)-1] else [(n &&& 511)-1, ((n >>> 9) &&& 511)-1, (n >>> 18)-1]
def normalAt (i : Nat) : List Nat := entries (lookup normalTable i)
def col (v : Tag) (i : Nat) : List Nat :=
  if i < 127 then entries (lookup colTable (v.val * 127 + i)) else []
def reduce (s : Finset Tag) : List Nat :=
  let mask := ∑ v ∈ s, (1 : Nat) <<< v.val
  if mask &&& 2 != 0 then [] else
  let z := mask >>> 2
  if z = 0 then normalAt 0 else
  let c := z.log2
  let y := z - (1 <<< c)
  if y = 0 then normalAt (1+c) else
  let b := y.log2
  let x := y - (1 <<< b)
  if x = 0 then normalAt (25 + c*(c-1)/2 + b) else
  normalAt (301 + c*(c-1)*(c-2)/6 + b*(b-1)/2 + x.log2)

-- The substitution uses 24 variables. The tags zero and one denote constant one and zero.
def tagTable : Array Nat := #[0, 2, 3, 4, 2, 5, 6, 7, 8, 9, 10, 11, 0, 1, 1, 1, 1, 0, 2, 1, 1, 1, 0, 0, 12, 1, 1, 0, 0, 13, 1, 1, 0, 0, 14, 15, 1, 0, 0, 0, 16, 1, 0, 0, 0, 17, 18, 0, 0, 0, 19, 20, 0, 0, 0, 21, 22, 0, 0, 0, 23, 24, 0, 0, 0, 0, 25]
def tag : PEqualNP.Outside.L_pcx_105_aux.V → Tag
  | .inl i => Fin.ofNat 26 (tagTable[i.val]?.getD 1)
  | .inr (h,j) => if h < 11 ∧ j < 5 then Fin.ofNat 26 (tagTable[12+h*5+j]?.getD 1) else 1
end PEqualNP.Outside.L_pcx_105_aux.Lower

namespace PEqualNP.Outside.L_pcx_105_aux.Lower

def toggle (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x = y then ys else if x < y then x :: y :: ys else y :: toggle x ys

-- Toggle equal entries in pairs to add vectors over the two-element field.
def canonical (xs : List Nat) : List Nat := xs.foldr toggle []

def okAt (v : Tag) (s : Finset Tag) : Bool :=
  canonical ((reduce s).flatMap (col v)) == canonical (reduce (insert v s))

def ok (v : Tag) : Bool :=
  okAt v ∅ && (List.finRange 26).all (fun a =>
    okAt v {a} && (List.finRange 26).all (fun b => okAt v {a,b}))

end PEqualNP.Outside.L_pcx_105_aux.Lower

namespace PEqualNP.Outside.L_pcx_105_aux.Lower

open PEqualNP.ProofComplexity MvPolynomial

abbrev Vec := Nat →₀ ZMod 2
lemma cancelVec (x : Vec) : x + x = 0 := by
  ext i
  simp [CharTwo.add_self_eq_zero]

noncomputable def unitVec (i : Nat) : Vec := Finsupp.single i 1
noncomputable def unpack : List Nat → Vec
  | [] => 0
  | x :: xs => unitVec x + unpack xs

lemma unpackAppend (a b : List Nat) : unpack (a ++ b) = unpack a + unpack b := by
  induction a with
  | nil => simp [unpack]
  | cons x xs ih => simp [unpack, ih, add_assoc]

lemma unpackToggle (x : Nat) (xs : List Nat) :
    unpack (toggle x xs) = unitVec x + unpack xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    by_cases h : x = y
    · subst y
      simp [toggle, unpack, ← add_assoc, cancelVec]
    · by_cases h' : x < y
      · simp [toggle, h, h', unpack]
      · simp [toggle, h, h', unpack, ih, add_left_comm]

lemma unpackCanon (xs : List Nat) : unpack (canonical xs) = unpack xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact (unpackToggle x (canonical xs)).trans (congrArg (unitVec x + ·) ih)

noncomputable def action (v : Tag) : Vec →ₗ[ZMod 2] Vec :=
  Finsupp.linearCombination _ (fun n => unpack (col v n))

lemma actionUnpack (v : Tag) (xs : List Nat) :
    action v (unpack xs) = unpack (xs.flatMap (col v)) := by
  induction xs with
  | nil => simp [unpack]
  | cons x xs ih =>
    simp only [unpack, map_add, List.flatMap_cons, unpackAppend, ih]
    simp [action, unitVec]

lemma fromCheck (v : Tag) (s : Finset Tag) (h : okAt v s = true) :
    action v (unpack (reduce s)) = unpack (reduce (insert v s)) := by
  rw [actionUnpack]
  have he : canonical ((reduce s).flatMap (col v)) = canonical (reduce (insert v s)) :=
    by simpa [okAt] using h
  simpa only [unpackCanon] using congrArg unpack he

lemma compatible (cert : ∀ v, ok v = true) (v : Tag) (s : Finset Tag) (hs : s.card ≤ 2) :
    action v (unpack (reduce s)) = unpack (reduce (insert v s)) := by
  apply fromCheck
  have h := cert v
  simp only [ok, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const] at h
  rcases (show s.card = 0 ∨ s.card = 1 ∨ s.card = 2 by omega) with h0 | h1 | h2
  · obtain rfl := Finset.card_eq_zero.mp h0
    exact h.1
  · obtain ⟨a,rfl⟩ := Finset.card_eq_one.mp h1
    exact (h.2 a).1
  · obtain ⟨a,b,_,rfl⟩ := Finset.card_eq_two.mp h2
    exact (h.2 a).2 b

def shadow (d : V →₀ Nat) : Finset Tag := d.support.image tag

noncomputable def interp : Poly V →ₗ[ZMod 2] Vec :=
  (Finsupp.linearCombination _ (fun d => unpack (reduce (shadow d)))) ∘ₗ
    (AddMonoidAlgebra.coeffLinearEquiv _).toLinearMap

lemma interpMono (d : V →₀ Nat) (c : ZMod 2) :
    interp (monomial d c) = c • unpack (reduce (shadow d)) := by
  change Finsupp.linearCombination _ _ (Finsupp.single d c) = _
  simp

lemma shadowInsert (v : V) (d : V →₀ Nat) :
    shadow (Finsupp.single v 1 + d) = insert (tag v) (shadow d) := by
  have h : (Finsupp.single v 1 + d).support = insert v d.support := by
    ext w
    by_cases hw : w = v
    · subst w
      simp [Finsupp.mem_support_iff]
    · simp [Finsupp.mem_support_iff, Finsupp.single_eq_of_ne (Ne.symm hw), hw]
  simp [shadow, h]

lemma interpMul (cert : ∀ v, ok v = true) (v : V) (p : Poly V) (hd : p.totalDegree ≤ 2) :
    interp (X v * p) = action (tag v) (interp p) := by
  calc
    interp (X v * p) = interp (X v * ∑ d ∈ p.support, monomial d (p.coeff d)) :=
      congrArg (fun z => interp (X v * z)) p.as_sum
    _ = action (tag v) (interp (∑ d ∈ p.support, monomial d (p.coeff d))) := by
      rw [Finset.mul_sum]
      simp only [map_sum]
      apply Finset.sum_congr rfl
      intro d hd'
      have hcard : d.support.card ≤ d.sum (fun _ e => e) := by
        change d.support.card ≤ ∑ i ∈ d.support, d i
        simpa using (Finset.sum_le_sum (s := d.support) (f := fun _ => 1) (g := fun i => d i)
          (fun i hi => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)))
      have hc : (shadow d).card ≤ 2 :=
        Finset.card_image_le.trans (hcard.trans ((le_totalDegree hd').trans hd))
      change interp (monomial (Finsupp.single v 1) 1 * monomial d (p.coeff d)) = _
      rw [monomial_mul_monomial, one_mul, interpMono, interpMono, map_smul, shadowInsert]
      rw [compatible cert _ _ hc]
    _ = action (tag v) (interp p) := congrArg (fun z => action (tag v) (interp z)) p.as_sum.symm

lemma interpOne : interp 1 = unpack (reduce ∅) := by
  rw [one_def, interpMono]
  simp [shadow]

lemma interpBool (v : V) : interp (X v * X v + X v) = 0 := by
  change interp (monomial (Finsupp.single v 1) 1 * monomial (Finsupp.single v 1) 1 +
    monomial (Finsupp.single v 1) 1) = 0
  rw [map_add, monomial_mul_monomial, one_mul, interpMono, interpMono, shadowInsert]
  simp [shadow, cancelVec]

end PEqualNP.Outside.L_pcx_105_aux.Lower

namespace PEqualNP.Outside.L_pcx_105_aux.Lower

open PEqualNP.ProofComplexity MvPolynomial

def applyLit (l : Literal V) (z : List Nat) : List Nat :=
  if l.2 then z ++ z.flatMap (col (tag l.1)) else z.flatMap (col (tag l.1))

def evaluate (l : List (Literal V)) : List Nat := l.foldr applyLit (reduce ∅)

lemma entailClause (cert : ∀ v, ok v = true) (ls : List (Literal V)) (hn : ls.Nodup)
    (hlen : ls.length ≤ 3) : interp (clausePoly ls.toFinset) = unpack (evaluate ls) := by
  induction ls with
  | nil => simpa [clausePoly, evaluate] using interpOne
  | cons l ls ih =>
    have hnot := (List.nodup_cons.mp hn).1
    have htail := ih (List.nodup_cons.mp hn).2 (by simp at hlen; omega)
    have hd : (clausePoly ls.toFinset).totalDegree ≤ 2 := by
      have h₁ := clauseDegree ls.toFinset
      have h₂ := List.toFinset_card_le ls
      simp at hlen
      omega
    rw [List.toFinset_cons, cpInsert _ _ (by simpa using hnot)]
    obtain ⟨v,b⟩ := l
    cases b <;> simp [factor, evaluate, applyLit, add_mul, interpMul cert _ _ hd, htail,
      actionUnpack, unpackAppend, List.foldr_cons]

lemma vanishes (cert : ∀ v, ok v = true) (ls : List (Literal V)) (hn : ls.Nodup)
    (hlen : ls.length ≤ 3) (hz : canonical (evaluate ls) = []) :
    interp (clausePoly ls.toFinset) = 0 := by
  rw [entailClause cert ls hn hlen, ← unpackCanon, hz]
  rfl

def AxOk (ls : List (Literal V)) : Bool := (canonical (evaluate ls)).isEmpty

lemma vanishIf (cert : ∀ v, ok v = true) (ls : List (Literal V)) (hn : ls.Nodup)
    (hlen : ls.length ≤ 3) (hz : AxOk ls = true) :
    interp (clausePoly ls.toFinset) = 0 := by
  exact vanishes cert ls hn hlen (List.isEmpty_iff.mp hz)

lemma edgePass : ∀ e ∈ edges, AxOk [xp e.1, xp e.2] = true ∧ e.1 ≠ e.2 := by
  decide +kernel

lemma startPass : ∀ i : Fin 12, i.val + 1 < 12 → AxOk [xn i, sp i.val 0] = true := by
  decide +kernel

lemma carryPass : ∀ (i : Fin 12) (j : Fin 5), 0 < i.val → i.val + 1 < 12 →
    AxOk [sn (i.val-1) j.val, sp i.val j.val] = true := by
  decide +kernel

lemma incPass : ∀ (i : Fin 12) (g : Fin 4), 0 < i.val → i.val + 1 < 12 →
    AxOk [xn i, sn (i.val-1) g.val, sp i.val (g.val+1)] = true := by
  decide +kernel

lemma stopPass : ∀ i : Fin 12, 0 < i.val → AxOk [xn i, sn (i.val-1) 4] = true := by
  decide +kernel

lemma zeroPass : ∀ j : Fin 5, 1 ≤ j.val → AxOk [sn 0 j.val] = true := by
  decide +kernel

lemma formulaVanishes (cert : ∀ v, ok v = true) (C : Clause V) (h : C ∈ formula) :
    interp (clausePoly C) = 0 := by
  rcases h with ((((he | ha) | hb) | hc) | hd) | hf
  · obtain ⟨e, he, rfl⟩ := he
    have hx := edgePass e he
    simpa [List.toFinset_cons] using vanishIf cert [xp e.1,xp e.2] (by simp [xp, hx.2]) (by simp) hx.1
  · obtain ⟨i, hi, rfl⟩ := ha
    simpa [List.toFinset_cons] using vanishIf cert [xn i,sp i.val 0] (by simp [xn,sp]) (by simp) (startPass i hi)
  · obtain ⟨i, h, j, hi, hb, hj, rfl⟩ := hb
    have eqn : i.val-1 = h := by omega
    have hx := carryPass i ⟨j,hj⟩ (by omega) hb
    simpa [List.toFinset_cons] using vanishIf cert [sn h j,sp i.val j] (by simp [sn,sp]) (by simp) (by simpa [eqn] using hx)
  · obtain ⟨i, h, g, hi, hb, hg, rfl⟩ := hc
    have eqn : i.val-1 = h := by omega
    have hx := incPass i ⟨g,by omega⟩ (by omega) hb
    simpa [List.toFinset_cons] using vanishIf cert [xn i,sn h g,sp i.val (g+1)] (by simp [xn,sn,sp]) (by simp)
      (by simpa [eqn] using hx)
  · obtain ⟨i,h,hi,rfl⟩ := hd
    have eqn : i.val-1 = h := by omega
    have hx := stopPass i (by omega)
    simpa [List.toFinset_cons] using vanishIf cert [xn i,sn h 4] (by simp [xn,sn]) (by simp) (by simpa [eqn] using hx)
  · obtain ⟨j,hlo,hhi,rfl⟩ := hf
    simpa [List.toFinset_cons] using vanishIf cert [sn 0 j] (by simp) (by simp) (zeroPass ⟨j,hhi⟩ hlo)

lemma invariant (cert : ∀ v, ok v = true) {p : Poly V} (h : PCDerivable (cnfSystem formula) 3 p) :
    interp p = 0 := by
  induction h with
  | ax hp _ =>
    rcases hp with ⟨v,rfl⟩ | ⟨c,hc,rfl⟩
    · exact interpBool v
    · exact formulaVanishes cert c hc
  | zero => exact map_zero interp
  | add _ _ h₁ h₂ => simp [h₁,h₂]
  | @mulX v p _ hd ih =>
    by_cases hp : p = 0
    · simp [hp]
    rw [totalDegree_mul_of_isDomain (X_ne_zero v) hp, totalDegree_X] at hd
    rw [interpMul cert _ _ (by omega), ih, map_zero]

lemma noDegreeThreeOfCertificate (cert : ∀ v, ok v = true) (Fs : Set (Clause V))
    (hF : Fs = formula) : ¬ PCRefutable (cnfSystem Fs) 3 := by
  subst Fs
  intro h
  have he := invariant cert h
  rw [interpOne, show reduce ∅ = [0] by decide +kernel] at he
  simpa [unpack, unitVec] using he

end PEqualNP.Outside.L_pcx_105_aux.Lower

namespace PEqualNP.Outside.L_pcx_105_aux.Lower

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row0 : ok 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row1 : ok 1 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row2 : ok 2 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row3 : ok 3 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row4 : ok 4 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row5 : ok 5 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row6 : ok 6 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row7 : ok 7 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row8 : ok 8 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row9 : ok 9 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row10 : ok 10 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row11 : ok 11 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row12 : ok 12 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row13 : ok 13 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row14 : ok 14 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row15 : ok 15 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row16 : ok 16 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row17 : ok 17 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row18 : ok 18 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row19 : ok 19 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row20 : ok 20 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row21 : ok 21 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row22 : ok 22 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row23 : ok 23 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row24 : ok 24 = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma row25 : ok 25 = true := by decide +kernel

lemma certified (v : Tag) : ok v = true := by
  fin_cases v
  · exact row0
  · exact row1
  · exact row2
  · exact row3
  · exact row4
  · exact row5
  · exact row6
  · exact row7
  · exact row8
  · exact row9
  · exact row10
  · exact row11
  · exact row12
  · exact row13
  · exact row14
  · exact row15
  · exact row16
  · exact row17
  · exact row18
  · exact row19
  · exact row20
  · exact row21
  · exact row22
  · exact row23
  · exact row24
  · exact row25

end PEqualNP.Outside.L_pcx_105_aux.Lower

theorem PEqualNP.Outside.L_pcx_105 : (∀ Fi : Set (PEqualNP.ProofComplexity.Clause (Fin 8 ⊕ (ℕ × ℕ))), Fi = {Cei | ∃ eei ∈ ([(0, 1), (0, 3), (0, 5), (0, 7), (2, 1), (2, 3), (2, 5), (2, 7), (4, 1), (4, 3), (4, 5), (4, 7), (6, 1), (6, 3), (6, 5), (6, 7)] : List (Fin 8 × Fin 8)), Cei = {(((Sum.inl eei.1) : Fin 8 ⊕ (ℕ × ℕ)), true), (((Sum.inl eei.2) : Fin 8 ⊕ (ℕ × ℕ)), true)}} ∪ {Cai | ∃ iai : Fin 8, iai.val + 1 < 8 ∧ Cai = {(((Sum.inl iai) : Fin 8 ⊕ (ℕ × ℕ)), false), (((Sum.inr (iai.val, 0)) : Fin 8 ⊕ (ℕ × ℕ)), true)}} ∪ {Cbi | ∃ (ibi : Fin 8) (hbi jbi : ℕ), ibi.val = hbi + 1 ∧ ibi.val + 1 < 8 ∧ jbi < 3 ∧ Cbi = {(((Sum.inr (hbi, jbi)) : Fin 8 ⊕ (ℕ × ℕ)), false), (((Sum.inr (ibi.val, jbi)) : Fin 8 ⊕ (ℕ × ℕ)), true)}} ∪ {Cci | ∃ (ici : Fin 8) (hci gci : ℕ), ici.val = hci + 1 ∧ ici.val + 1 < 8 ∧ gci + 1 < 3 ∧ Cci = {(((Sum.inl ici) : Fin 8 ⊕ (ℕ × ℕ)), false), (((Sum.inr (hci, gci)) : Fin 8 ⊕ (ℕ × ℕ)), false), (((Sum.inr (ici.val, gci + 1)) : Fin 8 ⊕ (ℕ × ℕ)), true)}} ∪ {Cdi | ∃ (idi : Fin 8) (hdi : ℕ), idi.val = hdi + 1 ∧ Cdi = {(((Sum.inl idi) : Fin 8 ⊕ (ℕ × ℕ)), false), (((Sum.inr (hdi, 2)) : Fin 8 ⊕ (ℕ × ℕ)), false)}} ∪ {Cfi | ∃ jfi : ℕ, 1 ≤ jfi ∧ jfi < 3 ∧ Cfi = {(((Sum.inr (0, jfi)) : Fin 8 ⊕ (ℕ × ℕ)), false)}} → PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem Fi) 3 ∧ ¬ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem Fi) 2) ∧ (∀ Fs : Set (PEqualNP.ProofComplexity.Clause (Fin 12 ⊕ (ℕ × ℕ))), Fs = {Ces | ∃ ees ∈ ([(0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11)] : List (Fin 12 × Fin 12)), Ces = {(((Sum.inl ees.1) : Fin 12 ⊕ (ℕ × ℕ)), true), (((Sum.inl ees.2) : Fin 12 ⊕ (ℕ × ℕ)), true)}} ∪ {Cas | ∃ ias : Fin 12, ias.val + 1 < 12 ∧ Cas = {(((Sum.inl ias) : Fin 12 ⊕ (ℕ × ℕ)), false), (((Sum.inr (ias.val, 0)) : Fin 12 ⊕ (ℕ × ℕ)), true)}} ∪ {Cbs | ∃ (ibs : Fin 12) (hbs jbs : ℕ), ibs.val = hbs + 1 ∧ ibs.val + 1 < 12 ∧ jbs < 5 ∧ Cbs = {(((Sum.inr (hbs, jbs)) : Fin 12 ⊕ (ℕ × ℕ)), false), (((Sum.inr (ibs.val, jbs)) : Fin 12 ⊕ (ℕ × ℕ)), true)}} ∪ {Ccs | ∃ (ics : Fin 12) (hcs gcs : ℕ), ics.val = hcs + 1 ∧ ics.val + 1 < 12 ∧ gcs + 1 < 5 ∧ Ccs = {(((Sum.inl ics) : Fin 12 ⊕ (ℕ × ℕ)), false), (((Sum.inr (hcs, gcs)) : Fin 12 ⊕ (ℕ × ℕ)), false), (((Sum.inr (ics.val, gcs + 1)) : Fin 12 ⊕ (ℕ × ℕ)), true)}} ∪ {Cds | ∃ (ids : Fin 12) (hds : ℕ), ids.val = hds + 1 ∧ Cds = {(((Sum.inl ids) : Fin 12 ⊕ (ℕ × ℕ)), false), (((Sum.inr (hds, 4)) : Fin 12 ⊕ (ℕ × ℕ)), false)}} ∪ {Cfs | ∃ jfs : ℕ, 1 ≤ jfs ∧ jfs < 5 ∧ Cfs = {(((Sum.inr (0, jfs)) : Fin 12 ⊕ (ℕ × ℕ)), false)}} → (∃ πas, PEqualNP.ProofComplexity.IsRefutation Fs πas ∧ ∀ Das ∈ πas, Das.card ≤ 3) ∧ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem Fs) 4 ∧ ¬ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem Fs) 3) := by
  constructor
  · intro Fi hi
    exact ⟨PEqualNP.Outside.L_pcx_105_aux.Small.degreeThree Fi hi, PEqualNP.Outside.L_pcx_105_aux.Small.noDegreeTwo Fi hi⟩
  · intro Fs hs
    exact ⟨PEqualNP.Outside.L_pcx_105_aux.widthThree Fs hs, PEqualNP.Outside.L_pcx_105_aux.degreeFour Fs hs,
      PEqualNP.Outside.L_pcx_105_aux.Lower.noDegreeThreeOfCertificate PEqualNP.Outside.L_pcx_105_aux.Lower.certified Fs hs⟩
