/-
Copyright 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosHajnal.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Basic Lemmas for Erdős–Hajnal on $P_6$-Free Graphs

This file proves foundational equivalences used throughout the formalization:
1. Complement invariance of `kappa` ($\kappa(\overline{G}) = \kappa(G)$) and induced subgraph freeness
   ($G$ is $H$-free iff $\overline{G}$ is $\overline{H}$-free).
2. Relationship between `(kappa G : ℝ) ≥ B` and `(G.cliqueNum : ℝ) ≥ B ∨ (G.indepNum : ℝ) ≥ B`.
3. Small-$n$ Ramsey base cases ($n = 0, 1$, and $\kappa(G) \ge 2$ for all $n \ge 2$).
4. Equivalence between large-$n$ Erdős–Hajnal bounds, universal-$n$ bounds, and
   `Erdos61.IsErdosHajnalLowerBound`.
-/

open Filter Finset SimpleGraph Real

namespace ErdosHajnalP6

variable {V : Type*}

/-- $\kappa(\overline{G}) = \kappa(G)$. -/
@[simp]
theorem kappa_compl (G : SimpleGraph V) : kappa Gᶜ = kappa G := by
  simp only [kappa, cliqueNum_compl, indepNum_compl, max_comm]

theorem cliqueNum_le_kappa (G : SimpleGraph V) : G.cliqueNum ≤ kappa G :=
  le_max_left _ _

theorem indepNum_le_kappa (G : SimpleGraph V) : G.indepNum ≤ kappa G :=
  le_max_right _ _

theorem kappa_cast_ge_iff (G : SimpleGraph V) (b : ℝ) :
    b ≤ (kappa G : ℝ) ↔ b ≤ (G.cliqueNum : ℝ) ∨ b ≤ (G.indepNum : ℝ) := by
  unfold kappa
  rw [Nat.cast_max, le_max_iff]

/-- Complementing commutes with induced subgraph pullback (`SimpleGraph.comap`) along an embedding. -/
@[simp]
theorem comap_compl {W : Type*} (G : SimpleGraph V) (g : W ↪ V) :
    (G.comap g)ᶜ = Gᶜ.comap g := by
  ext u v
  simp [compl_adj, comap_adj, g.injective.eq_iff]

/-- $G$ is induced-$H$-free if and only if $\overline{G}$ is induced-$\overline{H}$-free. -/
theorem isInducedSubgraphFree_compl_iff {W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) :
    IsInducedSubgraphFree G H ↔ IsInducedSubgraphFree Gᶜ Hᶜ := by
  unfold IsInducedSubgraphFree
  apply not_congr
  refine ⟨fun ⟨g, hg⟩ => ⟨g, ?_⟩, fun ⟨g, hg⟩ => ⟨g, ?_⟩⟩
  · rw [hg, comap_compl]
  · rw [← compl_compl H, hg, ← comap_compl, compl_compl]

/-- Specifically, $G$ is $P_6$-free iff $\overline{G}$ is $\overline{P_6}$-free. -/
theorem isP6Free_iff_compl_isP6ComplFree (G : SimpleGraph V) :
    IsInducedSubgraphFree G P6 ↔ IsInducedSubgraphFree Gᶜ P6Compl :=
  isInducedSubgraphFree_compl_iff G P6

/-- $G$ is induced-$H$-free iff there is no graph embedding $H \hookrightarrow_g G$. -/
theorem isInducedSubgraphFree_iff_isEmpty_embedding {W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) :
    IsInducedSubgraphFree G H ↔ IsEmpty (H ↪g G) := by
  unfold IsInducedSubgraphFree
  rw [isEmpty_iff]
  refine ⟨fun h f => h ⟨f.toEmbedding, ?_⟩, fun h ⟨g, hg⟩ => h ?_⟩
  · ext u v
    simp [comap_adj, f.map_adj_iff]
  · refine { toEmbedding := g, map_rel_iff' := ?_ }
    intro u v
    simp [hg, comap_adj]

/-! ### Invariance under Vertex Equivalences and Embeddings -/

theorem isNClique_of_comap {α β : Type*} {G : SimpleGraph β} {f : α ↪ β} {n : ℕ} {s : Finset α}
    (h : (G.comap f).IsNClique n s) : G.IsNClique n (s.map f) := by
  refine ⟨?_, by rw [Finset.card_map, h.card_eq]⟩
  intro x hx y hy hxy
  rcases Finset.mem_map.mp (Finset.mem_coe.mp hx) with ⟨a, ha, rfl⟩
  rcases Finset.mem_map.mp (Finset.mem_coe.mp hy) with ⟨b, hb, rfl⟩
  exact h.isClique ha hb (ne_of_apply_ne f hxy)

theorem cliqueNum_comap_equiv {α β : Type*} (G : SimpleGraph β) (e : α ≃ β) :
    (G.comap e.toEmbedding).cliqueNum = G.cliqueNum := by
  unfold SimpleGraph.cliqueNum
  congr 1
  ext n
  refine ⟨fun ⟨s, hs⟩ => ⟨s.map e.toEmbedding, isNClique_of_comap hs⟩, fun ⟨t, ht⟩ => ?_⟩
  have ht' : ((G.comap e.toEmbedding).comap e.symm.toEmbedding).IsNClique n t := by
    convert ht
    ext u v
    simp
  exact ⟨t.map e.symm.toEmbedding, isNClique_of_comap ht'⟩

theorem indepNum_comap_equiv {α β : Type*} (G : SimpleGraph β) (e : α ≃ β) :
    (G.comap e.toEmbedding).indepNum = G.indepNum := by
  rw [← cliqueNum_compl, ← cliqueNum_compl (G := G), comap_compl]
  exact cliqueNum_comap_equiv Gᶜ e

/-! ### Small-$n$ Base Cases for $\kappa(G)$ -/

section Fintype

variable [Fintype V]

theorem cliqueNum_le_card (G : SimpleGraph V) : G.cliqueNum ≤ Fintype.card V := by
  obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  exact hs.card_eq ▸ Finset.card_le_univ s

theorem indepNum_le_card (G : SimpleGraph V) : G.indepNum ≤ Fintype.card V := by
  rw [← cliqueNum_compl]
  exact cliqueNum_le_card Gᶜ

theorem kappa_le_card (G : SimpleGraph V) : kappa G ≤ Fintype.card V :=
  max_le (cliqueNum_le_card G) (indepNum_le_card G)

/-- On an empty vertex set `Fin 0`, $\kappa(G) = 0$. -/
@[simp]
theorem kappa_zero (G : SimpleGraph (Fin 0)) : kappa G = 0 := by
  have h := kappa_le_card G
  simp at h
  exact h

theorem cliqueNum_pos_of_nonempty [Nonempty V] (G : SimpleGraph V) : 1 ≤ G.cliqueNum := by
  obtain ⟨v⟩ := ‹Nonempty V›
  have hc : G.IsClique ({v} : Finset V) := by simp
  simpa using hc.card_le_cliqueNum

/-- On any nonempty vertex set, $\kappa(G) \ge 1$ (witnessed by a singleton clique). -/
theorem kappa_pos_of_nonempty [Nonempty V] (G : SimpleGraph V) : 1 ≤ kappa G :=
  (cliqueNum_pos_of_nonempty G).trans (cliqueNum_le_kappa G)

/-- On any vertex set with $|V| \ge 2$, $\kappa(G) \ge 2$ (any two distinct vertices form either
a 2-clique or a 2-independent set). -/
theorem kappa_ge_two_of_two_le_card (G : SimpleGraph V) (h : 2 ≤ Fintype.card V) :
    2 ≤ kappa G := by
  classical
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp h
  obtain ⟨u, v, huv⟩ := exists_pair_ne V
  have hcard : ({u, v} : Finset V).card = 2 := Finset.card_pair huv
  by_cases hadj : G.Adj u v
  · have hc : G.IsClique ({u, v} : Finset V) := by
      rw [Finset.coe_pair]
      exact G.isClique_pair.mpr (fun _ => hadj)
    have hle : 2 ≤ G.cliqueNum := hcard ▸ hc.card_le_cliqueNum
    exact hle.trans (cliqueNum_le_kappa G)
  · have hi : Gᶜ.IsClique ({u, v} : Finset V) := by
      rw [Finset.coe_pair]
      exact Gᶜ.isClique_pair.mpr (fun hne => by simp [compl_adj, hne, hadj])
    have hle : 2 ≤ G.indepNum := by
      rw [← cliqueNum_compl]
      exact hcard ▸ hi.card_le_cliqueNum
    exact hle.trans (indepNum_le_kappa G)

end Fintype

/-! ### Extending Large-$n$ Erdős–Hajnal Bounds to All $n$ and Arbitrary Finite Types -/

/--
Any universal bound for all $n \in \mathbb{N}$ immediately implies the `atTop` filter bound
`Erdos61.IsErdosHajnalLowerBound`.
-/
theorem isErdosHajnalLowerBound_of_forall_n {α : Type*} [Fintype α] [DecidableEq α]
    (H : SimpleGraph α) (c : ℝ)
    (h : ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      IsInducedSubgraphFree G H →
        (G.cliqueNum : ℝ) ≥ (n : ℝ) ^ c ∨ (G.indepNum : ℝ) ≥ (n : ℝ) ^ c) :
    Erdos61.IsErdosHajnalLowerBound H (fun n : ℕ => (n : ℝ) ^ c) := by
  unfold Erdos61.IsErdosHajnalLowerBound
  filter_upwards with n G hG
  exact (h n G hG).symm

/--
Given an Erdős–Hajnal lower bound `(n : ℝ) ^ c₀ ≤ (kappa G : ℝ)` for all $n \ge N_0$ (with $N_0 \ge 2$
and $c_0 > 0$), adjusting the exponent to $c = \min(c_0, \log 2 / \log N_0) > 0$ yields a universal
lower bound across all $n \in \mathbb{N}$, the `Erdos61.IsErdosHajnalLowerBound` filter formulation,
and the general finite-type formulation for all `W : Type` with `[Fintype W]`.
-/
theorem erdos_hajnal_all_n_of_large_n {α : Type*} [Fintype α] [DecidableEq α]
    (H : SimpleGraph α) {N₀ : ℕ} (hN₀ : 2 ≤ N₀) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (h_large : ∀ (n : ℕ), N₀ ≤ n → ∀ (G : SimpleGraph (Fin n)),
      IsInducedSubgraphFree G H → (n : ℝ) ^ c₀ ≤ (kappa G : ℝ)) :
    ∃ c > (0 : ℝ),
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)),
        (¬∃ g : α ↪ Fin n, H = G.comap g) →
          (G.cliqueNum : ℝ) ≥ (n : ℝ) ^ c ∨ (G.indepNum : ℝ) ≥ (n : ℝ) ^ c) ∧
      Erdos61.IsErdosHajnalLowerBound H (fun n : ℕ => (n : ℝ) ^ c) ∧
      (∀ (W : Type) [Fintype W] (G : SimpleGraph W),
        IsEmpty (H ↪g G) →
          (G.cliqueNum : ℝ) ≥ (Fintype.card W : ℝ) ^ c ∨
          (G.indepNum : ℝ) ≥ (Fintype.card W : ℝ) ^ c) := by
  let c₁ : ℝ := Real.log 2 / Real.log (N₀ : ℝ)
  let c : ℝ := min c₀ c₁
  have hN₀_cast : (2 : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hN₀
  have hN₀_gt_one : (1 : ℝ) < (N₀ : ℝ) := by linarith
  have hN₀_pos : (0 : ℝ) < (N₀ : ℝ) := by linarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogN₀_pos : 0 < Real.log (N₀ : ℝ) := Real.log_pos hN₀_gt_one
  have hc₁_pos : 0 < c₁ := div_pos hlog2_pos hlogN₀_pos
  have hc_pos : 0 < c := lt_min hc₀ hc₁_pos
  have h_N₀_rpow : (N₀ : ℝ) ^ c₁ = 2 := by
    dsimp [c₁]
    rw [Real.rpow_def_of_pos hN₀_pos, mul_div_cancel₀ _ (ne_of_gt hlogN₀_pos),
      Real.exp_log zero_lt_two]
  have h_all_n : ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      (¬∃ g : α ↪ Fin n, H = G.comap g) →
        (G.cliqueNum : ℝ) ≥ (n : ℝ) ^ c ∨ (G.indepNum : ℝ) ≥ (n : ℝ) ^ c := by
    intro n G hG
    change (n : ℝ) ^ c ≤ (G.cliqueNum : ℝ) ∨ (n : ℝ) ^ c ≤ (G.indepNum : ℝ)
    rw [← kappa_cast_ge_iff]
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [Real.zero_rpow (ne_of_gt hc_pos)]
    rcases eq_or_ne n 1 with rfl | hn1
    · simp only [Nat.cast_one, Real.one_rpow]
      haveI : Nonempty (Fin 1) := ⟨0⟩
      exact_mod_cast kappa_pos_of_nonempty G
    have hn2 : 2 ≤ n := by omega
    have hn_ge_one : (1 : ℝ) ≤ (n : ℝ) := by
      have : 1 ≤ n := by omega
      exact_mod_cast this
    by_cases hnN₀ : N₀ ≤ n
    · have h1 : (n : ℝ) ^ c ≤ (n : ℝ) ^ c₀ :=
        Real.rpow_le_rpow_of_exponent_le hn_ge_one (min_le_left _ _)
      exact h1.trans (h_large n hnN₀ G hG)
    · push_neg at hnN₀
      have hn_le_N₀ : (n : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast le_of_lt hnN₀
      have h1 : (n : ℝ) ^ c ≤ (n : ℝ) ^ c₁ :=
        Real.rpow_le_rpow_of_exponent_le hn_ge_one (min_le_right _ _)
      have h2 : (n : ℝ) ^ c₁ ≤ (N₀ : ℝ) ^ c₁ :=
        Real.rpow_le_rpow (by positivity) hn_le_N₀ (le_of_lt hc₁_pos)
      have h3 : (2 : ℝ) ≤ (kappa G : ℝ) := by
        have hcard : 2 ≤ Fintype.card (Fin n) := by simpa using hn2
        exact_mod_cast kappa_ge_two_of_two_le_card G hcard
      linarith
  refine ⟨c, hc_pos, h_all_n, isErdosHajnalLowerBound_of_forall_n H c h_all_n, ?_⟩
  intro W _ G h_empty
  classical
  let n := Fintype.card W
  let e : Fin n ≃ W := (Fintype.equivFin W).symm
  let G' : SimpleGraph (Fin n) := G.comap e.toEmbedding
  have hG' : ¬∃ g : α ↪ Fin n, H = G'.comap g := by
    rintro ⟨g, hg⟩
    have hf : H ↪g G :=
      { toEmbedding := g.trans e.toEmbedding
        map_rel_iff' := by
          intro u v
          simp [hg, G', comap_adj] }
    exact h_empty.false hf
  have h_res := h_all_n n G' hG'
  rwa [cliqueNum_comap_equiv G e, indepNum_comap_equiv G e] at h_res

end ErdosHajnalP6
