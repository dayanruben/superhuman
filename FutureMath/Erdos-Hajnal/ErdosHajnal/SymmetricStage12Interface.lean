/-
Copyright 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosHajnal.BasicLemmas
import ErdosHajnal.Defs
import ErdosHajnal.GenDefs
import ErdosHajnal.LayoutAndSparsification
import ErdosHajnal.P6Baseline
import ErdosHajnal.Stage2Reduction

/-!
# Co-Sparse Peeling, Seinsche Cograph Refinement, Symmetric Layout Refinement, and Stage 1–2 Interface
(Theorem 2 and Lemmas 2, 4, 5, and 7 of `main.tex`, lines 135–142 and 196–413)

This file formalizes the symmetric Stage 1–2 structural reduction framework of `main.tex`
(Part I, Section 4):

1. **Section 1 — Foundational Neighborhood, Cross-Edge, and Greedy Interval Partitioning Helpers**:
   Inclusion-minimal subset extraction (`exists_minimal_subset_ge'`) and greedy contiguous-interval
   partitioning (`exists_disjoint_family_sum_ge'`) used in co-sparse peeling.
2. **Section 2 — Lemma 2 (`pkCompl_free_cosparse_complete_blockade` & `pkCompl_free_cosparse_trigger_pair`,
   `main.tex` lines 196–204)**:
   Unconditional Co-Sparse Complete-Blockade and Trigger-Set Peeling Lemma for all $\overline{P_t}$-free
   graphs ($t \ge 2$), established via $t$-layer expanding towers and backwards induced-$P_t$ extraction
   in the complement graph $\overline{G}$.
3. **Section 3 — Lemma 4(1) & Seinsche's Theorem (`equal_sized_trigger_peeling_cograph` &
   `seinsche_cograph_clique_mul_indep`, `main.tex` lines 219–241)**:
   - **Lemma 4(1)**: Equal-Sized Trigger-Set Peeling to Blockades with Cograph ($P_4$-free) Pattern
     Graphs, preserving pointwise $x$-sparsity in case (a) with zero sub-sampling loss and yielding
     $100\%$ pairwise-pure cograph blockades at $x = 0$.
   - **Seinsche's Theorem (1974)**: Self-contained inductive proof that every $P_4$-free graph $J$
     on $m \ge 2$ vertices has $J$ or $\overline{J}$ disconnected (`exists_pure_bipartition_of_p4_free`)
     and hence satisfies $\omega(J)\alpha(J) \ge |V(J)|$ (`seinsche_cograph_clique_mul_indep`).
4. **Section 4 — Lemma 5 & Lemma 4(2) (`symmetric_layout_refinement_xsp_indep`, `cograph_subst`, &
   `defective_cograph_refinement`, `main.tex` lines 228–277)**:
   - **Lemma 5**: Global-Decided-Pair Symmetric Layout Refinement producing a weakly
     $x_{\mathrm{sp}}$-sparse-or-co-sparse $(\lceil \varepsilon^{-1}\rceil, \lfloor \varepsilon^{(20 C_{\mathrm{cap}} + 4)d^2}|S|\rfloor)$-blockade
     whose output block width depends **only on $\varepsilon$ and is completely independent of $x_{\mathrm{sp}}$**.
   - **Cograph Substitution Closure**: Proof that $P_4$-freeness is closed under vertex substitution (`cograph_subst`).
   - **Lemma 4(2)**: Defective Cograph Refinement extracting a $(2\varepsilon)$-restricted induced
     subgraph of order $\ge \varepsilon^{5C}|S_0|$ via Seinsche homogeneous-blockade degree pruning.
5. **Section 5 — Theorem 2, Viral Leaf-Extension Cores, & Lemma 7(1) (`rodl_theorem_general`,
   `viral_extension_core_of_not_restricted`, `pair_coupled_generalized_nice_of_comb_dichotomy`, &
   `coupled_generalized_nice_of_comb_dichotomy`, `main.tex` lines 135–142 and 288–331)**:
   - **Theorem 2**: General Qualitative Rödl Theorem for arbitrary finite forbidden graphs.
   - **Viral Leaf-Extension Core**: Extraction of $(H_1 - v_0)ᶜ \setminus \{u_0\}$ bases $\Phi$ and
     large extension cores $D$ forcing $100\%$ cross-block completeness in $\{H_1ᶜ, H_2ᶜ\}$-free graphs.
   - **Lemma 7(1)**: Deduction of Coupled Stage-1 Generalized Niceness (`IsPairCoupledGeneralizedNice` /
     `IsCoupledGeneralizedNice`) from the Stage-1 Comb Dichotomy `(CD1)`–`(CD3)` via Markov exact-width
     pointwise sparsity restoration (`markov_pointwise_sparse_exact_size`) and Lemma 5.
6. **Section 6 — Lemma 7(2) (`stage2_gn1_viral_purification`,
   `master_stage2_pair_eh_of_coupled_gen_nice_and_wonderful`, &
   `master_stage2_eh_of_coupled_gen_nice_and_wonderful`, `main.tex` lines 295 and 333–412)**:
   Master Stage-2 Reduction for Leaf-Reducible, Coupled Generalized Nice, and Thresholded Wonderful
   Families via One-Shot Simultaneous Co-Sparse-to-Complete Viral Purification at exact coupled
   sparsity $x_{\mathrm{sp}} = \varepsilon_{\mathrm{GN}}^{3 c_2} = y^{3 a c_2}$, Open-Interval
   $0$-Defect Pure Trigger Extraction, and Zero-Defect Cograph Peeling.
-/

set_option linter.unusedSectionVars false

open Finset SimpleGraph Real ErdosHajnalP6

namespace ErdosHajnalGen

variable {V : Type*} [Fintype V] [DecidableEq V]

/-!
## Section 1: Foundational Neighborhood, Cross-Edge, and Greedy Interval Partitioning Helpers
-/

@[simp]
private theorem mem_neighborFinsetIn' (G : SimpleGraph V) (v u : V) (S : Finset V) :
    u ∈ neighborFinsetIn G v S ↔ u ∈ S ∧ G.Adj v u := by
  classical
  simp [neighborFinsetIn]

private theorem neighborFinsetIn_subset' (G : SimpleGraph V) (v : V) (S : Finset V) :
    neighborFinsetIn G v S ⊆ S := by
  intro u hu
  exact ((mem_neighborFinsetIn' G v u S).mp hu).1

private theorem neighborFinsetIn_mono' (G : SimpleGraph V) (v : V) {S T : Finset V} (h : S ⊆ T) :
    neighborFinsetIn G v S ⊆ neighborFinsetIn G v T := by
  intro u hu
  rw [mem_neighborFinsetIn'] at hu ⊢
  exact ⟨h hu.1, hu.2⟩

private theorem isCompletePair_symm {G : SimpleGraph V} {A B : Finset V}
    (h : IsCompletePair G A B) : IsCompletePair G B A :=
  fun u hu v hv => (h v hv u hu).symm

private theorem isCompletePair_mono {G : SimpleGraph V} {A B A' B' : Finset V}
    (hA : A' ⊆ A) (hB : B' ⊆ B) (h : IsCompletePair G A B) :
    IsCompletePair G A' B' :=
  fun u hu v hv => h u (hA hu) v (hB hv)

private theorem crossEdgeCount_comm' (G : SimpleGraph V) (A B : Finset V) :
    crossEdgeCount G A B = crossEdgeCount G B A := by
  classical
  unfold crossEdgeCount neighborFinsetIn
  simp only [card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  refine sum_congr rfl (fun v _ => sum_congr rfl (fun u _ => ?_))
  rw [adj_comm]

private theorem exists_minimal_subset_ge' {α : Type*} [DecidableEq α] (f : Finset α → ℕ) (w : ℕ)
    (R : Finset α) (hR : w ≤ f R) :
    ∃ R_min ⊆ R, w ≤ f R_min ∧ ∀ r ∈ R_min, f (R_min.erase r) < w := by
  induction hn : R.card using Nat.strong_induction_on generalizing R with
  | _ n ih =>
    subst hn
    by_cases hmin : ∀ r ∈ R, f (R.erase r) < w
    · exact ⟨R, Subset.rfl, hR, hmin⟩
    · push_neg at hmin
      obtain ⟨r, hr, hge⟩ := hmin
      obtain ⟨R_min, hsub, hw_min, hmin'⟩ :=
        ih (R.erase r).card (card_erase_lt_of_mem hr) (R.erase r) hge rfl
      exact ⟨R_min, Subset.trans hsub (erase_subset r R), hw_min, hmin'⟩

private theorem exists_subset_sum_mem_Icc' {α : Type*} [DecidableEq α]
    (R : Finset α) (c : α → ℝ) (w M : ℝ)
    (_hw : 0 ≤ w) (_hM : 0 ≤ M)
    (hc_nonneg : ∀ i ∈ R, 0 ≤ c i) (hc_le : ∀ i ∈ R, c i ≤ M)
    (hsum : w ≤ ∑ i ∈ R, c i) :
    ∃ I ⊆ R, w ≤ ∑ i ∈ I, c i ∧ ∑ i ∈ I, c i ≤ w + M := by
  induction R using Finset.induction_on with
  | empty =>
    refine ⟨∅, Subset.rfl, hsum, ?_⟩
    simp only [sum_empty] at hsum ⊢
    linarith
  | @insert a R ha ih =>
    have hc_nonneg' : ∀ i ∈ R, 0 ≤ c i := fun i hi => hc_nonneg i (mem_insert_of_mem hi)
    have hc_le' : ∀ i ∈ R, c i ≤ M := fun i hi => hc_le i (mem_insert_of_mem hi)
    by_cases hR : w ≤ ∑ i ∈ R, c i
    · obtain ⟨I, hIR, hIw, hIM⟩ := ih hc_nonneg' hc_le' hR
      exact ⟨I, hIR.trans (subset_insert a R), hIw, hIM⟩
    · push_neg at hR
      refine ⟨insert a R, Subset.rfl, hsum, ?_⟩
      rw [sum_insert ha]
      have haM : c a ≤ M := hc_le a (mem_insert_self a R)
      linarith

private theorem exists_disjoint_family_sum_ge' {α : Type*} [DecidableEq α]
    (m : ℕ) (hm : 1 ≤ m) (R : Finset α) (c : α → ℝ) (w M : ℝ)
    (hw : 0 ≤ w) (hM : 0 ≤ M)
    (hc_nonneg : ∀ i ∈ R, 0 ≤ c i) (hc_le : ∀ i ∈ R, c i ≤ M)
    (hsum : (m : ℝ) * (w + M) - M ≤ ∑ i ∈ R, c i) :
    ∃ I : Fin m → Finset α,
      (∀ s : Fin m, I s ⊆ R) ∧
      (∀ s t : Fin m, s ≠ t → Disjoint (I s) (I t)) ∧
      (∀ s : Fin m, w ≤ ∑ i ∈ I s, c i) := by
  induction m generalizing R with
  | zero => omega
  | succ n ih =>
    by_cases hn : n = 0
    · subst hn
      refine ⟨fun _ => R, fun _ => Subset.rfl, ?_, ?_⟩
      · intro s t hst
        exact (hst (Fin.ext (by omega))).elim
      · intro _
        push_cast at hsum
        linarith
    · have hn1 : 1 ≤ n := by omega
      have hn_real : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      have hw_sum : w ≤ ∑ i ∈ R, c i := by
        push_cast at hsum
        nlinarith
      obtain ⟨I₀, hI₀R, hI₀_ge, hI₀_le⟩ :=
        exists_subset_sum_mem_Icc' R c w M hw hM hc_nonneg hc_le hw_sum
      let R' : Finset α := R \ I₀
      have hsplit : ∑ i ∈ R', c i + ∑ i ∈ I₀, c i = ∑ i ∈ R, c i :=
        sum_sdiff hI₀R
      have hsum' : (n : ℝ) * (w + M) - M ≤ ∑ i ∈ R', c i := by
        push_cast at hsum
        linarith
      obtain ⟨I', hI'R', hI'disj, hI'ge⟩ :=
        ih hn1 R' (fun i hi => hc_nonneg i (sdiff_subset hi))
          (fun i hi => hc_le i (sdiff_subset hi)) hsum'
      let I : Fin (n + 1) → Finset α := fun s =>
        if h : s.val < n then I' ⟨s.val, h⟩ else I₀
      refine ⟨I, ?_, ?_, ?_⟩
      · intro s
        dsimp [I]
        split_ifs with hs
        · exact (hI'R' ⟨s.val, hs⟩).trans sdiff_subset
        · exact hI₀R
      · intro s t hst
        dsimp [I]
        split_ifs with hs ht ht
        · have hne : (⟨s.val, hs⟩ : Fin n) ≠ ⟨t.val, ht⟩ :=
            fun h => hst (Fin.ext (congr_arg (Fin.val : Fin n → ℕ) h))
          exact hI'disj _ _ hne
        · rw [Finset.disjoint_left]
          intro x hx hx0
          exact (mem_sdiff.mp (hI'R' ⟨s.val, hs⟩ hx)).2 hx0
        · rw [Finset.disjoint_right]
          intro x hx hx0
          exact (mem_sdiff.mp (hI'R' ⟨t.val, ht⟩ hx)).2 hx0
        · exact (hst (Fin.ext (by omega))).elim
      · intro s
        dsimp [I]
        split_ifs with hs
        · exact hI'ge ⟨s.val, hs⟩
        · exact hI₀_ge

/-!
## Section 2: Lemma 2 — Unconditional Co-Sparse Complete-Blockade and Trigger-Set Peeling
for All $\overline{P_t}$-Free Graphs ($t \ge 2$, `main.tex` lines 196–204)
-/

/--
Generalized single-layer expansion step for Lemma 2 (`main.tex` lines 199–202):
Inside an expanding subgraph $H[U]$ of maximum degree $\le w$ where every $w$-subset has external
neighborhood $\ge (M + 1) w$, given previous layers $S_{\mathrm{prev}} \subseteq U$ of total size
$\le M w$ and current layer $S_{\mathrm{curr}} \subseteq S_{\mathrm{prev}}$ of size $\ge w$,
there exist an inclusion-minimal trigger set $R \subseteq S_{\mathrm{curr}}$ and a next layer
$S_{\mathrm{next}} \subseteq U \setminus S_{\mathrm{prev}}$ of size $w \le |S_{\mathrm{next}}| \le 2w$
such that every vertex in $S_{\mathrm{next}}$ has an $H$-neighbor in $R$ and $R$ has no $H$-edges
to $U \setminus (S_{\mathrm{prev}} \cup S_{\mathrm{next}})$.
-/
theorem exists_next_layer_gen (H : SimpleGraph V) (U : Finset V) (w M : ℕ) (hw : 1 ≤ w)
    (hdeg : ∀ u ∈ U, (neighborFinsetIn H u U).card ≤ w)
    (hexp : ∀ T ⊆ U, T.card = w → (M + 1) * w ≤ (extNeighIn H U T).card)
    (S_prev S_curr : Finset V) (hprev_U : S_prev ⊆ U) (hcurr_prev : S_curr ⊆ S_prev)
    (hcurr_card : w ≤ S_curr.card) (hprev_card : S_prev.card ≤ M * w) :
    ∃ R ⊆ S_curr, ∃ S_next ⊆ U \ S_prev,
      w ≤ S_next.card ∧
      S_next.card ≤ 2 * w ∧
      (∀ v ∈ S_next, ∃ u ∈ R, H.Adj u v) ∧
      (∀ u ∈ R, ∀ z ∈ U \ (S_prev ∪ S_next), ¬H.Adj u z) := by
  classical
  let layerNeigh : Finset V → Finset V :=
    fun X => (X.biUnion (fun u => neighborFinsetIn H u U)) \ S_prev
  obtain ⟨T, hT_curr, hT_card⟩ := exists_subset_card_eq hcurr_card
  have hT_prev : T ⊆ S_prev := Subset.trans hT_curr hcurr_prev
  have hT_U : T ⊆ U := Subset.trans hT_prev hprev_U
  have hext_sub : extNeighIn H U T ⊆ layerNeigh T ∪ S_prev := by
    intro v hv
    rw [mem_extNeighIn] at hv
    rcases hv with ⟨⟨u, huT, hvU, hadj⟩, _⟩
    rw [mem_union]
    by_cases hv_prev : v ∈ S_prev
    · exact Or.inr hv_prev
    · left
      simp only [layerNeigh, mem_sdiff, mem_biUnion, mem_neighborFinsetIn']
      exact ⟨⟨u, huT, hvU, hadj⟩, hv_prev⟩
  have hext_le : (extNeighIn H U T).card ≤ (layerNeigh T).card + S_prev.card :=
    (card_le_card hext_sub).trans (card_union_le _ _)
  have hM1 : (M + 1) * w ≤ (extNeighIn H U T).card := hexp T hT_U hT_card
  have hw_layerT : w ≤ (layerNeigh T).card := by
    have : (M + 1) * w = M * w + w := Nat.succ_mul M w
    omega
  obtain ⟨R, hRT, hw_R, hmin_R⟩ :=
    exists_minimal_subset_ge' (fun X => (layerNeigh X).card) w T hw_layerT
  have hR_curr : R ⊆ S_curr := Subset.trans hRT hT_curr
  have hR_U : R ⊆ U := Subset.trans hRT hT_U
  let S_next := layerNeigh R
  have hS_next_sub : S_next ⊆ U \ S_prev := by
    intro v hv
    simp only [S_next, layerNeigh, mem_sdiff, mem_biUnion, mem_neighborFinsetIn'] at hv
    rcases hv with ⟨⟨u, _, hvU, _⟩, hv_prev⟩
    exact mem_sdiff.mpr ⟨hvU, hv_prev⟩
  have hR_ne : R.Nonempty := by
    by_contra h_empty
    rw [not_nonempty_iff_eq_empty] at h_empty
    have h0 : (layerNeigh R).card = 0 := by simp [layerNeigh, h_empty]
    omega
  obtain ⟨r₀, hr₀⟩ := hR_ne
  have hS_next_split : S_next ⊆ layerNeigh (R.erase r₀) ∪ neighborFinsetIn H r₀ U := by
    intro v hv
    simp only [S_next, layerNeigh, mem_sdiff, mem_biUnion, mem_neighborFinsetIn'] at hv
    rcases hv with ⟨⟨u, huR, hvU, hadj⟩, hv_prev⟩
    rw [mem_union]
    by_cases hur₀ : u = r₀
    · subst hur₀
      exact Or.inr ((mem_neighborFinsetIn' H u v U).mpr ⟨hvU, hadj⟩)
    · left
      simp only [layerNeigh, mem_sdiff, mem_biUnion, mem_neighborFinsetIn']
      exact ⟨⟨u, mem_erase.mpr ⟨hur₀, huR⟩, hvU, hadj⟩, hv_prev⟩
  have hS_next_le : S_next.card ≤ 2 * w := by
    have h1 : S_next.card ≤ (layerNeigh (R.erase r₀)).card + (neighborFinsetIn H r₀ U).card :=
      (card_le_card hS_next_split).trans (card_union_le _ _)
    have h2 : (layerNeigh (R.erase r₀)).card < w := hmin_R r₀ hr₀
    have h3 : (neighborFinsetIn H r₀ U).card ≤ w := hdeg r₀ (hR_U hr₀)
    omega
  refine ⟨R, hR_curr, S_next, hS_next_sub, hw_R, hS_next_le, ?_, ?_⟩
  · intro v hv
    simp only [S_next, layerNeigh, mem_sdiff, mem_biUnion, mem_neighborFinsetIn'] at hv
    rcases hv with ⟨⟨u, huR, _, hadj⟩, _⟩
    exact ⟨u, huR, hadj⟩
  · intro u huR z hz hadj
    rw [mem_sdiff, mem_union, not_or] at hz
    obtain ⟨hzU, hz_prev, hz_next⟩ := hz
    apply hz_next
    simp only [S_next, layerNeigh, mem_sdiff, mem_biUnion, mem_neighborFinsetIn']
    exact ⟨⟨u, huR, hzU, hadj⟩, hz_prev⟩

/--
Inductive $k$-step layer tower construction in $H[U]$ for Lemma 2 (`main.tex` lines 201–202).
-/
private theorem exists_expanding_layer_tower (H : SimpleGraph V) (U : Finset V) (t w : ℕ)
    (ht : 2 ≤ t) (hw : 1 ≤ w) (hwU : w ≤ U.card)
    (hdeg : ∀ u ∈ U, (neighborFinsetIn H u U).card ≤ w)
    (hexp : ∀ T ⊆ U, T.card = w → (2 * t - 1) * w ≤ (extNeighIn H U T).card) :
    ∀ k : ℕ, k ≤ t - 1 →
      ∃ (S : Fin (k + 1) → Finset V) (R : Fin k → Finset V),
        (∀ p : Fin (k + 1), S p ⊆ U ∧ w ≤ (S p).card) ∧
        (Finset.univ.biUnion S).card ≤ (2 * k + 1) * w ∧
        (∀ p q : Fin (k + 1), p ≠ q → Disjoint (S p) (S q)) ∧
        (∀ p : Fin k, R p ⊆ S ⟨p.1, by omega⟩) ∧
        (∀ p : Fin k, ∀ v ∈ S ⟨p.1 + 1, by omega⟩, ∃ u ∈ R p, H.Adj u v) ∧
        (∀ p : Fin k, ∀ q : Fin (k + 1), p.1 + 1 < q.1 →
          ∀ u ∈ R p, ∀ z ∈ S q, ¬H.Adj u z) ∧
        (∀ p : Fin k, ∀ u ∈ R p, ∀ z ∈ U \ Finset.univ.biUnion S, ¬H.Adj u z) := by
  classical
  intro k
  induction k with
  | zero =>
    intro _
    obtain ⟨S₀, hS₀_U, hS₀_card⟩ := exists_subset_card_eq hwU
    refine ⟨fun _ => S₀, Fin.elim0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro _
      dsimp only
      exact ⟨hS₀_U, by omega⟩
    · have : (Finset.univ : Finset (Fin (0 + 1))).biUnion (fun _ => S₀) = S₀ := by
        ext x
        simp only [mem_biUnion, mem_univ, true_and]
        exact ⟨fun ⟨_, hx⟩ => hx, fun hx => ⟨⟨0, by omega⟩, hx⟩⟩
      rw [this, hS₀_card]
      omega
    · intro p q hpq
      exact (hpq (Fin.ext (by omega))).elim
    · intro p; exact p.elim0
    · intro p; exact p.elim0
    · intro p; exact p.elim0
    · intro p; exact p.elim0
  | succ k ih =>
    intro hk1
    obtain ⟨S, R, hS_U_w, hS_union_card, hS_disj, hR_sub, hR_adj, hR_nonadj_in, hR_nonadj_out⟩ :=
      ih (by omega)
    let S_prev : Finset V := Finset.univ.biUnion S
    let S_curr : Finset V := S ⟨k, Nat.lt_succ_self k⟩
    have hprev_U : S_prev ⊆ U := biUnion_subset.mpr (fun p _ => (hS_U_w p).1)
    have hcurr_prev : S_curr ⊆ S_prev :=
      subset_biUnion_of_mem S (mem_univ (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)))
    have hcurr_card : w ≤ S_curr.card := (hS_U_w ⟨k, Nat.lt_succ_self k⟩).2
    let M : ℕ := 2 * t - 2
    have hM1_eq : M + 1 = 2 * t - 1 := by omega
    have hprev_card : S_prev.card ≤ M * w := by
      have hkM : 2 * k + 1 ≤ M := by omega
      exact hS_union_card.trans (Nat.mul_le_mul_right w hkM)
    have hexp' : ∀ T ⊆ U, T.card = w → (M + 1) * w ≤ (extNeighIn H U T).card := by
      rwa [hM1_eq]
    obtain ⟨R_k, hR_k_curr, S_next, hS_next_sub, hw_S_next, hS_next_le, hS_next_adj, hR_k_out⟩ :=
      exists_next_layer_gen H U w M hw hdeg hexp' S_prev S_curr hprev_U hcurr_prev hcurr_card hprev_card
    let S' : Fin (k + 2) → Finset V := fun p =>
      if hp : p.1 < k + 1 then S ⟨p.1, hp⟩ else S_next
    let R' : Fin (k + 1) → Finset V := fun p =>
      if hp : p.1 < k then R ⟨p.1, hp⟩ else R_k
    have hS'_eq_lt : ∀ (p : Fin (k + 2)) (hp : p.1 < k + 1), S' p = S ⟨p.1, hp⟩ := by
      intro p hp
      dsimp only [S']
      rw [dif_pos hp]
    have hS'_last : S' ⟨k + 1, Nat.lt_succ_self (k + 1)⟩ = S_next := by
      dsimp only [S']
      rw [dif_neg (Nat.lt_irrefl _)]
    have hS'_biUnion : Finset.univ.biUnion S' = S_prev ∪ S_next := by
      ext x
      simp only [mem_biUnion, mem_univ, true_and, mem_union, S_prev]
      constructor
      · rintro ⟨p, hp⟩
        by_cases hlt : p.1 < k + 1
        · rw [hS'_eq_lt p hlt] at hp
          exact Or.inl ⟨(⟨p.1, hlt⟩ : Fin (k + 1)), hp⟩
        · have heq : p = ⟨k + 1, Nat.lt_succ_self (k + 1)⟩ := Fin.ext (by dsimp; have := p.2; omega)
          rw [heq, hS'_last] at hp
          exact Or.inr hp
      · rintro (⟨p, hp⟩ | hx_next)
        · refine ⟨⟨p.1, by omega⟩, ?_⟩
          rw [hS'_eq_lt ⟨p.1, by omega⟩ p.2]
          exact hp
        · refine ⟨⟨k + 1, Nat.lt_succ_self (k + 1)⟩, ?_⟩
          rw [hS'_last]
          exact hx_next
    refine ⟨S', R', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p
      by_cases hlt : p.1 < k + 1
      · rw [hS'_eq_lt p hlt]
        exact hS_U_w ⟨p.1, hlt⟩
      · have heq : p = ⟨k + 1, Nat.lt_succ_self (k + 1)⟩ := Fin.ext (by dsimp; have := p.2; omega)
        rw [heq, hS'_last]
        exact ⟨hS_next_sub.trans sdiff_subset, hw_S_next⟩
    · rw [hS'_biUnion]
      have h1 : (S_prev ∪ S_next).card ≤ S_prev.card + S_next.card := card_union_le _ _
      have hprev_le : S_prev.card ≤ (2 * k + 1) * w := hS_union_card
      have h2 : (2 * k + 1) * w + 2 * w = (2 * (k + 1) + 1) * w := by ring
      omega
    · intro p q hpq
      by_cases hp : p.1 < k + 1 <;> by_cases hq : q.1 < k + 1
      · rw [hS'_eq_lt p hp, hS'_eq_lt q hq]
        exact hS_disj ⟨p.1, hp⟩ ⟨q.1, hq⟩ (fun h => hpq (Fin.ext (Fin.mk.inj h)))
      · have hqe : q = ⟨k + 1, Nat.lt_succ_self (k + 1)⟩ := Fin.ext (by dsimp; have := q.2; omega)
        rw [hS'_eq_lt p hp, hqe, hS'_last]
        have hp_prev : S ⟨p.1, hp⟩ ⊆ S_prev := subset_biUnion_of_mem S (mem_univ _)
        exact Disjoint.mono hp_prev hS_next_sub disjoint_sdiff_self_right
      · have hpe : p = ⟨k + 1, Nat.lt_succ_self (k + 1)⟩ := Fin.ext (by dsimp; have := p.2; omega)
        rw [hpe, hS'_last, hS'_eq_lt q hq]
        have hq_prev : S ⟨q.1, hq⟩ ⊆ S_prev := subset_biUnion_of_mem S (mem_univ _)
        exact (Disjoint.mono hq_prev hS_next_sub disjoint_sdiff_self_right).symm
      · exact (hpq (Fin.ext (by have := p.2; have := q.2; omega))).elim
    · intro p
      by_cases hp : p.1 < k
      · have hp1 : p.1 < k + 1 := by omega
        dsimp only [R', S']
        rw [dif_pos hp, dif_pos hp1]
        exact hR_sub ⟨p.1, hp⟩
      · have hpe : p.1 = k := by have := p.2; omega
        have hp1 : p.1 < k + 1 := by have := p.2; omega
        dsimp only [R', S']
        rw [dif_neg hp, dif_pos hp1]
        have hidx : (⟨p.1, hp1⟩ : Fin (k + 1)) = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext hpe
        rw [hidx]
        exact hR_k_curr
    · intro p v hv
      by_cases hp : p.1 < k
      · have hp1 : p.1 + 1 < k + 1 := by omega
        dsimp only [R', S'] at hv ⊢
        rw [dif_pos hp]
        rw [dif_pos hp1] at hv
        exact hR_adj ⟨p.1, hp⟩ v hv
      · have hpe : p.1 = k := by have := p.2; omega
        have hp1 : ¬(p.1 + 1 < k + 1) := by omega
        dsimp only [R', S'] at hv ⊢
        rw [dif_neg hp]
        rw [dif_neg hp1] at hv
        exact hS_next_adj v hv
    · intro p q hpq u hu z hz
      by_cases hp : p.1 < k
      · dsimp only [R'] at hu
        rw [dif_pos hp] at hu
        by_cases hq : q.1 < k + 1
        · rw [hS'_eq_lt q hq] at hz
          exact hR_nonadj_in ⟨p.1, hp⟩ ⟨q.1, hq⟩ hpq u hu z hz
        · have hqe : q = ⟨k + 1, Nat.lt_succ_self (k + 1)⟩ := Fin.ext (by dsimp; have := q.2; omega)
          rw [hqe, hS'_last] at hz
          exact hR_nonadj_out ⟨p.1, hp⟩ u hu z (hS_next_sub hz)
      · have := p.2; have := q.2; omega
    · intro p u hu z hz
      rw [hS'_biUnion] at hz
      by_cases hp : p.1 < k
      · dsimp only [R'] at hu
        rw [dif_pos hp] at hu
        have hz' : z ∈ U \ S_prev := by
          rw [mem_sdiff] at hz ⊢
          exact ⟨hz.1, fun h => hz.2 (mem_union_left _ h)⟩
        exact hR_nonadj_out ⟨p.1, hp⟩ u hu z hz'
      · dsimp only [R'] at hu
        rw [dif_neg hp] at hu
        exact hR_k_out u hu z hz

/--
Backwards path extraction from an expanding $t$-layer tower: if $U \subseteq V$ has maximum degree
$\le w$ in $Gᶜ$ and every $w$-subset of $U$ has external neighborhood $\ge (2t - 1)w$ in $Gᶜ$,
then $G$ contains an induced copy of $\overline{P_t}$ (`PkCompl t`).
-/
private theorem not_isInducedSubgraphFree_pkCompl_of_expanding (G : SimpleGraph V) (U : Finset V)
    (t w : ℕ) (ht : 2 ≤ t) (hw : 1 ≤ w) (hwU : w ≤ U.card)
    (hdeg : ∀ u ∈ U, (neighborFinsetIn Gᶜ u U).card ≤ w)
    (hexp : ∀ T ⊆ U, T.card = w → (2 * t - 1) * w ≤ (extNeighIn Gᶜ U T).card) :
    ¬IsInducedSubgraphFree G (PkCompl t) := by
  classical
  obtain ⟨S, R, hS_U_w, _, hS_disj, hR_sub, hR_adj, hR_nonadj_in, _⟩ :=
    exists_expanding_layer_tower Gᶜ U t w ht hw hwU hdeg hexp (t - 1) le_rfl
  have h_back : ∀ d : ℕ, d < t →
      ∃ x : Fin t → V,
        (∀ i : Fin t, t - 1 - d ≤ i.1 → x i ∈ S ⟨i.1, by omega⟩) ∧
        (∀ i : Fin (t - 1), t - 1 - d ≤ i.1 →
          x ⟨i.1, by omega⟩ ∈ R i ∧ Gᶜ.Adj (x ⟨i.1, by omega⟩) (x ⟨i.1 + 1, by omega⟩)) := by
    intro d
    induction d with
    | zero =>
      intro _
      have hlast_ne : (S ⟨t - 1, by omega⟩).Nonempty :=
        card_pos.mp (lt_of_lt_of_le (by omega) (hS_U_w ⟨t - 1, by omega⟩).2)
      obtain ⟨v_last, hv_last⟩ := hlast_ne
      refine ⟨fun _ => v_last, ?_, ?_⟩
      · intro i hi
        have hieq : i.1 = t - 1 := by omega
        simpa [hieq] using hv_last
      · intro i hi
        omega
    | succ d ih =>
      intro hd1
      obtain ⟨x, hx_mem, hx_adj⟩ := ih (by omega)
      let p_idx : Fin (t - 1) := ⟨t - 1 - (d + 1), by omega⟩
      have hv_next_mem : x ⟨p_idx.1 + 1, by omega⟩ ∈ S ⟨p_idx.1 + 1, by omega⟩ :=
        hx_mem ⟨p_idx.1 + 1, by omega⟩ (by dsimp [p_idx]; omega)
      obtain ⟨u_curr, hu_R, hadj_curr⟩ := hR_adj p_idx _ hv_next_mem
      have hu_S : u_curr ∈ S ⟨p_idx.1, by omega⟩ := hR_sub p_idx hu_R
      let x' : Fin t → V := fun i => if i.1 = p_idx.1 then u_curr else x i
      refine ⟨x', ?_, ?_⟩
      · intro i hi
        dsimp [x']
        split_ifs with hieq
        · simpa [hieq] using hu_S
        · exact hx_mem i (by dsimp [p_idx] at hieq; omega)
      · intro i hi
        dsimp [x']
        by_cases hieq : i.1 = p_idx.1
        · have hi_fin : i = p_idx := Fin.ext hieq
          subst hi_fin
          have hne_succ : ¬(p_idx.1 + 1 = p_idx.1) := by omega
          rw [if_pos rfl, if_neg hne_succ]
          exact ⟨hu_R, hadj_curr⟩
        · have hgt : t - 1 - d ≤ i.1 := by dsimp [p_idx] at hieq; omega
          have hne1 : ¬(i.1 + 1 = p_idx.1) := by dsimp [p_idx]; omega
          rw [if_neg hieq, if_neg hne1]
          exact hx_adj i hgt
  obtain ⟨x, hx_mem_raw, hx_adj_raw⟩ := h_back (t - 1) (by omega)
  have hx_mem : ∀ i : Fin t, x i ∈ S ⟨i.1, by omega⟩ :=
    fun i => hx_mem_raw i (by omega)
  have hx_adj : ∀ i : Fin (t - 1),
      x ⟨i.1, by omega⟩ ∈ R i ∧ Gᶜ.Adj (x ⟨i.1, by omega⟩) (x ⟨i.1 + 1, by omega⟩) :=
    fun i => hx_adj_raw i (by omega)
  have hx_inj : Function.Injective x := by
    intro i j hij
    by_contra hne
    have hne' : (⟨i.1, by omega⟩ : Fin (t - 1 + 1)) ≠ ⟨j.1, by omega⟩ :=
      fun h => hne (Fin.ext (Fin.mk.inj h))
    exact Finset.disjoint_left.mp (hS_disj _ _ hne') (hx_mem i) (hij ▸ hx_mem j)
  have h_lt_adj : ∀ i j : Fin t, i.1 < j.1 → (Gᶜ.Adj (x i) (x j) ↔ j.1 = i.1 + 1) := by
    intro i j hij
    have hi_lt : i.1 < t - 1 := by omega
    constructor
    · intro hadj
      by_contra hne_succ
      have hgt : i.1 + 1 < j.1 := by omega
      exact hR_nonadj_in ⟨i.1, hi_lt⟩ ⟨j.1, by omega⟩ hgt
        (x i) (hx_adj ⟨i.1, hi_lt⟩).1 (x j) (hx_mem j) hadj
    · intro hsucc
      have h_step := (hx_adj ⟨i.1, hi_lt⟩).2
      have hi_eq : (⟨i.1, by omega⟩ : Fin t) = i := Fin.ext rfl
      have hj_eq : (⟨i.1 + 1, by omega⟩ : Fin t) = j := Fin.ext hsucc.symm
      rwa [hi_eq, hj_eq] at h_step
  intro hfree
  apply hfree
  refine ⟨⟨x, hx_inj⟩, ?_⟩
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · rw [PkCompl, compl_adj, pathGraph_adj, comap_adj, Function.Embedding.coeFn_mk]
    simp only [ne_eq, hij, not_false_eq_true, true_and]
    have hpath_iff : Gᶜ.Adj (x i) (x j) ↔ (i.1 + 1 = j.1 ∨ j.1 + 1 = i.1) := by
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hgt
      · rw [h_lt_adj i j hlt]
        omega
      · rw [Gᶜ.adj_comm, h_lt_adj j i hgt]
        omega
    rw [← hpath_iff, SimpleGraph.compl_adj]
    simp [hx_inj.ne hij]

/--
**Lemma 2(a) (`pkCompl_free_cosparse_complete_blockade`, Unconditional Co-Sparse Complete-Blockade
Lemma for All $\overline{P_t}$-Free Graphs, `main.tex` lines 196–204)**:
Let $t \ge 2$ be any integer (`ht : 2 ≤ t`), let $0 < y \le \frac{1}{12t}$, and let $G$ be a
$\overline{P_t}$-free graph (`IsInducedSubgraphFree G (PkCompl t)`) with $F \subseteq V(G)$ such
that $\overline{G}[F]$ is $y^2$-sparse (`IsEpsSparseOn Gᶜ F (y ^ 2)`) and $|F| \ge y^{-2}$.
Then $F$ contains a $100\%$ pairwise-complete $(\lceil y^{-1} \rceil, \lfloor y^2 |F| \rfloor)$-blockade
in $G$ (`IsCompleteBlockadeIn G F ⌈1 / y⌉₊ ⌊y ^ 2 * |F|⌋₊ B`).
-/
theorem pkCompl_free_cosparse_complete_blockade
    (G : SimpleGraph V) (F : Finset V) (t : ℕ) (y : ℝ)
    (ht : 2 ≤ t)
    (hG : IsInducedSubgraphFree G (PkCompl t))
    (hy0 : 0 < y) (hy_le : y ≤ 1 / (12 * (t : ℝ)))
    (hF_card : 1 / y ^ 2 ≤ (F.card : ℝ))
    (hsparse : IsEpsSparseOn Gᶜ F (y ^ 2)) :
    ∃ B : Fin ⌈1 / y⌉₊ → Finset V,
      IsCompleteBlockadeIn G F ⌈1 / y⌉₊ (⌊y ^ 2 * (F.card : ℝ)⌋₊ : ℝ) B := by
  classical
  let w : ℕ := ⌊y ^ 2 * (F.card : ℝ)⌋₊
  let μ : ℝ := 1 / (6 * y)
  have ht_real : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hy_12t : 12 * (t : ℝ) * y ≤ 1 := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 12 * (t : ℝ))).mp hy_le
    linarith
  have hy_24 : y ≤ 1 / 24 := by nlinarith
  have hy2_F : 1 ≤ y ^ 2 * (F.card : ℝ) := by
    have h1 : y ^ 2 * (1 / y ^ 2) ≤ y ^ 2 * (F.card : ℝ) :=
      mul_le_mul_of_nonneg_left hF_card (by positivity)
    rw [mul_one_div_cancel (by positivity)] at h1
    exact h1
  have hw_pos : 1 ≤ w := Nat.floor_pos.mpr hy2_F
  have hw_le_y2F : (w : ℝ) ≤ y ^ 2 * (F.card : ℝ) :=
    Nat.floor_le (by positivity)
  obtain ⟨U_rem, 𝒜, hU_rem_F, h𝒜_sub, h𝒜_ne, h𝒜_le, h𝒜_disj, h𝒜_comp, h𝒜_sum, hexp_rem⟩ :=
    peel_poorly_expanding_sets G F w μ
  by_cases hrem_half : (U_rem.card : ℝ) ≤ (1 / 2 : ℝ) * (F.card : ℝ)
  · have hsdiff_eq : ((F \ U_rem).card : ℝ) + (U_rem.card : ℝ) = (F.card : ℝ) := by
      exact_mod_cast card_sdiff_add_card_eq_card hU_rem_F
    have hsdiff_ge : (1 / 2 : ℝ) * (F.card : ℝ) ≤ ((F \ U_rem).card : ℝ) := by linarith
    have hμ_pos : 0 < 1 + μ := by dsimp [μ]; positivity
    have hμ_94y : (1 + μ) * ((9 / 4 : ℝ) * y * (F.card : ℝ)) ≤ (1 / 2 : ℝ) * (F.card : ℝ) := by
      have h1 : (1 + μ) * ((9 / 4 : ℝ) * y * (F.card : ℝ)) =
          ((9 / 4 : ℝ) * y + 3 / 8) * (F.card : ℝ) := by
        dsimp [μ]
        have hy_ne : y ≠ 0 := hy0.ne'
        field_simp
        ring
      rw [h1]
      have h2 : (9 / 4 : ℝ) * y + 3 / 8 ≤ 1 / 2 := by linarith
      exact mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg _)
    have hsum_94y : (9 / 4 : ℝ) * y * (F.card : ℝ) ≤ ∑ A ∈ 𝒜, (A.card : ℝ) := by
      have h1 : (1 + μ) * ((9 / 4 : ℝ) * y * (F.card : ℝ)) ≤
          (1 + μ) * (∑ A ∈ 𝒜, (A.card : ℝ)) :=
        hμ_94y.trans (hsdiff_ge.trans h𝒜_sum)
      exact le_of_mul_le_mul_left h1 hμ_pos
    let k : ℕ := ⌈1 / y⌉₊
    have hk_pos : 1 ≤ k := Nat.ceil_pos.mpr (by positivity)
    have hk_lt : (k : ℝ) < 1 / y + 1 := Nat.ceil_lt_add_one (by positivity)
    have hsum_target : (k : ℝ) * ((w : ℝ) + (w : ℝ)) - (w : ℝ) ≤ ∑ A ∈ 𝒜, (A.card : ℝ) := by
      have h1 : (k : ℝ) * ((w : ℝ) + (w : ℝ)) - (w : ℝ) = (2 * (k : ℝ) - 1) * (w : ℝ) := by ring
      have h2 : 2 * (k : ℝ) - 1 ≤ 2 * (1 / y) + 1 := by linarith
      have h3 : (2 * (k : ℝ) - 1) * (w : ℝ) ≤ (2 * (1 / y) + 1) * (y ^ 2 * (F.card : ℝ)) :=
        mul_le_mul h2 hw_le_y2F (Nat.cast_nonneg _) (by positivity)
      have h4 : (2 * (1 / y) + 1) * (y ^ 2 * (F.card : ℝ)) =
          (2 * y + y ^ 2) * (F.card : ℝ) := by
        have hy_ne : y ≠ 0 := hy0.ne'
        field_simp
      have h5 : 2 * y + y ^ 2 ≤ (9 / 4 : ℝ) * y := by nlinarith
      have h6 : (2 * y + y ^ 2) * (F.card : ℝ) ≤ (9 / 4 : ℝ) * y * (F.card : ℝ) :=
        mul_le_mul_of_nonneg_right h5 (Nat.cast_nonneg _)
      linarith
    obtain ⟨I, hI_sub, hI_disj, hI_sum⟩ :=
      exists_disjoint_family_sum_ge' k hk_pos 𝒜 (fun A => (A.card : ℝ)) (w : ℝ) (w : ℝ)
        (Nat.cast_nonneg _) (Nat.cast_nonneg _) (fun A _ => Nat.cast_nonneg _)
        (fun A hA => Nat.cast_le.mpr (h𝒜_le A hA)) hsum_target
    let B : Fin k → Finset V := fun s => (I s).biUnion id
    have hB_card : ∀ s : Fin k, ((B s).card : ℝ) = ∑ A ∈ I s, (A.card : ℝ) := by
      intro s
      have hnat : (B s).card = ∑ A ∈ I s, A.card :=
        card_biUnion (fun A₁ hA₁ A₂ hA₂ hne =>
          h𝒜_disj A₁ (hI_sub s hA₁) A₂ (hI_sub s hA₂) hne)
      exact_mod_cast hnat
    have hB_width : ∀ s : Fin k, (w : ℝ) ≤ ((B s).card : ℝ) := by
      intro s
      rw [hB_card s]
      exact hI_sum s
    have hB_ne : ∀ s : Fin k, (B s).Nonempty := by
      intro s
      have hpos : (0 : ℝ) < ((B s).card : ℝ) := by
        have : (0 : ℝ) < (w : ℝ) := by positivity
        linarith [hB_width s]
      exact card_pos.mp (by exact_mod_cast hpos)
    have hB_sub : ∀ s : Fin k, B s ⊆ F := by
      intro s u hu
      obtain ⟨A, hA_Is, huA⟩ := mem_biUnion.mp hu
      exact sdiff_subset (h𝒜_sub A (hI_sub s hA_Is) huA)
    have hB_disj : ∀ s r : Fin k, s ≠ r → Disjoint (B s) (B r) := by
      intro s r hsr
      rw [Finset.disjoint_left]
      intro u huBs huBr
      obtain ⟨A₁, hA₁, huA₁⟩ := mem_biUnion.mp huBs
      obtain ⟨A₂, hA₂, huA₂⟩ := mem_biUnion.mp huBr
      have hne : A₁ ≠ A₂ := fun h => Finset.disjoint_left.mp (hI_disj s r hsr) hA₁ (h ▸ hA₂)
      exact Finset.disjoint_left.mp (h𝒜_disj A₁ (hI_sub s hA₁) A₂ (hI_sub r hA₂) hne) huA₁ huA₂
    have hB_comp : ∀ s r : Fin k, s ≠ r → IsCompletePair G (B s) (B r) := by
      intro s r hsr u huBs v hvBr
      obtain ⟨A₁, hA₁, huA₁⟩ := mem_biUnion.mp huBs
      obtain ⟨A₂, hA₂, hvA₂⟩ := mem_biUnion.mp hvBr
      have hne : A₁ ≠ A₂ := fun h => Finset.disjoint_left.mp (hI_disj s r hsr) hA₁ (h ▸ hA₂)
      exact h𝒜_comp A₁ (hI_sub s hA₁) A₂ (hI_sub r hA₂) hne u huA₁ v hvA₂
    exact ⟨B, ⟨hB_sub, hB_ne, hB_disj, hB_width⟩, hB_comp⟩
  · exfalso
    push_neg at hrem_half
    have hdeg_U : ∀ u ∈ U_rem, (neighborFinsetIn Gᶜ u U_rem).card ≤ w := by
      intro u hu
      have hsub : neighborFinsetIn Gᶜ u U_rem ⊆ neighborFinsetIn Gᶜ u F :=
        neighborFinsetIn_mono' Gᶜ u hU_rem_F
      have hle_F : ((neighborFinsetIn Gᶜ u U_rem).card : ℝ) ≤ y ^ 2 * (F.card : ℝ) := by
        calc ((neighborFinsetIn Gᶜ u U_rem).card : ℝ)
          _ ≤ ((neighborFinsetIn Gᶜ u F).card : ℝ) := by exact_mod_cast card_le_card hsub
          _ ≤ y ^ 2 * (F.card : ℝ) := hsparse u (hU_rem_F hu)
      exact Nat.le_floor hle_F
    have hμ_ge_2t : 2 * (t : ℝ) ≤ μ := by
      dsimp [μ]
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hexp_2t : ∀ T ⊆ U_rem, T.card = w → (2 * t - 1) * w ≤ (extNeighIn Gᶜ U_rem T).card := by
      intro T hT hT_card
      have hT_ne : T.Nonempty := card_pos.mp (by omega)
      have hlt := hexp_rem T hT hT_ne (by omega)
      rw [hT_card] at hlt
      have h2t_sub : ((2 * t - 1 : ℕ) : ℝ) < 2 * (t : ℝ) := by
        have : (2 * t - 1 : ℕ) + 1 = 2 * t := by omega
        have hcast : ((2 * t - 1 : ℕ) : ℝ) + 1 = 2 * (t : ℝ) := by exact_mod_cast this
        linarith
      have hlt_real : (((2 * t - 1) * w : ℕ) : ℝ) < ((extNeighIn Gᶜ U_rem T).card : ℝ) := by
        push_cast
        have hw_pos_r : (0 : ℝ) < (w : ℝ) := by positivity
        nlinarith
      have hlt_nat : (2 * t - 1) * w < (extNeighIn Gᶜ U_rem T).card := by exact_mod_cast hlt_real
      omega
    have hw_le_U : w ≤ U_rem.card := by
      have hy2_le_half : y ^ 2 * (F.card : ℝ) ≤ (1 / 2 : ℝ) * (F.card : ℝ) := by
        have : y ^ 2 ≤ 1 / 2 := by nlinarith
        exact mul_le_mul_of_nonneg_right this (Nat.cast_nonneg _)
      have hw_lt : (w : ℝ) < (U_rem.card : ℝ) := by linarith
      exact_mod_cast hw_lt.le
    exact not_isInducedSubgraphFree_pkCompl_of_expanding G U_rem t w ht hw_pos hw_le_U
      hdeg_U hexp_2t hG

/--
Bounded peeling helper for Lemma 2 (`main.tex` line 203): peels poorly expanding sets of size
$\le w$ in $Gᶜ[U]$ until either the peeled union $X$ reaches target size $\ge \mathrm{target}$
(with $|X| < \mathrm{target} + w$) or the remainder $U_{\mathrm{rem}}$ is $\mu$-expanding.
-/
private theorem peel_until_target_or_expanding (G : SimpleGraph V) (U : Finset V) (w : ℕ)
    (μ target : ℝ) (_hw : 1 ≤ w) (htarget : 0 < target) :
    ∃ (X U_rem : Finset V),
      X ⊆ U ∧ U_rem ⊆ U ∧ Disjoint X U_rem ∧
      IsCompletePair G X U_rem ∧
      ((U \ U_rem).card : ℝ) ≤ (1 + μ) * (X.card : ℝ) ∧
      ((target ≤ (X.card : ℝ) ∧ (X.card : ℝ) < target + (w : ℝ)) ∨
       ((X.card : ℝ) < target ∧
        ∀ A ⊆ U_rem, A.Nonempty → A.card ≤ w →
          μ * (A.card : ℝ) < ((extNeighIn Gᶜ U_rem A).card : ℝ))) := by
  classical
  induction hn : U.card using Nat.strong_induction_on generalizing U target with
  | _ n ih =>
    subst hn
    by_cases hexp : ∀ A ⊆ U, A.Nonempty → A.card ≤ w →
        μ * (A.card : ℝ) < ((extNeighIn Gᶜ U A).card : ℝ)
    · refine ⟨∅, U, empty_subset _, Subset.rfl, disjoint_empty_left _, ?_, ?_, Or.inr ⟨?_, hexp⟩⟩
      · intro u hu; exact (notMem_empty u hu).elim
      · simp
      · simpa using htarget
    · push_neg at hexp
      obtain ⟨A₀, hA₀U, hA₀_ne, hA₀_le, hA₀_ext⟩ := hexp
      let N₀ := extNeighIn Gᶜ U A₀
      let U₁ := U \ (A₀ ∪ N₀)
      have hU₁U : U₁ ⊆ U := sdiff_subset
      obtain ⟨a₀, ha₀⟩ := hA₀_ne
      have ha₀_U : a₀ ∈ U := hA₀U ha₀
      have ha₀_not_U₁ : a₀ ∉ U₁ := by
        intro hmem
        exact (mem_sdiff.mp hmem).2 (mem_union_left _ ha₀)
      have hU₁_lt : U₁.card < U.card :=
        card_lt_card (ssubset_iff_of_subset hU₁U |>.mpr ⟨a₀, ha₀_U, ha₀_not_U₁⟩)
      have hA₀_disj_U₁ : Disjoint A₀ U₁ := by
        rw [Finset.disjoint_left]
        intro x hxA₀ hxU₁
        exact (mem_sdiff.mp hxU₁).2 (mem_union_left _ hxA₀)
      have hA₀_comp_U₁ : IsCompletePair G A₀ U₁ :=
        isCompletePair_of_disjoint_extNeighIn G U A₀
      have hsdiff_U₁ : ((U \ U₁).card : ℝ) ≤ (1 + μ) * (A₀.card : ℝ) := by
        have hsub : U \ U₁ ⊆ A₀ ∪ N₀ := by
          intro x hx
          rw [mem_sdiff] at hx
          by_contra hx0
          exact hx.2 (mem_sdiff.mpr ⟨hx.1, hx0⟩)
        have hnat : (U \ U₁).card ≤ A₀.card + N₀.card :=
          (card_le_card hsub).trans (card_union_le _ _)
        have hreal : ((U \ U₁).card : ℝ) ≤ (A₀.card : ℝ) + (N₀.card : ℝ) := by
          exact_mod_cast hnat
        linarith
      by_cases hA₀_target : target ≤ (A₀.card : ℝ)
      · refine ⟨A₀, U₁, hA₀U, hU₁U, hA₀_disj_U₁, hA₀_comp_U₁, hsdiff_U₁, Or.inl ⟨hA₀_target, ?_⟩⟩
        have hA₀_w : (A₀.card : ℝ) ≤ (w : ℝ) := by exact_mod_cast hA₀_le
        linarith
      · push_neg at hA₀_target
        let target' := target - (A₀.card : ℝ)
        have htarget' : 0 < target' := sub_pos.mpr hA₀_target
        obtain ⟨X₁, U_rem, hX₁U₁, hU_rem_U₁, hdisj₁, hcomp₁, hsdiff₁, hout₁⟩ :=
          ih U₁.card hU₁_lt U₁ target' htarget' rfl
        let X := A₀ ∪ X₁
        have hdisj_A₀_X₁ : Disjoint A₀ X₁ := Disjoint.mono_right hX₁U₁ hA₀_disj_U₁
        have hX_card : (X.card : ℝ) = (A₀.card : ℝ) + (X₁.card : ℝ) := by
          exact_mod_cast card_union_of_disjoint hdisj_A₀_X₁
        have hXU : X ⊆ U := union_subset hA₀U (hX₁U₁.trans hU₁U)
        have hU_rem_U : U_rem ⊆ U := hU_rem_U₁.trans hU₁U
        have hdisj_X_rem : Disjoint X U_rem :=
          disjoint_union_left.mpr ⟨Disjoint.mono_right hU_rem_U₁ hA₀_disj_U₁, hdisj₁⟩
        have hcomp_X_rem : IsCompletePair G X U_rem := by
          intro x hx y hy
          rcases mem_union.mp hx with hxA₀ | hxX₁
          · exact hA₀_comp_U₁ x hxA₀ y (hU_rem_U₁ hy)
          · exact hcomp₁ x hxX₁ y hy
        have hsdiff_tot : ((U \ U_rem).card : ℝ) ≤ (1 + μ) * (X.card : ℝ) := by
          have hsub : U \ U_rem ⊆ (U \ U₁) ∪ (U₁ \ U_rem) := by
            intro x hx
            rw [mem_sdiff] at hx
            by_cases hxU₁ : x ∈ U₁
            · exact mem_union_right _ (mem_sdiff.mpr ⟨hxU₁, hx.2⟩)
            · exact mem_union_left _ (mem_sdiff.mpr ⟨hx.1, hxU₁⟩)
          have hnat : (U \ U_rem).card ≤ (U \ U₁).card + (U₁ \ U_rem).card :=
            (card_le_card hsub).trans (card_union_le _ _)
          have hreal : ((U \ U_rem).card : ℝ) ≤
              ((U \ U₁).card : ℝ) + ((U₁ \ U_rem).card : ℝ) := by exact_mod_cast hnat
          rw [hX_card]
          linarith
        refine ⟨X, U_rem, hXU, hU_rem_U, hdisj_X_rem, hcomp_X_rem, hsdiff_tot, ?_⟩
        rcases hout₁ with ⟨hge, hlt⟩ | ⟨hlt, hexp_rem⟩
        · left
          rw [hX_card]
          dsimp [target'] at hge hlt
          exact ⟨by linarith, by linarith⟩
        · right
          rw [hX_card]
          dsimp [target'] at hlt
          exact ⟨by linarith, hexp_rem⟩

/--
**Lemma 2(b) (`pkCompl_free_cosparse_trigger_pair`, Unconditional Co-Sparse Trigger-Set Peeling
for All $\overline{P_t}$-Free Graphs, `main.tex` lines 196–204)**:
Let $t \ge 2$ be any integer (`ht : 2 ≤ t`), let $0 < y \le \frac{1}{12t}$, and let $G$ be a
$\overline{P_t}$-free graph (`IsInducedSubgraphFree G (PkCompl t)`) with $F \subseteq V(G)$ such
that $\overline{G}[F]$ is $y$-sparse (`IsEpsSparseOn Gᶜ F y`) and $|F| \ge y^{-2}$.
Then $F$ contains disjoint subsets $X, Y \subseteq F$ with $|X| \ge y^2 |F|$ and
$|Y| \ge (1 - 3ty)|F|$ such that $(X, Y)$ is $100\%$ complete in $G$ (`IsCompletePair G X Y`).
-/
theorem pkCompl_free_cosparse_trigger_pair
    (G : SimpleGraph V) (F : Finset V) (t : ℕ) (y : ℝ)
    (ht : 2 ≤ t)
    (hG : IsInducedSubgraphFree G (PkCompl t))
    (hy0 : 0 < y) (hy_le : y ≤ 1 / (12 * (t : ℝ)))
    (hF_card : 1 / y ^ 2 ≤ (F.card : ℝ))
    (hsparse : IsEpsSparseOn Gᶜ F y) :
    ∃ X ⊆ F, ∃ Y ⊆ F, Disjoint X Y ∧
      y ^ 2 * (F.card : ℝ) ≤ (X.card : ℝ) ∧
      (1 - 3 * (t : ℝ) * y) * (F.card : ℝ) ≤ (Y.card : ℝ) ∧
      IsCompletePair G X Y := by
  classical
  let w : ℕ := ⌊y * (F.card : ℝ)⌋₊
  let μ : ℝ := 2 * (t : ℝ) - 1
  let target : ℝ := y ^ 2 * (F.card : ℝ)
  have ht_real : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hy_12t : 12 * (t : ℝ) * y ≤ 1 := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 12 * (t : ℝ))).mp hy_le
    linarith
  have hy_24 : y ≤ 1 / 24 := by nlinarith
  have hy2_F : 1 ≤ y ^ 2 * (F.card : ℝ) := by
    have h1 : y ^ 2 * (1 / y ^ 2) ≤ y ^ 2 * (F.card : ℝ) :=
      mul_le_mul_of_nonneg_left hF_card (by positivity)
    rw [mul_one_div_cancel (by positivity)] at h1
    exact h1
  have hy_F_ge : 24 ≤ y * (F.card : ℝ) := by
    have : 24 * y ^ 2 ≤ y := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right this (Nat.cast_nonneg F.card)
    nlinarith
  have hw_pos : 1 ≤ w := Nat.floor_pos.mpr (by linarith)
  have hw_le_yF : (w : ℝ) ≤ y * (F.card : ℝ) := Nat.floor_le (by positivity)
  have htarget_pos : 0 < target := by dsimp [target]; linarith
  obtain ⟨X, U_rem, hXF, hU_rem_F, hdisj, hcomp, hsdiff, hout⟩ :=
    peel_until_target_or_expanding G F w μ target hw_pos htarget_pos
  rcases hout with ⟨hX_ge, hX_lt⟩ | ⟨hX_lt, hexp_rem⟩
  · refine ⟨X, hXF, U_rem, hU_rem_F, hdisj, hX_ge, ?_, hcomp⟩
    have hsdiff_eq : ((F \ U_rem).card : ℝ) + (U_rem.card : ℝ) = (F.card : ℝ) := by
      exact_mod_cast card_sdiff_add_card_eq_card hU_rem_F
    have h1_add_μ : 1 + μ = 2 * (t : ℝ) := by dsimp [μ]; ring
    have hX_le : (X.card : ℝ) ≤ (3 / 2 : ℝ) * y * (F.card : ℝ) := by
      have : target + (w : ℝ) ≤ (y ^ 2 + y) * (F.card : ℝ) := by
        dsimp [target]
        linarith
      have hy2_half : y ^ 2 ≤ (1 / 2 : ℝ) * y := by nlinarith
      nlinarith
    have hsdiff_le : ((F \ U_rem).card : ℝ) ≤ 3 * (t : ℝ) * y * (F.card : ℝ) := by
      calc ((F \ U_rem).card : ℝ)
        _ ≤ (1 + μ) * (X.card : ℝ) := hsdiff
        _ = 2 * (t : ℝ) * (X.card : ℝ) := by rw [h1_add_μ]
        _ ≤ 2 * (t : ℝ) * ((3 / 2 : ℝ) * y * (F.card : ℝ)) :=
          mul_le_mul_of_nonneg_left hX_le (by positivity)
        _ = 3 * (t : ℝ) * y * (F.card : ℝ) := by ring
    linarith
  · exfalso
    have hsdiff_eq : ((F \ U_rem).card : ℝ) + (U_rem.card : ℝ) = (F.card : ℝ) := by
      exact_mod_cast card_sdiff_add_card_eq_card hU_rem_F
    have hF_pos : (0 : ℝ) < (F.card : ℝ) := lt_of_lt_of_le (by positivity) hF_card
    have hsdiff_lt : ((F \ U_rem).card : ℝ) < (1 / 2 : ℝ) * (F.card : ℝ) := by
      have h1_add_μ : 1 + μ = 2 * (t : ℝ) := by dsimp [μ]; ring
      have h1 : ((F \ U_rem).card : ℝ) ≤ 2 * (t : ℝ) * (y ^ 2 * (F.card : ℝ)) := by
        calc ((F \ U_rem).card : ℝ)
          _ ≤ (1 + μ) * (X.card : ℝ) := hsdiff
          _ = 2 * (t : ℝ) * (X.card : ℝ) := by rw [h1_add_μ]
          _ ≤ 2 * (t : ℝ) * target := mul_le_mul_of_nonneg_left hX_lt.le (by positivity)
      have h2 : 2 * (t : ℝ) * y ^ 2 < 1 / 2 := by nlinarith
      nlinarith
    have hw_le_U : w ≤ U_rem.card := by
      have hw_lt : (w : ℝ) < (U_rem.card : ℝ) := by nlinarith
      exact_mod_cast hw_lt.le
    have hdeg_U : ∀ u ∈ U_rem, (neighborFinsetIn Gᶜ u U_rem).card ≤ w := by
      intro u hu
      have hsub : neighborFinsetIn Gᶜ u U_rem ⊆ neighborFinsetIn Gᶜ u F :=
        neighborFinsetIn_mono' Gᶜ u hU_rem_F
      have hle_F : ((neighborFinsetIn Gᶜ u U_rem).card : ℝ) ≤ y * (F.card : ℝ) := by
        calc ((neighborFinsetIn Gᶜ u U_rem).card : ℝ)
          _ ≤ ((neighborFinsetIn Gᶜ u F).card : ℝ) := by exact_mod_cast card_le_card hsub
          _ ≤ y * (F.card : ℝ) := hsparse u (hU_rem_F hu)
      exact Nat.le_floor hle_F
    have hexp_2t : ∀ T ⊆ U_rem, T.card = w → (2 * t - 1) * w ≤ (extNeighIn Gᶜ U_rem T).card := by
      intro T hT hT_card
      have hT_ne : T.Nonempty := card_pos.mp (by omega)
      have hlt := hexp_rem T hT hT_ne (by omega)
      rw [hT_card] at hlt
      have h2t_eq : (((2 * t - 1) * w : ℕ) : ℝ) = μ * (w : ℝ) := by
        have : (2 * t - 1 : ℕ) + 1 = 2 * t := by omega
        have hcast : ((2 * t - 1 : ℕ) : ℝ) + 1 = 2 * (t : ℝ) := by exact_mod_cast this
        have hsub_t : ((2 * t - 1 : ℕ) : ℝ) = 2 * (t : ℝ) - 1 := by linarith
        dsimp [μ]
        push_cast
        rw [hsub_t]
      have hlt_nat : (2 * t - 1) * w < (extNeighIn Gᶜ U_rem T).card := by
        exact_mod_cast (h2t_eq.trans_lt hlt)
      omega
    exact not_isInducedSubgraphFree_pkCompl_of_expanding G U_rem t w ht hw_pos hw_le_U
      hdeg_U hexp_2t hG

/-!
## Section 3: Lemma 4(1) & Seinsche's Theorem — Equal-Sized Trigger-Set Peeling to Cograph Blockades
and Seinsche's Cograph Product Theorem (`main.tex` lines 219–241)
-/

/-! ### Section 3A: Lemma 4(1) — Equal-Sized Trigger-Set Peeling to Cograph Blockades -/

/--
Constructs a cograph ($P_4$-free) pattern graph on `Fin k` from a boolean attachment vector
`isComp : Fin k → Prop` where vertex $i < j$ is complete or anticomplete to all $j > i$.
-/
def sequentialCograph {k : ℕ} (isComp : Fin k → Prop) : SimpleGraph (Fin k) where
  Adj i j := (i < j ∧ isComp i) ∨ (j < i ∧ isComp j)
  symm _ _ := fun h => h.symm
  loopless i := by
    rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact lt_irrefl i h

/--
Every `sequentialCograph isComp` is $P_4$-free (`IsInducedSubgraphFree _ (pathGraph 4)`), since in
any 4-element subset of `Fin k`, the minimum-index vertex has identical adjacency to the other 3
vertices, whereas every vertex of $P_4$ has both a neighbor and a non-neighbor in $P_4$.
-/
theorem sequentialCograph_isInducedSubgraphFree_pathGraph4 {k : ℕ} (isComp : Fin k → Prop) :
    IsInducedSubgraphFree (sequentialCograph isComp) (pathGraph 4) := by
  classical
  rintro ⟨g, hg⟩
  have huniv_ne : (Finset.univ : Finset (Fin 4)).Nonempty := ⟨0, mem_univ 0⟩
  obtain ⟨a₀, _, ha₀_min⟩ := exists_min_image Finset.univ (fun a : Fin 4 => (g a).1) huniv_ne
  have hlt_of_ne : ∀ b : Fin 4, b ≠ a₀ → g a₀ < g b := by
    intro b hb
    have hle : (g a₀).1 ≤ (g b).1 := ha₀_min b (mem_univ b)
    have hne : (g a₀).1 ≠ (g b).1 := Fin.val_ne_of_ne (g.injective.ne hb.symm)
    exact Nat.lt_of_le_of_ne hle hne
  have hadj_iff : ∀ b : Fin 4, b ≠ a₀ → ((pathGraph 4).Adj a₀ b ↔ isComp (g a₀)) := by
    intro b hb
    have h1 : (pathGraph 4).Adj a₀ b ↔ (sequentialCograph isComp).Adj (g a₀) (g b) := by
      conv_lhs => rw [hg]
      rfl
    rw [h1]
    dsimp [sequentialCograph]
    have hlt := hlt_of_ne b hb
    have hnot_gt : ¬(g b < g a₀) := not_lt_of_gt hlt
    simp [hlt, hnot_gt]
  fin_cases a₀
  · have h1 := (hadj_iff 1 (by decide)).mp (by decide)
    have h2 := (hadj_iff 2 (by decide)).mpr h1
    revert h2; decide
  · have h1 := (hadj_iff 0 (by decide)).mp (by decide)
    have h2 := (hadj_iff 3 (by decide)).mpr h1
    revert h2; decide
  · have h1 := (hadj_iff 3 (by decide)).mp (by decide)
    have h2 := (hadj_iff 0 (by decide)).mpr h1
    revert h2; decide
  · have h1 := (hadj_iff 2 (by decide)).mp (by decide)
    have h2 := (hadj_iff 1 (by decide)).mpr h1
    revert h2; decide

/--
Inductive helper for Lemma 4(1) (`equal_sized_trigger_peeling_cograph`, `main.tex` lines 222–240).
-/
private theorem equal_sized_trigger_peeling_aux (G : SimpleGraph V) (F₀ : Finset V)
    (a b y x : ℝ) (w : ℕ)
    (_ha : 1 ≤ a) (hb : 1 ≤ b) (hx : 0 ≤ x) (hy0 : 0 < y) (hyc : y ≤ (2 : ℝ) ^ (-4 * b))
    (hw_pos : 1 ≤ w) (hw_le : (w : ℝ) ≤ y ^ (a + 2) * (F₀.card : ℝ))
    (hstep : ∀ F ⊆ F₀, (2 : ℝ) ^ (-4 * b) * (F₀.card : ℝ) ≤ (F.card : ℝ) →
      ∃ X ⊆ F, ∃ Y ⊆ F, Disjoint X Y ∧
        (1 - b * y) * (F.card : ℝ) ≤ (Y.card : ℝ) ∧
        ((X.card = w ∧ (IsCompletePair G X Y ∨ IsXSparseTo G Y X x)) ∨
         (y ^ a * (F.card : ℝ) ≤ (X.card : ℝ) ∧ IsPurePair G X Y))) :
    ∀ (p s : ℕ), 1 ≤ p →
      (s : ℝ) + (p : ℝ) - 1 ≤ 2 * y⁻¹ →
      ∀ R ⊆ F₀, (1 - b * y) ^ s * (F₀.card : ℝ) ≤ (R.card : ℝ) →
        ∃ (B : Fin p → Finset V) (isComp : Fin p → Prop),
          IsBlockadeIn G R p (w : ℝ) B ∧
          (∀ i : Fin p, (B i).card = w) ∧
          (∀ i j : Fin p, i < j →
            (isComp i → IsCompletePair G (B i) (B j)) ∧
            (¬isComp i → IsXSparseTo G (B j) (B i) x)) ∧
          (x = 0 → ∀ i j : Fin p, i < j → ¬isComp i → IsAnticompletePair G (B i) (B j)) := by
  classical
  intro p
  induction p with
  | zero =>
    intro _ hp
    omega
  | succ p' ih =>
    intro s _hp hs R hRF₀ hR_card
    have hs_le : (s : ℝ) ≤ 2 * y⁻¹ := by
      have hp' : (0 : ℝ) ≤ (p' : ℝ) := Nat.cast_nonneg p'
      push_cast at hs
      linarith
    have hc_le_pow : (2 : ℝ) ^ (-4 * b) ≤ (1 - b * y) ^ s :=
      rpow_neg_four_le_one_sub_mul_pow hb hy0 hyc s hs_le
    have hR_ge_c : (2 : ℝ) ^ (-4 * b) * (F₀.card : ℝ) ≤ (R.card : ℝ) :=
      le_trans (mul_le_mul_of_nonneg_right hc_le_pow (Nat.cast_nonneg _)) hR_card
    have hy_lt_one : y < 1 := by
      have : (2 : ℝ) ^ (-4 * b) ≤ (2 : ℝ) ^ (-4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      have : (2 : ℝ) ^ (-4 : ℝ) < 1 := by norm_num
      linarith
    have hy2_le_c : y ^ (a + 2) ≤ y ^ a * (2 : ℝ) ^ (-4 * b) := by
      have h1 : y ^ (a + 2) = y ^ a * y * y := by
        rw [Real.rpow_add hy0, Real.rpow_two]
        ring
      have h2 : y * y ≤ (2 : ℝ) ^ (-4 * b) * 1 :=
        mul_le_mul hyc hy_lt_one.le hy0.le (by positivity)
      rw [h1]
      nlinarith [Real.rpow_pos_of_pos hy0 a]
    obtain ⟨X, hXR, Y, hYR, hdisj, hY_card, hcase⟩ := hstep R hRF₀ hR_ge_c
    have hB₀_ex : ∃ (B₀ : Finset V) (c₀ : Prop),
        B₀ ⊆ X ∧ B₀.card = w ∧
        (c₀ → IsCompletePair G B₀ Y) ∧
        (¬c₀ → IsXSparseTo G Y B₀ x) ∧
        (x = 0 → ¬c₀ → IsAnticompletePair G B₀ Y) := by
      rcases hcase with ⟨hX_card_w, hXY_rel⟩ | ⟨hX_card_ya, hXY_pure⟩
      · rcases hXY_rel with hcomp | hsp
        · refine ⟨X, True, Subset.rfl, hX_card_w, fun _ => hcomp, fun h => (h trivial).elim,
            fun _ h => (h trivial).elim⟩
        · refine ⟨X, False, Subset.rfl, hX_card_w, fun h => h.elim, fun _ => hsp, ?_⟩
          intro hx0 _ u huX v hvY hadj
          have hdeg := hsp v hvY
          rw [hx0, zero_mul] at hdeg
          have hu_mem : u ∈ neighborFinsetIn G v X :=
            (mem_neighborFinsetIn' G v u X).mpr ⟨huX, hadj.symm⟩
          have hpos : 0 < (neighborFinsetIn G v X).card := card_pos.mpr ⟨u, hu_mem⟩
          have hpos_r : (0 : ℝ) < ((neighborFinsetIn G v X).card : ℝ) := by exact_mod_cast hpos
          linarith
      · have hw_le_X_real : (w : ℝ) ≤ (X.card : ℝ) := by
          calc (w : ℝ)
            _ ≤ y ^ (a + 2) * (F₀.card : ℝ) := hw_le
            _ ≤ y ^ a * ((2 : ℝ) ^ (-4 * b) * (F₀.card : ℝ)) := by nlinarith
            _ ≤ y ^ a * (R.card : ℝ) := mul_le_mul_of_nonneg_left hR_ge_c (by positivity)
            _ ≤ (X.card : ℝ) := hX_card_ya
        have hw_le_X : w ≤ X.card := by exact_mod_cast hw_le_X_real
        obtain ⟨B₀, hB₀X, hB₀_card⟩ := exists_subset_card_eq hw_le_X
        rcases hXY_pure with hcomp | hanti
        · refine ⟨B₀, True, hB₀X, hB₀_card, fun _ => isCompletePair_mono hB₀X Subset.rfl hcomp,
            fun h => (h trivial).elim, fun _ h => (h trivial).elim⟩
        · refine ⟨B₀, False, hB₀X, hB₀_card, fun h => h.elim, ?_,
            fun _ _ => hanti.mono hB₀X Subset.rfl⟩
          intro _ v hvY
          have hemp : neighborFinsetIn G v B₀ = ∅ := by
            rw [eq_empty_iff_forall_notMem]
            intro u hu
            rw [mem_neighborFinsetIn'] at hu
            exact hanti u (hB₀X hu.1) v hvY hu.2.symm
          rw [hemp, card_empty, Nat.cast_zero]
          positivity
    obtain ⟨B₀, c₀, hB₀X, hB₀_card, hB₀_comp, hB₀_sp, hB₀_anti⟩ := hB₀_ex
    have hB₀R : B₀ ⊆ R := hB₀X.trans hXR
    have hB₀_ne : B₀.Nonempty := card_pos.mp (by omega)
    have hdisj_B₀Y : Disjoint B₀ Y := Disjoint.mono_left hB₀X hdisj
    rcases Nat.eq_zero_or_pos p' with rfl | hp'
    · refine ⟨fun _ => B₀, fun _ => c₀, ?_, fun _ => hB₀_card, ?_, ?_⟩
      · refine ⟨fun _ => hB₀R, fun _ => hB₀_ne, ?_, fun _ => by rw [hB₀_card]⟩
        intro i j hij
        exact (hij (Fin.ext (by omega))).elim
      · intro i j hij
        exact (by omega : ¬i < j).elim hij
      · intro _ i j hij
        exact (by omega : ¬i < j).elim hij
    · have hYF₀ : Y ⊆ F₀ := hYR.trans hRF₀
      have hY_pow : (1 - b * y) ^ (s + 1) * (F₀.card : ℝ) ≤ (Y.card : ℝ) := by
        have h1_sub_nonneg : 0 ≤ 1 - b * y := by
          have := mul_rpow_neg_four_le_quarter hb
          have : b * y ≤ 1 / 4 :=
            (mul_le_mul_of_nonneg_left hyc (by linarith)).trans this
          linarith
        rw [pow_succ']
        calc (1 - b * y) * (1 - b * y) ^ s * (F₀.card : ℝ)
          _ = (1 - b * y) * ((1 - b * y) ^ s * (F₀.card : ℝ)) := by ring
          _ ≤ (1 - b * y) * (R.card : ℝ) :=
            mul_le_mul_of_nonneg_left hR_card h1_sub_nonneg
          _ ≤ (Y.card : ℝ) := hY_card
      have hs' : ((s + 1 : ℕ) : ℝ) + (p' : ℝ) - 1 ≤ 2 * y⁻¹ := by
        push_cast at hs ⊢
        linarith
      obtain ⟨B', isComp', hB'_block, hB'_card, hB'_rel, hB'_anti⟩ :=
        ih (s + 1) hp' hs' Y hYF₀ hY_pow
      refine ⟨Fin.cons B₀ B', Fin.cons c₀ isComp', ?_, ?_, ?_, ?_⟩
      · refine ⟨?_, ?_, ?_, ?_⟩
        · intro i
          exact Fin.cases hB₀R (fun j => (hB'_block.subset_ambient j).trans hYR) i
        · intro i
          exact Fin.cases hB₀_ne hB'_block.nonempty_blocks i
        · intro i j
          induction i using Fin.cases with
          | zero =>
            induction j using Fin.cases with
            | zero => intro hij; exact (hij rfl).elim
            | succ j' =>
              intro _
              simp only [Fin.cons_zero, Fin.cons_succ]
              exact Disjoint.mono_right (hB'_block.subset_ambient j') hdisj_B₀Y
          | succ i' =>
            induction j using Fin.cases with
            | zero =>
              intro _
              simp only [Fin.cons_zero, Fin.cons_succ]
              exact (Disjoint.mono_right (hB'_block.subset_ambient i') hdisj_B₀Y).symm
            | succ j' =>
              intro hij
              simp only [Fin.cons_succ]
              exact hB'_block.pairwise_disjoint i' j' (fun h => hij (congrArg Fin.succ h))
        · intro i
          exact Fin.cases (by simp [hB₀_card]) hB'_block.width_ge i
      · intro i
        exact Fin.cases hB₀_card hB'_card i
      · intro i j
        induction i using Fin.cases with
        | zero =>
          induction j using Fin.cases with
          | zero => intro hij; exact (lt_irrefl _ hij).elim
          | succ j' =>
            intro _
            simp only [Fin.cons_zero, Fin.cons_succ]
            exact ⟨fun hc => isCompletePair_mono Subset.rfl (hB'_block.subset_ambient j') (hB₀_comp hc),
              fun hnc v hv => hB₀_sp hnc v (hB'_block.subset_ambient j' hv)⟩
        | succ i' =>
          induction j using Fin.cases with
          | zero => intro hij; exact (Nat.not_lt_zero _ hij).elim
          | succ j' =>
            intro hij
            simp only [Fin.cons_succ]
            exact hB'_rel i' j' (Fin.succ_lt_succ_iff.mp hij)
      · intro hx0 i j
        induction i using Fin.cases with
        | zero =>
          induction j using Fin.cases with
          | zero => intro hij; exact (lt_irrefl _ hij).elim
          | succ j' =>
            intro _ hnc
            simp only [Fin.cons_zero, Fin.cons_succ] at hnc ⊢
            exact (hB₀_anti hx0 hnc).mono Subset.rfl (hB'_block.subset_ambient j')
        | succ i' =>
          induction j using Fin.cases with
          | zero => intro hij; exact (Nat.not_lt_zero _ hij).elim
          | succ j' =>
            intro hij hnc
            simp only [Fin.cons_succ] at hnc ⊢
            exact hB'_anti hx0 i' j' (Fin.succ_lt_succ_iff.mp hij) hnc

/--
**Lemma 4(1) (`equal_sized_trigger_peeling_cograph`, Equal-Sized Trigger-Set Peeling to Blockade
Iteration, `main.tex` lines 222–240)**:
Let $a, b \ge 1$, $c := 2^{-4b}$, $0 \le x$, and $0 < y \le c$. Let $F_0 \subseteq V(G)$ with
$y^{a+2}|F_0| \ge 1$ and set $w := \lfloor y^{a+2}|F_0| \rfloor \ge 1$. Suppose every induced
subgraph $F \subseteq F_0$ with $|F| \ge c |F_0|$ contains disjoint subsets $X, Y \subseteq F$ with
$|Y| \ge (1 - by)|F|$ satisfying either:
- **(a)** $|X| = w$ and $Y$ is complete or pointwise $x$-sparse to $X$ in $G$ (`IsCompletePair G X Y ∨ IsXSparseTo G Y X x`); or
- **(b)** $|X| \ge y^a |F|$ and $(X, Y)$ is pure (complete or anticomplete) in $G$ (`IsPurePair G X Y`).
Then $F_0$ contains an equal-sized $(\lceil y^{-1} \rceil, w)$-blockade $B$ (`∀ i, (B i).card = w`)
and a cograph ($P_4$-free) pattern graph $J$ on $\text{Fin }\lceil y^{-1} \rceil$ (`sequentialCograph`)
such that:
1. every edge $ij \in E(J)$ is $100\%$ complete in $G$ (`IsCompletePair G (B i) (B j)`);
2. every non-edge $(i, j)$ ($i < j$) has $B_j$ pointwise $x$-sparse to $B_i$ in $G$ (with zero
   sub-sampling loss in case (a)), and hence $(B_i, B_j)$ is weakly $x$-sparse in $G$; and
3. when $x = 0$, $B$ is a $100\%$ pairwise-pure cograph blockade (`IsPureCographBlockadeIn G F₀ k w B`).
-/
theorem equal_sized_trigger_peeling_cograph (G : SimpleGraph V) (F₀ : Finset V)
    (a b y x : ℝ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hx : 0 ≤ x) (hy0 : 0 < y) (hyc : y ≤ (2 : ℝ) ^ (-4 * b))
    (hw₀ : 1 ≤ y ^ (a + 2) * (F₀.card : ℝ))
    (hstep : ∀ F ⊆ F₀, (2 : ℝ) ^ (-4 * b) * (F₀.card : ℝ) ≤ (F.card : ℝ) →
      ∃ X ⊆ F, ∃ Y ⊆ F, Disjoint X Y ∧
        (1 - b * y) * (F.card : ℝ) ≤ (Y.card : ℝ) ∧
        ((X.card = ⌊y ^ (a + 2) * (F₀.card : ℝ)⌋₊ ∧
            (IsCompletePair G X Y ∨ IsXSparseTo G Y X x)) ∨
         (y ^ a * (F.card : ℝ) ≤ (X.card : ℝ) ∧ IsPurePair G X Y))) :
    let k := ⌈y⁻¹⌉₊
    let w := ⌊y ^ (a + 2) * (F₀.card : ℝ)⌋₊
    ∃ (B : Fin k → Finset V) (J : SimpleGraph (Fin k)),
      IsBlockadeIn G F₀ k (w : ℝ) B ∧
      (∀ i : Fin k, (B i).card = w) ∧
      IsInducedSubgraphFree J (pathGraph 4) ∧
      (∀ i j : Fin k, i ≠ j →
        (J.Adj i j → IsCompletePair G (B i) (B j)) ∧
        (¬J.Adj i j → IsWeaklySparsePair G (B i) (B j) x)) ∧
      (∀ i j : Fin k, i < j → ¬J.Adj i j → IsXSparseTo G (B j) (B i) x) ∧
      (x = 0 → IsPureCographBlockadeIn G F₀ k (w : ℝ) B) := by
  classical
  let k := ⌈y⁻¹⌉₊
  let w := ⌊y ^ (a + 2) * (F₀.card : ℝ)⌋₊
  have hk_pos : 1 ≤ k := Nat.ceil_pos.mpr (inv_pos.mpr hy0)
  have hk_lt : (k : ℝ) < y⁻¹ + 1 := Nat.ceil_lt_add_one (inv_nonneg.mpr hy0.le)
  have hy_inv_pos : 0 < y⁻¹ := inv_pos.mpr hy0
  have hs0 : ((0 : ℕ) : ℝ) + (k : ℝ) - 1 ≤ 2 * y⁻¹ := by
    push_cast
    linarith
  have hw_pos : 1 ≤ w := Nat.floor_pos.mpr hw₀
  have hw_le : (w : ℝ) ≤ y ^ (a + 2) * (F₀.card : ℝ) := Nat.floor_le (by positivity)
  have hF₀_pow : (1 - b * y) ^ 0 * (F₀.card : ℝ) ≤ (F₀.card : ℝ) := by simp
  obtain ⟨B, isComp, hB_block, hB_card, hB_rel, hB_anti⟩ :=
    equal_sized_trigger_peeling_aux G F₀ a b y x w ha hb hx hy0 hyc hw_pos hw_le hstep
      k 0 hk_pos hs0 F₀ Subset.rfl hF₀_pow
  let J := sequentialCograph isComp
  refine ⟨B, J, hB_block, hB_card, sequentialCograph_isInducedSubgraphFree_pathGraph4 isComp,
    ?_, ?_, ?_⟩
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hadj_iff : J.Adj i j ↔ isComp i := by
        dsimp [J, sequentialCograph]
        have hnot_gt : ¬(j < i) := not_lt_of_gt hlt
        simp [hlt, hnot_gt]
      rw [hadj_iff]
      refine ⟨(hB_rel i j hlt).1, fun hnc => ?_⟩
      have hsp := (hB_rel i j hlt).2 hnc
      have hwj : IsWeaklySparsePair G (B j) (B i) x := isWeaklySparsePair_of_isXSparseTo hsp
      unfold IsWeaklySparsePair at hwj ⊢
      rw [crossEdgeCount_comm']
      calc (crossEdgeCount G (B j) (B i) : ℝ)
        _ ≤ x * ((B j).card : ℝ) * ((B i).card : ℝ) := hwj
        _ = x * ((B i).card : ℝ) * ((B j).card : ℝ) := by ring
    · have hadj_iff : J.Adj i j ↔ isComp j := by
        dsimp [J, sequentialCograph]
        have hnot_lt : ¬(i < j) := not_lt_of_gt hgt
        simp [hgt, hnot_lt]
      rw [hadj_iff]
      refine ⟨fun hc => isCompletePair_symm ((hB_rel j i hgt).1 hc), fun hnc => ?_⟩
      exact isWeaklySparsePair_of_isXSparseTo ((hB_rel j i hgt).2 hnc)
  · intro i j hlt hnadj
    have hnc : ¬isComp i := fun hc => hnadj (Or.inl ⟨hlt, hc⟩)
    exact (hB_rel i j hlt).2 hnc
  · intro hx0
    have hJ_eq_pure : purePatternGraph G B = J := by
      ext i j
      dsimp [purePatternGraph, J, sequentialCograph]
      by_cases hij : i = j
      · subst hij
        simp
      · simp only [hij, not_false_eq_true, true_and]
        rcases lt_or_gt_of_ne hij with hlt | hgt
        · have hnot_gt : ¬(j < i) := not_lt_of_gt hlt
          simp only [hlt, hnot_gt, false_and, or_false, true_and]
          constructor
          · intro hcomp
            by_contra hnc
            obtain ⟨u, hu⟩ := hB_block.nonempty_blocks i
            obtain ⟨v, hv⟩ := hB_block.nonempty_blocks j
            exact hB_anti hx0 i j hlt hnc u hu v hv (hcomp u hu v hv)
          · exact (hB_rel i j hlt).1
        · have hnot_lt : ¬(i < j) := not_lt_of_gt hgt
          simp only [hgt, hnot_lt, false_and, false_or, true_and]
          constructor
          · intro hcomp
            by_contra hnc
            obtain ⟨u, hu⟩ := hB_block.nonempty_blocks j
            obtain ⟨v, hv⟩ := hB_block.nonempty_blocks i
            exact hB_anti hx0 j i hgt hnc u hu v hv (hcomp v hv u hu).symm
          · exact fun hc => isCompletePair_symm ((hB_rel j i hgt).1 hc)
    refine ⟨⟨hB_block, fun i j hij => ?_⟩, ?_⟩
    · rcases lt_or_gt_of_ne hij with hlt | hgt
      · by_cases hc : isComp i
        · exact Or.inl ((hB_rel i j hlt).1 hc)
        · exact Or.inr (hB_anti hx0 i j hlt hc)
      · by_cases hc : isComp j
        · exact Or.inl (isCompletePair_symm ((hB_rel j i hgt).1 hc))
        · exact Or.inr (hB_anti hx0 j i hgt hc).symm
    · rw [hJ_eq_pure]
      exact sequentialCograph_isInducedSubgraphFree_pathGraph4 isComp

/-! ### Section 3B: Seinsche's Theorem (`seinsche_cograph_clique_mul_indep`) -/

/-- Explicit permutation `![2, 0, 3, 1]` on `Fin 4` witnessing `(pathGraph 4)ᶜ ≃g pathGraph 4`. -/
def pathGraph4ComplEquiv : Fin 4 ≃ Fin 4 where
  toFun := ![2, 0, 3, 1]
  invFun := ![1, 3, 0, 2]
  left_inv x := by fin_cases x <;> decide
  right_inv x := by fin_cases x <;> decide

/-- $\overline{P_4} \cong P_4$. -/
def pathGraph4ComplIso : (pathGraph 4)ᶜ ≃g pathGraph 4 where
  toEquiv := pathGraph4ComplEquiv
  map_rel_iff' := by
    intro a b
    fin_cases a <;> fin_cases b <;> decide

/-- A graph $J$ is $P_4$-free if and only if its complement $Jᶜ$ is $P_4$-free. -/
theorem isInducedSubgraphFree_compl_pathGraph4 {W : Type*} (J : SimpleGraph W) :
    IsInducedSubgraphFree Jᶜ (pathGraph 4) ↔ IsInducedSubgraphFree J (pathGraph 4) := by
  rw [isInducedSubgraphFree_compl_iff J (pathGraph 4)]
  constructor
  · rintro h ⟨g, hg⟩
    apply h
    refine ⟨pathGraph4ComplIso.symm.toEquiv.toEmbedding.trans g, ?_⟩
    ext u v
    simp only [comap_adj, Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
    rw [← pathGraph4ComplIso.symm.map_rel_iff]
    exact congr_arg (fun (H : SimpleGraph (Fin 4)) => H.Adj (pathGraph4ComplIso.symm u) (pathGraph4ComplIso.symm v)) hg |>.to_iff
  · rintro h ⟨g, hg⟩
    apply h
    refine ⟨pathGraph4ComplIso.toEquiv.toEmbedding.trans g, ?_⟩
    ext u v
    simp only [comap_adj, Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
    rw [← pathGraph4ComplIso.map_rel_iff]
    exact congr_arg (fun (H : SimpleGraph (Fin 4)) => H.Adj (pathGraph4ComplIso u) (pathGraph4ComplIso v)) hg |>.to_iff

/--
Explicit 4-vertex witness showing that $(b, v_0, a_1, a_2)$ induces $P_4$ in $H$ when consecutive
pairs are adjacent and non-consecutive pairs are non-adjacent.
-/
private theorem not_isInducedSubgraphFree_pathGraph4 {W : Type*} {H : SimpleGraph W}
    (b v₀ a₁ a₂ : W)
    (hne_bv₀ : b ≠ v₀) (hne_ba₁ : b ≠ a₁) (hne_ba₂ : b ≠ a₂)
    (hne_v₀a₁ : v₀ ≠ a₁) (hne_v₀a₂ : v₀ ≠ a₂) (hne_a₁a₂ : a₁ ≠ a₂)
    (ha_bv₀ : H.Adj b v₀) (ha_v₀a₁ : H.Adj v₀ a₁) (ha_a₁a₂ : H.Adj a₁ a₂)
    (hn_ba₁ : ¬H.Adj b a₁) (hn_ba₂ : ¬H.Adj b a₂) (hn_v₀a₂ : ¬H.Adj v₀ a₂) :
    ¬IsInducedSubgraphFree H (pathGraph 4) := by
  intro hfree
  apply hfree
  let f : Fin 4 → W := ![b, v₀, a₁, a₂]
  have hf_inj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [f] at hij ⊢ <;>
      first | exact False.elim (hne_bv₀ hij) | exact False.elim (hne_bv₀ hij.symm)
            | exact False.elim (hne_ba₁ hij) | exact False.elim (hne_ba₁ hij.symm)
            | exact False.elim (hne_ba₂ hij) | exact False.elim (hne_ba₂ hij.symm)
            | exact False.elim (hne_v₀a₁ hij) | exact False.elim (hne_v₀a₁ hij.symm)
            | exact False.elim (hne_v₀a₂ hij) | exact False.elim (hne_v₀a₂ hij.symm)
            | exact False.elim (hne_a₁a₂ hij) | exact False.elim (hne_a₁a₂ hij.symm)
  refine ⟨⟨f, hf_inj⟩, ?_⟩
  ext i j
  simp only [pathGraph_adj, comap_adj, Function.Embedding.coeFn_mk]
  fin_cases i <;> fin_cases j <;> simp [f] <;>
    first | exact ha_bv₀ | exact ha_bv₀.symm | exact ha_v₀a₁ | exact ha_v₀a₁.symm
          | exact ha_a₁a₂ | exact ha_a₁a₂.symm
          | exact hn_ba₁ | exact fun h => hn_ba₁ h.symm
          | exact hn_ba₂ | exact fun h => hn_ba₂ h.symm
          | exact hn_v₀a₂ | exact fun h => hn_v₀a₂ h.symm

/--
Inductive step of Seinsche's disconnection lemma: if $S' = S \setminus \{v_0\} = A_0 \sqcup B_0$
is an anticomplete bipartition of $S'$ in a $P_4$-free graph $H$ and $z \in A_0$ is non-adjacent
to $v_0$, then $S$ admits a pure (complete or anticomplete) bipartition in $H$.
-/
private theorem extend_anticomplete_bipartition_one_side {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (hH : IsInducedSubgraphFree H (pathGraph 4))
    (S A₀ B₀ : Finset W) (v₀ z : W)
    (hv₀ : v₀ ∈ S) (hAB_union : A₀ ∪ B₀ = S.erase v₀) (hAB_disj : Disjoint A₀ B₀)
    (_hA₀_ne : A₀.Nonempty) (hB₀_ne : B₀.Nonempty)
    (hanti_AB : IsAnticompletePair H A₀ B₀)
    (hzA₀ : z ∈ A₀) (hz_nadj : ¬H.Adj v₀ z) :
    ∃ A B : Finset W, A ∪ B = S ∧ Disjoint A B ∧ A.Nonempty ∧ B.Nonempty ∧
      (IsCompletePair H A B ∨ IsAnticompletePair H A B) := by
  classical
  let S' := S.erase v₀
  have hA₀S' : A₀ ⊆ S' := by dsimp [S']; rw [← hAB_union]; exact subset_union_left
  have hB₀S' : B₀ ⊆ S' := by dsimp [S']; rw [← hAB_union]; exact subset_union_right
  have hv₀_not_S' : v₀ ∉ S' := notMem_erase v₀ S
  -- Connected component C₁ of H[A₀] containing z
  let C₁ := A₀.filter (fun x => ∃ hx : x ∈ A₀, (H.induce (A₀ : Set W)).Reachable ⟨z, hzA₀⟩ ⟨x, hx⟩)
  have hC₁A₀ : C₁ ⊆ A₀ := filter_subset _ _
  have hzC₁ : z ∈ C₁ := by
    refine mem_filter.mpr ⟨hzA₀, hzA₀, Reachable.refl _⟩
  have hC₁_ne : C₁.Nonempty := ⟨z, hzC₁⟩
  have hC₁_anti_A₀ : IsAnticompletePair H C₁ (A₀ \ C₁) := by
    intro x hx y hy hadj
    obtain ⟨hxA₀, _, hreach⟩ := mem_filter.mp hx
    obtain ⟨hyA₀, hy_not_C₁⟩ := mem_sdiff.mp hy
    have hadj_ind : (H.induce (A₀ : Set W)).Adj ⟨x, hxA₀⟩ ⟨y, hyA₀⟩ := hadj
    exact hy_not_C₁ (mem_filter.mpr ⟨hyA₀, hyA₀, hreach.trans (Adj.reachable hadj_ind)⟩)
  have hC₁_conn : (H.induce (C₁ : Set W)).Connected := by
    rw [connected_iff_exists_forall_reachable]
    refine ⟨⟨z, hzC₁⟩, ?_⟩
    rintro ⟨x, hxC₁⟩
    obtain ⟨hxA₀, _, hreach⟩ := mem_filter.mp hxC₁
    obtain ⟨p⟩ := hreach
    have hp_in_C₁ : ∀ (u w : ↥(A₀ : Set W)) (q : (H.induce (A₀ : Set W)).Walk u w),
        u.1 ∈ C₁ → (∀ y ∈ q.support, y.1 ∈ C₁) := by
      intro u w q
      induction q with
      | nil =>
        intro hu y hy
        simp only [Walk.support_nil, List.mem_singleton] at hy
        subst hy
        exact hu
      | @cons u₁ u₂ u₃ hadj q ih =>
        intro hu₁ y hy
        have hu₂_C₁ : u₂.1 ∈ C₁ := by
          by_contra hu₂_not
          exact hC₁_anti_A₀ u₁.1 hu₁ u₂.1 (mem_sdiff.mpr ⟨u₂.2, hu₂_not⟩) hadj
        simp only [Walk.support_cons, List.mem_cons] at hy
        rcases hy with rfl | hy'
        · exact hu₁
        · exact ih hu₂_C₁ y hy'
    have hwalk_sub : ∀ y ∈ p.support, y.1 ∈ C₁ := hp_in_C₁ ⟨z, hzA₀⟩ ⟨x, hxA₀⟩ p hzC₁
    -- Lift walk `p` to `H.induce C₁`
    have hlift : ∀ (u w : ↥(A₀ : Set W)) (q : (H.induce (A₀ : Set W)).Walk u w)
        (hu : u.1 ∈ C₁) (hw : w.1 ∈ C₁) (hq : ∀ y ∈ q.support, y.1 ∈ C₁),
        (H.induce (C₁ : Set W)).Reachable ⟨u.1, hu⟩ ⟨w.1, hw⟩ := by
      intro u w q
      induction q with
      | nil =>
        intro hu _ _
        exact Reachable.refl _
      | @cons u₁ u₂ u₃ hadj q ih =>
        intro hu₁ hu₃ hq
        have hu₂ : u₂.1 ∈ C₁ := hq u₂ (Walk.start_mem_support q |> List.mem_cons_of_mem u₁)
        have hadj_C₁ : (H.induce (C₁ : Set W)).Adj ⟨u₁.1, hu₁⟩ ⟨u₂.1, hu₂⟩ := hadj
        exact (Adj.reachable hadj_C₁).trans
          (ih hu₂ hu₃ (fun y hy => hq y (List.mem_cons_of_mem u₁ hy)))
    exact hlift ⟨z, hzA₀⟩ ⟨x, hxA₀⟩ p hzC₁ hxC₁ hwalk_sub
  -- Connected component C₂ of H[B₀] via exists_anticonnected_component_in on Hᶜ
  obtain ⟨C₂, hC₂B₀, hC₂_ne, _, hC₂_comp_c⟩ := exists_anticonnected_component_in Hᶜ B₀ hB₀_ne
  have hC₂_anti_B₀ : IsAnticompletePair H C₂ (B₀ \ C₂) := by
    have hd : Disjoint C₂ (B₀ \ C₂) := disjoint_sdiff_self_right
    rw [isAnticompletePair_iff_isCompletePair_compl hd]
    exact hC₂_comp_c
  -- Check whether v₀ has any H-neighbor in C₁ and in C₂
  by_cases hC₁_nadj : ∀ x ∈ C₁, ¬H.Adj v₀ x
  · -- C₁ is H-anticomplete to S \ C₁
    have hC₁S : C₁ ⊆ S := hC₁A₀.trans (hA₀S'.trans (erase_subset v₀ S))
    have hSC₁_ne : (S \ C₁).Nonempty := by
      obtain ⟨b, hb⟩ := hC₂_ne
      refine ⟨b, mem_sdiff.mpr ⟨hB₀S' (hC₂B₀ hb) |> mem_of_mem_erase, ?_⟩⟩
      intro hbC₁
      exact Finset.disjoint_left.mp hAB_disj (hC₁A₀ hbC₁) (hC₂B₀ hb)
    refine ⟨C₁, S \ C₁, union_sdiff_of_subset hC₁S, disjoint_sdiff_self_right, hC₁_ne, hSC₁_ne, Or.inr ?_⟩
    intro x hxC₁ y hySC₁ hadj
    obtain ⟨hyS, hy_not_C₁⟩ := mem_sdiff.mp hySC₁
    by_cases hyv₀ : y = v₀
    · subst hyv₀
      exact hC₁_nadj x hxC₁ hadj.symm
    · have hyS' : y ∈ S.erase v₀ := mem_erase.mpr ⟨hyv₀, hyS⟩
      rw [← hAB_union] at hyS'
      rcases mem_union.mp hyS' with hyA₀ | hyB₀
      · exact hC₁_anti_A₀ x hxC₁ y (mem_sdiff.mpr ⟨hyA₀, hy_not_C₁⟩) hadj
      · exact hanti_AB x (hC₁A₀ hxC₁) y hyB₀ hadj
  · push_neg at hC₁_nadj
    obtain ⟨x₁, hx₁C₁, hx₁_adj⟩ := hC₁_nadj
    by_cases hC₂_nadj : ∀ y ∈ C₂, ¬H.Adj v₀ y
    · -- C₂ is H-anticomplete to S \ C₂
      have hC₂S : C₂ ⊆ S := hC₂B₀.trans (hB₀S'.trans (erase_subset v₀ S))
      have hSC₂_ne : (S \ C₂).Nonempty := by
        refine ⟨z, mem_sdiff.mpr ⟨hA₀S' hzA₀ |> mem_of_mem_erase, ?_⟩⟩
        intro hzC₂
        exact Finset.disjoint_left.mp hAB_disj hzA₀ (hC₂B₀ hzC₂)
      refine ⟨C₂, S \ C₂, union_sdiff_of_subset hC₂S, disjoint_sdiff_self_right, hC₂_ne, hSC₂_ne, Or.inr ?_⟩
      intro x hxC₂ y hySC₂ hadj
      obtain ⟨hyS, hy_not_C₂⟩ := mem_sdiff.mp hySC₂
      by_cases hyv₀ : y = v₀
      · subst hyv₀
        exact hC₂_nadj x hxC₂ hadj.symm
      · have hyS' : y ∈ S.erase v₀ := mem_erase.mpr ⟨hyv₀, hyS⟩
        rw [← hAB_union] at hyS'
        rcases mem_union.mp hyS' with hyA₀ | hyB₀
        · exact hanti_AB y hyA₀ x (hC₂B₀ hxC₂) hadj.symm
        · exact hC₂_anti_B₀ x hxC₂ y (mem_sdiff.mpr ⟨hyB₀, hy_not_C₂⟩) hadj
    · exfalso
      push_neg at hC₂_nadj
      obtain ⟨b, hbC₂, hb_adj⟩ := hC₂_nadj
      let N₁ := neighborFinsetIn H v₀ C₁
      have hx₁N₁ : x₁ ∈ N₁ := (mem_neighborFinsetIn' H v₀ x₁ C₁).mpr ⟨hx₁C₁, hx₁_adj⟩
      have hz_not_N₁ : z ∉ N₁ := fun hzN₁ => hz_nadj ((mem_neighborFinsetIn' H v₀ z C₁).mp hzN₁).2
      have hreach : (H.induce (C₁ : Set W)).Reachable ⟨x₁, hx₁C₁⟩ ⟨z, hzC₁⟩ :=
        hC₁_conn ⟨x₁, hx₁C₁⟩ ⟨z, hzC₁⟩
      obtain ⟨a₁, ha₁N₁, a₂, ha₂_sdiff, ha_a₁a₂⟩ :=
        exists_adj_of_walk_mem_notMem H C₁ N₁ hreach.some hx₁N₁ hz_not_N₁
      obtain ⟨ha₁C₁, ha_v₀a₁⟩ := (mem_neighborFinsetIn' H v₀ a₁ C₁).mp ha₁N₁
      obtain ⟨ha₂C₁, ha₂_not_N₁⟩ := mem_sdiff.mp ha₂_sdiff
      have hn_v₀a₂ : ¬H.Adj v₀ a₂ := fun hadj =>
        ha₂_not_N₁ ((mem_neighborFinsetIn' H v₀ a₂ C₁).mpr ⟨ha₂C₁, hadj⟩)
      have ha₁A₀ : a₁ ∈ A₀ := hC₁A₀ ha₁C₁
      have ha₂A₀ : a₂ ∈ A₀ := hC₁A₀ ha₂C₁
      have hbB₀ : b ∈ B₀ := hC₂B₀ hbC₂
      have hn_ba₁ : ¬H.Adj b a₁ := fun hadj => hanti_AB a₁ ha₁A₀ b hbB₀ hadj.symm
      have hn_ba₂ : ¬H.Adj b a₂ := fun hadj => hanti_AB a₂ ha₂A₀ b hbB₀ hadj.symm
      have hne_bv₀ : b ≠ v₀ := fun h => hv₀_not_S' (h ▸ hB₀S' hbB₀)
      have hne_ba₁ : b ≠ a₁ := fun h => Finset.disjoint_right.mp hAB_disj hbB₀ (h ▸ ha₁A₀)
      have hne_ba₂ : b ≠ a₂ := fun h => Finset.disjoint_right.mp hAB_disj hbB₀ (h ▸ ha₂A₀)
      have hne_v₀a₁ : v₀ ≠ a₁ := H.ne_of_adj ha_v₀a₁
      have hne_v₀a₂ : v₀ ≠ a₂ := fun h => hv₀_not_S' (h ▸ hA₀S' ha₂A₀)
      have hne_a₁a₂ : a₁ ≠ a₂ := H.ne_of_adj ha_a₁a₂
      exact not_isInducedSubgraphFree_pathGraph4 b v₀ a₁ a₂
        hne_bv₀ hne_ba₁ hne_ba₂ hne_v₀a₁ hne_v₀a₂ hne_a₁a₂
        hb_adj.symm ha_v₀a₁ ha_a₁a₂ hn_ba₁ hn_ba₂ hn_v₀a₂ hH

private theorem extend_anticomplete_bipartition_of_p4_free {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (hH : IsInducedSubgraphFree H (pathGraph 4))
    (S A₀ B₀ : Finset W) (v₀ : W)
    (hv₀ : v₀ ∈ S) (hAB_union : A₀ ∪ B₀ = S.erase v₀) (hAB_disj : Disjoint A₀ B₀)
    (hA₀_ne : A₀.Nonempty) (hB₀_ne : B₀.Nonempty)
    (hanti_AB : IsAnticompletePair H A₀ B₀) :
    ∃ A B : Finset W, A ∪ B = S ∧ Disjoint A B ∧ A.Nonempty ∧ B.Nonempty ∧
      (IsCompletePair H A B ∨ IsAnticompletePair H A B) := by
  classical
  by_cases hall_adj : ∀ z ∈ S.erase v₀, H.Adj v₀ z
  · -- {v₀} is H-complete to S.erase v₀
    refine ⟨{v₀}, S.erase v₀, ?_, disjoint_singleton_left.mpr (notMem_erase v₀ S),
      singleton_nonempty v₀, hA₀_ne.mono (hAB_union ▸ subset_union_left), Or.inl ?_⟩
    · rw [singleton_union, insert_erase hv₀]
    · intro x hx y hy
      rw [mem_singleton.mp hx]
      exact hall_adj y hy
  · push_neg at hall_adj
    obtain ⟨z, hz_mem, hz_nadj⟩ := hall_adj
    rw [← hAB_union] at hz_mem
    rcases mem_union.mp hz_mem with hzA₀ | hzB₀
    · exact extend_anticomplete_bipartition_one_side H hH S A₀ B₀ v₀ z
        hv₀ hAB_union hAB_disj hA₀_ne hB₀_ne hanti_AB hzA₀ hz_nadj
    · have hBA_union : B₀ ∪ A₀ = S.erase v₀ := by rw [union_comm, hAB_union]
      exact extend_anticomplete_bipartition_one_side H hH S B₀ A₀ v₀ z
        hv₀ hBA_union hAB_disj.symm hB₀_ne hA₀_ne hanti_AB.symm hzB₀ hz_nadj

/--
**Seinsche's Disconnection Lemma (`exists_pure_bipartition_of_p4_free`, `main.tex` line 241)**:
Every induced subgraph $J[S]$ ($|S| \ge 2$) of a $P_4$-free graph $J$ admits a pure bipartition
$S = A \sqcup B$ ($A, B \neq \emptyset$, $(A, B)$ complete or anticomplete in $J$).
-/
theorem exists_pure_bipartition_of_p4_free {W : Type*} [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) (hJ : IsInducedSubgraphFree J (pathGraph 4))
    (S : Finset W) (hS : 2 ≤ S.card) :
    ∃ A B : Finset W, A ∪ B = S ∧ Disjoint A B ∧ A.Nonempty ∧ B.Nonempty ∧
      (IsCompletePair J A B ∨ IsAnticompletePair J A B) := by
  classical
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    subst hn
    by_cases h2 : S.card = 2
    · obtain ⟨u, v, huv, rfl⟩ := card_eq_two.mp h2
      refine ⟨{u}, {v}, rfl, disjoint_singleton.mpr huv, singleton_nonempty u,
        singleton_nonempty v, ?_⟩
      by_cases hadj : J.Adj u v
      · left
        intro x hx y hy
        rw [mem_singleton.mp hx, mem_singleton.mp hy]
        exact hadj
      · right
        intro x hx y hy
        rw [mem_singleton.mp hx, mem_singleton.mp hy]
        exact hadj
    · have h3 : 3 ≤ S.card := by omega
      have hS_ne : S.Nonempty := card_pos.mp (by omega)
      obtain ⟨v₀, hv₀⟩ := hS_ne
      let S' := S.erase v₀
      have hS'_card_add : S'.card + 1 = S.card := card_erase_add_one hv₀
      have hS'_lt : S'.card < S.card := by omega
      have hS'_ge2 : 2 ≤ S'.card := by omega
      obtain ⟨A₀, B₀, hAB_union, hAB_disj, hA₀_ne, hB₀_ne, hpure₀⟩ :=
        ih S'.card hS'_lt S' hS'_ge2 rfl
      rcases hpure₀ with hcomp₀ | hanti₀
      · have hJc : IsInducedSubgraphFree Jᶜ (pathGraph 4) :=
          (isInducedSubgraphFree_compl_pathGraph4 J).mpr hJ
        have hanti_c : IsAnticompletePair Jᶜ A₀ B₀ := by
          rw [isAnticompletePair_iff_isCompletePair_compl hAB_disj, compl_compl]
          exact hcomp₀
        obtain ⟨A, B, hAB_S, hAB_d, hA_ne, hB_ne, hpure_c⟩ :=
          extend_anticomplete_bipartition_of_p4_free Jᶜ hJc S A₀ B₀ v₀
            hv₀ hAB_union hAB_disj hA₀_ne hB₀_ne hanti_c
        refine ⟨A, B, hAB_S, hAB_d, hA_ne, hB_ne, ?_⟩
        rcases hpure_c with hcomp_c | hanti_c'
        · exact Or.inr ((isAnticompletePair_iff_isCompletePair_compl hAB_d).mpr hcomp_c)
        · rw [isAnticompletePair_iff_isCompletePair_compl hAB_d, compl_compl] at hanti_c'
          exact Or.inl hanti_c'
      · exact extend_anticomplete_bipartition_of_p4_free J hJ S A₀ B₀ v₀
          hv₀ hAB_union hAB_disj hA₀_ne hB₀_ne hanti₀

/--
Subset-level Seinsche product inequality: for every $P_4$-free graph $J$ and every nonempty
subset $S \subseteq V(J)$, there exist a clique $C \subseteq S$ in $J$ and an independent set
$I \subseteq S$ in $J$ (`Jᶜ.IsClique I`) such that $|S| \le |C| \cdot |I|$.
-/
theorem seinsche_exists_clique_and_indep_on {W : Type*} [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) (hJ : IsInducedSubgraphFree J (pathGraph 4))
    (S : Finset W) (hS : S.Nonempty) :
    ∃ C ⊆ S, ∃ I ⊆ S, J.IsClique (C : Set W) ∧ Jᶜ.IsClique (I : Set W) ∧
      S.card ≤ C.card * I.card := by
  classical
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    subst hn
    by_cases h1 : S.card ≤ 1
    · obtain ⟨v, hv⟩ := hS
      have hS_eq : S = {v} := eq_singleton_iff_unique_mem.mpr ⟨hv, fun u hu =>
        card_le_one.mp h1 u hu v hv⟩
      subst hS_eq
      refine ⟨{v}, Subset.rfl, {v}, Subset.rfl, by simp, by simp, by simp⟩
    · push_neg at h1
      obtain ⟨A, B, hAB_S, hAB_disj, hA_ne, hB_ne, hpure⟩ :=
        exists_pure_bipartition_of_p4_free J hJ S h1
      have hcard_sum : A.card + B.card = S.card := by
        rw [← hAB_S]
        exact card_union_of_disjoint hAB_disj |>.symm
      have hA_pos : 0 < A.card := card_pos.mpr hA_ne
      have hB_pos : 0 < B.card := card_pos.mpr hB_ne
      have hA_lt : A.card < S.card := by omega
      have hB_lt : B.card < S.card := by omega
      obtain ⟨CA, hCA_A, IA, hIA_A, hCA_cl, hIA_cl, hA_prod⟩ := ih A.card hA_lt A hA_ne rfl
      obtain ⟨CB, hCB_B, IB, hIB_B, hCB_cl, hIB_cl, hB_prod⟩ := ih B.card hB_lt B hB_ne rfl
      have hAS : A ⊆ S := hAB_S ▸ subset_union_left
      have hBS : B ⊆ S := hAB_S ▸ subset_union_right
      rcases hpure with hcomp | hanti
      · -- (A, B) is complete in J: CA ∪ CB is a clique in J
        let C := CA ∪ CB
        let I := if IA.card ≤ IB.card then IB else IA
        have hdisj_C : Disjoint CA CB := Disjoint.mono hCA_A hCB_B hAB_disj
        have hC_card : C.card = CA.card + CB.card := card_union_of_disjoint hdisj_C
        have hC_cl : J.IsClique (C : Set W) := by
          intro x hx y hy hxy
          simp only [C, coe_union, Set.mem_union] at hx hy
          rcases hx with hxA | hxB <;> rcases hy with hyA | hyB
          · exact hCA_cl hxA hyA hxy
          · exact hcomp x (hCA_A hxA) y (hCB_B hyB)
          · exact (hcomp y (hCA_A hyA) x (hCB_B hxB)).symm
          · exact hCB_cl hxB hyB hxy
        have hIS : I ⊆ S := by
          dsimp [I]; split_ifs <;> [exact hIB_B.trans hBS; exact hIA_A.trans hAS]
        have hI_cl : Jᶜ.IsClique (I : Set W) := by
          dsimp [I]; split_ifs <;> [exact hIB_cl; exact hIA_cl]
        have hIA_le : IA.card ≤ I.card := by dsimp [I]; split_ifs <;> omega
        have hIB_le : IB.card ≤ I.card := by dsimp [I]; split_ifs <;> omega
        refine ⟨C, union_subset (hCA_A.trans hAS) (hCB_B.trans hBS), I, hIS, hC_cl, hI_cl, ?_⟩
        rw [hC_card, Nat.add_mul]
        have h1' : CA.card * IA.card ≤ CA.card * I.card := Nat.mul_le_mul_left CA.card hIA_le
        have h2' : CB.card * IB.card ≤ CB.card * I.card := Nat.mul_le_mul_left CB.card hIB_le
        omega
      · -- (A, B) is anticomplete in J: IA ∪ IB is an independent set in J
        let C := if CA.card ≤ CB.card then CB else CA
        let I := IA ∪ IB
        have hdisj_I : Disjoint IA IB := Disjoint.mono hIA_A hIB_B hAB_disj
        have hI_card : I.card = IA.card + IB.card := card_union_of_disjoint hdisj_I
        have hI_cl : Jᶜ.IsClique (I : Set W) := by
          intro x hx y hy hxy
          simp only [I, coe_union, Set.mem_union] at hx hy
          rcases hx with hxA | hxB <;> rcases hy with hyA | hyB
          · exact hIA_cl hxA hyA hxy
          · exact ⟨hxy, hanti x (hIA_A hxA) y (hIB_B hyB)⟩
          · exact ⟨hxy, fun hadj => hanti y (hIA_A hyA) x (hIB_B hxB) hadj.symm⟩
          · exact hIB_cl hxB hyB hxy
        have hCS : C ⊆ S := by
          dsimp [C]; split_ifs <;> [exact hCB_B.trans hBS; exact hCA_A.trans hAS]
        have hC_cl : J.IsClique (C : Set W) := by
          dsimp [C]; split_ifs <;> [exact hCB_cl; exact hCA_cl]
        have hCA_le : CA.card ≤ C.card := by dsimp [C]; split_ifs <;> omega
        have hCB_le : CB.card ≤ C.card := by dsimp [C]; split_ifs <;> omega
        refine ⟨C, hCS, I, union_subset (hIA_A.trans hAS) (hIB_B.trans hBS), hC_cl, hI_cl, ?_⟩
        rw [hI_card, Nat.mul_add]
        have h1' : CA.card * IA.card ≤ C.card * IA.card := Nat.mul_le_mul_right IA.card hCA_le
        have h2' : CB.card * IB.card ≤ C.card * IB.card := Nat.mul_le_mul_right IB.card hCB_le
        omega

/--
**Seinsche's Theorem (`seinsche_cograph_clique_mul_indep`, Seinsche 1974, `main.tex` line 241)**:
Every $P_4$-free graph $J$ (cograph) on a nonempty finite vertex type $W$ satisfies
$|W| \le \omega(J) \cdot \alpha(J)$ (`Fintype.card W ≤ J.cliqueNum * J.indepNum`), proved from
first principles via `exists_pure_bipartition_of_p4_free` and `seinsche_exists_clique_and_indep_on`.
-/
theorem seinsche_cograph_clique_mul_indep {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (J : SimpleGraph W) (hJ : IsInducedSubgraphFree J (pathGraph 4)) :
    Fintype.card W ≤ J.cliqueNum * J.indepNum := by
  have huniv_ne : (Finset.univ : Finset W).Nonempty := Finset.univ_nonempty
  obtain ⟨C, _, I, _, hC_cl, hI_cl, hprod⟩ :=
    seinsche_exists_clique_and_indep_on J hJ Finset.univ huniv_ne
  rw [Finset.card_univ] at hprod
  have hC_le : C.card ≤ J.cliqueNum := hC_cl.card_le_cliqueNum
  have hI_le : I.card ≤ J.indepNum := by
    rw [← cliqueNum_compl]
    exact hI_cl.card_le_cliqueNum
  exact hprod.trans (Nat.mul_le_mul hC_le hI_le)

/--
Explicit subset extraction corollary of Seinsche's Theorem (`main.tex` lines 251, 258, 407):
If $J$ is a $P_4$-free graph on $W$ and $(r - 1)^2 < |W|$ (for example, when $|W| \ge \varepsilon^{-2}$
and $r = \lceil \varepsilon^{-1} \rceil$), then $J$ contains a vertex subset $R \subseteq V(J)$
of exact cardinality $|R| = r$ that is either a clique in $J$ or an independent set in $J$
(`Jᶜ.IsClique R`).
-/
theorem seinsche_exists_clique_or_indep_card_eq {W : Type*} [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) (hJ : IsInducedSubgraphFree J (pathGraph 4))
    (r : ℕ) (hr : 1 ≤ r) (hcard : (r - 1) ^ 2 < Fintype.card W) :
    ∃ R : Finset W, R.card = r ∧ (J.IsClique (R : Set W) ∨ Jᶜ.IsClique (R : Set W)) := by
  have hW_pos : 0 < Fintype.card W := lt_of_le_of_lt (Nat.zero_le _) hcard
  haveI : Nonempty W := Fintype.card_pos_iff.mp hW_pos
  obtain ⟨C, _, I, _, hC_cl, hI_cl, hprod⟩ :=
    seinsche_exists_clique_and_indep_on J hJ Finset.univ Finset.univ_nonempty
  rw [Finset.card_univ] at hprod
  have hor : r ≤ C.card ∨ r ≤ I.card := by
    by_contra hlt_both
    push_neg at hlt_both
    have hC_le : C.card ≤ r - 1 := by omega
    have hI_le : I.card ≤ r - 1 := by omega
    have hmul_le : C.card * I.card ≤ (r - 1) ^ 2 := by
      rw [sq]
      exact Nat.mul_le_mul hC_le hI_le
    omega
  rcases hor with hrC | hrI
  · obtain ⟨R, hRC, hR_card⟩ := exists_subset_card_eq hrC
    exact ⟨R, hR_card, Or.inl (hC_cl.subset (Finset.coe_subset.mpr hRC))⟩
  · obtain ⟨R, hRI, hR_card⟩ := exists_subset_card_eq hrI
    exact ⟨R, hR_card, Or.inr (hI_cl.subset (Finset.coe_subset.mpr hRI))⟩

/-!
## Section 4: Global-Decided-Pair Symmetric Layout Refinement (Lemma 5), Cograph Substitution
Closure (`cograph_subst`), and Defective Cograph Refinement (Lemma 4(2), `main.tex` lines 228–277)
-/

open Classical in
/--
Pairwise ordered wrong edge count between blocks $A_i$ and $A_j$ in a layout $(J, A)$:
$|E_{\overline{G}}(A_i, A_j)|$ when $ij \in E(J)$, and $|E_G(A_i, A_j)|$ when $ij \notin E(J)$.
-/
noncomputable def symmPairWrongCount {I : Type*}
    (G : SimpleGraph V) (J : SimpleGraph I) (A : I → Finset V) (i j : I) : ℕ :=
  if i ≠ j then
    if J.Adj i j then crossEdgeCount Gᶜ (A i) (A j)
    else crossEdgeCount G (A i) (A j)
  else 0

/--
Total number of ordered wrong pairs $2|Q(\mathcal{L})|$ in a symmetric layout $\mathcal{L} = (J, A)$.
-/
noncomputable def symmWrongEdgeCount {I : Type*} [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (J : SimpleGraph I) (A : I → Finset V) : ℕ :=
  ∑ i : I, ∑ j : I, symmPairWrongCount G J A i j

/--
A valid symmetric layout $\mathcal{L} = (J, A)$ inside $S \subseteq V(G)$ with parameters
$(\varepsilon, d, x_{\mathrm{def}})$ (Lemmas 4(2) & 5 of `main.tex`, lines 243–248 and 270),
satisfying:
- **(L1)** $|A_i| \ge \varepsilon^{2d} |S|$ for all $i \in I$;
- **(L2)** $\sum_{i \in I} |A_i|^{1/d} \ge |S|^{1/d}$; and
- **(L3)** $2|Q(\mathcal{L})| \le x_{\mathrm{def}} (|S|^2 - \sum_{i \in I} |A_i|^2) = x_{\mathrm{def}} \cdot 2|P(\mathcal{L})|$
  (`symmWrongEdgeCount G J A ≤ x_def * decidedBound S A`).
-/
structure IsSymmValidLayout {I : Type*} [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : Finset V) (ε d x_def : ℝ)
    (J : SimpleGraph I) (A : I → Finset V) : Prop where
  subset_ambient : ∀ i : I, A i ⊆ S
  nonempty_blocks : ∀ i : I, (A i).Nonempty
  pairwise_disjoint : ∀ i j : I, i ≠ j → Disjoint (A i) (A j)
  L1_width : ∀ i : I, ε ^ (2 * d) * (S.card : ℝ) ≤ ((A i).card : ℝ)
  L2_potential : (S.card : ℝ) ^ (1 / d) ≤ ∑ i : I, ((A i).card : ℝ) ^ (1 / d)
  L3_wrong : (symmWrongEdgeCount G J A : ℝ) ≤ x_def * decidedBound S A

/-- Transporting `IsSymmValidLayout` along a bijection $e : I_1 \simeq I_2$. -/
theorem IsSymmValidLayout.reindex {I₁ I₂ : Type*} [Fintype I₁] [DecidableEq I₁]
    [Fintype I₂] [DecidableEq I₂] (e : I₁ ≃ I₂)
    {G : SimpleGraph V} {S : Finset V} {ε d x_def : ℝ}
    {J : SimpleGraph I₂} {A : I₂ → Finset V}
    (h : IsSymmValidLayout G S ε d x_def J A) :
    IsSymmValidLayout G S ε d x_def (J.comap e) (A ∘ e) where
  subset_ambient i := h.subset_ambient (e i)
  nonempty_blocks i := h.nonempty_blocks (e i)
  pairwise_disjoint i j hij := h.pairwise_disjoint (e i) (e j) (e.injective.ne hij)
  L1_width i := h.L1_width (e i)
  L2_potential := by
    refine h.L2_potential.trans (le_of_eq ?_)
    exact (Equiv.sum_comp e (fun i => ((A i).card : ℝ) ^ (1 / d))).symm
  L3_wrong := by
    have hW : symmWrongEdgeCount G (J.comap e) (A ∘ e) = symmWrongEdgeCount G J A := by
      classical
      unfold symmWrongEdgeCount
      refine Fintype.sum_equiv e _ _ (fun i => Fintype.sum_equiv e _ _ (fun j => ?_))
      unfold symmPairWrongCount
      simp [Function.comp_apply, e.injective.ne_iff]
    have hD : decidedBound S (A ∘ e) = decidedBound S A := by
      unfold decidedBound
      simp only [Function.comp_apply]
      rw [Equiv.sum_comp e (fun i => ((A i).card : ℝ) ^ 2)]
    rw [hW, hD]
    exact h.L3_wrong

theorem symmPairWrongCount_le_symmWrongEdgeCount {I : Type*} [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (J : SimpleGraph I) (A : I → Finset V) (i₀ j₀ : I) :
    symmPairWrongCount G J A i₀ j₀ ≤ symmWrongEdgeCount G J A := by
  unfold symmWrongEdgeCount
  have h1 : symmPairWrongCount G J A i₀ j₀ ≤ ∑ j : I, symmPairWrongCount G J A i₀ j :=
    Finset.single_le_sum (f := fun j : I => symmPairWrongCount G J A i₀ j)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j₀)
  have h2 : (∑ j : I, symmPairWrongCount G J A i₀ j) ≤
      ∑ i : I, ∑ j : I, symmPairWrongCount G J A i j :=
    Finset.single_le_sum (f := fun i : I => ∑ j : I, symmPairWrongCount G J A i j)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i₀)
  exact h1.trans h2

/-- The trivial 1-block symmetric layout on `Fin 1` with $A_0 = S$. -/
theorem isSymmValidLayout_trivial (G : SimpleGraph V) {S : Finset V} (hS : S.Nonempty)
    {ε d x_def : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hd : 0 < d) :
    IsSymmValidLayout G S ε d x_def (⊥ : SimpleGraph (Fin 1)) (fun _ => S) where
  subset_ambient _ := Subset.rfl
  nonempty_blocks _ := hS
  pairwise_disjoint i j hij := False.elim (hij (Subsingleton.elim i j))
  L1_width _ := by
    have hpow : ε ^ (2 * d) ≤ 1 := Real.rpow_le_one hε.le hε1.le (by positivity)
    calc ε ^ (2 * d) * (S.card : ℝ)
        ≤ 1 * (S.card : ℝ) := mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _)
      _ = (S.card : ℝ) := one_mul _
  L2_potential := by simp
  L3_wrong := by
    unfold symmWrongEdgeCount symmPairWrongCount decidedBound
    simp

/--
Substituting a $(k, |A_{j_0}| / k^d)$-blockade $(B_1, \dots, B_k)$ with pattern graph $K$ inside
$A_{j_0}$ ($1 \le k < \lceil \varepsilon^{-1} \rceil$) preserves `IsSymmValidLayout` on
`{i : Fin m // i ≠ j₀} ⊕ Fin k`.
-/
theorem symm_layout_subst_step {m k : ℕ} {G : SimpleGraph V} {S : Finset V}
    {ε d x_def : ℝ} {J : SimpleGraph (Fin m)} {A : Fin m → Finset V}
    (hL : IsSymmValidLayout G S ε d x_def J A) (j₀ : Fin m)
    (hε : 0 < ε) (hd : 1 ≤ d) (hx : 0 ≤ x_def)
    (hk_pos : 1 ≤ k) (hk_lt : k < ⌈ε⁻¹⌉₊)
    (hAj₀ : ε ^ d * (S.card : ℝ) ≤ ((A j₀).card : ℝ))
    {K : SimpleGraph (Fin k)} {B : Fin k → Finset V}
    (hB_block : IsBlockadeIn G (A j₀) k (((A j₀).card : ℝ) / (k : ℝ) ^ d) B)
    (hB_pairs : ∀ p q : Fin k, p ≠ q →
      (symmPairWrongCount G K B p q : ℝ) ≤ x_def * ((B p).card : ℝ) * ((B q).card : ℝ)) :
    IsSymmValidLayout G S ε d x_def (substGraph J j₀ K)
      (Sum.elim (fun i : {i : Fin m // i ≠ j₀} => A i.1) B) where
  subset_ambient x := by
    cases x with
    | inl i => exact hL.subset_ambient i.1
    | inr p => exact (hB_block.subset_ambient p).trans (hL.subset_ambient j₀)
  nonempty_blocks x := by
    cases x with
    | inl i => exact hL.nonempty_blocks i.1
    | inr p => exact hB_block.nonempty_blocks p
  pairwise_disjoint x y hxy := by
    cases x with
    | inl i =>
      cases y with
      | inl j =>
        exact hL.pairwise_disjoint i.1 j.1 (fun heq => hxy (congrArg Sum.inl (Subtype.ext heq)))
      | inr q =>
        exact Disjoint.mono_right (hB_block.subset_ambient q) (hL.pairwise_disjoint i.1 j₀ i.2)
    | inr p =>
      cases y with
      | inl j =>
        exact Disjoint.mono_left (hB_block.subset_ambient p) (hL.pairwise_disjoint j₀ j.1 j.2.symm)
      | inr q =>
        exact hB_block.pairwise_disjoint p q (fun heq => hxy (congrArg Sum.inr heq))
  L1_width x := by
    cases x with
    | inl i => exact hL.L1_width i.1
    | inr p =>
      simp only [Sum.elim_inr]
      have hk_le_inv : (k : ℝ) ≤ ε⁻¹ := (Nat.lt_ceil.mp hk_lt).le
      have hk_pos_real : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos
      have hkd_pos : 0 < (k : ℝ) ^ d := Real.rpow_pos_of_pos hk_pos_real d
      have hεk_le : ε * (k : ℝ) ≤ 1 := by
        calc ε * (k : ℝ) ≤ ε * ε⁻¹ := mul_le_mul_of_nonneg_left hk_le_inv hε.le
          _ = 1 := mul_inv_cancel₀ hε.ne'
      have hεkd_le : ε ^ d * (k : ℝ) ^ d ≤ 1 := by
        rw [← Real.mul_rpow hε.le hk_pos_real.le]
        exact Real.rpow_le_one (by positivity) hεk_le (by linarith)
      have hstep : ε ^ (2 * d) * (S.card : ℝ) ≤ ((A j₀).card : ℝ) / (k : ℝ) ^ d := by
        rw [le_div_iff₀ hkd_pos]
        have h2d : ε ^ (2 * d) = ε ^ d * ε ^ d := by
          rw [← Real.rpow_add hε]
          ring_nf
        calc ε ^ (2 * d) * (S.card : ℝ) * (k : ℝ) ^ d
            = (ε ^ d * (k : ℝ) ^ d) * (ε ^ d * (S.card : ℝ)) := by rw [h2d]; ring
          _ ≤ 1 * ((A j₀).card : ℝ) :=
              mul_le_mul hεkd_le hAj₀ (by positivity) (by positivity)
          _ = ((A j₀).card : ℝ) := one_mul _
      exact hstep.trans (hB_block.width_ge p)
  L2_potential := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    have hk_pos_real : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos
    have hd_pos : 0 < d := by linarith
    have h1d_nonneg : 0 ≤ 1 / d := by positivity
    have hB_pot : ((A j₀).card : ℝ) ^ (1 / d) ≤ ∑ p : Fin k, ((B p).card : ℝ) ^ (1 / d) := by
      have hterm : ∀ p : Fin k,
          ((A j₀).card : ℝ) ^ (1 / d) / (k : ℝ) ≤ ((B p).card : ℝ) ^ (1 / d) := by
        intro p
        have h1 := Real.rpow_le_rpow (by positivity) (hB_block.width_ge p) h1d_nonneg
        have h2 : (((A j₀).card : ℝ) / (k : ℝ) ^ d) ^ (1 / d) =
            ((A j₀).card : ℝ) ^ (1 / d) / (k : ℝ) := by
          rw [Real.div_rpow (Nat.cast_nonneg _) (by positivity),
            ← Real.rpow_mul hk_pos_real.le, mul_one_div_cancel hd_pos.ne', Real.rpow_one]
        rwa [h2] at h1
      calc ((A j₀).card : ℝ) ^ (1 / d)
          = (k : ℝ) * (((A j₀).card : ℝ) ^ (1 / d) / (k : ℝ)) :=
            (mul_div_cancel₀ _ hk_pos_real.ne').symm
        _ = ∑ _p : Fin k, (((A j₀).card : ℝ) ^ (1 / d) / (k : ℝ)) := by
            simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ p : Fin k, ((B p).card : ℝ) ^ (1 / d) :=
            Finset.sum_le_sum (fun p _ => hterm p)
    have hdecomp := sum_fin_eq_add_sum_subtype_ne j₀ (fun i => ((A i).card : ℝ) ^ (1 / d))
    linarith [hL.L2_potential]
  L3_wrong := by
    classical
    let J' := substGraph J j₀ K
    let A' := Sum.elim (fun i : {i : Fin m // i ≠ j₀} => A i.1) B
    have hW_split : symmWrongEdgeCount G J' A' =
        (∑ i : {i : Fin m // i ≠ j₀}, ∑ j : {i : Fin m // i ≠ j₀},
          symmPairWrongCount G J A i.1 j.1) +
        (∑ i : {i : Fin m // i ≠ j₀}, ∑ p : Fin k,
          if J.Adj i.1 j₀ then crossEdgeCount Gᶜ (A i.1) (B p)
          else crossEdgeCount G (A i.1) (B p)) +
        (∑ p : Fin k, ∑ j : {i : Fin m // i ≠ j₀},
          if J.Adj j₀ j.1 then crossEdgeCount Gᶜ (B p) (A j.1)
          else crossEdgeCount G (B p) (A j.1)) +
        symmWrongEdgeCount G K B := by
      unfold symmWrongEdgeCount
      rw [Fintype.sum_sum_type]
      simp_rw [Fintype.sum_sum_type, Finset.sum_add_distrib]
      have h11 : (∑ x : {i : Fin m // i ≠ j₀}, ∑ y : {i : Fin m // i ≠ j₀},
          symmPairWrongCount G J' A' (Sum.inl x) (Sum.inl y)) =
          ∑ i : {i : Fin m // i ≠ j₀}, ∑ j : {i : Fin m // i ≠ j₀},
            symmPairWrongCount G J A i.1 j.1 := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        unfold symmPairWrongCount
        by_cases hij : i = j
        · subst hij
          simp
        · have hval : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
          simp [hij, hval, J', A', substGraph]
      have h12 : (∑ x : {i : Fin m // i ≠ j₀}, ∑ p : Fin k,
          symmPairWrongCount G J' A' (Sum.inl x) (Sum.inr p)) =
          ∑ i : {i : Fin m // i ≠ j₀}, ∑ p : Fin k,
            if J.Adj i.1 j₀ then crossEdgeCount Gᶜ (A i.1) (B p)
            else crossEdgeCount G (A i.1) (B p) := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun p _ => ?_))
        unfold symmPairWrongCount
        simp [J', A', substGraph]
      have h21 : (∑ p : Fin k, ∑ y : {i : Fin m // i ≠ j₀},
          symmPairWrongCount G J' A' (Sum.inr p) (Sum.inl y)) =
          ∑ p : Fin k, ∑ j : {i : Fin m // i ≠ j₀},
            if J.Adj j₀ j.1 then crossEdgeCount Gᶜ (B p) (A j.1)
            else crossEdgeCount G (B p) (A j.1) := by
        refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun j _ => ?_))
        unfold symmPairWrongCount
        simp [J', A', substGraph]
      have h22 : (∑ p : Fin k, ∑ q : Fin k,
          symmPairWrongCount G J' A' (Sum.inr p) (Sum.inr q)) =
          ∑ p : Fin k, ∑ q : Fin k, symmPairWrongCount G K B p q := by
        refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
        unfold symmPairWrongCount
        by_cases hpq : p = q <;> simp [hpq, J', A', substGraph]
      rw [h11, h12, h21, h22]
      omega
    have h12_le : (∑ i : {i : Fin m // i ≠ j₀}, ∑ p : Fin k,
        if J.Adj i.1 j₀ then crossEdgeCount Gᶜ (A i.1) (B p)
        else crossEdgeCount G (A i.1) (B p)) ≤
        ∑ i : {i : Fin m // i ≠ j₀}, symmPairWrongCount G J A i.1 j₀ := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      have hi : i.1 ≠ j₀ := i.2
      unfold symmPairWrongCount
      by_cases hadj : J.Adj i.1 j₀ <;> simp [hi, hadj]
      · exact sum_crossEdgeCount_right_le Gᶜ (A i.1) (A j₀) B
          hB_block.subset_ambient hB_block.pairwise_disjoint
      · exact sum_crossEdgeCount_right_le G (A i.1) (A j₀) B
          hB_block.subset_ambient hB_block.pairwise_disjoint
    have h21_le : (∑ p : Fin k, ∑ j : {i : Fin m // i ≠ j₀},
        if J.Adj j₀ j.1 then crossEdgeCount Gᶜ (B p) (A j.1)
        else crossEdgeCount G (B p) (A j.1)) ≤
        ∑ j : {i : Fin m // i ≠ j₀}, symmPairWrongCount G J A j₀ j.1 := by
      rw [Finset.sum_comm]
      refine Finset.sum_le_sum (fun j _ => ?_)
      have hj : j₀ ≠ j.1 := j.2.symm
      unfold symmPairWrongCount
      by_cases hadj : J.Adj j₀ j.1 <;> simp [hj, hadj]
      · exact sum_crossEdgeCount_left_le Gᶜ (A j.1) (A j₀) B
          hB_block.subset_ambient hB_block.pairwise_disjoint
      · exact sum_crossEdgeCount_left_le G (A j.1) (A j₀) B
          hB_block.subset_ambient hB_block.pairwise_disjoint
    have hW_old_eq : symmWrongEdgeCount G J A =
        (∑ i : {i : Fin m // i ≠ j₀}, ∑ j : {i : Fin m // i ≠ j₀},
          symmPairWrongCount G J A i.1 j.1) +
        (∑ i : {i : Fin m // i ≠ j₀}, symmPairWrongCount G J A i.1 j₀) +
        (∑ j : {i : Fin m // i ≠ j₀}, symmPairWrongCount G J A j₀ j.1) := by
      unfold symmWrongEdgeCount
      rw [sum_fin_eq_add_sum_subtype_ne j₀]
      rw [sum_fin_eq_add_sum_subtype_ne j₀ (fun j => symmPairWrongCount G J A j₀ j)]
      have h_inner : (∑ i : {i : Fin m // i ≠ j₀}, ∑ j : Fin m,
          symmPairWrongCount G J A i.1 j) =
          (∑ i : {i : Fin m // i ≠ j₀}, symmPairWrongCount G J A i.1 j₀) +
          (∑ i : {i : Fin m // i ≠ j₀}, ∑ j : {i : Fin m // i ≠ j₀},
            symmPairWrongCount G J A i.1 j.1) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        exact sum_fin_eq_add_sum_subtype_ne j₀ _
      rw [h_inner]
      have h_diag : symmPairWrongCount G J A j₀ j₀ = 0 := by simp [symmPairWrongCount]
      rw [h_diag, zero_add]
      ring
    have hW_nat : symmWrongEdgeCount G J' A' ≤
        symmWrongEdgeCount G J A + symmWrongEdgeCount G K B := by omega
    have hW_real : (symmWrongEdgeCount G J' A' : ℝ) ≤
        (symmWrongEdgeCount G J A : ℝ) + (symmWrongEdgeCount G K B : ℝ) := by
      exact_mod_cast hW_nat
    have h22_le : (symmWrongEdgeCount G K B : ℝ) ≤
        x_def * (((A j₀).card : ℝ) ^ 2 - ∑ p : Fin k, ((B p).card : ℝ) ^ 2) := by
      unfold symmWrongEdgeCount
      push_cast
      have hpointwise : (∑ p : Fin k, ∑ q : Fin k, (symmPairWrongCount G K B p q : ℝ)) ≤
          ∑ p : Fin k, ∑ q : Fin k,
            (if p ≠ q then x_def * ((B p).card : ℝ) * ((B q).card : ℝ) else 0) := by
        refine Finset.sum_le_sum (fun p _ => Finset.sum_le_sum (fun q _ => ?_))
        by_cases hpq : p = q
        · simp [hpq, symmPairWrongCount]
        · simp only [ne_eq, hpq, not_false_eq_true, ↓reduceIte]
          exact hB_pairs p q hpq
      have hfactor : (∑ p : Fin k, ∑ q : Fin k,
          (if p ≠ q then x_def * ((B p).card : ℝ) * ((B q).card : ℝ) else 0)) =
          x_def * (∑ p : Fin k, ∑ q : Fin k,
            if p ≠ q then ((B p).card : ℝ) * ((B q).card : ℝ) else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun q _ => ?_)
        by_cases hpq : p = q <;> simp [hpq, mul_assoc]
      have hoff := sum_offDiag_card_mul_le_sq_sub hB_block.subset_ambient hB_block.pairwise_disjoint
      calc (∑ p : Fin k, ∑ q : Fin k, (symmPairWrongCount G K B p q : ℝ))
          ≤ x_def * (∑ p : Fin k, ∑ q : Fin k,
              if p ≠ q then ((B p).card : ℝ) * ((B q).card : ℝ) else 0) := by
            rw [← hfactor]
            exact hpointwise
        _ ≤ x_def * (((A j₀).card : ℝ) ^ 2 - ∑ p : Fin k, ((B p).card : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hoff hx
    have hD_eq : decidedBound S A' =
        decidedBound S A + (((A j₀).card : ℝ) ^ 2 - ∑ p : Fin k, ((B p).card : ℝ) ^ 2) := by
      unfold decidedBound
      rw [Fintype.sum_sum_type, sum_fin_eq_add_sum_subtype_ne j₀ (fun i => ((A i).card : ℝ) ^ 2)]
      simp only [A', Sum.elim_inl, Sum.elim_inr]
      ring
    rw [hD_eq, mul_add]
    linarith [hL.L3_wrong]

open Classical in
/--
Canonical symmetric pattern graph of a weakly $x$-sparse-or-co-sparse blockade $B$:
$pq \in E(K)$ iff $p \neq q$ and $(B_p, B_q)$ is not weakly $x$-sparse in $G$.
-/
noncomputable def canonicalSymmPatternGraph (G : SimpleGraph V) {k : ℕ} (x : ℝ)
    (B : Fin k → Finset V) : SimpleGraph (Fin k) where
  Adj p q := p ≠ q ∧ ¬IsWeaklySparsePair G (B p) (B q) x
  symm p q := by
    rintro ⟨hne, hnot⟩
    refine ⟨hne.symm, fun hqp => hnot ?_⟩
    unfold IsWeaklySparsePair at hqp ⊢
    rw [crossEdgeCount_comm']
    calc (crossEdgeCount G (B q) (B p) : ℝ)
      _ ≤ x * ((B q).card : ℝ) * ((B p).card : ℝ) := hqp
      _ = x * ((B p).card : ℝ) * ((B q).card : ℝ) := by ring
  loopless p := fun h => h.1 rfl

theorem symmPairWrongCount_canonical_le {G : SimpleGraph V} {S : Finset V} {k : ℕ} {w x : ℝ}
    {B : Fin k → Finset V}
    (hB : IsWeaklySparseOrCoSparseBlockadeIn G S k w x B) {p q : Fin k} (hpq : p ≠ q) :
    (symmPairWrongCount G (canonicalSymmPatternGraph G x B) B p q : ℝ) ≤
      x * ((B p).card : ℝ) * ((B q).card : ℝ) := by
  classical
  unfold symmPairWrongCount canonicalSymmPatternGraph
  rw [if_pos hpq]
  dsimp only
  by_cases hsp : IsWeaklySparsePair G (B p) (B q) x
  · have hnadj : ¬(p ≠ q ∧ ¬IsWeaklySparsePair G (B p) (B q) x) := fun h => h.2 hsp
    rw [if_neg hnadj]
    exact hsp
  · have hadj : p ≠ q ∧ ¬IsWeaklySparsePair G (B p) (B q) x := ⟨hpq, hsp⟩
    rw [if_pos hadj]
    rcases hB.2 p q hpq with h1 | h2
    · exact (hsp h1).elim
    · exact h2

/--
Extracting a weakly $x_{\mathrm{sp}}$-sparse-or-co-sparse $(\lceil \varepsilon^{-1} \rceil, \lfloor \varepsilon^{(20 C_{\mathrm{cap}} + 4) d^2} |S| \rfloor)$-blockade
from a valid symmetric layout of length $m \ge \lceil \varepsilon^{-1} \rceil$ with
$x_{\mathrm{in}} = x_{\mathrm{sp}} \varepsilon^{4d}$ (Lemma 5 of `main.tex`, lines 270–274).
-/
theorem symmValidLayout_extract_blockade {m : ℕ} {G : SimpleGraph V} {S : Finset V}
    {ε d C_cap x_sp : ℝ} {J : SimpleGraph (Fin m)} {A : Fin m → Finset V}
    (hL : IsSymmValidLayout G S ε d (x_sp * ε ^ (4 * d)) J A)
    (hε : 0 < ε) (hε_half : ε < 1 / 2) (hd : 1 ≤ d) (hC_cap : 2 ≤ C_cap) (hx_sp : 0 ≤ x_sp)
    (hm : ⌈ε⁻¹⌉₊ ≤ m) :
    ∃ B : Fin ⌈ε⁻¹⌉₊ → Finset V,
      IsWeaklySparseOrCoSparseBlockadeIn G S ⌈ε⁻¹⌉₊
        (⌊ε ^ ((20 * C_cap + 4) * d ^ 2) * (S.card : ℝ)⌋₊ : ℝ) x_sp B := by
  have hε1 : ε < 1 := by linarith
  refine ⟨restrictBlockade hm A, ?_, ?_⟩
  · refine {
      subset_ambient := fun i => hL.subset_ambient (Fin.castLE hm i)
      nonempty_blocks := fun i => hL.nonempty_blocks (Fin.castLE hm i)
      pairwise_disjoint := fun i j hij =>
        hL.pairwise_disjoint _ _ (fun heq => hij ((Fin.castLE_injective hm) heq))
      width_ge := fun i => ?_
    }
    have hfloor : (⌊ε ^ ((20 * C_cap + 4) * d ^ 2) * (S.card : ℝ)⌋₊ : ℝ) ≤
        ε ^ ((20 * C_cap + 4) * d ^ 2) * (S.card : ℝ) :=
      Nat.floor_le (by positivity)
    have hexp_le : 2 * d ≤ (20 * C_cap + 4) * d ^ 2 := by nlinarith
    have hrpow : ε ^ ((20 * C_cap + 4) * d ^ 2) ≤ ε ^ (2 * d) :=
      Real.rpow_le_rpow_of_exponent_ge hε hε1.le hexp_le
    calc (⌊ε ^ ((20 * C_cap + 4) * d ^ 2) * (S.card : ℝ)⌋₊ : ℝ)
        ≤ ε ^ ((20 * C_cap + 4) * d ^ 2) * (S.card : ℝ) := hfloor
      _ ≤ ε ^ (2 * d) * (S.card : ℝ) := mul_le_mul_of_nonneg_right hrpow (Nat.cast_nonneg _)
      _ ≤ ((A (Fin.castLE hm i)).card : ℝ) := hL.L1_width (Fin.castLE hm i)
  · intro i j hij
    let i' : Fin m := Fin.castLE hm i
    let j' : Fin m := Fin.castLE hm j
    have hij' : i' ≠ j' := fun heq => hij ((Fin.castLE_injective hm) heq)
    have hpair_le : (symmPairWrongCount G J A i' j' : ℝ) ≤
        x_sp * ((A i').card : ℝ) * ((A j').card : ℝ) := by
      have h1 : (symmPairWrongCount G J A i' j' : ℝ) ≤ (symmWrongEdgeCount G J A : ℝ) := by
        exact_mod_cast symmPairWrongCount_le_symmWrongEdgeCount G J A i' j'
      have h2 := hL.L3_wrong
      have h3 := decidedBound_le_sq S A
      have hxin_pos : 0 ≤ x_sp * ε ^ (4 * d) := by positivity
      have hcross_sq : (symmPairWrongCount G J A i' j' : ℝ) ≤
          (x_sp * ε ^ (4 * d)) * (S.card : ℝ) ^ 2 := by
        linarith [mul_le_mul_of_nonneg_left h3 hxin_pos]
      have hAi : ε ^ (2 * d) * (S.card : ℝ) ≤ ((A i').card : ℝ) := hL.L1_width i'
      have hAj : ε ^ (2 * d) * (S.card : ℝ) ≤ ((A j').card : ℝ) := hL.L1_width j'
      have hprod : (ε ^ (2 * d) * (S.card : ℝ)) * (ε ^ (2 * d) * (S.card : ℝ)) ≤
          ((A i').card : ℝ) * ((A j').card : ℝ) :=
        mul_le_mul hAi hAj (by positivity) (by positivity)
      have h4d_eq : ε ^ (4 * d) * (S.card : ℝ) ^ 2 =
          (ε ^ (2 * d) * (S.card : ℝ)) * (ε ^ (2 * d) * (S.card : ℝ)) := by
        have : ε ^ (4 * d) = ε ^ (2 * d) * ε ^ (2 * d) := by
          rw [← Real.rpow_add hε]
          ring_nf
        rw [this]
        ring
      calc (symmPairWrongCount G J A i' j' : ℝ)
          ≤ (x_sp * ε ^ (4 * d)) * (S.card : ℝ) ^ 2 := hcross_sq
        _ = x_sp * (ε ^ (4 * d) * (S.card : ℝ) ^ 2) := by ring
        _ = x_sp * ((ε ^ (2 * d) * (S.card : ℝ)) * (ε ^ (2 * d) * (S.card : ℝ))) := by rw [h4d_eq]
        _ ≤ x_sp * (((A i').card : ℝ) * ((A j').card : ℝ)) :=
            mul_le_mul_of_nonneg_left hprod hx_sp
        _ = x_sp * ((A i').card : ℝ) * ((A j').card : ℝ) := by ring
    unfold symmPairWrongCount at hpair_le
    rw [if_pos hij'] at hpair_le
    unfold IsWeaklySparseOrCoSparsePair IsWeaklySparsePair restrictBlockade
    by_cases hadj : J.Adj i' j'
    · rw [if_pos hadj] at hpair_le
      exact Or.inr hpair_le
    · rw [if_neg hadj] at hpair_le
      exact Or.inl hpair_le

/--
Large-$k$ case ($k \ge \lceil \varepsilon^{-1} \rceil$) of Lemma 5 (`main.tex` line 276):
if $A_0 \subseteq S$ has $|A_0| \ge \varepsilon^d |S|$ and contains a weakly $x_{\mathrm{in}}$-sparse-or-co-sparse
$(k, |A_0| / k^d)$-blockade with $\lceil \varepsilon^{-1} \rceil \le k \le K_{\max} = \lceil \varepsilon^{-20 d C_{\mathrm{cap}}} \rceil$,
then restricting to the first $\lceil \varepsilon^{-1} \rceil$ blocks gives a weakly $x_{\mathrm{sp}}$-sparse-or-co-sparse
$(\lceil \varepsilon^{-1} \rceil, \lfloor \varepsilon^{(20 C_{\mathrm{cap}} + 4) d^2} |S| \rfloor)$-blockade in $S$.
-/
theorem symm_layout_refinement_case_large_k {G : SimpleGraph V} {S A₀ : Finset V}
    {ε d C_cap x_sp : ℝ} {k : ℕ} {B : Fin k → Finset V}
    (hA₀_sub : A₀ ⊆ S) (hA₀_card : ε ^ d * (S.card : ℝ) ≤ (A₀.card : ℝ))
    (hε : 0 < ε) (hε_half : ε < 1 / 2) (hd : 1 ≤ d) (hC_cap : 2 ≤ C_cap) (hx_sp : 0 ≤ x_sp)
    (hk_ge : ⌈ε⁻¹⌉₊ ≤ k) (hk_le : k ≤ ⌈ε ^ (-20 * d * C_cap)⌉₊)
    (hB : IsWeaklySparseOrCoSparseBlockadeIn G A₀ k ((A₀.card : ℝ) / (k : ℝ) ^ d)
      (x_sp * ε ^ (4 * d)) B) :
    ∃ B' : Fin ⌈ε⁻¹⌉₊ → Finset V,
      IsWeaklySparseOrCoSparseBlockadeIn G S ⌈ε⁻¹⌉₊
        (⌊ε ^ ((20 * C_cap + 4) * d ^ 2) * (S.card : ℝ)⌋₊ : ℝ) x_sp B' := by
  have hε1 : ε < 1 := by linarith
  have hk_pos : (0 : ℝ) < (k : ℝ) := by
    have : 0 < ⌈ε⁻¹⌉₊ := Nat.ceil_pos.mpr (inv_pos.mpr hε)
    exact_mod_cast this.trans_le hk_ge
  have hkd_pos : 0 < (k : ℝ) ^ d := Real.rpow_pos_of_pos hk_pos d
  have hε_inv_ge2 : (2 : ℝ) ≤ ε ^ (-1 : ℝ) := by
    have hε_inv2 : ε ≤ (2 : ℝ)⁻¹ := by linarith
    rw [Real.rpow_neg_one, ← inv_inv (2 : ℝ)]
    exact inv_anti₀ hε hε_inv2
  have hk_le_eps : (k : ℝ) ≤ ε ^ (-(20 * d * C_cap + 1)) := by
    have hceil_lt : (⌈ε ^ (-20 * d * C_cap)⌉₊ : ℝ) < ε ^ (-20 * d * C_cap) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have h1_le : (1 : ℝ) ≤ ε ^ (-20 * d * C_cap) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1.le (by nlinarith)
    have hk_real : (k : ℝ) ≤ (⌈ε ^ (-20 * d * C_cap)⌉₊ : ℝ) := by exact_mod_cast hk_le
    calc (k : ℝ)
        ≤ 2 * ε ^ (-20 * d * C_cap) := by linarith
      _ ≤ ε ^ (-1 : ℝ) * ε ^ (-20 * d * C_cap) :=
          mul_le_mul_of_nonneg_right hε_inv_ge2 (by positivity)
      _ = ε ^ (-(20 * d * C_cap + 1)) := by
          rw [← Real.rpow_add hε]
          congr 1; ring
  have hkd_le : (k : ℝ) ^ d ≤ (ε ^ ((20 * d * C_cap + 1) * d))⁻¹ := by
    calc (k : ℝ) ^ d
        ≤ (ε ^ (-(20 * d * C_cap + 1))) ^ d := Real.rpow_le_rpow hk_pos.le hk_le_eps (by linarith)
      _ = (ε ^ ((20 * d * C_cap + 1) * d))⁻¹ := by
          rw [← Real.rpow_mul hε.le, ← Real.rpow_neg hε.le]
          congr 1; ring
  have hwidth : (⌊ε ^ ((20 * C_cap + 4) * d ^ 2) * (S.card : ℝ)⌋₊ : ℝ) ≤
      (A₀.card : ℝ) / (k : ℝ) ^ d := by
    have hfloor : (⌊ε ^ ((20 * C_cap + 4) * d ^ 2) * (S.card : ℝ)⌋₊ : ℝ) ≤
        ε ^ ((20 * C_cap + 4) * d ^ 2) * (S.card : ℝ) :=
      Nat.floor_le (by positivity)
    have hexp : (20 * d * C_cap + 1) * d + d ≤ (20 * C_cap + 4) * d ^ 2 := by nlinarith
    have hrpow : ε ^ ((20 * C_cap + 4) * d ^ 2) ≤ ε ^ ((20 * d * C_cap + 1) * d + d) :=
      Real.rpow_le_rpow_of_exponent_ge hε hε1.le hexp
    have hmul_kd : ε ^ ((20 * d * C_cap + 1) * d) * (k : ℝ) ^ d ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hkd_le (by positivity : 0 ≤ ε ^ ((20 * d * C_cap + 1) * d))
      rwa [mul_inv_cancel₀ (by positivity)] at this
    have hdiv : ε ^ ((20 * d * C_cap + 1) * d + d) * (S.card : ℝ) ≤
        (A₀.card : ℝ) / (k : ℝ) ^ d := by
      rw [le_div_iff₀ hkd_pos, Real.rpow_add hε]
      calc (ε ^ ((20 * d * C_cap + 1) * d) * ε ^ d) * (S.card : ℝ) * (k : ℝ) ^ d
          = (ε ^ ((20 * d * C_cap + 1) * d) * (k : ℝ) ^ d) * (ε ^ d * (S.card : ℝ)) := by ring
        _ ≤ 1 * (A₀.card : ℝ) :=
            mul_le_mul hmul_kd hA₀_card (by positivity) (by positivity)
        _ = (A₀.card : ℝ) := one_mul _
    exact hfloor.trans ((mul_le_mul_of_nonneg_right hrpow (Nat.cast_nonneg _)).trans hdiv)
  refine ⟨restrictBlockade hk_ge B,
    ((hB.1.mono_ambient hA₀_sub).mono_width hwidth).restrict hk_ge, ?_⟩
  intro i j hij
  have hij' : Fin.castLE hk_ge i ≠ Fin.castLE hk_ge j :=
    fun heq => hij ((Fin.castLE_injective hk_ge) heq)
  have hxin_le_xsp : x_sp * ε ^ (4 * d) ≤ x_sp := by
    have hpow : ε ^ (4 * d) ≤ 1 := Real.rpow_le_one hε.le hε1.le (by positivity)
    calc x_sp * ε ^ (4 * d) ≤ x_sp * 1 := mul_le_mul_of_nonneg_left hpow hx_sp
      _ = x_sp := mul_one _
  rcases hB.2 (Fin.castLE hk_ge i) (Fin.castLE hk_ge j) hij' with hsp | hcosp
  · exact Or.inl (hsp.mono hxin_le_xsp)
  · exact Or.inr (hcosp.mono hxin_le_xsp)

/--
Inductive Symmetric Layout Refinement Loop (Lemma 5 of `main.tex`).
-/
theorem symm_layout_refinement_induction (G : SimpleGraph V) (S : Finset V)
    {ε d C_cap x_sp : ℝ}
    (hε : 0 < ε) (hε_half : ε < 1 / 2) (hd : 1 ≤ d) (hC_cap : 2 ≤ C_cap) (hx_sp : 0 ≤ x_sp)
    (hblockade : ∀ F ⊆ S, ε ^ d * (S.card : ℝ) ≤ (F.card : ℝ) →
      ∃ (k : ℕ) (B : Fin k → Finset V),
        2 ≤ k ∧ k ≤ ⌈ε ^ (-20 * d * C_cap)⌉₊ ∧
        IsWeaklySparseOrCoSparseBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ d)
          (x_sp * ε ^ (4 * d)) B) :
    ∀ (rem m : ℕ) (J : SimpleGraph (Fin m)) (A : Fin m → Finset V),
      1 ≤ m → ⌈ε⁻¹⌉₊ - m ≤ rem →
      IsSymmValidLayout G S ε d (x_sp * ε ^ (4 * d)) J A →
      ∃ B : Fin ⌈ε⁻¹⌉₊ → Finset V,
        IsWeaklySparseOrCoSparseBlockadeIn G S ⌈ε⁻¹⌉₊
          (⌊ε ^ ((20 * C_cap + 4) * d ^ 2) * (S.card : ℝ)⌋₊ : ℝ) x_sp B := by
  intro rem
  induction rem with
  | zero =>
    intro m J A _ hrem hL
    have hm : ⌈ε⁻¹⌉₊ ≤ m := Nat.sub_eq_zero_iff_le.mp (Nat.le_zero.mp hrem)
    exact symmValidLayout_extract_blockade hL hε hε_half hd hC_cap hx_sp hm
  | succ rem ih =>
    intro m J A hm_pos hrem hL
    by_cases hm_ge : ⌈ε⁻¹⌉₊ ≤ m
    · exact symmValidLayout_extract_blockade hL hε hε_half hd hC_cap hx_sp hm_ge
    · push_neg at hm_ge
      obtain ⟨j₀, hj₀_card⟩ := exists_block_card_ge_of_L2 hm_pos hm_ge hε hd hL.L2_potential
      obtain ⟨k, B, hk_two, hk_upper, hB⟩ :=
        hblockade (A j₀) (hL.subset_ambient j₀) hj₀_card
      by_cases hk_ge : ⌈ε⁻¹⌉₊ ≤ k
      · exact symm_layout_refinement_case_large_k (hL.subset_ambient j₀) hj₀_card
          hε hε_half hd hC_cap hx_sp hk_ge hk_upper hB
      · push_neg at hk_ge
        let K := canonicalSymmPatternGraph G (x_sp * ε ^ (4 * d)) B
        have hL_sum := symm_layout_subst_step hL j₀ hε hd (by positivity)
          (by omega) hk_ge hj₀_card hB.1
          (fun p q hpq => symmPairWrongCount_canonical_le hB hpq)
        let I' := {i : Fin m // i ≠ j₀} ⊕ Fin k
        let m' := Fintype.card I'
        have hm'_eq : m' = m - 1 + k := card_substIndex j₀
        have hL' : IsSymmValidLayout G S ε d (x_sp * ε ^ (4 * d))
            ((substGraph J j₀ K).comap (Fintype.equivFin I').symm)
            ((Sum.elim (fun i : {i : Fin m // i ≠ j₀} => A i.1) B) ∘ (Fintype.equivFin I').symm) :=
          hL_sum.reindex (Fintype.equivFin I').symm
        exact ih m' _ _ (by omega) (by omega) hL'

/--
**Lemma 5 (`symmetric_layout_refinement_xsp_indep`, Global-Decided-Pair Symmetric Layout Refinement,
`main.tex` lines 267–277)**:
Let $\varepsilon \in (0, 1/2)$, $d \ge 1$, $C_{\mathrm{cap}} \ge 2$,
$K_{\max} := \lceil \varepsilon^{-20 d C_{\mathrm{cap}}} \rceil$, $x_{\mathrm{sp}} \ge 0$, and
$x_{\mathrm{in}} := x_{\mathrm{sp}} \varepsilon^{4d}$. Let $S \subseteq V(G)$ be nonempty
(for instance $|S| \ge K_{\max}^{2d}$) such that every $F \subseteq S$ with $|F| \ge \varepsilon^d |S|$
contains a $(k, |F| / k^d)$-blockade ($k \in [2, K_{\max}]$) that is weakly $x_{\mathrm{in}}$-sparse-or-co-sparse
in $G$. Then $S$ contains an $(\lceil \varepsilon^{-1} \rceil, \lfloor \varepsilon^{(20 C_{\mathrm{cap}} + 4) d^2} |S| \rfloor)$-blockade
that is weakly $x_{\mathrm{sp}}$-sparse-or-co-sparse in $G$, whose output block width
$\lfloor \varepsilon^{(20 C_{\mathrm{cap}} + 4) d^2} |S| \rfloor$ depends **only on $\varepsilon$ (and $d, C_{\mathrm{cap}}, |S|$)
and is completely independent of $x_{\mathrm{sp}}$**.
-/
theorem symmetric_layout_refinement_xsp_indep (G : SimpleGraph V) (S : Finset V)
    {ε d C_cap x_sp : ℝ}
    (hε : 0 < ε) (hε_half : ε < 1 / 2) (hd : 1 ≤ d) (hC_cap : 2 ≤ C_cap) (hx_sp : 0 ≤ x_sp)
    (hS_ne : S.Nonempty)
    (hblockade : ∀ F ⊆ S, ε ^ d * (S.card : ℝ) ≤ (F.card : ℝ) →
      ∃ (k : ℕ) (B : Fin k → Finset V),
        2 ≤ k ∧ k ≤ ⌈ε ^ (-20 * d * C_cap)⌉₊ ∧
        IsWeaklySparseOrCoSparseBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ d)
          (x_sp * ε ^ (4 * d)) B) :
    ∃ B : Fin ⌈ε⁻¹⌉₊ → Finset V,
      IsWeaklySparseOrCoSparseBlockadeIn G S ⌈ε⁻¹⌉₊
        (⌊ε ^ ((20 * C_cap + 4) * d ^ 2) * (S.card : ℝ)⌋₊ : ℝ) x_sp B := by
  have hL₀ : IsSymmValidLayout G S ε d (x_sp * ε ^ (4 * d)) (⊥ : SimpleGraph (Fin 1)) (fun _ => S) :=
    isSymmValidLayout_trivial G hS_ne hε (by linarith) (by linarith)
  exact symm_layout_refinement_induction G S hε hε_half hd hC_cap hx_sp hblockade
    (⌈ε⁻¹⌉₊ - 1) 1 (⊥ : SimpleGraph (Fin 1)) (fun _ => S) le_rfl le_rfl hL₀

/-! ### Cograph ($P_4$-Free) Substitution Closure (`cograph_subst`) -/

/--
Finite check on `Finset (Fin 4)`: $P_4$ is prime — no subset $M \subseteq \text{Fin } 4$ of
cardinality $2$ or $3$ has uniform adjacency to $\text{Fin } 4 \setminus M$ in `pathGraph 4`.
-/
private theorem pathGraph4_no_module_two_or_three :
    ∀ M : Finset (Fin 4), 2 ≤ M.card → M.card ≤ 3 →
      ¬(∀ b : Fin 4, b ∉ M → ∀ a₁ ∈ M, ∀ a₂ ∈ M,
        (pathGraph 4).Adj b a₁ ↔ (pathGraph 4).Adj b a₂) := by
  decide

/--
**Cograph Substitution Closure (`cograph_subst`, `main.tex` line 253)**:
If $J$ and $K$ are $P_4$-free (`IsInducedSubgraphFree _ (pathGraph 4)`), then substituting $K$
for any vertex $j_0 \in V(J)$ produces a $P_4$-free graph `substGraph J j₀ K`.
-/
theorem cograph_subst {W₁ W₂ : Type*} [DecidableEq W₁]
    (J : SimpleGraph W₁) (j₀ : W₁) (K : SimpleGraph W₂)
    (hJ : IsInducedSubgraphFree J (pathGraph 4))
    (hK : IsInducedSubgraphFree K (pathGraph 4)) :
    IsInducedSubgraphFree (substGraph J j₀ K) (pathGraph 4) := by
  classical
  rintro ⟨g, hg⟩
  let M : Finset (Fin 4) := Finset.univ.filter (fun a : Fin 4 => (g a).isRight)
  have hM_le4 : M.card ≤ 4 := by
    calc M.card ≤ (Finset.univ : Finset (Fin 4)).card := card_filter_le _ _
      _ = 4 := by simp
  rcases (by omega : M.card = 0 ∨ M.card = 1 ∨ (2 ≤ M.card ∧ M.card ≤ 3) ∨ M.card = 4) with
    h0 | h1 | ⟨h2, h3⟩ | h4
  · -- M.card = 0: all vertices map into Sum.inl, embedding P_4 into J
    have hall_left : ∀ a : Fin 4, ∃ u : {v : W₁ // v ≠ j₀}, g a = Sum.inl u := by
      intro a
      have ha_not : a ∉ M := by rw [card_eq_zero.mp h0]; exact notMem_empty a
      simp only [M, mem_filter, mem_univ, true_and] at ha_not
      rcases hga : g a with u | x
      · exact ⟨u, rfl⟩
      · simp [hga] at ha_not
    let f : Fin 4 → W₁ := fun a => (Classical.choose (hall_left a)).1
    have hf_spec : ∀ a : Fin 4, g a = Sum.inl (Classical.choose (hall_left a)) :=
      fun a => Classical.choose_spec (hall_left a)
    have hf_inj : Function.Injective f := by
      intro a b hab
      apply g.injective
      rw [hf_spec a, hf_spec b]
      exact congrArg Sum.inl (Subtype.ext hab)
    apply hJ
    refine ⟨⟨f, hf_inj⟩, ?_⟩
    ext a b
    have hadj : (pathGraph 4).Adj a b ↔ (substGraph J j₀ K).Adj (g a) (g b) :=
      congr_arg (fun (H : SimpleGraph (Fin 4)) => H.Adj a b) hg |>.to_iff
    rw [comap_adj, Function.Embedding.coeFn_mk]
    rw [hf_spec a, hf_spec b] at hadj
    exact hadj
  · -- M.card = 1: one vertex maps into Sum.inr, sending it to j₀ embeds P_4 into J
    obtain ⟨a₀, ha₀_eq⟩ := card_eq_one.mp h1
    have hall_other : ∀ a : Fin 4, a ≠ a₀ → ∃ u : {v : W₁ // v ≠ j₀}, g a = Sum.inl u := by
      intro a ha
      have ha_not : a ∉ M := by rw [ha₀_eq, mem_singleton]; exact ha
      simp only [M, mem_filter, mem_univ, true_and] at ha_not
      rcases hga : g a with u | x
      · exact ⟨u, rfl⟩
      · simp [hga] at ha_not
    have ha₀_right : ∃ x₀ : W₂, g a₀ = Sum.inr x₀ := by
      have ha₀_mem : a₀ ∈ M := by rw [ha₀_eq]; exact mem_singleton_self a₀
      simp only [M, mem_filter, mem_univ, true_and] at ha₀_mem
      rcases hga₀ : g a₀ with u | x
      · simp [hga₀] at ha₀_mem
      · exact ⟨x, rfl⟩
    obtain ⟨x₀, hx₀_eq⟩ := ha₀_right
    let f : Fin 4 → W₁ := fun a =>
      if h : a = a₀ then j₀ else (Classical.choose (hall_other a h)).1
    have hf_inj : Function.Injective f := by
      intro a b hab
      dsimp [f] at hab
      by_cases ha : a = a₀ <;> by_cases hb : b = a₀
      · exact ha.trans hb.symm
      · rw [dif_pos ha, dif_neg hb] at hab
        exact ((Classical.choose (hall_other b hb)).2 hab.symm).elim
      · rw [dif_neg ha, dif_pos hb] at hab
        exact ((Classical.choose (hall_other a ha)).2 hab).elim
      · rw [dif_neg ha, dif_neg hb] at hab
        apply g.injective
        rw [Classical.choose_spec (hall_other a ha), Classical.choose_spec (hall_other b hb)]
        exact congrArg Sum.inl (Subtype.ext hab)
    apply hJ
    refine ⟨⟨f, hf_inj⟩, ?_⟩
    ext a b
    have hadj : (pathGraph 4).Adj a b ↔ (substGraph J j₀ K).Adj (g a) (g b) :=
      congr_arg (fun (H : SimpleGraph (Fin 4)) => H.Adj a b) hg |>.to_iff
    rw [comap_adj, Function.Embedding.coeFn_mk]
    by_cases ha : a = a₀ <;> by_cases hb : b = a₀
    · subst ha; subst hb
      simp
    · subst ha
      have hgb := Classical.choose_spec (hall_other b hb)
      rw [hx₀_eq, hgb] at hadj
      dsimp only [f]
      rw [dif_pos rfl, dif_neg hb]
      exact hadj
    · subst hb
      have hga := Classical.choose_spec (hall_other a ha)
      rw [hga, hx₀_eq] at hadj
      dsimp only [f]
      rw [dif_neg ha, dif_pos rfl]
      exact hadj
    · have hga := Classical.choose_spec (hall_other a ha)
      have hgb := Classical.choose_spec (hall_other b hb)
      rw [hga, hgb] at hadj
      dsimp only [f]
      rw [dif_neg ha, dif_neg hb]
      exact hadj
  · -- 2 ≤ M.card ≤ 3: M is a non-trivial proper module of P_4, impossible!
    refine pathGraph4_no_module_two_or_three M h2 h3 ?_
    intro b hb_not a₁ ha₁ a₂ ha₂
    have hb_left : ∃ u : {v : W₁ // v ≠ j₀}, g b = Sum.inl u := by
      simp only [M, mem_filter, mem_univ, true_and] at hb_not
      rcases hgb : g b with u | x
      · exact ⟨u, rfl⟩
      · simp [hgb] at hb_not
    have ha₁_right : ∃ x₁ : W₂, g a₁ = Sum.inr x₁ := by
      simp only [M, mem_filter, mem_univ, true_and] at ha₁
      rcases hga₁ : g a₁ with u | x
      · simp [hga₁] at ha₁
      · exact ⟨x, rfl⟩
    have ha₂_right : ∃ x₂ : W₂, g a₂ = Sum.inr x₂ := by
      simp only [M, mem_filter, mem_univ, true_and] at ha₂
      rcases hga₂ : g a₂ with u | x
      · simp [hga₂] at ha₂
      · exact ⟨x, rfl⟩
    obtain ⟨u, hgb⟩ := hb_left
    obtain ⟨x₁, hga₁⟩ := ha₁_right
    obtain ⟨x₂, hga₂⟩ := ha₂_right
    have hadj₁ := congr_arg (fun (H : SimpleGraph (Fin 4)) => H.Adj b a₁) hg
    have hadj₂ := congr_arg (fun (H : SimpleGraph (Fin 4)) => H.Adj b a₂) hg
    simp only [comap_adj, hgb, hga₁, hga₂, substGraph] at hadj₁ hadj₂
    rw [hadj₁, hadj₂]
  · -- M.card = 4: all vertices map into Sum.inr, embedding P_4 into K
    have hM_univ : M = Finset.univ :=
      eq_of_subset_of_card_le (subset_univ _) (by simp [h4])
    have hall_right : ∀ a : Fin 4, ∃ x : W₂, g a = Sum.inr x := by
      intro a
      have ha_mem : a ∈ M := by rw [hM_univ]; exact mem_univ a
      simp only [M, mem_filter, mem_univ, true_and] at ha_mem
      rcases hga : g a with u | x
      · simp [hga] at ha_mem
      · exact ⟨x, rfl⟩
    let f : Fin 4 → W₂ := fun a => Classical.choose (hall_right a)
    have hf_spec : ∀ a : Fin 4, g a = Sum.inr (f a) :=
      fun a => Classical.choose_spec (hall_right a)
    have hf_inj : Function.Injective f := by
      intro a b hab
      apply g.injective
      rw [hf_spec a, hf_spec b, hab]
    apply hK
    refine ⟨⟨f, hf_inj⟩, ?_⟩
    ext a b
    have hadj := congr_arg (fun (H : SimpleGraph (Fin 4)) => H.Adj a b) hg
    simpa [comap_adj, substGraph, hf_spec a, hf_spec b] using hadj

/-! ### Section 4B: Lemma 4(2) — Defective Cograph Refinement (`defective_cograph_refinement`) -/

/--
Transporting `IsInducedSubgraphFree _ (pathGraph 4)` along `comap` by an injection.
-/
theorem isInducedSubgraphFree_comap {W₁ W₂ W₃ : Type*} (J : SimpleGraph W₂) (H : SimpleGraph W₃)
    (f : W₁ ↪ W₂) (hJ : IsInducedSubgraphFree J H) :
    IsInducedSubgraphFree (J.comap f) H := by
  rintro ⟨g, hg⟩
  apply hJ
  refine ⟨g.trans f, ?_⟩
  ext u v
  have h := congr_arg (fun (K : SimpleGraph W₃) => K.Adj u v) hg
  simpa [comap_adj] using h

/--
Markov degree pruning on an equal-sized homogeneous family of $r = \lceil \varepsilon^{-1} \rceil$
blocks $X_i$ ($i \in R$) of size $w_0 \ge 1$ whose total ordered cross-edges in $H$ do not exceed
$\varepsilon^2 w_0^2$ (`main.tex` lines 251, 260–264):
pruning each $X_i$ to exact size $w' := \lceil \frac{1}{2} w_0 \rceil$ produces a $(2\varepsilon)$-sparse
subset $S \subseteq S_0$ in $H$ of exact cardinality $|S| = \lceil \varepsilon^{-1} \rceil w'$.
-/
theorem homogeneous_blockade_extract_sparse (H : SimpleGraph V) (S₀ : Finset V)
    {m : ℕ} (w₀ : ℕ) (ε : ℝ) (R : Finset (Fin m)) (X : Fin m → Finset V)
    (hε0 : 0 < ε) (hε8 : ε ≤ 1 / 8) (hw₀ : 1 ≤ w₀)
    (hR_card : R.card = ⌈ε⁻¹⌉₊)
    (hX_sub : ∀ i ∈ R, X i ⊆ S₀)
    (hX_card : ∀ i ∈ R, (X i).card = w₀)
    (hX_disj : ∀ i ∈ R, ∀ j ∈ R, i ≠ j → Disjoint (X i) (X j))
    (hwrong_sum : (∑ i ∈ R, ∑ j ∈ R.erase i, (crossEdgeCount H (X i) (X j) : ℝ)) ≤
      ε ^ 2 * (w₀ : ℝ) ^ 2) :
    ∃ S ⊆ S₀, IsEpsSparseOn H S (2 * ε) ∧
      S.card = ⌈ε⁻¹⌉₊ * ⌈(1 / 2 : ℝ) * (w₀ : ℝ)⌉₊ := by
  classical
  let r := ⌈ε⁻¹⌉₊
  let w' := ⌈(1 / 2 : ℝ) * (w₀ : ℝ)⌉₊
  have hr_ge_inv : ε⁻¹ ≤ (r : ℝ) := Nat.le_ceil _
  have h8_le_inv : (8 : ℝ) ≤ ε⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hε0]
    linarith
  have hr_ge8 : (8 : ℝ) ≤ (r : ℝ) := h8_le_inv.trans hr_ge_inv
  have hw₀_pos : (0 : ℝ) < (w₀ : ℝ) := by positivity
  have hw'_ge : (1 / 2 : ℝ) * (w₀ : ℝ) ≤ (w' : ℝ) := Nat.le_ceil _
  have hw'_pos : 1 ≤ w' := Nat.ceil_pos.mpr (by positivity)
  let U_other : Fin m → Finset V := fun i => (R.erase i).biUnion X
  let Bad : Fin m → Finset V := fun i =>
    (X i).filter (fun u => ε * (w₀ : ℝ) < ((neighborFinsetIn H u (U_other i)).card : ℝ))
  have hBad_card : ∀ i ∈ R, ((Bad i).card : ℝ) ≤ ε * (w₀ : ℝ) := by
    intro i hi
    have hU_cross : (crossEdgeCount H (X i) (U_other i) : ℝ) ≤
        ∑ j ∈ R.erase i, (crossEdgeCount H (X i) (X j) : ℝ) := by
      have hnat : crossEdgeCount H (X i) (U_other i) ≤
          ∑ j ∈ R.erase i, crossEdgeCount H (X i) (X j) := by
        unfold crossEdgeCount
        rw [Finset.sum_comm]
        refine Finset.sum_le_sum (fun u _ => ?_)
        have hsub_u : neighborFinsetIn H u (U_other i) ⊆
            (R.erase i).biUnion (fun j => neighborFinsetIn H u (X j)) := by
          intro v hv
          rw [mem_neighborFinsetIn'] at hv
          obtain ⟨hv_other, hadj⟩ := hv
          obtain ⟨j, hj_mem, hvXj⟩ := mem_biUnion.mp hv_other
          exact mem_biUnion.mpr ⟨j, hj_mem, (mem_neighborFinsetIn' H u v (X j)).mpr ⟨hvXj, hadj⟩⟩
        exact (card_le_card hsub_u).trans card_biUnion_le
      exact_mod_cast hnat
    have hi_le_tot : (∑ j ∈ R.erase i, (crossEdgeCount H (X i) (X j) : ℝ)) ≤
        ∑ i' ∈ R, ∑ j ∈ R.erase i', (crossEdgeCount H (X i') (X j) : ℝ) :=
      Finset.single_le_sum
        (f := fun i' => ∑ j ∈ R.erase i', (crossEdgeCount H (X i') (X j) : ℝ))
        (fun _ _ => sum_nonneg (fun _ _ => Nat.cast_nonneg _)) hi
    have hmarkov : ((Bad i).card : ℝ) * (ε * (w₀ : ℝ)) ≤
        (crossEdgeCount H (X i) (U_other i) : ℝ) := by
      calc ((Bad i).card : ℝ) * (ε * (w₀ : ℝ))
        _ = ∑ _u ∈ Bad i, ε * (w₀ : ℝ) := by rw [sum_const, nsmul_eq_mul]
        _ ≤ ∑ u ∈ Bad i, ((neighborFinsetIn H u (U_other i)).card : ℝ) :=
          sum_le_sum (fun u hu => (mem_filter.mp hu).2.le)
        _ ≤ ∑ u ∈ X i, ((neighborFinsetIn H u (U_other i)).card : ℝ) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.cast_nonneg _)
        _ = (crossEdgeCount H (X i) (U_other i) : ℝ) := by
          exact_mod_cast (crossEdgeCount_eq_sum_left H (X i) (U_other i)).symm
    have hprod : ((Bad i).card : ℝ) * (ε * (w₀ : ℝ)) ≤
        (ε * (w₀ : ℝ)) * (ε * (w₀ : ℝ)) := by
      calc ((Bad i).card : ℝ) * (ε * (w₀ : ℝ))
        _ ≤ ε ^ 2 * (w₀ : ℝ) ^ 2 :=
          hmarkov.trans (hU_cross.trans (hi_le_tot.trans hwrong_sum))
        _ = (ε * (w₀ : ℝ)) * (ε * (w₀ : ℝ)) := by ring
    exact le_of_mul_le_mul_right hprod (by positivity)
  have hw'_le_good : ∀ i ∈ R, w' ≤ (X i \ Bad i).card := by
    intro i hi
    have hBad_sub : Bad i ⊆ X i := filter_subset _ _
    have hcard_eq : ((X i \ Bad i).card : ℝ) + ((Bad i).card : ℝ) = (w₀ : ℝ) := by
      rw [← hX_card i hi]
      exact_mod_cast card_sdiff_add_card_eq_card hBad_sub
    have hBad_lt : ((Bad i).card : ℝ) ≤ (1 / 8 : ℝ) * (w₀ : ℝ) := by
      calc ((Bad i).card : ℝ)
        _ ≤ ε * (w₀ : ℝ) := hBad_card i hi
        _ ≤ (1 / 8 : ℝ) * (w₀ : ℝ) := mul_le_mul_of_nonneg_right hε8 (Nat.cast_nonneg _)
    have hgood_ge : (1 / 2 : ℝ) * (w₀ : ℝ) ≤ ((X i \ Bad i).card : ℝ) := by linarith
    exact Nat.ceil_le.mpr hgood_ge
  let B' : Fin m → Finset V := fun i =>
    if hi : i ∈ R then (exists_subset_card_eq (hw'_le_good i hi)).choose else ∅
  have hB'_sub : ∀ i ∈ R, B' i ⊆ X i \ Bad i := by
    intro i hi
    dsimp [B']
    rw [dif_pos hi]
    exact (exists_subset_card_eq (hw'_le_good i hi)).choose_spec.1
  have hB'_card : ∀ i ∈ R, (B' i).card = w' := by
    intro i hi
    dsimp [B']
    rw [dif_pos hi]
    exact (exists_subset_card_eq (hw'_le_good i hi)).choose_spec.2
  have hB'_disj : ∀ i ∈ R, ∀ j ∈ R, i ≠ j → Disjoint (B' i) (B' j) :=
    fun i hi j hj hij =>
      Disjoint.mono ((hB'_sub i hi).trans sdiff_subset) ((hB'_sub j hj).trans sdiff_subset)
        (hX_disj i hi j hj hij)
  let S := R.biUnion B'
  have hSS₀ : S ⊆ S₀ := by
    intro v hv
    obtain ⟨i, hi, hvB⟩ := mem_biUnion.mp hv
    exact hX_sub i hi (sdiff_subset (hB'_sub i hi hvB))
  have hS_card : S.card = r * w' := by
    dsimp [S]
    rw [card_biUnion hB'_disj]
    calc ∑ i ∈ R, (B' i).card
      _ = ∑ _i ∈ R, w' := sum_congr rfl hB'_card
      _ = R.card * w' := by rw [sum_const, smul_eq_mul]
      _ = r * w' := by rw [hR_card]
  have hS_card_real : (S.card : ℝ) = (r : ℝ) * (w' : ℝ) := by exact_mod_cast hS_card
  refine ⟨S, hSS₀, ?_, hS_card⟩
  intro u huS
  obtain ⟨i₀, hi₀, huB₀⟩ := mem_biUnion.mp huS
  have hu_not_Bad : u ∉ Bad i₀ := (mem_sdiff.mp (hB'_sub i₀ hi₀ huB₀)).2
  have hu_Xi₀ : u ∈ X i₀ := (mem_sdiff.mp (hB'_sub i₀ hi₀ huB₀)).1
  have hdeg_other : ((neighborFinsetIn H u (U_other i₀)).card : ℝ) ≤ ε * (w₀ : ℝ) := by
    by_contra hgt
    push_neg at hgt
    exact hu_not_Bad (mem_filter.mpr ⟨hu_Xi₀, hgt⟩)
  have hneigh_sub : neighborFinsetIn H u S ⊆ B' i₀ ∪ neighborFinsetIn H u (U_other i₀) := by
    intro v hv
    rw [mem_neighborFinsetIn'] at hv
    obtain ⟨hvS, hadj⟩ := hv
    obtain ⟨j, hjR, hvBj⟩ := mem_biUnion.mp hvS
    by_cases hji₀ : j = i₀
    · subst hji₀
      exact mem_union_left _ hvBj
    · refine mem_union_right _ ((mem_neighborFinsetIn' H u v (U_other i₀)).mpr ⟨?_, hadj⟩)
      exact mem_biUnion.mpr ⟨j, mem_erase.mpr ⟨hji₀, hjR⟩,
        sdiff_subset (hB'_sub j hjR hvBj)⟩
  have hdeg_nat : (neighborFinsetIn H u S).card ≤
      (B' i₀).card + (neighborFinsetIn H u (U_other i₀)).card :=
    (card_le_card hneigh_sub).trans (card_union_le _ _)
  have hdeg_real : ((neighborFinsetIn H u S).card : ℝ) ≤ (w' : ℝ) + ε * (w₀ : ℝ) := by
    have h1 : ((neighborFinsetIn H u S).card : ℝ) ≤
        ((B' i₀).card : ℝ) + ((neighborFinsetIn H u (U_other i₀)).card : ℝ) := by
      exact_mod_cast hdeg_nat
    rw [hB'_card i₀ hi₀] at h1
    linarith
  have hw₀_le_2w' : (w₀ : ℝ) ≤ 2 * (w' : ℝ) := by linarith
  have hw'_le_epsS : (w' : ℝ) ≤ ε * (S.card : ℝ) := by
    have h1 : 1 ≤ ε * (r : ℝ) := by
      calc (1 : ℝ) = ε * ε⁻¹ := (mul_inv_cancel₀ hε0.ne').symm
        _ ≤ ε * (r : ℝ) := mul_le_mul_of_nonneg_left hr_ge_inv hε0.le
    calc (w' : ℝ) = 1 * (w' : ℝ) := (one_mul _).symm
      _ ≤ (ε * (r : ℝ)) * (w' : ℝ) := mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)
      _ = ε * (S.card : ℝ) := by rw [hS_card_real]; ring
  have hεw₀_le_epsS : ε * (w₀ : ℝ) ≤ ε * (S.card : ℝ) := by
    calc ε * (w₀ : ℝ)
      _ ≤ ε * (2 * (w' : ℝ)) := mul_le_mul_of_nonneg_left hw₀_le_2w' hε0.le
      _ ≤ ε * ((r : ℝ) * (w' : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ hε0.le
          exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
      _ = ε * (S.card : ℝ) := by rw [hS_card_real]
  linarith

/--
**Seinsche Cograph Blockade-to-Restricted-Subgraph Extraction (`cograph_blockade_seinsche_extract_restricted`,
`main.tex` lines 251, 258–264, 407)**:
Given an equal-sized $(m, w_0)$-blockade $X$ in $S_0$ ($m \ge \lceil \varepsilon^{-2} \rceil$,
$w_0 \ge 1$, $\varepsilon \in (0, 1/8]$) with a $P_4$-free pattern graph $J$ on $\text{Fin } m$
such that for every clique or independent set $R \subseteq \text{Fin } m$ of size
$r = \lceil \varepsilon^{-1} \rceil$, the total ordered wrong pairs across $R$ is at most
$\varepsilon^2 w_0^2$, Seinsche's Theorem and `homogeneous_blockade_extract_sparse`
produce a $(2\varepsilon)$-restricted subset $S \subseteq S_0$ of size
$\lceil \varepsilon^{-1} \rceil \lceil \frac{1}{2} w_0 \rceil$.
-/
theorem cograph_blockade_seinsche_extract_restricted (G : SimpleGraph V) (S₀ : Finset V)
    {m : ℕ} (w₀ : ℕ) (ε : ℝ) (J : SimpleGraph (Fin m)) (X : Fin m → Finset V)
    (hε0 : 0 < ε) (hε8 : ε ≤ 1 / 8) (hw₀ : 1 ≤ w₀)
    (hm : ⌈ε ^ (-2 : ℝ)⌉₊ ≤ m)
    (hJ : IsInducedSubgraphFree J (pathGraph 4))
    (hX_sub : ∀ i : Fin m, X i ⊆ S₀)
    (hX_card : ∀ i : Fin m, (X i).card = w₀)
    (hX_disj : ∀ i j : Fin m, i ≠ j → Disjoint (X i) (X j))
    (hwrong : ∀ R : Finset (Fin m), R.card = ⌈ε⁻¹⌉₊ →
      (∑ i ∈ R, ∑ j ∈ R.erase i, (symmPairWrongCount G J X i j : ℝ)) ≤
        ε ^ 2 * (w₀ : ℝ) ^ 2) :
    ∃ S ⊆ S₀, IsEpsRestrictedOn G S (2 * ε) ∧
      S.card = ⌈ε⁻¹⌉₊ * ⌈(1 / 2 : ℝ) * (w₀ : ℝ)⌉₊ := by
  let r := ⌈ε⁻¹⌉₊
  have hr_pos : 1 ≤ r := Nat.ceil_pos.mpr (inv_pos.mpr hε0)
  have hcard_sq : (r - 1) ^ 2 < Fintype.card (Fin m) := by
    rw [Fintype.card_fin]
    have hr1_lt : ((r - 1 : ℕ) : ℝ) < ε⁻¹ := by
      have hcast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
        rw [Nat.cast_sub hr_pos, Nat.cast_one]
      rw [hcast]
      have hceil_lt := Nat.ceil_lt_add_one (inv_nonneg.mpr hε0.le)
      linarith
    have hsq_lt : (((r - 1) ^ 2 : ℕ) : ℝ) < ε ^ (-2 : ℝ) := by
      push_cast
      have hinv_sq : (ε⁻¹) ^ 2 = ε ^ (-2 : ℝ) := by
        rw [inv_pow, ← Real.rpow_natCast ε 2, ← Real.rpow_neg hε0.le]
        norm_num
      rw [← hinv_sq]
      exact pow_lt_pow_left₀ hr1_lt (Nat.cast_nonneg _) two_ne_zero
    have hm_ge : ε ^ (-2 : ℝ) ≤ (m : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hm)
    exact_mod_cast hsq_lt.trans_le hm_ge
  obtain ⟨R, hR_card, hR_hom⟩ := seinsche_exists_clique_or_indep_card_eq J hJ r hr_pos hcard_sq
  have hw_R := hwrong R hR_card
  rcases hR_hom with hcl | hind
  · -- R is a clique in J: symmPairWrongCount on R equals crossEdgeCount Gᶜ
    have hsum_eq : (∑ i ∈ R, ∑ j ∈ R.erase i, (crossEdgeCount Gᶜ (X i) (X j) : ℝ)) =
        ∑ i ∈ R, ∑ j ∈ R.erase i, (symmPairWrongCount G J X i j : ℝ) := by
      refine sum_congr rfl (fun i hi => sum_congr rfl (fun j hj => ?_))
      obtain ⟨hji, hjR⟩ := mem_erase.mp hj
      have hij : i ≠ j := hji.symm
      have hadj : J.Adj i j := hcl hi hjR hij
      unfold symmPairWrongCount
      rw [if_pos hij, if_pos hadj]
    rw [← hsum_eq] at hw_R
    obtain ⟨S, hSS₀, hS_sp, hS_card⟩ :=
      homogeneous_blockade_extract_sparse Gᶜ S₀ w₀ ε R X hε0 hε8 hw₀ hR_card
        (fun i _ => hX_sub i) (fun i _ => hX_card i) (fun i _ j _ hij => hX_disj i j hij) hw_R
    exact ⟨S, hSS₀, Or.inr hS_sp, hS_card⟩
  · -- R is an independent set in J: symmPairWrongCount on R equals crossEdgeCount G
    have hsum_eq : (∑ i ∈ R, ∑ j ∈ R.erase i, (crossEdgeCount G (X i) (X j) : ℝ)) =
        ∑ i ∈ R, ∑ j ∈ R.erase i, (symmPairWrongCount G J X i j : ℝ) := by
      refine sum_congr rfl (fun i hi => sum_congr rfl (fun j hj => ?_))
      obtain ⟨hji, hjR⟩ := mem_erase.mp hj
      have hij : i ≠ j := hji.symm
      have hnadj : ¬J.Adj i j := (hind hi hjR hij).2
      unfold symmPairWrongCount
      rw [if_pos hij, if_neg hnadj]
    rw [← hsum_eq] at hw_R
    obtain ⟨S, hSS₀, hS_sp, hS_card⟩ :=
      homogeneous_blockade_extract_sparse G S₀ w₀ ε R X hε0 hε8 hw₀ hR_card
        (fun i _ => hX_sub i) (fun i _ => hX_card i) (fun i _ j _ hij => hX_disj i j hij) hw_R
    exact ⟨S, hSS₀, Or.inl hS_sp, hS_card⟩

/--
**Outcome B of Lemma 4(2) (`cograph_blockade_outcome_B_extract`, `main.tex` line 251)**:
An equal-sized $(k, w_0)$-blockade ($k \ge \lceil \varepsilon^{-2} \rceil$, $w_0 \ge 1$) inside $F \subseteq S_0$
with a $P_4$-free pattern graph $K$ and pairwise defect at most $x_{\mathrm{B}} = \frac{1}{8} \varepsilon^4$
directly yields a $(2\varepsilon)$-restricted subset $S \subseteq S_0$ of size
$\lceil \varepsilon^{-1} \rceil \lceil \frac{1}{2} w_0 \rceil$.
-/
theorem cograph_blockade_outcome_B_extract (G : SimpleGraph V) (S₀ F : Finset V)
    {k : ℕ} (w₀ : ℕ) (ε : ℝ) (K : SimpleGraph (Fin k)) (B : Fin k → Finset V)
    (hFS₀ : F ⊆ S₀) (hε0 : 0 < ε) (hε8 : ε ≤ 1 / 8) (hw₀ : 1 ≤ w₀)
    (hk : ⌈ε ^ (-2 : ℝ)⌉₊ ≤ k)
    (hK : IsInducedSubgraphFree K (pathGraph 4))
    (hB_block : IsBlockadeIn G F k (w₀ : ℝ) B)
    (hB_card : ∀ i : Fin k, (B i).card = w₀)
    (hB_pairs : ∀ i j : Fin k, i ≠ j →
      (symmPairWrongCount G K B i j : ℝ) ≤
        ((1 / 8 : ℝ) * ε ^ 4) * ((B i).card : ℝ) * ((B j).card : ℝ)) :
    ∃ S ⊆ S₀, IsEpsRestrictedOn G S (2 * ε) ∧
      S.card = ⌈ε⁻¹⌉₊ * ⌈(1 / 2 : ℝ) * (w₀ : ℝ)⌉₊ := by
  refine cograph_blockade_seinsche_extract_restricted G S₀ w₀ ε K B hε0 hε8 hw₀ hk hK
    (fun i => (hB_block.subset_ambient i).trans hFS₀) hB_card hB_block.pairwise_disjoint ?_
  intro R hR_card
  have hterm : ∀ i ∈ R, ∀ j ∈ R.erase i,
      (symmPairWrongCount G K B i j : ℝ) ≤ ((1 / 8 : ℝ) * ε ^ 4) * (w₀ : ℝ) ^ 2 := by
    intro i _ j hj
    have hij : i ≠ j := (mem_erase.mp hj).1.symm
    have hp := hB_pairs i j hij
    rw [hB_card i, hB_card j] at hp
    linarith [sq (w₀ : ℝ)]
  have hsum1 : (∑ i ∈ R, ∑ j ∈ R.erase i, (symmPairWrongCount G K B i j : ℝ)) ≤
      (R.card : ℝ) * ((R.card : ℝ) - 1) * (((1 / 8 : ℝ) * ε ^ 4) * (w₀ : ℝ) ^ 2) := by
    calc ∑ i ∈ R, ∑ j ∈ R.erase i, (symmPairWrongCount G K B i j : ℝ)
      _ ≤ ∑ i ∈ R, ∑ _j ∈ R.erase i, (((1 / 8 : ℝ) * ε ^ 4) * (w₀ : ℝ) ^ 2) :=
        sum_le_sum (fun i hi => sum_le_sum (fun j hj => hterm i hi j hj))
      _ = ∑ i ∈ R, ((R.erase i).card : ℝ) * (((1 / 8 : ℝ) * ε ^ 4) * (w₀ : ℝ) ^ 2) := by
        refine sum_congr rfl (fun i _ => ?_)
        rw [sum_const, nsmul_eq_mul]
      _ = (R.card : ℝ) * ((R.card : ℝ) - 1) * (((1 / 8 : ℝ) * ε ^ 4) * (w₀ : ℝ) ^ 2) := by
        have h_erase : ∀ i ∈ R, ((R.erase i).card : ℝ) = (R.card : ℝ) - 1 := by
          intro i hi
          have hadd := card_erase_add_one hi
          have hcast : ((R.erase i).card : ℝ) + 1 = (R.card : ℝ) := by exact_mod_cast hadd
          linarith
        calc ∑ i ∈ R, ((R.erase i).card : ℝ) * (((1 / 8 : ℝ) * ε ^ 4) * (w₀ : ℝ) ^ 2)
          _ = ∑ _i ∈ R, ((R.card : ℝ) - 1) * (((1 / 8 : ℝ) * ε ^ 4) * (w₀ : ℝ) ^ 2) :=
            sum_congr rfl (fun i hi => by rw [h_erase i hi])
          _ = (R.card : ℝ) * ((R.card : ℝ) - 1) * (((1 / 8 : ℝ) * ε ^ 4) * (w₀ : ℝ) ^ 2) := by
            rw [sum_const, nsmul_eq_mul]
            ring
  rw [hR_card] at hsum1
  have hr_lt : (⌈ε⁻¹⌉₊ : ℝ) < ε⁻¹ + 1 := Nat.ceil_lt_add_one (inv_nonneg.mpr hε0.le)
  have h1_le_inv : (1 : ℝ) ≤ ε⁻¹ := by
    rw [le_inv_comm₀ zero_lt_one hε0]
    linarith
  have hr_le_2inv : (⌈ε⁻¹⌉₊ : ℝ) ≤ 2 * ε⁻¹ := by linarith
  have hr1_le_inv : (⌈ε⁻¹⌉₊ : ℝ) - 1 ≤ ε⁻¹ := by linarith
  have hr_pos : 0 ≤ (⌈ε⁻¹⌉₊ : ℝ) - 1 := by
    have : 1 ≤ ⌈ε⁻¹⌉₊ := Nat.ceil_pos.mpr (inv_pos.mpr hε0)
    have hcast : (1 : ℝ) ≤ (⌈ε⁻¹⌉₊ : ℝ) := by exact_mod_cast this
    linarith
  have hprod_r : (⌈ε⁻¹⌉₊ : ℝ) * ((⌈ε⁻¹⌉₊ : ℝ) - 1) ≤ 2 * (ε⁻¹) ^ 2 := by
    calc (⌈ε⁻¹⌉₊ : ℝ) * ((⌈ε⁻¹⌉₊ : ℝ) - 1)
      _ ≤ (2 * ε⁻¹) * ε⁻¹ := mul_le_mul hr_le_2inv hr1_le_inv hr_pos (by positivity)
      _ = 2 * (ε⁻¹) ^ 2 := by ring
  have hprod_eps : (2 * (ε⁻¹) ^ 2) * ((1 / 8 : ℝ) * ε ^ 4) = (1 / 4 : ℝ) * ε ^ 2 := by
    have hne : ε ≠ 0 := hε0.ne'
    field_simp
    ring
  calc (∑ i ∈ R, ∑ j ∈ R.erase i, (symmPairWrongCount G K B i j : ℝ))
    _ ≤ (⌈ε⁻¹⌉₊ : ℝ) * ((⌈ε⁻¹⌉₊ : ℝ) - 1) * (((1 / 8 : ℝ) * ε ^ 4) * (w₀ : ℝ) ^ 2) := hsum1
    _ ≤ (2 * (ε⁻¹) ^ 2) * (((1 / 8 : ℝ) * ε ^ 4) * (w₀ : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hprod_r (by positivity)
    _ = ((2 * (ε⁻¹) ^ 2) * ((1 / 8 : ℝ) * ε ^ 4)) * (w₀ : ℝ) ^ 2 := by ring
    _ = (1 / 4 : ℝ) * ε ^ 2 * (w₀ : ℝ) ^ 2 := by rw [hprod_eps]
    _ ≤ ε ^ 2 * (w₀ : ℝ) ^ 2 := by nlinarith

/--
Sub-sampling any symmetric layout $(J, A)$ (where $|A_i| \ge w_0 \ge 1$ and
`symmWrongEdgeCount G J A ≤ ε ^ 2 * w₀ ^ 2`) to equal-sized subsets $X_i \subseteq A_i$
of cardinality $w_0$ preserves the wrong-edge bound and extracts a $(2\varepsilon)$-restricted
subset $S \subseteq S_0$ via `cograph_blockade_seinsche_extract_restricted`.
-/
theorem cograph_layout_sub_sample_extract_restricted {m : ℕ} (G : SimpleGraph V) (S₀ : Finset V)
    (w₀ : ℕ) (ε : ℝ) (J : SimpleGraph (Fin m)) (A : Fin m → Finset V)
    (hε0 : 0 < ε) (hε8 : ε ≤ 1 / 8) (hw₀ : 1 ≤ w₀)
    (hm : ⌈ε ^ (-2 : ℝ)⌉₊ ≤ m)
    (hJ : IsInducedSubgraphFree J (pathGraph 4))
    (hA_sub : ∀ i : Fin m, A i ⊆ S₀)
    (hA_disj : ∀ i j : Fin m, i ≠ j → Disjoint (A i) (A j))
    (hA_width : ∀ i : Fin m, w₀ ≤ (A i).card)
    (hW_bound : (symmWrongEdgeCount G J A : ℝ) ≤ ε ^ 2 * (w₀ : ℝ) ^ 2) :
    ∃ S ⊆ S₀, IsEpsRestrictedOn G S (2 * ε) ∧
      S.card = ⌈ε⁻¹⌉₊ * ⌈(1 / 2 : ℝ) * (w₀ : ℝ)⌉₊ := by
  classical
  let X : Fin m → Finset V := fun i => (exists_subset_card_eq (hA_width i)).choose
  have hX_sub_A : ∀ i : Fin m, X i ⊆ A i :=
    fun i => (exists_subset_card_eq (hA_width i)).choose_spec.1
  have hX_card : ∀ i : Fin m, (X i).card = w₀ :=
    fun i => (exists_subset_card_eq (hA_width i)).choose_spec.2
  have hX_disj : ∀ i j : Fin m, i ≠ j → Disjoint (X i) (X j) :=
    fun i j hij => Disjoint.mono (hX_sub_A i) (hX_sub_A j) (hA_disj i j hij)
  have hpair_mono : ∀ i j : Fin m,
      symmPairWrongCount G J X i j ≤ symmPairWrongCount G J A i j := by
    intro i j
    unfold symmPairWrongCount
    by_cases hij : i = j
    · simp [hij]
    · rw [if_pos hij, if_pos hij]
      have hcross_mono : ∀ H : SimpleGraph V,
          crossEdgeCount H (X i) (X j) ≤ crossEdgeCount H (A i) (A j) := by
        intro H
        unfold crossEdgeCount
        refine (sum_le_sum_of_subset (hX_sub_A i)).trans ?_
        exact sum_le_sum (fun u _ => card_le_card (neighborFinsetIn_mono' H u (hX_sub_A j)))
      by_cases hadj : J.Adj i j
      · rw [if_pos hadj, if_pos hadj]
        exact hcross_mono Gᶜ
      · rw [if_neg hadj, if_neg hadj]
        exact hcross_mono G
  refine cograph_blockade_seinsche_extract_restricted G S₀ w₀ ε J X hε0 hε8 hw₀ hm hJ
    (fun i => (hX_sub_A i).trans (hA_sub i)) hX_card hX_disj ?_
  intro R _
  have hsum_nat : (∑ i ∈ R, ∑ j ∈ R.erase i, symmPairWrongCount G J X i j) ≤
      symmWrongEdgeCount G J A := by
    unfold symmWrongEdgeCount
    calc ∑ i ∈ R, ∑ j ∈ R.erase i, symmPairWrongCount G J X i j
      _ ≤ ∑ i ∈ R, ∑ j ∈ R.erase i, symmPairWrongCount G J A i j :=
        sum_le_sum (fun i _ => sum_le_sum (fun j _ => hpair_mono i j))
      _ ≤ ∑ i ∈ R, ∑ j : Fin m, symmPairWrongCount G J A i j :=
        sum_le_sum (fun i _ => sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _))
      _ ≤ ∑ i : Fin m, ∑ j : Fin m, symmPairWrongCount G J A i j :=
        sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
  exact (by exact_mod_cast hsum_nat :
    (∑ i ∈ R, ∑ j ∈ R.erase i, (symmPairWrongCount G J X i j : ℝ)) ≤
      (symmWrongEdgeCount G J A : ℝ)).trans hW_bound

/--
Inductive Defective Cograph Refinement Loop for Lemma 4(2) (`main.tex` lines 248–264).
-/
theorem defective_cograph_refinement_induction (G : SimpleGraph V) (S₀ : Finset V)
    {C ε x_def : ℝ}
    (hC : 1 ≤ C) (hε0 : 0 < ε) (hε8 : ε ≤ 1 / 8)
    (hx_def0 : 0 ≤ x_def) (hx_def_le : x_def ≤ ε ^ (12 * C))
    (hS₀_card : 4 * ε ^ (-(5 * C)) ≤ (S₀.card : ℝ))
    (hdichotomy : ∀ F ⊆ S₀, (1 / 2 : ℝ) * ε ^ (2 * C) * (S₀.card : ℝ) ≤ (F.card : ℝ) →
      -- Outcome R
      (∃ S ⊆ F, IsEpsRestrictedOn G S (2 * ε) ∧ ε ^ (5 * C) * (S₀.card : ℝ) ≤ (S.card : ℝ)) ∨
      -- Outcome B (at k ≥ ⌈ε ^ (-2 : ℝ)⌉₊ and w₀ ≥ ε ^ (5 * C) * |S₀|)
      (∃ (k w₀ : ℕ) (K : SimpleGraph (Fin k)) (B : Fin k → Finset V),
        ⌈ε ^ (-2 : ℝ)⌉₊ ≤ k ∧ 1 ≤ w₀ ∧
        ε ^ (5 * C) * (S₀.card : ℝ) ≤ (w₀ : ℝ) ∧
        IsInducedSubgraphFree K (pathGraph 4) ∧
        IsBlockadeIn G F k (w₀ : ℝ) B ∧
        (∀ i : Fin k, (B i).card = w₀) ∧
        (∀ i j : Fin k, i ≠ j →
          (symmPairWrongCount G K B i j : ℝ) ≤
            ((1 / 8 : ℝ) * ε ^ 4) * ((B i).card : ℝ) * ((B j).card : ℝ))) ∨
      -- Outcome A (low-arity 2 ≤ k < ⌈ε ^ (-2 : ℝ)⌉₊)
      (∃ (k : ℕ) (K : SimpleGraph (Fin k)) (B : Fin k → Finset V),
        2 ≤ k ∧ k < ⌈ε ^ (-2 : ℝ)⌉₊ ∧
        IsInducedSubgraphFree K (pathGraph 4) ∧
        IsBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ C) B ∧
        (∀ p q : Fin k, p ≠ q →
          (symmPairWrongCount G K B p q : ℝ) ≤ x_def * ((B p).card : ℝ) * ((B q).card : ℝ)))) :
    ∀ (rem m : ℕ) (J : SimpleGraph (Fin m)) (A : Fin m → Finset V),
      1 ≤ m → ⌈(ε ^ 2)⁻¹⌉₊ - m ≤ rem →
      IsInducedSubgraphFree J (pathGraph 4) →
      IsSymmValidLayout G S₀ (ε ^ 2) C x_def J A →
      ∃ S ⊆ S₀, IsEpsRestrictedOn G S (2 * ε) ∧ ε ^ (5 * C) * (S₀.card : ℝ) ≤ (S.card : ℝ) := by
  have hε2_pos : 0 < ε ^ 2 := sq_pos_of_pos hε0
  have hε1 : ε < 1 := by linarith
  have hε2_inv_eq : (ε ^ 2)⁻¹ = ε ^ (-2 : ℝ) := by
    rw [← Real.rpow_natCast ε 2, ← Real.rpow_neg hε0.le]
    norm_num
  have hceil_eq : ⌈(ε ^ 2)⁻¹⌉₊ = ⌈ε ^ (-2 : ℝ)⌉₊ := by rw [hε2_inv_eq]
  have h8_le_inv : (8 : ℝ) ≤ ε⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hε0]
    linarith
  have hr_ge8 : (8 : ℝ) ≤ (⌈ε⁻¹⌉₊ : ℝ) := h8_le_inv.trans (Nat.le_ceil _)
  have h_size_from_w₀ : ∀ {w₀ : ℕ}, ε ^ (5 * C) * (S₀.card : ℝ) ≤ (w₀ : ℝ) →
      ε ^ (5 * C) * (S₀.card : ℝ) ≤
        ((⌈ε⁻¹⌉₊ * ⌈(1 / 2 : ℝ) * (w₀ : ℝ)⌉₊ : ℕ) : ℝ) := by
    intro w₀ hw₀_ge
    push_cast
    have hw'_ge : (1 / 2 : ℝ) * (w₀ : ℝ) ≤ (⌈(1 / 2 : ℝ) * (w₀ : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
    calc ε ^ (5 * C) * (S₀.card : ℝ)
      _ ≤ (w₀ : ℝ) := hw₀_ge
      _ ≤ (8 : ℝ) * ((1 / 2 : ℝ) * (w₀ : ℝ)) := by linarith
      _ ≤ (⌈ε⁻¹⌉₊ : ℝ) * (⌈(1 / 2 : ℝ) * (w₀ : ℝ)⌉₊ : ℝ) :=
        mul_le_mul hr_ge8 hw'_ge (by positivity) (by positivity)
  -- Terminal extraction helper when m ≥ ⌈(ε ^ 2)⁻¹⌉₊
  have h_extract : ∀ (m : ℕ) (J : SimpleGraph (Fin m)) (A : Fin m → Finset V),
      ⌈(ε ^ 2)⁻¹⌉₊ ≤ m →
      IsInducedSubgraphFree J (pathGraph 4) →
      IsSymmValidLayout G S₀ (ε ^ 2) C x_def J A →
      ∃ S ⊆ S₀, IsEpsRestrictedOn G S (2 * ε) ∧ ε ^ (5 * C) * (S₀.card : ℝ) ≤ (S.card : ℝ) := by
    intro m J A hm hJ hL
    have hm' : ⌈ε ^ (-2 : ℝ)⌉₊ ≤ m := hceil_eq ▸ hm
    let w₀ : ℕ := ⌈ε ^ (5 * C) * (S₀.card : ℝ)⌉₊
    have hw₀_ge_real : ε ^ (5 * C) * (S₀.card : ℝ) ≤ (w₀ : ℝ) := Nat.le_ceil _
    have h4_le_w₀ : (4 : ℝ) ≤ ε ^ (5 * C) * (S₀.card : ℝ) := by
      have h1 : ε ^ (5 * C) * (4 * ε ^ (-(5 * C))) = 4 := by
        calc ε ^ (5 * C) * (4 * ε ^ (-(5 * C)))
          _ = 4 * (ε ^ (5 * C) * ε ^ (-(5 * C))) := by ring
          _ = 4 * 1 := by rw [← Real.rpow_add hε0]; simp
          _ = 4 := mul_one 4
      calc (4 : ℝ) = ε ^ (5 * C) * (4 * ε ^ (-(5 * C))) := h1.symm
        _ ≤ ε ^ (5 * C) * (S₀.card : ℝ) := mul_le_mul_of_nonneg_left hS₀_card (by positivity)
    have hw₀_pos : 1 ≤ w₀ := Nat.ceil_pos.mpr (by linarith)
    have hA_width : ∀ i : Fin m, w₀ ≤ (A i).card := by
      intro i
      have hAi : (ε ^ 2) ^ (2 * C) * (S₀.card : ℝ) ≤ ((A i).card : ℝ) := hL.L1_width i
      have h4C_eq : (ε ^ 2) ^ (2 * C) = ε ^ (4 * C) := by
        rw [← Real.rpow_natCast ε 2, ← Real.rpow_mul hε0.le]
        congr 1; ring
      rw [h4C_eq] at hAi
      have hw₀_lt : (w₀ : ℝ) < ε ^ (5 * C) * (S₀.card : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
      have h5C_4C : ε ^ (5 * C) + ε ^ (5 * C) ≤ ε ^ (4 * C) := by
        have hεC_le : 2 * ε ^ C ≤ 1 := by
          have : ε ^ C ≤ ε ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le hC
          rw [Real.rpow_one] at this
          linarith
        calc ε ^ (5 * C) + ε ^ (5 * C)
          _ = (2 * ε ^ C) * ε ^ (4 * C) := by
            have : ε ^ (5 * C) = ε ^ C * ε ^ (4 * C) := by
              rw [← Real.rpow_add hε0]; congr 1; ring
            rw [this]; ring
          _ ≤ 1 * ε ^ (4 * C) := mul_le_mul_of_nonneg_right hεC_le (by positivity)
          _ = ε ^ (4 * C) := one_mul _
      have hw₀_le_Ai : (w₀ : ℝ) ≤ ((A i).card : ℝ) := by nlinarith
      exact_mod_cast hw₀_le_Ai
    have hW_bound : (symmWrongEdgeCount G J A : ℝ) ≤ ε ^ 2 * (w₀ : ℝ) ^ 2 := by
      have h1 := hL.L3_wrong
      have h2 := decidedBound_le_sq S₀ A
      have h3 : (symmWrongEdgeCount G J A : ℝ) ≤ ε ^ (12 * C) * (S₀.card : ℝ) ^ 2 := by
        calc (symmWrongEdgeCount G J A : ℝ)
          _ ≤ x_def * decidedBound S₀ A := h1
          _ ≤ x_def * (S₀.card : ℝ) ^ 2 := mul_le_mul_of_nonneg_left h2 hx_def0
          _ ≤ ε ^ (12 * C) * (S₀.card : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hx_def_le (sq_nonneg _)
      have h12C_eq : ε ^ (12 * C) * (S₀.card : ℝ) ^ 2 =
          ε ^ (2 * C) * (ε ^ (5 * C) * (S₀.card : ℝ)) ^ 2 := by
        have : ε ^ (12 * C) = ε ^ (2 * C) * (ε ^ (5 * C)) ^ 2 := by
          rw [sq, ← Real.rpow_add hε0, ← Real.rpow_add hε0]
          congr 1; ring
        rw [this]
        ring
      have h2C_le : ε ^ (2 * C) ≤ ε ^ 2 := by
        have : ε ^ (2 * C) ≤ ε ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (by linarith)
        rwa [Real.rpow_two] at this
      have hw₀_sq : (ε ^ (5 * C) * (S₀.card : ℝ)) ^ 2 ≤ (w₀ : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hw₀_ge_real 2
      calc (symmWrongEdgeCount G J A : ℝ)
        _ ≤ ε ^ (12 * C) * (S₀.card : ℝ) ^ 2 := h3
        _ = ε ^ (2 * C) * (ε ^ (5 * C) * (S₀.card : ℝ)) ^ 2 := h12C_eq
        _ ≤ ε ^ 2 * (w₀ : ℝ) ^ 2 := mul_le_mul h2C_le hw₀_sq (by positivity) (by positivity)
    obtain ⟨S, hSS₀, hS_rest, hS_card⟩ :=
      cograph_layout_sub_sample_extract_restricted G S₀ w₀ ε J A hε0 hε8 hw₀_pos hm' hJ
        hL.subset_ambient hL.pairwise_disjoint hA_width hW_bound
    exact ⟨S, hSS₀, hS_rest, hS_card ▸ h_size_from_w₀ hw₀_ge_real⟩
  intro rem
  induction rem with
  | zero =>
    intro m J A _ hrem hJ hL
    have hm : ⌈(ε ^ 2)⁻¹⌉₊ ≤ m := Nat.sub_eq_zero_iff_le.mp (Nat.le_zero.mp hrem)
    exact h_extract m J A hm hJ hL
  | succ rem ih =>
    intro m J A hm_pos hrem hJ hL
    by_cases hm_ge : ⌈(ε ^ 2)⁻¹⌉₊ ≤ m
    · exact h_extract m J A hm_ge hJ hL
    · push_neg at hm_ge
      obtain ⟨j₀, hj₀_card⟩ := exists_block_card_ge_of_L2 hm_pos hm_ge hε2_pos hC hL.L2_potential
      have h2C_eq : (ε ^ 2) ^ C = ε ^ (2 * C) := by
        rw [← Real.rpow_natCast ε 2, ← Real.rpow_mul hε0.le]
        push_cast; rfl
      rw [h2C_eq] at hj₀_card
      have hj₀_half : (1 / 2 : ℝ) * ε ^ (2 * C) * (S₀.card : ℝ) ≤ ((A j₀).card : ℝ) := by
        nlinarith [show (0 : ℝ) ≤ ε ^ (2 * C) * (S₀.card : ℝ) by positivity]
      rcases hdichotomy (A j₀) (hL.subset_ambient j₀) hj₀_half with
        ⟨S, hSA, hS_rest, hS_card⟩ |
        ⟨k, w₀, K, B, hk_ge, hw₀_pos, hw₀_ge, hK, hB_block, hB_card, hB_pairs⟩ |
        ⟨k, K, B, hk_two, hk_lt, hK, hB_block, hB_pairs⟩
      · exact ⟨S, hSA.trans (hL.subset_ambient j₀), hS_rest, hS_card⟩
      · obtain ⟨S, hSS₀, hS_rest, hS_card⟩ :=
          cograph_blockade_outcome_B_extract G S₀ (A j₀) w₀ ε K B
            (hL.subset_ambient j₀) hε0 hε8 hw₀_pos hk_ge hK hB_block hB_card hB_pairs
        exact ⟨S, hSS₀, hS_rest, hS_card ▸ h_size_from_w₀ hw₀_ge⟩
      · have hk_lt' : k < ⌈(ε ^ 2)⁻¹⌉₊ := hceil_eq.symm ▸ hk_lt
        have hj₀_card' : (ε ^ 2) ^ C * (S₀.card : ℝ) ≤ ((A j₀).card : ℝ) := by
          rwa [h2C_eq]
        have hL_sum := symm_layout_subst_step hL j₀ hε2_pos hC hx_def0
          (by omega) hk_lt' hj₀_card' hB_block hB_pairs
        let I' := {i : Fin m // i ≠ j₀} ⊕ Fin k
        let m' := Fintype.card I'
        have hm'_eq : m' = m - 1 + k := card_substIndex j₀
        let e := (Fintype.equivFin I').symm
        have hJ_sum : IsInducedSubgraphFree (substGraph J j₀ K) (pathGraph 4) :=
          cograph_subst J j₀ K hJ hK
        have hJ' : IsInducedSubgraphFree ((substGraph J j₀ K).comap e) (pathGraph 4) :=
          isInducedSubgraphFree_comap (substGraph J j₀ K) (pathGraph 4) e.toEmbedding hJ_sum
        have hL' : IsSymmValidLayout G S₀ (ε ^ 2) C x_def
            ((substGraph J j₀ K).comap e)
            ((Sum.elim (fun i : {i : Fin m // i ≠ j₀} => A i.1) B) ∘ e) :=
          hL_sum.reindex e
        exact ih m' _ _ (by omega) (by omega) hJ' hL'

/--
**Lemma 4(2) (`defective_cograph_refinement`, `main.tex` lines 228–264)**:
Let $C \ge 1$, $\varepsilon \in (0, 1/8]$, and $x_{\mathrm{def}} \in [0, \varepsilon^{12 C}]$.
Let $S_0 \subseteq V(G)$ with $|S_0| \ge 4 \varepsilon^{-5C}$ such that every induced subgraph
$F \subseteq S_0$ with $|F| \ge \frac{1}{2} \varepsilon^{2C} |S_0|$ satisfies at least one of:
- **(Outcome R)** $F$ contains a $(2\varepsilon)$-restricted subset of order $\ge \varepsilon^{5C}|S_0|$;
- **(Outcome B — High-Arity Direct Seinsche Extraction at $C$-Independent Defect $x_{\mathrm{B}} = \frac{1}{8}\varepsilon^4$)**
  $F$ contains an equal-sized $(k, w_0)$-blockade ($k \ge \lceil \varepsilon^{-2} \rceil$,
  $w_0 \ge \varepsilon^{5C}|S_0|$) with a $P_4$-free pattern graph $K$ and pairwise defect
  `symmPairWrongCount G K B i j ≤ (1/8) ε^4 |B_i| |B_j|`; or
- **(Outcome A — Low-Arity Global-Decided-Pair Layout Refinement)** $F$ contains a
  $(k, |F| / k^C)$-blockade ($2 \le k < \lceil \varepsilon^{-2} \rceil$) with a $P_4$-free pattern
  graph $K$ and pairwise defect `symmPairWrongCount G K B p q ≤ x_def |B_p| |B_q|` (including
  $x_{\mathrm{def}} = 0$ for $100\%$ pairwise-pure cograph blockades in Lemma 7(2)).
Then $S_0$ contains a $(2\varepsilon)$-restricted subset $S \subseteq S_0$ of order at least
$\varepsilon^{5C} |S_0|$.
-/
theorem defective_cograph_refinement (G : SimpleGraph V) (S₀ : Finset V)
    {C ε x_def : ℝ}
    (hC : 1 ≤ C) (hε0 : 0 < ε) (hε8 : ε ≤ 1 / 8)
    (hx_def0 : 0 ≤ x_def) (hx_def_le : x_def ≤ ε ^ (12 * C))
    (hS₀_card : 4 * ε ^ (-(5 * C)) ≤ (S₀.card : ℝ))
    (hdichotomy : ∀ F ⊆ S₀, (1 / 2 : ℝ) * ε ^ (2 * C) * (S₀.card : ℝ) ≤ (F.card : ℝ) →
      (∃ S ⊆ F, IsEpsRestrictedOn G S (2 * ε) ∧ ε ^ (5 * C) * (S₀.card : ℝ) ≤ (S.card : ℝ)) ∨
      (∃ (k w₀ : ℕ) (K : SimpleGraph (Fin k)) (B : Fin k → Finset V),
        ⌈ε ^ (-2 : ℝ)⌉₊ ≤ k ∧ 1 ≤ w₀ ∧
        ε ^ (5 * C) * (S₀.card : ℝ) ≤ (w₀ : ℝ) ∧
        IsInducedSubgraphFree K (pathGraph 4) ∧
        IsBlockadeIn G F k (w₀ : ℝ) B ∧
        (∀ i : Fin k, (B i).card = w₀) ∧
        (∀ i j : Fin k, i ≠ j →
          (symmPairWrongCount G K B i j : ℝ) ≤
            ((1 / 8 : ℝ) * ε ^ 4) * ((B i).card : ℝ) * ((B j).card : ℝ))) ∨
      (∃ (k : ℕ) (K : SimpleGraph (Fin k)) (B : Fin k → Finset V),
        2 ≤ k ∧ k < ⌈ε ^ (-2 : ℝ)⌉₊ ∧
        IsInducedSubgraphFree K (pathGraph 4) ∧
        IsBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ C) B ∧
        (∀ p q : Fin k, p ≠ q →
          (symmPairWrongCount G K B p q : ℝ) ≤ x_def * ((B p).card : ℝ) * ((B q).card : ℝ)))) :
    ∃ S ⊆ S₀, IsEpsRestrictedOn G S (2 * ε) ∧ ε ^ (5 * C) * (S₀.card : ℝ) ≤ (S.card : ℝ) := by
  have hS₀_pos : 0 < (S₀.card : ℝ) := lt_of_lt_of_le (by positivity) hS₀_card
  have hS₀_ne : S₀.Nonempty := card_pos.mp (by exact_mod_cast hS₀_pos)
  have hε2_pos : 0 < ε ^ 2 := sq_pos_of_pos hε0
  have hε2_lt1 : ε ^ 2 < 1 := by nlinarith
  have hL₀ : IsSymmValidLayout G S₀ (ε ^ 2) C x_def (⊥ : SimpleGraph (Fin 1)) (fun _ => S₀) :=
    isSymmValidLayout_trivial G hS₀_ne hε2_pos hε2_lt1 (by linarith)
  have hJ₀ : IsInducedSubgraphFree (⊥ : SimpleGraph (Fin 1)) (pathGraph 4) := by
    rintro ⟨g, _⟩
    have hcard := Fintype.card_le_of_injective g g.injective
    simp at hcard
  exact defective_cograph_refinement_induction G S₀ hC hε0 hε8 hx_def0 hx_def_le hS₀_card
    hdichotomy (⌈(ε ^ 2)⁻¹⌉₊ - 1) 1 (⊥ : SimpleGraph (Fin 1)) (fun _ => S₀) le_rfl le_rfl hJ₀ hL₀

/-!
## Section 5: Qualitative Rödl Theorem (Theorem 2), Viral Leaf-Extension Cores, and
Deduction of Coupled Generalized Niceness (Lemma 7(1), `main.tex` lines 135–142 and 288–331)
-/

/-! ### Section 5A: Qualitative Rödl Theorem for Arbitrary Finite Graphs (`rodl_theorem_general`) -/

private theorem exists_disjoint_subsets_card_eq' (S : Finset V) (m₀ : ℕ) :
    ∀ k : ℕ, k * m₀ ≤ S.card →
      ∃ T : Fin k → Finset V,
        (∀ i, T i ⊆ S) ∧
        (∀ i j, i ≠ j → Disjoint (T i) (T j)) ∧
        (∀ i, (T i).card = m₀) := by
  intro k
  induction k generalizing S with
  | zero =>
    intro _
    exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ k ih =>
    intro hk
    have hm₀ : m₀ ≤ S.card := by
      have : 1 * m₀ ≤ (k + 1) * m₀ := Nat.mul_le_mul_right m₀ (by omega)
      omega
    obtain ⟨A, hAS, hA_card⟩ := exists_subset_card_eq hm₀
    have hS_sdiff : k * m₀ ≤ (S \ A).card := by
      have hsum := card_sdiff_add_card_eq_card hAS
      have h1 : (k + 1) * m₀ = k * m₀ + m₀ := by ring
      omega
    obtain ⟨T', hT'S, hT'_disj, hT'_card⟩ := ih (S \ A) hS_sdiff
    have hdisj_AT' : ∀ j : Fin k, Disjoint A (T' j) :=
      fun j => Disjoint.mono_right (hT'S j) disjoint_sdiff_self_right
    refine ⟨Fin.cons A T', ?_, ?_, ?_⟩
    · intro i
      exact Fin.cases hAS (fun j => Subset.trans (hT'S j) sdiff_subset) i
    · intro i j
      refine Fin.cases ?_ ?_ i <;> refine Fin.cases ?_ ?_ j
      · intro hij; exact (hij rfl).elim
      · intro j' _; simp only [Fin.cons_zero, Fin.cons_succ]; exact hdisj_AT' j'
      · intro i' _; simp only [Fin.cons_zero, Fin.cons_succ]; exact (hdisj_AT' i').symm
      · intro j' i' hij
        simp only [Fin.cons_succ]
        exact hT'_disj i' j' (fun h => hij (congrArg Fin.succ h))
    · intro i
      exact Fin.cases hA_card hT'_card i

private theorem induced_fin_free_sparse_or_cosparse_pair (G : SimpleGraph V)
    {h₀ : ℕ} (hh₀ : 2 ≤ h₀) (H : SimpleGraph (Fin h₀)) (hG : IsInducedSubgraphFree G H)
    (S : Finset V) (x₀ : ℝ) (hx₀0 : 0 < x₀) (hx₀1 : x₀ ≤ 1)
    (hS_card : 2 * max h₀ 4 ≤ S.card) :
    let h := max h₀ 4
    ∃ L ⊆ S, ∃ R ⊆ S, Disjoint L R ∧
      (x₀ / (2 * (h : ℝ))) ^ h * (S.card : ℝ) ≤ (L.card : ℝ) ∧
      (x₀ / (2 * (h : ℝ))) ^ h * (S.card : ℝ) ≤ (R.card : ℝ) ∧
      (IsXSparseTo G L R x₀ ∨ IsXSparseTo Gᶜ L R x₀) := by
  classical
  let h := max h₀ 4
  have hh_ge4 : 4 ≤ h := le_max_right h₀ 4
  have hh_ge_h₀ : h₀ ≤ h := le_max_left h₀ 4
  by_contra hno_pair
  let m₀ : ℕ := S.card / h₀
  have hm₀_mul : h₀ * m₀ ≤ S.card := Nat.mul_div_le S.card h₀
  have hm₀_ge : (S.card : ℝ) / (2 * (h : ℝ)) ≤ (m₀ : ℝ) := by
    have hdiv_mod := Nat.div_add_mod S.card h₀
    have hmod_lt : S.card % h₀ < h₀ := Nat.mod_lt S.card (by omega)
    have hS_ge_2h₀ : 2 * h₀ ≤ S.card := (Nat.mul_le_mul_left 2 hh_ge_h₀).trans hS_card
    have hm₀_pos : 1 ≤ m₀ := by
      have : h₀ ≤ S.card := by omega
      exact Nat.div_pos this (by omega)
    have hnat : S.card ≤ 2 * h * m₀ := by
      calc S.card = h₀ * m₀ + S.card % h₀ := hdiv_mod.symm
        _ ≤ h₀ * m₀ + h₀ * m₀ := Nat.add_le_add_left (le_trans (le_of_lt hmod_lt)
            (Nat.le_mul_of_pos_right h₀ hm₀_pos)) _
        _ = 2 * h₀ * m₀ := by ring
        _ ≤ 2 * h * m₀ := Nat.mul_le_mul_right m₀ (Nat.mul_le_mul_left 2 hh_ge_h₀)
    have hreal : (S.card : ℝ) ≤ 2 * (h : ℝ) * (m₀ : ℝ) := by exact_mod_cast hnat
    rw [div_le_iff₀ (by positivity)]
    linarith
  obtain ⟨T, hTS, hT_disj, hT_card⟩ := exists_disjoint_subsets_card_eq' S m₀ h₀ hm₀_mul
  let w₁ : ℝ := (x₀ / (2 * (h : ℝ))) ^ h * (S.card : ℝ)
  have hS_pos : (0 : ℝ) < (S.card : ℝ) := by
    have : 0 < S.card := by omega
    exact_mod_cast this
  have hw₁_pos : 0 < w₁ := by dsimp [w₁]; positivity
  have hh₀_w₁_le : (h₀ : ℝ) * w₁ ≤ x₀ ^ (h - 1) * (m₀ : ℝ) := by
    have hh_pos_nat : 1 ≤ h := by omega
    have hh_pow_eq : (x₀ / (2 * (h : ℝ))) ^ h =
        (1 / (2 * (h : ℝ)) ^ (h - 1)) * x₀ * x₀ ^ (h - 1) * (1 / (2 * (h : ℝ))) := by
      have h_sub : h = (h - 1) + 1 := (Nat.sub_add_cancel hh_pos_nat).symm
      have h_x : x₀ ^ h = x₀ ^ (h - 1) * x₀ := by rw [← pow_succ, ← h_sub]
      have h_2h : (2 * (h : ℝ)) ^ h = (2 * (h : ℝ)) ^ (h - 1) * (2 * (h : ℝ)) := by
        rw [← pow_succ, ← h_sub]
      rw [div_pow, h_x, h_2h]
      ring
    have h2h_pow_ge : (h : ℝ) ≤ (2 * (h : ℝ)) ^ (h - 1) := by
      have h3 : 3 ≤ h - 1 := by omega
      have h2h_ge8 : (8 : ℝ) ≤ 2 * (h : ℝ) := by
        have : (4 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh_ge4
        linarith
      calc (h : ℝ) ≤ 2 * (h : ℝ) := by linarith
        _ = (2 * (h : ℝ)) ^ 1 := (pow_one _).symm
        _ ≤ (2 * (h : ℝ)) ^ (h - 1) := pow_le_pow_right₀ (by linarith) (by omega)
    have h_ratio_le : (h₀ : ℝ) / (2 * (h : ℝ)) ^ (h - 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact (by exact_mod_cast hh_ge_h₀ : (h₀ : ℝ) ≤ (h : ℝ)).trans h2h_pow_ge
    calc (h₀ : ℝ) * w₁
      _ = ((h₀ : ℝ) / (2 * (h : ℝ)) ^ (h - 1)) * x₀ * (x₀ ^ (h - 1) * ((S.card : ℝ) / (2 * (h : ℝ)))) := by
        dsimp [w₁]
        rw [hh_pow_eq]
        ring
      _ ≤ 1 * 1 * (x₀ ^ (h - 1) * (m₀ : ℝ)) := by
        refine mul_le_mul ?_ (mul_le_mul_of_nonneg_left hm₀_ge (by positivity))
          (by positivity) (by positivity)
        exact mul_le_mul h_ratio_le hx₀1 hx₀0.le zero_le_one
      _ = x₀ ^ (h - 1) * (m₀ : ℝ) := by ring
  have hS_ne : S.Nonempty := card_pos.mp (by omega)
  obtain ⟨v_dummy, _⟩ := hS_ne
  have h_ind : ∀ t : ℕ, t ≤ h₀ →
      ∃ (v : Fin h₀ → V) (R : Fin h₀ → Finset V),
        (∀ i : Fin h₀, i.val < t → v i ∈ T i) ∧
        (∀ i j : Fin h₀, i.val < t → j.val < t → (G.Adj (v i) (v j) ↔ H.Adj i j)) ∧
        (∀ k : Fin h₀, R k ⊆ T k) ∧
        (∀ k : Fin h₀, t ≤ k.val → x₀ ^ t * (m₀ : ℝ) ≤ ((R k).card : ℝ)) ∧
        (∀ i k : Fin h₀, i.val < t → t ≤ k.val → ∀ u ∈ R k, (G.Adj (v i) u ↔ H.Adj i k)) := by
    intro t
    induction t with
    | zero =>
      intro _
      refine ⟨fun _ => v_dummy, T, ?_, ?_, fun _ => Subset.rfl, ?_, ?_⟩
      · intro i hi; omega
      · intro i _ hi _; omega
      · intro k _; simp [hT_card k]
      · intro i _ hi _; omega
    | succ t ih =>
      intro ht1
      obtain ⟨v, R, hv_mem, hv_adj, hR_sub, hR_card, hR_adj⟩ := ih (by omega)
      let t_fin : Fin h₀ := ⟨t, ht1⟩
      have ht_le_hm1 : t ≤ h - 1 := by omega
      have hRt_ge : x₀ ^ (h - 1) * (m₀ : ℝ) ≤ ((R t_fin).card : ℝ) := by
        have hxt : x₀ ^ (h - 1) ≤ x₀ ^ t := pow_le_pow_of_le_one hx₀0.le hx₀1 ht_le_hm1
        calc x₀ ^ (h - 1) * (m₀ : ℝ)
          _ ≤ x₀ ^ t * (m₀ : ℝ) := mul_le_mul_of_nonneg_right hxt (Nat.cast_nonneg _)
          _ ≤ ((R t_fin).card : ℝ) := hR_card t_fin le_rfl
      let Bad : Fin h₀ → Finset V := fun k =>
        if t < k.val then
          (R t_fin).filter (fun u =>
            ((neighborFinsetIn (if H.Adj t_fin k then G else Gᶜ) u (R k)).card : ℝ) ≤
              x₀ * ((R k).card : ℝ))
        else ∅
      have hBad_lt : ∀ k : Fin h₀, ((Bad k).card : ℝ) < w₁ := by
        intro k
        dsimp [Bad]
        by_cases htk : t < k.val
        · rw [if_pos htk]
          by_contra hge
          push_neg at hge
          have hRk_ge_w₁ : w₁ ≤ ((R k).card : ℝ) := by
            have hxt : x₀ ^ (h - 1) ≤ x₀ ^ t := pow_le_pow_of_le_one hx₀0.le hx₀1 ht_le_hm1
            have hh₀_ge1 : (1 : ℝ) ≤ (h₀ : ℝ) := by exact_mod_cast (by omega : 1 ≤ h₀)
            calc w₁ = 1 * w₁ := (one_mul _).symm
              _ ≤ (h₀ : ℝ) * w₁ := mul_le_mul_of_nonneg_right hh₀_ge1 hw₁_pos.le
              _ ≤ x₀ ^ (h - 1) * (m₀ : ℝ) := hh₀_w₁_le
              _ ≤ x₀ ^ t * (m₀ : ℝ) := mul_le_mul_of_nonneg_right hxt (Nat.cast_nonneg _)
              _ ≤ ((R k).card : ℝ) := hR_card k (by omega)
          let L_k := (R t_fin).filter (fun u =>
            ((neighborFinsetIn (if H.Adj t_fin k then G else Gᶜ) u (R k)).card : ℝ) ≤
              x₀ * ((R k).card : ℝ))
          have hLk_sub : L_k ⊆ S := Subset.trans (filter_subset _ _)
            (Subset.trans (hR_sub t_fin) (hTS t_fin))
          have hRk_sub : R k ⊆ S := Subset.trans (hR_sub k) (hTS k)
          have htk_ne : t_fin ≠ k := fun heq => by
            have : t = k.val := congrArg Fin.val heq
            omega
          have hdisj_LR : Disjoint L_k (R k) :=
            Disjoint.mono (Subset.trans (filter_subset _ _) (hR_sub t_fin)) (hR_sub k)
              (hT_disj t_fin k htk_ne)
          have hsparse_LR : IsXSparseTo G L_k (R k) x₀ ∨ IsXSparseTo Gᶜ L_k (R k) x₀ := by
            by_cases hadj : H.Adj t_fin k
            · left; intro u hu; simp only [L_k, if_pos hadj, mem_filter] at hu; exact hu.2
            · right; intro u hu; simp only [L_k, if_neg hadj, mem_filter] at hu; exact hu.2
          exact hno_pair ⟨L_k, hLk_sub, R k, hRk_sub, hdisj_LR, hge, hRk_ge_w₁, hsparse_LR⟩
        · rw [if_neg htk]
          simpa using hw₁_pos
      haveI : Nonempty (Fin h₀) := ⟨⟨0, by omega⟩⟩
      have hbiUnion_lt : ((Finset.univ.biUnion Bad).card : ℝ) < ((R t_fin).card : ℝ) := by
        have h1 : ((Finset.univ.biUnion Bad).card : ℝ) ≤ ∑ k : Fin h₀, ((Bad k).card : ℝ) := by
          exact_mod_cast card_biUnion_le
        have h2 : ∑ k : Fin h₀, ((Bad k).card : ℝ) < ∑ _k : Fin h₀, w₁ :=
          sum_lt_sum_of_nonempty univ_nonempty (fun k _ => hBad_lt k)
        have h3 : (∑ _k : Fin h₀, w₁) = (h₀ : ℝ) * w₁ := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        linarith
      have hgood_ne : (R t_fin \ Finset.univ.biUnion Bad).Nonempty := by
        rw [nonempty_iff_ne_empty]
        intro hemp
        have hsub : R t_fin ⊆ Finset.univ.biUnion Bad := sdiff_eq_empty_iff_subset.mp hemp
        have hle : ((R t_fin).card : ℝ) ≤ ((Finset.univ.biUnion Bad).card : ℝ) := by
          exact_mod_cast card_le_card hsub
        linarith
      obtain ⟨v_t, hv_t⟩ := hgood_ne
      rw [mem_sdiff, mem_biUnion] at hv_t
      obtain ⟨hv_t_R, hv_t_not_bad⟩ := hv_t
      push_neg at hv_t_not_bad
      let v' : Fin h₀ → V := fun i => if i = t_fin then v_t else v i
      let R' : Fin h₀ → Finset V := fun k =>
        if t < k.val then
          neighborFinsetIn (if H.Adj t_fin k then G else Gᶜ) v_t (R k)
        else R k
      refine ⟨v', R', ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi
        dsimp [v']
        split_ifs with hit
        · subst hit; exact hR_sub t_fin hv_t_R
        · have hit_val : i.val ≠ t := fun h => hit (Fin.ext h)
          exact hv_mem i (by omega)
      · intro i j hi hj
        dsimp [v']
        split_ifs with hit hjt hjt
        · subst hit; subst hjt; simp
        · subst hit
          have hjt_val : j.val < t := by
            have : j.val ≠ t := fun h => hjt (Fin.ext h)
            omega
          have h_step := hR_adj j t_fin hjt_val le_rfl v_t hv_t_R
          exact ⟨fun hadj => (h_step.mp hadj.symm).symm, fun hadj => (h_step.mpr hadj.symm).symm⟩
        · subst hjt
          have hit_val : i.val < t := by
            have : i.val ≠ t := fun h => hit (Fin.ext h)
            omega
          exact hR_adj i t_fin hit_val le_rfl v_t hv_t_R
        · have hit_val : i.val < t := by
            have : i.val ≠ t := fun h => hit (Fin.ext h)
            omega
          have hjt_val : j.val < t := by
            have : j.val ≠ t := fun h => hjt (Fin.ext h)
            omega
          exact hv_adj i j hit_val hjt_val
      · intro k
        dsimp [R']
        by_cases htk : t < k.val
        · rw [if_pos htk]
          exact Subset.trans (neighborFinsetIn_subset' _ _ _) (hR_sub k)
        · rw [if_neg htk]
          exact hR_sub k
      · intro k hk
        have htk : t < k.val := by omega
        dsimp [R']
        rw [if_pos htk]
        have hnot_bad := hv_t_not_bad k (mem_univ k)
        simp only [Bad, if_pos htk, mem_filter, hv_t_R, true_and, not_le] at hnot_bad
        have hRk_ge := hR_card k (by omega)
        calc x₀ ^ (t + 1) * (m₀ : ℝ)
          _ = x₀ * (x₀ ^ t * (m₀ : ℝ)) := by ring
          _ ≤ x₀ * ((R k).card : ℝ) := mul_le_mul_of_nonneg_left hRk_ge hx₀0.le
          _ ≤ ((neighborFinsetIn (if H.Adj t_fin k then G else Gᶜ) v_t (R k)).card : ℝ) :=
            hnot_bad.le
      · intro i k hi hk u hu
        have htk : t < k.val := by omega
        dsimp [R'] at hu
        rw [if_pos htk] at hu
        have hu_Rk : u ∈ R k := neighborFinsetIn_subset' _ _ _ hu
        dsimp [v']
        split_ifs with hit
        · subst hit
          by_cases hadj : H.Adj t_fin k
          · rw [if_pos hadj, mem_neighborFinsetIn'] at hu
            exact iff_of_true hu.2 hadj
          · rw [if_neg hadj, mem_neighborFinsetIn', compl_adj] at hu
            exact iff_of_false hu.2.2 hadj
        · have hit_val : i.val < t := by
            have : i.val ≠ t := fun h => hit (Fin.ext h)
            omega
          exact hR_adj i k hit_val (by omega) u hu_Rk
  obtain ⟨v, _, hv_mem, hv_adj, _, _, _⟩ := h_ind h₀ le_rfl
  have hv_inj : Function.Injective v := by
    intro i j hij
    by_contra hne
    have hi : v i ∈ T i := hv_mem i i.isLt
    have hj : v i ∈ T j := hij ▸ hv_mem j j.isLt
    exact Finset.disjoint_left.mp (hT_disj i j hne) hi hj
  apply hG
  refine ⟨⟨v, hv_inj⟩, ?_⟩
  ext i j
  exact (hv_adj i j i.isLt j.isLt).symm

private theorem crossEdgeCount_union_right' (H : SimpleGraph V) (A B₁ B₂ : Finset V)
    (hdisj : Disjoint B₁ B₂) :
    crossEdgeCount H A (B₁ ∪ B₂) = crossEdgeCount H A B₁ + crossEdgeCount H A B₂ := by
  classical
  unfold crossEdgeCount
  rw [← sum_add_distrib]
  refine sum_congr rfl (fun u _ => ?_)
  have heq : neighborFinsetIn H u (B₁ ∪ B₂) =
      neighborFinsetIn H u B₁ ∪ neighborFinsetIn H u B₂ := by
    ext v
    simp [or_and_right]
  have hdisj' : Disjoint (neighborFinsetIn H u B₁) (neighborFinsetIn H u B₂) :=
    Disjoint.mono (neighborFinsetIn_subset' _ _ _) (neighborFinsetIn_subset' _ _ _) hdisj
  rw [heq, card_union_of_disjoint hdisj']

private theorem crossEdgeCount_union_union' (H : SimpleGraph V) (X U' : Finset V)
    (hdisj : Disjoint X U') :
    crossEdgeCount H (X ∪ U') (X ∪ U') =
      crossEdgeCount H X X + 2 * crossEdgeCount H X U' + crossEdgeCount H U' U' := by
  have hunion_left : ∀ B, crossEdgeCount H (X ∪ U') B = crossEdgeCount H X B + crossEdgeCount H U' B := by
    intro B
    unfold crossEdgeCount
    exact sum_union hdisj
  rw [hunion_left (X ∪ U'), crossEdgeCount_union_right' H X X U' hdisj,
    crossEdgeCount_union_right' H U' X U' hdisj, crossEdgeCount_comm' H U' X]
  ring

private theorem crossEdgeCount_self_le' (H : SimpleGraph V) (X : Finset V) :
    crossEdgeCount H X X ≤ X.card * X.card := by
  unfold crossEdgeCount
  calc ∑ u ∈ X, (neighborFinsetIn H u X).card
    _ ≤ ∑ _u ∈ X, X.card :=
      sum_le_sum (fun u _ => card_le_card (neighborFinsetIn_subset' H u X))
    _ = X.card * X.card := by rw [sum_const, smul_eq_mul]

private theorem extend_low_edge_subset' (H : SimpleGraph V) (Y L R U' : Finset V)
    (p' m : ℕ) (x₀ : ℝ) (hx₀0 : 0 ≤ x₀) (_hm : 1 ≤ m)
    (hLY : L ⊆ Y) (hRY : R ⊆ Y) (hdisj : Disjoint L R)
    (hR_card : m ≤ R.card) (hLR : IsXSparseTo H L R x₀)
    (hU'L : U' ⊆ L) (hU'_card : U'.card = p' * m)
    (hU'_edges : (crossEdgeCount H U' U' : ℝ) ≤ ((p' : ℝ) + (p' : ℝ) ^ 2 * x₀) * (m : ℝ) ^ 2) :
    ∃ U ⊆ Y, U.card = (p' + 1) * m ∧
      (crossEdgeCount H U U : ℝ) ≤
        (((p' + 1 : ℕ) : ℝ) + ((p' + 1 : ℕ) : ℝ) ^ 2 * x₀) * (m : ℝ) ^ 2 := by
  classical
  have hR_pos : (0 : ℝ) < (R.card : ℝ) := by
    have : 0 < R.card := by omega
    exact_mod_cast this
  have hcross_U'R : (crossEdgeCount H R U' : ℝ) ≤ (U'.card : ℝ) * (x₀ * (R.card : ℝ)) := by
    rw [crossEdgeCount_comm' H R U', crossEdgeCount_eq_sum_left]
    push_cast
    calc ∑ u ∈ U', ((neighborFinsetIn H u R).card : ℝ)
      _ ≤ ∑ _u ∈ U', x₀ * (R.card : ℝ) := sum_le_sum (fun u hu => hLR u (hU'L hu))
      _ = (U'.card : ℝ) * (x₀ * (R.card : ℝ)) := by rw [sum_const, nsmul_eq_mul]
  let w : V → ℝ := fun v => ((neighborFinsetIn H v U').card : ℝ)
  obtain ⟨X, hXR, hX_card, hX_sum⟩ :=
    exists_subset_card_eq_sum_le R w (fun _ _ => Nat.cast_nonneg _) m hR_card
  have hcross_XU' : (crossEdgeCount H X U' : ℝ) ≤ (p' : ℝ) * x₀ * (m : ℝ) ^ 2 := by
    have hsum_X : ∑ v ∈ X, w v = (crossEdgeCount H X U' : ℝ) := by
      dsimp [w]
      exact_mod_cast (crossEdgeCount_eq_sum_left H X U').symm
    have hsum_R : ∑ v ∈ R, w v = (crossEdgeCount H R U' : ℝ) := by
      dsimp [w]
      exact_mod_cast (crossEdgeCount_eq_sum_left H R U').symm
    have hmul : (R.card : ℝ) * (crossEdgeCount H X U' : ℝ) ≤
        (R.card : ℝ) * ((p' : ℝ) * x₀ * (m : ℝ) ^ 2) := by
      calc (R.card : ℝ) * (crossEdgeCount H X U' : ℝ)
        _ = (R.card : ℝ) * (∑ v ∈ X, w v) := by rw [hsum_X]
        _ ≤ (m : ℝ) * (∑ v ∈ R, w v) := hX_sum
        _ = (m : ℝ) * (crossEdgeCount H R U' : ℝ) := by rw [hsum_R]
        _ ≤ (m : ℝ) * ((U'.card : ℝ) * (x₀ * (R.card : ℝ))) :=
          mul_le_mul_of_nonneg_left hcross_U'R (Nat.cast_nonneg _)
        _ = (R.card : ℝ) * ((p' : ℝ) * x₀ * (m : ℝ) ^ 2) := by
          rw [hU'_card]; push_cast; ring
    exact le_of_mul_le_mul_left hmul hR_pos
  have hdisj_XU' : Disjoint X U' := Disjoint.mono hXR hU'L hdisj.symm
  let U := X ∪ U'
  have hU_card : U.card = (p' + 1) * m := by
    rw [card_union_of_disjoint hdisj_XU', hX_card, hU'_card]; ring
  have hXX : (crossEdgeCount H X X : ℝ) ≤ (m : ℝ) ^ 2 := by
    have hle := crossEdgeCount_self_le' H X
    rw [hX_card] at hle
    have hle' : (crossEdgeCount H X X : ℝ) ≤ (m : ℝ) * (m : ℝ) := by exact_mod_cast hle
    linarith [sq (m : ℝ)]
  refine ⟨U, union_subset (hXR.trans hRY) (hU'L.trans hLY), hU_card, ?_⟩
  have hunion_real : (crossEdgeCount H (X ∪ U') (X ∪ U') : ℝ) =
      (crossEdgeCount H X X : ℝ) + 2 * (crossEdgeCount H X U' : ℝ) +
        (crossEdgeCount H U' U' : ℝ) := by
    exact_mod_cast crossEdgeCount_union_union' H X U' hdisj_XU'
  dsimp [U]
  rw [hunion_real]
  calc (crossEdgeCount H X X : ℝ) + 2 * (crossEdgeCount H X U' : ℝ) + (crossEdgeCount H U' U' : ℝ)
    _ ≤ (m : ℝ) ^ 2 + 2 * ((p' : ℝ) * x₀ * (m : ℝ) ^ 2) +
        ((p' : ℝ) + (p' : ℝ) ^ 2 * x₀) * (m : ℝ) ^ 2 := by linarith
    _ ≤ (((p' + 1 : ℕ) : ℝ) + ((p' + 1 : ℕ) : ℝ) ^ 2 * x₀) * (m : ℝ) ^ 2 := by
      push_cast
      have : 0 ≤ x₀ * (m : ℝ) ^ 2 := by positivity
      nlinarith

private theorem rodl_ramsey_low_edge_subset_gen (G : SimpleGraph V)
    {h₀ : ℕ} (hh₀ : 2 ≤ h₀) (H : SimpleGraph (Fin h₀)) (hG : IsInducedSubgraphFree G H)
    (x₀ w₀ : ℝ) (hx₀0 : 0 < x₀) (hx₀1 : x₀ ≤ 1)
    (hw₀ : ((2 * max h₀ 4 : ℕ) : ℝ) ≤ w₀) :
    let h := max h₀ 4
    let m := ⌈w₀⌉₊
    let c₁ := (x₀ / (2 * (h : ℝ))) ^ h
    ∀ (N : ℕ) (p q : ℕ), 1 ≤ p → 1 ≤ q → p + q = N →
      ∀ Y : Finset V, w₀ ≤ c₁ ^ (p + q - 2) * (Y.card : ℝ) →
        (∃ U ⊆ Y, U.card = p * m ∧
          (crossEdgeCount G U U : ℝ) ≤ ((p : ℝ) + (p : ℝ) ^ 2 * x₀) * (m : ℝ) ^ 2) ∨
        (∃ U ⊆ Y, U.card = q * m ∧
          (crossEdgeCount Gᶜ U U : ℝ) ≤ ((q : ℝ) + (q : ℝ) ^ 2 * x₀) * (m : ℝ) ^ 2) := by
  intro h m c₁ N
  have hh_ge4 : 4 ≤ h := le_max_right h₀ 4
  have hc₁_pos : 0 < c₁ := by dsimp [c₁]; positivity
  have hc₁_le_one : c₁ ≤ 1 := by
    dsimp [c₁]
    have h2h : (8 : ℝ) ≤ 2 * (h : ℝ) := by
      have : (4 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh_ge4
      linarith
    have : x₀ / (2 * (h : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    exact pow_le_one₀ (by positivity) this
  have hw₀_pos : 0 < w₀ := by
    have : (8 : ℝ) ≤ ((2 * max h₀ 4 : ℕ) : ℝ) := by exact_mod_cast (by omega : 8 ≤ 2 * max h₀ 4)
    linarith
  have hm_ge1 : 1 ≤ m := Nat.ceil_pos.mpr hw₀_pos
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro p q hp hq hN Y hY_card
    have hc₁_pow_le_one : c₁ ^ (p + q - 2) ≤ 1 := pow_le_one₀ hc₁_pos.le hc₁_le_one
    have hw₀_le_Y : w₀ ≤ (Y.card : ℝ) := by
      calc w₀ ≤ c₁ ^ (p + q - 2) * (Y.card : ℝ) := hY_card
        _ ≤ 1 * (Y.card : ℝ) := mul_le_mul_of_nonneg_right hc₁_pow_le_one (Nat.cast_nonneg _)
        _ = (Y.card : ℝ) := one_mul _
    have hm_le_Y : m ≤ Y.card := Nat.ceil_le.mpr hw₀_le_Y
    have hY_2h : 2 * max h₀ 4 ≤ Y.card := by
      exact_mod_cast hw₀.trans hw₀_le_Y
    rcases p with _ | p'
    · omega
    · rcases Nat.eq_zero_or_pos p' with rfl | hp'
      · left
        obtain ⟨U, hUY, hU_card⟩ := exists_subset_card_eq hm_le_Y
        refine ⟨U, hUY, by simpa using hU_card, ?_⟩
        have hUU := crossEdgeCount_self_le' G U
        rw [hU_card] at hUU
        have hUU' : (crossEdgeCount G U U : ℝ) ≤ (m : ℝ) * (m : ℝ) := by exact_mod_cast hUU
        push_cast
        have : 0 ≤ x₀ * (m : ℝ) ^ 2 := by positivity
        nlinarith [sq (m : ℝ)]
      · rcases q with _ | q'
        · omega
        · rcases Nat.eq_zero_or_pos q' with rfl | hq'
          · right
            obtain ⟨U, hUY, hU_card⟩ := exists_subset_card_eq hm_le_Y
            refine ⟨U, hUY, by simpa using hU_card, ?_⟩
            have hUU := crossEdgeCount_self_le' Gᶜ U
            rw [hU_card] at hUU
            have hUU' : (crossEdgeCount Gᶜ U U : ℝ) ≤ (m : ℝ) * (m : ℝ) := by exact_mod_cast hUU
            push_cast
            have : 0 ≤ x₀ * (m : ℝ) ^ 2 := by positivity
            nlinarith [sq (m : ℝ)]
          · obtain ⟨L, hLY, R, hRY, hdisj, hL_card, hR_card, hsparse⟩ :=
              induced_fin_free_sparse_or_cosparse_pair G hh₀ H hG Y x₀ hx₀0 hx₀1 hY_2h
            have hexp : p' + 1 + (q' + 1) - 2 = (p' + q' - 1) + 1 := by omega
            have hY_card' : w₀ ≤ c₁ ^ (p' + q' - 1) * (c₁ * (Y.card : ℝ)) := by
              rw [hexp, pow_succ] at hY_card
              linarith
            have hw₀_le_R : w₀ ≤ (R.card : ℝ) := by
              have hpow_le : c₁ ^ (p' + q' - 1) ≤ 1 := pow_le_one₀ hc₁_pos.le hc₁_le_one
              calc w₀ ≤ c₁ ^ (p' + q' - 1) * (c₁ * (Y.card : ℝ)) := hY_card'
                _ ≤ 1 * (c₁ * (Y.card : ℝ)) := mul_le_mul_of_nonneg_right hpow_le (by positivity)
                _ = c₁ * (Y.card : ℝ) := one_mul _
                _ ≤ (R.card : ℝ) := hR_card
            have hm_le_R : m ≤ R.card := Nat.ceil_le.mpr hw₀_le_R
            have hL_ind : w₀ ≤ c₁ ^ (p' + q' - 1) * (L.card : ℝ) :=
              hY_card'.trans (mul_le_mul_of_nonneg_left hL_card (by positivity))
            rcases hsparse with hLR_G | hLR_Gc
            · have hlt : p' + (q' + 1) < N := by omega
              have hexp_L : p' + (q' + 1) - 2 = p' + q' - 1 := by omega
              rcases ih (p' + (q' + 1)) hlt p' (q' + 1) hp' (by omega) rfl L (hexp_L ▸ hL_ind) with
                ⟨U', hU'L, hU'_card, hU'_edges⟩ | ⟨U, hUL, hU_card, hU_edges⟩
              · left
                exact extend_low_edge_subset' G Y L R U' p' m x₀ hx₀0.le hm_ge1
                  hLY hRY hdisj hm_le_R hLR_G hU'L hU'_card hU'_edges
              · right; exact ⟨U, hUL.trans hLY, hU_card, hU_edges⟩
            · have hlt : (p' + 1) + q' < N := by omega
              have hexp_L : (p' + 1) + q' - 2 = p' + q' - 1 := by omega
              rcases ih ((p' + 1) + q') hlt (p' + 1) q' (by omega) hq' rfl L (hexp_L ▸ hL_ind) with
                ⟨U, hUL, hU_card, hU_edges⟩ | ⟨U', hU'L, hU'_card, hU'_edges⟩
              · left; exact ⟨U, hUL.trans hLY, hU_card, hU_edges⟩
              · right
                exact extend_low_edge_subset' Gᶜ Y L R U' q' m x₀ hx₀0.le hm_ge1
                  hLY hRY hdisj hm_le_R hLR_Gc hU'L hU'_card hU'_edges

private theorem sparse_subset_of_low_edge_subset' (H : SimpleGraph V) (F U : Finset V)
    (ℓ m : ℕ) (ξ x₀ : ℝ) (hξ0 : 0 < ξ) (hℓ_ge : 8 / ξ ≤ (ℓ : ℝ)) (hx₀_le : x₀ ≤ ξ / 8)
    (hℓ1 : 1 ≤ ℓ) (hm1 : 1 ≤ m) (hUF : U ⊆ F) (hU_card : U.card = ℓ * m)
    (hU_edges : (crossEdgeCount H U U : ℝ) ≤ ((ℓ : ℝ) + (ℓ : ℝ) ^ 2 * x₀) * (m : ℝ) ^ 2) :
    ∃ F₀ ⊆ F, IsEpsSparseOn H F₀ ξ ∧ (m : ℝ) / 2 ≤ (F₀.card : ℝ) := by
  classical
  have hU_card_real : (U.card : ℝ) = (ℓ : ℝ) * (m : ℝ) := by exact_mod_cast hU_card
  have hU_pos : (0 : ℝ) < (U.card : ℝ) := by
    rw [hU_card_real]
    have : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ1
    have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    positivity
  have hℓ_bound : (ℓ : ℝ) ≤ (ξ / 8) * (ℓ : ℝ) ^ 2 := by
    have h1 : 8 ≤ (ℓ : ℝ) * ξ := (div_le_iff₀ hξ0).mp hℓ_ge
    have h2 : 1 ≤ (ξ / 8) * (ℓ : ℝ) := by linarith
    calc (ℓ : ℝ) = 1 * (ℓ : ℝ) := (one_mul _).symm
      _ ≤ ((ξ / 8) * (ℓ : ℝ)) * (ℓ : ℝ) := mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg _)
      _ = (ξ / 8) * (ℓ : ℝ) ^ 2 := by ring
  have hedges_bound : (crossEdgeCount H U U : ℝ) ≤ (ξ / 4) * (U.card : ℝ) ^ 2 := by
    calc (crossEdgeCount H U U : ℝ)
      _ ≤ ((ℓ : ℝ) + (ℓ : ℝ) ^ 2 * x₀) * (m : ℝ) ^ 2 := hU_edges
      _ ≤ ((ξ / 8) * (ℓ : ℝ) ^ 2 + (ℓ : ℝ) ^ 2 * (ξ / 8)) * (m : ℝ) ^ 2 := by
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        have : (ℓ : ℝ) ^ 2 * x₀ ≤ (ℓ : ℝ) ^ 2 * (ξ / 8) :=
          mul_le_mul_of_nonneg_left hx₀_le (sq_nonneg _)
        linarith
      _ = (ξ / 4) * ((ℓ : ℝ) * (m : ℝ)) ^ 2 := by ring
      _ = (ξ / 4) * (U.card : ℝ) ^ 2 := by rw [hU_card_real]
  let P : V → Prop := fun v => ((neighborFinsetIn H v U).card : ℝ) ≤ (ξ / 2) * (U.card : ℝ)
  let F₀ := U.filter P
  let B := U.filter (fun v => ¬P v)
  have hsum_cards : (F₀.card : ℝ) + (B.card : ℝ) = (U.card : ℝ) := by
    exact_mod_cast card_filter_add_card_filter_not P
  have hB_edges : (B.card : ℝ) * ((ξ / 2) * (U.card : ℝ)) ≤ (crossEdgeCount H U U : ℝ) := by
    calc (B.card : ℝ) * ((ξ / 2) * (U.card : ℝ))
      _ = ∑ _v ∈ B, (ξ / 2) * (U.card : ℝ) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ v ∈ B, ((neighborFinsetIn H v U).card : ℝ) := by
        refine sum_le_sum (fun v hv => ?_)
        simp only [B, P, mem_filter, not_le] at hv
        exact hv.2.le
      _ ≤ ∑ v ∈ U, ((neighborFinsetIn H v U).card : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.cast_nonneg _)
      _ = (crossEdgeCount H U U : ℝ) := by
        exact_mod_cast (crossEdgeCount_eq_sum_left H U U).symm
  have hB_le : (B.card : ℝ) ≤ (U.card : ℝ) / 2 := by
    have hpos : 0 < (ξ / 2) * (U.card : ℝ) := by positivity
    have hmul : ((ξ / 2) * (U.card : ℝ)) * (B.card : ℝ) ≤
        ((ξ / 2) * (U.card : ℝ)) * ((U.card : ℝ) / 2) := by
      calc ((ξ / 2) * (U.card : ℝ)) * (B.card : ℝ)
        _ = (B.card : ℝ) * ((ξ / 2) * (U.card : ℝ)) := mul_comm _ _
        _ ≤ (crossEdgeCount H U U : ℝ) := hB_edges
        _ ≤ (ξ / 4) * (U.card : ℝ) ^ 2 := hedges_bound
        _ = ((ξ / 2) * (U.card : ℝ)) * ((U.card : ℝ) / 2) := by ring
    exact le_of_mul_le_mul_left hmul hpos
  have hF₀_ge_m : (m : ℝ) / 2 ≤ (F₀.card : ℝ) := by
    have hm_le_U : (m : ℝ) ≤ (U.card : ℝ) := by
      rw [hU_card_real]
      have hℓ1' : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ1
      calc (m : ℝ) = 1 * (m : ℝ) := (one_mul _).symm
        _ ≤ (ℓ : ℝ) * (m : ℝ) := mul_le_mul_of_nonneg_right hℓ1' (Nat.cast_nonneg _)
    linarith
  refine ⟨F₀, (filter_subset _ _).trans hUF, ?_, hF₀_ge_m⟩
  intro v hv
  have hvU : v ∈ U ∧ ((neighborFinsetIn H v U).card : ℝ) ≤ (ξ / 2) * (U.card : ℝ) := by
    simpa [F₀, P] using hv
  have hle_U : ((neighborFinsetIn H v F₀).card : ℝ) ≤ ((neighborFinsetIn H v U).card : ℝ) := by
    exact_mod_cast card_le_card (neighborFinsetIn_mono' H v (filter_subset _ _))
  calc ((neighborFinsetIn H v F₀).card : ℝ)
    _ ≤ (ξ / 2) * (U.card : ℝ) := hle_U.trans hvU.2
    _ ≤ (ξ / 2) * (2 * (F₀.card : ℝ)) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = ξ * (F₀.card : ℝ) := by ring

/--
Explicit positive constant $\delta(h_0, \xi)$ for Theorem 2 (Rödl's Theorem, `main.tex` line 138):
$$\delta(h_0, \xi) := \frac{1}{2 h}\left(\frac{\xi}{16 h}\right)^{2 h \lceil 8 / \xi \rceil}, \qquad h := \max(h_0, 4).$$
-/
noncomputable def symmRodlDeltaGen (h₀ : ℕ) (ξ : ℝ) : ℝ :=
  let h := max h₀ 4
  ((ξ / (16 * (h : ℝ))) ^ h) ^ (2 * ⌈8 / ξ⌉₊) / (2 * (h : ℝ))

private theorem rodlDeltaGen_pos (h₀ : ℕ) {ξ : ℝ} (hξ0 : 0 < ξ) : 0 < symmRodlDeltaGen h₀ ξ := by
  unfold symmRodlDeltaGen
  dsimp only
  have hh : (4 : ℝ) ≤ (max h₀ 4 : ℝ) := by exact_mod_cast le_max_right h₀ 4
  positivity

/--
**Theorem 2 (`rodl_theorem_general`, Rödl's Theorem, `main.tex` lines 135–142)**:
For every finite graph $H : \text{SimpleGraph } W$ (`[Fintype W]`) and every $\xi \in (0, 1/2)$,
every $H$-free graph $G$ and every vertex subset $F \subseteq V(G)$ contains a $\xi$-restricted
subset $F_0 \subseteq F$ with $|F_0| \ge \mathrm{rodlDeltaGen}(|W|, \xi) |F|$.
-/
private theorem rodl_theorem_general {W : Type*} [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (hG : IsInducedSubgraphFree G H)
    (ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ < 1 / 2) (F : Finset V) :
    ∃ F₀ ⊆ F, IsEpsRestrictedOn G F₀ ξ ∧
      symmRodlDeltaGen (Fintype.card W) ξ * (F.card : ℝ) ≤ (F₀.card : ℝ) := by
  classical
  let h₀ := Fintype.card W
  rcases (by omega : h₀ = 0 ∨ h₀ = 1 ∨ 2 ≤ h₀) with hh0 | hh1 | hh2
  · -- h₀ = 0: W is empty, so IsInducedSubgraphFree G H is False!
    exfalso
    haveI : IsEmpty W := Fintype.card_eq_zero_iff.mp hh0
    apply hG
    refine ⟨⟨fun w => isEmptyElim w, fun w => isEmptyElim w⟩, ?_⟩
    ext w; exact isEmptyElim w
  · -- h₀ = 1: W has 1 vertex, so any H-free graph has V empty (F = ∅)
    rcases F.eq_empty_or_nonempty with rfl | ⟨v₀, _⟩
    · refine ⟨∅, Subset.rfl, Or.inl (fun u hu => (notMem_empty u hu).elim), by simp⟩
    · exfalso
      apply hG
      refine ⟨⟨fun _ => v₀, fun w₁ w₂ _ => Fintype.card_le_one_iff.mp (by omega) w₁ w₂⟩, ?_⟩
      ext w₁ w₂
      have heq : w₁ = w₂ := Fintype.card_le_one_iff.mp (by omega) w₁ w₂
      subst heq
      simp
  · -- h₀ ≥ 2: transfer H to Fin h₀ and apply rodl_ramsey_low_edge_subset_gen
    let eW : Fin h₀ ≃ W := (Fintype.equivFin W).symm
    let H' : SimpleGraph (Fin h₀) := H.comap eW.toEmbedding
    have hG' : IsInducedSubgraphFree G H' := by
      rintro ⟨g, hg⟩
      apply hG
      refine ⟨eW.symm.toEmbedding.trans g, ?_⟩
      ext w₁ w₂
      have hadj := congr_arg (fun (K : SimpleGraph (Fin h₀)) => K.Adj (eW.symm w₁) (eW.symm w₂)) hg
      simpa [H', comap_adj] using hadj
    let h := max h₀ 4
    have hh_ge4 : 4 ≤ h := le_max_right h₀ 4
    have hh_pos_real : (0 : ℝ) < (h : ℝ) := by
      have : (4 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh_ge4
      linarith
    let x₀ : ℝ := ξ / 8
    have hx₀0 : 0 < x₀ := by dsimp [x₀]; positivity
    have hx₀1 : x₀ ≤ 1 := by dsimp [x₀]; linarith
    let c₁ : ℝ := (x₀ / (2 * (h : ℝ))) ^ h
    have hc₁_eq : c₁ = (ξ / (16 * (h : ℝ))) ^ h := by dsimp [c₁, x₀]; ring
    have hc₁_pos : 0 < c₁ := by dsimp [c₁]; positivity
    have hc₁_le_one : c₁ ≤ 1 := by
      dsimp [c₁]
      have h4 : (4 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh_ge4
      have : x₀ / (2 * (h : ℝ)) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith
      exact pow_le_one₀ (by positivity) this
    let ℓ : ℕ := ⌈8 / ξ⌉₊
    have hℓ_ge : 8 / ξ ≤ (ℓ : ℝ) := Nat.le_ceil _
    have hℓ1 : 1 ≤ ℓ := Nat.ceil_pos.mpr (by positivity)
    let w₀ : ℝ := c₁ ^ (2 * ℓ - 2) * (F.card : ℝ)
    have hdelta_le_w₀ : (2 * (h : ℝ)) * symmRodlDeltaGen h₀ ξ * (F.card : ℝ) ≤ w₀ := by
      have hpow : c₁ ^ (2 * ℓ) ≤ c₁ ^ (2 * ℓ - 2) :=
        pow_le_pow_of_le_one hc₁_pos.le hc₁_le_one (by omega)
      calc (2 * (h : ℝ)) * symmRodlDeltaGen h₀ ξ * (F.card : ℝ)
        _ = c₁ ^ (2 * ℓ) * (F.card : ℝ) := by
          unfold symmRodlDeltaGen
          dsimp only
          change (2 * (h : ℝ)) * (((ξ / (16 * (h : ℝ))) ^ h) ^ (2 * ℓ) / (2 * (h : ℝ))) *
            (F.card : ℝ) = c₁ ^ (2 * ℓ) * (F.card : ℝ)
          rw [← hc₁_eq, mul_div_cancel₀ _ (by positivity)]
        _ ≤ c₁ ^ (2 * ℓ - 2) * (F.card : ℝ) :=
          mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _)
        _ = w₀ := rfl
    by_cases hw₀ : (2 * (h : ℝ)) ≤ w₀
    · let m : ℕ := ⌈w₀⌉₊
      have hm1 : 1 ≤ m := Nat.ceil_pos.mpr (by linarith)
      have hw₀_le_m : w₀ ≤ (m : ℝ) := Nat.le_ceil w₀
      have hF_ind : w₀ ≤ c₁ ^ (ℓ + ℓ - 2) * (F.card : ℝ) := by
        have : ℓ + ℓ - 2 = 2 * ℓ - 2 := by omega
        rw [this]
      have hw₀_max : ((2 * max h₀ 4 : ℕ) : ℝ) ≤ w₀ := by
        have : ((2 * max h₀ 4 : ℕ) : ℝ) = 2 * (h : ℝ) := by
          dsimp [h]
          push_cast
          rfl
        linarith
      rcases rodl_ramsey_low_edge_subset_gen G hh2 H' hG' x₀ w₀ hx₀0 hx₀1 hw₀_max
          (ℓ + ℓ) ℓ ℓ hℓ1 hℓ1 rfl F hF_ind with
        ⟨U, hUF, hU_card, hU_edges⟩ | ⟨U, hUF, hU_card, hU_edges⟩
      · obtain ⟨F₀, hF₀F, hF₀_sparse, hF₀_card⟩ :=
          sparse_subset_of_low_edge_subset' G F U ℓ m ξ x₀ hξ0 hℓ_ge le_rfl hℓ1 hm1
            hUF hU_card hU_edges
        refine ⟨F₀, hF₀F, Or.inl hF₀_sparse, ?_⟩
        have hdelta_nonneg : 0 ≤ symmRodlDeltaGen h₀ ξ * (F.card : ℝ) := by
          have := rodlDeltaGen_pos h₀ hξ0
          positivity
        have h4 : (4 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh_ge4
        nlinarith
      · obtain ⟨F₀, hF₀F, hF₀_sparse, hF₀_card⟩ :=
          sparse_subset_of_low_edge_subset' Gᶜ F U ℓ m ξ x₀ hξ0 hℓ_ge le_rfl hℓ1 hm1
            hUF hU_card hU_edges
        refine ⟨F₀, hF₀F, Or.inr hF₀_sparse, ?_⟩
        have hdelta_nonneg : 0 ≤ symmRodlDeltaGen h₀ ξ * (F.card : ℝ) := by
          have := rodlDeltaGen_pos h₀ hξ0
          positivity
        have h4 : (4 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh_ge4
        nlinarith
    · push_neg at hw₀
      rcases F.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
      · refine ⟨∅, Subset.rfl, Or.inl (fun u hu => (notMem_empty u hu).elim), by simp⟩
      · refine ⟨{v}, singleton_subset_iff.mpr hv, Or.inl ?_, ?_⟩
        · intro u hu
          rw [mem_singleton.mp hu]
          have hemp : neighborFinsetIn G v {v} = ∅ := by
            rw [eq_empty_iff_forall_notMem]
            intro w hw
            rw [mem_neighborFinsetIn', mem_singleton] at hw
            exact G.loopless v (hw.1 ▸ hw.2)
          rw [hemp]
          simp [hξ0.le]
        · rw [card_singleton, Nat.cast_one]
          have hdelta_nonneg : 0 ≤ symmRodlDeltaGen h₀ ξ * (F.card : ℝ) := by
            have := rodlDeltaGen_pos h₀ hξ0
            positivity
          have h4 : (4 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh_ge4
          nlinarith

/-! ### Section 5B: Viral Leaf-Extension Cores (`viral_extension_core_of_not_restricted`) -/

/--
Transporting `IsEpsRestrictedOn` from an induced subgraph `G.induce A` on `↥(A : Set V)` to `G`.
-/
private theorem isEpsRestrictedOn_map_subtype (G : SimpleGraph V) (A : Finset V)
    (S_sub : Finset ↥(A : Set V)) (ε : ℝ)
    (h : IsEpsRestrictedOn (G.induce (A : Set V)) S_sub ε) :
    IsEpsRestrictedOn G (S_sub.map (Function.Embedding.subtype _)) ε := by
  have htransfer : ∀ H : SimpleGraph V,
      IsEpsSparseOn (H.induce (A : Set V)) S_sub ε →
      IsEpsSparseOn H (S_sub.map (Function.Embedding.subtype _)) ε := by
    intro H hsp u hu
    rcases Finset.mem_map.mp hu with ⟨a, ha, rfl⟩
    have hcard_map : (S_sub.map (Function.Embedding.subtype _)).card = S_sub.card :=
      Finset.card_map _
    have hneigh_eq : (neighborFinsetIn H a.1 (S_sub.map (Function.Embedding.subtype _))).card =
        (neighborFinsetIn (H.induce (A : Set V)) a S_sub).card := by
      have heq : neighborFinsetIn H a.1 (S_sub.map (Function.Embedding.subtype _)) =
          (neighborFinsetIn (H.induce (A : Set V)) a S_sub).map (Function.Embedding.subtype _) := by
        ext x
        simp only [mem_neighborFinsetIn', Finset.mem_map, Function.Embedding.coe_subtype]
        constructor
        · rintro ⟨⟨b, hb, rfl⟩, hadj⟩
          exact ⟨b, ⟨hb, hadj⟩, rfl⟩
        · rintro ⟨b, ⟨hb, hadj⟩, rfl⟩
          exact ⟨⟨b, hb, rfl⟩, hadj⟩
      rw [heq, Finset.card_map]
    simp only [Function.Embedding.coe_subtype]
    rw [hcard_map, hneigh_eq]
    exact hsp a ha
  rcases h with hG | hGc
  · exact Or.inl (htransfer G hG)
  · refine Or.inr (htransfer Gᶜ ?_)
    have hind_compl : (Gᶜ).induce (A : Set V) = (G.induce (A : Set V))ᶜ := by
      ext x y
      exact ⟨fun ⟨hne, hnad⟩ => ⟨fun h => hne (congrArg Subtype.val h), hnad⟩,
             fun ⟨hne, hnad⟩ => ⟨fun h => hne (Subtype.ext h), hnad⟩⟩
    rw [hind_compl]
    exact hGc

/--
If $G$ is induced-$H$-free, then `indCopyCount H (G.induce A) = 0`.
-/
private theorem indCopyCount_induce_eq_zero_of_free {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) (A : Finset V) (hG : IsInducedSubgraphFree G H) :
    indCopyCount H (G.induce (A : Set V)) = 0 := by
  classical
  unfold indCopyCount
  rw [card_eq_zero, filter_eq_empty_iff]
  intro g _ hg
  apply hG
  refine ⟨g.trans (Function.Embedding.subtype _), ?_⟩
  ext w₁ w₂
  have hadj := congr_arg (fun (K : SimpleGraph W) => K.Adj w₁ w₂) hg
  simpa [comap_adj] using hadj.symm

/--
**Viral Leaf-Extension Core Extraction (`viral_extension_core_of_not_restricted`,
`main.tex` lines 299, 367–376, 386)**:
Let $H_1 : \text{SimpleGraph } W_1$ ($h := |W_1| \ge 3$) have a degree-$1$ leaf $v_0 \in W_1$ with
unique neighbor $u_0 \neq v_0$ (`∀ w, H₁.Adj v₀ w ↔ w = u₀`), and let $H_1' := H_1 - v_0$.
Suppose $((H_1')ᶜ, H_2ᶜ)$ satisfies the viral property at exponent $d' > 0$.
Then for every $\{H_1ᶜ, H_2ᶜ\}$-free graph $G$, every nonempty subset $A \subseteq V(G)$, and
every $\varepsilon_{\mathrm{in}} \in (0, 1/2)$, either:
1. $A$ contains an $\varepsilon_{\mathrm{in}}$-restricted subset $U \subseteq A$ of cardinality
   $|U| \ge \varepsilon_{\mathrm{in}}^{d'} |A|$; or
2. there exist a base copy $\Phi \subseteq A$ of $(H_1 - v_0)ᶜ \setminus \{u_0\}$ with
   $|\Phi| = h - 2$ and an extension core $D \subseteq A \setminus \Phi$ of cardinality
   $|D| > \varepsilon_{\mathrm{in}}^{d' (h - 1)} |A|$ such that for **every $u \in D$ and every
   vertex $v \in V(G) \setminus (\Phi \cup \{u\})$ that is adjacent in $G$ to all of $\Phi$,
   $G.\text{Adj } u\ v$ holds**.
-/
theorem viral_extension_core_of_not_restricted
    {V : Type} [Fintype V] [DecidableEq V]
    {W₁ W₂ : Type*} [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]
    (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂)
    (v₀ u₀ : W₁) (hu₀_ne : u₀ ≠ v₀)
    (hleaf : ∀ w : W₁, H₁.Adj v₀ w ↔ w = u₀)
    (hh : 3 ≤ Fintype.card W₁)
    {d' : ℝ} (_hd' : 0 < d')
    (hviral : ∀ (U_type : Type) [Fintype U_type] [DecidableEq U_type]
      (F_G : SimpleGraph U_type) (ε : ℝ),
      0 < ε → ε < 1 / 2 →
      (indCopyCount (H₁.comap (Subtype.val : {w : W₁ // w ≠ v₀} → W₁))ᶜ F_G : ℝ) ≤
        (ε ^ d' * (Fintype.card U_type : ℝ)) ^ (Fintype.card {w : W₁ // w ≠ v₀}) →
      (indCopyCount H₂ᶜ F_G : ℝ) ≤
        (ε ^ d' * (Fintype.card U_type : ℝ)) ^ (Fintype.card W₂) →
      ∃ S : Finset U_type, IsEpsRestrictedOn F_G S ε ∧
        ε ^ d' * (Fintype.card U_type : ℝ) ≤ (S.card : ℝ))
    (G : SimpleGraph V) (hG₁ : IsInducedSubgraphFree G H₁ᶜ) (hG₂ : IsInducedSubgraphFree G H₂ᶜ)
    (A : Finset V) (hA_ne : A.Nonempty)
    (ε_in : ℝ) (hε0 : 0 < ε_in) (hε_half : ε_in < 1 / 2) :
    (∃ U ⊆ A, IsEpsRestrictedOn G U ε_in ∧ ε_in ^ d' * (A.card : ℝ) ≤ (U.card : ℝ)) ∨
    (∃ Φ ⊆ A, ∃ D ⊆ A,
      Φ.card ≤ Fintype.card W₁ - 2 ∧
      Disjoint Φ D ∧
      ε_in ^ (d' * ((Fintype.card W₁ - 1 : ℕ) : ℝ)) * (A.card : ℝ) < (D.card : ℝ) ∧
      ∀ u ∈ D, ∀ v : V, v ∉ Φ → v ≠ u → (∀ z ∈ Φ, G.Adj z v) → G.Adj u v) := by
  classical
  let W₁' := {w : W₁ // w ≠ v₀}
  let H₁' := H₁.comap (Subtype.val : W₁' → W₁)
  let u₀' : W₁' := ⟨u₀, hu₀_ne⟩
  let W₁'' := {w : W₁' // w ≠ u₀'}
  let F_A := G.induce (A : Set V)
  have hcard_A : Fintype.card ↥(A : Set V) = A.card := Fintype.card_coe A
  have hcard_W₁' : Fintype.card W₁' = Fintype.card W₁ - 1 := by
    have heq : Fintype.card W₁' = (Finset.univ.erase v₀).card := by
      rw [← Fintype.card_coe]
      exact Fintype.card_congr (Equiv.subtypeEquivRight (fun w => by simp [mem_erase]))
    have h1 := card_erase_add_one (mem_univ v₀)
    rw [Finset.card_univ] at h1
    omega
  have hcard_W₁'' : Fintype.card W₁'' = Fintype.card W₁ - 2 := by
    have heq : Fintype.card W₁'' = (Finset.univ.erase u₀').card := by
      rw [← Fintype.card_coe]
      exact Fintype.card_congr (Equiv.subtypeEquivRight (fun w => by simp [mem_erase]))
    have h1 := card_erase_add_one (mem_univ u₀')
    rw [Finset.card_univ] at h1
    omega
  by_cases hcopy_le : (indCopyCount (H₁')ᶜ F_A : ℝ) ≤
      (ε_in ^ d' * (Fintype.card ↥(A : Set V) : ℝ)) ^ (Fintype.card W₁')
  · -- Case 1: Few induced copies of (H₁')ᶜ -> Virality produces ε_in-restricted U ⊆ A
    left
    have hcopy₂ : (indCopyCount H₂ᶜ F_A : ℝ) ≤
        (ε_in ^ d' * (Fintype.card ↥(A : Set V) : ℝ)) ^ (Fintype.card W₂) := by
      rw [indCopyCount_induce_eq_zero_of_free G H₂ᶜ A hG₂, Nat.cast_zero]
      positivity
    obtain ⟨S_sub, hS_rest, hS_card⟩ := hviral ↥(A : Set V) F_A ε_in hε0 hε_half hcopy_le hcopy₂
    let U := S_sub.map (Function.Embedding.subtype _)
    have hUA : U ⊆ A := by
      intro x hx
      rcases Finset.mem_map.mp hx with ⟨a, _, rfl⟩
      exact a.2
    have hU_card : ε_in ^ d' * (A.card : ℝ) ≤ (U.card : ℝ) := by
      dsimp [U]
      rw [Finset.card_map, ← hcard_A]
      exact hS_card
    exact ⟨U, hUA, isEpsRestrictedOn_map_subtype G A S_sub ε_in hS_rest, hU_card⟩
  · -- Case 2: Many induced copies of (H₁')ᶜ -> Pigeonhole over W₁'' → A
    right
    push_neg at hcopy_le
    let Copies : Finset (W₁' ↪ ↥(A : Set V)) :=
      Finset.univ.filter (fun g : W₁' ↪ ↥(A : Set V) => F_A.comap g = (H₁')ᶜ)
    have hCopies_card : Copies.card = indCopyCount (H₁')ᶜ F_A := rfl
    let restrictMap : (W₁' ↪ ↥(A : Set V)) → (W₁'' → ↥(A : Set V)) :=
      fun g w => g w.1
    let Ext : (W₁'' → ↥(A : Set V)) → Finset (W₁' ↪ ↥(A : Set V)) :=
      fun f => Copies.filter (fun g => restrictMap g = f)
    have hpart : Copies.card = ∑ f : W₁'' → ↥(A : Set V), (Ext f).card := by
      rw [← card_biUnion]
      · congr 1
        ext g
        simp [Ext]
      · intro f₁ _ f₂ _ hf
        change Disjoint (Ext f₁) (Ext f₂)
        rw [Finset.disjoint_left]
        intro g hg₁ hg₂
        exact hf ((mem_filter.mp hg₁).2.symm.trans (mem_filter.mp hg₂).2)
    have hcard_funcs : Fintype.card (W₁'' → ↥(A : Set V)) = A.card ^ (Fintype.card W₁ - 2) := by
      rw [Fintype.card_fun, hcard_A, hcard_W₁'']
    have hA_pos : (0 : ℝ) < (A.card : ℝ) := Nat.cast_pos.mpr (card_pos.mpr hA_ne)
    have hsum_gt : (∑ _f : W₁'' → ↥(A : Set V),
        ε_in ^ (d' * ((Fintype.card W₁ - 1 : ℕ) : ℝ)) * (A.card : ℝ)) <
        ∑ f : W₁'' → ↥(A : Set V), ((Ext f).card : ℝ) := by
      rw [sum_const, card_univ, hcard_funcs, nsmul_eq_mul]
      have hcast_sum : (∑ f : W₁'' → ↥(A : Set V), ((Ext f).card : ℝ)) =
          (indCopyCount (H₁')ᶜ F_A : ℝ) := by
        rw [← hCopies_card, hpart]
        push_cast; rfl
      rw [hcast_sum]
      have hlhs_eq : ((A.card ^ (Fintype.card W₁ - 2) : ℕ) : ℝ) *
          (ε_in ^ (d' * ((Fintype.card W₁ - 1 : ℕ) : ℝ)) * (A.card : ℝ)) =
          (ε_in ^ d' * (Fintype.card ↥(A : Set V) : ℝ)) ^ (Fintype.card W₁') := by
        rw [hcard_A, hcard_W₁', mul_pow, ← Real.rpow_natCast (ε_in ^ d'), ← Real.rpow_mul hε0.le]
        push_cast
        have hpow_A : (A.card : ℝ) ^ (Fintype.card W₁ - 2) * (A.card : ℝ) =
            (A.card : ℝ) ^ (Fintype.card W₁ - 1) := by
          have : Fintype.card W₁ - 1 = (Fintype.card W₁ - 2) + 1 := by omega
          rw [this, pow_succ]
        rw [show (A.card : ℝ) ^ (Fintype.card W₁ - 2) *
            (ε_in ^ (d' * ((Fintype.card W₁ - 1 : ℕ) : ℝ)) * (A.card : ℝ)) =
            ε_in ^ (d' * ((Fintype.card W₁ - 1 : ℕ) : ℝ)) *
            ((A.card : ℝ) ^ (Fintype.card W₁ - 2) * (A.card : ℝ)) by ring, hpow_A]
      rw [hlhs_eq]
      exact hcopy_le
    obtain ⟨f₀, _, hf₀_gt⟩ := Finset.exists_lt_of_sum_lt hsum_gt
    -- Map Ext f₀ injectively into A via g ↦ (g u₀').1
    let evalU₀ : (W₁' ↪ ↥(A : Set V)) → V := fun g => (g u₀').1
    have heval_inj : Set.InjOn evalU₀ (Ext f₀ : Set (W₁' ↪ ↥(A : Set V))) := by
      intro g₁ hg₁ g₂ hg₂ heq
      have hf₁ : restrictMap g₁ = f₀ := (mem_filter.mp hg₁).2
      have hf₂ : restrictMap g₂ = f₀ := (mem_filter.mp hg₂).2
      ext x
      by_cases hxu₀ : x = u₀'
      · subst hxu₀
        exact heq
      · have hx_eq₁ : g₁ x = f₀ ⟨x, hxu₀⟩ := congr_fun hf₁ ⟨x, hxu₀⟩
        have hx_eq₂ : g₂ x = f₀ ⟨x, hxu₀⟩ := congr_fun hf₂ ⟨x, hxu₀⟩
        rw [hx_eq₁, hx_eq₂]
    let D : Finset V := (Ext f₀).image evalU₀
    have hD_card_eq : D.card = (Ext f₀).card := card_image_of_injOn heval_inj
    have hDA : D ⊆ A := by
      intro u hu
      obtain ⟨g, _, rfl⟩ := mem_image.mp hu
      exact (g u₀').2
    let Φ : Finset V := Finset.univ.image (fun w : W₁'' => (f₀ w).1)
    have hΦA : Φ ⊆ A := by
      intro z hz
      obtain ⟨w, _, rfl⟩ := mem_image.mp hz
      exact (f₀ w).2
    have hΦ_card : Φ.card ≤ Fintype.card W₁ - 2 := by
      calc Φ.card ≤ (Finset.univ : Finset W₁'').card := card_image_le
        _ = Fintype.card W₁'' := card_univ
        _ = Fintype.card W₁ - 2 := hcard_W₁''
    have hdisj_ΦD : Disjoint Φ D := by
      rw [Finset.disjoint_left]
      intro z hzΦ hzD
      obtain ⟨w, _, hw_eq⟩ := mem_image.mp hzΦ
      obtain ⟨g, hg_mem, hg_eq⟩ := mem_image.mp hzD
      have hgw : g w.1 = f₀ w := congr_fun (mem_filter.mp hg_mem).2 w
      dsimp [evalU₀] at hg_eq
      have hgu₀ : (g w.1).1 = (g u₀').1 :=
        (congrArg Subtype.val hgw).trans (hw_eq.trans hg_eq.symm)
      exact w.2 (g.injective (Subtype.ext hgu₀))
    refine ⟨Φ, hΦA, D, hDA, hΦ_card, hdisj_ΦD, ?_, ?_⟩
    · rw [hD_card_eq]
      exact hf₀_gt
    · intro u huD v hv_not_Φ hv_ne_u hv_adj_Φ
      obtain ⟨g, hg_mem, rfl⟩ := mem_image.mp huD
      have hg_comap : F_A.comap g = (H₁')ᶜ := (mem_filter.mp (mem_filter.mp hg_mem).1).2
      have hg_f₀ : restrictMap g = f₀ := (mem_filter.mp hg_mem).2
      by_contra hnad_uv
      -- Construct embedding W₁ ↪ V of H₁ᶜ into G
      let embFun : W₁ → V := fun w =>
        if hw : w = v₀ then v else (g ⟨w, hw⟩).1
      have hemb_v₀ : embFun v₀ = v := by simp [embFun]
      have hemb_u₀ : embFun u₀ = evalU₀ g := by
        dsimp [embFun, evalU₀, u₀']
        rw [dif_neg hu₀_ne]
      have hemb_other : ∀ (w : W₁) (hw_v₀ : w ≠ v₀) (hw_u₀ : w ≠ u₀),
          embFun w = (f₀ ⟨⟨w, hw_v₀⟩, fun h => hw_u₀ (congrArg Subtype.val h)⟩).1 := by
        intro w hw_v₀ hw_u₀
        dsimp [embFun]
        rw [dif_neg hw_v₀]
        have hgw : g ⟨w, hw_v₀⟩ = f₀ ⟨⟨w, hw_v₀⟩, fun h => hw_u₀ (congrArg Subtype.val h)⟩ :=
          congr_fun hg_f₀ ⟨⟨w, hw_v₀⟩, fun h => hw_u₀ (congrArg Subtype.val h)⟩
        exact congrArg Subtype.val hgw
      have hemb_mem_Φ : ∀ (w : W₁) (hw_v₀ : w ≠ v₀) (hw_u₀ : w ≠ u₀), embFun w ∈ Φ := by
        intro w hw_v₀ hw_u₀
        rw [hemb_other w hw_v₀ hw_u₀]
        exact mem_image_of_mem _ (mem_univ _)
      have hemb_inj : Function.Injective embFun := by
        intro x y hxy
        by_cases hx : x = v₀ <;> by_cases hy : y = v₀
        · exact hx.trans hy.symm
        · subst hx
          rw [hemb_v₀] at hxy
          by_cases hyu : y = u₀
          · subst hyu; rw [hemb_u₀] at hxy; exact (hv_ne_u hxy).elim
          · exact (hv_not_Φ (hxy.symm ▸ hemb_mem_Φ y hy hyu)).elim
        · subst hy
          rw [hemb_v₀] at hxy
          by_cases hxu : x = u₀
          · subst hxu; rw [hemb_u₀] at hxy; exact (hv_ne_u hxy.symm).elim
          · exact (hv_not_Φ (hxy ▸ hemb_mem_Φ x hx hxu)).elim
        · dsimp [embFun] at hxy
          rw [dif_neg hx, dif_neg hy] at hxy
          exact congrArg Subtype.val (g.injective (Subtype.ext hxy))
      apply hG₁
      refine ⟨⟨embFun, hemb_inj⟩, ?_⟩
      ext x y
      rw [comap_adj, Function.Embedding.coeFn_mk]
      by_cases hxy : x = y
      · subst hxy; simp
      · have hpair_v₀ : ∀ (w : W₁) (hw : w ≠ v₀),
            (H₁ᶜ.Adj v₀ w ↔ G.Adj (embFun v₀) (embFun w)) := by
          intro w hw
          rw [hemb_v₀, SimpleGraph.compl_adj, hleaf w]
          simp only [ne_eq, hw.symm, not_false_eq_true, true_and]
          by_cases hwu : w = u₀
          · subst hwu
            rw [hemb_u₀]
            exact ⟨fun h => (h rfl).elim, fun hadj => (hnad_uv hadj.symm).elim⟩
          · simp only [hwu, not_false_eq_true, true_iff]
            exact (hv_adj_Φ (embFun w) (hemb_mem_Φ w hw hwu)).symm
        by_cases hx : x = v₀
        · subst hx
          exact hpair_v₀ y (Ne.symm hxy)
        · by_cases hy : y = v₀
          · subst hy
            rw [H₁ᶜ.adj_comm, G.adj_comm]
            exact hpair_v₀ x hxy
          · dsimp [embFun]
            rw [dif_neg hx, dif_neg hy]
            have hadj_sub := congr_arg (fun (K : SimpleGraph W₁') => K.Adj ⟨x, hx⟩ ⟨y, hy⟩) hg_comap
            have hne_sub : (⟨x, hx⟩ : W₁') ≠ ⟨y, hy⟩ := fun h => hxy (congrArg Subtype.val h)
            simpa [F_A, H₁', comap_adj, SimpleGraph.compl_adj, Function.Embedding.coe_subtype,
              hne_sub, hxy] using hadj_sub.symm

/--
**Co-Sparse Trigger-or-Restricted Lemma for Leaf-Reducible Graphs
(`leaf_reducible_cosparse_trigger_or_restricted`, `main.tex` lines 299, 315, 386)**:
In an $\{H_1ᶜ, H_2ᶜ\}$-free graph $G$ where $H_1$ ($h := |H_1| \ge 3$) has a degree-$1$ leaf $v_0$
with unique neighbor $u_0$ and $((H_1 - v_0)ᶜ, H_2ᶜ)$ is viral with exponent $d' > 0$,
for any $y$-co-sparse subgraph $F' \subseteq V(G)$ (`IsEpsSparseOn Gᶜ F' y`, $0 < y < 1/2$,
$|F'| \ge 1$), either:
1. $F'$ contains a $(y^4)$-restricted subset $U \subseteq F'$ of cardinality
   $|U| \ge y^{4 d' + 1} |F'|$; or
2. $F'$ contains disjoint subsets $X, Y \subseteq F'$ with $|X| > y^{4 d' (h - 1) + 1} |F'|$,
   $|Y| \ge (1 - h y) |F'|$, and $(X, Y)$ $100\%$ complete in $G$ (`IsCompletePair G X Y`).
-/
theorem leaf_reducible_cosparse_trigger_or_restricted
    {V : Type} [Fintype V] [DecidableEq V]
    {W₁ W₂ : Type*} [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]
    (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂)
    (v₀ u₀ : W₁) (hu₀_ne : u₀ ≠ v₀)
    (hleaf : ∀ w : W₁, H₁.Adj v₀ w ↔ w = u₀)
    (hh : 3 ≤ Fintype.card W₁)
    {d' : ℝ} (hd' : 0 < d')
    (hviral : ∀ (U_type : Type) [Fintype U_type] [DecidableEq U_type]
      (F_G : SimpleGraph U_type) (ε : ℝ),
      0 < ε → ε < 1 / 2 →
      (indCopyCount (H₁.comap (Subtype.val : {w : W₁ // w ≠ v₀} → W₁))ᶜ F_G : ℝ) ≤
        (ε ^ d' * (Fintype.card U_type : ℝ)) ^ (Fintype.card {w : W₁ // w ≠ v₀}) →
      (indCopyCount H₂ᶜ F_G : ℝ) ≤
        (ε ^ d' * (Fintype.card U_type : ℝ)) ^ (Fintype.card W₂) →
      ∃ S : Finset U_type, IsEpsRestrictedOn F_G S ε ∧
        ε ^ d' * (Fintype.card U_type : ℝ) ≤ (S.card : ℝ))
    (G : SimpleGraph V) (hG₁ : IsInducedSubgraphFree G H₁ᶜ) (hG₂ : IsInducedSubgraphFree G H₂ᶜ)
    (F' : Finset V) (_hF'_ne : F'.Nonempty)
    (y : ℝ) (hy0 : 0 < y) (hy_half : y < 1 / 2)
    (hy_F' : 1 ≤ y * (F'.card : ℝ))
    (hcosparse : IsEpsSparseOn Gᶜ F' y) :
    (∃ U ⊆ F', IsEpsRestrictedOn G U (y ^ 4) ∧
      y ^ (4 * d' + 1) * (F'.card : ℝ) ≤ (U.card : ℝ)) ∨
    (∃ X ⊆ F', ∃ Y ⊆ F', Disjoint X Y ∧
      y ^ (4 * d' * ((Fintype.card W₁ - 1 : ℕ) : ℝ) + 1) * (F'.card : ℝ) < (X.card : ℝ) ∧
      (1 - (Fintype.card W₁ : ℝ) * y) * (F'.card : ℝ) ≤ (Y.card : ℝ) ∧
      IsCompletePair G X Y) := by
  classical
  let s_card : ℕ := ⌈y * (F'.card : ℝ)⌉₊
  have hs_le_F' : s_card ≤ F'.card := by
    apply Nat.ceil_le.mpr
    calc y * (F'.card : ℝ) ≤ (1 / 2 : ℝ) * (F'.card : ℝ) :=
        mul_le_mul_of_nonneg_right hy_half.le (Nat.cast_nonneg _)
      _ ≤ (F'.card : ℝ) := by linarith [(Nat.cast_nonneg F'.card : (0 : ℝ) ≤ (F'.card : ℝ))]
  have hs_pos : 1 ≤ s_card := Nat.ceil_pos.mpr (by positivity)
  obtain ⟨S, hSF', hS_card⟩ := exists_subset_card_eq hs_le_F'
  have hS_ne : S.Nonempty := card_pos.mp (by omega)
  have hy_S : y * (F'.card : ℝ) ≤ (S.card : ℝ) := by
    rw [hS_card]
    exact Nat.le_ceil _
  have hy4_pos : 0 < y ^ 4 := by positivity
  have hy4_half : y ^ 4 < 1 / 2 := by
    calc y ^ 4 < (1 / 2 : ℝ) ^ 4 := pow_lt_pow_left₀ hy_half hy0.le (by norm_num)
      _ < 1 / 2 := by norm_num
  rcases viral_extension_core_of_not_restricted H₁ H₂ v₀ u₀ hu₀_ne hleaf hh hd' hviral
      G hG₁ hG₂ S hS_ne (y ^ 4) hy4_pos hy4_half with
    ⟨U, hUS, hU_rest, hU_card⟩ | ⟨Φ, hΦS, D, hDS, hΦ_card, hdisj_ΦD, hD_card, hD_ext⟩
  · left
    refine ⟨U, hUS.trans hSF', hU_rest, ?_⟩
    have hy_pow : (y ^ 4) ^ d' * y = y ^ (4 * d' + 1) := by
      rw [← Real.rpow_natCast y 4, ← Real.rpow_mul hy0.le, ← Real.rpow_add_one hy0.ne']
      push_cast
      rfl
    calc y ^ (4 * d' + 1) * (F'.card : ℝ)
      _ = (y ^ 4) ^ d' * (y * (F'.card : ℝ)) := by rw [← hy_pow]; ring
      _ ≤ (y ^ 4) ^ d' * (S.card : ℝ) := mul_le_mul_of_nonneg_left hy_S (by positivity)
      _ ≤ (U.card : ℝ) := hU_card
  · right
    let BadExt : Finset V := Φ.biUnion (fun z => neighborFinsetIn Gᶜ z F')
    let Y : Finset V := (F' \ S) \ BadExt
    have hYF' : Y ⊆ F' := sdiff_subset.trans sdiff_subset
    have hdisj_DY : Disjoint D Y := by
      rw [Finset.disjoint_left]
      intro u huD huY
      exact (mem_sdiff.mp (mem_sdiff.mp huY).1).2 (hDS huD)
    have hcomp_DY : IsCompletePair G D Y := by
      intro u huD v hvY
      have hv_not_S : v ∉ S := (mem_sdiff.mp (mem_sdiff.mp hvY).1).2
      have hv_F' : v ∈ F' := (mem_sdiff.mp (mem_sdiff.mp hvY).1).1
      have hv_not_Bad : v ∉ BadExt := (mem_sdiff.mp hvY).2
      have hv_not_Φ : v ∉ Φ := fun hvΦ => hv_not_S (hΦS hvΦ)
      have hv_ne_u : v ≠ u := fun h => hv_not_S (h ▸ hDS huD)
      refine hD_ext u huD v hv_not_Φ hv_ne_u ?_
      intro z hzΦ
      have hne_zv : z ≠ v := fun h => hv_not_Φ (h ▸ hzΦ)
      by_contra hnad_zv
      have hadj_c : Gᶜ.Adj z v := ⟨hne_zv, hnad_zv⟩
      exact hv_not_Bad (mem_biUnion.mpr ⟨z, hzΦ,
        (mem_neighborFinsetIn' Gᶜ z v F').mpr ⟨hv_F', hadj_c⟩⟩)
    have hBad_card : (BadExt.card : ℝ) ≤ ((Fintype.card W₁ - 2 : ℕ) : ℝ) * (y * (F'.card : ℝ)) := by
      have hnat : BadExt.card ≤ ∑ z ∈ Φ, (neighborFinsetIn Gᶜ z F').card := card_biUnion_le
      calc (BadExt.card : ℝ)
        _ ≤ ∑ z ∈ Φ, ((neighborFinsetIn Gᶜ z F').card : ℝ) := by exact_mod_cast hnat
        _ ≤ ∑ _z ∈ Φ, y * (F'.card : ℝ) :=
          sum_le_sum (fun z hz => hcosparse z (hSF' (hΦS hz)))
        _ = (Φ.card : ℝ) * (y * (F'.card : ℝ)) := by rw [sum_const, nsmul_eq_mul]
        _ ≤ ((Fintype.card W₁ - 2 : ℕ) : ℝ) * (y * (F'.card : ℝ)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hΦ_card) (by positivity)
    have hY_card : (1 - (Fintype.card W₁ : ℝ) * y) * (F'.card : ℝ) ≤ (Y.card : ℝ) := by
      have hsub : F' ⊆ Y ∪ S ∪ BadExt := by
        intro v hv
        by_cases hvS : v ∈ S
        · exact mem_union_left _ (mem_union_right _ hvS)
        · by_cases hvB : v ∈ BadExt
          · exact mem_union_right _ hvB
          · exact mem_union_left _ (mem_union_left _ (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hv, hvS⟩, hvB⟩))
      have hnat : F'.card ≤ Y.card + S.card + BadExt.card :=
        (card_le_card hsub).trans ((card_union_le _ _).trans
          (Nat.add_le_add_right (card_union_le _ _) _))
      have hreal : (F'.card : ℝ) ≤ (Y.card : ℝ) + (S.card : ℝ) + (BadExt.card : ℝ) := by
        exact_mod_cast hnat
      have hS_lt : (S.card : ℝ) < y * (F'.card : ℝ) + 1 := by
        rw [hS_card]
        exact Nat.ceil_lt_add_one (by positivity)
      have hS_le_2y : (S.card : ℝ) ≤ 2 * (y * (F'.card : ℝ)) := by linarith
      have hW₁_sub : ((Fintype.card W₁ - 2 : ℕ) : ℝ) + 2 = (Fintype.card W₁ : ℝ) := by
        have : (Fintype.card W₁ - 2) + 2 = Fintype.card W₁ := by omega
        exact_mod_cast this
      nlinarith
    have hD_gt : y ^ (4 * d' * ((Fintype.card W₁ - 1 : ℕ) : ℝ) + 1) * (F'.card : ℝ) <
        (D.card : ℝ) := by
      have hy_pow : (y ^ 4) ^ (d' * ((Fintype.card W₁ - 1 : ℕ) : ℝ)) * y =
          y ^ (4 * d' * ((Fintype.card W₁ - 1 : ℕ) : ℝ) + 1) := by
        rw [← Real.rpow_natCast y 4, ← Real.rpow_mul hy0.le, ← Real.rpow_add_one hy0.ne']
        congr 1; ring
      calc y ^ (4 * d' * ((Fintype.card W₁ - 1 : ℕ) : ℝ) + 1) * (F'.card : ℝ)
        _ = (y ^ 4) ^ (d' * ((Fintype.card W₁ - 1 : ℕ) : ℝ)) * (y * (F'.card : ℝ)) := by
          rw [← hy_pow]; ring
        _ ≤ (y ^ 4) ^ (d' * ((Fintype.card W₁ - 1 : ℕ) : ℝ)) * (S.card : ℝ) :=
          mul_le_mul_of_nonneg_left hy_S (by positivity)
        _ < (D.card : ℝ) := hD_card
    exact ⟨D, hDS.trans hSF', Y, hYF', hdisj_DY, hD_gt, hY_card, hcomp_DY⟩

/-!
### Section 5C: Lemma 7(1) — Deduction of Coupled Generalized Niceness from Stage-1 Comb Dichotomy
(`pair_coupled_generalized_nice_of_comb_dichotomy` and `coupled_generalized_nice_of_comb_dichotomy`,
`main.tex` lines 288–331)
-/

/--
Explicit-constant formulation of two-graph coupled generalized niceness (`IsPairCoupledGeneralizedNice H₁ H₂`
at explicit positive constants $c_1, \dots, c_9$).
-/
def SatisfiesPairCoupledGenNiceAt {W₁ W₂ : Type*} (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂)
    (c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ : ℝ) : Prop :=
  0 < c₁ ∧ 0 < c₂ ∧ 0 < c₃ ∧ 0 < c₄ ∧ 0 < c₅ ∧ 0 < c₆ ∧ 0 < c₇ ∧ 0 < c₈ ∧ 0 < c₉ ∧
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (ε x_sp : ℝ),
    0 < ε → ε < 1 / 2 →
    ε ^ (3 * c₂) ≤ x_sp → x_sp ≤ ε ^ c₇ →
    IsInducedSubgraphFree G H₁ᶜ → IsInducedSubgraphFree G H₂ᶜ →
      (∃ B : Fin ⌈ε⁻¹⌉₊ → Finset V,
        IsWeaklySparseOrCoSparseBlockadeIn G Finset.univ ⌈ε⁻¹⌉₊
          (⌊ε ^ c₁ * (Fintype.card V : ℝ)⌋₊ : ℝ) x_sp B) ∨
      ((ε ^ c₃ * x_sp ^ c₃ * (Fintype.card V : ℝ)) ^ c₄ ≤ (kappa G : ℝ)) ∨
      (∃ k : ℕ, ⌈ε ^ (-c₆)⌉₊ ≤ k ∧ k ≤ ⌈ε ^ (-c₉)⌉₊ ∧
        ∃ B : Fin k → Finset V,
          IsPureCographBlockadeIn G Finset.univ k ((Fintype.card V : ℝ) / (k : ℝ) ^ c₅) B) ∨
      (∃ S : Finset V, IsEpsRestrictedOn G S (2 * ε ^ c₇) ∧
        ε ^ c₈ * (Fintype.card V : ℝ) ≤ (S.card : ℝ))

theorem SatisfiesPairCoupledGenNiceAt.to_isPairCoupledGeneralizedNice
    {W₁ W₂ : Type*} {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂}
    {c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ : ℝ}
    (h : SatisfiesPairCoupledGenNiceAt H₁ H₂ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉) :
    IsPairCoupledGeneralizedNice H₁ H₂ :=
  ⟨c₁, c₂, c₃, c₄, c₅, c₆, c₇, c₈, c₉, h⟩

theorem isCoupledGeneralizedNice_of_pair {W : Type*} {H : SimpleGraph W}
    (h : IsPairCoupledGeneralizedNice H H) :
    IsCoupledGeneralizedNice H := by
  obtain ⟨c₁, c₂, c₃, c₄, c₅, c₆, c₇, c₈, c₉, hc₁, hc₂, hc₃, hc₄, hc₅, hc₆, hc₇, hc₈, hc₉, hprop⟩ := h
  refine ⟨c₁, c₂, c₃, c₄, c₅, c₆, c₇, c₈, c₉, hc₁, hc₂, hc₃, hc₄, hc₅, hc₆, hc₇, hc₈, hc₉, ?_⟩
  intro V _ _ G ε x_sp hε0 hε_half hx_lo hx_hi hG
  exact hprop V G ε x_sp hε0 hε_half hx_lo hx_hi hG hG

/-- Every pairwise-pure blockade is weakly $x$-sparse-or-co-sparse for any $x \ge 0$. -/
theorem isWeaklySparseOrCoSparseBlockadeIn_of_isPureBlockadeIn
    {G : SimpleGraph V} {S : Finset V} {k : ℕ} {w x : ℝ} {B : Fin k → Finset V}
    (hx : 0 ≤ x) (hB : IsPureBlockadeIn G S k w B) :
    IsWeaklySparseOrCoSparseBlockadeIn G S k w x B := by
  refine ⟨hB.1, fun i j hij => ?_⟩
  rcases hB.2 i j hij with hcomp | hanti
  · right
    have h0 : IsXSparseTo Gᶜ (B i) (B j) 0 := by
      intro u hu
      have hemp : neighborFinsetIn Gᶜ u (B j) = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        intro v hv
        rw [mem_neighborFinsetIn', SimpleGraph.compl_adj] at hv
        exact hv.2.2 (hcomp u hu v hv.1)
      rw [hemp]
      simp
    exact (isWeaklySparsePair_of_isXSparseTo h0).mono hx
  · left
    have h0 : IsXSparseTo G (B i) (B j) 0 := by
      intro u hu
      have hemp : neighborFinsetIn G u (B j) = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        intro v hv
        rw [mem_neighborFinsetIn'] at hv
        exact hanti u hu v hv.1 hv.2
      rw [hemp]
      simp
    exact (isWeaklySparsePair_of_isXSparseTo h0).mono hx

theorem IsWeaklySparseOrCoSparseBlockadeIn.mono_sub_width_defect
    {G : SimpleGraph V} {F' F : Finset V} {k : ℕ} {w₁ w₂ x₁ x₂ : ℝ} {B : Fin k → Finset V}
    (hB : IsWeaklySparseOrCoSparseBlockadeIn G F' k w₁ x₁ B)
    (hsub : F' ⊆ F) (hw : w₂ ≤ w₁) (hx : x₁ ≤ x₂) :
    IsWeaklySparseOrCoSparseBlockadeIn G F k w₂ x₂ B := by
  refine ⟨(hB.1.mono_ambient hsub).mono_width hw, fun i j hij => ?_⟩
  rcases hB.2 i j hij with h1 | h2
  · exact Or.inl (h1.mono hx)
  · exact Or.inr (h2.mono hx)

/--
**Markov Pointwise Sparsity Restoration to Exact Size $w_1$ (`markov_pointwise_sparse_exact_size`,
`main.tex` lines 319–323)**:
Given disjoint $X_0, Y_0 \subseteq F'$ with $|X_0| \ge w_1 \ge 1$, $|Y_0| \ge (1 - 4y)|F'|$, and
$Y_0$ pointwise $x_{\mathrm{in}}^2$-sparse to $X_0$ in $G$ (where $0 < x_{\mathrm{in}} \le y$ and
$b_{\mathrm{leaf}} \ge 5$), averaging over $w_1$-element subsets of $X_0$ and pruning $Y_0$ by Markov's
inequality yields disjoint $X \subseteq X_0$ and $Y \subseteq Y_0$ with $|X| = w_1$,
$|Y| \ge (1 - b_{\mathrm{leaf}} y)|F'|$, and $Y$ pointwise $x_{\mathrm{in}}$-sparse to $X$ in $G$.
-/
theorem markov_pointwise_sparse_exact_size (G : SimpleGraph V) (F' X₀ Y₀ : Finset V)
    (w₁ : ℕ) (x_in y b_leaf : ℝ)
    (hw₁_pos : 1 ≤ w₁) (hw₁_le : w₁ ≤ X₀.card)
    (hx_pos : 0 < x_in) (hxy : x_in ≤ y) (hb_leaf : 5 ≤ b_leaf)
    (hX₀F' : X₀ ⊆ F') (hY₀F' : Y₀ ⊆ F') (hdisj : Disjoint X₀ Y₀)
    (hY₀_card : (1 - 4 * y) * (F'.card : ℝ) ≤ (Y₀.card : ℝ))
    (hsparse : IsXSparseTo G Y₀ X₀ (x_in ^ 2)) :
    ∃ X ⊆ F', ∃ Y ⊆ F', Disjoint X Y ∧
      X.card = w₁ ∧
      (1 - b_leaf * y) * (F'.card : ℝ) ≤ (Y.card : ℝ) ∧
      IsXSparseTo G Y X x_in := by
  classical
  have hX₀_pos : (0 : ℝ) < (X₀.card : ℝ) := by
    have : 0 < X₀.card := by omega
    exact_mod_cast this
  have hw₁_pos_real : (0 : ℝ) < (w₁ : ℝ) := by exact_mod_cast hw₁_pos
  let wt : V → ℝ := fun x => ((neighborFinsetIn G x Y₀).card : ℝ)
  obtain ⟨X, hXX₀, hX_card, hX_sum⟩ :=
    exists_subset_card_eq_sum_le X₀ wt (fun _ _ => Nat.cast_nonneg _) w₁ hw₁_le
  have hcross_X₀Y₀ : (crossEdgeCount G X₀ Y₀ : ℝ) ≤ x_in ^ 2 * (Y₀.card : ℝ) * (X₀.card : ℝ) := by
    rw [crossEdgeCount_comm' G X₀ Y₀]
    exact isWeaklySparsePair_of_isXSparseTo hsparse
  have hcross_Y₀X : (crossEdgeCount G Y₀ X : ℝ) ≤ x_in ^ 2 * (Y₀.card : ℝ) * (w₁ : ℝ) := by
    have hsum_X : ∑ x ∈ X, wt x = (crossEdgeCount G X Y₀ : ℝ) := by
      dsimp [wt]
      exact_mod_cast (crossEdgeCount_eq_sum_left G X Y₀).symm
    have hsum_X₀ : ∑ x ∈ X₀, wt x = (crossEdgeCount G X₀ Y₀ : ℝ) := by
      dsimp [wt]
      exact_mod_cast (crossEdgeCount_eq_sum_left G X₀ Y₀).symm
    have hmul : (X₀.card : ℝ) * (crossEdgeCount G Y₀ X : ℝ) ≤
        (X₀.card : ℝ) * (x_in ^ 2 * (Y₀.card : ℝ) * (w₁ : ℝ)) := by
      calc (X₀.card : ℝ) * (crossEdgeCount G Y₀ X : ℝ)
        _ = (X₀.card : ℝ) * (crossEdgeCount G X Y₀ : ℝ) := by rw [crossEdgeCount_comm' G Y₀ X]
        _ = (X₀.card : ℝ) * (∑ x ∈ X, wt x) := by rw [hsum_X]
        _ ≤ (w₁ : ℝ) * (∑ x ∈ X₀, wt x) := hX_sum
        _ = (w₁ : ℝ) * (crossEdgeCount G X₀ Y₀ : ℝ) := by rw [hsum_X₀]
        _ ≤ (w₁ : ℝ) * (x_in ^ 2 * (Y₀.card : ℝ) * (X₀.card : ℝ)) :=
          mul_le_mul_of_nonneg_left hcross_X₀Y₀ hw₁_pos_real.le
        _ = (X₀.card : ℝ) * (x_in ^ 2 * (Y₀.card : ℝ) * (w₁ : ℝ)) := by ring
    exact le_of_mul_le_mul_left hmul hX₀_pos
  let Y : Finset V := Y₀.filter (fun u => ((neighborFinsetIn G u X).card : ℝ) ≤ x_in * (X.card : ℝ))
  let Z_bad : Finset V :=
    Y₀.filter (fun u => ¬(((neighborFinsetIn G u X).card : ℝ) ≤ x_in * (X.card : ℝ)))
  have hpart_Y₀ : (Y.card : ℝ) + (Z_bad.card : ℝ) = (Y₀.card : ℝ) := by
    exact_mod_cast card_filter_add_card_filter_not
      (fun u => ((neighborFinsetIn G u X).card : ℝ) ≤ x_in * (X.card : ℝ))
  have hZ_bad_le : (Z_bad.card : ℝ) ≤ y * (F'.card : ℝ) := by
    have hsum_Z : (Z_bad.card : ℝ) * (x_in * (w₁ : ℝ)) ≤ (crossEdgeCount G Y₀ X : ℝ) := by
      have h1 : (Z_bad.card : ℝ) * (x_in * (w₁ : ℝ)) ≤
          ∑ u ∈ Z_bad, ((neighborFinsetIn G u X).card : ℝ) := by
        rw [← nsmul_eq_mul, ← sum_const]
        refine sum_le_sum (fun u hu => ?_)
        have hnot := (mem_filter.mp hu).2
        push_neg at hnot
        rw [hX_card] at hnot
        exact hnot.le
      have h2 : ∑ u ∈ Z_bad, ((neighborFinsetIn G u X).card : ℝ) ≤
          ∑ u ∈ Y₀, ((neighborFinsetIn G u X).card : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.cast_nonneg _)
      have h3 : (∑ u ∈ Y₀, ((neighborFinsetIn G u X).card : ℝ)) = (crossEdgeCount G Y₀ X : ℝ) := by
        exact_mod_cast (crossEdgeCount_eq_sum_left G Y₀ X).symm
      exact h1.trans (h2.trans_eq h3)
    have hmul_Z : (x_in * (w₁ : ℝ)) * (Z_bad.card : ℝ) ≤
        (x_in * (w₁ : ℝ)) * (x_in * (Y₀.card : ℝ)) := by
      calc (x_in * (w₁ : ℝ)) * (Z_bad.card : ℝ)
        _ = (Z_bad.card : ℝ) * (x_in * (w₁ : ℝ)) := mul_comm _ _
        _ ≤ (crossEdgeCount G Y₀ X : ℝ) := hsum_Z
        _ ≤ x_in ^ 2 * (Y₀.card : ℝ) * (w₁ : ℝ) := hcross_Y₀X
        _ = (x_in * (w₁ : ℝ)) * (x_in * (Y₀.card : ℝ)) := by ring
    have hZ_xin : (Z_bad.card : ℝ) ≤ x_in * (Y₀.card : ℝ) :=
      le_of_mul_le_mul_left hmul_Z (mul_pos hx_pos hw₁_pos_real)
    have hY₀_le_F' : (Y₀.card : ℝ) ≤ (F'.card : ℝ) := by exact_mod_cast card_le_card hY₀F'
    calc (Z_bad.card : ℝ)
      _ ≤ x_in * (Y₀.card : ℝ) := hZ_xin
      _ ≤ y * (F'.card : ℝ) := mul_le_mul hxy hY₀_le_F' (Nat.cast_nonneg _) (hx_pos.le.trans hxy)
  have hY_card : (1 - b_leaf * y) * (F'.card : ℝ) ≤ (Y.card : ℝ) := by
    have hy_nonneg : 0 ≤ y := hx_pos.le.trans hxy
    have hF'_nonneg : (0 : ℝ) ≤ (F'.card : ℝ) := Nat.cast_nonneg _
    have h5_le_b : 5 * y * (F'.card : ℝ) ≤ b_leaf * y * (F'.card : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb_leaf hy_nonneg) hF'_nonneg
    linarith
  refine ⟨X, hXX₀.trans hX₀F', Y, (filter_subset _ _).trans hY₀F',
    Disjoint.mono hXX₀ (filter_subset _ _) hdisj, hX_card, hY_card, ?_⟩
  intro u hu
  exact (mem_filter.mp hu).2

/--
Calibrated degree exponent $d$ for Lemma 7(1) (`main.tex` line 304).
-/
noncomputable def symmGenNiceD (a_leaf b_leaf C_comb c_B δ : ℝ) : ℝ :=
  let b₂ := b2Param a_leaf (2 * b_leaf) δ
  max 120 (C_comb + a_leaf + 100 * (b_leaf + 2) * (b₂ + 2) + 32 * b₂ / c_B +
    2 * (⌈Real.log (1 / δ) / Real.log 2⌉₊ : ℝ))

theorem one_hundred_twenty_le_symmGenNiceD (a_leaf b_leaf C_comb c_B δ : ℝ) :
    120 ≤ symmGenNiceD a_leaf b_leaf C_comb c_B δ :=
  le_max_left _ _

private theorem eps_rpow_le_two_rpow_neg {ε e : ℝ} (hε0 : 0 ≤ ε) (hε_half : ε < 1 / 2)
    (he : 0 ≤ e) :
    ε ^ e ≤ (2 : ℝ) ^ (-e) := by
  have h1 : ε ≤ (2 : ℝ) ^ (-1 : ℝ) := by
    rw [Real.rpow_neg_one]
    have : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
    linarith
  calc ε ^ e ≤ ((2 : ℝ) ^ (-1 : ℝ)) ^ e := Real.rpow_le_rpow hε0 h1 he
    _ = (2 : ℝ) ^ (-e) := by rw [← Real.rpow_mul (by norm_num)]; congr 1; ring

private theorem bLeaf_two_mul_eq {b_leaf : ℝ} (hb : 6 ≤ b_leaf) :
    bLeaf (2 * b_leaf) = 2 * b_leaf :=
  max_eq_left (by linarith)

private theorem cParam_two_mul_eq {b_leaf : ℝ} (hb : 6 ≤ b_leaf) :
    cParam (2 * b_leaf) = (2 : ℝ) ^ (-8 * b_leaf) := by
  unfold cParam
  rw [bLeaf_two_mul_eq hb]
  congr 1; ring

private theorem lambda0Param_two_mul_eq {b_leaf : ℝ} (hb : 6 ≤ b_leaf) :
    lambda0Param (2 * b_leaf) = (2 : ℝ) ^ (-80 * b_leaf) := by
  unfold lambda0Param
  rw [cParam_two_mul_eq hb, ← Real.rpow_mul (by norm_num)]
  congr 1; ring

private theorem rodl_initial_step_for_symm_gen_nice {W₁ : Type*} [Fintype W₁] [DecidableEq W₁]
    (G : SimpleGraph V) (H₁ : SimpleGraph W₁) (hG₁ : IsInducedSubgraphFree G H₁ᶜ)
    (F : Finset V) (a_leaf b_leaf : ℝ) :
    let lam0 := lambda0Param (2 * b_leaf)
    let δ := symmRodlDeltaGen (Fintype.card W₁) lam0
    let b₂ := b2Param a_leaf (2 * b_leaf) δ
    ∃ F₀ ⊆ F, IsEpsRestrictedOn G F₀ lam0 ∧
      lam0 ^ b₂ * (F.card : ℝ) ≤ (F₀.card : ℝ) := by
  intro lam0 δ b₂
  have hlam0_pos : 0 < lam0 := lambda0Param_pos (2 * b_leaf)
  have hlam0_half : lam0 < 1 / 2 := lambda0Param_lt_half (2 * b_leaf)
  have hδ_pos : 0 < δ := rodlDeltaGen_pos (Fintype.card W₁) hlam0_pos
  obtain ⟨F₀, hF₀_sub, hF₀_rest, hF₀_card⟩ :=
    rodl_theorem_general G H₁ᶜ hG₁ lam0 hlam0_pos hlam0_half F
  refine ⟨F₀, hF₀_sub, hF₀_rest, ?_⟩
  have hb₂_ceil : (⌈Real.log (1 / δ) / Real.log (1 / lam0)⌉₊ : ℝ) ≤ b₂ := le_max_right _ _
  have hdiv_le : Real.log (1 / δ) / Real.log (1 / lam0) ≤ b₂ :=
    (Nat.le_ceil _).trans hb₂_ceil
  have h1_lt_inv : 1 < 1 / lam0 := one_lt_one_div hlam0_pos (by linarith)
  have hlog_inv_pos : 0 < Real.log (1 / lam0) := Real.log_pos h1_lt_inv
  have hmul : Real.log (1 / δ) ≤ b₂ * Real.log (1 / lam0) :=
    (div_le_iff₀ hlog_inv_pos).mp hdiv_le
  rw [one_div, one_div, Real.log_inv, Real.log_inv] at hmul
  have hlog_le : Real.log (lam0 ^ b₂) ≤ Real.log δ := by
    rw [Real.log_rpow hlam0_pos]
    linarith
  have hpow_le : lam0 ^ b₂ ≤ δ :=
    (Real.log_le_log_iff (Real.rpow_pos_of_pos hlam0_pos b₂) hδ_pos).mp hlog_le
  exact (mul_le_mul_of_nonneg_right hpow_le (Nat.cast_nonneg _)).trans hF₀_card

private theorem localSparsityY_ge_eps_sq (b_leaf : ℝ) {ε lam : ℝ}
    (hε0 : 0 < ε) (hlam_ge : cParam (2 * b_leaf) * ε ^ (6 : ℝ) ≤ lam) :
    ε ^ 2 ≤ localSparsityY (2 * b_leaf) lam := by
  unfold localSparsityY
  have hc_pos : 0 < cParam (2 * b_leaf) := cParam_pos (2 * b_leaf)
  have hdiv : ε ^ (6 : ℝ) ≤ lam / cParam (2 * b_leaf) := by
    rw [le_div_iff₀ hc_pos, mul_comm]
    exact hlam_ge
  calc ε ^ 2
    _ = (ε ^ (6 : ℝ)) ^ ((1 : ℝ) / 3) := by
      rw [← Real.rpow_mul hε0.le, show (6 : ℝ) * (1 / 3) = ((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
    _ ≤ (lam / cParam (2 * b_leaf)) ^ ((1 : ℝ) / 3) :=
      Real.rpow_le_rpow (by positivity) hdiv (by positivity)

private theorem ceil_inv_localSparsityY_le_kmax (b_leaf : ℝ) {ε lam d C_cap : ℝ}
    (hε0 : 0 < ε) (hε_half : ε < 1 / 2) (hd : 120 ≤ d) (hC_cap : 2 ≤ C_cap)
    (hlam_ge : cParam (2 * b_leaf) * ε ^ (6 : ℝ) ≤ lam) :
    ⌈(localSparsityY (2 * b_leaf) lam)⁻¹⌉₊ ≤ ⌈ε ^ (-20 * d * C_cap)⌉₊ := by
  have hy_ge : ε ^ 2 ≤ localSparsityY (2 * b_leaf) lam :=
    localSparsityY_ge_eps_sq b_leaf hε0 hlam_ge
  have hε1 : ε ≤ 1 := by linarith
  have hinv : (localSparsityY (2 * b_leaf) lam)⁻¹ ≤ ε ^ (-20 * d * C_cap) := by
    calc (localSparsityY (2 * b_leaf) lam)⁻¹
      _ ≤ (ε ^ 2)⁻¹ := inv_anti₀ (by positivity) hy_ge
      _ = ε ^ (-2 : ℝ) := by
        rw [← Real.rpow_natCast ε 2, ← Real.rpow_neg hε0.le]
        norm_num
      _ ≤ ε ^ (-20 * d * C_cap) :=
        Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (by nlinarith)
  exact Nat.ceil_mono hinv

private theorem lam_b3Param_le_cParam_mul_y_rpow {a_leaf b_leaf lam : ℝ}
    (ha_leaf : 6 ≤ a_leaf) (hlam0 : 0 ≤ lam) (hlam_le : lam ≤ lambda0Param (2 * b_leaf)) :
    lam ^ (b3Param a_leaf) ≤
      cParam (2 * b_leaf) * (localSparsityY (2 * b_leaf) lam) ^ a_leaf := by
  set c := cParam (2 * b_leaf)
  set y := localSparsityY (2 * b_leaf) lam
  have hc_pos : 0 < c := cParam_pos (2 * b_leaf)
  have hc_le1 : c ≤ 1 := (cParam_lt_half (2 * b_leaf)).le.trans (by norm_num)
  have hy_nonneg : 0 ≤ y := by unfold y localSparsityY; positivity
  have hy_le1 : y ≤ 1 := (localSparsityY_lt_half (2 * b_leaf) hlam0 hlam_le).le.trans (by norm_num)
  have hlam_eq : lam = c * y ^ (3 : ℝ) := (cParam_mul_localSparsityY_cube (2 * b_leaf) hlam0).symm
  have hb3_ge : a_leaf ≤ b3Param a_leaf := by
    unfold b3Param cLeaf
    have : 4 * a_leaf + 1 ≤ max (4 * a_leaf + 1) 4 := le_max_left _ _
    linarith
  have hb3_ge1 : 1 ≤ b3Param a_leaf := by linarith
  have hc_pow : c ^ (b3Param a_leaf) ≤ c := by
    calc c ^ (b3Param a_leaf) ≤ c ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hc_pos hc_le1 hb3_ge1
      _ = c := Real.rpow_one c
  have hy_pow : (y ^ (3 : ℝ)) ^ (b3Param a_leaf) ≤ y ^ a_leaf := by
    rw [← Real.rpow_mul hy_nonneg]
    rcases eq_or_lt_of_le hy_nonneg with hy0 | hy_pos
    · rw [← hy0, Real.zero_rpow (by linarith), Real.zero_rpow (by linarith)]
    · exact Real.rpow_le_rpow_of_exponent_ge hy_pos hy_le1 (by linarith)
  rw [hlam_eq, Real.mul_rpow hc_pos.le (by positivity)]
  exact mul_le_mul hc_pow hy_pow (by positivity) hc_pos.le

private theorem symmGenNiceD_ge_comb_terms (a_leaf b_leaf C_comb c_B δ : ℝ) :
    C_comb + a_leaf + 100 * (b_leaf + 2) * (b2Param a_leaf (2 * b_leaf) δ + 2) +
      32 * b2Param a_leaf (2 * b_leaf) δ / c_B ≤
      symmGenNiceD a_leaf b_leaf C_comb c_B δ := by
  have h1 : C_comb + a_leaf + 100 * (b_leaf + 2) * (b2Param a_leaf (2 * b_leaf) δ + 2) +
      32 * b2Param a_leaf (2 * b_leaf) δ / c_B +
      2 * (⌈Real.log (1 / δ) / Real.log 2⌉₊ : ℝ) ≤
      symmGenNiceD a_leaf b_leaf C_comb c_B δ :=
    le_max_right _ _
  have hceil : 0 ≤ (⌈Real.log (1 / δ) / Real.log 2⌉₊ : ℝ) := Nat.cast_nonneg _
  linarith

private theorem symm_gen_nice_terminal_card_ge {a_leaf b_leaf C_comb C_cap c_B δ ε : ℝ}
    (ha_leaf : 6 ≤ a_leaf) (hb_leaf : 6 ≤ b_leaf) (hC_comb : 18 ≤ C_comb)
    (hC_cap : 2 ≤ C_cap) (hc_B : 0 < c_B) (hε0 : 0 < ε) (hε_half : ε < 1 / 2)
    {S F F₀ : Finset V}
    (hF : ε ^ (symmGenNiceD a_leaf b_leaf C_comb c_B δ) * (S.card : ℝ) ≤ (F.card : ℝ))
    (hF₀ : (lambda0Param (2 * b_leaf)) ^ (b2Param a_leaf (2 * b_leaf) δ) *
      (F.card : ℝ) ≤ (F₀.card : ℝ)) :
    let d := symmGenNiceD a_leaf b_leaf C_comb c_B δ
    let c₈ := (20 * C_cap + 4) * d ^ 2
    let lam_cut := cParam (2 * b_leaf) * ε ^ (6 : ℝ)
    let b₂ := b2Param a_leaf (2 * b_leaf) δ
    ε ^ c₈ * (S.card : ℝ) ≤ lam_cut ^ (b1Param * b₂) * (F₀.card : ℝ) ∧
    ε ^ c₈ * (S.card : ℝ) ≤ (F₀.card : ℝ) := by
  intro d c₈ lam_cut b₂
  have hε1 : ε ≤ 1 := by linarith
  have hc_pos : 0 < cParam (2 * b_leaf) := cParam_pos _
  have hlam0_pos : 0 < lambda0Param (2 * b_leaf) := lambda0Param_pos _
  have hlam_cut_pos : 0 < lam_cut := by dsimp [lam_cut]; positivity
  have hb₂_pos : 0 < b₂ := b2Param_pos a_leaf (2 * b_leaf) δ
  have hd_ge := symmGenNiceD_ge_comb_terms a_leaf b_leaf C_comb c_B δ
  have hd120 : 120 ≤ d := one_hundred_twenty_le_symmGenNiceD a_leaf b_leaf C_comb c_B δ
  have h32_pos : 0 ≤ 32 * b₂ / c_B := by positivity
  have hc_ge : ε ^ (8 * b_leaf) ≤ cParam (2 * b_leaf) := by
    rw [cParam_two_mul_eq hb_leaf, show (-8 * b_leaf : ℝ) = -(8 * b_leaf) by ring]
    exact eps_rpow_le_two_rpow_neg hε0.le hε_half (by linarith)
  have hlam0_ge : ε ^ (80 * b_leaf) ≤ lambda0Param (2 * b_leaf) := by
    rw [lambda0Param_two_mul_eq hb_leaf, show (-80 * b_leaf : ℝ) = -(80 * b_leaf) by ring]
    exact eps_rpow_le_two_rpow_neg hε0.le hε_half (by linarith)
  have hlam_cut_ge : ε ^ (8 * b_leaf + 6) ≤ lam_cut := by
    dsimp [lam_cut]
    rw [Real.rpow_add hε0]
    exact mul_le_mul_of_nonneg_right hc_ge (by positivity)
  have hlam0_b2_ge : ε ^ (80 * b_leaf * b₂) ≤ (lambda0Param (2 * b_leaf)) ^ b₂ := by
    rw [Real.rpow_mul hε0.le]
    exact Real.rpow_le_rpow (by positivity) hlam0_ge hb₂_pos.le
  have hlam_cut_b1b2_ge : ε ^ ((8 * b_leaf + 6) * b1Param * b₂) ≤ lam_cut ^ (b1Param * b₂) := by
    rw [show (8 * b_leaf + 6) * b1Param * b₂ = (8 * b_leaf + 6) * (b1Param * b₂) by ring,
      Real.rpow_mul hε0.le]
    exact Real.rpow_le_rpow (by positivity) hlam_cut_ge (by unfold b1Param; positivity)
  have hexp_F₀ : 80 * b_leaf * b₂ + d ≤ c₈ := by
    dsimp [c₈]
    nlinarith
  have hexp_cut : (8 * b_leaf + 6) * b1Param * b₂ + 80 * b_leaf * b₂ + d ≤ c₈ := by
    dsimp [c₈]
    unfold b1Param
    nlinarith
  have hF₀_bound : ε ^ c₈ * (S.card : ℝ) ≤ (F₀.card : ℝ) := by
    have hrpow : ε ^ c₈ ≤ (lambda0Param (2 * b_leaf)) ^ b₂ * ε ^ d := by
      calc ε ^ c₈
        _ ≤ ε ^ (80 * b_leaf * b₂ + d) := Real.rpow_le_rpow_of_exponent_ge hε0 hε1 hexp_F₀
        _ = ε ^ (80 * b_leaf * b₂) * ε ^ d := Real.rpow_add hε0 _ _
        _ ≤ (lambda0Param (2 * b_leaf)) ^ b₂ * ε ^ d :=
          mul_le_mul_of_nonneg_right hlam0_b2_ge (by positivity)
    calc ε ^ c₈ * (S.card : ℝ)
      _ ≤ ((lambda0Param (2 * b_leaf)) ^ b₂ * ε ^ d) * (S.card : ℝ) :=
        mul_le_mul_of_nonneg_right hrpow (Nat.cast_nonneg _)
      _ = (lambda0Param (2 * b_leaf)) ^ b₂ * (ε ^ d * (S.card : ℝ)) := by ring
      _ ≤ (lambda0Param (2 * b_leaf)) ^ b₂ * (F.card : ℝ) :=
        mul_le_mul_of_nonneg_left hF (by positivity)
      _ ≤ (F₀.card : ℝ) := hF₀
  refine ⟨?_, hF₀_bound⟩
  have hrpow : ε ^ c₈ ≤ lam_cut ^ (b1Param * b₂) * (lambda0Param (2 * b_leaf)) ^ b₂ * ε ^ d := by
    calc ε ^ c₈
      _ ≤ ε ^ ((8 * b_leaf + 6) * b1Param * b₂ + 80 * b_leaf * b₂ + d) :=
        Real.rpow_le_rpow_of_exponent_ge hε0 hε1 hexp_cut
      _ = ε ^ ((8 * b_leaf + 6) * b1Param * b₂) * ε ^ (80 * b_leaf * b₂) * ε ^ d := by
        rw [Real.rpow_add hε0, Real.rpow_add hε0]
      _ ≤ lam_cut ^ (b1Param * b₂) * (lambda0Param (2 * b_leaf)) ^ b₂ * ε ^ d := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul hlam_cut_b1b2_ge hlam0_b2_ge (by positivity) (by positivity)
  calc ε ^ c₈ * (S.card : ℝ)
    _ ≤ (lam_cut ^ (b1Param * b₂) * (lambda0Param (2 * b_leaf)) ^ b₂ * ε ^ d) * (S.card : ℝ) :=
      mul_le_mul_of_nonneg_right hrpow (Nat.cast_nonneg _)
    _ = lam_cut ^ (b1Param * b₂) * ((lambda0Param (2 * b_leaf)) ^ b₂ * (ε ^ d * (S.card : ℝ))) := by
      ring
    _ ≤ lam_cut ^ (b1Param * b₂) * ((lambda0Param (2 * b_leaf)) ^ b₂ * (F.card : ℝ)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left hF (by positivity)
    _ ≤ lam_cut ^ (b1Param * b₂) * (F₀.card : ℝ) :=
      mul_le_mul_of_nonneg_left hF₀ (by positivity)

private theorem symm_gen_nice_peel_width_ge {a_leaf b_leaf C_comb c_B δ lam : ℝ}
    {F F₀ F_t : Finset V}
    (ha_leaf : 6 ≤ a_leaf) (hb_leaf : 6 ≤ b_leaf) (hC_comb : 18 ≤ C_comb) (hc_B : 0 < c_B)
    (hlam_pos : 0 < lam) (hlam_le : lam ≤ lambda0Param (2 * b_leaf))
    (hF₀ : (lambda0Param (2 * b_leaf)) ^ (b2Param a_leaf (2 * b_leaf) δ) *
      (F.card : ℝ) ≤ (F₀.card : ℝ))
    (hFt : lam ^ (b2Param a_leaf (2 * b_leaf) δ) * (F₀.card : ℝ) ≤ (F_t.card : ℝ))
    (hw₁_ge2 : (2 : ℝ) ≤ (localSparsityY (2 * b_leaf) lam) ^ (a_leaf + 2) * (F_t.card : ℝ)) :
    let d := symmGenNiceD a_leaf b_leaf C_comb c_B δ
    let y := localSparsityY (2 * b_leaf) lam
    let k := ⌈y⁻¹⌉₊
    let w₁ := ⌊y ^ (a_leaf + 2) * (F_t.card : ℝ)⌋₊
    (F.card : ℝ) / (k : ℝ) ^ d ≤ (w₁ : ℝ) := by
  intro d y k w₁
  have hc_pos : 0 < cParam (2 * b_leaf) := cParam_pos _
  have hlam0_pos : 0 < lambda0Param (2 * b_leaf) := lambda0Param_pos _
  have hy_pos : 0 < y := localSparsityY_pos (2 * b_leaf) hlam_pos
  have hy_48 : y ≤ (2 : ℝ) ^ (-48 : ℝ) :=
    localSparsityY_le_two_rpow_neg_48 (2 * b_leaf) hlam_pos.le hlam_le
  have hy_inv_gt2 : 2 < y⁻¹ := by
    rw [lt_inv_comm₀ zero_lt_two hy_pos]
    have h48_lt : (2 : ℝ) ^ (-48 : ℝ) < (2 : ℝ)⁻¹ := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_lt_rpow_of_exponent_lt one_lt_two (by norm_num)
    exact hy_48.trans_lt h48_lt
  have hk_ge_inv : y⁻¹ ≤ (k : ℝ) := Nat.le_ceil _
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := hy_inv_gt2.le.trans hk_ge_inv
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by linarith
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  have hy_ge_k : (k : ℝ) ^ (-1 : ℝ) ≤ y := by
    rw [Real.rpow_neg_one, ← inv_inv y]
    exact inv_anti₀ (inv_pos.mpr hy_pos) hk_ge_inv
  have hc_ge_k : (k : ℝ) ^ (-(8 * b_leaf)) ≤ cParam (2 * b_leaf) := by
    rw [cParam_two_mul_eq hb_leaf, show (-8 * b_leaf : ℝ) = -(8 * b_leaf) by ring]
    exact rpow_neg_le_two_rpow_neg hk2 (by linarith)
  have hlam0_ge_k : (k : ℝ) ^ (-(80 * b_leaf)) ≤ lambda0Param (2 * b_leaf) := by
    rw [lambda0Param_two_mul_eq hb_leaf, show (-80 * b_leaf : ℝ) = -(80 * b_leaf) by ring]
    exact rpow_neg_le_two_rpow_neg hk2 (by linarith)
  have hlam_ge_k : (k : ℝ) ^ (-(8 * b_leaf + 3)) ≤ lam := by
    have hlam_eq : lam = cParam (2 * b_leaf) * y ^ (3 : ℝ) :=
      (cParam_mul_localSparsityY_cube (2 * b_leaf) hlam_pos.le).symm
    rw [hlam_eq, show -(8 * b_leaf + 3) = -(8 * b_leaf) + -3 by ring, Real.rpow_add hk_pos]
    refine mul_le_mul hc_ge_k ?_ (by positivity) (by positivity)
    calc (k : ℝ) ^ (-3 : ℝ)
      _ = ((k : ℝ) ^ (-1 : ℝ)) ^ (3 : ℝ) := by rw [← Real.rpow_mul hk_pos.le]; norm_num
      _ ≤ y ^ (3 : ℝ) := Real.rpow_le_rpow (by positivity) hy_ge_k (by norm_num)
  set b₂ := b2Param a_leaf (2 * b_leaf) δ
  have hb₂_pos : 0 < b₂ := b2Param_pos a_leaf (2 * b_leaf) δ
  have hlam_b2_ge : (k : ℝ) ^ (-((8 * b_leaf + 3) * b₂)) ≤ lam ^ b₂ := by
    rw [show -((8 * b_leaf + 3) * b₂) = -(8 * b_leaf + 3) * b₂ by ring, Real.rpow_mul hk_pos.le]
    exact Real.rpow_le_rpow (by positivity) hlam_ge_k hb₂_pos.le
  have hlam0_b2_ge : (k : ℝ) ^ (-(80 * b_leaf * b₂)) ≤ (lambda0Param (2 * b_leaf)) ^ b₂ := by
    rw [show -(80 * b_leaf * b₂) = -(80 * b_leaf) * b₂ by ring, Real.rpow_mul hk_pos.le]
    exact Real.rpow_le_rpow (by positivity) hlam0_ge_k hb₂_pos.le
  have hy_a2_ge : (k : ℝ) ^ (-(a_leaf + 2)) ≤ y ^ (a_leaf + 2) := by
    calc (k : ℝ) ^ (-(a_leaf + 2))
      _ = ((k : ℝ) ^ (-1 : ℝ)) ^ (a_leaf + 2) := by
        rw [← Real.rpow_mul hk_pos.le]; congr 1; ring
      _ ≤ y ^ (a_leaf + 2) := Real.rpow_le_rpow (by positivity) hy_ge_k (by linarith)
  have hhalf_ge : (k : ℝ) ^ (-1 : ℝ) ≤ (1 / 2 : ℝ) := by
    have h := rpow_neg_le_two_rpow_neg hk2 zero_le_one
    rwa [show (2 : ℝ) ^ (-1 : ℝ) = 1 / 2 by norm_num] at h
  have hd_ge := symmGenNiceD_ge_comb_terms a_leaf b_leaf C_comb c_B δ
  have h32_pos : 0 ≤ 32 * b₂ / c_B := by positivity
  have hexp : 1 + (a_leaf + 2) + (8 * b_leaf + 3) * b₂ + 80 * b_leaf * b₂ ≤ d := by nlinarith
  have hk_neg_d : (k : ℝ) ^ (-d) ≤
      (1 / 2 : ℝ) * y ^ (a_leaf + 2) * lam ^ b₂ * (lambda0Param (2 * b_leaf)) ^ b₂ := by
    calc (k : ℝ) ^ (-d)
      _ ≤ (k : ℝ) ^ (-(1 + (a_leaf + 2) + (8 * b_leaf + 3) * b₂ + 80 * b_leaf * b₂)) :=
        Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)
      _ = (k : ℝ) ^ (-1 : ℝ) * (k : ℝ) ^ (-(a_leaf + 2)) *
          (k : ℝ) ^ (-((8 * b_leaf + 3) * b₂)) * (k : ℝ) ^ (-(80 * b_leaf * b₂)) := by
        rw [show -(1 + (a_leaf + 2) + (8 * b_leaf + 3) * b₂ + 80 * b_leaf * b₂) =
          -1 + -(a_leaf + 2) + -((8 * b_leaf + 3) * b₂) + -(80 * b_leaf * b₂) by ring,
          Real.rpow_add hk_pos, Real.rpow_add hk_pos, Real.rpow_add hk_pos]
      _ ≤ (1 / 2 : ℝ) * y ^ (a_leaf + 2) * lam ^ b₂ * (lambda0Param (2 * b_leaf)) ^ b₂ := by
        refine mul_le_mul ?_ hlam0_b2_ge (by positivity) (by positivity)
        refine mul_le_mul ?_ hlam_b2_ge (by positivity) (by positivity)
        exact mul_le_mul hhalf_ge hy_a2_ge (by positivity) (by positivity)
  have hw₁_half : (1 / 2 : ℝ) * (y ^ (a_leaf + 2) * (F_t.card : ℝ)) ≤ (w₁ : ℝ) := by
    have hgt : y ^ (a_leaf + 2) * (F_t.card : ℝ) - 1 < (w₁ : ℝ) :=
      Nat.sub_one_lt_floor _
    linarith
  rw [div_eq_mul_inv, ← Real.rpow_neg hk_pos.le, mul_comm]
  calc (k : ℝ) ^ (-d) * (F.card : ℝ)
    _ ≤ ((1 / 2 : ℝ) * y ^ (a_leaf + 2) * lam ^ b₂ * (lambda0Param (2 * b_leaf)) ^ b₂) *
        (F.card : ℝ) := mul_le_mul_of_nonneg_right hk_neg_d (Nat.cast_nonneg _)
    _ = (1 / 2 : ℝ) * y ^ (a_leaf + 2) * (lam ^ b₂ *
        ((lambda0Param (2 * b_leaf)) ^ b₂ * (F.card : ℝ))) := by ring
    _ ≤ (1 / 2 : ℝ) * y ^ (a_leaf + 2) * (lam ^ b₂ * (F₀.card : ℝ)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left hF₀ (by positivity)
    _ ≤ (1 / 2 : ℝ) * y ^ (a_leaf + 2) * (F_t.card : ℝ) :=
      mul_le_mul_of_nonneg_left hFt (by positivity)
    _ = (1 / 2 : ℝ) * (y ^ (a_leaf + 2) * (F_t.card : ℝ)) := by ring
    _ ≤ (w₁ : ℝ) := hw₁_half

private theorem symm_gen_nice_comb_width_ge {a_leaf b_leaf C_comb c_B δ lam : ℝ}
    {F F₀ F_t F' : Finset V} {ℓ k : ℕ}
    (ha_leaf : 6 ≤ a_leaf) (hb_leaf : 6 ≤ b_leaf) (_hC_comb : 18 ≤ C_comb) (hc_B : 0 < c_B)
    (hlam_pos : 0 < lam)
    (hF₀ : (lambda0Param (2 * b_leaf)) ^ (b2Param a_leaf (2 * b_leaf) δ) *
      (F.card : ℝ) ≤ (F₀.card : ℝ))
    (hFt : lam ^ (b2Param a_leaf (2 * b_leaf) δ) * (F₀.card : ℝ) ≤ (F_t.card : ℝ))
    (hF' : cParam (2 * b_leaf) * (F_t.card : ℝ) ≤ (F'.card : ℝ))
    (hℓ_lo : (localSparsityY (2 * b_leaf) lam) ^ (-(1 / 4 : ℝ)) ≤ (ℓ : ℝ))
    (hk2 : 2 ≤ k) (hk_lo : (1 / 2 : ℝ) * (ℓ : ℝ) ^ c_B ≤ (k : ℝ)) :
    let d := symmGenNiceD a_leaf b_leaf C_comb c_B δ
    (F.card : ℝ) / (k : ℝ) ^ d ≤ (F'.card : ℝ) / (k : ℝ) ^ C_comb := by
  intro d
  have hc_pos : 0 < cParam (2 * b_leaf) := cParam_pos _
  have hlam0_pos : 0 < lambda0Param (2 * b_leaf) := lambda0Param_pos _
  set y := localSparsityY (2 * b_leaf) lam
  have hy_pos : 0 < y := localSparsityY_pos (2 * b_leaf) hlam_pos
  have hk2_real : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by linarith
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  have hy_ge_k : (k : ℝ) ^ (-8 / c_B) ≤ y := by
    have h2k_le : 2 * (k : ℝ) ≤ (k : ℝ) ^ (2 : ℝ) := by
      rw [Real.rpow_two]; nlinarith
    have hℓ_cB : (ℓ : ℝ) ^ c_B ≤ (k : ℝ) ^ (2 : ℝ) := by linarith
    have hy_cB4 : y ^ (-c_B / 4) ≤ (k : ℝ) ^ (2 : ℝ) := by
      calc y ^ (-c_B / 4)
        _ = (y ^ (-(1 / 4 : ℝ))) ^ c_B := by rw [← Real.rpow_mul hy_pos.le]; congr 1; ring
        _ ≤ (ℓ : ℝ) ^ c_B := Real.rpow_le_rpow (by positivity) hℓ_lo hc_B.le
        _ ≤ (k : ℝ) ^ (2 : ℝ) := hℓ_cB
    have hy_inv_le : y⁻¹ ≤ (k : ℝ) ^ (8 / c_B) := by
      calc y⁻¹
        _ = (y ^ (-c_B / 4)) ^ (4 / c_B) := by
          have hc_B_ne : c_B ≠ 0 := hc_B.ne'
          rw [← Real.rpow_mul hy_pos.le,
            show (-c_B / 4) * (4 / c_B) = -1 by field_simp, Real.rpow_neg_one]
        _ ≤ ((k : ℝ) ^ (2 : ℝ)) ^ (4 / c_B) :=
          Real.rpow_le_rpow (by positivity) hy_cB4 (by positivity)
        _ = (k : ℝ) ^ (8 / c_B) := by rw [← Real.rpow_mul hk_pos.le]; congr 1; ring
    rw [show (-8 / c_B : ℝ) = -(8 / c_B) by ring, Real.rpow_neg hk_pos.le, ← inv_inv y]
    exact inv_anti₀ (inv_pos.mpr hy_pos) hy_inv_le
  have hc_ge_k : (k : ℝ) ^ (-(8 * b_leaf)) ≤ cParam (2 * b_leaf) := by
    rw [cParam_two_mul_eq hb_leaf, show (-8 * b_leaf : ℝ) = -(8 * b_leaf) by ring]
    exact rpow_neg_le_two_rpow_neg hk2_real (by linarith)
  have hlam0_ge_k : (k : ℝ) ^ (-(80 * b_leaf)) ≤ lambda0Param (2 * b_leaf) := by
    rw [lambda0Param_two_mul_eq hb_leaf, show (-80 * b_leaf : ℝ) = -(80 * b_leaf) by ring]
    exact rpow_neg_le_two_rpow_neg hk2_real (by linarith)
  have hlam_ge_k : (k : ℝ) ^ (-(8 * b_leaf + 24 / c_B)) ≤ lam := by
    have hlam_eq : lam = cParam (2 * b_leaf) * y ^ (3 : ℝ) :=
      (cParam_mul_localSparsityY_cube (2 * b_leaf) hlam_pos.le).symm
    rw [hlam_eq, show -(8 * b_leaf + 24 / c_B) = -(8 * b_leaf) + (-24 / c_B) by ring,
      Real.rpow_add hk_pos]
    refine mul_le_mul hc_ge_k ?_ (by positivity) (by positivity)
    calc (k : ℝ) ^ (-24 / c_B)
      _ = ((k : ℝ) ^ (-8 / c_B)) ^ (3 : ℝ) := by
        rw [← Real.rpow_mul hk_pos.le]; congr 1; ring
      _ ≤ y ^ (3 : ℝ) := Real.rpow_le_rpow (by positivity) hy_ge_k (by norm_num)
  set b₂ := b2Param a_leaf (2 * b_leaf) δ
  have hb₂_pos : 0 < b₂ := b2Param_pos a_leaf (2 * b_leaf) δ
  have hlam_b2_ge : (k : ℝ) ^ (-((8 * b_leaf + 24 / c_B) * b₂)) ≤ lam ^ b₂ := by
    rw [show -((8 * b_leaf + 24 / c_B) * b₂) = -(8 * b_leaf + 24 / c_B) * b₂ by ring,
      Real.rpow_mul hk_pos.le]
    exact Real.rpow_le_rpow (by positivity) hlam_ge_k hb₂_pos.le
  have hlam0_b2_ge : (k : ℝ) ^ (-(80 * b_leaf * b₂)) ≤ (lambda0Param (2 * b_leaf)) ^ b₂ := by
    rw [show -(80 * b_leaf * b₂) = -(80 * b_leaf) * b₂ by ring, Real.rpow_mul hk_pos.le]
    exact Real.rpow_le_rpow (by positivity) hlam0_ge_k hb₂_pos.le
  have hd_ge := symmGenNiceD_ge_comb_terms a_leaf b_leaf C_comb c_B δ
  have hexp : C_comb + 8 * b_leaf + (8 * b_leaf + 24 / c_B) * b₂ + 80 * b_leaf * b₂ ≤ d := by
    have : 24 * b₂ / c_B ≤ 32 * b₂ / c_B := by
      rw [div_le_div_iff_of_pos_right hc_B]
      linarith
    have : (8 * b_leaf + 24 / c_B) * b₂ = 8 * b_leaf * b₂ + 24 * b₂ / c_B := by ring
    nlinarith
  have hk_neg_d : (k : ℝ) ^ (-d) ≤
      (k : ℝ) ^ (-C_comb) * cParam (2 * b_leaf) * lam ^ b₂ *
        (lambda0Param (2 * b_leaf)) ^ b₂ := by
    calc (k : ℝ) ^ (-d)
      _ ≤ (k : ℝ) ^ (-(C_comb + 8 * b_leaf + (8 * b_leaf + 24 / c_B) * b₂ + 80 * b_leaf * b₂)) :=
        Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)
      _ = (k : ℝ) ^ (-C_comb) * (k : ℝ) ^ (-(8 * b_leaf)) *
          (k : ℝ) ^ (-((8 * b_leaf + 24 / c_B) * b₂)) * (k : ℝ) ^ (-(80 * b_leaf * b₂)) := by
        rw [show -(C_comb + 8 * b_leaf + (8 * b_leaf + 24 / c_B) * b₂ + 80 * b_leaf * b₂) =
          -C_comb + -(8 * b_leaf) + -((8 * b_leaf + 24 / c_B) * b₂) + -(80 * b_leaf * b₂) by ring,
          Real.rpow_add hk_pos, Real.rpow_add hk_pos, Real.rpow_add hk_pos]
      _ ≤ (k : ℝ) ^ (-C_comb) * cParam (2 * b_leaf) * lam ^ b₂ *
          (lambda0Param (2 * b_leaf)) ^ b₂ := by
        refine mul_le_mul ?_ hlam0_b2_ge (by positivity) (by positivity)
        refine mul_le_mul ?_ hlam_b2_ge (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left hc_ge_k (by positivity)
  rw [div_eq_mul_inv, div_eq_mul_inv, ← Real.rpow_neg hk_pos.le, ← Real.rpow_neg hk_pos.le,
    mul_comm (F.card : ℝ), mul_comm (F'.card : ℝ)]
  calc (k : ℝ) ^ (-d) * (F.card : ℝ)
    _ ≤ ((k : ℝ) ^ (-C_comb) * cParam (2 * b_leaf) * lam ^ b₂ *
        (lambda0Param (2 * b_leaf)) ^ b₂) * (F.card : ℝ) :=
      mul_le_mul_of_nonneg_right hk_neg_d (Nat.cast_nonneg _)
    _ = (k : ℝ) ^ (-C_comb) * (cParam (2 * b_leaf) * (lam ^ b₂ *
        ((lambda0Param (2 * b_leaf)) ^ b₂ * (F.card : ℝ)))) := by ring
    _ ≤ (k : ℝ) ^ (-C_comb) * (cParam (2 * b_leaf) * (lam ^ b₂ * (F₀.card : ℝ))) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left hF₀ (by positivity)
    _ ≤ (k : ℝ) ^ (-C_comb) * (cParam (2 * b_leaf) * (F_t.card : ℝ)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left hFt (by positivity)
    _ ≤ (k : ℝ) ^ (-C_comb) * (F'.card : ℝ) :=
      mul_le_mul_of_nonneg_left hF' (by positivity)

private theorem symm_gen_nice_sub_card_ge {a_leaf b_leaf C_comb C_cap c_B δ ε lam n_V : ℝ}
    {F F₀ F_t : Finset V}
    (ha_leaf : 6 ≤ a_leaf) (hb_leaf : 6 ≤ b_leaf) (hC_comb : 18 ≤ C_comb)
    (hC_cap : 2 ≤ C_cap) (hc_B : 0 < c_B) (hε0 : 0 < ε) (hε_half : ε < 1 / 2)
    (hlam_ge : cParam (2 * b_leaf) * ε ^ (6 : ℝ) ≤ lam)
    (hn_V : ε ^ (-40 * C_cap * (symmGenNiceD a_leaf b_leaf C_comb c_B δ) ^ 2) ≤ n_V)
    (hF : ε ^ (symmGenNiceD a_leaf b_leaf C_comb c_B δ) * n_V ≤ (F.card : ℝ))
    (hF₀ : (lambda0Param (2 * b_leaf)) ^ (b2Param a_leaf (2 * b_leaf) δ) *
      (F.card : ℝ) ≤ (F₀.card : ℝ))
    (hFt : lam ^ (b2Param a_leaf (2 * b_leaf) δ) * (F₀.card : ℝ) ≤ (F_t.card : ℝ)) :
    let d := symmGenNiceD a_leaf b_leaf C_comb c_B δ
    let y := localSparsityY (2 * b_leaf) lam
    (2 : ℝ) ≤ y ^ (a_leaf + 2) * (F_t.card : ℝ) ∧
    (2 : ℝ) ≤ y ^ (a_leaf + 2) * (cParam (2 * b_leaf) * (F_t.card : ℝ)) ∧
    ε ^ (3 * d) * n_V ≤ cParam (2 * b_leaf) * (F_t.card : ℝ) := by
  intro d y
  have hε1 : ε ≤ 1 := by linarith
  have hc_pos : 0 < cParam (2 * b_leaf) := cParam_pos _
  have hlam0_pos : 0 < lambda0Param (2 * b_leaf) := lambda0Param_pos _
  have hlam_pos : 0 < lam := (by positivity : 0 < cParam (2 * b_leaf) * ε ^ (6 : ℝ)).trans_le hlam_ge
  have hy_pos : 0 < y := localSparsityY_pos (2 * b_leaf) hlam_pos
  have hb₂_pos : 0 < b2Param a_leaf (2 * b_leaf) δ := b2Param_pos a_leaf (2 * b_leaf) δ
  set b₂ := b2Param a_leaf (2 * b_leaf) δ
  have hd_ge := symmGenNiceD_ge_comb_terms a_leaf b_leaf C_comb c_B δ
  have hd120 : 120 ≤ d := one_hundred_twenty_le_symmGenNiceD a_leaf b_leaf C_comb c_B δ
  have h32_pos : 0 ≤ 32 * b₂ / c_B := by positivity
  have hc_ge : ε ^ (8 * b_leaf) ≤ cParam (2 * b_leaf) := by
    rw [cParam_two_mul_eq hb_leaf, show (-8 * b_leaf : ℝ) = -(8 * b_leaf) by ring]
    exact eps_rpow_le_two_rpow_neg hε0.le hε_half (by linarith)
  have hlam_ge_eps : ε ^ (8 * b_leaf + 6) ≤ lam := by
    refine (?_ : ε ^ (8 * b_leaf + 6) ≤ cParam (2 * b_leaf) * ε ^ (6 : ℝ)).trans hlam_ge
    rw [Real.rpow_add hε0]
    exact mul_le_mul_of_nonneg_right hc_ge (by positivity)
  have hlam0_ge : ε ^ (80 * b_leaf) ≤ lambda0Param (2 * b_leaf) := by
    rw [lambda0Param_two_mul_eq hb_leaf, show (-80 * b_leaf : ℝ) = -(80 * b_leaf) by ring]
    exact eps_rpow_le_two_rpow_neg hε0.le hε_half (by linarith)
  have h1 : ε ^ ((8 * b_leaf + 6) * b₂) ≤ lam ^ b₂ := by
    rw [Real.rpow_mul hε0.le]; exact Real.rpow_le_rpow (by positivity) hlam_ge_eps hb₂_pos.le
  have h2 : ε ^ (80 * b_leaf * b₂) ≤ (lambda0Param (2 * b_leaf)) ^ b₂ := by
    rw [Real.rpow_mul hε0.le]; exact Real.rpow_le_rpow (by positivity) hlam0_ge hb₂_pos.le
  have hexp_3d : 8 * b_leaf + (8 * b_leaf + 6) * b₂ + 80 * b_leaf * b₂ + d ≤ 3 * d := by
    nlinarith
  have hc_Ft_ge : ε ^ (3 * d) * n_V ≤ cParam (2 * b_leaf) * (F_t.card : ℝ) := by
    have hrpow : ε ^ (3 * d) ≤
        cParam (2 * b_leaf) * lam ^ b₂ * (lambda0Param (2 * b_leaf)) ^ b₂ * ε ^ d := by
      calc ε ^ (3 * d)
        _ ≤ ε ^ (8 * b_leaf + (8 * b_leaf + 6) * b₂ + 80 * b_leaf * b₂ + d) :=
          Real.rpow_le_rpow_of_exponent_ge hε0 hε1 hexp_3d
        _ = ε ^ (8 * b_leaf) * ε ^ ((8 * b_leaf + 6) * b₂) *
            ε ^ (80 * b_leaf * b₂) * ε ^ d := by
          rw [Real.rpow_add hε0, Real.rpow_add hε0, Real.rpow_add hε0]
        _ ≤ cParam (2 * b_leaf) * lam ^ b₂ * (lambda0Param (2 * b_leaf)) ^ b₂ * ε ^ d := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          refine mul_le_mul ?_ h2 (by positivity) (by positivity)
          exact mul_le_mul hc_ge h1 (by positivity) (by positivity)
    have hn_V_nonneg : 0 ≤ n_V := (by positivity : (0 : ℝ) ≤ _).trans hn_V
    calc ε ^ (3 * d) * n_V
      _ ≤ (cParam (2 * b_leaf) * lam ^ b₂ * (lambda0Param (2 * b_leaf)) ^ b₂ * ε ^ d) * n_V :=
        mul_le_mul_of_nonneg_right hrpow hn_V_nonneg
      _ = cParam (2 * b_leaf) * (lam ^ b₂ * ((lambda0Param (2 * b_leaf)) ^ b₂ *
          (ε ^ d * n_V))) := by ring
      _ ≤ cParam (2 * b_leaf) * (lam ^ b₂ * ((lambda0Param (2 * b_leaf)) ^ b₂ * (F.card : ℝ))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hF (by positivity)
      _ ≤ cParam (2 * b_leaf) * (lam ^ b₂ * (F₀.card : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hF₀ (by positivity)
      _ ≤ cParam (2 * b_leaf) * (F_t.card : ℝ) :=
        mul_le_mul_of_nonneg_left hFt (by positivity)
  have hy_ge_eps2 : ε ^ 2 ≤ y := localSparsityY_ge_eps_sq b_leaf hε0 hlam_ge
  have hy_a2_ge : ε ^ (2 * (a_leaf + 2)) ≤ y ^ (a_leaf + 2) := by
    calc ε ^ (2 * (a_leaf + 2))
      _ = (ε ^ (2 : ℝ)) ^ (a_leaf + 2) := by rw [← Real.rpow_mul hε0.le]
      _ = (ε ^ 2) ^ (a_leaf + 2) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      _ ≤ y ^ (a_leaf + 2) := Real.rpow_le_rpow (by positivity) hy_ge_eps2 (by linarith)
  have h2_le_c_Ft : (2 : ℝ) ≤ y ^ (a_leaf + 2) * (cParam (2 * b_leaf) * (F_t.card : ℝ)) := by
    have hexp : 2 * (a_leaf + 2) + 3 * d - 40 * C_cap * d ^ 2 ≤ -1 := by nlinarith
    have h2_le_eps : (2 : ℝ) ≤ ε ^ (-1 : ℝ) := by
      rw [Real.rpow_neg_one, ← inv_inv (2 : ℝ)]
      exact inv_anti₀ hε0 (by linarith)
    calc (2 : ℝ)
      _ ≤ ε ^ (-1 : ℝ) := h2_le_eps
      _ ≤ ε ^ (2 * (a_leaf + 2) + 3 * d - 40 * C_cap * d ^ 2) :=
        Real.rpow_le_rpow_of_exponent_ge hε0 hε1 hexp
      _ = ε ^ (2 * (a_leaf + 2)) * (ε ^ (3 * d) * ε ^ (-40 * C_cap * d ^ 2)) := by
        rw [show 2 * (a_leaf + 2) + 3 * d - 40 * C_cap * d ^ 2 =
          2 * (a_leaf + 2) + (3 * d + -40 * C_cap * d ^ 2) by ring,
          Real.rpow_add hε0, Real.rpow_add hε0]
      _ ≤ y ^ (a_leaf + 2) * (ε ^ (3 * d) * n_V) := by
        refine mul_le_mul hy_a2_ge ?_ (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left hn_V (by positivity)
      _ ≤ y ^ (a_leaf + 2) * (cParam (2 * b_leaf) * (F_t.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hc_Ft_ge (by positivity)
  have h2_le_Ft : (2 : ℝ) ≤ y ^ (a_leaf + 2) * (F_t.card : ℝ) := by
    have hc_le1 : cParam (2 * b_leaf) ≤ 1 := (cParam_lt_half _).le.trans (by norm_num)
    calc (2 : ℝ)
      _ ≤ y ^ (a_leaf + 2) * (cParam (2 * b_leaf) * (F_t.card : ℝ)) := h2_le_c_Ft
      _ ≤ y ^ (a_leaf + 2) * (1 * (F_t.card : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right hc_le1 (Nat.cast_nonneg _)
      _ = y ^ (a_leaf + 2) * (F_t.card : ℝ) := by ring
  exact ⟨h2_le_Ft, h2_le_c_Ft, hc_Ft_ge⟩

private theorem symm_gen_nice_cd1_bound {d C_comb C_cap c_A ε x_sp y : ℝ}
    {F' : Finset V} {ℓ : ℕ} {n_V : ℝ}
    (hd120 : 120 ≤ d) (hC_comb : 18 ≤ C_comb) (hC_cap : 2 ≤ C_cap) (hc_A : 0 < c_A)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hx_sp_pos : 0 < x_sp) (hx_sp_le1 : x_sp ≤ 1)
    (hn_V : 0 ≤ n_V) (hy_pos : 0 < y)
    (hℓ_lo : y ^ (-(1 / 4 : ℝ)) ≤ (ℓ : ℝ))
    (hℓ_hi : (ℓ : ℝ) ≤ ((x_sp * ε ^ (4 * d)) ^ 2)⁻¹)
    (hF'_ge_V : ε ^ (3 * d) * n_V ≤ (F'.card : ℝ)) :
    let c₃ := 42 * d ^ 2 * C_cap * (C_comb + 2)
    (ε ^ c₃ * x_sp ^ c₃ * n_V) ^ c_A ≤ (y ^ 4 * (F'.card : ℝ) / (ℓ : ℝ) ^ 2) ^ c_A := by
  intro c₃
  have hℓ_pos : (0 : ℝ) < (ℓ : ℝ) := lt_of_lt_of_le (by positivity) hℓ_lo
  have hx_3_pos : 0 < (x_sp * ε ^ (4 * d)) ^ 2 := by positivity
  have hw_ge_18 : (F'.card : ℝ) / (ℓ : ℝ) ^ 18 ≤ y ^ 4 * (F'.card : ℝ) / (ℓ : ℝ) ^ 2 := by
    have hy_inv_le_ℓ4 : y⁻¹ ≤ (ℓ : ℝ) ^ 4 := by
      have hp := pow_le_pow_left₀ (by positivity) hℓ_lo 4
      have h_eq : (y ^ (-(1 / 4 : ℝ))) ^ 4 = y⁻¹ := by
        rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul hy_pos.le]
        norm_num
        exact Real.rpow_neg_one y
      rwa [h_eq] at hp
    have hy4_inv_le_ℓ16 : (y ^ 4)⁻¹ ≤ (ℓ : ℝ) ^ 16 := by
      have hp := pow_le_pow_left₀ (by positivity) hy_inv_le_ℓ4 4
      rwa [inv_pow, ← pow_mul] at hp
    have hℓ16_inv_le_y4 : ((ℓ : ℝ) ^ 16)⁻¹ ≤ y ^ 4 := by
      rw [← inv_inv (y ^ 4)]
      exact inv_anti₀ (by positivity) hy4_inv_le_ℓ16
    have hℓ_ne : (ℓ : ℝ) ≠ 0 := hℓ_pos.ne'
    calc (F'.card : ℝ) / (ℓ : ℝ) ^ 18
      _ = ((ℓ : ℝ) ^ 16)⁻¹ * ((F'.card : ℝ) / (ℓ : ℝ) ^ 2) := by
        rw [show (18 : ℕ) = 2 + 16 by rfl, pow_add, ← div_div, div_eq_inv_mul]
      _ ≤ y ^ 4 * ((F'.card : ℝ) / (ℓ : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hℓ16_inv_le_y4 (by positivity)
      _ = y ^ 4 * (F'.card : ℝ) / (ℓ : ℝ) ^ 2 := (mul_div_assoc _ _ _).symm
  have hℓ_inv_ge : (x_sp * ε ^ (4 * d)) ^ 2 ≤ (ℓ : ℝ)⁻¹ := by
    rw [← inv_inv ((x_sp * ε ^ (4 * d)) ^ 2)]
    exact inv_anti₀ hℓ_pos hℓ_hi
  have hw_ge_c3 : ε ^ c₃ * x_sp ^ c₃ * n_V ≤ (F'.card : ℝ) / (ℓ : ℝ) ^ 18 := by
    rw [div_eq_mul_inv, ← inv_pow]
    have hx_3_18 : x_sp ^ (36 : ℝ) * ε ^ (144 * d) ≤ ((ℓ : ℝ)⁻¹) ^ 18 := by
      have hx_3_eq : ((x_sp * ε ^ (4 * d)) ^ 2) ^ 18 = x_sp ^ (36 : ℝ) * ε ^ (144 * d) := by
        rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← Real.rpow_natCast x_sp 36,
          ← Real.rpow_natCast (ε ^ (4 * d)) 36, ← Real.rpow_mul hε0.le]
        congr 2; ring
      rw [← hx_3_eq]
      exact pow_le_pow_left₀ hx_3_pos.le hℓ_inv_ge 18
    have hcap_comb : 40 ≤ C_cap * (C_comb + 2) := by nlinarith
    have hd_sq : 120 * d ≤ d ^ 2 := by nlinarith
    have hε_c3 : ε ^ c₃ ≤ ε ^ (147 * d) := by
      dsimp [c₃]
      have : 147 * d ≤ 42 * d ^ 2 * (C_cap * (C_comb + 2)) := by nlinarith
      exact Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (by linarith)
    have hx_c3 : x_sp ^ c₃ ≤ x_sp ^ (36 : ℝ) := by
      dsimp [c₃]
      have : (36 : ℝ) ≤ 42 * d ^ 2 * (C_cap * (C_comb + 2)) := by nlinarith
      exact Real.rpow_le_rpow_of_exponent_ge hx_sp_pos hx_sp_le1 (by linarith)
    calc ε ^ c₃ * x_sp ^ c₃ * n_V
      _ ≤ ε ^ (147 * d) * x_sp ^ (36 : ℝ) * n_V := by
        refine mul_le_mul_of_nonneg_right ?_ hn_V
        exact mul_le_mul hε_c3 hx_c3 (by positivity) (by positivity)
      _ = (ε ^ (3 * d) * n_V) * (x_sp ^ (36 : ℝ) * ε ^ (144 * d)) := by
        rw [show (147 * d : ℝ) = 3 * d + 144 * d by ring, Real.rpow_add hε0]; ring
      _ ≤ (F'.card : ℝ) * ((ℓ : ℝ)⁻¹) ^ 18 :=
        mul_le_mul hF'_ge_V hx_3_18 (by positivity) (by positivity)
  exact Real.rpow_le_rpow (by positivity) (hw_ge_c3.trans hw_ge_18) hc_A.le

private theorem symm_gen_nice_cd23_kmax {d C_cap ε x_sp : ℝ} {k : ℕ}
    (hd120 : 120 ≤ d) (hC_cap : 2 ≤ C_cap) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hx_lo : ε ^ (3 * d) ≤ x_sp)
    (hk_hi : k ≤ ⌈((x_sp * ε ^ (4 * d)) ^ 2) ^ (-C_cap)⌉₊) :
    k ≤ ⌈ε ^ (-20 * d * C_cap)⌉₊ := by
  have hx_sp_pos : 0 < x_sp := (Real.rpow_pos_of_pos hε0 (3 * d)).trans_le hx_lo
  have hx_3_pos : 0 < (x_sp * ε ^ (4 * d)) ^ 2 := by positivity
  have hx_3_ge : ε ^ (14 * d) ≤ (x_sp * ε ^ (4 * d)) ^ 2 := by
    calc ε ^ (14 * d)
      _ = (ε ^ (3 * d) * ε ^ (4 * d)) ^ 2 := by
        rw [← Real.rpow_add hε0, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hε0.le]
        congr 1; ring
      _ ≤ (x_sp * ε ^ (4 * d)) ^ 2 :=
        pow_le_pow_left₀ (by positivity)
          (mul_le_mul_of_nonneg_right hx_lo (by positivity)) 2
  have hx_3_neg_cap : ((x_sp * ε ^ (4 * d)) ^ 2) ^ (-C_cap) ≤ ε ^ (-20 * d * C_cap) := by
    calc ((x_sp * ε ^ (4 * d)) ^ 2) ^ (-C_cap)
      _ = (((x_sp * ε ^ (4 * d)) ^ 2) ^ C_cap)⁻¹ := Real.rpow_neg hx_3_pos.le C_cap
      _ ≤ ((ε ^ (14 * d)) ^ C_cap)⁻¹ :=
        inv_anti₀ (by positivity)
          (Real.rpow_le_rpow (by positivity) hx_3_ge (by linarith))
      _ = ε ^ (-14 * d * C_cap) := by
        rw [← Real.rpow_mul hε0.le, ← Real.rpow_neg hε0.le]
        congr 1; ring
      _ ≤ ε ^ (-20 * d * C_cap) :=
        Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (by nlinarith)
  exact hk_hi.trans (Nat.ceil_mono hx_3_neg_cap)

/--
**Lemma 7(1) (`pair_coupled_generalized_nice_of_comb_dichotomy_explicit`, `main.tex` lines 288–331)**:
Let $\{H_1, H_2\}$ be a finite two-graph family ($|H_1| \ge 2$) satisfying the co-sparse peeling
property with parameters $a_{\mathrm{leaf}}, b_{\mathrm{leaf}} \ge 6$ and the Stage-1 Comb Dichotomy
`(CD1)`–`(CD3)` with parameters $C_{\mathrm{comb}} \ge 18$, $C_{\mathrm{cap}} \ge 2$, and
$c_{\mathrm{A}}, c_{\mathrm{B}} > 0$. Then $\{H_1, H_2\}$ satisfies `SatisfiesPairCoupledGenNiceAt`
(and hence `IsPairCoupledGeneralizedNice H₁ H₂`) with explicit constants:
$c_1 = c_8 = (20 C_{\mathrm{cap}} + 4) d^2$, $c_2 = d \ge 120$,
$c_3 = 42 d^2 C_{\mathrm{cap}} (C_{\mathrm{comb}} + 2)$, $c_4 = c_{\mathrm{A}}$,
$c_5 = C_{\mathrm{comb}} + 2 d$, $c_6 = 2$, $c_7 = 6$, and $c_9 = 20 d C_{\mathrm{cap}}$.
-/
theorem pair_coupled_generalized_nice_of_comb_dichotomy_explicit
    {W₁ W₂ : Type*} [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]
    (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂)
    (_hh₁ : 2 ≤ Fintype.card W₁)
    (a_leaf b_leaf C_comb C_cap c_A c_B : ℝ)
    (ha_leaf : 6 ≤ a_leaf) (hb_leaf : 6 ≤ b_leaf)
    (hC_comb : 18 ≤ C_comb) (hC_cap : 2 ≤ C_cap)
    (hc_A : 0 < c_A) (hc_B : 0 < c_B)
    (h_cosparse_peel : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      (F' : Finset V) (y : ℝ),
      IsInducedSubgraphFree G H₁ᶜ → IsInducedSubgraphFree G H₂ᶜ →
      0 < y → y ≤ (2 : ℝ) ^ (-4 * b_leaf) →
      1 ≤ y ^ (a_leaf + 2) * (F'.card : ℝ) →
      IsEpsSparseOn Gᶜ F' (y ^ 3) →
        (∃ U ⊆ F', IsEpsRestrictedOn G U (y ^ 4) ∧
          y ^ a_leaf * (F'.card : ℝ) ≤ (U.card : ℝ)) ∨
        (∃ X ⊆ F', ∃ Y ⊆ F', Disjoint X Y ∧
          y ^ a_leaf * (F'.card : ℝ) ≤ (X.card : ℝ) ∧
          (1 - b_leaf * y) * (F'.card : ℝ) ≤ (Y.card : ℝ) ∧
          IsCompletePair G X Y))
    (h_comb_dichotomy : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      (F' : Finset V) (x y : ℝ) (ℓ : ℕ) (a : Fin ℓ → V) (B : Fin ℓ → Finset V) (v : V),
      IsInducedSubgraphFree G H₁ᶜ → IsInducedSubgraphFree G H₂ᶜ →
      0 < x → x ≤ y → y ≤ (2 : ℝ)⁻¹ ^ 16 →
      y ^ (-(1 / 4 : ℝ)) ≤ (ℓ : ℝ) → (ℓ : ℝ) ≤ x⁻¹ → 64 ≤ ℓ →
      IsCombIn G F' ℓ (y ^ 4 * (F'.card : ℝ) / (ℓ : ℝ) ^ 2) a B →
      IsCombExternalApex G F' ℓ a B v →
        -- (CD1)
        ((y ^ 4 * (F'.card : ℝ) / (ℓ : ℝ) ^ 2) ^ c_A ≤ (kappa G : ℝ)) ∨
        -- (CD2) or (CD3)
        (∃ k : ℕ, 2 ≤ k ∧ (1 / 2 : ℝ) * (ℓ : ℝ) ^ c_B ≤ (k : ℝ) ∧ k ≤ ⌈x ^ (-C_cap)⌉₊ ∧
          ∃ U : Fin k → Finset V,
            IsPureBlockadeIn G F' k ((F'.card : ℝ) / (k : ℝ) ^ C_comb) U ∨
            IsWeaklySparseOrCoSparseBlockadeIn G F' k ((F'.card : ℝ) / (k : ℝ) ^ C_comb) x U)) :
    let δ := symmRodlDeltaGen (Fintype.card W₁) (lambda0Param (2 * b_leaf))
    let d := symmGenNiceD a_leaf b_leaf C_comb c_B δ
    SatisfiesPairCoupledGenNiceAt H₁ H₂
      ((20 * C_cap + 4) * d ^ 2)
      d
      (42 * d ^ 2 * C_cap * (C_comb + 2))
      c_A
      (C_comb + 2 * d)
      2
      6
      ((20 * C_cap + 4) * d ^ 2)
      (20 * d * C_cap) := by
  classical
  intro δ d
  have hd120 : 120 ≤ d := one_hundred_twenty_le_symmGenNiceD a_leaf b_leaf C_comb c_B δ
  have hd1 : 1 ≤ d := by linarith
  have hc₁_pos : 0 < (20 * C_cap + 4) * d ^ 2 := by positivity
  have hc₂_pos : 0 < d := by linarith
  have hc₃_pos : 0 < 42 * d ^ 2 * C_cap * (C_comb + 2) := by positivity
  have hc₅_pos : 0 < C_comb + 2 * d := by positivity
  have hc₉_pos : 0 < 20 * d * C_cap := by positivity
  refine ⟨hc₁_pos, hc₂_pos, hc₃_pos, hc_A, hc₅_pos, zero_lt_two, by norm_num, hc₁_pos, hc₉_pos, ?_⟩
  intro V _ _ G ε x_sp hε0 hε_half hx_lo hx_hi hG₁ hG₂
  set c₁ := (20 * C_cap + 4) * d ^ 2
  set c₃ := 42 * d ^ 2 * C_cap * (C_comb + 2)
  set c₉ := 20 * d * C_cap
  have hε1 : ε ≤ 1 := by linarith
  have hx_sp_pos : 0 < x_sp := (Real.rpow_pos_of_pos hε0 (3 * d)).trans_le hx_lo
  have hx_sp_le1 : x_sp ≤ 1 :=
    hx_hi.trans (Real.rpow_le_one hε0.le hε1 (by norm_num))
  -- Handle empty V or small |V| ≤ ε ^ (-40 * C_cap * d ^ 2) via (GN2)
  by_cases hV_small : (Fintype.card V : ℝ) ≤ ε ^ (-40 * C_cap * d ^ 2)
  · right; left
    rcases Nat.eq_zero_or_pos (Fintype.card V) with h0 | hpos
    · rw [h0, Nat.cast_zero, mul_zero, Real.zero_rpow hc_A.ne']
      exact Nat.cast_nonneg _
    · have hkappa_ge1 : (1 : ℝ) ≤ (kappa G : ℝ) := by
        haveI : Nonempty V := Fintype.card_pos_iff.mp hpos
        exact_mod_cast kappa_pos_of_nonempty G
      have hprod_le1 : ε ^ c₃ * x_sp ^ c₃ * (Fintype.card V : ℝ) ≤ 1 := by
        have hx_c3_le1 : x_sp ^ c₃ ≤ 1 := Real.rpow_le_one hx_sp_pos.le hx_sp_le1 hc₃_pos.le
        have hε_c3_le : ε ^ c₃ ≤ ε ^ (40 * C_cap * d ^ 2) := by
          dsimp [c₃]
          exact Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (by nlinarith)
        calc ε ^ c₃ * x_sp ^ c₃ * (Fintype.card V : ℝ)
          _ ≤ ε ^ (40 * C_cap * d ^ 2) * 1 * ε ^ (-40 * C_cap * d ^ 2) := by
            refine mul_le_mul ?_ hV_small (Nat.cast_nonneg _) (by positivity)
            exact mul_le_mul hε_c3_le hx_c3_le1 (by positivity) (by positivity)
          _ = 1 := by
            rw [mul_one, ← Real.rpow_add hε0]
            norm_num
      calc (ε ^ c₃ * x_sp ^ c₃ * (Fintype.card V : ℝ)) ^ c_A
        _ ≤ (1 : ℝ) ^ c_A := Real.rpow_le_rpow (by positivity) hprod_le1 hc_A.le
        _ = 1 := Real.one_rpow c_A
        _ ≤ (kappa G : ℝ) := hkappa_ge1
  · push_neg at hV_small
    have hV_ne : (Finset.univ : Finset V).Nonempty := by
      rw [Finset.univ_nonempty_iff, ← Fintype.card_pos_iff]
      have : (0 : ℝ) < (Fintype.card V : ℝ) := lt_trans (by positivity) hV_small
      exact_mod_cast this
    let x_in : ℝ := x_sp * ε ^ (4 * d)
    have hx_in_pos : 0 < x_in := by dsimp [x_in]; positivity
    -- Either every F ⊆ univ of size ≥ ε^d |V| has a weakly x_in-sparse-or-co-sparse blockade (giving GN1 via Lemma 5),
    -- or some F fails this, in which case multi-scale sparsification gives (GN2) or (GN4).
    by_cases hall_F : ∀ F ⊆ (Finset.univ : Finset V),
        ε ^ d * ((Finset.univ : Finset V).card : ℝ) ≤ (F.card : ℝ) →
        ∃ (k : ℕ) (B : Fin k → Finset V),
          2 ≤ k ∧ k ≤ ⌈ε ^ (-20 * d * C_cap)⌉₊ ∧
          IsWeaklySparseOrCoSparseBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ d)
            (x_sp * ε ^ (4 * d)) B
    · left
      simpa [Finset.card_univ] using
        symmetric_layout_refinement_xsp_indep G Finset.univ hε0 hε_half hd1 hC_cap
          hx_sp_pos.le hV_ne hall_F
    · push_neg at hall_F
      obtain ⟨F, hF_sub, hF_card, hF_no_block⟩ := hall_F
      rw [Finset.card_univ] at hF_card
      let lam0 := lambda0Param (2 * b_leaf)
      let lam_cut := cParam (2 * b_leaf) * ε ^ (6 : ℝ)
      let b₂ := b2Param a_leaf (2 * b_leaf) δ
      let b₃ := b3Param a_leaf
      have hc_pos : 0 < cParam (2 * b_leaf) := cParam_pos _
      have hlam_cut_pos : 0 < lam_cut := by dsimp [lam_cut]; positivity
      obtain ⟨F₀, hF₀_sub, hF₀_rest, hF₀_card⟩ :=
        rodl_initial_step_for_symm_gen_nice G H₁ hG₁ F a_leaf b_leaf
      have hterm_bounds :=
        symm_gen_nice_terminal_card_ge ha_leaf hb_leaf hC_comb hC_cap hc_B hε0 hε_half
          (by simpa [Finset.card_univ] using hF_card) hF₀_card
      rw [Finset.card_univ] at hterm_bounds
      by_cases hlam_cmp : lam_cut < lam0
      · -- Multi-scale sparsification from lam0 down to lam_cut
        let O : Finset V → Prop := fun _ =>
          ((ε ^ c₃ * x_sp ^ c₃ * (Fintype.card V : ℝ)) ^ c_A ≤ (kappa G : ℝ)) ∨
          (∃ (k : ℕ) (B : Fin k → Finset V),
            2 ≤ k ∧ k ≤ ⌈ε ^ (-20 * d * C_cap)⌉₊ ∧
            IsWeaklySparseOrCoSparseBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ d)
              (x_sp * ε ^ (4 * d)) B)
        have hstep : ∀ lam ∈ Set.Icc lam_cut lam0, ∀ F_t ⊆ F₀,
            IsEpsRestrictedOn G F_t lam → lam ^ b₂ * (F₀.card : ℝ) ≤ (F_t.card : ℝ) →
              O F_t ∨ ∃ F'' ⊆ F_t, IsEpsRestrictedOn G F'' (lam ^ b1Param) ∧
                lam ^ b₃ * (F_t.card : ℝ) ≤ (F''.card : ℝ) := by
          intro lam hlam_mem F_t hFt_sub hFt_rest hFt_card
          have hlam_pos : 0 < lam := hlam_cut_pos.trans_le hlam_mem.1
          have hlam_le : lam ≤ lam0 := hlam_mem.2
          let y := localSparsityY (2 * b_leaf) lam
          have hy_pos : 0 < y := localSparsityY_pos (2 * b_leaf) hlam_pos
          have hy_ge_eps2 : ε ^ 2 ≤ y := localSparsityY_ge_eps_sq b_leaf hε0 hlam_mem.1
          have hy_48 : y ≤ (2 : ℝ) ^ (-48 : ℝ) :=
            localSparsityY_le_two_rpow_neg_48 (2 * b_leaf) hlam_pos.le hlam_le
          have hy_le_c : y ≤ (2 : ℝ) ^ (-4 * b_leaf) := by
            have hy_c3 : y ≤ (cParam (2 * b_leaf)) ^ (3 : ℝ) :=
              localSparsityY_le_cParam_cube (2 * b_leaf) hlam_pos.le hlam_le
            have hc_le1 : cParam (2 * b_leaf) ≤ 1 :=
              (cParam_lt_half (2 * b_leaf)).le.trans (by norm_num)
            have hc3_le_c : (cParam (2 * b_leaf)) ^ (3 : ℝ) ≤ cParam (2 * b_leaf) := by
              calc (cParam (2 * b_leaf)) ^ (3 : ℝ)
                _ ≤ (cParam (2 * b_leaf)) ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_ge hc_pos hc_le1 (by norm_num)
                _ = cParam (2 * b_leaf) := Real.rpow_one _
            have hc_le_4b : cParam (2 * b_leaf) ≤ (2 : ℝ) ^ (-4 * b_leaf) := by
              rw [cParam_two_mul_eq hb_leaf]
              exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            exact hy_c3.trans (hc3_le_c.trans hc_le_4b)
          obtain ⟨hy_a2_Ft_ge2, hy_a2_c_Ft_ge2, hc_Ft_ge_V⟩ :=
            symm_gen_nice_sub_card_ge ha_leaf hb_leaf hC_comb hC_cap hc_B hε0 hε_half
              hlam_mem.1 hV_small.le hF_card hF₀_card hFt_card
          let w₁ := ⌊y ^ (a_leaf + 2) * (F_t.card : ℝ)⌋₊
          have hw₁_pos : 1 ≤ w₁ := Nat.floor_pos.mpr (by linarith)
          -- Case split on whether every F' ⊆ F_t (|F'| ≥ c |F_t|) satisfies Lemma 4(1)'s trigger condition
          by_cases htrig : ∀ F' ⊆ F_t, (2 : ℝ) ^ (-4 * b_leaf) * (F_t.card : ℝ) ≤ (F'.card : ℝ) →
              ∃ X ⊆ F', ∃ Y ⊆ F', Disjoint X Y ∧
                (1 - b_leaf * y) * (F'.card : ℝ) ≤ (Y.card : ℝ) ∧
                ((X.card = w₁ ∧ (IsCompletePair G X Y ∨ IsXSparseTo G Y X x_in)) ∨
                 (y ^ a_leaf * (F'.card : ℝ) ≤ (X.card : ℝ) ∧ IsPurePair G X Y))
          · -- Every F' has a trigger pair -> Lemma 4(1) produces an (⌈y⁻¹⌉₊, w₁)-blockade satisfying O
            left; right
            obtain ⟨B, J, hB_block, _, _, hB_pairs, _, _⟩ :=
              equal_sized_trigger_peeling_cograph G F_t a_leaf b_leaf y x_in
                (by linarith) (by linarith) hx_in_pos.le hy_pos hy_le_c
                (by linarith) htrig
            let k := ⌈y⁻¹⌉₊
            have hk2 : 2 ≤ k := by
              have hy_inv_gt2 : 2 < y⁻¹ := by
                rw [lt_inv_comm₀ zero_lt_two hy_pos]
                have h48_lt : (2 : ℝ) ^ (-48 : ℝ) < (2 : ℝ)⁻¹ := by
                  rw [← Real.rpow_neg_one]
                  exact Real.rpow_lt_rpow_of_exponent_lt one_lt_two (by norm_num)
                exact hy_48.trans_lt h48_lt
              have : (2 : ℝ) < (k : ℝ) := hy_inv_gt2.trans_le (Nat.le_ceil _)
              exact_mod_cast this.le
            have hk_le_kmax : k ≤ ⌈ε ^ (-20 * d * C_cap)⌉₊ :=
              ceil_inv_localSparsityY_le_kmax b_leaf hε0 hε_half hd120 hC_cap hlam_mem.1
            have hw_ge : (F.card : ℝ) / (k : ℝ) ^ d ≤ (w₁ : ℝ) :=
              symm_gen_nice_peel_width_ge ha_leaf hb_leaf hC_comb hc_B hlam_pos hlam_le
                hF₀_card hFt_card hy_a2_Ft_ge2
            refine ⟨k, B, hk2, hk_le_kmax, ?_⟩
            refine ⟨(hB_block.mono_ambient (hFt_sub.trans hF₀_sub)).mono_width hw_ge, ?_⟩
            intro i j hij
            by_cases hadj : J.Adj i j
            · right
              have hcomp := (hB_pairs i j hij).1 hadj
              have h0 : IsXSparseTo Gᶜ (B i) (B j) 0 := by
                intro u hu
                have hemp : neighborFinsetIn Gᶜ u (B j) = ∅ := by
                  rw [eq_empty_iff_forall_notMem]
                  intro v hv
                  rw [mem_neighborFinsetIn', SimpleGraph.compl_adj] at hv
                  exact hv.2.2 (hcomp u hu v hv.1)
                rw [hemp]; simp
              exact (isWeaklySparsePair_of_isXSparseTo h0).mono hx_in_pos.le
            · exact Or.inl ((hB_pairs i j hij).2 hadj)
          · -- Some F' ⊆ F_t fails the trigger condition
            push_neg at htrig
            obtain ⟨F', hF'_sub, hF'_4b, hF'_no_trig⟩ := htrig
            have hc_le_4b : cParam (2 * b_leaf) ≤ (2 : ℝ) ^ (-4 * b_leaf) := by
              rw [cParam_two_mul_eq hb_leaf]
              exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            have hF'_c : cParam (2 * b_leaf) * (F_t.card : ℝ) ≤ (F'.card : ℝ) :=
              (mul_le_mul_of_nonneg_right hc_le_4b (Nat.cast_nonneg _)).trans hF'_4b
            have hF'_rest : IsEpsRestrictedOn G F' (y ^ 3) :=
              isEpsRestrictedOn_localSparsityY_cube_of_subset G F_t F' (2 * b_leaf)
                hlam_pos.le hF'_sub hF'_c hFt_rest
            have hy_a2_F'_ge1 : 1 ≤ y ^ (a_leaf + 2) * (F'.card : ℝ) := by
              calc (1 : ℝ) ≤ 2 := by norm_num
                _ ≤ y ^ (a_leaf + 2) * (cParam (2 * b_leaf) * (F_t.card : ℝ)) := hy_a2_c_Ft_ge2
                _ ≤ y ^ (a_leaf + 2) * (F'.card : ℝ) :=
                  mul_le_mul_of_nonneg_left hF'_c (by positivity)
            rcases hF'_rest with h_sparse | h_cosparse
            · -- Subcase B2: F' is y^3-sparse in G -> apply upside_down_comb_extraction at x_3 = x_in^2
              let x_3 := x_in ^ 2
              have hx_3_pos : 0 < x_3 := sq_pos_of_pos hx_in_pos
              have hx_in_le_y : x_in ≤ y := by
                have hx_in_le : x_in ≤ ε ^ (4 * d + 6) := by
                  dsimp [x_in]
                  calc x_sp * ε ^ (4 * d)
                    _ ≤ ε ^ (6 : ℝ) * ε ^ (4 * d) :=
                      mul_le_mul_of_nonneg_right hx_hi (by positivity)
                    _ = ε ^ (4 * d + 6) := by rw [← Real.rpow_add hε0]; congr 1; ring
                have hε_le : ε ^ (4 * d + 6) ≤ ε ^ 2 := by
                  rw [← Real.rpow_natCast ε 2]
                  exact Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (by push_cast; linarith)
                exact hx_in_le.trans (hε_le.trans hy_ge_eps2)
              have hx_3_le_x_in : x_3 ≤ x_in := by
                dsimp [x_3]
                have hy_le1 : y ≤ 1 := hy_48.trans (by norm_num)
                nlinarith [hx_in_le_y.trans hy_le1]
              have hx_3_le_y : x_3 ≤ y := hx_3_le_x_in.trans hx_in_le_y
              have hy_inv16 : y ≤ (2 : ℝ)⁻¹ ^ 16 :=
                hy_48.trans (by norm_num : (2 : ℝ) ^ (-48 : ℝ) ≤ (2 : ℝ)⁻¹ ^ 16)
              have hy_inv8 : y ≤ (2 : ℝ)⁻¹ ^ 8 :=
                hy_48.trans (by norm_num : (2 : ℝ) ^ (-48 : ℝ) ≤ (2 : ℝ)⁻¹ ^ 8)
              have hF'_y4 : y⁻¹ ^ 4 ≤ (F'.card : ℝ) := by
                have hy_le1 : y ≤ 1 := hy_48.trans (by norm_num)
                have h1 : y ^ (a_leaf + 2) ≤ y ^ (4 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_ge hy_pos hy_le1 (by linarith)
                have h2 : 1 ≤ y ^ (4 : ℝ) * (F'.card : ℝ) :=
                  hy_a2_F'_ge1.trans (mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _))
                rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h2
                rw [inv_pow]
                exact (inv_le_iff_one_le_mul₀' (by positivity)).mpr h2
              rcases upside_down_comb_extraction G F' x_3 y hx_3_pos hx_3_le_y hy_inv8 h_sparse hF'_y4 with
                h_2y4 | ⟨X₀, Y₀, hX₀F', hY₀F', hdisj₀, hX₀_card, hY₀_card, hY₀_sparse⟩ |
                ⟨ℓ, a, B_comb, v, hℓ_lo, hℓ_hi, hcomb, hapex⟩
              · -- Outcome 1 of Lemma 3: F' is 2y^4-sparse -> advances multi-scale step
                right
                refine ⟨F', hF'_sub,
                  Or.inl (h_2y4.mono (two_mul_localSparsityY_pow_four_nat_le (2 * b_leaf) hlam_pos.le hlam_le)),
                  ?_⟩
                exact (mul_le_mul_of_nonneg_right
                  (lam_b3Param_le_cParam a_leaf (2 * b_leaf) hlam_pos.le hlam_le)
                  (Nat.cast_nonneg _)).trans hF'_c
              · -- Outcome 2 of Lemma 3: Markov exact-size restoration contradicts hF'_no_trig
                exfalso
                have hw₁_le_X₀ : w₁ ≤ X₀.card := by
                  have hw₁_real : (w₁ : ℝ) ≤ y ^ (a_leaf + 2) * (F_t.card : ℝ) :=
                    Nat.floor_le (by positivity)
                  have hy_sub_le_4b : y ^ (a_leaf - 2) ≤ (2 : ℝ) ^ (-4 * b_leaf) := by
                    have hy_le1 : y ≤ 1 := hy_48.trans (by norm_num)
                    calc y ^ (a_leaf - 2)
                      _ ≤ y ^ (1 : ℝ) :=
                        Real.rpow_le_rpow_of_exponent_ge hy_pos hy_le1 (by linarith)
                      _ = y := Real.rpow_one y
                      _ ≤ (2 : ℝ) ^ (-4 * b_leaf) := hy_le_c
                  have h_chain : (w₁ : ℝ) ≤ (X₀.card : ℝ) := by
                    calc (w₁ : ℝ)
                      _ ≤ y ^ (a_leaf + 2) * (F_t.card : ℝ) := hw₁_real
                      _ = y ^ (4 : ℝ) * (y ^ (a_leaf - 2) * (F_t.card : ℝ)) := by
                        rw [show a_leaf + 2 = 4 + (a_leaf - 2) by ring, Real.rpow_add hy_pos]; ring
                      _ ≤ y ^ (4 : ℝ) * ((2 : ℝ) ^ (-4 * b_leaf) * (F_t.card : ℝ)) := by
                        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                        exact mul_le_mul_of_nonneg_right hy_sub_le_4b (Nat.cast_nonneg _)
                      _ ≤ y ^ (4 : ℝ) * (F'.card : ℝ) :=
                        mul_le_mul_of_nonneg_left hF'_4b (by positivity)
                      _ = y ^ 4 * (F'.card : ℝ) := by
                        rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
                      _ ≤ (X₀.card : ℝ) := hX₀_card
                  exact_mod_cast h_chain
                obtain ⟨X, hXF', Y, hYF', hdisj_XY, hX_card, hY_card, hXY_sparse⟩ :=
                  markov_pointwise_sparse_exact_size G F' X₀ Y₀ w₁ x_in y b_leaf
                    hw₁_pos hw₁_le_X₀ hx_in_pos hx_in_le_y (by linarith)
                    hX₀F' hY₀F' hdisj₀ hY₀_card hY₀_sparse
                exact ((hF'_no_trig X hXF' Y hYF' hdisj_XY hY_card).1 hX_card).2 hXY_sparse
              · -- Outcome 3 of Lemma 3: Comb Dichotomy on F' at x_3 = x_in^2
                left
                have hℓ_64 : 64 ≤ ℓ := by
                  have h1 : y ^ (1 / 4 : ℝ) ≤ ((2 : ℝ) ^ (-48 : ℝ)) ^ (1 / 4 : ℝ) :=
                    Real.rpow_le_rpow hy_pos.le hy_48 (by norm_num)
                  have h2 : ((2 : ℝ) ^ (-48 : ℝ)) ^ (1 / 4 : ℝ) = (2 : ℝ) ^ (-12 : ℝ) := by
                    rw [← Real.rpow_mul two_pos.le]; norm_num
                  have h3 : (2 : ℝ) ^ (12 : ℝ) ≤ (y ^ (1 / 4 : ℝ))⁻¹ := by
                    rw [show (2 : ℝ) ^ (12 : ℝ) = ((2 : ℝ) ^ (-12 : ℝ))⁻¹ by
                      rw [← Real.rpow_neg two_pos.le]; norm_num]
                    exact inv_anti₀ (by positivity) (h1.trans_eq h2)
                  have h4 : (64 : ℝ) ≤ (ℓ : ℝ) := by
                    have h64 : (64 : ℝ) ≤ (2 : ℝ) ^ (12 : ℝ) := by norm_num
                    rw [Real.rpow_neg hy_pos.le] at hℓ_lo
                    exact h64.trans (h3.trans hℓ_lo)
                  exact_mod_cast h4
                rcases h_comb_dichotomy V G F' x_3 y ℓ a B_comb v hG₁ hG₂
                    hx_3_pos hx_3_le_y hy_inv16 hℓ_lo hℓ_hi hℓ_64 hcomb hapex with
                  hCD1 | ⟨k, hk2, hk_lo, hk_hi, U, hU⟩
                · -- (CD1) -> (GN2)
                  left
                  exact le_trans
                    (symm_gen_nice_cd1_bound hd120 hC_comb hC_cap hc_A hε0 hε1
                      hx_sp_pos hx_sp_le1 (Nat.cast_nonneg _) hy_pos hℓ_lo hℓ_hi
                      (hc_Ft_ge_V.trans hF'_c))
                    hCD1
                · -- (CD2) or (CD3) -> satisfies property O
                  right
                  have hk_le_kmax : k ≤ ⌈ε ^ (-20 * d * C_cap)⌉₊ :=
                    symm_gen_nice_cd23_kmax hd120 hC_cap hε0 hε1 hx_lo hk_hi
                  have hw_comb : (F.card : ℝ) / (k : ℝ) ^ d ≤
                      (F'.card : ℝ) / (k : ℝ) ^ C_comb :=
                    symm_gen_nice_comb_width_ge ha_leaf hb_leaf hC_comb hc_B hlam_pos
                      hF₀_card hFt_card hF'_c hℓ_lo hk2 hk_lo
                  have hU_weak : IsWeaklySparseOrCoSparseBlockadeIn G F' k
                      ((F'.card : ℝ) / (k : ℝ) ^ C_comb) x_3 U := by
                    rcases hU with hU_pure | hU_wk
                    · exact isWeaklySparseOrCoSparseBlockadeIn_of_isPureBlockadeIn hx_3_pos.le hU_pure
                    · exact hU_wk
                  exact ⟨k, U, hk2, hk_le_kmax,
                    hU_weak.mono_sub_width_defect (hF'_sub.trans (hFt_sub.trans hF₀_sub))
                      hw_comb hx_3_le_x_in⟩
            · -- Subcase B1: F' is y^3-co-sparse -> h_cosparse_peel gives y^4-restricted subset
              right
              rcases h_cosparse_peel V G F' y hG₁ hG₂ hy_pos hy_le_c hy_a2_F'_ge1 h_cosparse with
                ⟨U, hUF', hU_rest, hU_card⟩ | ⟨X, hXF', Y, hYF', hdisj_XY, hX_card, hY_card, hcomp⟩
              · refine ⟨U, hUF'.trans hF'_sub,
                  hU_rest.mono (localSparsityY_pow_four_nat_le (2 * b_leaf) hlam_pos.le hlam_le),
                  ?_⟩
                have hlam_b3 := lam_b3Param_le_cParam_mul_y_rpow ha_leaf hlam_pos.le hlam_le
                calc lam ^ b₃ * (F_t.card : ℝ)
                  _ ≤ (cParam (2 * b_leaf) * y ^ a_leaf) * (F_t.card : ℝ) :=
                    mul_le_mul_of_nonneg_right hlam_b3 (Nat.cast_nonneg _)
                  _ = y ^ a_leaf * (cParam (2 * b_leaf) * (F_t.card : ℝ)) := by ring
                  _ ≤ y ^ a_leaf * (F'.card : ℝ) :=
                    mul_le_mul_of_nonneg_left hF'_c (by positivity)
                  _ ≤ (U.card : ℝ) := hU_card
              · exfalso
                exact (hF'_no_trig X hXF' Y hYF' hdisj_XY hY_card).2 hX_card (Or.inl hcomp)
        rcases lem_multiscale_sparsification G F₀ O
            (lambda0Param_pos (2 * b_leaf)) (lambda0Param_lt_half (2 * b_leaf))
            hlam_cut_pos hlam_cmp
            one_lt_b1Param (b2Param_pos a_leaf (2 * b_leaf) δ) (b3Param_pos a_leaf)
            (gen_nice_exponent_ineq a_leaf (2 * b_leaf) δ) hF₀_rest hstep with
          ⟨F_t, _, hOF_t⟩ | ⟨S_cut, _, hS_rest, hS_card⟩
        · rcases hOF_t with hGN2 | ⟨k, B, hk2, hk_le, hB⟩
          · exact Or.inr (Or.inl hGN2)
          · exact False.elim (hF_no_block k B hk2 hk_le hB)
        · right; right; right
          have hcut_le : lam_cut ≤ 2 * ε ^ (6 : ℝ) := by
            dsimp [lam_cut]
            have : cParam (2 * b_leaf) ≤ 2 := (cParam_lt_half _).le.trans (by norm_num)
            exact mul_le_mul_of_nonneg_right this (by positivity)
          exact ⟨S_cut, hS_rest.mono hcut_le, hterm_bounds.1.trans hS_card⟩
      · -- lam0 ≤ lam_cut < 2 * ε^6 -> F₀ immediately satisfies (GN4)
        push_neg at hlam_cmp
        right; right; right
        have hlam0_le : lam0 ≤ 2 * ε ^ (6 : ℝ) := by
          refine hlam_cmp.trans ?_
          dsimp [lam_cut]
          have : cParam (2 * b_leaf) ≤ 2 := (cParam_lt_half _).le.trans (by norm_num)
          exact mul_le_mul_of_nonneg_right this (by positivity)
        exact ⟨F₀, hF₀_rest.mono hlam0_le, hterm_bounds.2⟩

/--
**Lemma 7(1) (`pair_coupled_generalized_nice_of_comb_dichotomy`, `main.tex` lines 288–331)**:
Let $\{H_1, H_2\}$ be a finite two-graph family ($|H_1| \ge 2$) satisfying the co-sparse peeling
property (`h_cosparse_peel` at $a_{\mathrm{leaf}}, b_{\mathrm{leaf}} \ge 6$) and the Stage-1 Comb
Dichotomy `(CD1)`–`(CD3)` (`h_comb_dichotomy` at $C_{\mathrm{comb}} \ge 18$, $C_{\mathrm{cap}} \ge 2$,
and $c_{\mathrm{A}}, c_{\mathrm{B}} > 0$). Then $\{H_1, H_2\}$ is coupled Stage-1 generalized nice
(`IsPairCoupledGeneralizedNice H₁ H₂`, Definition 2(3) of `main.tex`), deduced directly from
`pair_coupled_generalized_nice_of_comb_dichotomy_explicit`.
-/
theorem pair_coupled_generalized_nice_of_comb_dichotomy
    {W₁ W₂ : Type*} [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]
    (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂)
    (hh₁ : 2 ≤ Fintype.card W₁)
    (a_leaf b_leaf C_comb C_cap c_A c_B : ℝ)
    (ha_leaf : 6 ≤ a_leaf) (hb_leaf : 6 ≤ b_leaf)
    (hC_comb : 18 ≤ C_comb) (hC_cap : 2 ≤ C_cap)
    (hc_A : 0 < c_A) (hc_B : 0 < c_B)
    (h_cosparse_peel : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      (F' : Finset V) (y : ℝ),
      IsInducedSubgraphFree G H₁ᶜ → IsInducedSubgraphFree G H₂ᶜ →
      0 < y → y ≤ (2 : ℝ) ^ (-4 * b_leaf) →
      1 ≤ y ^ (a_leaf + 2) * (F'.card : ℝ) →
      IsEpsSparseOn Gᶜ F' (y ^ 3) →
        (∃ U ⊆ F', IsEpsRestrictedOn G U (y ^ 4) ∧
          y ^ a_leaf * (F'.card : ℝ) ≤ (U.card : ℝ)) ∨
        (∃ X ⊆ F', ∃ Y ⊆ F', Disjoint X Y ∧
          y ^ a_leaf * (F'.card : ℝ) ≤ (X.card : ℝ) ∧
          (1 - b_leaf * y) * (F'.card : ℝ) ≤ (Y.card : ℝ) ∧
          IsCompletePair G X Y))
    (h_comb_dichotomy : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      (F' : Finset V) (x y : ℝ) (ℓ : ℕ) (a : Fin ℓ → V) (B : Fin ℓ → Finset V) (v : V),
      IsInducedSubgraphFree G H₁ᶜ → IsInducedSubgraphFree G H₂ᶜ →
      0 < x → x ≤ y → y ≤ (2 : ℝ)⁻¹ ^ 16 →
      y ^ (-(1 / 4 : ℝ)) ≤ (ℓ : ℝ) → (ℓ : ℝ) ≤ x⁻¹ → 64 ≤ ℓ →
      IsCombIn G F' ℓ (y ^ 4 * (F'.card : ℝ) / (ℓ : ℝ) ^ 2) a B →
      IsCombExternalApex G F' ℓ a B v →
        ((y ^ 4 * (F'.card : ℝ) / (ℓ : ℝ) ^ 2) ^ c_A ≤ (kappa G : ℝ)) ∨
        (∃ k : ℕ, 2 ≤ k ∧ (1 / 2 : ℝ) * (ℓ : ℝ) ^ c_B ≤ (k : ℝ) ∧ k ≤ ⌈x ^ (-C_cap)⌉₊ ∧
          ∃ U : Fin k → Finset V,
            IsPureBlockadeIn G F' k ((F'.card : ℝ) / (k : ℝ) ^ C_comb) U ∨
            IsWeaklySparseOrCoSparseBlockadeIn G F' k ((F'.card : ℝ) / (k : ℝ) ^ C_comb) x U)) :
    IsPairCoupledGeneralizedNice H₁ H₂ :=
  (pair_coupled_generalized_nice_of_comb_dichotomy_explicit H₁ H₂ hh₁
    a_leaf b_leaf C_comb C_cap c_A c_B ha_leaf hb_leaf hC_comb hC_cap hc_A hc_B
    h_cosparse_peel h_comb_dichotomy).to_isPairCoupledGeneralizedNice

/--
**Single-Graph Lemma 7(1) (`coupled_generalized_nice_of_comb_dichotomy`, `main.tex` lines 288–331)**:
Let $H$ (`SimpleGraph W`, $|W| \ge 2$) satisfy the co-sparse peeling property (`h_cosparse_peel` at
$a_{\mathrm{leaf}}, b_{\mathrm{leaf}} \ge 6$) and the Stage-1 Comb Dichotomy `(CD1)`–`(CD3)`
(`h_comb_dichotomy` at $C_{\mathrm{comb}} \ge 18$, $C_{\mathrm{cap}} \ge 2$, and $c_{\mathrm{A}}, c_{\mathrm{B}} > 0$).
Then $H$ is coupled Stage-1 generalized nice (`IsCoupledGeneralizedNice H`, Definition 2(3) of `main.tex`).
-/
theorem coupled_generalized_nice_of_comb_dichotomy
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W)
    (hh : 2 ≤ Fintype.card W)
    (a_leaf b_leaf C_comb C_cap c_A c_B : ℝ)
    (ha_leaf : 6 ≤ a_leaf) (hb_leaf : 6 ≤ b_leaf)
    (hC_comb : 18 ≤ C_comb) (hC_cap : 2 ≤ C_cap)
    (hc_A : 0 < c_A) (hc_B : 0 < c_B)
    (h_cosparse_peel : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      (F' : Finset V) (y : ℝ),
      IsInducedSubgraphFree G Hᶜ →
      0 < y → y ≤ (2 : ℝ) ^ (-4 * b_leaf) →
      1 ≤ y ^ (a_leaf + 2) * (F'.card : ℝ) →
      IsEpsSparseOn Gᶜ F' (y ^ 3) →
        (∃ U ⊆ F', IsEpsRestrictedOn G U (y ^ 4) ∧
          y ^ a_leaf * (F'.card : ℝ) ≤ (U.card : ℝ)) ∨
        (∃ X ⊆ F', ∃ Y ⊆ F', Disjoint X Y ∧
          y ^ a_leaf * (F'.card : ℝ) ≤ (X.card : ℝ) ∧
          (1 - b_leaf * y) * (F'.card : ℝ) ≤ (Y.card : ℝ) ∧
          IsCompletePair G X Y))
    (h_comb_dichotomy : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      (F' : Finset V) (x y : ℝ) (ℓ : ℕ) (a : Fin ℓ → V) (B : Fin ℓ → Finset V) (v : V),
      IsInducedSubgraphFree G Hᶜ →
      0 < x → x ≤ y → y ≤ (2 : ℝ)⁻¹ ^ 16 →
      y ^ (-(1 / 4 : ℝ)) ≤ (ℓ : ℝ) → (ℓ : ℝ) ≤ x⁻¹ → 64 ≤ ℓ →
      IsCombIn G F' ℓ (y ^ 4 * (F'.card : ℝ) / (ℓ : ℝ) ^ 2) a B →
      IsCombExternalApex G F' ℓ a B v →
        ((y ^ 4 * (F'.card : ℝ) / (ℓ : ℝ) ^ 2) ^ c_A ≤ (kappa G : ℝ)) ∨
        (∃ k : ℕ, 2 ≤ k ∧ (1 / 2 : ℝ) * (ℓ : ℝ) ^ c_B ≤ (k : ℝ) ∧ k ≤ ⌈x ^ (-C_cap)⌉₊ ∧
          ∃ U : Fin k → Finset V,
            IsPureBlockadeIn G F' k ((F'.card : ℝ) / (k : ℝ) ^ C_comb) U ∨
            IsWeaklySparseOrCoSparseBlockadeIn G F' k ((F'.card : ℝ) / (k : ℝ) ^ C_comb) x U)) :
    IsCoupledGeneralizedNice H :=
  isCoupledGeneralizedNice_of_pair <|
    pair_coupled_generalized_nice_of_comb_dichotomy H H hh
      a_leaf b_leaf C_comb C_cap c_A c_B ha_leaf hb_leaf hC_comb hC_cap hc_A hc_B
      (fun V _ _ G F' y hG _ => h_cosparse_peel V G F' y hG)
      (fun V _ _ G F' x y ℓ a B v hG _ => h_comb_dichotomy V G F' x y ℓ a B v hG)

/--
**Path Specialization of Lemma 7(1) (`pair_coupled_generalized_nice_of_path_comb_dichotomy`,
`main.tex` line 299)**:
When $H_1 = P_t$ (`pathGraph t`, $t \ge 2$), Lemma 2 (`pkCompl_free_cosparse_trigger_pair`)
automatically discharges the co-sparse peeling hypothesis with $a_{\mathrm{leaf}} = 6$ and
$b_{\mathrm{leaf}} = 3 t \ge 6$.
-/
theorem pair_coupled_generalized_nice_of_path_comb_dichotomy
    {W₂ : Type*} [Fintype W₂] [DecidableEq W₂]
    (t : ℕ) (ht : 2 ≤ t) (H₂ : SimpleGraph W₂)
    (C_comb C_cap c_A c_B : ℝ)
    (hC_comb : 18 ≤ C_comb) (hC_cap : 2 ≤ C_cap)
    (hc_A : 0 < c_A) (hc_B : 0 < c_B)
    (h_comb_dichotomy : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      (F' : Finset V) (x y : ℝ) (ℓ : ℕ) (a : Fin ℓ → V) (B : Fin ℓ → Finset V) (v : V),
      IsInducedSubgraphFree G (pathGraph t)ᶜ → IsInducedSubgraphFree G H₂ᶜ →
      0 < x → x ≤ y → y ≤ (2 : ℝ)⁻¹ ^ 16 →
      y ^ (-(1 / 4 : ℝ)) ≤ (ℓ : ℝ) → (ℓ : ℝ) ≤ x⁻¹ → 64 ≤ ℓ →
      IsCombIn G F' ℓ (y ^ 4 * (F'.card : ℝ) / (ℓ : ℝ) ^ 2) a B →
      IsCombExternalApex G F' ℓ a B v →
        ((y ^ 4 * (F'.card : ℝ) / (ℓ : ℝ) ^ 2) ^ c_A ≤ (kappa G : ℝ)) ∨
        (∃ k : ℕ, 2 ≤ k ∧ (1 / 2 : ℝ) * (ℓ : ℝ) ^ c_B ≤ (k : ℝ) ∧ k ≤ ⌈x ^ (-C_cap)⌉₊ ∧
          ∃ U : Fin k → Finset V,
            IsPureBlockadeIn G F' k ((F'.card : ℝ) / (k : ℝ) ^ C_comb) U ∨
            IsWeaklySparseOrCoSparseBlockadeIn G F' k ((F'.card : ℝ) / (k : ℝ) ^ C_comb) x U)) :
    IsPairCoupledGeneralizedNice (pathGraph t) H₂ := by
  have hh₁ : 2 ≤ Fintype.card (Fin t) := by rw [Fintype.card_fin]; exact ht
  have hb_leaf : 6 ≤ 3 * (t : ℝ) := by
    have : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    linarith
  refine pair_coupled_generalized_nice_of_comb_dichotomy (pathGraph t) H₂ hh₁
    6 (3 * (t : ℝ)) C_comb C_cap c_A c_B le_rfl hb_leaf hC_comb hC_cap hc_A hc_B ?_ h_comb_dichotomy
  intro V _ _ G F' y hG₁ _ hy0 hy_le hy_F' h_cosparse
  right
  have hy_le1 : y ≤ 1 := by
    have h1 : (2 : ℝ) ^ (-4 * (3 * (t : ℝ))) ≤ (2 : ℝ) ^ (-24 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h2 : (2 : ℝ) ^ (-24 : ℝ) ≤ 1 := by norm_num
    exact hy_le.trans (h1.trans h2)
  have hy_le_t : y ≤ 1 / (12 * (t : ℝ)) := by
    have h12t : 12 * (t : ℝ) ≤ (2 : ℝ) ^ (12 * (t : ℝ)) := by
      have ht2 : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
      have hlin : 12 * (t : ℝ) ≤ (2 : ℝ) ^ (12 : ℝ) * (t : ℝ) := by norm_num; linarith
      have ht_nat : t ≤ 2 ^ t := Nat.lt_two_pow_self.le
      have ht_real : (t : ℝ) ≤ (2 : ℝ) ^ (t : ℝ) := by
        rw [Real.rpow_natCast]; exact_mod_cast ht_nat
      have hexp : (2 : ℝ) ^ (12 : ℝ) * (t : ℝ) ≤ (2 : ℝ) ^ (12 * (t : ℝ)) := by
        calc (2 : ℝ) ^ (12 : ℝ) * (t : ℝ)
          _ ≤ (2 : ℝ) ^ (12 : ℝ) * (2 : ℝ) ^ (t : ℝ) :=
            mul_le_mul_of_nonneg_left ht_real (by positivity)
          _ = (2 : ℝ) ^ (12 + (t : ℝ)) := (Real.rpow_add two_pos 12 (t : ℝ)).symm
          _ ≤ (2 : ℝ) ^ (12 * (t : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      exact hlin.trans hexp
    have hy_neg : y ≤ (2 : ℝ) ^ (-(12 * (t : ℝ))) := by
      convert hy_le using 2; ring
    rw [Real.rpow_neg (by norm_num), ← one_div] at hy_neg
    exact hy_neg.trans (one_div_le_one_div_of_le (by positivity) h12t)
  have hy2_F' : 1 / y ^ 2 ≤ (F'.card : ℝ) := by
    have h1 : y ^ (6 + 2 : ℝ) ≤ y ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hy0 hy_le1 (by norm_num)
    have h2 : 1 ≤ y ^ 2 * (F'.card : ℝ) := by
      have := hy_F'.trans (mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _))
      rwa [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
    rwa [div_le_iff₀' (by positivity)]
  have hcosparse_y : IsEpsSparseOn Gᶜ F' y := by
    refine h_cosparse.mono ?_
    nlinarith [sq_nonneg y]
  obtain ⟨X, hXF', Y, hYF', hdisj, hX_card, hY_card, hcomp⟩ :=
    pkCompl_free_cosparse_trigger_pair G F' t y ht hG₁ hy0 hy_le_t hy2_F' hcosparse_y
  refine ⟨X, hXF', Y, hYF', hdisj, ?_, hY_card, hcomp⟩
  have hy6_le_y2 : y ^ (6 : ℝ) ≤ y ^ 2 := by
    rw [← Real.rpow_natCast y 2]
    exact Real.rpow_le_rpow_of_exponent_ge hy0 hy_le1 (by norm_num)
  exact (mul_le_mul_of_nonneg_right hy6_le_y2 (Nat.cast_nonneg _)).trans hX_card

/--
**Single-Graph Path Specialization of Lemma 7(1) (`coupled_generalized_nice_of_path_comb_dichotomy`)**:
Deduction of `IsCoupledGeneralizedNice (pathGraph t)` ($t \ge 2$) from the Stage-1 Comb Dichotomy.
-/
theorem coupled_generalized_nice_of_path_comb_dichotomy
    (t : ℕ) (ht : 2 ≤ t)
    (C_comb C_cap c_A c_B : ℝ)
    (hC_comb : 18 ≤ C_comb) (hC_cap : 2 ≤ C_cap)
    (hc_A : 0 < c_A) (hc_B : 0 < c_B)
    (h_comb_dichotomy : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      (F' : Finset V) (x y : ℝ) (ℓ : ℕ) (a : Fin ℓ → V) (B : Fin ℓ → Finset V) (v : V),
      IsInducedSubgraphFree G (pathGraph t)ᶜ →
      0 < x → x ≤ y → y ≤ (2 : ℝ)⁻¹ ^ 16 →
      y ^ (-(1 / 4 : ℝ)) ≤ (ℓ : ℝ) → (ℓ : ℝ) ≤ x⁻¹ → 64 ≤ ℓ →
      IsCombIn G F' ℓ (y ^ 4 * (F'.card : ℝ) / (ℓ : ℝ) ^ 2) a B →
      IsCombExternalApex G F' ℓ a B v →
        ((y ^ 4 * (F'.card : ℝ) / (ℓ : ℝ) ^ 2) ^ c_A ≤ (kappa G : ℝ)) ∨
        (∃ k : ℕ, 2 ≤ k ∧ (1 / 2 : ℝ) * (ℓ : ℝ) ^ c_B ≤ (k : ℝ) ∧ k ≤ ⌈x ^ (-C_cap)⌉₊ ∧
          ∃ U : Fin k → Finset V,
            IsPureBlockadeIn G F' k ((F'.card : ℝ) / (k : ℝ) ^ C_comb) U ∨
            IsWeaklySparseOrCoSparseBlockadeIn G F' k ((F'.card : ℝ) / (k : ℝ) ^ C_comb) x U)) :
    IsCoupledGeneralizedNice (pathGraph t) :=
  isCoupledGeneralizedNice_of_pair <|
    pair_coupled_generalized_nice_of_path_comb_dichotomy t ht (pathGraph t)
      C_comb C_cap c_A c_B hC_comb hC_cap hc_A hc_B
      (fun V _ _ G F' x y ℓ a B v hG _ => h_comb_dichotomy V G F' x y ℓ a B v hG)

/--
**Leaf-Reducible Specialization of Lemma 7(1) (`pair_coupled_generalized_nice_of_leaf_reducible_comb_dichotomy`,
`main.tex` line 299)**:
When $H_1$ ($|H_1| \ge 3$) has a degree-$1$ leaf $v_0$ with unique neighbor $u_0 \neq v_0$ and
$((H_1 - v_0)ᶜ, H_2ᶜ)$ is viral (`IsPairViral`), `leaf_reducible_cosparse_trigger_or_restricted`
automatically discharges the co-sparse peeling hypothesis with $a_{\mathrm{leaf}} = 4 d' |H_1| + 6$
and $b_{\mathrm{leaf}} = 2 |H_1| \ge 6$.
-/
theorem pair_coupled_generalized_nice_of_leaf_reducible_comb_dichotomy
    {W₁ W₂ : Type*} [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]
    (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂)
    (v₀ u₀ : W₁) (hu₀_ne : u₀ ≠ v₀)
    (hleaf : ∀ w : W₁, H₁.Adj v₀ w ↔ w = u₀)
    (hh₁ : 3 ≤ Fintype.card W₁)
    (hviral : IsPairViral (H₁.comap (Subtype.val : {w : W₁ // w ≠ v₀} → W₁))ᶜ H₂ᶜ)
    (C_comb C_cap c_A c_B : ℝ)
    (hC_comb : 18 ≤ C_comb) (hC_cap : 2 ≤ C_cap)
    (hc_A : 0 < c_A) (hc_B : 0 < c_B)
    (h_comb_dichotomy : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      (F' : Finset V) (x y : ℝ) (ℓ : ℕ) (a : Fin ℓ → V) (B : Fin ℓ → Finset V) (v : V),
      IsInducedSubgraphFree G H₁ᶜ → IsInducedSubgraphFree G H₂ᶜ →
      0 < x → x ≤ y → y ≤ (2 : ℝ)⁻¹ ^ 16 →
      y ^ (-(1 / 4 : ℝ)) ≤ (ℓ : ℝ) → (ℓ : ℝ) ≤ x⁻¹ → 64 ≤ ℓ →
      IsCombIn G F' ℓ (y ^ 4 * (F'.card : ℝ) / (ℓ : ℝ) ^ 2) a B →
      IsCombExternalApex G F' ℓ a B v →
        ((y ^ 4 * (F'.card : ℝ) / (ℓ : ℝ) ^ 2) ^ c_A ≤ (kappa G : ℝ)) ∨
        (∃ k : ℕ, 2 ≤ k ∧ (1 / 2 : ℝ) * (ℓ : ℝ) ^ c_B ≤ (k : ℝ) ∧ k ≤ ⌈x ^ (-C_cap)⌉₊ ∧
          ∃ U : Fin k → Finset V,
            IsPureBlockadeIn G F' k ((F'.card : ℝ) / (k : ℝ) ^ C_comb) U ∨
            IsWeaklySparseOrCoSparseBlockadeIn G F' k ((F'.card : ℝ) / (k : ℝ) ^ C_comb) x U)) :
    IsPairCoupledGeneralizedNice H₁ H₂ := by
  obtain ⟨d', hd', hviral_prop⟩ := hviral
  let a_leaf : ℝ := 4 * d' * (Fintype.card W₁ : ℝ) + 6
  let b_leaf : ℝ := 2 * (Fintype.card W₁ : ℝ)
  have hh₁_real : (3 : ℝ) ≤ (Fintype.card W₁ : ℝ) := by exact_mod_cast hh₁
  have ha_leaf : 6 ≤ a_leaf := by
    dsimp [a_leaf]
    have : 0 ≤ 4 * d' * (Fintype.card W₁ : ℝ) := by positivity
    linarith
  have hb_leaf : 6 ≤ b_leaf := by dsimp [b_leaf]; linarith
  refine pair_coupled_generalized_nice_of_comb_dichotomy H₁ H₂ (by omega)
    a_leaf b_leaf C_comb C_cap c_A c_B ha_leaf hb_leaf hC_comb hC_cap hc_A hc_B ?_ h_comb_dichotomy
  intro V _ _ G F' y hG₁ hG₂ hy0 hy_le hy_F' h_cosparse
  have hy_half : y < 1 / 2 := by
    have h1 : (2 : ℝ) ^ (-4 * b_leaf) ≤ (2 : ℝ) ^ (-24 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h2 : (2 : ℝ) ^ (-24 : ℝ) < 1 / 2 := by norm_num
    exact hy_le.trans_lt (h1.trans_lt h2)
  have hy_le1 : y ≤ 1 := by linarith
  have hy1_F' : 1 ≤ y * (F'.card : ℝ) := by
    have h1 : y ^ (a_leaf + 2) ≤ y ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hy0 hy_le1 (by linarith)
    rw [Real.rpow_one] at h1
    exact hy_F'.trans (mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _))
  have hF'_ne : F'.Nonempty := by
    rw [← card_pos]
    have : (0 : ℝ) < (F'.card : ℝ) := by nlinarith
    exact_mod_cast this
  have hcosparse_y : IsEpsSparseOn Gᶜ F' y := by
    refine h_cosparse.mono ?_
    nlinarith [sq_nonneg y]
  rcases leaf_reducible_cosparse_trigger_or_restricted H₁ H₂ v₀ u₀ hu₀_ne hleaf hh₁ hd' hviral_prop
      G hG₁ hG₂ F' hF'_ne y hy0 hy_half hy1_F' hcosparse_y with
    ⟨U, hUF', hU_rest, hU_card⟩ | ⟨X, hXF', Y, hYF', hdisj, hX_card, hY_card, hcomp⟩
  · left
    refine ⟨U, hUF', hU_rest, ?_⟩
    have hexp : 4 * d' + 1 ≤ a_leaf := by dsimp [a_leaf]; nlinarith
    have hrpow : y ^ a_leaf ≤ y ^ (4 * d' + 1) :=
      Real.rpow_le_rpow_of_exponent_ge hy0 hy_le1 hexp
    exact (mul_le_mul_of_nonneg_right hrpow (Nat.cast_nonneg _)).trans hU_card
  · right
    refine ⟨X, hXF', Y, hYF', hdisj, ?_, ?_, hcomp⟩
    · have hW₁_sub : ((Fintype.card W₁ - 1 : ℕ) : ℝ) ≤ (Fintype.card W₁ : ℝ) := by
        exact_mod_cast Nat.sub_le (Fintype.card W₁) 1
      have hexp : 4 * d' * ((Fintype.card W₁ - 1 : ℕ) : ℝ) + 1 ≤ a_leaf := by
        dsimp [a_leaf]; nlinarith
      have hrpow : y ^ a_leaf ≤ y ^ (4 * d' * ((Fintype.card W₁ - 1 : ℕ) : ℝ) + 1) :=
        Real.rpow_le_rpow_of_exponent_ge hy0 hy_le1 hexp
      exact (mul_le_mul_of_nonneg_right hrpow (Nat.cast_nonneg _)).trans hX_card.le
    · have h1 : (1 - b_leaf * y) * (F'.card : ℝ) ≤
          (1 - (Fintype.card W₁ : ℝ) * y) * (F'.card : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
        dsimp [b_leaf]; nlinarith
      exact h1.trans hY_card

/--
**Single-Graph Leaf-Reducible Specialization of Lemma 7(1) (`coupled_generalized_nice_of_leaf_reducible_comb_dichotomy`)**:
When $H$ ($|H| \ge 3$) has a degree-$1$ leaf $v_0$ with unique neighbor $u_0 \neq v_0$ and
$(H - v_0)ᶜ$ is viral (`IsViral`), `IsCoupledGeneralizedNice H` follows from the Stage-1 Comb Dichotomy.
-/
theorem coupled_generalized_nice_of_leaf_reducible_comb_dichotomy
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W)
    (v₀ u₀ : W) (hu₀_ne : u₀ ≠ v₀)
    (hleaf : ∀ w : W, H.Adj v₀ w ↔ w = u₀)
    (hh : 3 ≤ Fintype.card W)
    (hviral : IsViral (H.comap (Subtype.val : {w : W // w ≠ v₀} → W))ᶜ)
    (C_comb C_cap c_A c_B : ℝ)
    (hC_comb : 18 ≤ C_comb) (hC_cap : 2 ≤ C_cap)
    (hc_A : 0 < c_A) (hc_B : 0 < c_B)
    (h_comb_dichotomy : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      (F' : Finset V) (x y : ℝ) (ℓ : ℕ) (a : Fin ℓ → V) (B : Fin ℓ → Finset V) (v : V),
      IsInducedSubgraphFree G Hᶜ →
      0 < x → x ≤ y → y ≤ (2 : ℝ)⁻¹ ^ 16 →
      y ^ (-(1 / 4 : ℝ)) ≤ (ℓ : ℝ) → (ℓ : ℝ) ≤ x⁻¹ → 64 ≤ ℓ →
      IsCombIn G F' ℓ (y ^ 4 * (F'.card : ℝ) / (ℓ : ℝ) ^ 2) a B →
      IsCombExternalApex G F' ℓ a B v →
        ((y ^ 4 * (F'.card : ℝ) / (ℓ : ℝ) ^ 2) ^ c_A ≤ (kappa G : ℝ)) ∨
        (∃ k : ℕ, 2 ≤ k ∧ (1 / 2 : ℝ) * (ℓ : ℝ) ^ c_B ≤ (k : ℝ) ∧ k ≤ ⌈x ^ (-C_cap)⌉₊ ∧
          ∃ U : Fin k → Finset V,
            IsPureBlockadeIn G F' k ((F'.card : ℝ) / (k : ℝ) ^ C_comb) U ∨
            IsWeaklySparseOrCoSparseBlockadeIn G F' k ((F'.card : ℝ) / (k : ℝ) ^ C_comb) x U)) :
    IsCoupledGeneralizedNice H := by
  have hpair_viral : IsPairViral (H.comap (Subtype.val : {w : W // w ≠ v₀} → W))ᶜ Hᶜ := by
    obtain ⟨d', hd', hv⟩ := hviral
    exact ⟨d', hd', fun V _ _ G ε hε0 hε_half hc1 _ => hv V G ε hε0 hε_half hc1⟩
  exact isCoupledGeneralizedNice_of_pair <|
    pair_coupled_generalized_nice_of_leaf_reducible_comb_dichotomy H H v₀ u₀ hu₀_ne hleaf hh
      hpair_viral C_comb C_cap c_A c_B hC_comb hC_cap hc_A hc_B
      (fun V _ _ G F' x y ℓ a B v hG _ => h_comb_dichotomy V G F' x y ℓ a B v hG)

/-!
## Section 6: Lemma 7(2) — Master Stage-2 Reduction for Generalized Nice and Thresholded Wonderful Families
(`master_stage2_pair_eh_of_coupled_gen_nice_and_wonderful` and
`master_stage2_eh_of_coupled_gen_nice_and_wonderful`, `main.tex` lines 295, 333–412)
-/

/-! ### Section 6A: Two-Graph Thresholded Wonderfulness, `HasPairErdosHajnalProp` Complementation, and Subtype Transport -/

/--
Two-graph open-interval thresholded wonderfulness (`IsPairThresholdedWonderful H₁ H₂`,
Definition 2(4) of `main.tex` for a family $\{H_1, H_2\}$).
-/
def IsPairThresholdedWonderful {W₁ W₂ : Type*} (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂) : Prop :=
  ∃ (a : ℕ) (y_thr : ℝ), 7 ≤ a ∧ 0 < y_thr ∧ y_thr ≤ 1 / 4 ∧
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      (y δ_cross : ℝ) (ℓ w : ℕ) (B : Fin ℓ → Finset V),
      0 < y → y ≤ y_thr →
      IsInducedSubgraphFree G H₁ᶜ → IsInducedSubgraphFree G H₂ᶜ →
      y ^ (-(a : ℝ)) ≤ (ℓ : ℝ) →
      0 < δ_cross → δ_cross ≤ min (y ^ a) (1 / (8 * (ℓ : ℝ) ^ 2)) →
      1 ≤ w →
      IsCompleteOrXSparseBlockadeIn G Finset.univ ℓ (w : ℝ) δ_cross B →
      (∀ i : Fin ℓ, (B i).card = w ∧ IsAnticonnected G (B i)) →
        (∃ S : Finset V, IsEpsRestrictedOn G S (y ^ 4) ∧ (w : ℝ) ≤ (S.card : ℝ)) ∨
        (∃ i_star : Fin ℓ,
          (((Finset.univ \ Finset.biUnion Finset.univ B).filter (fun v =>
            0 < (neighborFinsetIn G v (B i_star)).card ∧
            ((neighborFinsetIn G v (B i_star)).card : ℝ) < (1 / 2) * (w : ℝ))).card : ℝ) ≤
            y * (Fintype.card V : ℝ))

theorem IsThresholdedWonderful.to_pair {W : Type*} {H : SimpleGraph W}
    (h : IsThresholdedWonderful H) :
    IsPairThresholdedWonderful H H := by
  obtain ⟨a, y_thr, ha, hy0, hy_quarter, hprop⟩ := h
  refine ⟨a, y_thr, ha, hy0, hy_quarter, ?_⟩
  intro V _ _ G y δ_cross ℓ w B hy_pos hy_le hG _ hℓ hδ0 hδ_le hw hB hB_anti
  exact hprop V G y δ_cross ℓ w B hy_pos hy_le hG hℓ hδ0 hδ_le hw hB hB_anti

private theorem HasPairErdosHajnalProp.compl {W₁ W₂ : Type*} {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂}
    (h : HasPairErdosHajnalProp H₁ H₂) :
    HasPairErdosHajnalProp H₁ᶜ H₂ᶜ := by
  obtain ⟨c, hc, h_bound⟩ := h
  refine ⟨c, hc, fun V _ _ G hG₁ hG₂ => ?_⟩
  have hG₁' : IsInducedSubgraphFree Gᶜ H₁ := by
    rw [isInducedSubgraphFree_compl_iff, compl_compl]; exact hG₁
  have hG₂' : IsInducedSubgraphFree Gᶜ H₂ := by
    rw [isInducedSubgraphFree_compl_iff, compl_compl]; exact hG₂
  have h_le := h_bound V Gᶜ hG₁' hG₂'
  rwa [kappa_compl] at h_le

theorem HasPairErdosHajnalProp.of_compl {W₁ W₂ : Type*} {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂}
    (h : HasPairErdosHajnalProp H₁ᶜ H₂ᶜ) :
    HasPairErdosHajnalProp H₁ H₂ := by
  have h' := h.compl
  rwa [compl_compl, compl_compl] at h'

theorem hasErdosHajnalProp_of_pair {W : Type*} {H : SimpleGraph W}
    (h : HasPairErdosHajnalProp H H) :
    HasErdosHajnalProp H := by
  obtain ⟨c, hc, h_bound⟩ := h
  exact ⟨c, hc, fun V _ _ G hG => h_bound V G hG hG⟩

private theorem isInducedSubgraphFree_induce {W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    (F' : Finset V) (hG : IsInducedSubgraphFree G H) :
    IsInducedSubgraphFree (G.induce (F' : Set V)) H := by
  rintro ⟨g, hg⟩
  apply hG
  refine ⟨g.trans (Function.Embedding.subtype _), ?_⟩
  ext w₁ w₂
  have hadj := congr_arg (fun (K : SimpleGraph W) => K.Adj w₁ w₂) hg
  simpa [comap_adj] using hadj

private theorem isEpsSparseOn_induce_univ (G : SimpleGraph V) (F' : Finset V) (y : ℝ)
    (h : IsEpsSparseOn G F' y) :
    IsEpsSparseOn (G.induce (F' : Set V)) Finset.univ y := by
  intro a _
  have hcard_univ : (Finset.univ : Finset ↥(F' : Set V)).card = F'.card :=
    Finset.card_univ.trans (Fintype.card_coe F')
  have hneigh_le : (neighborFinsetIn (G.induce (F' : Set V)) a Finset.univ).card ≤
      (neighborFinsetIn G a.1 F').card := by
    have hmap : (neighborFinsetIn (G.induce (F' : Set V)) a Finset.univ).map
        (Function.Embedding.subtype _) ⊆ neighborFinsetIn G a.1 F' := by
      intro x hx
      rcases Finset.mem_map.mp hx with ⟨b, hb, rfl⟩
      rw [mem_neighborFinsetIn'] at hb ⊢
      exact ⟨b.2, hb.2⟩
    rw [← Finset.card_map (Function.Embedding.subtype _)]
    exact card_le_card hmap
  rw [hcard_univ]
  exact (by exact_mod_cast hneigh_le :
    ((neighborFinsetIn (G.induce (F' : Set V)) a Finset.univ).card : ℝ) ≤
      ((neighborFinsetIn G a.1 F').card : ℝ)).trans (h a.1 a.2)

private theorem isAnticompletePair_map_subtype (G : SimpleGraph V) (F' : Finset V)
    (X_sub Y_sub : Finset ↥(F' : Set V))
    (h : IsAnticompletePair (G.induce (F' : Set V)) X_sub Y_sub) :
    IsAnticompletePair G (X_sub.map (Function.Embedding.subtype _))
      (Y_sub.map (Function.Embedding.subtype _)) := by
  intro u hu v hv
  rcases Finset.mem_map.mp hu with ⟨a, ha, rfl⟩
  rcases Finset.mem_map.mp hv with ⟨b, hb, rfl⟩
  exact h a ha b hb

private theorem isCompletePair_map_subtype (G : SimpleGraph V) (F' : Finset V)
    (X_sub Y_sub : Finset ↥(F' : Set V))
    (h : IsCompletePair (G.induce (F' : Set V)) X_sub Y_sub) :
    IsCompletePair G (X_sub.map (Function.Embedding.subtype _))
      (Y_sub.map (Function.Embedding.subtype _)) := by
  intro u hu v hv
  rcases Finset.mem_map.mp hu with ⟨a, ha, rfl⟩
  rcases Finset.mem_map.mp hv with ⟨b, hb, rfl⟩
  exact h a ha b hb

private theorem isPureCographBlockadeIn_map_subtype (G : SimpleGraph V) (F' : Finset V)
    {k : ℕ} {w : ℝ} (B_sub : Fin k → Finset ↥(F' : Set V))
    (h : IsPureCographBlockadeIn (G.induce (F' : Set V)) Finset.univ k w B_sub) :
    let emb := Function.Embedding.subtype (fun x : V => x ∈ (F' : Set V))
    IsPureCographBlockadeIn G F' k w (fun i => (B_sub i).map emb) := by
  intro emb
  have hblock : IsBlockadeIn G F' k w (fun i => (B_sub i).map emb) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i x hx
      rcases Finset.mem_map.mp hx with ⟨a, _, rfl⟩
      exact a.2
    · intro i
      exact (h.1.1.nonempty_blocks i).map
    · intro i j hij
      exact Finset.disjoint_map emb |>.mpr (h.1.1.pairwise_disjoint i j hij)
    · intro i
      rw [Finset.card_map]
      exact h.1.1.width_ge i
  have hpure : ∀ i j : Fin k, i ≠ j →
      IsPurePair G ((B_sub i).map emb) ((B_sub j).map emb) := by
    intro i j hij
    rcases h.1.2 i j hij with hcomp | hanti
    · exact Or.inl (isCompletePair_map_subtype G F' (B_sub i) (B_sub j) hcomp)
    · exact Or.inr (isAnticompletePair_map_subtype G F' (B_sub i) (B_sub j) hanti)
  have hpat_eq : purePatternGraph G (fun i => (B_sub i).map emb) =
      purePatternGraph (G.induce (F' : Set V)) B_sub := by
    ext i j
    dsimp [purePatternGraph]
    by_cases hij : i = j
    · simp [hij]
    · simp only [hij, not_false_eq_true, true_and]
      constructor
      · intro hcomp a ha b hb
        exact hcomp (emb a) (Finset.mem_map_of_mem emb ha)
          (emb b) (Finset.mem_map_of_mem emb hb)
      · exact isCompletePair_map_subtype G F' (B_sub i) (B_sub j)
  refine ⟨⟨hblock, hpure⟩, ?_⟩
  rw [hpat_eq]
  exact h.2

/-!
### Section 6B: Step 1 of Lemma 7(2) — Simultaneous Co-Sparse-to-Complete Purification on `(GN1)`
(`stage2_gn1_viral_purification`, `main.tex` lines 350–383)
-/

/--
Symmetric one-block shrinking helper (`shrink_one_block_symm`, `main.tex` line 366):
Given blocks $A : \text{Fin }\ell \to \text{Finset } V$ with $|A_i| \ge m \ge 1$ and symmetric
pairwise edge-graph family $H_{\mathrm{pair}}(i, j) = H_{\mathrm{pair}}(j, i)$ satisfying
$\text{crossEdgeCount }(H_{\mathrm{pair}}(i, j))\ A_i\ A_j \le c(i, j)|A_i||A_j|$ for all $i \neq j$,
shrinking block $A_r$ to a subset $X_r \subseteq A_r$ of exact size $m$ multiplies $c(i, j)$ for
pairs involving $r$ by at most $\ell$.
-/
private theorem shrink_one_block_symm (ℓ m : ℕ) (hm : 1 ≤ m)
    (H_pair : Fin ℓ → Fin ℓ → SimpleGraph V) (hH_symm : ∀ i j, H_pair i j = H_pair j i)
    (A : Fin ℓ → Finset V) (hA_card : ∀ i : Fin ℓ, m ≤ (A i).card)
    (c : Fin ℓ → Fin ℓ → ℝ) (hc_pos : ∀ i j, 0 < c i j) (hc_symm : ∀ i j, c i j = c j i)
    (hpairs : ∀ i j : Fin ℓ, i ≠ j →
      (crossEdgeCount (H_pair i j) (A i) (A j) : ℝ) ≤ c i j * ((A i).card : ℝ) * ((A j).card : ℝ))
    (r : Fin ℓ) :
    ∃ X_r ⊆ A r, X_r.card = m ∧
      ∀ i j : Fin ℓ, i ≠ j →
        let A' := fun t => if t = r then X_r else A t
        let c' := fun s t => if s = r ∨ t = r then (ℓ : ℝ) * c s t else c s t
        (crossEdgeCount (H_pair i j) (A' i) (A' j) : ℝ) ≤
          c' i j * ((A' i).card : ℝ) * ((A' j).card : ℝ) := by
  classical
  have hAr_pos : (0 : ℝ) < ((A r).card : ℝ) := by
    have : 0 < (A r).card := lt_of_lt_of_le (by omega) (hA_card r)
    exact_mod_cast this
  have hAj_pos : ∀ j : Fin ℓ, (0 : ℝ) < ((A j).card : ℝ) := by
    intro j
    have : 0 < (A j).card := lt_of_lt_of_le (by omega) (hA_card j)
    exact_mod_cast this
  let J_idx := (Finset.univ : Finset (Fin ℓ)).filter (fun j => r ≠ j)
  let denom : Fin ℓ → ℝ := fun j => c r j * ((A r).card : ℝ) * ((A j).card : ℝ)
  have hdenom_pos : ∀ j : Fin ℓ, 0 < denom j :=
    fun j => mul_pos (mul_pos (hc_pos r j) hAr_pos) (hAj_pos j)
  let f : Fin ℓ → V → ℝ :=
    fun j u => ((neighborFinsetIn (H_pair r j) u (A j)).card : ℝ) * (denom j)⁻¹
  have hf_nonneg : ∀ j u, 0 ≤ f j u :=
    fun j u => mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.mpr (hdenom_pos j).le)
  let w : V → ℝ := fun u => ∑ j ∈ J_idx, f j u
  have hw_nonneg : ∀ u ∈ A r, 0 ≤ w u := fun u _ => sum_nonneg (fun j _ => hf_nonneg j u)
  have hsum_f_le_one : ∀ j ∈ J_idx, ∑ u ∈ A r, f j u ≤ 1 := by
    intro j hj
    have hrj : r ≠ j := (mem_filter.mp hj).2
    dsimp [f]
    rw [← sum_mul]
    have hsum_eq : (∑ u ∈ A r, ((neighborFinsetIn (H_pair r j) u (A j)).card : ℝ)) =
        (crossEdgeCount (H_pair r j) (A r) (A j) : ℝ) := by
      exact_mod_cast (crossEdgeCount_eq_sum_left (H_pair r j) (A r) (A j)).symm
    rw [hsum_eq]
    have h1 := mul_le_mul_of_nonneg_right (hpairs r j hrj) (inv_nonneg.mpr (hdenom_pos j).le)
    rwa [mul_inv_cancel₀ (hdenom_pos j).ne'] at h1
  have hsum_w_le : ∑ u ∈ A r, w u ≤ (ℓ : ℝ) := by
    dsimp [w]
    rw [sum_comm]
    calc ∑ j ∈ J_idx, ∑ u ∈ A r, f j u
      _ ≤ ∑ _j ∈ J_idx, (1 : ℝ) := sum_le_sum hsum_f_le_one
      _ = (J_idx.card : ℝ) := by rw [sum_const, nsmul_eq_mul, mul_one]
      _ ≤ (ℓ : ℝ) := by
        have : J_idx.card ≤ ℓ :=
          (card_filter_le _ _).trans_eq (by rw [card_univ, Fintype.card_fin])
        exact_mod_cast this
  obtain ⟨X_r, hXr_sub, hXr_card, hXr_sum⟩ :=
    exists_subset_card_eq_sum_le (A r) w hw_nonneg m (hA_card r)
  have hXr_bound : ∀ j : Fin ℓ, r ≠ j →
      (crossEdgeCount (H_pair r j) X_r (A j) : ℝ) ≤
        ((ℓ : ℝ) * c r j) * (m : ℝ) * ((A j).card : ℝ) := by
    intro j hrj
    have hjJ : j ∈ J_idx := mem_filter.mpr ⟨mem_univ j, hrj⟩
    have hj_le_w : ∑ u ∈ X_r, f j u ≤ ∑ u ∈ X_r, w u := by
      dsimp [w]
      rw [sum_comm]
      exact single_le_sum (fun j' _ => sum_nonneg (fun u _ => hf_nonneg j' u)) hjJ
    have hsum_Xr : ∑ u ∈ X_r, f j u =
        (crossEdgeCount (H_pair r j) X_r (A j) : ℝ) * (denom j)⁻¹ := by
      dsimp [f]
      rw [← sum_mul]
      congr 1
      exact_mod_cast (crossEdgeCount_eq_sum_left (H_pair r j) X_r (A j)).symm
    have h1 : ((A r).card : ℝ) * ((crossEdgeCount (H_pair r j) X_r (A j) : ℝ) * (denom j)⁻¹) ≤
        (m : ℝ) * (ℓ : ℝ) := by
      calc ((A r).card : ℝ) * ((crossEdgeCount (H_pair r j) X_r (A j) : ℝ) * (denom j)⁻¹)
        _ = ((A r).card : ℝ) * (∑ u ∈ X_r, f j u) := by rw [hsum_Xr]
        _ ≤ ((A r).card : ℝ) * (∑ u ∈ X_r, w u) :=
          mul_le_mul_of_nonneg_left hj_le_w hAr_pos.le
        _ ≤ (m : ℝ) * (∑ u ∈ A r, w u) := hXr_sum
        _ ≤ (m : ℝ) * (ℓ : ℝ) := mul_le_mul_of_nonneg_left hsum_w_le (Nat.cast_nonneg _)
    have hdenom_ne : denom j ≠ 0 := (hdenom_pos j).ne'
    have h2 : ((A r).card : ℝ) * (crossEdgeCount (H_pair r j) X_r (A j) : ℝ) ≤
        ((m : ℝ) * (ℓ : ℝ)) * denom j := by
      have hmul := mul_le_mul_of_nonneg_right h1 (hdenom_pos j).le
      have hlhs : ((A r).card : ℝ) *
          ((crossEdgeCount (H_pair r j) X_r (A j) : ℝ) * (denom j)⁻¹) * denom j =
          ((A r).card : ℝ) * (crossEdgeCount (H_pair r j) X_r (A j) : ℝ) *
          ((denom j)⁻¹ * denom j) := by ring
      rw [hlhs, inv_mul_cancel₀ hdenom_ne, mul_one] at hmul
      exact hmul
    have h3 : ((A r).card : ℝ) * (crossEdgeCount (H_pair r j) X_r (A j) : ℝ) ≤
        ((A r).card : ℝ) * (((ℓ : ℝ) * c r j) * (m : ℝ) * ((A j).card : ℝ)) := by
      calc ((A r).card : ℝ) * (crossEdgeCount (H_pair r j) X_r (A j) : ℝ)
        _ ≤ ((m : ℝ) * (ℓ : ℝ)) * (c r j * ((A r).card : ℝ) * ((A j).card : ℝ)) := h2
        _ = ((A r).card : ℝ) * (((ℓ : ℝ) * c r j) * (m : ℝ) * ((A j).card : ℝ)) := by ring
    exact le_of_mul_le_mul_left h3 hAr_pos
  refine ⟨X_r, hXr_sub, hXr_card, ?_⟩
  intro i j hij
  dsimp only
  by_cases hir : i = r
  · subst hir
    have hjr : j ≠ i := hij.symm
    rw [if_pos rfl, if_neg hjr, if_pos (Or.inl rfl), hXr_card]
    exact hXr_bound j hij
  · by_cases hjr : j = r
    · subst hjr
      rw [if_neg hir, if_pos rfl, if_pos (Or.inr rfl), hXr_card]
      have hb := hXr_bound i hij.symm
      rw [hH_symm j i, crossEdgeCount_comm', hc_symm j i] at hb
      linarith
    · have hor : ¬(i = r ∨ j = r) := not_or.mpr ⟨hir, hjr⟩
      rw [if_neg hir, if_neg hjr, if_neg hor]
      exact hpairs i j hij

/--
**Sub-step 1.1a (`step1a_symm_equal_size_presampling`, `main.tex` line 366)**:
Given an $(\ell, W_0)$-blockade $A$ with $W_0 \ge 1$ and $\text{crossEdgeCount }(H_{\mathrm{pair}}(i, j))\ A_i\ A_j \le x_{\mathrm{sp}} |A_i| |A_j|$
for all $i \neq j$, sequentially applying `shrink_one_block_symm` yields $A''_i \subseteq A_i$ of
exact size $|A''_i| = W_0$ such that
$\text{crossEdgeCount }(H_{\mathrm{pair}}(i, j))\ A''_i\ A''_j \le \ell^2 x_{\mathrm{sp}} W_0^2$.
-/
private theorem step1a_symm_equal_size_presampling (ℓ W₀ : ℕ) (x_sp : ℝ)
    (hℓ : 1 ≤ ℓ) (hW₀ : 1 ≤ W₀) (hx_sp : 0 < x_sp)
    (H_pair : Fin ℓ → Fin ℓ → SimpleGraph V) (hH_symm : ∀ i j, H_pair i j = H_pair j i)
    (A : Fin ℓ → Finset V) (hA_card : ∀ i : Fin ℓ, W₀ ≤ (A i).card)
    (hpairs : ∀ i j : Fin ℓ, i ≠ j →
      (crossEdgeCount (H_pair i j) (A i) (A j) : ℝ) ≤ x_sp * ((A i).card : ℝ) * ((A j).card : ℝ)) :
    ∃ A'' : Fin ℓ → Finset V,
      (∀ i, A'' i ⊆ A i) ∧
      (∀ i, (A'' i).card = W₀) ∧
      (∀ i j : Fin ℓ, i ≠ j →
        (crossEdgeCount (H_pair i j) (A'' i) (A'' j) : ℝ) ≤
          (ℓ : ℝ) ^ 2 * x_sp * (W₀ : ℝ) * (W₀ : ℝ)) := by
  have hℓ_pos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  let coeff (k : ℕ) (i j : Fin ℓ) : ℝ :=
    (if i.val < k then (ℓ : ℝ) else 1) * (if j.val < k then (ℓ : ℝ) else 1) * x_sp
  have hcoeff_pos : ∀ k i j, 0 < coeff k i j := by
    intro k i j
    dsimp [coeff]
    have h1 : (0 : ℝ) < if i.val < k then (ℓ : ℝ) else 1 := by split_ifs <;> positivity
    have h2 : (0 : ℝ) < if j.val < k then (ℓ : ℝ) else 1 := by split_ifs <;> positivity
    positivity
  have hcoeff_symm : ∀ k i j, coeff k i j = coeff k j i := by
    intro k i j; dsimp [coeff]; ring
  have h_ind : ∀ k : ℕ, k ≤ ℓ →
      ∃ X : Fin ℓ → Finset V,
        (∀ i, X i ⊆ A i) ∧
        (∀ i, W₀ ≤ (X i).card) ∧
        (∀ i : Fin ℓ, i.val < k → (X i).card = W₀) ∧
        (∀ i j : Fin ℓ, i ≠ j →
          (crossEdgeCount (H_pair i j) (X i) (X j) : ℝ) ≤
            coeff k i j * ((X i).card : ℝ) * ((X j).card : ℝ)) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨A, fun _ => Subset.rfl, hA_card, fun i hi => by omega, ?_⟩
      intro i j hij
      simpa [coeff] using hpairs i j hij
    | succ k ih =>
      intro hk
      obtain ⟨X, hX_sub, hX_ge, hX_eq, hX_pairs⟩ := ih (by omega)
      let r : Fin ℓ := ⟨k, hk⟩
      obtain ⟨X_r, hXr_sub, hXr_card, hXr_pairs⟩ :=
        shrink_one_block_symm ℓ W₀ hW₀ H_pair hH_symm X hX_ge (coeff k)
          (hcoeff_pos k) (hcoeff_symm k) hX_pairs r
      let X' : Fin ℓ → Finset V := fun i => if i = r then X_r else X i
      refine ⟨X', ?_, ?_, ?_, ?_⟩
      · intro i; dsimp [X']; split_ifs with hir
        · subst hir; exact hXr_sub.trans (hX_sub r)
        · exact hX_sub i
      · intro i; dsimp [X']; split_ifs with hir
        · omega
        · exact hX_ge i
      · intro i hi; dsimp [X']; split_ifs with hir
        · exact hXr_card
        · have : i.val ≠ k := fun h => hir (Fin.ext h)
          exact hX_eq i (by omega)
      · intro i j hij
        have hp := hXr_pairs i j hij
        dsimp only at hp
        have hcoeff_step :
            (if i = r ∨ j = r then (ℓ : ℝ) * coeff k i j else coeff k i j) = coeff (k + 1) i j := by
          have hij_val : i.val ≠ j.val := fun h => hij (Fin.ext h)
          dsimp [coeff]
          by_cases hir : i = r
          · have hik : i.val = k := congrArg Fin.val hir
            have hjk : j.val ≠ k := fun h => hij_val (hik.trans h.symm)
            have hj_lt : (j.val < k + 1) ↔ (j.val < k) := by omega
            rw [if_pos (Or.inl hir), if_neg (by omega : ¬i.val < k),
              if_pos (by omega : i.val < k + 1)]
            simp only [hj_lt]; ring
          · have hik : i.val ≠ k := fun h => hir (Fin.ext h)
            by_cases hjr : j = r
            · have hjk : j.val = k := congrArg Fin.val hjr
              have hi_lt : (i.val < k + 1) ↔ (i.val < k) := by omega
              rw [if_pos (Or.inr hjr), if_neg (by omega : ¬j.val < k),
                if_pos (by omega : j.val < k + 1)]
              simp only [hi_lt]; ring
            · have hjk : j.val ≠ k := fun h => hjr (Fin.ext h)
              have hor : ¬(i = r ∨ j = r) := not_or.mpr ⟨hir, hjr⟩
              have hi_lt : (i.val < k + 1) ↔ (i.val < k) := by omega
              have hj_lt : (j.val < k + 1) ↔ (j.val < k) := by omega
              rw [if_neg hor]
              simp only [hi_lt, hj_lt]
        rwa [hcoeff_step] at hp
  obtain ⟨A'', hA''_sub, _, hA''_eq, hA''_pairs⟩ := h_ind ℓ le_rfl
  have hA''_card : ∀ i : Fin ℓ, (A'' i).card = W₀ := fun i => hA''_eq i i.isLt
  refine ⟨A'', hA''_sub, hA''_card, ?_⟩
  intro i j hij
  have hp := hA''_pairs i j hij
  dsimp [coeff] at hp
  rw [if_pos i.isLt, if_pos j.isLt, hA''_card i, hA''_card j] at hp
  linarith [sq (ℓ : ℝ)]

/--
**Sub-step 1.1b (`step1b_symm_markov_pruning`, `main.tex` line 366)**:
Given equal-sized blocks $A''_i$ of size $W_0 = 2 W_{\mathrm{mid}}$ ($W_{\mathrm{mid}} \ge 1$, $\ell \ge 1$)
with $\text{crossEdgeCount }(H_{\mathrm{pair}}(i, j))\ A''_i\ A''_j \le \ell^2 x_{\mathrm{sp}} W_0^2$,
Markov-pruning vertices with $> 2 \ell^3 x_{\mathrm{sp}} W_0 = 4 \ell^3 x_{\mathrm{sp}} W_{\mathrm{mid}}$
neighbors in $A''_j$ in $H_{\mathrm{pair}}(i, j)$ and truncating to exact size $W_{\mathrm{mid}}$
yields $A'_i \subseteq A''_i$ with $|A'_i| = W_{\mathrm{mid}}$ such that for all $i \neq j$ and
all $u \in A'_i$, $|N_{H_{\mathrm{pair}}(i, j)}(u) \cap A'_j| \le 4 \ell^3 x_{\mathrm{sp}} W_{\mathrm{mid}}$.
-/
private theorem step1b_symm_markov_pruning (ℓ W_mid : ℕ) (x_sp : ℝ)
    (hℓ : 1 ≤ ℓ) (hW_mid : 1 ≤ W_mid) (hx_sp : 0 < x_sp)
    (H_pair : Fin ℓ → Fin ℓ → SimpleGraph V)
    (A'' : Fin ℓ → Finset V) (hA''_card : ∀ i : Fin ℓ, (A'' i).card = 2 * W_mid)
    (hpairs : ∀ i j : Fin ℓ, i ≠ j →
      (crossEdgeCount (H_pair i j) (A'' i) (A'' j) : ℝ) ≤
        (ℓ : ℝ) ^ 2 * x_sp * ((2 * W_mid : ℕ) : ℝ) * ((2 * W_mid : ℕ) : ℝ)) :
    ∃ A' : Fin ℓ → Finset V,
      (∀ i, A' i ⊆ A'' i) ∧
      (∀ i, (A' i).card = W_mid) ∧
      (∀ i j : Fin ℓ, i ≠ j → ∀ u ∈ A' i,
        ((neighborFinsetIn (H_pair i j) u (A' j)).card : ℝ) ≤
          4 * (ℓ : ℝ) ^ 3 * x_sp * (W_mid : ℝ)) := by
  classical
  let W₀ := 2 * W_mid
  have hℓ_pos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  have hW_mid_pos : (0 : ℝ) < (W_mid : ℝ) := by exact_mod_cast hW_mid
  let thr : ℝ := 4 * (ℓ : ℝ) ^ 3 * x_sp * (W_mid : ℝ)
  have hthr_pos : 0 < thr := by dsimp [thr]; positivity
  let bad (i j : Fin ℓ) : Finset V :=
    if i ≠ j then
      (A'' i).filter (fun u => thr < ((neighborFinsetIn (H_pair i j) u (A'' j)).card : ℝ))
    else ∅
  have hbad_card : ∀ i j : Fin ℓ, ((bad i j).card : ℝ) * (ℓ : ℝ) ≤ (W_mid : ℝ) := by
    intro i j
    dsimp [bad]
    by_cases hij : i ≠ j
    · rw [if_pos hij]
      let B_ij := (A'' i).filter (fun u => thr < ((neighborFinsetIn (H_pair i j) u (A'' j)).card : ℝ))
      have hmarkov : (B_ij.card : ℝ) * thr ≤ (crossEdgeCount (H_pair i j) (A'' i) (A'' j) : ℝ) := by
        calc (B_ij.card : ℝ) * thr
          _ = ∑ _u ∈ B_ij, thr := by rw [sum_const, nsmul_eq_mul]
          _ ≤ ∑ u ∈ B_ij, ((neighborFinsetIn (H_pair i j) u (A'' j)).card : ℝ) :=
            sum_le_sum (fun u hu => (mem_filter.mp hu).2.le)
          _ ≤ ∑ u ∈ A'' i, ((neighborFinsetIn (H_pair i j) u (A'' j)).card : ℝ) :=
            sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.cast_nonneg _)
          _ = (crossEdgeCount (H_pair i j) (A'' i) (A'' j) : ℝ) := by
            exact_mod_cast (crossEdgeCount_eq_sum_left (H_pair i j) (A'' i) (A'' j)).symm
      have hp := hpairs i j hij
      push_cast at hp
      have hmul : (4 * (ℓ : ℝ) ^ 2 * x_sp * (W_mid : ℝ)) * (((B_ij.card : ℝ) * (ℓ : ℝ))) ≤
          (4 * (ℓ : ℝ) ^ 2 * x_sp * (W_mid : ℝ)) * (W_mid : ℝ) := by
        calc (4 * (ℓ : ℝ) ^ 2 * x_sp * (W_mid : ℝ)) * (((B_ij.card : ℝ) * (ℓ : ℝ)))
          _ = (B_ij.card : ℝ) * thr := by dsimp [thr]; ring
          _ ≤ (crossEdgeCount (H_pair i j) (A'' i) (A'' j) : ℝ) := hmarkov
          _ ≤ (ℓ : ℝ) ^ 2 * x_sp * (2 * (W_mid : ℝ)) * (2 * (W_mid : ℝ)) := hp
          _ = (4 * (ℓ : ℝ) ^ 2 * x_sp * (W_mid : ℝ)) * (W_mid : ℝ) := by ring
      exact le_of_mul_le_mul_left hmul (by positivity)
    · rw [if_neg hij]
      simp only [card_empty, Nat.cast_zero, zero_mul]
      exact hW_mid_pos.le
  let Good (i : Fin ℓ) : Finset V := A'' i \ (Finset.univ : Finset (Fin ℓ)).biUnion (bad i)
  have hGood_card : ∀ i : Fin ℓ, W_mid ≤ (Good i).card := by
    intro i
    have hbiUnion_le : (((Finset.univ : Finset (Fin ℓ)).biUnion (bad i)).card : ℝ) ≤ (W_mid : ℝ) := by
      have h1 : (((Finset.univ : Finset (Fin ℓ)).biUnion (bad i)).card : ℝ) ≤
          ∑ j : Fin ℓ, ((bad i j).card : ℝ) := by exact_mod_cast card_biUnion_le
      have h2 : (∑ j : Fin ℓ, ((bad i j).card : ℝ)) * (ℓ : ℝ) ≤ (W_mid : ℝ) * (ℓ : ℝ) := by
        rw [sum_mul]
        calc ∑ j : Fin ℓ, ((bad i j).card : ℝ) * (ℓ : ℝ)
          _ ≤ ∑ _j : Fin ℓ, (W_mid : ℝ) := sum_le_sum (fun j _ => hbad_card i j)
          _ = (ℓ : ℝ) * (W_mid : ℝ) := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
          _ = (W_mid : ℝ) * (ℓ : ℝ) := mul_comm _ _
      exact h1.trans (le_of_mul_le_mul_right h2 hℓ_pos)
    have hsdiff_nat : (A'' i).card ≤
        (Good i).card + ((Finset.univ : Finset (Fin ℓ)).biUnion (bad i)).card :=
      card_le_card_sdiff_add_card
    have hsdiff_real : ((A'' i).card : ℝ) ≤
        ((Good i).card : ℝ) + (((Finset.univ : Finset (Fin ℓ)).biUnion (bad i)).card : ℝ) := by
      exact_mod_cast hsdiff_nat
    rw [hA''_card i] at hsdiff_real
    push_cast at hsdiff_real
    have hge : (W_mid : ℝ) ≤ ((Good i).card : ℝ) := by linarith
    exact_mod_cast hge
  let A' (i : Fin ℓ) : Finset V := (exists_subset_card_eq (hGood_card i)).choose
  have hA'_Good : ∀ i, A' i ⊆ Good i := fun i => (exists_subset_card_eq (hGood_card i)).choose_spec.1
  have hA'_card : ∀ i, (A' i).card = W_mid :=
    fun i => (exists_subset_card_eq (hGood_card i)).choose_spec.2
  have hA'_sub : ∀ i, A' i ⊆ A'' i := fun i => (hA'_Good i).trans sdiff_subset
  refine ⟨A', hA'_sub, hA'_card, ?_⟩
  intro i j hij u hu
  have hu_Good : u ∈ Good i := hA'_Good i hu
  have hu_not_bad : u ∉ bad i j := by
    simp only [Good, mem_sdiff, mem_biUnion, mem_univ, true_and, not_exists] at hu_Good
    exact hu_Good.2 j
  have hu_A'' : u ∈ A'' i := hA'_sub i hu
  have hdeg_A'' : ((neighborFinsetIn (H_pair i j) u (A'' j)).card : ℝ) ≤ thr := by
    by_contra! hgt
    dsimp [bad] at hu_not_bad
    rw [if_pos hij, mem_filter] at hu_not_bad
    exact hu_not_bad ⟨hu_A'', hgt⟩
  have hdeg_sub : (neighborFinsetIn (H_pair i j) u (A' j)).card ≤
      (neighborFinsetIn (H_pair i j) u (A'' j)).card :=
    card_le_card (neighborFinsetIn_mono' (H_pair i j) u (hA'_sub j))
  exact (by exact_mod_cast hdeg_sub :
    ((neighborFinsetIn (H_pair i j) u (A' j)).card : ℝ) ≤
      ((neighborFinsetIn (H_pair i j) u (A'' j)).card : ℝ)).trans hdeg_A''

/--
Scale bound for Step 1.3 (`step1c_delta_wrong_le`, `main.tex` lines 376, 379):
When $y \in (0, 2^{-120}]$, $a \ge \max(20, 4h, 4 d' h + 10)$, $c_2 \ge 4$,
$\ell = \lceil y^{-a} \rceil$, $x_{\mathrm{sp}} = (y^a)^{3 c_2}$, and
$M_{\mathrm{ceil}} = \lceil y^{-(4 d' h + 2)} \rceil$, we have
$\ell \cdot h \cdot \bigl(8 \ell^5 x_{\mathrm{sp}} M_{\mathrm{ceil}}\bigr) \le y^{3a}$.
-/
private theorem step1c_delta_wrong_le {y d' c₂ : ℝ} {a h : ℕ}
    (hy0 : 0 < y) (hy120 : y ≤ (2 : ℝ) ^ (-120 : ℝ))
    (hd' : 0 < d') (hc₂ : 4 ≤ c₂) (hh : 3 ≤ h)
    (ha20 : 20 ≤ a) (ha_4h : 4 * h ≤ a) (ha_dh : 4 * d' * (h : ℝ) + 10 ≤ (a : ℝ)) :
    let ε_GN := y ^ a
    let ℓ := ⌈ε_GN⁻¹⌉₊
    let x_sp := ε_GN ^ (3 * c₂)
    let M_ceil := ⌈y ^ (-(4 * d' * (h : ℝ) + 2))⌉₊
    (ℓ : ℝ) * (h : ℝ) * (8 * (ℓ : ℝ) ^ 5 * x_sp * (M_ceil : ℝ)) ≤ y ^ (3 * a) := by
  intro ε_GN ℓ x_sp M_ceil
  have hy_le1 : y ≤ 1 := hy120.trans (by norm_num)
  have ha_pos : 1 ≤ a := by omega
  have hε_pos : 0 < ε_GN := by dsimp [ε_GN]; positivity
  have hε_le_y : ε_GN ≤ y := by
    dsimp [ε_GN]
    calc y ^ a ≤ y ^ 1 := pow_le_pow_of_le_one hy0.le hy_le1 ha_pos
      _ = y := pow_one y
  have hε_le1 : ε_GN ≤ 1 := hε_le_y.trans hy_le1
  have h1_le_ε_inv : (1 : ℝ) ≤ ε_GN⁻¹ := one_le_inv₀ hε_pos |>.mpr hε_le1
  have hℓ_le : (ℓ : ℝ) ≤ 2 * y ^ (-(a : ℝ)) := by
    have hlt : (ℓ : ℝ) < ε_GN⁻¹ + 1 := Nat.ceil_lt_add_one (inv_nonneg.mpr hε_pos.le)
    have hε_inv_eq : ε_GN⁻¹ = y ^ (-(a : ℝ)) := by
      dsimp [ε_GN]
      rw [← Real.rpow_natCast y a, ← Real.rpow_neg hy0.le]
    linarith
  have hM_le_ya : (M_ceil : ℝ) ≤ 2 * y ^ (-(a : ℝ)) := by
    have hpos_exp : 0 ≤ 4 * d' * (h : ℝ) + 2 := by positivity
    have h1_le_M : (1 : ℝ) ≤ y ^ (-(4 * d' * (h : ℝ) + 2)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy0 hy_le1 (by linarith)
    have hlt : (M_ceil : ℝ) < y ^ (-(4 * d' * (h : ℝ) + 2)) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hrpow : y ^ (-(4 * d' * (h : ℝ) + 2)) ≤ y ^ (-(a : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hy0 hy_le1 (by linarith)
    linarith
  have hh_le_ya : (h : ℝ) ≤ y ^ (-(a : ℝ)) := by
    have h2_le_inv : (2 : ℝ) ≤ y⁻¹ := by
      rw [le_inv_comm₀ zero_lt_two hy0]
      exact hy120.trans (by norm_num)
    have hh_le_2a : h ≤ 2 ^ a := (by omega : h ≤ a).trans Nat.lt_two_pow_self.le
    calc (h : ℝ)
      _ ≤ ((2 ^ a : ℕ) : ℝ) := by exact_mod_cast hh_le_2a
      _ = (2 : ℝ) ^ a := by push_cast; rfl
      _ ≤ (y⁻¹) ^ a := pow_le_pow_left₀ zero_le_two h2_le_inv a
      _ = y ^ (-(a : ℝ)) := by
        rw [inv_pow, ← Real.rpow_natCast y a, ← Real.rpow_neg hy0.le]
  have hx_sp_le : x_sp ≤ y ^ (12 * (a : ℝ)) := by
    dsimp [x_sp, ε_GN]
    rw [← Real.rpow_natCast y a, ← Real.rpow_mul hy0.le]
    exact Real.rpow_le_rpow_of_exponent_ge hy0 hy_le1 (by nlinarith)
  have hℓ5_le : (ℓ : ℝ) ^ 5 ≤ 32 * y ^ (-5 * (a : ℝ)) := by
    calc (ℓ : ℝ) ^ 5
      _ ≤ (2 * y ^ (-(a : ℝ))) ^ 5 := pow_le_pow_left₀ (Nat.cast_nonneg _) hℓ_le 5
      _ = 32 * (y ^ (-(a : ℝ))) ^ (5 : ℝ) := by
        rw [mul_pow, show (2 : ℝ) ^ 5 = 32 by norm_num,
          show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      _ = 32 * y ^ (-5 * (a : ℝ)) := by
        rw [← Real.rpow_mul hy0.le]; congr 2; ring
  have hprod_le : (ℓ : ℝ) * (h : ℝ) * (8 * (ℓ : ℝ) ^ 5 * x_sp * (M_ceil : ℝ)) ≤
      1024 * y ^ (4 * (a : ℝ)) := by
    have h1 : (ℓ : ℝ) * (h : ℝ) ≤ 2 * y ^ (-2 * (a : ℝ)) := by
      calc (ℓ : ℝ) * (h : ℝ)
        _ ≤ (2 * y ^ (-(a : ℝ))) * y ^ (-(a : ℝ)) :=
          mul_le_mul hℓ_le hh_le_ya (Nat.cast_nonneg _) (by positivity)
        _ = 2 * (y ^ (-(a : ℝ)) * y ^ (-(a : ℝ))) := by ring
        _ = 2 * y ^ (-2 * (a : ℝ)) := by
          rw [← Real.rpow_add hy0]; congr 2; ring
    have h2 : 8 * (ℓ : ℝ) ^ 5 * x_sp * (M_ceil : ℝ) ≤ 512 * y ^ (6 * (a : ℝ)) := by
      calc 8 * (ℓ : ℝ) ^ 5 * x_sp * (M_ceil : ℝ)
        _ ≤ 8 * (32 * y ^ (-5 * (a : ℝ))) * y ^ (12 * (a : ℝ)) * (2 * y ^ (-(a : ℝ))) := by
          refine mul_le_mul ?_ hM_le_ya (Nat.cast_nonneg _) (by positivity)
          refine mul_le_mul ?_ hx_sp_le (by dsimp [x_sp]; positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left hℓ5_le (by norm_num)
        _ = 512 * (y ^ (-5 * (a : ℝ)) * y ^ (12 * (a : ℝ)) * y ^ (-(a : ℝ))) := by ring
        _ = 512 * y ^ (6 * (a : ℝ)) := by
          rw [← Real.rpow_add hy0, ← Real.rpow_add hy0]; congr 2; ring
    calc (ℓ : ℝ) * (h : ℝ) * (8 * (ℓ : ℝ) ^ 5 * x_sp * (M_ceil : ℝ))
      _ ≤ (2 * y ^ (-2 * (a : ℝ))) * (512 * y ^ (6 * (a : ℝ))) :=
        mul_le_mul h1 h2 (by dsimp [x_sp]; positivity) (by positivity)
      _ = 1024 * (y ^ (-2 * (a : ℝ)) * y ^ (6 * (a : ℝ))) := by ring
      _ = 1024 * y ^ (4 * (a : ℝ)) := by
        rw [← Real.rpow_add hy0]; congr 2; ring
  have h1024_ya : 1024 * y ^ (a : ℝ) ≤ 1 := by
    have hya_le_y : y ^ (a : ℝ) ≤ y := by
      calc y ^ (a : ℝ) ≤ y ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hy0 hy_le1 (by exact_mod_cast ha_pos)
        _ = y := Real.rpow_one y
    have h1024_y : 1024 * y ≤ 1 := by
      have : (2 : ℝ) ^ (-120 : ℝ) ≤ 1 / 1024 := by norm_num
      linarith [hy120.trans this]
    exact (mul_le_mul_of_nonneg_left hya_le_y (by norm_num)).trans h1024_y
  calc (ℓ : ℝ) * (h : ℝ) * (8 * (ℓ : ℝ) ^ 5 * x_sp * (M_ceil : ℝ))
    _ ≤ 1024 * y ^ (4 * (a : ℝ)) := hprod_le
    _ = (1024 * y ^ (a : ℝ)) * y ^ (3 * (a : ℝ)) := by
      rw [show 4 * (a : ℝ) = (a : ℝ) + 3 * (a : ℝ) by ring, Real.rpow_add hy0]; ring
    _ ≤ 1 * y ^ (3 * (a : ℝ)) := mul_le_mul_of_nonneg_right h1024_ya (by positivity)
    _ = y ^ (3 * a) := by
      rw [one_mul, ← Real.rpow_natCast y (3 * a)]
      push_cast; rfl

open Classical in
/--
**Sub-step 1.2 & 1.3 (`step1c_viral_purification_to_complete`, `main.tex` lines 367–376)**:
Given pairwise disjoint blocks $A'_i$ ($i \in \text{Fin }\ell$) in an $\{H_1ᶜ, H_2ᶜ\}$-free graph
$G : \text{SimpleGraph } V_{\mathrm{type}}$ (`V_type : Type`) with $|A'_i| = W_{\mathrm{mid}} = 2 M_{\mathrm{ceil}} \ell^2 w_y$
and $|N_{H_{\mathrm{pair}}(i, j)}(u) \cap A'_j| \le 4 \ell^3 x_{\mathrm{sp}} W_{\mathrm{mid}}$ for all $i \neq j$,
applying `viral_extension_core_of_not_restricted` to each $A'_i$ at $\varepsilon_{\mathrm{in}} = y^4$
and deleting non-neighbors of $\Phi_i$ whenever $J.\text{Adj } i\ j$ yields either:
- **(R2)** a $2y^2$-restricted subset $U \subseteq V_{\mathrm{type}}$ of size $\ge w_y$; or
- purified cores $D'_j \subseteq A'_j$ of size $|D'_j| \ge 2 \ell^2 w_y$ such that **every edge
  $J.\text{Adj } i\ j$ is $100\%$ complete in $G$ (`IsCompletePair G (D' i) (D' j)`)**!
-/
private theorem step1c_viral_purification_to_complete
    {V_type : Type} [Fintype V_type] [DecidableEq V_type]
    {W₁ W₂ : Type*} [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]
    (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂)
    (v₀ u₀ : W₁) (hu₀_ne : u₀ ≠ v₀)
    (hleaf : ∀ w : W₁, H₁.Adj v₀ w ↔ w = u₀)
    (hh : 3 ≤ Fintype.card W₁)
    {d' : ℝ} (hd' : 0 < d')
    (hviral : ∀ (U_type : Type) [Fintype U_type] [DecidableEq U_type]
      (F_G : SimpleGraph U_type) (ε : ℝ),
      0 < ε → ε < 1 / 2 →
      (indCopyCount (H₁.comap (Subtype.val : {w : W₁ // w ≠ v₀} → W₁))ᶜ F_G : ℝ) ≤
        (ε ^ d' * (Fintype.card U_type : ℝ)) ^ (Fintype.card {w : W₁ // w ≠ v₀}) →
      (indCopyCount H₂ᶜ F_G : ℝ) ≤
        (ε ^ d' * (Fintype.card U_type : ℝ)) ^ (Fintype.card W₂) →
      ∃ S : Finset U_type, IsEpsRestrictedOn F_G S ε ∧
        ε ^ d' * (Fintype.card U_type : ℝ) ≤ (S.card : ℝ))
    (G : SimpleGraph V_type) (hG₁ : IsInducedSubgraphFree G H₁ᶜ) (hG₂ : IsInducedSubgraphFree G H₂ᶜ)
    {y c₂ : ℝ} {a w_y : ℕ}
    (hy0 : 0 < y) (hy120 : y ≤ (2 : ℝ) ^ (-120 : ℝ))
    (hc₂ : 4 ≤ c₂) (ha20 : 20 ≤ a)
    (ha_4h : 4 * Fintype.card W₁ ≤ a)
    (ha_dh : 4 * d' * (Fintype.card W₁ : ℝ) + 10 ≤ (a : ℝ))
    (hw_y : 1 ≤ w_y)
    (J : SimpleGraph (Fin ⌈(y ^ a)⁻¹⌉₊))
    (A' : Fin ⌈(y ^ a)⁻¹⌉₊ → Finset V_type)
    (hA'_disj : ∀ i j, i ≠ j → Disjoint (A' i) (A' j))
    (hA'_card : ∀ i, (A' i).card =
      2 * ⌈y ^ (-(4 * d' * (Fintype.card W₁ : ℝ) + 2))⌉₊ * ⌈(y ^ a)⁻¹⌉₊ ^ 2 * w_y)
    (hA'_deg : ∀ i j : Fin ⌈(y ^ a)⁻¹⌉₊, i ≠ j → ∀ u ∈ A' i,
      ((neighborFinsetIn (if J.Adj i j then Gᶜ else G) u (A' j)).card : ℝ) ≤
        4 * (⌈(y ^ a)⁻¹⌉₊ : ℝ) ^ 3 * ((y ^ a) ^ (3 * c₂)) *
          ((2 * ⌈y ^ (-(4 * d' * (Fintype.card W₁ : ℝ) + 2))⌉₊ *
            ⌈(y ^ a)⁻¹⌉₊ ^ 2 * w_y : ℕ) : ℝ)) :
    let ℓ := ⌈(y ^ a)⁻¹⌉₊
    (∃ U : Finset V_type, IsEpsRestrictedOn G U (2 * y ^ 2) ∧ (w_y : ℝ) ≤ (U.card : ℝ)) ∨
    (∃ D' : Fin ℓ → Finset V_type,
      (∀ j, D' j ⊆ A' j) ∧
      (∀ j, 2 * (ℓ : ℝ) ^ 2 * (w_y : ℝ) ≤ ((D' j).card : ℝ)) ∧
      (∀ i j : Fin ℓ, J.Adj i j → IsCompletePair G (D' i) (D' j))) := by
  classical
  intro ℓ
  let h := Fintype.card W₁
  let ε_GN := y ^ a
  let x_sp := ε_GN ^ (3 * c₂)
  let M_ceil := ⌈y ^ (-(4 * d' * (h : ℝ) + 2))⌉₊
  let W_mid := 2 * M_ceil * ℓ ^ 2 * w_y
  have hy_le1 : y ≤ 1 := hy120.trans (by norm_num)
  have hy4_pos : 0 < y ^ 4 := by positivity
  have hy4_half : y ^ 4 < 1 / 2 := by
    have : y < 1 / 2 := hy120.trans_lt (by norm_num)
    calc y ^ 4 < (1 / 2 : ℝ) ^ 4 := pow_lt_pow_left₀ this hy0.le (by norm_num)
      _ < 1 / 2 := by norm_num
  have hy4_le_2y2 : y ^ 4 ≤ 2 * y ^ 2 := by nlinarith [sq_nonneg y]
  have hℓ_pos : 1 ≤ ℓ := Nat.ceil_pos.mpr (by positivity)
  have hM_pos : 1 ≤ M_ceil := Nat.ceil_pos.mpr (by positivity)
  have hW_mid_pos : 1 ≤ W_mid :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos zero_lt_two hM_pos) (pow_pos hℓ_pos 2)) hw_y
  have hM_ge : y ^ (-(4 * d' * (h : ℝ) + 2)) ≤ (M_ceil : ℝ) := Nat.le_ceil _
  -- Check whether every A'_i avoids a y^4-restricted subset of size ≥ (y^4)^d' |A'_i|
  by_cases h_some_rest : ∃ i : Fin ℓ, ∃ U ⊆ A' i,
      IsEpsRestrictedOn G U (y ^ 4) ∧ (y ^ 4) ^ d' * ((A' i).card : ℝ) ≤ (U.card : ℝ)
  · left
    obtain ⟨i, U, _, hU_rest, hU_card⟩ := h_some_rest
    refine ⟨U, hU_rest.mono hy4_le_2y2, ?_⟩
    have h1 : (1 : ℝ) ≤ (y ^ 4) ^ d' * (M_ceil : ℝ) := by
      have hexp : y ^ (4 * d') * y ^ (-(4 * d' * (h : ℝ) + 2)) ≥ 1 := by
        rw [← Real.rpow_add hy0]
        have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast (by omega : 1 ≤ h)
        exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy0 hy_le1 (by nlinarith)
      calc (1 : ℝ)
        _ ≤ y ^ (4 * d') * y ^ (-(4 * d' * (h : ℝ) + 2)) := hexp
        _ = (y ^ 4) ^ d' * y ^ (-(4 * d' * (h : ℝ) + 2)) := by
          rw [← Real.rpow_natCast y 4, ← Real.rpow_mul hy0.le]; push_cast; rfl
        _ ≤ (y ^ 4) ^ d' * (M_ceil : ℝ) := mul_le_mul_of_nonneg_left hM_ge (by positivity)
    have h2 : (w_y : ℝ) ≤ (y ^ 4) ^ d' * ((A' i).card : ℝ) := by
      rw [hA'_card i]
      push_cast
      have hℓ2_ge1 : (1 : ℝ) ≤ (ℓ : ℝ) ^ 2 := by
        have : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ_pos
        nlinarith
      calc (w_y : ℝ)
        _ ≤ ((y ^ 4) ^ d' * (M_ceil : ℝ)) * (w_y : ℝ) := by
          nlinarith [show (0 : ℝ) ≤ (w_y : ℝ) by positivity]
        _ ≤ ((y ^ 4) ^ d' * (M_ceil : ℝ)) * (2 * (ℓ : ℝ) ^ 2 * (w_y : ℝ)) :=
          mul_le_mul_of_nonneg_left (by nlinarith [show (0 : ℝ) ≤ (w_y : ℝ) by positivity])
            (by positivity)
        _ = (y ^ 4) ^ d' * (2 * (M_ceil : ℝ) * (ℓ : ℝ) ^ 2 * (w_y : ℝ)) := by ring
    exact h2.trans hU_card
  · right
    push_neg at h_some_rest
    have hex_core : ∀ i : Fin ℓ, ∃ Φ ⊆ A' i, ∃ D ⊆ A' i,
        Φ.card ≤ h - 2 ∧ Disjoint Φ D ∧
        4 * (ℓ : ℝ) ^ 2 * (w_y : ℝ) ≤ (D.card : ℝ) ∧
        ∀ u ∈ D, ∀ v : V_type, v ∉ Φ → v ≠ u → (∀ z ∈ Φ, G.Adj z v) → G.Adj u v := by
      intro i
      have hA'_ne : (A' i).Nonempty := card_pos.mp (by rw [hA'_card i]; exact hW_mid_pos)
      rcases viral_extension_core_of_not_restricted H₁ H₂ v₀ u₀ hu₀_ne hleaf hh hd' hviral
          G hG₁ hG₂ (A' i) hA'_ne (y ^ 4) hy4_pos hy4_half with
        ⟨U, hUA', hU_rest, hU_card⟩ | ⟨Φ, hΦA', D, hDA', hΦ_card, hdisj, hD_card, hD_ext⟩
      · exact False.elim (not_le.mpr (h_some_rest i U hUA' hU_rest) hU_card)
      · refine ⟨Φ, hΦA', D, hDA', hΦ_card, hdisj, ?_, hD_ext⟩
        have h1 : (2 : ℝ) ≤ (y ^ 4) ^ (d' * ((h - 1 : ℕ) : ℝ)) * (M_ceil : ℝ) := by
          have hsub : ((h - 1 : ℕ) : ℝ) ≤ (h : ℝ) := by exact_mod_cast Nat.sub_le h 1
          have hexp : 4 * d' * ((h - 1 : ℕ) : ℝ) + -(4 * d' * (h : ℝ) + 2) ≤ -2 := by nlinarith
          have h2_le_y2 : (2 : ℝ) ≤ y ^ (-2 : ℝ) := by
            have hy_inv2 : (2 : ℝ) ≤ y ^ (-1 : ℝ) := by
              rw [Real.rpow_neg_one, le_inv_comm₀ zero_lt_two hy0]
              exact hy120.trans (by norm_num)
            exact hy_inv2.trans (Real.rpow_le_rpow_of_exponent_ge hy0 hy_le1 (by norm_num))
          calc (2 : ℝ)
            _ ≤ y ^ (-2 : ℝ) := h2_le_y2
            _ ≤ y ^ (4 * d' * ((h - 1 : ℕ) : ℝ) + -(4 * d' * (h : ℝ) + 2)) :=
              Real.rpow_le_rpow_of_exponent_ge hy0 hy_le1 hexp
            _ = (y ^ 4) ^ (d' * ((h - 1 : ℕ) : ℝ)) * y ^ (-(4 * d' * (h : ℝ) + 2)) := by
              rw [Real.rpow_add hy0, ← Real.rpow_natCast y 4, ← Real.rpow_mul hy0.le]
              congr 2; ring
            _ ≤ (y ^ 4) ^ (d' * ((h - 1 : ℕ) : ℝ)) * (M_ceil : ℝ) :=
              mul_le_mul_of_nonneg_left hM_ge (by positivity)
        have h2 : 4 * (ℓ : ℝ) ^ 2 * (w_y : ℝ) ≤
            (y ^ 4) ^ (d' * ((h - 1 : ℕ) : ℝ)) * ((A' i).card : ℝ) := by
          rw [hA'_card i]
          push_cast
          calc 4 * (ℓ : ℝ) ^ 2 * (w_y : ℝ)
            _ = 2 * (2 * (ℓ : ℝ) ^ 2 * (w_y : ℝ)) := by ring
            _ ≤ ((y ^ 4) ^ (d' * ((h - 1 : ℕ) : ℝ)) * (M_ceil : ℝ)) *
                (2 * (ℓ : ℝ) ^ 2 * (w_y : ℝ)) :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
            _ = (y ^ 4) ^ (d' * ((h - 1 : ℕ) : ℝ)) *
                (2 * (M_ceil : ℝ) * (ℓ : ℝ) ^ 2 * (w_y : ℝ)) := by ring
        exact h2.trans hD_card.le
    let Φ (i : Fin ℓ) : Finset V_type := (hex_core i).choose
    have hΦ_spec := fun i => (hex_core i).choose_spec
    let D (i : Fin ℓ) : Finset V_type := (hΦ_spec i).2.choose
    have hD_spec := fun i => (hΦ_spec i).2.choose_spec
    have hΦ_sub : ∀ i, Φ i ⊆ A' i := fun i => (hΦ_spec i).1
    have hD_sub : ∀ i, D i ⊆ A' i := fun i => (hD_spec i).1
    have hΦ_card : ∀ i, (Φ i).card ≤ h - 2 := fun i => (hD_spec i).2.1
    have hD_card : ∀ i, 4 * (ℓ : ℝ) ^ 2 * (w_y : ℝ) ≤ ((D i).card : ℝ) :=
      fun i => (hD_spec i).2.2.2.1
    have hD_ext : ∀ i, ∀ u ∈ D i, ∀ v : V_type, v ∉ Φ i → v ≠ u →
        (∀ z ∈ Φ i, G.Adj z v) → G.Adj u v :=
      fun i => (hD_spec i).2.2.2.2
    -- Define D'_j := D_j \ ⋃_{i : J.Adj i j} ⋃_{z ∈ Φ_i} (A'_j ∩ N_{Gᶜ}(z))
    let badPair (j i : Fin ℓ) : Finset V_type :=
      if J.Adj i j then
        (Φ i).biUnion (fun z => neighborFinsetIn Gᶜ z (A' j))
      else ∅
    let BadNonEdge (j : Fin ℓ) : Finset V_type :=
      (Finset.univ : Finset (Fin ℓ)).biUnion (badPair j)
    let D' (j : Fin ℓ) : Finset V_type := D j \ BadNonEdge j
    have hD'_sub : ∀ j, D' j ⊆ A' j := fun j => sdiff_subset.trans (hD_sub j)
    -- Bound |BadNonEdge j| ≤ w_y using step1c_delta_wrong_le
    have hBad_card : ∀ j : Fin ℓ, ((BadNonEdge j).card : ℝ) ≤ (w_y : ℝ) := by
      intro j
      let Δ_wrong : ℝ := 4 * (ℓ : ℝ) ^ 3 * x_sp * (W_mid : ℝ)
      have hpair_le : ∀ i : Fin ℓ, ((badPair j i).card : ℝ) ≤ (h : ℝ) * Δ_wrong := by
        intro i
        dsimp [badPair]
        split_ifs with hadj
        · have hij : i ≠ j := J.ne_of_adj hadj
          have h1 : (((Φ i).biUnion (fun z => neighborFinsetIn Gᶜ z (A' j))).card : ℝ) ≤
              ∑ z ∈ Φ i, ((neighborFinsetIn Gᶜ z (A' j)).card : ℝ) := by
            exact_mod_cast card_biUnion_le
          have h2 : ∑ z ∈ Φ i, ((neighborFinsetIn Gᶜ z (A' j)).card : ℝ) ≤
              ∑ _z ∈ Φ i, Δ_wrong := by
            refine sum_le_sum (fun z hz => ?_)
            have hdeg := hA'_deg i j hij z (hΦ_sub i hz)
            rw [if_pos hadj] at hdeg
            exact hdeg
          have hΦ_le_h : ((Φ i).card : ℝ) ≤ (h : ℝ) := by
            have : (Φ i).card ≤ h := (hΦ_card i).trans (Nat.sub_le h 2)
            exact_mod_cast this
          have hΔ_nonneg : 0 ≤ Δ_wrong := by dsimp [Δ_wrong, x_sp, ε_GN]; positivity
          calc (((Φ i).biUnion (fun z => neighborFinsetIn Gᶜ z (A' j))).card : ℝ)
            _ ≤ ∑ _z ∈ Φ i, Δ_wrong := h1.trans h2
            _ = ((Φ i).card : ℝ) * Δ_wrong := by rw [sum_const, nsmul_eq_mul]
            _ ≤ (h : ℝ) * Δ_wrong := mul_le_mul_of_nonneg_right hΦ_le_h hΔ_nonneg
        · simp only [card_empty, Nat.cast_zero]
          dsimp [Δ_wrong, x_sp, ε_GN]; positivity
      have hbiUnion : ((BadNonEdge j).card : ℝ) ≤ (ℓ : ℝ) * (h : ℝ) * Δ_wrong := by
        have h1 : ((BadNonEdge j).card : ℝ) ≤ ∑ i : Fin ℓ, ((badPair j i).card : ℝ) := by
          exact_mod_cast card_biUnion_le
        calc ((BadNonEdge j).card : ℝ)
          _ ≤ ∑ _i : Fin ℓ, (h : ℝ) * Δ_wrong :=
            h1.trans (sum_le_sum (fun i _ => hpair_le i))
          _ = (ℓ : ℝ) * ((h : ℝ) * Δ_wrong) := by
            rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
          _ = (ℓ : ℝ) * (h : ℝ) * Δ_wrong := by ring
      have hΔ_eq : (ℓ : ℝ) * (h : ℝ) * Δ_wrong =
          ((ℓ : ℝ) * (h : ℝ) * (8 * (ℓ : ℝ) ^ 5 * x_sp * (M_ceil : ℝ))) * (w_y : ℝ) := by
        dsimp [Δ_wrong, W_mid]
        push_cast
        ring
      have hscale := step1c_delta_wrong_le hy0 hy120 hd' hc₂ hh ha20 ha_4h ha_dh
      have hy3a_le1 : y ^ (3 * a) ≤ 1 := pow_le_one₀ hy0.le hy_le1
      calc ((BadNonEdge j).card : ℝ)
        _ ≤ ((ℓ : ℝ) * (h : ℝ) * (8 * (ℓ : ℝ) ^ 5 * x_sp * (M_ceil : ℝ))) * (w_y : ℝ) :=
          hbiUnion.trans_eq hΔ_eq
        _ ≤ y ^ (3 * a) * (w_y : ℝ) := mul_le_mul_of_nonneg_right hscale (Nat.cast_nonneg _)
        _ ≤ 1 * (w_y : ℝ) := mul_le_mul_of_nonneg_right hy3a_le1 (Nat.cast_nonneg _)
        _ = (w_y : ℝ) := one_mul _
    have hD'_card : ∀ j : Fin ℓ, 2 * (ℓ : ℝ) ^ 2 * (w_y : ℝ) ≤ ((D' j).card : ℝ) := by
      intro j
      have hsdiff_nat : (D j).card ≤ (D' j).card + (BadNonEdge j).card :=
        card_le_card_sdiff_add_card
      have hsdiff_real : ((D j).card : ℝ) ≤ ((D' j).card : ℝ) + ((BadNonEdge j).card : ℝ) := by
        exact_mod_cast hsdiff_nat
      have hℓ2_ge1 : (1 : ℝ) ≤ (ℓ : ℝ) ^ 2 := by
        have : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ_pos
        nlinarith
      have hD_ge := hD_card j
      have hB_le := hBad_card j
      nlinarith [show (0 : ℝ) ≤ (w_y : ℝ) by positivity]
    refine ⟨D', hD'_sub, hD'_card, ?_⟩
    intro i j hadj u hu v hv
    have hij : i ≠ j := J.ne_of_adj hadj
    have hu_D : u ∈ D i := (mem_sdiff.mp hu).1
    have hv_A'j : v ∈ A' j := hD'_sub j hv
    have hv_not_Φi : v ∉ Φ i :=
      fun hvΦ => Finset.disjoint_left.mp (hA'_disj i j hij) (hΦ_sub i hvΦ) hv_A'j
    have hv_ne_u : v ≠ u :=
      fun heq => Finset.disjoint_left.mp (hA'_disj i j hij) (hD'_sub i hu) (heq ▸ hv_A'j)
    refine hD_ext i u hu_D v hv_not_Φi hv_ne_u ?_
    intro z hzΦ
    have hv_not_Bad : v ∉ BadNonEdge j := (mem_sdiff.mp hv).2
    have hne_zv : z ≠ v := fun h => hv_not_Φi (h ▸ hzΦ)
    by_contra hnad_zv
    have hadj_c : Gᶜ.Adj z v := ⟨hne_zv, hnad_zv⟩
    apply hv_not_Bad
    rw [mem_biUnion]
    refine ⟨i, mem_univ i, ?_⟩
    dsimp [badPair]
    rw [if_pos hadj, mem_biUnion]
    exact ⟨z, hzΦ, (mem_neighborFinsetIn' Gᶜ z v (A' j)).mpr ⟨hv_A'j, hadj_c⟩⟩

/--
**Sub-step 1.4 (`step1d_anticonnected_pruning`, `main.tex` line 377)**:
Given purified cores $D'_j \subseteq A'_j$ ($j \in \text{Fin }\ell$, $\ell = \lceil y^{-a} \rceil \ge 2$)
of size $|D'_j| \ge 2 \ell^2 w_y$ where every edge $J.\text{Adj } i\ j$ is $100\%$ complete in $G$
and every non-edge $¬J.\text{Adj } i\ j$ ($i \neq j$) has $|N_G(u) \cap A'_j| \le y^{3a} w_y$ for all
$u \in A'_i$, applying Lemma 1 (`anticonnected_component_or_complete_blockade`) and
`exists_anticonnected_subset_card_eq` yields either:
- **(R2)** a $2y^2$-restricted subset $U \subseteq V_{\mathrm{type}}$ of size $\ge w_y$; or
- an equal-sized anticonnected complete-or-$y^{3a}$-sparse $(\ell, w_y)$-blockade $B$.
-/
private theorem step1d_anticonnected_pruning
    {V_type : Type} [Fintype V_type] [DecidableEq V_type]
    (G : SimpleGraph V_type)
    {y : ℝ} {a w_y : ℕ}
    (hy0 : 0 < y) (hy120 : y ≤ (2 : ℝ) ^ (-120 : ℝ))
    (ha20 : 20 ≤ a) (hw_y : 1 ≤ w_y)
    (J : SimpleGraph (Fin ⌈(y ^ a)⁻¹⌉₊))
    (A' D' : Fin ⌈(y ^ a)⁻¹⌉₊ → Finset V_type)
    (hA'_disj : ∀ i j, i ≠ j → Disjoint (A' i) (A' j))
    (hD'_sub : ∀ j, D' j ⊆ A' j)
    (hD'_card : ∀ j, 2 * (⌈(y ^ a)⁻¹⌉₊ : ℝ) ^ 2 * (w_y : ℝ) ≤ ((D' j).card : ℝ))
    (hD'_comp : ∀ i j, J.Adj i j → IsCompletePair G (D' i) (D' j))
    (hA'_nonedge_deg : ∀ i j : Fin ⌈(y ^ a)⁻¹⌉₊, i ≠ j → ¬J.Adj i j → ∀ u ∈ A' i,
      ((neighborFinsetIn G u (A' j)).card : ℝ) ≤ y ^ (3 * a) * (w_y : ℝ)) :
    let ℓ := ⌈(y ^ a)⁻¹⌉₊
    (∃ U : Finset V_type, IsEpsRestrictedOn G U (2 * y ^ 2) ∧ (w_y : ℝ) ≤ (U.card : ℝ)) ∨
    (∃ B : Fin ℓ → Finset V_type,
      IsCompleteOrXSparseBlockadeIn G Finset.univ ℓ (w_y : ℝ) (y ^ (3 * a)) B ∧
      (∀ i : Fin ℓ, (B i).card = w_y ∧ IsAnticonnected G (B i))) := by
  classical
  intro ℓ
  have hy_le1 : y ≤ 1 := hy120.trans (by norm_num)
  have hℓ_ge_inv : (y ^ a)⁻¹ ≤ (ℓ : ℝ) := Nat.le_ceil _
  have hℓ2 : 2 ≤ ℓ := by
    have h2_le_ya_inv : (2 : ℝ) ≤ (y ^ a)⁻¹ := by
      rw [le_inv_comm₀ zero_lt_two (by positivity)]
      calc y ^ a ≤ y ^ 1 := pow_le_pow_of_le_one hy0.le hy_le1 (by omega)
        _ = y := pow_one y
        _ ≤ (2 : ℝ)⁻¹ := hy120.trans (by norm_num)
    exact_mod_cast h2_le_ya_inv.trans hℓ_ge_inv
  have hℓ_pos : (0 : ℝ) < (ℓ : ℝ) := by positivity
  by_cases hall_anti : ∀ j : Fin ℓ, ∃ C ⊆ D' j, C.Nonempty ∧ IsAnticonnected G C ∧
      ((D' j).card : ℝ) / (ℓ : ℝ) ≤ (C.card : ℝ)
  · right
    have hB_ex : ∀ j : Fin ℓ, ∃ B_j ⊆ D' j, B_j.card = w_y ∧ IsAnticonnected G B_j := by
      intro j
      let C_j := (hall_anti j).choose
      have hCj_spec := (hall_anti j).choose_spec
      have hw_le_Cj : w_y ≤ C_j.card := by
        have h1 : (w_y : ℝ) ≤ ((D' j).card : ℝ) / (ℓ : ℝ) := by
          rw [le_div_iff₀ hℓ_pos]
          have hℓ_ge1 : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast (by omega : 1 ≤ ℓ)
          have hDj := hD'_card j
          nlinarith [show (0 : ℝ) ≤ (w_y : ℝ) * (ℓ : ℝ) by positivity]
        exact_mod_cast h1.trans hCj_spec.2.2.2
      obtain ⟨B_j, hBj_Cj, hBj_card, hBj_anti⟩ :=
        exists_anticonnected_subset_card_eq G C_j w_y hCj_spec.2.2.1 hw_y hw_le_Cj
      exact ⟨B_j, hBj_Cj.trans hCj_spec.1, hBj_card, hBj_anti⟩
    let B (j : Fin ℓ) : Finset V_type := (hB_ex j).choose
    have hB_sub : ∀ j, B j ⊆ D' j := fun j => (hB_ex j).choose_spec.1
    have hB_card : ∀ j, (B j).card = w_y := fun j => (hB_ex j).choose_spec.2.1
    have hB_anti : ∀ j, IsAnticonnected G (B j) := fun j => (hB_ex j).choose_spec.2.2
    have hB_block : IsBlockadeIn G Finset.univ ℓ (w_y : ℝ) B := by
      refine ⟨fun _ => subset_univ _, ?_, ?_, ?_⟩
      · intro j; exact card_pos.mp (by rw [hB_card j]; omega)
      · intro i j hij
        exact Disjoint.mono ((hB_sub i).trans (hD'_sub i)) ((hB_sub j).trans (hD'_sub j))
          (hA'_disj i j hij)
      · intro j; rw [hB_card j]
    refine ⟨B, ⟨hB_block, ?_⟩, fun j => ⟨hB_card j, hB_anti j⟩⟩
    intro i j hij
    by_cases hadj : J.Adj i j
    · exact Or.inl (isCompletePair_mono (hB_sub i) (hB_sub j) (hD'_comp i j hadj))
    · right
      have hnadj_symm : ¬J.Adj j i := fun h => hadj (J.symm h)
      have hdeg_dir : ∀ (p q : Fin ℓ), p ≠ q → ¬J.Adj p q →
          IsXSparseTo G (B p) (B q) (y ^ (3 * a)) := by
        intro p q hpq hnpq u hu
        have hu_A' : u ∈ A' p := hD'_sub p (hB_sub p hu)
        have hsub : neighborFinsetIn G u (B q) ⊆ neighborFinsetIn G u (A' q) :=
          neighborFinsetIn_mono' G u ((hB_sub q).trans (hD'_sub q))
        rw [hB_card q]
        exact (by exact_mod_cast card_le_card hsub :
          ((neighborFinsetIn G u (B q)).card : ℝ) ≤
            ((neighborFinsetIn G u (A' q)).card : ℝ)).trans (hA'_nonedge_deg p q hpq hnpq u hu_A')
      exact ⟨hdeg_dir j i hij.symm hnadj_symm, hdeg_dir i j hij hadj⟩
  · left
    push_neg at hall_anti
    obtain ⟨j₀, hj₀⟩ := hall_anti
    have hD'_ne : (D' j₀).Nonempty := by
      rw [← card_pos]
      have : (0 : ℝ) < ((D' j₀).card : ℝ) := lt_of_lt_of_le (by positivity) (hD'_card j₀)
      exact_mod_cast this
    rcases anticonnected_component_or_complete_blockade G (D' j₀) ℓ hD'_ne hℓ2 with
      ⟨C, hC_sub, hC_ne, hC_anti, _, hC_card⟩ | ⟨B_comp, hB_comp⟩
    · exact False.elim (not_le.mpr (hj₀ C hC_sub hC_ne hC_anti) hC_card)
    · -- Complete (ℓ, |D'_j₀| / ℓ^2)-blockade in D'_j₀ -> equalize blocks to w_y -> union is (1/ℓ)-co-sparse
      have hw_le_comp : ∀ p : Fin ℓ, w_y ≤ (B_comp p).card := by
        intro p
        have h1 : (w_y : ℝ) ≤ ((D' j₀).card : ℝ) / (ℓ : ℝ) ^ 2 := by
          rw [le_div_iff₀ (by positivity)]
          have hDj := hD'_card j₀
          nlinarith [show (0 : ℝ) ≤ (w_y : ℝ) * (ℓ : ℝ) ^ 2 by positivity]
        exact_mod_cast h1.trans (hB_comp.1.width_ge p)
      let X (p : Fin ℓ) : Finset V_type := (exists_subset_card_eq (hw_le_comp p)).choose
      have hX_sub : ∀ p, X p ⊆ B_comp p := fun p => (exists_subset_card_eq (hw_le_comp p)).choose_spec.1
      have hX_card : ∀ p, (X p).card = w_y := fun p => (exists_subset_card_eq (hw_le_comp p)).choose_spec.2
      have hX_disj : ∀ p q, p ≠ q → Disjoint (X p) (X q) :=
        fun p q hpq => Disjoint.mono (hX_sub p) (hX_sub q) (hB_comp.1.pairwise_disjoint p q hpq)
      let U := (Finset.univ : Finset (Fin ℓ)).biUnion X
      have hU_card : U.card = ℓ * w_y := by
        rw [card_biUnion (fun p _ q _ hpq => hX_disj p q hpq)]
        calc ∑ p : Fin ℓ, (X p).card
          _ = ∑ _p : Fin ℓ, w_y := sum_congr rfl (fun p _ => hX_card p)
          _ = ℓ * w_y := by rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
      have hw_le_U : (w_y : ℝ) ≤ (U.card : ℝ) := by
        rw [hU_card]
        push_cast
        have : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast (by omega : 1 ≤ ℓ)
        nlinarith [show (0 : ℝ) ≤ (w_y : ℝ) by positivity]
      refine ⟨U, Or.inr ?_, hw_le_U⟩
      intro u hu
      obtain ⟨p, _, hup⟩ := mem_biUnion.mp hu
      have hneigh_sub : neighborFinsetIn Gᶜ u U ⊆ X p := by
        intro v hv
        rw [mem_neighborFinsetIn', SimpleGraph.compl_adj] at hv
        obtain ⟨q, _, hvq⟩ := mem_biUnion.mp hv.1
        by_cases hpq : p = q
        · exact hpq ▸ hvq
        · exact False.elim (hv.2.2 (hB_comp.2 p q hpq u (hX_sub p hup) v (hX_sub q hvq)))
      have hdeg_le : ((neighborFinsetIn Gᶜ u U).card : ℝ) ≤ (w_y : ℝ) := by
        rw [← hX_card p]
        exact_mod_cast card_le_card hneigh_sub
      have h1_le_2y2_ℓ : (1 : ℝ) ≤ 2 * y ^ 2 * (ℓ : ℝ) := by
        have hya_le_y2 : y ^ a ≤ y ^ 2 := pow_le_pow_of_le_one hy0.le hy_le1 (by omega)
        have h1_le_y2_ℓ : 1 ≤ y ^ 2 * (ℓ : ℝ) := by
          have := mul_le_mul_of_nonneg_left hℓ_ge_inv (by positivity : 0 ≤ y ^ a)
          rw [mul_inv_cancel₀ (by positivity)] at this
          exact this.trans (mul_le_mul_of_nonneg_right hya_le_y2 (by positivity))
        nlinarith [show (0 : ℝ) ≤ y ^ 2 * (ℓ : ℝ) by positivity]
      rw [hU_card]
      push_cast
      calc ((neighborFinsetIn Gᶜ u U).card : ℝ)
        _ ≤ 1 * (w_y : ℝ) := by linarith
        _ ≤ (2 * y ^ 2 * (ℓ : ℝ)) * (w_y : ℝ) :=
          mul_le_mul_of_nonneg_right h1_le_2y2_ℓ (Nat.cast_nonneg _)
        _ = 2 * y ^ 2 * ((ℓ : ℝ) * (w_y : ℝ)) := by ring

/--
**Complete Step 1 of Lemma 7(2) (`stage2_gn1_viral_purification`, `main.tex` lines 350–383)**:
Combining Sub-steps 1.1a (`step1a_symm_equal_size_presampling`), 1.1b (`step1b_symm_markov_pruning`),
1.2–1.3 (`step1c_viral_purification_to_complete`), and 1.4 (`step1d_anticonnected_pruning`)
to purify any `(GN1)` blockade at coupled sparsity $x_{\mathrm{sp}} = \varepsilon_{\mathrm{GN}}^{3 c_2}$
into either **(R2)** or an equal-sized anticonnected complete-or-$y^{3a}$-sparse $(\ell, w_y)$-blockade.
-/
theorem stage2_gn1_viral_purification
    {V_type : Type} [Fintype V_type] [DecidableEq V_type]
    {W₁ W₂ : Type*} [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]
    (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂)
    (v₀ u₀ : W₁) (hu₀_ne : u₀ ≠ v₀)
    (hleaf : ∀ w : W₁, H₁.Adj v₀ w ↔ w = u₀)
    (hh : 3 ≤ Fintype.card W₁)
    {d' : ℝ} (hd' : 0 < d')
    (hviral : ∀ (U_type : Type) [Fintype U_type] [DecidableEq U_type]
      (F_G : SimpleGraph U_type) (ε : ℝ),
      0 < ε → ε < 1 / 2 →
      (indCopyCount (H₁.comap (Subtype.val : {w : W₁ // w ≠ v₀} → W₁))ᶜ F_G : ℝ) ≤
        (ε ^ d' * (Fintype.card U_type : ℝ)) ^ (Fintype.card {w : W₁ // w ≠ v₀}) →
      (indCopyCount H₂ᶜ F_G : ℝ) ≤
        (ε ^ d' * (Fintype.card U_type : ℝ)) ^ (Fintype.card W₂) →
      ∃ S : Finset U_type, IsEpsRestrictedOn F_G S ε ∧
        ε ^ d' * (Fintype.card U_type : ℝ) ≤ (S.card : ℝ))
    (G : SimpleGraph V_type) (hG₁ : IsInducedSubgraphFree G H₁ᶜ) (hG₂ : IsInducedSubgraphFree G H₂ᶜ)
    {y c₂ m₁ : ℝ} {a w_y : ℕ}
    (hy0 : 0 < y) (hy120 : y ≤ (2 : ℝ) ^ (-120 : ℝ))
    (hc₂ : 4 ≤ c₂) (ha20 : 20 ≤ a)
    (ha_4h : 4 * Fintype.card W₁ ≤ a)
    (ha_dh : 4 * d' * (Fintype.card W₁ : ℝ) + 10 ≤ (a : ℝ))
    (hw_y : 1 ≤ w_y)
    (hm₁_ge : ((4 * ⌈y ^ (-(4 * d' * (Fintype.card W₁ : ℝ) + 2))⌉₊ *
      ⌈(y ^ a)⁻¹⌉₊ ^ 2 * w_y : ℕ) : ℝ) ≤ m₁)
    (A : Fin ⌈(y ^ a)⁻¹⌉₊ → Finset V_type)
    (hA : IsWeaklySparseOrCoSparseBlockadeIn G Finset.univ ⌈(y ^ a)⁻¹⌉₊ m₁ ((y ^ a) ^ (3 * c₂)) A) :
    let ℓ := ⌈(y ^ a)⁻¹⌉₊
    (∃ U : Finset V_type, IsEpsRestrictedOn G U (2 * y ^ 2) ∧ (w_y : ℝ) ≤ (U.card : ℝ)) ∨
    (∃ B : Fin ℓ → Finset V_type,
      IsCompleteOrXSparseBlockadeIn G Finset.univ ℓ (w_y : ℝ) (y ^ (3 * a)) B ∧
      (∀ i : Fin ℓ, (B i).card = w_y ∧ IsAnticonnected G (B i))) := by
  classical
  intro ℓ
  let h := Fintype.card W₁
  let ε_GN := y ^ a
  let x_sp := ε_GN ^ (3 * c₂)
  let M_ceil := ⌈y ^ (-(4 * d' * (h : ℝ) + 2))⌉₊
  let W_mid := 2 * M_ceil * ℓ ^ 2 * w_y
  let W₀ := 2 * W_mid
  have hW₀_eq : W₀ = 4 * M_ceil * ℓ ^ 2 * w_y := by dsimp [W₀, W_mid]; ring
  have hℓ_pos : 1 ≤ ℓ := Nat.ceil_pos.mpr (by positivity)
  have hM_pos : 1 ≤ M_ceil := Nat.ceil_pos.mpr (by positivity)
  have hW_mid_pos : 1 ≤ W_mid :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos zero_lt_two hM_pos) (pow_pos hℓ_pos 2)) hw_y
  have hW₀_pos : 1 ≤ W₀ := Nat.mul_pos zero_lt_two hW_mid_pos
  have hx_sp_pos : 0 < x_sp := by dsimp [x_sp, ε_GN]; positivity
  let J := canonicalSymmPatternGraph G x_sp A
  let H_pair (i j : Fin ℓ) : SimpleGraph V_type := if J.Adj i j then Gᶜ else G
  have hH_symm : ∀ i j, H_pair i j = H_pair j i := by
    intro i j; dsimp [H_pair]; rw [J.adj_comm]
  have hA_card : ∀ i : Fin ℓ, W₀ ≤ (A i).card := by
    intro i
    have hge : (W₀ : ℝ) ≤ ((A i).card : ℝ) := by
      rw [hW₀_eq]
      exact hm₁_ge.trans (hA.1.width_ge i)
    exact_mod_cast hge
  have hA_pairs : ∀ i j : Fin ℓ, i ≠ j →
      (crossEdgeCount (H_pair i j) (A i) (A j) : ℝ) ≤ x_sp * ((A i).card : ℝ) * ((A j).card : ℝ) := by
    intro i j hij
    have hcan := symmPairWrongCount_canonical_le hA hij
    unfold symmPairWrongCount at hcan
    rw [if_pos hij] at hcan
    by_cases hadj : J.Adj i j
    · dsimp [H_pair, J] at hadj ⊢
      rw [if_pos hadj] at hcan ⊢
      exact hcan
    · dsimp [H_pair, J] at hadj ⊢
      rw [if_neg hadj] at hcan ⊢
      exact hcan
  obtain ⟨A'', hA''_sub, hA''_card, hA''_pairs⟩ :=
    step1a_symm_equal_size_presampling ℓ W₀ x_sp hℓ_pos hW₀_pos hx_sp_pos H_pair hH_symm A hA_card hA_pairs
  obtain ⟨A', hA'_sub, hA'_card, hA'_deg⟩ :=
    step1b_symm_markov_pruning ℓ W_mid x_sp hℓ_pos hW_mid_pos hx_sp_pos H_pair A'' hA''_card hA''_pairs
  have hA'_disj : ∀ i j : Fin ℓ, i ≠ j → Disjoint (A' i) (A' j) :=
    fun i j hij => Disjoint.mono ((hA'_sub i).trans (hA''_sub i)) ((hA'_sub j).trans (hA''_sub j))
      (hA.1.pairwise_disjoint i j hij)
  rcases step1c_viral_purification_to_complete H₁ H₂ v₀ u₀ hu₀_ne hleaf hh hd' hviral
      G hG₁ hG₂ hy0 hy120 hc₂ ha20 ha_4h ha_dh hw_y J A' hA'_disj hA'_card hA'_deg with
    hR2 | ⟨D', hD'_sub, hD'_card, hD'_comp⟩
  · exact Or.inl hR2
  · have hA'_nonedge_deg : ∀ i j : Fin ℓ, i ≠ j → ¬J.Adj i j → ∀ u ∈ A' i,
        ((neighborFinsetIn G u (A' j)).card : ℝ) ≤ y ^ (3 * a) * (w_y : ℝ) := by
      intro i j hij hnadj u hu
      have hdeg := hA'_deg i j hij u hu
      dsimp [H_pair] at hdeg
      rw [if_neg hnadj] at hdeg
      have hscale := step1c_delta_wrong_le hy0 hy120 hd' hc₂ hh ha20 ha_4h ha_dh
      have h1 : 4 * (ℓ : ℝ) ^ 3 * x_sp * (W_mid : ℝ) ≤
          ((ℓ : ℝ) * (h : ℝ) * (8 * (ℓ : ℝ) ^ 5 * x_sp * (M_ceil : ℝ))) * (w_y : ℝ) := by
        dsimp [W_mid]
        push_cast
        have hℓ_ge1 : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ_pos
        have hh_ge1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast (by omega : 1 ≤ h)
        have hℓ3_le_ℓ6 : (ℓ : ℝ) ^ 3 ≤ (ℓ : ℝ) * (ℓ : ℝ) ^ 5 := by
          calc (ℓ : ℝ) ^ 3 = (ℓ : ℝ) ^ 3 * 1 := (mul_one _).symm
            _ ≤ (ℓ : ℝ) ^ 3 * (ℓ : ℝ) ^ 3 :=
              mul_le_mul_of_nonneg_left (one_le_pow₀ hℓ_ge1) (by positivity)
            _ = (ℓ : ℝ) * (ℓ : ℝ) ^ 5 := by ring
        have hnonneg : 0 ≤ x_sp * (M_ceil : ℝ) * (w_y : ℝ) := by dsimp [x_sp, ε_GN]; positivity
        calc 4 * (ℓ : ℝ) ^ 3 * x_sp * (2 * (M_ceil : ℝ) * (ℓ : ℝ) ^ 2 * (w_y : ℝ))
          _ = 8 * (ℓ : ℝ) ^ 5 * (x_sp * (M_ceil : ℝ) * (w_y : ℝ)) := by ring
          _ ≤ 8 * ((ℓ : ℝ) * (h : ℝ) * (ℓ : ℝ) ^ 5) * (x_sp * (M_ceil : ℝ) * (w_y : ℝ)) := by
            refine mul_le_mul_of_nonneg_right ?_ hnonneg
            have h1_le_ℓh : (1 : ℝ) ≤ (ℓ : ℝ) * (h : ℝ) := by nlinarith
            nlinarith [show (0 : ℝ) ≤ (ℓ : ℝ) ^ 5 by positivity]
          _ = ((ℓ : ℝ) * (h : ℝ) * (8 * (ℓ : ℝ) ^ 5 * x_sp * (M_ceil : ℝ))) * (w_y : ℝ) := by ring
      exact hdeg.trans (h1.trans (mul_le_mul_of_nonneg_right hscale (Nat.cast_nonneg _)))
    exact step1d_anticonnected_pruning G hy0 hy120 ha20 hw_y J A' D'
      hA'_disj hD'_sub hD'_card hD'_comp hA'_nonedge_deg

/-!
### Section 6C: Steps 2 & 3 of Lemma 7(2) — Pure Cograph Blockade Termination & Master Stage-2 Reduction
(`cograph_stage2_reduction`, `master_stage2_pair_eh_of_coupled_gen_nice_and_wonderful`, and
`master_stage2_eh_of_coupled_gen_nice_and_wonderful`, `main.tex` lines 384–412)
-/

/--
Every $100\%$ pairwise-pure blockade $B$ has $0$ wrong pairs relative to its `purePatternGraph G B`.
-/
theorem symmPairWrongCount_purePatternGraph_eq_zero {G : SimpleGraph V} {S : Finset V}
    {k : ℕ} {w : ℝ} {B : Fin k → Finset V}
    (hB : IsPureBlockadeIn G S k w B) (p q : Fin k) :
    symmPairWrongCount G (purePatternGraph G B) B p q = 0 := by
  classical
  unfold symmPairWrongCount
  by_cases hpq : p = q
  · simp [hpq]
  · rw [if_pos hpq]
    by_cases hadj : (purePatternGraph G B).Adj p q
    · rw [if_pos hadj]
      have hcomp : IsCompletePair G (B p) (B q) := hadj.2
      unfold crossEdgeCount
      rw [sum_eq_zero_iff]
      intro u hu
      rw [card_eq_zero, eq_empty_iff_forall_notMem]
      intro v hv
      rw [mem_neighborFinsetIn', SimpleGraph.compl_adj] at hv
      exact hv.2.2 (hcomp u hu v hv.1)
    · rw [if_neg hadj]
      have hanti : IsAnticompletePair G (B p) (B q) := by
        rcases hB.2 p q hpq with hcomp | hanti
        · exact False.elim (hadj ⟨hpq, hcomp⟩)
        · exact hanti
      unfold crossEdgeCount
      rw [sum_eq_zero_iff]
      intro u hu
      rw [card_eq_zero, eq_empty_iff_forall_notMem]
      intro v hv
      rw [mem_neighborFinsetIn'] at hv
      exact hanti u hu v hv.1 hv.2

/--
**Seinsche Pure-Cograph $\kappa$-Lower Bound (`kappa_ge_of_isPureCographBlockadeIn`, `main.tex` line 407)**:
If $B : \text{Fin } k \to \text{Finset } V$ is a $100\%$ pairwise-pure cograph $(k, w)$-blockade in $G$
(`IsPureCographBlockadeIn G F k w B`) and $(r - 1)^2 < k$ ($r \ge 1$), then $\kappa(G) \ge r$.
-/
theorem kappa_ge_of_isPureCographBlockadeIn {G : SimpleGraph V} {F : Finset V}
    {k : ℕ} {w : ℝ} {B : Fin k → Finset V} (r : ℕ) (hr : 1 ≤ r) (hk : (r - 1) ^ 2 < k)
    (hB : IsPureCographBlockadeIn G F k w B) :
    r ≤ kappa G := by
  classical
  have hk_card : (r - 1) ^ 2 < Fintype.card (Fin k) := by rwa [Fintype.card_fin]
  obtain ⟨R, hR_card, hR_hom⟩ :=
    seinsche_exists_clique_or_indep_card_eq (purePatternGraph G B) hB.2 r hr hk_card
  let f : Fin k → V := fun i => (hB.1.1.nonempty_blocks i).choose
  have hf_mem : ∀ i : Fin k, f i ∈ B i := fun i => (hB.1.1.nonempty_blocks i).choose_spec
  have hf_inj : Function.Injective f := by
    intro i j hij
    by_contra hne
    exact Finset.disjoint_left.mp (hB.1.1.pairwise_disjoint i j hne) (hf_mem i) (hij ▸ hf_mem j)
  let S := R.image f
  have hS_card : S.card = r := by
    rw [card_image_of_injective R hf_inj, hR_card]
  rcases hR_hom with hcl | hind
  · -- R is a clique in purePatternGraph G B -> S is a clique in G
    have hS_clique : G.IsClique (S : Set V) := by
      intro u hu v hv huv
      rcases mem_image.mp hu with ⟨i, hi, rfl⟩
      rcases mem_image.mp hv with ⟨j, hj, rfl⟩
      have hij : i ≠ j := fun h => huv (congrArg f h)
      exact (hcl hi hj hij).2 (f i) (hf_mem i) (f j) (hf_mem j)
    have hle : r ≤ G.cliqueNum := hS_card ▸ hS_clique.card_le_cliqueNum
    exact hle.trans (cliqueNum_le_kappa G)
  · -- R is an independent set in purePatternGraph G B -> S is a clique in Gᶜ
    have hS_indep : Gᶜ.IsClique (S : Set V) := by
      intro u hu v hv huv
      rcases mem_image.mp hu with ⟨i, hi, rfl⟩
      rcases mem_image.mp hv with ⟨j, hj, rfl⟩
      have hij : i ≠ j := fun h => huv (congrArg f h)
      have hnadj : ¬(purePatternGraph G B).Adj i j := (hind hi hj hij).2
      have hanti : IsAnticompletePair G (B i) (B j) := by
        rcases hB.1.2 i j hij with hcomp | hanti
        · exact False.elim (hnadj ⟨hij, hcomp⟩)
        · exact hanti
      exact ⟨huv, hanti (f i) (hf_mem i) (f j) (hf_mem j)⟩
    have hle : r ≤ G.indepNum := by
      rw [← cliqueNum_compl]
      exact hS_card ▸ hS_indep.card_le_cliqueNum
    exact hle.trans (indepNum_le_kappa G)

private theorem cograph_stage2_scale_bounds {C₁ N : ℝ}
    (hC₁ : 1 ≤ C₁) (hN_ge : (2 : ℝ) ^ (84 * C₁ ^ 2) ≤ N) :
    let ε := (1 / 2 : ℝ) * N ^ (-1 / (21 * C₁ ^ 2))
    let x := N ^ (-1 / (3 * C₁))
    (2 * ε)⁻¹ ≤ ε ^ (5 * C₁) * N ∧
    4 * ε ^ (-(5 * C₁)) ≤ N ∧
    N ^ (1 / 3 : ℝ) ≤ x ^ C₁ * ((1 / 2 : ℝ) * ε ^ (2 * C₁) * N) := by
  intro ε x
  have hC₁_pos : 0 < C₁ := by linarith
  have hC₁_ne : C₁ ≠ 0 := hC₁_pos.ne'
  have hN_pos : 0 < N := lt_of_lt_of_le (by positivity) hN_ge
  have hN_ge1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ (2 : ℝ) ^ (84 * C₁ ^ 2) := Real.one_le_rpow (by norm_num) (by positivity)
    linarith
  have hN_pow_21 : (16 : ℝ) ≤ N ^ (1 / (21 * C₁ ^ 2)) := by
    have h1 : (2 : ℝ) ^ (4 : ℝ) = ((2 : ℝ) ^ (84 * C₁ ^ 2)) ^ (1 / (21 * C₁ ^ 2)) := by
      rw [← Real.rpow_mul two_pos.le]
      congr 1; field_simp; ring
    have h2 : ((2 : ℝ) ^ (84 * C₁ ^ 2)) ^ (1 / (21 * C₁ ^ 2)) ≤ N ^ (1 / (21 * C₁ ^ 2)) :=
      Real.rpow_le_rpow (by positivity) hN_ge (by positivity)
    have h3 : (2 : ℝ) ^ (4 : ℝ) = 16 := by norm_num
    linarith
  have hN_pow_84 : (2 : ℝ) ≤ N ^ (1 / (84 * C₁ ^ 2)) := by
    have h1 : (2 : ℝ) = ((2 : ℝ) ^ (84 * C₁ ^ 2)) ^ (1 / (84 * C₁ ^ 2)) := by
      rw [← Real.rpow_mul two_pos.le, show (84 * C₁ ^ 2) * (1 / (84 * C₁ ^ 2)) = 1 by field_simp,
        Real.rpow_one]
    rw [h1]
    exact Real.rpow_le_rpow (by positivity) hN_ge (by positivity)
  have hε0 : 0 < ε := by dsimp [ε]; positivity
  have h2ε_inv_eq : (2 * ε)⁻¹ = N ^ (1 / (21 * C₁ ^ 2)) := by
    dsimp [ε]
    rw [← mul_assoc, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_mul, ← Real.rpow_neg hN_pos.le]
    congr 1; ring
  have h2_5C₁_le : (2 : ℝ) ^ (5 * C₁) ≤ N ^ (5 / (84 * C₁)) := by
    calc (2 : ℝ) ^ (5 * C₁)
      _ ≤ (N ^ (1 / (84 * C₁ ^ 2))) ^ (5 * C₁) :=
        Real.rpow_le_rpow zero_le_two hN_pow_84 (by positivity)
      _ = N ^ (5 / (84 * C₁)) := by
        rw [← Real.rpow_mul hN_pos.le]
        congr 1; field_simp
  have hε_eq : ε = (2 : ℝ) ^ (-1 : ℝ) * N ^ (-1 / (21 * C₁ ^ 2)) := by
    dsimp [ε]; congr 1; norm_num
  have h2ε_inv_le_5C₁ : (2 * ε)⁻¹ ≤ ε ^ (5 * C₁) * N := by
    have hε_5C₁ : ε ^ (5 * C₁) = (2 : ℝ) ^ (-(5 * C₁)) * N ^ (-5 / (21 * C₁)) := by
      rw [hε_eq, Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_mul two_pos.le, ← Real.rpow_mul hN_pos.le]
      have he1 : (-1 : ℝ) * (5 * C₁) = -(5 * C₁) := by ring
      have he2 : (-1 / (21 * C₁ ^ 2)) * (5 * C₁) = -5 / (21 * C₁) := by field_simp
      rw [he1, he2]
    rw [h2ε_inv_eq, hε_5C₁, mul_assoc, ← Real.rpow_add_one hN_pos.ne']
    have h2_inv : N ^ (-5 / (84 * C₁)) ≤ (2 : ℝ) ^ (-(5 * C₁)) := by
      rw [show (-5 / (84 * C₁) : ℝ) = -(5 / (84 * C₁)) by ring,
        Real.rpow_neg hN_pos.le, Real.rpow_neg two_pos.le]
      exact inv_anti₀ (by positivity) h2_5C₁_le
    calc N ^ (1 / (21 * C₁ ^ 2))
      _ ≤ N ^ (-5 / (84 * C₁) + (-5 / (21 * C₁) + 1)) := by
        refine Real.rpow_le_rpow_of_exponent_le hN_ge1 ?_
        have h1 : 1 / (21 * C₁ ^ 2) ≤ 1 / 21 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
        have h2 : 5 / (84 * C₁) ≤ 5 / 84 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
        have h3 : 5 / (21 * C₁) ≤ 5 / 21 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
        have h4 : -5 / (84 * C₁) = -(5 / (84 * C₁)) := by ring
        have h5 : -5 / (21 * C₁) = -(5 / (21 * C₁)) := by ring
        linarith
      _ = N ^ (-5 / (84 * C₁)) * N ^ (-5 / (21 * C₁) + 1) := Real.rpow_add hN_pos _ _
      _ ≤ (2 : ℝ) ^ (-(5 * C₁)) * N ^ (-5 / (21 * C₁) + 1) :=
        mul_le_mul_of_nonneg_right h2_inv (by positivity)
  have hS₀_card_4 : 4 * ε ^ (-(5 * C₁)) ≤ N := by
    have h4_le_2ε : (4 : ℝ) ≤ (2 * ε)⁻¹ := by rw [h2ε_inv_eq]; linarith
    have hmul := mul_le_mul_of_nonneg_right (h4_le_2ε.trans h2ε_inv_le_5C₁)
      (by positivity : 0 ≤ ε ^ (-(5 * C₁)))
    have hcancel : ε ^ (5 * C₁) * N * ε ^ (-(5 * C₁)) = N := by
      calc ε ^ (5 * C₁) * N * ε ^ (-(5 * C₁))
        _ = (ε ^ (5 * C₁) * ε ^ (-(5 * C₁))) * N := by ring
        _ = 1 * N := by rw [← Real.rpow_add hε0]; simp
        _ = N := one_mul N
    rwa [hcancel] at hmul
  have hx_C₁_N : N ^ (1 / 3 : ℝ) ≤ x ^ C₁ * ((1 / 2 : ℝ) * ε ^ (2 * C₁) * N) := by
    have hx_C₁_eq : x ^ C₁ = N ^ (-1 / 3 : ℝ) := by
      dsimp [x]; rw [← Real.rpow_mul hN_pos.le]
      congr 1; field_simp
    have hε_2C₁_ge : N ^ (-1 / 7 : ℝ) ≤ (1 / 2 : ℝ) * ε ^ (2 * C₁) := by
      have hε_2C₁ : (1 / 2 : ℝ) * ε ^ (2 * C₁) =
          (2 : ℝ) ^ (-(2 * C₁ + 1)) * N ^ (-2 / (21 * C₁)) := by
        rw [show (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) by norm_num, hε_eq,
          Real.mul_rpow (by positivity) (by positivity),
          ← Real.rpow_mul two_pos.le, ← Real.rpow_mul hN_pos.le, ← mul_assoc,
          ← Real.rpow_add two_pos]
        have he1 : (-1 : ℝ) + (-1) * (2 * C₁) = -(2 * C₁ + 1) := by ring
        have he2 : (-1 / (21 * C₁ ^ 2)) * (2 * C₁) = -2 / (21 * C₁) := by field_simp
        rw [he1, he2]
      rw [hε_2C₁]
      have h2_pow : N ^ (-(2 * C₁ + 1) / (84 * C₁ ^ 2)) ≤ (2 : ℝ) ^ (-(2 * C₁ + 1)) := by
        rw [show -(2 * C₁ + 1) / (84 * C₁ ^ 2) = -((2 * C₁ + 1) / (84 * C₁ ^ 2)) by ring,
          Real.rpow_neg hN_pos.le, Real.rpow_neg two_pos.le]
        refine inv_anti₀ (by positivity) ?_
        calc (2 : ℝ) ^ (2 * C₁ + 1)
          _ ≤ (N ^ (1 / (84 * C₁ ^ 2))) ^ (2 * C₁ + 1) :=
            Real.rpow_le_rpow zero_le_two hN_pow_84 (by positivity)
          _ = N ^ ((2 * C₁ + 1) / (84 * C₁ ^ 2)) := by
            rw [← Real.rpow_mul hN_pos.le]; congr 1; ring
      calc N ^ (-1 / 7 : ℝ)
        _ ≤ N ^ (-(2 * C₁ + 1) / (84 * C₁ ^ 2) + -2 / (21 * C₁)) := by
          refine Real.rpow_le_rpow_of_exponent_le hN_ge1 ?_
          have h1 : (2 * C₁ + 1) / (84 * C₁ ^ 2) ≤ 3 / 84 := by
            rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
          have h2 : 2 / (21 * C₁) ≤ 2 / 21 := by
            rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
          have h3 : -(2 * C₁ + 1) / (84 * C₁ ^ 2) = -((2 * C₁ + 1) / (84 * C₁ ^ 2)) := by ring
          have h4 : -2 / (21 * C₁) = -(2 / (21 * C₁)) := by ring
          linarith
        _ = N ^ (-(2 * C₁ + 1) / (84 * C₁ ^ 2)) * N ^ (-2 / (21 * C₁)) := Real.rpow_add hN_pos _ _
        _ ≤ (2 : ℝ) ^ (-(2 * C₁ + 1)) * N ^ (-2 / (21 * C₁)) :=
          mul_le_mul_of_nonneg_right h2_pow (by positivity)
    calc N ^ (1 / 3 : ℝ)
      _ ≤ N ^ (-1 / 3 + (-1 / 7 + 1) : ℝ) := Real.rpow_le_rpow_of_exponent_le hN_ge1 (by norm_num)
      _ = N ^ (-1 / 3 : ℝ) * (N ^ (-1 / 7 : ℝ) * N) := by
        rw [Real.rpow_add hN_pos, Real.rpow_add_one hN_pos.ne']
      _ ≤ x ^ C₁ * ((1 / 2 : ℝ) * ε ^ (2 * C₁) * N) := by
        rw [hx_C₁_eq]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right hε_2C₁_ge hN_pos.le
  exact ⟨h2ε_inv_le_5C₁, hS₀_card_4, hx_C₁_N⟩

/--
**Cograph Stage-2 Reduction (`cograph_stage2_reduction`, `main.tex` lines 394–410)**:
Suppose $C_1 \ge 1$ and $0 < C_2 \le 1$, and for every $x \in (0, 1/2)$ and every $F \subseteq S_0$,
either:
- **(i)** $F$ contains an $x$-restricted subset $S \subseteq F$ with $|S| \ge x^{C_1}|F|$,
- **(ii)** $F$ contains a $100\%$ pairwise-pure cograph $(k, |F|/k^{C_1})$-blockade for some $k \ge 2$, or
- **(iii)** $\kappa(G) \ge (x^{C_1}|F|)^{C_2}$.
Then for $q := 84 C_1^2$, $c := C_2 / q$, and $|S_0| \ge 2^q$, we have $\kappa(G) \ge |S_0|^c$.
-/
theorem cograph_stage2_reduction (G : SimpleGraph V) (S₀ : Finset V) (C₁ C₂ : ℝ)
    (hC₁ : 1 ≤ C₁) (hC₂0 : 0 < C₂) (_hC₂1 : C₂ ≤ 1)
    (h_multiscale : ∀ x : ℝ, 0 < x → x < 1 / 2 → ∀ F ⊆ S₀,
      (∃ S ⊆ F, IsEpsRestrictedOn G S x ∧ x ^ C₁ * (F.card : ℝ) ≤ (S.card : ℝ)) ∨
      (∃ k : ℕ, 2 ≤ k ∧ ∃ B : Fin k → Finset V,
        IsPureCographBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ C₁) B) ∨
      (x ^ C₁ * (F.card : ℝ)) ^ C₂ ≤ (kappa G : ℝ)) :
    let q := 84 * C₁ ^ 2
    let c := C₂ / q
    (2 : ℝ) ^ q ≤ (S₀.card : ℝ) → (S₀.card : ℝ) ^ c ≤ (kappa G : ℝ) := by
  classical
  intro q c hS₀_ge
  have hC₁_pos : 0 < C₁ := by linarith
  have hq_ge : 84 ≤ q := by dsimp [q]; nlinarith
  have hq_pos : 0 < q := by linarith
  have hS₀_pos : (0 : ℝ) < (S₀.card : ℝ) := lt_of_lt_of_le (by positivity) hS₀_ge
  have hS₀_ge1 : (1 : ℝ) ≤ (S₀.card : ℝ) := by
    have : (1 : ℝ) ≤ (2 : ℝ) ^ q := Real.one_le_rpow (by norm_num) hq_pos.le
    linarith
  have hN_pow_21 : (16 : ℝ) ≤ (S₀.card : ℝ) ^ (1 / (21 * C₁ ^ 2)) := by
    have h1 : (2 : ℝ) ^ (4 : ℝ) = ((2 : ℝ) ^ q) ^ (1 / (21 * C₁ ^ 2)) := by
      rw [← Real.rpow_mul two_pos.le]
      congr 1; dsimp [q]
      have hne : C₁ ≠ 0 := hC₁_pos.ne'
      field_simp; ring
    have h2 : ((2 : ℝ) ^ q) ^ (1 / (21 * C₁ ^ 2)) ≤ (S₀.card : ℝ) ^ (1 / (21 * C₁ ^ 2)) :=
      Real.rpow_le_rpow (by positivity) hS₀_ge (by positivity)
    have h3 : (2 : ℝ) ^ (4 : ℝ) = 16 := by norm_num
    linarith
  have hN_pow_84 : (2 : ℝ) ≤ (S₀.card : ℝ) ^ (1 / (84 * C₁ ^ 2)) := by
    have h1 : (2 : ℝ) = ((2 : ℝ) ^ q) ^ (1 / (84 * C₁ ^ 2)) := by
      rw [← Real.rpow_mul two_pos.le]
      have hne : C₁ ≠ 0 := hC₁_pos.ne'
      have hq_mul : q * (1 / (84 * C₁ ^ 2)) = 1 := by dsimp [q]; field_simp
      rw [hq_mul, Real.rpow_one]
    rw [h1]
    exact Real.rpow_le_rpow (by positivity) hS₀_ge (by positivity)
  let ε : ℝ := (1 / 2 : ℝ) * (S₀.card : ℝ) ^ (-1 / (21 * C₁ ^ 2))
  let x : ℝ := (S₀.card : ℝ) ^ (-1 / (3 * C₁))
  have hε0 : 0 < ε := by dsimp [ε]; positivity
  have hx0 : 0 < x := by dsimp [x]; positivity
  have h2ε_inv_eq : (2 * ε)⁻¹ = (S₀.card : ℝ) ^ (1 / (21 * C₁ ^ 2)) := by
    dsimp [ε]
    rw [← mul_assoc, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_mul,
      ← Real.rpow_neg hS₀_pos.le]
    congr 1; ring
  have hε8 : ε ≤ 1 / 8 := by
    have h16 : (16 : ℝ) ≤ (2 * ε)⁻¹ := h2ε_inv_eq.symm ▸ hN_pow_21
    have hmul := mul_le_mul_of_nonneg_right h16 (by positivity : 0 ≤ 2 * ε)
    rw [inv_mul_cancel₀ (by positivity)] at hmul
    linarith
  have hx_inv_eq : x⁻¹ = (S₀.card : ℝ) ^ (1 / (3 * C₁)) := by
    dsimp [x]
    rw [← Real.rpow_neg hS₀_pos.le]
    congr 1; ring
  have hx_half : x < 1 / 2 := by
    have h1 : 1 / (21 * C₁ ^ 2) ≤ 1 / (3 * C₁) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    have h16_x : (16 : ℝ) ≤ x⁻¹ := by
      rw [hx_inv_eq]
      exact hN_pow_21.trans (Real.rpow_le_rpow_of_exponent_le hS₀_ge1 h1)
    have hmul := mul_le_mul_of_nonneg_right h16_x hx0.le
    rw [inv_mul_cancel₀ hx0.ne'] at hmul
    linarith
  have hNc_le_4ε_inv : (S₀.card : ℝ) ^ c ≤ (4 * ε)⁻¹ := by
    have h4ε_inv : (4 * ε)⁻¹ = (1 / 2 : ℝ) * (S₀.card : ℝ) ^ (1 / (21 * C₁ ^ 2)) := by
      rw [show 4 * ε = 2 * (2 * ε) by ring, mul_inv, h2ε_inv_eq]
      ring
    rw [h4ε_inv]
    have hc_le_84 : c ≤ 1 / (84 * C₁ ^ 2) := by
      dsimp [c, q]
      exact div_le_div_of_nonneg_right _hC₂1 (by positivity)
    have hNc_le_84 : (S₀.card : ℝ) ^ c ≤ (S₀.card : ℝ) ^ (1 / (84 * C₁ ^ 2)) :=
      Real.rpow_le_rpow_of_exponent_le hS₀_ge1 hc_le_84
    have h84_4 : ((S₀.card : ℝ) ^ (1 / (84 * C₁ ^ 2))) ^ (4 : ℝ) =
        (S₀.card : ℝ) ^ (1 / (21 * C₁ ^ 2)) := by
      rw [← Real.rpow_mul hS₀_pos.le]
      congr 1; have hne : C₁ ≠ 0 := hC₁_pos.ne'; field_simp; ring
    have h2_le_84_cube : (2 : ℝ) ≤ ((S₀.card : ℝ) ^ (1 / (84 * C₁ ^ 2))) ^ (3 : ℝ) := by
      calc (2 : ℝ) ≤ (2 : ℝ) ^ (3 : ℝ) := by norm_num
        _ ≤ ((S₀.card : ℝ) ^ (1 / (84 * C₁ ^ 2))) ^ (3 : ℝ) :=
          Real.rpow_le_rpow zero_le_two hN_pow_84 (by norm_num)
    have h_split : (S₀.card : ℝ) ^ (1 / (21 * C₁ ^ 2)) =
        ((S₀.card : ℝ) ^ (1 / (84 * C₁ ^ 2))) ^ (3 : ℝ) *
        (S₀.card : ℝ) ^ (1 / (84 * C₁ ^ 2)) := by
      rw [← h84_4, show (4 : ℝ) = 3 + 1 by norm_num, Real.rpow_add (by positivity),
        Real.rpow_one]
    rw [h_split]
    have hpos_84 : 0 ≤ (S₀.card : ℝ) ^ (1 / (84 * C₁ ^ 2)) := by positivity
    nlinarith
  obtain ⟨h2ε_inv_le_5C₁, hS₀_card_4, hx_C₁_N⟩ := cograph_stage2_scale_bounds hC₁ hS₀_ge
  -- Case split on whether every F ⊆ S₀ (|F| ≥ (1/2) ε^(2 C₁) |S₀|) has a low-arity pure cograph blockade
  by_cases hall_low : ∀ F ⊆ S₀, (1 / 2 : ℝ) * ε ^ (2 * C₁) * (S₀.card : ℝ) ≤ (F.card : ℝ) →
      ∃ k : ℕ, 2 ≤ k ∧ k < ⌈ε ^ (-2 : ℝ)⌉₊ ∧
        ∃ B : Fin k → Finset V,
          IsPureCographBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ C₁) B
  · -- Apply defective_cograph_refinement (Lemma 4(2)) at x_def = 0
    have hdich : ∀ F ⊆ S₀, (1 / 2 : ℝ) * ε ^ (2 * C₁) * (S₀.card : ℝ) ≤ (F.card : ℝ) →
        (∃ S ⊆ F, IsEpsRestrictedOn G S (2 * ε) ∧ ε ^ (5 * C₁) * (S₀.card : ℝ) ≤ (S.card : ℝ)) ∨
        (∃ (k w₀ : ℕ) (K : SimpleGraph (Fin k)) (B : Fin k → Finset V),
          ⌈ε ^ (-2 : ℝ)⌉₊ ≤ k ∧ 1 ≤ w₀ ∧
          ε ^ (5 * C₁) * (S₀.card : ℝ) ≤ (w₀ : ℝ) ∧
          IsInducedSubgraphFree K (pathGraph 4) ∧
          IsBlockadeIn G F k (w₀ : ℝ) B ∧
          (∀ i : Fin k, (B i).card = w₀) ∧
          (∀ i j : Fin k, i ≠ j →
            (symmPairWrongCount G K B i j : ℝ) ≤
              ((1 / 8 : ℝ) * ε ^ 4) * ((B i).card : ℝ) * ((B j).card : ℝ))) ∨
        (∃ (k : ℕ) (K : SimpleGraph (Fin k)) (B : Fin k → Finset V),
          2 ≤ k ∧ k < ⌈ε ^ (-2 : ℝ)⌉₊ ∧
          IsInducedSubgraphFree K (pathGraph 4) ∧
          IsBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ C₁) B ∧
          (∀ p q : Fin k, p ≠ q →
            (symmPairWrongCount G K B p q : ℝ) ≤ 0 * ((B p).card : ℝ) * ((B q).card : ℝ))) := by
      intro F hFS₀ hF_card
      obtain ⟨k, hk2, hk_lt, B, hB⟩ := hall_low F hFS₀ hF_card
      right; right
      refine ⟨k, purePatternGraph G B, B, hk2, hk_lt, hB.2, hB.1.1, ?_⟩
      intro p q _
      rw [symmPairWrongCount_purePatternGraph_eq_zero hB.1 p q]
      simp
    obtain ⟨S, _, hS_rest, hS_card⟩ :=
      defective_cograph_refinement G S₀ hC₁ hε0 hε8 le_rfl (by positivity) hS₀_card_4 hdich
    have hS_ge_inv : (2 * ε)⁻¹ ≤ (S.card : ℝ) := h2ε_inv_le_5C₁.trans hS_card
    have hkappa_ge : (2 * (2 * ε))⁻¹ ≤ (kappa G : ℝ) :=
      kappa_ge_inv_two_mul_of_isEpsRestrictedOn G S (2 * ε) (by positivity) hS_ge_inv hS_rest
    rw [show 2 * (2 * ε) = 4 * ε by ring] at hkappa_ge
    exact hNc_le_4ε_inv.trans hkappa_ge
  · -- Some F ⊆ S₀ has no low-arity pure cograph blockade -> invoke h_multiscale at x
    push_neg at hall_low
    obtain ⟨F, hFS₀, hF_card, hF_no_low⟩ := hall_low
    have hx_C₁_F : (S₀.card : ℝ) ^ (1 / 3 : ℝ) ≤ x ^ C₁ * (F.card : ℝ) :=
      hx_C₁_N.trans (mul_le_mul_of_nonneg_left hF_card (by positivity))
    rcases h_multiscale x hx0 hx_half F hFS₀ with
      ⟨S, _, hS_rest, hS_card⟩ | ⟨k, hk2, B, hB⟩ | hkappa
    · -- (i) S is x-restricted with |S| ≥ x^C₁ |F| ≥ x⁻¹
      have hx_inv_le : x⁻¹ ≤ (S.card : ℝ) := by
        have h1 : x⁻¹ ≤ (S₀.card : ℝ) ^ (1 / 3 : ℝ) := by
          rw [hx_inv_eq]
          refine Real.rpow_le_rpow_of_exponent_le hS₀_ge1 ?_
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
        exact h1.trans (hx_C₁_F.trans hS_card)
      have hkappa_ge : (2 * x)⁻¹ ≤ (kappa G : ℝ) :=
        kappa_ge_inv_two_mul_of_isEpsRestrictedOn G S x hx0 hx_inv_le hS_rest
      have h4ε_le_2x : (4 * ε)⁻¹ ≤ (2 * x)⁻¹ := by
        rw [show 4 * ε = 2 * (2 * ε) by ring, mul_inv, h2ε_inv_eq, mul_inv, hx_inv_eq]
        have h1 : 1 / (21 * C₁ ^ 2) ≤ 1 / (3 * C₁) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hS₀_ge1 h1) (by positivity)
      exact hNc_le_4ε_inv.trans (h4ε_le_2x.trans hkappa_ge)
    · -- (ii) Pure cograph blockade -> must have k ≥ ⌈ε ^ (-2 : ℝ)⌉₊ -> Seinsche gives kappa G ≥ ⌈ε⁻¹⌉₊
      by_cases hk_lt : k < ⌈ε ^ (-2 : ℝ)⌉₊
      · exact False.elim (hF_no_low k hk2 hk_lt B hB)
      · push_neg at hk_lt
        let r := ⌈ε⁻¹⌉₊
        have hr_pos : 1 ≤ r := Nat.ceil_pos.mpr (inv_pos.mpr hε0)
        have hr_sq_lt : (r - 1) ^ 2 < k := by
          have hr1_lt : ((r - 1 : ℕ) : ℝ) < ε⁻¹ := by
            rw [Nat.cast_sub hr_pos, Nat.cast_one]
            have hceil_lt := Nat.ceil_lt_add_one (inv_nonneg.mpr hε0.le)
            linarith
          have hsq_lt : (((r - 1) ^ 2 : ℕ) : ℝ) < ε ^ (-2 : ℝ) := by
            push_cast
            have hinv_sq : (ε⁻¹) ^ 2 = ε ^ (-2 : ℝ) := by
              rw [inv_pow, ← Real.rpow_natCast ε 2, ← Real.rpow_neg hε0.le]; norm_num
            rw [← hinv_sq]
            exact pow_lt_pow_left₀ hr1_lt (Nat.cast_nonneg _) two_ne_zero
          have hk_ge_real : ε ^ (-2 : ℝ) ≤ (k : ℝ) :=
            (Nat.le_ceil _).trans (by exact_mod_cast hk_lt)
          exact_mod_cast hsq_lt.trans_le hk_ge_real
        have hkappa_r : r ≤ kappa G := kappa_ge_of_isPureCographBlockadeIn r hr_pos hr_sq_lt hB
        have h4ε_le_r : (4 * ε)⁻¹ ≤ (r : ℝ) := by
          calc (4 * ε)⁻¹ ≤ ε⁻¹ := inv_anti₀ hε0 (by linarith)
            _ ≤ (r : ℝ) := Nat.le_ceil _
        exact hNc_le_4ε_inv.trans (h4ε_le_r.trans (by exact_mod_cast hkappa_r))
    · -- (iii) (x^C₁ |F|)^C₂ ≤ kappa G
      have hNc_le : (S₀.card : ℝ) ^ c ≤ (x ^ C₁ * (F.card : ℝ)) ^ C₂ := by
        calc (S₀.card : ℝ) ^ c
          _ ≤ (S₀.card : ℝ) ^ (C₂ * (1 / 3 : ℝ)) := by
            dsimp [c, q]
            refine Real.rpow_le_rpow_of_exponent_le hS₀_ge1 ?_
            rw [div_le_iff₀ (by positivity)]
            nlinarith
          _ = ((S₀.card : ℝ) ^ (1 / 3 : ℝ)) ^ C₂ := by
            rw [← Real.rpow_mul hS₀_pos.le, mul_comm]
          _ ≤ (x ^ C₁ * (F.card : ℝ)) ^ C₂ :=
            Real.rpow_le_rpow (by positivity) hx_C₁_F hC₂0.le
      exact hNc_le.trans hkappa

/--
Extending a large-cardinality Erdős–Hajnal bound (`|V| ≥ 2^q ⟹ |V|^{C₂/q} ≤ κ(G)`, where $q \ge 1$
and $0 < C_2 \le 1$) to all finite graphs (`HasPairErdosHajnalProp H₁ᶜ H₂ᶜ`, `main.tex` line 394):
for $1 \le |V| \le 2^q$, $|V|^{C_2/q} \le 2^{C_2} \le 2$, while $\kappa(G) = 1 = |V|^{C_2/q}$ when
$|V| = 1$ and $\kappa(G) \ge 2$ when $|V| \ge 2$.
-/
theorem hasPairErdosHajnalProp_of_large_card {W₁ W₂ : Type*}
    (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂) {q C₂ : ℝ}
    (hq : 1 ≤ q) (hC₂0 : 0 < C₂) (hC₂1 : C₂ ≤ 1)
    (h_large : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      IsInducedSubgraphFree G H₁ᶜ → IsInducedSubgraphFree G H₂ᶜ →
      (2 : ℝ) ^ q ≤ (Fintype.card V : ℝ) →
        (Fintype.card V : ℝ) ^ (C₂ / q) ≤ (kappa G : ℝ)) :
    HasPairErdosHajnalProp H₁ᶜ H₂ᶜ := by
  let c := C₂ / q
  have hc_pos : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc_pos, ?_⟩
  intro V _ _ G hG₁ hG₂
  by_cases hlarge : (2 : ℝ) ^ q ≤ (Fintype.card V : ℝ)
  · exact h_large V G hG₁ hG₂ hlarge
  · push_neg at hlarge
    rcases (by omega : Fintype.card V = 0 ∨ Fintype.card V = 1 ∨ 2 ≤ Fintype.card V) with
      h0 | h1 | h2
    · rw [h0, Nat.cast_zero, Real.zero_rpow hc_pos.ne']
      exact Nat.cast_nonneg _
    · rw [h1, Nat.cast_one, Real.one_rpow]
      haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
      exact_mod_cast kappa_pos_of_nonempty G
    · have hkappa2 : (2 : ℝ) ≤ (kappa G : ℝ) := by
        exact_mod_cast kappa_ge_two_of_two_le_card G h2
      have hpow_le2 : (Fintype.card V : ℝ) ^ c ≤ 2 := by
        calc (Fintype.card V : ℝ) ^ c
          _ ≤ ((2 : ℝ) ^ q) ^ c := Real.rpow_le_rpow (Nat.cast_nonneg _) hlarge.le hc_pos.le
          _ = (2 : ℝ) ^ C₂ := by
            dsimp [c]
            rw [← Real.rpow_mul two_pos.le, mul_div_cancel₀ _ (by linarith)]
          _ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le one_le_two hC₂1
          _ = 2 := Real.rpow_one 2
      exact hpow_le2.trans hkappa2

private theorem two_rpow_neg_K0_le_c0 {c₀ : ℝ} (hc₀_pos : 0 < c₀) :
    let K₀ := (⌈Real.log (1 / c₀) / Real.log 2⌉₊ : ℝ) + 1
    (2 : ℝ) ^ (-K₀) ≤ c₀ := by
  intro K₀
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hdiv : Real.log (1 / c₀) / Real.log 2 ≤ K₀ := by
    dsimp [K₀]
    linarith [Nat.le_ceil (Real.log (1 / c₀) / Real.log 2)]
  have hmul : Real.log (1 / c₀) ≤ K₀ * Real.log 2 := (div_le_iff₀ hlog2).mp hdiv
  rw [one_div, Real.log_inv] at hmul
  have hlog_le : Real.log ((2 : ℝ) ^ (-K₀)) ≤ Real.log c₀ := by
    rw [Real.log_rpow two_pos]
    linarith
  exact (Real.log_le_log_iff (by positivity) hc₀_pos).mp hlog_le

private theorem two_mul_y_sq_le_lam_b1 {c₀ lam : ℝ}
    (hc₀_pos : 0 < c₀) (hc₀_120 : c₀ ≤ (2 : ℝ) ^ (-120 : ℝ))
    (hlam0 : 0 ≤ lam) (hlam_le : lam ≤ c₀ ^ 4) :
    2 * (lam / c₀) ^ 2 ≤ lam ^ (11 / 10 : ℝ) := by
  rcases eq_or_lt_of_le hlam0 with rfl | hlam_pos
  · simp [Real.zero_rpow (by norm_num : (11 / 10 : ℝ) ≠ 0)]
  · have hc₀_le1 : c₀ ≤ 1 := hc₀_120.trans (by norm_num)
    have hlam_eq : (lam / c₀) ^ 2 = c₀ ^ (-2 : ℝ) * (lam ^ (9 / 10 : ℝ) * lam ^ (11 / 10 : ℝ)) := by
      rw [div_pow, div_eq_inv_mul, ← Real.rpow_natCast c₀ 2, ← Real.rpow_neg hc₀_pos.le,
        ← Real.rpow_add hlam_pos, show (9 / 10 : ℝ) + 11 / 10 = ((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
      push_cast; ring
    have hlam_9_10 : lam ^ (9 / 10 : ℝ) ≤ c₀ ^ (18 / 5 : ℝ) := by
      calc lam ^ (9 / 10 : ℝ)
        _ ≤ (c₀ ^ 4) ^ (9 / 10 : ℝ) := Real.rpow_le_rpow hlam0 hlam_le (by norm_num)
        _ = c₀ ^ (18 / 5 : ℝ) := by
          rw [← Real.rpow_natCast c₀ 4, ← Real.rpow_mul hc₀_pos.le]
          congr 1; norm_num
    have h2_c₀ : 2 * (c₀ ^ (-2 : ℝ) * lam ^ (9 / 10 : ℝ)) ≤ 1 := by
      calc 2 * (c₀ ^ (-2 : ℝ) * lam ^ (9 / 10 : ℝ))
        _ ≤ 2 * (c₀ ^ (-2 : ℝ) * c₀ ^ (18 / 5 : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ zero_le_two
          exact mul_le_mul_of_nonneg_left hlam_9_10 (by positivity)
        _ = 2 * c₀ ^ (8 / 5 : ℝ) := by rw [← Real.rpow_add hc₀_pos]; congr 2; norm_num
        _ ≤ 2 * c₀ ^ (1 : ℝ) := by
          refine mul_le_mul_of_nonneg_left ?_ zero_le_two
          exact Real.rpow_le_rpow_of_exponent_ge hc₀_pos hc₀_le1 (by norm_num)
        _ = 2 * c₀ := by rw [Real.rpow_one]
        _ ≤ 1 := by
          have : (2 : ℝ) ^ (-120 : ℝ) ≤ 1 / 2 := by norm_num
          linarith [hc₀_120.trans this]
    calc 2 * (lam / c₀) ^ 2
      _ = (2 * (c₀ ^ (-2 : ℝ) * lam ^ (9 / 10 : ℝ))) * lam ^ (11 / 10 : ℝ) := by
        rw [hlam_eq]; ring
      _ ≤ 1 * lam ^ (11 / 10 : ℝ) := mul_le_mul_of_nonneg_right h2_c₀ (by positivity)
      _ = lam ^ (11 / 10 : ℝ) := one_mul _

private theorem stage2_gn1_m1_ge_W0 {y c₀ c₁ d' a_peel : ℝ} {a h : ℕ} {F_t F' : Finset V}
    (hy0 : 0 < y) (hy_c₀ : y ≤ c₀) (hc₀_120 : c₀ ≤ (2 : ℝ) ^ (-120 : ℝ))
    (_hc₁ : 0 < c₁) (hd' : 0 < d') (_ha20 : 20 ≤ a)
    (ha_peel : (a : ℝ) * c₁ + 4 * d' * (h : ℝ) + 2 * (a : ℝ) + 10 ≤ a_peel)
    (hF'_c₀ : c₀ * (F_t.card : ℝ) ≤ (F'.card : ℝ))
    (hw_ge2 : (2 : ℝ) ≤ y ^ (a_peel + 2) * (F_t.card : ℝ)) :
    let w_y := ⌊y ^ (a_peel + 2) * (F_t.card : ℝ)⌋₊
    ((4 * ⌈y ^ (-(4 * d' * (h : ℝ) + 2))⌉₊ * ⌈(y ^ a)⁻¹⌉₊ ^ 2 * w_y : ℕ) : ℝ) ≤
      (⌊(y ^ a) ^ c₁ * (F'.card : ℝ)⌋₊ : ℝ) := by
  intro w_y
  have hy120 : y ≤ (2 : ℝ) ^ (-120 : ℝ) := hy_c₀.trans hc₀_120
  have hy_le1 : y ≤ 1 := hy120.trans (by norm_num)
  let M_ceil := ⌈y ^ (-(4 * d' * (h : ℝ) + 2))⌉₊
  let ℓ := ⌈(y ^ a)⁻¹⌉₊
  have hM_le : (M_ceil : ℝ) ≤ 2 * y ^ (-(4 * d' * (h : ℝ) + 2)) := by
    have hpos : 0 ≤ 4 * d' * (h : ℝ) + 2 := by positivity
    have h1 : (1 : ℝ) ≤ y ^ (-(4 * d' * (h : ℝ) + 2)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy0 hy_le1 (by linarith)
    have hlt := Nat.ceil_lt_add_one (by positivity : 0 ≤ y ^ (-(4 * d' * (h : ℝ) + 2)))
    dsimp [M_ceil]; linarith
  have hℓ_le : (ℓ : ℝ) ≤ 2 * y ^ (-(a : ℝ)) := by
    have h1 : (1 : ℝ) ≤ (y ^ a)⁻¹ := by
      rw [one_le_inv₀ (by positivity)]
      exact pow_le_one₀ hy0.le hy_le1
    have hlt := Nat.ceil_lt_add_one (by positivity : 0 ≤ (y ^ a)⁻¹)
    have heq : (y ^ a)⁻¹ = y ^ (-(a : ℝ)) := by
      rw [← Real.rpow_natCast y a, ← Real.rpow_neg hy0.le]
    dsimp [ℓ]; linarith
  have hℓ2_le : (ℓ : ℝ) ^ 2 ≤ 4 * y ^ (-2 * (a : ℝ)) := by
    calc (ℓ : ℝ) ^ 2 ≤ (2 * y ^ (-(a : ℝ))) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hℓ_le 2
      _ = 4 * (y ^ (-(a : ℝ))) ^ (2 : ℝ) := by rw [mul_pow, Real.rpow_two]; ring
      _ = 4 * y ^ (-2 * (a : ℝ)) := by rw [← Real.rpow_mul hy0.le]; congr 2; ring
  have hw_le : (w_y : ℝ) ≤ y ^ (a_peel + 2) * (F_t.card : ℝ) := Nat.floor_le (by positivity)
  have h32_y8 : 32 * y ^ (8 : ℝ) ≤ 1 / 2 := by
    have hy_inv2 : y ≤ 1 / 2 := hy120.trans (by norm_num)
    calc 32 * y ^ (8 : ℝ)
      _ ≤ 32 * (1 / 2 : ℝ) ^ (8 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hy0.le hy_inv2 (by norm_num)) (by norm_num)
      _ ≤ 1 / 2 := by
        rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        norm_num
  have hlhs_le : ((4 * M_ceil * ℓ ^ 2 * w_y : ℕ) : ℝ) ≤
      (1 / 2 : ℝ) * ((y ^ a) ^ c₁ * (F'.card : ℝ)) := by
    push_cast
    have hprod1 : 4 * (M_ceil : ℝ) * (ℓ : ℝ) ^ 2 * (w_y : ℝ) ≤
        32 * y ^ (a_peel - 4 * d' * (h : ℝ) - 2 * (a : ℝ)) * (F_t.card : ℝ) := by
      calc 4 * (M_ceil : ℝ) * (ℓ : ℝ) ^ 2 * (w_y : ℝ)
        _ ≤ 4 * (2 * y ^ (-(4 * d' * (h : ℝ) + 2))) * (4 * y ^ (-2 * (a : ℝ))) *
            (y ^ (a_peel + 2) * (F_t.card : ℝ)) := by
          refine mul_le_mul ?_ hw_le (Nat.cast_nonneg _) (by positivity)
          refine mul_le_mul ?_ hℓ2_le (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left hM_le (by norm_num)
        _ = 32 * (y ^ (-(4 * d' * (h : ℝ) + 2)) * y ^ (-2 * (a : ℝ)) * y ^ (a_peel + 2)) *
            (F_t.card : ℝ) := by ring
        _ = 32 * y ^ (a_peel - 4 * d' * (h : ℝ) - 2 * (a : ℝ)) * (F_t.card : ℝ) := by
          rw [← Real.rpow_add hy0, ← Real.rpow_add hy0]; congr 3; ring
    have hexp_ge : (a : ℝ) * c₁ + 9 ≤ a_peel - 4 * d' * (h : ℝ) - 2 * (a : ℝ) := by linarith
    have hrpow_le : y ^ (a_peel - 4 * d' * (h : ℝ) - 2 * (a : ℝ)) ≤
        y ^ (8 : ℝ) * y * (y ^ a) ^ c₁ := by
      calc y ^ (a_peel - 4 * d' * (h : ℝ) - 2 * (a : ℝ))
        _ ≤ y ^ ((a : ℝ) * c₁ + 9) := Real.rpow_le_rpow_of_exponent_ge hy0 hy_le1 hexp_ge
        _ = y ^ (8 : ℝ) * y ^ (1 : ℝ) * y ^ ((a : ℝ) * c₁) := by
          rw [show (a : ℝ) * c₁ + 9 = 8 + 1 + (a : ℝ) * c₁ by ring,
            Real.rpow_add hy0, Real.rpow_add hy0]
        _ = y ^ (8 : ℝ) * y * (y ^ a) ^ c₁ := by
          rw [Real.rpow_one, ← Real.rpow_natCast y a, ← Real.rpow_mul hy0.le]
    calc 4 * (M_ceil : ℝ) * (ℓ : ℝ) ^ 2 * (w_y : ℝ)
      _ ≤ 32 * (y ^ (8 : ℝ) * y * (y ^ a) ^ c₁) * (F_t.card : ℝ) :=
        hprod1.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrpow_le (by norm_num)) (Nat.cast_nonneg _))
      _ = (32 * y ^ (8 : ℝ)) * (y ^ a) ^ c₁ * (y * (F_t.card : ℝ)) := by ring
      _ ≤ (1 / 2 : ℝ) * (y ^ a) ^ c₁ * (c₀ * (F_t.card : ℝ)) := by
        refine mul_le_mul ?_ (mul_le_mul_of_nonneg_right hy_c₀ (Nat.cast_nonneg _))
          (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right h32_y8 (by positivity)
      _ = (1 / 2 : ℝ) * ((y ^ a) ^ c₁ * (c₀ * (F_t.card : ℝ))) := by ring
      _ ≤ (1 / 2 : ℝ) * ((y ^ a) ^ c₁ * (F'.card : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hF'_c₀ (by positivity)
  have h2_le_rhs : (2 : ℝ) ≤ (y ^ a) ^ c₁ * (F'.card : ℝ) := by
    have hy_a_c1 : y ^ (a_peel + 2) ≤ (y ^ a) ^ c₁ * c₀ := by
      have h1 : y ^ (a_peel + 2) ≤ y ^ ((a : ℝ) * c₁ + 1) := by
        refine Real.rpow_le_rpow_of_exponent_ge hy0 hy_le1 ?_
        have : (0 : ℝ) ≤ 4 * d' * (h : ℝ) := by positivity
        have : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
        linarith
      have h2 : y ^ ((a : ℝ) * c₁ + 1) = (y ^ a) ^ c₁ * y := by
        rw [Real.rpow_add_one hy0.ne', ← Real.rpow_natCast y a, ← Real.rpow_mul hy0.le]
      rw [h2] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left hy_c₀ (by positivity))
    calc (2 : ℝ) ≤ y ^ (a_peel + 2) * (F_t.card : ℝ) := hw_ge2
      _ ≤ ((y ^ a) ^ c₁ * c₀) * (F_t.card : ℝ) :=
        mul_le_mul_of_nonneg_right hy_a_c1 (Nat.cast_nonneg _)
      _ = (y ^ a) ^ c₁ * (c₀ * (F_t.card : ℝ)) := by ring
      _ ≤ (y ^ a) ^ c₁ * (F'.card : ℝ) := mul_le_mul_of_nonneg_left hF'_c₀ (by positivity)
  have hfloor_gt : (y ^ a) ^ c₁ * (F'.card : ℝ) - 1 < (⌊(y ^ a) ^ c₁ * (F'.card : ℝ)⌋₊ : ℝ) :=
    Nat.sub_one_lt_floor _
  linarith

set_option maxHeartbeats 400000 in
/--
**Branch 2 of Step 2 (`stage2_step2_branch2_gn`, `main.tex` lines 355–383, 387–392)**:
When $G[F']$ is $y$-sparse (`IsEpsSparseOn G F' y`, $|F'| \ge c_0 |F_t|$), applying
`SatisfiesPairCoupledGenNiceAt` to `G.induce F'` at $(\varepsilon_{\mathrm{GN}}, x_{\mathrm{sp}}) = (y^a, y^{3 a c_2})$
together with `stage2_gn1_viral_purification`, `IsPairThresholdedWonderful`, and
`step1d_open_interval_attachment` yields either:
- **(T1)** $(y^{b_3}|F_t|)^{c_4} \le \kappa(G)$;
- **(R2)** a $2y^2$-restricted subset $U \subseteq F'$ of size $\ge w_y$;
- **(R3)** a $100\%$ pairwise-pure cograph $(k_F, |F_t| / k_F^{c_5 + 4})$-blockade in $F_t$ with $k_F \ge \lceil y^{-1} \rceil$; or
- **(R4)** disjoint $X, Y \subseteq F'$ with $|X| = w_y$, $|Y| \ge (1 - a_5 y)|F'|$, and `IsAnticompletePair G X Y`.
-/
private theorem stage2_step2_branch2_gn
    {V : Type} [Fintype V] [DecidableEq V]
    {W₁ W₂ : Type*} [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]
    (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂)
    (v₀ u₀ : W₁) (hu₀_ne : u₀ ≠ v₀)
    (hleaf : ∀ w : W₁, H₁.Adj v₀ w ↔ w = u₀)
    (hh : 3 ≤ Fintype.card W₁)
    {d' : ℝ} (hd' : 0 < d')
    (hviral : ∀ (U_type : Type) [Fintype U_type] [DecidableEq U_type]
      (F_G : SimpleGraph U_type) (ε : ℝ),
      0 < ε → ε < 1 / 2 →
      (indCopyCount (H₁.comap (Subtype.val : {w : W₁ // w ≠ v₀} → W₁))ᶜ F_G : ℝ) ≤
        (ε ^ d' * (Fintype.card U_type : ℝ)) ^ (Fintype.card {w : W₁ // w ≠ v₀}) →
      (indCopyCount H₂ᶜ F_G : ℝ) ≤
        (ε ^ d' * (Fintype.card U_type : ℝ)) ^ (Fintype.card W₂) →
      ∃ S : Finset U_type, IsEpsRestrictedOn F_G S ε ∧
        ε ^ d' * (Fintype.card U_type : ℝ) ≤ (S.card : ℝ))
    {c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ : ℝ}
    (hc₂4 : 4 ≤ c₂) (hc₆1 : 1 ≤ c₆) (hc₇1 : 1 ≤ c₇) (hc₇_le : c₇ ≤ 3 * c₂)
    (hGN : SatisfiesPairCoupledGenNiceAt H₁ H₂ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉)
    {a_thr : ℕ} {y_thr : ℝ}
    (_ha_thr7 : 7 ≤ a_thr)
    (hwond : ∀ (U_type : Type) [Fintype U_type] [DecidableEq U_type] (F_G : SimpleGraph U_type)
      (y δ_cross : ℝ) (ℓ w : ℕ) (B : Fin ℓ → Finset U_type),
      0 < y → y ≤ y_thr →
      IsInducedSubgraphFree F_G H₁ᶜ → IsInducedSubgraphFree F_G H₂ᶜ →
      y ^ (-(a_thr : ℝ)) ≤ (ℓ : ℝ) →
      0 < δ_cross → δ_cross ≤ min (y ^ a_thr) (1 / (8 * (ℓ : ℝ) ^ 2)) →
      1 ≤ w →
      IsCompleteOrXSparseBlockadeIn F_G Finset.univ ℓ (w : ℝ) δ_cross B →
      (∀ i : Fin ℓ, (B i).card = w ∧ IsAnticonnected F_G (B i)) →
        (∃ S : Finset U_type, IsEpsRestrictedOn F_G S (y ^ 4) ∧ (w : ℝ) ≤ (S.card : ℝ)) ∨
        (∃ i_star : Fin ℓ,
          (((Finset.univ \ Finset.biUnion Finset.univ B).filter (fun v =>
            0 < (neighborFinsetIn F_G v (B i_star)).card ∧
            ((neighborFinsetIn F_G v (B i_star)).card : ℝ) < (1 / 2) * (w : ℝ))).card : ℝ) ≤
            y * (Fintype.card U_type : ℝ)))
    (G : SimpleGraph V) (hG₁ : IsInducedSubgraphFree G H₁ᶜ) (hG₂ : IsInducedSubgraphFree G H₂ᶜ)
    {F_t F' : Finset V} (hF'_sub : F' ⊆ F_t)
    {y c₀ a_peel a_5 b₃ : ℝ} {a : ℕ}
    (hy0 : 0 < y) (hy_c₀ : y ≤ c₀)
    (hc₀_pos : 0 < c₀) (hc₀_thr : c₀ ≤ y_thr) (hc₀_120 : c₀ ≤ (2 : ℝ) ^ (-120 : ℝ))
    (ha_thr_le : a_thr ≤ a) (ha20 : 20 ≤ a)
    (ha_4h : 4 * Fintype.card W₁ ≤ a)
    (ha_dh : 4 * d' * (Fintype.card W₁ : ℝ) + 10 ≤ (a : ℝ))
    (ha_peel_c₁ : (a : ℝ) * c₁ + 4 * d' * (Fintype.card W₁ : ℝ) + 2 * (a : ℝ) + 10 ≤ a_peel)
    (ha_peel_c₈ : (a : ℝ) * c₈ + 2 ≤ a_peel)
    (ha_peel_4a : 4 * (a : ℝ) + 10 ≤ a_peel)
    (ha_5_ge4 : 4 ≤ a_5)
    (hb₃_ge : (a : ℝ) * (3 * c₂ + 1) * c₃ + 1 ≤ b₃)
    (hF'_c₀ : c₀ * (F_t.card : ℝ) ≤ (F'.card : ℝ))
    (hw_ge2 : (2 : ℝ) ≤ y ^ (a_peel + 2) * (F_t.card : ℝ))
    (hF'_sparse : IsEpsSparseOn G F' y) :
    let w_y := ⌊y ^ (a_peel + 2) * (F_t.card : ℝ)⌋₊
    -- (T1)
    ((y ^ b₃ * (F_t.card : ℝ)) ^ c₄ ≤ (kappa G : ℝ)) ∨
    -- (R2)
    (∃ U ⊆ F', IsEpsRestrictedOn G U (2 * y ^ 2) ∧ (w_y : ℝ) ≤ (U.card : ℝ)) ∨
    -- (R3)
    (∃ k_F : ℕ, ⌈y⁻¹⌉₊ ≤ k_F ∧ ∃ B : Fin k_F → Finset V,
      IsPureCographBlockadeIn G F_t k_F (c₀ * (F_t.card : ℝ) / (k_F : ℝ) ^ c₅) B) ∨
    -- (R4)
    (∃ X ⊆ F', ∃ Y ⊆ F', Disjoint X Y ∧
      X.card = w_y ∧ (1 - a_5 * y) * (F'.card : ℝ) ≤ (Y.card : ℝ) ∧ IsPurePair G X Y) := by
  classical
  intro w_y
  obtain ⟨hc₁_pos, _, hc₃_pos, hc₄_pos, hc₅_pos, _, _, hc₈_pos, _, hGN_prop⟩ := hGN
  have ha20_real : (20 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha20
  have hy120 : y ≤ (2 : ℝ) ^ (-120 : ℝ) := hy_c₀.trans hc₀_120
  have hy_le1 : y ≤ 1 := hy120.trans (by norm_num)
  have hw_y_pos : 1 ≤ w_y := Nat.floor_pos.mpr (by linarith)
  have hw_y_le : (w_y : ℝ) ≤ y ^ (a_peel + 2) * (F_t.card : ℝ) := Nat.floor_le (by positivity)
  let ε_GN := y ^ a
  let x_sp := ε_GN ^ (3 * c₂)
  have hε_pos : 0 < ε_GN := by dsimp [ε_GN]; positivity
  have hε_le_y : ε_GN ≤ y := by
    dsimp [ε_GN]
    calc y ^ a ≤ y ^ 1 := pow_le_pow_of_le_one hy0.le hy_le1 (by omega)
      _ = y := pow_one y
  have hε_half : ε_GN < 1 / 2 := hε_le_y.trans_lt (hy120.trans_lt (by norm_num))
  have hε_le1 : ε_GN ≤ 1 := hε_half.le.trans (by norm_num)
  have hx_hi : x_sp ≤ ε_GN ^ c₇ :=
    Real.rpow_le_rpow_of_exponent_ge hε_pos hε_le1 hc₇_le
  -- Work on F_G := G.induce (F' : Set V)
  let F_G := G.induce (F' : Set V)
  let emb := Function.Embedding.subtype (fun x : V => x ∈ (F' : Set V))
  have hFG₁ : IsInducedSubgraphFree F_G H₁ᶜ := isInducedSubgraphFree_induce G H₁ᶜ F' hG₁
  have hFG₂ : IsInducedSubgraphFree F_G H₂ᶜ := isInducedSubgraphFree_induce G H₂ᶜ F' hG₂
  have hcard_FG : Fintype.card ↥(F' : Set V) = F'.card := Fintype.card_coe F'
  rcases hGN_prop ↥(F' : Set V) F_G ε_GN x_sp hε_pos hε_half le_rfl hx_hi hFG₁ hFG₂ with
    ⟨A_sub, hA_sub⟩ | hGN2 | ⟨k_F, hk_lo, _, B_sub, hB_sub⟩ | ⟨S_sub, hS_rest, hS_card⟩
  · -- (GN1): Purify A_sub on F_G via stage2_gn1_viral_purification
    rw [hcard_FG] at hA_sub
    have hm₁_ge : ((4 * ⌈y ^ (-(4 * d' * (Fintype.card W₁ : ℝ) + 2))⌉₊ *
        ⌈(y ^ a)⁻¹⌉₊ ^ 2 * w_y : ℕ) : ℝ) ≤ (⌊ε_GN ^ c₁ * (F'.card : ℝ)⌋₊ : ℝ) :=
      stage2_gn1_m1_ge_W0 hy0 hy_c₀ hc₀_120 hc₁_pos hd' ha20 ha_peel_c₁ hF'_c₀ hw_ge2
    rcases stage2_gn1_viral_purification H₁ H₂ v₀ u₀ hu₀_ne hleaf hh hd' hviral
        F_G hFG₁ hFG₂ hy0 hy120 hc₂4 ha20 ha_4h ha_dh hw_y_pos hm₁_ge A_sub hA_sub with
      ⟨U_sub, hU_rest, hU_card⟩ | ⟨B_pur, hB_pur_block, hB_pur_anti⟩
    · -- (R2) from purification
      right; left
      let U := U_sub.map emb
      have hUF' : U ⊆ F' := by intro x hx; rcases Finset.mem_map.mp hx with ⟨z, _, rfl⟩; exact z.2
      exact ⟨U, hUF', isEpsRestrictedOn_map_subtype G F' U_sub (2 * y ^ 2) hU_rest,
        by dsimp [U]; rw [Finset.card_map]; exact hU_card⟩
    · -- Apply IsPairThresholdedWonderful to F_G and B_pur at y and δ_cross = y ^ (3 * a)
      let ℓ := ⌈(y ^ a)⁻¹⌉₊
      have hℓ_ge_inv : (y ^ a)⁻¹ ≤ (ℓ : ℝ) := Nat.le_ceil _
      have hℓ_ge_athr : y ^ (-(a_thr : ℝ)) ≤ (ℓ : ℝ) := by
        have h1 : y ^ (-(a_thr : ℝ)) ≤ y ^ (-(a : ℝ)) := by
          refine Real.rpow_le_rpow_of_exponent_ge hy0 hy_le1 ?_
          have : (a_thr : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha_thr_le
          linarith
        have h2 : y ^ (-(a : ℝ)) = (y ^ a)⁻¹ := by
          rw [Real.rpow_neg hy0.le, Real.rpow_natCast]
        exact (h1.trans_eq h2).trans hℓ_ge_inv
      have hδ_pos : 0 < y ^ (3 * a) := by positivity
      have hδ_le_min : y ^ (3 * a) ≤ min (y ^ a_thr) (1 / (8 * (ℓ : ℝ) ^ 2)) := by
        refine le_min (pow_le_pow_of_le_one hy0.le hy_le1 (by omega)) ?_
        rw [le_div_iff₀ (by positivity)]
        have hℓ_le : (ℓ : ℝ) ≤ 2 * y ^ (-(a : ℝ)) := by
          have h1 : (1 : ℝ) ≤ (y ^ a)⁻¹ := by
            rw [one_le_inv₀ (by positivity)]; exact pow_le_one₀ hy0.le hy_le1
          have hlt := Nat.ceil_lt_add_one (by positivity : 0 ≤ (y ^ a)⁻¹)
          have heq : (y ^ a)⁻¹ = y ^ (-(a : ℝ)) := by
            rw [← Real.rpow_natCast y a, ← Real.rpow_neg hy0.le]
          dsimp [ℓ]; linarith
        have hℓ2_le : (ℓ : ℝ) ^ 2 ≤ 4 * y ^ (-2 * (a : ℝ)) := by
          calc (ℓ : ℝ) ^ 2 ≤ (2 * y ^ (-(a : ℝ))) ^ 2 :=
              pow_le_pow_left₀ (Nat.cast_nonneg _) hℓ_le 2
            _ = 4 * (y ^ (-(a : ℝ))) ^ (2 : ℝ) := by rw [mul_pow, Real.rpow_two]; ring
            _ = 4 * y ^ (-2 * (a : ℝ)) := by rw [← Real.rpow_mul hy0.le]; congr 2; ring
        have hya_le_y : y ^ (a : ℝ) ≤ y := by
          calc y ^ (a : ℝ) ≤ y ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_ge hy0 hy_le1 (by linarith)
            _ = y := Real.rpow_one y
        calc y ^ (3 * a) * (8 * (ℓ : ℝ) ^ 2)
          _ ≤ y ^ (3 * (a : ℝ)) * (8 * (4 * y ^ (-2 * (a : ℝ)))) := by
            rw [← Real.rpow_natCast y (3 * a), show ((3 * a : ℕ) : ℝ) = 3 * (a : ℝ) by push_cast; rfl]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hℓ2_le (by norm_num)) (by positivity)
          _ = 32 * (y ^ (3 * (a : ℝ)) * y ^ (-2 * (a : ℝ))) := by ring
          _ = 32 * y ^ (a : ℝ) := by rw [← Real.rpow_add hy0]; congr 2; ring
          _ ≤ 32 * y := mul_le_mul_of_nonneg_left hya_le_y (by norm_num)
          _ ≤ 1 := by
            have : (2 : ℝ) ^ (-120 : ℝ) ≤ 1 / 32 := by norm_num
            linarith [hy120.trans this]
      rcases hwond ↥(F' : Set V) F_G y (y ^ (3 * a)) ℓ w_y B_pur hy0 (hy_c₀.trans hc₀_thr)
          hFG₁ hFG₂ hℓ_ge_athr hδ_pos hδ_le_min hw_y_pos hB_pur_block hB_pur_anti with
        ⟨S_wond, hS_wond_rest, hS_wond_card⟩ | ⟨i_star, hi_star⟩
      · -- (W1) -> (R2)
        right; left
        let U := S_wond.map emb
        have hUF' : U ⊆ F' := by intro x hx; rcases Finset.mem_map.mp hx with ⟨z, _, rfl⟩; exact z.2
        have hy4_le_2y2 : y ^ 4 ≤ 2 * y ^ 2 := by
          have h1 : y ^ 4 ≤ y ^ 2 := pow_le_pow_of_le_one hy0.le hy_le1 (by omega)
          have h2 : 1 * y ^ 2 ≤ 2 * y ^ 2 := mul_le_mul_of_nonneg_right one_le_two (sq_nonneg y)
          rw [one_mul] at h2
          exact h1.trans h2
        exact ⟨U, hUF', (isEpsRestrictedOn_map_subtype G F' S_wond (y ^ 4) hS_wond_rest).mono hy4_le_2y2,
          by dsimp [U]; rw [Finset.card_map]; exact hS_wond_card⟩
      · -- (W2) -> (R4) via step1d_open_interval_attachment on F_G
        right; right; right
        have hFG_sparse : IsEpsSparseOn F_G Finset.univ y := isEpsSparseOn_induce_univ G F' y hF'_sparse
        have hcard_univ : (Finset.univ : Finset ↥(F' : Set V)).card = F'.card :=
          Finset.card_univ.trans hcard_FG
        have hℓw : ((ℓ * w_y : ℕ) : ℝ) ≤ y * ((Finset.univ : Finset ↥(F' : Set V)).card : ℝ) := by
          rw [hcard_univ]; push_cast
          have hℓ_le : (ℓ : ℝ) ≤ 2 * y ^ (-(a : ℝ)) := by
            have h1 : (1 : ℝ) ≤ (y ^ a)⁻¹ := by
              rw [one_le_inv₀ (by positivity)]; exact pow_le_one₀ hy0.le hy_le1
            have hlt := Nat.ceil_lt_add_one (by positivity : 0 ≤ (y ^ a)⁻¹)
            have heq : (y ^ a)⁻¹ = y ^ (-(a : ℝ)) := by
              rw [← Real.rpow_natCast y a, ← Real.rpow_neg hy0.le]
            dsimp [ℓ]; linarith
          have h2y_le1 : 2 * y ≤ 1 := by
            have : (2 : ℝ) ^ (-120 : ℝ) ≤ 1 / 2 := by norm_num
            linarith [hy120.trans this]
          have hexp : y ^ (a_peel + 2 - (a : ℝ)) ≤ y * y * c₀ := by
            calc y ^ (a_peel + 2 - (a : ℝ))
              _ ≤ y ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hy0 hy_le1 (by linarith)
              _ = y * y * y := by
                rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
              _ ≤ y * y * c₀ := mul_le_mul_of_nonneg_left hy_c₀ (by positivity)
          calc (ℓ : ℝ) * (w_y : ℝ)
            _ ≤ (2 * y ^ (-(a : ℝ))) * (y ^ (a_peel + 2) * (F_t.card : ℝ)) :=
              mul_le_mul hℓ_le hw_y_le (Nat.cast_nonneg _) (by positivity)
            _ = 2 * (y ^ (-(a : ℝ)) * y ^ (a_peel + 2)) * (F_t.card : ℝ) := by ring
            _ = 2 * y ^ (a_peel + 2 - (a : ℝ)) * (F_t.card : ℝ) := by
              rw [← Real.rpow_add hy0]; congr 3; ring
            _ ≤ 2 * (y * y * c₀) * (F_t.card : ℝ) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp zero_le_two) (Nat.cast_nonneg _)
            _ = (2 * y) * (y * (c₀ * (F_t.card : ℝ))) := by ring
            _ ≤ 1 * (y * (F'.card : ℝ)) :=
              mul_le_mul h2y_le1 (mul_le_mul_of_nonneg_left hF'_c₀ hy0.le) (by positivity) zero_le_one
            _ = y * (F'.card : ℝ) := one_mul _
        have hopen_univ : (((Finset.univ \ (Finset.univ : Finset (Fin ℓ)).biUnion B_pur).filter (fun v =>
            0 < (neighborFinsetIn F_G v (B_pur i_star)).card ∧
            ((neighborFinsetIn F_G v (B_pur i_star)).card : ℝ) < (1 / 2 : ℝ) * (w_y : ℝ))).card : ℝ) ≤
            y * ((Finset.univ : Finset ↥(F' : Set V)).card : ℝ) := by
          rw [Finset.card_univ]; exact hi_star
        obtain ⟨X_sub, _, Y_sub, _, hdisj_sub, hX_card, hY_card, hanti_sub⟩ :=
          step1d_open_interval_attachment F_G Finset.univ ℓ w_y y hw_y_pos hy0 hFG_sparse
            B_pur (fun _ => subset_univ _) (fun i => (hB_pur_anti i).1) hℓw i_star hopen_univ
        rw [hcard_univ] at hY_card
        let X := X_sub.map emb
        let Y := Y_sub.map emb
        have hXF' : X ⊆ F' := by intro x hx; rcases Finset.mem_map.mp hx with ⟨z, _, rfl⟩; exact z.2
        have hYF' : Y ⊆ F' := by intro x hx; rcases Finset.mem_map.mp hx with ⟨z, _, rfl⟩; exact z.2
        have hdisj_XY : Disjoint X Y := (Finset.disjoint_map emb).mpr hdisj_sub
        have hY_a5 : (1 - a_5 * y) * (F'.card : ℝ) ≤ (Y.card : ℝ) := by
          dsimp [Y]; rw [Finset.card_map]
          have h1 : (1 - a_5 * y) * (F'.card : ℝ) ≤ (1 - 4 * y) * (F'.card : ℝ) := by
            refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
            exact sub_le_sub_left (mul_le_mul_of_nonneg_right ha_5_ge4 hy0.le) 1
          exact h1.trans hY_card
        exact ⟨X, hXF', Y, hYF', hdisj_XY, by dsimp [X]; rw [Finset.card_map]; exact hX_card, hY_a5,
          Or.inr (isAnticompletePair_map_subtype G F' X_sub Y_sub hanti_sub)⟩
  · -- (GN2) -> (T1)
    left
    rw [hcard_FG] at hGN2
    have hkappa_le : (kappa F_G : ℝ) ≤ (kappa G : ℝ) := by
      exact_mod_cast kappa_comap_le G emb
    have hprod_ge : y ^ b₃ * (F_t.card : ℝ) ≤ ε_GN ^ c₃ * x_sp ^ c₃ * (F'.card : ℝ) := by
      have heq : ε_GN ^ c₃ * x_sp ^ c₃ = y ^ ((a : ℝ) * (3 * c₂ + 1) * c₃) := by
        dsimp [x_sp, ε_GN]
        rw [← Real.rpow_mul (by positivity), ← Real.rpow_add (by positivity),
          ← Real.rpow_natCast y a, ← Real.rpow_mul hy0.le]
        congr 1; ring
      rw [heq]
      have hy_b3 : y ^ b₃ ≤ y ^ ((a : ℝ) * (3 * c₂ + 1) * c₃) * y := by
        calc y ^ b₃
          _ ≤ y ^ ((a : ℝ) * (3 * c₂ + 1) * c₃ + 1) :=
            Real.rpow_le_rpow_of_exponent_ge hy0 hy_le1 hb₃_ge
          _ = y ^ ((a : ℝ) * (3 * c₂ + 1) * c₃) * y := Real.rpow_add_one hy0.ne' _
      calc y ^ b₃ * (F_t.card : ℝ)
        _ ≤ (y ^ ((a : ℝ) * (3 * c₂ + 1) * c₃) * y) * (F_t.card : ℝ) :=
          mul_le_mul_of_nonneg_right hy_b3 (Nat.cast_nonneg _)
        _ ≤ (y ^ ((a : ℝ) * (3 * c₂ + 1) * c₃) * c₀) * (F_t.card : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hy_c₀ (by positivity))
            (Nat.cast_nonneg _)
        _ = y ^ ((a : ℝ) * (3 * c₂ + 1) * c₃) * (c₀ * (F_t.card : ℝ)) := by ring
        _ ≤ y ^ ((a : ℝ) * (3 * c₂ + 1) * c₃) * (F'.card : ℝ) :=
          mul_le_mul_of_nonneg_left hF'_c₀ (by positivity)
    exact (Real.rpow_le_rpow (by positivity) hprod_ge hc₄_pos.le).trans (hGN2.trans hkappa_le)
  · -- (GN3) -> (R3)
    right; right; left
    rw [hcard_FG] at hB_sub
    have hk_ge_y : ⌈y⁻¹⌉₊ ≤ k_F := by
      have h1 : y⁻¹ ≤ ε_GN ^ (-c₆) := by
        dsimp [ε_GN]
        rw [← Real.rpow_neg_one y, ← Real.rpow_natCast y a, ← Real.rpow_mul hy0.le]
        refine Real.rpow_le_rpow_of_exponent_ge hy0 hy_le1 ?_
        have hmul : 1 * 1 ≤ (a : ℝ) * c₆ :=
          mul_le_mul (by linarith) hc₆1 zero_le_one (by linarith)
        linarith
      exact (Nat.ceil_mono h1).trans hk_lo
    have hk_pos : (0 : ℝ) < (k_F : ℝ) := by
      have : 0 < ⌈y⁻¹⌉₊ := Nat.ceil_pos.mpr (inv_pos.mpr hy0)
      exact_mod_cast this.trans_le hk_ge_y
    have hB_F' := isPureCographBlockadeIn_map_subtype G F' B_sub hB_sub
    have hw_c₀ : c₀ * (F_t.card : ℝ) / (k_F : ℝ) ^ c₅ ≤ (F'.card : ℝ) / (k_F : ℝ) ^ c₅ :=
      div_le_div_of_nonneg_right hF'_c₀ (by positivity)
    exact ⟨k_F, hk_ge_y, fun i => (B_sub i).map emb,
      ⟨⟨(hB_F'.1.1.mono_ambient hF'_sub).mono_width hw_c₀, hB_F'.1.2⟩, hB_F'.2⟩⟩
  · -- (GN4) -> (R2)
    right; left
    rw [hcard_FG] at hS_card
    let U := S_sub.map emb
    have hUF' : U ⊆ F' := by intro x hx; rcases Finset.mem_map.mp hx with ⟨z, _, rfl⟩; exact z.2
    have h2_c₇ : 2 * ε_GN ^ c₇ ≤ 2 * y ^ 2 := by
      dsimp [ε_GN]
      rw [← Real.rpow_natCast y a, ← Real.rpow_mul hy0.le, ← Real.rpow_natCast y 2]
      refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hy0 hy_le1 ?_) zero_le_two
      have hmul : 20 * 1 ≤ (a : ℝ) * c₇ :=
        mul_le_mul ha20_real hc₇1 zero_le_one (by linarith)
      push_cast; linarith
    have hw_le_U : (w_y : ℝ) ≤ (U.card : ℝ) := by
      dsimp [U]; rw [Finset.card_map]
      have h1 : y ^ (a_peel + 2) ≤ ε_GN ^ c₈ * c₀ := by
        dsimp [ε_GN]
        rw [← Real.rpow_natCast y a, ← Real.rpow_mul hy0.le]
        calc y ^ (a_peel + 2)
          _ ≤ y ^ ((a : ℝ) * c₈ + 1) := Real.rpow_le_rpow_of_exponent_ge hy0 hy_le1 (by linarith)
          _ = y ^ ((a : ℝ) * c₈) * y := Real.rpow_add_one hy0.ne' _
          _ ≤ y ^ ((a : ℝ) * c₈) * c₀ := mul_le_mul_of_nonneg_left hy_c₀ (by positivity)
      calc (w_y : ℝ)
        _ ≤ y ^ (a_peel + 2) * (F_t.card : ℝ) := hw_y_le
        _ ≤ (ε_GN ^ c₈ * c₀) * (F_t.card : ℝ) :=
          mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)
        _ = ε_GN ^ c₈ * (c₀ * (F_t.card : ℝ)) := by ring
        _ ≤ ε_GN ^ c₈ * (F'.card : ℝ) := mul_le_mul_of_nonneg_left hF'_c₀ (by positivity)
        _ ≤ (S_sub.card : ℝ) := hS_card
    exact ⟨U, hUF', (isEpsRestrictedOn_map_subtype G F' S_sub (2 * ε_GN ^ c₇) hS_rest).mono h2_c₇,
      hw_le_U⟩

theorem IsPureCographBlockadeIn.mono_ambient_width {G : SimpleGraph V} {F' F : Finset V}
    {k : ℕ} {w₁ w₂ : ℝ} {B : Fin k → Finset V}
    (hB : IsPureCographBlockadeIn G F' k w₁ B) (hsub : F' ⊆ F) (hw : w₂ ≤ w₁) :
    IsPureCographBlockadeIn G F k w₂ B :=
  ⟨⟨(hB.1.1.mono_ambient hsub).mono_width hw, hB.1.2⟩, hB.2⟩

set_option maxHeartbeats 800000 in
/--
**Master Stage-2 Reduction for Coupled Generalized Nice and Thresholded Wonderful Families
(`master_stage2_pair_eh_of_coupled_gen_nice_and_wonderful`, Lemma 7(2) of `main.tex`, lines 295, 333–412)**:
Let $\{H_1, H_2\}$ be a finite two-graph family ($|H_1| \ge 3$) such that:
1. $H_1$ has a degree-$1$ leaf $v_0$ with unique neighbor $u_0 \neq v_0$, and $((H_1 - v_0)ᶜ, H_2ᶜ)$
   is viral (`IsPairViral`);
2. $\{H_1, H_2\}$ is open-interval thresholded wonderful (`IsPairThresholdedWonderful H₁ H₂`); and
3. $\{H_1, H_2\}$ satisfies coupled Stage-1 generalized niceness (`SatisfiesPairCoupledGenNiceAt H₁ H₂ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉`
   with $c_2 \ge 4$, $c_6 \ge 1$, $c_7 \ge 1$, and $c_7 \le 3 c_2$ — satisfied by every output of Lemma 7(1)).
Then both $\{H_1ᶜ, H_2ᶜ\}$ and $\{H_1, H_2\}$ satisfy the Erdős–Hajnal property (`HasPairErdosHajnalProp`),
proved in three self-contained steps (`main.tex` lines 350–411):
- **Step 1 (`stage2_gn1_viral_purification`)**: One-shot simultaneous co-sparse-to-$100\%$-complete
  purification of `(GN1)` at exact coupled sparsity $x_{\mathrm{sp}} = \varepsilon_{\mathrm{GN}}^{3 c_2} = y^{3 a c_2}$;
- **Step 2 (`stage2_step2_branch2_gn` & `leaf_reducible_cosparse_trigger_or_restricted`)**:
  Open-interval extraction of $0$-defect pure (complete or anticomplete) trigger pairs $(X, Y)$;
- **Step 3 (`equal_sized_trigger_peeling_cograph` at $x = 0$ & `cograph_stage2_reduction`)**:
  Zero-defect pure-cograph blockade peeling and termination via Seinsche's Theorem and Lemma 4(2).
-/
theorem master_stage2_pair_eh_of_coupled_gen_nice_and_wonderful
    {W₁ W₂ : Type*} [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]
    (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂)
    (v₀ u₀ : W₁) (hu₀_ne : u₀ ≠ v₀)
    (hleaf : ∀ w : W₁, H₁.Adj v₀ w ↔ w = u₀)
    (hh : 3 ≤ Fintype.card W₁)
    (hviral : IsPairViral (H₁.comap (Subtype.val : {w : W₁ // w ≠ v₀} → W₁))ᶜ H₂ᶜ)
    (hwond : IsPairThresholdedWonderful H₁ H₂)
    {c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ : ℝ}
    (hc₂4 : 4 ≤ c₂) (hc₆1 : 1 ≤ c₆) (hc₇1 : 1 ≤ c₇) (hc₇_le : c₇ ≤ 3 * c₂)
    (hGN : SatisfiesPairCoupledGenNiceAt H₁ H₂ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉) :
    HasPairErdosHajnalProp H₁ᶜ H₂ᶜ ∧ HasPairErdosHajnalProp H₁ H₂ := by
  classical
  have h_compl : HasPairErdosHajnalProp H₁ᶜ H₂ᶜ := by
    obtain ⟨d', hd', hviral_prop⟩ := hviral
    obtain ⟨a_thr, y_thr, ha_thr7, hy_thr_pos, hy_thr_quarter, hwond_prop⟩ := hwond
    have ⟨hc₁_pos, _, hc₃_pos, hc₄_pos, hc₅_pos, _, _, hc₈_pos, _, _⟩ := hGN
    let h := Fintype.card W₁
    let a_leaf : ℝ := 4 * d' * (h : ℝ) + 6
    let b_leaf : ℝ := 3 * (h : ℝ)
    let a_5 : ℝ := 4 + b_leaf
    let a : ℕ := max (max a_thr 20) (max (4 * h) ⌈4 * d' * (h : ℝ) + 10⌉₊)
    let c₀ : ℝ := min ((2 : ℝ) ^ (-8 * a_5)) (min y_thr ((2 : ℝ) ^ (-120 : ℝ)))
    let lam0 : ℝ := c₀ ^ 4
    let δ₂ : ℝ := symmRodlDeltaGen h lam0
    let a_peel : ℝ := (a : ℝ) * max c₁ c₈ + 4 * d' * (h : ℝ) + 4 * (a : ℝ) + 10
    let b₁ : ℝ := 11 / 10
    let b₃ : ℝ := 2 * (a : ℝ) * c₃ * (3 * c₂ + 1) + a_peel + a_leaf + 10
    let b₂ : ℝ := max (20 * b₃) ((⌈Real.log (1 / δ₂) / Real.log (1 / lam0)⌉₊ : ℝ) + 1)
    let K₀ : ℝ := (⌈Real.log (1 / c₀) / Real.log 2⌉₊ : ℝ) + 1
    let C₁ : ℝ := 5 * b₂ * K₀ + a_peel + b₂ + b₃ + c₅ + K₀ + 20
    let C₂ : ℝ := min c₄ 1
    -- Basic positivity and parameter bounds
    have ha_thr_le : a_thr ≤ a := (le_max_left _ _).trans (le_max_left _ _)
    have ha20 : 20 ≤ a := (le_max_right _ _).trans (le_max_left _ _)
    have ha_4h : 4 * h ≤ a := (le_max_left _ _).trans (le_max_right _ _)
    have ha_dh : 4 * d' * (h : ℝ) + 10 ≤ (a : ℝ) := by
      have h1 : ⌈4 * d' * (h : ℝ) + 10⌉₊ ≤ a := (le_max_right _ _).trans (le_max_right _ _)
      exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
    have hh_real : (3 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
    have ha_5_ge13 : 13 ≤ a_5 := by dsimp [a_5, b_leaf]; linarith
    have ha_5_ge_h : (h : ℝ) ≤ a_5 := by dsimp [a_5, b_leaf]; linarith
    have hc₀_pos : 0 < c₀ := by dsimp [c₀]; exact lt_min (by positivity) (lt_min hy_thr_pos (by positivity))
    have hc₀_8a5 : c₀ ≤ (2 : ℝ) ^ (-8 * a_5) := min_le_left _ _
    have hc₀_thr : c₀ ≤ y_thr := (min_le_right _ _).trans (min_le_left _ _)
    have hc₀_120 : c₀ ≤ (2 : ℝ) ^ (-120 : ℝ) := (min_le_right _ _).trans (min_le_right _ _)
    have hc₀_le1 : c₀ ≤ 1 := hc₀_120.trans (by norm_num)
    have hlam0_eq : lam0 = c₀ ^ 4 := rfl
    have hlam0_pos : 0 < lam0 := by rw [hlam0_eq]; positivity
    have hlam0_half : lam0 < 1 / 2 := by
      rw [hlam0_eq]
      calc c₀ ^ 4 ≤ c₀ ^ 1 := pow_le_pow_of_le_one hc₀_pos.le hc₀_le1 (by omega)
        _ = c₀ := pow_one c₀
        _ < 1 / 2 := hc₀_120.trans_lt (by norm_num)
    have hδ₂_eq : symmRodlDeltaGen h lam0 = δ₂ := rfl
    have hδ₂_pos : 0 < δ₂ := rodlDeltaGen_pos h hlam0_pos
    have ha_peel_pos : 10 ≤ a_peel := by
      dsimp [a_peel]
      have h1 : 0 ≤ (a : ℝ) * max c₁ c₈ + 4 * d' * (h : ℝ) + 4 * (a : ℝ) := by
        have : 0 < max c₁ c₈ := lt_of_lt_of_le hc₁_pos (le_max_left _ _)
        positivity
      linarith
    have ha_peel_c₁ : (a : ℝ) * c₁ + 4 * d' * (h : ℝ) + 2 * (a : ℝ) + 10 ≤ a_peel := by
      dsimp [a_peel]
      have h1 : (a : ℝ) * c₁ ≤ (a : ℝ) * max c₁ c₈ :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (Nat.cast_nonneg _)
      have h2 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg _
      linarith
    have ha_peel_c₈ : (a : ℝ) * c₈ + 2 ≤ a_peel := by
      dsimp [a_peel]
      have h1 : (a : ℝ) * c₈ ≤ (a : ℝ) * max c₁ c₈ :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (Nat.cast_nonneg _)
      have h2 : 0 ≤ 4 * d' * (h : ℝ) + 4 * (a : ℝ) := by positivity
      linarith
    have ha_peel_4a : 4 * (a : ℝ) + 10 ≤ a_peel := by
      dsimp [a_peel]
      have h1 : 0 ≤ (a : ℝ) * max c₁ c₈ + 4 * d' * (h : ℝ) := by
        have : 0 < max c₁ c₈ := lt_of_lt_of_le hc₁_pos (le_max_left _ _)
        positivity
      linarith
    have ha_peel_4dh : 4 * d' * (h : ℝ) + 10 ≤ a_peel := by
      dsimp [a_peel]
      have h1 : 0 ≤ (a : ℝ) * max c₁ c₈ + 4 * (a : ℝ) := by
        have : 0 < max c₁ c₈ := lt_of_lt_of_le hc₁_pos (le_max_left _ _)
        positivity
      linarith
    have hb₁_eq : b₁ = 11 / 10 := rfl
    have hb₁_gt1 : 1 < b₁ := by rw [hb₁_eq]; norm_num
    have hb₃_pos : 10 ≤ b₃ := by
      dsimp [b₃, a_leaf]
      have h1 : 0 ≤ 2 * (a : ℝ) * c₃ * (3 * c₂ + 1) + a_peel + (4 * d' * (h : ℝ) + 6) := by
        have : 0 < a_peel := by linarith
        positivity
      linarith
    have hb₃_ge : (a : ℝ) * (3 * c₂ + 1) * c₃ + 1 ≤ b₃ := by
      dsimp [b₃, a_leaf]
      have h1 : (a : ℝ) * (3 * c₂ + 1) * c₃ ≤ 2 * (a : ℝ) * c₃ * (3 * c₂ + 1) := by
        have : 0 ≤ (a : ℝ) * c₃ * (3 * c₂ + 1) := by positivity
        linarith
      have h2 : 0 ≤ a_peel + (4 * d' * (h : ℝ) + 6) := by
        have : 0 < a_peel := by linarith
        positivity
      linarith
    have hb₃_ge_peel : a_peel + 3 ≤ b₃ := by
      dsimp [b₃, a_leaf]
      have h1 : 0 ≤ 2 * (a : ℝ) * c₃ * (3 * c₂ + 1) + (4 * d' * (h : ℝ) + 6) := by positivity
      linarith
    have hb₂_ge_20b3 : 20 * b₃ ≤ b₂ := le_max_left _ _
    have hb₂_pos : 0 < b₂ := by linarith
    have hb₁_b₂_ge_b₃ : (b₁ - 1) * b₂ ≥ b₃ := by rw [hb₁_eq]; linarith
    have hlam0_b2_le_δ₂ : lam0 ^ b₂ ≤ δ₂ := by
      have hb₂_ceil : (⌈Real.log (1 / δ₂) / Real.log (1 / lam0)⌉₊ : ℝ) ≤ b₂ := by
        have : (⌈Real.log (1 / δ₂) / Real.log (1 / lam0)⌉₊ : ℝ) + 1 ≤ b₂ := le_max_right _ _
        linarith
      have hdiv : Real.log (1 / δ₂) / Real.log (1 / lam0) ≤ b₂ :=
        (Nat.le_ceil _).trans hb₂_ceil
      have hlog_pos : 0 < Real.log (1 / lam0) :=
        Real.log_pos (one_lt_one_div hlam0_pos (by linarith))
      have hmul : Real.log (1 / δ₂) ≤ b₂ * Real.log (1 / lam0) := (div_le_iff₀ hlog_pos).mp hdiv
      rw [one_div, one_div, Real.log_inv, Real.log_inv] at hmul
      have hlog_le : Real.log (lam0 ^ b₂) ≤ Real.log δ₂ := by
        rw [Real.log_rpow hlam0_pos]; linarith
      exact (Real.log_le_log_iff (by positivity) hδ₂_pos).mp hlog_le
    have hK₀_pos : 1 ≤ K₀ := by
      dsimp [K₀]
      have h1 : (0 : ℝ) ≤ (⌈Real.log (1 / c₀) / Real.log 2⌉₊ : ℝ) := Nat.cast_nonneg _
      linarith
    have h2_K₀ : (2 : ℝ) ^ (-K₀) ≤ c₀ := two_rpow_neg_K0_le_c0 hc₀_pos
    have hb2K0_pos : 0 < b₂ * K₀ := by positivity
    have hC₁_ge1 : 1 ≤ C₁ := by dsimp [C₁]; linarith
    have hC₁_ge_b3_b2 : b₃ + b₂ + 4 * K₀ * b₂ ≤ C₁ := by dsimp [C₁]; linarith
    have hC₁_ge_peel : (a_peel + 2) + K₀ + (K₀ + 1) * b₂ + 4 * K₀ * b₂ ≤ C₁ := by
      dsimp [C₁]; linarith
    have hC₁_ge_c5 : c₅ + K₀ + (K₀ + 1) * b₂ + 4 * K₀ * b₂ ≤ C₁ := by
      dsimp [C₁]; linarith
    have hC₁_ge_b1_b2 : b₁ * b₂ + 4 * K₀ * b₂ ≤ C₁ := by
      dsimp [C₁]; rw [hb₁_eq]
      have h1 : 1 * b₂ ≤ b₂ * K₀ := by
        calc 1 * b₂ = b₂ * 1 := by ring
          _ ≤ b₂ * K₀ := mul_le_mul_of_nonneg_left hK₀_pos hb₂_pos.le
      linarith
    have hC₁_ge_4K0_b2 : 4 * K₀ * b₂ ≤ C₁ := by dsimp [C₁]; linarith
    have hC₂_pos : 0 < C₂ := lt_min hc₄_pos zero_lt_one
    have hC₂_le1 : C₂ ≤ 1 := min_le_right _ _
    have hC₂_le_c₄ : C₂ ≤ c₄ := min_le_left _ _
    -- Clear values of nested let-bindings so whnf/isDefEq/linarith treat them as atomic variables
    clear_value C₂ C₁ K₀ b₂ b₃ b₁ a_peel δ₂ lam0 c₀ a a_5 b_leaf a_leaf
    let q : ℝ := 84 * C₁ ^ 2
    have hq_ge1 : 1 ≤ q := by
      dsimp [q]
      have h1 : 1 * 1 ≤ C₁ * C₁ := mul_le_mul hC₁_ge1 hC₁_ge1 zero_le_one (by linarith)
      linarith
    -- Reduce to |V| ≥ 2^q via hasPairErdosHajnalProp_of_large_card
    refine hasPairErdosHajnalProp_of_large_card H₁ H₂ hq_ge1 hC₂_pos hC₂_le1 ?_
    intro V _ _ G hG₁ hG₂ hV_large
    haveI : Nonempty V := by
      rw [← Fintype.card_pos_iff]
      have : (0 : ℝ) < (Fintype.card V : ℝ) := lt_of_lt_of_le (by positivity) hV_large
      exact_mod_cast this
    have hkappa_ge1 : (1 : ℝ) ≤ (kappa G : ℝ) := by exact_mod_cast kappa_pos_of_nonempty G
    -- Apply cograph_stage2_reduction on S₀ := Finset.univ
    have hS₀_card : ((Finset.univ : Finset V).card : ℝ) = (Fintype.card V : ℝ) := by
      rw [Finset.card_univ]
    refine hS₀_card ▸ cograph_stage2_reduction G Finset.univ C₁ C₂ hC₁_ge1 hC₂_pos hC₂_le1 ?_
      (hS₀_card.symm ▸ hV_large)
    intro x hx0 hx_half F _
    have hx_le1 : x ≤ 1 := by linarith
    -- Step 3a: Apply rodl_theorem_general to F at scale lam0
    obtain ⟨F₀, hF₀_sub, hF₀_rest, hF₀_δ₂⟩ :=
      rodl_theorem_general G H₁ᶜ hG₁ lam0 hlam0_pos hlam0_half F
    rw [hδ₂_eq] at hF₀_δ₂
    have hF₀_card : lam0 ^ b₂ * (F.card : ℝ) ≤ (F₀.card : ℝ) :=
      (mul_le_mul_of_nonneg_right hlam0_b2_le_δ₂ (Nat.cast_nonneg _)).trans hF₀_δ₂
    -- Bound x ^ (4 * K₀) ≤ lam0
    have hx_K₀ : x ^ K₀ ≤ c₀ :=
      (eps_rpow_le_two_rpow_neg hx0.le hx_half (by linarith)).trans h2_K₀
    have hx_4K₀ : x ^ (4 * K₀) ≤ lam0 := by
      rw [hlam0_eq]
      calc x ^ (4 * K₀)
        _ = (x ^ K₀) ^ (4 : ℝ) := by rw [← Real.rpow_mul hx0.le]; congr 1; ring
        _ = (x ^ K₀) ^ 4 := by rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        _ ≤ c₀ ^ 4 := pow_le_pow_left₀ (by positivity) hx_K₀ 4
    have hx_lam0_b2 : x ^ (4 * K₀ * b₂) ≤ lam0 ^ b₂ := by
      rw [Real.rpow_mul hx0.le]
      exact Real.rpow_le_rpow (by positivity) hx_4K₀ hb₂_pos.le
    by_cases hx_lt_lam0 : x < lam0
    · -- Multi-scale sparsification from lam0 down to x
      let O : Finset V → Prop := fun _ =>
        (∃ k : ℕ, 2 ≤ k ∧ ∃ B : Fin k → Finset V,
          IsPureCographBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ C₁) B) ∨
        (x ^ C₁ * (F.card : ℝ)) ^ C₂ ≤ (kappa G : ℝ)
      have hstep : ∀ lam ∈ Set.Icc x lam0, ∀ F_t ⊆ F₀,
          IsEpsRestrictedOn G F_t lam → lam ^ b₂ * (F₀.card : ℝ) ≤ (F_t.card : ℝ) →
            O F_t ∨ ∃ U ⊆ F_t, IsEpsRestrictedOn G U (lam ^ b₁) ∧
              lam ^ b₃ * (F_t.card : ℝ) ≤ (U.card : ℝ) := by
        intro lam hlam_mem F_t hFt_sub hFt_rest hFt_card
        have hlam_pos : 0 < lam := hx0.trans_le hlam_mem.1
        have hlam_le : lam ≤ lam0 := hlam_mem.2
        let y := lam / c₀
        have hy0 : 0 < y := div_pos hlam_pos hc₀_pos
        have hy_c₀3 : y ≤ c₀ ^ 3 := by
          dsimp [y]
          rw [div_le_iff₀ hc₀_pos, show c₀ ^ 3 * c₀ = lam0 by rw [hlam0_eq]; ring]
          exact hlam_le
        have hy_c₀ : y ≤ c₀ := by
          calc y ≤ c₀ ^ 3 := hy_c₀3
            _ ≤ c₀ ^ 1 := pow_le_pow_of_le_one hc₀_pos.le hc₀_le1 (by omega)
            _ = c₀ := pow_one c₀
        have hy120 : y ≤ (2 : ℝ) ^ (-120 : ℝ) := hy_c₀.trans hc₀_120
        have hy_le1 : y ≤ 1 := hy120.trans (by norm_num)
        have hlam_le_y : lam ≤ y := by
          dsimp [y]
          rw [le_div_iff₀ hc₀_pos]
          exact mul_le_of_le_one_right hlam_pos.le hc₀_le1
        have hx_le_y : x ≤ y := hlam_mem.1.trans hlam_le_y
        -- Helper to convert y ^ b₃ * |F_t| ≥ x ^ C₁ * |F| into Outcome (iii)
        have h_T1_to_O : (y ^ b₃ * (F_t.card : ℝ)) ^ c₄ ≤ (kappa G : ℝ) →
            (x ^ C₁ * (F.card : ℝ)) ^ C₂ ≤ (kappa G : ℝ) := by
          intro hT1
          have hx_C₁_le_y_b3 : x ^ C₁ * (F.card : ℝ) ≤ y ^ b₃ * (F_t.card : ℝ) := by
            have hrpow : x ^ C₁ ≤ y ^ b₃ * lam ^ b₂ * lam0 ^ b₂ := by
              have h1 : x ^ b₃ ≤ y ^ b₃ := Real.rpow_le_rpow hx0.le hx_le_y (by linarith)
              have h2 : x ^ b₂ ≤ lam ^ b₂ := Real.rpow_le_rpow hx0.le hlam_mem.1 hb₂_pos.le
              calc x ^ C₁
                _ ≤ x ^ (b₃ + b₂ + 4 * K₀ * b₂) :=
                  Real.rpow_le_rpow_of_exponent_ge hx0 hx_le1 hC₁_ge_b3_b2
                _ = x ^ b₃ * x ^ b₂ * x ^ (4 * K₀ * b₂) := by
                  rw [Real.rpow_add hx0, Real.rpow_add hx0]
                _ ≤ y ^ b₃ * lam ^ b₂ * lam0 ^ b₂ := by
                  refine mul_le_mul ?_ hx_lam0_b2 (by positivity) (by positivity)
                  exact mul_le_mul h1 h2 (by positivity) (by positivity)
            calc x ^ C₁ * (F.card : ℝ)
              _ ≤ (y ^ b₃ * lam ^ b₂ * lam0 ^ b₂) * (F.card : ℝ) :=
                mul_le_mul_of_nonneg_right hrpow (Nat.cast_nonneg _)
              _ = y ^ b₃ * (lam ^ b₂ * (lam0 ^ b₂ * (F.card : ℝ))) := by ring
              _ ≤ y ^ b₃ * (lam ^ b₂ * (F₀.card : ℝ)) := by
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                exact mul_le_mul_of_nonneg_left hF₀_card (by positivity)
              _ ≤ y ^ b₃ * (F_t.card : ℝ) :=
                mul_le_mul_of_nonneg_left hFt_card (by positivity)
          by_cases h_yb3_le1 : y ^ b₃ * (F_t.card : ℝ) ≤ 1
          · calc (x ^ C₁ * (F.card : ℝ)) ^ C₂
              _ ≤ (1 : ℝ) ^ C₂ :=
                Real.rpow_le_rpow (by positivity) (hx_C₁_le_y_b3.trans h_yb3_le1) hC₂_pos.le
              _ = 1 := Real.one_rpow C₂
              _ ≤ (kappa G : ℝ) := hkappa_ge1
          · push_neg at h_yb3_le1
            calc (x ^ C₁ * (F.card : ℝ)) ^ C₂
              _ ≤ (y ^ b₃ * (F_t.card : ℝ)) ^ C₂ :=
                Real.rpow_le_rpow (by positivity) hx_C₁_le_y_b3 hC₂_pos.le
              _ ≤ (y ^ b₃ * (F_t.card : ℝ)) ^ c₄ :=
                Real.rpow_le_rpow_of_exponent_le h_yb3_le1.le hC₂_le_c₄
              _ ≤ (kappa G : ℝ) := hT1
        -- Small F_t case: y ^ (a_peel + 2) * |F_t| < 2 -> y ^ b₃ * |F_t| ≤ 1 -> (T1)
        by_cases hw_ge2 : (2 : ℝ) ≤ y ^ (a_peel + 2) * (F_t.card : ℝ)
        · let w_y := ⌊y ^ (a_peel + 2) * (F_t.card : ℝ)⌋₊
          have hw_y_half : (1 / 2 : ℝ) * (y ^ (a_peel + 2) * (F_t.card : ℝ)) ≤ (w_y : ℝ) := by
            have := Nat.sub_one_lt_floor (y ^ (a_peel + 2) * (F_t.card : ℝ))
            linarith
          have hw_y_ge_b3 : lam ^ b₃ * (F_t.card : ℝ) ≤ (w_y : ℝ) := by
            have h2y_le1 : 2 * y ≤ 1 := by
              have : (2 : ℝ) ^ (-120 : ℝ) ≤ 1 / 2 := by norm_num
              linarith [hy120.trans this]
            have h1 : lam ^ b₃ ≤ (1 / 2 : ℝ) * y ^ (a_peel + 2) := by
              calc lam ^ b₃
                _ ≤ y ^ b₃ := Real.rpow_le_rpow hlam_pos.le hlam_le_y (by linarith)
                _ ≤ y ^ (a_peel + 3) :=
                  Real.rpow_le_rpow_of_exponent_ge hy0 hy_le1 hb₃_ge_peel
                _ = y * y ^ (a_peel + 2) := by
                  rw [show a_peel + 3 = 1 + (a_peel + 2) by ring, Real.rpow_add hy0, Real.rpow_one]
                _ ≤ (1 / 2 : ℝ) * y ^ (a_peel + 2) :=
                  mul_le_mul_of_nonneg_right (by linarith) (by positivity)
            exact (mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)).trans
              (by linarith [hw_y_half])
          -- Helper to upgrade any pure cograph blockade in F_t of arity k_F ≥ ⌈y⁻¹⌉₊ to F
          have h_upgrade_block : ∀ (k_F : ℕ) (B : Fin k_F → Finset V) (e : ℝ),
              ⌈y⁻¹⌉₊ ≤ k_F → 0 ≤ e → e + K₀ + (K₀ + 1) * b₂ + 4 * K₀ * b₂ ≤ C₁ →
              IsPureCographBlockadeIn G F_t k_F (c₀ * y ^ e * (F_t.card : ℝ)) B →
              O F_t := by
            intro k_F B e hk_ge_y he0 hexp_C₁ hB
            left
            have hy_inv2 : (2 : ℝ) < y⁻¹ := by
              rw [lt_inv_comm₀ zero_lt_two hy0]
              exact hy120.trans_lt (by norm_num)
            have hk_ge_inv : y⁻¹ ≤ (k_F : ℝ) :=
              (Nat.le_ceil _).trans (by exact_mod_cast hk_ge_y)
            have hk2 : 2 ≤ k_F := by
              have : (2 : ℝ) < (k_F : ℝ) := hy_inv2.trans_le hk_ge_inv
              exact_mod_cast this.le
            have hk2_real : (2 : ℝ) ≤ (k_F : ℝ) := by exact_mod_cast hk2
            have hk1 : (1 : ℝ) ≤ (k_F : ℝ) := by linarith
            have hk_pos : (0 : ℝ) < (k_F : ℝ) := by linarith
            have hy_ge_k : (k_F : ℝ) ^ (-1 : ℝ) ≤ y := by
              rw [Real.rpow_neg_one, ← inv_inv y]
              exact inv_anti₀ (inv_pos.mpr hy0) hk_ge_inv
            have hc₀_ge_k : (k_F : ℝ) ^ (-K₀) ≤ c₀ :=
              (rpow_neg_le_two_rpow_neg hk2_real (by linarith)).trans h2_K₀
            have hlam_ge_k : (k_F : ℝ) ^ (-(K₀ + 1)) ≤ lam := by
              have hlam_eq : lam = c₀ * y := by dsimp [y]; rw [mul_div_cancel₀ _ hc₀_pos.ne']
              rw [hlam_eq, show -(K₀ + 1) = -K₀ + -1 by ring, Real.rpow_add hk_pos]
              exact mul_le_mul hc₀_ge_k hy_ge_k (by positivity) (by positivity)
            have hlam0_ge_k : (k_F : ℝ) ^ (-(4 * K₀)) ≤ lam0 := by
              rw [hlam0_eq]
              calc (k_F : ℝ) ^ (-(4 * K₀))
                _ = ((k_F : ℝ) ^ (-K₀)) ^ (4 : ℝ) := by
                  rw [← Real.rpow_mul hk_pos.le]; congr 1; ring
                _ = ((k_F : ℝ) ^ (-K₀)) ^ 4 := by
                  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
                _ ≤ c₀ ^ 4 := pow_le_pow_left₀ (by positivity) hc₀_ge_k 4
            have hye_ge_k : (k_F : ℝ) ^ (-e) ≤ y ^ e := by
              calc (k_F : ℝ) ^ (-e)
                _ = ((k_F : ℝ) ^ (-1 : ℝ)) ^ e := by
                  rw [← Real.rpow_mul hk_pos.le]; congr 1; ring
                _ ≤ y ^ e := Real.rpow_le_rpow (by positivity) hy_ge_k he0
            have hlam_b2 : (k_F : ℝ) ^ (-((K₀ + 1) * b₂)) ≤ lam ^ b₂ := by
              rw [show -((K₀ + 1) * b₂) = -(K₀ + 1) * b₂ by ring, Real.rpow_mul hk_pos.le]
              exact Real.rpow_le_rpow (by positivity) hlam_ge_k hb₂_pos.le
            have hlam0_b2 : (k_F : ℝ) ^ (-(4 * K₀ * b₂)) ≤ lam0 ^ b₂ := by
              rw [show -(4 * K₀ * b₂) = -(4 * K₀) * b₂ by ring, Real.rpow_mul hk_pos.le]
              exact Real.rpow_le_rpow (by positivity) hlam0_ge_k hb₂_pos.le
            have hk_C₁ : (k_F : ℝ) ^ (-C₁) ≤ c₀ * y ^ e * lam ^ b₂ * lam0 ^ b₂ := by
              calc (k_F : ℝ) ^ (-C₁)
                _ ≤ (k_F : ℝ) ^ (-(e + K₀ + (K₀ + 1) * b₂ + 4 * K₀ * b₂)) :=
                  Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)
                _ = (k_F : ℝ) ^ (-K₀) * (k_F : ℝ) ^ (-e) *
                    (k_F : ℝ) ^ (-((K₀ + 1) * b₂)) * (k_F : ℝ) ^ (-(4 * K₀ * b₂)) := by
                  rw [show -(e + K₀ + (K₀ + 1) * b₂ + 4 * K₀ * b₂) =
                    -K₀ + -e + -((K₀ + 1) * b₂) + -(4 * K₀ * b₂) by ring,
                    Real.rpow_add hk_pos, Real.rpow_add hk_pos, Real.rpow_add hk_pos]
                _ ≤ c₀ * y ^ e * lam ^ b₂ * lam0 ^ b₂ := by
                  refine mul_le_mul ?_ hlam0_b2 (by positivity) (by positivity)
                  refine mul_le_mul ?_ hlam_b2 (by positivity) (by positivity)
                  exact mul_le_mul hc₀_ge_k hye_ge_k (by positivity) (by positivity)
            have hw_F : (F.card : ℝ) / (k_F : ℝ) ^ C₁ ≤ c₀ * y ^ e * (F_t.card : ℝ) := by
              rw [div_eq_mul_inv, ← Real.rpow_neg hk_pos.le, mul_comm]
              calc (k_F : ℝ) ^ (-C₁) * (F.card : ℝ)
                _ ≤ (c₀ * y ^ e * lam ^ b₂ * lam0 ^ b₂) * (F.card : ℝ) :=
                  mul_le_mul_of_nonneg_right hk_C₁ (Nat.cast_nonneg _)
                _ = c₀ * y ^ e * (lam ^ b₂ * (lam0 ^ b₂ * (F.card : ℝ))) := by ring
                _ ≤ c₀ * y ^ e * (lam ^ b₂ * (F₀.card : ℝ)) := by
                  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                  exact mul_le_mul_of_nonneg_left hF₀_card (by positivity)
                _ ≤ c₀ * y ^ e * (F_t.card : ℝ) :=
                  mul_le_mul_of_nonneg_left hFt_card (by positivity)
            exact ⟨k_F, hk2, B, hB.mono_ambient_width (hFt_sub.trans hF₀_sub) hw_F⟩
          -- Check if every F' ⊆ F_t (2^(-4 a_5) |F_t| ≤ |F'|) satisfies (R4)
          by_cases hall_R4 : ∀ F' ⊆ F_t, (2 : ℝ) ^ (-4 * a_5) * (F_t.card : ℝ) ≤ (F'.card : ℝ) →
              ∃ X ⊆ F', ∃ Y ⊆ F', Disjoint X Y ∧
                (1 - a_5 * y) * (F'.card : ℝ) ≤ (Y.card : ℝ) ∧
                ((X.card = w_y ∧ (IsCompletePair G X Y ∨ IsXSparseTo G Y X 0)) ∨
                 (y ^ a_peel * (F'.card : ℝ) ≤ (X.card : ℝ) ∧ IsPurePair G X Y))
          · -- Lemma 4(1) at x = 0 produces IsPureCographBlockadeIn G F_t ⌈y⁻¹⌉₊ w_y B
            left
            have hy_4a5 : y ≤ (2 : ℝ) ^ (-4 * a_5) :=
              hy_c₀.trans (hc₀_8a5.trans
                (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)))
            obtain ⟨B, _, _, _, _, _, _, hB_pure_fn⟩ :=
              equal_sized_trigger_peeling_cograph G F_t a_peel a_5 y 0
                (by linarith) (by linarith) le_rfl hy0 hy_4a5 (by linarith) hall_R4
            have hB_pure := hB_pure_fn rfl
            have hw_c₀ : c₀ * y ^ (a_peel + 2) * (F_t.card : ℝ) ≤ (w_y : ℝ) := by
              have hc₀_half : c₀ ≤ 1 / 2 := hc₀_120.trans (by norm_num)
              calc c₀ * y ^ (a_peel + 2) * (F_t.card : ℝ)
                _ = c₀ * (y ^ (a_peel + 2) * (F_t.card : ℝ)) := by ring
                _ ≤ (1 / 2 : ℝ) * (y ^ (a_peel + 2) * (F_t.card : ℝ)) :=
                  mul_le_mul_of_nonneg_right hc₀_half (by positivity)
                _ ≤ (w_y : ℝ) := hw_y_half
            exact h_upgrade_block ⌈y⁻¹⌉₊ B (a_peel + 2) le_rfl (by linarith) hC₁_ge_peel
              (hB_pure.mono_ambient_width Subset.rfl hw_c₀)
          · -- Some F' ⊆ F_t fails (R4)
            push_neg at hall_R4
            obtain ⟨F', hF'_sub, hF'_4a5, hF'_no_R4⟩ := hall_R4
            have hc₀_le_4a5 : c₀ ≤ (2 : ℝ) ^ (-4 * a_5) :=
              hc₀_8a5.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
            have hF'_c₀ : c₀ * (F_t.card : ℝ) ≤ (F'.card : ℝ) :=
              (mul_le_mul_of_nonneg_right hc₀_le_4a5 (Nat.cast_nonneg _)).trans hF'_4a5
            have hF'_rest : IsEpsRestrictedOn G F' y :=
              stage2_step2_restricted_sub_of_subset G F_t F' lam c₀
                hlam_pos.le hc₀_pos hF'_sub hF'_c₀ hFt_rest
            have h2y2_le_b1 : 2 * y ^ 2 ≤ lam ^ b₁ := by
              dsimp [y]; rw [hb₁_eq]
              exact two_mul_y_sq_le_lam_b1 hc₀_pos hc₀_120 hlam_pos.le (hlam0_eq ▸ hlam_le)
            rcases hF'_rest with hF'_sparse | hF'_cosparse
            · -- Branch 2: F' is y-sparse in G -> stage2_step2_branch2_gn
              rcases stage2_step2_branch2_gn H₁ H₂ v₀ u₀ hu₀_ne hleaf hh hd' hviral_prop
                  hc₂4 hc₆1 hc₇1 hc₇_le hGN ha_thr7 hwond_prop G hG₁ hG₂ hF'_sub
                  hy0 hy_c₀ hc₀_pos hc₀_thr hc₀_120 ha_thr_le ha20 ha_4h ha_dh
                  ha_peel_c₁ ha_peel_c₈ ha_peel_4a (by linarith : 4 ≤ a_5) hb₃_ge
                  hF'_c₀ hw_ge2 hF'_sparse with
                hT1 | ⟨U, hUF', hU_rest, hU_card⟩ | ⟨k_F, hk_ge_y, B, hB⟩ |
                ⟨X, hXF', Y, hYF', hdisj_XY, hX_card, hY_card, hpure_XY⟩
              · exact Or.inl (Or.inr (h_T1_to_O hT1))
              · exact Or.inr ⟨U, hUF'.trans hF'_sub, hU_rest.mono h2y2_le_b1,
                  hw_y_ge_b3.trans hU_card⟩
              · left
                -- Upgrade hB : IsPureCographBlockadeIn G F_t k_F (c₀ * |F_t| / k_F^c₅) B to F
                have hk_ge_inv : y⁻¹ ≤ (k_F : ℝ) :=
                  (Nat.le_ceil _).trans (by exact_mod_cast hk_ge_y)
                have hy_inv2 : (2 : ℝ) < y⁻¹ := by
                  rw [lt_inv_comm₀ zero_lt_two hy0]
                  exact hy120.trans_lt (by norm_num)
                have hk2 : 2 ≤ k_F := by
                  have : (2 : ℝ) < (k_F : ℝ) := hy_inv2.trans_le hk_ge_inv
                  exact_mod_cast this.le
                have hk2_real : (2 : ℝ) ≤ (k_F : ℝ) := by exact_mod_cast hk2
                have hk1 : (1 : ℝ) ≤ (k_F : ℝ) := by linarith
                have hk_pos : (0 : ℝ) < (k_F : ℝ) := by linarith
                have hy_ge_k : (k_F : ℝ) ^ (-1 : ℝ) ≤ y := by
                  rw [Real.rpow_neg_one, ← inv_inv y]
                  exact inv_anti₀ (inv_pos.mpr hy0) hk_ge_inv
                have hc₀_ge_k : (k_F : ℝ) ^ (-K₀) ≤ c₀ :=
                  (rpow_neg_le_two_rpow_neg hk2_real (by linarith)).trans h2_K₀
                have hlam_ge_k : (k_F : ℝ) ^ (-(K₀ + 1)) ≤ lam := by
                  have hlam_eq : lam = c₀ * y := by dsimp [y]; rw [mul_div_cancel₀ _ hc₀_pos.ne']
                  rw [hlam_eq, show -(K₀ + 1) = -K₀ + -1 by ring, Real.rpow_add hk_pos]
                  exact mul_le_mul hc₀_ge_k hy_ge_k (by positivity) (by positivity)
                have hlam0_ge_k : (k_F : ℝ) ^ (-(4 * K₀)) ≤ lam0 := by
                  rw [hlam0_eq]
                  calc (k_F : ℝ) ^ (-(4 * K₀))
                    _ = ((k_F : ℝ) ^ (-K₀)) ^ (4 : ℝ) := by
                      rw [← Real.rpow_mul hk_pos.le]; congr 1; ring
                    _ = ((k_F : ℝ) ^ (-K₀)) ^ 4 := by
                      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
                    _ ≤ c₀ ^ 4 := pow_le_pow_left₀ (by positivity) hc₀_ge_k 4
                have hlam_b2 : (k_F : ℝ) ^ (-((K₀ + 1) * b₂)) ≤ lam ^ b₂ := by
                  rw [show -((K₀ + 1) * b₂) = -(K₀ + 1) * b₂ by ring, Real.rpow_mul hk_pos.le]
                  exact Real.rpow_le_rpow (by positivity) hlam_ge_k hb₂_pos.le
                have hlam0_b2 : (k_F : ℝ) ^ (-(4 * K₀ * b₂)) ≤ lam0 ^ b₂ := by
                  rw [show -(4 * K₀ * b₂) = -(4 * K₀) * b₂ by ring, Real.rpow_mul hk_pos.le]
                  exact Real.rpow_le_rpow (by positivity) hlam0_ge_k hb₂_pos.le
                have hk_C₁ : (k_F : ℝ) ^ (-C₁) ≤
                    (k_F : ℝ) ^ (-c₅) * c₀ * lam ^ b₂ * lam0 ^ b₂ := by
                  calc (k_F : ℝ) ^ (-C₁)
                    _ ≤ (k_F : ℝ) ^ (-(c₅ + K₀ + (K₀ + 1) * b₂ + 4 * K₀ * b₂)) :=
                      Real.rpow_le_rpow_of_exponent_le hk1 (by linarith [hC₁_ge_c5])
                    _ = (k_F : ℝ) ^ (-c₅) * (k_F : ℝ) ^ (-K₀) *
                        (k_F : ℝ) ^ (-((K₀ + 1) * b₂)) * (k_F : ℝ) ^ (-(4 * K₀ * b₂)) := by
                      rw [show -(c₅ + K₀ + (K₀ + 1) * b₂ + 4 * K₀ * b₂) =
                        -c₅ + -K₀ + -((K₀ + 1) * b₂) + -(4 * K₀ * b₂) by ring,
                        Real.rpow_add hk_pos, Real.rpow_add hk_pos, Real.rpow_add hk_pos]
                    _ ≤ (k_F : ℝ) ^ (-c₅) * c₀ * lam ^ b₂ * lam0 ^ b₂ := by
                      refine mul_le_mul ?_ hlam0_b2 (by positivity) (by positivity)
                      refine mul_le_mul ?_ hlam_b2 (by positivity) (by positivity)
                      exact mul_le_mul_of_nonneg_left hc₀_ge_k (by positivity)
                have hw_F : (F.card : ℝ) / (k_F : ℝ) ^ C₁ ≤
                    c₀ * (F_t.card : ℝ) / (k_F : ℝ) ^ c₅ := by
                  rw [div_eq_mul_inv, div_eq_mul_inv, ← Real.rpow_neg hk_pos.le,
                    ← Real.rpow_neg hk_pos.le, mul_comm (F.card : ℝ),
                    mul_comm (c₀ * (F_t.card : ℝ))]
                  calc (k_F : ℝ) ^ (-C₁) * (F.card : ℝ)
                    _ ≤ ((k_F : ℝ) ^ (-c₅) * c₀ * lam ^ b₂ * lam0 ^ b₂) * (F.card : ℝ) :=
                      mul_le_mul_of_nonneg_right hk_C₁ (Nat.cast_nonneg _)
                    _ = (k_F : ℝ) ^ (-c₅) * (c₀ * (lam ^ b₂ *
                        (lam0 ^ b₂ * (F.card : ℝ)))) := by ring
                    _ ≤ (k_F : ℝ) ^ (-c₅) * (c₀ * (lam ^ b₂ * (F₀.card : ℝ))) := by
                      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                      refine mul_le_mul_of_nonneg_left ?_ hc₀_pos.le
                      exact mul_le_mul_of_nonneg_left hF₀_card (by positivity)
                    _ ≤ (k_F : ℝ) ^ (-c₅) * (c₀ * (F_t.card : ℝ)) := by
                      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                      exact mul_le_mul_of_nonneg_left hFt_card hc₀_pos.le
                exact Or.inl ⟨k_F, hk2, B,
                  hB.mono_ambient_width (hFt_sub.trans hF₀_sub) hw_F⟩
              · exfalso
                rcases hpure_XY with hcomp | hanti
                · exact ((hF'_no_R4 X hXF' Y hYF' hdisj_XY hY_card).1 hX_card).1 hcomp
                · have hsp0 : IsXSparseTo G Y X 0 := by
                    intro u hu
                    have hemp : neighborFinsetIn G u X = ∅ := by
                      rw [eq_empty_iff_forall_notMem]
                      intro v hv
                      rw [mem_neighborFinsetIn'] at hv
                      exact hanti v hv.1 u hu (G.symm hv.2)
                    rw [hemp]; simp
                  exact ((hF'_no_R4 X hXF' Y hYF' hdisj_XY hY_card).1 hX_card).2 hsp0
            · -- Branch 1: F' is y-co-sparse in G -> leaf_reducible_cosparse_trigger_or_restricted
              have hy_half : y < 1 / 2 := hy120.trans_lt (by norm_num)
              have hy_F'_ge1 : 1 ≤ y * (F'.card : ℝ) := by
                have hy_a_le : y ^ (a_peel + 2) ≤ y * c₀ := by
                  calc y ^ (a_peel + 2)
                    _ ≤ y ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hy0 hy_le1 (by linarith)
                    _ = y * y := by rw [Real.rpow_two]; ring
                    _ ≤ y * c₀ := mul_le_mul_of_nonneg_left hy_c₀ hy0.le
                calc (1 : ℝ) ≤ 2 := by norm_num
                  _ ≤ y ^ (a_peel + 2) * (F_t.card : ℝ) := hw_ge2
                  _ ≤ (y * c₀) * (F_t.card : ℝ) :=
                    mul_le_mul_of_nonneg_right hy_a_le (Nat.cast_nonneg _)
                  _ = y * (c₀ * (F_t.card : ℝ)) := by ring
                  _ ≤ y * (F'.card : ℝ) := mul_le_mul_of_nonneg_left hF'_c₀ hy0.le
              have hF'_ne : F'.Nonempty := by
                rw [← card_pos]
                have hpos : (0 : ℝ) < y * (F'.card : ℝ) := lt_of_lt_of_le zero_lt_one hy_F'_ge1
                have : (0 : ℝ) < (F'.card : ℝ) := pos_of_mul_pos_right hpos hy0.le
                exact_mod_cast this
              rcases leaf_reducible_cosparse_trigger_or_restricted H₁ H₂ v₀ u₀ hu₀_ne hleaf hh hd'
                  hviral_prop G hG₁ hG₂ F' hF'_ne y hy0 hy_half hy_F'_ge1 hF'_cosparse with
                ⟨U, hUF', hU_rest, hU_card⟩ |
                ⟨X₀, hX₀F', Y, hYF', hdisj_X₀Y, hX₀_card, hY_card, hcomp_X₀Y⟩
              · -- (R2)
                right
                have hy4_le_b1 : y ^ 4 ≤ lam ^ b₁ := by
                  have hy4_le_2y2 : y ^ 4 ≤ 2 * y ^ 2 := by
                    have h1 : y ^ 4 ≤ y ^ 2 := pow_le_pow_of_le_one hy0.le hy_le1 (by omega)
                    have h2 : 1 * y ^ 2 ≤ 2 * y ^ 2 := mul_le_mul_of_nonneg_right one_le_two (sq_nonneg y)
                    rw [one_mul] at h2
                    exact h1.trans h2
                  exact hy4_le_2y2.trans h2y2_le_b1
                have hw_le_U : (w_y : ℝ) ≤ (U.card : ℝ) := by
                  have h1 : y ^ (a_peel + 2) ≤ y ^ (4 * d' + 1) * c₀ := by
                    have hexp : 4 * d' + 2 ≤ a_peel + 2 := by
                      have : 4 * d' * 1 ≤ 4 * d' * (h : ℝ) :=
                        mul_le_mul_of_nonneg_left (by linarith [hh_real]) (by positivity)
                      linarith [ha_peel_4dh]
                    calc y ^ (a_peel + 2)
                      _ ≤ y ^ (4 * d' + 2) := Real.rpow_le_rpow_of_exponent_ge hy0 hy_le1 hexp
                      _ = y ^ (4 * d' + 1) * y := by
                        rw [show 4 * d' + 2 = (4 * d' + 1) + 1 by ring, Real.rpow_add_one hy0.ne']
                      _ ≤ y ^ (4 * d' + 1) * c₀ :=
                        mul_le_mul_of_nonneg_left hy_c₀ (by positivity)
                  calc (w_y : ℝ)
                    _ ≤ y ^ (a_peel + 2) * (F_t.card : ℝ) := Nat.floor_le (by positivity)
                    _ ≤ (y ^ (4 * d' + 1) * c₀) * (F_t.card : ℝ) :=
                      mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)
                    _ = y ^ (4 * d' + 1) * (c₀ * (F_t.card : ℝ)) := by ring
                    _ ≤ y ^ (4 * d' + 1) * (F'.card : ℝ) :=
                      mul_le_mul_of_nonneg_left hF'_c₀ (by positivity)
                    _ ≤ (U.card : ℝ) := hU_card
                exact ⟨U, hUF'.trans hF'_sub, hU_rest.mono hy4_le_b1, hw_y_ge_b3.trans hw_le_U⟩
              · -- (R4) contradicts hF'_no_R4
                exfalso
                have hw_le_X₀ : w_y ≤ X₀.card := by
                  have hsub : ((h - 1 : ℕ) : ℝ) ≤ (h : ℝ) := by exact_mod_cast Nat.sub_le h 1
                  have h1 : y ^ (a_peel + 2) ≤
                      y ^ (4 * d' * ((h - 1 : ℕ) : ℝ) + 1) * c₀ := by
                    have hexp : 4 * d' * ((h - 1 : ℕ) : ℝ) + 2 ≤ a_peel + 2 := by
                      have : 4 * d' * ((h - 1 : ℕ) : ℝ) ≤ 4 * d' * (h : ℝ) :=
                        mul_le_mul_of_nonneg_left hsub (by positivity)
                      linarith [ha_peel_4dh]
                    calc y ^ (a_peel + 2)
                      _ ≤ y ^ (4 * d' * ((h - 1 : ℕ) : ℝ) + 2) :=
                        Real.rpow_le_rpow_of_exponent_ge hy0 hy_le1 hexp
                      _ = y ^ (4 * d' * ((h - 1 : ℕ) : ℝ) + 1) * y := by
                        rw [show 4 * d' * ((h - 1 : ℕ) : ℝ) + 2 =
                          (4 * d' * ((h - 1 : ℕ) : ℝ) + 1) + 1 by ring, Real.rpow_add_one hy0.ne']
                      _ ≤ y ^ (4 * d' * ((h - 1 : ℕ) : ℝ) + 1) * c₀ :=
                        mul_le_mul_of_nonneg_left hy_c₀ (by positivity)
                  have hreal : (w_y : ℝ) ≤ (X₀.card : ℝ) := by
                    calc (w_y : ℝ)
                      _ ≤ y ^ (a_peel + 2) * (F_t.card : ℝ) := Nat.floor_le (by positivity)
                      _ ≤ (y ^ (4 * d' * ((h - 1 : ℕ) : ℝ) + 1) * c₀) * (F_t.card : ℝ) :=
                        mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)
                      _ = y ^ (4 * d' * ((h - 1 : ℕ) : ℝ) + 1) * (c₀ * (F_t.card : ℝ)) := by ring
                      _ ≤ y ^ (4 * d' * ((h - 1 : ℕ) : ℝ) + 1) * (F'.card : ℝ) :=
                        mul_le_mul_of_nonneg_left hF'_c₀ (by positivity)
                      _ ≤ (X₀.card : ℝ) := hX₀_card.le
                  exact_mod_cast hreal
                obtain ⟨X, hXX₀, hX_card⟩ := exists_subset_card_eq hw_le_X₀
                have hY_a5 : (1 - a_5 * y) * (F'.card : ℝ) ≤ (Y.card : ℝ) := by
                  have h1 : (1 - a_5 * y) * (F'.card : ℝ) ≤ (1 - (h : ℝ) * y) * (F'.card : ℝ) := by
                    refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
                    exact sub_le_sub_left (mul_le_mul_of_nonneg_right ha_5_ge_h hy0.le) 1
                  exact h1.trans hY_card
                exact ((hF'_no_R4 X (hXX₀.trans hX₀F') Y hYF'
                  (Disjoint.mono_left hXX₀ hdisj_X₀Y) hY_a5).1 hX_card).1
                  (isCompletePair_mono hXX₀ Subset.rfl hcomp_X₀Y)
        · -- Small F_t: y ^ (a_peel + 2) * |F_t| < 2 -> y ^ b₃ * |F_t| ≤ 1 -> (T1)
          left; right
          push_neg at hw_ge2
          have h2y_le1 : 2 * y ≤ 1 := by
            have : (2 : ℝ) ^ (-120 : ℝ) ≤ 1 / 2 := by norm_num
            linarith [hy120.trans this]
          have hy_b3_Ft : y ^ b₃ * (F_t.card : ℝ) ≤ 1 := by
            have h1 : y ^ b₃ ≤ y * y ^ (a_peel + 2) := by
              calc y ^ b₃
                _ ≤ y ^ (a_peel + 3) :=
                  Real.rpow_le_rpow_of_exponent_ge hy0 hy_le1 hb₃_ge_peel
                _ = y * y ^ (a_peel + 2) := by
                  rw [show a_peel + 3 = 1 + (a_peel + 2) by ring, Real.rpow_add hy0, Real.rpow_one]
            calc y ^ b₃ * (F_t.card : ℝ)
              _ ≤ (y * y ^ (a_peel + 2)) * (F_t.card : ℝ) :=
                mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)
              _ = y * (y ^ (a_peel + 2) * (F_t.card : ℝ)) := by ring
              _ ≤ y * 2 := mul_le_mul_of_nonneg_left hw_ge2.le hy0.le
              _ ≤ 1 := by linarith
          apply h_T1_to_O
          calc (y ^ b₃ * (F_t.card : ℝ)) ^ c₄
            _ ≤ (1 : ℝ) ^ c₄ := Real.rpow_le_rpow (by positivity) hy_b3_Ft hc₄_pos.le
            _ = 1 := Real.one_rpow c₄
            _ ≤ (kappa G : ℝ) := hkappa_ge1
      rcases lem_multiscale_sparsification G F₀ O hlam0_pos hlam0_half hx0 hx_lt_lam0
          hb₁_gt1 hb₂_pos (by linarith : 0 < b₃) hb₁_b₂_ge_b₃
          hF₀_rest hstep with
        ⟨_, _, hO⟩ | ⟨S_x, hS_sub, hS_rest, hS_card⟩
      · exact Or.inr hO
      · left
        refine ⟨S_x, hS_sub.trans hF₀_sub, hS_rest, ?_⟩
        have hrpow : x ^ C₁ ≤ x ^ (b₁ * b₂) * lam0 ^ b₂ := by
          calc x ^ C₁
            _ ≤ x ^ (b₁ * b₂ + 4 * K₀ * b₂) :=
              Real.rpow_le_rpow_of_exponent_ge hx0 hx_le1 hC₁_ge_b1_b2
            _ = x ^ (b₁ * b₂) * x ^ (4 * K₀ * b₂) := Real.rpow_add hx0 _ _
            _ ≤ x ^ (b₁ * b₂) * lam0 ^ b₂ :=
              mul_le_mul_of_nonneg_left hx_lam0_b2 (by positivity)
        calc x ^ C₁ * (F.card : ℝ)
          _ ≤ (x ^ (b₁ * b₂) * lam0 ^ b₂) * (F.card : ℝ) :=
            mul_le_mul_of_nonneg_right hrpow (Nat.cast_nonneg _)
          _ = x ^ (b₁ * b₂) * (lam0 ^ b₂ * (F.card : ℝ)) := by ring
          _ ≤ x ^ (b₁ * b₂) * (F₀.card : ℝ) :=
            mul_le_mul_of_nonneg_left hF₀_card (by positivity)
          _ ≤ (S_x.card : ℝ) := hS_card
    · -- lam0 ≤ x -> F₀ itself is x-restricted with |F₀| ≥ x ^ C₁ * |F|
      push_neg at hx_lt_lam0
      left
      refine ⟨F₀, hF₀_sub, hF₀_rest.mono hx_lt_lam0, ?_⟩
      have hrpow : x ^ C₁ ≤ lam0 ^ b₂ := by
        calc x ^ C₁
          _ ≤ x ^ (4 * K₀ * b₂) :=
            Real.rpow_le_rpow_of_exponent_ge hx0 hx_le1 hC₁_ge_4K0_b2
          _ ≤ lam0 ^ b₂ := hx_lam0_b2
      exact (mul_le_mul_of_nonneg_right hrpow (Nat.cast_nonneg _)).trans hF₀_card
  exact ⟨h_compl, h_compl.of_compl⟩

/--
**Single-Graph Master Stage-2 Reduction (`master_stage2_eh_of_coupled_gen_nice_and_wonderful`,
Lemma 7(2) of `main.tex`, lines 295 and 333–412)**:
Let $H$ (`SimpleGraph W`, $|W| \ge 3$) be a finite graph with a degree-$1$ leaf $v_0 \in W$ and unique
neighbor $u_0 \neq v_0$ such that:
1. the leaf-reduced complement $(H - v_0)ᶜ$ is viral (`IsViral`);
2. $H$ satisfies open-interval thresholded wonderfulness (`IsThresholdedWonderful H`); and
3. $\{H, H\}$ satisfies coupled Stage-1 generalized niceness
   (`SatisfiesPairCoupledGenNiceAt H H c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉` with $c_2 \ge 4$, $c_6 \ge 1$,
   $c_7 \ge 1$, and $c_7 \le 3 c_2$).
Then both $Hᶜ$ and $H$ satisfy the Erdős–Hajnal property (`HasErdosHajnalProp`).
-/
theorem master_stage2_eh_of_coupled_gen_nice_and_wonderful
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W)
    (v₀ u₀ : W) (hu₀_ne : u₀ ≠ v₀)
    (hleaf : ∀ w : W, H.Adj v₀ w ↔ w = u₀)
    (hh : 3 ≤ Fintype.card W)
    (hviral : IsViral (H.comap (Subtype.val : {w : W // w ≠ v₀} → W))ᶜ)
    (hwond : IsThresholdedWonderful H)
    {c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ : ℝ}
    (hc₂4 : 4 ≤ c₂) (hc₆1 : 1 ≤ c₆) (hc₇1 : 1 ≤ c₇) (hc₇_le : c₇ ≤ 3 * c₂)
    (hGN : SatisfiesPairCoupledGenNiceAt H H c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉) :
    HasErdosHajnalProp Hᶜ ∧ HasErdosHajnalProp H := by
  have hpair_viral : IsPairViral (H.comap (Subtype.val : {w : W // w ≠ v₀} → W))ᶜ Hᶜ := by
    obtain ⟨d', hd', hv⟩ := hviral
    exact ⟨d', hd', fun V _ _ G ε hε0 hε_half hc1 _ => hv V G ε hε0 hε_half hc1⟩
  obtain ⟨hpair_compl, hpair⟩ :=
    master_stage2_pair_eh_of_coupled_gen_nice_and_wonderful H H v₀ u₀ hu₀_ne hleaf hh
      hpair_viral hwond.to_pair hc₂4 hc₆1 hc₇1 hc₇_le hGN
  exact ⟨hasErdosHajnalProp_of_pair hpair_compl, hasErdosHajnalProp_of_pair hpair⟩

/-! ### Axiom Verification Checks -/

#print axioms pkCompl_free_cosparse_complete_blockade
#print axioms pkCompl_free_cosparse_trigger_pair
#print axioms equal_sized_trigger_peeling_cograph
#print axioms seinsche_cograph_clique_mul_indep
#print axioms defective_cograph_refinement
#print axioms symmetric_layout_refinement_xsp_indep
#print axioms pair_coupled_generalized_nice_of_comb_dichotomy
#print axioms coupled_generalized_nice_of_comb_dichotomy
#print axioms master_stage2_pair_eh_of_coupled_gen_nice_and_wonderful
#print axioms master_stage2_eh_of_coupled_gen_nice_and_wonderful

end ErdosHajnalGen
