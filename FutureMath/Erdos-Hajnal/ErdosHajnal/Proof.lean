/-
Copyright 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosHajnal.AllPathsDefs
import ErdosHajnal.BasicLemmas
import ErdosHajnal.BirdBroomsForestsAndTowers
import ErdosHajnal.CombModules
import ErdosHajnal.Defs
import ErdosHajnal.GallaiAndCombDichotomy
import ErdosHajnal.GenDefs
import ErdosHajnal.LayoutAndSparsification
import ErdosHajnal.P6Baseline
import ErdosHajnal.P9BaselineProof
import ErdosHajnal.RecursiveGallaiAndStage1
import ErdosHajnal.SmallTreesAndInfiniteTowers
import ErdosHajnal.SpidersAndBirdsStage1
import ErdosHajnal.SpidersAndBirdsStage1Dichotomy
import ErdosHajnal.SpidersAndBirdsStage1Escape
import ErdosHajnal.SpidersAndBirdsWitnesses
import ErdosHajnal.Stage2Reduction
import ErdosHajnal.Stage2Witnesses
import ErdosHajnal.SymmetricStage12Interface
import ErdosHajnal.UniversalTerminalPathAndAllPaths
import ErdosHajnal.ViralityAndClosures
import ErdosHajnal.WitnessGraph

/-!
# Unconditional Resolution of All Main Theorems (`Proof.lean`, Synthesizing `main.tex`)

This file synthesizes the first-principles proof modules across Stages 1 and 2 to prove every
theorem stated in `Problem.lean` (`Erdos61.*`) unconditionally from Mathlib + standard Lean 4 axioms
with zero `sorry`s, zero custom axioms, and zero hardcoding.
-/

open Filter Finset SimpleGraph Real ErdosHajnalP6 ErdosHajnalGen

namespace Erdos61

private lemma card_neighborFinset_le_one_of_adj_iff {W : Type} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (v₀ w₀ : W)
    (h_adj : ∀ w : W, H.Adj v₀ w ↔ w = w₀) :
    (neighborFinsetIn H v₀ Finset.univ).card ≤ 1 := by
  have hsub : neighborFinsetIn H v₀ Finset.univ ⊆ {w₀} := by
    intro w hw
    rw [mem_neighborFinsetIn] at hw
    exact Finset.mem_singleton.mpr ((h_adj w).mp hw.2)
  exact le_trans (Finset.card_le_card hsub) (by simp)

/-- Unconditional single-graph Erdős–Hajnal, complement EH, polynomial Rödl, and virality for
every subdivided spider `SpiderGraph d` ($d \ge 2$). -/
theorem hasErdosHajnalProp_spiderGraph_all :
    ∀ d : ℕ, 2 ≤ d →
      HasErdosHajnalProp (SpiderGraph d) ∧
      HasErdosHajnalProp (SpiderGraph d)ᶜ ∧
      HasPolyRodlProp (SpiderGraph d) ∧
      IsViral (SpiderGraph d) := by
  intro d hd
  have hEH : ∀ m : ℕ, 2 ≤ m → HasErdosHajnalProp (SpiderGraph m) := by
    intro m hm
    induction m using Nat.strongRecOn with
    | ind m ihm =>
      obtain ⟨hleaf, _, hviral⟩ := spiderGraph_leaf_reducible m hm
      obtain ⟨c₁, c₂, c₃, c₄, c₅, c₆, c₇, c₈, c₉, hc₂, hc₆, hc₇, hc₇₂, hGN⟩ :=
        exists_satisfiesPairCoupledGenNiceAt_spiderGraph m hm
      have h_wond : IsThresholdedWonderful (SpiderGraph m) := by
        by_cases hm2 : m = 2
        · exact spiderGraph_isThresholdedWonderful_of_prev m hm (Or.inl hm2)
        · exact spiderGraph_isThresholdedWonderful_of_prev m hm
            (Or.inr (ihm (m - 1) (by omega) (by omega)))
      exact (master_stage2_eh_of_coupled_gen_nice_and_wonderful
        (SpiderGraph m) ⟨1, by omega⟩ ⟨0, by omega⟩
        (by intro h; have hv : (0 : ℕ) = 1 := congrArg Fin.val h; omega)
        hleaf (by rw [Fintype.card_fin]; omega) hviral h_wond
        hc₂ hc₆ hc₇ hc₇₂ hGN).2
  have hd_eh : HasErdosHajnalProp (SpiderGraph d) := hEH d hd
  exact ⟨hd_eh, hd_eh.compl,
    (eh_iff_polyRodl_iff_isViral (SpiderGraph d)).1.mp hd_eh,
    (eh_iff_polyRodl_iff_isViral (SpiderGraph d)).2.mp
      ((eh_iff_polyRodl_iff_isViral (SpiderGraph d)).1.mp hd_eh)⟩

/-- Unconditional Stage-2 Thresholded Wonderfulness for every subdivided spider `SpiderGraph d` ($d \ge 2$). -/
theorem spiderGraph_isThresholdedWonderful_all :
    ∀ d : ℕ, 2 ≤ d → IsThresholdedWonderful (SpiderGraph d) := by
  intro d hd
  by_cases hd2 : d = 2
  · exact spiderGraph_isThresholdedWonderful_of_prev d hd (Or.inl hd2)
  · exact spiderGraph_isThresholdedWonderful_of_prev d hd
      (Or.inr (hasErdosHajnalProp_spiderGraph_all (d - 1) (by omega)).1)

/-- Unconditional single-graph Erdős–Hajnal, complement EH, polynomial Rödl, and virality for
every unicyclic bird `BirdDGraph d` ($d \ge 1$, including `BullGraph = BirdDGraph 1`). -/
theorem hasErdosHajnalProp_birdDGraph_all :
    ∀ d : ℕ, 1 ≤ d →
      HasErdosHajnalProp (BirdDGraph d) ∧
      HasErdosHajnalProp (BirdDGraph d)ᶜ ∧
      HasPolyRodlProp (BirdDGraph d) ∧
      IsViral (BirdDGraph d) := by
  intro d hd
  have hEH : ∀ m : ℕ, 1 ≤ m → HasErdosHajnalProp (BirdDGraph m) := by
    intro m hm
    induction m using Nat.strongRecOn with
    | ind m ihm =>
      by_cases hm1 : m = 1
      · subst hm1; exact hasErdosHajnalProp_bullGraph
      · have hm2 : 2 ≤ m := by omega
        obtain ⟨hleaf, _, hviral⟩ := birdDGraph_leaf_reducible m hm2
        obtain ⟨c₁, c₂, c₃, c₄, c₅, c₆, c₇, c₈, c₉, hc₂, hc₆, hc₇, hc₇₂, hGN⟩ :=
          exists_satisfiesPairCoupledGenNiceAt_birdDGraph m hm2
        have h_wond : IsThresholdedWonderful (BirdDGraph m) := by
          by_cases hm6 : m ≤ 6
          · exact birdDGraph_isThresholdedWonderful_le_6 m hm hm6
          · exact birdDGraph_isThresholdedWonderful_ge_6 m (by omega)
              (hasErdosHajnalProp_all_paths (m + 3) (by omega)).1
              (ihm (m - 1) (by omega) (by omega))
        exact (master_stage2_eh_of_coupled_gen_nice_and_wonderful
          (BirdDGraph m) ⟨0, by omega⟩ ⟨1, by omega⟩
          (by intro h; have hv : (1 : ℕ) = 0 := congrArg Fin.val h; omega)
          hleaf (by rw [Fintype.card_fin]; omega) hviral h_wond
          hc₂ hc₆ hc₇ hc₇₂ hGN).2
  have hd_eh : HasErdosHajnalProp (BirdDGraph d) := hEH d hd
  exact ⟨hd_eh, hd_eh.compl,
    (eh_iff_polyRodl_iff_isViral (BirdDGraph d)).1.mp hd_eh,
    (eh_iff_polyRodl_iff_isViral (BirdDGraph d)).2.mp
      ((eh_iff_polyRodl_iff_isViral (BirdDGraph d)).1.mp hd_eh)⟩

/-- Unconditional Stage-2 Thresholded Wonderfulness for every unicyclic bird `BirdDGraph d` ($d \ge 1$). -/
theorem birdDGraph_isThresholdedWonderful_all :
    ∀ d : ℕ, 1 ≤ d → IsThresholdedWonderful (BirdDGraph d) := by
  intro d hd
  by_cases hd6 : d ≤ 6
  · exact birdDGraph_isThresholdedWonderful_le_6 d hd hd6
  · exact birdDGraph_isThresholdedWonderful_ge_6 d (by omega)
      (hasErdosHajnalProp_all_paths (d + 3) (by omega)).1
      (hasErdosHajnalProp_birdDGraph_all (d - 1) (by omega)).1

/-- Unconditional single-graph Erdős–Hajnal, complement EH, polynomial Rödl, and virality for
every leaf-substituted spider `LeafSubstSpiderGraph d a b c` ($d \ge 2, a, b, c \ge 1$) and
every bicyclic sawtooth `SawtoothGraph d` ($d \ge 1$). -/
theorem hasErdosHajnalProp_leafSubstSpider_and_sawtooth :
    (∀ (d a b c : ℕ), 2 ≤ d → 1 ≤ a → 1 ≤ b → 1 ≤ c →
      HasErdosHajnalProp (LeafSubstSpiderGraph d a b c) ∧
      HasErdosHajnalProp (LeafSubstSpiderGraph d a b c)ᶜ ∧
      HasPolyRodlProp (LeafSubstSpiderGraph d a b c) ∧
      IsViral (LeafSubstSpiderGraph d a b c)) ∧
    (∀ d : ℕ, 1 ≤ d →
      HasErdosHajnalProp (SawtoothGraph d) ∧
      HasErdosHajnalProp (SawtoothGraph d)ᶜ ∧
      HasPolyRodlProp (SawtoothGraph d) ∧
      IsViral (SawtoothGraph d)) := by
  constructor
  · intro d a b c hd ha hb hc
    haveI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
    haveI : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
    haveI : Nonempty (Fin c) := ⟨⟨0, hc⟩⟩
    have h0 : HasErdosHajnalProp (SpiderGraph (max d 1)) :=
      (hasErdosHajnalProp_spiderGraph_all (max d 1) (by omega)).1
    have h1 : HasErdosHajnalProp
        (substGraph (SpiderGraph (max d 1)) (spiderLeaf1 d) (⊥ : SimpleGraph (Fin a))) :=
      hasErdosHajnalProp_substGraph_tp _ _ _ h0 (hasErdosHajnalProp_bot_fin_all a)
    have h2 : HasErdosHajnalProp
        (substGraph (substGraph (SpiderGraph (max d 1)) (spiderLeaf1 d) (⊥ : SimpleGraph (Fin a)))
          (spiderLeaf2 d a) (⊥ : SimpleGraph (Fin b))) :=
      hasErdosHajnalProp_substGraph_tp _ _ _ h1 (hasErdosHajnalProp_bot_fin_all b)
    have h3 : HasErdosHajnalProp (LeafSubstSpiderGraph d a b c) :=
      hasErdosHajnalProp_substGraph_tp _ _ _ h2 (hasErdosHajnalProp_bot_fin_all c)
    exact ⟨h3, h3.compl,
      (eh_iff_polyRodl_iff_isViral _).1.mp h3,
      (eh_iff_polyRodl_iff_isViral _).2.mp ((eh_iff_polyRodl_iff_isViral _).1.mp h3)⟩
  · intro d hd
    have h_top2 : HasErdosHajnalProp (⊤ : SimpleGraph (Fin 2)) :=
      (compl_bot : (⊥ : SimpleGraph (Fin 2))ᶜ = ⊤) ▸ (hasErdosHajnalProp_bot_fin_all 2).compl
    have h_saw : HasErdosHajnalProp (SawtoothGraph d) :=
      hasErdosHajnalProp_substGraph_tp (BirdDGraph d) 0 (⊤ : SimpleGraph (Fin 2))
        (hasErdosHajnalProp_birdDGraph_all d hd).1 h_top2
    exact ⟨h_saw, h_saw.compl,
      (eh_iff_polyRodl_iff_isViral _).1.mp h_saw,
      (eh_iff_polyRodl_iff_isViral _).2.mp ((eh_iff_polyRodl_iff_isViral _).1.mp h_saw)⟩

/-- Every generator in `InBNew` satisfies `HasErdosHajnalProp`. -/
theorem hasErdosHajnalProp_of_inBNew {W : Type} [Fintype W] [DecidableEq W]
    (B : SimpleGraph W) (hB : InBNew B) : HasErdosHajnalProp B := by
  rcases hB with hB9 | hBull | ⟨d, hd2, _, hSp⟩ | ⟨d, hd3, _, hBd⟩
  · rcases hB9 with h1 | h2 | h3 | h4 | h5 | ⟨t, ht1, _, h6 | h7⟩
    · obtain ⟨e⟩ := h1
      exact hasErdosHajnalProp_of_iso' e.symm
        ((compl_bot : (⊥ : SimpleGraph (Fin 1))ᶜ = ⊤) ▸ (hasErdosHajnalProp_bot_fin_all 1).compl)
    · obtain ⟨e⟩ := h2
      exact hasErdosHajnalProp_of_iso' e.symm
        ((compl_bot : (⊥ : SimpleGraph (Fin 2))ᶜ = ⊤) ▸ (hasErdosHajnalProp_bot_fin_all 2).compl)
    · obtain ⟨e⟩ := h3; exact hasErdosHajnalProp_of_iso' e.symm (hasErdosHajnalProp_bot_fin_all 2)
    · obtain ⟨e⟩ := h4; exact hasErdosHajnalProp_of_iso' e.symm P9Baseline.main_theorem_C1_forest_pairs_and_closures.1.1
    · obtain ⟨e⟩ := h5; exact hasErdosHajnalProp_of_iso' e.symm P9Baseline.main_theorem_C1_forest_pairs_and_closures.1.2.1
    · obtain ⟨e⟩ := h6; exact hasErdosHajnalProp_of_iso' e.symm (hasErdosHajnalProp_all_paths t ht1).1
    · obtain ⟨e⟩ := h7; exact hasErdosHajnalProp_of_iso' e.symm (hasErdosHajnalProp_all_paths t ht1).2.1
  · obtain ⟨eBull⟩ := hBull
    exact hasErdosHajnalProp_of_iso' eBull.symm hasErdosHajnalProp_bullGraph
  · rcases hSp with h1 | h2
    · obtain ⟨e⟩ := h1; exact hasErdosHajnalProp_of_iso' e.symm (hasErdosHajnalProp_spiderGraph_all d hd2).1
    · obtain ⟨e⟩ := h2; exact hasErdosHajnalProp_of_iso' e.symm (hasErdosHajnalProp_spiderGraph_all d hd2).2.1
  · rcases hBd with h1 | h2
    · obtain ⟨e⟩ := h1; exact hasErdosHajnalProp_of_iso' e.symm (hasErdosHajnalProp_birdDGraph_all d (by omega)).1
    · obtain ⟨e⟩ := h2; exact hasErdosHajnalProp_of_iso' e.symm (hasErdosHajnalProp_birdDGraph_all d (by omega)).2.1

/-- Every generator in `InBInfty` satisfies `HasErdosHajnalProp`. -/
theorem hasErdosHajnalProp_of_inBInfty {W : Type} [Fintype W] [DecidableEq W]
    (B : SimpleGraph W) (hB : InBInfty B) : HasErdosHajnalProp B := by
  rcases hB with hNew | ⟨k, hk10, hPk⟩ | ⟨d, hd6, hSp⟩ | ⟨d, hd7, hBd⟩ | ⟨d, hd1, hSaw⟩
  · exact hasErdosHajnalProp_of_inBNew B hNew
  · rcases hPk with h1 | h2
    · obtain ⟨e⟩ := h1; exact hasErdosHajnalProp_of_iso' e.symm (hasErdosHajnalProp_all_paths k (by omega)).1
    · obtain ⟨e⟩ := h2; exact hasErdosHajnalProp_of_iso' e.symm (hasErdosHajnalProp_all_paths k (by omega)).2.1
  · rcases hSp with h1 | h2
    · obtain ⟨e⟩ := h1; exact hasErdosHajnalProp_of_iso' e.symm (hasErdosHajnalProp_spiderGraph_all d (by omega)).1
    · obtain ⟨e⟩ := h2; exact hasErdosHajnalProp_of_iso' e.symm (hasErdosHajnalProp_spiderGraph_all d (by omega)).2.1
  · rcases hBd with h1 | h2
    · obtain ⟨e⟩ := h1; exact hasErdosHajnalProp_of_iso' e.symm (hasErdosHajnalProp_birdDGraph_all d (by omega)).1
    · obtain ⟨e⟩ := h2; exact hasErdosHajnalProp_of_iso' e.symm (hasErdosHajnalProp_birdDGraph_all d (by omega)).2.1
  · rcases hSaw with h1 | h2
    · obtain ⟨e⟩ := h1; exact hasErdosHajnalProp_of_iso' e.symm (hasErdosHajnalProp_leafSubstSpider_and_sawtooth.2 d hd1).1
    · obtain ⟨e⟩ := h2; exact hasErdosHajnalProp_of_iso' e.symm (hasErdosHajnalProp_leafSubstSpider_and_sawtooth.2 d hd1).2.1

/-! ### Main Exported Theorems Matching `Problem.lean` One-for-One -/

/-- **Main Theorem (A.1) — Universal Statement for All Finite Paths $P_k$ ($k \ge 1$)**. -/
theorem erdos_hajnal_all_paths :
    ∀ k : ℕ, 1 ≤ k →
      ∃ c > (0 : ℝ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
        IsInducedSubgraphFree G (pathGraph k) →
          (G.cliqueNum : ℝ) ≥ (n : ℝ) ^ c ∨ (G.indepNum : ℝ) ≥ (n : ℝ) ^ c :=
  erdos_hajnal_all_paths_proof

/-- **Erdős Problem 61 (`FormalConjectures` Asymptotic Variant for All Finite Paths $P_k$, $k \ge 1$)**. -/
theorem erdos_61.variants.all_paths :
    ∀ k : ℕ, 1 ≤ k →
      ∃ c > (0 : ℝ), IsErdosHajnalLowerBound (pathGraph k) (fun n : ℕ => (n : ℝ) ^ c) :=
  erdos_61_variants_all_paths_proof

/-- **Main Theorem (A.1) — Full Equivalence Statement (`HasErdosHajnalProp`, `HasPolyRodlProp`, and
`IsViral`) for All Finite Paths $P_k$ and Co-Paths $\overline{P_k}$ ($k \ge 1$)**. -/
theorem erdos_hajnal_all_paths_fintype :
    ∀ k : ℕ, 1 ≤ k →
      HasErdosHajnalProp (pathGraph k) ∧
      HasErdosHajnalProp (pathGraph k)ᶜ ∧
      HasPolyRodlProp (pathGraph k) ∧
      HasPolyRodlProp (pathGraph k)ᶜ ∧
      IsViral (pathGraph k) ∧
      IsViral (pathGraph k)ᶜ :=
  hasErdosHajnalProp_all_paths

/-- **Main Theorem (A.2)–(A.3) — All Linear/Co-Linear Forests, All $(s, d)$-Brooms ($s, d \ge 1$),
and All Double Brooms $\mathrm{DB}(a, d, b)$ ($a, d, b \ge 1$)**. -/
theorem main_theorem_A2_linear_forests_and_brooms :
    (∀ (ks : List ℕ), 1 ≤ ks.length → (∀ k ∈ ks, 1 ≤ k) →
      HasErdosHajnalProp (LinearForestGraph ks) ∧
      HasErdosHajnalProp (LinearForestGraph ks)ᶜ ∧
      HasPolyRodlProp (LinearForestGraph ks) ∧
      IsViral (LinearForestGraph ks)) ∧
    (∀ (s d : ℕ), 1 ≤ s → 1 ≤ d →
      HasErdosHajnalProp (BroomGraph s d) ∧
      HasErdosHajnalProp (BroomGraph s d)ᶜ ∧
      HasPolyRodlProp (BroomGraph s d) ∧
      IsViral (BroomGraph s d)) ∧
    (∀ (a d b : ℕ), 1 ≤ a → 1 ≤ d → 1 ≤ b →
      HasErdosHajnalProp (DoubleBroomGraph a d b) ∧
      HasErdosHajnalProp (DoubleBroomGraph a d b)ᶜ ∧
      HasPolyRodlProp (DoubleBroomGraph a d b) ∧
      IsViral (DoubleBroomGraph a d b)) :=
  main_theorem_A2_linear_forests_and_brooms_proof

/-- **Main Theorem (A.4) — All Prime Subdivided Spiders $S_{1,2,d}$ ($d \ge 2$),
Leaf-Substituted Spiders, Unicyclic Birds $\mathrm{Bird}_d$ ($d \ge 1$), and Sawtooths $M_{2,d}$ ($d \ge 1$)**. -/
theorem main_theorem_A4_spiders_birds_sawtooths :
    (∀ d : ℕ, 2 ≤ d →
      HasErdosHajnalProp (SpiderGraph d) ∧
      HasErdosHajnalProp (SpiderGraph d)ᶜ ∧
      HasPolyRodlProp (SpiderGraph d) ∧
      IsViral (SpiderGraph d)) ∧
    (∀ (d a b c : ℕ), 2 ≤ d → 1 ≤ a → 1 ≤ b → 1 ≤ c →
      HasErdosHajnalProp (LeafSubstSpiderGraph d a b c) ∧
      HasErdosHajnalProp (LeafSubstSpiderGraph d a b c)ᶜ ∧
      HasPolyRodlProp (LeafSubstSpiderGraph d a b c) ∧
      IsViral (LeafSubstSpiderGraph d a b c)) ∧
    (∀ d : ℕ, 1 ≤ d →
      HasErdosHajnalProp (BirdDGraph d) ∧
      HasErdosHajnalProp (BirdDGraph d)ᶜ ∧
      HasPolyRodlProp (BirdDGraph d) ∧
      IsViral (BirdDGraph d)) ∧
    (∀ d : ℕ, 1 ≤ d →
      HasErdosHajnalProp (SawtoothGraph d) ∧
      HasErdosHajnalProp (SawtoothGraph d)ᶜ ∧
      HasPolyRodlProp (SawtoothGraph d) ∧
      IsViral (SawtoothGraph d)) :=
  ⟨hasErdosHajnalProp_spiderGraph_all,
   hasErdosHajnalProp_leafSubstSpider_and_sawtooth.1,
   hasErdosHajnalProp_birdDGraph_all,
   hasErdosHajnalProp_leafSubstSpider_and_sawtooth.2⟩

/-- **Main Theorem (A.5) — All Trees of Order $\le 6$, Forests of Component Order $\le 6$,
and $10/11$ Trees on $7$ Vertices (Excluding Solely $S_{2,2,2}$)**. -/
theorem main_theorem_A5_small_trees_and_forests :
    (∀ (W : Type) [Fintype W] [DecidableEq W] [Nonempty W] (T : SimpleGraph W),
      T.IsTree → Fintype.card W ≤ 6 →
        InHClosureBNew T ∧ HasErdosHajnalProp T ∧ HasErdosHajnalProp Tᶜ ∧
        HasPolyRodlProp T ∧ IsViral T) ∧
    (∀ (W : Type) [Fintype W] [DecidableEq W] [Nonempty W] (F : SimpleGraph W)
      [DecidableRel F.Reachable],
      F.IsAcyclic →
      (∀ u : W, (Finset.univ.filter (fun v : W => F.Reachable u v)).card ≤ 6) →
        InHClosureBNew F ∧ HasErdosHajnalProp F ∧ HasErdosHajnalProp Fᶜ ∧
        HasPolyRodlProp F ∧ IsViral F) ∧
    (∀ (W : Type) [Fintype W] [DecidableEq W] (T : SimpleGraph W),
      T.IsTree → Fintype.card W = 7 → ¬Nonempty (T ≃g SubdividedClawGraph) →
        InHClosureBNew T ∧ HasErdosHajnalProp T ∧ HasErdosHajnalProp Tᶜ ∧
        HasPolyRodlProp T ∧ IsViral T) :=
  small_trees_and_forests_of_base hasErdosHajnalProp_of_inBNew

/-- **Main Theorem (B) — Uniform Stage-1 Comb/Co-Comb Dichotomy, Leaf-Reducibility,
Stage-1 Coupled Generalized Niceness, and Stage-2 Thresholded Wonderfulness Across All Families**. -/
theorem main_theorem_B_stage1_stage2_all_families :
    (∀ r : ℕ, 1 ≤ r → Stage1CombCoCombDichotomyAt r) ∧
    (∀ k : ℕ, 6 ≤ k →
      (∃ v₀ : Fin k, (neighborFinsetIn (pathGraph k) v₀ Finset.univ).card ≤ 1 ∧
        HasErdosHajnalProp ((pathGraph k).comap (Subtype.val : {v : Fin k // v ≠ v₀} → Fin k))) ∧
      IsCoupledGeneralizedNice (pathGraph k) ∧
      IsCoupledGeneralizedNice (pathGraph k)ᶜ ∧
      IsThresholdedWonderful (pathGraph k)) ∧
    (∀ d : ℕ, 2 ≤ d →
      (∃ v₀ : Fin (d + 4), (neighborFinsetIn (SpiderGraph d) v₀ Finset.univ).card ≤ 1 ∧
        HasErdosHajnalProp ((SpiderGraph d).comap (Subtype.val : {v : Fin (d + 4) // v ≠ v₀} → Fin (d + 4)))) ∧
      IsCoupledGeneralizedNice (SpiderGraph d) ∧
      IsCoupledGeneralizedNice (SpiderGraph d)ᶜ ∧
      IsThresholdedWonderful (SpiderGraph d)) ∧
    (∀ d : ℕ, 2 ≤ d →
      (∃ v₀ : Fin (d + 4), (neighborFinsetIn (BirdDGraph d) v₀ Finset.univ).card ≤ 1 ∧
        HasErdosHajnalProp ((BirdDGraph d).comap (Subtype.val : {v : Fin (d + 4) // v ≠ v₀} → Fin (d + 4)))) ∧
      IsCoupledGeneralizedNice (BirdDGraph d) ∧
      IsCoupledGeneralizedNice (BirdDGraph d)ᶜ ∧
      IsThresholdedWonderful (BirdDGraph d)) := by
  refine ⟨stage1_comb_cocomb_dichotomy_all_r_proof, main_theorem_B_paths_all_k, ?_, ?_⟩
  · intro d hd
    have hl := spiderGraph_leaf_reducible d hd
    have hnice := spiderGraph_isCoupledGeneralizedNice d hd
    exact ⟨⟨⟨1, by omega⟩, card_neighborFinset_le_one_of_adj_iff (SpiderGraph d) ⟨1, by omega⟩ ⟨0, by omega⟩ hl.1, hl.2.1⟩,
      hnice.1, hnice.2, spiderGraph_isThresholdedWonderful_all d hd⟩
  · intro d hd
    have hl := birdDGraph_leaf_reducible d hd
    have hnice := birdDGraph_isCoupledGeneralizedNice d (by omega)
    exact ⟨⟨⟨0, by omega⟩, card_neighborFinset_le_one_of_adj_iff (BirdDGraph d) ⟨0, by omega⟩ ⟨1, by omega⟩ hl.1, hl.2.1⟩,
      hnice.1, hnice.2, birdDGraph_isThresholdedWonderful_all d (by omega)⟩

/-- **Main Theorem (C) — Strict Closure Containments, Opposite-Chirality Forest & Closure Pairs,
Hooked-Claw Pairs, and Countably Infinitely Many Prime Non-Split Viral Extension Towers**. -/
theorem main_theorem_C_closures_forest_pairs_hook4_and_infinite_towers :
    ((∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W),
        InHClosure 9 H → InHClosureBNew H) ∧
     (InHClosureBNew (SpiderGraph 2) ∧ ¬InHClosure 9 (SpiderGraph 2)) ∧
     (∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W),
        InHClosureBNew H → InHClosureBInfty H) ∧
     (InHClosureBInfty (SpiderGraph 6) ∧ ¬InHClosureBNew (SpiderGraph 6))) ∧
    ((∀ (W₁ W₂ : Type) [Fintype W₁] [DecidableEq W₁] [Nonempty W₁]
        [Fintype W₂] [DecidableEq W₂] [Nonempty W₂]
        (F₁ : SimpleGraph W₁) (F₂ : SimpleGraph W₂),
        F₁.IsAcyclic → F₂.IsAcyclic →
          HasPairErdosHajnalProp F₁ F₂ᶜ ∧ HasPairPolyRodlProp F₁ F₂ᶜ ∧ IsPairViral F₁ F₂ᶜ) ∧
     (∀ (W₁ W₂ : Type) [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]
        (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂),
        InJClosureBInfty H₁ → InJClosureBInfty H₂ →
          HasPairErdosHajnalProp H₁ H₂ᶜ ∧ HasPairPolyRodlProp H₁ H₂ᶜ ∧ IsPairViral H₁ H₂ᶜ) ∧
     (∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W),
        InHClosureBInfty H →
          HasErdosHajnalProp H ∧ HasErdosHajnalProp Hᶜ ∧ HasPolyRodlProp H ∧ IsViral H)) ∧
    (∀ (W : Type) [Fintype W] [DecidableEq W] (Q : SimpleGraph W) (S : Set W),
      HasErdosHajnalProp Q → 1 ≤ Fintype.card W →
        ∀ t : ℕ, 1 ≤ t →
          HasPairErdosHajnalProp (pathGraph t) (Hook4Graph Q S) ∧
          HasPairErdosHajnalProp (pathGraph t)ᶜ (Hook4Graph Q S)ᶜ ∧
          HasPairPolyRodlProp (pathGraph t) (Hook4Graph Q S) ∧
          IsPairViral (pathGraph t) (Hook4Graph Q S)) ∧
    (∀ (W₀ : Type) [Fintype W₀] [DecidableEq W₀] (G₀ : SimpleGraph W₀) (x₀ : W₀),
      (IsPrimeGraph G₀ ∧ 6 ≤ Fintype.card W₀ ∧
       (∀ u : W₀, (neighborFinsetIn G₀ u Finset.univ).card ≤ Fintype.card W₀ - 3) ∧
       (neighborFinsetIn G₀ x₀ Finset.univ).card = 1 ∧
       ¬IsSplitGraph G₀ ∧
       InHClosureBInfty G₀ ∧
       InHClosureBInfty (G₀.comap (Subtype.val : {w : W₀ // w ≠ x₀} → W₀))) →
      (∀ r : ℕ,
        InHClosureBInfty (GenPrimeTowerGraph G₀ x₀ r) ∧
        HasErdosHajnalProp (GenPrimeTowerGraph G₀ x₀ r) ∧
        HasErdosHajnalProp (GenPrimeTowerGraph G₀ x₀ r)ᶜ ∧
        IsViral (GenPrimeTowerGraph G₀ x₀ r) ∧
        IsPrimeGraph (GenPrimeTowerGraph G₀ x₀ r) ∧
        ¬IsSplitGraph (GenPrimeTowerGraph G₀ x₀ r) ∧
        ¬InJClosureC5 (GenPrimeTowerGraph G₀ x₀ r)ᶜ) ∧
      (∀ r₁ r₂ : ℕ,
        Nonempty (GenPrimeTowerGraph G₀ x₀ r₁ ≃g GenPrimeTowerGraph G₀ x₀ r₂) ↔ r₁ = r₂)) ∧
    ((∀ (k : ℕ) (hk : 6 ≤ k) (r : ℕ),
        InHClosureBInfty (GenPrimeTowerGraph (pathGraph k) ⟨k - 1, by omega⟩ r) ∧
        HasErdosHajnalProp (GenPrimeTowerGraph (pathGraph k) ⟨k - 1, by omega⟩ r) ∧
        IsPrimeGraph (GenPrimeTowerGraph (pathGraph k) ⟨k - 1, by omega⟩ r) ∧
        ¬IsSplitGraph (GenPrimeTowerGraph (pathGraph k) ⟨k - 1, by omega⟩ r)) ∧
     (∀ d : ℕ, 2 ≤ d → ∀ r : ℕ,
        InHClosureBInfty (GenPrimeTowerGraph (SpiderGraph d) (Fin.last (d + 3)) r) ∧
        HasErdosHajnalProp (GenPrimeTowerGraph (SpiderGraph d) (Fin.last (d + 3)) r) ∧
        IsPrimeGraph (GenPrimeTowerGraph (SpiderGraph d) (Fin.last (d + 3)) r) ∧
        ¬IsSplitGraph (GenPrimeTowerGraph (SpiderGraph d) (Fin.last (d + 3)) r)) ∧
     (∀ d : ℕ, 2 ≤ d → ∀ r : ℕ,
        InHClosureBInfty (GenPrimeTowerGraph (BirdDGraph d) (Fin.last (d + 3)) r) ∧
        HasErdosHajnalProp (GenPrimeTowerGraph (BirdDGraph d) (Fin.last (d + 3)) r) ∧
        IsPrimeGraph (GenPrimeTowerGraph (BirdDGraph d) (Fin.last (d + 3)) r) ∧
        ¬IsSplitGraph (GenPrimeTowerGraph (BirdDGraph d) (Fin.last (d + 3)) r))) := by
  refine ⟨⟨fun _ _ _ _ h => inHClosure9_to_inHClosureBNew h,
          ⟨inHClosureBNew_spiderGraph 2 (by omega) (by omega), spiderGraph_2_not_inHClosure9⟩,
          fun _ _ _ _ h => inHClosureBNew_to_inHClosureBInfty h,
          ⟨⟨InJClosureBInfty.base _ ?_, InJClosureBInfty.base _ ?_⟩,
           spiderGraph_6_not_inHClosureBNew⟩⟩,
         ⟨opposite_chirality_forest_pairs_eh,
          fun _ _ _ _ _ _ H₁ H₂ h₁ h₂ =>
            let ⟨hv, hp, he⟩ := inJClosureBInfty_pair_viral_of_base hasErdosHajnalProp_of_inBInfty H₁ H₂ h₁ h₂
            ⟨he, hp, hv⟩,
          fun _ _ _ H => inHClosureBInfty_eh_of_base hasErdosHajnalProp_of_inBInfty H⟩,
         pair_Pt_Hook4_eh_all_t,
         genPrimeTower_main_of_base hasErdosHajnalProp_of_inBInfty,
         base_families_genPrimeTowers_of_base hasErdosHajnalProp_of_inBInfty⟩
  · right; right; left; exact ⟨6, le_rfl, Or.inl ⟨SimpleGraph.Iso.refl⟩⟩
  · right; right; left; exact ⟨6, le_rfl, Or.inr ⟨SimpleGraph.Iso.refl⟩⟩

end Erdos61
