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
import ErdosHajnal.P6Baseline
import ErdosHajnal.RecursiveGallaiAndStage1
import ErdosHajnal.SpidersAndBirdsStage1Escape
import ErdosHajnal.SymmetricStage12Interface
import ErdosHajnal.ViralityAndClosures

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 1600000

open Filter Finset SimpleGraph Real ErdosHajnalP6

namespace ErdosHajnalGen

/-!
## Section 4: Unified Depth-$r$ Stage-1 Comb/Co-Comb Dichotomy for All `SpiderGraph d` and `BirdDGraph d`
(`Proposition 7(2c)` of `main.tex`, lines 1267 & 1308–1318)
-/

/-- Grouping anticonnected components of $G[M_T \setminus N_F(u)]$ (where $G \in \{F, Fᶜ\}$) into a
pairwise-pure $(p_{\mathrm{comp}}, \tau)$-blockade in $F[N_*]$. -/
lemma exists_pure_blockade_of_nonneigh_components {V : Type*} [Fintype V] [DecidableEq V]
    (G F : SimpleGraph V) {M_T N_star : Finset V} {u : V} {p_comp : ℕ} {τ : ℝ}
    (hNs_MT : N_star ⊆ M_T) (hτ_pos : 0 < τ)
    (hG_pure : ∀ A B : Finset V, Disjoint A B → IsCompletePair G A B → IsPurePair F A B)
    (h_mod : ∀ C : Finset V,
      IsAnticonnectedComponentOf G (M_T \ neighborFinsetIn F u M_T) C → IsProperModuleIn F M_T C)
    (h_small : ∀ X : Finset V,
      IsProperModuleIn F M_T X → (X ∩ N_star).Nonempty → ((X ∩ N_star).card : ℝ) ≤ τ)
    (h_deg : 2 * (p_comp : ℝ) * τ ≤ ((N_star \ neighborFinsetIn F u N_star).card : ℝ)) :
    ∃ D : Fin p_comp → Finset V, IsPureBlockadeIn F N_star p_comp τ D := by
  classical
  let Z_T := M_T \ neighborFinsetIn F u M_T
  let Z_star := N_star \ neighborFinsetIn F u N_star
  obtain ⟨q, C, hC_fam⟩ := exists_anticonnectedComponentFamily G Z_T
  let C' : Fin q → Finset V := fun s => C s ∩ N_star
  have hC'_disj : ∀ s t : Fin q, s ≠ t → Disjoint (C' s) (C' t) :=
    fun s t hst => Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left (hC_fam.pairwise_disjoint s t hst))
  have hC'_comp : ∀ s t : Fin q, s ≠ t → IsCompletePair G (C' s) (C' t) := by
    intro s t hst x hx y hy
    have hcomp := (hC_fam.is_component s).isCompletePair_of_disjoint
      (hC_fam.is_component t) (hC_fam.pairwise_disjoint s t hst)
    exact hcomp x (Finset.mem_inter.mp hx).1 y (Finset.mem_inter.mp hy).1
  have hC'_union : Finset.univ.biUnion C' = Z_star := by
    ext x
    simp only [C', Z_star, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_inter, Finset.mem_sdiff, ErdosHajnalP6.mem_neighborFinsetIn_iff]
    constructor
    · rintro ⟨s, hxCs, hxNs⟩
      have hxZT := (hC_fam.is_component s).1 hxCs
      rw [Finset.mem_sdiff, ErdosHajnalP6.mem_neighborFinsetIn_iff] at hxZT
      exact ⟨hxNs, fun h => hxZT.2 ⟨hNs_MT hxNs, h.2⟩⟩
    · rintro ⟨hxNs, hnadj⟩
      have hxZT : x ∈ Z_T := by
        rw [Finset.mem_sdiff, ErdosHajnalP6.mem_neighborFinsetIn_iff]
        exact ⟨hNs_MT hxNs, fun h => hnadj ⟨hxNs, h.2⟩⟩
      rw [← hC_fam.biUnion_eq, Finset.mem_biUnion] at hxZT
      obtain ⟨s, _, hxCs⟩ := hxZT
      exact ⟨s, hxCs, hxNs⟩
  have hC'_sum : ∑ s : Fin q, ((C' s).card : ℝ) = (Z_star.card : ℝ) := by
    have h_nat : ∑ s : Fin q, (C' s).card = Z_star.card := by
      rw [← hC'_union, Finset.card_biUnion]
      intro s _ t _ hst; exact hC'_disj s t hst
    exact_mod_cast h_nat
  have hC'_each : ∀ s ∈ (Finset.univ : Finset (Fin q)),
      0 ≤ ((C' s).card : ℝ) ∧ ((C' s).card : ℝ) ≤ τ := by
    intro s _
    refine ⟨Nat.cast_nonneg _, ?_⟩
    by_cases hne : (C' s).Nonempty
    · exact h_small (C s) (h_mod (C s) (hC_fam.is_component s)) hne
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
      exact le_of_lt hτ_pos
  obtain ⟨I, hI_sub, hI_disj⟩ := exists_disjoint_subsets_sum_ge_aux
    (fun s : Fin q => ((C' s).card : ℝ)) τ hτ_pos p_comp Finset.univ hC'_each (by linarith)
  let D : Fin p_comp → Finset V := fun j => (I j).biUnion C'
  have hD_card : ∀ j : Fin p_comp, (D j).card = ∑ s ∈ I j, (C' s).card :=
    fun j => Finset.card_biUnion (fun s _ t _ hst => hC'_disj s t hst)
  have hD_width : ∀ j : Fin p_comp, τ ≤ ((D j).card : ℝ) := by
    intro j
    rw [hD_card j, Nat.cast_sum]
    exact (hI_sub j).2
  have hD_ne : ∀ j : Fin p_comp, (D j).Nonempty := by
    intro j
    rw [← Finset.card_pos, ← @Nat.cast_pos ℝ]
    linarith [hD_width j]
  have hD_disj : ∀ j₁ j₂ : Fin p_comp, j₁ ≠ j₂ → Disjoint (D j₁) (D j₂) := by
    intro j₁ j₂ hj
    rw [Finset.disjoint_biUnion_left]
    intro s hs
    rw [Finset.disjoint_biUnion_right]
    intro t ht
    have hst : s ≠ t := fun h => Finset.disjoint_left.mp (hI_disj j₁ j₂ hj) hs (h ▸ ht)
    exact hC'_disj s t hst
  refine ⟨D, ⟨fun j => Finset.biUnion_subset.mpr (fun s _ => Finset.inter_subset_right),
    hD_ne, hD_disj, hD_width⟩, ?_⟩
  intro j₁ j₂ hj
  refine hG_pure (D j₁) (D j₂) (hD_disj j₁ j₂ hj) ?_
  intro x hx y hy
  rcases Finset.mem_biUnion.mp hx with ⟨s, hs, hxCs⟩
  rcases Finset.mem_biUnion.mp hy with ⟨t, ht, hyCt⟩
  have hst : s ≠ t := fun h => Finset.disjoint_left.mp (hI_disj j₁ j₂ hj) hs (h ▸ ht)
  exact hC'_comp s t hst x hxCs y hyCt

/-- Unified abstract interface capturing Proposition 7(2a) (`SpiderGraph`) and Proposition 7(2b) (`BirdDGraph`). -/
def HasNonNeighPureGrouping (H_fam : (d : ℕ) → SimpleGraph (Fin (d + 4))) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {F : SimpleGraph V} {S : Finset V}
    {ℓ s r p_comp : ℕ} {w τ : ℝ} {a : Fin ℓ → V} {B : Fin ℓ → Finset V}
    {stems : Fin ℓ → Fin s → V} {i j : Fin ℓ}
    (hij : i ≠ j) (hτ_pos : 0 < τ)
    (hfree : IsInducedSubgraphFree F (H_fam (s + 1 + r))ᶜ)
    (hcomb : IsCombOrCoCombIn F S ℓ w a B)
    (hstems : HasPerHandleApexStems F S ℓ s a B stems)
    (z : Fin (r + 1) → V) (M : Fin (r + 1) → Finset V)
    (hz0 : z 0 ∈ B j) (hM0 : M 0 ⊆ B i)
    (hM_step : ∀ q : Fin r, M q.succ ⊆ neighborFinsetIn F (z q.castSucc) (M q.castSucc))
    (hz_step : ∀ q : Fin r, z q.succ ∈ M q.castSucc ∧ ¬F.Adj (z q.castSucc) (z q.succ))
    {N_star : Finset V} (hNs_sub : N_star ⊆ M (Fin.last r))
    (hz_not_anti : ∃ x ∈ M (Fin.last r), F.Adj (z (Fin.last r)) x)
    (h_small : ∀ X : Finset V,
      IsProperModuleIn F (M (Fin.last r)) X → (X ∩ N_star).Nonempty →
      ((X ∩ N_star).card : ℝ) ≤ τ)
    (h_nondeg : 2 * (p_comp : ℝ) * τ ≤
      ((N_star \ neighborFinsetIn F (z (Fin.last r)) N_star).card : ℝ)),
    ∃ D : Fin p_comp → Finset V, IsPureBlockadeIn F N_star p_comp τ D

/-- `SpiderGraph` satisfies `HasNonNeighPureGrouping` via Proposition 7(2a)
(`spider_terminal_nonneighborhood_modularity`). -/
theorem spiderGraph_hasNonNeighPureGrouping : HasNonNeighPureGrouping SpiderGraph := by
  intro V _ _ F S ℓ s r p_comp w τ a B stems i j hij hτ_pos hfree hcomb hstems z M hz0 hM0
    hM_step hz_step N_star hNs_sub hz_not_anti h_small h_nondeg
  exact exists_pure_blockade_of_nonneigh_components Fᶜ F hNs_sub hτ_pos
    (fun _ _ _ hcomp => Or.inr (fun u hu v hv hadj => (hcomp u hu v hv).2 hadj))
    (fun C hC => spider_terminal_nonneighborhood_modularity hfree hcomb hstems hij
      z M hz0 hM0 hM_step hz_step hz_not_anti hC)
    h_small h_nondeg

/-- `BirdDGraph` satisfies `HasNonNeighPureGrouping` via Proposition 7(2b)
(`bird_terminal_nonneighborhood_modularity`). -/
theorem birdDGraph_hasNonNeighPureGrouping : HasNonNeighPureGrouping BirdDGraph := by
  intro V _ _ F S ℓ s r p_comp w τ a B stems i j hij hτ_pos hfree hcomb hstems z M hz0 hM0
    hM_step hz_step N_star hNs_sub hz_not_anti h_small h_nondeg
  exact exists_pure_blockade_of_nonneigh_components F F hNs_sub hτ_pos
    (fun _ _ _ hcomp => Or.inl hcomp)
    (fun C hC => bird_terminal_nonneighborhood_modularity hfree hcomb hstems hij
      z M hz0 hM0 hM_step hz_step hz_not_anti hC)
    h_small h_nondeg

/-- Strong depth-$r$ Stage-1 Comb/Co-Comb Dichotomy for a graph family `H_fam` at parameter $s + r$. -/
def Stage1FamilyStrongAt (H_fam : (d : ℕ) → SimpleGraph (Fin (d + 4))) (r : ℕ) : Prop :=
  1 ≤ r →
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : SimpleGraph V) (S : Finset V)
    (s ℓ p_cap L_max : ℕ) (η_out w : ℝ)
    (a : Fin ℓ → V) (B : Fin ℓ → Finset V) (stems : Fin ℓ → Fin s → V),
    1 ≤ s → 64 ≤ ℓ → ℓ ≤ p_cap → 2 ≤ L_max → L_max ≤ ℓ →
    0 < η_out → η_out ≤ (2 : ℝ)⁻¹ ^ 16 →
    IsInducedSubgraphFree F (H_fam (s + r))ᶜ →
    IsCombOrCoCombIn F S ℓ w a B →
    HasPerHandleApexStems F S ℓ s a B stems →
    combMinWidth r η_out p_cap ≤ w →
      let U_ambient := Finset.biUnion Finset.univ B
      (∃ k : ℕ, L_max ≤ k ∧ k ≤ p_cap ∧
        ∃ U : Fin k → Finset V,
          IsWeaklySparseOrCoSparseBlockadeIn F U_ambient k
            (w / ((2 : ℝ) ^ (60 * r) * (k : ℝ) ^ (2 * splitTreeD r))) η_out U) ∨
      (∃ U : Fin p_cap → Finset V,
        IsWeaklySparseOrCoSparseBlockadeIn F U_ambient p_cap
          ((2 : ℝ) ^ (-(200 * (r : ℝ) ^ 2)) * η_out ^ r * (p_cap : ℝ) ^ (-(capExpE r : ℝ)) * w)
          η_out U)

/-- Depth-$r$ Stage-1 Comb/Co-Comb Dichotomy statement (`Proposition 7(2c)` depth-$r$ counterpart of
`Stage1CombCoCombDichotomyAt r`) for a graph family `H_fam` at parameter $s + r$. -/
def Stage1FamilyAt (H_fam : (d : ℕ) → SimpleGraph (Fin (d + 4))) (r : ℕ) : Prop :=
  1 ≤ r →
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : SimpleGraph V) (S : Finset V)
    (s ℓ p_cap L_max : ℕ) (η_out w : ℝ)
    (a : Fin ℓ → V) (B : Fin ℓ → Finset V) (stems : Fin ℓ → Fin s → V),
    1 ≤ s → 64 ≤ ℓ → ℓ ≤ p_cap → 2 ≤ L_max → L_max ≤ ℓ →
    0 < η_out → η_out ≤ (2 : ℝ)⁻¹ ^ 16 →
    IsInducedSubgraphFree F (H_fam (s + r))ᶜ →
    IsCombOrCoCombIn F S ℓ w a B →
    HasPerHandleApexStems F S ℓ s a B stems →
    combMinWidth r η_out p_cap ≤ w →
      let U_ambient := Finset.biUnion Finset.univ B
      (∃ k : ℕ, L_max ≤ k ∧ k ≤ p_cap ∧
        ∃ U : Fin k → Finset V,
          IsWeaklySparseOrCoSparseBlockadeIn F U_ambient k
            (w / ((2 : ℝ) ^ (60 * r) * (k : ℝ) ^ (3 * splitTreeD r))) η_out U) ∨
      (∃ U : Fin p_cap → Finset V,
        IsWeaklySparseOrCoSparseBlockadeIn F U_ambient p_cap
          ((2 : ℝ) ^ (-(200 * (r : ℝ) ^ 2)) * η_out ^ r * (p_cap : ℝ) ^ (-(capExpE r : ℝ)) * w)
          η_out U)

theorem Stage1FamilyStrongAt.to_weak {H_fam : (d : ℕ) → SimpleGraph (Fin (d + 4))} {r : ℕ}
    (h : Stage1FamilyStrongAt H_fam r) : Stage1FamilyAt H_fam r := by
  intro hr V _ _ F S s ℓ p_cap L_max η_out w a B stems
    hs hℓ hp hL_low hL_high hη_pos hη_ub hfree hcomb hstems hw
  rcases h hr V F S s ℓ p_cap L_max η_out w a B stems
      hs hℓ hp hL_low hL_high hη_pos hη_ub hfree hcomb hstems hw with
    ⟨k, hk_low, hk_high, U, hU⟩ | ⟨U, hU⟩
  · left
    refine ⟨k, hk_low, hk_high, U, hU.mono_ambient_width_eps Finset.Subset.rfl ?_ le_rfl⟩
    have hp_pos : (0 : ℝ) < (p_cap : ℝ) := Nat.cast_pos.mpr (by omega)
    have hw_nn : 0 ≤ w := by
      have : 0 < combMinWidth r η_out p_cap := by unfold combMinWidth; positivity
      linarith
    have hk_ge1 : (1 : ℝ) ≤ (k : ℝ) := Nat.one_le_cast.mpr (by omega)
    have hk_pow : (k : ℝ) ^ (2 * splitTreeD r) ≤ (k : ℝ) ^ (3 * splitTreeD r) :=
      pow_le_pow_right₀ hk_ge1 (by omega)
    exact div_le_div_of_nonneg_left hw_nn (by positivity)
      (mul_le_mul_of_nonneg_left hk_pow (by positivity))
  · right; exact ⟨U, hU⟩

/-- Base case $r = 1$ (`s + 1 = s + 1 + 0`) of the Stage-1 Comb/Co-Comb Dichotomy for any
graph family `H_fam` satisfying `HasNonNeighPureGrouping H_fam`. -/
theorem stage1Family_strong_r1 {H_fam : (d : ℕ) → SimpleGraph (Fin (d + 4))}
    (h_grp : HasNonNeighPureGrouping H_fam) :
    Stage1FamilyStrongAt H_fam 1 := by
  intro _ V _ _ F S s ℓ p_cap L_max η_out w a B stems
    hs hℓ hp_cap hL_low hL_high hη_pos hη_ub hfree hcomb hstems hw U_ambient
  have hℓ_16 : 16 ≤ ℓ := by omega
  have hp_cap_r : (64 : ℝ) ≤ (p_cap : ℝ) := Nat.ofNat_le_cast.mpr (le_trans hℓ hp_cap)
  have hp_pos : (0 : ℝ) < (p_cap : ℝ) := by linarith
  have hη_le1 : η_out ≤ 1 := le_trans hη_ub (by norm_num)
  have hη_inv_ge1 : 1 ≤ η_out⁻¹ := one_le_inv₀ hη_pos |>.mpr hη_le1
  have hw_pos : 0 < w := by
    have : 0 < combMinWidth 1 η_out p_cap := by unfold combMinWidth; positivity
    linarith
  have hw_nn : 0 ≤ w := le_of_lt hw_pos
  have hw_p1 : (2 : ℝ) ^ 44 * η_out⁻¹ * (p_cap : ℝ) ^ 22 ≤ w := by
    unfold combMinWidth capExpE splitTreeD at hw
    have h_exp : (400 * 1 ^ 2 : ℕ) = 400 ∧ (8 * 1 * 16 ^ 1 + 2 * 8 : ℕ) = 144 := ⟨by decide, by decide⟩
    rw [h_exp.1, h_exp.2, Nat.cast_one, mul_one] at hw
    have h_η3 : η_out⁻¹ ≤ η_out ^ (-3 : ℝ) := by
      rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg (le_of_lt hη_pos),
        Real.rpow_natCast, ← inv_pow]
      exact le_self_pow₀ hη_inv_ge1 (by omega)
    have h_p : (p_cap : ℝ) ^ 22 ≤ (p_cap : ℝ) ^ 144 :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have h_2 : (2 : ℝ) ^ 44 ≤ (2 : ℝ) ^ 400 := pow_le_pow_right₀ (by norm_num) (by omega)
    calc (2 : ℝ) ^ 44 * η_out⁻¹ * (p_cap : ℝ) ^ 22
        ≤ (2 : ℝ) ^ 400 * η_out ^ (-3 : ℝ) * (p_cap : ℝ) ^ 144 := by
          refine mul_le_mul (mul_le_mul h_2 h_η3 (by positivity) (by positivity))
            h_p (by positivity) (by positivity)
      _ ≤ w := hw
  have hB_block : IsBlockadeIn F S ℓ w B := by
    rcases hcomb with hc | hco
    · exact hc.is_blockade
    · exact hco.is_blockade
  have hB_sub_U : ∀ i : Fin ℓ, B i ⊆ U_ambient :=
    fun i => Finset.subset_biUnion_of_mem B (Finset.mem_univ i)
  have hℓ_r : (16 : ℝ) ≤ (ℓ : ℝ) := Nat.ofNat_le_cast.mpr hℓ_16
  let p_comp : ℕ := min p_cap ⌈8 * (ℓ : ℝ) ^ 2 * η_out⁻¹⌉₊
  have hp_comp_le_p : p_comp ≤ p_cap := Nat.min_le_left _ _
  have hℓ_le_comp : ℓ ≤ p_comp := by
    refine le_min hp_cap ?_
    have h1 : (ℓ : ℝ) ≤ 8 * (ℓ : ℝ) ^ 2 * 1 := by nlinarith
    have h2 : 8 * (ℓ : ℝ) ^ 2 * 1 ≤ 8 * (ℓ : ℝ) ^ 2 * η_out⁻¹ :=
      mul_le_mul_of_nonneg_left hη_inv_ge1 (by positivity)
    have h3 : (ℓ : ℝ) ≤ (⌈8 * (ℓ : ℝ) ^ 2 * η_out⁻¹⌉₊ : ℝ) :=
      le_trans (by linarith) (Nat.le_ceil (8 * (ℓ : ℝ) ^ 2 * η_out⁻¹))
    exact Nat.cast_le.mp h3
  have hp_comp_pos : (0 : ℝ) < (p_comp : ℝ) := Nat.cast_pos.mpr (by omega)
  have hp_comp_cases : p_comp = p_cap ∨ (p_comp < p_cap ∧ 8 * (ℓ : ℝ) ^ 2 * η_out⁻¹ ≤ (p_comp : ℝ)) := by
    by_cases hp_eq : p_comp = p_cap
    · exact Or.inl hp_eq
    · refine Or.inr ⟨lt_of_le_of_ne hp_comp_le_p hp_eq, ?_⟩
      have hp_ceil : p_comp = ⌈8 * (ℓ : ℝ) ^ 2 * η_out⁻¹⌉₊ :=
        Nat.min_eq_right (le_of_lt (by omega : ⌈8 * (ℓ : ℝ) ^ 2 * η_out⁻¹⌉₊ < p_cap))
      rw [hp_ceil]; exact Nat.le_ceil _
  let θ₁ : ℝ := η_out / (64 * (ℓ : ℝ) * (p_comp : ℝ) ^ 2)
  have hθ₁_def : θ₁ = η_out / (64 * (ℓ : ℝ) * (p_comp : ℝ) ^ 2) := rfl
  have hθ₁_pos : 0 < θ₁ := by unfold θ₁; positivity
  have hθ₁_ub : θ₁ ≤ 1 / (64 * (ℓ : ℝ) ^ 2) := by
    unfold θ₁
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (ℓ : ℝ) ≤ (p_comp : ℝ) := Nat.cast_le.mpr hℓ_le_comp
    have h2 : (ℓ : ℝ) ^ 2 ≤ (p_comp : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    nlinarith
  have hθ₁_lb : η_out / (64 * (p_cap : ℝ) ^ 3) ≤ θ₁ := by
    unfold θ₁
    refine div_le_div_of_nonneg_left (le_of_lt hη_pos) (by positivity) ?_
    have h1 : (ℓ : ℝ) ≤ (p_cap : ℝ) := Nat.cast_le.mpr hp_cap
    have h2 : (p_comp : ℝ) ^ 2 ≤ (p_cap : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (Nat.cast_le.mpr hp_comp_le_p) 2
    calc 64 * (ℓ : ℝ) * (p_comp : ℝ) ^ 2
        ≤ 64 * (p_cap : ℝ) * (p_cap : ℝ) ^ 2 := by
          refine mul_le_mul (by linarith) h2 (by positivity) (by positivity)
      _ = 64 * (p_cap : ℝ) ^ 3 := by ring
  have h_min_θ₁ : η_out / (64 * (p_cap : ℝ) ^ 4) ≤ min θ₁ (1 / (64 * (p_cap : ℝ) ^ 2)) := by
    refine le_min ?_ ?_
    · refine le_trans ?_ hθ₁_lb
      refine div_le_div_of_nonneg_left (le_of_lt hη_pos) (by positivity) ?_
      have : (1 : ℝ) ≤ (p_cap : ℝ) := by linarith
      calc 64 * (p_cap : ℝ) ^ 3 = 64 * (p_cap : ℝ) ^ 3 * 1 := by ring
        _ ≤ 64 * (p_cap : ℝ) ^ 3 * (p_cap : ℝ) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = 64 * (p_cap : ℝ) ^ 4 := by ring
    · rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : (1 : ℝ) ≤ (p_cap : ℝ) ^ 2 := by nlinarith
      nlinarith
  have hw₁_precond : 64 * (p_cap : ℝ) ^ 2 * θ₁⁻¹ * (4 * (ℓ : ℝ)) ^ 16 ≤ w := by
    have hθ₁_inv_ub : θ₁⁻¹ ≤ 64 * (p_cap : ℝ) ^ 3 * η_out⁻¹ := by
      have h1 := one_div_le_one_div_of_le (by positivity : 0 < η_out / (64 * (p_cap : ℝ) ^ 3)) hθ₁_lb
      rw [one_div, one_div_div] at h1
      calc θ₁⁻¹ ≤ 64 * (p_cap : ℝ) ^ 3 / η_out := h1
        _ = 64 * (p_cap : ℝ) ^ 3 * η_out⁻¹ := div_eq_mul_inv _ _
    have h4ℓ_le : (4 * (ℓ : ℝ)) ^ 16 ≤ (2 : ℝ) ^ 32 * (p_cap : ℝ) ^ 16 := by
      have h1 : (ℓ : ℝ) ^ 16 ≤ (p_cap : ℝ) ^ 16 :=
        pow_le_pow_left₀ (by positivity) (Nat.cast_le.mpr hp_cap) 16
      calc (4 * (ℓ : ℝ)) ^ 16 = (2 : ℝ) ^ 32 * (ℓ : ℝ) ^ 16 := by ring
        _ ≤ (2 : ℝ) ^ 32 * (p_cap : ℝ) ^ 16 := mul_le_mul_of_nonneg_left h1 (by positivity)
    have hp21_22 : (p_cap : ℝ) ^ 21 ≤ (p_cap : ℝ) ^ 22 :=
      pow_le_pow_right₀ (by linarith) (by omega)
    calc 64 * (p_cap : ℝ) ^ 2 * θ₁⁻¹ * (4 * (ℓ : ℝ)) ^ 16
        ≤ 64 * (p_cap : ℝ) ^ 2 * (64 * (p_cap : ℝ) ^ 3 * η_out⁻¹) * ((2 : ℝ) ^ 32 * (p_cap : ℝ) ^ 16) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hθ₁_inv_ub (by positivity))
            h4ℓ_le (by positivity) (by positivity)
      _ = (2 : ℝ) ^ 44 * η_out⁻¹ * (p_cap : ℝ) ^ 21 := by ring
      _ ≤ (2 : ℝ) ^ 44 * η_out⁻¹ * (p_cap : ℝ) ^ 22 :=
          mul_le_mul_of_nonneg_left hp21_22 (by positivity)
      _ ≤ w := hw_p1
  clear_value p_comp θ₁
  have h_cap_bound :
      (2 : ℝ) ^ (-(200 * ((1 : ℕ) : ℝ) ^ 2)) * η_out ^ 1 * (p_cap : ℝ) ^ (-(capExpE 1 : ℝ)) * w ≤
      (η_out / (64 * (p_cap : ℝ) ^ 4)) * (w / (L_max : ℝ) ^ 8) := by
    unfold capExpE
    rw [show (8 * 1 * 16 ^ 1 : ℕ) = 128 by decide, Nat.cast_one, one_pow, mul_one, pow_one]
    have hp_rpow : (p_cap : ℝ) ^ (-((128 : ℕ) : ℝ)) = ((p_cap : ℝ) ^ 128)⁻¹ := by
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
    rw [hp_rpow]
    have hL8_p8 : (L_max : ℝ) ^ 8 ≤ (p_cap : ℝ) ^ 8 :=
      pow_le_pow_left₀ (by positivity) (Nat.cast_le.mpr (le_trans hL_high hp_cap)) 8
    have h_p12 : (p_cap : ℝ) ^ 12 ≤ (p_cap : ℝ) ^ 128 :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have h_2 : (2 : ℝ) ^ (-200 : ℝ) ≤ 1 / 64 := by
      rw [show (-200 : ℝ) = -((200 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by norm_num),
        Real.rpow_natCast]
      have h6_200 : (2 : ℝ) ^ 6 ≤ (2 : ℝ) ^ 200 := pow_le_pow_right₀ (by norm_num) (by omega)
      calc ((2 : ℝ) ^ 200)⁻¹ ≤ ((2 : ℝ) ^ 6)⁻¹ := inv_anti₀ (by positivity) h6_200
        _ = 1 / 64 := by norm_num
    calc (2 : ℝ) ^ (-200 : ℝ) * η_out * ((p_cap : ℝ) ^ 128)⁻¹ * w
        ≤ (1 / 64) * η_out * ((p_cap : ℝ) ^ 12)⁻¹ * w := by
          refine mul_le_mul_of_nonneg_right ?_ hw_nn
          refine mul_le_mul (mul_le_mul_of_nonneg_right h_2 (le_of_lt hη_pos))
            (inv_anti₀ (by positivity) h_p12) (by positivity) (by positivity)
      _ = (η_out / (64 * (p_cap : ℝ) ^ 4)) * (w / (p_cap : ℝ) ^ 8) := by ring
      _ ≤ (η_out / (64 * (p_cap : ℝ) ^ 4)) * (w / (L_max : ℝ) ^ 8) :=
          mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_left hw_nn (by positivity) hL8_p8) (by positivity)
  by_cases h_gc2_cap : ∃ (i : Fin ℓ) (Q : Fin p_cap → Finset V),
      IsPureBlockadeIn F (B i) p_cap
        (min θ₁ (1 / (64 * (p_cap : ℝ) ^ 2)) * (((B i).card : ℝ) / (L_max : ℝ) ^ 8)) Q
  · right
    obtain ⟨i, Q, hQ⟩ := h_gc2_cap
    refine ⟨Q, (IsPureBlockadeIn.isWeaklySparseOrCoSparseBlockadeIn hQ (le_of_lt hη_pos)).mono_ambient_width_eps
      (hB_sub_U i) ?_ le_rfl⟩
    refine le_trans h_cap_bound ?_
    exact mul_le_mul h_min_θ₁
      (div_le_div_of_nonneg_right (hB_block.width_ge i) (by positivity))
      (by positivity) (by positivity)
  · by_cases h_gc2_split : ∃ (i : Fin ℓ), L_max < p_cap ∧ ∃ (k : ℕ) (U : Fin k → Finset V),
        L_max ≤ k ∧ k < p_cap ∧
        IsPureBlockadeIn F (B i) k (((B i).card : ℝ) / (64 * (k : ℝ) ^ 10)) U
    · left
      obtain ⟨i, _, k, U, hkL, hkp, hU⟩ := h_gc2_split
      refine ⟨k, hkL, le_of_lt hkp, U,
        (IsPureBlockadeIn.isWeaklySparseOrCoSparseBlockadeIn hU (le_of_lt hη_pos)).mono_ambient_width_eps
          (hB_sub_U i) ?_ le_rfl⟩
      unfold splitTreeD
      rw [show 60 * 1 = 60 by omega, show 2 * 8 = 16 by omega]
      have hk_ge1 : (1 : ℝ) ≤ (k : ℝ) := Nat.one_le_cast.mpr (by omega)
      have hk_10_16 : (k : ℝ) ^ 10 ≤ (k : ℝ) ^ 16 := pow_le_pow_right₀ hk_ge1 (by omega)
      have h64 : (64 : ℝ) ≤ (2 : ℝ) ^ 60 := by norm_num
      calc w / ((2 : ℝ) ^ 60 * (k : ℝ) ^ 16)
          ≤ w / (64 * (k : ℝ) ^ 10) :=
            div_le_div_of_nonneg_left hw_nn (by positivity)
              (mul_le_mul h64 hk_10_16 (by positivity) (by positivity))
        _ ≤ ((B i).card : ℝ) / (64 * (k : ℝ) ^ 10) :=
            div_le_div_of_nonneg_right (hB_block.width_ge i) (by positivity)
    · have h_all_core : ∀ i : Fin ℓ,
          ∃ M_T : Finset V, M_T ⊆ B i ∧
            ∃ M_star : Finset V, M_star ⊆ M_T ∧
              (15 / 64 : ℝ) * (w / (L_max : ℝ) ^ 8) < (M_star.card : ℝ) ∧
              (∀ X : Finset V, IsProperModuleIn F M_T X → (X ∩ M_star).Nonempty →
                X ⊆ M_star ∧ (X.card : ℝ) < 5 * θ₁ * (M_star.card : ℝ)) := by
        intro i
        have hBi_card : 64 * (p_cap : ℝ) ^ 2 * θ₁⁻¹ * (4 * (ℓ : ℝ)) ^ 16 ≤ ((B i).card : ℝ) :=
          le_trans hw₁_precond (hB_block.width_ge i)
        rcases iterated_gallai_core_decomposition F (B i) ℓ p_cap L_max θ₁
            hℓ_16 hp_cap hL_low hL_high hθ₁_pos hθ₁_ub hBi_card with
          ⟨W, hWB, hW_gt, M_T, hMT_W, _, _, M_star, hMs_MT, hMs_gt, hMs_prop⟩ | h_sp | ⟨Q, hQ⟩
        · have hW_w1 : w / (L_max : ℝ) ^ 8 < (W.card : ℝ) :=
            lt_of_le_of_lt (div_le_div_of_nonneg_right (hB_block.width_ge i) (by positivity)) hW_gt
          exact ⟨M_T, hMT_W.trans hWB, M_star, hMs_MT, by linarith, hMs_prop⟩
        · exact False.elim (h_gc2_split ⟨i, h_sp⟩)
        · exact False.elim (h_gc2_cap ⟨i, Q, hQ⟩)
      obtain ⟨M_T, hMT_all⟩ := Classical.axiomOfChoice h_all_core
      obtain ⟨M_star, hMs_all⟩ := Classical.axiomOfChoice (fun i => (hMT_all i).2)
      have hMT_sub_B : ∀ i : Fin ℓ, M_T i ⊆ B i := fun i => (hMT_all i).1
      have hMs_sub_MT : ∀ i : Fin ℓ, M_star i ⊆ M_T i := fun i => (hMs_all i).1
      have hMs_sub_B : ∀ i : Fin ℓ, M_star i ⊆ B i := fun i => (hMs_sub_MT i).trans (hMT_sub_B i)
      have hMs_gt_w1 : ∀ i : Fin ℓ,
          (15 / 64 : ℝ) * (w / (L_max : ℝ) ^ 8) < ((M_star i).card : ℝ) :=
        fun i => (hMs_all i).2.1
      have hMs_prop : ∀ (i : Fin ℓ) (X : Finset V),
          IsProperModuleIn F (M_T i) X → (X ∩ M_star i).Nonempty →
          X ⊆ M_star i ∧ (X.card : ℝ) < 5 * θ₁ * ((M_star i).card : ℝ) :=
        fun i => (hMs_all i).2.2
      have hMs_ne : ∀ i : Fin ℓ, (M_star i).Nonempty := by
        intro i
        rw [← Finset.card_pos, ← @Nat.cast_pos ℝ]
        have : 0 < (15 / 64 : ℝ) * (w / (L_max : ℝ) ^ 8) := by positivity
        linarith [hMs_gt_w1 i]
      by_cases h_dense_nonneigh : ∃ (i j : Fin ℓ), j ≠ i ∧ ∃ u ∈ M_star j,
          (∃ z ∈ M_T i, F.Adj u z) ∧
          (η_out / (2 * (ℓ : ℝ))) * ((M_star i).card : ℝ) ≤
            (((M_star i) \ neighborFinsetIn F u (M_star i)).card : ℝ)
      · obtain ⟨i, j, hji, u, hu_Mj, hu_ex_adj, hu_nonneigh_ge⟩ := h_dense_nonneigh
        let τ_i := 5 * θ₁ * ((M_star i).card : ℝ)
        have hτ_pos : 0 < τ_i := by
          unfold τ_i
          have : 0 < ((M_star i).card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr (hMs_ne i))
          positivity
        have h_nondeg : 2 * (p_comp : ℝ) * τ_i ≤
            (((M_star i) \ neighborFinsetIn F u (M_star i)).card : ℝ) := by
          have h_le : 2 * (p_comp : ℝ) * τ_i ≤ (η_out / (2 * (ℓ : ℝ))) * ((M_star i).card : ℝ) := by
            unfold τ_i
            rw [hθ₁_def]
            have h1 : 10 * (p_comp : ℝ) / (64 * (ℓ : ℝ) * (p_comp : ℝ) ^ 2) ≤ 1 / (2 * (ℓ : ℝ)) := by
              rw [div_le_div_iff₀ (by positivity) (by positivity)]
              have hp1 : (1 : ℝ) ≤ (p_comp : ℝ) := Nat.one_le_cast.mpr (by omega)
              have hℓ0 : (0 : ℝ) ≤ (ℓ : ℝ) := Nat.cast_nonneg _
              have hp2 : (1 : ℝ) ≤ (p_comp : ℝ) ^ 2 := by nlinarith
              have hmul : 0 ≤ (ℓ : ℝ) * (p_comp : ℝ) := by positivity
              nlinarith
            calc 2 * (p_comp : ℝ) * (5 * (η_out / (64 * (ℓ : ℝ) * (p_comp : ℝ) ^ 2)) * ((M_star i).card : ℝ))
                = (10 * (p_comp : ℝ) / (64 * (ℓ : ℝ) * (p_comp : ℝ) ^ 2)) * (η_out * ((M_star i).card : ℝ)) := by ring
              _ ≤ (1 / (2 * (ℓ : ℝ))) * (η_out * ((M_star i).card : ℝ)) :=
                  mul_le_mul_of_nonneg_right h1 (by positivity)
              _ = (η_out / (2 * (ℓ : ℝ))) * ((M_star i).card : ℝ) := by ring
          exact le_trans h_le hu_nonneigh_ge
        have hfree0 : IsInducedSubgraphFree F (H_fam (s + 1 + 0))ᶜ := hfree
        have h_small0 : ∀ X : Finset V,
            IsProperModuleIn F (M_T i) X → (X ∩ M_star i).Nonempty →
            ((X ∩ M_star i).card : ℝ) ≤ τ_i :=
          fun X hX hX_ne => le_trans (Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_left))
            (le_of_lt (hMs_prop i X hX hX_ne).2)
        obtain ⟨D_pure, hD_pure_Ms⟩ := h_grp hji.symm hτ_pos hfree0 hcomb hstems
          (fun _ => u) (fun _ => M_T i) (hMs_sub_B j hu_Mj) (hMT_sub_B i)
          (fun q => Fin.elim0 q) (fun q => Fin.elim0 q) (hMs_sub_MT i) hu_ex_adj
          h_small0 h_nondeg
        have hD_pure : IsPureBlockadeIn F U_ambient p_comp τ_i D_pure :=
          ⟨hD_pure_Ms.1.mono_ambient ((hMs_sub_B i).trans (hB_sub_U i)), hD_pure_Ms.2⟩
        have hτ_gt_θ1 : θ₁ * (w / (L_max : ℝ) ^ 8) < τ_i := by
          have h1 := hMs_gt_w1 i
          have h_pos : 0 < w / (L_max : ℝ) ^ 8 := by positivity
          calc θ₁ * (w / (L_max : ℝ) ^ 8)
              < 5 * θ₁ * ((15 / 64 : ℝ) * (w / (L_max : ℝ) ^ 8)) := by nlinarith
            _ < 5 * θ₁ * ((M_star i).card : ℝ) := mul_lt_mul_of_pos_left h1 (by positivity)
        rcases hp_comp_cases with hp_eq_cap | ⟨hp_lt, h_ceil_le⟩
        · right
          subst hp_eq_cap
          refine ⟨D_pure,
            (IsPureBlockadeIn.isWeaklySparseOrCoSparseBlockadeIn hD_pure
              (le_of_lt hη_pos)).mono_ambient_width_eps Finset.Subset.rfl ?_ le_rfl⟩
          exact le_trans h_cap_bound
            (le_trans (mul_le_mul_of_nonneg_right h_min_θ₁ (by positivity))
              (le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity))
                (le_of_lt hτ_gt_θ1)))
        · left
          have hL_le_comp : L_max ≤ p_comp := le_trans hL_high hℓ_le_comp
          have h_w_split := prop1_pure_split_width_bound hℓ_16 hL_low hL_high hL_le_comp
            hη_pos hw_nn h_ceil_le hθ₁_def (le_of_lt hτ_gt_θ1)
          refine ⟨p_comp, hL_le_comp, le_of_lt hp_lt, D_pure,
            (IsPureBlockadeIn.isWeaklySparseOrCoSparseBlockadeIn hD_pure (le_of_lt hη_pos)).mono_ambient_width_eps
              Finset.Subset.rfl ?_ le_rfl⟩
          unfold splitTreeD
          rw [show 60 * 1 = 60 by omega, show 2 * 8 = 16 by omega]
          have hk_ge1 : (1 : ℝ) ≤ (p_comp : ℝ) := Nat.one_le_cast.mpr (by omega)
          have hk_10_16 : (p_comp : ℝ) ^ 10 ≤ (p_comp : ℝ) ^ 16 := pow_le_pow_right₀ hk_ge1 (by omega)
          have h64 : (64 : ℝ) ≤ (2 : ℝ) ^ 60 := by norm_num
          calc w / ((2 : ℝ) ^ 60 * (p_comp : ℝ) ^ 16)
              ≤ w / (64 * (p_comp : ℝ) ^ 10) :=
                div_le_div_of_nonneg_left hw_nn (by positivity)
                  (mul_le_mul h64 hk_10_16 (by positivity) (by positivity))
            _ ≤ τ_i := h_w_split
      · left
        push_neg at h_dense_nonneigh
        have h_sparse_compl : ∀ (i j : Fin ℓ), j ≠ i → ∀ u ∈ M_star j,
            (¬∀ z ∈ M_star i, Fᶜ.Adj u z) →
            ((neighborFinsetIn Fᶜ u (M_star i)).card : ℝ) < (η_out / (2 * (ℓ : ℝ))) * ((M_star i).card : ℝ) := by
          intro i j hji u hu_Mj hu_not_comp_c
          push_neg at hu_not_comp_c
          obtain ⟨z₀, hz₀_Ms, hz₀_nadj_c⟩ := hu_not_comp_c
          have huz₀_ne : u ≠ z₀ :=
            fun h => Finset.disjoint_left.mp (hB_block.pairwise_disjoint j i hji)
              (hMs_sub_B j hu_Mj) (h ▸ hMs_sub_B i hz₀_Ms)
          have huz₀_adj : F.Adj u z₀ :=
            Classical.byContradiction (fun hn => hz₀_nadj_c ⟨huz₀_ne, hn⟩)
          have h_sub : neighborFinsetIn Fᶜ u (M_star i) ⊆ (M_star i) \ neighborFinsetIn F u (M_star i) := by
            intro z hz
            obtain ⟨hz_Ms, _, hnadj⟩ := (ErdosHajnalP6.mem_neighborFinsetIn_iff Fᶜ u (M_star i) z).mp hz
            exact Finset.mem_sdiff.mpr ⟨hz_Ms,
              fun h => hnadj ((ErdosHajnalP6.mem_neighborFinsetIn_iff F u (M_star i) z).mp h).2⟩
          exact lt_of_le_of_lt (Nat.cast_le.mpr (Finset.card_le_card h_sub))
            (h_dense_nonneigh i j hji u hu_Mj ⟨z₀, hMs_sub_MT i hz₀_Ms, huz₀_adj⟩)
        have hM_width : ∀ i : Fin ℓ, (2 : ℝ)⁻¹ ^ 3 * (L_max : ℝ)⁻¹ ^ 8 * w ≤ ((M_star i).card : ℝ) := by
          intro i
          have h1 := hMs_gt_w1 i
          have h_eq : (2 : ℝ)⁻¹ ^ 3 * (L_max : ℝ)⁻¹ ^ 8 * w = (8 / 64 : ℝ) * (w / (L_max : ℝ) ^ 8) := by
            rw [inv_pow]; norm_num; ring
          have h_pos : 0 ≤ w / (L_max : ℝ) ^ 8 := by positivity
          linarith
        obtain ⟨D, _, hD_block_c⟩ := prop1_cross_block_purification (F := Fᶜ)
          hℓ_16 hη_pos hη_ub hB_sub_U hB_block.pairwise_disjoint hMs_sub_B hMs_ne hM_width h_sparse_compl
        have hD_weak : IsWeaklySparseOrCoSparseBlockadeIn F U_ambient ℓ
            ((2 : ℝ)⁻¹ ^ 4 * (L_max : ℝ)⁻¹ ^ 8 * w) η_out D := by
          have h1c := IsCompleteOrXSparseBlockadeIn.isWeaklySparseOrCoSparseBlockadeIn hD_block_c (le_of_lt hη_pos)
          have h1 : IsWeaklySparseOrCoSparseBlockadeIn F U_ambient ℓ
              ((2 : ℝ)⁻¹ ^ 3 * (L_max : ℝ)⁻¹ ^ 8 * w / 2) η_out D :=
            ⟨⟨h1c.1.1, h1c.1.2, h1c.1.3, h1c.1.4⟩,
             fun i j hij => (h1c.2 i j hij).elim
               (fun ha => Or.inr ha)
               (fun hb => Or.inl (by simpa [compl_compl] using hb))⟩
          exact h1.mono_ambient_width_eps Finset.Subset.rfl (by norm_num; ring_nf; exact le_rfl) le_rfl
        refine ⟨ℓ, hL_high, hp_cap, D, hD_weak.mono_ambient_width_eps Finset.Subset.rfl ?_ le_rfl⟩
        unfold splitTreeD
        rw [show 60 * 1 = 60 by omega, show 2 * 8 = 16 by omega]
        have hL_le_ℓ : (L_max : ℝ) ^ 8 ≤ (ℓ : ℝ) ^ 16 := by
          calc (L_max : ℝ) ^ 8 ≤ (ℓ : ℝ) ^ 8 :=
                pow_le_pow_left₀ (by positivity) (Nat.cast_le.mpr hL_high) 8
            _ ≤ (ℓ : ℝ) ^ 16 := pow_le_pow_right₀ (by linarith) (by omega)
        have h_2 : (2 : ℝ) ^ 4 ≤ (2 : ℝ) ^ 60 := by norm_num
        have h_eq : (2 : ℝ)⁻¹ ^ 4 * (L_max : ℝ)⁻¹ ^ 8 * w = w / ((2 : ℝ) ^ 4 * (L_max : ℝ) ^ 8) := by
          rw [inv_pow, inv_pow]; ring
        rw [h_eq]
        exact div_le_div_of_nonneg_left hw_nn (by positivity)
          (mul_le_mul h_2 hL_le_ℓ (by positivity) (by positivity))

/-- Depth-$d$ Core Dichotomy for any graph family `H_fam` satisfying `HasNonNeighPureGrouping H_fam`
(`general_depth_d_nonneigh_core_dichotomy`): at chain depth $d \ge 1$, forbidding `(H_fam (s + 1 + d))ᶜ`
either extracts a pairwise-pure $(p_{\mathrm{comp}}, 5 \theta |N^*|)$-blockade inside $N^*$ or
finds a large subset $A_* \subseteq A_{\mathrm{pool}}$ that is anticomplete or co-sparse to $N^*$. -/
theorem general_depth_d_nonneigh_core_dichotomy
    {H_fam : (d : ℕ) → SimpleGraph (Fin (d + 4))}
    (h_grp : HasNonNeighPureGrouping H_fam)
    {V : Type} [Fintype V] [DecidableEq V]
    {F : SimpleGraph V} {S : Finset V}
    {ℓ s d p_comp : ℕ} {w θ : ℝ} {a : Fin ℓ → V} {B : Fin ℓ → Finset V}
    {stems : Fin ℓ → Fin s → V} {i j : Fin ℓ}
    (hij : i ≠ j) (hd : 1 ≤ d) (hθ_pos : 0 < θ)
    (hfree : IsInducedSubgraphFree F (H_fam (s + 1 + d))ᶜ)
    (hcomb : IsCombOrCoCombIn F S ℓ w a B)
    (hstems : HasPerHandleApexStems F S ℓ s a B stems)
    (z : Fin d → V) (M : Fin (d + 1) → Finset V)
    (hz0 : z ⟨0, hd⟩ ∈ B j) (hM0 : M 0 ⊆ B i)
    (hM_step : ∀ c : Fin d, M c.succ ⊆ neighborFinsetIn F (z c) (M c.castSucc))
    (hz_step : ∀ c : Fin d, ∀ hc1 : 1 ≤ c.1,
      z c ∈ M ⟨c.1 - 1, by omega⟩ ∧ ¬F.Adj (z ⟨c.1 - 1, by omega⟩) (z c))
    {N_star A_pool : Finset V}
    (hNs_sub : N_star ⊆ M (Fin.last d)) (hNs_ne : N_star.Nonempty)
    (hNs_small : ∀ X : Finset V,
      IsProperModuleIn F (M (Fin.last d)) X → (X ∩ N_star).Nonempty →
      (X.card : ℝ) < 5 * θ * (N_star.card : ℝ))
    (hA_in : ∀ v ∈ A_pool, v ∈ M ⟨d - 1, by omega⟩ ∧ ¬F.Adj (z ⟨d - 1, by omega⟩) v) :
    (∃ D : Fin p_comp → Finset V,
      IsPureBlockadeIn F N_star p_comp (5 * θ * (N_star.card : ℝ)) D) ∨
    (∃ A_star ⊆ A_pool,
      (A_pool.card : ℝ) / 2 ≤ (A_star.card : ℝ) ∧
      Disjoint N_star A_star ∧
      (IsAnticompletePair F N_star A_star ∨
       IsXSparseTo Fᶜ A_star N_star (10 * (p_comp : ℝ) * θ))) := by
  classical
  let τ := 5 * θ * (N_star.card : ℝ)
  have hτ_pos : 0 < τ := by
    unfold τ
    have : 0 < (N_star.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hNs_ne)
    positivity
  have hNA_disj : Disjoint N_star A_pool := by
    rw [Finset.disjoint_left]
    intro x hxN hxA
    have hc_last : (⟨d - 1, by omega⟩ : Fin d).succ = Fin.last d := by ext; dsimp; omega
    have hx_in_Z : x ∈ neighborFinsetIn F (z ⟨d - 1, by omega⟩) (M ⟨d - 1, by omega⟩) := by
      have h1 : M (Fin.last d) ⊆ neighborFinsetIn F (z ⟨d - 1, by omega⟩) (M ⟨d - 1, by omega⟩) := by
        rw [← hc_last]; exact hM_step ⟨d - 1, by omega⟩
      exact h1 (hNs_sub hxN)
    exact (hA_in x hxA).2 ((ErdosHajnalP6.mem_neighborFinsetIn_iff F _ _ x).mp hx_in_Z).2
  by_cases h_dense : ∃ w_cut ∈ A_pool,
      (∃ x ∈ M (Fin.last d), F.Adj w_cut x) ∧
      2 * (p_comp : ℝ) * τ ≤ ((N_star \ neighborFinsetIn F w_cut N_star).card : ℝ)
  · left
    obtain ⟨w_cut, hw_in, hw_ex_adj, hw_deg⟩ := h_dense
    let z_full : Fin (d + 1) → V := fun c =>
      if hcd : c.1 < d then z ⟨c.1, hcd⟩ else w_cut
    have hz_full_lt : ∀ c : Fin (d + 1), ∀ hcd : c.1 < d, z_full c = z ⟨c.1, hcd⟩ :=
      fun c hcd => dif_pos hcd
    have hz_full_last : z_full (Fin.last d) = w_cut := dif_neg (by dsimp; omega)
    have hz_full_0 : z_full 0 ∈ B j := by
      rw [hz_full_lt 0 (by simp; omega)]; exact hz0
    have hM_full_step : ∀ c : Fin d,
        M c.succ ⊆ neighborFinsetIn F (z_full c.castSucc) (M c.castSucc) := by
      intro c
      rw [hz_full_lt c.castSucc c.2]; exact hM_step c
    have hz_full_step : ∀ c : Fin d,
        z_full c.succ ∈ M c.castSucc ∧ ¬F.Adj (z_full c.castSucc) (z_full c.succ) := by
      intro c
      rw [hz_full_lt c.castSucc c.2]
      by_cases hc1 : c.1 + 1 < d
      · rw [hz_full_lt c.succ hc1]
        have h_st := hz_step ⟨c.1 + 1, hc1⟩ (by simp)
        have h_eq : (⟨(⟨c.1 + 1, hc1⟩ : Fin d).1 - 1, by omega⟩ : Fin d) = c := by ext; simp
        have h_eqM : (⟨(⟨c.1 + 1, hc1⟩ : Fin d).1 - 1, by omega⟩ : Fin (d + 1)) = c.castSucc := by ext; simp
        rwa [h_eq, h_eqM] at h_st
      · have hc_succ_last : c.succ = Fin.last d := by ext; dsimp; omega
        rw [hc_succ_last, hz_full_last]
        have hc_eq : c = ⟨d - 1, by omega⟩ := by ext; dsimp; omega
        rw [hc_eq]
        exact hA_in w_cut hw_in
    have hw_ex_adj' : ∃ x ∈ M (Fin.last d), F.Adj (z_full (Fin.last d)) x := by
      rwa [hz_full_last]
    have hw_deg' : 2 * (p_comp : ℝ) * τ ≤
        ((N_star \ neighborFinsetIn F (z_full (Fin.last d)) N_star).card : ℝ) := by
      rwa [hz_full_last]
    exact h_grp hij hτ_pos hfree hcomb hstems z_full M hz_full_0 hM0 hM_full_step hz_full_step
      hNs_sub hw_ex_adj'
      (fun X hX hX_ne => le_trans (Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_left))
        (le_of_lt (hNs_small X hX hX_ne)))
      hw_deg'
  · right
    push_neg at h_dense
    let A_anti := A_pool.filter (fun v => ∀ x ∈ N_star, ¬F.Adj v x)
    let A_cosp := A_pool \ A_anti
    have hA_anti_sub : A_anti ⊆ A_pool := Finset.filter_subset _ _
    have hA_cosp_sub : A_cosp ⊆ A_pool := Finset.sdiff_subset
    have hA_sum : (A_cosp.card : ℝ) + (A_anti.card : ℝ) = (A_pool.card : ℝ) := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card hA_anti_sub
    have hA_cosp_sparse : IsXSparseTo Fᶜ A_cosp N_star (10 * (p_comp : ℝ) * θ) := by
      intro v hv
      obtain ⟨hvA, hv_not_anti⟩ := Finset.mem_sdiff.mp hv
      have hv_ex_Ns : ∃ x ∈ N_star, F.Adj v x := by
        by_contra! h_no
        exact hv_not_anti (Finset.mem_filter.mpr ⟨hvA, h_no⟩)
      obtain ⟨x₀, hx₀_Ns, hx₀_adj⟩ := hv_ex_Ns
      have h_sub : neighborFinsetIn Fᶜ v N_star ⊆ N_star \ neighborFinsetIn F v N_star := by
        intro x hx
        obtain ⟨hxN, _, hnadj⟩ := (ErdosHajnalP6.mem_neighborFinsetIn_iff Fᶜ v N_star x).mp hx
        exact Finset.mem_sdiff.mpr ⟨hxN,
          fun h => hnadj ((ErdosHajnalP6.mem_neighborFinsetIn_iff F v N_star x).mp h).2⟩
      have h_lt := lt_of_le_of_lt (Nat.cast_le.mpr (Finset.card_le_card h_sub))
        (h_dense v hvA ⟨x₀, hNs_sub hx₀_Ns, hx₀_adj⟩)
      have h_eq : 2 * (p_comp : ℝ) * τ = (10 * (p_comp : ℝ) * θ) * (N_star.card : ℝ) := by
        unfold τ; ring
      linarith
    by_cases h_half : A_cosp.card ≤ A_anti.card
    · have h_r : (A_cosp.card : ℝ) ≤ (A_anti.card : ℝ) := Nat.cast_le.mpr h_half
      refine ⟨A_anti, hA_anti_sub, by linarith,
        Finset.disjoint_of_subset_right hA_anti_sub hNA_disj,
        Or.inl (fun x hx v hv hadj => (Finset.mem_filter.mp hv).2 x hx (F.symm hadj))⟩
    · have h_r : (A_anti.card : ℝ) ≤ (A_cosp.card : ℝ) := Nat.cast_le.mpr (by omega)
      refine ⟨A_cosp, hA_cosp_sub, by linarith,
        Finset.disjoint_of_subset_right hA_cosp_sub hNA_disj,
        Or.inr hA_cosp_sparse⟩

/-- Pairwise-pure blockade counterpart of `complete_blockade_at_pcomp_global`: resolves a
pairwise-pure $(p_{\mathrm{comp}}, 5 \theta_r |N^*|)$-blockade inside $N^* \subseteq W_z \subseteq U_{\mathrm{ambient}}$. -/
lemma pure_blockade_at_pcomp_global {V : Type*} [Fintype V] [DecidableEq V]
    {F : SimpleGraph V} {U_ambient W_z N_star : Finset V}
    {r d ℓ p_cap p_comp L_max : ℕ} {η_out η₀ θ_r w : ℝ}
    {D : Fin p_comp → Finset V}
    (hr : 2 ≤ r) (hd : d ≤ r - 1) (hℓ : 64 ≤ ℓ) (hp_cap : ℓ ≤ p_cap)
    (hL_low : 2 ≤ L_max) (hL_high : L_max ≤ ℓ)
    (hp_comp_cases : p_comp = p_cap ∨ (p_comp < p_cap ∧ 8 * (ℓ : ℝ) ^ 2 * η₀⁻¹ ≤ (p_comp : ℝ)))
    (hη_pos : 0 < η_out) (hη_ub : η_out ≤ 1)
    (hη₀_pos : 0 < η₀) (hη₀_ub : η₀ ≤ 1)
    (hθ_def : θ_r = η₀ / (64 * (ℓ : ℝ) * (p_comp : ℝ) ^ 2))
    (hθ_pos : 0 < θ_r)
    (hθ_lb : (2 : ℝ)⁻¹ ^ (120 * r + 8) * (p_cap : ℝ)⁻¹ ^ (4 * splitTreeD r + 3) * η_out ≤ θ_r)
    (hw_nn : 0 ≤ w)
    (hWz_sub : W_z ⊆ U_ambient)
    (hWz_active : w / (L_max : ℝ) ^ (splitTreeD r) ≤ (W_z.card : ℝ))
    (hNs_sub : N_star ⊆ W_z)
    (hNs_card : (W_z.card : ℝ) / (2 : ℝ) ^ (23 * d + 3) ≤ (N_star.card : ℝ))
    (hD_pure : IsPureBlockadeIn F N_star p_comp (5 * θ_r * (N_star.card : ℝ)) D) :
    (∃ U : Fin p_cap → Finset V,
      IsWeaklySparseOrCoSparseBlockadeIn F U_ambient p_cap
        ((2 : ℝ) ^ (-(200 * (r : ℝ) ^ 2)) * η_out ^ r * (p_cap : ℝ) ^ (-(capExpE r : ℝ)) * w)
        η_out U) ∨
    (∃ k : ℕ, L_max ≤ k ∧ k ≤ p_cap ∧
      ∃ U : Fin k → Finset V,
        IsWeaklySparseOrCoSparseBlockadeIn F U_ambient k
          (w / ((2 : ℝ) ^ (60 * r) * (k : ℝ) ^ (2 * splitTreeD r))) η_out U) := by
  have hp_64 : 64 ≤ p_cap := le_trans hℓ hp_cap
  have hL_pos : (0 : ℝ) < (L_max : ℝ) := Nat.cast_pos.mpr (by omega)
  have hD_weak := (IsPureBlockadeIn.isWeaklySparseOrCoSparseBlockadeIn
    hD_pure (le_of_lt hη_pos)).mono_ambient_width_eps (hNs_sub.trans hWz_sub) le_rfl le_rfl
  rcases hp_comp_cases with rfl | ⟨hp_lt_cap, hp_ge_ceil⟩
  · left
    refine ⟨D, hD_weak.mono_ambient_width_eps Finset.Subset.rfl ?_ le_rfl⟩
    have hL_p : (L_max : ℝ) ^ (splitTreeD r) ≤ (p_comp : ℝ) ^ (splitTreeD r) :=
      pow_le_pow_left₀ (by positivity) (Nat.cast_le.mpr (le_trans hL_high hp_cap)) (splitTreeD r)
    have hWz_pcap : w / (p_comp : ℝ) ^ (splitTreeD r) ≤ (W_z.card : ℝ) :=
      le_trans (div_le_div_of_nonneg_left hw_nn (by positivity) hL_p) hWz_active
    have h_cap := theta_r_cap_width_le hr hd hp_64 hη_pos hη_ub hw_nn hθ_lb hWz_pcap
    have h_5_Ns : (W_z.card : ℝ) / (2 : ℝ) ^ (23 * d + 1) ≤ 5 * (N_star.card : ℝ) := by
      calc (W_z.card : ℝ) / (2 : ℝ) ^ (23 * d + 1)
          = 4 * ((W_z.card : ℝ) / (2 : ℝ) ^ (23 * d + 3)) := by
            rw [show 23 * d + 3 = (23 * d + 1) + 2 by omega, pow_add]; ring
        _ ≤ 5 * (N_star.card : ℝ) := by linarith
    calc (2 : ℝ) ^ (-(200 * (r : ℝ) ^ 2)) * η_out ^ r * (p_comp : ℝ) ^ (-(capExpE r : ℝ)) * w
        ≤ θ_r * ((W_z.card : ℝ) / (2 : ℝ) ^ (23 * d + 1)) := h_cap
      _ ≤ θ_r * (5 * (N_star.card : ℝ)) := mul_le_mul_of_nonneg_left h_5_Ns (le_of_lt hθ_pos)
      _ = 5 * θ_r * (N_star.card : ℝ) := by ring
  · right
    have hℓ_r : (64 : ℝ) ≤ (ℓ : ℝ) := Nat.ofNat_le_cast.mpr hℓ
    have hη₀_inv_ge1 : 1 ≤ η₀⁻¹ := one_le_inv₀ hη₀_pos |>.mpr hη₀_ub
    have h_ell_le_pcomp : ℓ ≤ p_comp := by
      have h1 : (ℓ : ℝ) ≤ 8 * (ℓ : ℝ) ^ 2 * η₀⁻¹ := by nlinarith
      exact Nat.cast_le.mp (le_trans h1 hp_ge_ceil)
    have hL_le_pcomp : L_max ≤ p_comp := le_trans hL_high h_ell_le_pcomp
    have hp_comp_pos : (0 : ℝ) < (p_comp : ℝ) := Nat.cast_pos.mpr (by omega)
    have hp_comp_ge1 : (1 : ℝ) ≤ (p_comp : ℝ) := Nat.one_le_cast.mpr (by omega)
    refine ⟨p_comp, hL_le_pcomp, le_of_lt hp_lt_cap, D,
      hD_weak.mono_ambient_width_eps Finset.Subset.rfl ?_ le_rfl⟩
    have hθ_ge_inv_p3 : 1 / (p_comp : ℝ) ^ 3 ≤ θ_r := by
      have h_eta_lb : 8 * (ℓ : ℝ) ^ 2 / (p_comp : ℝ) ≤ η₀ := by
        rw [div_le_iff₀ hp_comp_pos]
        have h1 := mul_le_mul_of_nonneg_right hp_ge_ceil (le_of_lt hη₀_pos)
        rwa [mul_assoc, inv_mul_cancel₀ (ne_of_gt hη₀_pos), mul_one, mul_comm (p_comp : ℝ) η₀] at h1
      rw [hθ_def]
      calc 1 / (p_comp : ℝ) ^ 3
          ≤ ((ℓ : ℝ) / 8) / (p_comp : ℝ) ^ 3 := by
            refine div_le_div_of_nonneg_right ?_ (by positivity)
            linarith
        _ = (8 * (ℓ : ℝ) ^ 2 / (p_comp : ℝ)) / (64 * (ℓ : ℝ) * (p_comp : ℝ) ^ 2) := by
            field_simp; ring
        _ ≤ η₀ / (64 * (ℓ : ℝ) * (p_comp : ℝ) ^ 2) :=
            div_le_div_of_nonneg_right h_eta_lb (by positivity)
    have hL_p_D : (L_max : ℝ) ^ (splitTreeD r) ≤ (p_comp : ℝ) ^ (splitTreeD r) :=
      pow_le_pow_left₀ (by positivity) (Nat.cast_le.mpr hL_le_pcomp) (splitTreeD r)
    have h2_pow : (2 : ℝ) ^ (23 * d + 3) ≤ (2 : ℝ) ^ (60 * r) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hp_pow : (p_comp : ℝ) ^ (splitTreeD r) * (p_comp : ℝ) ^ 3 ≤
        (p_comp : ℝ) ^ (2 * splitTreeD r) := by
      rw [← pow_add]
      have : 8 ≤ splitTreeD r := by have := (splitTreeD_eq_eight_mul r hr).2.1; omega
      exact pow_le_pow_right₀ hp_comp_ge1 (by omega)
    calc w / ((2 : ℝ) ^ (60 * r) * (p_comp : ℝ) ^ (2 * splitTreeD r))
        ≤ w / ((2 : ℝ) ^ (23 * d + 3) * ((p_comp : ℝ) ^ (splitTreeD r) * (p_comp : ℝ) ^ 3)) :=
          div_le_div_of_nonneg_left hw_nn (by positivity)
            (mul_le_mul h2_pow hp_pow (by positivity) (by positivity))
      _ = (1 / (p_comp : ℝ) ^ 3) *
            ((w / (p_comp : ℝ) ^ (splitTreeD r)) / (2 : ℝ) ^ (23 * d + 3)) := by ring
      _ ≤ θ_r * ((W_z.card : ℝ) / (2 : ℝ) ^ (23 * d + 3)) := by
          refine mul_le_mul hθ_ge_inv_p3 ?_ (by positivity) (le_of_lt hθ_pos)
          exact div_le_div_of_nonneg_right
            (le_trans (div_le_div_of_nonneg_left hw_nn (by positivity) hL_p_D) hWz_active)
            (by positivity)
      _ ≤ 5 * θ_r * (N_star.card : ℝ) := by
          have h1 : θ_r * ((W_z.card : ℝ) / (2 : ℝ) ^ (23 * d + 3)) ≤ θ_r * (N_star.card : ℝ) :=
            mul_le_mul_of_nonneg_left hNs_card (le_of_lt hθ_pos)
          have h2 : 0 ≤ θ_r * (N_star.card : ℝ) := by positivity
          linarith

/-- Regime A / Regime B recursive call resolver for `Stage1FamilyStrongAt H_fam`. -/
theorem resolve_recursive_family_call
    {H_fam : (d : ℕ) → SimpleGraph (Fin (d + 4))}
    {V : Type} [Fintype V] [DecidableEq V]
    {F : SimpleGraph V} {S U_ambient W_z M_base : Finset V}
    {r r' d s' k_comb p_cap L_max : ℕ} {η_out η₀ w w_sub : ℝ}
    {u : Fin k_comb → V} {B' : Fin k_comb → Finset V}
    {stems' : Fin k_comb → Fin s' → V}
    (hr : 2 ≤ r) (hr'1 : 1 ≤ r') (hr'r : r' < r) (hr_sum : r' + d + 1 = r)
    (hs' : 1 ≤ s') (hp_cap : 64 ≤ p_cap) (hL_low : 2 ≤ L_max) (hL_high : L_max ≤ p_cap)
    (hη_pos : 0 < η_out) (hη_ub : η_out ≤ (2 : ℝ)⁻¹ ^ 16)
    (hη₀_pos : 0 < η₀) (hη₀_le_out : η₀ ≤ η_out)
    (hη₀_lb : (2 : ℝ)⁻¹ ^ (120 * r + 2) * (p_cap : ℝ)⁻¹ ^ (4 * splitTreeD r) * η_out ≤ η₀)
    (hIH : Stage1FamilyStrongAt H_fam r')
    (hfree : IsInducedSubgraphFree F (H_fam (s' + r'))ᶜ)
    (hWz_sub : W_z ⊆ U_ambient)
    (hWz_active : w / (L_max : ℝ) ^ (splitTreeD r) ≤ (W_z.card : ℝ))
    (hM_sub : M_base ⊆ W_z)
    (hM_card : (W_z.card : ℝ) / (2 : ℝ) ^ (23 * d + 3) ≤ (M_base.card : ℝ))
    (hk_64 : 64 ≤ k_comb)
    (hB'_sub : ∀ q : Fin k_comb, B' q ⊆ M_base)
    (hcomb' : IsCombOrCoCombIn F S k_comb w_sub u B')
    (hstems' : HasPerHandleApexStems F S k_comb s' u B' stems')
    (hw_ge : combMinWidth r η_out p_cap ≤ w)
    (hw_sub_k : (M_base.card : ℝ) / (16 * (k_comb : ℝ) ^ 2) ≤ w_sub)
    (hw_sub_lb : (2 : ℝ)⁻¹ ^ (145 * r + 10) * (p_cap : ℝ)⁻¹ ^ (5 * splitTreeD r + 2) * η_out * w ≤ w_sub)
    (hw_sub_cap :
      (2 : ℝ)⁻¹ ^ ((120 * r + 2) * (r - 1) + 25 * r + 10) *
      (p_cap : ℝ)⁻¹ ^ ((4 * r' + 5) * splitTreeD r + 2) *
      η_out ^ r * w ≤ η₀ ^ r' * w_sub) :
    (∃ U : Fin p_cap → Finset V,
      IsWeaklySparseOrCoSparseBlockadeIn F U_ambient p_cap
        ((2 : ℝ) ^ (-(200 * (r : ℝ) ^ 2)) * η_out ^ r * (p_cap : ℝ) ^ (-(capExpE r : ℝ)) * w)
        η_out U) ∨
    (∃ k : ℕ, L_max ≤ k ∧ k ≤ p_cap ∧
      ∃ U : Fin k → Finset V,
        IsWeaklySparseOrCoSparseBlockadeIn F U_ambient k
          (w / ((2 : ℝ) ^ (60 * r) * (k : ℝ) ^ (2 * splitTreeD r))) η_out U) ∨
    (∃ (k : ℕ) (U : Fin k → Finset V),
      64 ≤ k ∧ k < L_max ∧
      IsWeaklySparseOrCoSparseBlockadeIn F W_z k
        ((W_z.card : ℝ) / ((2 : ℝ) ^ 60 * (k : ℝ) ^ (5 * (splitTreeD r / 8)))) η₀ U) := by
  have hp_pos : (0 : ℝ) < (p_cap : ℝ) := Nat.cast_pos.mpr (by omega)
  have hw_pos : 0 ≤ w := by
    have : 0 < combMinWidth r η_out p_cap := by unfold combMinWidth; positivity
    linarith
  have hη_le1 : η_out ≤ 1 := le_trans hη_ub (by norm_num)
  have hη₀_ub : η₀ ≤ (2 : ℝ)⁻¹ ^ 16 := le_trans hη₀_le_out hη_ub
  have hη₀_le1 : η₀ ≤ 1 := le_trans hη₀_le_out hη_le1
  have hw_sub_min : combMinWidth r' η₀ p_cap ≤ w_sub :=
    combMinWidth_recursive_le hr hr'1 hr'r hp_cap hη_pos hη_le1 hη₀_pos hη₀_lb hw_ge hw_sub_lb
  have hw_sub_nn : 0 ≤ w_sub := by
    have : 0 < combMinWidth r' η₀ p_cap := by unfold combMinWidth; positivity
    linarith
  have h_cap_le := cap_width_recursive_le hr hr'1 hr'r hp_cap hη_pos hw_pos hw_sub_cap
  let k' := min k_comb p_cap
  have hk'_le_comb : k' ≤ k_comb := Nat.min_le_left _ _
  have hk'_le_pcap : k' ≤ p_cap := Nat.min_le_right _ _
  have hk'_64 : 64 ≤ k' := le_min hk_64 hp_cap
  obtain ⟨hcomb_k', hstems_k', hU_sub_B'⟩ :=
    restrict_combOrCoComb_and_stems hk'_le_comb hcomb' hstems'
  let B'_k' : Fin k' → Finset V := fun i => B' (Fin.castLE hk'_le_comb i)
  have hUk'_sub_Wz : Finset.univ.biUnion B'_k' ⊆ W_z := by
    refine hU_sub_B'.trans ?_
    rw [Finset.biUnion_subset]
    exact fun q _ => (hB'_sub q).trans hM_sub
  have h_ih := hIH hr'1 V F S s' k' p_cap k' η₀ w_sub
    (fun i => u (Fin.castLE hk'_le_comb i)) B'_k'
    (fun i => stems' (Fin.castLE hk'_le_comb i))
    hs' hk'_64 hk'_le_pcap (by omega) le_rfl hη₀_pos hη₀_ub hfree hcomb_k' hstems_k' hw_sub_min
  by_cases h_regA : k_comb ≤ p_cap
  · have hk'_eq : k' = k_comb := Nat.min_eq_left h_regA
    rcases h_ih with ⟨k, hk'_le_k, hk_le_pcap, U, hU⟩ | ⟨U, hU_cap⟩
    · have hk_comb_le_k : k_comb ≤ k := hk'_eq ▸ hk'_le_k
      have hk_64_out : 64 ≤ k := le_trans hk_64 hk_comb_le_k
      have hk_ge1 : (1 : ℝ) ≤ (k : ℝ) := Nat.one_le_cast.mpr (by omega)
      have h_width_Wz : (W_z.card : ℝ) / ((2 : ℝ) ^ 60 * (k : ℝ) ^ (5 * (splitTreeD r / 8))) ≤
          w_sub / ((2 : ℝ) ^ (60 * r') * (k : ℝ) ^ (2 * splitTreeD r')) := by
        have hk_comb_le_k_r : (k_comb : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (Nat.cast_le.mpr hk_comb_le_k) 2
        have hw_sub_Wz : (W_z.card : ℝ) / ((2 : ℝ) ^ (23 * d + 7) * (k : ℝ) ^ 2) ≤ w_sub := by
          calc (W_z.card : ℝ) / ((2 : ℝ) ^ (23 * d + 7) * (k : ℝ) ^ 2)
              ≤ (W_z.card : ℝ) / ((2 : ℝ) ^ (23 * d + 7) * (k_comb : ℝ) ^ 2) :=
                div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
                  (mul_le_mul_of_nonneg_left hk_comb_le_k_r (by positivity))
            _ = ((W_z.card : ℝ) / (2 : ℝ) ^ (23 * d + 3)) / (16 * (k_comb : ℝ) ^ 2) := by
                rw [show 23 * d + 7 = (23 * d + 3) + 4 by omega, pow_add]; norm_num; ring
            _ ≤ (M_base.card : ℝ) / (16 * (k_comb : ℝ) ^ 2) :=
                div_le_div_of_nonneg_right hM_card (by positivity)
            _ ≤ w_sub := hw_sub_k
        have h_2_60r : (2 : ℝ) ^ (60 * r' + (23 * d + 7)) ≤ (k : ℝ) ^ (10 * r) := by
          have h_exp_le : 60 * r' + (23 * d + 7) ≤ 60 * r := by omega
          have h1 : (2 : ℝ) ^ (60 * r' + (23 * d + 7)) ≤ (2 : ℝ) ^ (60 * r) :=
            pow_le_pow_right₀ (by norm_num) h_exp_le
          have h64 : (2 : ℝ) ^ 6 ≤ (k : ℝ) := by
            have : (64 : ℝ) ≤ (k : ℝ) := Nat.ofNat_le_cast.mpr hk_64_out
            norm_num at this ⊢; exact this
          have h2 : ((2 : ℝ) ^ 6) ^ (10 * r) ≤ (k : ℝ) ^ (10 * r) :=
            pow_le_pow_left₀ (by positivity) h64 (10 * r)
          rw [← pow_mul, show 6 * (10 * r) = 60 * r by ring] at h2
          exact le_trans h1 h2
        have h_exp_k := splitTreeD_type1_exp_bound r r' hr hr'r
        have h_den : (2 : ℝ) ^ (60 * r') * (2 : ℝ) ^ (23 * d + 7) *
            ((k : ℝ) ^ 2 * (k : ℝ) ^ (2 * splitTreeD r')) ≤
            (2 : ℝ) ^ 60 * (k : ℝ) ^ (5 * (splitTreeD r / 8)) := by
          calc (2 : ℝ) ^ (60 * r') * (2 : ℝ) ^ (23 * d + 7) *
                ((k : ℝ) ^ 2 * (k : ℝ) ^ (2 * splitTreeD r'))
              = (2 : ℝ) ^ (60 * r' + (23 * d + 7)) * (k : ℝ) ^ (2 * splitTreeD r' + 2) := by
                rw [← pow_add, ← pow_add]; ring
            _ ≤ (k : ℝ) ^ (10 * r) * (k : ℝ) ^ (2 * splitTreeD r' + 2) :=
                mul_le_mul_of_nonneg_right h_2_60r (by positivity)
            _ = 1 * (k : ℝ) ^ (2 * splitTreeD r' + 2 + 10 * r) := by rw [← pow_add]; ring
            _ ≤ (2 : ℝ) ^ 60 * (k : ℝ) ^ (5 * (splitTreeD r / 8)) := by
                refine mul_le_mul (by norm_num) ?_ (by positivity) (by positivity)
                exact pow_le_pow_right₀ hk_ge1 h_exp_k
        calc (W_z.card : ℝ) / ((2 : ℝ) ^ 60 * (k : ℝ) ^ (5 * (splitTreeD r / 8)))
            ≤ (W_z.card : ℝ) / ((2 : ℝ) ^ (60 * r') * (2 : ℝ) ^ (23 * d + 7) *
                ((k : ℝ) ^ 2 * (k : ℝ) ^ (2 * splitTreeD r'))) :=
              div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) h_den
          _ = ((W_z.card : ℝ) / ((2 : ℝ) ^ (23 * d + 7) * (k : ℝ) ^ 2)) /
                ((2 : ℝ) ^ (60 * r') * (k : ℝ) ^ (2 * splitTreeD r')) := by ring
          _ ≤ w_sub / ((2 : ℝ) ^ (60 * r') * (k : ℝ) ^ (2 * splitTreeD r')) :=
              div_le_div_of_nonneg_right hw_sub_Wz (by positivity)
      by_cases hk_lt_L : k < L_max
      · right; right
        exact ⟨k, U, hk_64_out, hk_lt_L,
          hU.mono_ambient_width_eps hUk'_sub_Wz h_width_Wz le_rfl⟩
      · right; left
        push_neg at hk_lt_L
        refine ⟨k, hk_lt_L, hk_le_pcap, U,
          hU.mono_ambient_width_eps (hUk'_sub_Wz.trans hWz_sub) ?_ hη₀_le_out⟩
        have hL_le_k_D : (L_max : ℝ) ^ (splitTreeD r) ≤ (k : ℝ) ^ (splitTreeD r) :=
          pow_le_pow_left₀ (by positivity) (Nat.cast_le.mpr hk_lt_L) (splitTreeD r)
        have h_Dr_sum : splitTreeD r + 5 * (splitTreeD r / 8) ≤ 2 * splitTreeD r := by
          have := (splitTreeD_eq_eight_mul r hr).1; omega
        have hk_sum_le : (k : ℝ) ^ (splitTreeD r) * (k : ℝ) ^ (5 * (splitTreeD r / 8)) ≤
            (k : ℝ) ^ (2 * splitTreeD r) := by
          rw [← pow_add]; exact pow_le_pow_right₀ hk_ge1 h_Dr_sum
        have h2_60_le : (2 : ℝ) ^ 60 ≤ (2 : ℝ) ^ (60 * r) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        calc w / ((2 : ℝ) ^ (60 * r) * (k : ℝ) ^ (2 * splitTreeD r))
            ≤ w / ((2 : ℝ) ^ 60 * ((k : ℝ) ^ (splitTreeD r) * (k : ℝ) ^ (5 * (splitTreeD r / 8)))) :=
              div_le_div_of_nonneg_left hw_pos (by positivity)
                (mul_le_mul h2_60_le hk_sum_le (by positivity) (by positivity))
          _ = (w / (k : ℝ) ^ (splitTreeD r)) / ((2 : ℝ) ^ 60 * (k : ℝ) ^ (5 * (splitTreeD r / 8))) := by ring
          _ ≤ (w / (L_max : ℝ) ^ (splitTreeD r)) / ((2 : ℝ) ^ 60 * (k : ℝ) ^ (5 * (splitTreeD r / 8))) :=
              div_le_div_of_nonneg_right
                (div_le_div_of_nonneg_left hw_pos (by positivity) hL_le_k_D) (by positivity)
          _ ≤ (W_z.card : ℝ) / ((2 : ℝ) ^ 60 * (k : ℝ) ^ (5 * (splitTreeD r / 8))) :=
              div_le_div_of_nonneg_right hWz_active (by positivity)
          _ ≤ w_sub / ((2 : ℝ) ^ (60 * r') * (k : ℝ) ^ (2 * splitTreeD r')) := h_width_Wz
    · left
      exact ⟨U, hU_cap.mono_ambient_width_eps (hUk'_sub_Wz.trans hWz_sub) h_cap_le hη₀_le_out⟩
  · push_neg at h_regA
    have hk'_eq : k' = p_cap := Nat.min_eq_right (le_of_lt h_regA)
    left
    rcases h_ih with ⟨k, hk'_le_k, hk_le_pcap, U, hU⟩ | ⟨U, hU_cap⟩
    · have hk_eq_p : k = p_cap := by omega
      subst hk_eq_p
      have h_ge_cap := split_or_cross_at_pcap_ge_cap_width hr'1 hp_cap hη₀_pos hη₀_le1 hw_sub_nn
      exact ⟨U, hU.mono_ambient_width_eps (hUk'_sub_Wz.trans hWz_sub)
        (le_trans h_cap_le h_ge_cap) hη₀_le_out⟩
    · exact ⟨U, hU_cap.mono_ambient_width_eps (hUk'_sub_Wz.trans hWz_sub) h_cap_le hη₀_le_out⟩

/-- Terminal cutter-chain case ($d = r - 1$, `s + 1 + d = s + r`) for `Stage1FamilyStrongAt H_fam`. -/
theorem depth_r_minus_1_family_cutter_chain
    {H_fam : (d : ℕ) → SimpleGraph (Fin (d + 4))}
    (h_grp : HasNonNeighPureGrouping H_fam)
    {V : Type} [Fintype V] [DecidableEq V]
    {F : SimpleGraph V} {S U_ambient W_z : Finset V}
    {r d s ℓ p_cap p_comp L_max : ℕ} {η_out η₀ θ_r w : ℝ}
    {a : Fin ℓ → V} {B : Fin ℓ → Finset V} {stems : Fin ℓ → Fin s → V}
    {i j : Fin ℓ}
    (hr : 2 ≤ r) (hd1 : 1 ≤ d) (hd_eq : d = r - 1) (hℓ : 64 ≤ ℓ) (hp_cap : ℓ ≤ p_cap)
    (hp_comp_cases : p_comp = p_cap ∨ (p_comp < p_cap ∧ 8 * (ℓ : ℝ) ^ 2 * η₀⁻¹ ≤ (p_comp : ℝ)))
    (hL_low : 2 ≤ L_max) (hL_high : L_max ≤ ℓ)
    (hη_pos : 0 < η_out) (hη_ub : η_out ≤ (2 : ℝ)⁻¹ ^ 16)
    (hη₀_pos : 0 < η₀) (hη₀_le_out : η₀ ≤ η_out)
    (hθ_def : θ_r = η₀ / (64 * (ℓ : ℝ) * (p_comp : ℝ) ^ 2))
    (hθ_pos : 0 < θ_r) (hθ_ub : θ_r ≤ 1 / (64 * (ℓ : ℝ) ^ 2))
    (hθ_lb : (2 : ℝ)⁻¹ ^ (120 * r + 8) * (p_cap : ℝ)⁻¹ ^ (4 * splitTreeD r + 3) * η_out ≤ θ_r)
    (hfree : IsInducedSubgraphFree F (H_fam (s + r))ᶜ)
    (hcomb : IsCombOrCoCombIn F S ℓ w a B)
    (hstems : HasPerHandleApexStems F S ℓ s a B stems)
    (hw_ge : combMinWidth r η_out p_cap ≤ w)
    (hij : i ≠ j)
    (hWz_sub_Bi : W_z ⊆ B i) (hWz_sub : W_z ⊆ U_ambient)
    (hWz_active : w / (L_max : ℝ) ^ (splitTreeD r) ≤ (W_z.card : ℝ))
    (z : Fin d → V) (M_core : Fin d → Finset V)
    (hz0 : z ⟨0, hd1⟩ ∈ B j)
    (hM0_sub : M_core ⟨0, hd1⟩ ⊆ W_z)
    (hM_step : ∀ c : Fin d, ∀ hc1 : 1 ≤ c.1,
      M_core c ⊆ neighborFinsetIn F (z ⟨c.1 - 1, by omega⟩) (M_core ⟨c.1 - 1, by omega⟩))
    (hz_step : ∀ c : Fin d, ∀ hc1 : 1 ≤ c.1,
      z c ∈ M_core ⟨c.1 - 1, by omega⟩ ∧ ¬F.Adj (z ⟨c.1 - 1, by omega⟩) (z c))
    (hM_last_card : (W_z.card : ℝ) / (2 : ℝ) ^ (23 * (d - 1) + 3) ≤ ((M_core ⟨d - 1, by omega⟩).card : ℝ))
    (hNd_low : (2 : ℝ)⁻¹ ^ 20 * ((M_core ⟨d - 1, by omega⟩).card : ℝ) ≤
      ((neighborFinsetIn F (z ⟨d - 1, by omega⟩) (M_core ⟨d - 1, by omega⟩)).card : ℝ))
    (hAd_low : (2 : ℝ)⁻¹ ^ 20 * ((M_core ⟨d - 1, by omega⟩).card : ℝ) ≤
      (((M_core ⟨d - 1, by omega⟩) \ neighborFinsetIn F (z ⟨d - 1, by omega⟩) (M_core ⟨d - 1, by omega⟩)).card : ℝ)) :
    (∃ U : Fin p_cap → Finset V,
      IsWeaklySparseOrCoSparseBlockadeIn F U_ambient p_cap
        ((2 : ℝ) ^ (-(200 * (r : ℝ) ^ 2)) * η_out ^ r * (p_cap : ℝ) ^ (-(capExpE r : ℝ)) * w)
        η_out U) ∨
    (∃ k : ℕ, L_max ≤ k ∧ k ≤ p_cap ∧
      ∃ U : Fin k → Finset V,
        IsWeaklySparseOrCoSparseBlockadeIn F U_ambient k
          (w / ((2 : ℝ) ^ (60 * r) * (k : ℝ) ^ (2 * splitTreeD r))) η_out U) ∨
    HasActiveLeafSplit F r L_max η₀ W_z := by
  classical
  have hp_64 : 64 ≤ p_cap := le_trans hℓ hp_cap
  have hL_p : L_max ≤ p_cap := le_trans hL_high hp_cap
  have hη_le1 : η_out ≤ 1 := le_trans hη_ub (by norm_num)
  have hη₀_le1 : η₀ ≤ 1 := le_trans hη₀_le_out hη_le1
  have hw_pos : 0 < w := by
    have : 0 < combMinWidth r η_out p_cap := by unfold combMinWidth; positivity
    linarith
  have hw_nn : 0 ≤ w := le_of_lt hw_pos
  have hWz_pos : 0 < W_z.card := by
    rw [← @Nat.cast_pos ℝ]
    have hL_pos : (0 : ℝ) < (L_max : ℝ) := Nat.cast_pos.mpr (by omega)
    have : 0 < w / (L_max : ℝ) ^ (splitTreeD r) := by positivity
    linarith
  have hWz_r_pos : (0 : ℝ) < (W_z.card : ℝ) := Nat.cast_pos.mpr hWz_pos
  have hM_core_sub_Wz : ∀ c : Fin d, M_core c ⊆ W_z := by
    intro c
    obtain ⟨m, hm_eq⟩ : ∃ m, c.1 = m := ⟨c.1, rfl⟩
    induction m generalizing c with
    | zero =>
      have hc0 : c = ⟨0, hd1⟩ := by ext; exact hm_eq
      rw [hc0]; exact hM0_sub
    | succ k ih_m =>
      have hc1 : 1 ≤ c.1 := by omega
      exact (hM_step c hc1).trans ((ErdosHajnalP6.neighborFinsetIn_subset F _ _).trans
        (ih_m ⟨c.1 - 1, by omega⟩ (by simp; omega)))
  have hM_last_sub_Wz : M_core ⟨d - 1, by omega⟩ ⊆ W_z := hM_core_sub_Wz ⟨d - 1, by omega⟩
  let N_d := neighborFinsetIn F (z ⟨d - 1, by omega⟩) (M_core ⟨d - 1, by omega⟩)
  let A_d := M_core ⟨d - 1, by omega⟩ \ N_d
  have hNd_sub_Wz : N_d ⊆ W_z := (ErdosHajnalP6.neighborFinsetIn_subset F _ _).trans hM_last_sub_Wz
  have hAd_sub_Wz : A_d ⊆ W_z := Finset.sdiff_subset.trans hM_last_sub_Wz
  have hNd_card : (W_z.card : ℝ) / (2 : ℝ) ^ (23 * d) ≤ (N_d.card : ℝ) := by
    calc (W_z.card : ℝ) / (2 : ℝ) ^ (23 * d)
        = (2 : ℝ)⁻¹ ^ 20 * ((W_z.card : ℝ) / (2 : ℝ) ^ (23 * (d - 1) + 3)) := by
          rw [show 23 * d = (23 * (d - 1) + 3) + 20 by omega, pow_add, inv_pow]; ring
      _ ≤ (2 : ℝ)⁻¹ ^ 20 * ((M_core ⟨d - 1, by omega⟩).card : ℝ) :=
          mul_le_mul_of_nonneg_left hM_last_card (by positivity)
      _ ≤ (N_d.card : ℝ) := hNd_low
  rcases gallai_core_or_split_at_depth_d hr (by omega) hℓ hp_cap hL_low hL_p hη_pos hη_le1
      hη₀_pos hθ_pos hθ_ub hθ_lb hw_ge hWz_sub hWz_active hNd_sub_Wz hNd_card with
    h_cap | h_soc | h_split | ⟨N_T, hNT_Nd, _, _, N_star, hNs_NT, _, hNs_card, hNs_prop⟩
  · exact Or.inl h_cap
  · exact Or.inr (Or.inl h_soc)
  · exact Or.inr (Or.inr h_split)
  · have hNs_ne : N_star.Nonempty := by
      rw [← Finset.card_pos, ← @Nat.cast_pos ℝ]
      have : 0 < (W_z.card : ℝ) / (2 : ℝ) ^ (23 * d + 3) := div_pos hWz_r_pos (pow_pos (by norm_num) _)
      linarith
    obtain ⟨M_seq, hM_seq_lt, hM_seq_last⟩ :
        ∃ M_seq : Fin (d + 1) → Finset V,
          (∀ c : Fin (d + 1), ∀ hcd : c.1 < d, M_seq c = M_core ⟨c.1, hcd⟩) ∧
          M_seq (Fin.last d) = N_T :=
      ⟨fun c => if hcd : c.1 < d then M_core ⟨c.1, hcd⟩ else N_T,
       fun c hcd => dif_pos hcd, dif_neg (by dsimp; omega)⟩
    have hM_seq_0 : M_seq 0 ⊆ B i := by
      rw [hM_seq_lt 0 (by simp; omega)]
      exact hM0_sub.trans hWz_sub_Bi
    have hM_seq_step : ∀ c : Fin d, M_seq c.succ ⊆ neighborFinsetIn F (z c) (M_seq c.castSucc) := by
      intro c
      rw [hM_seq_lt c.castSucc c.2]
      by_cases hc1 : c.1 + 1 < d
      · rw [hM_seq_lt c.succ hc1]
        have h_st := hM_step ⟨c.1 + 1, hc1⟩ (by simp)
        have h_eq : (⟨(⟨c.1 + 1, hc1⟩ : Fin d).1 - 1, by omega⟩ : Fin d) = c := by ext; simp
        rwa [h_eq] at h_st
      · have hc_last : c.succ = Fin.last d := by ext; dsimp; omega
        have hc_eq : c = ⟨d - 1, by omega⟩ := by ext; dsimp; omega
        rw [hc_last, hM_seq_last, hc_eq]
        exact hNT_Nd
    have hz_seq_step : ∀ c : Fin d, ∀ hc1 : 1 ≤ c.1,
        z c ∈ M_seq ⟨c.1 - 1, by omega⟩ ∧ ¬F.Adj (z ⟨c.1 - 1, by omega⟩) (z c) := by
      intro c hc1
      rw [hM_seq_lt ⟨c.1 - 1, by omega⟩ (by simp; omega)]
      exact hz_step c hc1
    have hfree_d : IsInducedSubgraphFree F (H_fam (s + 1 + d))ᶜ := by
      rwa [show s + 1 + d = s + r by omega]
    have hNs_sub_last : N_star ⊆ M_seq (Fin.last d) := by rw [hM_seq_last]; exact hNs_NT
    have hNs_small : ∀ X : Finset V,
        IsProperModuleIn F (M_seq (Fin.last d)) X → (X ∩ N_star).Nonempty →
        (X.card : ℝ) < 5 * θ_r * (N_star.card : ℝ) := by
      rw [hM_seq_last]
      exact fun X hX hX_ne => (hNs_prop X hX hX_ne).2.2
    have hAd_in : ∀ v ∈ A_d, v ∈ M_seq ⟨d - 1, by omega⟩ ∧ ¬F.Adj (z ⟨d - 1, by omega⟩) v := by
      intro v hv
      rw [hM_seq_lt ⟨d - 1, by omega⟩ (by simp; omega)]
      obtain ⟨hvM, hv_notN⟩ := Finset.mem_sdiff.mp hv
      exact ⟨hvM, fun hadj => hv_notN ((ErdosHajnalP6.mem_neighborFinsetIn_iff F _ _ v).mpr ⟨hvM, hadj⟩)⟩
    rcases general_depth_d_nonneigh_core_dichotomy h_grp (p_comp := p_comp) hij hd1 hθ_pos hfree_d hcomb hstems
        z M_seq hz0 hM_seq_0 hM_seq_step hz_seq_step hNs_sub_last hNs_ne hNs_small hAd_in with
      ⟨D, hD_pure⟩ | ⟨A_star, hAs_sub, hAs_card, hNA_disj, h_anti_or_cosp⟩
    · rcases pure_blockade_at_pcomp_global hr (by omega) hℓ hp_cap hL_low hL_high hp_comp_cases
          hη_pos hη_le1 hη₀_pos hη₀_le1 hθ_def hθ_pos hθ_lb hw_nn hWz_sub hWz_active
          (hNs_NT.trans (hNT_Nd.trans hNd_sub_Wz)) hNs_card hD_pure with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
    · right
      have h_10_le : 10 * (p_comp : ℝ) * θ_r ≤ η₀ := by
        rw [hθ_def]
        have hℓ_r : (64 : ℝ) ≤ (ℓ : ℝ) := Nat.ofNat_le_cast.mpr hℓ
        have hp_comp_ge : (1 : ℝ) ≤ (p_comp : ℝ) := by
          rcases hp_comp_cases with rfl | ⟨_, h_c⟩
          · exact Nat.one_le_cast.mpr (by omega)
          · have : (1 : ℝ) ≤ 8 * (ℓ : ℝ) ^ 2 * η₀⁻¹ := by
              have : 1 ≤ η₀⁻¹ := one_le_inv₀ hη₀_pos |>.mpr hη₀_le1
              nlinarith
            linarith
        have h_div_le1 : 10 * (p_comp : ℝ) / (64 * (ℓ : ℝ) * (p_comp : ℝ) ^ 2) ≤ 1 := by
          rw [div_le_one (by positivity)]; nlinarith
        calc 10 * (p_comp : ℝ) * (η₀ / (64 * (ℓ : ℝ) * (p_comp : ℝ) ^ 2))
            = η₀ * (10 * (p_comp : ℝ) / (64 * (ℓ : ℝ) * (p_comp : ℝ) ^ 2)) := by ring
          _ ≤ η₀ * 1 := mul_le_mul_of_nonneg_left h_div_le1 (le_of_lt hη₀_pos)
          _ = η₀ := mul_one η₀
      have h_sp_pair : IsWeaklySparseOrCoSparsePair F N_star A_star η₀ := by
        rcases h_anti_or_cosp with h_anti | h_cosp
        · exact isWeaklySparseOrCoSparsePair_of_isPurePair hNA_disj (le_of_lt hη₀_pos) (Or.inr h_anti)
        · exact Or.inr ((IsWeaklySparsePair.symm
            (crossEdgeCount_le_of_isXSparseTo Fᶜ A_star N_star (10 * (p_comp : ℝ) * θ_r) h_cosp)).mono h_10_le)
      have hNs_25r : (W_z.card : ℝ) / (2 : ℝ) ^ (25 * r) ≤ (N_star.card : ℝ) := by
        have : (2 : ℝ) ^ (23 * d + 3) ≤ (2 : ℝ) ^ (25 * r) := pow_le_pow_right₀ (by norm_num) (by omega)
        exact le_trans (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) this) hNs_card
      have hAs_25r : (W_z.card : ℝ) / (2 : ℝ) ^ (25 * r) ≤ (A_star.card : ℝ) := by
        have h1 : (W_z.card : ℝ) / (2 : ℝ) ^ (23 * (d - 1) + 24) ≤ (A_star.card : ℝ) := by
          calc (W_z.card : ℝ) / (2 : ℝ) ^ (23 * (d - 1) + 24)
              = ((2 : ℝ)⁻¹ ^ 20 * ((W_z.card : ℝ) / (2 : ℝ) ^ (23 * (d - 1) + 3))) / 2 := by
                rw [show 23 * (d - 1) + 24 = (23 * (d - 1) + 3) + 20 + 1 by omega,
                  pow_add, pow_add, inv_pow]; ring
            _ ≤ ((2 : ℝ)⁻¹ ^ 20 * ((M_core ⟨d - 1, by omega⟩).card : ℝ)) / 2 :=
                div_le_div_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hM_last_card (by positivity)) (by positivity)
            _ ≤ (A_d.card : ℝ) / 2 := div_le_div_of_nonneg_right hAd_low (by positivity)
            _ ≤ (A_star.card : ℝ) := hAs_card
        have h2 : (2 : ℝ) ^ (23 * (d - 1) + 24) ≤ (2 : ℝ) ^ (25 * r) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        exact le_trans (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) h2) h1
      exact two_block_type2_split_or_global hr hL_low hL_p hη₀_le_out hw_nn hWz_sub hWz_pos
        hWz_active (hNs_NT.trans (hNT_Nd.trans hNd_sub_Wz)) (hAs_sub.trans hAd_sub_Wz)
        hNA_disj hNs_25r hAs_25r h_sp_pair

/-- Inductive cutter-chain step $d \to d + 1$ ($1 \le d \le r - 2$) for `Stage1FamilyStrongAt H_fam`. -/
theorem depth_d_family_cutter_chain_step
    {H_fam : (d : ℕ) → SimpleGraph (Fin (d + 4))}
    {V : Type} [Fintype V] [DecidableEq V]
    {F : SimpleGraph V} {S U_ambient W_z : Finset V}
    {r d s ℓ p_cap L_max : ℕ} {η_out η₀ θ_r w : ℝ}
    {a : Fin ℓ → V} {B : Fin ℓ → Finset V} {stems : Fin ℓ → Fin s → V}
    {i j : Fin ℓ}
    (hr : 2 ≤ r) (hd1 : 1 ≤ d) (hd_le : d ≤ r - 2) (hs : 1 ≤ s) (hℓ : 64 ≤ ℓ) (hp_cap : ℓ ≤ p_cap)
    (hL_low : 2 ≤ L_max) (hL_high : L_max ≤ ℓ)
    (hη_pos : 0 < η_out) (hη_ub : η_out ≤ (2 : ℝ)⁻¹ ^ 16)
    (hη₀_pos : 0 < η₀) (hη₀_le_out : η₀ ≤ η_out)
    (hη₀_ub19 : η₀ ≤ (2 : ℝ)⁻¹ ^ 19)
    (hη₀_lb : (2 : ℝ)⁻¹ ^ (120 * r + 2) * (p_cap : ℝ)⁻¹ ^ (4 * splitTreeD r) * η_out ≤ η₀)
    (hθ_pos : 0 < θ_r) (hθ_ub : θ_r ≤ 1 / (64 * (ℓ : ℝ) ^ 2))
    (hθ_lb : (2 : ℝ)⁻¹ ^ (120 * r + 8) * (p_cap : ℝ)⁻¹ ^ (4 * splitTreeD r + 3) * η_out ≤ θ_r)
    (hIH : ∀ r' : ℕ, 1 ≤ r' → r' < r → Stage1FamilyStrongAt H_fam r')
    (hfree : IsInducedSubgraphFree F (H_fam (s + r))ᶜ)
    (hcomb : IsCombOrCoCombIn F S ℓ w a B)
    (hstems : HasPerHandleApexStems F S ℓ s a B stems)
    (hw_ge : combMinWidth r η_out p_cap ≤ w)
    (hij : i ≠ j)
    (hWz_sub_Bi : W_z ⊆ B i) (hWz_sub : W_z ⊆ U_ambient)
    (hWz_active : w / (L_max : ℝ) ^ (splitTreeD r) ≤ (W_z.card : ℝ))
    (z : Fin d → V) (M_core : Fin d → Finset V)
    (hz0 : z ⟨0, hd1⟩ ∈ B j)
    (hM0_sub : M_core ⟨0, hd1⟩ ⊆ W_z)
    (hM_step : ∀ c : Fin d, ∀ hc1 : 1 ≤ c.1,
      M_core c ⊆ neighborFinsetIn F (z ⟨c.1 - 1, by omega⟩) (M_core ⟨c.1 - 1, by omega⟩))
    (hz_step : ∀ c : Fin d, ∀ hc1 : 1 ≤ c.1,
      z c ∈ M_core ⟨c.1 - 1, by omega⟩ ∧ ¬F.Adj (z ⟨c.1 - 1, by omega⟩) (z c))
    (hM_last_card : (W_z.card : ℝ) / (2 : ℝ) ^ (23 * (d - 1) + 3) ≤ ((M_core ⟨d - 1, by omega⟩).card : ℝ))
    (hNd_low : (2 : ℝ)⁻¹ ^ 20 * ((M_core ⟨d - 1, by omega⟩).card : ℝ) ≤
      ((neighborFinsetIn F (z ⟨d - 1, by omega⟩) (M_core ⟨d - 1, by omega⟩)).card : ℝ))
    (hAd_low : (2 : ℝ)⁻¹ ^ 20 * ((M_core ⟨d - 1, by omega⟩).card : ℝ) ≤
      (((M_core ⟨d - 1, by omega⟩) \ neighborFinsetIn F (z ⟨d - 1, by omega⟩) (M_core ⟨d - 1, by omega⟩)).card : ℝ)) :
    (∃ U : Fin p_cap → Finset V,
      IsWeaklySparseOrCoSparseBlockadeIn F U_ambient p_cap
        ((2 : ℝ) ^ (-(200 * (r : ℝ) ^ 2)) * η_out ^ r * (p_cap : ℝ) ^ (-(capExpE r : ℝ)) * w)
        η_out U) ∨
    (∃ k : ℕ, L_max ≤ k ∧ k ≤ p_cap ∧
      ∃ U : Fin k → Finset V,
        IsWeaklySparseOrCoSparseBlockadeIn F U_ambient k
          (w / ((2 : ℝ) ^ (60 * r) * (k : ℝ) ^ (2 * splitTreeD r))) η_out U) ∨
    HasActiveLeafSplit F r L_max η₀ W_z ∨
    (∃ (z' : Fin (d + 1) → V) (M_core' : Fin (d + 1) → Finset V),
      z' ⟨0, by omega⟩ ∈ B j ∧
      M_core' ⟨0, by omega⟩ ⊆ W_z ∧
      (∀ c : Fin (d + 1), ∀ hc1 : 1 ≤ c.1,
        M_core' c ⊆ neighborFinsetIn F (z' ⟨c.1 - 1, by omega⟩) (M_core' ⟨c.1 - 1, by omega⟩)) ∧
      (∀ c : Fin (d + 1), ∀ hc1 : 1 ≤ c.1,
        z' c ∈ M_core' ⟨c.1 - 1, by omega⟩ ∧ ¬F.Adj (z' ⟨c.1 - 1, by omega⟩) (z' c)) ∧
      (W_z.card : ℝ) / (2 : ℝ) ^ (23 * d + 3) ≤ ((M_core' ⟨d, by omega⟩).card : ℝ) ∧
      (2 : ℝ)⁻¹ ^ 20 * ((M_core' ⟨d, by omega⟩).card : ℝ) ≤
        ((neighborFinsetIn F (z' ⟨d, by omega⟩) (M_core' ⟨d, by omega⟩)).card : ℝ) ∧
      (2 : ℝ)⁻¹ ^ 20 * ((M_core' ⟨d, by omega⟩).card : ℝ) ≤
        (((M_core' ⟨d, by omega⟩) \ neighborFinsetIn F (z' ⟨d, by omega⟩) (M_core' ⟨d, by omega⟩)).card : ℝ)) := by
  classical
  have hp_64 : 64 ≤ p_cap := le_trans hℓ hp_cap
  have hL_p : L_max ≤ p_cap := le_trans hL_high hp_cap
  have hη_le1 : η_out ≤ 1 := le_trans hη_ub (by norm_num)
  have hw_pos : 0 < w := by
    have : 0 < combMinWidth r η_out p_cap := by unfold combMinWidth; positivity
    linarith
  have hw_nn : 0 ≤ w := le_of_lt hw_pos
  have hWz_pos : 0 < W_z.card := by
    rw [← @Nat.cast_pos ℝ]
    have hL_pos : (0 : ℝ) < (L_max : ℝ) := Nat.cast_pos.mpr (by omega)
    have : 0 < w / (L_max : ℝ) ^ (splitTreeD r) := by positivity
    linarith
  have hWz_r_pos : (0 : ℝ) < (W_z.card : ℝ) := Nat.cast_pos.mpr hWz_pos
  have hM_core_sub_Wz : ∀ c : Fin d, M_core c ⊆ W_z := by
    intro c
    obtain ⟨m, hm_eq⟩ : ∃ m, c.1 = m := ⟨c.1, rfl⟩
    induction m generalizing c with
    | zero =>
      have hc0 : c = ⟨0, hd1⟩ := by ext; exact hm_eq
      rw [hc0]; exact hM0_sub
    | succ k ih_m =>
      have hc1 : 1 ≤ c.1 := by omega
      exact (hM_step c hc1).trans ((ErdosHajnalP6.neighborFinsetIn_subset F _ _).trans
        (ih_m ⟨c.1 - 1, by omega⟩ (by simp; omega)))
  have hM_last_sub_Wz : M_core ⟨d - 1, by omega⟩ ⊆ W_z := hM_core_sub_Wz ⟨d - 1, by omega⟩
  let N_d := neighborFinsetIn F (z ⟨d - 1, by omega⟩) (M_core ⟨d - 1, by omega⟩)
  let A_d := M_core ⟨d - 1, by omega⟩ \ N_d
  have hNd_sub_Wz : N_d ⊆ W_z := (ErdosHajnalP6.neighborFinsetIn_subset F _ _).trans hM_last_sub_Wz
  have hAd_sub_Wz : A_d ⊆ W_z := Finset.sdiff_subset.trans hM_last_sub_Wz
  have hNd_card : (W_z.card : ℝ) / (2 : ℝ) ^ (23 * d) ≤ (N_d.card : ℝ) := by
    calc (W_z.card : ℝ) / (2 : ℝ) ^ (23 * d)
        = (2 : ℝ)⁻¹ ^ 20 * ((W_z.card : ℝ) / (2 : ℝ) ^ (23 * (d - 1) + 3)) := by
          rw [show 23 * d = (23 * (d - 1) + 3) + 20 by omega, pow_add, inv_pow]; ring
      _ ≤ (2 : ℝ)⁻¹ ^ 20 * ((M_core ⟨d - 1, by omega⟩).card : ℝ) :=
          mul_le_mul_of_nonneg_left hM_last_card (by positivity)
      _ ≤ (N_d.card : ℝ) := hNd_low
  rcases gallai_core_or_split_at_depth_d hr (by omega) hℓ hp_cap hL_low hL_p hη_pos hη_le1
      hη₀_pos hθ_pos hθ_ub hθ_lb hw_ge hWz_sub hWz_active hNd_sub_Wz hNd_card with
    h_cap | h_soc | h_split | ⟨N_T, hNT_Nd, _, _, N_star, hNs_NT, _, hNs_card, _⟩
  · exact Or.inl h_cap
  · exact Or.inr (Or.inl h_soc)
  · exact Or.inr (Or.inr (Or.inl h_split))
  · have hNs_sub_Nd : N_star ⊆ N_d := hNs_NT.trans hNT_Nd
    have hNs_sub_Wz : N_star ⊆ W_z := hNs_sub_Nd.trans hNd_sub_Wz
    have hNs_ne : N_star.Nonempty := by
      rw [← Finset.card_pos, ← @Nat.cast_pos ℝ]
      have : 0 < (W_z.card : ℝ) / (2 : ℝ) ^ (23 * d + 3) := div_pos hWz_r_pos (pow_pos (by norm_num) _)
      linarith
    by_cases h_bal : ∃ z_d ∈ A_d,
        (2 : ℝ)⁻¹ ^ 20 * (N_star.card : ℝ) ≤ ((neighborFinsetIn F z_d N_star).card : ℝ) ∧
        (2 : ℝ)⁻¹ ^ 20 * (N_star.card : ℝ) ≤ ((N_star \ neighborFinsetIn F z_d N_star).card : ℝ)
    · right; right; right
      obtain ⟨z_d, hz_d_in, hz_d_low, hz_d_high⟩ := h_bal
      obtain ⟨z', hz'_lt, hz'_last⟩ :
          ∃ z' : Fin (d + 1) → V,
            (∀ c : Fin (d + 1), ∀ hcd : c.1 < d, z' c = z ⟨c.1, hcd⟩) ∧
            z' ⟨d, by omega⟩ = z_d :=
        ⟨fun c => if hcd : c.1 < d then z ⟨c.1, hcd⟩ else z_d,
         fun c hcd => dif_pos hcd, dif_neg (by dsimp; omega)⟩
      obtain ⟨M_core', hM'_lt, hM'_last⟩ :
          ∃ M_core' : Fin (d + 1) → Finset V,
            (∀ c : Fin (d + 1), ∀ hcd : c.1 < d, M_core' c = M_core ⟨c.1, hcd⟩) ∧
            M_core' ⟨d, by omega⟩ = N_star :=
        ⟨fun c => if hcd : c.1 < d then M_core ⟨c.1, hcd⟩ else N_star,
         fun c hcd => dif_pos hcd, dif_neg (by dsimp; omega)⟩
      refine ⟨z', M_core', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hz'_lt ⟨0, by omega⟩ (by simp; omega)]; exact hz0
      · rw [hM'_lt ⟨0, by omega⟩ (by simp; omega)]; exact hM0_sub
      · rintro ⟨c_val, hc_lt⟩ hc1
        by_cases hcd : c_val < d
        · rw [hM'_lt ⟨c_val, hc_lt⟩ hcd, hz'_lt ⟨c_val - 1, by omega⟩ (by simp; omega),
            hM'_lt ⟨c_val - 1, by omega⟩ (by simp; omega)]
          exact hM_step ⟨c_val, hcd⟩ hc1
        · have hc_eq : c_val = d := by simp at hc1 hcd ⊢; omega
          subst c_val
          rw [hM'_last, hz'_lt ⟨d - 1, by omega⟩ (by simp; omega),
            hM'_lt ⟨d - 1, by omega⟩ (by simp; omega)]
          exact hNs_sub_Nd
      · rintro ⟨c_val, hc_lt⟩ hc1
        by_cases hcd : c_val < d
        · rw [hz'_lt ⟨c_val, hc_lt⟩ hcd, hz'_lt ⟨c_val - 1, by omega⟩ (by simp; omega),
            hM'_lt ⟨c_val - 1, by omega⟩ (by simp; omega)]
          exact hz_step ⟨c_val, hcd⟩ hc1
        · have hc_eq : c_val = d := by simp at hc1 hcd ⊢; omega
          subst c_val
          rw [hz'_last, hz'_lt ⟨d - 1, by omega⟩ (by simp; omega),
            hM'_lt ⟨d - 1, by omega⟩ (by simp; omega)]
          obtain ⟨hvM, hv_notN⟩ := Finset.mem_sdiff.mp hz_d_in
          exact ⟨hvM, fun hadj => hv_notN ((ErdosHajnalP6.mem_neighborFinsetIn_iff F _ _ z_d).mpr ⟨hvM, hadj⟩)⟩
      · rw [hM'_last]; exact hNs_card
      · rw [hz'_last, hM'_last]; exact hz_d_low
      · rw [hz'_last, hM'_last]; exact hz_d_high
    · push_neg at h_bal
      let A_sp := A_d.filter (fun v =>
        ((neighborFinsetIn F v N_star).card : ℝ) < (2 : ℝ)⁻¹ ^ 20 * (N_star.card : ℝ))
      let A_co := A_d \ A_sp
      have hA_sp_sub : A_sp ⊆ A_d := Finset.filter_subset _ _
      have hA_co_sub : A_co ⊆ A_d := Finset.sdiff_subset
      have hA_sum : (A_co.card : ℝ) + (A_sp.card : ℝ) = (A_d.card : ℝ) := by
        exact_mod_cast Finset.card_sdiff_add_card_eq_card hA_sp_sub
      have hA_co_deg : ∀ v ∈ A_co,
          ((N_star \ neighborFinsetIn F v N_star).card : ℝ) < (2 : ℝ)⁻¹ ^ 20 * (N_star.card : ℝ) := by
        intro v hv
        obtain ⟨hvA, hv_not_sp⟩ := Finset.mem_sdiff.mp hv
        have hv_ge : (2 : ℝ)⁻¹ ^ 20 * (N_star.card : ℝ) ≤ ((neighborFinsetIn F v N_star).card : ℝ) := by
          by_contra! hlt
          exact hv_not_sp (Finset.mem_filter.mpr ⟨hvA, hlt⟩)
        exact h_bal v hvA hv_ge
      obtain ⟨A_half, hAh_sub, hAh_card, hAh_pool⟩ :
          ∃ A_half ⊆ A_d, (A_d.card : ℝ) / 2 ≤ (A_half.card : ℝ) ∧
            ((∀ v ∈ A_half, ((neighborFinsetIn F v N_star).card : ℝ) < (2 : ℝ)⁻¹ ^ 20 * (N_star.card : ℝ)) ∨
             (∀ v ∈ A_half, ((N_star \ neighborFinsetIn F v N_star).card : ℝ) < (2 : ℝ)⁻¹ ^ 20 * (N_star.card : ℝ))) := by
        by_cases h_cmp : A_co.card ≤ A_sp.card
        · have h_r : (A_co.card : ℝ) ≤ (A_sp.card : ℝ) := Nat.cast_le.mpr h_cmp
          exact ⟨A_sp, hA_sp_sub, by linarith, Or.inl (fun v hv => (Finset.mem_filter.mp hv).2)⟩
        · have h_r : (A_sp.card : ℝ) ≤ (A_co.card : ℝ) := Nat.cast_le.mpr (by omega)
          exact ⟨A_co, hA_co_sub, by linarith, Or.inr hA_co_deg⟩
      obtain ⟨M_seq', hM_seq'_lt, hM_seq'_last⟩ :
          ∃ M_seq' : Fin (d + 1) → Finset V,
            (∀ c : Fin (d + 1), ∀ hcd : c.1 < d, M_seq' c = M_core ⟨c.1, hcd⟩) ∧
            M_seq' (Fin.last d) = N_star :=
        ⟨fun c => if hcd : c.1 < d then M_core ⟨c.1, hcd⟩ else N_star,
         fun c hcd => dif_pos hcd, dif_neg (by dsimp; omega)⟩
      have hM_seq'_0 : M_seq' 0 ⊆ B i := by
        rw [hM_seq'_lt 0 (by simp; omega)]; exact hM0_sub.trans hWz_sub_Bi
      have hM_seq'_step : ∀ c : Fin d, M_seq' c.succ ⊆ neighborFinsetIn F (z c) (M_seq' c.castSucc) := by
        intro c
        rw [hM_seq'_lt c.castSucc c.2]
        by_cases hc1 : c.1 + 1 < d
        · rw [hM_seq'_lt c.succ hc1]
          have h_st := hM_step ⟨c.1 + 1, hc1⟩ (by simp)
          have h_eq : (⟨(⟨c.1 + 1, hc1⟩ : Fin d).1 - 1, by omega⟩ : Fin d) = c := by ext; simp
          rwa [h_eq] at h_st
        · have hc_last : c.succ = Fin.last d := by ext; dsimp; omega
          have hc_eq : c = ⟨d - 1, by omega⟩ := by ext; dsimp; omega
          rw [hc_last, hM_seq'_last, hc_eq]
          exact hNs_sub_Nd
      have hz_seq'_step : ∀ c : Fin d, ∀ hc1 : 1 ≤ c.1,
          z c ∈ M_seq' ⟨c.1 - 1, by omega⟩ ∧ ¬F.Adj (z ⟨c.1 - 1, by omega⟩) (z c) := by
        intro c hc1
        rw [hM_seq'_lt ⟨c.1 - 1, by omega⟩ (by simp; omega)]
        exact hz_step c hc1
      have hAh_in : ∀ v ∈ A_half, v ∈ M_seq' ⟨d - 1, by omega⟩ ∧ ¬F.Adj (z ⟨d - 1, by omega⟩) v := by
        intro v hv
        rw [hM_seq'_lt ⟨d - 1, by omega⟩ (by simp; omega)]
        obtain ⟨hvM, hv_notN⟩ := Finset.mem_sdiff.mp (hAh_sub hv)
        exact ⟨hvM, fun hadj => hv_notN ((ErdosHajnalP6.mem_neighborFinsetIn_iff F _ _ v).mpr ⟨hvM, hadj⟩)⟩
      have hτ_pos : 0 < η₀ / 2 := by positivity
      have hτ_ub : η₀ / 2 ≤ (2 : ℝ)⁻¹ ^ 20 := by
        calc η₀ / 2 ≤ (2 : ℝ)⁻¹ ^ 19 / 2 := div_le_div_of_nonneg_right hη₀_ub19 (by positivity)
          _ = (2 : ℝ)⁻¹ ^ 20 := by norm_num
      have hM_seq'_ne : (M_seq' (Fin.last d)).Nonempty := by rw [hM_seq'_last]; exact hNs_ne
      have hAh_pool' :
          (∀ v ∈ A_half, ((neighborFinsetIn F v (M_seq' (Fin.last d))).card : ℝ) <
            (2 : ℝ)⁻¹ ^ 20 * ((M_seq' (Fin.last d)).card : ℝ)) ∨
          (∀ v ∈ A_half, (((M_seq' (Fin.last d)) \ neighborFinsetIn F v (M_seq' (Fin.last d))).card : ℝ) <
            (2 : ℝ)⁻¹ ^ 20 * ((M_seq' (Fin.last d)).card : ℝ)) := by
        rwa [hM_seq'_last]
      rcases internal_depth_d_stem_promotion hij hd1 hcomb hstems z M_seq' hz0 hM_seq'_0
          hM_seq'_step hz_seq'_step hM_seq'_ne hAh_in hτ_pos hτ_ub hAh_pool' with
        ⟨R_end, hR_sub, hR_half, hRA_disj, hRA_sp⟩ |
        ⟨k_comb, u_comb, N', stems'', hk_512, _, hN'_sub, hcomb', hstems''⟩
      · rw [hM_seq'_last] at hR_sub hR_half
        rw [show 2 * (η₀ / 2) = η₀ by ring] at hRA_sp
        have hR_25r : (W_z.card : ℝ) / (2 : ℝ) ^ (25 * r) ≤ (R_end.card : ℝ) := by
          have h1 : (W_z.card : ℝ) / (2 : ℝ) ^ (23 * d + 4) ≤ (R_end.card : ℝ) := by
            calc (W_z.card : ℝ) / (2 : ℝ) ^ (23 * d + 4)
                = ((W_z.card : ℝ) / (2 : ℝ) ^ (23 * d + 3)) / 2 := by
                  rw [show 23 * d + 4 = (23 * d + 3) + 1 by omega, pow_add]; ring
              _ ≤ (N_star.card : ℝ) / 2 := div_le_div_of_nonneg_right hNs_card (by positivity)
              _ ≤ (R_end.card : ℝ) := le_of_lt hR_half
          have h2 : (2 : ℝ) ^ (23 * d + 4) ≤ (2 : ℝ) ^ (25 * r) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          exact le_trans (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) h2) h1
        have hAh_25r : (W_z.card : ℝ) / (2 : ℝ) ^ (25 * r) ≤ (A_half.card : ℝ) := by
          have h1 : (W_z.card : ℝ) / (2 : ℝ) ^ (23 * (d - 1) + 24) ≤ (A_half.card : ℝ) := by
            calc (W_z.card : ℝ) / (2 : ℝ) ^ (23 * (d - 1) + 24)
                = ((2 : ℝ)⁻¹ ^ 20 * ((W_z.card : ℝ) / (2 : ℝ) ^ (23 * (d - 1) + 3))) / 2 := by
                  rw [show 23 * (d - 1) + 24 = (23 * (d - 1) + 3) + 20 + 1 by omega,
                    pow_add, pow_add, inv_pow]; ring
              _ ≤ ((2 : ℝ)⁻¹ ^ 20 * ((M_core ⟨d - 1, by omega⟩).card : ℝ)) / 2 :=
                  div_le_div_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hM_last_card (by positivity)) (by positivity)
              _ ≤ (A_d.card : ℝ) / 2 := div_le_div_of_nonneg_right hAd_low (by positivity)
              _ ≤ (A_half.card : ℝ) := hAh_card
          have h2 : (2 : ℝ) ^ (23 * (d - 1) + 24) ≤ (2 : ℝ) ^ (25 * r) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          exact le_trans (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) h2) h1
        rcases two_block_type2_split_or_global hr hL_low hL_p hη₀_le_out hw_nn hWz_sub hWz_pos
            hWz_active (hR_sub.trans hNs_sub_Wz) (hAh_sub.trans hAd_sub_Wz)
            hRA_disj hR_25r hAh_25r hRA_sp with h_soc | h_split
        · exact Or.inr (Or.inl h_soc)
        · exact Or.inr (Or.inr (Or.inl h_split))
      · rw [hM_seq'_last] at hN'_sub hcomb'
        let r' := r - 1 - d
        have hr'1 : 1 ≤ r' := by omega
        have hr'r : r' < r := by omega
        have hr_sum' : r' + d + 1 = r := by omega
        have hfree_r' : IsInducedSubgraphFree F (H_fam ((s + 1 + d) + r'))ᶜ := by
          rwa [show (s + 1 + d) + r' = s + r by omega]
        have hw_sub_ge : (η₀ / 4) * (N_star.card : ℝ) ≤
            max ((N_star.card : ℝ) / (16 * (k_comb : ℝ) ^ 2)) ((η₀ / 2 / 2) * (N_star.card : ℝ)) := by
          rw [show η₀ / 4 = η₀ / 2 / 2 by ring]
          exact le_max_right _ _
        obtain ⟨hw_sub_lb, hw_sub_cap⟩ :=
          internal_promo_width_bounds hr hd1 hr'1 hr_sum' hp_64 hL_low hL_p hη_pos hη_le1 hη₀_pos
            hη₀_lb hw_nn hWz_active hNs_card hw_sub_ge
        rcases resolve_recursive_family_call hr hr'1 hr'r hr_sum' (by omega) hp_64 hL_low hL_p
            hη_pos hη_ub hη₀_pos hη₀_le_out hη₀_lb (hIH r' hr'1 hr'r) hfree_r' hWz_sub
            hWz_active hNs_sub_Wz hNs_card (by omega) hN'_sub hcomb' hstems'' hw_ge
            (le_max_left _ _) hw_sub_lb hw_sub_cap with
          h_cap | h_soc | ⟨k_sp, U_sp, hk64, hkL, hU_sp⟩
        · exact Or.inl h_cap
        · exact Or.inr (Or.inl h_soc)
        · exact Or.inr (Or.inr (Or.inl (hasActiveLeafSplit_of_type1 hk64 hkL hU_sp)))

/-- Inductive cutter-chain dichotomy over all `rem = r - 1 - d` for `Stage1FamilyStrongAt H_fam`. -/
theorem depth_d_family_cutter_chain_dichotomy
    {H_fam : (d : ℕ) → SimpleGraph (Fin (d + 4))}
    (h_grp : HasNonNeighPureGrouping H_fam)
    {V : Type} [Fintype V] [DecidableEq V]
    {F : SimpleGraph V} {S U_ambient W_z : Finset V}
    {r s ℓ p_cap p_comp L_max : ℕ} {η_out η₀ θ_r w : ℝ}
    {a : Fin ℓ → V} {B : Fin ℓ → Finset V} {stems : Fin ℓ → Fin s → V}
    {i j : Fin ℓ}
    (hr : 2 ≤ r) (hs : 1 ≤ s) (hℓ : 64 ≤ ℓ) (hp_cap : ℓ ≤ p_cap)
    (hp_comp_cases : p_comp = p_cap ∨ (p_comp < p_cap ∧ 8 * (ℓ : ℝ) ^ 2 * η₀⁻¹ ≤ (p_comp : ℝ)))
    (hL_low : 2 ≤ L_max) (hL_high : L_max ≤ ℓ)
    (hη_pos : 0 < η_out) (hη_ub : η_out ≤ (2 : ℝ)⁻¹ ^ 16)
    (hη₀_pos : 0 < η₀) (hη₀_le_out : η₀ ≤ η_out)
    (hη₀_ub19 : η₀ ≤ (2 : ℝ)⁻¹ ^ 19)
    (hη₀_lb : (2 : ℝ)⁻¹ ^ (120 * r + 2) * (p_cap : ℝ)⁻¹ ^ (4 * splitTreeD r) * η_out ≤ η₀)
    (hθ_def : θ_r = η₀ / (64 * (ℓ : ℝ) * (p_comp : ℝ) ^ 2))
    (hθ_pos : 0 < θ_r) (hθ_ub : θ_r ≤ 1 / (64 * (ℓ : ℝ) ^ 2))
    (hθ_lb : (2 : ℝ)⁻¹ ^ (120 * r + 8) * (p_cap : ℝ)⁻¹ ^ (4 * splitTreeD r + 3) * η_out ≤ θ_r)
    (hIH : ∀ r' : ℕ, 1 ≤ r' → r' < r → Stage1FamilyStrongAt H_fam r')
    (hfree : IsInducedSubgraphFree F (H_fam (s + r))ᶜ)
    (hcomb : IsCombOrCoCombIn F S ℓ w a B)
    (hstems : HasPerHandleApexStems F S ℓ s a B stems)
    (hw_ge : combMinWidth r η_out p_cap ≤ w)
    (hij : i ≠ j)
    (hWz_sub_Bi : W_z ⊆ B i) (hWz_sub : W_z ⊆ U_ambient)
    (hWz_active : w / (L_max : ℝ) ^ (splitTreeD r) ≤ (W_z.card : ℝ)) :
    ∀ (rem d : ℕ) (hd1 : 1 ≤ d) (h_sum : d + rem = r - 1)
      (z : Fin d → V) (M_core : Fin d → Finset V),
      z ⟨0, hd1⟩ ∈ B j →
      M_core ⟨0, hd1⟩ ⊆ W_z →
      (∀ c : Fin d, ∀ hc1 : 1 ≤ c.1,
        M_core c ⊆ neighborFinsetIn F (z ⟨c.1 - 1, by omega⟩) (M_core ⟨c.1 - 1, by omega⟩)) →
      (∀ c : Fin d, ∀ hc1 : 1 ≤ c.1,
        z c ∈ M_core ⟨c.1 - 1, by omega⟩ ∧ ¬F.Adj (z ⟨c.1 - 1, by omega⟩) (z c)) →
      (W_z.card : ℝ) / (2 : ℝ) ^ (23 * (d - 1) + 3) ≤ ((M_core ⟨d - 1, by omega⟩).card : ℝ) →
      (2 : ℝ)⁻¹ ^ 20 * ((M_core ⟨d - 1, by omega⟩).card : ℝ) ≤
        ((neighborFinsetIn F (z ⟨d - 1, by omega⟩) (M_core ⟨d - 1, by omega⟩)).card : ℝ) →
      (2 : ℝ)⁻¹ ^ 20 * ((M_core ⟨d - 1, by omega⟩).card : ℝ) ≤
        (((M_core ⟨d - 1, by omega⟩) \ neighborFinsetIn F (z ⟨d - 1, by omega⟩) (M_core ⟨d - 1, by omega⟩)).card : ℝ) →
      (∃ U : Fin p_cap → Finset V,
        IsWeaklySparseOrCoSparseBlockadeIn F U_ambient p_cap
          ((2 : ℝ) ^ (-(200 * (r : ℝ) ^ 2)) * η_out ^ r * (p_cap : ℝ) ^ (-(capExpE r : ℝ)) * w)
          η_out U) ∨
      (∃ k : ℕ, L_max ≤ k ∧ k ≤ p_cap ∧
        ∃ U : Fin k → Finset V,
          IsWeaklySparseOrCoSparseBlockadeIn F U_ambient k
            (w / ((2 : ℝ) ^ (60 * r) * (k : ℝ) ^ (2 * splitTreeD r))) η_out U) ∨
      HasActiveLeafSplit F r L_max η₀ W_z := by
  intro rem
  induction rem with
  | zero =>
    intro d hd1 h_sum z M_core hz0 hM0_sub hM_step hz_step hM_last_card hNd_low hAd_low
    exact depth_r_minus_1_family_cutter_chain h_grp hr hd1 (by omega) hℓ hp_cap hp_comp_cases
      hL_low hL_high hη_pos hη_ub hη₀_pos hη₀_le_out hθ_def hθ_pos hθ_ub hθ_lb hfree hcomb hstems
      hw_ge hij hWz_sub_Bi hWz_sub hWz_active z M_core hz0 hM0_sub hM_step hz_step
      hM_last_card hNd_low hAd_low
  | succ rem' ih =>
    intro d hd1 h_sum z M_core hz0 hM0_sub hM_step hz_step hM_last_card hNd_low hAd_low
    rcases depth_d_family_cutter_chain_step hr hd1 (by omega) hs hℓ hp_cap hL_low hL_high hη_pos hη_ub
        hη₀_pos hη₀_le_out hη₀_ub19 hη₀_lb hθ_pos hθ_ub hθ_lb hIH hfree hcomb hstems hw_ge hij
        hWz_sub_Bi hWz_sub hWz_active z M_core hz0 hM0_sub hM_step hz_step hM_last_card hNd_low hAd_low with
      h_cap | h_soc | h_split | ⟨z', M_core', hz0', hM0', hM_st', hz_st', hM_card', hN_low', hA_low'⟩
    · exact Or.inl h_cap
    · exact Or.inr (Or.inl h_soc)
    · exact Or.inr (Or.inr h_split)
    · exact ih (d + 1) (by omega) (by omega) z' M_core' hz0' hM0' hM_st' hz_st'
        (by simpa using hM_card') (by simpa using hN_low') (by simpa using hA_low')

/-- Single iteration on active leaves for `Stage1FamilyStrongAt H_fam`. -/
theorem active_leaves_family_step_or_global
    {H_fam : (d : ℕ) → SimpleGraph (Fin (d + 4))}
    (h_grp : HasNonNeighPureGrouping H_fam)
    {V : Type} [Fintype V] [DecidableEq V]
    {F : SimpleGraph V} {S U_ambient : Finset V}
    {r s ℓ p_cap p_comp L_max : ℕ} {η_out η₀ θ_r w : ℝ}
    {a : Fin ℓ → V} {B W_z : Fin ℓ → Finset V} {stems : Fin ℓ → Fin s → V}
    (hr : 2 ≤ r) (hs : 1 ≤ s) (hℓ : 64 ≤ ℓ) (hp_cap : ℓ ≤ p_cap)
    (hp_comp_cases : p_comp = p_cap ∨ (p_comp < p_cap ∧ 8 * (ℓ : ℝ) ^ 2 * η₀⁻¹ ≤ (p_comp : ℝ)))
    (hL_low : 2 ≤ L_max) (hL_high : L_max ≤ ℓ)
    (hη_pos : 0 < η_out) (hη_ub : η_out ≤ (2 : ℝ)⁻¹ ^ 16)
    (hη₀_pos : 0 < η₀) (hη₀_le_out : η₀ ≤ η_out)
    (hη₀_ub19 : η₀ ≤ (2 : ℝ)⁻¹ ^ 19)
    (hη₀_lb : (2 : ℝ)⁻¹ ^ (120 * r + 2) * (p_cap : ℝ)⁻¹ ^ (4 * splitTreeD r) * η_out ≤ η₀)
    (hθ_def : θ_r = η₀ / (64 * (ℓ : ℝ) * (p_comp : ℝ) ^ 2))
    (hθ_pos : 0 < θ_r) (hθ_ub : θ_r ≤ 1 / (64 * (ℓ : ℝ) ^ 2))
    (hθ_lb : (2 : ℝ)⁻¹ ^ (120 * r + 8) * (p_cap : ℝ)⁻¹ ^ (4 * splitTreeD r + 3) * η_out ≤ θ_r)
    (hIH : ∀ r' : ℕ, 1 ≤ r' → r' < r → Stage1FamilyStrongAt H_fam r')
    (hfree : IsInducedSubgraphFree F (H_fam (s + r))ᶜ)
    (hcomb : IsCombOrCoCombIn F S ℓ w a B)
    (hstems : HasPerHandleApexStems F S ℓ s a B stems)
    (hw_ge : combMinWidth r η_out p_cap ≤ w)
    (hB_sub : ∀ i : Fin ℓ, B i ⊆ U_ambient)
    (hWz_sub_B : ∀ i : Fin ℓ, W_z i ⊆ B i)
    (hWz_active : ∀ i : Fin ℓ, w / (L_max : ℝ) ^ (splitTreeD r) ≤ ((W_z i).card : ℝ)) :
    (∃ U : Fin p_cap → Finset V,
      IsWeaklySparseOrCoSparseBlockadeIn F U_ambient p_cap
        ((2 : ℝ) ^ (-(200 * (r : ℝ) ^ 2)) * η_out ^ r * (p_cap : ℝ) ^ (-(capExpE r : ℝ)) * w)
        η_out U) ∨
    (∃ k : ℕ, L_max ≤ k ∧ k ≤ p_cap ∧
      ∃ U : Fin k → Finset V,
        IsWeaklySparseOrCoSparseBlockadeIn F U_ambient k
          (w / ((2 : ℝ) ^ (60 * r) * (k : ℝ) ^ (2 * splitTreeD r))) η_out U) ∨
    (∃ i : Fin ℓ, HasActiveLeafSplit F r L_max η₀ (W_z i)) := by
  classical
  have hp_64 : 64 ≤ p_cap := le_trans hℓ hp_cap
  have hL_p : L_max ≤ p_cap := le_trans hL_high hp_cap
  have hη_le1 : η_out ≤ 1 := le_trans hη_ub (by norm_num)
  have hw_pos : 0 < w := by
    have : 0 < combMinWidth r η_out p_cap := by unfold combMinWidth; positivity
    linarith
  have hw_nn : 0 ≤ w := le_of_lt hw_pos
  have hL_pos : (0 : ℝ) < (L_max : ℝ) := Nat.cast_pos.mpr (by omega)
  have hWz_sub_U : ∀ i : Fin ℓ, W_z i ⊆ U_ambient := fun i => (hWz_sub_B i).trans (hB_sub i)
  have h_step1 : ∀ i : Fin ℓ,
      (∃ U : Fin p_cap → Finset V,
        IsWeaklySparseOrCoSparseBlockadeIn F U_ambient p_cap
          ((2 : ℝ) ^ (-(200 * (r : ℝ) ^ 2)) * η_out ^ r * (p_cap : ℝ) ^ (-(capExpE r : ℝ)) * w)
          η_out U) ∨
      (∃ k : ℕ, L_max ≤ k ∧ k ≤ p_cap ∧
        ∃ U : Fin k → Finset V,
          IsWeaklySparseOrCoSparseBlockadeIn F U_ambient k
            (w / ((2 : ℝ) ^ (60 * r) * (k : ℝ) ^ (2 * splitTreeD r))) η_out U) ∨
      HasActiveLeafSplit F r L_max η₀ (W_z i) ∨
      (∃ M_star ⊆ W_z i, ((W_z i).card : ℝ) / (2 : ℝ) ^ 3 ≤ (M_star.card : ℝ)) := by
    intro i
    rcases gallai_core_or_split_at_depth_d (d := 0) hr (by omega) hℓ hp_cap hL_low hL_p
        hη_pos hη_le1 hη₀_pos hθ_pos hθ_ub hθ_lb hw_ge (hWz_sub_U i) (hWz_active i)
        Finset.Subset.rfl (by simp) with
      h_cap | h_soc | h_split | ⟨N_T, hNT_Wz, _, _, M_star, hMs_NT, _, hMs_card, _⟩
    · exact Or.inl h_cap
    · exact Or.inr (Or.inl h_soc)
    · exact Or.inr (Or.inr (Or.inl h_split))
    · exact Or.inr (Or.inr (Or.inr ⟨M_star, hMs_NT.trans hNT_Wz, by simpa using hMs_card⟩))
  by_cases h_early :
      (∃ U : Fin p_cap → Finset V,
        IsWeaklySparseOrCoSparseBlockadeIn F U_ambient p_cap
          ((2 : ℝ) ^ (-(200 * (r : ℝ) ^ 2)) * η_out ^ r * (p_cap : ℝ) ^ (-(capExpE r : ℝ)) * w)
          η_out U) ∨
      (∃ k : ℕ, L_max ≤ k ∧ k ≤ p_cap ∧
        ∃ U : Fin k → Finset V,
          IsWeaklySparseOrCoSparseBlockadeIn F U_ambient k
            (w / ((2 : ℝ) ^ (60 * r) * (k : ℝ) ^ (2 * splitTreeD r))) η_out U) ∨
      (∃ i : Fin ℓ, HasActiveLeafSplit F r L_max η₀ (W_z i))
  · exact h_early
  · have h_all_core : ∀ i : Fin ℓ,
        ∃ M_star : Finset V, M_star ⊆ W_z i ∧ ((W_z i).card : ℝ) / (2 : ℝ) ^ 3 ≤ (M_star.card : ℝ) := by
      intro i
      rcases h_step1 i with h1 | h2 | h3 | h4
      · exact False.elim (h_early (Or.inl h1))
      · exact False.elim (h_early (Or.inr (Or.inl h2)))
      · exact False.elim (h_early (Or.inr (Or.inr ⟨i, h3⟩)))
      · exact h4
    obtain ⟨M_star, hMs⟩ := Classical.axiomOfChoice h_all_core
    have hMs_sub_Wz : ∀ i : Fin ℓ, M_star i ⊆ W_z i := fun i => (hMs i).1
    have hMs_sub_B : ∀ i : Fin ℓ, M_star i ⊆ B i := fun i => (hMs_sub_Wz i).trans (hWz_sub_B i)
    have hMs_card : ∀ i : Fin ℓ, ((W_z i).card : ℝ) / (2 : ℝ) ^ 3 ≤ ((M_star i).card : ℝ) :=
      fun i => (hMs i).2
    have hMs_ne : ∀ i : Fin ℓ, (M_star i).Nonempty := by
      intro i
      rw [← Finset.card_pos, ← @Nat.cast_pos ℝ]
      have h1 : 0 < w / (L_max : ℝ) ^ (splitTreeD r) := by positivity
      have h2 := hWz_active i
      have h3 := hMs_card i
      linarith
    by_cases h_step2 : ∃ (i j : Fin ℓ), i ≠ j ∧ ∃ u ∈ M_star j,
        (2 : ℝ)⁻¹ ^ 20 * ((M_star i).card : ℝ) ≤ ((neighborFinsetIn F u (M_star i)).card : ℝ) ∧
        (2 : ℝ)⁻¹ ^ 20 * ((M_star i).card : ℝ) ≤ (((M_star i) \ neighborFinsetIn F u (M_star i)).card : ℝ)
    · obtain ⟨i, j, hij, u, hu_Mj, hu_low, hu_high⟩ := h_step2
      rcases depth_d_family_cutter_chain_dichotomy h_grp hr hs hℓ hp_cap hp_comp_cases hL_low hL_high
          hη_pos hη_ub hη₀_pos hη₀_le_out hη₀_ub19 hη₀_lb hθ_def hθ_pos hθ_ub hθ_lb hIH hfree hcomb
          hstems hw_ge hij (hWz_sub_B i) (hWz_sub_U i) (hWz_active i)
          (r - 2) 1 le_rfl (by omega) (fun _ => u) (fun _ => M_star i)
          (hMs_sub_B j hu_Mj) (hMs_sub_Wz i)
          (fun c hc1 => by fin_cases c; omega)
          (fun c hc1 => by fin_cases c; omega)
          (by simpa using hMs_card i) hu_low hu_high with
        h_cap | h_soc | h_split
      · exact Or.inl h_cap
      · exact Or.inr (Or.inl h_soc)
      · exact Or.inr (Or.inr ⟨i, h_split⟩)
    · push_neg at h_step2
      let τ := η_out / (8 * (ℓ : ℝ))
      have hℓ_r : (64 : ℝ) ≤ (ℓ : ℝ) := Nat.ofNat_le_cast.mpr hℓ
      have hτ_pos : 0 < τ := by unfold τ; positivity
      have hτ_ub : τ ≤ (2 : ℝ)⁻¹ ^ 20 := by
        unfold τ
        calc η_out / (8 * (ℓ : ℝ))
            ≤ (2 : ℝ)⁻¹ ^ 16 / (8 * 64) :=
              div_le_div₀ (by positivity) hη_ub (by positivity) (by linarith)
          _ = (2 : ℝ)⁻¹ ^ 25 := by norm_num
          _ ≤ (2 : ℝ)⁻¹ ^ 20 := by norm_num
      let U_ext (i : Fin ℓ) : Finset V := (Finset.univ.erase i).biUnion M_star
      let S_pool (i : Fin ℓ) : Finset V :=
        (U_ext i).filter (fun u =>
          ((neighborFinsetIn F u (M_star i)).card : ℝ) < (2 : ℝ)⁻¹ ^ 20 * ((M_star i).card : ℝ))
      let D_pool (i : Fin ℓ) : Finset V := U_ext i \ S_pool i
      have hU_ext_sub : ∀ i : Fin ℓ, U_ext i ⊆ (Finset.univ.erase i).biUnion B := by
        intro i
        refine Finset.biUnion_subset.mpr (fun j hj => ?_)
        exact (hMs_sub_B j).trans (Finset.subset_biUnion_of_mem B hj)
      have hD_pool_deg : ∀ (i : Fin ℓ), ∀ u ∈ D_pool i,
          (((M_star i) \ neighborFinsetIn F u (M_star i)).card : ℝ) <
            (2 : ℝ)⁻¹ ^ 20 * ((M_star i).card : ℝ) := by
        intro i u hu
        obtain ⟨hu_ext, hu_not_S⟩ := Finset.mem_sdiff.mp hu
        obtain ⟨j, hj_er, hu_Mj⟩ := Finset.mem_biUnion.mp hu_ext
        have hji : i ≠ j := (Finset.mem_erase.mp hj_er).1.symm
        have hu_ge : (2 : ℝ)⁻¹ ^ 20 * ((M_star i).card : ℝ) ≤
            ((neighborFinsetIn F u (M_star i)).card : ℝ) := by
          by_contra! hlt
          exact hu_not_S (Finset.mem_filter.mpr ⟨hu_ext, hlt⟩)
        exact h_step2 i j hji u hu_Mj hu_ge
      have h_step3 : ∀ i : Fin ℓ,
          (∃ M_i' : Finset V, M_i' ⊆ M_star i ∧
            (7 / 8 : ℝ) * ((M_star i).card : ℝ) < (M_i'.card : ℝ) ∧
            (∀ u ∈ S_pool i, ((neighborFinsetIn F u M_i').card : ℝ) ≤ τ * ((M_star i).card : ℝ)) ∧
            (∀ u ∈ D_pool i, ((M_i' \ neighborFinsetIn F u M_i').card : ℝ) ≤ τ * ((M_star i).card : ℝ))) ∨
          (∃ (k_comb : ℕ) (u : Fin k_comb → V) (B' : Fin k_comb → Finset V)
             (stems' : Fin k_comb → Fin (s + 1) → V),
            512 < k_comb ∧ (k_comb : ℝ) < τ⁻¹ ∧
            (∀ q : Fin k_comb, B' q ⊆ M_star i) ∧
            IsCombOrCoCombIn F S k_comb
              (max (((M_star i).card : ℝ) / (16 * (k_comb : ℝ) ^ 2)) ((τ / 2) * ((M_star i).card : ℝ))) u B' ∧
            HasPerHandleApexStems F S k_comb (s + 1) u B' stems') :=
        fun i => union_pool_stem_promotion hcomb hstems (hMs_sub_B i) (hMs_ne i) hτ_pos hτ_ub
          ((Finset.filter_subset _ _).trans (hU_ext_sub i))
          (Finset.sdiff_subset.trans (hU_ext_sub i))
          (fun u hu => (Finset.mem_filter.mp hu).2) (hD_pool_deg i)
      by_cases h_promo : ∃ i : Fin ℓ,
          ∃ (k_comb : ℕ) (u : Fin k_comb → V) (B' : Fin k_comb → Finset V)
             (stems' : Fin k_comb → Fin (s + 1) → V),
            512 < k_comb ∧ (k_comb : ℝ) < τ⁻¹ ∧
            (∀ q : Fin k_comb, B' q ⊆ M_star i) ∧
            IsCombOrCoCombIn F S k_comb
              (max (((M_star i).card : ℝ) / (16 * (k_comb : ℝ) ^ 2)) ((τ / 2) * ((M_star i).card : ℝ))) u B' ∧
            HasPerHandleApexStems F S k_comb (s + 1) u B' stems'
      · obtain ⟨i, k_comb, u_c, B', stems', hk_512, _, hB'_sub, hcomb', hstems'⟩ := h_promo
        have hr'1 : 1 ≤ r - 1 := by omega
        have hr'r : r - 1 < r := by omega
        have hr_sum : (r - 1) + 0 + 1 = r := by omega
        have hfree_r' : IsInducedSubgraphFree F (H_fam ((s + 1) + (r - 1)))ᶜ := by
          rwa [show (s + 1) + (r - 1) = s + r by omega]
        have hw_sub_ge : (η_out / (16 * (ℓ : ℝ))) * ((M_star i).card : ℝ) ≤
            max (((M_star i).card : ℝ) / (16 * (k_comb : ℝ) ^ 2)) ((τ / 2) * ((M_star i).card : ℝ)) := by
          have h_eq : η_out / (16 * (ℓ : ℝ)) = τ / 2 := by unfold τ; ring
          rw [h_eq]; exact le_max_right _ _
        obtain ⟨hw_sub_lb, hw_sub_cap⟩ :=
          union_promo_width_bounds hr hℓ hp_cap hL_low hL_high hη_pos hη₀_lb hw_nn
            (hWz_active i) (hMs_card i) hw_sub_ge
        rcases resolve_recursive_family_call (d := 0) hr hr'1 hr'r hr_sum (by omega) hp_64 hL_low hL_p
            hη_pos hη_ub hη₀_pos hη₀_le_out hη₀_lb (hIH (r - 1) hr'1 hr'r) hfree_r' (hWz_sub_U i)
            (hWz_active i) (hMs_sub_Wz i) (by simpa using hMs_card i) (by omega)
            hB'_sub hcomb' hstems' hw_ge (le_max_left _ _) hw_sub_lb hw_sub_cap with
          h_cap | h_soc | ⟨k_sp, U_sp, hk64, hkL, hU_sp⟩
        · exact Or.inl h_cap
        · exact Or.inr (Or.inl h_soc)
        · exact Or.inr (Or.inr ⟨i, hasActiveLeafSplit_of_type1 hk64 hkL hU_sp⟩)
      · right; left
        have h_all_stop : ∀ i : Fin ℓ,
            ∃ M_i' : Finset V, M_i' ⊆ M_star i ∧
              (7 / 8 : ℝ) * ((M_star i).card : ℝ) < (M_i'.card : ℝ) ∧
              (∀ u ∈ S_pool i, ((neighborFinsetIn F u M_i').card : ℝ) ≤ τ * ((M_star i).card : ℝ)) ∧
              (∀ u ∈ D_pool i, ((M_i' \ neighborFinsetIn F u M_i').card : ℝ) ≤ τ * ((M_star i).card : ℝ)) := by
          intro i
          rcases h_step3 i with h_st | h_pr
          · exact h_st
          · exact False.elim (h_promo ⟨i, h_pr⟩)
        obtain ⟨M', hM'⟩ := Classical.axiomOfChoice h_all_stop
        have hB_block : IsBlockadeIn F S ℓ w B := by
          rcases hcomb with hc | hco
          · exact hc.is_blockade
          · exact hco.is_blockade
        have hM'_sub_B : ∀ i : Fin ℓ, M' i ⊆ B i :=
          fun i => (hM' i).1.trans (hMs_sub_B i)
        have hM'_width : ∀ i : Fin ℓ,
            w / ((2 : ℝ) ^ (60 * r) * (ℓ : ℝ) ^ (2 * splitTreeD r)) ≤ ((M' i).card : ℝ) := by
          intro i
          have hL_ell_D : (L_max : ℝ) ^ (splitTreeD r) ≤ (ℓ : ℝ) ^ (splitTreeD r) :=
            pow_le_pow_left₀ (by positivity) (Nat.cast_le.mpr hL_high) (splitTreeD r)
          have h_ell_ge1 : (1 : ℝ) ≤ (ℓ : ℝ) := by linarith
          have h2_pow : (2 : ℝ) ^ 4 ≤ (2 : ℝ) ^ (60 * r) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          have h_ell_pow : (ℓ : ℝ) ^ (splitTreeD r) ≤ (ℓ : ℝ) ^ (2 * splitTreeD r) :=
            pow_le_pow_right₀ h_ell_ge1 (by omega)
          calc w / ((2 : ℝ) ^ (60 * r) * (ℓ : ℝ) ^ (2 * splitTreeD r))
              ≤ w / ((2 : ℝ) ^ 4 * (ℓ : ℝ) ^ (splitTreeD r)) :=
                div_le_div_of_nonneg_left hw_nn (by positivity)
                  (mul_le_mul h2_pow h_ell_pow (by positivity) (by positivity))
            _ ≤ w / ((2 : ℝ) ^ 4 * (L_max : ℝ) ^ (splitTreeD r)) :=
                div_le_div_of_nonneg_left hw_nn (by positivity)
                  (mul_le_mul_of_nonneg_left hL_ell_D (by positivity))
            _ = (1 / 2 : ℝ) * ((w / (L_max : ℝ) ^ (splitTreeD r)) / (2 : ℝ) ^ 3) := by ring
            _ ≤ (7 / 8 : ℝ) * (((W_z i).card : ℝ) / (2 : ℝ) ^ 3) := by
                refine mul_le_mul (by norm_num) ?_ (by positivity) (by positivity)
                exact div_le_div_of_nonneg_right (hWz_active i) (by positivity)
            _ ≤ (7 / 8 : ℝ) * ((M_star i).card : ℝ) :=
                mul_le_mul_of_nonneg_left (hMs_card i) (by positivity)
            _ ≤ ((M' i).card : ℝ) := le_of_lt (hM' i).2.1
        have hM'_ne : ∀ i : Fin ℓ, (M' i).Nonempty := by
          intro i
          rw [← Finset.card_pos, ← @Nat.cast_pos ℝ]
          have : 0 < w / ((2 : ℝ) ^ (60 * r) * (ℓ : ℝ) ^ (2 * splitTreeD r)) := by positivity
          linarith [hM'_width i]
        have hM'_block : IsBlockadeIn F U_ambient ℓ
            (w / ((2 : ℝ) ^ (60 * r) * (ℓ : ℝ) ^ (2 * splitTreeD r))) M' :=
          { subset_ambient := fun i => (hM'_sub_B i).trans (hB_sub i)
            nonempty_blocks := hM'_ne
            pairwise_disjoint := fun i j hij =>
              Finset.disjoint_of_subset_left (hM'_sub_B i)
                (Finset.disjoint_of_subset_right (hM'_sub_B j) (hB_block.pairwise_disjoint i j hij))
            width_ge := hM'_width }
        have hM'_part : ∀ (i j : Fin ℓ), i ≠ j → ∀ u ∈ M' j,
            ((neighborFinsetIn F u (M' i)).card : ℝ) ≤ (η_out / (4 * (ℓ : ℝ))) * ((M' i).card : ℝ) ∨
            (((M' i) \ neighborFinsetIn F u (M' i)).card : ℝ) ≤ (η_out / (4 * (ℓ : ℝ))) * ((M' i).card : ℝ) := by
          intro i j hij u hu_M'j
          have hu_Msj : u ∈ M_star j := (hM' j).1 hu_M'j
          have hu_ext : u ∈ U_ext i :=
            Finset.mem_biUnion.mpr ⟨j, Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩, hu_Msj⟩
          have h_Ms_le_2M' : ((M_star i).card : ℝ) ≤ 2 * ((M' i).card : ℝ) := by
            have := (hM' i).2.1; linarith
          have h_τ_bound : τ * ((M_star i).card : ℝ) ≤ (η_out / (4 * (ℓ : ℝ))) * ((M' i).card : ℝ) := by
            calc τ * ((M_star i).card : ℝ)
                ≤ τ * (2 * ((M' i).card : ℝ)) :=
                  mul_le_mul_of_nonneg_left h_Ms_le_2M' (le_of_lt hτ_pos)
              _ = (η_out / (4 * (ℓ : ℝ))) * ((M' i).card : ℝ) := by unfold τ; ring
          by_cases hu_S : u ∈ S_pool i
          · left; exact le_trans ((hM' i).2.2.1 u hu_S) h_τ_bound
          · right; exact le_trans ((hM' i).2.2.2 u (Finset.mem_sdiff.mpr ⟨hu_ext, hu_S⟩)) h_τ_bound
        exact ⟨ℓ, hL_high, hp_cap, M',
          bipartite_double_counting_dichotomy (by omega) hη_pos hM'_block hM'_part⟩

/-- Inductive step $r \ge 2$ (`stage1Family_strong_step`) of the Stage-1 Comb/Co-Comb Dichotomy
for any graph family `H_fam` satisfying `HasNonNeighPureGrouping H_fam`. -/
theorem stage1Family_strong_step
    {H_fam : (d : ℕ) → SimpleGraph (Fin (d + 4))}
    (h_grp : HasNonNeighPureGrouping H_fam)
    {r : ℕ} (hr : 2 ≤ r)
    (hIH : ∀ r' : ℕ, 1 ≤ r' → r' < r → Stage1FamilyStrongAt H_fam r') :
    Stage1FamilyStrongAt H_fam r := by
  classical
  intro _ V _ _ F S s ℓ p_cap L_max η_out w a B stems hs hℓ hp_cap hL_low hL_high
    hη_pos hη_ub hfree hcomb hstems hw_ge U_ambient
  have hp_64 : 64 ≤ p_cap := le_trans hℓ hp_cap
  have hL_p : L_max ≤ p_cap := le_trans hL_high hp_cap
  have hL_pos : (0 : ℝ) < (L_max : ℝ) := Nat.cast_pos.mpr (by omega)
  have hp_pos : (0 : ℝ) < (p_cap : ℝ) := Nat.cast_pos.mpr (by omega)
  have hℓ_r : (64 : ℝ) ≤ (ℓ : ℝ) := Nat.ofNat_le_cast.mpr hℓ
  have hw_pos : 0 < w := by
    have : 0 < combMinWidth r η_out p_cap := by unfold combMinWidth; positivity
    linarith
  have hw_nn : 0 ≤ w := le_of_lt hw_pos
  have h_tr := treeParamR_bounds r hr
  have h_Dr_info := splitTreeD_eq_eight_mul r hr
  let m := splitTreeD r / 8
  have h_Dr_eq : splitTreeD r = 8 * m := h_Dr_info.1
  have hm_ge8 : 8 ≤ m := h_Dr_info.2.1
  have hD_pos : 1 ≤ 8 * m := by omega
  let β_inv := (2 : ℝ) ^ (60 * treeParamR r) * (L_max : ℝ) ^ (2 * (8 * m))
  have hβ_pos : 0 < β_inv := by unfold β_inv; positivity
  let η₀ := η_out / (4 * β_inv ^ 2)
  have hη₀_pos : 0 < η₀ := by unfold η₀; positivity
  have hβ_ge2 : (2 : ℝ) ≤ β_inv := by
    unfold β_inv
    have h1 : (2 : ℝ) ≤ (2 : ℝ) ^ (60 * treeParamR r) := by
      have : 1 ≤ 60 * treeParamR r := by have := h_tr.1; omega
      simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) this
    have h2 : (1 : ℝ) ≤ (L_max : ℝ) ^ (2 * (8 * m)) :=
      one_le_pow₀ (Nat.one_le_cast.mpr (by omega))
    nlinarith
  have hη₀_ub19 : η₀ ≤ (2 : ℝ)⁻¹ ^ 19 := by
    unfold η₀
    have h_den : (16 : ℝ) ≤ 4 * β_inv ^ 2 := by nlinarith
    calc η_out / (4 * β_inv ^ 2)
        ≤ (2 : ℝ)⁻¹ ^ 16 / 16 := div_le_div₀ (by positivity) hη_ub (by positivity) h_den
      _ = (2 : ℝ)⁻¹ ^ 20 := by norm_num
      _ ≤ (2 : ℝ)⁻¹ ^ 19 := by norm_num
  have hη₀_le_out : η₀ ≤ η_out := by
    unfold η₀
    exact div_le_self (le_of_lt hη_pos) (by nlinarith)
  have hη₀_β2_le : η₀ * β_inv ^ 2 ≤ η_out := by
    unfold η₀
    have h_eq : η_out / (4 * β_inv ^ 2) * β_inv ^ 2 = η_out / 4 := by field_simp
    rw [h_eq]; linarith
  have hη₀_lb : (2 : ℝ)⁻¹ ^ (120 * r + 2) * (p_cap : ℝ)⁻¹ ^ (4 * splitTreeD r) * η_out ≤ η₀ := by
    have hβ_ub : β_inv ≤ (2 : ℝ) ^ (60 * r) * (p_cap : ℝ) ^ (2 * splitTreeD r) := by
      unfold β_inv
      rw [← h_Dr_eq]
      exact mul_le_mul (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left 60 h_tr.2.1))
        (pow_le_pow_left₀ (by positivity) (Nat.cast_le.mpr hL_p) _) (by positivity) (by positivity)
    have h_4β2_ub : 4 * β_inv ^ 2 ≤ (2 : ℝ) ^ (120 * r + 2) * (p_cap : ℝ) ^ (4 * splitTreeD r) := by
      have h1 := pow_le_pow_left₀ (le_of_lt hβ_pos) hβ_ub 2
      have h2 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 4)
      calc 4 * β_inv ^ 2
          ≤ 4 * ((2 : ℝ) ^ (60 * r) * (p_cap : ℝ) ^ (2 * splitTreeD r)) ^ 2 := h2
        _ = (2 : ℝ) ^ (120 * r + 2) * (p_cap : ℝ) ^ (4 * splitTreeD r) := by
            rw [mul_pow, ← pow_mul, ← pow_mul, show 120 * r + 2 = 2 + 60 * r * 2 by omega,
              pow_add (a := (2 : ℝ)) (m := 2), show 2 * splitTreeD r * 2 = 4 * splitTreeD r by ring]
            norm_num; ring
    unfold η₀
    calc (2 : ℝ)⁻¹ ^ (120 * r + 2) * (p_cap : ℝ)⁻¹ ^ (4 * splitTreeD r) * η_out
        = η_out / ((2 : ℝ) ^ (120 * r + 2) * (p_cap : ℝ) ^ (4 * splitTreeD r)) := by
          rw [inv_pow, inv_pow]; ring
      _ ≤ η_out / (4 * β_inv ^ 2) :=
          div_le_div_of_nonneg_left (le_of_lt hη_pos) (by positivity) h_4β2_ub
  let p_raw := ⌈8 * (ℓ : ℝ) ^ 2 * η₀⁻¹⌉₊
  let p_comp := min p_raw p_cap
  have hp_comp_cases : p_comp = p_cap ∨ (p_comp < p_cap ∧ 8 * (ℓ : ℝ) ^ 2 * η₀⁻¹ ≤ (p_comp : ℝ)) := by
    by_cases h_cmp : p_cap ≤ p_raw
    · exact Or.inl (Nat.min_eq_right h_cmp)
    · push_neg at h_cmp
      have h_eq : p_comp = p_raw := Nat.min_eq_left (le_of_lt h_cmp)
      refine Or.inr ⟨by omega, ?_⟩
      rw [h_eq]; exact Nat.le_ceil _
  have hℓ_le_pcomp : ℓ ≤ p_comp := by
    refine le_min ?_ hp_cap
    have hη₀_inv_ge1 : 1 ≤ η₀⁻¹ := one_le_inv₀ hη₀_pos |>.mpr (le_trans hη₀_ub19 (by norm_num))
    have h1 : (ℓ : ℝ) ≤ 8 * (ℓ : ℝ) ^ 2 * η₀⁻¹ := by nlinarith
    exact Nat.cast_le.mp (le_trans h1 (Nat.le_ceil _))
  have hp_comp_le_cap : p_comp ≤ p_cap := Nat.min_le_right _ _
  let θ_r := η₀ / (64 * (ℓ : ℝ) * (p_comp : ℝ) ^ 2)
  have hθ_pos : 0 < θ_r := by
    unfold θ_r
    have : (0 : ℝ) < (p_comp : ℝ) := Nat.cast_pos.mpr (by omega)
    positivity
  have hθ_ub : θ_r ≤ 1 / (64 * (ℓ : ℝ) ^ 2) := by
    unfold θ_r
    have hη₀_le1 : η₀ ≤ 1 := le_trans hη₀_ub19 (by norm_num)
    have hp_ge_ell : (ℓ : ℝ) ≤ (p_comp : ℝ) := Nat.cast_le.mpr hℓ_le_pcomp
    have h_den : 64 * (ℓ : ℝ) ^ 2 ≤ 64 * (ℓ : ℝ) * (p_comp : ℝ) ^ 2 := by nlinarith
    exact div_le_div₀ zero_le_one hη₀_le1 (by positivity) h_den
  have hθ_lb : (2 : ℝ)⁻¹ ^ (120 * r + 8) * (p_cap : ℝ)⁻¹ ^ (4 * splitTreeD r + 3) * η_out ≤ θ_r := by
    unfold θ_r
    have h_den : 64 * (ℓ : ℝ) * (p_comp : ℝ) ^ 2 ≤ (2 : ℝ) ^ 6 * (p_cap : ℝ) ^ 3 := by
      have h1 : (ℓ : ℝ) ≤ (p_cap : ℝ) := Nat.cast_le.mpr hp_cap
      have h2 : (p_comp : ℝ) ^ 2 ≤ (p_cap : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (Nat.cast_le.mpr hp_comp_le_cap) 2
      calc 64 * (ℓ : ℝ) * (p_comp : ℝ) ^ 2
          ≤ (2 : ℝ) ^ 6 * (p_cap : ℝ) * (p_cap : ℝ) ^ 2 := by
            have h64 : (64 : ℝ) = (2 : ℝ) ^ 6 := by norm_num
            rw [h64]
            exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2 (by positivity) (by positivity)
        _ = (2 : ℝ) ^ 6 * (p_cap : ℝ) ^ 3 := by ring
    calc (2 : ℝ)⁻¹ ^ (120 * r + 8) * (p_cap : ℝ)⁻¹ ^ (4 * splitTreeD r + 3) * η_out
        = ((2 : ℝ)⁻¹ ^ (120 * r + 2) * (p_cap : ℝ)⁻¹ ^ (4 * splitTreeD r) * η_out) /
            ((2 : ℝ) ^ 6 * (p_cap : ℝ) ^ 3) := by
          rw [show 120 * r + 8 = (120 * r + 2) + 6 by omega,
            pow_add (a := (2 : ℝ)⁻¹) (m := 120 * r + 2) (n := 6),
            pow_add (a := (p_cap : ℝ)⁻¹) (m := 4 * splitTreeD r) (n := 3),
            inv_pow (a := (2 : ℝ)) (n := 6),
            inv_pow (a := (p_cap : ℝ)) (n := 3)]; ring
      _ ≤ η₀ / ((2 : ℝ) ^ 6 * (p_cap : ℝ) ^ 3) :=
          div_le_div_of_nonneg_right hη₀_lb (by positivity)
      _ ≤ η₀ / (64 * (ℓ : ℝ) * (p_comp : ℝ) ^ 2) :=
          div_le_div_of_nonneg_left (le_of_lt hη₀_pos) (by positivity) h_den
  have hB_block : IsBlockadeIn F S ℓ w B := by
    rcases hcomb with hc | hco
    · exact hc.is_blockade
    · exact hco.is_blockade
  have hB_sub_U : ∀ i : Fin ℓ, B i ⊆ U_ambient :=
    fun i => Finset.subset_biUnion_of_mem B (Finset.mem_univ i)
  have h_outer : ∀ (N : ℕ)
      (T : (i : Fin ℓ) → ActiveLeafSplitTree F (B i) (treeParamR r) (8 * m) L_max η₀),
      (∑ i : Fin ℓ, (L_max - (T i).leaves.card)) ≤ N →
      (∃ k : ℕ, L_max ≤ k ∧ k ≤ p_cap ∧
        ∃ U : Fin k → Finset V,
          IsWeaklySparseOrCoSparseBlockadeIn F U_ambient k
            (w / ((2 : ℝ) ^ (60 * r) * (k : ℝ) ^ (2 * splitTreeD r))) η_out U) ∨
      (∃ U : Fin p_cap → Finset V,
        IsWeaklySparseOrCoSparseBlockadeIn F U_ambient p_cap
          ((2 : ℝ) ^ (-(200 * (r : ℝ) ^ 2)) * η_out ^ r * (p_cap : ℝ) ^ (-(capExpE r : ℝ)) * w)
          η_out U) := by
    intro N
    induction N with
    | zero =>
      intro T h_sum_0
      have h_all_ge : ∀ i : Fin ℓ, L_max ≤ (T i).leaves.card := by
        intro i
        have h_le : L_max - (T i).leaves.card ≤ ∑ j : Fin ℓ, (L_max - (T j).leaves.card) :=
          Finset.single_le_sum (f := fun j : Fin ℓ => L_max - (T j).leaves.card)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        omega
      let i₀ : Fin ℓ := ⟨0, by omega⟩
      rcases active_leaf_split_tree_dichotomy (T i₀) hD_pos hL_low (le_of_lt hη₀_pos) with
        ⟨h_lt, _⟩ | ⟨_, U, hU_tree⟩
      · exact False.elim (by have := h_all_ge i₀; omega)
      · left
        refine ⟨L_max, le_rfl, hL_p, U,
          hU_tree.mono_ambient_width_eps (hB_sub_U i₀) ?_ hη₀_β2_le⟩
        have h_β_le : β_inv ≤ (2 : ℝ) ^ (60 * r) * (L_max : ℝ) ^ (2 * splitTreeD r) := by
          unfold β_inv
          rw [← h_Dr_eq]
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left 60 h_tr.2.1)) (by positivity)
        calc w / ((2 : ℝ) ^ (60 * r) * (L_max : ℝ) ^ (2 * splitTreeD r))
            ≤ w / β_inv := div_le_div_of_nonneg_left hw_nn hβ_pos h_β_le
          _ ≤ ((B i₀).card : ℝ) / β_inv :=
              div_le_div_of_nonneg_right (hB_block.width_ge i₀) (le_of_lt hβ_pos)
    | succ M ih =>
      intro T h_sum_M
      by_cases h_some_ge : ∃ i : Fin ℓ, L_max ≤ (T i).leaves.card
      · obtain ⟨i₀, hi₀_ge⟩ := h_some_ge
        rcases active_leaf_split_tree_dichotomy (T i₀) hD_pos hL_low (le_of_lt hη₀_pos) with
          ⟨h_lt, _⟩ | ⟨_, U, hU_tree⟩
        · exact False.elim (by omega)
        · left
          refine ⟨L_max, le_rfl, hL_p, U,
            hU_tree.mono_ambient_width_eps (hB_sub_U i₀) ?_ hη₀_β2_le⟩
          have h_β_le : β_inv ≤ (2 : ℝ) ^ (60 * r) * (L_max : ℝ) ^ (2 * splitTreeD r) := by
            unfold β_inv
            rw [← h_Dr_eq]
            exact mul_le_mul_of_nonneg_right
              (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left 60 h_tr.2.1)) (by positivity)
          calc w / ((2 : ℝ) ^ (60 * r) * (L_max : ℝ) ^ (2 * splitTreeD r))
              ≤ w / β_inv := div_le_div_of_nonneg_left hw_nn hβ_pos h_β_le
            _ ≤ ((B i₀).card : ℝ) / β_inv :=
                div_le_div_of_nonneg_right (hB_block.width_ge i₀) (le_of_lt hβ_pos)
      · push_neg at h_some_ge
        have h_ex_Wz : ∀ i : Fin ℓ,
            ∃ W_i : Finset V, W_i ∈ (T i).leaves ∧
              ((B i).card : ℝ) / (L_max : ℝ) ^ (8 * m) ≤ (W_i.card : ℝ) :=
          fun i => (T i).exists_active_leaf hD_pos (h_some_ge i)
        obtain ⟨W_z, hWz⟩ := Classical.axiomOfChoice h_ex_Wz
        have hWz_mem : ∀ i : Fin ℓ, W_z i ∈ (T i).leaves := fun i => (hWz i).1
        have hWz_sub_B : ∀ i : Fin ℓ, W_z i ⊆ B i := fun i => ((T i).subset_B (W_z i) (hWz_mem i)).1
        have hWz_active_B : ∀ i : Fin ℓ, ((B i).card : ℝ) / (L_max : ℝ) ^ (8 * m) ≤ ((W_z i).card : ℝ) :=
          fun i => (hWz i).2
        have hWz_active_w : ∀ i : Fin ℓ, w / (L_max : ℝ) ^ (splitTreeD r) ≤ ((W_z i).card : ℝ) := by
          intro i
          rw [h_Dr_eq]
          exact le_trans (div_le_div_of_nonneg_right (hB_block.width_ge i) (by positivity))
            (hWz_active_B i)
        rcases active_leaves_family_step_or_global h_grp hr hs hℓ hp_cap hp_comp_cases hL_low hL_high
            hη_pos hη_ub hη₀_pos hη₀_le_out hη₀_ub19 hη₀_lb rfl hθ_pos hθ_ub hθ_lb hIH
            hfree hcomb hstems hw_ge hB_sub_U hWz_sub_B hWz_active_w with
          h_cap | h_soc | ⟨i₀, k_sp, w_sp, U_sp, hk2, hkL, hU_sp, h_split⟩
        · exact Or.inr h_cap
        · exact Or.inl h_soc
        · let T_new_i₀ := (T i₀).split_active_leaf (hWz_mem i₀) (hWz_active_B i₀)
            h_tr.1 hm_ge8 hk2 hkL hU_sp h_split
          have h_card_gt : (T i₀).leaves.card < T_new_i₀.leaves.card :=
            (T i₀).split_active_leaf_card_gt (hWz_mem i₀) (hWz_active_B i₀)
              h_tr.1 hm_ge8 hk2 hkL hU_sp h_split
          obtain ⟨T', hT'_eq, hT'_ne⟩ :
              ∃ T' : (i : Fin ℓ) → ActiveLeafSplitTree F (B i) (treeParamR r) (8 * m) L_max η₀,
                (T' i₀).leaves.card = T_new_i₀.leaves.card ∧
                (∀ i : Fin ℓ, i ≠ i₀ → (T' i).leaves.card = (T i).leaves.card) := by
            refine ⟨fun i => if h : i = i₀ then h ▸ T_new_i₀ else T i, ?_, ?_⟩
            · simp
            · intro i hi; simp [hi]
          have h_sum_lt : (∑ i : Fin ℓ, (L_max - (T' i).leaves.card)) <
              ∑ i : Fin ℓ, (L_max - (T i).leaves.card) := by
            refine Finset.sum_lt_sum (fun i _ => ?_) ⟨i₀, Finset.mem_univ i₀, ?_⟩
            · by_cases hi : i = i₀
              · subst hi; rw [hT'_eq]; omega
              · rw [hT'_ne i hi]
            · rw [hT'_eq]
              have := h_some_ge i₀
              omega
          exact ih T' (by omega)
  let T₀ : (i : Fin ℓ) → ActiveLeafSplitTree F (B i) (treeParamR r) (8 * m) L_max η₀ :=
    fun i => ActiveLeafSplitTree.root F (B i) (treeParamR r) (8 * m) L_max η₀ (hB_block.nonempty_blocks i)
  exact h_outer (∑ i : Fin ℓ, (L_max - (T₀ i).leaves.card)) T₀ le_rfl

/-- **Master Stage-1 Family Dichotomy (`stage1Family_all_r`)**: For every graph family `H_fam`
satisfying `HasNonNeighPureGrouping H_fam` and every integer $r \ge 1$, `Stage1FamilyAt H_fam r` holds. -/
theorem stage1Family_strong_all_r {H_fam : (d : ℕ) → SimpleGraph (Fin (d + 4))}
    (h_grp : HasNonNeighPureGrouping H_fam) (r : ℕ) (hr : 1 ≤ r) :
    Stage1FamilyStrongAt H_fam r := by
  induction r using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn1 : n = 1
    · subst hn1; exact stage1Family_strong_r1 h_grp
    · have hn2 : 2 ≤ n := by omega
      exact stage1Family_strong_step h_grp hn2 (fun r' hr'1 hr'n => ih r' hr'n hr'1)

theorem stage1Family_all_r {H_fam : (d : ℕ) → SimpleGraph (Fin (d + 4))}
    (h_grp : HasNonNeighPureGrouping H_fam) (r : ℕ) (hr : 1 ≤ r) :
    Stage1FamilyAt H_fam r :=
  (stage1Family_strong_all_r h_grp r hr).to_weak

/-- **Proposition 7(2c) Stage-1 Comb/Co-Comb Dichotomy for Spiders (`spider_stage1_comb_cocomb_dichotomy`)**:
For every integer $r \ge 1$, `Stage1FamilyAt SpiderGraph r` holds unconditionally. -/
theorem spider_stage1_comb_cocomb_dichotomy (r : ℕ) (hr : 1 ≤ r) :
    Stage1FamilyAt SpiderGraph r :=
  stage1Family_all_r spiderGraph_hasNonNeighPureGrouping r hr

/-- **Proposition 7(2c) Stage-1 Comb/Co-Comb Dichotomy for Generalized Birds (`bird_stage1_comb_cocomb_dichotomy`)**:
For every integer $r \ge 1$, `Stage1FamilyAt BirdDGraph r` holds unconditionally. -/
theorem bird_stage1_comb_cocomb_dichotomy (r : ℕ) (hr : 1 ≤ r) :
    Stage1FamilyAt BirdDGraph r :=
  stage1Family_all_r birdDGraph_hasNonNeighPureGrouping r hr

/-- **Unified Comb Dichotomy Condition `(CD3)` (`stage1Family_comb_dichotomy_condition`)**:
For any graph family `H_fam` satisfying `HasNonNeighPureGrouping H_fam` and any $d \ge 2$
($r := d - 1 \ge 1$, so $1 + r = d$), any `(H_fam d)ᶜ`-free graph $F$ satisfies condition `(CD3)`
of `pair_coupled_generalized_nice_of_comb_dichotomy_explicit` with exponent
`C_comb := pathCombExpC (d + 4)`. -/
theorem stage1Family_comb_dichotomy_condition
    {H_fam : (d : ℕ) → SimpleGraph (Fin (d + 4))}
    (h_grp : HasNonNeighPureGrouping H_fam)
    {V : Type} [Fintype V] [DecidableEq V]
    {F : SimpleGraph V} {S : Finset V} {d ℓ : ℕ} {x y w : ℝ}
    {a : Fin ℓ → V} {B : Fin ℓ → Finset V} {v : V}
    (hd : 2 ≤ d)
    (hx_pos : 0 < x) (hxy : x ≤ y) (hy_ub : y ≤ (2 : ℝ)⁻¹ ^ 16)
    (hℓ_low : ⌈(1 / 2 : ℝ) * y⁻¹⌉₊ ≤ ℓ) (hℓ_high : ℓ ≤ ⌊x⁻¹⌋₊)
    (hfree : IsInducedSubgraphFree F (H_fam d)ᶜ)
    (hcomb : IsCombIn F S ℓ w a B)
    (hv : IsCombExternalApex F S ℓ a B v)
    (hw_ge_S : (S.card : ℝ) / (ℓ : ℝ) ^ 18 ≤ w) :
    let p_cap := ⌈x⁻¹ ^ 2⌉₊
    ∃ k' : ℕ, ℓ ≤ k' ∧ k' ≤ p_cap ∧
      ∃ U : Fin k' → Finset V,
        IsWeaklySparseOrCoSparseBlockadeIn F S k'
          ((S.card : ℝ) / (k' : ℝ) ^ (pathCombExpC (d + 4))) x U := by
  classical
  intro p_cap
  let r := d - 1
  have hr : 1 ≤ r := by omega
  have hx_ub : x ≤ (2 : ℝ)⁻¹ ^ 16 := le_trans hxy hy_ub
  have hx_le1 : x ≤ 1 := le_trans hx_ub (by norm_num)
  have hx_inv_ge1 : 1 ≤ x⁻¹ := one_le_inv₀ hx_pos |>.mpr hx_le1
  have hℓ_64 : 64 ≤ ℓ := by
    have hy_pos : 0 < y := lt_of_lt_of_le hx_pos hxy
    have hy_inv : (2 : ℝ) ^ 16 ≤ y⁻¹ := by
      have h1 := inv_anti₀ hy_pos hy_ub
      rwa [inv_pow, inv_inv] at h1
    have h64_ceil : (64 : ℝ) ≤ (1 / 2 : ℝ) * y⁻¹ := by linarith [show (128 : ℝ) ≤ (2 : ℝ) ^ 16 by norm_num]
    have h1 : (64 : ℝ) ≤ (⌈(1 / 2 : ℝ) * y⁻¹⌉₊ : ℝ) := le_trans h64_ceil (Nat.le_ceil _)
    exact le_trans (Nat.ofNat_le_cast.mp h1) hℓ_low
  have hx2_le_pcap : x⁻¹ ^ 2 ≤ (p_cap : ℝ) := Nat.le_ceil (x⁻¹ ^ 2)
  have hx_inv_le_pcap : x⁻¹ ≤ (p_cap : ℝ) := by
    have : x⁻¹ ≤ x⁻¹ ^ 2 := by nlinarith
    exact le_trans this hx2_le_pcap
  have hℓ_le_pcap : ℓ ≤ p_cap := by
    have h1 : (ℓ : ℝ) ≤ x⁻¹ :=
      le_trans (Nat.cast_le.mpr hℓ_high) (Nat.floor_le (by positivity))
    exact Nat.cast_le.mp (le_trans h1 hx_inv_le_pcap)
  have hp_64 : 64 ≤ p_cap := le_trans hℓ_64 hℓ_le_pcap
  have hp_r : (64 : ℝ) ≤ (p_cap : ℝ) := Nat.ofNat_le_cast.mpr hp_64
  have hp_pos : (0 : ℝ) < (p_cap : ℝ) := by linarith
  have hp_ge1 : (1 : ℝ) ≤ (p_cap : ℝ) := by linarith
  have hp_inv_le_x : (p_cap : ℝ)⁻¹ ≤ x := by
    have h1 : 1 ≤ (p_cap : ℝ) * x ^ 2 := by
      have h := mul_le_mul_of_nonneg_right hx2_le_pcap (show 0 ≤ x ^ 2 by positivity)
      rwa [inv_pow, inv_mul_cancel₀ (ne_of_gt (pow_pos hx_pos 2))] at h
    have h2 : (p_cap : ℝ) * x ^ 2 ≤ x * (p_cap : ℝ) := by nlinarith
    exact (inv_le_iff_one_le_mul₀ hp_pos).mpr (le_trans h1 h2)
  have hℓ_le_S : ℓ ≤ S.card := comb_blockade_card_ge_ell hcomb.is_blockade
  have hℓ_pos_r : (0 : ℝ) < (ℓ : ℝ) := Nat.cast_pos.mpr (by omega)
  have hw_nn : 0 ≤ w := le_trans (by positivity) hw_ge_S
  let C := pathCombExpC (d + 4)
  have hC_eq : C = 3 * capExpE r + 4 * splitTreeD r + 100 := by
    change 3 * capExpE (d + 4 - 5) + 4 * splitTreeD (d + 4 - 5) + 100 =
      3 * capExpE r + 4 * splitTreeD r + 100
    rw [show d + 4 - 5 = r by omega]
  by_cases hw_min : combMinWidth r x p_cap ≤ w
  · have hstems := hasPerHandleApexStems_one_of_isCombExternalApex hv
    have hfree_r : IsInducedSubgraphFree F (H_fam (1 + r))ᶜ := by
      rwa [show 1 + r = d by omega]
    have hU_sub_S : Finset.univ.biUnion B ⊆ S :=
      Finset.biUnion_subset.mpr (fun i _ => hcomb.is_blockade.subset_ambient i)
    rcases stage1Family_all_r h_grp r hr hr V F S 1 ℓ p_cap ℓ x w a B (fun _ _ => v)
        le_rfl hℓ_64 hℓ_le_pcap (by omega) le_rfl hx_pos hx_ub hfree_r (Or.inl hcomb) hstems hw_min with
      ⟨k', hℓ_k', hk'_p, U, hU⟩ | ⟨U, hU_cap⟩
    · refine ⟨k', hℓ_k', hk'_p, U, hU.mono_ambient_width_eps hU_sub_S ?_ le_rfl⟩
      have hk'_64 : 64 ≤ k' := le_trans hℓ_64 hℓ_k'
      have hk'_ge1 : (1 : ℝ) ≤ (k' : ℝ) := Nat.one_le_cast.mpr (by omega)
      have hℓ_k'_18 : (ℓ : ℝ) ^ 18 ≤ (k' : ℝ) ^ 18 :=
        pow_le_pow_left₀ (by positivity) (Nat.cast_le.mpr hℓ_k') 18
      have h2_60r : (2 : ℝ) ^ (60 * r) ≤ (k' : ℝ) ^ (10 * r) := by
        have h64 : (2 : ℝ) ^ 6 ≤ (k' : ℝ) := by
          have : (64 : ℝ) ≤ (k' : ℝ) := Nat.ofNat_le_cast.mpr hk'_64
          norm_num at this ⊢; exact this
        have h1 := pow_le_pow_left₀ (by positivity) h64 (10 * r)
        rwa [← pow_mul, show 6 * (10 * r) = 60 * r by ring] at h1
      have h_exp_le : 18 + 10 * r + 3 * splitTreeD r ≤ C := by
        rw [hC_eq]
        have : 10 * r ≤ 2 * capExpE r := by
          unfold capExpE
          have : 1 ≤ 16 ^ r := Nat.one_le_pow r 16 (by omega)
          nlinarith
        omega
      have h_den : (ℓ : ℝ) ^ 18 * ((2 : ℝ) ^ (60 * r) * (k' : ℝ) ^ (3 * splitTreeD r)) ≤ (k' : ℝ) ^ C := by
        calc (ℓ : ℝ) ^ 18 * ((2 : ℝ) ^ (60 * r) * (k' : ℝ) ^ (3 * splitTreeD r))
            ≤ (k' : ℝ) ^ 18 * ((k' : ℝ) ^ (10 * r) * (k' : ℝ) ^ (3 * splitTreeD r)) :=
              mul_le_mul hℓ_k'_18 (mul_le_mul_of_nonneg_right h2_60r (by positivity))
                (by positivity) (by positivity)
          _ = (k' : ℝ) ^ (18 + 10 * r + 3 * splitTreeD r) := by rw [← pow_add, ← pow_add]; ring_nf
          _ ≤ (k' : ℝ) ^ C := pow_le_pow_right₀ hk'_ge1 h_exp_le
      calc (S.card : ℝ) / (k' : ℝ) ^ C
          ≤ (S.card : ℝ) / ((ℓ : ℝ) ^ 18 * ((2 : ℝ) ^ (60 * r) * (k' : ℝ) ^ (3 * splitTreeD r))) :=
            div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) h_den
        _ = ((S.card : ℝ) / (ℓ : ℝ) ^ 18) / ((2 : ℝ) ^ (60 * r) * (k' : ℝ) ^ (3 * splitTreeD r)) := by ring
        _ ≤ w / ((2 : ℝ) ^ (60 * r) * (k' : ℝ) ^ (3 * splitTreeD r)) :=
            div_le_div_of_nonneg_right hw_ge_S (by positivity)
    · refine ⟨p_cap, hℓ_le_pcap, le_rfl, U, hU_cap.mono_ambient_width_eps hU_sub_S ?_ le_rfl⟩
      rw [show -(200 * (r : ℝ) ^ 2) = -(((200 * r ^ 2 : ℕ) : ℝ)) by push_cast; ring,
        rpow_neg_natCast (by norm_num) (200 * r ^ 2), ← inv_pow,
        show -(capExpE r : ℝ) = -(((capExpE r : ℕ) : ℝ)) by rfl,
        rpow_neg_natCast (le_of_lt hp_pos) (capExpE r), ← inv_pow]
      have h2_p : (p_cap : ℝ)⁻¹ ^ (35 * r ^ 2) ≤ (2 : ℝ)⁻¹ ^ (200 * r ^ 2) := by
        have h64 : (p_cap : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ ^ 6 := by
          have : (2 : ℝ) ^ 6 ≤ (p_cap : ℝ) := by norm_num at hp_r ⊢; exact hp_r
          rw [inv_pow]; exact inv_anti₀ (by positivity) this
        have h1 := pow_le_pow_left₀ (by positivity) h64 (35 * r ^ 2)
        rw [← pow_mul, show 6 * (35 * r ^ 2) = 210 * r ^ 2 by ring] at h1
        exact le_trans h1 (pow_le_pow_of_le_one (by positivity) (by norm_num) (by nlinarith))
      have hx_r : (p_cap : ℝ)⁻¹ ^ r ≤ x ^ r :=
        pow_le_pow_left₀ (by positivity) hp_inv_le_x r
      have hw_p : (S.card : ℝ) * (p_cap : ℝ)⁻¹ ^ 18 ≤ w := by
        calc (S.card : ℝ) * (p_cap : ℝ)⁻¹ ^ 18
            = (S.card : ℝ) / (p_cap : ℝ) ^ 18 := by rw [inv_pow]; ring
          _ ≤ (S.card : ℝ) / (ℓ : ℝ) ^ 18 :=
              div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
                (pow_le_pow_left₀ (by positivity) (Nat.cast_le.mpr hℓ_le_pcap) 18)
          _ ≤ w := hw_ge_S
      have h_exp_le : 35 * r ^ 2 + r + capExpE r + 18 ≤ C := by
        rw [hC_eq]
        have := seventy_sq_le_two_mul_capExpE r hr
        omega
      have hp_C : (p_cap : ℝ)⁻¹ ^ C ≤
          (p_cap : ℝ)⁻¹ ^ (35 * r ^ 2) * (p_cap : ℝ)⁻¹ ^ r *
          (p_cap : ℝ)⁻¹ ^ (capExpE r) * (p_cap : ℝ)⁻¹ ^ 18 := by
        rw [← pow_add, ← pow_add, ← pow_add]
        exact pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hp_ge1) h_exp_le
      calc (S.card : ℝ) / (p_cap : ℝ) ^ C
          = (S.card : ℝ) * (p_cap : ℝ)⁻¹ ^ C := by rw [inv_pow]; ring
        _ ≤ (S.card : ℝ) * ((p_cap : ℝ)⁻¹ ^ (35 * r ^ 2) * (p_cap : ℝ)⁻¹ ^ r *
              (p_cap : ℝ)⁻¹ ^ (capExpE r) * (p_cap : ℝ)⁻¹ ^ 18) :=
            mul_le_mul_of_nonneg_left hp_C (Nat.cast_nonneg _)
        _ = (p_cap : ℝ)⁻¹ ^ (35 * r ^ 2) * (p_cap : ℝ)⁻¹ ^ r * (p_cap : ℝ)⁻¹ ^ (capExpE r) *
              ((S.card : ℝ) * (p_cap : ℝ)⁻¹ ^ 18) := by ring
        _ ≤ (2 : ℝ)⁻¹ ^ (200 * r ^ 2) * x ^ r * (p_cap : ℝ)⁻¹ ^ (capExpE r) * w := by
            refine mul_le_mul ?_ hw_p (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_right (mul_le_mul h2_p hx_r (by positivity) (by positivity))
              (by positivity)
  · push_neg at hw_min
    let k' := min S.card p_cap
    have hk'_le_S : k' ≤ S.card := Nat.min_le_left _ _
    have hk'_le_p : k' ≤ p_cap := Nat.min_le_right _ _
    have hℓ_le_k' : ℓ ≤ k' := le_min hℓ_le_S hℓ_le_pcap
    obtain ⟨U, hU_pure⟩ := singleton_pure_blockade_of_card_ge F S hk'_le_S
    refine ⟨k', hℓ_le_k', hk'_le_p, U,
      (IsPureBlockadeIn.isWeaklySparseOrCoSparseBlockadeIn hU_pure (le_of_lt hx_pos)).mono_ambient_width_eps
        Finset.Subset.rfl ?_ le_rfl⟩
    have hk'_pos : (0 : ℝ) < (k' : ℝ) := Nat.cast_pos.mpr (by omega)
    have hk'_ge1 : (1 : ℝ) ≤ (k' : ℝ) := Nat.one_le_cast.mpr (by omega)
    by_cases hS_le_p : S.card ≤ p_cap
    · have hk'_eq : k' = S.card := Nat.min_eq_left hS_le_p
      rw [← hk'_eq, div_le_one (by positivity)]
      have hC_pos : 1 ≤ C := by rw [hC_eq]; omega
      simpa using pow_le_pow_right₀ hk'_ge1 hC_pos
    · push_neg at hS_le_p
      have hk'_eq : k' = p_cap := Nat.min_eq_right (le_of_lt hS_le_p)
      rw [hk'_eq, div_le_one (by positivity)]
      unfold combMinWidth at hw_min
      rw [show -(3 * (r : ℝ)) = -(((3 * r : ℕ) : ℝ)) by push_cast; ring,
        rpow_neg_natCast (le_of_lt hx_pos) (3 * r), ← inv_pow] at hw_min
      have h2_400 : (2 : ℝ) ^ (400 * r ^ 2) ≤ (p_cap : ℝ) ^ (70 * r ^ 2) := by
        have h64 : (2 : ℝ) ^ 6 ≤ (p_cap : ℝ) := by norm_num at hp_r ⊢; exact hp_r
        have h1 := pow_le_pow_left₀ (by positivity) h64 (70 * r ^ 2)
        rw [← pow_mul, show 6 * (70 * r ^ 2) = 420 * r ^ 2 by ring] at h1
        exact le_trans (pow_le_pow_right₀ (by norm_num) (by nlinarith)) h1
      have hx_3r : (x⁻¹) ^ (3 * r) ≤ (p_cap : ℝ) ^ (3 * r) :=
        pow_le_pow_left₀ (by positivity) hx_inv_le_pcap (3 * r)
      have hw_le_p : w ≤ (p_cap : ℝ) ^ (70 * r ^ 2 + 3 * r + (capExpE r + 2 * splitTreeD r)) := by
        calc w ≤ (2 : ℝ) ^ (400 * r ^ 2) * (x⁻¹) ^ (3 * r) * (p_cap : ℝ) ^ (capExpE r + 2 * splitTreeD r) :=
              le_of_lt hw_min
          _ ≤ (p_cap : ℝ) ^ (70 * r ^ 2) * (p_cap : ℝ) ^ (3 * r) * (p_cap : ℝ) ^ (capExpE r + 2 * splitTreeD r) :=
              mul_le_mul_of_nonneg_right (mul_le_mul h2_400 hx_3r (by positivity) (by positivity)) (by positivity)
          _ = (p_cap : ℝ) ^ (70 * r ^ 2 + 3 * r + (capExpE r + 2 * splitTreeD r)) := by
              rw [← pow_add, ← pow_add]
      have hS_le_ell_w : (S.card : ℝ) ≤ (p_cap : ℝ) ^ 18 * w := by
        have h1 : (S.card : ℝ) ≤ (ℓ : ℝ) ^ 18 * w := by
          have hℓ_pos : (0 : ℝ) < (ℓ : ℝ) ^ 18 := by positivity
          have := (div_le_iff₀ hℓ_pos).mp hw_ge_S
          linarith
        have h2 : (ℓ : ℝ) ^ 18 ≤ (p_cap : ℝ) ^ 18 :=
          pow_le_pow_left₀ (by positivity) (Nat.cast_le.mpr hℓ_le_pcap) 18
        exact le_trans h1 (mul_le_mul_of_nonneg_right h2 hw_nn)
      have h_exp_le : 18 + (70 * r ^ 2 + 3 * r + (capExpE r + 2 * splitTreeD r)) ≤ C := by
        rw [hC_eq]
        have := seventy_sq_le_two_mul_capExpE r hr
        omega
      calc (S.card : ℝ)
          ≤ (p_cap : ℝ) ^ 18 * w := hS_le_ell_w
        _ ≤ (p_cap : ℝ) ^ 18 * (p_cap : ℝ) ^ (70 * r ^ 2 + 3 * r + (capExpE r + 2 * splitTreeD r)) :=
            mul_le_mul_of_nonneg_left hw_le_p (by positivity)
        _ = (p_cap : ℝ) ^ (18 + (70 * r ^ 2 + 3 * r + (capExpE r + 2 * splitTreeD r))) := by
            rw [← pow_add]
        _ ≤ (p_cap : ℝ) ^ C := pow_le_pow_right₀ hp_ge1 h_exp_le

/-- Condition `(CD3)` for `SpiderGraph d` ($d \ge 2$). -/
theorem spider_comb_dichotomy_condition
    {V : Type} [Fintype V] [DecidableEq V]
    {F : SimpleGraph V} {S : Finset V} {d ℓ : ℕ} {x y w : ℝ}
    {a : Fin ℓ → V} {B : Fin ℓ → Finset V} {v : V}
    (hd : 2 ≤ d)
    (hx_pos : 0 < x) (hxy : x ≤ y) (hy_ub : y ≤ (2 : ℝ)⁻¹ ^ 16)
    (hℓ_low : ⌈(1 / 2 : ℝ) * y⁻¹⌉₊ ≤ ℓ) (hℓ_high : ℓ ≤ ⌊x⁻¹⌋₊)
    (hfree : IsInducedSubgraphFree F (SpiderGraph d)ᶜ)
    (hcomb : IsCombIn F S ℓ w a B)
    (hv : IsCombExternalApex F S ℓ a B v)
    (hw_ge_S : (S.card : ℝ) / (ℓ : ℝ) ^ 18 ≤ w) :
    let p_cap := ⌈x⁻¹ ^ 2⌉₊
    ∃ k' : ℕ, ℓ ≤ k' ∧ k' ≤ p_cap ∧
      ∃ U : Fin k' → Finset V,
        IsWeaklySparseOrCoSparseBlockadeIn F S k'
          ((S.card : ℝ) / (k' : ℝ) ^ (pathCombExpC (d + 4))) x U :=
  stage1Family_comb_dichotomy_condition spiderGraph_hasNonNeighPureGrouping
    hd hx_pos hxy hy_ub hℓ_low hℓ_high hfree hcomb hv hw_ge_S

/-- Condition `(CD3)` for `BirdDGraph d` ($d \ge 2$). -/
theorem bird_comb_dichotomy_condition
    {V : Type} [Fintype V] [DecidableEq V]
    {F : SimpleGraph V} {S : Finset V} {d ℓ : ℕ} {x y w : ℝ}
    {a : Fin ℓ → V} {B : Fin ℓ → Finset V} {v : V}
    (hd : 2 ≤ d)
    (hx_pos : 0 < x) (hxy : x ≤ y) (hy_ub : y ≤ (2 : ℝ)⁻¹ ^ 16)
    (hℓ_low : ⌈(1 / 2 : ℝ) * y⁻¹⌉₊ ≤ ℓ) (hℓ_high : ℓ ≤ ⌊x⁻¹⌋₊)
    (hfree : IsInducedSubgraphFree F (BirdDGraph d)ᶜ)
    (hcomb : IsCombIn F S ℓ w a B)
    (hv : IsCombExternalApex F S ℓ a B v)
    (hw_ge_S : (S.card : ℝ) / (ℓ : ℝ) ^ 18 ≤ w) :
    let p_cap := ⌈x⁻¹ ^ 2⌉₊
    ∃ k' : ℕ, ℓ ≤ k' ∧ k' ≤ p_cap ∧
      ∃ U : Fin k' → Finset V,
        IsWeaklySparseOrCoSparseBlockadeIn F S k'
          ((S.card : ℝ) / (k' : ℝ) ^ (pathCombExpC (d + 4))) x U :=
  stage1Family_comb_dichotomy_condition birdDGraph_hasNonNeighPureGrouping
    hd hx_pos hxy hy_ub hℓ_low hℓ_high hfree hcomb hv hw_ge_S

/-!
## Section 5: Unconditional Leaf-Reducibility and Stage-1 Coupled Generalized Niceness
(`Proposition 7(2c)` & `Lemma 14(1)` / `Proposition 8(1)` / `Theorem 9(1)` of `main.tex`)
-/

/-- Hereditary monotonicity of `HasErdosHajnalProp` along an induced graph embedding $H_1 \hookrightarrow_g H_2$. -/
theorem hasErdosHajnalProp_of_embedding' {W₁ W₂ : Type*}
    {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂}
    (f : H₁ ↪g H₂) (h₂ : HasErdosHajnalProp H₂) : HasErdosHajnalProp H₁ := by
  obtain ⟨c, hc, hprop⟩ := h₂
  refine ⟨c, hc, fun V _ _ G hG => hprop V G ?_⟩
  rintro ⟨g, hg⟩
  refine hG ⟨f.toEmbedding.trans g, ?_⟩
  ext u v
  exact f.map_rel_iff.symm.trans (congr_arg (fun H : SimpleGraph W₂ => H.Adj (f u) (f v)) hg).to_iff

/-- Canonical induced graph embedding $P_j \hookrightarrow_g P_k$ for $j \le k$. -/
def pathGraph_mono_embedding' {j k : ℕ} (hjk : j ≤ k) : pathGraph j ↪g pathGraph k where
  toEmbedding := Fin.castLEEmb hjk
  map_rel_iff' := by
    intro a b
    simp [pathGraph_adj]

/-- Complement invariance of `IsPureBlockadeIn`. -/
lemma isPureBlockadeIn_compl_of_pure' {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {S : Finset V} {k : ℕ} {w : ℝ} {B : Fin k → Finset V}
    (hB : IsPureBlockadeIn Gᶜ S k w B) : IsPureBlockadeIn G S k w B := by
  refine ⟨⟨hB.1.subset_ambient, hB.1.nonempty_blocks, hB.1.pairwise_disjoint, hB.1.width_ge⟩, ?_⟩
  intro i j hij
  have hdisj := hB.1.pairwise_disjoint i j hij
  rcases hB.2 i j hij with hcomp | hanti
  · right
    intro u hu v hv hadj
    exact (hcomp u hu v hv).2 hadj
  · left
    intro u hu v hv
    have hne : u ≠ v := fun h => Finset.disjoint_left.mp hdisj hu (h ▸ hv)
    by_contra hnadj
    exact hanti u hu v hv ⟨hne, hnadj⟩

/-- Pattern graph complement identity for a pairwise-pure blockade in $Gᶜ$. -/
lemma purePatternGraph_compl_eq' {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {S : Finset V} {k : ℕ} {w : ℝ} {B : Fin k → Finset V}
    (hB : IsPureBlockadeIn Gᶜ S k w B) :
    purePatternGraph G B = (purePatternGraph Gᶜ B)ᶜ := by
  ext i j
  simp only [purePatternGraph, SimpleGraph.compl_adj, not_and]
  refine ⟨fun ⟨hij, hcomp⟩ => ⟨hij, fun _ hcomp_c => ?_⟩, fun ⟨hij, hncomp_c⟩ => ⟨hij, ?_⟩⟩
  · obtain ⟨u, hu⟩ := hB.1.nonempty_blocks i
    obtain ⟨v, hv⟩ := hB.1.nonempty_blocks j
    exact (hcomp_c u hu v hv).2 (hcomp u hu v hv)
  · rcases hB.2 i j hij with hcomp_c | hanti_c
    · exact False.elim (hncomp_c hij hcomp_c)
    · intro u hu v hv
      have hne : u ≠ v :=
        fun h => Finset.disjoint_left.mp (hB.1.pairwise_disjoint i j hij) hu (h ▸ hv)
      by_contra hnadj
      exact hanti_c u hu v hv ⟨hne, hnadj⟩

def pathGraph4ComplIsoStage1 : (pathGraph 4)ᶜ ≃g pathGraph 4 where
  toFun := ![2, 0, 3, 1]
  invFun := ![1, 3, 0, 2]
  left_inv u := by fin_cases u <;> rfl
  right_inv v := by fin_cases v <;> rfl
  map_rel_iff' := by intro u v; fin_cases u <;> fin_cases v <;> decide

lemma isInducedSubgraphFree_compl_pathGraph4_imp {W : Type*} (J : SimpleGraph W) :
    IsInducedSubgraphFree Jᶜ (pathGraph 4) → IsInducedSubgraphFree J (pathGraph 4) := by
  intro h ⟨g, hg⟩
  refine h ⟨pathGraph4ComplIsoStage1.symm.toEquiv.toEmbedding.trans g, ?_⟩
  ext u v
  dsimp
  rw [← pathGraph4ComplIsoStage1.symm.map_rel_iff]
  simp only [compl_adj, comap_adj]
  have h1 := (congr_arg (fun K => K.Adj (pathGraph4ComplIsoStage1.symm u) (pathGraph4ComplIsoStage1.symm v)) hg).to_iff
  rw [h1]
  exact and_congr g.injective.ne_iff.symm Iff.rfl

lemma isInducedSubgraphFree_compl_pathGraph4_iff' {W : Type*} (J : SimpleGraph W) :
    IsInducedSubgraphFree Jᶜ (pathGraph 4) ↔ IsInducedSubgraphFree J (pathGraph 4) :=
  ⟨isInducedSubgraphFree_compl_pathGraph4_imp J,
   fun h => by simpa [compl_compl] using isInducedSubgraphFree_compl_pathGraph4_imp Jᶜ (by simpa [compl_compl] using h)⟩

/-- Complement symmetry of `IsCoupledGeneralizedNice`: if $H$ is coupled Stage-1 generalized nice,
then so is $Hᶜ$. -/
theorem isCoupledGeneralizedNice_compl {W : Type*} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} (h : IsCoupledGeneralizedNice H) : IsCoupledGeneralizedNice Hᶜ := by
  obtain ⟨c₁, c₂, c₃, c₄, c₅, c₆, c₇, c₈, c₉,
    hc₁, hc₂, hc₃, hc₄, hc₅, hc₆, hc₇, hc₈, hc₉, hprop⟩ := h
  refine ⟨c₁, c₂, c₃, c₄, c₅, c₆, c₇, c₈, c₉,
    hc₁, hc₂, hc₃, hc₄, hc₅, hc₆, hc₇, hc₈, hc₉, ?_⟩
  intro V _ _ G ε x_sp hε0 hε_half hx_lo hx_hi hG
  have hGc : IsInducedSubgraphFree Gᶜ Hᶜ := by
    rw [compl_compl] at hG
    exact (isInducedSubgraphFree_compl_iff G H).mp hG
  rcases hprop V Gᶜ ε x_sp hε0 hε_half hx_lo hx_hi hGc with
    ⟨B, hB⟩ | hGN2 | ⟨k, hk_lo, hk_hi, B, hB⟩ | ⟨S, hS_rest, hS_card⟩
  · left
    refine ⟨B, ⟨hB.1.subset_ambient, hB.1.nonempty_blocks, hB.1.pairwise_disjoint, hB.1.width_ge⟩, ?_⟩
    intro i j hij
    rcases hB.2 i j hij with h1 | h2
    · exact Or.inr h1
    · rw [compl_compl] at h2
      exact Or.inl h2
  · right; left
    rwa [kappa_compl] at hGN2
  · right; right; left
    refine ⟨k, hk_lo, hk_hi, B, isPureBlockadeIn_compl_of_pure' hB.1, ?_⟩
    rw [purePatternGraph_compl_eq' hB.1]
    exact (isInducedSubgraphFree_compl_pathGraph4_iff' (purePatternGraph Gᶜ B)).mpr hB.2
  · right; right; right
    refine ⟨S, ?_, hS_card⟩
    rcases hS_rest with h1 | h2
    · exact Or.inr h1
    · rw [compl_compl] at h2
      exact Or.inl h2

/-- Arithmetic lower bound $|F'| / \ell^{18} \le y^4 |F'| / \ell^2$ when $\ell \ge y^{-1/4}$. -/
lemma comb_width_ge_card_div_pow_18' {V : Type*} (F' : Finset V) {y : ℝ} {ℓ : ℕ}
    (hy0 : 0 < y) (hℓ_lo : y ^ (-(1 / 4 : ℝ)) ≤ (ℓ : ℝ)) :
    (F'.card : ℝ) / (ℓ : ℝ) ^ 18 ≤ y ^ 4 * (F'.card : ℝ) / (ℓ : ℝ) ^ 2 := by
  have hℓ_pos : (0 : ℝ) < (ℓ : ℝ) := lt_of_lt_of_le (by positivity) hℓ_lo
  have hy_inv_le_ℓ4 : y⁻¹ ≤ (ℓ : ℝ) ^ 4 := by
    have hp := pow_le_pow_left₀ (by positivity) hℓ_lo 4
    have h_eq : (y ^ (-(1 / 4 : ℝ))) ^ 4 = y⁻¹ := by
      rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul hy0.le]
      norm_num
      exact Real.rpow_neg_one y
    rwa [h_eq] at hp
  have hy4_inv_le_ℓ16 : (y ^ 4)⁻¹ ≤ (ℓ : ℝ) ^ 16 := by
    have hp := pow_le_pow_left₀ (by positivity) hy_inv_le_ℓ4 4
    rwa [inv_pow, ← pow_mul] at hp
  have hℓ16_inv_le_y4 : ((ℓ : ℝ) ^ 16)⁻¹ ≤ y ^ 4 := by
    rw [← inv_inv (y ^ 4)]
    exact inv_anti₀ (by positivity) hy4_inv_le_ℓ16
  calc (F'.card : ℝ) / (ℓ : ℝ) ^ 18
    _ = ((ℓ : ℝ) ^ 16)⁻¹ * ((F'.card : ℝ) / (ℓ : ℝ) ^ 2) := by
      rw [show (18 : ℕ) = 2 + 16 by rfl, pow_add, ← div_div, div_eq_inv_mul]
    _ ≤ y ^ 4 * ((F'.card : ℝ) / (ℓ : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hℓ16_inv_le_y4 (by positivity)
    _ = y ^ 4 * (F'.card : ℝ) / (ℓ : ℝ) ^ 2 := (mul_div_assoc _ _ _).symm

/-- `64 ≤ ℓ` form of `stage1Family_comb_dichotomy_condition` matching Lemma 7(1). -/
theorem stage1Family_comb_dichotomy_64
    {H_fam : (d : ℕ) → SimpleGraph (Fin (d + 4))}
    (h_grp : HasNonNeighPureGrouping H_fam)
    {V : Type} [Fintype V] [DecidableEq V]
    {F : SimpleGraph V} {S : Finset V} {d ℓ : ℕ} {x y w : ℝ}
    {a : Fin ℓ → V} {B : Fin ℓ → Finset V} {v : V}
    (hd : 2 ≤ d)
    (hx_pos : 0 < x) (hxy : x ≤ y) (hy_ub : y ≤ (2 : ℝ)⁻¹ ^ 16)
    (hℓ_64 : 64 ≤ ℓ) (hℓ_high : (ℓ : ℝ) ≤ x⁻¹)
    (hfree : IsInducedSubgraphFree F (H_fam d)ᶜ)
    (hcomb : IsCombIn F S ℓ w a B)
    (hv : IsCombExternalApex F S ℓ a B v)
    (hw_ge_S : (S.card : ℝ) / (ℓ : ℝ) ^ 18 ≤ w) :
    let p_cap := ⌈x ^ (-2 : ℝ)⌉₊
    ∃ k' : ℕ, ℓ ≤ k' ∧ k' ≤ p_cap ∧
      ∃ U : Fin k' → Finset V,
        IsWeaklySparseOrCoSparseBlockadeIn F S k'
          ((S.card : ℝ) / (k' : ℝ) ^ (pathCombExpC (d + 4))) x U := by
  classical
  intro p_cap
  let r := d - 1
  have hr : 1 ≤ r := by omega
  have hx_ub : x ≤ (2 : ℝ)⁻¹ ^ 16 := le_trans hxy hy_ub
  have hx_le1 : x ≤ 1 := le_trans hx_ub (by norm_num)
  have hx_inv_ge1 : 1 ≤ x⁻¹ := one_le_inv₀ hx_pos |>.mpr hx_le1
  have hp_cap_eq : x ^ (-2 : ℝ) = x⁻¹ ^ 2 := by
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hx_pos.le,
      Real.rpow_natCast, inv_pow]
  have hx2_le_pcap : x⁻¹ ^ 2 ≤ (p_cap : ℝ) := by
    dsimp [p_cap]; rw [hp_cap_eq]; exact Nat.le_ceil (x⁻¹ ^ 2)
  have hx_inv_le_pcap : x⁻¹ ≤ (p_cap : ℝ) := by
    have : x⁻¹ ≤ x⁻¹ ^ 2 := by nlinarith
    exact le_trans this hx2_le_pcap
  have hℓ_le_pcap : ℓ ≤ p_cap :=
    Nat.cast_le.mp (le_trans hℓ_high hx_inv_le_pcap)
  have hp_64 : 64 ≤ p_cap := le_trans hℓ_64 hℓ_le_pcap
  have hp_r : (64 : ℝ) ≤ (p_cap : ℝ) := Nat.ofNat_le_cast.mpr hp_64
  have hp_pos : (0 : ℝ) < (p_cap : ℝ) := by linarith
  have hp_ge1 : (1 : ℝ) ≤ (p_cap : ℝ) := by linarith
  have hp_inv_le_x : (p_cap : ℝ)⁻¹ ≤ x := by
    have h1 : 1 ≤ (p_cap : ℝ) * x ^ 2 := by
      have h := mul_le_mul_of_nonneg_right hx2_le_pcap (show 0 ≤ x ^ 2 by positivity)
      rwa [inv_pow, inv_mul_cancel₀ (ne_of_gt (pow_pos hx_pos 2))] at h
    have h2 : (p_cap : ℝ) * x ^ 2 ≤ x * (p_cap : ℝ) := by nlinarith
    exact (inv_le_iff_one_le_mul₀ hp_pos).mpr (le_trans h1 h2)
  have hℓ_le_S : ℓ ≤ S.card := comb_blockade_card_ge_ell hcomb.is_blockade
  have hw_nn : 0 ≤ w := le_trans (by positivity) hw_ge_S
  let C := pathCombExpC (d + 4)
  have hC_eq : C = 3 * capExpE r + 4 * splitTreeD r + 100 := by
    change 3 * capExpE (d + 4 - 5) + 4 * splitTreeD (d + 4 - 5) + 100 =
      3 * capExpE r + 4 * splitTreeD r + 100
    rw [show d + 4 - 5 = r by omega]
  by_cases hw_min : combMinWidth r x p_cap ≤ w
  · have hstems := hasPerHandleApexStems_one_of_isCombExternalApex hv
    have hfree_r : IsInducedSubgraphFree F (H_fam (1 + r))ᶜ := by
      rwa [show 1 + r = d by omega]
    have hU_sub_S : Finset.univ.biUnion B ⊆ S :=
      Finset.biUnion_subset.mpr (fun i _ => hcomb.is_blockade.subset_ambient i)
    rcases stage1Family_all_r h_grp r hr hr V F S 1 ℓ p_cap ℓ x w a B (fun _ _ => v)
        le_rfl hℓ_64 hℓ_le_pcap (by omega) le_rfl hx_pos hx_ub hfree_r (Or.inl hcomb) hstems hw_min with
      ⟨k', hℓ_k', hk'_p, U, hU⟩ | ⟨U, hU_cap⟩
    · refine ⟨k', hℓ_k', hk'_p, U, hU.mono_ambient_width_eps hU_sub_S ?_ le_rfl⟩
      have hk'_64 : 64 ≤ k' := le_trans hℓ_64 hℓ_k'
      have hk'_ge1 : (1 : ℝ) ≤ (k' : ℝ) := Nat.one_le_cast.mpr (by omega)
      have hℓ_k'_18 : (ℓ : ℝ) ^ 18 ≤ (k' : ℝ) ^ 18 :=
        pow_le_pow_left₀ (by positivity) (Nat.cast_le.mpr hℓ_k') 18
      have h2_60r : (2 : ℝ) ^ (60 * r) ≤ (k' : ℝ) ^ (10 * r) := by
        have h64 : (2 : ℝ) ^ 6 ≤ (k' : ℝ) := by
          have : (64 : ℝ) ≤ (k' : ℝ) := Nat.ofNat_le_cast.mpr hk'_64
          norm_num at this ⊢; exact this
        have h1 := pow_le_pow_left₀ (by positivity) h64 (10 * r)
        rwa [← pow_mul, show 6 * (10 * r) = 60 * r by ring] at h1
      have h_exp_le : 18 + 10 * r + 3 * splitTreeD r ≤ C := by
        rw [hC_eq]
        have : 10 * r ≤ 2 * capExpE r := by
          unfold capExpE
          have : 1 ≤ 16 ^ r := Nat.one_le_pow r 16 (by omega)
          nlinarith
        omega
      have h_den : (ℓ : ℝ) ^ 18 * ((2 : ℝ) ^ (60 * r) * (k' : ℝ) ^ (3 * splitTreeD r)) ≤ (k' : ℝ) ^ C := by
        calc (ℓ : ℝ) ^ 18 * ((2 : ℝ) ^ (60 * r) * (k' : ℝ) ^ (3 * splitTreeD r))
            ≤ (k' : ℝ) ^ 18 * ((k' : ℝ) ^ (10 * r) * (k' : ℝ) ^ (3 * splitTreeD r)) :=
              mul_le_mul hℓ_k'_18 (mul_le_mul_of_nonneg_right h2_60r (by positivity))
                (by positivity) (by positivity)
          _ = (k' : ℝ) ^ (18 + 10 * r + 3 * splitTreeD r) := by rw [← pow_add, ← pow_add]; ring_nf
          _ ≤ (k' : ℝ) ^ C := pow_le_pow_right₀ hk'_ge1 h_exp_le
      calc (S.card : ℝ) / (k' : ℝ) ^ C
          ≤ (S.card : ℝ) / ((ℓ : ℝ) ^ 18 * ((2 : ℝ) ^ (60 * r) * (k' : ℝ) ^ (3 * splitTreeD r))) :=
            div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) h_den
        _ = ((S.card : ℝ) / (ℓ : ℝ) ^ 18) / ((2 : ℝ) ^ (60 * r) * (k' : ℝ) ^ (3 * splitTreeD r)) := by ring
        _ ≤ w / ((2 : ℝ) ^ (60 * r) * (k' : ℝ) ^ (3 * splitTreeD r)) :=
            div_le_div_of_nonneg_right hw_ge_S (by positivity)
    · refine ⟨p_cap, hℓ_le_pcap, le_rfl, U, hU_cap.mono_ambient_width_eps hU_sub_S ?_ le_rfl⟩
      rw [show -(200 * (r : ℝ) ^ 2) = -(((200 * r ^ 2 : ℕ) : ℝ)) by push_cast; ring,
        rpow_neg_natCast (by norm_num) (200 * r ^ 2), ← inv_pow,
        show -(capExpE r : ℝ) = -(((capExpE r : ℕ) : ℝ)) by rfl,
        rpow_neg_natCast (le_of_lt hp_pos) (capExpE r), ← inv_pow]
      have h2_p : (p_cap : ℝ)⁻¹ ^ (35 * r ^ 2) ≤ (2 : ℝ)⁻¹ ^ (200 * r ^ 2) := by
        have h64 : (p_cap : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ ^ 6 := by
          have : (2 : ℝ) ^ 6 ≤ (p_cap : ℝ) := by norm_num at hp_r ⊢; exact hp_r
          rw [inv_pow]; exact inv_anti₀ (by positivity) this
        have h1 := pow_le_pow_left₀ (by positivity) h64 (35 * r ^ 2)
        rw [← pow_mul, show 6 * (35 * r ^ 2) = 210 * r ^ 2 by ring] at h1
        exact le_trans h1 (pow_le_pow_of_le_one (by positivity) (by norm_num) (by nlinarith))
      have hx_r : (p_cap : ℝ)⁻¹ ^ r ≤ x ^ r :=
        pow_le_pow_left₀ (by positivity) hp_inv_le_x r
      have hw_p : (S.card : ℝ) * (p_cap : ℝ)⁻¹ ^ 18 ≤ w := by
        calc (S.card : ℝ) * (p_cap : ℝ)⁻¹ ^ 18
            = (S.card : ℝ) / (p_cap : ℝ) ^ 18 := by rw [inv_pow]; ring
          _ ≤ (S.card : ℝ) / (ℓ : ℝ) ^ 18 :=
              div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
                (pow_le_pow_left₀ (by positivity) (Nat.cast_le.mpr hℓ_le_pcap) 18)
          _ ≤ w := hw_ge_S
      have h_exp_le : 35 * r ^ 2 + r + capExpE r + 18 ≤ C := by
        rw [hC_eq]
        have := seventy_sq_le_two_mul_capExpE r hr
        omega
      have hp_C : (p_cap : ℝ)⁻¹ ^ C ≤
          (p_cap : ℝ)⁻¹ ^ (35 * r ^ 2) * (p_cap : ℝ)⁻¹ ^ r *
          (p_cap : ℝ)⁻¹ ^ (capExpE r) * (p_cap : ℝ)⁻¹ ^ 18 := by
        rw [← pow_add, ← pow_add, ← pow_add]
        exact pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hp_ge1) h_exp_le
      calc (S.card : ℝ) / (p_cap : ℝ) ^ C
          = (S.card : ℝ) * (p_cap : ℝ)⁻¹ ^ C := by rw [inv_pow]; ring
        _ ≤ (S.card : ℝ) * ((p_cap : ℝ)⁻¹ ^ (35 * r ^ 2) * (p_cap : ℝ)⁻¹ ^ r *
              (p_cap : ℝ)⁻¹ ^ (capExpE r) * (p_cap : ℝ)⁻¹ ^ 18) :=
            mul_le_mul_of_nonneg_left hp_C (Nat.cast_nonneg _)
        _ = (p_cap : ℝ)⁻¹ ^ (35 * r ^ 2) * (p_cap : ℝ)⁻¹ ^ r * (p_cap : ℝ)⁻¹ ^ (capExpE r) *
              ((S.card : ℝ) * (p_cap : ℝ)⁻¹ ^ 18) := by ring
        _ ≤ (2 : ℝ)⁻¹ ^ (200 * r ^ 2) * x ^ r * (p_cap : ℝ)⁻¹ ^ (capExpE r) * w := by
            refine mul_le_mul ?_ hw_p (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_right (mul_le_mul h2_p hx_r (by positivity) (by positivity))
              (by positivity)
  · push_neg at hw_min
    let k' := min S.card p_cap
    have hk'_le_S : k' ≤ S.card := Nat.min_le_left _ _
    have hk'_le_p : k' ≤ p_cap := Nat.min_le_right _ _
    have hℓ_le_k' : ℓ ≤ k' := le_min hℓ_le_S hℓ_le_pcap
    obtain ⟨U, hU_pure⟩ := singleton_pure_blockade_of_card_ge F S hk'_le_S
    refine ⟨k', hℓ_le_k', hk'_le_p, U,
      (IsPureBlockadeIn.isWeaklySparseOrCoSparseBlockadeIn hU_pure (le_of_lt hx_pos)).mono_ambient_width_eps
        Finset.Subset.rfl ?_ le_rfl⟩
    have hk'_pos : (0 : ℝ) < (k' : ℝ) := Nat.cast_pos.mpr (by omega)
    have hk'_ge1 : (1 : ℝ) ≤ (k' : ℝ) := Nat.one_le_cast.mpr (by omega)
    by_cases hS_le_p : S.card ≤ p_cap
    · have hk'_eq : k' = S.card := Nat.min_eq_left hS_le_p
      rw [← hk'_eq, div_le_one (by positivity)]
      have hC_pos : 1 ≤ C := by rw [hC_eq]; omega
      simpa using pow_le_pow_right₀ hk'_ge1 hC_pos
    · push_neg at hS_le_p
      have hk'_eq : k' = p_cap := Nat.min_eq_right (le_of_lt hS_le_p)
      rw [hk'_eq, div_le_one (by positivity)]
      unfold combMinWidth at hw_min
      rw [show -(3 * (r : ℝ)) = -(((3 * r : ℕ) : ℝ)) by push_cast; ring,
        rpow_neg_natCast (le_of_lt hx_pos) (3 * r), ← inv_pow] at hw_min
      have h2_400 : (2 : ℝ) ^ (400 * r ^ 2) ≤ (p_cap : ℝ) ^ (70 * r ^ 2) := by
        have h64 : (2 : ℝ) ^ 6 ≤ (p_cap : ℝ) := by norm_num at hp_r ⊢; exact hp_r
        have h1 := pow_le_pow_left₀ (by positivity) h64 (70 * r ^ 2)
        rw [← pow_mul, show 6 * (70 * r ^ 2) = 420 * r ^ 2 by ring] at h1
        exact le_trans (pow_le_pow_right₀ (by norm_num) (by nlinarith)) h1
      have hx_3r : (x⁻¹) ^ (3 * r) ≤ (p_cap : ℝ) ^ (3 * r) :=
        pow_le_pow_left₀ (by positivity) hx_inv_le_pcap (3 * r)
      have hw_le_p : w ≤ (p_cap : ℝ) ^ (70 * r ^ 2 + 3 * r + (capExpE r + 2 * splitTreeD r)) := by
        calc w ≤ (2 : ℝ) ^ (400 * r ^ 2) * (x⁻¹) ^ (3 * r) * (p_cap : ℝ) ^ (capExpE r + 2 * splitTreeD r) :=
              le_of_lt hw_min
          _ ≤ (p_cap : ℝ) ^ (70 * r ^ 2) * (p_cap : ℝ) ^ (3 * r) * (p_cap : ℝ) ^ (capExpE r + 2 * splitTreeD r) :=
              mul_le_mul_of_nonneg_right (mul_le_mul h2_400 hx_3r (by positivity) (by positivity)) (by positivity)
          _ = (p_cap : ℝ) ^ (70 * r ^ 2 + 3 * r + (capExpE r + 2 * splitTreeD r)) := by
              rw [← pow_add, ← pow_add]
      have hS_le_ell_w : (S.card : ℝ) ≤ (p_cap : ℝ) ^ 18 * w := by
        have h1 : (S.card : ℝ) ≤ (ℓ : ℝ) ^ 18 * w := by
          have hℓ_pos : (0 : ℝ) < (ℓ : ℝ) ^ 18 := by positivity
          have := (div_le_iff₀ hℓ_pos).mp hw_ge_S
          linarith
        have h2 : (ℓ : ℝ) ^ 18 ≤ (p_cap : ℝ) ^ 18 :=
          pow_le_pow_left₀ (by positivity) (Nat.cast_le.mpr hℓ_le_pcap) 18
        exact le_trans h1 (mul_le_mul_of_nonneg_right h2 hw_nn)
      have h_exp_le : 18 + (70 * r ^ 2 + 3 * r + (capExpE r + 2 * splitTreeD r)) ≤ C := by
        rw [hC_eq]
        have := seventy_sq_le_two_mul_capExpE r hr
        omega
      calc (S.card : ℝ)
          ≤ (p_cap : ℝ) ^ 18 * w := hS_le_ell_w
        _ ≤ (p_cap : ℝ) ^ 18 * (p_cap : ℝ) ^ (70 * r ^ 2 + 3 * r + (capExpE r + 2 * splitTreeD r)) :=
            mul_le_mul_of_nonneg_left hw_le_p (by positivity)
        _ = (p_cap : ℝ) ^ (18 + (70 * r ^ 2 + 3 * r + (capExpE r + 2 * splitTreeD r))) := by
            rw [← pow_add]
        _ ≤ (p_cap : ℝ) ^ C := pow_le_pow_right₀ hp_ge1 h_exp_le

/-- **Proposition 7(2c) Pair Generalized Niceness (`pair_path_spider_isCoupledGeneralizedNice`)**:
For all $t \ge 2$ and $d \ge 2$, the two-graph family `{pathGraph t, SpiderGraph d}` is unconditionally
coupled Stage-1 generalized nice (`IsPairCoupledGeneralizedNice (pathGraph t) (SpiderGraph d)`). -/
theorem pair_path_spider_isCoupledGeneralizedNice (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) :
    IsPairCoupledGeneralizedNice (pathGraph t) (SpiderGraph d) := by
  let C_comb : ℝ := (pathCombExpC (d + 4) : ℝ)
  have hC_comb : 18 ≤ C_comb := by
    dsimp [C_comb, pathCombExpC]
    exact_mod_cast (by omega : 18 ≤ 3 * capExpE (d + 4 - 5) + 4 * splitTreeD (d + 4 - 5) + 100)
  refine pair_coupled_generalized_nice_of_path_comb_dichotomy t ht (SpiderGraph d)
    C_comb 2 1 1 hC_comb le_rfl zero_lt_one zero_lt_one ?_
  intro V _ _ G F' x y ℓ a B v _ hG₂ hx_pos hxy hy_ub hℓ_lo hℓ_hi hℓ_64 hcomb hapex
  right
  have hy0 : 0 < y := hx_pos.trans_le hxy
  have hw_ge_S := comb_width_ge_card_div_pow_18' F' hy0 hℓ_lo
  obtain ⟨k', hℓ_k', hk'_p, U, hU⟩ :=
    stage1Family_comb_dichotomy_64 spiderGraph_hasNonNeighPureGrouping hd
      hx_pos hxy hy_ub hℓ_64 hℓ_hi hG₂ hcomb hapex hw_ge_S
  have hk'_lo : (1 / 2 : ℝ) * (ℓ : ℝ) ^ (1 : ℝ) ≤ (k' : ℝ) := by
    rw [Real.rpow_one]
    have : (ℓ : ℝ) ≤ (k' : ℝ) := by exact_mod_cast hℓ_k'
    linarith
  refine ⟨k', by omega, hk'_lo, hk'_p, U, Or.inr ?_⟩
  dsimp [C_comb]; rw [Real.rpow_natCast]; exact hU

/-- **Proposition 7(2c) Pair Generalized Niceness (`pair_path_bird_isCoupledGeneralizedNice`)**:
For all $t \ge 2$ and $d \ge 2$, the two-graph family `{pathGraph t, BirdDGraph d}` is unconditionally
coupled Stage-1 generalized nice (`IsPairCoupledGeneralizedNice (pathGraph t) (BirdDGraph d)`). -/
theorem pair_path_bird_isCoupledGeneralizedNice (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) :
    IsPairCoupledGeneralizedNice (pathGraph t) (BirdDGraph d) := by
  let C_comb : ℝ := (pathCombExpC (d + 4) : ℝ)
  have hC_comb : 18 ≤ C_comb := by
    dsimp [C_comb, pathCombExpC]
    exact_mod_cast (by omega : 18 ≤ 3 * capExpE (d + 4 - 5) + 4 * splitTreeD (d + 4 - 5) + 100)
  refine pair_coupled_generalized_nice_of_path_comb_dichotomy t ht (BirdDGraph d)
    C_comb 2 1 1 hC_comb le_rfl zero_lt_one zero_lt_one ?_
  intro V _ _ G F' x y ℓ a B v _ hG₂ hx_pos hxy hy_ub hℓ_lo hℓ_hi hℓ_64 hcomb hapex
  right
  have hy0 : 0 < y := hx_pos.trans_le hxy
  have hw_ge_S := comb_width_ge_card_div_pow_18' F' hy0 hℓ_lo
  obtain ⟨k', hℓ_k', hk'_p, U, hU⟩ :=
    stage1Family_comb_dichotomy_64 birdDGraph_hasNonNeighPureGrouping hd
      hx_pos hxy hy_ub hℓ_64 hℓ_hi hG₂ hcomb hapex hw_ge_S
  have hk'_lo : (1 / 2 : ℝ) * (ℓ : ℝ) ^ (1 : ℝ) ≤ (k' : ℝ) := by
    rw [Real.rpow_one]
    have : (ℓ : ℝ) ≤ (k' : ℝ) := by exact_mod_cast hℓ_k'
    linarith
  refine ⟨k', by omega, hk'_lo, hk'_p, U, Or.inr ?_⟩
  dsimp [C_comb]; rw [Real.rpow_natCast]; exact hU


end ErdosHajnalGen
