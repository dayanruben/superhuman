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
import ErdosHajnal.SmallTreesAndInfiniteTowers
import ErdosHajnal.SpidersAndBirdsStage1Dichotomy
import ErdosHajnal.SpidersAndBirdsStage1Escape
import ErdosHajnal.SymmetricStage12Interface
import ErdosHajnal.UniversalTerminalPathAndAllPaths
import ErdosHajnal.ViralityAndClosures

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open Filter Finset SimpleGraph Real ErdosHajnalP6

namespace ErdosHajnalGen

/-- Forward vertex map from `Fin (d + 3)` onto `{w : Fin (d + 4) // w ≠ ⟨1, _⟩}` mapping
`(0, 1, 2, 3 + q)` to `(3, 2, 0, 4 + q)` (`(x_2, w_2, c, u_1, ..., u_d)`). -/
def spiderMinus1ToSubtype (d : ℕ) (_hd : 2 ≤ d) (i : Fin (d + 3)) :
    {w : Fin (d + 4) // w ≠ ⟨1, by omega⟩} :=
  if hi0 : i.1 = 0 then ⟨⟨3, by omega⟩, by intro h; have hv : (3 : ℕ) = 1 := congrArg Fin.val h; omega⟩
  else if hi1 : i.1 = 1 then ⟨⟨2, by omega⟩, by intro h; have hv : (2 : ℕ) = 1 := congrArg Fin.val h; omega⟩
  else if hi2 : i.1 = 2 then ⟨⟨0, by omega⟩, by intro h; have hv : (0 : ℕ) = 1 := congrArg Fin.val h; omega⟩
  else ⟨⟨i.1 + 1, by have := i.2; omega⟩,
    by intro h; have hv : i.1 + 1 = 1 := congrArg Fin.val h; omega⟩

lemma spiderMinus1ToSubtype_val (d : ℕ) (hd : 2 ≤ d) (i : Fin (d + 3)) :
    (spiderMinus1ToSubtype d hd i).1.1 =
      if i.1 = 0 then 3
      else if i.1 = 1 then 2
      else if i.1 = 2 then 0
      else i.1 + 1 := by
  unfold spiderMinus1ToSubtype
  split_ifs <;> rfl

lemma spiderMinus1ToSubtype_bijective (d : ℕ) (hd : 2 ≤ d) :
    Function.Bijective (spiderMinus1ToSubtype d hd) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · intro a b hab
    have hv : (spiderMinus1ToSubtype d hd a).1.1 = (spiderMinus1ToSubtype d hd b).1.1 :=
      congrArg (fun x => x.1.1) hab
    rw [spiderMinus1ToSubtype_val, spiderMinus1ToSubtype_val] at hv
    apply Fin.ext
    split_ifs at hv <;> omega
  · rw [Fintype.card_fin, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
    omega

lemma spiderGraph_adj_val_iff (d : ℕ) (x y : Fin (d + 4)) :
    (SpiderGraph d).Adj x y ↔
      ((x.1 = 0 ∧ (y.1 = 1 ∨ y.1 = 2 ∨ y.1 = 4)) ∨
       ((x.1 = 1 ∨ x.1 = 2 ∨ x.1 = 4) ∧ y.1 = 0) ∨
       (x.1 = 2 ∧ y.1 = 3) ∨ (x.1 = 3 ∧ y.1 = 2) ∨
       (4 ≤ x.1 ∧ y.1 = x.1 + 1) ∨ (4 ≤ y.1 ∧ x.1 = y.1 + 1)) := by
  by_cases hlt : x.1 < y.1
  · rw [spiderGraph_adj_of_lt hlt]
    omega
  · by_cases hgt : y.1 < x.1
    · rw [(SpiderGraph d).adj_comm, spiderGraph_adj_of_lt hgt]
      omega
    · have heq : x = y := Fin.ext (by omega)
      subst heq
      constructor
      · intro h; exact False.elim ((SpiderGraph d).loopless x h)
      · intro h; omega

noncomputable def pathIsoSpiderMinus1 (d : ℕ) (hd : 2 ≤ d) :
    pathGraph (d + 3) ≃g
      (SpiderGraph d).comap (Subtype.val : {w : Fin (d + 4) // w ≠ ⟨1, by omega⟩} → Fin (d + 4)) where
  toEquiv := Equiv.ofBijective (spiderMinus1ToSubtype d hd) (spiderMinus1ToSubtype_bijective d hd)
  map_rel_iff' := by
    intro a b
    change (SpiderGraph d).Adj (spiderMinus1ToSubtype d hd a).1 (spiderMinus1ToSubtype d hd b).1 ↔
      (pathGraph (d + 3)).Adj a b
    simp only [spiderGraph_adj_val_iff, pathGraph_adj, spiderMinus1ToSubtype_val]
    have ha := a.2
    have hb := b.2
    split_ifs <;> simp_all <;> omega

/-- Leaf-reducibility of `SpiderGraph d` ($d \ge 2$) at leaf `w₁ = ⟨1, _⟩`. -/
theorem spiderGraph_leaf_reducible (d : ℕ) (hd : 2 ≤ d) :
    (∀ w : Fin (d + 4), (SpiderGraph d).Adj ⟨1, by omega⟩ w ↔ w = ⟨0, by omega⟩) ∧
    HasErdosHajnalProp ((SpiderGraph d).comap
      (Subtype.val : {w : Fin (d + 4) // w ≠ ⟨1, by omega⟩} → Fin (d + 4))) ∧
    IsViral ((SpiderGraph d).comap
      (Subtype.val : {w : Fin (d + 4) // w ≠ ⟨1, by omega⟩} → Fin (d + 4)))ᶜ := by
  have h1 : ∀ w : Fin (d + 4), (SpiderGraph d).Adj ⟨1, by omega⟩ w ↔ w = ⟨0, by omega⟩ := by
    intro w
    have h0 : (⟨0, by omega⟩ : Fin (d + 4)).1 = 0 := rfl
    have h1v : (⟨1, by omega⟩ : Fin (d + 4)).1 = 1 := rfl
    rw [spiderGraph_adj_val_iff, Fin.ext_iff, h0, h1v]
    omega
  have h2 : HasErdosHajnalProp ((SpiderGraph d).comap
      (Subtype.val : {w : Fin (d + 4) // w ≠ ⟨1, by omega⟩} → Fin (d + 4))) :=
    hasErdosHajnalProp_of_iso' (pathIsoSpiderMinus1 d hd)
      (hasErdosHajnalProp_pathGraph_all (d + 3) (by omega))
  haveI : Nonempty {w : Fin (d + 4) // w ≠ ⟨1, by omega⟩} :=
    ⟨⟨⟨0, by omega⟩, by intro h; have hv : (0 : ℕ) = 1 := congrArg Fin.val h; omega⟩⟩
  exact ⟨h1, h2,
    (eh_iff_polyRodl_iff_isViral _).2.mp ((eh_iff_polyRodl_iff_isViral _).1.mp h2.compl)⟩

/-- Forward map from `{v : Fin (d + 2) // v ≠ 0} ⊕ Fin 2` onto `{w : Fin (d + 4) // w ≠ ⟨0, _⟩}`
mapping `inr 0 ↦ 1` ($b_1$), `inr 1 ↦ 3` ($b_3$), `inl 1 ↦ 2` ($b_2$), and `inl (2 + q) ↦ 4 + q` ($u_{q+1}$). -/
def substPathK2ToBirdMinus0 (d : ℕ) (_hd : 2 ≤ d) :
    {v : Fin (d + 2) // v ≠ 0} ⊕ Fin 2 → {w : Fin (d + 4) // w ≠ ⟨0, by omega⟩}
  | Sum.inr i =>
      if i.1 = 0 then ⟨⟨1, by omega⟩, by intro h; have hv : (1 : ℕ) = 0 := congrArg Fin.val h; omega⟩
      else ⟨⟨3, by omega⟩, by intro h; have hv : (3 : ℕ) = 0 := congrArg Fin.val h; omega⟩
  | Sum.inl v =>
      if v.1.1 = 1 then ⟨⟨2, by omega⟩, by intro h; have hv : (2 : ℕ) = 0 := congrArg Fin.val h; omega⟩
      else ⟨⟨v.1.1 + 2, by have := v.1.2; omega⟩,
        by intro h; have hv : v.1.1 + 2 = 0 := congrArg Fin.val h; omega⟩

lemma substPathK2ToBirdMinus0_inr (d : ℕ) (hd : 2 ≤ d) (i : Fin 2) :
    (substPathK2ToBirdMinus0 d hd (Sum.inr i)).1.1 = if i.1 = 0 then 1 else 3 := by
  dsimp [substPathK2ToBirdMinus0]; split_ifs <;> rfl

lemma substPathK2ToBirdMinus0_inl (d : ℕ) (hd : 2 ≤ d) (v : {v : Fin (d + 2) // v ≠ 0}) :
    (substPathK2ToBirdMinus0 d hd (Sum.inl v)).1.1 = if v.1.1 = 1 then 2 else v.1.1 + 2 := by
  dsimp [substPathK2ToBirdMinus0]; split_ifs <;> rfl

lemma substPathK2ToBirdMinus0_bijective (d : ℕ) (hd : 2 ≤ d) :
    Function.Bijective (substPathK2ToBirdMinus0 d hd) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have hv : (substPathK2ToBirdMinus0 d hd x).1.1 = (substPathK2ToBirdMinus0 d hd y).1.1 :=
      congrArg (fun z => z.1.1) hxy
    cases x with
    | inr i =>
      have hi := i.2
      cases y with
      | inr j =>
        have hj := j.2
        rw [substPathK2ToBirdMinus0_inr, substPathK2ToBirdMinus0_inr] at hv
        congr 1; apply Fin.ext
        split_ifs at hv <;> omega
      | inl v =>
        have hv0 : v.1.1 ≠ 0 := fun h => v.2 (Fin.ext h)
        rw [substPathK2ToBirdMinus0_inr, substPathK2ToBirdMinus0_inl] at hv
        split_ifs at hv <;> omega
    | inl u =>
      have hu0 : u.1.1 ≠ 0 := fun h => u.2 (Fin.ext h)
      cases y with
      | inr j =>
        rw [substPathK2ToBirdMinus0_inl, substPathK2ToBirdMinus0_inr] at hv
        split_ifs at hv <;> omega
      | inl v =>
        have hv0 : v.1.1 ≠ 0 := fun h => v.2 (Fin.ext h)
        rw [substPathK2ToBirdMinus0_inl, substPathK2ToBirdMinus0_inl] at hv
        congr 1; apply Subtype.ext; apply Fin.ext
        split_ifs at hv <;> omega
  · simp only [Fintype.card_sum, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
    omega

lemma birdDGraph_adj_val_iff (d : ℕ) (x y : Fin (d + 4)) :
    (BirdDGraph d).Adj x y ↔
      ((x.1 = 0 ∧ y.1 = 1) ∨ (x.1 = 1 ∧ y.1 = 0) ∨
       (x.1 = 1 ∧ (y.1 = 2 ∨ y.1 = 3)) ∨ ((x.1 = 2 ∨ x.1 = 3) ∧ y.1 = 1) ∨
       (x.1 = 2 ∧ (y.1 = 3 ∨ y.1 = 4)) ∨ ((x.1 = 3 ∨ x.1 = 4) ∧ y.1 = 2) ∨
       (4 ≤ x.1 ∧ y.1 = x.1 + 1) ∨ (4 ≤ y.1 ∧ x.1 = y.1 + 1)) := by
  by_cases hlt : x.1 < y.1
  · rw [birdDGraph_adj_of_lt hlt]
    omega
  · by_cases hgt : y.1 < x.1
    · rw [(BirdDGraph d).adj_comm, birdDGraph_adj_of_lt hgt]
      omega
    · have heq : x = y := Fin.ext (by omega)
      subst heq
      constructor
      · intro h; exact False.elim ((BirdDGraph d).loopless x h)
      · intro h; omega

noncomputable def substPathK2IsoBirdMinus0 (d : ℕ) (hd : 2 ≤ d) :
    substGraph (pathGraph (d + 2)) 0 (⊤ : SimpleGraph (Fin 2)) ≃g
      (BirdDGraph d).comap (Subtype.val : {w : Fin (d + 4) // w ≠ ⟨0, by omega⟩} → Fin (d + 4)) where
  toEquiv := Equiv.ofBijective (substPathK2ToBirdMinus0 d hd) (substPathK2ToBirdMinus0_bijective d hd)
  map_rel_iff' := by
    intro x y
    change (BirdDGraph d).Adj (substPathK2ToBirdMinus0 d hd x).1 (substPathK2ToBirdMinus0 d hd y).1 ↔
      (substGraph (pathGraph (d + 2)) 0 (⊤ : SimpleGraph (Fin 2))).Adj x y
    rw [birdDGraph_adj_val_iff]
    cases x with
    | inr i =>
      cases y with
      | inr j =>
        have h_rhs : (substGraph (pathGraph (d + 2)) 0 (⊤ : SimpleGraph (Fin 2))).Adj
            (Sum.inr i) (Sum.inr j) ↔ i ≠ j := Iff.rfl
        simp only [substPathK2ToBirdMinus0_inr, h_rhs]
        fin_cases i <;> fin_cases j <;> decide
      | inl v =>
        have hv0 : v.1.1 ≠ 0 := fun h => v.2 (Fin.ext h)
        have hv_lt := v.1.2
        have h_rhs1 : (substGraph (pathGraph (d + 2)) 0 (⊤ : SimpleGraph (Fin 2))).Adj
            (Sum.inr i) (Sum.inl v) ↔ (pathGraph (d + 2)).Adj 0 v.1 := Iff.rfl
        have h0val : (0 : Fin (d + 2)).1 = 0 := rfl
        simp only [substPathK2ToBirdMinus0_inr, substPathK2ToBirdMinus0_inl, h_rhs1,
          pathGraph_adj, h0val]
        split_ifs <;> simp_all <;> omega
    | inl u =>
      have hu0 : u.1.1 ≠ 0 := fun h => u.2 (Fin.ext h)
      have hu_lt := u.1.2
      cases y with
      | inr j =>
        have h_rhs1 : (substGraph (pathGraph (d + 2)) 0 (⊤ : SimpleGraph (Fin 2))).Adj
            (Sum.inl u) (Sum.inr j) ↔ (pathGraph (d + 2)).Adj u.1 0 := Iff.rfl
        have h0val : (0 : Fin (d + 2)).1 = 0 := rfl
        simp only [substPathK2ToBirdMinus0_inl, substPathK2ToBirdMinus0_inr, h_rhs1,
          pathGraph_adj, h0val]
        split_ifs <;> simp_all <;> omega
      | inl v =>
        have hv0 : v.1.1 ≠ 0 := fun h => v.2 (Fin.ext h)
        have hv_lt := v.1.2
        have h_rhs1 : (substGraph (pathGraph (d + 2)) 0 (⊤ : SimpleGraph (Fin 2))).Adj
            (Sum.inl u) (Sum.inl v) ↔ (pathGraph (d + 2)).Adj u.1 v.1 := Iff.rfl
        simp only [substPathK2ToBirdMinus0_inl, h_rhs1, pathGraph_adj]
        split_ifs <;> simp_all <;> omega

/-- Leaf-reducibility of `BirdDGraph d` ($d \ge 2$) at leaf `b₀ = ⟨0, _⟩`. -/
theorem birdDGraph_leaf_reducible (d : ℕ) (hd : 2 ≤ d) :
    (∀ w : Fin (d + 4), (BirdDGraph d).Adj ⟨0, by omega⟩ w ↔ w = ⟨1, by omega⟩) ∧
    HasErdosHajnalProp ((BirdDGraph d).comap
      (Subtype.val : {w : Fin (d + 4) // w ≠ ⟨0, by omega⟩} → Fin (d + 4))) ∧
    IsViral ((BirdDGraph d).comap
      (Subtype.val : {w : Fin (d + 4) // w ≠ ⟨0, by omega⟩} → Fin (d + 4)))ᶜ := by
  have h1 : ∀ w : Fin (d + 4), (BirdDGraph d).Adj ⟨0, by omega⟩ w ↔ w = ⟨1, by omega⟩ := by
    intro w
    have h0 : (⟨0, by omega⟩ : Fin (d + 4)).1 = 0 := rfl
    have h1v : (⟨1, by omega⟩ : Fin (d + 4)).1 = 1 := rfl
    rw [birdDGraph_adj_val_iff, Fin.ext_iff, h0, h1v]
    omega
  have h_top2 : HasErdosHajnalProp (⊤ : SimpleGraph (Fin 2)) :=
    (compl_bot : (⊥ : SimpleGraph (Fin 2))ᶜ = ⊤) ▸ (hasErdosHajnalProp_bot_fin_all 2).compl
  have h_sub : HasErdosHajnalProp (substGraph (pathGraph (d + 2)) 0 (⊤ : SimpleGraph (Fin 2))) :=
    hasErdosHajnalProp_substGraph_tp (pathGraph (d + 2)) 0 (⊤ : SimpleGraph (Fin 2))
      (hasErdosHajnalProp_pathGraph_all (d + 2) (by omega)) h_top2
  have h2 : HasErdosHajnalProp ((BirdDGraph d).comap
      (Subtype.val : {w : Fin (d + 4) // w ≠ ⟨0, by omega⟩} → Fin (d + 4))) :=
    hasErdosHajnalProp_of_iso' (substPathK2IsoBirdMinus0 d hd) h_sub
  haveI : Nonempty {w : Fin (d + 4) // w ≠ ⟨0, by omega⟩} :=
    ⟨⟨⟨1, by omega⟩, by intro h; have hv : (1 : ℕ) = 0 := congrArg Fin.val h; omega⟩⟩
  exact ⟨h1, h2,
    (eh_iff_polyRodl_iff_isViral _).2.mp ((eh_iff_polyRodl_iff_isViral _).1.mp h2.compl)⟩

/-- Explicit constants `SatisfiesPairCoupledGenNiceAt (SpiderGraph d) (SpiderGraph d)` ($d \ge 2$). -/
theorem exists_satisfiesPairCoupledGenNiceAt_spiderGraph (d : ℕ) (hd : 2 ≤ d) :
    ∃ (c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ : ℝ),
      4 ≤ c₂ ∧ 1 ≤ c₆ ∧ 1 ≤ c₇ ∧ c₇ ≤ 3 * c₂ ∧
      SatisfiesPairCoupledGenNiceAt (SpiderGraph d) (SpiderGraph d)
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ := by
  obtain ⟨hleaf, _, hviral⟩ := spiderGraph_leaf_reducible d hd
  obtain ⟨d', hd'_pos, hv_prop⟩ := hviral
  have hh₁ : 3 ≤ Fintype.card (Fin (d + 4)) := by rw [Fintype.card_fin]; omega
  let a_leaf : ℝ := 4 * d' * (Fintype.card (Fin (d + 4)) : ℝ) + 6
  let b_leaf : ℝ := 2 * (Fintype.card (Fin (d + 4)) : ℝ)
  have ha_leaf : 6 ≤ a_leaf := by
    dsimp [a_leaf]
    have : 0 ≤ 4 * d' * (Fintype.card (Fin (d + 4)) : ℝ) := by positivity
    linarith
  have hb_leaf : 6 ≤ b_leaf := by
    dsimp [b_leaf]
    have : (3 : ℝ) ≤ (Fintype.card (Fin (d + 4)) : ℝ) := by exact_mod_cast hh₁
    linarith
  let C_comb : ℝ := (pathCombExpC (d + 4) : ℝ)
  have hC_comb : 18 ≤ C_comb := by
    dsimp [C_comb, pathCombExpC]
    exact_mod_cast (by omega : 18 ≤ 3 * capExpE (d + 4 - 5) + 4 * splitTreeD (d + 4 - 5) + 100)
  have hGN := pair_coupled_generalized_nice_of_comb_dichotomy_explicit
    (SpiderGraph d) (SpiderGraph d) (by omega)
    a_leaf b_leaf C_comb 2 1 1 ha_leaf hb_leaf hC_comb le_rfl zero_lt_one zero_lt_one
    (fun V _ _ G F' y hG₁ hG₂ hy0 hy_le hy_F' h_cosparse => by
      have hy_half : y < 1 / 2 := by
        have h1 : (2 : ℝ) ^ (-4 * b_leaf) ≤ (2 : ℝ) ^ (-24 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        exact hy_le.trans_lt (h1.trans_lt (by norm_num))
      have hy_le1 : y ≤ 1 := by linarith
      have hy1_F' : 1 ≤ y * (F'.card : ℝ) := by
        have h1 : y ^ (a_leaf + 2) ≤ y ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hy0 hy_le1 (by linarith)
        rw [Real.rpow_one] at h1
        exact hy_F'.trans (mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _))
      have hF'_ne : F'.Nonempty := by
        rw [← Finset.card_pos]; exact_mod_cast (by nlinarith : (0 : ℝ) < (F'.card : ℝ))
      have hcosparse_y : IsEpsSparseOn Gᶜ F' y := h_cosparse.mono (by nlinarith [sq_nonneg y])
      rcases leaf_reducible_cosparse_trigger_or_restricted (SpiderGraph d) (SpiderGraph d)
          ⟨1, by omega⟩ ⟨0, by omega⟩ (Fin.ext_iff.not.mpr (by simp)) hleaf hh₁ hd'_pos
          (fun U_t _ _ F_G ε hε0 hε_half hc1 _ => hv_prop U_t F_G ε hε0 hε_half hc1)
          G hG₁ hG₂ F' hF'_ne y hy0 hy_half hy1_F' hcosparse_y with
        ⟨U, hUF', hU_rest, hU_card⟩ | ⟨X, hXF', Y, hYF', hdisj, hX_card, hY_card, hcomp⟩
      · left
        refine ⟨U, hUF', hU_rest, ?_⟩
        have hrpow : y ^ a_leaf ≤ y ^ (4 * d' + 1) :=
          Real.rpow_le_rpow_of_exponent_ge hy0 hy_le1 (by dsimp [a_leaf]; nlinarith [show (3 : ℝ) ≤ (Fintype.card (Fin (d + 4)) : ℝ) by exact_mod_cast hh₁])
        exact (mul_le_mul_of_nonneg_right hrpow (Nat.cast_nonneg _)).trans hU_card
      · right
        refine ⟨X, hXF', Y, hYF', hdisj, ?_, ?_, hcomp⟩
        · have hW_sub : ((Fintype.card (Fin (d + 4)) - 1 : ℕ) : ℝ) ≤ (Fintype.card (Fin (d + 4)) : ℝ) := by
            exact_mod_cast Nat.sub_le (Fintype.card (Fin (d + 4))) 1
          have hrpow : y ^ a_leaf ≤ y ^ (4 * d' * ((Fintype.card (Fin (d + 4)) - 1 : ℕ) : ℝ) + 1) :=
            Real.rpow_le_rpow_of_exponent_ge hy0 hy_le1 (by dsimp [a_leaf]; nlinarith)
          exact (mul_le_mul_of_nonneg_right hrpow (Nat.cast_nonneg _)).trans hX_card.le
        · have h1 : (1 - b_leaf * y) * (F'.card : ℝ) ≤
              (1 - (Fintype.card (Fin (d + 4)) : ℝ) * y) * (F'.card : ℝ) :=
            mul_le_mul_of_nonneg_right (by dsimp [b_leaf]; nlinarith) (Nat.cast_nonneg _)
          exact h1.trans hY_card)
    (fun V _ _ G F' x y ℓ a B v hG₁ _ hx_pos hxy hy_ub hℓ_lo hℓ_hi hℓ_64 hcomb hapex => by
      right
      have hy0 : 0 < y := hx_pos.trans_le hxy
      have hw_ge_S := comb_width_ge_card_div_pow_18' F' hy0 hℓ_lo
      obtain ⟨k', hℓ_k', hk'_p, U, hU⟩ :=
        stage1Family_comb_dichotomy_64 spiderGraph_hasNonNeighPureGrouping hd
          hx_pos hxy hy_ub hℓ_64 hℓ_hi hG₁ hcomb hapex hw_ge_S
      have hk'_lo : (1 / 2 : ℝ) * (ℓ : ℝ) ^ (1 : ℝ) ≤ (k' : ℝ) := by
        rw [Real.rpow_one]
        have : (ℓ : ℝ) ≤ (k' : ℝ) := by exact_mod_cast hℓ_k'
        linarith
      refine ⟨k', by omega, hk'_lo, hk'_p, U, Or.inr ?_⟩
      dsimp [C_comb]; rw [Real.rpow_natCast]; exact hU)
  dsimp only at hGN
  set δ := symmRodlDeltaGen (Fintype.card (Fin (d + 4))) (lambda0Param (2 * b_leaf))
  set d_gn := symmGenNiceD a_leaf b_leaf C_comb 1 δ
  have hd120 : 120 ≤ d_gn := one_hundred_twenty_le_symmGenNiceD a_leaf b_leaf C_comb 1 δ
  exact ⟨_, d_gn, _, _, _, 2, 6, _, _, by linarith, by norm_num, by norm_num, by linarith, hGN⟩

/-- Explicit constants `SatisfiesPairCoupledGenNiceAt (BirdDGraph d) (BirdDGraph d)` ($d \ge 2$). -/
theorem exists_satisfiesPairCoupledGenNiceAt_birdDGraph (d : ℕ) (hd : 2 ≤ d) :
    ∃ (c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ : ℝ),
      4 ≤ c₂ ∧ 1 ≤ c₆ ∧ 1 ≤ c₇ ∧ c₇ ≤ 3 * c₂ ∧
      SatisfiesPairCoupledGenNiceAt (BirdDGraph d) (BirdDGraph d)
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ := by
  obtain ⟨hleaf, _, hviral⟩ := birdDGraph_leaf_reducible d hd
  obtain ⟨d', hd'_pos, hv_prop⟩ := hviral
  have hh₁ : 3 ≤ Fintype.card (Fin (d + 4)) := by rw [Fintype.card_fin]; omega
  let a_leaf : ℝ := 4 * d' * (Fintype.card (Fin (d + 4)) : ℝ) + 6
  let b_leaf : ℝ := 2 * (Fintype.card (Fin (d + 4)) : ℝ)
  have ha_leaf : 6 ≤ a_leaf := by
    dsimp [a_leaf]
    have : 0 ≤ 4 * d' * (Fintype.card (Fin (d + 4)) : ℝ) := by positivity
    linarith
  have hb_leaf : 6 ≤ b_leaf := by
    dsimp [b_leaf]
    have : (3 : ℝ) ≤ (Fintype.card (Fin (d + 4)) : ℝ) := by exact_mod_cast hh₁
    linarith
  let C_comb : ℝ := (pathCombExpC (d + 4) : ℝ)
  have hC_comb : 18 ≤ C_comb := by
    dsimp [C_comb, pathCombExpC]
    exact_mod_cast (by omega : 18 ≤ 3 * capExpE (d + 4 - 5) + 4 * splitTreeD (d + 4 - 5) + 100)
  have hGN := pair_coupled_generalized_nice_of_comb_dichotomy_explicit
    (BirdDGraph d) (BirdDGraph d) (by omega)
    a_leaf b_leaf C_comb 2 1 1 ha_leaf hb_leaf hC_comb le_rfl zero_lt_one zero_lt_one
    (fun V _ _ G F' y hG₁ hG₂ hy0 hy_le hy_F' h_cosparse => by
      have hy_half : y < 1 / 2 := by
        have h1 : (2 : ℝ) ^ (-4 * b_leaf) ≤ (2 : ℝ) ^ (-24 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        exact hy_le.trans_lt (h1.trans_lt (by norm_num))
      have hy_le1 : y ≤ 1 := by linarith
      have hy1_F' : 1 ≤ y * (F'.card : ℝ) := by
        have h1 : y ^ (a_leaf + 2) ≤ y ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hy0 hy_le1 (by linarith)
        rw [Real.rpow_one] at h1
        exact hy_F'.trans (mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _))
      have hF'_ne : F'.Nonempty := by
        rw [← Finset.card_pos]; exact_mod_cast (by nlinarith : (0 : ℝ) < (F'.card : ℝ))
      have hcosparse_y : IsEpsSparseOn Gᶜ F' y := h_cosparse.mono (by nlinarith [sq_nonneg y])
      rcases leaf_reducible_cosparse_trigger_or_restricted (BirdDGraph d) (BirdDGraph d)
          ⟨0, by omega⟩ ⟨1, by omega⟩ (Fin.ext_iff.not.mpr (by simp)) hleaf hh₁ hd'_pos
          (fun U_t _ _ F_G ε hε0 hε_half hc1 _ => hv_prop U_t F_G ε hε0 hε_half hc1)
          G hG₁ hG₂ F' hF'_ne y hy0 hy_half hy1_F' hcosparse_y with
        ⟨U, hUF', hU_rest, hU_card⟩ | ⟨X, hXF', Y, hYF', hdisj, hX_card, hY_card, hcomp⟩
      · left
        refine ⟨U, hUF', hU_rest, ?_⟩
        have hrpow : y ^ a_leaf ≤ y ^ (4 * d' + 1) :=
          Real.rpow_le_rpow_of_exponent_ge hy0 hy_le1 (by dsimp [a_leaf]; nlinarith [show (3 : ℝ) ≤ (Fintype.card (Fin (d + 4)) : ℝ) by exact_mod_cast hh₁])
        exact (mul_le_mul_of_nonneg_right hrpow (Nat.cast_nonneg _)).trans hU_card
      · right
        refine ⟨X, hXF', Y, hYF', hdisj, ?_, ?_, hcomp⟩
        · have hW_sub : ((Fintype.card (Fin (d + 4)) - 1 : ℕ) : ℝ) ≤ (Fintype.card (Fin (d + 4)) : ℝ) := by
            exact_mod_cast Nat.sub_le (Fintype.card (Fin (d + 4))) 1
          have hrpow : y ^ a_leaf ≤ y ^ (4 * d' * ((Fintype.card (Fin (d + 4)) - 1 : ℕ) : ℝ) + 1) :=
            Real.rpow_le_rpow_of_exponent_ge hy0 hy_le1 (by dsimp [a_leaf]; nlinarith)
          exact (mul_le_mul_of_nonneg_right hrpow (Nat.cast_nonneg _)).trans hX_card.le
        · have h1 : (1 - b_leaf * y) * (F'.card : ℝ) ≤
              (1 - (Fintype.card (Fin (d + 4)) : ℝ) * y) * (F'.card : ℝ) :=
            mul_le_mul_of_nonneg_right (by dsimp [b_leaf]; nlinarith) (Nat.cast_nonneg _)
          exact h1.trans hY_card)
    (fun V _ _ G F' x y ℓ a B v hG₁ _ hx_pos hxy hy_ub hℓ_lo hℓ_hi hℓ_64 hcomb hapex => by
      right
      have hy0 : 0 < y := hx_pos.trans_le hxy
      have hw_ge_S := comb_width_ge_card_div_pow_18' F' hy0 hℓ_lo
      obtain ⟨k', hℓ_k', hk'_p, U, hU⟩ :=
        stage1Family_comb_dichotomy_64 birdDGraph_hasNonNeighPureGrouping hd
          hx_pos hxy hy_ub hℓ_64 hℓ_hi hG₁ hcomb hapex hw_ge_S
      have hk'_lo : (1 / 2 : ℝ) * (ℓ : ℝ) ^ (1 : ℝ) ≤ (k' : ℝ) := by
        rw [Real.rpow_one]
        have : (ℓ : ℝ) ≤ (k' : ℝ) := by exact_mod_cast hℓ_k'
        linarith
      refine ⟨k', by omega, hk'_lo, hk'_p, U, Or.inr ?_⟩
      dsimp [C_comb]; rw [Real.rpow_natCast]; exact hU)
  dsimp only at hGN
  set δ := symmRodlDeltaGen (Fintype.card (Fin (d + 4))) (lambda0Param (2 * b_leaf))
  set d_gn := symmGenNiceD a_leaf b_leaf C_comb 1 δ
  have hd120 : 120 ≤ d_gn := one_hundred_twenty_le_symmGenNiceD a_leaf b_leaf C_comb 1 δ
  exact ⟨_, d_gn, _, _, _, 2, 6, _, _, by linarith, by norm_num, by norm_num, by linarith, hGN⟩

/-- **Proposition 7(2c) & Theorem 9 (`spiderGraph_isCoupledGeneralizedNice`)**. -/
theorem spiderGraph_isCoupledGeneralizedNice :
    ∀ d : ℕ, 2 ≤ d → IsCoupledGeneralizedNice (SpiderGraph d) ∧ IsCoupledGeneralizedNice (SpiderGraph d)ᶜ := by
  intro d hd
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hGN⟩ :=
    exists_satisfiesPairCoupledGenNiceAt_spiderGraph d hd
  have h1 : IsCoupledGeneralizedNice (SpiderGraph d) :=
    isCoupledGeneralizedNice_of_pair hGN.to_isPairCoupledGeneralizedNice
  exact ⟨h1, isCoupledGeneralizedNice_compl h1⟩

/-- Any graph `H` on a non-empty finite vertex type satisfying `HasErdosHajnalProp H` satisfies
`IsCoupledGeneralizedNice H` via `HasPolyRodlProp Hᶜ` in `(GN4)`. -/
theorem isCoupledGeneralizedNice_of_hasErdosHajnalProp {W : Type} [Fintype W] [DecidableEq W]
    [Nonempty W] (H : SimpleGraph W) (h_eh : HasErdosHajnalProp H) :
    IsCoupledGeneralizedNice H := by
  obtain ⟨d', hd'_pos, hrodl⟩ := (eh_iff_polyRodl_iff_isViral Hᶜ).1.mp h_eh.compl
  refine ⟨1, 1, 1, 1, 1, 1, 1, d', 1,
    zero_lt_one, zero_lt_one, zero_lt_one, zero_lt_one, zero_lt_one,
    zero_lt_one, zero_lt_one, hd'_pos, zero_lt_one, ?_⟩
  intro V _ _ G ε x_sp hε0 hε_half _ _ hG
  right; right; right
  obtain ⟨S, hS_rest, hS_card⟩ := hrodl V G ε hε0 hε_half hG
  refine ⟨S, hS_rest.mono ?_, hS_card⟩
  rw [Real.rpow_one]
  linarith

/-- **Proposition 7(2c) & Theorem 9 (`birdDGraph_isCoupledGeneralizedNice`)**. -/
theorem birdDGraph_isCoupledGeneralizedNice :
    ∀ d : ℕ, 1 ≤ d → IsCoupledGeneralizedNice (BirdDGraph d) ∧ IsCoupledGeneralizedNice (BirdDGraph d)ᶜ := by
  intro d hd
  by_cases hd1 : d = 1
  · subst hd1
    have h1 : IsCoupledGeneralizedNice BullGraph :=
      isCoupledGeneralizedNice_of_hasErdosHajnalProp BullGraph hasErdosHajnalProp_bullGraph
    exact ⟨h1, isCoupledGeneralizedNice_compl h1⟩
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hGN⟩ :=
      exists_satisfiesPairCoupledGenNiceAt_birdDGraph d (by omega)
    have h1 : IsCoupledGeneralizedNice (BirdDGraph d) :=
      isCoupledGeneralizedNice_of_pair hGN.to_isPairCoupledGeneralizedNice
    exact ⟨h1, isCoupledGeneralizedNice_compl h1⟩

theorem spiderGraph_isPrime (d : ℕ) (hd : 2 ≤ d) : IsPrimeGraph (SpiderGraph d) :=
  (spiderGraph_genPrimeTower_base_props d hd).1

theorem spiderGraph_not_isSplit (d : ℕ) (hd : 2 ≤ d) : ¬IsSplitGraph (SpiderGraph d) :=
  (spiderGraph_genPrimeTower_base_props d hd).2.2.2.2.1

theorem spiderGraph_maxDeg_le_card_sub_three (d : ℕ) (hd : 2 ≤ d) (u : Fin (d + 4)) :
    (neighborFinsetIn (SpiderGraph d) u Finset.univ).card ≤ (d + 4) - 3 := by
  simpa [Fintype.card_fin] using (spiderGraph_genPrimeTower_base_props d hd).2.2.1 u

theorem spiderGraph_2_not_inHClosure9 : ¬InHClosure 9 (SpiderGraph 2) :=
  spiderGraph2_strict_containment.2

theorem spiderGraph_6_not_inHClosureBNew : ¬InHClosureBNew (SpiderGraph 6) :=
  spiderGraph6_strict_containment.2

theorem birdDGraph_iso_iff (d₁ d₂ : ℕ) :
    Nonempty (BirdDGraph d₁ ≃g BirdDGraph d₂) ↔ d₁ = d₂ := by
  constructor
  · rintro ⟨iso⟩
    have h := Fintype.card_congr iso.toEquiv
    simp only [Fintype.card_fin] at h
    omega
  · rintro rfl
    exact ⟨SimpleGraph.Iso.refl⟩

theorem birdDGraph_isPrime (d : ℕ) (hd : 2 ≤ d) : IsPrimeGraph (BirdDGraph d) :=
  (birdDGraph_genPrimeTower_base_props d hd).1

theorem birdDGraph_not_isSplit (d : ℕ) (hd : 2 ≤ d) : ¬IsSplitGraph (BirdDGraph d) :=
  (birdDGraph_genPrimeTower_base_props d hd).2.2.2.2.1

theorem birdDGraph_maxDeg_le_card_sub_three (d : ℕ) (hd : 2 ≤ d) (u : Fin (d + 4)) :
    (neighborFinsetIn (BirdDGraph d) u Finset.univ).card ≤ (d + 4) - 3 := by
  simpa [Fintype.card_fin] using (birdDGraph_genPrimeTower_base_props d hd).2.2.1 u

end ErdosHajnalGen
