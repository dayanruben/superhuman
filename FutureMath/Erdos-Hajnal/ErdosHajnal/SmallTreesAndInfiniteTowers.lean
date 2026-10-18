/-
Copyright 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosHajnal.AllPathsDefs
import ErdosHajnal.BasicLemmas
import ErdosHajnal.BirdBroomsForestsAndTowers
import ErdosHajnal.Defs
import ErdosHajnal.GenDefs
import ErdosHajnal.P6Baseline
import ErdosHajnal.P9BaselineProof
import ErdosHajnal.ViralityAndClosures

/-!
# Classification of Small Trees/Forests, Strict Viral Closure Containments, and Generalized Prime Non-Split Extension Towers (`Theorem 8` & `Proposition 6(3)` of `main.tex`)

This module proves:
1. **Closure Monotonicity, Strict Containments, and Master Pair-Virality Closures**
   (`Section 1`: $\mathcal{H}(\mathcal{B}_9^*) \subsetneq \mathcal{H}(\mathcal{B}_{\mathrm{new}}^*) \subsetneq \mathcal{H}(\mathcal{B}_\infty^*)$,
   plus `inJClosureBNew_pair_viral_of_base`, `inHClosureBNew_eh_of_base`,
   `inJClosureBInfty_pair_viral_of_base`, `inHClosureBInfty_eh_of_base`).
2. **Exhaustive Classification of All Trees of Order $\le 6$, Forests of Component Order $\le 6$,
   and $10/11$ Trees on $7$ Vertices** (`Section 2`, Theorem 8(1) of `main.tex`).
3. **Generalized Canonical Alternating Prime Non-Split Extension Towers**
   (`Section 3`, Proposition 6(3) of `main.tex` for general base $(G_0, x_0)$ and base families
   $\{(P_k, v_k)\}_{k \ge 6}$, $\{(S_{1,2,d}, u_d)\}_{d \ge 2}$, and $\{(\mathrm{Bird}_d, u_d)\}_{d \ge 2}$).
-/

open Finset SimpleGraph ErdosHajnalP6

namespace ErdosHajnalGen

/-!
### Section 1: Closure Monotonicity and Master Pair-Virality Theorems
-/

/-- Generator inclusion $\mathcal{B}_9^* \subseteq \mathcal{B}_{\mathrm{new}}^*$. -/
theorem inBStar9_to_inBNew {W : Type} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} (h : InBStar 9 H) : InBNew H :=
  Or.inl h

/-- Monotonicity $\mathcal{J}(\mathcal{B}_9^*) \subseteq \mathcal{J}(\mathcal{B}_{\mathrm{new}}^*)$. -/
theorem inJClosure9_to_inJClosureBNew {W : Type} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} (h : InJClosure 9 H) : InJClosureBNew H := by
  induction h with
  | base H hB => exact InJClosureBNew.base H (inBStar9_to_inBNew hB)
  | iso H₁ H₂ _ he ih => exact InJClosureBNew.iso H₁ H₂ ih he
  | subst H₁ v₀ H₂ _ _ ih₁ ih₂ => exact InJClosureBNew.subst H₁ v₀ H₂ ih₁ ih₂
  | add_leaf H v₀ hdeg _ ih => exact InJClosureBNew.add_leaf H v₀ hdeg ih

/-- Symmetric closure monotonicity $\mathcal{H}(\mathcal{B}_9^*) \subseteq \mathcal{H}(\mathcal{B}_{\mathrm{new}}^*)$. -/
theorem inHClosure9_to_inHClosureBNew {W : Type} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} (h : InHClosure 9 H) : InHClosureBNew H :=
  ⟨inJClosure9_to_inJClosureBNew h.1, inJClosure9_to_inJClosureBNew h.2⟩

/-- Generator inclusion $\mathcal{B}_{\mathrm{new}}^* \subseteq \mathcal{B}_\infty^*$. -/
theorem inBNew_to_inBInfty {W : Type} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} (h : InBNew H) : InBInfty H :=
  Or.inl h

/-- Monotonicity $\mathcal{J}(\mathcal{B}_{\mathrm{new}}^*) \subseteq \mathcal{J}(\mathcal{B}_\infty^*)$. -/
theorem inJClosureBNew_to_inJClosureBInfty {W : Type} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} (h : InJClosureBNew H) : InJClosureBInfty H := by
  induction h with
  | base H hB => exact InJClosureBInfty.base H (inBNew_to_inBInfty hB)
  | iso H₁ H₂ _ he ih => exact InJClosureBInfty.iso H₁ H₂ ih he
  | subst H₁ v₀ H₂ _ _ ih₁ ih₂ => exact InJClosureBInfty.subst H₁ v₀ H₂ ih₁ ih₂
  | add_leaf H v₀ hdeg _ ih => exact InJClosureBInfty.add_leaf H v₀ hdeg ih

/-- Symmetric closure monotonicity $\mathcal{H}(\mathcal{B}_{\mathrm{new}}^*) \subseteq \mathcal{H}(\mathcal{B}_\infty^*)$. -/
theorem inHClosureBNew_to_inHClosureBInfty {W : Type} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} (h : InHClosureBNew H) : InHClosureBInfty H :=
  ⟨inJClosureBNew_to_inJClosureBInfty h.1, inJClosureBNew_to_inJClosureBInfty h.2⟩

/-- Every graph in `InBNew` has positive vertex cardinality. -/
theorem inBNew_card_pos {W : Type} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} (h : InBNew H) : 1 ≤ Fintype.card W := by
  rcases h with h9 | he | ⟨d, _, _, he | he⟩ | ⟨d, _, _, he | he⟩
  · exact inJClosure_card_pos (InJClosure.base H h9)
  · obtain ⟨e⟩ := he; rw [Fintype.card_congr e.toEquiv, Fintype.card_fin]; omega
  · obtain ⟨e⟩ := he; rw [Fintype.card_congr e.toEquiv, Fintype.card_fin]; omega
  · obtain ⟨e⟩ := he; rw [Fintype.card_congr e.toEquiv, Fintype.card_fin]; omega
  · obtain ⟨e⟩ := he; rw [Fintype.card_congr e.toEquiv, Fintype.card_fin]; omega
  · obtain ⟨e⟩ := he; rw [Fintype.card_congr e.toEquiv, Fintype.card_fin]; omega

/-- Every graph in `InJClosureBNew` has positive vertex cardinality. -/
theorem inJClosureBNew_card_pos {W : Type} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} (h : InJClosureBNew H) : 1 ≤ Fintype.card W := by
  induction h with
  | base H hB => exact inBNew_card_pos hB
  | iso _ _ _ he ih =>
      obtain ⟨e⟩ := he
      rw [← Fintype.card_congr e.toEquiv]
      exact ih
  | @subst W₁ W₂ _ _ _ _ H₁ v₀ H₂ _ _ ih₁ ih₂ =>
      haveI : Nonempty W₁ := ⟨v₀⟩
      haveI : Nonempty W₂ := Fintype.card_pos_iff.mp ih₂
      haveI : Nonempty ({v : W₁ // v ≠ v₀} ⊕ W₂) :=
        Nonempty.map Sum.inr inferInstance
      exact Fintype.card_pos
  | add_leaf _ v₀ _ _ _ =>
      haveI : Nonempty _ := ⟨v₀⟩
      exact Fintype.card_pos

/-- Every graph in `InBInfty` has positive vertex cardinality. -/
theorem inBInfty_card_pos {W : Type} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} (h : InBInfty H) : 1 ≤ Fintype.card W := by
  rcases h with hNew | ⟨k, hk, he | he⟩ | ⟨d, hd, he | he⟩ | ⟨d, hd, he | he⟩ |
      ⟨d, hd, he | he⟩
  · exact inBNew_card_pos hNew
  · obtain ⟨e⟩ := he; rw [Fintype.card_congr e.toEquiv, Fintype.card_fin]; omega
  · obtain ⟨e⟩ := he; rw [Fintype.card_congr e.toEquiv, Fintype.card_fin]; omega
  · obtain ⟨e⟩ := he; rw [Fintype.card_congr e.toEquiv, Fintype.card_fin]; omega
  · obtain ⟨e⟩ := he; rw [Fintype.card_congr e.toEquiv, Fintype.card_fin]; omega
  · obtain ⟨e⟩ := he; rw [Fintype.card_congr e.toEquiv, Fintype.card_fin]; omega
  · obtain ⟨e⟩ := he; rw [Fintype.card_congr e.toEquiv, Fintype.card_fin]; omega
  · obtain ⟨e⟩ := he
    rw [Fintype.card_congr e.toEquiv]
    haveI : Nonempty ({v : Fin (d + 4) // v ≠ 0} ⊕ Fin 2) := ⟨Sum.inr 0⟩
    exact Fintype.card_pos
  · obtain ⟨e⟩ := he
    rw [Fintype.card_congr e.toEquiv]
    haveI : Nonempty ({v : Fin (d + 4) // v ≠ 0} ⊕ Fin 2) := ⟨Sum.inr 0⟩
    exact Fintype.card_pos

/-- Every graph in `InJClosureBInfty` has positive vertex cardinality. -/
theorem inJClosureBInfty_card_pos {W : Type} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} (h : InJClosureBInfty H) : 1 ≤ Fintype.card W := by
  induction h with
  | base H hB => exact inBInfty_card_pos hB
  | iso _ _ _ he ih =>
      obtain ⟨e⟩ := he
      rw [← Fintype.card_congr e.toEquiv]
      exact ih
  | @subst W₁ W₂ _ _ _ _ H₁ v₀ H₂ _ _ ih₁ ih₂ =>
      haveI : Nonempty W₁ := ⟨v₀⟩
      haveI : Nonempty W₂ := Fintype.card_pos_iff.mp ih₂
      haveI : Nonempty ({v : W₁ // v ≠ v₀} ⊕ W₂) :=
        Nonempty.map Sum.inr inferInstance
      exact Fintype.card_pos
  | add_leaf _ v₀ _ _ _ =>
      haveI : Nonempty _ := ⟨v₀⟩
      exact Fintype.card_pos

/-- Isomorphism invariance of `InBNew`. -/
theorem InBNew.of_iso {W₁ W₂ : Type} [Fintype W₁] [DecidableEq W₁]
    [Fintype W₂] [DecidableEq W₂] {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂}
    (e : H₁ ≃g H₂) (h : InBNew H₁) : InBNew H₂ := by
  rcases h with h9 | he₀ | ⟨d, hd1, hd2, he₀ | he₀⟩ | ⟨d, hd1, hd2, he₀ | he₀⟩
  · exact Or.inl (InBStar.of_iso e h9)
  · obtain ⟨e₀⟩ := he₀; exact Or.inr (Or.inl ⟨e.symm.trans e₀⟩)
  · obtain ⟨e₀⟩ := he₀; exact Or.inr (Or.inr (Or.inl ⟨d, hd1, hd2, Or.inl ⟨e.symm.trans e₀⟩⟩))
  · obtain ⟨e₀⟩ := he₀; exact Or.inr (Or.inr (Or.inl ⟨d, hd1, hd2, Or.inr ⟨e.symm.trans e₀⟩⟩))
  · obtain ⟨e₀⟩ := he₀; exact Or.inr (Or.inr (Or.inr ⟨d, hd1, hd2, Or.inl ⟨e.symm.trans e₀⟩⟩))
  · obtain ⟨e₀⟩ := he₀; exact Or.inr (Or.inr (Or.inr ⟨d, hd1, hd2, Or.inr ⟨e.symm.trans e₀⟩⟩))

/-- Isomorphism invariance of `InBInfty`. -/
theorem InBInfty.of_iso {W₁ W₂ : Type} [Fintype W₁] [DecidableEq W₁]
    [Fintype W₂] [DecidableEq W₂] {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂}
    (e : H₁ ≃g H₂) (h : InBInfty H₁) : InBInfty H₂ := by
  rcases h with hNew | ⟨k, hk, he₀ | he₀⟩ | ⟨d, hd, he₀ | he₀⟩ |
      ⟨d, hd, he₀ | he₀⟩ | ⟨d, hd, he₀ | he₀⟩
  · exact Or.inl (InBNew.of_iso e hNew)
  · obtain ⟨e₀⟩ := he₀; exact Or.inr (Or.inl ⟨k, hk, Or.inl ⟨e.symm.trans e₀⟩⟩)
  · obtain ⟨e₀⟩ := he₀; exact Or.inr (Or.inl ⟨k, hk, Or.inr ⟨e.symm.trans e₀⟩⟩)
  · obtain ⟨e₀⟩ := he₀; exact Or.inr (Or.inr (Or.inl ⟨d, hd, Or.inl ⟨e.symm.trans e₀⟩⟩))
  · obtain ⟨e₀⟩ := he₀; exact Or.inr (Or.inr (Or.inl ⟨d, hd, Or.inr ⟨e.symm.trans e₀⟩⟩))
  · obtain ⟨e₀⟩ := he₀; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨d, hd, Or.inl ⟨e.symm.trans e₀⟩⟩)))
  · obtain ⟨e₀⟩ := he₀; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨d, hd, Or.inr ⟨e.symm.trans e₀⟩⟩)))
  · obtain ⟨e₀⟩ := he₀; exact Or.inr (Or.inr (Or.inr (Or.inr ⟨d, hd, Or.inl ⟨e.symm.trans e₀⟩⟩)))
  · obtain ⟨e₀⟩ := he₀; exact Or.inr (Or.inr (Or.inr (Or.inr ⟨d, hd, Or.inr ⟨e.symm.trans e₀⟩⟩)))

/-- Structural decomposition predicate for `InJClosureBNew`. -/
def InJClosureBNewDecomp {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) : Prop :=
  InBNew H ∨
  (∃ (W_a W_b : Type) (_ : Fintype W_a) (_ : DecidableEq W_a) (_ : Fintype W_b) (_ : DecidableEq W_b)
      (H_a : SimpleGraph W_a) (v₀ : W_a) (H_b : SimpleGraph W_b),
    2 ≤ Fintype.card W_a ∧ 2 ≤ Fintype.card W_b ∧
    InJClosureBNew H_a ∧ InJClosureBNew H_b ∧
    Nonempty (substGraph H_a v₀ H_b ≃g H)) ∨
  (3 ≤ Fintype.card W ∧ ∃ v₀ : W,
    (neighborFinsetIn H v₀ Finset.univ).card ≤ 1 ∧
    InJClosureBNew (H.comap (Subtype.val : {v : W // v ≠ v₀} → W)))

/-- `InJClosureBNewDecomp` is invariant under isomorphism. -/
theorem InJClosureBNewDecomp.of_iso {W₁ W₂ : Type} [Fintype W₁] [DecidableEq W₁]
    [Fintype W₂] [DecidableEq W₂] {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂}
    (e : H₁ ≃g H₂) (h : InJClosureBNewDecomp H₁) : InJClosureBNewDecomp H₂ := by
  rcases h with hB | ⟨W_a, W_b, f_a, d_a, f_b, d_b, H_a, v₀, H_b, hcard_a, hcard_b, hJa, hJb, ⟨e₀⟩⟩ |
      ⟨hcard3, v₁, hdeg₁, hJ_sub⟩
  · exact Or.inl (InBNew.of_iso e hB)
  · exact Or.inr (Or.inl ⟨W_a, W_b, f_a, d_a, f_b, d_b, H_a, v₀, H_b,
      hcard_a, hcard_b, hJa, hJb, ⟨e₀.trans e⟩⟩)
  · right; right
    have hcard_eq : Fintype.card W₂ = Fintype.card W₁ := Fintype.card_congr e.symm.toEquiv
    refine ⟨hcard_eq ▸ hcard3, e v₁, ?_, ?_⟩
    · have h_bij : (neighborFinsetIn H₂ (e v₁) Finset.univ).card =
          (neighborFinsetIn H₁ v₁ Finset.univ).card := by
        refine Finset.card_bij (fun w _ => e.symm w) ?_ ?_ ?_
        · intro w hw
          rw [mem_neighborFinsetIn_iff] at hw ⊢
          refine ⟨mem_univ _, ?_⟩
          have h1 := (e.map_rel_iff (a := v₁) (b := e.symm w)).mp
          simp only [RelIso.apply_symm_apply] at h1
          exact h1 hw.2
        · intro w₁ _ w₂ _ h_eq
          exact e.symm.injective h_eq
        · intro u hu
          rw [mem_neighborFinsetIn_iff] at hu
          refine ⟨e u, ?_, e.symm_apply_apply u⟩
          rw [mem_neighborFinsetIn_iff]
          exact ⟨mem_univ _, e.map_rel_iff.mpr hu.2⟩
      omega
    · let e_sub : H₁.comap (Subtype.val : {v : W₁ // v ≠ v₁} → W₁) ≃g
          H₂.comap (Subtype.val : {v : W₂ // v ≠ e v₁} → W₂) :=
        { toFun := fun ⟨u, hu⟩ => ⟨e u, fun h => hu (e.injective h)⟩
          invFun := fun ⟨w, hw⟩ => ⟨e.symm w, fun h => hw (by rw [← h, e.apply_symm_apply])⟩
          left_inv := fun ⟨u, _⟩ => Subtype.ext (e.symm_apply_apply u)
          right_inv := fun ⟨w, _⟩ => Subtype.ext (e.apply_symm_apply w)
          map_rel_iff' := by
            rintro ⟨u, _⟩ ⟨v, _⟩
            exact e.map_rel_iff }
      exact InJClosureBNew.iso _ _ hJ_sub ⟨e_sub⟩

/-- Decomposition theorem for `InJClosureBNew`. -/
theorem inJClosureBNew_decomp {W : Type} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} (hJ : InJClosureBNew H) : InJClosureBNewDecomp H := by
  induction hJ with
  | base H hB => exact Or.inl hB
  | iso H₁ H₂ _ he ih =>
      obtain ⟨e⟩ := he
      exact InJClosureBNewDecomp.of_iso e ih
  | @subst W₁ W₂ _ _ _ _ H₁ v₀ H₂ hJ₁ hJ₂ ih₁ ih₂ =>
      have hpos₁ : 1 ≤ Fintype.card W₁ := inJClosureBNew_card_pos hJ₁
      have hpos₂ : 1 ≤ Fintype.card W₂ := inJClosureBNew_card_pos hJ₂
      rcases eq_or_ne (Fintype.card W₁) 1 with h1 | h1_ne
      · exact InJClosureBNewDecomp.of_iso (substGraphIsoOfCardOne H₁ v₀ H₂ h1).symm ih₂
      · rcases eq_or_ne (Fintype.card W₂) 1 with h2 | h2_ne
        · exact InJClosureBNewDecomp.of_iso (substGraphIsoOfCardOneRight H₁ v₀ H₂ h2).symm ih₁
        · exact Or.inr (Or.inl ⟨W₁, W₂, inferInstance, inferInstance, inferInstance, inferInstance,
            H₁, v₀, H₂, by omega, by omega, hJ₁, hJ₂, ⟨SimpleGraph.Iso.refl⟩⟩)
  | @add_leaf W _ _ H v₀ hdeg hJ_sub _ =>
      haveI : Nonempty W := ⟨v₀⟩
      have hpos : 1 ≤ Fintype.card W := Fintype.card_pos
      by_cases hle2 : Fintype.card W ≤ 2
      · exact Or.inl (Or.inl (inBStar_of_card_le_two 9 H hpos hle2))
      · exact Or.inr (Or.inr ⟨by omega, v₀, hdeg, hJ_sub⟩)

/-- Structural decomposition predicate for `InJClosureBInfty`. -/
def InJClosureBInftyDecomp {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) : Prop :=
  InBInfty H ∨
  (∃ (W_a W_b : Type) (_ : Fintype W_a) (_ : DecidableEq W_a) (_ : Fintype W_b) (_ : DecidableEq W_b)
      (H_a : SimpleGraph W_a) (v₀ : W_a) (H_b : SimpleGraph W_b),
    2 ≤ Fintype.card W_a ∧ 2 ≤ Fintype.card W_b ∧
    InJClosureBInfty H_a ∧ InJClosureBInfty H_b ∧
    Nonempty (substGraph H_a v₀ H_b ≃g H)) ∨
  (3 ≤ Fintype.card W ∧ ∃ v₀ : W,
    (neighborFinsetIn H v₀ Finset.univ).card ≤ 1 ∧
    InJClosureBInfty (H.comap (Subtype.val : {v : W // v ≠ v₀} → W)))

/-- `InJClosureBInftyDecomp` is invariant under isomorphism. -/
theorem InJClosureBInftyDecomp.of_iso {W₁ W₂ : Type} [Fintype W₁] [DecidableEq W₁]
    [Fintype W₂] [DecidableEq W₂] {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂}
    (e : H₁ ≃g H₂) (h : InJClosureBInftyDecomp H₁) : InJClosureBInftyDecomp H₂ := by
  rcases h with hB | ⟨W_a, W_b, f_a, d_a, f_b, d_b, H_a, v₀, H_b, hcard_a, hcard_b, hJa, hJb, ⟨e₀⟩⟩ |
      ⟨hcard3, v₁, hdeg₁, hJ_sub⟩
  · exact Or.inl (InBInfty.of_iso e hB)
  · exact Or.inr (Or.inl ⟨W_a, W_b, f_a, d_a, f_b, d_b, H_a, v₀, H_b,
      hcard_a, hcard_b, hJa, hJb, ⟨e₀.trans e⟩⟩)
  · right; right
    have hcard_eq : Fintype.card W₂ = Fintype.card W₁ := Fintype.card_congr e.symm.toEquiv
    refine ⟨hcard_eq ▸ hcard3, e v₁, ?_, ?_⟩
    · have h_bij : (neighborFinsetIn H₂ (e v₁) Finset.univ).card =
          (neighborFinsetIn H₁ v₁ Finset.univ).card := by
        refine Finset.card_bij (fun w _ => e.symm w) ?_ ?_ ?_
        · intro w hw
          rw [mem_neighborFinsetIn_iff] at hw ⊢
          refine ⟨mem_univ _, ?_⟩
          have h1 := (e.map_rel_iff (a := v₁) (b := e.symm w)).mp
          simp only [RelIso.apply_symm_apply] at h1
          exact h1 hw.2
        · intro w₁ _ w₂ _ h_eq
          exact e.symm.injective h_eq
        · intro u hu
          rw [mem_neighborFinsetIn_iff] at hu
          refine ⟨e u, ?_, e.symm_apply_apply u⟩
          rw [mem_neighborFinsetIn_iff]
          exact ⟨mem_univ _, e.map_rel_iff.mpr hu.2⟩
      omega
    · let e_sub : H₁.comap (Subtype.val : {v : W₁ // v ≠ v₁} → W₁) ≃g
          H₂.comap (Subtype.val : {v : W₂ // v ≠ e v₁} → W₂) :=
        { toFun := fun ⟨u, hu⟩ => ⟨e u, fun h => hu (e.injective h)⟩
          invFun := fun ⟨w, hw⟩ => ⟨e.symm w, fun h => hw (by rw [← h, e.apply_symm_apply])⟩
          left_inv := fun ⟨u, _⟩ => Subtype.ext (e.symm_apply_apply u)
          right_inv := fun ⟨w, _⟩ => Subtype.ext (e.apply_symm_apply w)
          map_rel_iff' := by
            rintro ⟨u, _⟩ ⟨v, _⟩
            exact e.map_rel_iff }
      exact InJClosureBInfty.iso _ _ hJ_sub ⟨e_sub⟩

/-- Decomposition theorem for `InJClosureBInfty`. -/
theorem inJClosureBInfty_decomp {W : Type} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} (hJ : InJClosureBInfty H) : InJClosureBInftyDecomp H := by
  induction hJ with
  | base H hB => exact Or.inl hB
  | iso H₁ H₂ _ he ih =>
      obtain ⟨e⟩ := he
      exact InJClosureBInftyDecomp.of_iso e ih
  | @subst W₁ W₂ _ _ _ _ H₁ v₀ H₂ hJ₁ hJ₂ ih₁ ih₂ =>
      have hpos₁ : 1 ≤ Fintype.card W₁ := inJClosureBInfty_card_pos hJ₁
      have hpos₂ : 1 ≤ Fintype.card W₂ := inJClosureBInfty_card_pos hJ₂
      rcases eq_or_ne (Fintype.card W₁) 1 with h1 | h1_ne
      · exact InJClosureBInftyDecomp.of_iso (substGraphIsoOfCardOne H₁ v₀ H₂ h1).symm ih₂
      · rcases eq_or_ne (Fintype.card W₂) 1 with h2 | h2_ne
        · exact InJClosureBInftyDecomp.of_iso (substGraphIsoOfCardOneRight H₁ v₀ H₂ h2).symm ih₁
        · exact Or.inr (Or.inl ⟨W₁, W₂, inferInstance, inferInstance, inferInstance, inferInstance,
            H₁, v₀, H₂, by omega, by omega, hJ₁, hJ₂, ⟨SimpleGraph.Iso.refl⟩⟩)
  | @add_leaf W _ _ H v₀ hdeg hJ_sub _ =>
      haveI : Nonempty W := ⟨v₀⟩
      have hpos : 1 ≤ Fintype.card W := Fintype.card_pos
      by_cases hle2 : Fintype.card W ≤ 2
      · exact Or.inl (Or.inl (Or.inl (inBStar_of_card_le_two 9 H hpos hle2)))
      · exact Or.inr (Or.inr ⟨by omega, v₀, hdeg, hJ_sub⟩)

/-- Strong induction helper for `InJClosureBNew` pair virality. -/
private theorem inJClosureBNew_isPairViral_aux
    (h_base : ∀ {W : Type} [Fintype W] [DecidableEq W] (B : SimpleGraph W),
      InBNew B → HasErdosHajnalProp B) :
    ∀ (N : ℕ) {W₁ W₂ : Type} [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]
      (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂),
      Fintype.card W₁ + Fintype.card W₂ = N →
      InJClosureBNew H₁ → InJClosureBNew H₂ →
      IsPairViral H₁ H₂ᶜ := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro W₁ W₂ _ _ _ _ H₁ H₂ hN hJ₁ hJ₂
    have hpos₁ : 1 ≤ Fintype.card W₁ := inJClosureBNew_card_pos hJ₁
    have hpos₂ : 1 ≤ Fintype.card W₂ := inJClosureBNew_card_pos hJ₂
    haveI : Nonempty W₁ := Fintype.card_pos_iff.mp hpos₁
    haveI : Nonempty W₂ := Fintype.card_pos_iff.mp hpos₂
    rcases inJClosureBNew_decomp hJ₁ with
      hB₁ |
      ⟨W_a, W_b, f_a, d_a, f_b, d_b, H_a, v₀, H_b, hcard_a, hcard_b, hJa, hJb, ⟨e₁⟩⟩ |
      ⟨hcard₁_3, v₀, hdeg₁, hJ₁_sub⟩
    · have hv₁ : IsViral H₁ := isViral_of_hasErdosHajnalProp (h_base H₁ hB₁)
      exact isPairViral_of_isViral_left H₂ᶜ hv₁
    · have hW₁_card : Fintype.card W₁ = Fintype.card W_a - 1 + Fintype.card W_b := by
        rw [← Fintype.card_congr e₁.toEquiv, card_substGraph_vert v₀]
      have hlt_a : Fintype.card W_a + Fintype.card W₂ < N := by omega
      have hlt_b : Fintype.card W_b + Fintype.card W₂ < N := by omega
      have hv_a : IsPairViral H_a H₂ᶜ := ih _ hlt_a H_a H₂ rfl hJa hJ₂
      have hv_b : IsPairViral H_b H₂ᶜ := ih _ hlt_b H_b H₂ rfl hJb hJ₂
      exact IsPairViral.congr e₁ SimpleGraph.Iso.refl (isPairViral_substGraph H_a v₀ H_b H₂ᶜ hv_a hv_b)
    · rcases inJClosureBNew_decomp hJ₂ with
        hB₂ |
        ⟨V_a, V_b, f_va, d_va, f_vb, d_vb, J_a, w₀, J_b, hcard_va, hcard_vb, hJ_va, hJ_vb, ⟨e₂⟩⟩ |
        ⟨hcard₂_3, w₀, hdeg₂, hJ₂_sub⟩
      · have hv₂_c : IsViral H₂ᶜ := isViral_of_hasErdosHajnalProp (h_base H₂ hB₂).compl
        exact isPairViral_of_isViral_right H₁ hv₂_c
      · have hW₂_card : Fintype.card W₂ = Fintype.card V_a - 1 + Fintype.card V_b := by
          rw [← Fintype.card_congr e₂.toEquiv, card_substGraph_vert w₀]
        have hlt_va : Fintype.card W₁ + Fintype.card V_a < N := by omega
        have hlt_vb : Fintype.card W₁ + Fintype.card V_b < N := by omega
        have hv_va : IsPairViral H₁ J_aᶜ := ih _ hlt_va H₁ J_a rfl hJ₁ hJ_va
        have hv_vb : IsPairViral H₁ J_bᶜ := ih _ hlt_vb H₁ J_b rfl hJ₁ hJ_vb
        have hv_subst_c : IsPairViral (substGraph J_aᶜ w₀ J_bᶜ) H₁ :=
          isPairViral_substGraph J_aᶜ w₀ J_bᶜ H₁ hv_va.symm hv_vb.symm
        rw [← substGraph_compl] at hv_subst_c
        exact (IsPairViral.congr (complIso e₂) SimpleGraph.Iso.refl hv_subst_c).symm
      · have hlt₁ : Fintype.card {v : W₁ // v ≠ v₀} + Fintype.card W₂ < N := by
          rw [card_subtype_ne v₀]; omega
        have hlt₂ : Fintype.card W₁ + Fintype.card {w : W₂ // w ≠ w₀} < N := by
          rw [card_subtype_ne w₀]; omega
        have hv_sub₁ : IsPairViral (H₁.comap (Subtype.val : {v : W₁ // v ≠ v₀} → W₁)) H₂ᶜ :=
          ih _ hlt₁ _ H₂ rfl hJ₁_sub hJ₂
        have hv_sub₂ : IsPairViral H₁ (H₂.comap (Subtype.val : {w : W₂ // w ≠ w₀} → W₂))ᶜ :=
          ih _ hlt₂ H₁ _ rfl hJ₁ hJ₂_sub
        exact isPairViral_simultaneous_leaf_coleaf H₁ v₀ H₂ w₀
          hcard₁_3 hcard₂_3 hdeg₁ hdeg₂ hv_sub₁ hv_sub₂

/-- Master two-graph closure theorem for $\mathcal{J}(\mathcal{B}_{\mathrm{new}}^*)$. -/
theorem inJClosureBNew_pair_viral_of_base
    (h_base : ∀ {W : Type} [Fintype W] [DecidableEq W] (B : SimpleGraph W),
      InBNew B → HasErdosHajnalProp B)
    {W₁ W₂ : Type} [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]
    (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂)
    (hJ₁ : InJClosureBNew H₁) (hJ₂ : InJClosureBNew H₂) :
    IsPairViral H₁ H₂ᶜ ∧ HasPairPolyRodlProp H₁ H₂ᶜ ∧ HasPairErdosHajnalProp H₁ H₂ᶜ := by
  have h_viral : IsPairViral H₁ H₂ᶜ :=
    inJClosureBNew_isPairViral_aux h_base (Fintype.card W₁ + Fintype.card W₂) H₁ H₂ rfl hJ₁ hJ₂
  have h_rodl : HasPairPolyRodlProp H₁ H₂ᶜ := hasPairPolyRodlProp_of_isPairViral h_viral
  have h_eh : HasPairErdosHajnalProp H₁ H₂ᶜ := hasPairErdosHajnalProp_of_hasPairPolyRodlProp h_rodl
  exact ⟨h_viral, h_rodl, h_eh⟩

/-- Master single-graph closure theorem for $\mathcal{H}(\mathcal{B}_{\mathrm{new}}^*)$. -/
theorem inHClosureBNew_eh_of_base
    (h_base : ∀ {W : Type} [Fintype W] [DecidableEq W] (B : SimpleGraph W),
      InBNew B → HasErdosHajnalProp B)
    {W : Type} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (hH : InHClosureBNew H) :
    HasErdosHajnalProp H ∧ HasErdosHajnalProp Hᶜ ∧ HasPolyRodlProp H ∧ IsViral H := by
  obtain ⟨hJ, hJc⟩ := hH
  obtain ⟨h_viral, h_rodl, h_eh⟩ := inJClosureBNew_pair_viral_of_base h_base H Hᶜ hJ hJc
  rw [compl_compl] at h_viral h_rodl h_eh
  have h_eh_single : HasErdosHajnalProp H := (hasPairErdosHajnalProp_self_iff H).mp h_eh
  have h_rodl_single : HasPolyRodlProp H := (hasPairPolyRodlProp_self_iff H).mp h_rodl
  have h_viral_single : IsViral H := (isPairViral_self_iff H).mp h_viral
  exact ⟨h_eh_single, h_eh_single.compl, h_rodl_single, h_viral_single⟩

/-- Strong induction helper for `InJClosureBInfty` pair virality. -/
private theorem inJClosureBInfty_isPairViral_aux
    (h_base : ∀ {W : Type} [Fintype W] [DecidableEq W] (B : SimpleGraph W),
      InBInfty B → HasErdosHajnalProp B) :
    ∀ (N : ℕ) {W₁ W₂ : Type} [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]
      (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂),
      Fintype.card W₁ + Fintype.card W₂ = N →
      InJClosureBInfty H₁ → InJClosureBInfty H₂ →
      IsPairViral H₁ H₂ᶜ := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro W₁ W₂ _ _ _ _ H₁ H₂ hN hJ₁ hJ₂
    have hpos₁ : 1 ≤ Fintype.card W₁ := inJClosureBInfty_card_pos hJ₁
    have hpos₂ : 1 ≤ Fintype.card W₂ := inJClosureBInfty_card_pos hJ₂
    haveI : Nonempty W₁ := Fintype.card_pos_iff.mp hpos₁
    haveI : Nonempty W₂ := Fintype.card_pos_iff.mp hpos₂
    rcases inJClosureBInfty_decomp hJ₁ with
      hB₁ |
      ⟨W_a, W_b, f_a, d_a, f_b, d_b, H_a, v₀, H_b, hcard_a, hcard_b, hJa, hJb, ⟨e₁⟩⟩ |
      ⟨hcard₁_3, v₀, hdeg₁, hJ₁_sub⟩
    · have hv₁ : IsViral H₁ := isViral_of_hasErdosHajnalProp (h_base H₁ hB₁)
      exact isPairViral_of_isViral_left H₂ᶜ hv₁
    · have hW₁_card : Fintype.card W₁ = Fintype.card W_a - 1 + Fintype.card W_b := by
        rw [← Fintype.card_congr e₁.toEquiv, card_substGraph_vert v₀]
      have hlt_a : Fintype.card W_a + Fintype.card W₂ < N := by omega
      have hlt_b : Fintype.card W_b + Fintype.card W₂ < N := by omega
      have hv_a : IsPairViral H_a H₂ᶜ := ih _ hlt_a H_a H₂ rfl hJa hJ₂
      have hv_b : IsPairViral H_b H₂ᶜ := ih _ hlt_b H_b H₂ rfl hJb hJ₂
      exact IsPairViral.congr e₁ SimpleGraph.Iso.refl (isPairViral_substGraph H_a v₀ H_b H₂ᶜ hv_a hv_b)
    · rcases inJClosureBInfty_decomp hJ₂ with
        hB₂ |
        ⟨V_a, V_b, f_va, d_va, f_vb, d_vb, J_a, w₀, J_b, hcard_va, hcard_vb, hJ_va, hJ_vb, ⟨e₂⟩⟩ |
        ⟨hcard₂_3, w₀, hdeg₂, hJ₂_sub⟩
      · have hv₂_c : IsViral H₂ᶜ := isViral_of_hasErdosHajnalProp (h_base H₂ hB₂).compl
        exact isPairViral_of_isViral_right H₁ hv₂_c
      · have hW₂_card : Fintype.card W₂ = Fintype.card V_a - 1 + Fintype.card V_b := by
          rw [← Fintype.card_congr e₂.toEquiv, card_substGraph_vert w₀]
        have hlt_va : Fintype.card W₁ + Fintype.card V_a < N := by omega
        have hlt_vb : Fintype.card W₁ + Fintype.card V_b < N := by omega
        have hv_va : IsPairViral H₁ J_aᶜ := ih _ hlt_va H₁ J_a rfl hJ₁ hJ_va
        have hv_vb : IsPairViral H₁ J_bᶜ := ih _ hlt_vb H₁ J_b rfl hJ₁ hJ_vb
        have hv_subst_c : IsPairViral (substGraph J_aᶜ w₀ J_bᶜ) H₁ :=
          isPairViral_substGraph J_aᶜ w₀ J_bᶜ H₁ hv_va.symm hv_vb.symm
        rw [← substGraph_compl] at hv_subst_c
        exact (IsPairViral.congr (complIso e₂) SimpleGraph.Iso.refl hv_subst_c).symm
      · have hlt₁ : Fintype.card {v : W₁ // v ≠ v₀} + Fintype.card W₂ < N := by
          rw [card_subtype_ne v₀]; omega
        have hlt₂ : Fintype.card W₁ + Fintype.card {w : W₂ // w ≠ w₀} < N := by
          rw [card_subtype_ne w₀]; omega
        have hv_sub₁ : IsPairViral (H₁.comap (Subtype.val : {v : W₁ // v ≠ v₀} → W₁)) H₂ᶜ :=
          ih _ hlt₁ _ H₂ rfl hJ₁_sub hJ₂
        have hv_sub₂ : IsPairViral H₁ (H₂.comap (Subtype.val : {w : W₂ // w ≠ w₀} → W₂))ᶜ :=
          ih _ hlt₂ H₁ _ rfl hJ₁ hJ₂_sub
        exact isPairViral_simultaneous_leaf_coleaf H₁ v₀ H₂ w₀
          hcard₁_3 hcard₂_3 hdeg₁ hdeg₂ hv_sub₁ hv_sub₂

/-- Master two-graph closure theorem for $\mathcal{J}(\mathcal{B}_\infty^*)$. -/
theorem inJClosureBInfty_pair_viral_of_base
    (h_base : ∀ {W : Type} [Fintype W] [DecidableEq W] (B : SimpleGraph W),
      InBInfty B → HasErdosHajnalProp B)
    {W₁ W₂ : Type} [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]
    (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂)
    (hJ₁ : InJClosureBInfty H₁) (hJ₂ : InJClosureBInfty H₂) :
    IsPairViral H₁ H₂ᶜ ∧ HasPairPolyRodlProp H₁ H₂ᶜ ∧ HasPairErdosHajnalProp H₁ H₂ᶜ := by
  have h_viral : IsPairViral H₁ H₂ᶜ :=
    inJClosureBInfty_isPairViral_aux h_base (Fintype.card W₁ + Fintype.card W₂) H₁ H₂ rfl hJ₁ hJ₂
  have h_rodl : HasPairPolyRodlProp H₁ H₂ᶜ := hasPairPolyRodlProp_of_isPairViral h_viral
  have h_eh : HasPairErdosHajnalProp H₁ H₂ᶜ := hasPairErdosHajnalProp_of_hasPairPolyRodlProp h_rodl
  exact ⟨h_viral, h_rodl, h_eh⟩

/-- Master single-graph closure theorem for $\mathcal{H}(\mathcal{B}_\infty^*)$. -/
theorem inHClosureBInfty_eh_of_base
    (h_base : ∀ {W : Type} [Fintype W] [DecidableEq W] (B : SimpleGraph W),
      InBInfty B → HasErdosHajnalProp B)
    {W : Type} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (hH : InHClosureBInfty H) :
    HasErdosHajnalProp H ∧ HasErdosHajnalProp Hᶜ ∧ HasPolyRodlProp H ∧ IsViral H := by
  obtain ⟨hJ, hJc⟩ := hH
  obtain ⟨h_viral, h_rodl, h_eh⟩ := inJClosureBInfty_pair_viral_of_base h_base H Hᶜ hJ hJc
  rw [compl_compl] at h_viral h_rodl h_eh
  have h_eh_single : HasErdosHajnalProp H := (hasPairErdosHajnalProp_self_iff H).mp h_eh
  have h_rodl_single : HasPolyRodlProp H := (hasPairPolyRodlProp_self_iff H).mp h_rodl
  have h_viral_single : IsViral H := (isPairViral_self_iff H).mp h_viral
  exact ⟨h_eh_single, h_eh_single.compl, h_rodl_single, h_viral_single⟩

/-!
### Section 2: Exhaustive Classification of Small Trees/Forests (`Theorem 8(1)`) & Strict Containments (`Theorem 8(2)`, `Theorem 9(3)`)
-/

/-- Computable characterization of `IsPrimeGraph` avoiding `Classical.propDecidable`. -/
theorem isPrimeGraph_iff_dec {W : Type} [Fintype W] [DecidableEq W] (G : SimpleGraph W) :
    IsPrimeGraph G ↔
      4 ≤ Fintype.card W ∧
      ∀ M : Finset W, M.Nonempty → M ⊂ Finset.univ →
        (∀ z : W, z ∉ M → (∀ x ∈ M, G.Adj z x) ∨ (∀ x ∈ M, ¬G.Adj z x)) → M.card = 1 := by
  unfold IsPrimeGraph IsProperModuleIn IsModuleIn IsVertexPureTo
  constructor
  · intro h; refine ⟨h.1, fun M hne hss hmod => h.2 M ⟨hne, hss, Finset.subset_univ M, fun z _ hz => hmod z hz⟩⟩
  · intro h; refine ⟨h.1, fun M ⟨hne, hss, _, hmod⟩ => h.2 M hne hss (fun z hz => hmod z (Finset.mem_univ z) hz)⟩

/-- No graph containing two induced $2K_2$ edges $(a, b)$ and $(c, d)$ can be a split graph. -/
theorem not_isSplitGraph_of_two_indep_edges {W : Type} [Fintype W] [DecidableEq W]
    {G : SimpleGraph W} {a b c d : W}
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : ¬G.Adj a c) (had : ¬G.Adj a d) (hbc : ¬G.Adj b c) (hbd : ¬G.Adj b d) :
    ¬IsSplitGraph G := by
  rintro ⟨C, I, hCI, _, hC, hI⟩
  have h_mem : ∀ x : W, x ∈ C ∨ x ∈ I := fun x => Finset.mem_union.mp (hCI ▸ Finset.mem_univ x)
  have h1 : a ∈ C ∨ b ∈ C := by
    rcases h_mem a with haC | haI
    · exact Or.inl haC
    · rcases h_mem b with hbC | hbI
      · exact Or.inr hbC
      · exact False.elim (((compl_adj G a b).mp (hI haI hbI (G.ne_of_adj hab))).2 hab)
  have h2 : c ∈ C ∨ d ∈ C := by
    rcases h_mem c with hcC | hcI
    · exact Or.inl hcC
    · rcases h_mem d with hdC | hdI
      · exact Or.inr hdC
      · exact False.elim (((compl_adj G c d).mp (hI hcI hdI (G.ne_of_adj hcd))).2 hcd)
  rcases h1 with haC | hbC <;> rcases h2 with hcC | hdC
  · exact hac (hC haC hcC (fun h => hbc (h ▸ hab.symm)))
  · exact had (hC haC hdC (fun h => by subst h; exact hac hcd.symm))
  · exact hbc (hC hbC hcC (fun h => by subst h; exact hac hab))
  · exact hbd (hC hbC hdC (fun h => by subst h; exact had hab))

/-- Computable ordered edge pair count `(Finset.univ : Finset (W × W)).filter (fun p => G.Adj p.1 p.2)`. -/
def orderedEdgeCount {W : Type} [Fintype W] (G : SimpleGraph W) [DecidableRel G.Adj] : ℕ :=
  ((Finset.univ : Finset (W × W)).filter (fun p => G.Adj p.1 p.2)).card

theorem orderedEdgeCount_iso {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (G₁ : SimpleGraph A) [DecidableRel G₁.Adj] (G₂ : SimpleGraph B) [DecidableRel G₂.Adj]
    (iso : G₁ ≃g G₂) : orderedEdgeCount G₁ = orderedEdgeCount G₂ := by
  unfold orderedEdgeCount
  refine Finset.card_bij (fun p _ => (iso p.1, iso p.2)) ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨Finset.mem_univ _, iso.map_rel_iff.mpr hp.2⟩
  · intro p₁ _ p₂ _ h
    exact Prod.ext (iso.injective (congrArg Prod.fst h)) (iso.injective (congrArg Prod.snd h))
  · intro q hq
    rw [Finset.mem_filter] at hq
    refine ⟨(iso.symm q.1, iso.symm q.2), ?_, Prod.ext (iso.apply_symm_apply q.1) (iso.apply_symm_apply q.2)⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (iso.map_rel_iff (a := iso.symm q.1) (b := iso.symm q.2)).mp (by simpa using hq.2)⟩

private def isoOfComplLeft {A B : Type} {G₁ : SimpleGraph A} {G₂ : SimpleGraph B}
    (e : G₁ᶜ ≃g G₂) : G₁ ≃g G₂ᶜ where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro a b
    have h := e.map_rel_iff (a := a) (b := b)
    by_cases hab : a = b
    · subst hab
      have h1 : ¬G₁.Adj a a := G₁.loopless a
      have h2 : ¬G₂ᶜ.Adj (e a) (e a) := G₂ᶜ.loopless (e a)
      tauto
    · have heab : e a ≠ e b := fun heq => hab (e.injective heq)
      simp only [compl_adj, ne_eq, hab, not_false_eq_true, true_and] at h
      simp only [compl_adj, ne_eq]
      tauto

private def isoOfComplBoth {A B : Type} {G₁ : SimpleGraph A} {G₂ : SimpleGraph B}
    (e : G₁ᶜ ≃g G₂ᶜ) : G₁ ≃g G₂ where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro a b
    have h := e.map_rel_iff (a := a) (b := b)
    by_cases hab : a = b
    · subst hab
      have h1 : ¬G₁.Adj a a := G₁.loopless a
      have h2 : ¬G₂.Adj (e a) (e a) := G₂.loopless (e a)
      tauto
    · have heab : e a ≠ e b := fun heq => hab (e.injective heq)
      simp only [compl_adj, ne_eq, hab, heab, not_false_eq_true, true_and] at h
      tauto

private theorem card_pair_le_two {α : Type*} [DecidableEq α] (a b : α) :
    ({a, b} : Finset α).card ≤ 2 :=
  le_trans (Finset.card_insert_le a {b}) (by simp)

private theorem card_triple_le_three {α : Type*} [DecidableEq α] (a b c : α) :
    ({a, b, c} : Finset α).card ≤ 3 :=
  le_trans (Finset.card_insert_le a {b, c}) (by have := card_pair_le_two b c; omega)

/-- In any non-trivial substitution `substGraph H_a v₀ H_b` (`2 ≤ card W_a`, `2 ≤ card W_b`),
the substituted fiber `Sum.inr '' univ` is a proper module of cardinality `≥ 2`, so the substitution is not prime. -/
theorem not_isPrimeGraph_substGraph {W_a W_b : Type} [Fintype W_a] [DecidableEq W_a]
    [Fintype W_b] [DecidableEq W_b]
    (H_a : SimpleGraph W_a) (v₀ : W_a) (H_b : SimpleGraph W_b)
    (ha : 2 ≤ Fintype.card W_a) (hb : 2 ≤ Fintype.card W_b) :
    ¬IsPrimeGraph (substGraph H_a v₀ H_b) := by
  intro hPrime
  let M : Finset ({v : W_a // v ≠ v₀} ⊕ W_b) := Finset.univ.image Sum.inr
  have hM_card : M.card = Fintype.card W_b := by
    rw [Finset.card_image_of_injective _ Sum.inr_injective, Finset.card_univ]
  have hM_ne : M.Nonempty := by
    rw [← Finset.card_pos, hM_card]; omega
  have hM_ssub : M ⊂ Finset.univ := by
    rw [Finset.ssubset_univ_iff]
    intro h_univ
    obtain ⟨w, hw⟩ : ∃ w : W_a, w ≠ v₀ := by
      have hcard_ne : 1 ≤ Fintype.card {v : W_a // v ≠ v₀} := by
        rw [card_subtype_ne v₀]; omega
      obtain ⟨⟨w, hw⟩⟩ := Fintype.card_pos_iff.mp hcard_ne
      exact ⟨w, hw⟩
    have hm : (Sum.inl ⟨w, hw⟩ : {v : W_a // v ≠ v₀} ⊕ W_b) ∈ M := h_univ ▸ Finset.mem_univ _
    rcases Finset.mem_image.mp hm with ⟨y, _, hy⟩
    cases hy
  have hM_mod : IsModuleIn (substGraph H_a v₀ H_b) Finset.univ M := by
    refine ⟨Finset.subset_univ _, fun z _ hz => ?_⟩
    rcases z with ⟨w, hw⟩ | y
    · by_cases hadj : H_a.Adj w v₀
      · left
        intro u hu
        rcases Finset.mem_image.mp hu with ⟨y_u, _, rfl⟩
        exact hadj
      · right
        intro u hu hzu
        rcases Finset.mem_image.mp hu with ⟨y_u, _, rfl⟩
        exact hadj hzu
    · exfalso
      exact hz (Finset.mem_image_of_mem Sum.inr (Finset.mem_univ y))
  have h1 := hPrime.2 M ⟨hM_ne, hM_ssub, hM_mod⟩
  omega

/-- Any prime graph $H$ with minimum degree $\ge 2$ in $\mathcal{J}(\mathcal{B}_k^*)$ must belong to $\mathcal{B}_k^*$. -/
theorem inBStar_of_inJClosure_prime_minDeg_ge_two {k : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} (hPrime : IsPrimeGraph H)
    (hMinDeg : ∀ u : W, 2 ≤ (neighborFinsetIn H u Finset.univ).card)
    (hJ : InJClosure k H) : InBStar k H := by
  rcases inJClosure_decomp hJ with
    hB | ⟨W_a, W_b, f_a, d_a, f_b, d_b, H_a, v₀, H_b, ha, hb, _, _, ⟨e⟩⟩ | ⟨_, v₀, hdeg, _⟩
  · exact hB
  · exact False.elim (not_isPrimeGraph_substGraph H_a v₀ H_b ha hb (hPrime.of_iso e.symm))
  · have := hMinDeg v₀; omega

/-- Any prime graph $H$ with minimum degree $\ge 2$ in $\mathcal{J}(\mathcal{B}_{\mathrm{new}}^*)$ must belong to $\mathcal{B}_{\mathrm{new}}^*$. -/
theorem inBNew_of_inJClosureBNew_prime_minDeg_ge_two {W : Type} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} (hPrime : IsPrimeGraph H)
    (hMinDeg : ∀ u : W, 2 ≤ (neighborFinsetIn H u Finset.univ).card)
    (hJ : InJClosureBNew H) : InBNew H := by
  rcases inJClosureBNew_decomp hJ with
    hB | ⟨W_a, W_b, f_a, d_a, f_b, d_b, H_a, v₀, H_b, ha, hb, _, _, ⟨e⟩⟩ | ⟨_, v₀, hdeg, _⟩
  · exact hB
  · exact False.elim (not_isPrimeGraph_substGraph H_a v₀ H_b ha hb (hPrime.of_iso e.symm))
  · have := hMinDeg v₀; omega

/-- `InHClosureBNew` is invariant under graph isomorphism. -/
theorem inHClosureBNew_of_iso {W₁ W₂ : Type} [Fintype W₁] [DecidableEq W₁]
    [Fintype W₂] [DecidableEq W₂] {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂}
    (e : H₁ ≃g H₂) (h : InHClosureBNew H₁) : InHClosureBNew H₂ :=
  ⟨InJClosureBNew.iso H₁ H₂ h.1 ⟨e⟩, InJClosureBNew.iso H₁ᶜ H₂ᶜ h.2 ⟨complIso e⟩⟩

/-- `InHClosureBInfty` is invariant under graph isomorphism. -/
theorem inHClosureBInfty_of_iso {W₁ W₂ : Type} [Fintype W₁] [DecidableEq W₁]
    [Fintype W₂] [DecidableEq W₂] {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂}
    (e : H₁ ≃g H₂) (h : InHClosureBInfty H₁) : InHClosureBInfty H₂ :=
  ⟨InJClosureBInfty.iso H₁ H₂ h.1 ⟨e⟩, InJClosureBInfty.iso H₁ᶜ H₂ᶜ h.2 ⟨complIso e⟩⟩

/-- `InHClosureBNew` is closed under vertex substitution `substGraph H₁ v₀ H₂`. -/
theorem inHClosureBNew_subst {W₁ W₂ : Type} [Fintype W₁] [DecidableEq W₁]
    [Fintype W₂] [DecidableEq W₂] {H₁ : SimpleGraph W₁} (v₀ : W₁) {H₂ : SimpleGraph W₂}
    (h₁ : InHClosureBNew H₁) (h₂ : InHClosureBNew H₂) :
    InHClosureBNew (substGraph H₁ v₀ H₂) := by
  refine ⟨InJClosureBNew.subst H₁ v₀ H₂ h₁.1 h₂.1, ?_⟩
  rw [substGraph_compl]
  exact InJClosureBNew.subst H₁ᶜ v₀ H₂ᶜ h₁.2 h₂.2

/-- `InHClosureBInfty` is closed under vertex substitution `substGraph H₁ v₀ H₂`. -/
theorem inHClosureBInfty_subst {W₁ W₂ : Type} [Fintype W₁] [DecidableEq W₁]
    [Fintype W₂] [DecidableEq W₂] {H₁ : SimpleGraph W₁} (v₀ : W₁) {H₂ : SimpleGraph W₂}
    (h₁ : InHClosureBInfty H₁) (h₂ : InHClosureBInfty H₂) :
    InHClosureBInfty (substGraph H₁ v₀ H₂) := by
  refine ⟨InJClosureBInfty.subst H₁ v₀ H₂ h₁.1 h₂.1, ?_⟩
  rw [substGraph_compl]
  exact InJClosureBInfty.subst H₁ᶜ v₀ H₂ᶜ h₁.2 h₂.2

/-- `(⊥ : SimpleGraph (Fin 2))` belongs to `InHClosureBNew`. -/
theorem inHClosureBNew_bot_fin2 : InHClosureBNew (⊥ : SimpleGraph (Fin 2)) := by
  refine ⟨InJClosureBNew.base _ (Or.inl (Or.inr (Or.inr (Or.inl ⟨SimpleGraph.Iso.refl⟩)))), ?_⟩
  have e : (⊥ : SimpleGraph (Fin 2))ᶜ ≃g (⊤ : SimpleGraph (Fin 2)) :=
    { toEquiv := Equiv.refl (Fin 2)
      map_rel_iff' := by intro a b; simp }
  exact InJClosureBNew.iso _ _ (InJClosureBNew.base _ (Or.inl (Or.inr (Or.inl ⟨SimpleGraph.Iso.refl⟩)))) ⟨e.symm⟩

/-- `pathGraph k` belongs to `InHClosureBNew` for all $1 \le k \le 9$. -/
theorem inHClosureBNew_pathGraph (k : ℕ) (hk1 : 1 ≤ k) (hk9 : k ≤ 9) :
    InHClosureBNew (pathGraph k) :=
  ⟨InJClosureBNew.base _ (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨k, hk1, hk9, Or.inl ⟨SimpleGraph.Iso.refl⟩⟩)))))),
   InJClosureBNew.base _ (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨k, hk1, hk9, Or.inr ⟨SimpleGraph.Iso.refl⟩⟩))))))⟩

/-- `SpiderGraph d` belongs to `InHClosureBNew` for all $2 \le d \le 5$. -/
theorem inHClosureBNew_spiderGraph (d : ℕ) (hd2 : 2 ≤ d) (hd5 : d ≤ 5) :
    InHClosureBNew (SpiderGraph d) :=
  ⟨InJClosureBNew.base _ (Or.inr (Or.inr (Or.inl ⟨d, hd2, hd5, Or.inl ⟨SimpleGraph.Iso.refl⟩⟩))),
   InJClosureBNew.base _ (Or.inr (Or.inr (Or.inl ⟨d, hd2, hd5, Or.inr ⟨SimpleGraph.Iso.refl⟩⟩)))⟩

/-- Explicit isomorphism `substGraph (G - v) ⟨u, huv⟩ (⊥ : SimpleGraph (Fin 2)) ≃g G` when $u \neq v$
are non-adjacent false twins in $G$. -/
def falseTwinsSubstIso {W : Type} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) (u v : W) (huv : u ≠ v) (hnadj : ¬G.Adj u v)
    (htwin : ∀ w : W, G.Adj u w ↔ G.Adj v w) :
    substGraph (G.comap (Subtype.val : {w : W // w ≠ v} → W)) ⟨u, huv⟩ (⊥ : SimpleGraph (Fin 2)) ≃g G where
  toFun s :=
    match s with
    | Sum.inl w => w.1.1
    | Sum.inr 0 => u
    | Sum.inr 1 => v
  invFun x :=
    if hxv : x = v then Sum.inr 1
    else if hxu : x = u then Sum.inr 0
    else Sum.inl ⟨⟨x, hxv⟩, fun h => hxu (congrArg Subtype.val h)⟩
  left_inv s := by
    rcases s with ⟨⟨w, hwv⟩, hwu⟩ | i
    · have hwu' : w ≠ u := fun h => hwu (Subtype.ext h)
      simp [hwv, hwu']
    · fin_cases i
      · simp [huv]
      · simp
  right_inv x := by
    by_cases hxv : x = v
    · subst hxv; simp
    · by_cases hxu : x = u
      · subst hxu; simp [huv]
      · simp [hxv, hxu]
  map_rel_iff' := by
    have hnadj' : ¬G.Adj v u := fun h => hnadj h.symm
    rintro (⟨⟨w₁, hw₁v⟩, hw₁u⟩ | i) (⟨⟨w₂, hw₂v⟩, hw₂u⟩ | j)
    · rfl
    · fin_cases j
      · rfl
      · dsimp [substGraph]
        exact ⟨fun h => (htwin w₁).mpr h.symm |>.symm, fun h => (htwin w₁).mp h.symm |>.symm⟩
    · fin_cases i
      · rfl
      · dsimp [substGraph]
        exact ⟨fun h => (htwin w₂).mpr h, fun h => (htwin w₂).mp h⟩
    · fin_cases i <;> fin_cases j <;> simp [substGraph, hnadj, hnadj']

/-- **False-Twin Reduction for `InHClosureBNew`**: if $u \neq v$ are non-adjacent vertices with the same neighborhood
in $G$ and $G - v \in \mathcal{H}(\mathcal{B}_{\mathrm{new}}^*)$, then $G \in \mathcal{H}(\mathcal{B}_{\mathrm{new}}^*)$. -/
theorem inHClosureBNew_of_false_twins {W : Type} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) (u v : W) (huv : u ≠ v) (hnadj : ¬G.Adj u v)
    (htwin : ∀ w : W, G.Adj u w ↔ G.Adj v w)
    (hG' : InHClosureBNew (G.comap (Subtype.val : {w : W // w ≠ v} → W))) :
    InHClosureBNew G :=
  inHClosureBNew_of_iso (falseTwinsSubstIso G u v huv hnadj htwin)
    (inHClosureBNew_subst ⟨u, huv⟩ hG' inHClosureBNew_bot_fin2)

private theorem empty_fin2_ne_zero_ne_one (x : {i : Fin 2 // i ≠ 0})
    (hx : x ≠ ⟨1, by decide⟩) : False := by
  rcases x with ⟨i, hi⟩
  fin_cases i
  · exact hi rfl
  · exact hx rfl

/-- Explicit isomorphism representing a partition $W = C \sqcup (W \setminus C)$ with no edges between $C$ and $W \setminus C$
as a two-step substitution into $\overline{K_2}$. -/
def anticompleteSplitIso {W : Type} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) (C : Finset W)
    (h_anti : ∀ x ∈ C, ∀ y ∉ C, ¬G.Adj x y) :
    substGraph
      (substGraph (⊥ : SimpleGraph (Fin 2)) 0 (G.comap (Subtype.val : {w : W // w ∈ C} → W)))
      (Sum.inl ⟨1, by decide⟩)
      (G.comap (Subtype.val : {w : W // w ∉ C} → W)) ≃g G where
  toFun z :=
    match z with
    | Sum.inl ⟨Sum.inl x, hne⟩ =>
        False.elim (empty_fin2_ne_zero_ne_one x (fun h => hne (congrArg Sum.inl h)))
    | Sum.inl ⟨Sum.inr w₁, _⟩ => w₁.1
    | Sum.inr w₂ => w₂.1
  invFun w :=
    if hw : w ∈ C then
      Sum.inl ⟨Sum.inr ⟨w, hw⟩, fun h => by cases h⟩
    else
      Sum.inr ⟨w, hw⟩
  left_inv z := by
    rcases z with ⟨x | ⟨w₁, hw₁⟩, hne⟩ | ⟨w₂, hw₂⟩
    · exact False.elim (empty_fin2_ne_zero_ne_one x (fun h => hne (congrArg Sum.inl h)))
    · dsimp; rw [dif_pos hw₁]
    · dsimp; rw [dif_neg hw₂]
  right_inv w := by
    by_cases hw : w ∈ C <;> simp [hw]
  map_rel_iff' := by
    rintro (⟨x | ⟨w₁, hw₁⟩, hne₁⟩ | ⟨w₂, hw₂⟩)
           (⟨y | ⟨v₁, hv₁⟩, hne₂⟩ | ⟨v₂, hv₂⟩)
    · exact False.elim (empty_fin2_ne_zero_ne_one x (fun h => hne₁ (congrArg Sum.inl h)))
    · exact False.elim (empty_fin2_ne_zero_ne_one x (fun h => hne₁ (congrArg Sum.inl h)))
    · exact False.elim (empty_fin2_ne_zero_ne_one x (fun h => hne₁ (congrArg Sum.inl h)))
    · exact False.elim (empty_fin2_ne_zero_ne_one y (fun h => hne₂ (congrArg Sum.inl h)))
    · rfl
    · dsimp [substGraph]
      exact ⟨fun h => False.elim (h_anti w₁ hw₁ v₂ hv₂ h), False.elim⟩
    · exact False.elim (empty_fin2_ne_zero_ne_one y (fun h => hne₂ (congrArg Sum.inl h)))
    · dsimp [substGraph]
      exact ⟨fun h => False.elim (h_anti v₁ hv₁ w₂ hw₂ h.symm), False.elim⟩
    · rfl

/-- **`InHClosureBNew` Anticomplete Partition Closure**: if $W = C \sqcup (W \setminus C)$ with no edges across $(C, W \setminus C)$
and both $G[C]$ and $G[W \setminus C]$ lie in `InHClosureBNew`, then $G \in \mathcal{H}(\mathcal{B}_{\mathrm{new}}^*)$. -/
theorem inHClosureBNew_of_anticomplete_split {W : Type} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) (C : Finset W)
    (h_anti : ∀ x ∈ C, ∀ y ∉ C, ¬G.Adj x y)
    (h₁ : InHClosureBNew (G.comap (Subtype.val : {w : W // w ∈ C} → W)))
    (h₂ : InHClosureBNew (G.comap (Subtype.val : {w : W // w ∉ C} → W))) :
    InHClosureBNew G :=
  inHClosureBNew_of_iso (anticompleteSplitIso G C h_anti)
    (inHClosureBNew_subst (Sum.inl ⟨1, by decide⟩)
      (inHClosureBNew_subst 0 inHClosureBNew_bot_fin2 h₁) h₂)

private theorem walk_adj_of_length_eq_one {W₀ : Type} {H₀ : SimpleGraph W₀} {a b : W₀} :
    ∀ (q : H₀.Walk a b), q.length = 1 → H₀.Adj a b
  | .nil, h => by simp at h
  | .cons hadj .nil, _ => hadj
  | .cons _ (.cons _ _), h => by simp at h

private theorem walk_comap_injective {W : Type} {P : W → Prop} {G : SimpleGraph W}
    {x y : Subtype P} :
    Function.Injective (Walk.map ({ toFun := Subtype.val, map_rel' := fun {_ _} h => h } : G.comap Subtype.val →g G) :
      (G.comap Subtype.val).Walk x y → G.Walk x.1 y.1) := by
  intro q₁ q₂ h
  induction q₁ with
  | nil =>
      cases q₂ with
      | nil => rfl
      | cons _ _ => simp at h
  | @cons a b c h₁ q₁' ih =>
      cases q₂ with
      | nil => simp at h
      | @cons _ b' _ h₂ q₂' =>
          simp only [Walk.map_cons, Walk.cons.injEq] at h
          obtain ⟨hb, hq⟩ := h
          have hb' : b = b' := Subtype.ext hb
          subst hb'
          exact congrArg (Walk.cons h₁) (ih (eq_of_heq hq))

private theorem injective_of_univ_image_card_eq {A B : Type} [Fintype A] [DecidableEq B]
    (f : A → B) (h : (Finset.univ.image f).card = Fintype.card A) : Function.Injective f := by
  have hinj : Set.InjOn f (Finset.univ : Finset A) :=
    Finset.injOn_of_card_image_eq (by rw [h, Finset.card_univ])
  intro x y hxy
  exact hinj (Finset.mem_univ x) (Finset.mem_univ y) hxy

/-- **Universal Tree Isomorphism Lemma (`isoOfConnectedHomToAcyclic`)**:
Any injective graph homomorphism $f : W_0 \to W$ from a connected graph $H_0$ to an acyclic graph $T$
with $|W_0| = |W|$ is automatically a graph isomorphism $H_0 \simeq_g T$. -/
noncomputable def isoOfConnectedHomToAcyclic {W₀ W : Type} [Fintype W₀] [DecidableEq W₀]
    [Fintype W] [DecidableEq W]
    {H₀ : SimpleGraph W₀} {T : SimpleGraph W}
    (hH₀ : H₀.Connected) (hT : T.IsAcyclic) (hcard : Fintype.card W₀ = Fintype.card W)
    (f : W₀ → W) (hf_inj : Function.Injective f)
    (hf_hom : ∀ a b : W₀, H₀.Adj a b → T.Adj (f a) (f b)) : H₀ ≃g T :=
  let f_hom : H₀ →g T := { toFun := f, map_rel' := @hf_hom }
  { toEquiv := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf_inj, hcard⟩)
    map_rel_iff' := by
      intro a b
      simp only [Equiv.ofBijective_apply]
      refine ⟨?_, hf_hom a b⟩
      intro hadj
      obtain ⟨w₀⟩ := hH₀.preconnected a b
      let p₂ : T.Walk (f a) (f b) := Walk.map f_hom w₀.toPath.1
      have hp₂ : p₂.IsPath := Walk.IsPath.mk' (by
        rw [Walk.support_map]
        exact w₀.toPath.2.support_nodup.map hf_inj)
      let p₁ : T.Walk (f a) (f b) := Walk.cons hadj Walk.nil
      have hp₁ : p₁.IsPath := Walk.IsPath.mk' (by
        have hne : f a ≠ f b := T.ne_of_adj hadj
        simp [p₁, hne])
      have hp_eq : p₂ = p₁ :=
        congrArg Subtype.val ((SimpleGraph.isAcyclic_iff_path_unique.mp hT) ⟨p₂, hp₂⟩ ⟨p₁, hp₁⟩)
      have hlen : w₀.toPath.1.length = 1 := by
        simpa [p₂, p₁] using congrArg Walk.length hp_eq
      exact walk_adj_of_length_eq_one w₀.toPath.1 hlen }

/-- No triangles in an acyclic graph $T$. -/
theorem acyclic_no_triangle {W : Type} [DecidableEq W] {T : SimpleGraph W}
    (hT : T.IsAcyclic) {a b c : W} (hab : T.Adj a b) (hbc : T.Adj b c) : ¬T.Adj a c := by
  intro hac
  have h_ab : a ≠ b := T.ne_of_adj hab
  have h_bc : b ≠ c := T.ne_of_adj hbc
  have h_ac : a ≠ c := T.ne_of_adj hac
  let p₁ : T.Walk a c := Walk.cons hac Walk.nil
  have hp₁ : p₁.IsPath := Walk.IsPath.mk' (by simp [p₁, h_ac])
  let p₂ : T.Walk a c := Walk.cons hab (Walk.cons hbc Walk.nil)
  have hp₂ : p₂.IsPath := Walk.IsPath.mk' (by simp [p₂, h_ab, h_bc, h_ac])
  have hp_eq : p₂ = p₁ :=
    congrArg Subtype.val ((SimpleGraph.isAcyclic_iff_path_unique.mp hT) ⟨p₂, hp₂⟩ ⟨p₁, hp₁⟩)
  have hlen := congrArg Walk.length hp_eq
  simp [p₁, p₂] at hlen

/-- No 4-cycles in an acyclic graph $T$. -/
theorem acyclic_no_quad {W : Type} [DecidableEq W] {T : SimpleGraph W}
    (hT : T.IsAcyclic) {a b c d : W} (hac : a ≠ c) (hbd : b ≠ d)
    (hab : T.Adj a b) (hbc : T.Adj b c) (hcd : T.Adj c d) : ¬T.Adj a d := by
  intro had
  have h_ab : a ≠ b := T.ne_of_adj hab
  have h_bc : b ≠ c := T.ne_of_adj hbc
  have h_cd : c ≠ d := T.ne_of_adj hcd
  have h_ad : a ≠ d := T.ne_of_adj had
  let p₁ : T.Walk a d := Walk.cons had Walk.nil
  have hp₁ : p₁.IsPath := Walk.IsPath.mk' (by simp [p₁, h_ad])
  let p₂ : T.Walk a d := Walk.cons hab (Walk.cons hbc (Walk.cons hcd Walk.nil))
  have hp₂ : p₂.IsPath := Walk.IsPath.mk' (by simp [p₂, h_ab, h_bc, h_cd, h_ad, hac, hbd])
  have hp_eq : p₂ = p₁ :=
    congrArg Subtype.val ((SimpleGraph.isAcyclic_iff_path_unique.mp hT) ⟨p₂, hp₂⟩ ⟨p₁, hp₁⟩)
  have hlen := congrArg Walk.length hp_eq
  simp [p₁, p₂] at hlen

/-- Deleting a degree-1 leaf $v$ (unique neighbor $p$) from a tree $T$ produces a tree $T - v$. -/
theorem isTree_delete_leaf {W : Type} [DecidableEq W] {T : SimpleGraph W}
    (hT : T.IsTree) {v p : W} (hleaf : ∀ w : W, T.Adj v w ↔ w = p) :
    (T.comap (Subtype.val : {w : W // w ≠ v} → W)).IsTree := by
  let W' := {w : W // w ≠ v}
  let T' := T.comap (Subtype.val : W' → W)
  have hpv : p ≠ v := fun h => T.loopless v (h ▸ (hleaf p).mpr rfl)
  have h_no_visit : ∀ {a b : W} (q : T.Walk a b),
      q.IsPath → a ≠ v → b ≠ v → v ∉ q.support := by
    intro a b q hq ha hb
    induction q with
    | nil =>
        simp [ha.symm]
    | @cons x y z h_xy q' ih =>
        by_cases hy : y = v
        · subst hy
          have hxp : x = p := (hleaf x).mp h_xy.symm
          subst hxp
          cases q' with
          | nil => exact False.elim (hb rfl)
          | @cons _ w _ h_vw q'' =>
              have hwp : w = x := (hleaf w).mp h_vw
              subst hwp
              have hnodup := hq.support_nodup
              simp at hnodup
        · have hnot : v ∉ q'.support := ih hq.of_cons hy hb
          simp [ha.symm, hnot]
  have h_lift : ∀ {a b : W} (q : T.Walk a b) (ha : a ≠ v) (hb : b ≠ v),
      (∀ z ∈ q.support, z ≠ v) → Nonempty (T'.Walk ⟨a, ha⟩ ⟨b, hb⟩) := by
    intro a b q ha hb hsup
    induction q with
    | nil => exact ⟨Walk.nil⟩
    | @cons x y z h_xy q' ih =>
        have hy : y ≠ v := hsup y (by simp)
        have hsup' : ∀ w ∈ q'.support, w ≠ v :=
          fun w hw => hsup w (by simp [hw])
        obtain ⟨q'_lift⟩ := ih hy hb hsup'
        exact ⟨@Walk.cons W' T' ⟨x, ha⟩ ⟨y, hy⟩ ⟨z, hb⟩ h_xy q'_lift⟩
  haveI : Nonempty W' := ⟨⟨p, hpv⟩⟩
  refine ⟨SimpleGraph.Connected.mk fun x y => ?_, ?_⟩
  · obtain ⟨w₀⟩ := hT.1.preconnected x.1 y.1
    let q : T.Walk x.1 y.1 := w₀.toPath.1
    have hnot : v ∉ q.support := h_no_visit q w₀.toPath.2 x.2 y.2
    exact h_lift q x.2 y.2 (fun z hz hzv => hnot (hzv ▸ hz))
  · rw [SimpleGraph.isAcyclic_iff_path_unique]
    intro x y ⟨q₁, hq₁⟩ ⟨q₂, hq₂⟩
    apply Subtype.ext
    let f_hom : T' →g T := { toFun := Subtype.val, map_rel' := fun {_ _} h => h }
    let p₁ : T.Walk x.1 y.1 := Walk.map f_hom q₁
    let p₂ : T.Walk x.1 y.1 := Walk.map f_hom q₂
    have hp₁ : p₁.IsPath := Walk.IsPath.mk' (by rw [Walk.support_map]; exact hq₁.support_nodup.map Subtype.val_injective)
    have hp₂ : p₂.IsPath := Walk.IsPath.mk' (by rw [Walk.support_map]; exact hq₂.support_nodup.map Subtype.val_injective)
    have hp_eq : p₁ = p₂ :=
      congrArg Subtype.val ((SimpleGraph.isAcyclic_iff_path_unique.mp hT.2) ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩)
    exact walk_comap_injective hp_eq

/-- Every non-trivial finite tree ($|W| \ge 2$) possesses at least one leaf $v_0$ with a unique neighbor $p_0$. -/
theorem tree_exists_leaf_of_card_ge_two {W : Type} [Fintype W] [DecidableEq W]
    {T : SimpleGraph W} (hT : T.IsTree) (hcard : 2 ≤ Fintype.card W) :
    ∃ v₀ p₀ : W, ∀ w : W, T.Adj v₀ w ↔ w = p₀ := by
  haveI : Nonempty W := hT.1.nonempty
  let pathFn : W × W → Σ x y : W, T.Walk x y :=
    fun p => ⟨p.1, p.2, (hT.1.preconnected p.1 p.2).some.toPath.1⟩
  obtain ⟨p_max, _, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (W × W)) (fun p => (pathFn p).2.2.length) Finset.univ_nonempty
  let x₀ := p_max.1
  let y₀ := p_max.2
  let P : T.Walk x₀ y₀ := (pathFn p_max).2.2
  have hP_path : P.IsPath := (hT.1.preconnected x₀ y₀).some.toPath.2
  have hP_pos : 1 ≤ P.length := by
    obtain ⟨z, hz⟩ : ∃ z : W, z ≠ x₀ := by
      have hne : 1 ≤ Fintype.card {w : W // w ≠ x₀} := by rw [card_subtype_ne x₀]; omega
      obtain ⟨⟨z, hz⟩⟩ := Fintype.card_pos_iff.mp hne
      exact ⟨z, hz⟩
    have hlen_z : 1 ≤ (pathFn (x₀, z)).2.2.length := by
      cases hq : (pathFn (x₀, z)).2.2 with
      | nil => exact False.elim (hz rfl)
      | cons _ _ => simp
    exact le_trans hlen_z (hmax (x₀, z) (Finset.mem_univ _))
  have h_extract : ∀ (y : W) (Q : T.Walk y x₀), Q.IsPath → Q.length = P.length →
      ∃ v₀ p₀ : W, ∀ w : W, T.Adj v₀ w ↔ w = p₀ := by
    intro y Q hQp hQlen
    cases Q with
    | nil => simp at hQlen; omega
    | @cons y p₀ _ h_yp Q' =>
        refine ⟨y, p₀, fun w => ⟨?_, fun h => h ▸ h_yp⟩⟩
        intro h_yw
        by_contra hwp
        by_cases hw_mem : w ∈ (Walk.cons h_yp Q').support
        · have hw_ne_y : w ≠ y := fun h => T.loopless y (h ▸ h_yw)
          have hw_Q' : w ∈ Q'.support := by
            simp only [Walk.support_cons, List.mem_cons] at hw_mem
            rcases hw_mem with rfl | hw'
            · exact False.elim (hw_ne_y rfl)
            · exact hw'
          let sub : T.Walk p₀ w := Q'.takeUntil w hw_Q'
          have hsub_path : sub.IsPath := hQp.of_cons.takeUntil hw_Q'
          have hsub_pos : 1 ≤ sub.length := by
            cases hsub : sub with
            | nil => exact False.elim (hwp rfl)
            | cons _ _ => simp
          let p₁ : T.Walk y w := Walk.cons h_yw Walk.nil
          have hp₁ : p₁.IsPath := Walk.IsPath.mk' (by simp [p₁, hw_ne_y.symm])
          let p₂ : T.Walk y w := Walk.cons h_yp sub
          have hp₂ : p₂.IsPath := Walk.IsPath.cons hsub_path (by
            intro hy_sub
            have hy_Q' : y ∈ Q'.support := Walk.support_takeUntil_subset Q' hw_Q' hy_sub
            have hnodup := hQp.support_nodup
            rw [Walk.support_cons, List.nodup_cons] at hnodup
            exact hnodup.1 hy_Q')
          have hp_eq : p₂ = p₁ :=
            congrArg Subtype.val ((SimpleGraph.isAcyclic_iff_path_unique.mp hT.2) ⟨p₂, hp₂⟩ ⟨p₁, hp₁⟩)
          have hlen := congrArg Walk.length hp_eq
          simp only [p₁, p₂, Walk.length_cons, Walk.length_nil] at hlen
          omega
        · let Q_ext : T.Walk w x₀ := Walk.cons h_yw.symm (Walk.cons h_yp Q')
          have hQ_ext_path : Q_ext.IsPath := Walk.IsPath.cons hQp hw_mem
          have h_unique : (pathFn (w, x₀)).2.2 = Q_ext :=
            congrArg Subtype.val ((SimpleGraph.isAcyclic_iff_path_unique.mp hT.2)
              ⟨(pathFn (w, x₀)).2.2, (hT.1.preconnected w x₀).some.toPath.2⟩
              ⟨Q_ext, hQ_ext_path⟩)
          have hle := hmax (w, x₀) (Finset.mem_univ _)
          rw [h_unique] at hle
          have hlen_ext : Q_ext.length = Q'.length + 2 := by simp [Q_ext]
          have hlen_q : (Walk.cons h_yp Q').length = Q'.length + 1 := by simp
          rw [hlen_q] at hQlen
          rw [hlen_ext] at hle
          dsimp [P] at hQlen
          omega
  exact h_extract y₀ P.reverse hP_path.reverse (Walk.length_reverse P)

/-- Connectedness of `pathGraph n` for $n \ge 1$. -/
theorem pathGraph_connected (n : ℕ) (hn : 1 ≤ n) : (pathGraph n).Connected := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hwalk0 : ∀ (m : ℕ) (hm : m < n), Nonempty ((pathGraph n).Walk ⟨0, hn⟩ ⟨m, hm⟩) := by
    intro m
    induction m with
    | zero => intro hm; exact ⟨Walk.nil⟩
    | succ m ih =>
        intro hm
        obtain ⟨w⟩ := ih (by omega)
        have hadj : (pathGraph n).Adj ⟨m, by omega⟩ ⟨m + 1, hm⟩ :=
          pathGraph_adj.mpr (by dsimp; omega)
        exact ⟨w.concat hadj⟩
  refine SimpleGraph.Connected.mk fun i j => ?_
  obtain ⟨wi⟩ := hwalk0 i.1 i.2
  obtain ⟨wj⟩ := hwalk0 j.1 j.2
  exact ⟨wi.reverse.append wj⟩

/-- Every tree $T$ with maximum degree $\le 2$ is isomorphic to `pathGraph (Fintype.card W)`. -/
theorem tree_iso_pathGraph_of_max_deg_le_two {W : Type} [Fintype W] [DecidableEq W] [Nonempty W]
    {T : SimpleGraph W} (hT : T.IsTree)
    (hdeg : ∀ v : W, (neighborFinsetIn T v Finset.univ).card ≤ 2) :
    Nonempty (pathGraph (Fintype.card W) ≃g T) := by
  have h_aux : ∀ (n : ℕ) {U : Type} [Fintype U] [DecidableEq U] [Nonempty U] (G : SimpleGraph U),
      Fintype.card U = n → G.IsTree →
      (∀ v : U, (neighborFinsetIn G v Finset.univ).card ≤ 2) →
      Nonempty (pathGraph n ≃g G) := by
    intro n
    induction n with
    | zero =>
        intro U _ _ _ _ hcard
        exact False.elim (by have := Fintype.card_pos (α := U); omega)
    | succ m ih =>
        intro U _ _ _ G hcard hG hdegG
        by_cases hm0 : m = 0
        · subst hm0
          let e := Fintype.equivFinOfCardEq hcard
          exact ⟨isoOfConnectedHomToAcyclic (pathGraph_connected 1 le_rfl) hG.2 hcard.symm e.symm e.symm.injective
            (by intro a b h; have : a = b := Fin.ext (by omega); subst this; exact False.elim ((pathGraph 1).loopless a h))⟩
        · have hcard2 : 2 ≤ Fintype.card U := by omega
          obtain ⟨v₀, p₀, hleaf⟩ := tree_exists_leaf_of_card_ge_two hG hcard2
          let U' := {w : U // w ≠ v₀}
          let G' := G.comap (Subtype.val : U' → U)
          have hpv : p₀ ≠ v₀ := fun h => G.loopless v₀ (h ▸ (hleaf p₀).mpr rfl)
          have hcard' : Fintype.card U' = m := by rw [card_subtype_ne v₀]; omega
          haveI : Nonempty U' := ⟨⟨p₀, hpv⟩⟩
          have hdeg' : ∀ u : U', (neighborFinsetIn G' u Finset.univ).card ≤ 2 := by
            intro u
            have hsub : (neighborFinsetIn G' u Finset.univ).map ⟨Subtype.val, Subtype.val_injective⟩ ⊆
                neighborFinsetIn G u.1 Finset.univ := by
              intro x hx
              rcases Finset.mem_map.mp hx with ⟨w, hw, rfl⟩
              rw [mem_neighborFinsetIn_iff] at hw ⊢
              exact ⟨Finset.mem_univ _, hw.2⟩
            calc (neighborFinsetIn G' u Finset.univ).card
                = ((neighborFinsetIn G' u Finset.univ).map ⟨Subtype.val, Subtype.val_injective⟩).card :=
                  (Finset.card_map _).symm
              _ ≤ (neighborFinsetIn G u.1 Finset.univ).card := Finset.card_le_card hsub
              _ ≤ 2 := hdegG u.1
          obtain ⟨e'⟩ := ih G' hcard' (isTree_delete_leaf hG hleaf) hdeg'
          let k₀ : Fin m := e'.symm ⟨p₀, hpv⟩
          have hk₀_end : k₀.1 = 0 ∨ k₀.1 = m - 1 := by
            by_contra hk_int
            push_neg at hk_int
            let a : U' := e' ⟨k₀.1 - 1, by omega⟩
            let b : U' := e' ⟨k₀.1 + 1, by omega⟩
            have hadj_a : G.Adj p₀ a.1 := by
              have : G'.Adj (e' k₀) a := e'.map_rel_iff.mpr (pathGraph_adj.mpr (by dsimp [a]; omega))
              simpa [k₀] using this
            have hadj_b : G.Adj p₀ b.1 := by
              have : G'.Adj (e' k₀) b := e'.map_rel_iff.mpr (pathGraph_adj.mpr (by dsimp [b]; omega))
              simpa [k₀] using this
            have hab_ne : a.1 ≠ b.1 := fun h => by
              have : (⟨k₀.1 - 1, by omega⟩ : Fin m) = ⟨k₀.1 + 1, by omega⟩ :=
                e'.injective (Subtype.ext h)
              have := congrArg Fin.val this; dsimp at this; omega
            have hsub3 : ({v₀, a.1, b.1} : Finset U) ⊆ neighborFinsetIn G p₀ Finset.univ := by
              intro z hz
              rw [mem_neighborFinsetIn_iff]
              refine ⟨Finset.mem_univ _, ?_⟩
              rcases Finset.mem_insert.mp hz with rfl | hz'
              · exact ((hleaf p₀).mpr rfl).symm
              · rcases Finset.mem_insert.mp hz' with rfl | hz''
                · exact hadj_a
                · rw [Finset.mem_singleton.mp hz'']; exact hadj_b
            have hcard3 : ({v₀, a.1, b.1} : Finset U).card = 3 := by
              rw [Finset.card_insert_of_notMem (by simp [a.2.symm, b.2.symm]),
                  Finset.card_pair hab_ne]
            have hle3 := Finset.card_le_card hsub3
            rw [hcard3] at hle3
            have := hdegG p₀; omega
          rcases hk₀_end with hk0 | hkm
          · let f : Fin (m + 1) → U := fun i =>
              if i.1 = 0 then v₀ else (e' ⟨i.1 - 1, by omega⟩).1
            have hf_inj : Function.Injective f := by
              intro i j hij
              dsimp only [f] at hij
              split_ifs at hij with hi hj hj
              · exact Fin.ext (by omega)
              · exact False.elim ((e' _).2 hij.symm)
              · exact False.elim ((e' _).2 hij)
              · have h_eq := e'.injective (Subtype.ext hij)
                exact Fin.ext (by have := congrArg Fin.val h_eq; dsimp at this; omega)
            have hf_hom : ∀ i j : Fin (m + 1), (pathGraph (m + 1)).Adj i j → G.Adj (f i) (f j) := by
              intro i j hadj
              have := i.2; have := j.2
              rw [pathGraph_adj] at hadj
              dsimp only [f]
              split_ifs with hi hj hj
              · omega
              · have hj1 : j.1 - 1 = k₀.1 := by omega
                have hk_eq : (⟨j.1 - 1, by omega⟩ : Fin m) = k₀ := Fin.ext hj1
                rw [hk_eq]
                have he_eq : (e' k₀).1 = p₀ := by simp [k₀]
                rw [he_eq]
                exact (hleaf p₀).mpr rfl
              · have hi1 : i.1 - 1 = k₀.1 := by omega
                have hk_eq : (⟨i.1 - 1, by omega⟩ : Fin m) = k₀ := Fin.ext hi1
                rw [hk_eq]
                have he_eq : (e' k₀).1 = p₀ := by simp [k₀]
                rw [he_eq]
                exact ((hleaf p₀).mpr rfl).symm
              · exact e'.map_rel_iff.mpr (pathGraph_adj.mpr (by dsimp; omega))
            exact ⟨isoOfConnectedHomToAcyclic (pathGraph_connected (m + 1) (by omega)) hG.2
              (by rw [Fintype.card_fin, hcard]) f hf_inj hf_hom⟩
          · let f : Fin (m + 1) → U := fun i =>
              if hi : i.1 < m then (e' ⟨i.1, hi⟩).1 else v₀
            have hf_inj : Function.Injective f := by
              intro i j hij
              have := i.2; have := j.2
              dsimp only [f] at hij
              split_ifs at hij with hi hj hj
              · have h_eq := e'.injective (Subtype.ext hij)
                exact Fin.ext (by simpa using congrArg Fin.val h_eq)
              · exact False.elim ((e' _).2 hij)
              · exact False.elim ((e' _).2 hij.symm)
              · exact Fin.ext (by omega)
            have hf_hom : ∀ i j : Fin (m + 1), (pathGraph (m + 1)).Adj i j → G.Adj (f i) (f j) := by
              intro i j hadj
              have hi_lt := i.2; have hj_lt := j.2
              rw [pathGraph_adj] at hadj
              dsimp only [f]
              split_ifs with hi hj hj
              · exact e'.map_rel_iff.mpr (pathGraph_adj.mpr (by dsimp; omega))
              · have hik : i.1 = k₀.1 := by omega
                have hk_eq : (⟨i.1, hi⟩ : Fin m) = k₀ := Fin.ext hik
                rw [hk_eq]
                have he_eq : (e' k₀).1 = p₀ := by simp [k₀]
                rw [he_eq]
                exact ((hleaf p₀).mpr rfl).symm
              · have hjk : j.1 = k₀.1 := by omega
                have hk_eq : (⟨j.1, hj⟩ : Fin m) = k₀ := Fin.ext hjk
                rw [hk_eq]
                have he_eq : (e' k₀).1 = p₀ := by simp [k₀]
                rw [he_eq]
                exact (hleaf p₀).mpr rfl
              · omega
            exact ⟨isoOfConnectedHomToAcyclic (pathGraph_connected (m + 1) (by omega)) hG.2
              (by rw [Fintype.card_fin, hcard]) f hf_inj hf_hom⟩
  exact h_aux (Fintype.card W) T rfl hT hdeg

/-- Connectedness of `SpiderGraph d` for all $d \ge 1$. -/
theorem spiderGraph_connected (d : ℕ) (hd : 1 ≤ d) : (SpiderGraph d).Connected := by
  haveI : Nonempty (Fin (d + 4)) := ⟨0⟩
  have hwalk0 : ∀ (m : ℕ) (hm : m < d + 4), Nonempty ((SpiderGraph d).Walk 0 ⟨m, hm⟩) := by
    intro m
    induction m with
    | zero => intro _; exact ⟨Walk.nil⟩
    | succ m ih =>
        intro hm
        rcases eq_or_ne m 0 with rfl | hm0
        · exact ⟨Walk.cons (by dsimp [SpiderGraph, spiderAdjLt]; simp) Walk.nil⟩
        · rcases eq_or_ne m 1 with rfl | hm1
          · exact ⟨Walk.cons (by dsimp [SpiderGraph, spiderAdjLt]; simp) Walk.nil⟩
          · rcases eq_or_ne m 2 with rfl | hm2
            · have hadj02 : (SpiderGraph d).Adj 0 ⟨2, by omega⟩ := by
                dsimp [SpiderGraph, spiderAdjLt]; simp
              have hadj23 : (SpiderGraph d).Adj ⟨2, by omega⟩ ⟨3, hm⟩ := by
                dsimp [SpiderGraph, spiderAdjLt]; simp
              exact ⟨Walk.cons hadj02 (Walk.cons hadj23 Walk.nil)⟩
            · rcases eq_or_ne m 3 with rfl | hm3
              · exact ⟨Walk.cons (by dsimp [SpiderGraph, spiderAdjLt]; simp) Walk.nil⟩
              · obtain ⟨w⟩ := ih (by omega)
                have hadj : (SpiderGraph d).Adj ⟨m, by omega⟩ ⟨m + 1, hm⟩ := by
                  dsimp [SpiderGraph, spiderAdjLt]
                  rw [if_pos (by omega : m < m + 1)]
                  simp [show 4 ≤ m by omega]
                exact ⟨w.concat hadj⟩
  refine SimpleGraph.Connected.mk fun i j => ?_
  obtain ⟨wi⟩ := hwalk0 i.1 i.2
  obtain ⟨wj⟩ := hwalk0 j.1 j.2
  exact ⟨wi.reverse.append wj⟩

/-- Connectedness of `SubdividedClawGraph`. -/
theorem subdividedClawGraph_connected : SubdividedClawGraph.Connected := by
  haveI : Nonempty (Fin 7) := ⟨0⟩
  have hwalk0 : ∀ v : Fin 7, Nonempty (SubdividedClawGraph.Walk 0 v) := by
    intro v
    fin_cases v
    · exact ⟨Walk.nil⟩
    · exact ⟨Walk.cons (by decide) Walk.nil⟩
    · exact ⟨Walk.cons (v := (1 : Fin 7)) (by decide) (Walk.cons (by decide) Walk.nil)⟩
    · exact ⟨Walk.cons (by decide) Walk.nil⟩
    · exact ⟨Walk.cons (v := (3 : Fin 7)) (by decide) (Walk.cons (by decide) Walk.nil)⟩
    · exact ⟨Walk.cons (by decide) Walk.nil⟩
    · exact ⟨Walk.cons (v := (5 : Fin 7)) (by decide) (Walk.cons (by decide) Walk.nil)⟩
  refine SimpleGraph.Connected.mk fun i j => ?_
  obtain ⟨wi⟩ := hwalk0 i
  obtain ⟨wj⟩ := hwalk0 j
  exact ⟨wi.reverse.append wj⟩

/-- Auxiliary 7-vertex fork tree `ForkGraph` on `Fin 7` (`0 = c`, `1 = u₁`, `2 = u₂`, `3 = w₂`, `4 = z`, `5 = u₃`, `6 = w₃`),
isomorphic to `substGraph (SpiderGraph 2) ⟨3, _⟩ (⊥ : SimpleGraph (Fin 2))`. -/
def ForkGraph : SimpleGraph (Fin 7) where
  Adj u v :=
    (u = 0 ∧ (v = 1 ∨ v = 2 ∨ v = 5)) ∨
    ((u = 1 ∨ u = 2 ∨ u = 5) ∧ v = 0) ∨
    (u = 2 ∧ (v = 3 ∨ v = 4)) ∨
    ((u = 3 ∨ u = 4) ∧ v = 2) ∨
    (u = 5 ∧ v = 6) ∨ (u = 6 ∧ v = 5)
  symm _ _ := by tauto
  loopless u := by fin_cases u <;> decide

instance instDecidableRelForkGraphAdj : DecidableRel ForkGraph.Adj := by
  intro u v; dsimp [ForkGraph]; infer_instance

/-- Connectedness of `ForkGraph`. -/
theorem forkGraph_connected : ForkGraph.Connected := by
  haveI : Nonempty (Fin 7) := ⟨0⟩
  have hwalk0 : ∀ v : Fin 7, Nonempty (ForkGraph.Walk 0 v) := by
    intro v
    fin_cases v
    · exact ⟨Walk.nil⟩
    · exact ⟨Walk.cons (by decide) Walk.nil⟩
    · exact ⟨Walk.cons (by decide) Walk.nil⟩
    · exact ⟨Walk.cons (v := (2 : Fin 7)) (by decide) (Walk.cons (by decide) Walk.nil)⟩
    · exact ⟨Walk.cons (v := (2 : Fin 7)) (by decide) (Walk.cons (by decide) Walk.nil)⟩
    · exact ⟨Walk.cons (by decide) Walk.nil⟩
    · exact ⟨Walk.cons (v := (5 : Fin 7)) (by decide) (Walk.cons (by decide) Walk.nil)⟩
  refine SimpleGraph.Connected.mk fun i j => ?_
  obtain ⟨wi⟩ := hwalk0 i
  obtain ⟨wj⟩ := hwalk0 j
  exact ⟨wi.reverse.append wj⟩

/-- Explicit isomorphism `substGraph (SpiderGraph 2) ⟨3, _⟩ (⊥ : SimpleGraph (Fin 2)) ≃g ForkGraph`. -/
def substSpider2IsoForkGraph :
    substGraph (SpiderGraph 2) ⟨3, by decide⟩ (⊥ : SimpleGraph (Fin 2)) ≃g ForkGraph where
  toFun s :=
    match s with
    | Sum.inl ⟨0, _⟩ => 0
    | Sum.inl ⟨1, _⟩ => 1
    | Sum.inl ⟨2, _⟩ => 2
    | Sum.inl ⟨3, h⟩ => False.elim (h rfl)
    | Sum.inl ⟨4, _⟩ => 5
    | Sum.inl ⟨5, _⟩ => 6
    | Sum.inr 0 => 3
    | Sum.inr 1 => 4
  invFun i :=
    match i with
    | 0 => Sum.inl ⟨0, by decide⟩
    | 1 => Sum.inl ⟨1, by decide⟩
    | 2 => Sum.inl ⟨2, by decide⟩
    | 3 => Sum.inr 0
    | 4 => Sum.inr 1
    | 5 => Sum.inl ⟨4, by decide⟩
    | 6 => Sum.inl ⟨5, by decide⟩
  left_inv := by rintro (⟨i, hi⟩ | i) <;> fin_cases i <;> first | rfl | exact False.elim (hi rfl)
  right_inv := fun i => by fin_cases i <;> rfl
  map_rel_iff' := by
    rintro (⟨i, hi⟩ | i) (⟨j, hj⟩ | j)
    · fin_cases i <;> fin_cases j <;> decide +revert
    · fin_cases i <;> fin_cases j <;> decide +revert
    · fin_cases i <;> fin_cases j <;> decide +revert
    · fin_cases i <;> fin_cases j <;> decide +revert

private theorem spiderGraph2_adj_cases {i j : Fin 6} (h : (SpiderGraph 2).Adj i j) :
    (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
    (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨
    (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨
    (i = 0 ∧ j = 4) ∨ (i = 4 ∧ j = 0) ∨
    (i = 4 ∧ j = 5) ∨ (i = 5 ∧ j = 4) := by
  fin_cases i <;> fin_cases j <;> simp_all [SpiderGraph, spiderAdjLt]

private theorem spiderGraph3_adj_cases {i j : Fin 7} (h : (SpiderGraph 3).Adj i j) :
    (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
    (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨
    (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨
    (i = 0 ∧ j = 4) ∨ (i = 4 ∧ j = 0) ∨
    (i = 4 ∧ j = 5) ∨ (i = 5 ∧ j = 4) ∨
    (i = 5 ∧ j = 6) ∨ (i = 6 ∧ j = 5) := by
  fin_cases i <;> fin_cases j <;> simp_all [SpiderGraph, spiderAdjLt]

private theorem subdividedClaw_adj_cases {i j : Fin 7} (h : SubdividedClawGraph.Adj i j) :
    (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
    (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
    (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) ∨
    (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) ∨
    (i = 0 ∧ j = 5) ∨ (i = 5 ∧ j = 0) ∨
    (i = 5 ∧ j = 6) ∨ (i = 6 ∧ j = 5) := by
  fin_cases i <;> fin_cases j <;> simp_all [SubdividedClawGraph]

private theorem forkGraph_adj_cases {i j : Fin 7} (h : ForkGraph.Adj i j) :
    (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
    (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨
    (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨
    (i = 2 ∧ j = 4) ∨ (i = 4 ∧ j = 2) ∨
    (i = 0 ∧ j = 5) ∨ (i = 5 ∧ j = 0) ∨
    (i = 5 ∧ j = 6) ∨ (i = 6 ∧ j = 5) := by
  fin_cases i <;> fin_cases j <;> simp_all [ForkGraph]

/-- **Twin-Leaf-Free Branch Counting & Center Classification (`twinLeafFree_center_classification`)**:
Let $T$ be a finite tree with no twin leaves (`∀ u v : W, u ≠ v → deg(u) = 1 → deg(v) = 1 → ∀ p, T.Adj u p → ¬T.Adj v p`),
and let $c \in W$ have degree $d = \deg_T(c) \ge 3$. Then:
1. $6 \le |W|$;
2. If $|W| = 6$, then `Nonempty (SpiderGraph 2 ≃g T)`;
3. If $|W| = 7$, then either `Nonempty (SubdividedClawGraph ≃g T)`, `Nonempty (SpiderGraph 3 ≃g T)`,
   or `Nonempty (ForkGraph ≃g T)`. -/
theorem twinLeafFree_center_classification {W : Type} [Fintype W] [DecidableEq W]
    {T : SimpleGraph W} (hT : T.IsTree)
    (h_no_twins : ∀ u v : W, u ≠ v →
      (neighborFinsetIn T u Finset.univ).card = 1 →
      (neighborFinsetIn T v Finset.univ).card = 1 →
      ∀ p : W, T.Adj u p → ¬T.Adj v p)
    {c : W} (hc_deg : 3 ≤ (neighborFinsetIn T c Finset.univ).card) :
    6 ≤ Fintype.card W ∧
    (Fintype.card W = 6 → Nonempty (SpiderGraph 2 ≃g T)) ∧
    (Fintype.card W = 7 →
      Nonempty (SubdividedClawGraph ≃g T) ∨
      Nonempty (SpiderGraph 3 ≃g T) ∨
      Nonempty (ForkGraph ≃g T)) := by
  classical
  let N_c := neighborFinsetIn T c Finset.univ
  let S_lf := N_c.filter (fun u => (neighborFinsetIn T u Finset.univ).card = 1)
  let S_nl := N_c.filter (fun u => 2 ≤ (neighborFinsetIn T u Finset.univ).card)
  have hN_part : N_c = S_lf ∪ S_nl := by
    ext u
    simp only [N_c, S_lf, S_nl, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hu
      have hpos : 1 ≤ (neighborFinsetIn T u Finset.univ).card :=
        Finset.card_pos.mpr ⟨c, (mem_neighborFinsetIn_iff T u c Finset.univ).mpr ⟨Finset.mem_univ c, (mem_neighborFinsetIn_iff T c u Finset.univ).mp hu |>.2.symm⟩⟩
      by_cases h1 : (neighborFinsetIn T u Finset.univ).card = 1
      · exact Or.inl ⟨hu, h1⟩
      · exact Or.inr ⟨hu, by omega⟩
    · rintro (⟨hu, _⟩ | ⟨hu, _⟩) <;> exact hu
  have hS_disj : Disjoint S_lf S_nl := by
    rw [Finset.disjoint_left]
    intro u hu1 hu2
    have h1 := (Finset.mem_filter.mp hu1).2
    have h2 := (Finset.mem_filter.mp hu2).2
    omega
  have hS_lf_le1 : S_lf.card ≤ 1 := by
    refine Finset.card_le_one.mpr ?_
    intro u hu v hv
    by_contra huv
    exact h_no_twins u v huv (Finset.mem_filter.mp hu).2 (Finset.mem_filter.mp hv).2 c
      ((mem_neighborFinsetIn_iff T c u Finset.univ).mp (Finset.mem_filter.mp hu).1).2.symm
      ((mem_neighborFinsetIn_iff T c v Finset.univ).mp (Finset.mem_filter.mp hv).1).2.symm
  have hN_sum : N_c.card = S_lf.card + S_nl.card := by
    conv_lhs => rw [hN_part]
    exact Finset.card_union_of_disjoint hS_disj
  have hex_second : ∀ u ∈ S_nl, ∃ w : W, w ≠ c ∧ T.Adj u w := by
    intro u hu
    have hcard_u : 2 ≤ (neighborFinsetIn T u Finset.univ).card := (Finset.mem_filter.mp hu).2
    have hcard_er : 1 ≤ ((neighborFinsetIn T u Finset.univ).erase c).card := by
      have hc_mem : c ∈ neighborFinsetIn T u Finset.univ :=
        (mem_neighborFinsetIn_iff T u c Finset.univ).mpr
          ⟨Finset.mem_univ c, ((mem_neighborFinsetIn_iff T c u Finset.univ).mp (Finset.mem_filter.mp hu).1).2.symm⟩
      rw [Finset.card_erase_of_mem hc_mem]
      omega
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hcard_er
    obtain ⟨hw_ne, hw_mem⟩ := Finset.mem_erase.mp hw
    exact ⟨w, hw_ne, ((mem_neighborFinsetIn_iff T u w Finset.univ).mp hw_mem).2⟩
  let secN : W → W := fun u => if h : u ∈ S_nl then Classical.choose (hex_second u h) else c
  have hsec_spec : ∀ u ∈ S_nl, secN u ≠ c ∧ T.Adj u (secN u) := by
    intro u hu
    dsimp [secN]; rw [dif_pos hu]
    exact Classical.choose_spec (hex_second u hu)
  have hsec_inj : Set.InjOn secN S_nl := by
    intro u₁ hu₁ u₂ hu₂ heq
    by_contra hne
    have hcu₁ : T.Adj c u₁ := ((mem_neighborFinsetIn_iff T c u₁ Finset.univ).mp (Finset.mem_filter.mp hu₁).1).2
    have hcu₂ : T.Adj c u₂ := ((mem_neighborFinsetIn_iff T c u₂ Finset.univ).mp (Finset.mem_filter.mp hu₂).1).2
    have hu₁w := (hsec_spec u₁ hu₁).2
    have hu₂w : T.Adj u₂ (secN u₁) := heq ▸ (hsec_spec u₂ hu₂).2
    exact acyclic_no_quad hT.2 (hsec_spec u₁ hu₁).1.symm hne hcu₁ hu₁w hu₂w.symm hcu₂
  have hdisj_c_N : c ∉ N_c := fun hc => T.loopless c ((mem_neighborFinsetIn_iff T c c Finset.univ).mp hc).2
  have hdisj_sec_N : Disjoint N_c (S_nl.image secN) := by
    rw [Finset.disjoint_left]
    intro v hv_N hv_sec
    rcases Finset.mem_image.mp hv_sec with ⟨u, hu, rfl⟩
    have hcu : T.Adj c u := ((mem_neighborFinsetIn_iff T c u Finset.univ).mp (Finset.mem_filter.mp hu).1).2
    have hcv : T.Adj c (secN u) := ((mem_neighborFinsetIn_iff T c (secN u) Finset.univ).mp hv_N).2
    exact acyclic_no_triangle hT.2 hcu (hsec_spec u hu).2 hcv
  have hc_not_sec : c ∉ S_nl.image secN := by
    intro hc
    rcases Finset.mem_image.mp hc with ⟨u, hu, h_eq⟩
    exact (hsec_spec u hu).1 h_eq
  let Core := insert c (N_c ∪ S_nl.image secN)
  have hCore_card : Core.card = 1 + N_c.card + S_nl.card := by
    dsimp [Core]
    rw [Finset.card_insert_of_notMem (by simp [hdisj_c_N, hc_not_sec]),
        Finset.card_union_of_disjoint hdisj_sec_N,
        Finset.card_image_of_injOn hsec_inj]
    ring
  have hW_ge_Core : Core.card ≤ Fintype.card W := Finset.card_le_univ Core
  have hNc_ge3 : 3 ≤ N_c.card := hc_deg
  have hW_ge_6 : 6 ≤ Fintype.card W := by omega
  refine ⟨hW_ge_6, ?_, ?_⟩
  · -- Case |W| = 6
    intro hW6
    have hd_eq3 : N_c.card = 3 := by omega
    have hlf_eq1 : S_lf.card = 1 := by omega
    have hnl_eq2 : S_nl.card = 2 := by omega
    obtain ⟨u₁, hu₁_eq⟩ := Finset.card_eq_one.mp hlf_eq1
    have hu₁_lf : u₁ ∈ S_lf := hu₁_eq ▸ Finset.mem_singleton_self u₁
    obtain ⟨u₂, u₃, hu₂₃, hu_nl_eq⟩ := Finset.card_eq_two.mp hnl_eq2
    have hu₂_nl : u₂ ∈ S_nl := hu_nl_eq ▸ Finset.mem_insert_self u₂ {u₃}
    have hu₃_nl : u₃ ∈ S_nl := hu_nl_eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self u₃)
    let w₂ := secN u₂
    let w₃ := secN u₃
    let f : Fin 6 → W := ![c, u₁, u₂, w₂, u₃, w₃]
    have hf_sub : Finset.univ.image f = Core := by
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Core, hN_part, hu₁_eq, hu_nl_eq,
        Finset.image_insert, Finset.image_singleton, Finset.mem_insert, Finset.mem_union,
        Finset.mem_singleton]
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp [f, w₂, w₃]
      · rintro (rfl | ((rfl | (rfl | rfl)) | (rfl | rfl)))
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
        · exact ⟨2, rfl⟩
        · exact ⟨4, rfl⟩
        · exact ⟨3, rfl⟩
        · exact ⟨5, rfl⟩
    have hf_inj : Function.Injective f := by
      have hcard_img : (Finset.univ.image f).card = Fintype.card (Fin 6) := by
        rw [hf_sub, hCore_card, hd_eq3, hnl_eq2, Fintype.card_fin]
      exact injective_of_univ_image_card_eq f hcard_img
    have hcu₁ : T.Adj c u₁ := ((mem_neighborFinsetIn_iff T c u₁ Finset.univ).mp (Finset.mem_filter.mp hu₁_lf).1).2
    have hcu₂ : T.Adj c u₂ := ((mem_neighborFinsetIn_iff T c u₂ Finset.univ).mp (Finset.mem_filter.mp hu₂_nl).1).2
    have hcu₃ : T.Adj c u₃ := ((mem_neighborFinsetIn_iff T c u₃ Finset.univ).mp (Finset.mem_filter.mp hu₃_nl).1).2
    have hu₂w₂ : T.Adj u₂ w₂ := (hsec_spec u₂ hu₂_nl).2
    have hu₃w₃ : T.Adj u₃ w₃ := (hsec_spec u₃ hu₃_nl).2
    have hf_hom : ∀ i j : Fin 6, (SpiderGraph 2).Adj i j → T.Adj (f i) (f j) := by
      intro i j hadj
      rcases spiderGraph2_adj_cases hadj with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hcu₁
      · exact hcu₁.symm
      · exact hcu₂
      · exact hcu₂.symm
      · exact hu₂w₂
      · exact hu₂w₂.symm
      · exact hcu₃
      · exact hcu₃.symm
      · exact hu₃w₃
      · exact hu₃w₃.symm
    exact ⟨isoOfConnectedHomToAcyclic (spiderGraph_connected 2 (by omega)) hT.2
      (by rw [Fintype.card_fin, hW6]) f hf_inj hf_hom⟩
  · -- Case |W| = 7
    intro hW7
    have hd_eq3 : N_c.card = 3 := by omega
    by_cases hnl3 : S_nl.card = 3
    · -- Subcase A: S_nl.card = 3 => SubdividedClawGraph
      have hlf0 : S_lf.card = 0 := by omega
      obtain ⟨u₁, u₂, u₃, hu₁₂, hu₁₃, hu₂₃, hu_eq⟩ := Finset.card_eq_three.mp hnl3
      have hu₁ : u₁ ∈ S_nl := hu_eq ▸ by simp
      have hu₂ : u₂ ∈ S_nl := hu_eq ▸ by simp
      have hu₃ : u₃ ∈ S_nl := hu_eq ▸ by simp
      let f : Fin 7 → W := ![c, u₁, secN u₁, u₂, secN u₂, u₃, secN u₃]
      have hf_sub : Finset.univ.image f = Core := by
        ext x
        simp only [Finset.mem_image, Finset.mem_univ, true_and, Core, hN_part,
          Finset.card_eq_zero.mp hlf0, Finset.empty_union, hu_eq,
          Finset.image_insert, Finset.image_singleton, Finset.mem_insert, Finset.mem_union,
          Finset.mem_singleton]
        constructor
        · rintro ⟨i, rfl⟩
          fin_cases i <;> simp [f]
        · rintro (rfl | ((rfl | rfl | rfl) | (rfl | rfl | rfl)))
          · exact ⟨0, rfl⟩
          · exact ⟨1, rfl⟩
          · exact ⟨3, rfl⟩
          · exact ⟨5, rfl⟩
          · exact ⟨2, rfl⟩
          · exact ⟨4, rfl⟩
          · exact ⟨6, rfl⟩
      have hf_inj : Function.Injective f := by
        have hcard_img : (Finset.univ.image f).card = Fintype.card (Fin 7) := by
          rw [hf_sub, hCore_card, hd_eq3, hnl3, Fintype.card_fin]
        exact injective_of_univ_image_card_eq f hcard_img
      have hcu₁ : T.Adj c u₁ := ((mem_neighborFinsetIn_iff T c u₁ Finset.univ).mp (Finset.mem_filter.mp hu₁).1).2
      have hcu₂ : T.Adj c u₂ := ((mem_neighborFinsetIn_iff T c u₂ Finset.univ).mp (Finset.mem_filter.mp hu₂).1).2
      have hcu₃ : T.Adj c u₃ := ((mem_neighborFinsetIn_iff T c u₃ Finset.univ).mp (Finset.mem_filter.mp hu₃).1).2
      have hw₁ := (hsec_spec u₁ hu₁).2
      have hw₂ := (hsec_spec u₂ hu₂).2
      have hw₃ := (hsec_spec u₃ hu₃).2
      have hf_hom : ∀ i j : Fin 7, SubdividedClawGraph.Adj i j → T.Adj (f i) (f j) := by
        intro i j hadj
        rcases subdividedClaw_adj_cases hadj with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hcu₁
        · exact hcu₁.symm
        · exact hw₁
        · exact hw₁.symm
        · exact hcu₂
        · exact hcu₂.symm
        · exact hw₂
        · exact hw₂.symm
        · exact hcu₃
        · exact hcu₃.symm
        · exact hw₃
        · exact hw₃.symm
      exact Or.inl ⟨isoOfConnectedHomToAcyclic subdividedClawGraph_connected hT.2
        (by rw [Fintype.card_fin, hW7]) f hf_inj hf_hom⟩
    · -- Subcase B: S_nl.card = 2, S_lf.card = 1
      have hnl2 : S_nl.card = 2 := by omega
      have hlf1 : S_lf.card = 1 := by omega
      obtain ⟨u₁, hu₁_eq⟩ := Finset.card_eq_one.mp hlf1
      have hu₁_lf : u₁ ∈ S_lf := hu₁_eq ▸ Finset.mem_singleton_self u₁
      obtain ⟨u₂, u₃, hu₂₃, hu_nl_eq⟩ := Finset.card_eq_two.mp hnl2
      have hu₂_nl : u₂ ∈ S_nl := hu_nl_eq ▸ Finset.mem_insert_self u₂ {u₃}
      have hu₃_nl : u₃ ∈ S_nl := hu_nl_eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self u₃)
      let w₂ := secN u₂
      let w₃ := secN u₃
      have hCore6 : Core.card = 6 := by rw [hCore_card, hd_eq3, hnl2]
      have hsdiff1 : (Finset.univ \ Core).card = 1 := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ Core), Finset.card_univ, hW7, hCore6]
      obtain ⟨z, hz_eq⟩ := Finset.card_eq_one.mp hsdiff1
      have hz_sdiff : z ∈ Finset.univ \ Core := hz_eq ▸ Finset.mem_singleton_self z
      have hz_not : z ∉ Core := (Finset.mem_sdiff.mp hz_sdiff).2
      have hex_att : ∃ x ∈ Core, T.Adj x z := by
        obtain ⟨q⟩ := hT.1.preconnected c z
        have hc_in : c ∈ Core := Finset.mem_insert_self c _
        have h_walk : ∀ {a b : W} (w : T.Walk a b), a ∈ Core → b ∉ Core → ∃ x ∈ Core, T.Adj x b ∨ ∃ y ∉ Core, T.Adj x y := by
          intro a b w ha hb
          induction w with
          | nil => exact False.elim (hb ha)
          | @cons x y _ h_xy w' ih =>
              by_cases hy : y ∈ Core
              · exact ih hy hb
              · exact ⟨x, ha, Or.inr ⟨y, hy, h_xy⟩⟩
        obtain ⟨x, hx_Core, h_or⟩ := h_walk q hc_in hz_not
        rcases h_or with hadj | ⟨y, hy_not, h_xy⟩
        · exact ⟨x, hx_Core, hadj⟩
        · have hy_sdiff : y ∈ Finset.univ \ Core := Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hy_not⟩
          rw [hz_eq, Finset.mem_singleton] at hy_sdiff
          exact ⟨x, hx_Core, hy_sdiff ▸ h_xy⟩
      obtain ⟨x, hx_Core, hxz⟩ := hex_att
      have hCore_list : ∀ y : W, y ∈ Core ↔ y = c ∨ y = u₁ ∨ y = u₂ ∨ y = u₃ ∨ y = w₂ ∨ y = w₃ := by
        intro y
        simp only [Core, hN_part, hu₁_eq, hu_nl_eq, Finset.image_insert, Finset.image_singleton,
          Finset.mem_insert, Finset.mem_union, Finset.mem_singleton, w₂, w₃]
        tauto
      have hcu₁ : T.Adj c u₁ := ((mem_neighborFinsetIn_iff T c u₁ Finset.univ).mp (Finset.mem_filter.mp hu₁_lf).1).2
      have hcu₂ : T.Adj c u₂ := ((mem_neighborFinsetIn_iff T c u₂ Finset.univ).mp (Finset.mem_filter.mp hu₂_nl).1).2
      have hcu₃ : T.Adj c u₃ := ((mem_neighborFinsetIn_iff T c u₃ Finset.univ).mp (Finset.mem_filter.mp hu₃_nl).1).2
      have hu₂w₂ : T.Adj u₂ w₂ := (hsec_spec u₂ hu₂_nl).2
      have hu₃w₃ : T.Adj u₃ w₃ := (hsec_spec u₃ hu₃_nl).2
      rcases (hCore_list x).mp hx_Core with hxc | hxu₁ | hxu₂ | hxu₃ | hxw₂ | hxw₃
      · exfalso
        rw [hxc] at hxz
        exact hz_not (Finset.mem_insert_of_mem (Finset.mem_union_left _
          ((mem_neighborFinsetIn_iff T c z Finset.univ).mpr ⟨Finset.mem_univ z, hxz⟩)))
      · exfalso
        rw [hxu₁] at hxz
        have hu₁_deg1 : (neighborFinsetIn T u₁ Finset.univ).card = 1 := (Finset.mem_filter.mp hu₁_lf).2
        have hcz_eq : z = c := Finset.card_le_one.mp (le_of_eq hu₁_deg1)
          z ((mem_neighborFinsetIn_iff T u₁ z Finset.univ).mpr ⟨Finset.mem_univ z, hxz⟩)
          c ((mem_neighborFinsetIn_iff T u₁ c Finset.univ).mpr ⟨Finset.mem_univ c, hcu₁.symm⟩)
        exact hz_not (hcz_eq ▸ Finset.mem_insert_self c _)
      · -- x = u₂: ForkGraph ≃g T via ![c, u₁, u₂, w₂, z, u₃, w₃]
        rw [hxu₂] at hxz
        right; right
        let g : Fin 7 → W := ![c, u₁, u₂, w₂, z, u₃, w₃]
        have hg_img : Finset.univ.image g = insert z Core := by
          ext y
          simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, hCore_list]
          constructor
          · rintro ⟨i, rfl⟩; fin_cases i <;> simp [g]
          · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
            · exact ⟨4, rfl⟩
            · exact ⟨0, rfl⟩
            · exact ⟨1, rfl⟩
            · exact ⟨2, rfl⟩
            · exact ⟨5, rfl⟩
            · exact ⟨3, rfl⟩
            · exact ⟨6, rfl⟩
        have hg_inj : Function.Injective g := by
          have hcard_img : (Finset.univ.image g).card = Fintype.card (Fin 7) := by
            rw [hg_img, Finset.card_insert_of_notMem hz_not, hCore6, Fintype.card_fin]
          exact injective_of_univ_image_card_eq g hcard_img
        have hg_hom : ∀ i j : Fin 7, ForkGraph.Adj i j → T.Adj (g i) (g j) := by
          intro i j hadj
          rcases forkGraph_adj_cases hadj with
            ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
            ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hcu₁
          · exact hcu₁.symm
          · exact hcu₂
          · exact hcu₂.symm
          · exact hu₂w₂
          · exact hu₂w₂.symm
          · exact hxz
          · exact hxz.symm
          · exact hcu₃
          · exact hcu₃.symm
          · exact hu₃w₃
          · exact hu₃w₃.symm
        exact ⟨isoOfConnectedHomToAcyclic forkGraph_connected hT.2
          (by rw [Fintype.card_fin, hW7]) g hg_inj hg_hom⟩
      · -- x = u₃: ForkGraph ≃g T via ![c, u₁, u₃, w₃, z, u₂, w₂]
        rw [hxu₃] at hxz
        right; right
        let g : Fin 7 → W := ![c, u₁, u₃, w₃, z, u₂, w₂]
        have hg_img : Finset.univ.image g = insert z Core := by
          ext y
          simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, hCore_list]
          constructor
          · rintro ⟨i, rfl⟩; fin_cases i <;> simp [g]
          · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
            · exact ⟨4, rfl⟩
            · exact ⟨0, rfl⟩
            · exact ⟨1, rfl⟩
            · exact ⟨5, rfl⟩
            · exact ⟨2, rfl⟩
            · exact ⟨6, rfl⟩
            · exact ⟨3, rfl⟩
        have hg_inj : Function.Injective g := by
          have hcard_img : (Finset.univ.image g).card = Fintype.card (Fin 7) := by
            rw [hg_img, Finset.card_insert_of_notMem hz_not, hCore6, Fintype.card_fin]
          exact injective_of_univ_image_card_eq g hcard_img
        have hg_hom : ∀ i j : Fin 7, ForkGraph.Adj i j → T.Adj (g i) (g j) := by
          intro i j hadj
          rcases forkGraph_adj_cases hadj with
            ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
            ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hcu₁
          · exact hcu₁.symm
          · exact hcu₃
          · exact hcu₃.symm
          · exact hu₃w₃
          · exact hu₃w₃.symm
          · exact hxz
          · exact hxz.symm
          · exact hcu₂
          · exact hcu₂.symm
          · exact hu₂w₂
          · exact hu₂w₂.symm
        exact ⟨isoOfConnectedHomToAcyclic forkGraph_connected hT.2
          (by rw [Fintype.card_fin, hW7]) g hg_inj hg_hom⟩
      · -- x = w₂: SpiderGraph 3 ≃g T via ![c, u₁, u₃, w₃, u₂, w₂, z]
        rw [hxw₂] at hxz
        right; left
        let g : Fin 7 → W := ![c, u₁, u₃, w₃, u₂, w₂, z]
        have hg_img : Finset.univ.image g = insert z Core := by
          ext y
          simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, hCore_list]
          constructor
          · rintro ⟨i, rfl⟩; fin_cases i <;> simp [g]
          · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
            · exact ⟨6, rfl⟩
            · exact ⟨0, rfl⟩
            · exact ⟨1, rfl⟩
            · exact ⟨4, rfl⟩
            · exact ⟨2, rfl⟩
            · exact ⟨5, rfl⟩
            · exact ⟨3, rfl⟩
        have hg_inj : Function.Injective g := by
          have hcard_img : (Finset.univ.image g).card = Fintype.card (Fin 7) := by
            rw [hg_img, Finset.card_insert_of_notMem hz_not, hCore6, Fintype.card_fin]
          exact injective_of_univ_image_card_eq g hcard_img
        have hg_hom : ∀ i j : Fin 7, (SpiderGraph 3).Adj i j → T.Adj (g i) (g j) := by
          intro i j hadj
          rcases spiderGraph3_adj_cases hadj with
            ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
            ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hcu₁
          · exact hcu₁.symm
          · exact hcu₃
          · exact hcu₃.symm
          · exact hu₃w₃
          · exact hu₃w₃.symm
          · exact hcu₂
          · exact hcu₂.symm
          · exact hu₂w₂
          · exact hu₂w₂.symm
          · exact hxz
          · exact hxz.symm
        exact ⟨isoOfConnectedHomToAcyclic (spiderGraph_connected 3 (by omega)) hT.2
          (by rw [Fintype.card_fin, hW7]) g hg_inj hg_hom⟩
      · -- x = w₃: SpiderGraph 3 ≃g T via ![c, u₁, u₂, w₂, u₃, w₃, z]
        rw [hxw₃] at hxz
        right; left
        let g : Fin 7 → W := ![c, u₁, u₂, w₂, u₃, w₃, z]
        have hg_img : Finset.univ.image g = insert z Core := by
          ext y
          simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, hCore_list]
          constructor
          · rintro ⟨i, rfl⟩; fin_cases i <;> simp [g]
          · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
            · exact ⟨6, rfl⟩
            · exact ⟨0, rfl⟩
            · exact ⟨1, rfl⟩
            · exact ⟨2, rfl⟩
            · exact ⟨4, rfl⟩
            · exact ⟨3, rfl⟩
            · exact ⟨5, rfl⟩
        have hg_inj : Function.Injective g := by
          have hcard_img : (Finset.univ.image g).card = Fintype.card (Fin 7) := by
            rw [hg_img, Finset.card_insert_of_notMem hz_not, hCore6, Fintype.card_fin]
          exact injective_of_univ_image_card_eq g hcard_img
        have hg_hom : ∀ i j : Fin 7, (SpiderGraph 3).Adj i j → T.Adj (g i) (g j) := by
          intro i j hadj
          rcases spiderGraph3_adj_cases hadj with
            ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
            ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hcu₁
          · exact hcu₁.symm
          · exact hcu₂
          · exact hcu₂.symm
          · exact hu₂w₂
          · exact hu₂w₂.symm
          · exact hcu₃
          · exact hcu₃.symm
          · exact hu₃w₃
          · exact hu₃w₃.symm
          · exact hxz
          · exact hxz.symm
        exact ⟨isoOfConnectedHomToAcyclic (spiderGraph_connected 3 (by omega)) hT.2
          (by rw [Fintype.card_fin, hW7]) g hg_inj hg_hom⟩

/-- **Theorem 8(1a): Every finite tree $T$ with $1 \le |V(T)| \le 6$ belongs to `InHClosureBNew`.** -/
theorem tree_card_le_6_inHClosureBNew {W : Type} [Fintype W] [DecidableEq W] [Nonempty W]
    (T : SimpleGraph W) (hT : T.IsTree) (hcard : Fintype.card W ≤ 6) :
    InHClosureBNew T := by
  have h_ind : ∀ (n : ℕ) {U : Type} [Fintype U] [DecidableEq U] [Nonempty U] (G : SimpleGraph U),
      Fintype.card U = n → n ≤ 6 → G.IsTree → InHClosureBNew G := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
        intro U _ _ _ G hcardU hn6 hG
        by_cases h_twins : ∃ u v : U, u ≠ v ∧
            (neighborFinsetIn G u Finset.univ).card = 1 ∧
            (neighborFinsetIn G v Finset.univ).card = 1 ∧
            ∃ p : U, G.Adj u p ∧ G.Adj v p
        · obtain ⟨u, v, huv, hdu, hdv, p, hup, hvp⟩ := h_twins
          have hu_unique : ∀ w : U, G.Adj u w ↔ w = p :=
            fun w => ⟨fun h => Finset.card_le_one.mp (le_of_eq hdu)
              w ((mem_neighborFinsetIn_iff G u w Finset.univ).mpr ⟨Finset.mem_univ w, h⟩)
              p ((mem_neighborFinsetIn_iff G u p Finset.univ).mpr ⟨Finset.mem_univ p, hup⟩),
              fun h => h ▸ hup⟩
          have hv_unique : ∀ w : U, G.Adj v w ↔ w = p :=
            fun w => ⟨fun h => Finset.card_le_one.mp (le_of_eq hdv)
              w ((mem_neighborFinsetIn_iff G v w Finset.univ).mpr ⟨Finset.mem_univ w, h⟩)
              p ((mem_neighborFinsetIn_iff G v p Finset.univ).mpr ⟨Finset.mem_univ p, hvp⟩),
              fun h => h ▸ hvp⟩
          have hnadj_uv : ¬G.Adj u v := fun h => G.loopless p ((hu_unique v).mp h ▸ hvp.symm)
          have htwin_uv : ∀ w : U, G.Adj u w ↔ G.Adj v w :=
            fun w => (hu_unique w).trans (hv_unique w).symm
          haveI : Nonempty {w : U // w ≠ v} := ⟨⟨u, huv⟩⟩
          have hcard_pos_U : 1 ≤ Fintype.card U := Fintype.card_pos
          have hcard' : Fintype.card {w : U // w ≠ v} = n - 1 := by rw [card_subtype_ne v]; omega
          have hG' := ih (n - 1) (by omega) _ hcard' (by omega) (isTree_delete_leaf hG hv_unique)
          exact inHClosureBNew_of_false_twins G u v huv hnadj_uv htwin_uv hG'
        · push_neg at h_twins
          by_cases hmax2 : ∀ v : U, (neighborFinsetIn G v Finset.univ).card ≤ 2
          · obtain ⟨e⟩ := tree_iso_pathGraph_of_max_deg_le_two hG hmax2
            exact inHClosureBNew_of_iso e (inHClosureBNew_pathGraph (Fintype.card U) Fintype.card_pos (by omega))
          · push_neg at hmax2
            obtain ⟨c, hc⟩ := hmax2
            have hc3 : 3 ≤ (neighborFinsetIn G c Finset.univ).card := by omega
            obtain ⟨h6, hiso6, _⟩ := twinLeafFree_center_classification hG h_twins hc3
            obtain ⟨e⟩ := hiso6 (by omega)
            exact inHClosureBNew_of_iso e (inHClosureBNew_spiderGraph 2 le_rfl (by omega))
  exact h_ind (Fintype.card W) T rfl hcard hT

/-- **Theorem 8(1c): Every $7$-vertex tree $T$ not isomorphic to `SubdividedClawGraph` ($S_{2,2,2}$)
belongs to `InHClosureBNew`.** -/
theorem tree_card_eq_7_inHClosureBNew {W : Type} [Fintype W] [DecidableEq W]
    (T : SimpleGraph W) (hT : T.IsTree) (hcard7 : Fintype.card W = 7)
    (h_not_claw : ¬Nonempty (T ≃g SubdividedClawGraph)) :
    InHClosureBNew T := by
  haveI : Nonempty W := hT.1.nonempty
  by_cases h_twins : ∃ u v : W, u ≠ v ∧
      (neighborFinsetIn T u Finset.univ).card = 1 ∧
      (neighborFinsetIn T v Finset.univ).card = 1 ∧
      ∃ p : W, T.Adj u p ∧ T.Adj v p
  · obtain ⟨u, v, huv, hdu, hdv, p, hup, hvp⟩ := h_twins
    have hu_unique : ∀ w : W, T.Adj u w ↔ w = p :=
      fun w => ⟨fun h => Finset.card_le_one.mp (le_of_eq hdu)
        w ((mem_neighborFinsetIn_iff T u w Finset.univ).mpr ⟨Finset.mem_univ w, h⟩)
        p ((mem_neighborFinsetIn_iff T u p Finset.univ).mpr ⟨Finset.mem_univ p, hup⟩),
        fun h => h ▸ hup⟩
    have hv_unique : ∀ w : W, T.Adj v w ↔ w = p :=
      fun w => ⟨fun h => Finset.card_le_one.mp (le_of_eq hdv)
        w ((mem_neighborFinsetIn_iff T v w Finset.univ).mpr ⟨Finset.mem_univ w, h⟩)
        p ((mem_neighborFinsetIn_iff T v p Finset.univ).mpr ⟨Finset.mem_univ p, hvp⟩),
        fun h => h ▸ hvp⟩
    have hnadj_uv : ¬T.Adj u v := fun h => T.loopless p ((hu_unique v).mp h ▸ hvp.symm)
    have htwin_uv : ∀ w : W, T.Adj u w ↔ T.Adj v w :=
      fun w => (hu_unique w).trans (hv_unique w).symm
    haveI : Nonempty {w : W // w ≠ v} := ⟨⟨u, huv⟩⟩
    have hcard6 : Fintype.card {w : W // w ≠ v} ≤ 6 := by rw [card_subtype_ne v, hcard7]
    exact inHClosureBNew_of_false_twins T u v huv hnadj_uv htwin_uv
      (tree_card_le_6_inHClosureBNew _ (isTree_delete_leaf hT hv_unique) hcard6)
  · push_neg at h_twins
    by_cases hmax2 : ∀ v : W, (neighborFinsetIn T v Finset.univ).card ≤ 2
    · obtain ⟨e⟩ := tree_iso_pathGraph_of_max_deg_le_two hT hmax2
      rw [hcard7] at e
      exact inHClosureBNew_of_iso e (inHClosureBNew_pathGraph 7 (by omega) (by omega))
    · push_neg at hmax2
      obtain ⟨c, hc⟩ := hmax2
      have hc3 : 3 ≤ (neighborFinsetIn T c Finset.univ).card := by omega
      obtain ⟨_, _, hiso7⟩ := twinLeafFree_center_classification hT h_twins hc3
      rcases hiso7 hcard7 with h_claw | h_sp3 | h_fork
      · obtain ⟨e_claw⟩ := h_claw
        exact False.elim (h_not_claw ⟨e_claw.symm⟩)
      · obtain ⟨e_sp3⟩ := h_sp3
        exact inHClosureBNew_of_iso e_sp3 (inHClosureBNew_spiderGraph 3 (by omega) (by omega))
      · obtain ⟨e_fork⟩ := h_fork
        exact inHClosureBNew_of_iso (substSpider2IsoForkGraph.trans e_fork)
          (inHClosureBNew_subst ⟨3, by decide⟩ (inHClosureBNew_spiderGraph 2 le_rfl (by omega)) inHClosureBNew_bot_fin2)

/-- **Theorem 8(1b): Every non-empty finite forest $F$ whose connected components each have order $\le 6$
belongs to `InHClosureBNew`.** -/
theorem forest_comp_card_le_6_inHClosureBNew {W : Type} [Fintype W] [DecidableEq W] [Nonempty W]
    (F : SimpleGraph W) [DecidableRel F.Reachable]
    (hAcyc : F.IsAcyclic)
    (hComp : ∀ u : W, (Finset.univ.filter (fun v : W => F.Reachable u v)).card ≤ 6) :
    InHClosureBNew F := by
  have h_ind : ∀ (n : ℕ) {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]
      (G : SimpleGraph U) [DecidableRel G.Reachable],
      Fintype.card U = n → G.IsAcyclic →
      (∀ u : U, (Finset.univ.filter (fun v : U => G.Reachable u v)).card ≤ 6) →
      InHClosureBNew G := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
        intro U _ _ _ G _ hcard hG_acyc hG_comp
        let u₀ : U := Classical.arbitrary U
        let C : Finset U := Finset.univ.filter (fun v : U => G.Reachable u₀ v)
        have hu₀_C : u₀ ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ u₀, SimpleGraph.Reachable.refl u₀⟩
        have h_anti : ∀ x ∈ C, ∀ y ∉ C, ¬G.Adj x y := by
          intro x hx y hy hadj
          exact hy (Finset.mem_filter.mpr ⟨Finset.mem_univ y,
            (Finset.mem_filter.mp hx).2.trans hadj.reachable⟩)
        let UC := {w : U // w ∈ C}
        let GC := G.comap (Subtype.val : UC → U)
        haveI : Nonempty UC := ⟨⟨u₀, hu₀_C⟩⟩
        have hGC_tree : GC.IsTree := by
          refine ⟨SimpleGraph.Connected.mk fun a b => ?_, ?_⟩
          · obtain ⟨w_ab⟩ := (Finset.mem_filter.mp a.2).2.symm.trans (Finset.mem_filter.mp b.2).2
            have h_lift_walk : ∀ {x y : U} (p : G.Walk x y) (hx : x ∈ C),
                ∃ hy : y ∈ C, Nonempty (GC.Walk ⟨x, hx⟩ ⟨y, hy⟩) := by
              intro x y p hx
              induction p with
              | nil => exact ⟨hx, ⟨Walk.nil⟩⟩
              | @cons x z y h_xz p' ihp =>
                  have hz : z ∈ C := Finset.mem_filter.mpr
                    ⟨Finset.mem_univ z, (Finset.mem_filter.mp hx).2.trans h_xz.reachable⟩
                  obtain ⟨hy, ⟨p'_lift⟩⟩ := ihp hz
                  exact ⟨hy, ⟨@Walk.cons UC GC ⟨x, hx⟩ ⟨z, hz⟩ ⟨y, hy⟩ h_xz p'_lift⟩⟩
            obtain ⟨_, ⟨p_lift⟩⟩ := h_lift_walk w_ab a.2
            exact ⟨p_lift⟩
          · rw [SimpleGraph.isAcyclic_iff_path_unique]
            intro x y ⟨q₁, hq₁⟩ ⟨q₂, hq₂⟩
            apply Subtype.ext
            let f_hom : GC →g G := { toFun := Subtype.val, map_rel' := fun {_ _} h => h }
            let p₁ : G.Walk x.1 y.1 := Walk.map f_hom q₁
            let p₂ : G.Walk x.1 y.1 := Walk.map f_hom q₂
            have hp₁ : p₁.IsPath := Walk.IsPath.mk' (by rw [Walk.support_map]; exact hq₁.support_nodup.map Subtype.val_injective)
            have hp₂ : p₂.IsPath := Walk.IsPath.mk' (by rw [Walk.support_map]; exact hq₂.support_nodup.map Subtype.val_injective)
            have hp_eq : p₁ = p₂ :=
              congrArg Subtype.val ((SimpleGraph.isAcyclic_iff_path_unique.mp hG_acyc) ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩)
            exact walk_comap_injective hp_eq
        have hC_card_le6 : Fintype.card UC ≤ 6 := by
          rw [Fintype.card_coe]; exact hG_comp u₀
        have hGC_inH : InHClosureBNew GC :=
          tree_card_le_6_inHClosureBNew GC hGC_tree hC_card_le6
        by_cases h_rest_empty : ∀ v : U, v ∈ C
        · let e_all : GC ≃g G :=
            { toFun := Subtype.val
              invFun := fun v => ⟨v, h_rest_empty v⟩
              left_inv := fun ⟨_, _⟩ => rfl
              right_inv := fun _ => rfl
              map_rel_iff' := by intro _ _; rfl }
          exact inHClosureBNew_of_iso e_all hGC_inH
        · push_neg at h_rest_empty
          obtain ⟨v_out, hv_out⟩ := h_rest_empty
          let U' := {w : U // w ∉ C}
          let G' := G.comap (Subtype.val : U' → U)
          haveI : Nonempty U' := ⟨⟨v_out, hv_out⟩⟩
          haveI : DecidableRel G'.Reachable := Classical.decRel _
          have hlt_n : Fintype.card U' < n := by
            have hC_pos : 1 ≤ C.card := Finset.card_pos.mpr ⟨u₀, hu₀_C⟩
            have hC_le_n : C.card ≤ n := hcard ▸ Finset.card_le_univ C
            have hU'_eq : Fintype.card U' = (Finset.univ \ C).card := by
              rw [Finset.sdiff_eq_filter]
              exact Fintype.card_subtype _
            rw [hU'_eq, Finset.card_sdiff_of_subset (Finset.subset_univ C), Finset.card_univ, hcard]
            omega
          have hG'_acyc : G'.IsAcyclic := by
            rw [SimpleGraph.isAcyclic_iff_path_unique]
            intro x y ⟨q₁, hq₁⟩ ⟨q₂, hq₂⟩
            apply Subtype.ext
            let f_hom : G' →g G := { toFun := Subtype.val, map_rel' := fun {_ _} h => h }
            let p₁ : G.Walk x.1 y.1 := Walk.map f_hom q₁
            let p₂ : G.Walk x.1 y.1 := Walk.map f_hom q₂
            have hp₁ : p₁.IsPath := Walk.IsPath.mk' (by rw [Walk.support_map]; exact hq₁.support_nodup.map Subtype.val_injective)
            have hp₂ : p₂.IsPath := Walk.IsPath.mk' (by rw [Walk.support_map]; exact hq₂.support_nodup.map Subtype.val_injective)
            have hp_eq : p₁ = p₂ :=
              congrArg Subtype.val ((SimpleGraph.isAcyclic_iff_path_unique.mp hG_acyc) ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩)
            exact walk_comap_injective hp_eq
          have hG'_comp : ∀ u : U', (Finset.univ.filter (fun v : U' => G'.Reachable u v)).card ≤ 6 := by
            intro u
            have hsub : (Finset.univ.filter (fun v : U' => G'.Reachable u v)).map
                ⟨Subtype.val, Subtype.val_injective⟩ ⊆
                Finset.univ.filter (fun v : U => G.Reachable u.1 v) := by
              intro x hx
              rcases Finset.mem_map.mp hx with ⟨v, hv, rfl⟩
              rw [Finset.mem_filter] at hv ⊢
              obtain ⟨_, ⟨p⟩⟩ := hv
              let f_hom : G' →g G := { toFun := Subtype.val, map_rel' := fun {_ _} h => h }
              exact ⟨Finset.mem_univ _, ⟨Walk.map f_hom p⟩⟩
            calc (Finset.univ.filter (fun v : U' => G'.Reachable u v)).card
                = ((Finset.univ.filter (fun v : U' => G'.Reachable u v)).map ⟨Subtype.val, Subtype.val_injective⟩).card :=
                  (Finset.card_map _).symm
              _ ≤ (Finset.univ.filter (fun v : U => G.Reachable u.1 v)).card := Finset.card_le_card hsub
              _ ≤ 6 := hG_comp u.1
          have hG'_inH : InHClosureBNew G' := ih _ hlt_n G' rfl hG'_acyc hG'_comp
          exact inHClosureBNew_of_anticomplete_split G C h_anti hGC_inH hG'_inH
  exact h_ind (Fintype.card W) F rfl hAcyc hComp

/-- **Combined Theorem 8(1) Interface (`small_trees_and_forests_of_base`)**:
Given `∀ B, InBNew B → HasErdosHajnalProp B`, proves the exact statement of `main_theorem_A5_small_trees_and_forests`. -/
theorem small_trees_and_forests_of_base
    (h_base : ∀ {W : Type} [Fintype W] [DecidableEq W] (B : SimpleGraph W),
      InBNew B → HasErdosHajnalProp B) :
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
        HasPolyRodlProp T ∧ IsViral T) := by
  refine ⟨?_, ?_, ?_⟩
  · intro W _ _ _ T hT hcard
    have hH := tree_card_le_6_inHClosureBNew T hT hcard
    exact ⟨hH, inHClosureBNew_eh_of_base h_base T hH⟩
  · intro W _ _ _ F _ hAcyc hComp
    have hH := forest_comp_card_le_6_inHClosureBNew F hAcyc hComp
    exact ⟨hH, inHClosureBNew_eh_of_base h_base F hH⟩
  · intro W _ _ T hT hcard7 hNotClaw
    have hH := tree_card_eq_7_inHClosureBNew T hT hcard7 hNotClaw
    exact ⟨hH, inHClosureBNew_eh_of_base h_base T hH⟩

/-!
### Section 3: Generalized Prime Non-Split Extension Towers (`GenPrimeTowerGraph G₀ x₀ r`) & Base Families
-/

noncomputable instance instDecidableRelGenPrimeTowerAdj {W₀ : Type*} (G₀ : SimpleGraph W₀) (x₀ : W₀) (r : ℕ) :
    DecidableRel (GenPrimeTowerGraph G₀ x₀ r).Adj :=
  Classical.decRel _

@[simp] theorem genPrimeTower_adj_inl_inl {W₀ : Type*} (G₀ : SimpleGraph W₀) (x₀ : W₀) (r : ℕ)
    (w₁ w₂ : W₀) :
    (GenPrimeTowerGraph G₀ x₀ r).Adj (Sum.inl w₁) (Sum.inl w₂) ↔ G₀.Adj w₁ w₂ := Iff.rfl

@[simp] theorem genPrimeTower_adj_inl_inr {W₀ : Type*} (G₀ : SimpleGraph W₀) (x₀ : W₀) (r : ℕ)
    (w : W₀) (j : Fin r) :
    (GenPrimeTowerGraph G₀ x₀ r).Adj (Sum.inl w) (Sum.inr j) ↔
      (j.1 % 2 = 0 ∧ (if j.1 = 0 then w ≠ x₀ else True)) := Iff.rfl

@[simp] theorem genPrimeTower_adj_inr_inl {W₀ : Type*} (G₀ : SimpleGraph W₀) (x₀ : W₀) (r : ℕ)
    (j : Fin r) (w : W₀) :
    (GenPrimeTowerGraph G₀ x₀ r).Adj (Sum.inr j) (Sum.inl w) ↔
      (j.1 % 2 = 0 ∧ (if j.1 = 0 then w ≠ x₀ else True)) := Iff.rfl

@[simp] theorem genPrimeTower_adj_inr_inr {W₀ : Type*} (G₀ : SimpleGraph W₀) (x₀ : W₀) (r : ℕ)
    (i j : Fin r) :
    (GenPrimeTowerGraph G₀ x₀ r).Adj (Sum.inr i) (Sum.inr j) ↔
      (if i.1 < j.1 then genTowerStepAdjLt i.1 j.1
       else if j.1 < i.1 then genTowerStepAdjLt j.1 i.1
       else False) := Iff.rfl

/-- Canonical induced graph embedding $G_0 \hookrightarrow_g H_{n_0+r}^{(G_0)}$ (`g₀EmbGenPrimeTower`). -/
def g₀EmbGenPrimeTower {W₀ : Type*} (G₀ : SimpleGraph W₀) (x₀ : W₀) (r : ℕ) :
    G₀ ↪g GenPrimeTowerGraph G₀ x₀ r where
  toEmbedding := Function.Embedding.inl
  map_rel_iff' := by intro _ _; rfl

/-- Base-case isomorphism $H_{n_0}^{(G_0)} \simeq_g G_0$ (`genPrimeTowerZeroIso`). -/
def genPrimeTowerZeroIso {W₀ : Type*} (G₀ : SimpleGraph W₀) (x₀ : W₀) :
    GenPrimeTowerGraph G₀ x₀ 0 ≃g G₀ where
  toFun := fun s =>
    match s with
    | Sum.inl w => w
    | Sum.inr i => i.elim0
  invFun := Sum.inl
  left_inv := fun s => by rcases s with w | i; rfl; exact i.elim0
  right_inv := fun _ => rfl
  map_rel_iff' := by rintro (w₁ | i₁) (w₂ | i₂); rfl; exact i₂.elim0; exact i₁.elim0; exact i₁.elim0

/-- Deleting the top tower vertex `Sum.inr (Fin.last r)` from `GenPrimeTowerGraph G₀ x₀ (r + 1)`
yields `GenPrimeTowerGraph G₀ x₀ r`. -/
def genPrimeTowerStepIso {W₀ : Type*} [DecidableEq W₀] (G₀ : SimpleGraph W₀) (x₀ : W₀) (r : ℕ) :
    (GenPrimeTowerGraph G₀ x₀ (r + 1)).comap
      (Subtype.val : {v : W₀ ⊕ Fin (r + 1) // v ≠ Sum.inr (Fin.last r)} → W₀ ⊕ Fin (r + 1)) ≃g
      GenPrimeTowerGraph G₀ x₀ r where
  toFun v :=
    match hv : v.1 with
    | Sum.inl w => Sum.inl w
    | Sum.inr i =>
        Sum.inr ⟨i.1, by
          have hi_ne : i ≠ Fin.last r := fun h => v.2 (by rw [hv, h])
          have hi_lt := i.2
          have hi_val : i.1 ≠ r := fun h => hi_ne (Fin.ext h)
          omega⟩
  invFun s :=
    match s with
    | Sum.inl w => ⟨Sum.inl w, fun h => by cases h⟩
    | Sum.inr i => ⟨Sum.inr ⟨i.1, by omega⟩, fun h => by
        have := congrArg Fin.val (Sum.inr.inj h); dsimp at this; omega⟩
  left_inv v := by
    rcases v with ⟨w | i, hne⟩
    · rfl
    · rfl
  right_inv s := by
    rcases s with w | i
    · rfl
    · rfl
  map_rel_iff' := by
    rintro ⟨w₁ | i₁, h₁⟩ ⟨w₂ | i₂, h₂⟩ <;> rfl

/-- **Pairwise Non-Isomorphism (`genPrimeTower_iso_iff_eq`)**:
`GenPrimeTowerGraph G₀ x₀ r₁` and `GenPrimeTowerGraph G₀ x₀ r₂` are isomorphic iff $r_1 = r_2$. -/
theorem genPrimeTower_iso_iff_eq {W₀ : Type*} [Fintype W₀] [DecidableEq W₀]
    (G₀ : SimpleGraph W₀) (x₀ : W₀) (r₁ r₂ : ℕ) :
    Nonempty (GenPrimeTowerGraph G₀ x₀ r₁ ≃g GenPrimeTowerGraph G₀ x₀ r₂) ↔ r₁ = r₂ := by
  constructor
  · rintro ⟨iso⟩
    have hcard := Fintype.card_congr iso.toEquiv
    simp only [Fintype.card_sum, Fintype.card_fin] at hcard
    omega
  · rintro rfl
    exact ⟨SimpleGraph.Iso.refl⟩

/-- **Non-Splitness (`genPrimeTower_not_isSplitGraph`)**:
If $G_0$ is not a split graph, then `GenPrimeTowerGraph G₀ x₀ r` is not a split graph for any $r \ge 0$. -/
theorem genPrimeTower_not_isSplitGraph {W₀ : Type*} [Fintype W₀] [DecidableEq W₀]
    (G₀ : SimpleGraph W₀) (x₀ : W₀) (hNotSplit : ¬IsSplitGraph G₀) (r : ℕ) :
    ¬IsSplitGraph (GenPrimeTowerGraph G₀ x₀ r) :=
  fun h => hNotSplit (IsSplitGraph.of_embedding (g₀EmbGenPrimeTower G₀ x₀ r) h)

/-- If $|W_0| \ge 6$ and $\Delta(G_0) \le |W_0| - 3$, then every vertex of $\overline{G_0}$ has degree $\ge 2$. -/
theorem g₀Compl_min_deg_ge_two {W₀ : Type*} [Fintype W₀] [DecidableEq W₀]
    (G₀ : SimpleGraph W₀) (hCard : 6 ≤ Fintype.card W₀)
    (hMaxDeg : ∀ u : W₀, (neighborFinsetIn G₀ u Finset.univ).card ≤ Fintype.card W₀ - 3)
    (u : W₀) :
    2 ≤ (neighborFinsetIn G₀ᶜ u Finset.univ).card := by
  have hsub : Finset.univ \ insert u (neighborFinsetIn G₀ u Finset.univ) ⊆
      neighborFinsetIn G₀ᶜ u Finset.univ := by
    intro v hv
    rw [Finset.mem_sdiff, Finset.mem_insert] at hv
    push_neg at hv
    rw [mem_neighborFinsetIn_iff, compl_adj]
    exact ⟨Finset.mem_univ v, hv.2.1.symm, fun hadj =>
      hv.2.2 ((mem_neighborFinsetIn_iff G₀ u v Finset.univ).mpr ⟨Finset.mem_univ v, hadj⟩)⟩
  have hu_not : u ∉ neighborFinsetIn G₀ u Finset.univ :=
    fun h => G₀.loopless u ((mem_neighborFinsetIn_iff G₀ u u Finset.univ).mp h).2
  have hcard_ins : (insert u (neighborFinsetIn G₀ u Finset.univ)).card =
      (neighborFinsetIn G₀ u Finset.univ).card + 1 :=
    Finset.card_insert_of_notMem hu_not
  have hcard_sdiff : (Finset.univ \ insert u (neighborFinsetIn G₀ u Finset.univ)).card =
      Fintype.card W₀ - (insert u (neighborFinsetIn G₀ u Finset.univ)).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
  have hle := Finset.card_le_card hsub
  have hd := hMaxDeg u
  omega

/-- **Non-Membership in `InJClosureC5` (`genPrimeTowerCompl_not_inJClosureC5`)**:
For any prime graph $G_0$ with $|W_0| \ge 6$ and $\Delta(G_0) \le |W_0| - 3$,
`(GenPrimeTowerGraph G₀ x₀ r)ᶜ` does not belong to $\mathcal{J}(\{K_1, K_2, \overline{K_2}, C_5\})$. -/
theorem genPrimeTowerCompl_not_inJClosureC5 {W₀ : Type} [Fintype W₀] [DecidableEq W₀]
    (G₀ : SimpleGraph W₀) (x₀ : W₀)
    (hPrime₀ : IsPrimeGraph G₀) (hCard₀ : 6 ≤ Fintype.card W₀)
    (hMaxDeg₀ : ∀ u : W₀, (neighborFinsetIn G₀ u Finset.univ).card ≤ Fintype.card W₀ - 3)
    (r : ℕ) :
    ¬InJClosureC5 (GenPrimeTowerGraph G₀ x₀ r)ᶜ := by
  intro hH
  have h_inv : HasNoLargeMinDegTwoPrimeInduced (GenPrimeTowerGraph G₀ x₀ r)ᶜ :=
    inJClosureC5_hasNoLargeMinDegTwoPrimeInduced hH
  have h_emb : Nonempty (G₀ᶜ ↪g (GenPrimeTowerGraph G₀ x₀ r)ᶜ) :=
    ⟨complEmbedding (g₀EmbGenPrimeTower G₀ x₀ r)⟩
  have h_prime : IsPrimeGraph G₀ᶜ := (isPrimeGraph_compl_iff G₀).mpr hPrime₀
  obtain ⟨u₀, hu₀⟩ := h_inv G₀ᶜ h_emb hCard₀ h_prime
  have h_ge2 := g₀Compl_min_deg_ge_two G₀ hCard₀ hMaxDeg₀ u₀
  omega

/-- Every vertex of a prime graph $G_0$ has degree at least $1$ (no isolated vertices). -/
theorem primeGraph_exists_neighbor {W₀ : Type*} [Fintype W₀] [DecidableEq W₀]
    {G₀ : SimpleGraph W₀} (hPrime : IsPrimeGraph G₀) (u : W₀) :
    ∃ w : W₀, G₀.Adj u w := by
  by_contra h_iso
  push_neg at h_iso
  let M := Finset.univ.erase u
  have hM_card : M.card = Fintype.card W₀ - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ]
  have h4 := hPrime.1
  have hM_ne : M.Nonempty := by rw [← Finset.card_pos, hM_card]; omega
  have hM_ssub : M ⊂ Finset.univ :=
    Finset.erase_ssubset (Finset.mem_univ u)
  have hM_mod : IsModuleIn G₀ Finset.univ M := by
    refine ⟨Finset.subset_univ _, fun z _ hz => Or.inr fun v _ hzv => ?_⟩
    have hzu : z = u := by
      by_contra hne
      exact hz (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ z⟩)
    exact h_iso v (hzu ▸ hzv)
  have h1 := hPrime.2 M ⟨hM_ne, hM_ssub, hM_mod⟩
  omega

/-- **Primality of Generalized Tower (`genPrimeTower_isPrimeGraph`)**:
For any prime graph $G_0$ on $\ge 6$ vertices with $\Delta(G_0) \le |W_0| - 3$ and $x_0 \in W_0$,
`GenPrimeTowerGraph G₀ x₀ r` is prime (`IsPrimeGraph`) for all $r \ge 0$. -/
theorem genPrimeTower_isPrimeGraph {W₀ : Type} [Fintype W₀] [DecidableEq W₀]
    (G₀ : SimpleGraph W₀) (x₀ : W₀)
    (hPrime₀ : IsPrimeGraph G₀) (hCard₀ : 6 ≤ Fintype.card W₀)
    (hMaxDeg₀ : ∀ u : W₀, (neighborFinsetIn G₀ u Finset.univ).card ≤ Fintype.card W₀ - 3)
    (r : ℕ) :
    IsPrimeGraph (GenPrimeTowerGraph G₀ x₀ r) := by
  induction r with
  | zero =>
      exact hPrime₀.of_iso (genPrimeTowerZeroIso G₀ x₀).symm
  | succ r ih =>
      have hG_prev : IsPrimeGraph ((GenPrimeTowerGraph G₀ x₀ (r + 1)).comap
          (Subtype.val : {v : W₀ ⊕ Fin (r + 1) // v ≠ Sum.inr (Fin.last r)} → W₀ ⊕ Fin (r + 1))) :=
        ih.of_iso (genPrimeTowerStepIso G₀ x₀ r).symm
      rcases eq_or_ne r 0 with rfl | hr_pos
      · -- Step r + 1 = 1 (co-leaf Sum.inr (Fin.last 0), w₀ = Sum.inl x₀)
        have hw₀_ne : (Sum.inl x₀ : W₀ ⊕ Fin 1) ≠ Sum.inr (Fin.last 0) := Sum.inl_ne_inr
        refine isPrimeGraph_of_add_coleaf hG_prev hw₀_ne ?_ ?_ ?_
        · rintro (w | i)
          · rw [compl_adj, genPrimeTower_adj_inr_inl]
            dsimp [Fin.last]
            simp only [Sum.inr_ne_inl, not_false_eq_true, true_and, Sum.inl.injEq]
            tauto
          · fin_cases i
            exact ⟨fun h => False.elim ((GenPrimeTowerGraph G₀ x₀ 1)ᶜ.loopless _ h),
              fun h => by cases h⟩
        · have hdeg_x₀ := g₀Compl_min_deg_ge_two G₀ hCard₀ hMaxDeg₀ x₀
          obtain ⟨y, hy⟩ := Finset.card_pos.mp (by omega : 0 < (neighborFinsetIn G₀ᶜ x₀ Finset.univ).card)
          have hadj_c := ((mem_neighborFinsetIn_iff G₀ᶜ x₀ y Finset.univ).mp hy).2
          refine ⟨Sum.inl y, Sum.inl_ne_inr, ?_⟩
          rw [compl_adj, genPrimeTower_adj_inl_inl]
          rw [compl_adj] at hadj_c
          exact ⟨fun h => hadj_c.1 (Sum.inl.inj h), hadj_c.2⟩
        · rintro (z₀ | i) hzu hzw₀
          · have hz_ne : z₀ ≠ x₀ := fun h => hzw₀ (congrArg Sum.inl h)
            have hdeg_z := g₀Compl_min_deg_ge_two G₀ hCard₀ hMaxDeg₀ z₀
            have her_pos : 1 ≤ ((neighborFinsetIn G₀ᶜ z₀ Finset.univ).erase x₀).card := by
              by_cases hx_mem : x₀ ∈ neighborFinsetIn G₀ᶜ z₀ Finset.univ
              · rw [Finset.card_erase_of_mem hx_mem]; omega
              · rw [Finset.erase_eq_of_notMem hx_mem]; omega
            obtain ⟨y, hy⟩ := Finset.card_pos.mp her_pos
            obtain ⟨hy_ne_x₀, hy_mem⟩ := Finset.mem_erase.mp hy
            have hadj_c := ((mem_neighborFinsetIn_iff G₀ᶜ z₀ y Finset.univ).mp hy_mem).2
            refine ⟨Sum.inl y, Sum.inl_ne_inr, fun h => hy_ne_x₀ (Sum.inl.inj h), ?_⟩
            rw [compl_adj, genPrimeTower_adj_inl_inl]
            rw [compl_adj] at hadj_c
            exact ⟨fun h => hadj_c.1 (Sum.inl.inj h), hadj_c.2⟩
          · fin_cases i
            exact False.elim (hzu rfl)
      · -- Step r + 1 ≥ 2: w₀ = Sum.inr ⟨r - 1, _⟩
        let w₀ : W₀ ⊕ Fin (r + 1) := Sum.inr ⟨r - 1, by omega⟩
        have hw₀_ne : w₀ ≠ Sum.inr (Fin.last r) := fun h => by
          have := congrArg Fin.val (Sum.inr.inj h); dsimp [Fin.last] at this; omega
        by_cases hr_even : (r + 1) % 2 = 0
        · -- Even step (r % 2 = 1): leaf addition in G
          have hr_odd : r % 2 = 1 := by omega
          refine isPrimeGraph_of_add_leaf hG_prev hw₀_ne ?_ ?_ ?_
          · rintro (w | i)
            · rw [genPrimeTower_adj_inr_inl]; dsimp [Fin.last]; simp [hr_odd]
            · rw [genPrimeTower_adj_inr_inr]; dsimp [Fin.last, genTowerStepAdjLt]
              have hi_lt := i.2
              by_cases hir : i.1 = r
              · rw [if_neg (by omega : ¬r < i.1), if_neg (by omega : ¬i.1 < r)]
                simp only [false_iff]
                intro h
                have := congrArg Fin.val (Sum.inr.inj h); dsimp [w₀] at this; omega
              · rw [if_neg (by omega : ¬r < i.1), if_pos (by omega : i.1 < r),
                    if_neg (by omega : ¬r % 2 = 0)]
                rw [Sum.inr.injEq, Fin.ext_iff]; dsimp; omega
          · have hcard_er : 1 ≤ ((Finset.univ : Finset W₀).erase x₀).card := by
              rw [Finset.card_erase_of_mem (Finset.mem_univ x₀), Finset.card_univ]; omega
            obtain ⟨y, hy⟩ := Finset.card_pos.mp hcard_er
            have hy_ne : y ≠ x₀ := (Finset.mem_erase.mp hy).1
            refine ⟨Sum.inl y, Sum.inl_ne_inr, ?_⟩
            rw [genPrimeTower_adj_inr_inl]; dsimp
            exact ⟨by omega, by (split_ifs; simp [hy_ne])⟩
          · rintro (z₀ | i) hzu hzw₀
            · obtain ⟨y, hzy⟩ := primeGraph_exists_neighbor hPrime₀ z₀
              exact ⟨Sum.inl y, Sum.inl_ne_inr, Sum.inl_ne_inr, hzy⟩
            · have hi_lt : i.1 < r - 1 := by
                have := i.2
                have h1 : i.1 ≠ r := fun h => hzu (congrArg Sum.inr (Fin.ext h))
                have h2 : i.1 ≠ r - 1 := fun h => hzw₀ (congrArg Sum.inr (Fin.ext h))
                omega
              by_cases hi_par : i.1 % 2 = 0
              · have hcard_er : 1 ≤ ((Finset.univ : Finset W₀).erase x₀).card := by
                  rw [Finset.card_erase_of_mem (Finset.mem_univ x₀), Finset.card_univ]; omega
                obtain ⟨y, hy⟩ := Finset.card_pos.mp hcard_er
                have hy_ne : y ≠ x₀ := (Finset.mem_erase.mp hy).1
                refine ⟨Sum.inl y, Sum.inl_ne_inr, Sum.inl_ne_inr, ?_⟩
                rw [genPrimeTower_adj_inr_inl]
                exact ⟨hi_par, by (split_ifs; simp [hy_ne])⟩
              · refine ⟨Sum.inr ⟨i.1 - 1, by omega⟩,
                  fun h => by have := congrArg Fin.val (Sum.inr.inj h); dsimp [Fin.last] at this; omega,
                  fun h => by have := congrArg Fin.val (Sum.inr.inj h); dsimp at this; omega, ?_⟩
                rw [genPrimeTower_adj_inr_inr]; dsimp [genTowerStepAdjLt]
                rw [if_neg (by omega : ¬i.1 < i.1 - 1), if_pos (by omega : i.1 - 1 < i.1), if_neg hi_par]
                omega
        · -- Odd step ≥ 3 (r % 2 = 0, r ≥ 2): co-leaf addition in G
          have hr_ev : r % 2 = 0 := by omega
          refine isPrimeGraph_of_add_coleaf hG_prev hw₀_ne ?_ ?_ ?_
          · rintro (w | i)
            · rw [compl_adj, genPrimeTower_adj_inr_inl]
              dsimp [Fin.last]
              rw [if_neg hr_pos]
              exact ⟨fun h => False.elim (h.2 ⟨hr_ev, trivial⟩),
                fun h => by dsimp [w₀] at h; cases h⟩
            · rw [compl_adj, genPrimeTower_adj_inr_inr]
              dsimp [Fin.last, genTowerStepAdjLt]
              have hi_lt := i.2
              by_cases hir : i.1 = r
              · rw [if_neg (by omega : ¬r < i.1), if_neg (by omega : ¬i.1 < r)]
                constructor
                · intro h; exact False.elim (h.1 (congrArg Sum.inr (Fin.ext hir.symm)))
                · intro h; have := congrArg Fin.val (Sum.inr.inj h); dsimp [w₀] at this; omega
              · rw [if_neg (by omega : ¬r < i.1), if_pos (by omega : i.1 < r), if_pos hr_ev]
                constructor
                · intro h
                  have hne_i : i.1 = r - 1 := by have h2 := h.2; omega
                  apply congrArg Sum.inr; ext; dsimp [w₀]; exact hne_i
                · intro h
                  have hval := congrArg Fin.val (Sum.inr.inj h); dsimp [w₀] at hval
                  exact ⟨fun heq => by have := congrArg Fin.val (Sum.inr.inj heq); dsimp [Fin.last] at this; omega,
                    by omega⟩
          · refine ⟨Sum.inl x₀, Sum.inl_ne_inr, ?_⟩
            dsimp only [w₀]
            rw [compl_adj, genPrimeTower_adj_inr_inl]
            refine ⟨Sum.inr_ne_inl, ?_⟩
            dsimp
            intro h; have h1 : (r - 1) % 2 = 0 := h.1; omega
          · rintro (z₀ | i) hzu hzw₀
            · have hdeg_z := g₀Compl_min_deg_ge_two G₀ hCard₀ hMaxDeg₀ z₀
              obtain ⟨y, hy⟩ := Finset.card_pos.mp (by omega : 0 < (neighborFinsetIn G₀ᶜ z₀ Finset.univ).card)
              have hadj_c := ((mem_neighborFinsetIn_iff G₀ᶜ z₀ y Finset.univ).mp hy).2
              refine ⟨Sum.inl y, Sum.inl_ne_inr, Sum.inl_ne_inr, ?_⟩
              rw [compl_adj, genPrimeTower_adj_inl_inl]
              rw [compl_adj] at hadj_c
              exact ⟨fun h => hadj_c.1 (Sum.inl.inj h), hadj_c.2⟩
            · have hi_lt : i.1 < r - 1 := by
                have := i.2
                have h1 : i.1 ≠ r := fun h => hzu (congrArg Sum.inr (Fin.ext h))
                have h2 : i.1 ≠ r - 1 := fun h => hzw₀ (congrArg Sum.inr (Fin.ext h))
                omega
              by_cases hi0 : i.1 = 0
              · refine ⟨Sum.inl x₀, Sum.inl_ne_inr, Sum.inl_ne_inr, ?_⟩
                rw [compl_adj, genPrimeTower_adj_inr_inl]
                refine ⟨Sum.inr_ne_inl, ?_⟩
                rw [if_pos hi0]; simp
              · by_cases hi_par : i.1 % 2 = 0
                · refine ⟨Sum.inr ⟨i.1 - 1, by omega⟩,
                    fun h => by have := congrArg Fin.val (Sum.inr.inj h); dsimp [Fin.last] at this; omega,
                    fun h => by have := congrArg Fin.val (Sum.inr.inj h); dsimp at this; omega, ?_⟩
                  rw [compl_adj, genPrimeTower_adj_inr_inr]
                  refine ⟨fun h => by have := congrArg Fin.val (Sum.inr.inj h); dsimp at this; omega, ?_⟩
                  dsimp [genTowerStepAdjLt]
                  rw [if_neg (by omega : ¬i.1 < i.1 - 1), if_pos (by omega : i.1 - 1 < i.1), if_pos hi_par]
                  omega
                · refine ⟨Sum.inl x₀, Sum.inl_ne_inr, Sum.inl_ne_inr, ?_⟩
                  rw [compl_adj, genPrimeTower_adj_inr_inl]
                  exact ⟨Sum.inr_ne_inl, fun h => hi_par h.1⟩

/-- Explicit step-1 deletion isomorphism: deleting `Sum.inl x₀` from `GenPrimeTowerGraph G₀ x₀ 1` yields
`substGraph (⊤ : SimpleGraph (Fin 2)) 0 (G₀ - x₀)`. -/
def genPrimeTowerOneDeleteIso {W₀ : Type*} [DecidableEq W₀] (G₀ : SimpleGraph W₀) (x₀ : W₀) :
    substGraph (⊤ : SimpleGraph (Fin 2)) 0 (G₀.comap (Subtype.val : {w : W₀ // w ≠ x₀} → W₀)) ≃g
      (GenPrimeTowerGraph G₀ x₀ 1).comap
        (Subtype.val : {v : W₀ ⊕ Fin 1 // v ≠ Sum.inl x₀} → W₀ ⊕ Fin 1) where
  toFun s :=
    match s with
    | Sum.inl _ => ⟨Sum.inr 0, fun h => by cases h⟩
    | Sum.inr w => ⟨Sum.inl w.1, fun h => w.2 (Sum.inl.inj h)⟩
  invFun v :=
    match hv : v.1 with
    | Sum.inl w => Sum.inr ⟨w, fun h => v.2 (by rw [hv, h])⟩
    | Sum.inr _ => Sum.inl ⟨1, by decide⟩
  left_inv s := by
    rcases s with ⟨ix, hix⟩ | w
    · dsimp; congr 1; fin_cases ix; exact False.elim (hix rfl); rfl
    · rfl
  right_inv v := by
    rcases v with ⟨w | i, hne⟩
    · rfl
    · fin_cases i; rfl
  map_rel_iff' := by
    rintro (⟨ix, hix⟩ | ⟨w₁, hw₁⟩) (⟨iy, hiy⟩ | ⟨w₂, hw₂⟩)
    · simp only [comap_adj, substGraph, top_adj, ne_eq]
      dsimp; rw [genPrimeTower_adj_inr_inr]
      constructor
      · intro h; simp at h
      · intro hxy; exfalso
        fin_cases ix; exact hix rfl; fin_cases iy; exact hiy rfl; exact hxy rfl
    · simp only [comap_adj, substGraph, top_adj, ne_eq, hix, not_false_eq_true, iff_true]
      dsimp; rw [genPrimeTower_adj_inr_inl]; simp [hw₂]
    · simp only [comap_adj, substGraph, top_adj, ne_eq, hiy.symm, not_false_eq_true, iff_true]
      dsimp; rw [genPrimeTower_adj_inl_inr]; simp [hw₁]
    · rfl

/-- Explicit odd-step deletion isomorphism: when `(m + 2) % 2 = 1`, deleting `Sum.inr ⟨m, _⟩` from
`GenPrimeTowerGraph G₀ x₀ (m + 2)` yields `substGraph (⊤ : SimpleGraph (Fin 2)) 0 (GenPrimeTowerGraph G₀ x₀ m)`. -/
def genPrimeTowerOddStepDeleteIso {W₀ : Type*} [DecidableEq W₀]
    (G₀ : SimpleGraph W₀) (x₀ : W₀) (m : ℕ) (hm_odd : (m + 2) % 2 = 1) :
    substGraph (⊤ : SimpleGraph (Fin 2)) 0 (GenPrimeTowerGraph G₀ x₀ m) ≃g
      (GenPrimeTowerGraph G₀ x₀ (m + 2)).comap
        (Subtype.val : {v : W₀ ⊕ Fin (m + 2) // v ≠ Sum.inr ⟨m, by omega⟩} → W₀ ⊕ Fin (m + 2)) where
  toFun s :=
    match s with
    | Sum.inl _ => ⟨Sum.inr ⟨m + 1, by omega⟩, fun h => by
        have := congrArg Fin.val (Sum.inr.inj h); dsimp at this; omega⟩
    | Sum.inr (Sum.inl w) => ⟨Sum.inl w, fun h => by cases h⟩
    | Sum.inr (Sum.inr i) => ⟨Sum.inr ⟨i.1, by omega⟩, fun h => by
        have := congrArg Fin.val (Sum.inr.inj h); dsimp at this; omega⟩
  invFun v :=
    match hv : v.1 with
    | Sum.inl w => Sum.inr (Sum.inl w)
    | Sum.inr i =>
        if h : i.1 < m then Sum.inr (Sum.inr ⟨i.1, h⟩)
        else Sum.inl ⟨1, by decide⟩
  left_inv s := by
    rcases s with ⟨ix, hix⟩ | (w | i)
    · dsimp; rw [dif_neg (by omega)]; congr 1; fin_cases ix; exact False.elim (hix rfl); rfl
    · rfl
    · dsimp; rw [if_pos i.2]
  right_inv v := by
    rcases v with ⟨w | i, hne⟩
    · rfl
    · dsimp
      by_cases h : i.1 < m
      · rw [dif_pos h]
      · rw [dif_neg h]
        apply Subtype.ext; dsimp
        apply congrArg Sum.inr; ext; dsimp
        have hi_ne : i.1 ≠ m := fun hm => hne (congrArg Sum.inr (Fin.ext hm))
        omega
  map_rel_iff' := by
    rintro (⟨ix, hix⟩ | (w₁ | i₁)) (⟨iy, hiy⟩ | (w₂ | i₂))
    · simp only [comap_adj, substGraph, top_adj, ne_eq]
      dsimp; rw [genPrimeTower_adj_inr_inr]
      constructor
      · intro h; simp at h
      · intro hxy; exfalso
        fin_cases ix; exact hix rfl; fin_cases iy; exact hiy rfl; exact hxy rfl
    · simp only [comap_adj, substGraph, top_adj, ne_eq, hix, not_false_eq_true, iff_true]
      dsimp; rw [genPrimeTower_adj_inr_inl]; dsimp
      exact ⟨by omega, trivial⟩
    · simp only [comap_adj, substGraph, top_adj, ne_eq, hix, not_false_eq_true, iff_true]
      dsimp; rw [genPrimeTower_adj_inr_inr]; dsimp [genTowerStepAdjLt]
      have hi₂ := i₂.2
      rw [if_neg (by omega : ¬m + 1 < i₂.1), if_pos (by omega : i₂.1 < m + 1),
          if_pos (by omega : (m + 1) % 2 = 0)]
      omega
    · simp only [comap_adj, substGraph, top_adj, ne_eq, hiy.symm, not_false_eq_true, iff_true]
      dsimp; rw [genPrimeTower_adj_inl_inr]; dsimp
      exact ⟨by omega, trivial⟩
    · rfl
    · rfl
    · simp only [comap_adj, substGraph, top_adj, ne_eq, hiy.symm, not_false_eq_true, iff_true]
      dsimp; rw [genPrimeTower_adj_inr_inr]; dsimp [genTowerStepAdjLt]
      have hi₁ := i₁.2
      rw [if_pos (by omega : i₁.1 < m + 1), if_pos (by omega : (m + 1) % 2 = 0)]
      omega
    · rfl
    · rfl

/-- Explicit even-step complement deletion isomorphism: when `(m + 2) % 2 = 0`, deleting `Sum.inr ⟨m, _⟩` from
`(GenPrimeTowerGraph G₀ x₀ (m + 2))ᶜ` yields `substGraph (⊤ : SimpleGraph (Fin 2)) 0 (GenPrimeTowerGraph G₀ x₀ m)ᶜ`. -/
def genPrimeTowerEvenStepDeleteComplIso {W₀ : Type*} [DecidableEq W₀]
    (G₀ : SimpleGraph W₀) (x₀ : W₀) (m : ℕ) (hm_even : (m + 2) % 2 = 0) :
    substGraph (⊤ : SimpleGraph (Fin 2)) 0 (GenPrimeTowerGraph G₀ x₀ m)ᶜ ≃g
      (GenPrimeTowerGraph G₀ x₀ (m + 2))ᶜ.comap
        (Subtype.val : {v : W₀ ⊕ Fin (m + 2) // v ≠ Sum.inr ⟨m, by omega⟩} → W₀ ⊕ Fin (m + 2)) where
  toFun s :=
    match s with
    | Sum.inl _ => ⟨Sum.inr ⟨m + 1, by omega⟩, fun h => by
        have := congrArg Fin.val (Sum.inr.inj h); dsimp at this; omega⟩
    | Sum.inr (Sum.inl w) => ⟨Sum.inl w, fun h => by cases h⟩
    | Sum.inr (Sum.inr i) => ⟨Sum.inr ⟨i.1, by omega⟩, fun h => by
        have := congrArg Fin.val (Sum.inr.inj h); dsimp at this; omega⟩
  invFun v :=
    match hv : v.1 with
    | Sum.inl w => Sum.inr (Sum.inl w)
    | Sum.inr i =>
        if h : i.1 < m then Sum.inr (Sum.inr ⟨i.1, h⟩)
        else Sum.inl ⟨1, by decide⟩
  left_inv s := by
    rcases s with ⟨ix, hix⟩ | (w | i)
    · dsimp; rw [dif_neg (by omega)]; congr 1; fin_cases ix; exact False.elim (hix rfl); rfl
    · rfl
    · dsimp; rw [if_pos i.2]
  right_inv v := by
    rcases v with ⟨w | i, hne⟩
    · rfl
    · dsimp
      by_cases h : i.1 < m
      · rw [dif_pos h]
      · rw [dif_neg h]
        apply Subtype.ext; dsimp
        apply congrArg Sum.inr; ext; dsimp
        have hi_ne : i.1 ≠ m := fun hm => hne (congrArg Sum.inr (Fin.ext hm))
        omega
  map_rel_iff' := by
    rintro (⟨ix, hix⟩ | (w₁ | i₁)) (⟨iy, hiy⟩ | (w₂ | i₂))
    · simp only [comap_adj, substGraph, top_adj, ne_eq, compl_adj]
      dsimp
      constructor
      · intro h; exact False.elim (h.1 rfl)
      · intro hxy; exfalso
        fin_cases ix; exact hix rfl; fin_cases iy; exact hiy rfl; exact hxy rfl
    · simp only [comap_adj, substGraph, top_adj, ne_eq, hix, not_false_eq_true, iff_true, compl_adj]
      dsimp; rw [genPrimeTower_adj_inr_inl]; dsimp
      exact ⟨Sum.inr_ne_inl, fun h => by omega⟩
    · simp only [comap_adj, substGraph, top_adj, ne_eq, hix, not_false_eq_true, iff_true, compl_adj]
      dsimp; rw [genPrimeTower_adj_inr_inr]; dsimp [genTowerStepAdjLt]
      have hi₂ := i₂.2
      refine ⟨fun h => by have := congrArg Fin.val (Sum.inr.inj h); dsimp at this; omega, ?_⟩
      rw [if_neg (by omega : ¬m + 1 < i₂.1), if_pos (by omega : i₂.1 < m + 1),
          if_neg (by omega : ¬(m + 1) % 2 = 0)]
      omega
    · simp only [comap_adj, substGraph, top_adj, ne_eq, hiy.symm, not_false_eq_true, iff_true, compl_adj]
      dsimp; rw [genPrimeTower_adj_inl_inr]; dsimp
      exact ⟨Sum.inl_ne_inr, fun h => by omega⟩
    · simp only [comap_adj, substGraph, compl_adj, ne_eq]
      dsimp; simp only [Sum.inl.injEq]; rfl
    · simp only [comap_adj, substGraph, compl_adj, ne_eq]
      dsimp; simp only [Sum.inl_ne_inr, not_false_eq_true, true_and]; rfl
    · simp only [comap_adj, substGraph, top_adj, ne_eq, hiy.symm, not_false_eq_true, iff_true, compl_adj]
      dsimp; rw [genPrimeTower_adj_inr_inr]; dsimp [genTowerStepAdjLt]
      have hi₁ := i₁.2
      refine ⟨fun h => by have := congrArg Fin.val (Sum.inr.inj h); dsimp at this; omega, ?_⟩
      rw [if_pos (by omega : i₁.1 < m + 1), if_neg (by omega : ¬(m + 1) % 2 = 0)]
      omega
    · simp only [comap_adj, substGraph, compl_adj, ne_eq]
      dsimp; simp only [Sum.inr_ne_inl, not_false_eq_true, true_and]; rfl
    · simp only [comap_adj, substGraph, compl_adj, ne_eq]
      dsimp; simp only [Sum.inr.injEq, Fin.ext_iff]; rfl

/-- **Closure Membership (`genPrimeTower_inHClosureBInfty`)**:
Whenever $G_0 \in \mathcal{H}(\mathcal{B}_\infty^*)$, $G_0 - x_0 \in \mathcal{H}(\mathcal{B}_\infty^*)$, and
$\deg_{G_0}(x_0) \le 1$, every tower graph `GenPrimeTowerGraph G₀ x₀ r` belongs to $\mathcal{H}(\mathcal{B}_\infty^*)$. -/
theorem genPrimeTower_inHClosureBInfty {W₀ : Type} [Fintype W₀] [DecidableEq W₀]
    (G₀ : SimpleGraph W₀) (x₀ : W₀)
    (hx₀_deg : (neighborFinsetIn G₀ x₀ Finset.univ).card ≤ 1)
    (hG₀ : InHClosureBInfty G₀)
    (hG₀_del : InHClosureBInfty (G₀.comap (Subtype.val : {w : W₀ // w ≠ x₀} → W₀)))
    (r : ℕ) :
    InHClosureBInfty (GenPrimeTowerGraph G₀ x₀ r) := by
  have hk2 : InJClosureBInfty (⊤ : SimpleGraph (Fin 2)) :=
    InJClosureBInfty.base _ (Or.inl (Or.inl (Or.inr (Or.inl ⟨SimpleGraph.Iso.refl⟩))))
  induction r using Nat.strong_induction_on with
  | h r ih =>
      rcases r with _ | k
      · exact inHClosureBInfty_of_iso (genPrimeTowerZeroIso G₀ x₀).symm hG₀
      · have ih_k : InHClosureBInfty (GenPrimeTowerGraph G₀ x₀ k) := ih k (Nat.lt_succ_self k)
        rcases k with _ | m
        · -- Step 1
          let u : W₀ ⊕ Fin 1 := Sum.inr 0
          let vx₀ : W₀ ⊕ Fin 1 := Sum.inl x₀
          constructor
          · have hvx₀_deg : (neighborFinsetIn (GenPrimeTowerGraph G₀ x₀ 1) vx₀ Finset.univ).card ≤ 1 := by
              have hsub : neighborFinsetIn (GenPrimeTowerGraph G₀ x₀ 1) vx₀ Finset.univ ⊆
                  (neighborFinsetIn G₀ x₀ Finset.univ).map Function.Embedding.inl := by
                rintro (w | i) hw
                · rw [mem_neighborFinsetIn_iff] at hw
                  exact Finset.mem_map_of_mem Function.Embedding.inl
                    ((mem_neighborFinsetIn_iff G₀ x₀ w Finset.univ).mpr ⟨Finset.mem_univ w, hw.2⟩)
                · rw [mem_neighborFinsetIn_iff, genPrimeTower_adj_inl_inr] at hw
                  fin_cases i
                  exact False.elim (hw.2.2 rfl)
              calc (neighborFinsetIn (GenPrimeTowerGraph G₀ x₀ 1) vx₀ Finset.univ).card
                  ≤ ((neighborFinsetIn G₀ x₀ Finset.univ).map Function.Embedding.inl).card := Finset.card_le_card hsub
                _ = (neighborFinsetIn G₀ x₀ Finset.univ).card := Finset.card_map _
                _ ≤ 1 := hx₀_deg
            have h_subst : InJClosureBInfty (substGraph (⊤ : SimpleGraph (Fin 2)) 0 (G₀.comap (Subtype.val : {w : W₀ // w ≠ x₀} → W₀))) :=
              InJClosureBInfty.subst _ 0 _ hk2 hG₀_del.1
            have h_del : InJClosureBInfty ((GenPrimeTowerGraph G₀ x₀ 1).comap
                (Subtype.val : {v : W₀ ⊕ Fin 1 // v ≠ vx₀} → W₀ ⊕ Fin 1)) :=
              InJClosureBInfty.iso _ _ h_subst ⟨genPrimeTowerOneDeleteIso G₀ x₀⟩
            exact InJClosureBInfty.add_leaf _ vx₀ hvx₀_deg h_del
          · have hu_deg : (neighborFinsetIn (GenPrimeTowerGraph G₀ x₀ 1)ᶜ u Finset.univ).card ≤ 1 := by
              refine card_neighborFinsetIn_le_one_of_unique _ u vx₀ ?_
              rintro (w | i) hadj
              · rw [compl_adj, genPrimeTower_adj_inr_inl] at hadj
                dsimp [u] at hadj
                have hwx₀ : w = x₀ := by tauto
                subst hwx₀; rfl
              · fin_cases i
                exact False.elim ((GenPrimeTowerGraph G₀ x₀ 1)ᶜ.loopless u hadj)
            have h_del : InJClosureBInfty ((GenPrimeTowerGraph G₀ x₀ 1)ᶜ.comap
                (Subtype.val : {v : W₀ ⊕ Fin 1 // v ≠ u} → W₀ ⊕ Fin 1)) :=
              InJClosureBInfty.iso _ _ ih_k.2
                ⟨(complIso (genPrimeTowerStepIso G₀ x₀ 0)).symm.trans (complComapSubtypeIso u).symm⟩
            exact InJClosureBInfty.add_leaf _ u hu_deg h_del
        · -- Step m + 2
          have ih_m : InHClosureBInfty (GenPrimeTowerGraph G₀ x₀ m) := ih m (by omega)
          let u : W₀ ⊕ Fin (m + 2) := Sum.inr (Fin.last (m + 1))
          let w₀ : W₀ ⊕ Fin (m + 2) := Sum.inr ⟨m, by omega⟩
          by_cases hm_even : (m + 2) % 2 = 0
          · constructor
            · have hu_deg : (neighborFinsetIn (GenPrimeTowerGraph G₀ x₀ (m + 2)) u Finset.univ).card ≤ 1 := by
                refine card_neighborFinsetIn_le_one_of_unique _ u w₀ ?_
                rintro (w | i) hadj
                · rw [genPrimeTower_adj_inr_inl] at hadj; dsimp [u, Fin.last] at hadj; omega
                · rw [genPrimeTower_adj_inr_inr] at hadj; dsimp [genTowerStepAdjLt, u, Fin.last] at hadj
                  have hi := i.2
                  by_cases him : i.1 = m + 1
                  · rw [if_neg (by omega : ¬m + 1 < i.1), if_neg (by omega : ¬i.1 < m + 1)] at hadj
                    exact False.elim hadj
                  · rw [if_neg (by omega : ¬m + 1 < i.1), if_pos (by omega : i.1 < m + 1),
                        if_neg (by omega : ¬(m + 1) % 2 = 0)] at hadj
                    apply congrArg Sum.inr; ext; dsimp; omega
              have h_del : InJClosureBInfty ((GenPrimeTowerGraph G₀ x₀ (m + 2)).comap
                  (Subtype.val : {v : W₀ ⊕ Fin (m + 2) // v ≠ u} → W₀ ⊕ Fin (m + 2))) :=
                InJClosureBInfty.iso _ _ ih_k.1 ⟨(genPrimeTowerStepIso G₀ x₀ (m + 1)).symm⟩
              exact InJClosureBInfty.add_leaf _ u hu_deg h_del
            · let prev_w : W₀ ⊕ Fin (m + 2) :=
                if m = 0 then Sum.inl x₀ else Sum.inr ⟨m - 1, by omega⟩
              have hw₀_deg : (neighborFinsetIn (GenPrimeTowerGraph G₀ x₀ (m + 2))ᶜ w₀ Finset.univ).card ≤ 1 := by
                refine card_neighborFinsetIn_le_one_of_unique _ w₀ prev_w ?_
                rintro (w | i) hadj
                · rw [compl_adj, genPrimeTower_adj_inr_inl] at hadj
                  dsimp [w₀] at hadj
                  have hm0 : m = 0 := by
                    by_contra hmnz
                    exact hadj.2 ⟨by omega, by rw [if_neg hmnz]; trivial⟩
                  subst hm0
                  have hwx₀ : w = x₀ := by simp at hadj; exact hadj
                  subst hwx₀
                  rfl
                · obtain ⟨hne, hnadj⟩ := (compl_adj _ _ _).mp hadj
                  have hi := i.2
                  have him_ne : m ≠ i.1 := fun h => hne (congrArg Sum.inr (Fin.ext (by dsimp; exact h)))
                  by_cases hil : i.1 < m
                  · have hmnz : m ≠ 0 := by omega
                    rw [genPrimeTower_adj_inr_inr] at hnadj
                    dsimp [genTowerStepAdjLt, w₀] at hnadj
                    rw [if_neg (by omega : ¬m < i.1), if_pos hil, if_pos (by omega : m % 2 = 0)] at hnadj
                    dsimp [prev_w]; rw [if_neg hmnz]
                    apply congrArg Sum.inr; ext; dsimp; omega
                  · have hml : m < i.1 := by omega
                    rw [genPrimeTower_adj_inr_inr] at hnadj
                    dsimp [genTowerStepAdjLt, w₀] at hnadj
                    rw [if_pos hml, if_neg (by omega : ¬i.1 % 2 = 0)] at hnadj
                    omega
              have h_subst : InJClosureBInfty (substGraph (⊤ : SimpleGraph (Fin 2)) 0 (GenPrimeTowerGraph G₀ x₀ m)ᶜ) :=
                InJClosureBInfty.subst _ 0 _ hk2 ih_m.2
              have h_del : InJClosureBInfty ((GenPrimeTowerGraph G₀ x₀ (m + 2))ᶜ.comap
                  (Subtype.val : {v : W₀ ⊕ Fin (m + 2) // v ≠ w₀} → W₀ ⊕ Fin (m + 2))) :=
                InJClosureBInfty.iso _ _ h_subst ⟨genPrimeTowerEvenStepDeleteComplIso G₀ x₀ m hm_even⟩
              exact InJClosureBInfty.add_leaf _ w₀ hw₀_deg h_del
          · have hm_odd : (m + 2) % 2 = 1 := by omega
            constructor
            · let prev_w : W₀ ⊕ Fin (m + 2) := Sum.inr ⟨m - 1, by omega⟩
              have hw₀_deg : (neighborFinsetIn (GenPrimeTowerGraph G₀ x₀ (m + 2)) w₀ Finset.univ).card ≤ 1 := by
                refine card_neighborFinsetIn_le_one_of_unique _ w₀ prev_w ?_
                rintro (w | i) hadj
                · rw [genPrimeTower_adj_inr_inl] at hadj; dsimp [w₀] at hadj; omega
                · have hi := i.2
                  have him_ne : m ≠ i.1 := fun h => by
                    have hw_eq : w₀ = Sum.inr i := congrArg Sum.inr (Fin.ext (by dsimp [w₀]; exact h))
                    exact (GenPrimeTowerGraph G₀ x₀ (m + 2)).loopless w₀ (hw_eq ▸ hadj)
                  by_cases hil : i.1 < m
                  · rw [genPrimeTower_adj_inr_inr] at hadj
                    dsimp [genTowerStepAdjLt, w₀] at hadj
                    rw [if_neg (by omega : ¬m < i.1), if_pos hil, if_neg (by omega : ¬m % 2 = 0)] at hadj
                    apply congrArg Sum.inr; ext; dsimp; omega
                  · have hml : m < i.1 := by omega
                    rw [genPrimeTower_adj_inr_inr] at hadj
                    dsimp [genTowerStepAdjLt, w₀] at hadj
                    rw [if_pos hml, if_pos (by omega : i.1 % 2 = 0)] at hadj
                    omega
              have h_subst : InJClosureBInfty (substGraph (⊤ : SimpleGraph (Fin 2)) 0 (GenPrimeTowerGraph G₀ x₀ m)) :=
                InJClosureBInfty.subst _ 0 _ hk2 ih_m.1
              have h_del : InJClosureBInfty ((GenPrimeTowerGraph G₀ x₀ (m + 2)).comap
                  (Subtype.val : {v : W₀ ⊕ Fin (m + 2) // v ≠ w₀} → W₀ ⊕ Fin (m + 2))) :=
                InJClosureBInfty.iso _ _ h_subst ⟨genPrimeTowerOddStepDeleteIso G₀ x₀ m hm_odd⟩
              exact InJClosureBInfty.add_leaf _ w₀ hw₀_deg h_del
            · have hu_deg : (neighborFinsetIn (GenPrimeTowerGraph G₀ x₀ (m + 2))ᶜ u Finset.univ).card ≤ 1 := by
                refine card_neighborFinsetIn_le_one_of_unique _ u w₀ ?_
                rintro (w | i) hadj
                · rw [compl_adj, genPrimeTower_adj_inr_inl] at hadj
                  dsimp [u, Fin.last] at hadj
                  exfalso
                  exact hadj.2 ⟨by omega, trivial⟩
                · obtain ⟨hne, hnadj⟩ := (compl_adj _ _ _).mp hadj
                  have hi := i.2
                  have him_ne : m + 1 ≠ i.1 := fun h => hne (congrArg Sum.inr (Fin.ext (by dsimp [Fin.last]; exact h)))
                  rw [genPrimeTower_adj_inr_inr] at hnadj
                  dsimp [genTowerStepAdjLt, u, Fin.last] at hnadj
                  rw [if_neg (by omega : ¬m + 1 < i.1), if_pos (by omega : i.1 < m + 1),
                      if_pos (by omega : (m + 1) % 2 = 0)] at hnadj
                  apply congrArg Sum.inr; ext; dsimp; omega
              have h_del : InJClosureBInfty ((GenPrimeTowerGraph G₀ x₀ (m + 2))ᶜ.comap
                  (Subtype.val : {v : W₀ ⊕ Fin (m + 2) // v ≠ u} → W₀ ⊕ Fin (m + 2))) :=
                InJClosureBInfty.iso _ _ ih_k.2
                  ⟨(complIso (genPrimeTowerStepIso G₀ x₀ (m + 1))).symm.trans (complComapSubtypeIso u).symm⟩
              exact InJClosureBInfty.add_leaf _ u hu_deg h_del

/-- **Proposition 6(3) Master General Base Theorem (`genPrimeTower_main_of_base`)**:
Directly matches `Problem.lean` lines 259–275! -/
theorem genPrimeTower_main_of_base
    (h_base : ∀ {W : Type} [Fintype W] [DecidableEq W] (B : SimpleGraph W),
      InBInfty B → HasErdosHajnalProp B)
    (W₀ : Type) [Fintype W₀] [DecidableEq W₀] (G₀ : SimpleGraph W₀) (x₀ : W₀)
    (h_hyp : IsPrimeGraph G₀ ∧ 6 ≤ Fintype.card W₀ ∧
       (∀ u : W₀, (neighborFinsetIn G₀ u Finset.univ).card ≤ Fintype.card W₀ - 3) ∧
       (neighborFinsetIn G₀ x₀ Finset.univ).card = 1 ∧
       ¬IsSplitGraph G₀ ∧
       InHClosureBInfty G₀ ∧
       InHClosureBInfty (G₀.comap (Subtype.val : {w : W₀ // w ≠ x₀} → W₀))) :
    (∀ r : ℕ,
      InHClosureBInfty (GenPrimeTowerGraph G₀ x₀ r) ∧
      HasErdosHajnalProp (GenPrimeTowerGraph G₀ x₀ r) ∧
      HasErdosHajnalProp (GenPrimeTowerGraph G₀ x₀ r)ᶜ ∧
      IsViral (GenPrimeTowerGraph G₀ x₀ r) ∧
      IsPrimeGraph (GenPrimeTowerGraph G₀ x₀ r) ∧
      ¬IsSplitGraph (GenPrimeTowerGraph G₀ x₀ r) ∧
      ¬InJClosureC5 (GenPrimeTowerGraph G₀ x₀ r)ᶜ) ∧
    (∀ r₁ r₂ : ℕ,
      Nonempty (GenPrimeTowerGraph G₀ x₀ r₁ ≃g GenPrimeTowerGraph G₀ x₀ r₂) ↔ r₁ = r₂) := by
  obtain ⟨hPrime₀, hCard₀, hMaxDeg₀, hx₀_deg, hNotSplit₀, hG₀, hG₀_del⟩ := h_hyp
  refine ⟨fun r => ?_, genPrimeTower_iso_iff_eq G₀ x₀⟩
  have hInH : InHClosureBInfty (GenPrimeTowerGraph G₀ x₀ r) :=
    genPrimeTower_inHClosureBInfty G₀ x₀ (le_of_eq hx₀_deg) hG₀ hG₀_del r
  obtain ⟨hEH, hEH_c, _, hViral⟩ := inHClosureBInfty_eh_of_base h_base _ hInH
  exact ⟨hInH, hEH, hEH_c, hViral,
    genPrimeTower_isPrimeGraph G₀ x₀ hPrime₀ hCard₀ hMaxDeg₀ r,
    genPrimeTower_not_isSplitGraph G₀ x₀ hNotSplit₀ r,
    genPrimeTowerCompl_not_inJClosureC5 G₀ x₀ hPrime₀ hCard₀ hMaxDeg₀ r⟩

/-!
### Section 4: Base Family Verification & Strict Containment Witnesses (`pathGraph k`, `SpiderGraph d`, `BirdDGraph d`)
-/

/-- Deleting the last vertex `Fin.last (d + 3)` from `SpiderGraph (d + 1)` yields `SpiderGraph d`. -/
def spiderGraphStepIso (d : ℕ) :
    (SpiderGraph (d + 1)).comap
      (Subtype.val : {v : Fin (d + 1 + 4) // v ≠ Fin.last (d + 4)} → Fin (d + 1 + 4)) ≃g
      SpiderGraph d where
  toFun v := ⟨v.1.1, by
    have hne : v.1.1 ≠ d + 4 := fun h => v.2 (Fin.ext h)
    have := v.1.2
    omega⟩
  invFun i := ⟨⟨i.1, by omega⟩, fun h => by
    have := congrArg Fin.val h; dsimp [Fin.last] at this; omega⟩
  left_inv v := by apply Subtype.ext; ext; rfl
  right_inv i := by ext; rfl
  map_rel_iff' := by intro a b; rfl

/-- `SpiderGraph d` is prime for every $d \ge 2$. -/
theorem isPrimeGraph_spiderGraph (d : ℕ) (hd : 2 ≤ d) :
    IsPrimeGraph (SpiderGraph d) := by
  have h2 : IsPrimeGraph (SpiderGraph 2) := (isPrimeGraph_iff_dec (SpiderGraph 2)).mpr (by decide)
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, d = m + 2 := ⟨d - 2, by omega⟩
  clear hd
  induction m with
  | zero => exact h2
  | succ m ih =>
      let n := m + 1 + 2
      let G := SpiderGraph n
      let u : Fin (n + 4) := Fin.last (n + 3)
      let w₀ : Fin (n + 4) := ⟨n + 2, by omega⟩
      have hG₀ : IsPrimeGraph (G.comap (Subtype.val : {v : Fin (n + 4) // v ≠ u} → Fin (n + 4))) :=
        ih.of_iso (spiderGraphStepIso (m + 2)).symm
      have hw₀_ne : w₀ ≠ u := fun h => by have := congrArg Fin.val h; dsimp [w₀, u, Fin.last] at this; omega
      refine isPrimeGraph_of_add_leaf hG₀ hw₀_ne ?_ ?_ ?_
      · intro v
        have hv := v.2
        by_cases hvu : v = u
        · subst hvu; exact ⟨fun h => False.elim (G.loopless u h), fun h => False.elim (hw₀_ne h.symm)⟩
        · have hvl : v.1 < n + 3 := by
            have hne : v.1 ≠ n + 3 := fun h => hvu (Fin.ext h)
            omega
          dsimp [G, SpiderGraph, spiderAdjLt, u, w₀, Fin.last]
          rw [if_neg (by omega : ¬n + 3 < v.1), if_pos hvl, Fin.ext_iff]
          dsimp
          constructor
          · intro h
            simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
            rcases h with ((⟨_, _⟩ | ⟨_, _⟩) | ⟨_, h2⟩) <;> omega
          · intro h; rw [h]; simp [show 4 ≤ n + 2 by omega]
      · refine ⟨⟨n + 1, by omega⟩, fun h => by have := congrArg Fin.val h; dsimp [u, Fin.last] at this; omega, ?_⟩
        dsimp [G, SpiderGraph, spiderAdjLt, w₀]
        rw [if_neg (by omega : ¬n + 2 < n + 1), if_pos (by omega : n + 1 < n + 2)]
        simp [show 4 ≤ n + 1 by omega]
      · intro z hzu hzw₀
        have hz := z.2
        have hz_lt : z.1 < n + 2 := by
          have h1 : z.1 ≠ n + 3 := fun h => hzu (Fin.ext h)
          have h2 : z.1 ≠ n + 2 := fun h => hzw₀ (Fin.ext h)
          omega
        rcases eq_or_ne z.1 0 with hz0 | hz0
        · refine ⟨⟨(2 : ℕ), by omega⟩,
            fun h => by have := congrArg Fin.val h; dsimp [u, Fin.last] at this; omega,
            fun h => by have := congrArg Fin.val h; dsimp [w₀] at this; omega, ?_⟩
          dsimp [G, SpiderGraph, spiderAdjLt]
          rw [if_pos (by omega : z.1 < 2)]; simp [hz0]
        · rcases eq_or_ne z.1 1 with hz1 | hz1
          · refine ⟨⟨(0 : ℕ), by omega⟩,
              fun h => by have := congrArg Fin.val h; dsimp [u, Fin.last] at this; omega,
              fun h => by have := congrArg Fin.val h; dsimp [w₀] at this; omega, ?_⟩
            dsimp [G, SpiderGraph, spiderAdjLt]
            rw [if_pos (by omega : 0 < z.1)]; simp [hz1]
          · rcases eq_or_ne z.1 2 with hz2 | hz2
            · refine ⟨⟨(0 : ℕ), by omega⟩,
                fun h => by have := congrArg Fin.val h; dsimp [u, Fin.last] at this; omega,
                fun h => by have := congrArg Fin.val h; dsimp [w₀] at this; omega, ?_⟩
              dsimp [G, SpiderGraph, spiderAdjLt]
              rw [if_pos (by omega : 0 < z.1)]; simp [hz2]
            · rcases eq_or_ne z.1 3 with hz3 | hz3
              · refine ⟨⟨(2 : ℕ), by omega⟩,
                  fun h => by have := congrArg Fin.val h; dsimp [u, Fin.last] at this; omega,
                  fun h => by have := congrArg Fin.val h; dsimp [w₀] at this; omega, ?_⟩
                dsimp [G, SpiderGraph, spiderAdjLt]
                rw [if_neg (by omega : ¬z.1 < 2), if_pos (by omega : 2 < z.1)]; simp [hz3]
              · rcases eq_or_ne z.1 4 with hz4 | hz4
                · refine ⟨⟨(0 : ℕ), by omega⟩,
                    fun h => by have := congrArg Fin.val h; dsimp [u, Fin.last] at this; omega,
                    fun h => by have := congrArg Fin.val h; dsimp [w₀] at this; omega, ?_⟩
                  dsimp [G, SpiderGraph, spiderAdjLt]
                  rw [if_pos (by omega : 0 < z.1)]; simp [hz4]
                · refine ⟨⟨z.1 - 1, by omega⟩,
                    fun h => by have := congrArg Fin.val h; dsimp [u, Fin.last] at this; omega,
                    fun h => by have := congrArg Fin.val h; dsimp [w₀] at this; omega, ?_⟩
                  dsimp [G, SpiderGraph, spiderAdjLt]
                  rw [if_neg (by omega : ¬z.1 < z.1 - 1), if_pos (by omega : z.1 - 1 < z.1)]
                  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
                  right; exact ⟨by omega, by omega⟩

/-- Every vertex in `SpiderGraph d` ($d \ge 2$) has degree at most $3 \le (d + 4) - 3$. -/
theorem spiderGraph_deg_le (d : ℕ) (hd : 2 ≤ d) (u : Fin (d + 4)) :
    (neighborFinsetIn (SpiderGraph d) u Finset.univ).card ≤ Fintype.card (Fin (d + 4)) - 3 := by
  rw [Fintype.card_fin]
  have hu := u.2
  by_cases hu0 : u.1 = 0
  · let a₁ : Fin (d + 4) := ⟨1, by omega⟩
    let a₂ : Fin (d + 4) := ⟨2, by omega⟩
    let a₄ : Fin (d + 4) := ⟨4, by omega⟩
    have hsub : neighborFinsetIn (SpiderGraph d) u Finset.univ ⊆ ({a₁, a₂, a₄} : Finset (Fin (d + 4))) := by
      intro v hv
      rw [mem_neighborFinsetIn_iff] at hv
      have hadj := hv.2
      have hne : u ≠ v := (SpiderGraph d).ne_of_adj hadj
      have h0lt : 0 < v.1 := by have := Fin.ext_iff.not.mp hne; omega
      dsimp [SpiderGraph, spiderAdjLt] at hadj
      rw [if_pos (by omega : u.1 < v.1)] at hadj
      simp only [hu0, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hadj
      have hv_or : v.1 = 1 ∨ v.1 = 2 ∨ v.1 = 4 := by omega
      rcases hv_or with hv1 | hv2 | hv4
      · have hveq : v = a₁ := Fin.ext hv1; rw [hveq]; simp
      · have hveq : v = a₂ := Fin.ext hv2; rw [hveq]; simp
      · have hveq : v = a₄ := Fin.ext hv4; rw [hveq]; simp
    have h1 := Finset.card_le_card hsub
    have h2 := card_triple_le_three a₁ a₂ a₄
    omega
  · let pred : Fin (d + 4) :=
      if u.1 ≤ 2 ∨ u.1 = 4 then ⟨0, by omega⟩
      else ⟨u.1 - 1, by omega⟩
    let succ : Fin (d + 4) :=
      if u.1 = 2 then ⟨3, by omega⟩
      else if hs : u.1 + 1 < d + 4 then ⟨u.1 + 1, hs⟩
      else pred
    have hsub : neighborFinsetIn (SpiderGraph d) u Finset.univ ⊆ ({pred, succ} : Finset (Fin (d + 4))) := by
      intro v hv
      have hvb := v.2
      rw [mem_neighborFinsetIn_iff] at hv
      have hadj := hv.2
      by_cases huv : u.1 < v.1
      · dsimp [SpiderGraph, spiderAdjLt] at hadj
        rw [if_pos huv] at hadj
        simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hadj
        rcases hadj with ((⟨h0, _⟩ | ⟨hu2, hv3⟩) | ⟨hu4, hv_s⟩)
        · omega
        · have hv_succ : v = succ := by
            dsimp [succ]; rw [if_pos hu2]; exact Fin.ext hv3
          rw [hv_succ]; simp
        · have hv_succ : v = succ := by
            dsimp [succ]
            rw [if_neg (by omega : ¬u.1 = 2), dif_pos (by omega : u.1 + 1 < d + 4)]
            exact Fin.ext hv_s
          rw [hv_succ]; simp
      · have hvu : v.1 < u.1 := by
          have hne := (SpiderGraph d).ne_of_adj hadj
          have := Fin.ext_iff.not.mp hne; omega
        dsimp [SpiderGraph, spiderAdjLt] at hadj
        rw [if_neg huv, if_pos hvu] at hadj
        simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hadj
        rcases hadj with ((⟨hv0, hu_or⟩ | ⟨hv2, hu3⟩) | ⟨hv4, hu_s⟩)
        · have hv_pred : v = pred := by
            dsimp [pred]; rw [if_pos (by omega : u.1 ≤ 2 ∨ u.1 = 4)]; exact Fin.ext hv0
          rw [hv_pred]; simp
        · have hv_pred : v = pred := by
            dsimp [pred]; rw [if_neg (by omega : ¬(u.1 ≤ 2 ∨ u.1 = 4))]
            exact Fin.ext (show v.1 = u.1 - 1 by omega)
          rw [hv_pred]; simp
        · have hv_pred : v = pred := by
            dsimp [pred]; rw [if_neg (by omega : ¬(u.1 ≤ 2 ∨ u.1 = 4))]
            exact Fin.ext (show v.1 = u.1 - 1 by omega)
          rw [hv_pred]; simp
    have h1 := Finset.card_le_card hsub
    have h2 := card_pair_le_two pred succ
    omega

/-- **Strict Containment Witness 1 (`spiderGraph2_strict_containment`)**:
`SpiderGraph 2 ∈ InHClosureBNew` AND `¬InHClosure 9 (SpiderGraph 2)`. -/
theorem spiderGraph2_strict_containment :
    InHClosureBNew (SpiderGraph 2) ∧ ¬InHClosure 9 (SpiderGraph 2) := by
  refine ⟨inHClosureBNew_spiderGraph 2 le_rfl (by omega), ?_⟩
  intro hH9
  have hPrime : IsPrimeGraph (SpiderGraph 2)ᶜ := (isPrimeGraph_compl_iff _).mpr (isPrimeGraph_spiderGraph 2 le_rfl)
  have hMinDeg : ∀ u : Fin 6, 2 ≤ (neighborFinsetIn (SpiderGraph 2)ᶜ u Finset.univ).card :=
    g₀Compl_min_deg_ge_two (SpiderGraph 2) (by decide) (spiderGraph_deg_le 2 le_rfl)
  have hB9 : InBStar 9 (SpiderGraph 2)ᶜ :=
    inBStar_of_inJClosure_prime_minDeg_ge_two hPrime hMinDeg hH9.2
  have s_sp2 : orderedEdgeCount (SpiderGraph 2) = 10 := by decide
  rcases hB9 with he | he | he | he | he | ⟨t, _, _, he | he⟩
  · obtain ⟨e⟩ := he; have := Fintype.card_congr e.toEquiv; simp at this
  · obtain ⟨e⟩ := he; have := Fintype.card_congr e.toEquiv; simp at this
  · obtain ⟨e⟩ := he; have := Fintype.card_congr e.toEquiv; simp at this
  · obtain ⟨e⟩ := he
    have heq := orderedEdgeCount_iso (SpiderGraph 2) BirdGraphᶜ (isoOfComplLeft e)
    have s2 : orderedEdgeCount BirdGraphᶜ = 18 := by decide
    omega
  · obtain ⟨e⟩ := he
    have heq := orderedEdgeCount_iso (SpiderGraph 2) BirdGraph (isoOfComplBoth e)
    have s2 : orderedEdgeCount BirdGraph = 12 := by decide
    omega
  · obtain ⟨e⟩ := he
    have ht6 : t = 6 := by have := Fintype.card_congr e.toEquiv; simp at this; omega
    subst ht6
    have heq := orderedEdgeCount_iso (SpiderGraph 2) (pathGraph 6)ᶜ (isoOfComplLeft e)
    have s2 : orderedEdgeCount (pathGraph 6)ᶜ = 20 := by decide
    omega
  · obtain ⟨e⟩ := he
    have ht6 : t = 6 := by have := Fintype.card_congr e.toEquiv; simp at this; omega
    subst ht6
    let iso : SpiderGraph 2 ≃g pathGraph 6 := isoOfComplBoth e
    have h01 : (pathGraph 6).Adj (iso 0) (iso 1) := iso.map_rel_iff.mpr (by decide)
    have h02 : (pathGraph 6).Adj (iso 0) (iso 2) := iso.map_rel_iff.mpr (by decide)
    have h04 : (pathGraph 6).Adj (iso 0) (iso 4) := iso.map_rel_iff.mpr (by decide)
    have hne12 : iso 1 ≠ iso 2 := iso.injective.ne (by decide)
    have hne14 : iso 1 ≠ iso 4 := iso.injective.ne (by decide)
    have hne24 : iso 2 ≠ iso 4 := iso.injective.ne (by decide)
    rw [pathGraph_adj] at h01 h02 h04
    have := Fin.ext_iff.not.mp hne12
    have := Fin.ext_iff.not.mp hne14
    have := Fin.ext_iff.not.mp hne24
    omega

/-- **Strict Containment Witness 2 (`spiderGraph6_strict_containment`)**:
`SpiderGraph 6 ∈ InHClosureBInfty` AND `¬InHClosureBNew (SpiderGraph 6)`. -/
theorem spiderGraph6_strict_containment :
    InHClosureBInfty (SpiderGraph 6) ∧ ¬InHClosureBNew (SpiderGraph 6) := by
  refine ⟨⟨InJClosureBInfty.base _ (Or.inr (Or.inr (Or.inl ⟨6, le_rfl, Or.inl ⟨SimpleGraph.Iso.refl⟩⟩))),
           InJClosureBInfty.base _ (Or.inr (Or.inr (Or.inl ⟨6, le_rfl, Or.inr ⟨SimpleGraph.Iso.refl⟩⟩)))⟩, ?_⟩
  intro hHNew
  have hPrime : IsPrimeGraph (SpiderGraph 6)ᶜ := (isPrimeGraph_compl_iff _).mpr (isPrimeGraph_spiderGraph 6 (by omega))
  have hMinDeg : ∀ u : Fin 10, 2 ≤ (neighborFinsetIn (SpiderGraph 6)ᶜ u Finset.univ).card :=
    g₀Compl_min_deg_ge_two (SpiderGraph 6) (by decide) (spiderGraph_deg_le 6 (by omega))
  have hBNew : InBNew (SpiderGraph 6)ᶜ :=
    inBNew_of_inJClosureBNew_prime_minDeg_ge_two hPrime hMinDeg hHNew.2
  have s_sp6 : orderedEdgeCount (SpiderGraph 6) = 18 := by decide
  rcases hBNew with h9 | he | ⟨d, hd2, hd5, he | he⟩ | ⟨d, hd3, hd6, he | he⟩
  · rcases h9 with he | he | he | he | he | ⟨t, _, ht9, he | he⟩
    · obtain ⟨e⟩ := he; have := Fintype.card_congr e.toEquiv; simp at this
    · obtain ⟨e⟩ := he; have := Fintype.card_congr e.toEquiv; simp at this
    · obtain ⟨e⟩ := he; have := Fintype.card_congr e.toEquiv; simp at this
    · obtain ⟨e⟩ := he; have := Fintype.card_congr e.toEquiv; simp at this
    · obtain ⟨e⟩ := he; have := Fintype.card_congr e.toEquiv; simp at this
    · obtain ⟨e⟩ := he; have := Fintype.card_congr e.toEquiv; simp at this; omega
    · obtain ⟨e⟩ := he; have := Fintype.card_congr e.toEquiv; simp at this; omega
  · obtain ⟨e⟩ := he; have := Fintype.card_congr e.toEquiv; simp at this
  · obtain ⟨e⟩ := he; have := Fintype.card_congr e.toEquiv; simp at this; omega
  · obtain ⟨e⟩ := he; have := Fintype.card_congr e.toEquiv; simp at this; omega
  · obtain ⟨e⟩ := he
    have hd6_eq : d = 6 := by have := Fintype.card_congr e.toEquiv; simp at this; omega
    subst hd6_eq
    have heq := orderedEdgeCount_iso (SpiderGraph 6) (BirdDGraph 6)ᶜ (isoOfComplLeft e)
    have s2 : orderedEdgeCount (BirdDGraph 6)ᶜ = 70 := by decide
    omega
  · obtain ⟨e⟩ := he
    have hd6_eq : d = 6 := by have := Fintype.card_congr e.toEquiv; simp at this; omega
    subst hd6_eq
    have heq := orderedEdgeCount_iso (SpiderGraph 6) (BirdDGraph 6) (isoOfComplBoth e)
    have s2 : orderedEdgeCount (BirdDGraph 6) = 20 := by decide
    omega

/-- Deleting the last vertex `Fin.last (d + 3)` from `BirdDGraph (d + 1)` yields `BirdDGraph d`. -/
def birdDGraphStepIso (d : ℕ) :
    (BirdDGraph (d + 1)).comap
      (Subtype.val : {v : Fin (d + 1 + 4) // v ≠ Fin.last (d + 4)} → Fin (d + 1 + 4)) ≃g
      BirdDGraph d where
  toFun v := ⟨v.1.1, by
    have hne : v.1.1 ≠ d + 4 := fun h => v.2 (Fin.ext h)
    have := v.1.2
    omega⟩
  invFun i := ⟨⟨i.1, by omega⟩, fun h => by
    have := congrArg Fin.val h; dsimp [Fin.last] at this; omega⟩
  left_inv v := by apply Subtype.ext; ext; rfl
  right_inv i := by ext; rfl
  map_rel_iff' := by intro a b; rfl

/-- `BirdDGraph d` is prime for every $d \ge 2$. -/
theorem isPrimeGraph_birdDGraph (d : ℕ) (hd : 2 ≤ d) :
    IsPrimeGraph (BirdDGraph d) := by
  have h2 : IsPrimeGraph (BirdDGraph 2) := (isPrimeGraph_iff_dec (BirdDGraph 2)).mpr (by decide)
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, d = m + 2 := ⟨d - 2, by omega⟩
  clear hd
  induction m with
  | zero => exact h2
  | succ m ih =>
      let n := m + 1 + 2
      let G := BirdDGraph n
      let u : Fin (n + 4) := Fin.last (n + 3)
      let w₀ : Fin (n + 4) := ⟨n + 2, by omega⟩
      have hG₀ : IsPrimeGraph (G.comap (Subtype.val : {v : Fin (n + 4) // v ≠ u} → Fin (n + 4))) :=
        ih.of_iso (birdDGraphStepIso (m + 2)).symm
      have hw₀_ne : w₀ ≠ u := fun h => by have := congrArg Fin.val h; dsimp [w₀, u, Fin.last] at this; omega
      refine isPrimeGraph_of_add_leaf hG₀ hw₀_ne ?_ ?_ ?_
      · intro v
        have hv := v.2
        by_cases hvu : v = u
        · subst hvu; exact ⟨fun h => False.elim (G.loopless u h), fun h => False.elim (hw₀_ne h.symm)⟩
        · have hvl : v.1 < n + 3 := by
            have hne : v.1 ≠ n + 3 := fun h => hvu (Fin.ext h)
            omega
          dsimp [G, BirdDGraph, birdDAdjLt, u, w₀, Fin.last]
          rw [if_neg (by omega : ¬n + 3 < v.1), if_pos hvl, Fin.ext_iff]
          dsimp
          constructor
          · intro h
            simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
            rcases h with (((⟨_, _⟩ | ⟨_, _⟩) | ⟨_, _⟩) | ⟨_, h2⟩) <;> omega
          · intro h; rw [h]; simp [show 4 ≤ n + 2 by omega]
      · refine ⟨⟨n + 1, by omega⟩, fun h => by have := congrArg Fin.val h; dsimp [u, Fin.last] at this; omega, ?_⟩
        dsimp [G, BirdDGraph, birdDAdjLt, w₀]
        rw [if_neg (by omega : ¬n + 2 < n + 1), if_pos (by omega : n + 1 < n + 2)]
        simp [show 4 ≤ n + 1 by omega]
      · intro z hzu hzw₀
        have hz := z.2
        have hz_lt : z.1 < n + 2 := by
          have h1 : z.1 ≠ n + 3 := fun h => hzu (Fin.ext h)
          have h2 : z.1 ≠ n + 2 := fun h => hzw₀ (Fin.ext h)
          omega
        rcases eq_or_ne z.1 0 with hz0 | hz0
        · let k1 : ℕ := 1
          have hk1 : k1 = 1 := rfl
          refine ⟨⟨k1, by omega⟩,
            fun h => by have := congrArg Fin.val h; dsimp [u, Fin.last] at this; omega,
            fun h => by have := congrArg Fin.val h; dsimp [w₀] at this; omega, ?_⟩
          dsimp [G, BirdDGraph, birdDAdjLt]
          rw [if_pos (by omega : z.1 < k1)]; simp [hz0, hk1]
        · rcases eq_or_ne z.1 1 with hz1 | hz1
          · refine ⟨⟨(0 : ℕ), by omega⟩,
              fun h => by have := congrArg Fin.val h; dsimp [u, Fin.last] at this; omega,
              fun h => by have := congrArg Fin.val h; dsimp [w₀] at this; omega, ?_⟩
            dsimp [G, BirdDGraph, birdDAdjLt]
            rw [if_pos (by omega : 0 < z.1)]; simp [hz1]
          · rcases eq_or_ne z.1 2 with hz2 | hz2
            · refine ⟨⟨(3 : ℕ), by omega⟩,
                fun h => by have := congrArg Fin.val h; dsimp [u, Fin.last] at this; omega,
                fun h => by have := congrArg Fin.val h; dsimp [w₀] at this; omega, ?_⟩
              dsimp [G, BirdDGraph, birdDAdjLt]
              rw [if_pos (by omega : z.1 < 3)]; simp [hz2]
            · rcases eq_or_ne z.1 3 with hz3 | hz3
              · refine ⟨⟨(2 : ℕ), by omega⟩,
                  fun h => by have := congrArg Fin.val h; dsimp [u, Fin.last] at this; omega,
                  fun h => by have := congrArg Fin.val h; dsimp [w₀] at this; omega, ?_⟩
                dsimp [G, BirdDGraph, birdDAdjLt]
                rw [if_neg (by omega : ¬z.1 < 2), if_pos (by omega : 2 < z.1)]; simp [hz3]
              · rcases eq_or_ne z.1 4 with hz4 | hz4
                · refine ⟨⟨(2 : ℕ), by omega⟩,
                    fun h => by have := congrArg Fin.val h; dsimp [u, Fin.last] at this; omega,
                    fun h => by have := congrArg Fin.val h; dsimp [w₀] at this; omega, ?_⟩
                  dsimp [G, BirdDGraph, birdDAdjLt]
                  rw [if_neg (by omega : ¬z.1 < 2), if_pos (by omega : 2 < z.1)]; simp [hz4]
                · refine ⟨⟨z.1 - 1, by omega⟩,
                    fun h => by have := congrArg Fin.val h; dsimp [u, Fin.last] at this; omega,
                    fun h => by have := congrArg Fin.val h; dsimp [w₀] at this; omega, ?_⟩
                  dsimp [G, BirdDGraph, birdDAdjLt]
                  rw [if_neg (by omega : ¬z.1 < z.1 - 1), if_pos (by omega : z.1 - 1 < z.1)]
                  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
                  right; exact ⟨by omega, by omega⟩

/-- Every vertex in `BirdDGraph d` ($d \ge 2$) has degree at most $3 \le (d + 4) - 3$. -/
theorem birdDGraph_deg_le (d : ℕ) (hd : 2 ≤ d) (u : Fin (d + 4)) :
    (neighborFinsetIn (BirdDGraph d) u Finset.univ).card ≤ Fintype.card (Fin (d + 4)) - 3 := by
  rw [Fintype.card_fin]
  have hu := u.2
  by_cases hu4 : u.1 < 4
  · let b₀ : Fin (d + 4) := ⟨0, by omega⟩
    let b₁ : Fin (d + 4) := ⟨1, by omega⟩
    let b₂ : Fin (d + 4) := ⟨2, by omega⟩
    let b₃ : Fin (d + 4) := ⟨3, by omega⟩
    let b₄ : Fin (d + 4) := ⟨4, by omega⟩
    let S₃ : Finset (Fin (d + 4)) :=
      if u.1 = 1 then {b₀, b₂, b₃}
      else if u.1 = 2 then {b₁, b₃, b₄}
      else {b₁, b₂, b₃}
    have hsub : neighborFinsetIn (BirdDGraph d) u Finset.univ ⊆ S₃ := by
      intro v hv
      have hvb := v.2
      rw [mem_neighborFinsetIn_iff] at hv
      have hadj := hv.2
      have hne := (BirdDGraph d).ne_of_adj hadj
      by_cases huv : u.1 < v.1
      · dsimp [BirdDGraph, birdDAdjLt] at hadj
        rw [if_pos huv] at hadj
        simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hadj
        rcases eq_or_ne u.1 0 with h0 | h0
        · have hv1 : v = b₁ := Fin.ext (show v.1 = 1 by omega)
          dsimp [S₃]; rw [if_neg (by omega), if_neg (by omega), hv1]; simp
        · rcases eq_or_ne u.1 1 with h1 | h1
          · have hv_or : v.1 = 2 ∨ v.1 = 3 := by omega
            dsimp [S₃]; rw [if_pos h1]
            rcases hv_or with hv2 | hv3
            · rw [show v = b₂ from Fin.ext hv2]; simp
            · rw [show v = b₃ from Fin.ext hv3]; simp
          · rcases eq_or_ne u.1 2 with h2 | h2
            · have hv_or : v.1 = 3 ∨ v.1 = 4 := by omega
              dsimp [S₃]; rw [if_neg h1, if_pos h2]
              rcases hv_or with hv3 | hv4
              · rw [show v = b₃ from Fin.ext hv3]; simp
              · rw [show v = b₄ from Fin.ext hv4]; simp
            · omega
      · have hvu : v.1 < u.1 := by have := Fin.ext_iff.not.mp hne; omega
        dsimp [BirdDGraph, birdDAdjLt] at hadj
        rw [if_neg huv, if_pos hvu] at hadj
        simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hadj
        rcases eq_or_ne u.1 1 with h1 | h1
        · have hv0 : v = b₀ := Fin.ext (show v.1 = 0 by omega)
          dsimp [S₃]; rw [if_pos h1, hv0]; simp
        · rcases eq_or_ne u.1 2 with h2 | h2
          · have hv1 : v = b₁ := Fin.ext (show v.1 = 1 by omega)
            dsimp [S₃]; rw [if_neg h1, if_pos h2, hv1]; simp
          · have hv_or : v.1 = 1 ∨ v.1 = 2 := by omega
            dsimp [S₃]; rw [if_neg h1, if_neg h2]
            rcases hv_or with hv1 | hv2
            · rw [show v = b₁ from Fin.ext hv1]; simp
            · rw [show v = b₂ from Fin.ext hv2]; simp
    have hcard_S₃ : S₃.card ≤ 3 := by
      dsimp [S₃]; split_ifs <;> exact card_triple_le_three _ _ _
    have h1 := Finset.card_le_card hsub
    omega
  · let pred : Fin (d + 4) := if u.1 = 4 then ⟨2, by omega⟩ else ⟨u.1 - 1, by omega⟩
    let succ : Fin (d + 4) := if hs : u.1 + 1 < d + 4 then ⟨u.1 + 1, hs⟩ else pred
    have hsub : neighborFinsetIn (BirdDGraph d) u Finset.univ ⊆ ({pred, succ} : Finset (Fin (d + 4))) := by
      intro v hv
      have hvb := v.2
      rw [mem_neighborFinsetIn_iff] at hv
      have hadj := hv.2
      have hne := (BirdDGraph d).ne_of_adj hadj
      by_cases huv : u.1 < v.1
      · dsimp [BirdDGraph, birdDAdjLt] at hadj
        rw [if_pos huv] at hadj
        simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hadj
        have hv_s : v = succ := by
          dsimp [succ]; rw [dif_pos (by omega : u.1 + 1 < d + 4)]
          exact Fin.ext (show v.1 = u.1 + 1 by omega)
        rw [hv_s]; simp
      · have hvu : v.1 < u.1 := by have := Fin.ext_iff.not.mp hne; omega
        dsimp [BirdDGraph, birdDAdjLt] at hadj
        rw [if_neg huv, if_pos hvu] at hadj
        simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hadj
        by_cases hu_eq4 : u.1 = 4
        · have hv_p : v = pred := by
            dsimp [pred]; rw [if_pos hu_eq4]; exact Fin.ext (show v.1 = 2 by omega)
          rw [hv_p]; simp
        · have hv_p : v = pred := by
            dsimp [pred]; rw [if_neg hu_eq4]; exact Fin.ext (show v.1 = u.1 - 1 by omega)
          rw [hv_p]; simp
    have h1 := Finset.card_le_card hsub
    have h2 := card_pair_le_two pred succ
    omega

/-- `BirdDGraph 2 ≃g BirdGraph`. -/
def birdDGraph2IsoBirdGraph : BirdDGraph 2 ≃g BirdGraph where
  toEquiv :=
    { toFun := ![5, 1, 0, 2, 3, 4]
      invFun := ![2, 1, 3, 4, 5, 0]
      left_inv := fun i => by fin_cases i <;> rfl
      right_inv := fun i => by fin_cases i <;> rfl }
  map_rel_iff' := by intro i j; fin_cases i <;> fin_cases j <;> decide

/-- `BullGraph` (`BirdDGraph 1`) is self-complementary (`BullGraphᶜ ≃g BullGraph`). -/
def bullGraphSelfComplIso : BullGraphᶜ ≃g BullGraph where
  toEquiv :=
    { toFun := ![1, 4, 0, 3, 2]
      invFun := ![2, 0, 4, 3, 1]
      left_inv := fun i => by fin_cases i <;> rfl
      right_inv := fun i => by fin_cases i <;> rfl }
  map_rel_iff' := by intro i j; fin_cases i <;> fin_cases j <;> decide

/-- Base tower hypotheses for `(pathGraph k, ⟨k - 1, _⟩)` ($k \ge 6$). -/
theorem pathGraph_genPrimeTower_base_props (k : ℕ) (hk : 6 ≤ k) :
    IsPrimeGraph (pathGraph k) ∧ 6 ≤ Fintype.card (Fin k) ∧
    (∀ u : Fin k, (neighborFinsetIn (pathGraph k) u Finset.univ).card ≤ Fintype.card (Fin k) - 3) ∧
    (neighborFinsetIn (pathGraph k) ⟨k - 1, by omega⟩ Finset.univ).card = 1 ∧
    ¬IsSplitGraph (pathGraph k) ∧
    InHClosureBInfty (pathGraph k) ∧
    InHClosureBInfty ((pathGraph k).comap (Subtype.val : {w : Fin k // w ≠ ⟨k - 1, by omega⟩} → Fin k)) := by
  have inBInfty_path : ∀ m : ℕ, 1 ≤ m → InHClosureBInfty (pathGraph m) := by
    intro m hm1
    by_cases hm9 : m ≤ 9
    · exact inHClosureBNew_to_inHClosureBInfty (inHClosureBNew_pathGraph m hm1 hm9)
    · exact ⟨InJClosureBInfty.base _ (Or.inr (Or.inl ⟨m, by omega, Or.inl ⟨SimpleGraph.Iso.refl⟩⟩)),
             InJClosureBInfty.base _ (Or.inr (Or.inl ⟨m, by omega, Or.inr ⟨SimpleGraph.Iso.refl⟩⟩))⟩
  refine ⟨isPrimeGraph_pathGraph (by omega), by rw [Fintype.card_fin]; exact hk, ?_, ?_, ?_,
    inBInfty_path k (by omega), ?_⟩
  · intro u
    rw [Fintype.card_fin]
    have hu := u.2
    let p : Fin k := ⟨u.1 - 1, by omega⟩
    let s : Fin k := ⟨min (u.1 + 1) (k - 1), by omega⟩
    have hsub : neighborFinsetIn (pathGraph k) u Finset.univ ⊆ ({p, s} : Finset (Fin k)) := by
      intro v hv
      have hvb := v.2
      rw [mem_neighborFinsetIn_iff, pathGraph_adj] at hv
      rcases hv.2 with hv1 | hv2
      · rw [show v = s from Fin.ext (by dsimp [s]; omega)]; simp
      · rw [show v = p from Fin.ext (by dsimp [p]; omega)]; simp
    have h1 := Finset.card_le_card hsub
    have h2 := card_pair_le_two p s
    omega
  · have h_eq : neighborFinsetIn (pathGraph k) ⟨k - 1, by omega⟩ Finset.univ = {⟨k - 2, by omega⟩} := by
      ext v
      have hvb := v.2
      rw [mem_neighborFinsetIn_iff, Finset.mem_singleton, pathGraph_adj, Fin.ext_iff]
      simp only [Finset.mem_univ, true_and]
      constructor
      · intro h; omega
      · intro h; right; omega
    rw [h_eq, Finset.card_singleton]
  · intro hsp
    let emb : pathGraph 6 ↪g pathGraph k :=
      { toEmbedding := Fin.castLEEmb hk
        map_rel_iff' := by intro _ _; simp [pathGraph_adj] }
    exact not_isSplitGraph_pathGraph_six (IsSplitGraph.of_embedding emb hsp)
  · let e_del : (pathGraph k).comap (Subtype.val : {w : Fin k // w ≠ ⟨k - 1, by omega⟩} → Fin k) ≃g
        pathGraph (k - 1) :=
      { toFun := fun v => ⟨v.1.1, by
          have := v.1.2
          have hne : v.1.1 ≠ k - 1 := fun h => v.2 (Fin.ext h)
          omega⟩
        invFun := fun i => ⟨⟨i.1, by omega⟩, fun h => by have := congrArg Fin.val h; dsimp at this; omega⟩
        left_inv := fun _ => by apply Subtype.ext; ext; rfl
        right_inv := fun _ => by ext; rfl
        map_rel_iff' := by intro _ _; simp [pathGraph_adj] }
    exact inHClosureBInfty_of_iso e_del.symm (inBInfty_path (k - 1) (by omega))

/-- Deleting `Fin.last 5` (`5`) from `SpiderGraph 2` yields `substGraph (pathGraph 4) 0 (⊥ : SimpleGraph (Fin 2))`. -/
def spiderGraph2DeleteLastIso :
    substGraph (pathGraph 4) 0 (⊥ : SimpleGraph (Fin 2)) ≃g
      (SpiderGraph 2).comap (Subtype.val : {w : Fin 6 // w ≠ Fin.last 5} → Fin 6) where
  toFun s :=
    match s with
    | Sum.inl ⟨0, h⟩ => False.elim (h rfl)
    | Sum.inl ⟨1, _⟩ => ⟨0, by decide⟩
    | Sum.inl ⟨2, _⟩ => ⟨2, by decide⟩
    | Sum.inl ⟨3, _⟩ => ⟨3, by decide⟩
    | Sum.inr 0 => ⟨1, by decide⟩
    | Sum.inr 1 => ⟨4, by decide⟩
  invFun v :=
    match v with
    | ⟨0, _⟩ => Sum.inl ⟨1, by decide⟩
    | ⟨1, _⟩ => Sum.inr 0
    | ⟨2, _⟩ => Sum.inl ⟨2, by decide⟩
    | ⟨3, _⟩ => Sum.inl ⟨3, by decide⟩
    | ⟨4, _⟩ => Sum.inr 1
    | ⟨5, h⟩ => False.elim (h rfl)
  left_inv := by rintro (⟨i, hi⟩ | i) <;> fin_cases i <;> first | rfl | exact False.elim (hi rfl)
  right_inv := by rintro ⟨i, hi⟩; fin_cases i <;> first | rfl | exact False.elim (hi rfl)
  map_rel_iff' := by
    rintro (⟨i, hi⟩ | i) (⟨j, hj⟩ | j)
    · fin_cases i <;> fin_cases j <;> decide +revert
    · fin_cases i <;> fin_cases j <;> decide +revert
    · fin_cases i <;> fin_cases j <;> decide +revert
    · fin_cases i <;> fin_cases j <;> decide +revert

/-- Base tower hypotheses for `(SpiderGraph d, Fin.last (d + 3))` ($d \ge 2$). -/
theorem spiderGraph_genPrimeTower_base_props (d : ℕ) (hd : 2 ≤ d) :
    IsPrimeGraph (SpiderGraph d) ∧ 6 ≤ Fintype.card (Fin (d + 4)) ∧
    (∀ u : Fin (d + 4), (neighborFinsetIn (SpiderGraph d) u Finset.univ).card ≤ Fintype.card (Fin (d + 4)) - 3) ∧
    (neighborFinsetIn (SpiderGraph d) (Fin.last (d + 3)) Finset.univ).card = 1 ∧
    ¬IsSplitGraph (SpiderGraph d) ∧
    InHClosureBInfty (SpiderGraph d) ∧
    InHClosureBInfty ((SpiderGraph d).comap (Subtype.val : {w : Fin (d + 4) // w ≠ Fin.last (d + 3)} → Fin (d + 4))) := by
  have inBInfty_sp : ∀ m : ℕ, 2 ≤ m → InHClosureBInfty (SpiderGraph m) := by
    intro m hm2
    by_cases hm5 : m ≤ 5
    · exact inHClosureBNew_to_inHClosureBInfty (inHClosureBNew_spiderGraph m hm2 hm5)
    · exact ⟨InJClosureBInfty.base _ (Or.inr (Or.inr (Or.inl ⟨m, by omega, Or.inl ⟨SimpleGraph.Iso.refl⟩⟩))),
             InJClosureBInfty.base _ (Or.inr (Or.inr (Or.inl ⟨m, by omega, Or.inr ⟨SimpleGraph.Iso.refl⟩⟩)))⟩
  have hleaf_last : ∀ w : Fin (d + 4), (SpiderGraph d).Adj (Fin.last (d + 3)) w ↔ w = ⟨d + 2, by omega⟩ := by
    intro w
    have hw := w.2
    by_cases hwl : w = Fin.last (d + 3)
    · subst hwl; simp [Fin.ext_iff]
    · have hwlt : w.1 < d + 3 := by
        have hne : w.1 ≠ d + 3 := fun h => hwl (Fin.ext h)
        omega
      dsimp [SpiderGraph, spiderAdjLt, Fin.last]
      rw [if_neg (by omega : ¬d + 3 < w.1), if_pos hwlt, Fin.ext_iff]
      dsimp
      constructor
      · intro h
        simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
        rcases h with ((⟨_, _⟩ | ⟨_, _⟩) | ⟨_, h2⟩) <;> omega
      · intro h; rw [h]; simp [show 4 ≤ d + 2 by omega]
  refine ⟨isPrimeGraph_spiderGraph d hd, by rw [Fintype.card_fin]; omega,
    spiderGraph_deg_le d hd, ?_, ?_, inBInfty_sp d hd, ?_⟩
  · have h_eq : neighborFinsetIn (SpiderGraph d) (Fin.last (d + 3)) Finset.univ = {⟨d + 2, by omega⟩} := by
      ext w; rw [mem_neighborFinsetIn_iff, Finset.mem_singleton]; simp [hleaf_last w]
    rw [h_eq, Finset.card_singleton]
  · intro hsp
    have h2 : ¬IsSplitGraph (SpiderGraph 2) :=
      not_isSplitGraph_of_two_indep_edges (a := (2 : Fin 6)) (b := 3) (c := 4) (d := 5)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    let emb : SpiderGraph 2 ↪g SpiderGraph d :=
      { toEmbedding := Fin.castLEEmb (by omega : 6 ≤ d + 4)
        map_rel_iff' := by intro _ _; rfl }
    exact h2 (IsSplitGraph.of_embedding emb hsp)
  · by_cases hd2 : d = 2
    · subst hd2
      exact inHClosureBNew_to_inHClosureBInfty
        (inHClosureBNew_of_iso spiderGraph2DeleteLastIso
          (inHClosureBNew_subst 0 (inHClosureBNew_pathGraph 4 (by omega) (by omega)) inHClosureBNew_bot_fin2))
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, d = m + 3 := ⟨d - 3, by omega⟩
      exact inHClosureBInfty_of_iso (spiderGraphStepIso (m + 2)).symm (inBInfty_sp (m + 2) (by omega))

/-- Base tower hypotheses for `(BirdDGraph d, Fin.last (d + 3))` ($d \ge 2$). -/
theorem birdDGraph_genPrimeTower_base_props (d : ℕ) (hd : 2 ≤ d) :
    IsPrimeGraph (BirdDGraph d) ∧ 6 ≤ Fintype.card (Fin (d + 4)) ∧
    (∀ u : Fin (d + 4), (neighborFinsetIn (BirdDGraph d) u Finset.univ).card ≤ Fintype.card (Fin (d + 4)) - 3) ∧
    (neighborFinsetIn (BirdDGraph d) (Fin.last (d + 3)) Finset.univ).card = 1 ∧
    ¬IsSplitGraph (BirdDGraph d) ∧
    InHClosureBInfty (BirdDGraph d) ∧
    InHClosureBInfty ((BirdDGraph d).comap (Subtype.val : {w : Fin (d + 4) // w ≠ Fin.last (d + 3)} → Fin (d + 4))) := by
  have inBInfty_bird : ∀ m : ℕ, 1 ≤ m → InHClosureBInfty (BirdDGraph m) := by
    intro m hm1
    rcases eq_or_ne m 1 with rfl | hm_ne1
    · exact inHClosureBNew_to_inHClosureBInfty
        ⟨InJClosureBNew.base _ (Or.inr (Or.inl ⟨SimpleGraph.Iso.refl⟩)),
         InJClosureBNew.base _ (Or.inr (Or.inl ⟨bullGraphSelfComplIso⟩))⟩
    · rcases eq_or_ne m 2 with rfl | hm_ne2
      · exact inHClosureBNew_to_inHClosureBInfty
          ⟨InJClosureBNew.base _ (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨birdDGraph2IsoBirdGraph⟩))))),
           InJClosureBNew.base _ (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨complIso birdDGraph2IsoBirdGraph⟩))))))⟩
      · by_cases hm6 : m ≤ 6
        · exact inHClosureBNew_to_inHClosureBInfty
            ⟨InJClosureBNew.base _ (Or.inr (Or.inr (Or.inr ⟨m, by omega, hm6, Or.inl ⟨SimpleGraph.Iso.refl⟩⟩))),
             InJClosureBNew.base _ (Or.inr (Or.inr (Or.inr ⟨m, by omega, hm6, Or.inr ⟨SimpleGraph.Iso.refl⟩⟩)))⟩
        · exact ⟨InJClosureBInfty.base _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, by omega, Or.inl ⟨SimpleGraph.Iso.refl⟩⟩)))),
                 InJClosureBInfty.base _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, by omega, Or.inr ⟨SimpleGraph.Iso.refl⟩⟩))))⟩
  have hleaf_last : ∀ w : Fin (d + 4), (BirdDGraph d).Adj (Fin.last (d + 3)) w ↔ w = ⟨d + 2, by omega⟩ := by
    intro w
    have hw := w.2
    by_cases hwl : w = Fin.last (d + 3)
    · subst hwl; simp [Fin.ext_iff]
    · have hwlt : w.1 < d + 3 := by
        have hne : w.1 ≠ d + 3 := fun h => hwl (Fin.ext h)
        omega
      dsimp [BirdDGraph, birdDAdjLt, Fin.last]
      rw [if_neg (by omega : ¬d + 3 < w.1), if_pos hwlt, Fin.ext_iff]
      dsimp
      constructor
      · intro h
        simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
        rcases h with (((⟨_, _⟩ | ⟨_, _⟩) | ⟨_, _⟩) | ⟨_, h2⟩) <;> omega
      · intro h; rw [h]; simp [show 4 ≤ d + 2 by omega]
  refine ⟨isPrimeGraph_birdDGraph d hd, by rw [Fintype.card_fin]; omega,
    birdDGraph_deg_le d hd, ?_, ?_, inBInfty_bird d (by omega), ?_⟩
  · have h_eq : neighborFinsetIn (BirdDGraph d) (Fin.last (d + 3)) Finset.univ = {⟨d + 2, by omega⟩} := by
      ext w; rw [mem_neighborFinsetIn_iff, Finset.mem_singleton]; simp [hleaf_last w]
    rw [h_eq, Finset.card_singleton]
  · intro hsp
    have h2 : ¬IsSplitGraph (BirdDGraph 2) :=
      not_isSplitGraph_of_two_indep_edges (a := (0 : Fin 6)) (b := 1) (c := 4) (d := 5)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    let emb : BirdDGraph 2 ↪g BirdDGraph d :=
      { toEmbedding := Fin.castLEEmb (by omega : 6 ≤ d + 4)
        map_rel_iff' := by intro _ _; rfl }
    exact h2 (IsSplitGraph.of_embedding emb hsp)
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, d = m + 1 := ⟨d - 1, by omega⟩
    exact inHClosureBInfty_of_iso (birdDGraphStepIso m).symm (inBInfty_bird m (by omega))

/-- **Master Base Family Towers Corollary (`base_families_genPrimeTowers_of_base`)**:
Directly matches `Problem.lean` lines 276–290! -/
theorem base_families_genPrimeTowers_of_base
    (h_base : ∀ {W : Type} [Fintype W] [DecidableEq W] (B : SimpleGraph W),
      InBInfty B → HasErdosHajnalProp B) :
    (∀ (k : ℕ) (hk : 6 ≤ k) (r : ℕ),
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
        ¬IsSplitGraph (GenPrimeTowerGraph (BirdDGraph d) (Fin.last (d + 3)) r)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk r
    obtain ⟨h1, h2, _, _, h5, h6, _⟩ :=
      (genPrimeTower_main_of_base h_base (Fin k) (pathGraph k) ⟨k - 1, by omega⟩
        (pathGraph_genPrimeTower_base_props k hk)).1 r
    exact ⟨h1, h2, h5, h6⟩
  · intro d hd r
    obtain ⟨h1, h2, _, _, h5, h6, _⟩ :=
      (genPrimeTower_main_of_base h_base (Fin (d + 4)) (SpiderGraph d) (Fin.last (d + 3))
        (spiderGraph_genPrimeTower_base_props d hd)).1 r
    exact ⟨h1, h2, h5, h6⟩
  · intro d hd r
    obtain ⟨h1, h2, _, _, h5, h6, _⟩ :=
      (genPrimeTower_main_of_base h_base (Fin (d + 4)) (BirdDGraph d) (Fin.last (d + 3))
        (birdDGraph_genPrimeTower_base_props d hd)).1 r
    exact ⟨h1, h2, h5, h6⟩

end ErdosHajnalGen
