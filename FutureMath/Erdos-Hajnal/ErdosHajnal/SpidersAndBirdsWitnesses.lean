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
import ErdosHajnal.Stage2Witnesses
import ErdosHajnal.SymmetricStage12Interface
import ErdosHajnal.ViralityAndClosures
import ErdosHajnal.WitnessGraph

/-!
# Stage-2 Thresholded Wonderfulness Witnesses for All Subdivided Spiders $S_{1,2,d}$ ($d \ge 2$)
# and All Unicyclic Birds $\mathrm{Bird}_d$ ($d \ge 1$, Including $\mathrm{Bull} = \mathrm{Bird}_1$)
(Proposition 7(3)–(4), Lemma 14(1), and Proposition 8(2)–(3) of `main.tex`)

This self-contained module proves Stage-2 thresholded wonderfulness (`IsThresholdedWonderful`)
via explicit pure-substitution open-interval witnesses (`isThresholdedWonderful_of_openIntervalWitness`):
1. **`terminal_path_arm_dichotomy_witness` (Lemma 14(1) of `main.tex`)**:
   Self-contained recursive terminal-path pure-substitution arm construction
   $(\operatorname{Arm}_r(B_0), S_r(B_0))$ ($B_0 = G_0^c$) proving `HasErdosHajnalProp` from
   `HasErdosHajnalProp B_0` and certifying that every open-interval realization either embeds
   $G_0^+ = G_0 + (w_0 - w_1)$ into $G^c$ (`Arm-i`) or contains an induced $(r + 1)$-vertex path
   $(z_1 - \dots - z_r - y)$ in $G^c$ with $z_1, \dots, z_r \in f(S_r)$ and $y \notin f(S_r)$ (`Arm-ii`).
2. **`spiderGraph_isThresholdedWonderful_of_prev` (Proposition 7(3) & Proposition 8(2) of `main.tex`)**:
   Uniform one-bit open-interval pure-substitution witness certifying `IsThresholdedWonderful (SpiderGraph d)`
   across **all** $d \ge 2$ (`d = 2` unconditionally via $S_{1,2,1} \cong B(2,2) \in \mathcal{EH}$, and
   $d \ge 3$ from `HasErdosHajnalProp (SpiderGraph (d - 1))`).
3. **`birdDGraph_isThresholdedWonderful_le_6`, `isThresholdedWonderful_bullGraph`, &
   `birdDGraph_isThresholdedWonderful_ge_6` (Proposition 7(4) & Proposition 8(3) of `main.tex`)**:
   - Unconditional `IsThresholdedWonderful (BirdDGraph d)` for **all** $1 \le d \le 6$
     (including `BullGraph = BirdDGraph 1`) via the $34$-vertex cograph witness $W_{\mathrm{Bird}}^{(6)}$
     from $P_9 \in \mathcal{EH}$ and hereditary monotonicity $\mathrm{Bird}_d \hookrightarrow_g \mathrm{Bird}_6$;
   - `IsThresholdedWonderful (BirdDGraph d)` for **all** $d \ge 6$ from
     `HasErdosHajnalProp (pathGraph (d + 3))` and `HasErdosHajnalProp (BirdDGraph (d - 1))`
     via the recursive pure-substitution witness $W_{B,d}$.
-/

set_option linter.unusedSectionVars false

open Finset SimpleGraph Real ErdosHajnalP6 ErdosHajnalGen P9Baseline

namespace ErdosHajnalGen

/-! ### Section 1: Multi-Vertex Substitution (`multiSubstGraph`) and Two-Arm Join (`twoArmJoinGraph`) -/

/-- Hereditary monotonicity of `HasErdosHajnalProp` along an induced graph embedding $H_1 \hookrightarrow_g H_2$. -/
private theorem hasErdosHajnalProp_of_emb {W₁ W₂ : Type*}
    {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂}
    (f : H₁ ↪g H₂) (h₂ : HasErdosHajnalProp H₂) : HasErdosHajnalProp H₁ := by
  obtain ⟨c, hc, hprop⟩ := h₂
  refine ⟨c, hc, fun V _ _ G hG => hprop V G ?_⟩
  rintro ⟨g, hg⟩
  refine hG ⟨f.toEmbedding.trans g, ?_⟩
  ext u v
  exact f.map_rel_iff.symm.trans (congr_arg (fun H : SimpleGraph W₂ => H.Adj (f u) (f v)) hg).to_iff

/-- Complement isomorphism induced by $G_1 \simeq_g G_2$. -/
private def complIsoOf {W₁ W₂ : Type*} {G₁ : SimpleGraph W₁} {G₂ : SimpleGraph W₂}
    (e : G₁ ≃g G₂) : G₁ᶜ ≃g G₂ᶜ where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro a b
    simp only [RelIso.coe_fn_toEquiv, SimpleGraph.compl_adj, ne_eq,
      EmbeddingLike.apply_eq_iff_eq, e.map_rel_iff]

/-- Graph complementation commutes with vertex substitution (`substGraph`). -/
private theorem substGraph_compl_eq {V₁ V₂ : Type*} (H₁ : SimpleGraph V₁) (v₀ : V₁)
    (H₂ : SimpleGraph V₂) :
    (substGraph H₁ v₀ H₂)ᶜ = substGraph H₁ᶜ v₀ H₂ᶜ := by
  ext a b
  cases a with
  | inl u =>
    cases b with
    | inl w => simp [substGraph, compl_adj, Subtype.ext_iff]
    | inr y => simp [substGraph, compl_adj, u.2]
  | inr x =>
    cases b with
    | inl w => simp [substGraph, compl_adj, w.2.symm]
    | inr y => simp [substGraph, compl_adj]

/-- Vertex set obtained by simultaneously substituting `U` for the `k` distinct vertices `xs : Fin k ↪ W` of `W`. -/
abbrev MultiSubstVert (W : Type) {k : ℕ} (xs : Fin k ↪ W) (U : Type) : Type :=
  (Fin k × U) ⊕ {w : W // ∀ i : Fin k, w ≠ xs i}

/-- Canonical projection from `MultiSubstVert W xs U` onto the host vertex set `W`. -/
def multiSubstProj {W : Type} {k : ℕ} (xs : Fin k ↪ W) {U : Type} :
    MultiSubstVert W xs U → W
  | Sum.inl (i, _) => xs i
  | Sum.inr w => w.1

/-- Simultaneous substitution of `A : SimpleGraph U` into `k` distinct vertices `xs : Fin k ↪ W` of `B : SimpleGraph W`. -/
def multiSubstGraph {W : Type} (B : SimpleGraph W) {k : ℕ} (xs : Fin k ↪ W)
    {U : Type} (A : SimpleGraph U) : SimpleGraph (MultiSubstVert W xs U) where
  Adj p q :=
    match p, q with
    | Sum.inl (i, u₁), Sum.inl (j, u₂) => if i = j then A.Adj u₁ u₂ else B.Adj (xs i) (xs j)
    | _, _ => B.Adj (multiSubstProj xs p) (multiSubstProj xs q)
  symm p q h := by
    cases p with
    | inl iu =>
      cases q with
      | inl jv =>
        dsimp only at h ⊢
        by_cases hij : iu.1 = jv.1
        · rw [if_pos hij] at h
          rw [if_pos hij.symm]
          exact h.symm
        · rw [if_neg hij] at h
          rw [if_neg (Ne.symm hij)]
          exact h.symm
      | inr w => exact h.symm
    | inr w =>
      cases q with
      | inl jv => exact h.symm
      | inr z => exact h.symm
  loopless p := by
    cases p with
    | inl iu =>
      dsimp only
      rw [if_pos rfl]
      exact A.loopless iu.2
    | inr w => exact B.loopless w.1

/-- Simultaneous substitution `multiSubstGraph B xs A` preserves `HasErdosHajnalProp` for any `k : ℕ`
whenever `B` and `A` satisfy `HasErdosHajnalProp` (`[Nonempty U]`). -/
theorem hasErdosHajnalProp_multiSubstGraph {W U : Type} [Fintype W] [DecidableEq W]
    [Fintype U] [DecidableEq U] [Nonempty U]
    {B : SimpleGraph W} {A : SimpleGraph U}
    (hB : HasErdosHajnalProp B) (hA : HasErdosHajnalProp A) :
    ∀ {k : ℕ} (xs : Fin k ↪ W), HasErdosHajnalProp (multiSubstGraph B xs A) := by
  intro k
  induction k with
  | zero =>
    intro xs
    let iso₀ : B ≃g multiSubstGraph B xs A :=
      { toFun := fun w => Sum.inr ⟨w, fun i => Fin.elim0 i⟩
        invFun := fun x => match x with
          | Sum.inl (i, _) => Fin.elim0 i
          | Sum.inr w => w.1
        left_inv := fun _ => rfl
        right_inv := fun x => by
          cases x with
          | inl iu => exact Fin.elim0 iu.1
          | inr w => rfl
        map_rel_iff' := Iff.rfl }
    exact hasErdosHajnalProp_of_iso iso₀ hB
  | succ m ih =>
    intro xs
    let xs' : Fin m ↪ W := Fin.castSuccEmb.trans xs
    have hlast_not_xs' : ∀ i : Fin m, xs (Fin.last m) ≠ xs' i :=
      fun i h => Fin.castSucc_ne_last i (xs.injective h.symm)
    let v_last : MultiSubstVert W xs' U := Sum.inr ⟨xs (Fin.last m), hlast_not_xs'⟩
    have h_step : HasErdosHajnalProp (substGraph (multiSubstGraph B xs' A) v_last A) :=
      hasErdosHajnalProp_substGraph (multiSubstGraph B xs' A) v_last A (ih xs') hA
    let iso_step : substGraph (multiSubstGraph B xs' A) v_last A ≃g multiSubstGraph B xs A :=
      { toFun := fun z => match z with
          | Sum.inl ⟨Sum.inl (i, u), _⟩ => Sum.inl (i.castSucc, u)
          | Sum.inr u => Sum.inl (Fin.last m, u)
          | Sum.inl ⟨Sum.inr ⟨w, hw⟩, hne⟩ =>
              Sum.inr ⟨w, fun j => Fin.lastCases
                (fun h => hne (by
                  simp only [v_last, Sum.inr.injEq, Subtype.mk.injEq]
                  exact h))
                hw j⟩
        invFun := fun z => match z with
          | Sum.inl (j, u) =>
              Fin.lastCases (Sum.inr u)
                (fun i => Sum.inl ⟨Sum.inl (i, u), by simp [v_last]⟩) j
          | Sum.inr ⟨w, hw⟩ =>
              Sum.inl ⟨Sum.inr ⟨w, fun i => hw i.castSucc⟩, by
                intro h
                simp only [v_last, Sum.inr.injEq, Subtype.mk.injEq] at h
                exact hw (Fin.last m) h⟩
        left_inv := by
          rintro (⟨⟨i, u⟩ | ⟨w, hw⟩, hne⟩ | u)
          · simp
          · simp
          · simp
        right_inv := by
          rintro (⟨j, u⟩ | ⟨w, hw⟩)
          · refine Fin.lastCases ?_ ?_ j <;> simp
          · simp
        map_rel_iff' := by
          rintro (⟨⟨i₁, u₁⟩ | ⟨w₁, hw₁⟩, hne₁⟩ | u₁) (⟨⟨i₂, u₂⟩ | ⟨w₂, hw₂⟩, hne₂⟩ | u₂)
          · dsimp [substGraph, multiSubstGraph, xs']
            by_cases h : i₁ = i₂
            · subst h; simp
            · simp [h]
          · rfl
          · dsimp [substGraph, multiSubstGraph, multiSubstProj, xs', v_last]
            rw [if_neg (Fin.castSucc_ne_last i₁)]
          · rfl
          · rfl
          · rfl
          · dsimp [substGraph, multiSubstGraph, multiSubstProj, xs', v_last]
            rw [if_neg (Fin.castSucc_ne_last i₂).symm]
          · rfl
          · dsimp [substGraph, multiSubstGraph]
            rw [if_pos rfl] }
    exact hasErdosHajnalProp_of_iso iso_step h_step

/-- Two-arm join graph $K_2[0 \leftarrow W_L,\, 1 \leftarrow W_R]$ on `U_L ⊕ U_R` (complete across arms in $G$,
anticomplete across arms in $G^c$). -/
def twoArmJoinGraph {U_L U_R : Type*} (W_L : SimpleGraph U_L) (W_R : SimpleGraph U_R) :
    SimpleGraph (U_L ⊕ U_R) where
  Adj p q :=
    match p, q with
    | Sum.inl u₁, Sum.inl u₂ => W_L.Adj u₁ u₂
    | Sum.inr u₁, Sum.inr u₂ => W_R.Adj u₁ u₂
    | Sum.inl _, Sum.inr _ => True
    | Sum.inr _, Sum.inl _ => True
  symm p q h := by
    cases p <;> cases q <;> first | exact h.symm | exact trivial
  loopless p := by
    cases p with
    | inl u => exact W_L.loopless u
    | inr u => exact W_R.loopless u

/-- `twoArmJoinGraph W_L W_R` satisfies `HasErdosHajnalProp` whenever `[Nonempty U_L]`, `[Nonempty U_R]`,
and both `W_L` and `W_R` satisfy `HasErdosHajnalProp`. -/
theorem hasErdosHajnalProp_twoArmJoinGraph {U_L U_R : Type} [Fintype U_L] [DecidableEq U_L]
    [Fintype U_R] [DecidableEq U_R] [Nonempty U_L] [Nonempty U_R]
    {W_L : SimpleGraph U_L} {W_R : SimpleGraph U_R}
    (hL : HasErdosHajnalProp W_L) (hR : HasErdosHajnalProp W_R) :
    HasErdosHajnalProp (twoArmJoinGraph W_L W_R) := by
  have h1 := hasErdosHajnalProp_substGraph (⊤ : SimpleGraph (Fin 2)) 0 W_L
    hasErdosHajnalProp_top_fin2 hL
  let v₁ : {v : Fin 2 // v ≠ 0} ⊕ U_L := Sum.inl ⟨1, by decide⟩
  have h2 := hasErdosHajnalProp_substGraph _ v₁ W_R h1 hR
  let iso_join : substGraph (substGraph (⊤ : SimpleGraph (Fin 2)) 0 W_L) v₁ W_R ≃g
      twoArmJoinGraph W_L W_R :=
    { toFun := fun z => match z with
        | Sum.inl ⟨Sum.inr u, _⟩ => Sum.inl u
        | Sum.inr u => Sum.inr u
        | Sum.inl ⟨Sum.inl ⟨v, hv₀⟩, hne⟩ =>
            False.elim (hne (by
              have hv1 : v = 1 := by fin_cases v; exact False.elim (hv₀ rfl); rfl
              subst hv1; rfl))
      invFun := fun z => match z with
        | Sum.inl u => Sum.inl ⟨Sum.inr u, by simp [v₁]⟩
        | Sum.inr u => Sum.inr u
      left_inv := by
        rintro (⟨⟨v, hv₀⟩ | u, hne⟩ | u)
        · exfalso
          apply hne
          have hv1 : v = 1 := by fin_cases v; exact False.elim (hv₀ rfl); rfl
          subst hv1; rfl
        · rfl
        · rfl
      right_inv := by
        rintro (u | u) <;> rfl
      map_rel_iff' := by
        rintro (⟨⟨v₁', hv₁'⟩ | u₁, hne₁⟩ | u₁) (⟨⟨v₂', hv₂'⟩ | u₂, hne₂⟩ | u₂)
        · exfalso
          apply hne₁
          have hv1 : v₁' = 1 := by fin_cases v₁'; exact False.elim (hv₁' rfl); rfl
          subst hv1; rfl
        · exfalso
          apply hne₁
          have hv1 : v₁' = 1 := by fin_cases v₁'; exact False.elim (hv₁' rfl); rfl
          subst hv1; rfl
        · exfalso
          apply hne₁
          have hv1 : v₁' = 1 := by fin_cases v₁'; exact False.elim (hv₁' rfl); rfl
          subst hv1; rfl
        · exfalso
          apply hne₂
          have hv1 : v₂' = 1 := by fin_cases v₂'; exact False.elim (hv₂' rfl); rfl
          subst hv1; rfl
        · rfl
        · dsimp [twoArmJoinGraph, substGraph, v₁]; simp
        · exfalso
          apply hne₂
          have hv1 : v₂' = 1 := by fin_cases v₂'; exact False.elim (hv₂' rfl); rfl
          subst hv1; rfl
        · dsimp [twoArmJoinGraph, substGraph, v₁]; simp
        · rfl }
  exact hasErdosHajnalProp_of_iso iso_join h2

/-- Combined special vertex set `S_L ⊔ S_R` inside `U_L ⊕ U_R`. -/
def twoArmSpecFinset {U_L U_R : Type*} [DecidableEq U_L] [DecidableEq U_R]
    (S_L : Finset U_L) (S_R : Finset U_R) : Finset (U_L ⊕ U_R) :=
  S_L.map Function.Embedding.inl ∪ S_R.map Function.Embedding.inr

@[simp]
private theorem mem_twoArmSpecFinset_inl {U_L U_R : Type*} [DecidableEq U_L] [DecidableEq U_R]
    (S_L : Finset U_L) (S_R : Finset U_R) (u : U_L) :
    Sum.inl u ∈ twoArmSpecFinset S_L S_R ↔ u ∈ S_L := by
  simp [twoArmSpecFinset]

@[simp]
private theorem mem_twoArmSpecFinset_inr {U_L U_R : Type*} [DecidableEq U_L] [DecidableEq U_R]
    (S_L : Finset U_L) (S_R : Finset U_R) (u : U_R) :
    Sum.inr u ∈ twoArmSpecFinset S_L S_R ↔ u ∈ S_R := by
  simp [twoArmSpecFinset]

/-- Left restriction of an open-interval realization of `(twoArmJoinGraph W_L W_R, S_L ⊔ S_R)`. -/
def twoArmRealizationLeft {U_L U_R V : Type*} [DecidableEq U_L] [DecidableEq U_R]
    {W_L : SimpleGraph U_L} {W_R : SimpleGraph U_R}
    {S_L : Finset U_L} {S_R : Finset U_R}
    {G : SimpleGraph V} {v₀ : V} {f : U_L ⊕ U_R ↪ V}
    (hf : IsOpenIntervalRealization (twoArmJoinGraph W_L W_R) (twoArmSpecFinset S_L S_R) G v₀ f) :
    IsOpenIntervalRealization W_L S_L G v₀ (Function.Embedding.inl.trans f) where
  ne_ext u := hf.ne_ext (Sum.inl u)
  adj_ext_spec u hu := hf.adj_ext_spec (Sum.inl u) ((mem_twoArmSpecFinset_inl S_L S_R u).mpr hu)
  nonadj_ext_nonspec u hu :=
    hf.nonadj_ext_nonspec (Sum.inl u) (fun h => hu ((mem_twoArmSpecFinset_inl S_L S_R u).mp h))
  adj_of_wit_adj u₁ u₂ hadj := hf.adj_of_wit_adj (Sum.inl u₁) (Sum.inl u₂) hadj
  nonadj_of_wit_nonadj u₁ u₂ hne hspec hnadj :=
    hf.nonadj_of_wit_nonadj (Sum.inl u₁) (Sum.inl u₂) (fun h => hne (Sum.inl.inj h))
      (hspec.imp (fun h h' => h ((mem_twoArmSpecFinset_inl S_L S_R u₁).mp h'))
        (fun h h' => h ((mem_twoArmSpecFinset_inl S_L S_R u₂).mp h'))) hnadj

/-- Right restriction of an open-interval realization of `(twoArmJoinGraph W_L W_R, S_L ⊔ S_R)`. -/
def twoArmRealizationRight {U_L U_R V : Type*} [DecidableEq U_L] [DecidableEq U_R]
    {W_L : SimpleGraph U_L} {W_R : SimpleGraph U_R}
    {S_L : Finset U_L} {S_R : Finset U_R}
    {G : SimpleGraph V} {v₀ : V} {f : U_L ⊕ U_R ↪ V}
    (hf : IsOpenIntervalRealization (twoArmJoinGraph W_L W_R) (twoArmSpecFinset S_L S_R) G v₀ f) :
    IsOpenIntervalRealization W_R S_R G v₀ (Function.Embedding.inr.trans f) where
  ne_ext u := hf.ne_ext (Sum.inr u)
  adj_ext_spec u hu := hf.adj_ext_spec (Sum.inr u) ((mem_twoArmSpecFinset_inr S_L S_R u).mpr hu)
  nonadj_ext_nonspec u hu :=
    hf.nonadj_ext_nonspec (Sum.inr u) (fun h => hu ((mem_twoArmSpecFinset_inr S_L S_R u).mp h))
  adj_of_wit_adj u₁ u₂ hadj := hf.adj_of_wit_adj (Sum.inr u₁) (Sum.inr u₂) hadj
  nonadj_of_wit_nonadj u₁ u₂ hne hspec hnadj :=
    hf.nonadj_of_wit_nonadj (Sum.inr u₁) (Sum.inr u₂) (fun h => hne (Sum.inr.inj h))
      (hspec.imp (fun h h' => h ((mem_twoArmSpecFinset_inr S_L S_R u₁).mp h'))
        (fun h h' => h ((mem_twoArmSpecFinset_inr S_L S_R u₂).mp h'))) hnadj

/-! ### Section 2: Lemma 14(1) — Universal Terminal-Path Recursive Pure-Substitution Arm Dichotomy -/

/-- One-leaf terminal extension $G_0^+ := G_0 + (w_0 - w_1)$ on `Option W₀`, where `none` represents
the new degree-$1$ leaf $w_0$ adjacent solely to `some w₁`. -/
def terminalPathExtGraph {W₀ : Type*} (G₀ : SimpleGraph W₀) (w₁ : W₀) : SimpleGraph (Option W₀) where
  Adj a b :=
    match a, b with
    | none, none => False
    | none, some y => y = w₁
    | some x, none => x = w₁
    | some x, some y => G₀.Adj x y
  symm a b h := by
    cases a <;> cases b <;> first | exact h | exact h.symm
  loopless a := by
    cases a with
    | none => exact id
    | some x => exact G₀.loopless x

/-- Recursive vertex set of the depth-$(n+1)$ terminal-path pure-substitution arm
$\operatorname{Arm}_{n+1}(B_0)$ (Lemma 14(1) of `main.tex`, where $r = n + 1 \ge 1$). -/
abbrev ArmVert (W₀ : Type) {L : ℕ} (w_path : Fin L ↪ W₀) : ∀ (n : ℕ), n < L → Type
  | 0, _ => Fin 2
  | n + 1, hn =>
      MultiSubstVert W₀ ((Fin.castLEEmb hn).trans w_path)
        (ArmVert W₀ w_path n (Nat.lt_of_succ_lt hn))

instance instFintypeArmVert (W₀ : Type) [Fintype W₀] [DecidableEq W₀] {L : ℕ}
    (w_path : Fin L ↪ W₀) : ∀ (n : ℕ) (hn : n < L), Fintype (ArmVert W₀ w_path n hn)
  | 0, _ => inferInstanceAs (Fintype (Fin 2))
  | n + 1, hn =>
      letI := instFintypeArmVert W₀ w_path n (Nat.lt_of_succ_lt hn)
      inferInstanceAs (Fintype (MultiSubstVert W₀ _ _))

noncomputable instance instDecidableEqArmVert (W₀ : Type) {L : ℕ}
    (w_path : Fin L ↪ W₀) (n : ℕ) (hn : n < L) : DecidableEq (ArmVert W₀ w_path n hn) :=
  Classical.decEq _

instance instNonemptyArmVert (W₀ : Type) {L : ℕ}
    (w_path : Fin L ↪ W₀) : ∀ (n : ℕ) (hn : n < L), Nonempty (ArmVert W₀ w_path n hn)
  | 0, _ => ⟨0⟩
  | n + 1, hn =>
      letI := instNonemptyArmVert W₀ w_path n (Nat.lt_of_succ_lt hn)
      ⟨Sum.inl (⟨0, by omega⟩, Classical.arbitrary _)⟩

/-- Recursive graph $\operatorname{Arm}_{n+1}(B_0) \in \mathcal{J}(\{B_0, \overline{K_2}\})$
(Lemma 14(1) of `main.tex`, $r = n + 1 \ge 1$). -/
def armGraph {W₀ : Type} (B₀ : SimpleGraph W₀) {L : ℕ} (w_path : Fin L ↪ W₀) :
    ∀ (n : ℕ) (hn : n < L), SimpleGraph (ArmVert W₀ w_path n hn)
  | 0, _ => ⊥
  | n + 1, hn =>
      multiSubstGraph B₀ ((Fin.castLEEmb hn).trans w_path)
        (armGraph B₀ w_path n (Nat.lt_of_succ_lt hn))

/-- Boolean special-vertex membership predicate $S_{n+1}(B_0) \subseteq V(\operatorname{Arm}_{n+1}(B_0))$
(Lemma 14(1) of `main.tex`, $r = n + 1 \ge 1$). -/
def armSpecPred {W₀ : Type} {L : ℕ} (w_path : Fin L ↪ W₀) :
    ∀ (n : ℕ) (hn : n < L), ArmVert W₀ w_path n hn → Bool
  | 0, _, u => u == 0
  | n + 1, hn, Sum.inl (_, u) => armSpecPred w_path n (Nat.lt_of_succ_lt hn) u
  | _ + 1, _, Sum.inr _ => false

/-- Special vertex set $S_{n+1}(B_0)$ as a `Finset`. -/
noncomputable def armSpecFinset {W₀ : Type} [Fintype W₀] [DecidableEq W₀] {L : ℕ}
    (w_path : Fin L ↪ W₀) (n : ℕ) (hn : n < L) : Finset (ArmVert W₀ w_path n hn) :=
  Finset.univ.filter (fun u => armSpecPred w_path n hn u = true)

@[simp]
private theorem mem_armSpecFinset_iff {W₀ : Type} [Fintype W₀] [DecidableEq W₀] {L : ℕ}
    (w_path : Fin L ↪ W₀) (n : ℕ) (hn : n < L) (u : ArmVert W₀ w_path n hn) :
    u ∈ armSpecFinset w_path n hn ↔ armSpecPred w_path n hn u = true := by
  simp [armSpecFinset]

/-- Every pure-substitution arm $\operatorname{Arm}_{n+1}(B_0)$ inherits `HasErdosHajnalProp` from `B₀`
by iterated substitution closure (`hasErdosHajnalProp_multiSubstGraph`). -/
theorem hasErdosHajnalProp_armGraph {W₀ : Type} [Fintype W₀] [DecidableEq W₀]
    {B₀ : SimpleGraph W₀} (hB₀ : HasErdosHajnalProp B₀) {L : ℕ} (w_path : Fin L ↪ W₀) :
    ∀ (n : ℕ) (hn : n < L), HasErdosHajnalProp (armGraph B₀ w_path n hn)
  | 0, _ => hasErdosHajnalProp_bot_fin2
  | n + 1, hn =>
      hasErdosHajnalProp_multiSubstGraph hB₀
        (hasErdosHajnalProp_armGraph hB₀ w_path n (Nat.lt_of_succ_lt hn)) _

/-- Any path realization `z : Fin M → U` into `Gᶜ` where vertices `0..M-2` satisfy a property `P`
and vertex `M-1` violates `P` is injective for every `M : ℕ` (including `M = 3` where endpoints of `P₃`
are distinguished by `P`). -/
private theorem pathSpec_inj {U V : Type*} {G : SimpleGraph V} {g : U → V}
    {M : ℕ} {z : Fin M → U} {P : U → Prop}
    (hz_adj : ∀ i j : Fin M, Gᶜ.Adj (g (z i)) (g (z j)) ↔ (pathGraph M).Adj i j)
    (hz_spec : ∀ i : Fin M, i.1 + 1 < M → P (z i))
    (hz_nonspec : ∀ i : Fin M, i.1 + 1 = M → ¬P (z i)) :
    Function.Injective z := by
  have h_lt : ∀ i j : Fin M, i.1 < j.1 → z i ≠ z j := by
    intro i j hlt hij
    by_cases h_consec : j.1 = i.1 + 1
    · have hadj := (hz_adj i j).mpr (by rw [pathGraph_adj]; omega)
      exact hadj.1 (congr_arg g hij)
    · by_cases hi0 : 0 < i.1
      · let prev : Fin M := ⟨i.1 - 1, by omega⟩
        have h1 : Gᶜ.Adj (g (z prev)) (g (z i)) :=
          (hz_adj prev i).mpr (by rw [pathGraph_adj]; show (i.1 - 1) + 1 = i.1 ∨ i.1 + 1 = i.1 - 1; omega)
        rw [hij] at h1
        have h2 : (i.1 - 1) + 1 = j.1 ∨ j.1 + 1 = i.1 - 1 := pathGraph_adj.mp ((hz_adj prev j).mp h1)
        omega
      · by_cases hj_lt : j.1 + 1 < M
        · let succ : Fin M := ⟨j.1 + 1, hj_lt⟩
          have h1 : Gᶜ.Adj (g (z j)) (g (z succ)) :=
            (hz_adj j succ).mpr (by rw [pathGraph_adj]; show j.1 + 1 = j.1 + 1 ∨ (j.1 + 1) + 1 = j.1; omega)
          rw [← hij] at h1
          have h2 : i.1 + 1 = j.1 + 1 ∨ (j.1 + 1) + 1 = i.1 := pathGraph_adj.mp ((hz_adj i succ).mp h1)
          omega
        · have hj_last : j.1 + 1 = M := by omega
          exact hz_nonspec j hj_last (hij ▸ hz_spec i (by omega))
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
  · exact h_lt i j hlt hij
  · exact h_lt j i hgt hij.symm

/-- **Lemma 14(1) (`terminal_path_arm_dichotomy_witness`, `main.tex` lines 1396–1421 & 1432–1463)**:
Let `G₀ : SimpleGraph W₀` have an induced $L$-vertex terminal path `w_path : Fin L ↪ W₀` ($L \ge 2$)
satisfying `(TP-1)` and `(TP-2)`. For any integer $n$ with $n + 1 < L$ (i.e. $r = n + 1 \in \{1, \dots, L - 1\}$)
and any vertex embedding `f : ArmVert W₀ w_path n hn.le ↪ V` in a host graph `G : SimpleGraph V`
satisfying `(E-Non)` (`h_non`) and `(E-Edge)` (`h_edge`), **either**:
- **(Arm-i)**: $G^c$ contains an induced copy of $G_0^+ = \text{terminalPathExtGraph } G_0 \text{ (w\_path 0)}$; **or**
- **(Arm-ii)**: there exists an injective map `p : Fin (n + 2) → ArmVert W₀ w_path n hn.le` such that
  `(f ∘ p)` embeds `pathGraph (n + 2)` as an induced subgraph into $G^c$, `armSpecPred (p i) = true`
  for all $i < n + 1$, and `armSpecPred (p (Fin.last (n + 1))) = false`. -/
theorem terminal_path_arm_dichotomy_witness
    {W₀ : Type} {V : Type*} [Fintype W₀] [DecidableEq W₀]
    (G₀ : SimpleGraph W₀) {L : ℕ} (w_path : Fin L ↪ W₀)
    (hTP1 : ∀ a b : Fin L, a.1 < b.1 → (G₀.Adj (w_path a) (w_path b) ↔ b.1 = a.1 + 1))
    (hTP2 : ∀ z : W₀, (∀ a : Fin L, z ≠ w_path a) → ∀ a : Fin L, G₀.Adj z (w_path a) → a.1 = L - 1)
    (G : SimpleGraph V) :
    ∀ (n : ℕ) (hn : n + 1 < L) (f : ArmVert W₀ w_path n hn.le ↪ V),
      (∀ x y, (armGraph G₀ᶜ w_path n hn.le).Adj x y → G.Adj (f x) (f y)) →
      (∀ x y, x ≠ y →
        (armSpecPred w_path n hn.le x = false ∨ armSpecPred w_path n hn.le y = false) →
        ¬(armGraph G₀ᶜ w_path n hn.le).Adj x y → ¬G.Adj (f x) (f y)) →
      Nonempty (terminalPathExtGraph G₀ (w_path ⟨0, by omega⟩) ↪g Gᶜ) ∨
      (∃ p : Fin (n + 2) → ArmVert W₀ w_path n hn.le,
        (∀ i j : Fin (n + 2), Gᶜ.Adj (f (p i)) (f (p j)) ↔ (pathGraph (n + 2)).Adj i j) ∧
        (∀ i : Fin (n + 1), armSpecPred w_path n hn.le (p i.castSucc) = true) ∧
        armSpecPred w_path n hn.le (p (Fin.last (n + 1))) = false) := by
  intro n
  induction n with
  | zero =>
    intro hn f _ h_edge
    right
    refine ⟨id, ?_, ?_, rfl⟩
    · intro i j
      fin_cases i <;> fin_cases j
      · simp
      · have hne : (0 : Fin 2) ≠ 1 := by decide
        have hs : armSpecPred w_path 0 hn.le 1 = false := rfl
        have hna : ¬(armGraph G₀ᶜ w_path 0 hn.le).Adj 0 1 := False.elim
        exact iff_of_true ⟨fun h => hne (f.injective h), h_edge 0 1 hne (Or.inr hs) hna⟩ (by decide)
      · have hne : (1 : Fin 2) ≠ 0 := by decide
        have hs : armSpecPred w_path 0 hn.le 1 = false := rfl
        have hna : ¬(armGraph G₀ᶜ w_path 0 hn.le).Adj 1 0 := False.elim
        exact iff_of_true ⟨fun h => hne (f.injective h), h_edge 1 0 hne (Or.inl hs) hna⟩ (by decide)
      · simp
    · intro i
      fin_cases i
      rfl
  | succ n ih =>
    intro hn f h_non h_edge
    have hn_prev : n + 1 < L := Nat.lt_of_succ_lt hn
    let xs : Fin (n + 2) ↪ W₀ := (Fin.castLEEmb hn.le).trans w_path
    -- Restrict f to each child slot `a : Fin (n + 2)`
    let childEmb (a : Fin (n + 2)) : ArmVert W₀ w_path n hn_prev.le ↪ V :=
      ⟨fun u => f (Sum.inl (a, u)), fun u₁ u₂ h =>
        (Prod.mk.inj (Sum.inl.inj (f.injective h))).2⟩
    have h_child : ∀ a : Fin (n + 2),
        Nonempty (terminalPathExtGraph G₀ (w_path ⟨0, by omega⟩) ↪g Gᶜ) ∨
        (∃ p : Fin (n + 2) → ArmVert W₀ w_path n hn_prev.le,
          (∀ i j : Fin (n + 2), Gᶜ.Adj (childEmb a (p i)) (childEmb a (p j)) ↔
            (pathGraph (n + 2)).Adj i j) ∧
          (∀ i : Fin (n + 1), armSpecPred w_path n hn_prev.le (p i.castSucc) = true) ∧
          armSpecPred w_path n hn_prev.le (p (Fin.last (n + 1))) = false) := by
      intro a
      refine ih hn_prev (childEmb a) ?_ ?_
      · intro u₁ u₂ hadj
        apply h_non (Sum.inl (a, u₁)) (Sum.inl (a, u₂))
        dsimp [armGraph, multiSubstGraph]
        rw [if_pos rfl]
        exact hadj
      · intro u₁ u₂ hne hspec hnadj
        apply h_edge (Sum.inl (a, u₁)) (Sum.inl (a, u₂)) (fun h => hne (Prod.mk.inj (Sum.inl.inj h)).2) hspec
        dsimp [armGraph, multiSubstGraph]
        rw [if_pos rfl]
        exact hnadj
    by_cases h_arm1 : ∃ a : Fin (n + 2),
        Nonempty (terminalPathExtGraph G₀ (w_path ⟨0, by omega⟩) ↪g Gᶜ)
    · obtain ⟨_, h⟩ := h_arm1
      exact Or.inl h
    · push_neg at h_arm1
      have h_all_paths : ∀ a : Fin (n + 2),
          ∃ p : Fin (n + 2) → ArmVert W₀ w_path n hn_prev.le,
            (∀ i j : Fin (n + 2), Gᶜ.Adj (f (Sum.inl (a, p i))) (f (Sum.inl (a, p j))) ↔
              (pathGraph (n + 2)).Adj i j) ∧
            (∀ i : Fin (n + 1), armSpecPred w_path n hn_prev.le (p i.castSucc) = true) ∧
            armSpecPred w_path n hn_prev.le (p (Fin.last (n + 1))) = false :=
        fun a => (h_child a).resolve_left (not_nonempty_iff.mpr (h_arm1 a))
      choose z hz_path hz_spec hz_nonspec using h_all_paths
      -- Helper: cross-slot adjacency in `armGraph` between distinct vertices in `ArmVert (n + 1)`
      have h_proj_diff : ∀ x y : ArmVert W₀ w_path (n + 1) hn.le,
          multiSubstProj xs x ≠ multiSubstProj xs y →
          ((armGraph G₀ᶜ w_path (n + 1) hn.le).Adj x y ↔
            ¬G₀.Adj (multiSubstProj xs x) (multiSubstProj xs y)) := by
        intro x y hne
        cases x with
        | inl au =>
          cases y with
          | inl bv =>
            have hab : au.1 ≠ bv.1 := fun h => hne (congr_arg xs h)
            dsimp [armGraph, multiSubstGraph, multiSubstProj, xs] at hne ⊢
            rw [if_neg hab]
            simp [compl_adj, hne]
          | inr w =>
            dsimp [armGraph, multiSubstGraph, multiSubstProj, xs] at hne ⊢
            simp [compl_adj, hne]
        | inr w =>
          cases y with
          | inl bv =>
            dsimp [armGraph, multiSubstGraph, multiSubstProj, xs] at hne ⊢
            simp [compl_adj, hne]
          | inr w₂ =>
            dsimp [armGraph, multiSubstGraph, multiSubstProj] at hne ⊢
            simp [compl_adj, hne]
      -- Backward induction over `k : ℕ` (`k ≤ n + 1`), constructing suffix paths starting at slot `n + 1 - k`
      have h_back : ∀ k : ℕ, (hk : k ≤ n + 1) →
          Nonempty (terminalPathExtGraph G₀ (w_path ⟨0, by omega⟩) ↪g Gᶜ) ∨
          (∃ u_suf : ∀ a : Fin (n + 2), n + 1 - k ≤ a.1 → ArmVert W₀ w_path n hn_prev.le,
            (∀ (a : Fin (n + 2)) (ha : n + 1 - k ≤ a.1),
              armSpecPred w_path n hn_prev.le (u_suf a ha) = true) ∧
            (∀ (a : Fin (n + 2)) (ha : n + 1 - k ≤ a.1) (ha1 : a.1 + 1 < n + 2),
              Gᶜ.Adj (f (Sum.inl (a, u_suf a ha)))
                (f (Sum.inl (⟨a.1 + 1, ha1⟩, u_suf ⟨a.1 + 1, ha1⟩ (by dsimp; omega)))))) := by
        intro k
        induction k with
        | zero =>
          intro _
          right
          refine ⟨fun a _ => z a (0 : Fin (n + 1)).castSucc, fun a _ => hz_spec a 0, ?_⟩
          intro a ha ha1
          omega
        | succ k ihk =>
          intro hk
          rcases ihk (by omega) with h_done | ⟨u_suf, hu_spec, hu_adj⟩
          · exact Or.inl h_done
          · let q : Fin (n + 2) := ⟨n - k, by omega⟩
            have hq_val : q.1 = n - k := rfl
            let u_next : ArmVert W₀ w_path n hn_prev.le :=
              u_suf ⟨q.1 + 1, by omega⟩ (by dsimp; omega)
            by_cases h_some : ∃ i : Fin (n + 1),
                Gᶜ.Adj (f (Sum.inl (q, z q i.castSucc))) (f (Sum.inl (⟨q.1 + 1, by omega⟩, u_next)))
            · obtain ⟨i₀, hi₀⟩ := h_some
              right
              let u_new : ∀ a : Fin (n + 2), n + 1 - (k + 1) ≤ a.1 → ArmVert W₀ w_path n hn_prev.le :=
                fun a ha =>
                  if h_eq : a.1 = q.1 then z q i₀.castSucc
                  else u_suf a (by omega)
              refine ⟨u_new, ?_, ?_⟩
              · intro a ha
                dsimp [u_new]
                split_ifs with h_eq
                · exact hz_spec q i₀
                · exact hu_spec a (by omega)
              · intro a ha ha1
                dsimp [u_new]
                by_cases h_eq : a.1 = q.1
                · have ha_fin : a = q := Fin.ext h_eq
                  subst ha_fin
                  rw [dif_pos rfl, dif_neg (by omega)]
                  exact hi₀
                · rw [dif_neg h_eq, dif_neg (by omega)]
                  exact hu_adj a (by omega) ha1
            · -- No `i < n + 1` in slot `q` is adjacent in `Gᶜ` to `u_next`! Build `Arm-i` embedding `Option W₀ ↪g Gᶜ`!
              left
              push_neg at h_some
              have h_last_adj : Gᶜ.Adj (f (Sum.inl (q, z q (Fin.last (n + 1)))))
                  (f (Sum.inl (⟨q.1 + 1, by omega⟩, u_next))) := by
                have hne_xy : (Sum.inl (q, z q (Fin.last (n + 1))) : ArmVert W₀ w_path (n + 1) hn.le) ≠
                    Sum.inl (⟨q.1 + 1, by omega⟩, u_next) := by
                  intro h
                  have : q.1 = q.1 + 1 := congr_arg Fin.val (Prod.mk.inj (Sum.inl.inj h)).1
                  omega
                have hne_f : f (Sum.inl (q, z q (Fin.last (n + 1)))) ≠
                    f (Sum.inl (⟨q.1 + 1, by omega⟩, u_next)) := f.injective.ne hne_xy
                refine ⟨hne_f, h_edge _ _ hne_xy (Or.inl (hz_nonspec q)) ?_⟩
                have hproj : multiSubstProj xs (Sum.inl (q, z q (Fin.last (n + 1)))) =
                    w_path ⟨q.1, by omega⟩ := rfl
                have hproj' : multiSubstProj xs (Sum.inl (⟨q.1 + 1, by omega⟩, u_next)) =
                    w_path ⟨q.1 + 1, by omega⟩ := rfl
                have hne_p : multiSubstProj xs (Sum.inl (q, z q (Fin.last (n + 1)))) ≠
                    multiSubstProj xs (Sum.inl (⟨q.1 + 1, by omega⟩, u_next)) := by
                  rw [hproj, hproj']
                  exact w_path.injective.ne (by simp [Fin.ext_iff])
                rw [h_proj_diff _ _ hne_p, hproj, hproj']
                exact not_not.mpr ((hTP1 ⟨q.1, by omega⟩ ⟨q.1 + 1, by omega⟩ (by dsimp; omega)).mpr rfl)
              let pathNode : Fin (L + 1) → ArmVert W₀ w_path (n + 1) hn.le := fun p =>
                if hp1 : p.1 ≤ q.1 + 1 then
                  Sum.inl (q, z q ⟨n - q.1 + p.1, by omega⟩)
                else if hp2 : p.1 = q.1 + 2 then
                  Sum.inl (⟨q.1 + 1, by omega⟩, u_next)
                else if hp3 : p.1 ≤ n + 2 then
                  Sum.inl (⟨p.1 - 1, by omega⟩, z ⟨p.1 - 1, by omega⟩ (Fin.last (n + 1)))
                else
                  Sum.inr ⟨w_path ⟨p.1 - 1, by omega⟩,
                    fun i h => by
                      have : p.1 - 1 = i.1 := congr_arg Fin.val (w_path.injective h)
                      omega⟩
              have h_pathNode_proj : ∀ p : Fin (L + 1),
                  multiSubstProj xs (pathNode p) = w_path ⟨max q.1 (p.1 - 1), by omega⟩ := by
                intro p
                dsimp [pathNode]
                split_ifs with hp1 hp2 hp3
                · have hm : max q.1 (p.1 - 1) = q.1 := Nat.max_eq_left (by omega)
                  dsimp [multiSubstProj, xs]
                  congr 1; ext; dsimp; omega
                · have hm : max q.1 (p.1 - 1) = q.1 + 1 := by omega
                  dsimp [multiSubstProj, xs]
                  congr 1; ext; dsimp; omega
                · have hm : max q.1 (p.1 - 1) = p.1 - 1 := Nat.max_eq_right (by omega)
                  dsimp [multiSubstProj, xs]
                  congr 1; ext; dsimp; omega
                · have hm : max q.1 (p.1 - 1) = p.1 - 1 := Nat.max_eq_right (by omega)
                  dsimp [multiSubstProj]
                  congr 1; ext; dsimp; omega
              have h_pathNode_nonspec : ∀ p : Fin (L + 1), q.1 + 3 ≤ p.1 →
                  armSpecPred w_path (n + 1) hn.le (pathNode p) = false := by
                intro p hp
                dsimp [pathNode]
                rw [dif_neg (by omega), dif_neg (by omega)]
                split_ifs with hp3
                · exact hz_nonspec ⟨p.1 - 1, by omega⟩
                · rfl
              have h_pathNode_adj : ∀ p₁ p₂ : Fin (L + 1), p₁.1 < p₂.1 →
                  (Gᶜ.Adj (f (pathNode p₁)) (f (pathNode p₂)) ↔ p₂.1 = p₁.1 + 1) := by
                intro p₁ p₂ hlt
                by_cases hp₂_1 : p₂.1 ≤ q.1 + 1
                · have hp₁_1 : p₁.1 ≤ q.1 + 1 := by omega
                  have h1 : pathNode p₁ = Sum.inl (q, z q ⟨n - q.1 + p₁.1, by omega⟩) := by
                    dsimp [pathNode]; rw [dif_pos hp₁_1]
                  have h2 : pathNode p₂ = Sum.inl (q, z q ⟨n - q.1 + p₂.1, by omega⟩) := by
                    dsimp [pathNode]; rw [dif_pos hp₂_1]
                  rw [h1, h2, hz_path q ⟨n - q.1 + p₁.1, by omega⟩ ⟨n - q.1 + p₂.1, by omega⟩]
                  simp only [pathGraph_adj]
                  omega
                · by_cases hp₂_2 : p₂.1 = q.1 + 2
                  · have hp₁_1 : p₁.1 ≤ q.1 + 1 := by omega
                    have h1 : pathNode p₁ = Sum.inl (q, z q ⟨n - q.1 + p₁.1, by omega⟩) := by
                      dsimp [pathNode]; rw [dif_pos hp₁_1]
                    have h2 : pathNode p₂ = Sum.inl (⟨q.1 + 1, by omega⟩, u_next) := by
                      dsimp [pathNode]; rw [dif_neg (by omega), dif_pos hp₂_2]
                    rw [h1, h2]
                    by_cases h_consec : p₂.1 = p₁.1 + 1
                    · have h_idx : (⟨n - q.1 + p₁.1, by omega⟩ : Fin (n + 2)) = Fin.last (n + 1) := by
                        ext; dsimp; omega
                      rw [h_idx]
                      exact iff_of_true h_last_adj h_consec
                    · have h_idx : (⟨n - q.1 + p₁.1, by omega⟩ : Fin (n + 2)) =
                          (⟨n - q.1 + p₁.1, by omega⟩ : Fin (n + 1)).castSucc := rfl
                      rw [h_idx]
                      exact iff_of_false (h_some ⟨n - q.1 + p₁.1, by omega⟩) h_consec
                  · have hp₂_ge : q.1 + 3 ≤ p₂.1 := by omega
                    have hs₁_lt : max q.1 (p₁.1 - 1) < max q.1 (p₂.1 - 1) := by omega
                    have hproj_ne : multiSubstProj xs (pathNode p₁) ≠ multiSubstProj xs (pathNode p₂) := by
                      rw [h_pathNode_proj p₁, h_pathNode_proj p₂]
                      exact w_path.injective.ne (by simp [Fin.ext_iff]; omega)
                    have hne_node : pathNode p₁ ≠ pathNode p₂ := fun h => hproj_ne (congr_arg _ h)
                    by_cases h_consec : p₂.1 = p₁.1 + 1
                    · refine iff_of_true ⟨f.injective.ne hne_node, h_edge _ _ hne_node
                        (Or.inr (h_pathNode_nonspec p₂ hp₂_ge)) ?_⟩ h_consec
                      rw [h_proj_diff _ _ hproj_ne, h_pathNode_proj p₁, h_pathNode_proj p₂]
                      exact not_not.mpr ((hTP1 ⟨max q.1 (p₁.1 - 1), by omega⟩
                        ⟨max q.1 (p₂.1 - 1), by omega⟩ (by dsimp; exact hs₁_lt)).mpr (by dsimp; omega))
                    · refine iff_of_false (fun h => h.2 (h_non _ _ ?_)) h_consec
                      rw [h_proj_diff _ _ hproj_ne, h_pathNode_proj p₁, h_pathNode_proj p₂]
                      intro hg₀
                      have := (hTP1 ⟨max q.1 (p₁.1 - 1), by omega⟩
                        ⟨max q.1 (p₂.1 - 1), by omega⟩ (by dsimp; exact hs₁_lt)).mp hg₀
                      dsimp at this; omega
              classical
              let armMap : Option W₀ → ArmVert W₀ w_path (n + 1) hn.le
                | none => pathNode ⟨0, by omega⟩
                | some x =>
                    if hx : ∃ a : Fin L, w_path a = x then
                      pathNode ⟨(Classical.choose hx).1 + 1, by omega⟩
                    else
                      Sum.inr ⟨x, fun i h => hx ⟨⟨i.1, by omega⟩, h.symm⟩⟩
              have h_armMap_rel : ∀ x y : Option W₀, x ≠ y →
                  (Gᶜ.Adj (f (armMap x)) (f (armMap y)) ↔
                    (terminalPathExtGraph G₀ (w_path ⟨0, by omega⟩)).Adj x y) := by
                have h_path_iff : ∀ p₁ p₂ : Fin (L + 1), p₁ ≠ p₂ →
                    (Gᶜ.Adj (f (pathNode p₁)) (f (pathNode p₂)) ↔
                      (p₁.1 + 1 = p₂.1 ∨ p₂.1 + 1 = p₁.1)) := by
                  intro p₁ p₂ hp_ne
                  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hp_ne) with hlt | hgt
                  · rw [h_pathNode_adj p₁ p₂ hlt]; omega
                  · rw [adj_comm, h_pathNode_adj p₂ p₁ hgt]; omega
                have h_head_path : ∀ (z₀ : W₀) (hz₀ : ¬∃ a : Fin L, w_path a = z₀) (p : Fin (L + 1)),
                    (Gᶜ.Adj (f (pathNode p))
                      (f (Sum.inr ⟨z₀, fun i h => hz₀ ⟨⟨i.1, by omega⟩, h.symm⟩⟩)) ↔
                      (p.1 = L ∧ G₀.Adj (w_path ⟨L - 1, by omega⟩) z₀)) := by
                  intro z₀ hz₀ p
                  let headNode : ArmVert W₀ w_path (n + 1) hn.le :=
                    Sum.inr ⟨z₀, fun i h => hz₀ ⟨⟨i.1, by omega⟩, h.symm⟩⟩
                  have hz_not_path : ∀ a : Fin L, z₀ ≠ w_path a := fun a h => hz₀ ⟨a, h.symm⟩
                  have hproj_ne : multiSubstProj xs (pathNode p) ≠ multiSubstProj xs headNode := by
                    rw [h_pathNode_proj p]
                    exact fun h => hz₀ ⟨⟨max q.1 (p.1 - 1), by omega⟩, h⟩
                  have hne_node : pathNode p ≠ headNode := fun h => hproj_ne (congr_arg _ h)
                  by_cases hpL : p.1 = L
                  · have hmax : max q.1 (p.1 - 1) = L - 1 := by omega
                    constructor
                    · intro hgc
                      refine ⟨hpL, ?_⟩
                      by_contra hnG₀
                      refine hgc.2 (h_non _ _ ?_)
                      rw [h_proj_diff _ _ hproj_ne, h_pathNode_proj p]
                      simpa [headNode, multiSubstProj, hmax] using hnG₀
                    · rintro ⟨_, hG₀⟩
                      refine ⟨f.injective.ne hne_node, h_edge _ _ hne_node (Or.inr rfl) ?_⟩
                      rw [h_proj_diff _ _ hproj_ne, h_pathNode_proj p]
                      simpa [headNode, multiSubstProj, hmax] using hG₀
                  · have hlt_L : max q.1 (p.1 - 1) < L - 1 := by omega
                    refine iff_of_false (fun hgc => hgc.2 (h_non _ _ ?_)) (fun h => hpL h.1)
                    rw [h_proj_diff _ _ hproj_ne, h_pathNode_proj p]
                    intro hG₀
                    have := hTP2 z₀ hz_not_path ⟨max q.1 (p.1 - 1), by omega⟩ (G₀.symm hG₀)
                    dsimp at this; omega
                have h_on_path : ∀ (z₀ : W₀) (hz₀ : ∃ a : Fin L, w_path a = z₀),
                    ∃ a : Fin L, w_path a = z₀ ∧ armMap (some z₀) = pathNode ⟨a.1 + 1, by omega⟩ :=
                  fun z₀ hz₀ => ⟨Classical.choose hz₀, Classical.choose_spec hz₀, dif_pos hz₀⟩
                rintro (_ | x) (_ | y) hxy
                · exact False.elim (hxy rfl)
                · by_cases hy : ∃ a : Fin L, w_path a = y
                  · obtain ⟨a, rfl, h_ay⟩ := h_on_path y hy
                    clear hy hxy
                    change Gᶜ.Adj (f (pathNode ⟨0, by omega⟩)) (f (armMap (some (w_path a)))) ↔ _
                    rw [h_ay]
                    have hp_ne : (⟨0, by omega⟩ : Fin (L + 1)) ≠ ⟨a.1 + 1, by omega⟩ := by
                      intro h; have hv : (0 : ℕ) = a.1 + 1 := congr_arg Fin.val h; omega
                    rw [h_path_iff _ _ hp_ne]
                    change (0 + 1 = a.1 + 1 ∨ (a.1 + 1) + 1 = 0) ↔ w_path a = w_path ⟨0, by omega⟩
                    constructor
                    · intro h12
                      exact congr_arg w_path (Fin.ext (by show a.1 = 0; omega))
                    · intro h_eq
                      have ha0 : a.1 = 0 := congr_arg Fin.val (w_path.injective h_eq)
                      omega
                  · dsimp only [armMap]
                    rw [dif_neg hy, h_head_path y hy ⟨0, by omega⟩]
                    change (0 = L ∧ G₀.Adj (w_path ⟨L - 1, by omega⟩) y) ↔ y = w_path ⟨0, by omega⟩
                    exact iff_of_false (by omega) (fun h => hy ⟨⟨0, by omega⟩, h.symm⟩)
                · by_cases hx : ∃ a : Fin L, w_path a = x
                  · obtain ⟨a, rfl, h_ax⟩ := h_on_path x hx
                    clear hx hxy
                    change Gᶜ.Adj (f (armMap (some (w_path a)))) (f (pathNode ⟨0, by omega⟩)) ↔ _
                    rw [h_ax]
                    have hp_ne : (⟨a.1 + 1, by omega⟩ : Fin (L + 1)) ≠ ⟨0, by omega⟩ := by
                      intro h; have hv : a.1 + 1 = 0 := congr_arg Fin.val h; omega
                    rw [h_path_iff _ _ hp_ne]
                    change ((a.1 + 1) + 1 = 0 ∨ 0 + 1 = a.1 + 1) ↔ w_path a = w_path ⟨0, by omega⟩
                    constructor
                    · intro h12
                      exact congr_arg w_path (Fin.ext (by show a.1 = 0; omega))
                    · intro h_eq
                      have ha0 : a.1 = 0 := congr_arg Fin.val (w_path.injective h_eq)
                      omega
                  · dsimp only [armMap]
                    rw [dif_neg hx, adj_comm, h_head_path x hx ⟨0, by omega⟩]
                    change (0 = L ∧ G₀.Adj (w_path ⟨L - 1, by omega⟩) x) ↔ x = w_path ⟨0, by omega⟩
                    exact iff_of_false (by omega) (fun h => hx ⟨⟨0, by omega⟩, h.symm⟩)
                · have hx_ne_y : x ≠ y := fun h => hxy (congr_arg some h)
                  by_cases hx : ∃ a : Fin L, w_path a = x
                  · obtain ⟨a, rfl, h_ax⟩ := h_on_path x hx
                    clear hx hxy
                    rw [h_ax]
                    by_cases hy : ∃ b : Fin L, w_path b = y
                    · obtain ⟨b, rfl, h_by⟩ := h_on_path y hy
                      clear hy
                      rw [h_by]
                      have hab : a ≠ b := fun h => hx_ne_y (congr_arg w_path h)
                      have hp_ne : (⟨a.1 + 1, by omega⟩ : Fin (L + 1)) ≠ ⟨b.1 + 1, by omega⟩ := by
                        intro h
                        have hv : a.1 + 1 = b.1 + 1 := congr_arg Fin.val h
                        exact hab (Fin.ext (by omega))
                      rw [h_path_iff _ _ hp_ne]
                      change ((a.1 + 1) + 1 = b.1 + 1 ∨ (b.1 + 1) + 1 = a.1 + 1) ↔
                        G₀.Adj (w_path a) (w_path b)
                      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with hlt | hgt
                      · rw [hTP1 a b hlt]; omega
                      · rw [adj_comm, hTP1 b a hgt]; omega
                    · dsimp only [armMap]
                      rw [dif_neg hy, h_head_path y hy ⟨a.1 + 1, by omega⟩]
                      change (a.1 + 1 = L ∧ G₀.Adj (w_path ⟨L - 1, by omega⟩) y) ↔ G₀.Adj (w_path a) y
                      have hz_not_path : ∀ c : Fin L, y ≠ w_path c := fun c h => hy ⟨c, h.symm⟩
                      constructor
                      · rintro ⟨haL, hG₀⟩
                        have ha_eq : a = ⟨L - 1, by omega⟩ := Fin.ext (by show a.1 = L - 1; omega)
                        rwa [ha_eq]
                      · intro hG₀
                        have haL := hTP2 y hz_not_path a (G₀.symm hG₀)
                        have ha_eq : a = ⟨L - 1, by omega⟩ := Fin.ext haL
                        rw [ha_eq] at hG₀
                        exact ⟨by omega, hG₀⟩
                  · by_cases hy : ∃ b : Fin L, w_path b = y
                    · obtain ⟨b, rfl, h_by⟩ := h_on_path y hy
                      clear hy hxy
                      rw [h_by]
                      dsimp only [armMap]
                      rw [dif_neg hx, adj_comm, h_head_path x hx ⟨b.1 + 1, by omega⟩]
                      change (b.1 + 1 = L ∧ G₀.Adj (w_path ⟨L - 1, by omega⟩) x) ↔ G₀.Adj x (w_path b)
                      have hz_not_path : ∀ c : Fin L, x ≠ w_path c := fun c h => hx ⟨c, h.symm⟩
                      constructor
                      · rintro ⟨hbL, hG₀⟩
                        have hb_eq : b = ⟨L - 1, by omega⟩ := Fin.ext (by show b.1 = L - 1; omega)
                        rwa [hb_eq, adj_comm]
                      · intro hG₀
                        have hbL := hTP2 x hz_not_path b hG₀
                        have hb_eq : b = ⟨L - 1, by omega⟩ := Fin.ext hbL
                        rw [hb_eq] at hG₀
                        exact ⟨by omega, hG₀.symm⟩
                    · dsimp only [armMap, terminalPathExtGraph]
                      rw [dif_neg hx, dif_neg hy]
                      let nodeX : ArmVert W₀ w_path (n + 1) hn.le :=
                        Sum.inr ⟨x, fun i h => hx ⟨⟨i.1, by omega⟩, h.symm⟩⟩
                      let nodeY : ArmVert W₀ w_path (n + 1) hn.le :=
                        Sum.inr ⟨y, fun i h => hy ⟨⟨i.1, by omega⟩, h.symm⟩⟩
                      have hne_node : nodeX ≠ nodeY :=
                        fun h => hx_ne_y (congr_arg Subtype.val (Sum.inr.inj h))
                      constructor
                      · intro hgc
                        by_contra hnG₀
                        refine hgc.2 (h_non nodeX nodeY ?_)
                        simpa [nodeX, nodeY, armGraph, multiSubstGraph, multiSubstProj, hx_ne_y] using hnG₀
                      · intro hG₀
                        refine ⟨f.injective.ne hne_node, h_edge nodeX nodeY hne_node (Or.inl rfl) ?_⟩
                        simpa [nodeX, nodeY, armGraph, multiSubstGraph, multiSubstProj, hx_ne_y] using hG₀
              have h_armMap_inj : Function.Injective armMap := by
                have hz_q_inj : Function.Injective (z q) :=
                  pathSpec_inj (g := fun u => f (Sum.inl (q, u)))
                    (P := fun u => armSpecPred w_path n hn_prev.le u = true)
                    (hz_path q)
                    (fun i hi => hz_spec q ⟨i.1, by omega⟩)
                    (fun i hi => by
                      dsimp only
                      have hi_eq : i = Fin.last (n + 1) := Fin.ext (by show i.1 = n + 1; omega)
                      rw [hi_eq, hz_nonspec q]; decide)
                have h_pathNode_inj : Function.Injective pathNode := by
                  intro p₁ p₂ hp_eq
                  by_contra hp_ne
                  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hp_ne) with hlt | hgt
                  · by_cases hp₂_1 : p₂.1 ≤ q.1 + 1
                    · have hp₁_1 : p₁.1 ≤ q.1 + 1 := by omega
                      have h1 : pathNode p₁ = Sum.inl (q, z q ⟨n - q.1 + p₁.1, by omega⟩) := by
                        dsimp [pathNode]; rw [dif_pos hp₁_1]
                      have h2 : pathNode p₂ = Sum.inl (q, z q ⟨n - q.1 + p₂.1, by omega⟩) := by
                        dsimp [pathNode]; rw [dif_pos hp₂_1]
                      rw [h1, h2] at hp_eq
                      have hv : n - q.1 + p₁.1 = n - q.1 + p₂.1 :=
                        congr_arg Fin.val (hz_q_inj (Prod.mk.inj (Sum.inl.inj hp_eq)).2)
                      omega
                    · have hs : max q.1 (p₁.1 - 1) < max q.1 (p₂.1 - 1) := by omega
                      have hproj := congr_arg (multiSubstProj xs) hp_eq
                      rw [h_pathNode_proj p₁, h_pathNode_proj p₂] at hproj
                      have hfin := congr_arg Fin.val (w_path.injective hproj)
                      dsimp at hfin; omega
                  · by_cases hp₁_1 : p₁.1 ≤ q.1 + 1
                    · have hp₂_1 : p₂.1 ≤ q.1 + 1 := by omega
                      have h1 : pathNode p₂ = Sum.inl (q, z q ⟨n - q.1 + p₂.1, by omega⟩) := by
                        dsimp [pathNode]; rw [dif_pos hp₂_1]
                      have h2 : pathNode p₁ = Sum.inl (q, z q ⟨n - q.1 + p₁.1, by omega⟩) := by
                        dsimp [pathNode]; rw [dif_pos hp₁_1]
                      rw [h1, h2] at hp_eq
                      have hv : n - q.1 + p₁.1 = n - q.1 + p₂.1 :=
                        congr_arg Fin.val (hz_q_inj (Prod.mk.inj (Sum.inl.inj hp_eq)).2)
                      omega
                    · have hs : max q.1 (p₂.1 - 1) < max q.1 (p₁.1 - 1) := by omega
                      have hproj := congr_arg (multiSubstProj xs) hp_eq.symm
                      rw [h_pathNode_proj p₂, h_pathNode_proj p₁] at hproj
                      have hfin := congr_arg Fin.val (w_path.injective hproj)
                      dsimp at hfin; omega
                rintro (_ | x) (_ | y) heq
                · rfl
                · dsimp only [armMap] at heq
                  by_cases hy : ∃ b : Fin L, w_path b = y
                  · rw [dif_pos hy] at heq
                    have hfin := congr_arg Fin.val (h_pathNode_inj heq); dsimp at hfin; omega
                  · rw [dif_neg hy] at heq
                    have hproj := congr_arg (multiSubstProj xs) heq
                    rw [h_pathNode_proj] at hproj
                    exact False.elim (hy ⟨_, hproj⟩)
                · dsimp only [armMap] at heq
                  by_cases hx : ∃ a : Fin L, w_path a = x
                  · rw [dif_pos hx] at heq
                    have hfin := congr_arg Fin.val (h_pathNode_inj heq); dsimp at hfin; omega
                  · rw [dif_neg hx] at heq
                    have hproj := congr_arg (multiSubstProj xs) heq.symm
                    rw [h_pathNode_proj] at hproj
                    exact False.elim (hx ⟨_, hproj⟩)
                · dsimp only [armMap] at heq
                  by_cases hx : ∃ a : Fin L, w_path a = x
                  · rw [dif_pos hx] at heq
                    by_cases hy : ∃ b : Fin L, w_path b = y
                    · rw [dif_pos hy] at heq
                      have hfin := congr_arg Fin.val (h_pathNode_inj heq)
                      dsimp at hfin
                      have h_eq_ch : Classical.choose hx = Classical.choose hy := Fin.ext (by omega)
                      exact congr_arg some (by rw [← Classical.choose_spec hx, h_eq_ch, Classical.choose_spec hy])
                    · rw [dif_neg hy] at heq
                      have hproj := congr_arg (multiSubstProj xs) heq
                      rw [h_pathNode_proj] at hproj
                      exact False.elim (hy ⟨_, hproj⟩)
                  · rw [dif_neg hx] at heq
                    by_cases hy : ∃ b : Fin L, w_path b = y
                    · rw [dif_pos hy] at heq
                      have hproj := congr_arg (multiSubstProj xs) heq.symm
                      rw [h_pathNode_proj] at hproj
                      exact False.elim (hx ⟨_, hproj⟩)
                    · rw [dif_neg hy] at heq
                      exact congr_arg some (congr_arg Subtype.val (Sum.inr.inj heq))
              refine ⟨RelEmbedding.mk ⟨fun x => f (armMap x),
                fun x y h => h_armMap_inj (f.injective h)⟩ ?_⟩
              intro a b
              show Gᶜ.Adj (f (armMap a)) (f (armMap b)) ↔
                (terminalPathExtGraph G₀ (w_path ⟨0, by omega⟩)).Adj a b
              by_cases hab : a = b
              · subst hab; simp
              · exact h_armMap_rel a b hab
      rcases h_back (n + 1) le_rfl with h_done | ⟨u_all, hu_spec, hu_adj⟩
      · exact Or.inl h_done
      · right
        let w_end : ArmVert W₀ w_path (n + 1) hn.le :=
          Sum.inr ⟨w_path ⟨n + 2, by omega⟩,
            fun i h => by
              have hv := congr_arg Fin.val (w_path.injective h)
              simp at hv; omega⟩
        let p_full : Fin (n + 3) → ArmVert W₀ w_path (n + 1) hn.le := fun i =>
          if hi : i.1 < n + 2 then
            Sum.inl (⟨i.1, hi⟩, u_all ⟨i.1, hi⟩ (by omega))
          else
            w_end
        have hp_proj : ∀ i : Fin (n + 3),
            multiSubstProj xs (p_full i) = w_path ⟨i.1, by omega⟩ := by
          intro i
          dsimp [p_full]
          split_ifs with hi
          · dsimp [multiSubstProj, xs]
          · have hi_eq : i.1 = n + 2 := by omega
            simp [w_end, multiSubstProj, hi_eq]
        refine ⟨p_full, ?_, ?_, ?_⟩
        · have h_lt : ∀ i j : Fin (n + 3), i.1 < j.1 →
              (Gᶜ.Adj (f (p_full i)) (f (p_full j)) ↔ j.1 = i.1 + 1) := by
            intro i j hlt
            have hproj_ne : multiSubstProj xs (p_full i) ≠ multiSubstProj xs (p_full j) := by
              rw [hp_proj i, hp_proj j]
              exact w_path.injective.ne (by simp [Fin.ext_iff]; omega)
            have hne_p : p_full i ≠ p_full j := fun h => hproj_ne (congr_arg _ h)
            by_cases h_consec : j.1 = i.1 + 1
            · refine iff_of_true ?_ h_consec
              by_cases hj_lt : j.1 < n + 2
              · obtain ⟨i_val, hi_full⟩ := i
                obtain ⟨j_val, hj_full⟩ := j
                dsimp at hlt h_consec hj_lt ⊢
                subst h_consec
                have hi_lt : i_val < n + 2 := by omega
                dsimp [p_full]
                rw [dif_pos hi_lt, dif_pos hj_lt]
                exact hu_adj ⟨i_val, hi_lt⟩ (by omega) hj_lt
              · have h_ns : armSpecPred w_path (n + 1) hn.le (p_full j) = false := by
                  dsimp [p_full]; rw [dif_neg hj_lt]; rfl
                refine ⟨f.injective.ne hne_p, h_edge _ _ hne_p (Or.inr h_ns) ?_⟩
                rw [h_proj_diff _ _ hproj_ne, hp_proj i, hp_proj j]
                exact not_not.mpr ((hTP1 ⟨i.1, by omega⟩ ⟨j.1, by omega⟩ (by dsimp; exact hlt)).mpr (by dsimp; exact h_consec))
            · refine iff_of_false (fun hgc => hgc.2 (h_non _ _ ?_)) h_consec
              rw [h_proj_diff _ _ hproj_ne, hp_proj i, hp_proj j]
              intro hG₀
              have := (hTP1 ⟨i.1, by omega⟩ ⟨j.1, by omega⟩ (by dsimp; exact hlt)).mp hG₀
              dsimp at this; omega
          intro i j
          simp only [pathGraph_adj]
          by_cases hij : i = j
          · subst hij; simp
          · rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hgt
            · rw [h_lt i j hlt]; omega
            · rw [adj_comm, h_lt j i hgt]; omega
        · intro a
          dsimp [p_full]
          rw [dif_pos a.2]
          exact hu_spec a (by omega)
        · dsimp [p_full]
          rw [dif_neg (by simp)]
          rfl

/-! ### Section 3: Proposition 7(3) & Proposition 8(2) — All Subdivided Spiders `SpiderGraph d` ($d \ge 2$) -/

/-- Helper: any induced embedding `H ↪g Gᶜ` refutes `IsInducedSubgraphFree G Hᶜ`. -/
private theorem not_isInducedSubgraphFree_compl_of_emb_compl {W V : Type*}
    {H : SimpleGraph W} {G : SimpleGraph V} (emb : H ↪g Gᶜ) :
    ¬IsInducedSubgraphFree G Hᶜ := by
  intro hFree
  refine hFree ⟨emb.toEmbedding, ?_⟩
  ext a b
  by_cases hab : a = b
  · subst hab; simp
  · have h1 := emb.map_rel_iff (a := a) (b := b)
    simp only [compl_adj, comap_adj, hab, emb.injective.ne hab, ne_eq, not_false_eq_true,
      true_and] at h1 ⊢
    exact ⟨fun hn => by by_contra hg; exact hn (h1.mp hg),
      fun hg hn => h1.mpr hn hg⟩

/-- Terminal tail path embedding `a ↦ m + 3 - a` of length `m` inside `Fin (m + 4)`
(`0 ↦ u_m = m + 3`, ..., `m - 1 ↦ u_1 = 4`). -/
def tailPathEmb (m : ℕ) : Fin m ↪ Fin (m + 4) where
  toFun a := ⟨m + 3 - a.1, by omega⟩
  inj' a b h := Fin.ext (by
    have hv : m + 3 - a.1 = m + 3 - b.1 := congr_arg Fin.val h
    omega)

@[simp]
private theorem tailPathEmb_val (m : ℕ) (a : Fin m) :
    (tailPathEmb m a).1 = m + 3 - a.1 := rfl

private theorem tailPathEmb_spider_TP1 (m : ℕ) :
    ∀ a b : Fin m, a.1 < b.1 →
      ((SpiderGraph m).Adj (tailPathEmb m a) (tailPathEmb m b) ↔ b.1 = a.1 + 1) := by
  intro a b hlt
  dsimp [SpiderGraph]
  rw [if_neg (by omega), if_pos (by omega)]
  simp only [spiderAdjLt, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  omega

private theorem tailPathEmb_spider_TP2 (m : ℕ) :
    ∀ z : Fin (m + 4), (∀ a : Fin m, z ≠ tailPathEmb m a) →
      ∀ a : Fin m, (SpiderGraph m).Adj z (tailPathEmb m a) → a.1 = m - 1 := by
  intro z hz a hadj
  have hz4 : z.1 < 4 := by
    by_contra hge
    exact hz ⟨m + 3 - z.1, by omega⟩ (Fin.ext (by simp; omega))
  dsimp [SpiderGraph] at hadj
  rw [if_pos (by omega)] at hadj
  simp only [spiderAdjLt, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hadj
  omega

/-- Isomorphism `terminalPathExtGraph (SpiderGraph m) (tailPathEmb m 0) ≃g SpiderGraph (m + 1)` for `1 ≤ m`. -/
def spiderExtIso (m : ℕ) (hm : 1 ≤ m) :
    terminalPathExtGraph (SpiderGraph m) (tailPathEmb m ⟨0, by omega⟩) ≃g SpiderGraph (m + 1) where
  toFun
    | none => ⟨m + 4, by omega⟩
    | some x => ⟨x.1, by omega⟩
  invFun y :=
    if hy : y.1 < m + 4 then some ⟨y.1, hy⟩ else none
  left_inv
    | none => by simp
    | some x => by simp [x.2]
  right_inv y := by
    by_cases hy : y.1 < m + 4
    · simp [hy]
    · simp [hy]; ext; dsimp; omega
  map_rel_iff' := by
    rintro (_ | x) (_ | y)
    · simp [SpiderGraph]
    · have hlt : y.1 < m + 4 := y.2
      dsimp [SpiderGraph, terminalPathExtGraph]
      rw [if_neg (by omega), if_pos hlt]
      simp only [spiderAdjLt, tailPathEmb_val, Bool.or_eq_true, Bool.and_eq_true,
        beq_iff_eq, decide_eq_true_eq, Fin.ext_iff]
      omega
    · have hlt : x.1 < m + 4 := x.2
      dsimp [SpiderGraph, terminalPathExtGraph]
      rw [if_pos hlt]
      simp only [spiderAdjLt, tailPathEmb_val, Bool.or_eq_true, Bool.and_eq_true,
        beq_iff_eq, decide_eq_true_eq, Fin.ext_iff]
      omega
    · rfl

/-- Explicit graph isomorphism $P_4[0 \leftarrow \overline{K_2}] \simeq_g S_{1,2,1}$ (`SpiderGraph 1`). -/
private def substP4BotIsoSpider1 :
    substGraph (pathGraph 4) 0 (⊥ : SimpleGraph (Fin 2)) ≃g SpiderGraph 1 where
  toFun
    | Sum.inr 0 => 1
    | Sum.inr 1 => 4
    | Sum.inl ⟨1, _⟩ => 0
    | Sum.inl ⟨2, _⟩ => 2
    | Sum.inl ⟨3, _⟩ => 3
    | Sum.inl ⟨⟨0, _⟩, hne⟩ => False.elim (hne rfl)
  invFun
    | 0 => Sum.inl ⟨1, by decide⟩
    | 1 => Sum.inr 0
    | 2 => Sum.inl ⟨2, by decide⟩
    | 3 => Sum.inl ⟨3, by decide⟩
    | 4 => Sum.inr 1
  left_inv x := by
    rcases x with ⟨u, hu⟩ | r
    · fin_cases u
      · exact False.elim (hu rfl)
      · rfl
      · rfl
      · rfl
    · fin_cases r <;> rfl
  right_inv y := by fin_cases y <;> rfl
  map_rel_iff' := by
    rintro (⟨u, hu⟩ | r) (⟨v, hv⟩ | s)
    · fin_cases u <;> fin_cases v <;>
        first | exact False.elim (hu rfl) | exact False.elim (hv rfl) | decide +revert
    · fin_cases u <;> fin_cases s <;>
        first | exact False.elim (hu rfl) | decide +revert
    · fin_cases r <;> fin_cases v <;>
        first | exact False.elim (hv rfl) | decide +revert
    · fin_cases r <;> fin_cases s <;> decide

/-- `SpiderGraph 1` ($S_{1,2,1} \cong B(2,2)$) unconditionally satisfies `HasErdosHajnalProp`. -/
theorem hasErdosHajnalProp_spiderGraph_1 : HasErdosHajnalProp (SpiderGraph 1) := by
  have hP4 : HasErdosHajnalProp (pathGraph 4) :=
    (main_theorem_A_paths_le_9 4 (by decide) (by decide)).1
  have h_sub : HasErdosHajnalProp (substGraph (pathGraph 4) 0 (⊥ : SimpleGraph (Fin 2))) :=
    hasErdosHajnalProp_substGraph (pathGraph 4) 0 (⊥ : SimpleGraph (Fin 2))
      hP4 hasErdosHajnalProp_bot_fin2
  exact hasErdosHajnalProp_of_iso substP4BotIsoSpider1 h_sub

/-- Vertex set of the spider left arm $\operatorname{Arm}_{S,L}^{(d)} := (\text{SpiderGraph } (d - 1))[u_{d-1} \leftarrow K_2]^c$. -/
abbrev SpiderLeftVert (d : ℕ) : Type :=
  {v : Fin ((d - 1) + 4) // v ≠ Fin.last ((d - 1) + 3)} ⊕ Fin 2

/-- Left arm graph $\operatorname{Arm}_{S,L}^{(d)}$ in $G$-polarity ($G^c$-complement is $S_{1,2,d-1}[u_{d-1} \leftarrow K_2]$). -/
def spiderLeftArm (d : ℕ) : SimpleGraph (SpiderLeftVert d) :=
  (substGraph (SpiderGraph (d - 1)) (Fin.last ((d - 1) + 3)) (⊤ : SimpleGraph (Fin 2)))ᶜ

/-- Pure `ℕ` index map for the $(d+2)$-vertex induced path $(x_2 - w_2 - c - u_1 - \dots - u_{d-1})$. -/
def spiderLongPathVal (i : ℕ) : ℕ :=
  if i = 0 then 3
  else if i = 1 then 2
  else if i = 2 then 0
  else i + 1

/-- The $(d+2)$-vertex induced path $(x_2 - w_2 - c - u_1 - \dots - u_{d-1})$ inside `SpiderGraph (d - 1)` for any $d \ge 2$. -/
def spiderLongPath (d : ℕ) (idx : Fin (d + 2)) : Fin ((d - 1) + 4) :=
  ⟨spiderLongPathVal idx.1, by dsimp [spiderLongPathVal]; split_ifs <;> omega⟩

@[simp]
private theorem spiderLongPath_val (d : ℕ) (idx : Fin (d + 2)) :
    (spiderLongPath d idx).1 = spiderLongPathVal idx.1 := rfl

private theorem spiderLongPathVal_inj {d : ℕ} (_hd : 2 ≤ d) {i j : Fin (d + 2)}
    (h : spiderLongPath d i = spiderLongPath d j) : i.1 = j.1 := by
  have hv : spiderLongPathVal i.1 = spiderLongPathVal j.1 := congr_arg Fin.val h
  dsimp only [spiderLongPathVal] at hv
  split_ifs at hv <;> omega

private theorem spiderLongPathVal_ge3 {n : ℕ} (hn : 3 ≤ n) :
    spiderLongPathVal n = n + 1 := by
  unfold spiderLongPathVal
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

private theorem spiderLongPathVal_lt_iff {a b : ℕ} (hlt : a < b) :
    (let va := spiderLongPathVal a; let vb := spiderLongPathVal b
     if va < vb then spiderAdjLt va vb = true else if vb < va then spiderAdjLt vb va = true else False) ↔
    b = a + 1 := by
  dsimp only
  rcases (show (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 0 ∧ 3 ≤ b) ∨
      (a = 1 ∧ b = 2) ∨ (a = 1 ∧ 3 ≤ b) ∨ (a = 2 ∧ 3 ≤ b) ∨ (3 ≤ a ∧ 3 ≤ b) by omega) with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, hb3⟩ | ⟨rfl, rfl⟩ | ⟨rfl, hb3⟩ | ⟨rfl, hb3⟩ | ⟨ha3, hb3⟩
  · decide
  · decide
  · rw [show spiderLongPathVal 0 = 3 from rfl, spiderLongPathVal_ge3 hb3, if_pos (by omega)]
    unfold spiderAdjLt; simp; try omega
  · decide
  · rw [show spiderLongPathVal 1 = 2 from rfl, spiderLongPathVal_ge3 hb3, if_pos (by omega)]
    unfold spiderAdjLt; simp; try omega
  · rw [show spiderLongPathVal 2 = 0 from rfl, spiderLongPathVal_ge3 hb3, if_pos (by omega)]
    unfold spiderAdjLt; simp; try omega
  · rw [spiderLongPathVal_ge3 ha3, spiderLongPathVal_ge3 hb3, if_pos (by omega)]
    unfold spiderAdjLt; simp; try omega

private theorem spiderLongPath_adj_iff {d : ℕ} (_hd : 2 ≤ d) (i j : Fin (d + 2)) :
    (SpiderGraph (d - 1)).Adj (spiderLongPath d i) (spiderLongPath d j) ↔
      (i.1 + 1 = j.1 ∨ j.1 + 1 = i.1) := by
  have h_lt : ∀ a b : Fin (d + 2), a.1 < b.1 →
      ((SpiderGraph (d - 1)).Adj (spiderLongPath d a) (spiderLongPath d b) ↔ b.1 = a.1 + 1) :=
    fun _ _ hlt => spiderLongPathVal_lt_iff hlt
  by_cases hij : i = j
  · subst hij; simp
  · rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hgt
    · rw [h_lt i j hlt]; omega
    · rw [adj_comm, h_lt j i hgt]; omega

/-- Last 4 vertices `(p₀, p₁, p₂, p₃)` of the $(d+2)$-vertex path in `spiderLeftArm d` ($d \ge 2$). -/
def spiderLeftP0 {d : ℕ} (hd : 2 ≤ d) : SpiderLeftVert d :=
  Sum.inl ⟨spiderLongPath d ⟨d - 2, by omega⟩, by
    intro h
    have hv : spiderLongPathVal (d - 2) = (d - 1) + 3 := congr_arg Fin.val h
    dsimp only [spiderLongPathVal] at hv
    split_ifs at hv <;> omega⟩

def spiderLeftP1 {d : ℕ} (hd : 2 ≤ d) : SpiderLeftVert d :=
  Sum.inl ⟨spiderLongPath d ⟨d - 1, by omega⟩, by
    intro h
    have hv : spiderLongPathVal (d - 1) = (d - 1) + 3 := congr_arg Fin.val h
    dsimp only [spiderLongPathVal] at hv
    split_ifs at hv <;> omega⟩

def spiderLeftP2 {d : ℕ} (hd : 2 ≤ d) : SpiderLeftVert d :=
  Sum.inl ⟨spiderLongPath d ⟨d, by omega⟩, by
    intro h
    have hv : spiderLongPathVal d = (d - 1) + 3 := congr_arg Fin.val h
    dsimp only [spiderLongPathVal] at hv
    split_ifs at hv <;> omega⟩

def spiderLeftP3 (d : ℕ) : SpiderLeftVert d := Sum.inr 0

def spiderLeft4 {d : ℕ} (hd : 2 ≤ d) : Fin 4 → SpiderLeftVert d
  | 0 => spiderLeftP1 hd
  | 1 => spiderLeftP0 hd
  | 2 => spiderLeftP2 hd
  | 3 => spiderLeftP3 d

/-- 3-vertex left special set $S_{S,L}^{(d)} := \{p_0, p_2, p_3\}$ inside `spiderLeftArm d`. -/
def specSpiderLeftArm {d : ℕ} (hd : 2 ≤ d) : Finset (SpiderLeftVert d) :=
  {spiderLeftP0 hd, spiderLeftP2 hd, spiderLeftP3 d}

/-- Right arm vertex type for `SpiderGraph d`: singleton `Fin 1` at $d \le 2$, and `ArmVert` at $d = m + 3 \ge 3$. -/
abbrev SpiderRightVert : ℕ → Type
  | m + 3 => ArmVert (Fin ((m + 2) + 4)) (tailPathEmb (m + 2)) m (by omega)
  | _ => Fin 1

instance instFintypeSpiderRightVert : ∀ d : ℕ, Fintype (SpiderRightVert d)
  | m + 3 => inferInstanceAs (Fintype (ArmVert (Fin ((m + 2) + 4)) (tailPathEmb (m + 2)) m _))
  | 0 | 1 | 2 => inferInstanceAs (Fintype (Fin 1))

noncomputable instance instDecidableEqSpiderRightVert (d : ℕ) : DecidableEq (SpiderRightVert d) :=
  Classical.decEq _

instance instNonemptySpiderRightVert : ∀ d : ℕ, Nonempty (SpiderRightVert d)
  | m + 3 => inferInstanceAs (Nonempty (ArmVert (Fin ((m + 2) + 4)) (tailPathEmb (m + 2)) m _))
  | 0 | 1 | 2 => ⟨0⟩

/-- Right arm graph for `SpiderGraph d` ($d \ge 2$). -/
abbrev spiderRightArm : ∀ d : ℕ, SimpleGraph (SpiderRightVert d)
  | m + 3 => armGraph (SpiderGraph (m + 2))ᶜ (tailPathEmb (m + 2)) m (by omega)
  | 0 | 1 | 2 => ⊥

/-- Right arm special vertex set for `SpiderGraph d` ($d \ge 2$). -/
noncomputable abbrev specSpiderRightArm : ∀ d : ℕ, Finset (SpiderRightVert d)
  | m + 3 => armSpecFinset (tailPathEmb (m + 2)) m (by omega)
  | 0 | 1 | 2 => ∅

/-- Unified pure-substitution witness $W_{S,d}$ for `SpiderGraph d` ($d \ge 2$). -/
def witnessWSpider (d : ℕ) : SimpleGraph (SpiderLeftVert d ⊕ SpiderRightVert d) :=
  twoArmJoinGraph (spiderLeftArm d) (spiderRightArm d)

/-- Special vertex set $S_{S,d}$ for `witnessWSpider d` ($d \ge 2$). -/
noncomputable def specWSpider {d : ℕ} (hd : 2 ≤ d) : Finset (SpiderLeftVert d ⊕ SpiderRightVert d) :=
  twoArmSpecFinset (specSpiderLeftArm hd) (specSpiderRightArm d)

/-- `witnessWSpider d` satisfies `HasErdosHajnalProp` for every $d \ge 2$ whenever `SpiderGraph (d - 1)` does. -/
theorem hasErdosHajnalProp_witnessWSpider {d : ℕ} (hd : 2 ≤ d)
    (h_prev : HasErdosHajnalProp (SpiderGraph (d - 1))) :
    HasErdosHajnalProp (witnessWSpider d) := by
  have hL : HasErdosHajnalProp (spiderLeftArm d) :=
    (hasErdosHajnalProp_substGraph (SpiderGraph (d - 1))
      (Fin.last ((d - 1) + 3)) (⊤ : SimpleGraph (Fin 2)) h_prev hasErdosHajnalProp_top_fin2).compl
  have hR : HasErdosHajnalProp (spiderRightArm d) := by
    rcases eq_or_lt_of_le hd with rfl | hd_gt2
    · refine ⟨1, zero_lt_one, fun V _ _ G hG => ?_⟩
      haveI := isEmpty_of_isInducedSubgraphFree_card_le_one G (⊥ : SimpleGraph (Fin 1)) (by decide) hG
      have h0 : (Fintype.card V : ℝ) = 0 := by simp [Fintype.card_eq_zero]
      rw [h0, Real.zero_rpow one_ne_zero]
      exact Nat.cast_nonneg _
    · obtain ⟨m, rfl⟩ : ∃ m, d = m + 3 := ⟨d - 3, by omega⟩
      exact hasErdosHajnalProp_armGraph h_prev.compl (tailPathEmb (m + 2)) m (by omega)
  exact hasErdosHajnalProp_twoArmJoinGraph hL hR

/-- Helper (`g_L = 1`): cross-arm bridge embedding for `SpiderGraph d` ($d \ge 2$). -/
private theorem spiderBridge_embed {V : Type*} {d : ℕ} (hd : 2 ≤ d)
    {G : SimpleGraph V} {v₀ : V} {f : SpiderLeftVert d ⊕ SpiderRightVert d ↪ V}
    (hf : IsOpenIntervalRealization (witnessWSpider d) (specWSpider hd) G v₀ f)
    (hg_L : ¬G.Adj (f (Sum.inl (spiderLeftP2 hd))) (f (Sum.inl (spiderLeftP3 d))))
    (z : Fin (d - 1) → SpiderRightVert d)
    (hz_adj : ∀ i j : Fin (d - 1),
      Gᶜ.Adj (f (Sum.inr (z i))) (f (Sum.inr (z j))) ↔ (pathGraph (d - 1)).Adj i j)
    (hz_spec : ∀ i : Fin (d - 2), z ⟨i.1, by omega⟩ ∈ specSpiderRightArm d)
    (hz_nonspec : z ⟨d - 2, by omega⟩ ∉ specSpiderRightArm d) :
    Nonempty (SpiderGraph d ↪g Gᶜ) := by
  let f_L := Function.Embedding.inl.trans f
  let f_R := Function.Embedding.inr.trans f
  have hf_L := twoArmRealizationLeft hf
  have hf_R := twoArmRealizationRight hf
  have hp1_not_S : spiderLeftP1 hd ∉ specSpiderLeftArm hd := by
    simp only [specSpiderLeftArm, Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨?_, ?_, Sum.inl_ne_inr⟩
    · intro h
      have hv : d - 1 = d - 2 := spiderLongPathVal_inj hd (Subtype.ext_iff.mp (Sum.inl.inj h))
      omega
    · intro h
      have hv : d - 1 = d := spiderLongPathVal_inj hd (Subtype.ext_iff.mp (Sum.inl.inj h))
      omega
  have hz_inj : Function.Injective z :=
    pathSpec_inj (g := fun u => f (Sum.inr u)) (P := (· ∈ specSpiderRightArm d))
      hz_adj (fun i hi => hz_spec ⟨i.1, by omega⟩)
      (fun i hi => by
        have hi_eq : i = ⟨d - 2, by omega⟩ := Fin.ext (by show i.1 = d - 2; omega)
        rw [hi_eq]; exact hz_nonspec)
  have h_left4_inj : Function.Injective (spiderLeft4 hd) := by
    intro u v huv
    fin_cases u <;> fin_cases v
    · rfl
    · have hv : d - 1 = d - 2 := spiderLongPathVal_inj hd (Subtype.ext_iff.mp (Sum.inl.inj huv)); omega
    · have hv : d - 1 = d := spiderLongPathVal_inj hd (Subtype.ext_iff.mp (Sum.inl.inj huv)); omega
    · exact False.elim (Sum.inl_ne_inr huv)
    · have hv : d - 2 = d - 1 := spiderLongPathVal_inj hd (Subtype.ext_iff.mp (Sum.inl.inj huv)); omega
    · rfl
    · have hv : d - 2 = d := spiderLongPathVal_inj hd (Subtype.ext_iff.mp (Sum.inl.inj huv)); omega
    · exact False.elim (Sum.inl_ne_inr huv)
    · have hv : d = d - 1 := spiderLongPathVal_inj hd (Subtype.ext_iff.mp (Sum.inl.inj huv)); omega
    · have hv : d = d - 2 := spiderLongPathVal_inj hd (Subtype.ext_iff.mp (Sum.inl.inj huv)); omega
    · rfl
    · exact False.elim (Sum.inl_ne_inr huv)
    · exact False.elim (Sum.inr_ne_inl huv)
    · exact False.elim (Sum.inr_ne_inl huv)
    · exact False.elim (Sum.inr_ne_inl huv)
    · rfl
  let g_bridge_opt : Fin (d + 4) → Option (SpiderLeftVert d ⊕ SpiderRightVert d) := fun k =>
    if hk4 : k.1 < 4 then
      some (Sum.inl (spiderLeft4 hd ⟨k.1, hk4⟩))
    else if hk_eq4 : k.1 = 4 then
      none
    else
      some (Sum.inr (z ⟨d + 3 - k.1, by omega⟩))
  let g_bridge : Fin (d + 4) → V := fun k => Option.elim (g_bridge_opt k) v₀ f
  have hg_inj : Function.Injective g_bridge := by
    intro a b hab
    have h_opt_eq : g_bridge_opt a = g_bridge_opt b := by
      dsimp [g_bridge] at hab
      cases ha_o : g_bridge_opt a with
      | none =>
        cases hb_o : g_bridge_opt b with
        | none => rfl
        | some w =>
          rw [ha_o, hb_o] at hab
          exact False.elim (hf.ne_ext w hab.symm)
      | some u =>
        cases hb_o : g_bridge_opt b with
        | none =>
          rw [ha_o, hb_o] at hab
          exact False.elim (hf.ne_ext u hab)
        | some w =>
          rw [ha_o, hb_o] at hab
          exact congr_arg some (f.injective hab)
    by_cases ha4 : a.1 < 4
    · dsimp [g_bridge_opt] at h_opt_eq
      rw [dif_pos ha4] at h_opt_eq
      by_cases hb4 : b.1 < 4
      · rw [dif_pos hb4] at h_opt_eq
        have h4 : (⟨a.1, ha4⟩ : Fin 4) = ⟨b.1, hb4⟩ := h_left4_inj (Sum.inl.inj (Option.some.inj h_opt_eq))
        have hv : a.1 = b.1 := congr_arg (fun x : Fin 4 => x.1) h4
        exact Fin.ext hv
      · rw [dif_neg hb4] at h_opt_eq
        split_ifs at h_opt_eq; simp at h_opt_eq
    · dsimp [g_bridge_opt] at h_opt_eq
      rw [dif_neg ha4] at h_opt_eq
      by_cases hb4 : b.1 < 4
      · rw [dif_pos hb4] at h_opt_eq
        split_ifs at h_opt_eq; simp at h_opt_eq
      · rw [dif_neg hb4] at h_opt_eq
        by_cases ha_eq4 : a.1 = 4
        · rw [dif_pos ha_eq4] at h_opt_eq
          by_cases hb_eq4 : b.1 = 4
          · exact Fin.ext (by omega)
          · rw [dif_neg hb_eq4] at h_opt_eq; simp at h_opt_eq
        · rw [dif_neg ha_eq4] at h_opt_eq
          by_cases hb_eq4 : b.1 = 4
          · rw [dif_pos hb_eq4] at h_opt_eq; simp at h_opt_eq
          · rw [dif_neg hb_eq4] at h_opt_eq
            have hz_eq : d + 3 - a.1 = d + 3 - b.1 :=
              congr_arg Fin.val (hz_inj (Sum.inr.inj (Option.some.inj h_opt_eq)))
            exact Fin.ext (by omega)
  have hg_lt4 : ∀ (k : Fin (d + 4)) (idx : Fin 4), k.1 = idx.1 →
      g_bridge k = f_L (spiderLeft4 hd idx) := by
    intro k idx hk_eq
    have hk4 : k.1 < 4 := by omega
    dsimp [g_bridge, g_bridge_opt, f_L]
    rw [dif_pos hk4]
    exact congr_arg f_L (congr_arg (spiderLeft4 hd) (Fin.ext hk_eq))
  refine ⟨RelEmbedding.mk ⟨g_bridge, hg_inj⟩ ?_⟩
  have h_lt : ∀ a b : Fin (d + 4), a.1 < b.1 →
      (Gᶜ.Adj (g_bridge a) (g_bridge b) ↔ spiderAdjLt a.1 b.1 = true) := by
    intro a b hlt
    by_cases hb3 : b.1 ≤ 3
    · rcases (show (a.1 = 0 ∧ b.1 = 1) ∨ (a.1 = 0 ∧ b.1 = 2) ∨ (a.1 = 0 ∧ b.1 = 3) ∨
          (a.1 = 1 ∧ b.1 = 2) ∨ (a.1 = 1 ∧ b.1 = 3) ∨ (a.1 = 2 ∧ b.1 = 3) by omega) with
        ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rw [hg_lt4 a 0 ha, hg_lt4 b 1 hb]
        dsimp [spiderLeft4]
        refine iff_of_true ⟨f_L.injective.ne (fun h => ?_),
          hf_L.nonadj_of_wit_nonadj _ _ (fun h => ?_) (Or.inl hp1_not_S) ?_⟩
          (by simp [spiderAdjLt, ha, hb])
        · have hv : d - 1 = d - 2 := spiderLongPathVal_inj hd (Subtype.ext_iff.mp (Sum.inl.inj h)); omega
        · have hv : d - 1 = d - 2 := spiderLongPathVal_inj hd (Subtype.ext_iff.mp (Sum.inl.inj h)); omega
        · unfold spiderLeftArm
          rw [compl_adj]; push_neg; intro _
          exact (spiderLongPath_adj_iff hd ⟨d - 1, by omega⟩ ⟨d - 2, by omega⟩).mpr (by show (d - 1) + 1 = d - 2 ∨ (d - 2) + 1 = d - 1; omega)
      · rw [hg_lt4 a 0 ha, hg_lt4 b 2 hb]
        dsimp [spiderLeft4]
        refine iff_of_true ⟨f_L.injective.ne (fun h => ?_),
          hf_L.nonadj_of_wit_nonadj _ _ (fun h => ?_) (Or.inl hp1_not_S) ?_⟩
          (by simp [spiderAdjLt, ha, hb])
        · have hv : d - 1 = d := spiderLongPathVal_inj hd (Subtype.ext_iff.mp (Sum.inl.inj h)); omega
        · have hv : d - 1 = d := spiderLongPathVal_inj hd (Subtype.ext_iff.mp (Sum.inl.inj h)); omega
        · unfold spiderLeftArm
          rw [compl_adj]; push_neg; intro _
          exact (spiderLongPath_adj_iff hd ⟨d - 1, by omega⟩ ⟨d, by omega⟩).mpr (by show (d - 1) + 1 = d ∨ d + 1 = d - 1; omega)
      · rw [hg_lt4 a 0 ha, hg_lt4 b 3 hb]
        dsimp [spiderLeft4]
        refine iff_of_false (fun hgc => hgc.2 (hf_L.adj_of_wit_adj _ _ ?_))
          (by simp [spiderAdjLt, ha, hb])
        unfold spiderLeftArm
        rw [compl_adj]
        refine ⟨Sum.inl_ne_inr, ?_⟩
        dsimp [substGraph, spiderLeftP1, spiderLeftP3]
        have h_eq : Fin.last ((d - 1) + 3) = spiderLongPath d ⟨d + 1, by omega⟩ :=
          Fin.ext (by
            show (d - 1) + 3 = spiderLongPathVal (d + 1)
            dsimp only [spiderLongPathVal]
            rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
            omega)
        rw [h_eq]
        intro h_s
        have h_con : (d - 1) + 1 = d + 1 ∨ (d + 1) + 1 = d - 1 :=
          (spiderLongPath_adj_iff hd ⟨d - 1, by omega⟩ ⟨d + 1, by omega⟩).mp h_s
        omega
      · rw [hg_lt4 a 1 ha, hg_lt4 b 2 hb]
        dsimp [spiderLeft4]
        refine iff_of_false (fun hgc => hgc.2 (hf_L.adj_of_wit_adj _ _ ?_))
          (by simp [spiderAdjLt, ha, hb])
        unfold spiderLeftArm
        rw [compl_adj]
        refine ⟨fun h => by
          have hv : d - 2 = d := spiderLongPathVal_inj hd (Subtype.ext_iff.mp (Sum.inl.inj h))
          omega, ?_⟩
        dsimp [substGraph, spiderLeftP0, spiderLeftP2]
        intro h_s
        have h_con : (d - 2) + 1 = d ∨ d + 1 = d - 2 :=
          (spiderLongPath_adj_iff hd ⟨d - 2, by omega⟩ ⟨d, by omega⟩).mp h_s
        omega
      · rw [hg_lt4 a 1 ha, hg_lt4 b 3 hb]
        dsimp [spiderLeft4]
        refine iff_of_false (fun hgc => hgc.2 (hf_L.adj_of_wit_adj _ _ ?_))
          (by simp [spiderAdjLt, ha, hb])
        unfold spiderLeftArm
        rw [compl_adj]
        refine ⟨Sum.inl_ne_inr, ?_⟩
        dsimp [substGraph, spiderLeftP0, spiderLeftP3]
        have h_eq : Fin.last ((d - 1) + 3) = spiderLongPath d ⟨d + 1, by omega⟩ :=
          Fin.ext (by
            show (d - 1) + 3 = spiderLongPathVal (d + 1)
            dsimp only [spiderLongPathVal]
            rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
            omega)
        rw [h_eq]
        intro h_s
        have h_con : (d - 2) + 1 = d + 1 ∨ (d + 1) + 1 = d - 2 :=
          (spiderLongPath_adj_iff hd ⟨d - 2, by omega⟩ ⟨d + 1, by omega⟩).mp h_s
        omega
      · rw [hg_lt4 a 2 ha, hg_lt4 b 3 hb]
        dsimp [spiderLeft4]
        exact iff_of_true ⟨f_L.injective.ne Sum.inl_ne_inr, hg_L⟩
          (by simp [spiderAdjLt, ha, hb])
    · by_cases hb4 : b.1 = 4
      · have hgb : g_bridge b = v₀ := by
          dsimp [g_bridge, g_bridge_opt]; rw [dif_neg (by omega), dif_pos hb4]; rfl
        rw [hgb]
        by_cases ha0 : a.1 = 0
        · rw [hg_lt4 a 0 ha0]
          dsimp [spiderLeft4]
          exact iff_of_true ⟨hf_L.ne_ext _, fun h => hf_L.nonadj_ext_nonspec _ hp1_not_S h.symm⟩
            (by simp [spiderAdjLt, ha0, hb4])
        · rcases (show a.1 = 1 ∨ a.1 = 2 ∨ a.1 = 3 by omega) with ha | ha | ha
          · rw [hg_lt4 a 1 ha]
            dsimp [spiderLeft4]
            refine iff_of_false (fun hgc => hgc.2 (hf_L.adj_ext_spec _ ?_).symm)
              (by simp [spiderAdjLt, ha, hb4])
            simp [specSpiderLeftArm]
          · rw [hg_lt4 a 2 ha]
            dsimp [spiderLeft4]
            refine iff_of_false (fun hgc => hgc.2 (hf_L.adj_ext_spec _ ?_).symm)
              (by simp [spiderAdjLt, ha, hb4])
            simp [specSpiderLeftArm]
          · rw [hg_lt4 a 3 ha]
            dsimp [spiderLeft4]
            refine iff_of_false (fun hgc => hgc.2 (hf_L.adj_ext_spec _ ?_).symm)
              (by simp [spiderAdjLt, ha, hb4])
            simp [specSpiderLeftArm]
      · have hgb : g_bridge b = f (Sum.inr (z ⟨d + 3 - b.1, by omega⟩)) := by
          dsimp [g_bridge, g_bridge_opt]
          rw [dif_neg (by omega), dif_neg hb4]; rfl
        rw [hgb]
        by_cases ha3 : a.1 ≤ 3
        · have h_sp_false : spiderAdjLt a.1 b.1 = false := by
            unfold spiderAdjLt
            simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, beq_eq_false_iff_ne,
              decide_eq_false_iff_not]
            omega
          rw [h_sp_false]
          have hga : g_bridge a = f (Sum.inl (spiderLeft4 hd ⟨a.1, by omega⟩)) := by
            dsimp [g_bridge, g_bridge_opt]
            rw [dif_pos (by omega)]; rfl
          rw [hga]
          exact iff_of_false (fun hgc => hgc.2 (hf.adj_of_wit_adj _ _ trivial)) (by decide)
        · by_cases ha4 : a.1 = 4
          · have hga : g_bridge a = v₀ := by
              dsimp [g_bridge, g_bridge_opt]; rw [dif_neg (by omega), dif_pos ha4]; rfl
            rw [hga]
            by_cases hb5 : b.1 = 5
            · have hz_eq : (⟨d + 3 - b.1, by omega⟩ : Fin (d - 1)) = ⟨d - 2, by omega⟩ :=
                Fin.ext (by show d + 3 - b.1 = d - 2; omega)
              rw [hz_eq]
              exact iff_of_true ⟨(hf_R.ne_ext _).symm, hf_R.nonadj_ext_nonspec _ hz_nonspec⟩
                (by simp [spiderAdjLt, ha4, hb5])
            · have h_sp_false : spiderAdjLt a.1 b.1 = false := by
                unfold spiderAdjLt
                simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, beq_eq_false_iff_ne,
                  decide_eq_false_iff_not]
                omega
              rw [h_sp_false]
              refine iff_of_false (fun hgc => hgc.2 (hf_R.adj_ext_spec _ ?_)) (by decide)
              exact hz_spec ⟨d + 3 - b.1, by omega⟩
          · have hga : g_bridge a = f (Sum.inr (z ⟨d + 3 - a.1, by omega⟩)) := by
              dsimp [g_bridge, g_bridge_opt]
              rw [dif_neg (by omega), dif_neg ha4]; rfl
            rw [hga, hz_adj ⟨d + 3 - a.1, by omega⟩ ⟨d + 3 - b.1, by omega⟩]
            have h_sp : spiderAdjLt a.1 b.1 = true ↔ b.1 = a.1 + 1 := by
              unfold spiderAdjLt
              simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
              omega
            rw [h_sp, pathGraph_adj]
            show ((d + 3 - a.1) + 1 = d + 3 - b.1 ∨ (d + 3 - b.1) + 1 = d + 3 - a.1) ↔
              b.1 = a.1 + 1
            omega
  intro a b
  show Gᶜ.Adj (g_bridge a) (g_bridge b) ↔ (SpiderGraph d).Adj a b
  by_cases hab : a = b
  · subst hab; simp
  · rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with hlt | hgt
    · rw [h_lt a b hlt]
      dsimp [SpiderGraph]
      rw [if_pos hlt]
    · rw [adj_comm, h_lt b a hgt]
      dsimp [SpiderGraph]
      rw [if_neg (by omega), if_pos hgt]

/-- Helper (`g_L = 0`): left-arm embedding for `SpiderGraph d` ($d \ge 2$). -/
private theorem spiderLeft_embed {V : Type*} {d : ℕ} (hd : 2 ≤ d)
    {G : SimpleGraph V} {v₀ : V} {f_L : SpiderLeftVert d ↪ V}
    (hf_L : IsOpenIntervalRealization (spiderLeftArm d) (specSpiderLeftArm hd) G v₀ f_L)
    (hg_L : G.Adj (f_L (spiderLeftP2 hd)) (f_L (spiderLeftP3 d))) :
    Nonempty (SpiderGraph d ↪g Gᶜ) := by
  let emb_L : Fin (d + 4) → SpiderLeftVert d := fun k =>
    if hk : k.1 < d + 2 then
      Sum.inl ⟨⟨k.1, by omega⟩, fun h => by
        have hv : k.1 = (d - 1) + 3 := congr_arg Fin.val h; omega⟩
    else if k.1 = d + 2 then
      Sum.inr 1
    else
      Sum.inr 0
  have h_embL_inj : Function.Injective emb_L := by
    intro a b hab
    dsimp [emb_L] at hab
    by_cases ha1 : a.1 < d + 2
    · rw [dif_pos ha1] at hab
      by_cases hb1 : b.1 < d + 2
      · rw [dif_pos hb1] at hab
        exact Fin.ext (congr_arg (fun x => x.1.1) (Sum.inl.inj hab))
      · rw [dif_neg hb1] at hab
        split_ifs at hab
    · rw [dif_neg ha1] at hab
      by_cases hb1 : b.1 < d + 2
      · rw [dif_pos hb1] at hab
        split_ifs at hab
      · rw [dif_neg hb1] at hab
        by_cases ha2 : a.1 = d + 2
        · rw [if_pos ha2] at hab
          by_cases hb2 : b.1 = d + 2
          · exact Fin.ext (by omega)
          · rw [if_neg hb2] at hab; simp at hab
        · rw [if_neg ha2] at hab
          by_cases hb2 : b.1 = d + 2
          · rw [if_pos hb2] at hab; simp at hab
          · exact Fin.ext (by omega)
  have h_not_spec : ∀ k : Fin (d + 4),
      k.1 = d + 2 ∨ (k.1 < d + 2 ∧ k.1 ≠ (spiderLongPath d ⟨d - 2, by omega⟩).1 ∧
        k.1 ≠ (spiderLongPath d ⟨d, by omega⟩).1) →
      emb_L k ∉ specSpiderLeftArm hd := by
    intro k hk
    simp only [specSpiderLeftArm, Finset.mem_insert, Finset.mem_singleton, not_or]
    rcases hk with hk_eq | ⟨hlt, hne0, hne2⟩
    · dsimp [emb_L]
      rw [dif_neg (by omega), if_pos hk_eq]
      exact ⟨Sum.inr_ne_inl, Sum.inr_ne_inl, fun h => by
        have := congr_arg Fin.val (Sum.inr.inj h); simp at this⟩
    · dsimp [emb_L]
      rw [dif_pos hlt]
      exact ⟨fun h => hne0 (congr_arg (fun x => x.1.1) (Sum.inl.inj h)),
        fun h => hne2 (congr_arg (fun x => x.1.1) (Sum.inl.inj h)),
        Sum.inl_ne_inr⟩
  refine ⟨RelEmbedding.mk ⟨fun x => f_L (emb_L x), fun a b h => h_embL_inj (f_L.injective h)⟩ ?_⟩
  have h_lt : ∀ a b : Fin (d + 4), a.1 < b.1 →
      (Gᶜ.Adj (f_L (emb_L a)) (f_L (emb_L b)) ↔ spiderAdjLt a.1 b.1 = true) := by
    intro a b hlt
    by_cases hb_lt : b.1 < d + 2
    · have ha_lt : a.1 < d + 2 := by omega
      have h_same_sp : spiderAdjLt a.1 b.1 = true ↔
          (SpiderGraph (d - 1)).Adj ⟨a.1, by omega⟩ ⟨b.1, by omega⟩ := by
        dsimp [SpiderGraph]; rw [if_pos hlt]
      rw [h_same_sp]
      by_cases h_sp_adj : (SpiderGraph (d - 1)).Adj ⟨a.1, by omega⟩ ⟨b.1, by omega⟩
      · refine iff_of_true ⟨f_L.injective.ne (h_embL_inj.ne (Fin.ne_of_lt hlt)),
          hf_L.nonadj_of_wit_nonadj _ _ (h_embL_inj.ne (Fin.ne_of_lt hlt)) ?_ ?_⟩ h_sp_adj
        · have h_nonadj_p0_p2 : ¬(SpiderGraph (d - 1)).Adj
              (spiderLongPath d ⟨d - 2, by omega⟩) (spiderLongPath d ⟨d, by omega⟩) := by
            rw [spiderLongPath_adj_iff hd]; show ¬((d - 2) + 1 = d ∨ d + 1 = d - 2); omega
          by_cases ha_in : a.1 = (spiderLongPath d ⟨d - 2, by omega⟩).1 ∨
              a.1 = (spiderLongPath d ⟨d, by omega⟩).1
          · right
            refine h_not_spec b (Or.inr ⟨hb_lt, ?_, ?_⟩)
            · intro hb0
              rcases ha_in with ha0 | ha2
              · omega
              · apply h_nonadj_p0_p2
                have h_b_eq : (⟨b.1, by omega⟩ : Fin ((d - 1) + 4)) =
                    spiderLongPath d ⟨d - 2, by omega⟩ := Fin.ext hb0
                have h_a_eq : (⟨a.1, by omega⟩ : Fin ((d - 1) + 4)) =
                    spiderLongPath d ⟨d, by omega⟩ := Fin.ext ha2
                rwa [← h_b_eq, ← h_a_eq, adj_comm]
            · intro hb2
              rcases ha_in with ha0 | ha2
              · apply h_nonadj_p0_p2
                have h_a_eq : (⟨a.1, by omega⟩ : Fin ((d - 1) + 4)) =
                    spiderLongPath d ⟨d - 2, by omega⟩ := Fin.ext ha0
                have h_b_eq : (⟨b.1, by omega⟩ : Fin ((d - 1) + 4)) =
                    spiderLongPath d ⟨d, by omega⟩ := Fin.ext hb2
                rwa [← h_a_eq, ← h_b_eq]
              · omega
          · push_neg at ha_in
            exact Or.inl (h_not_spec a (Or.inr ⟨ha_lt, ha_in.1, ha_in.2⟩))
        · dsimp [emb_L]
          rw [dif_pos ha_lt, dif_pos hb_lt]
          unfold spiderLeftArm
          rw [compl_adj]
          exact fun h => h.2 h_sp_adj
      · refine iff_of_false (fun hgc => hgc.2 (hf_L.adj_of_wit_adj _ _ ?_)) h_sp_adj
        dsimp [emb_L]
        rw [dif_pos ha_lt, dif_pos hb_lt]
        unfold spiderLeftArm
        rw [compl_adj]
        exact ⟨fun h => Fin.ne_of_lt hlt (Fin.ext (congr_arg (fun x => x.1.1) (Sum.inl.inj h))), h_sp_adj⟩
    · by_cases hb_eq : b.1 = d + 2
      · have hb_ns : emb_L b ∉ specSpiderLeftArm hd := h_not_spec b (Or.inl hb_eq)
        have ha_lt : a.1 < d + 2 := by omega
        have h_adj_equiv : (SpiderGraph (d - 1)).Adj ⟨a.1, by omega⟩ (Fin.last ((d - 1) + 3)) ↔
            spiderAdjLt a.1 b.1 = true := by
          dsimp [SpiderGraph]
          rw [if_pos (by show a.1 < (d - 1) + 3; omega)]
          simp only [spiderAdjLt, hb_eq, Bool.or_eq_true, Bool.and_eq_true,
            beq_iff_eq, decide_eq_true_eq]
          omega
        by_cases h_sp : spiderAdjLt a.1 b.1 = true
        · refine iff_of_true ⟨f_L.injective.ne (h_embL_inj.ne (Fin.ne_of_lt hlt)),
            hf_L.nonadj_of_wit_nonadj _ _ (h_embL_inj.ne (Fin.ne_of_lt hlt)) (Or.inr hb_ns) ?_⟩ h_sp
          dsimp [emb_L]
          rw [dif_pos ha_lt, dif_neg (by omega), if_pos hb_eq]
          unfold spiderLeftArm
          rw [compl_adj]
          exact fun h => h.2 (h_adj_equiv.mpr h_sp)
        · refine iff_of_false (fun hgc => hgc.2 (hf_L.adj_of_wit_adj _ _ ?_)) h_sp
          dsimp [emb_L]
          rw [dif_pos ha_lt, dif_neg (by omega), if_pos hb_eq]
          unfold spiderLeftArm
          rw [compl_adj]
          exact ⟨Sum.inl_ne_inr, fun h => h_sp (h_adj_equiv.mp h)⟩
      · by_cases ha_eq : a.1 = d + 2
        · have ha_ns : emb_L a ∉ specSpiderLeftArm hd := h_not_spec a (Or.inl ha_eq)
          have h_sp_true : spiderAdjLt a.1 b.1 = true := by
            unfold spiderAdjLt
            simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
            omega
          refine iff_of_true ⟨f_L.injective.ne (h_embL_inj.ne (Fin.ne_of_lt hlt)),
            hf_L.nonadj_of_wit_nonadj _ _ (h_embL_inj.ne (Fin.ne_of_lt hlt)) (Or.inl ha_ns) ?_⟩ h_sp_true
          dsimp [emb_L]
          rw [dif_neg (by omega), if_pos ha_eq, dif_neg (by omega), if_neg (by omega)]
          unfold spiderLeftArm
          rw [compl_adj]
          dsimp [substGraph]
          exact fun h => h.2 (by simp)
        · have ha_lt : a.1 < d + 2 := by omega
          have h_sp_false : spiderAdjLt a.1 b.1 = false := by
            unfold spiderAdjLt
            simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, beq_eq_false_iff_ne,
              decide_eq_false_iff_not]
            omega
          rw [h_sp_false]
          by_cases h_u : (SpiderGraph (d - 1)).Adj ⟨a.1, by omega⟩ (Fin.last ((d - 1) + 3))
          · have ha_p2 : emb_L a = spiderLeftP2 hd := by
              dsimp [emb_L]
              rw [dif_pos ha_lt]
              have h_eq_lp : (⟨a.1, by omega⟩ : Fin ((d - 1) + 4)) =
                  spiderLongPath d ⟨d, by omega⟩ := by
                dsimp [SpiderGraph] at h_u
                rw [if_pos (by show a.1 < (d - 1) + 3; omega)] at h_u
                simp only [spiderAdjLt, Bool.or_eq_true, Bool.and_eq_true,
                  beq_iff_eq, decide_eq_true_eq] at h_u
                ext; show a.1 = spiderLongPathVal d
                dsimp only [spiderLongPathVal]; split_ifs <;> omega
              simp [spiderLeftP2, h_eq_lp]
            have hb_p3 : emb_L b = spiderLeftP3 d := by
              dsimp [emb_L]
              rw [dif_neg (by omega), if_neg (by omega)]
              rfl
            rw [ha_p2, hb_p3]
            exact iff_of_false (fun hgc => hgc.2 hg_L) (by decide)
          · refine iff_of_false (fun hgc => hgc.2 (hf_L.adj_of_wit_adj _ _ ?_)) (by decide)
            dsimp [emb_L]
            rw [dif_pos ha_lt, dif_neg (by omega), if_neg (by omega)]
            unfold spiderLeftArm
            rw [compl_adj]
            exact ⟨Sum.inl_ne_inr, h_u⟩
  intro a b
  show Gᶜ.Adj (f_L (emb_L a)) (f_L (emb_L b)) ↔ (SpiderGraph d).Adj a b
  by_cases hab : a = b
  · subst hab; simp
  · rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with hlt | hgt
    · rw [h_lt a b hlt]
      dsimp [SpiderGraph]; rw [if_pos hlt]
    · rw [adj_comm, h_lt b a hgt]
      dsimp [SpiderGraph]; rw [if_neg (by omega), if_pos hgt]

/-- **Proposition 7(3) & Proposition 8(2) (`spiderGraph_isThresholdedWonderful_of_prev`, `main.tex` lines 1323–1339 & 1506–1513)**:
For **every** integer $d \ge 2$, assuming either $d = 2$ or `HasErdosHajnalProp (SpiderGraph (d - 1))`,
`SpiderGraph d` ($S_{1,2,d}$) is Stage-2 thresholded wonderful (`IsThresholdedWonderful (SpiderGraph d)`). -/
theorem spiderGraph_isThresholdedWonderful_of_prev (d : ℕ) (hd : 2 ≤ d)
    (h_prev_or_two : d = 2 ∨ HasErdosHajnalProp (SpiderGraph (d - 1))) :
    IsThresholdedWonderful (SpiderGraph d) := by
  have h_prev : HasErdosHajnalProp (SpiderGraph (d - 1)) := by
    rcases h_prev_or_two with rfl | h
    · exact hasErdosHajnalProp_spiderGraph_1
    · exact h
  refine isThresholdedWonderful_of_openIntervalWitness (SpiderGraph d)
    (witnessWSpider d) (specWSpider hd) (hasErdosHajnalProp_witnessWSpider hd h_prev) ?_
  intro V _ _ G v₀ f hf hFree
  have h_emb : Nonempty (SpiderGraph d ↪g Gᶜ) := by
    let f_L := Function.Embedding.inl.trans f
    let f_R := Function.Embedding.inr.trans f
    have hf_L := twoArmRealizationLeft hf
    have hf_R := twoArmRealizationRight hf
    by_cases hg_L : ¬G.Adj (f_L (spiderLeftP2 hd)) (f_L (spiderLeftP3 d))
    · rcases eq_or_lt_of_le hd with rfl | hd_gt2
      · refine spiderBridge_embed (by decide : 2 ≤ 2) hf hg_L
          (fun _ => 0) (fun i j => by fin_cases i; fin_cases j; simp)
          (fun i => Fin.elim0 i) (by simp)
      · obtain ⟨m, rfl⟩ : ∃ m, d = m + 3 := ⟨d - 3, by omega⟩
        have h_tp := terminal_path_arm_dichotomy_witness
          (SpiderGraph (m + 2)) (tailPathEmb (m + 2))
          (tailPathEmb_spider_TP1 (m + 2)) (tailPathEmb_spider_TP2 (m + 2)) G
          m (by omega) f_R
          (fun x y hadj => hf_R.adj_of_wit_adj x y hadj)
          (fun x y hne hspec hnadj => hf_R.nonadj_of_wit_nonadj x y hne
            (hspec.imp
              (fun hx hmem => by
                have h1 := (mem_armSpecFinset_iff (tailPathEmb (m + 2)) m (by omega) x).mp hmem
                rw [hx] at h1; cases h1)
              (fun hy hmem => by
                have h1 := (mem_armSpecFinset_iff (tailPathEmb (m + 2)) m (by omega) y).mp hmem
                rw [hy] at h1; cases h1))
            hnadj)
        rcases h_tp with h_emb_ext | ⟨p, hp_adj, hp_spec, hp_nonspec⟩
        · obtain ⟨emb_ext⟩ := h_emb_ext
          exact ⟨(spiderExtIso (m + 2) (by omega)).symm.toRelEmbedding.trans emb_ext⟩
        · refine spiderBridge_embed hd hf hg_L p hp_adj
            (fun i => (mem_armSpecFinset_iff (tailPathEmb (m + 2)) m (by omega) _).mpr (hp_spec i))
            ?_
          intro hmem
          have h1 := (mem_armSpecFinset_iff (tailPathEmb (m + 2)) m (by omega) _).mp hmem
          have h_idx : (⟨m + 3 - 2, by omega⟩ : Fin (m + 2)) = Fin.last (m + 1) :=
            Fin.ext (by show m + 3 - 2 = m + 1; omega)
          rw [congr_arg p h_idx, hp_nonspec] at h1
          exact Bool.noConfusion h1
    · push_neg at hg_L
      exact spiderLeft_embed hd hf_L hg_L
  obtain ⟨emb⟩ := h_emb
  exact not_isInducedSubgraphFree_compl_of_emb_compl emb hFree

/-! ### Section 4: Proposition 7(4) & Proposition 8(3) — All Unicyclic Birds `BirdDGraph d` ($d \ge 1$) -/

/-- Canonical induced graph embedding $\mathrm{Bird}_{d_1} \hookrightarrow_g \mathrm{Bird}_{d_2}$ for $d_1 \le d_2$. -/
def birdDGraph_mono_embedding {d₁ d₂ : ℕ} (h : d₁ ≤ d₂) :
    BirdDGraph d₁ ↪g BirdDGraph d₂ where
  toEmbedding := Fin.castLEEmb (Nat.add_le_add_right h 4)
  map_rel_iff' := by
    simp [BirdDGraph, Fin.castLEEmb]

private theorem tailPathEmb_bird_TP1 (m : ℕ) :
    ∀ a b : Fin m, a.1 < b.1 →
      ((BirdDGraph m).Adj (tailPathEmb m a) (tailPathEmb m b) ↔ b.1 = a.1 + 1) := by
  intro a b hlt
  dsimp [BirdDGraph]
  rw [if_neg (by omega), if_pos (by omega)]
  simp only [birdDAdjLt, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  omega

private theorem tailPathEmb_bird_TP2 (m : ℕ) :
    ∀ z : Fin (m + 4), (∀ a : Fin m, z ≠ tailPathEmb m a) →
      ∀ a : Fin m, (BirdDGraph m).Adj z (tailPathEmb m a) → a.1 = m - 1 := by
  intro z hz a hadj
  have hz4 : z.1 < 4 := by
    by_contra hge
    exact hz ⟨m + 3 - z.1, by omega⟩ (Fin.ext (by simp; omega))
  dsimp [BirdDGraph] at hadj
  rw [if_pos (by omega)] at hadj
  simp only [birdDAdjLt, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hadj
  omega

/-- Isomorphism `terminalPathExtGraph (BirdDGraph m) (tailPathEmb m 0) ≃g BirdDGraph (m + 1)` for `1 ≤ m`. -/
def birdExtIso (m : ℕ) (hm : 1 ≤ m) :
    terminalPathExtGraph (BirdDGraph m) (tailPathEmb m ⟨0, by omega⟩) ≃g BirdDGraph (m + 1) where
  toFun
    | none => ⟨m + 4, by omega⟩
    | some x => ⟨x.1, by omega⟩
  invFun y :=
    if hy : y.1 < m + 4 then some ⟨y.1, hy⟩ else none
  left_inv
    | none => by simp
    | some x => by simp [x.2]
  right_inv y := by
    by_cases hy : y.1 < m + 4
    · simp [hy]
    · simp [hy]; ext; dsimp; omega
  map_rel_iff' := by
    rintro (_ | x) (_ | y)
    · simp [BirdDGraph]
    · have hlt : y.1 < m + 4 := y.2
      dsimp [BirdDGraph, terminalPathExtGraph]
      rw [if_neg (by omega), if_pos hlt]
      simp only [birdDAdjLt, tailPathEmb_val, Bool.or_eq_true, Bool.and_eq_true,
        beq_iff_eq, decide_eq_true_eq, Fin.ext_iff]
      omega
    · have hlt : x.1 < m + 4 := x.2
      dsimp [BirdDGraph, terminalPathExtGraph]
      rw [if_pos hlt]
      simp only [birdDAdjLt, tailPathEmb_val, Bool.or_eq_true, Bool.and_eq_true,
        beq_iff_eq, decide_eq_true_eq, Fin.ext_iff]
      omega
    · rfl

/-- 3-vertex cograph module $\overline{K_2}[1 \leftarrow \{0, 1\}_{K_2},\, 2 \leftarrow \{2\}_{K_1}]$ on `Fin 3`
(`0 = X_m ∈ S`, `1 = X_m' ∉ S`, `2 = X_m^* ∉ S`), isomorphic to `(pathGraph 3)ᶜ`. -/
def birdCographMod : SimpleGraph (Fin 3) where
  Adj u v := (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0)
  symm _ _ h := by tauto
  loopless u := by fin_cases u <;> simp

instance instDecidableRelBirdCographModAdj : DecidableRel birdCographMod.Adj :=
  fun u v => inferInstanceAs (Decidable ((u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0)))

private theorem hasErdosHajnalProp_birdCographMod : HasErdosHajnalProp birdCographMod := by
  let iso : (pathGraph 3)ᶜ ≃g birdCographMod :=
    { toFun := ![0, 2, 1]
      invFun := ![0, 2, 1]
      left_inv := fun i => by fin_cases i <;> rfl
      right_inv := fun i => by fin_cases i <;> rfl
      map_rel_iff' := by intro i j; fin_cases i <;> fin_cases j <;> decide }
  exact hasErdosHajnalProp_of_iso iso (main_theorem_A_paths_le_9 3 (by decide) (by decide)).2.1

/-- First 4 slot embedding `Fin 4 ↪ Fin (d + 3)` for $d \ge 2$. -/
def birdFirst4Emb {d : ℕ} (hd : 2 ≤ d) : Fin 4 ↪ Fin (d + 3) :=
  Fin.castLEEmb (by omega)

@[simp]
private theorem birdFirst4Emb_val {d : ℕ} (hd : 2 ≤ d) (m : Fin 4) :
    (birdFirst4Emb hd m).1 = m.1 := rfl

/-- Vertex type of $\operatorname{Arm}_{B,L}^{(d)}$ ($d \ge 2$). -/
abbrev BirdLeftVert {d : ℕ} (hd : 2 ≤ d) : Type :=
  MultiSubstVert (Fin (d + 3)) (birdFirst4Emb hd) (Fin 3)

/-- Left arm cograph-substituted co-path $\operatorname{Arm}_{B,L}^{(d)}$ ($d \ge 2$, Proposition 7(4) & Proposition 8(3)). -/
def birdLeftArm {d : ℕ} (hd : 2 ≤ d) : SimpleGraph (BirdLeftVert hd) :=
  multiSubstGraph (pathGraph (d + 3))ᶜ (birdFirst4Emb hd) birdCographMod

/-- 4-vertex special set $S_{B,L}^{(d)} := \{L_1, L_2, L_3, L_4\}$ (`Sum.inl (m, 0)` for `m : Fin 4`). -/
def specBirdLeftArm {d : ℕ} (hd : 2 ≤ d) : Finset (BirdLeftVert hd) :=
  Finset.univ.map ⟨fun m : Fin 4 => Sum.inl (m, 0), fun _ _ h => (Prod.mk.inj (Sum.inl.inj h)).1⟩

theorem hasErdosHajnalProp_birdLeftArm {d : ℕ} (hd : 2 ≤ d)
    (hP : HasErdosHajnalProp (pathGraph (d + 3))) :
    HasErdosHajnalProp (birdLeftArm hd) :=
  hasErdosHajnalProp_multiSubstGraph hP.compl hasErdosHajnalProp_birdCographMod (birdFirst4Emb hd)

/-- Decidable model graph on `Fin 13` capturing the exact induced subgraph of $G^c$ on the 12 vertices
in slots `0..3` (`3 * m + c` for `m : Fin 4`, `c : Fin 3`) plus vertex `L_tail 4` (`12` in slot `4`)
under Boolean state `(b₁, b₂, b₃)`. -/
def birdCore13Adj (b₁ b₂ b₃ : Bool) (u v : Fin 13) : Bool :=
  if u == v then false
  else
    let slot_u := u.1 / 3
    let sub_u := u.1 % 3
    let slot_v := v.1 / 3
    let sub_v := v.1 % 3
    if slot_u == slot_v then
      (sub_u == 2 || sub_v == 2)
    else if slot_u + 1 == slot_v || slot_v + 1 == slot_u then
      if (u.1 == 0 && v.1 == 3) || (u.1 == 3 && v.1 == 0) then b₁
      else if (u.1 == 3 && v.1 == 6) || (u.1 == 6 && v.1 == 3) then b₂
      else if (u.1 == 6 && v.1 == 9) || (u.1 == 9 && v.1 == 6) then b₃
      else true
    else false

private theorem hc13_same : ∀ (a₁ a₂ a₃ : Bool) (u v : Fin 13),
    u.1 < v.1 → v.1 < 12 → u.1 / 3 = v.1 / 3 →
    birdCore13Adj a₁ a₂ a₃ u v = decide (u.1 % 3 = 2 ∨ v.1 % 3 = 2) := by decide

private theorem hc13_consec_nonspec : ∀ (a₁ a₂ a₃ : Bool) (u v : Fin 13),
    u.1 < v.1 → v.1 < 12 → u.1 / 3 + 1 = v.1 / 3 → !(u.1 % 3 == 0 && v.1 % 3 == 0) = true →
    birdCore13Adj a₁ a₂ a₃ u v = true := by decide

private theorem hc13_far : ∀ (a₁ a₂ a₃ : Bool) (u v : Fin 13),
    u.1 < v.1 → v.1 < 12 → u.1 / 3 ≠ v.1 / 3 → u.1 / 3 + 1 ≠ v.1 / 3 →
    birdCore13Adj a₁ a₂ a₃ u v = false := by decide

private theorem hc13_12_adj : ∀ (a₁ a₂ a₃ : Bool) (u v : Fin 13),
    v.1 = 12 → u.1 / 3 = 3 → birdCore13Adj a₁ a₂ a₃ u v = true := by decide

private theorem hc13_12_nonadj : ∀ (a₁ a₂ a₃ : Bool) (u v : Fin 13),
    v.1 = 12 → u.1 < 12 → u.1 / 3 ≠ 3 → birdCore13Adj a₁ a₂ a₃ u v = false := by decide

private theorem hc13_refl : ∀ (a₁ a₂ a₃ : Bool) (u : Fin 13),
    birdCore13Adj a₁ a₂ a₃ u u = false := by decide

private theorem hc13_comm : ∀ (a₁ a₂ a₃ : Bool) (u v : Fin 13),
    birdCore13Adj a₁ a₂ a₃ u v = birdCore13Adj a₁ a₂ a₃ v u := by decide

/-- Explicit 6-vertex core map `Fin 6 → Fin 13` (`(y₀, y₁, y₂, y₃, z₁, z₂)`) for each of the 7 states
`(b₁, b₂, b₃) ≠ (true, true, true)` (`main.tex` lines 1343–1348). -/
def birdCore6Map (b₁ b₂ b₃ : Bool) : Fin 6 → Fin 13 :=
  if !b₁ then
    if !b₂ then ![0, 2, 3, 1, 7, 9]
    else if !b₃ then ![0, 2, 3, 1, 6, 10]
    else ![0, 2, 3, 1, 6, 9]
  else
    if !b₂ then
      if !b₃ then ![0, 4, 8, 6, 9, 12]
      else ![3, 5, 6, 4, 9, 12]
    else ![0, 3, 8, 6, 9, 12]

private theorem birdCore6Map_inj (b₁ b₂ b₃ : Bool) (hnot111 : ¬(b₁ = true ∧ b₂ = true ∧ b₃ = true)) :
    Function.Injective (birdCore6Map b₁ b₂ b₃) := by
  intro i j
  revert b₁ b₂ b₃ hnot111 i j
  decide

private theorem birdCore6Map_adj (b₁ b₂ b₃ : Bool) (hnot111 : ¬(b₁ = true ∧ b₂ = true ∧ b₃ = true))
    (i j : Fin 6) :
    birdCore13Adj b₁ b₂ b₃ (birdCore6Map b₁ b₂ b₃ i) (birdCore6Map b₁ b₂ b₃ j) =
      decide ((BirdDGraph 2).Adj i j) := by
  revert b₁ b₂ b₃ hnot111 i j
  decide

private theorem birdCore6Map_slot_bound : ∀ (a₁ a₂ a₃ : Bool),
    ¬(a₁ = true ∧ a₂ = true ∧ a₃ = true) →
    ∀ k : Fin 6,
      (k.1 ≤ 4 → (birdCore6Map a₁ a₂ a₃ k).1 / 3 ≤ 4 - (if a₁ then 1 else 2)) ∧
      (k.1 = 5 → (birdCore6Map a₁ a₂ a₃ k).1 / 3 = 5 - (if a₁ then 1 else 2)) := by decide

/-- Embedding `Fin 13` (`0..11` = `Fin 4 × Fin 3` via `(u / 3, u % 3)`, `12` = `Sum.inr ⟨4, _⟩`) into `BirdLeftVert hd`. -/
def birdCore13ToLeftVert {d : ℕ} (hd : 2 ≤ d) : Fin 13 ↪ BirdLeftVert hd where
  toFun u :=
    if hu : u.1 < 12 then
      Sum.inl (⟨u.1 / 3, by omega⟩, ⟨u.1 % 3, by omega⟩)
    else
      Sum.inr ⟨⟨4, by omega⟩, fun i h => by
        have hv : 4 = i.1 := congr_arg Fin.val h; omega⟩
  inj' u v h := by
    dsimp only at h
    by_cases hu : u.1 < 12
    · by_cases hv : v.1 < 12
      · rw [dif_pos hu, dif_pos hv] at h
        have h1 := Prod.mk.inj (Sum.inl.inj h)
        have hq : u.1 / 3 = v.1 / 3 := congr_arg Fin.val h1.1
        have hr : u.1 % 3 = v.1 % 3 := congr_arg Fin.val h1.2
        exact Fin.ext (by omega)
      · rw [dif_pos hu, dif_neg hv] at h
        exact False.elim (Sum.inl_ne_inr h)
    · by_cases hv : v.1 < 12
      · rw [dif_neg hu, dif_pos hv] at h
        exact False.elim (Sum.inr_ne_inl h)
      · exact Fin.ext (by omega)

/-- **Unified Left-Arm Bird Realization Lemma** (covers all 7 non-`(1,1,1)` Boolean states for ALL $d \ge 2$):
Whenever `(b₁, b₂, b₃) ≠ (true, true, true)`, `birdLeftArm hd` embeds `BirdDGraph d` directly into `Gᶜ`! -/
theorem birdLeftArm_embed {V : Type*} {d : ℕ} (hd : 2 ≤ d)
    {G : SimpleGraph V} {v₀ : V} {f : BirdLeftVert hd ↪ V}
    (hf : IsOpenIntervalRealization (birdLeftArm hd) (specBirdLeftArm hd) G v₀ f)
    (hnot111 : ¬(Gᶜ.Adj (f (Sum.inl (0, 0))) (f (Sum.inl (1, 0))) ∧
                 Gᶜ.Adj (f (Sum.inl (1, 0))) (f (Sum.inl (2, 0))) ∧
                 Gᶜ.Adj (f (Sum.inl (2, 0))) (f (Sum.inl (3, 0))))) :
    Nonempty (BirdDGraph d ↪g Gᶜ) := by
  classical
  let b₁ : Bool := decide (Gᶜ.Adj (f (Sum.inl (0, 0))) (f (Sum.inl (1, 0))))
  let b₂ : Bool := decide (Gᶜ.Adj (f (Sum.inl (1, 0))) (f (Sum.inl (2, 0))))
  let b₃ : Bool := decide (Gᶜ.Adj (f (Sum.inl (2, 0))) (f (Sum.inl (3, 0))))
  have hnot_bool : ¬(b₁ = true ∧ b₂ = true ∧ b₃ = true) := by
    simpa [b₁, b₂, b₃] using hnot111
  -- Exact agreement between `Gᶜ.Adj` on `f ∘ birdCore13ToLeftVert hd` and `birdCore13Adj b₁ b₂ b₃`
  have h_core13 : ∀ u v : Fin 13,
      Gᶜ.Adj (f (birdCore13ToLeftVert hd u)) (f (birdCore13ToLeftVert hd v)) ↔
        birdCore13Adj b₁ b₂ b₃ u v = true := by
    have h_symm_core : ∀ u v : Fin 13, u.1 < v.1 →
        (Gᶜ.Adj (f (birdCore13ToLeftVert hd u)) (f (birdCore13ToLeftVert hd v)) ↔
          birdCore13Adj b₁ b₂ b₃ u v = true) := by
      intro u v hlt
      have hne_uv : birdCore13ToLeftVert hd u ≠ birdCore13ToLeftVert hd v :=
        (birdCore13ToLeftVert hd).injective.ne (Fin.ne_of_lt hlt)
      by_cases hv12 : v.1 < 12
      · have hu12 : u.1 < 12 := by omega
        have h_u_eq : birdCore13ToLeftVert hd u = Sum.inl (⟨u.1 / 3, by omega⟩, ⟨u.1 % 3, by omega⟩) := by
          dsimp [birdCore13ToLeftVert]; rw [dif_pos hu12]
        have h_v_eq : birdCore13ToLeftVert hd v = Sum.inl (⟨v.1 / 3, by omega⟩, ⟨v.1 % 3, by omega⟩) := by
          dsimp [birdCore13ToLeftVert]; rw [dif_pos hv12]
        by_cases h_slot : u.1 / 3 = v.1 / 3
        · have hv_not_S : birdCore13ToLeftVert hd v ∉ specBirdLeftArm hd := by
            rw [h_v_eq]
            simp only [specBirdLeftArm, Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk,
              true_and, not_exists]
            intro m hm
            have hv_sub : (0 : ℕ) = v.1 % 3 := congr_arg Fin.val (Prod.mk.inj (Sum.inl.inj hm)).2
            omega
          rw [hc13_same b₁ b₂ b₃ u v hlt hv12 h_slot]
          by_cases hv2 : v.1 % 3 = 2
          · refine iff_of_true ⟨f.injective.ne hne_uv,
              hf.nonadj_of_wit_nonadj _ _ hne_uv (Or.inr hv_not_S) ?_⟩ (by simp [hv2])
            rw [h_u_eq, h_v_eq]
            dsimp only [birdLeftArm, multiSubstGraph]
            rw [if_pos (Fin.ext h_slot)]
            intro h_mod
            rcases h_mod with ⟨_, h1⟩ | ⟨_, h2_r⟩
            · have hv_sub : v.1 % 3 = 1 := congr_arg Fin.val h1
              omega
            · have hv_sub : v.1 % 3 = 0 := congr_arg Fin.val h2_r
              omega
          · have hv1_sub : u.1 % 3 = 0 ∧ v.1 % 3 = 1 := by omega
            refine iff_of_false (fun hgc => hgc.2 (hf.adj_of_wit_adj _ _ ?_)) (by simp; omega)
            rw [h_u_eq, h_v_eq]
            dsimp only [birdLeftArm, multiSubstGraph]
            rw [if_pos (Fin.ext h_slot)]
            left
            exact ⟨Fin.ext hv1_sub.1, Fin.ext hv1_sub.2⟩
        · by_cases h_consec : u.1 / 3 + 1 = v.1 / 3
          · by_cases h_both0 : u.1 % 3 = 0 ∧ v.1 % 3 = 0
            · rcases (show (u.1 = 0 ∧ v.1 = 3) ∨ (u.1 = 3 ∧ v.1 = 6) ∨ (u.1 = 6 ∧ v.1 = 9) by omega) with
                ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩
              · have hu_eq : u = 0 := Fin.ext hu
                have hv_eq : v = 3 := Fin.ext hv
                subst hu_eq hv_eq
                have h0 : birdCore13ToLeftVert hd 0 = Sum.inl (0, 0) := rfl
                have h3 : birdCore13ToLeftVert hd 3 = Sum.inl (1, 0) := rfl
                have hc : birdCore13Adj b₁ b₂ b₃ 0 3 = b₁ := rfl
                rw [h0, h3, hc]
                exact decide_eq_true_iff.symm
              · have hu_eq : u = 3 := Fin.ext hu
                have hv_eq : v = 6 := Fin.ext hv
                subst hu_eq hv_eq
                have h3 : birdCore13ToLeftVert hd 3 = Sum.inl (1, 0) := rfl
                have h6 : birdCore13ToLeftVert hd 6 = Sum.inl (2, 0) := rfl
                have hc : birdCore13Adj b₁ b₂ b₃ 3 6 = b₂ := rfl
                rw [h3, h6, hc]
                exact decide_eq_true_iff.symm
              · have hu_eq : u = 6 := Fin.ext hu
                have hv_eq : v = 9 := Fin.ext hv
                subst hu_eq hv_eq
                have h6 : birdCore13ToLeftVert hd 6 = Sum.inl (2, 0) := rfl
                have h9 : birdCore13ToLeftVert hd 9 = Sum.inl (3, 0) := rfl
                have hc : birdCore13Adj b₁ b₂ b₃ 6 9 = b₃ := rfl
                rw [h6, h9, hc]
                exact decide_eq_true_iff.symm
            · rw [hc13_consec_nonspec b₁ b₂ b₃ u v hlt hv12 h_consec (by simp; tauto)]
              refine iff_of_true ⟨f.injective.ne hne_uv, hf.nonadj_of_wit_nonadj _ _ hne_uv ?_ ?_⟩ rfl
              · by_cases hu0 : u.1 % 3 = 0
                · right
                  rw [h_v_eq]
                  simp only [specBirdLeftArm, Finset.mem_map, Finset.mem_univ,
                    Function.Embedding.coeFn_mk, true_and, not_exists]
                  intro m hm
                  have hv_sub : (0 : ℕ) = v.1 % 3 := congr_arg Fin.val (Prod.mk.inj (Sum.inl.inj hm)).2
                  omega
                · left
                  rw [h_u_eq]
                  simp only [specBirdLeftArm, Finset.mem_map, Finset.mem_univ,
                    Function.Embedding.coeFn_mk, true_and, not_exists]
                  intro m hm
                  have hu_sub : (0 : ℕ) = u.1 % 3 := congr_arg Fin.val (Prod.mk.inj (Sum.inl.inj hm)).2
                  omega
              · rw [h_u_eq, h_v_eq]
                dsimp only [birdLeftArm, multiSubstGraph]
                rw [if_neg (fun h => h_slot (congr_arg Fin.val h))]
                simp only [compl_adj, pathGraph_adj, birdFirst4Emb_val, not_and, not_not]
                intro _; left; exact h_consec
          · rw [hc13_far b₁ b₂ b₃ u v hlt hv12 h_slot h_consec]
            refine iff_of_false (fun hgc => hgc.2 (hf.adj_of_wit_adj _ _ ?_)) (by decide)
            rw [h_u_eq, h_v_eq]
            dsimp only [birdLeftArm, multiSubstGraph]
            rw [if_neg (fun h => h_slot (congr_arg Fin.val h))]
            simp only [compl_adj, pathGraph_adj, birdFirst4Emb_val]
            exact ⟨fun h => h_slot (congr_arg Fin.val h), by omega⟩
      · have hv12_eq : v.1 = 12 := by omega
        have hu12 : u.1 < 12 := by omega
        have hv_not_S : birdCore13ToLeftVert hd v ∉ specBirdLeftArm hd := by
          dsimp [birdCore13ToLeftVert, specBirdLeftArm]
          rw [dif_neg (by omega)]
          simp
        by_cases hu_slot3 : u.1 / 3 = 3
        · rw [hc13_12_adj b₁ b₂ b₃ u v hv12_eq hu_slot3]
          refine iff_of_true ⟨f.injective.ne hne_uv,
            hf.nonadj_of_wit_nonadj _ _ hne_uv (Or.inr hv_not_S) ?_⟩ rfl
          dsimp [birdCore13ToLeftVert, birdLeftArm, multiSubstGraph, multiSubstProj]
          rw [dif_pos hu12, dif_neg (by omega)]
          simp only [compl_adj, pathGraph_adj, birdFirst4Emb_val, not_and, not_not]
          intro _; left; dsimp; omega
        · rw [hc13_12_nonadj b₁ b₂ b₃ u v hv12_eq hu12 hu_slot3]
          refine iff_of_false (fun hgc => hgc.2 (hf.adj_of_wit_adj _ _ ?_)) (by decide)
          dsimp [birdCore13ToLeftVert, birdLeftArm, multiSubstGraph, multiSubstProj]
          rw [dif_pos hu12, dif_neg (by omega)]
          refine ⟨fun h => ?_, ?_⟩
          · have hv_eq : u.1 / 3 = 4 := congr_arg Fin.val h
            omega
          · simp only [pathGraph_adj, birdFirst4Emb_val]
            dsimp; omega
    intro u v
    by_cases huv : u = v
    · subst huv
      rw [hc13_refl b₁ b₂ b₃ u]; simp
    · rcases lt_or_gt_of_ne (Fin.val_ne_of_ne huv) with hlt | hgt
      · exact h_symm_core u v hlt
      · rw [adj_comm, h_symm_core v u hgt, hc13_comm b₁ b₂ b₃ u v]
  -- Now extend `birdCore6Map b₁ b₂ b₃` (`0..5`) to all `k : Fin (d + 4)` by appending tail vertices!
  let shift : ℕ := if b₁ then 1 else 2
  let embLeft : Fin (d + 4) → BirdLeftVert hd := fun k =>
    if hk : k.1 < 6 then
      birdCore13ToLeftVert hd (birdCore6Map b₁ b₂ b₃ ⟨k.1, hk⟩)
    else
      Sum.inr ⟨⟨k.1 - shift, by dsimp [shift]; split_ifs <;> omega⟩,
        fun i h => by
          have hv : k.1 - shift = i.1 := congr_arg Fin.val h
          dsimp [shift] at hv
          split_ifs at hv <;> omega⟩
  have h_slot_lt6 : ∀ k : Fin 6,
      (multiSubstProj (birdFirst4Emb hd) (birdCore13ToLeftVert hd (birdCore6Map b₁ b₂ b₃ k))).1 =
        (birdCore6Map b₁ b₂ b₃ k).1 / 3 := by
    intro k
    set u := birdCore6Map b₁ b₂ b₃ k
    dsimp [birdCore13ToLeftVert]
    split_ifs with hu
    · simp [multiSubstProj]
    · have hu12 : u.1 = 12 := by omega
      simp [multiSubstProj, hu12]
  have h_slot_bound := birdCore6Map_slot_bound b₁ b₂ b₃ hnot_bool
  have h_embLeft_inj : Function.Injective embLeft := by
    intro a b hab
    by_cases ha : a.1 < 6
    · by_cases hb : b.1 < 6
      · dsimp [embLeft] at hab
        rw [dif_pos ha, dif_pos hb] at hab
        have h_eq6 := birdCore6Map_inj b₁ b₂ b₃ hnot_bool
          ((birdCore13ToLeftVert hd).injective hab)
        exact Fin.ext (by have := congr_arg Fin.val h_eq6; simpa using this)
      · have ha_eq : embLeft a = birdCore13ToLeftVert hd (birdCore6Map b₁ b₂ b₃ ⟨a.1, ha⟩) := by
          dsimp [embLeft]; rw [dif_pos ha]
        have hb_eq : (multiSubstProj (birdFirst4Emb hd) (embLeft b)).1 = b.1 - shift := by
          dsimp [embLeft, multiSubstProj]; rw [dif_neg hb]
        have hproj : (multiSubstProj (birdFirst4Emb hd) (embLeft a)).1 =
            (multiSubstProj (birdFirst4Emb hd) (embLeft b)).1 :=
          congr_arg (fun z => (multiSubstProj (birdFirst4Emb hd) z).1) hab
        rw [ha_eq, h_slot_lt6 ⟨a.1, ha⟩, hb_eq] at hproj
        have h1 := h_slot_bound ⟨a.1, ha⟩
        dsimp [shift] at hproj h1
        split_ifs at hproj h1 <;> omega
    · by_cases hb : b.1 < 6
      · have ha_eq : (multiSubstProj (birdFirst4Emb hd) (embLeft a)).1 = a.1 - shift := by
          dsimp [embLeft, multiSubstProj]; rw [dif_neg ha]
        have hb_eq : embLeft b = birdCore13ToLeftVert hd (birdCore6Map b₁ b₂ b₃ ⟨b.1, hb⟩) := by
          dsimp [embLeft]; rw [dif_pos hb]
        have hproj : (multiSubstProj (birdFirst4Emb hd) (embLeft a)).1 =
            (multiSubstProj (birdFirst4Emb hd) (embLeft b)).1 :=
          congr_arg (fun z => (multiSubstProj (birdFirst4Emb hd) z).1) hab
        rw [ha_eq, hb_eq, h_slot_lt6 ⟨b.1, hb⟩] at hproj
        have h1 := h_slot_bound ⟨b.1, hb⟩
        dsimp [shift] at hproj h1
        split_ifs at hproj h1 <;> omega
      · have ha_eq : (multiSubstProj (birdFirst4Emb hd) (embLeft a)).1 = a.1 - shift := by
          dsimp [embLeft, multiSubstProj]; rw [dif_neg ha]
        have hb_eq : (multiSubstProj (birdFirst4Emb hd) (embLeft b)).1 = b.1 - shift := by
          dsimp [embLeft, multiSubstProj]; rw [dif_neg hb]
        have hv : a.1 - shift = b.1 - shift := by
          rw [← ha_eq, ← hb_eq]
          exact congr_arg (fun z => (multiSubstProj (birdFirst4Emb hd) z).1) hab
        dsimp [shift] at hv
        split_ifs at hv <;> exact Fin.ext (by omega)
  refine ⟨RelEmbedding.mk ⟨fun k => f (embLeft k), fun a b h => h_embLeft_inj (f.injective h)⟩ ?_⟩
  have h_lt : ∀ a b : Fin (d + 4), a.1 < b.1 →
      (Gᶜ.Adj (f (embLeft a)) (f (embLeft b)) ↔ birdDAdjLt a.1 b.1 = true) := by
    intro a b hlt
    by_cases hb6 : b.1 < 6
    · have ha6 : a.1 < 6 := by omega
      have h_c6 := birdCore6Map_adj b₁ b₂ b₃ hnot_bool ⟨a.1, ha6⟩ ⟨b.1, hb6⟩
      simp only [BirdDGraph, if_pos hlt] at h_c6
      dsimp [embLeft]
      rw [dif_pos ha6, dif_pos hb6, h_core13, h_c6]
      exact decide_eq_true_iff
    · have hb_not_S : embLeft b ∉ specBirdLeftArm hd := by
        dsimp [embLeft, specBirdLeftArm]
        rw [dif_neg hb6]
        simp
      have h_b_proj : (multiSubstProj (birdFirst4Emb hd) (embLeft b)).1 = b.1 - shift := by
        dsimp [embLeft, multiSubstProj]
        rw [dif_neg hb6]
      have h_b_adj_iff : ∀ x : BirdLeftVert hd,
          (multiSubstProj (birdFirst4Emb hd) x).1 < (multiSubstProj (birdFirst4Emb hd) (embLeft b)).1 →
          (Gᶜ.Adj (f x) (f (embLeft b)) ↔
            (multiSubstProj (birdFirst4Emb hd) (embLeft b)).1 =
              (multiSubstProj (birdFirst4Emb hd) x).1 + 1) := by
        intro x hx_lt
        have hne_xb : x ≠ embLeft b := fun h => by rw [h] at hx_lt; exact lt_irrefl _ hx_lt
        by_cases h_consec : (multiSubstProj (birdFirst4Emb hd) (embLeft b)).1 =
            (multiSubstProj (birdFirst4Emb hd) x).1 + 1
        · refine iff_of_true ⟨f.injective.ne hne_xb,
            hf.nonadj_of_wit_nonadj _ _ hne_xb (Or.inr hb_not_S) ?_⟩ h_consec
          dsimp [embLeft, birdLeftArm, multiSubstGraph] at *
          rw [dif_neg hb6] at *
          cases x with
          | inl mu =>
            simp only [compl_adj, pathGraph_adj, not_and, not_not]
            intro _; left; exact h_consec.symm
          | inr w =>
            simp only [compl_adj, pathGraph_adj, not_and, not_not]
            intro _; left; exact h_consec.symm
        · refine iff_of_false (fun hgc => hgc.2 (hf.adj_of_wit_adj _ _ ?_)) h_consec
          dsimp [embLeft, birdLeftArm, multiSubstGraph] at *
          rw [dif_neg hb6] at *
          cases x with
          | inl mu =>
            simp only [compl_adj, pathGraph_adj, Fin.ext_iff] at *
            omega
          | inr w =>
            simp only [compl_adj, pathGraph_adj, Fin.ext_iff] at *
            omega
      by_cases ha6 : a.1 < 6
      · have h_a_proj := h_slot_lt6 ⟨a.1, ha6⟩
        have h_bound := h_slot_bound ⟨a.1, ha6⟩
        dsimp only [embLeft]
        rw [dif_pos ha6]
        have hx_lt : (multiSubstProj (birdFirst4Emb hd)
            (birdCore13ToLeftVert hd (birdCore6Map b₁ b₂ b₃ ⟨a.1, ha6⟩))).1 <
            (multiSubstProj (birdFirst4Emb hd) (embLeft b)).1 := by
          rw [h_a_proj, h_b_proj]
          dsimp [shift] at h_bound ⊢
          split_ifs at h_bound ⊢ <;> omega
        rw [h_b_adj_iff _ hx_lt, h_a_proj, h_b_proj]
        by_cases ha5 : a.1 = 5
        · have hs5 := h_bound.2 ha5
          have h_bd : birdDAdjLt a.1 b.1 = true ↔ b.1 = 6 := by
            unfold birdDAdjLt
            simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
            omega
          rw [h_bd]
          dsimp [shift] at hs5 ⊢
          split_ifs at hs5 ⊢ <;> omega
        · have hs4 := h_bound.1 (by dsimp; omega)
          have h_bd : birdDAdjLt a.1 b.1 = false := by
            unfold birdDAdjLt
            simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, beq_eq_false_iff_ne,
              decide_eq_false_iff_not]
            omega
          rw [h_bd]
          dsimp [shift] at hs4 ⊢
          refine iff_of_false (fun h_bad => ?_) (by decide)
          split_ifs at hs4 h_bad <;> omega
      · have h_a_proj : (multiSubstProj (birdFirst4Emb hd) (embLeft a)).1 = a.1 - shift := by
          dsimp [embLeft, multiSubstProj]
          rw [dif_neg ha6]
        have hx_lt : (multiSubstProj (birdFirst4Emb hd) (embLeft a)).1 <
            (multiSubstProj (birdFirst4Emb hd) (embLeft b)).1 := by
          rw [h_a_proj, h_b_proj]
          dsimp [shift]; split_ifs <;> omega
        rw [h_b_adj_iff _ hx_lt, h_a_proj, h_b_proj]
        have h_bd : birdDAdjLt a.1 b.1 = true ↔ b.1 = a.1 + 1 := by
          unfold birdDAdjLt
          simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
          omega
        rw [h_bd]
        dsimp [shift]; split_ifs <;> omega
  intro a b
  show Gᶜ.Adj (f (embLeft a)) (f (embLeft b)) ↔ (BirdDGraph d).Adj a b
  by_cases hab : a = b
  · subst hab; simp
  · rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with hlt | hgt
    · rw [h_lt a b hlt]; dsimp [BirdDGraph]; rw [if_pos hlt]
    · rw [adj_comm, h_lt b a hgt]; dsimp [BirdDGraph]; rw [if_neg (by omega), if_pos hgt]

/-- Shared `(1, 1, 1)` cross-arm bridge embedding `(f_L L₁, f_L L₂, f_L L₃*, f_L L₃, v₀, z_{d-2}, ..., z₀)`
for ANY $d \ge 2$! -/
private theorem birdBridge_embed {V U_R : Type*} [DecidableEq U_R] {d : ℕ} (hd : 2 ≤ d)
    {W_R : SimpleGraph U_R} {S_R : Finset U_R}
    {G : SimpleGraph V} {v₀ : V}
    {f : BirdLeftVert hd ⊕ U_R ↪ V}
    (hf : IsOpenIntervalRealization (twoArmJoinGraph (birdLeftArm hd) W_R)
      (twoArmSpecFinset (specBirdLeftArm hd) S_R) G v₀ f)
    (h111 : Gᶜ.Adj (f (Sum.inl (Sum.inl (0, 0)))) (f (Sum.inl (Sum.inl (1, 0)))) ∧
            Gᶜ.Adj (f (Sum.inl (Sum.inl (1, 0)))) (f (Sum.inl (Sum.inl (2, 0)))) ∧
            Gᶜ.Adj (f (Sum.inl (Sum.inl (2, 0)))) (f (Sum.inl (Sum.inl (3, 0)))))
    (z : Fin (d - 1) → U_R)
    (hz_adj : ∀ i j : Fin (d - 1),
      Gᶜ.Adj (f (Sum.inr (z i))) (f (Sum.inr (z j))) ↔ (pathGraph (d - 1)).Adj i j)
    (hz_spec : ∀ i : Fin (d - 2), z ⟨i.1, by omega⟩ ∈ S_R)
    (hz_nonspec : z ⟨d - 2, by omega⟩ ∉ S_R) :
    Nonempty (BirdDGraph d ↪g Gᶜ) := by
  let f_L := Function.Embedding.inl.trans f
  let f_R := Function.Embedding.inr.trans f
  have hf_L := twoArmRealizationLeft hf
  have hf_R := twoArmRealizationRight hf
  have hz_inj : Function.Injective z :=
    pathSpec_inj (g := fun u => f (Sum.inr u)) (P := (· ∈ S_R))
      hz_adj (fun i hi => hz_spec ⟨i.1, by omega⟩)
      (fun i hi => by
        have hi_eq : i = ⟨d - 2, by omega⟩ := Fin.ext (by show i.1 = d - 2; omega)
        rw [hi_eq]; exact hz_nonspec)
  have hL3star_not_S : (Sum.inl (2, 2) : BirdLeftVert hd) ∉ specBirdLeftArm hd := by
    simp only [specBirdLeftArm, Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk,
      true_and, not_exists]
    intro m hm
    have hv : (0 : ℕ) = 2 := congr_arg Fin.val (Prod.mk.inj (Sum.inl.inj hm)).2
    omega
  let g_br_opt : Fin (d + 4) → Option (BirdLeftVert hd ⊕ U_R) := fun k =>
    if hk5 : k.1 < 5 then
      if k.1 = 0 then some (Sum.inl (Sum.inl (0, 0)))
      else if k.1 = 1 then some (Sum.inl (Sum.inl (1, 0)))
      else if k.1 = 2 then some (Sum.inl (Sum.inl (2, 2)))
      else if k.1 = 3 then some (Sum.inl (Sum.inl (2, 0)))
      else none
    else
      some (Sum.inr (z ⟨d + 3 - k.1, by omega⟩))
  let g_br : Fin (d + 4) → V := fun k => Option.elim (g_br_opt k) v₀ f
  have hg_inj : Function.Injective g_br := by
    intro a b hab
    have h_opt_eq : g_br_opt a = g_br_opt b := by
      dsimp [g_br] at hab
      cases ha_o : g_br_opt a with
      | none =>
        cases hb_o : g_br_opt b with
        | none => rfl
        | some w =>
          rw [ha_o, hb_o] at hab
          exact False.elim (hf.ne_ext w hab.symm)
      | some u =>
        cases hb_o : g_br_opt b with
        | none =>
          rw [ha_o, hb_o] at hab
          exact False.elim (hf.ne_ext u hab)
        | some w =>
          rw [ha_o, hb_o] at hab
          exact congr_arg some (f.injective hab)
    by_cases ha5 : a.1 < 5
    · by_cases hb5 : b.1 < 5
      · dsimp [g_br_opt] at h_opt_eq
        rw [dif_pos ha5, dif_pos hb5] at h_opt_eq
        rcases (show a.1 = 0 ∨ a.1 = 1 ∨ a.1 = 2 ∨ a.1 = 3 ∨ a.1 = 4 by omega) with
            ha | ha | ha | ha | ha <;>
          rcases (show b.1 = 0 ∨ b.1 = 1 ∨ b.1 = 2 ∨ b.1 = 3 ∨ b.1 = 4 by omega) with
            hb | hb | hb | hb | hb
        all_goals try exact Fin.ext (by omega)
        all_goals simp [ha, hb] at h_opt_eq
      · dsimp [g_br_opt] at h_opt_eq
        rw [dif_pos ha5, dif_neg hb5] at h_opt_eq
        rcases (show a.1 = 0 ∨ a.1 = 1 ∨ a.1 = 2 ∨ a.1 = 3 ∨ a.1 = 4 by omega) with
          ha | ha | ha | ha | ha <;> simp [ha] at h_opt_eq
    · by_cases hb5 : b.1 < 5
      · dsimp [g_br_opt] at h_opt_eq
        rw [dif_neg ha5, dif_pos hb5] at h_opt_eq
        rcases (show b.1 = 0 ∨ b.1 = 1 ∨ b.1 = 2 ∨ b.1 = 3 ∨ b.1 = 4 by omega) with
          hb | hb | hb | hb | hb <;> simp [hb] at h_opt_eq
      · dsimp [g_br_opt] at h_opt_eq
        rw [dif_neg ha5, dif_neg hb5] at h_opt_eq
        have hz_eq : d + 3 - a.1 = d + 3 - b.1 :=
          congr_arg Fin.val (hz_inj (Sum.inr.inj (Option.some.inj h_opt_eq)))
        exact Fin.ext (by omega)
  refine ⟨RelEmbedding.mk ⟨g_br, hg_inj⟩ ?_⟩
  have h_lt : ∀ a b : Fin (d + 4), a.1 < b.1 →
      (Gᶜ.Adj (g_br a) (g_br b) ↔ birdDAdjLt a.1 b.1 = true) := by
    intro a b hlt
    by_cases hb3 : b.1 ≤ 3
    · rcases (show (a.1 = 0 ∧ b.1 = 1) ∨ (a.1 = 0 ∧ b.1 = 2) ∨ (a.1 = 0 ∧ b.1 = 3) ∨
          (a.1 = 1 ∧ b.1 = 2) ∨ (a.1 = 1 ∧ b.1 = 3) ∨ (a.1 = 2 ∧ b.1 = 3) by omega) with
        ⟨ha, hv⟩ | ⟨ha, hv⟩ | ⟨ha, hv⟩ | ⟨ha, hv⟩ | ⟨ha, hv⟩ | ⟨ha, hv⟩
      · have hga : g_br a = f_L (Sum.inl (0, 0)) := by
          dsimp [g_br, g_br_opt, f_L]; rw [dif_pos (by omega)]; simp [ha]
        have hgb : g_br b = f_L (Sum.inl (1, 0)) := by
          dsimp [g_br, g_br_opt, f_L]; rw [dif_pos (by omega)]; simp [hv]
        rw [hga, hgb]
        exact iff_of_true h111.1 (by simp [birdDAdjLt, ha, hv])
      · have hga : g_br a = f_L (Sum.inl (0, 0)) := by
          dsimp [g_br, g_br_opt, f_L]; rw [dif_pos (by omega)]; simp [ha]
        have hgb : g_br b = f_L (Sum.inl (2, 2)) := by
          dsimp [g_br, g_br_opt, f_L]; rw [dif_pos (by omega)]; simp [hv]
        rw [hga, hgb]
        refine iff_of_false (fun hgc => hgc.2 (hf_L.adj_of_wit_adj _ _ ?_))
          (by simp [birdDAdjLt, ha, hv])
        simp [birdLeftArm, multiSubstGraph, birdFirst4Emb, pathGraph_adj]
      · have hga : g_br a = f_L (Sum.inl (0, 0)) := by
          dsimp [g_br, g_br_opt, f_L]; rw [dif_pos (by omega)]; simp [ha]
        have hgb : g_br b = f_L (Sum.inl (2, 0)) := by
          dsimp [g_br, g_br_opt, f_L]; rw [dif_pos (by omega)]; simp [hv]
        rw [hga, hgb]
        refine iff_of_false (fun hgc => hgc.2 (hf_L.adj_of_wit_adj _ _ ?_))
          (by simp [birdDAdjLt, ha, hv])
        simp [birdLeftArm, multiSubstGraph, birdFirst4Emb, pathGraph_adj]
      · have hga : g_br a = f_L (Sum.inl (1, 0)) := by
          dsimp [g_br, g_br_opt, f_L]; rw [dif_pos (by omega)]; simp [ha]
        have hgb : g_br b = f_L (Sum.inl (2, 2)) := by
          dsimp [g_br, g_br_opt, f_L]; rw [dif_pos (by omega)]; simp [hv]
        rw [hga, hgb]
        refine iff_of_true ⟨f_L.injective.ne (by simp),
          hf_L.nonadj_of_wit_nonadj _ _ (by simp) (Or.inr hL3star_not_S) ?_⟩
          (by simp [birdDAdjLt, ha, hv])
        simp [birdLeftArm, multiSubstGraph, birdFirst4Emb, compl_adj, pathGraph_adj]
      · have hga : g_br a = f_L (Sum.inl (1, 0)) := by
          dsimp [g_br, g_br_opt, f_L]; rw [dif_pos (by omega)]; simp [ha]
        have hgb : g_br b = f_L (Sum.inl (2, 0)) := by
          dsimp [g_br, g_br_opt, f_L]; rw [dif_pos (by omega)]; simp [hv]
        rw [hga, hgb]
        exact iff_of_true h111.2.1 (by simp [birdDAdjLt, ha, hv])
      · have hga : g_br a = f_L (Sum.inl (2, 2)) := by
          dsimp [g_br, g_br_opt, f_L]; rw [dif_pos (by omega)]; simp [ha]
        have hgb : g_br b = f_L (Sum.inl (2, 0)) := by
          dsimp [g_br, g_br_opt, f_L]; rw [dif_pos (by omega)]; simp [hv]
        rw [hga, hgb]
        refine iff_of_true ⟨f_L.injective.ne (by simp),
          hf_L.nonadj_of_wit_nonadj _ _ (by simp) (Or.inl hL3star_not_S) ?_⟩
          (by simp [birdDAdjLt, ha, hv])
        dsimp only [birdLeftArm, multiSubstGraph]
        rw [if_pos rfl]; decide
    · by_cases hb4 : b.1 = 4
      · have hgb : g_br b = v₀ := by
          dsimp [g_br, g_br_opt]; rw [dif_pos (by omega)]; simp [hb4]
        rw [hgb]
        by_cases ha2 : a.1 = 2
        · have hga : g_br a = f_L (Sum.inl (2, 2)) := by
            dsimp [g_br, g_br_opt, f_L]; rw [dif_pos (by omega)]; simp [ha2]
          rw [hga]
          exact iff_of_true ⟨(hf_L.ne_ext _), fun h => hf_L.nonadj_ext_nonspec _ hL3star_not_S h.symm⟩
            (by simp [birdDAdjLt, ha2, hb4])
        · rcases (show a.1 = 0 ∨ a.1 = 1 ∨ a.1 = 3 by omega) with ha | ha | ha
          · have hga : g_br a = f_L (Sum.inl (0, 0)) := by
              dsimp [g_br, g_br_opt, f_L]; rw [dif_pos (by omega)]; simp [ha]
            rw [hga]
            refine iff_of_false (fun hgc => hgc.2 (hf_L.adj_ext_spec _ ?_).symm)
              (by simp [birdDAdjLt, ha, hb4])
            exact Finset.mem_map.mpr ⟨0, Finset.mem_univ _, rfl⟩
          · have hga : g_br a = f_L (Sum.inl (1, 0)) := by
              dsimp [g_br, g_br_opt, f_L]; rw [dif_pos (by omega)]; simp [ha]
            rw [hga]
            refine iff_of_false (fun hgc => hgc.2 (hf_L.adj_ext_spec _ ?_).symm)
              (by simp [birdDAdjLt, ha, hb4])
            exact Finset.mem_map.mpr ⟨1, Finset.mem_univ _, rfl⟩
          · have hga : g_br a = f_L (Sum.inl (2, 0)) := by
              dsimp [g_br, g_br_opt, f_L]; rw [dif_pos (by omega)]; simp [ha]
            rw [hga]
            refine iff_of_false (fun hgc => hgc.2 (hf_L.adj_ext_spec _ ?_).symm)
              (by simp [birdDAdjLt, ha, hb4])
            exact Finset.mem_map.mpr ⟨2, Finset.mem_univ _, rfl⟩
      · have hgb : g_br b = f (Sum.inr (z ⟨d + 3 - b.1, by omega⟩)) := by
          dsimp [g_br, g_br_opt]; rw [dif_neg (by omega)]; rfl
        rw [hgb]
        by_cases ha3 : a.1 ≤ 3
        · have h_bd : birdDAdjLt a.1 b.1 = false := by
            unfold birdDAdjLt
            simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, beq_eq_false_iff_ne,
              decide_eq_false_iff_not]
            omega
          rw [h_bd]
          dsimp [g_br, g_br_opt]
          rw [dif_pos (by omega)]
          rcases (show a.1 = 0 ∨ a.1 = 1 ∨ a.1 = 2 ∨ a.1 = 3 by omega) with ha | ha | ha | ha <;>
            simp only [ha, ↓reduceIte, Option.elim_some] <;>
            exact iff_of_false (fun hgc => hgc.2 (hf.adj_of_wit_adj _ _ trivial)) (by decide)
        · by_cases ha4 : a.1 = 4
          · have hga : g_br a = v₀ := by
              dsimp [g_br, g_br_opt]; rw [dif_pos (by omega)]; simp [ha4]
            rw [hga]
            by_cases hb5 : b.1 = 5
            · have hz_eq : (⟨d + 3 - b.1, by omega⟩ : Fin (d - 1)) = ⟨d - 2, by omega⟩ :=
                Fin.ext (by show d + 3 - b.1 = d - 2; omega)
              rw [hz_eq]
              exact iff_of_true ⟨(hf_R.ne_ext _).symm, hf_R.nonadj_ext_nonspec _ hz_nonspec⟩
                (by simp [birdDAdjLt, ha4, hb5])
            · have h_bd : birdDAdjLt a.1 b.1 = false := by
                unfold birdDAdjLt
                simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, beq_eq_false_iff_ne,
                  decide_eq_false_iff_not]
                omega
              rw [h_bd]
              refine iff_of_false (fun hgc => hgc.2 (hf_R.adj_ext_spec _ ?_)) (by decide)
              exact hz_spec ⟨d + 3 - b.1, by omega⟩
          · have hga : g_br a = f (Sum.inr (z ⟨d + 3 - a.1, by omega⟩)) := by
              dsimp [g_br, g_br_opt]; rw [dif_neg (by omega)]; rfl
            rw [hga, hz_adj ⟨d + 3 - a.1, by omega⟩ ⟨d + 3 - b.1, by omega⟩]
            have h_bd : birdDAdjLt a.1 b.1 = true ↔ b.1 = a.1 + 1 := by
              unfold birdDAdjLt
              simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
              omega
            rw [h_bd, pathGraph_adj]
            show ((d + 3 - a.1) + 1 = d + 3 - b.1 ∨ (d + 3 - b.1) + 1 = d + 3 - a.1) ↔
              b.1 = a.1 + 1
            omega
  intro a b
  show Gᶜ.Adj (g_br a) (g_br b) ↔ (BirdDGraph d).Adj a b
  by_cases hab : a = b
  · subst hab; simp
  · rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with hlt | hgt
    · rw [h_lt a b hlt]; dsimp [BirdDGraph]; rw [if_pos hlt]
    · rw [adj_comm, h_lt b a hgt]; dsimp [BirdDGraph]; rw [if_neg (by omega), if_pos hgt]

/-- **Proposition 7(4) (`witnessWBird6`, `main.tex` lines 1280–1292 & 1341–1352)**:
Symmetric two-arm pure-substitution witness $W_{\mathrm{Bird}}^{(6)} := K_2[0 \leftarrow \operatorname{Arm}_{B,L}^{(6)}, 1 \leftarrow \operatorname{Arm}_{B,L}^{(6)}]$. -/
def witnessWBird6 : SimpleGraph (BirdLeftVert (by decide : 2 ≤ 6) ⊕ BirdLeftVert (by decide : 2 ≤ 6)) :=
  twoArmJoinGraph (birdLeftArm (by decide : 2 ≤ 6)) (birdLeftArm (by decide : 2 ≤ 6))

def specWBird6 : Finset (BirdLeftVert (by decide : 2 ≤ 6) ⊕ BirdLeftVert (by decide : 2 ≤ 6)) :=
  twoArmSpecFinset (specBirdLeftArm (by decide : 2 ≤ 6)) (specBirdLeftArm (by decide : 2 ≤ 6))

theorem hasErdosHajnalProp_witnessWBird6 : HasErdosHajnalProp witnessWBird6 := by
  have hP9 : HasErdosHajnalProp (pathGraph 9) :=
    (main_theorem_A_paths_le_9 9 (by decide) (by decide)).1
  have hArm := hasErdosHajnalProp_birdLeftArm (by decide : 2 ≤ 6) hP9
  exact hasErdosHajnalProp_twoArmJoinGraph hArm hArm

/-- **Proposition 7(4) & Proposition 7(3b) (`birdDGraph_isThresholdedWonderful_le_6`)**:
Every unicyclic bird `BirdDGraph d` with $1 \le d \le 6$ (simultaneously covering
$\mathrm{Bull} = \mathrm{Bird}_1$ and $\mathrm{Bird}_2, \dots, \mathrm{Bird}_6$ via
$\mathrm{Bird}_d \hookrightarrow_g \mathrm{Bird}_6$) is **unconditionally Stage-2 thresholded wonderful**! -/
theorem birdDGraph_isThresholdedWonderful_le_6 (d : ℕ) (_hd1 : 1 ≤ d) (hd6 : d ≤ 6) :
    IsThresholdedWonderful (BirdDGraph d) := by
  refine isThresholdedWonderful_of_openIntervalWitness (BirdDGraph d)
    witnessWBird6 specWBird6 hasErdosHajnalProp_witnessWBird6 ?_
  intro V _ _ G v₀ f hf hFree
  have h_emb6 : Nonempty (BirdDGraph 6 ↪g Gᶜ) := by
    let f_L := Function.Embedding.inl.trans f
    let f_R := Function.Embedding.inr.trans f
    have hf_L := twoArmRealizationLeft hf
    have hf_R := twoArmRealizationRight hf
    by_cases hL : Gᶜ.Adj (f_L (Sum.inl (0, 0))) (f_L (Sum.inl (1, 0))) ∧
                  Gᶜ.Adj (f_L (Sum.inl (1, 0))) (f_L (Sum.inl (2, 0))) ∧
                  Gᶜ.Adj (f_L (Sum.inl (2, 0))) (f_L (Sum.inl (3, 0)))
    · by_cases hR : Gᶜ.Adj (f_R (Sum.inl (0, 0))) (f_R (Sum.inl (1, 0))) ∧
                    Gᶜ.Adj (f_R (Sum.inl (1, 0))) (f_R (Sum.inl (2, 0))) ∧
                    Gᶜ.Adj (f_R (Sum.inl (2, 0))) (f_R (Sum.inl (3, 0)))
      · let zR : Fin 5 → BirdLeftVert (by decide : 2 ≤ 6)
          | 0 => Sum.inl (0, 0)
          | 1 => Sum.inl (1, 0)
          | 2 => Sum.inl (2, 0)
          | 3 => Sum.inl (3, 0)
          | 4 => Sum.inr ⟨4, fun i h => by
              have hv : 4 = i.1 := congr_arg Fin.val h; omega⟩
        refine birdBridge_embed (by decide : 2 ≤ 6) hf hL zR ?_ ?_ ?_
        · have hz_lt : ∀ i j : Fin 5, i.1 < j.1 →
              (Gᶜ.Adj (f_R (zR i)) (f_R (zR j)) ↔ j.1 = i.1 + 1) := by
            intro i j hlt
            fin_cases i <;> fin_cases j
            all_goals dsimp at hlt ⊢
            all_goals try omega
            · exact iff_of_true hR.1 rfl
            · refine iff_of_false (fun hgc => hgc.2 (hf_R.adj_of_wit_adj _ _ ?_)) (by decide)
              simp [zR, birdLeftArm, multiSubstGraph, birdFirst4Emb, pathGraph_adj]
            · refine iff_of_false (fun hgc => hgc.2 (hf_R.adj_of_wit_adj _ _ ?_)) (by decide)
              simp [zR, birdLeftArm, multiSubstGraph, birdFirst4Emb, pathGraph_adj]
            · refine iff_of_false (fun hgc => hgc.2 (hf_R.adj_of_wit_adj _ _ ?_)) (by decide)
              simp [zR, birdLeftArm, multiSubstGraph, multiSubstProj, birdFirst4Emb, pathGraph_adj]
            · exact iff_of_true hR.2.1 rfl
            · refine iff_of_false (fun hgc => hgc.2 (hf_R.adj_of_wit_adj _ _ ?_)) (by decide)
              simp [zR, birdLeftArm, multiSubstGraph, birdFirst4Emb, pathGraph_adj]
            · refine iff_of_false (fun hgc => hgc.2 (hf_R.adj_of_wit_adj _ _ ?_)) (by decide)
              simp [zR, birdLeftArm, multiSubstGraph, multiSubstProj, birdFirst4Emb, pathGraph_adj]
            · exact iff_of_true hR.2.2 rfl
            · refine iff_of_false (fun hgc => hgc.2 (hf_R.adj_of_wit_adj _ _ ?_)) (by decide)
              simp [zR, birdLeftArm, multiSubstGraph, multiSubstProj, birdFirst4Emb, pathGraph_adj]
            · refine iff_of_true ⟨f_R.injective.ne (by simp [zR]),
                hf_R.nonadj_of_wit_nonadj _ _ (by simp [zR])
                  (Or.inr (by simp [zR, specBirdLeftArm])) ?_⟩ rfl
              simp [zR, birdLeftArm, multiSubstGraph, multiSubstProj, birdFirst4Emb,
                compl_adj, pathGraph_adj]
          intro i j
          show Gᶜ.Adj (f_R (zR i)) (f_R (zR j)) ↔ (pathGraph (6 - 1)).Adj i j
          by_cases hij : i = j
          · subst hij; simp
          · rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hgt
            · rw [hz_lt i j hlt]; simp [pathGraph_adj]; omega
            · rw [adj_comm, hz_lt j i hgt]; simp [pathGraph_adj]; omega
        · intro i
          fin_cases i <;> exact Finset.mem_map.mpr ⟨_, Finset.mem_univ _, rfl⟩
        · simp [zR, specBirdLeftArm]
      · exact birdLeftArm_embed (by decide : 2 ≤ 6) hf_R hR
    · exact birdLeftArm_embed (by decide : 2 ≤ 6) hf_L hL
  obtain ⟨emb6⟩ := h_emb6
  exact not_isInducedSubgraphFree_compl_of_emb_compl ((birdDGraph_mono_embedding hd6).trans emb6) hFree

/-- Unconditional Stage-2 thresholded wonderfulness of `BullGraph` (`BirdDGraph 1`). -/
theorem isThresholdedWonderful_bullGraph : IsThresholdedWonderful BullGraph :=
  birdDGraph_isThresholdedWonderful_le_6 1 le_rfl (by decide)

/-- Two-arm pure-substitution witness $W_{B,d} := K_2[0 \leftarrow \operatorname{Arm}_{B,L}^{(d)}, 1 \leftarrow \operatorname{Arm}_{d-2}(\overline{\mathrm{Bird}_{d-1}})]$
for every integer $d \ge 6$ (Proposition 8(3) of `main.tex`). -/
def witnessWBirdGe6 (d : ℕ) (hd : 6 ≤ d) :
    SimpleGraph (BirdLeftVert (by omega : 2 ≤ d) ⊕
      ArmVert (Fin ((d - 1) + 4)) (tailPathEmb (d - 1)) (d - 3) (by omega)) :=
  twoArmJoinGraph (birdLeftArm (by omega : 2 ≤ d))
    (armGraph (BirdDGraph (d - 1))ᶜ (tailPathEmb (d - 1)) (d - 3) (by omega))

noncomputable def specWBirdGe6 (d : ℕ) (hd : 6 ≤ d) :
    Finset (BirdLeftVert (by omega : 2 ≤ d) ⊕
      ArmVert (Fin ((d - 1) + 4)) (tailPathEmb (d - 1)) (d - 3) (by omega)) :=
  twoArmSpecFinset (specBirdLeftArm (by omega : 2 ≤ d))
    (armSpecFinset (tailPathEmb (d - 1)) (d - 3) (by omega))

theorem hasErdosHajnalProp_witnessWBirdGe6 (d : ℕ) (hd : 6 ≤ d)
    (hP : HasErdosHajnalProp (pathGraph (d + 3)))
    (hB : HasErdosHajnalProp (BirdDGraph (d - 1))) :
    HasErdosHajnalProp (witnessWBirdGe6 d hd) :=
  hasErdosHajnalProp_twoArmJoinGraph
    (hasErdosHajnalProp_birdLeftArm (by omega) hP)
    (hasErdosHajnalProp_armGraph hB.compl (tailPathEmb (d - 1)) (d - 3) (by omega))

/-- **Proposition 8(3) (`birdDGraph_isThresholdedWonderful_ge_6`, `main.tex` lines 1514–1521 & 1566–1570)**:
For **every** integer $d \ge 6$, assuming `HasErdosHajnalProp (pathGraph (d + 3))` and
`HasErdosHajnalProp (BirdDGraph (d - 1))`, `BirdDGraph d` is Stage-2 thresholded wonderful! -/
theorem birdDGraph_isThresholdedWonderful_ge_6 (d : ℕ) (hd : 6 ≤ d)
    (hP : HasErdosHajnalProp (pathGraph (d + 3)))
    (hB : HasErdosHajnalProp (BirdDGraph (d - 1))) :
    IsThresholdedWonderful (BirdDGraph d) := by
  refine isThresholdedWonderful_of_openIntervalWitness (BirdDGraph d)
    (witnessWBirdGe6 d hd) (specWBirdGe6 d hd)
    (hasErdosHajnalProp_witnessWBirdGe6 d hd hP hB) ?_
  intro V _ _ G v₀ f hf hFree
  have h_emb : Nonempty (BirdDGraph d ↪g Gᶜ) := by
    let f_L := Function.Embedding.inl.trans f
    let f_R := Function.Embedding.inr.trans f
    have hf_L := twoArmRealizationLeft hf
    have hf_R := twoArmRealizationRight hf
    by_cases hL : Gᶜ.Adj (f_L (Sum.inl (0, 0))) (f_L (Sum.inl (1, 0))) ∧
                  Gᶜ.Adj (f_L (Sum.inl (1, 0))) (f_L (Sum.inl (2, 0))) ∧
                  Gᶜ.Adj (f_L (Sum.inl (2, 0))) (f_L (Sum.inl (3, 0)))
    · have h_tp := terminal_path_arm_dichotomy_witness
        (BirdDGraph (d - 1)) (tailPathEmb (d - 1))
        (tailPathEmb_bird_TP1 (d - 1)) (tailPathEmb_bird_TP2 (d - 1)) G
        (d - 3) (by omega) f_R
        (fun x y hadj => hf_R.adj_of_wit_adj x y hadj)
        (fun x y hne hspec hnadj => hf_R.nonadj_of_wit_nonadj x y hne
          (hspec.imp
            (fun hx hmem => by rw [mem_armSpecFinset_iff, hx] at hmem; cases hmem)
            (fun hy hmem => by rw [mem_armSpecFinset_iff, hy] at hmem; cases hmem))
          hnadj)
      rcases h_tp with h_nonempty_ext | ⟨p, hp_adj, hp_spec, hp_nonspec⟩
      · obtain ⟨emb_ext⟩ := h_nonempty_ext
        have hd_eq : (d - 1) + 1 = d := by omega
        have emb_mid : BirdDGraph ((d - 1) + 1) ↪g Gᶜ :=
          (birdExtIso (d - 1) (by omega)).symm.toRelEmbedding.trans emb_ext
        rw [hd_eq] at emb_mid
        exact ⟨emb_mid⟩
      · refine birdBridge_embed (by omega : 2 ≤ d) hf hL
          (fun i => p ⟨i.1, by omega⟩)
          (fun i j => by
            have := hp_adj ⟨i.1, by omega⟩ ⟨j.1, by omega⟩
            simpa [pathGraph_adj] using this)
          (fun i => by rw [mem_armSpecFinset_iff]; exact hp_spec ⟨i.1, by omega⟩)
          (fun hmem => by
            rw [mem_armSpecFinset_iff] at hmem
            dsimp only at hmem
            have h_last : (⟨d - 2, by omega⟩ : Fin ((d - 3) + 2)) = Fin.last (d - 3 + 1) :=
              Fin.ext (by show d - 2 = (d - 3) + 1; omega)
            rw [congr_arg p h_last, hp_nonspec] at hmem
            exact Bool.noConfusion hmem)
    · exact birdLeftArm_embed (by omega : 2 ≤ d) hf_L hL
  obtain ⟨emb⟩ := h_emb
  exact not_isInducedSubgraphFree_compl_of_emb_compl emb hFree

/-! ### Section 5: Axiom Verification -/

#print axioms terminal_path_arm_dichotomy_witness
#print axioms spiderGraph_isThresholdedWonderful_of_prev
#print axioms isThresholdedWonderful_bullGraph
#print axioms birdDGraph_isThresholdedWonderful_le_6
#print axioms birdDGraph_isThresholdedWonderful_ge_6

end ErdosHajnalGen
