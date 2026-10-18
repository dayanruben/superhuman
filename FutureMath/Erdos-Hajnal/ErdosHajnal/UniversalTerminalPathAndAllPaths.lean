/-
Copyright 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosHajnal.AllPathsDefs
import ErdosHajnal.BasicLemmas
import ErdosHajnal.Defs
import ErdosHajnal.GenDefs
import ErdosHajnal.P6Baseline
import ErdosHajnal.P9BaselineProof
import ErdosHajnal.RecursiveGallaiAndStage1
import ErdosHajnal.Stage2Witnesses
import ErdosHajnal.SymmetricStage12Interface
import ErdosHajnal.ViralityAndClosures

/-!
# Universal Terminal-Path Recursive Pure-Substitution Witnesses, Unified Pendant-$P_3$
Open-Interval Lifting, and Unconditional Erdős–Hajnal Property for All Paths $P_k$,
Linear Forests, Brooms, Double Brooms, and Hooked-Claw Pairs (`main.tex`, Part VI)

This file formalizes `Lemma 14`, `Proposition 8(1)`, `Theorem 7(1)`, and `Theorem 9(1)` of `main.tex`:

1. **Section 1 — Leaf Extensions `PlusLeafGraph`, Complete Joins `joinGraph`, and Substitution Helpers**:
   - `PlusLeafGraph G₀ w₁`: $G_0^+ := G_0 + (w_0 - w_1)$ on `Option W₀`.
   - `joinGraph H₁ H₂`: $K_2[1 \leftarrow H_1, 2 \leftarrow H_2]$ on `U₁ ⊕ U₂`, its isomorphism to nested
     `substGraph` over `⊤ : SimpleGraph (Fin 2)`, and restriction of `IsOpenIntervalRealization`.

2. **Section 2 — Universal Terminal-Path Recursive Pure-Substitution Arm (`Lemma 14(1)`)**:
   - `TermArmVert`, `TermArmGraph`, and `TermArmSpec`: Recursive pure-substitution arm
     $(\operatorname{Arm}_r(B_0), S_r(B_0)) \in \mathcal{J}(\{B_0, \overline{K_2}\})$.
   - `hasErdosHajnalProp_termArmGraph`: Proof via partial substitution stages that
     `HasErdosHajnalProp B₀ → HasErdosHajnalProp (TermArmGraph B₀ w_path r)` for all $r \ge 1$.
   - `terminal_path_arm_dichotomy`: Full general proof of **Lemma 14(1)** establishing that under
     `(E-Non)` and `(E-Edge)`, $\overline{G}[\{f(u)\}]$ contains either an induced `PlusLeafGraph G₀ w₁`
     (`Arm-i`) or an induced $(r + 1)$-vertex path with first $r$ vertices in `TermArmSpec` and last
     vertex outside `TermArmSpec` (`Arm-ii`).

3. **Section 3 — Unified Two-Polarity Pendant-$P_3$ Open-Interval Lifting (`Lemma 14(2)`)**:
   - `pendant_p3_open_interval_lifting`: Tuple-specific Markov degree pruning across $(h - 1)$-tuples
     of distinct blocks proving that for every $H_* = G_0 + (y - w_2 - x_2)$ of order $h \ge 4$:
     - **(a)** $J[I_{\mathrm{open}}(v_0)]$ is $(H_* - x_2)ᶜ$-free; and
     - **(b)** $J[I_{\mathrm{high}}^{\mathrm{open}}(v_0)]$ is $K_2[1 \leftarrow K_1, 2 \leftarrow \overline{G_0}]$-free.

4. **Section 4 — Proposition 8(1): Zero-Defect Thresholded Wonderfulness of All Paths $P_k$ ($k \ge 6$)**:
   - `isThresholdedWonderful_Pk_of_prev`: Certifies `IsThresholdedWonderful (pathGraph k)` for every
     $k \ge 6$ assuming `HasErdosHajnalProp (pathGraph (k - 1))` using the two-arm pure-substitution
     witness $H_{\mathrm{TP}}^{(k)} = K_2[1 \leftarrow \operatorname{Arm}_{r_L}(\overline{P_{k-1}}), 2 \leftarrow \operatorname{Arm}_{r_R}(\overline{P_{k-1}})]$.

5. **Section 5 — Theorem 9(1): Unconditional Erdős–Hajnal, Polynomial Rödl, and Virality for All
   Paths $P_k$ ($k \ge 1$), Linear Forests, Brooms, Double Brooms, Hooked-Claw Pairs, and Forest Pairs**:
   - `hasErdosHajnalProp_all_paths`, `erdos_hajnal_all_paths_proof`, `erdos_61_variants_all_paths_proof`
   - `isThresholdedWonderful_Pk`, `main_theorem_B_paths_all_k`
   - `main_theorem_A2_linear_forests_and_brooms_proof`
   - `pair_Pt_Hook4_eh_all_t` and `opposite_chirality_forest_pairs_eh`.
-/

set_option linter.unusedSectionVars false

open Filter Finset SimpleGraph Real ErdosHajnalP6

namespace ErdosHajnalGen

universe u

/-! ### Section 1: Leaf Extensions `PlusLeafGraph`, Complete Joins `joinGraph`, and Helpers -/

/-- Hereditary monotonicity of `HasErdosHajnalProp` along an induced graph embedding $H_1 \hookrightarrow_g H_2$. -/
theorem hasErdosHajnalProp_of_embedding_tp {W₁ W₂ : Type*}
    {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂}
    (f : H₁ ↪g H₂) (h₂ : HasErdosHajnalProp H₂) : HasErdosHajnalProp H₁ := by
  obtain ⟨c, hc, hprop⟩ := h₂
  refine ⟨c, hc, fun V _ _ G hG => hprop V G ?_⟩
  rintro ⟨g, hg⟩
  refine hG ⟨f.toEmbedding.trans g, ?_⟩
  ext u v
  exact f.map_rel_iff.symm.trans (congr_arg (fun H : SimpleGraph W₂ => H.Adj (f u) (f v)) hg).to_iff

/-- Graph isomorphism $G_1 \simeq_g G_2$ induces $G_1ᶜ \simeq_g G_2ᶜ$. -/
def complIsoTp {W₁ W₂ : Type*} {G₁ : SimpleGraph W₁} {G₂ : SimpleGraph W₂}
    (e : G₁ ≃g G₂) : G₁ᶜ ≃g G₂ᶜ where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro a b
    simp only [RelIso.coe_fn_toEquiv, SimpleGraph.compl_adj, ne_eq,
      EmbeddingLike.apply_eq_iff_eq, e.map_rel_iff]

/-- Canonical induced graph embedding $P_j \hookrightarrow_g P_k$ for $j \le k$. -/
def pathGraph_mono_emb_tp {j k : ℕ} (hjk : j ≤ k) : pathGraph j ↪g pathGraph k where
  toEmbedding := Fin.castLEEmb hjk
  map_rel_iff' := by
    intro a b
    simp [pathGraph_adj]

/-- Empty graph $\overline{K_m}$ (`⊥ : SimpleGraph (Fin m)`) embeds as an induced subgraph into
`pathGraph (2 * m)` via $i \mapsto 2 i$. -/
def botFinEmbedPathGraph (m : ℕ) : (⊥ : SimpleGraph (Fin m)) ↪g pathGraph (2 * m) where
  toEmbedding := ⟨fun i => ⟨2 * i.1, by omega⟩, fun i j h => Fin.ext (by
    have hv := congrArg Fin.val h
    dsimp only at hv
    omega)⟩
  map_rel_iff' := by
    intro i j
    simp only [Function.Embedding.coeFn_mk, SimpleGraph.bot_adj, pathGraph_adj]
    refine iff_of_false ?_ id
    rintro (h | h) <;> omega

/-- Vertex substitution closure `HasErdosHajnalProp (substGraph H₁ v₀ H₂)` across arbitrary finite types `W₁, W₂`. -/
theorem hasErdosHajnalProp_substGraph_tp
    {W₁ W₂ : Type} [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]
    (H₁ : SimpleGraph W₁) (v₀ : W₁) (H₂ : SimpleGraph W₂)
    (h₁ : HasErdosHajnalProp H₁) (h₂ : HasErdosHajnalProp H₂) :
    HasErdosHajnalProp (substGraph H₁ v₀ H₂) := by
  by_cases hne₂ : Nonempty W₂
  · exact hasErdosHajnalProp_substGraph H₁ v₀ H₂ h₁ h₂
  · haveI : IsEmpty W₂ := not_nonempty_iff.mp hne₂
    by_cases hne₁ : Nonempty {v : W₁ // v ≠ v₀}
    · let f : substGraph H₁ v₀ H₂ ↪g H₁ :=
        { toEmbedding := ⟨fun x => match x with
            | Sum.inl u => u.1
            | Sum.inr y => isEmptyElim y,
            by
              intro a b h
              cases a with
              | inl u => cases b with
                | inl w => exact congr_arg Sum.inl (Subtype.ext h)
                | inr y => exact isEmptyElim y
              | inr y => exact isEmptyElim y⟩
          map_rel_iff' := by
            intro a b
            cases a with
            | inl u => cases b with
              | inl w => rfl
              | inr y => exact isEmptyElim y
            | inr y => exact isEmptyElim y }
      exact hasErdosHajnalProp_of_embedding_tp f h₁
    · haveI : IsEmpty {v : W₁ // v ≠ v₀} := not_nonempty_iff.mp hne₁
      haveI : IsEmpty ({v : W₁ // v ≠ v₀} ⊕ W₂) := instIsEmptySum
      refine ⟨1, zero_lt_one, fun V _ _ G hG => ?_⟩
      exfalso
      refine hG ⟨Function.Embedding.ofIsEmpty, ?_⟩
      ext a b
      exact isEmptyElim a

/-- Leaf extension graph $G_0^+ := G_0 + (w_0 - w_1)$ on `Option W₀` (`Lemma 14(1)` of `main.tex`),
where `none` is a new degree-$1$ leaf adjacent solely to `some w₁`. -/
def PlusLeafGraph {W₀ : Type*} (G₀ : SimpleGraph W₀) (w₁ : W₀) : SimpleGraph (Option W₀) where
  Adj a b :=
    match a, b with
    | none, none => False
    | none, some w => w = w₁
    | some w, none => w = w₁
    | some x, some y => G₀.Adj x y
  symm a b := by
    cases a <;> cases b
    · exact id
    · exact id
    · exact id
    · exact fun h => G₀.symm h
  loopless a := by
    cases a with
    | none => exact id
    | some x => exact G₀.loopless x

/-- Map `Option (Fin (k - 1)) → Fin k` for `plusLeafPathIso`. -/
def plusLeafPathFun (k : ℕ) (hk : 2 ≤ k) : Option (Fin (k - 1)) → Fin k
  | none => ⟨0, by omega⟩
  | some a => ⟨a.1 + 1, by omega⟩

/-- Canonical isomorphism $P_{k-1}^+ \simeq_g P_k$ (`PlusLeafGraph (pathGraph (k - 1)) 0 ≃g pathGraph k`)
for $k \ge 2$. -/
def plusLeafPathIso (k : ℕ) (hk : 2 ≤ k) :
    PlusLeafGraph (pathGraph (k - 1)) ⟨0, by omega⟩ ≃g pathGraph k where
  toFun := plusLeafPathFun k hk
  invFun i := if h0 : i.1 = 0 then none else some ⟨i.1 - 1, by omega⟩
  left_inv x := by
    cases x with
    | none => rfl
    | some a =>
      have ha : a.1 + 1 ≠ 0 := by omega
      simp only [plusLeafPathFun, dif_neg ha]
      exact congrArg some (Fin.ext rfl)
  right_inv i := by
    by_cases h0 : i.1 = 0
    · simp only [dif_pos h0, plusLeafPathFun]
      exact Fin.ext h0.symm
    · simp only [dif_neg h0, plusLeafPathFun]
      exact Fin.ext (by dsimp; omega)
  map_rel_iff' := by
    intro a b
    cases a with
    | none =>
      cases b with
      | none => simp [plusLeafPathFun, PlusLeafGraph, pathGraph_adj]
      | some y =>
        simp only [PlusLeafGraph, pathGraph_adj, Fin.ext_iff]
        dsimp [plusLeafPathFun]
        omega
    | some x =>
      cases b with
      | none =>
        simp only [PlusLeafGraph, pathGraph_adj, Fin.ext_iff]
        dsimp [plusLeafPathFun]
        omega
      | some y =>
        simp only [PlusLeafGraph, pathGraph_adj]
        dsimp [plusLeafPathFun]
        omega

/-- Complete join $K_2[1 \leftarrow H_1,\, 2 \leftarrow H_2]$ (`joinGraph H₁ H₂`) on `U₁ ⊕ U₂`,
where all cross-summand pairs `(Sum.inl u₁, Sum.inr u₂)` are adjacent. -/
def joinGraph {U₁ U₂ : Type*} (H₁ : SimpleGraph U₁) (H₂ : SimpleGraph U₂) :
    SimpleGraph (U₁ ⊕ U₂) where
  Adj a b :=
    match a, b with
    | Sum.inl x, Sum.inl y => H₁.Adj x y
    | Sum.inr x, Sum.inr y => H₂.Adj x y
    | Sum.inl _, Sum.inr _ => True
    | Sum.inr _, Sum.inl _ => True
  symm a b := by
    cases a <;> cases b <;> first | exact fun h => H₁.symm h | exact fun h => H₂.symm h | exact id
  loopless a := by
    cases a with
    | inl x => exact H₁.loopless x
    | inr y => exact H₂.loopless y

/-- Explicit graph isomorphism showing `joinGraph H₁ H₂` is obtained by two vertex substitutions into
`⊤ : SimpleGraph (Fin 2)` ($K_2[0 \leftarrow H_1, 1 \leftarrow H_2]$). -/
def joinGraphIsoSubst {U₁ U₂ : Type*} (H₁ : SimpleGraph U₁) (H₂ : SimpleGraph U₂) :
    substGraph (substGraph (⊤ : SimpleGraph (Fin 2)) 0 H₁) (Sum.inl ⟨1, by decide⟩) H₂ ≃g
      joinGraph H₁ H₂ where
  toFun
    | Sum.inl ⟨Sum.inr u₁, _⟩ => Sum.inl u₁
    | Sum.inr u₂ => Sum.inr u₂
    | Sum.inl ⟨Sum.inl ⟨i, hi₀⟩, hne₁⟩ =>
        False.elim (by fin_cases i; exact hi₀ rfl; exact hne₁ rfl)
  invFun
    | Sum.inl u₁ => Sum.inl ⟨Sum.inr u₁, fun h => by cases h⟩
    | Sum.inr u₂ => Sum.inr u₂
  left_inv x := by
    rcases x with ⟨w, hw⟩ | u₂
    · rcases w with ⟨i, hi₀⟩ | u₁
      · fin_cases i
        · exact False.elim (hi₀ rfl)
        · exact False.elim (hw rfl)
      · rfl
    · rfl
  right_inv y := by
    cases y <;> rfl
  map_rel_iff' := by
    intro a b
    rcases a with ⟨w₁, hw₁⟩ | u₂ <;> rcases b with ⟨w₂, hw₂⟩ | v₂
    · rcases w₁ with ⟨i₁, hi₁⟩ | u₁ <;> rcases w₂ with ⟨i₂, hi₂⟩ | v₁
      · fin_cases i₁
        · exact False.elim (hi₁ rfl)
        · exact False.elim (hw₁ rfl)
      · fin_cases i₁
        · exact False.elim (hi₁ rfl)
        · exact False.elim (hw₁ rfl)
      · fin_cases i₂
        · exact False.elim (hi₂ rfl)
        · exact False.elim (hw₂ rfl)
      · rfl
    · rcases w₁ with ⟨i₁, hi₁⟩ | u₁
      · fin_cases i₁
        · exact False.elim (hi₁ rfl)
        · exact False.elim (hw₁ rfl)
      · simp [substGraph, joinGraph]
    · rcases w₂ with ⟨i₂, hi₂⟩ | v₁
      · fin_cases i₂
        · exact False.elim (hi₂ rfl)
        · exact False.elim (hw₂ rfl)
      · simp [substGraph, joinGraph]
    · rfl

/-- Closure of `HasErdosHajnalProp` under complete join `joinGraph H₁ H₂`. -/
theorem hasErdosHajnalProp_joinGraph {U₁ U₂ : Type} [Fintype U₁] [DecidableEq U₁]
    [Fintype U₂] [DecidableEq U₂] {H₁ : SimpleGraph U₁} {H₂ : SimpleGraph U₂}
    (h₁ : HasErdosHajnalProp H₁) (h₂ : HasErdosHajnalProp H₂) :
    HasErdosHajnalProp (joinGraph H₁ H₂) := by
  have hs₁ := hasErdosHajnalProp_substGraph_tp (⊤ : SimpleGraph (Fin 2)) 0 H₁
    hasErdosHajnalProp_top_fin2 h₁
  have hs₂ := hasErdosHajnalProp_substGraph_tp _ (Sum.inl ⟨1, by decide⟩) H₂ hs₁ h₂
  exact hasErdosHajnalProp_of_iso (joinGraphIsoSubst H₁ H₂) hs₂

/-- Disjoint union of special vertex sets `S₁ ⊔ S₂` inside `U₁ ⊕ U₂`. -/
def joinSpec {U₁ U₂ : Type*} [DecidableEq U₁] [DecidableEq U₂]
    (S₁ : Finset U₁) (S₂ : Finset U₂) : Finset (U₁ ⊕ U₂) :=
  S₁.map Function.Embedding.inl ∪ S₂.map Function.Embedding.inr

@[simp]
theorem mem_joinSpec_inl {U₁ U₂ : Type*} [DecidableEq U₁] [DecidableEq U₂]
    (S₁ : Finset U₁) (S₂ : Finset U₂) (u₁ : U₁) :
    Sum.inl u₁ ∈ joinSpec S₁ S₂ ↔ u₁ ∈ S₁ := by
  simp [joinSpec]

@[simp]
theorem mem_joinSpec_inr {U₁ U₂ : Type*} [DecidableEq U₁] [DecidableEq U₂]
    (S₁ : Finset U₁) (S₂ : Finset U₂) (u₂ : U₂) :
    Sum.inr u₂ ∈ joinSpec S₁ S₂ ↔ u₂ ∈ S₂ := by
  simp [joinSpec]

/-- Left restriction of `IsOpenIntervalRealization` across `joinGraph H₁ H₂`. -/
theorem IsOpenIntervalRealization.inl_join {U₁ U₂ V : Type*} [DecidableEq U₁] [DecidableEq U₂]
    {H₁ : SimpleGraph U₁} {H₂ : SimpleGraph U₂} {S₁ : Finset U₁} {S₂ : Finset U₂}
    {G : SimpleGraph V} {v₀ : V} {f : U₁ ⊕ U₂ ↪ V}
    (hf : IsOpenIntervalRealization (joinGraph H₁ H₂) (joinSpec S₁ S₂) G v₀ f) :
    IsOpenIntervalRealization H₁ S₁ G v₀ (Function.Embedding.inl.trans f) where
  ne_ext u := hf.ne_ext (Sum.inl u)
  adj_ext_spec u hu := hf.adj_ext_spec (Sum.inl u) ((mem_joinSpec_inl S₁ S₂ u).mpr hu)
  nonadj_ext_nonspec u hu := hf.nonadj_ext_nonspec (Sum.inl u) (by simpa using hu)
  adj_of_wit_adj u₁ u₂ hadj := hf.adj_of_wit_adj (Sum.inl u₁) (Sum.inl u₂) hadj
  nonadj_of_wit_nonadj u₁ u₂ hne hspec hnadj :=
    hf.nonadj_of_wit_nonadj (Sum.inl u₁) (Sum.inl u₂) (fun h => hne (Sum.inl.inj h))
      (hspec.imp (by simp) (by simp)) hnadj

/-- Right restriction of `IsOpenIntervalRealization` across `joinGraph H₁ H₂`. -/
theorem IsOpenIntervalRealization.inr_join {U₁ U₂ V : Type*} [DecidableEq U₁] [DecidableEq U₂]
    {H₁ : SimpleGraph U₁} {H₂ : SimpleGraph U₂} {S₁ : Finset U₁} {S₂ : Finset U₂}
    {G : SimpleGraph V} {v₀ : V} {f : U₁ ⊕ U₂ ↪ V}
    (hf : IsOpenIntervalRealization (joinGraph H₁ H₂) (joinSpec S₁ S₂) G v₀ f) :
    IsOpenIntervalRealization H₂ S₂ G v₀ (Function.Embedding.inr.trans f) where
  ne_ext u := hf.ne_ext (Sum.inr u)
  adj_ext_spec u hu := hf.adj_ext_spec (Sum.inr u) ((mem_joinSpec_inr S₁ S₂ u).mpr hu)
  nonadj_ext_nonspec u hu := hf.nonadj_ext_nonspec (Sum.inr u) (by simpa using hu)
  adj_of_wit_adj u₁ u₂ hadj := hf.adj_of_wit_adj (Sum.inr u₁) (Sum.inr u₂) hadj
  nonadj_of_wit_nonadj u₁ u₂ hne hspec hnadj :=
    hf.nonadj_of_wit_nonadj (Sum.inr u₁) (Sum.inr u₂) (fun h => hne (Sum.inr.inj h))
      (hspec.imp (by simp) (by simp)) hnadj

/-! ### Section 2: Universal Terminal-Path Recursive Pure-Substitution Arm (`Lemma 14(1)`) -/

/-- Canonical embedding of `m : Fin s` into `Fin L` when `s ≤ L`. -/
def slotFinLe {s L : ℕ} (hs : s ≤ L) (m : Fin s) : Fin L :=
  ⟨m.1, Nat.lt_of_lt_of_le m.2 hs⟩

/-- Remaining un-substituted vertices of $W_0$ after substituting the first `s` slots along `w_path`. -/
abbrev RemVert {W₀ : Type u} {L : ℕ} (w_path : Fin L ↪ W₀) (s : ℕ) (hs : s ≤ L) : Type u :=
  {z : W₀ // ∀ m : Fin s, z ≠ w_path (slotFinLe hs m)}

/-- Recursive vertex type `TermArmVert W₀ w_path r` of $\operatorname{Arm}_r(B_0)$ (`Lemma 14(1)` of `main.tex`). -/
def TermArmVert (W₀ : Type u) {L : ℕ} (w_path : Fin L ↪ W₀) : ℕ → Type u
  | 0 => ULift.{u} (Fin 2)
  | 1 => ULift.{u} (Fin 2)
  | r + 2 =>
      (Fin (min (r + 2) L) × TermArmVert W₀ w_path (r + 1)) ⊕
        RemVert w_path (min (r + 2) L) (Nat.min_le_right (r + 2) L)

instance instFintypeTermArmVert {W₀ : Type u} [Fintype W₀] [DecidableEq W₀]
    {L : ℕ} (w_path : Fin L ↪ W₀) : ∀ r : ℕ, Fintype (TermArmVert W₀ w_path r)
  | 0 => inferInstanceAs (Fintype (ULift.{u} (Fin 2)))
  | 1 => inferInstanceAs (Fintype (ULift.{u} (Fin 2)))
  | r + 2 =>
      letI : Fintype (TermArmVert W₀ w_path (r + 1)) := instFintypeTermArmVert w_path (r + 1)
      inferInstanceAs (Fintype ((Fin (min (r + 2) L) × TermArmVert W₀ w_path (r + 1)) ⊕
        RemVert w_path (min (r + 2) L) (Nat.min_le_right (r + 2) L)))

instance instDecidableEqTermArmVert {W₀ : Type u} [DecidableEq W₀]
    {L : ℕ} (w_path : Fin L ↪ W₀) : ∀ r : ℕ, DecidableEq (TermArmVert W₀ w_path r)
  | 0 => inferInstanceAs (DecidableEq (ULift.{u} (Fin 2)))
  | 1 => inferInstanceAs (DecidableEq (ULift.{u} (Fin 2)))
  | r + 2 =>
      letI : DecidableEq (TermArmVert W₀ w_path (r + 1)) := instDecidableEqTermArmVert w_path (r + 1)
      inferInstanceAs (DecidableEq ((Fin (min (r + 2) L) × TermArmVert W₀ w_path (r + 1)) ⊕
        RemVert w_path (min (r + 2) L) (Nat.min_le_right (r + 2) L)))

/-- Projection `armSlot` mapping each vertex of a partial or full substitution stage to its parent slot in $W_0$. -/
def armSlot {W₀ : Type u} {U : Type*} {L s : ℕ} (w_path : Fin L ↪ W₀) (hs : s ≤ L) :
    (Fin s × U) ⊕ RemVert w_path s hs → W₀
  | Sum.inl (m, _) => w_path (slotFinLe hs m)
  | Sum.inr z => z.1

/-- Partial substitution graph `TermArmStage B₀ w_path A s hs`: substitutes `A` into the first `s`
vertices `w_path 0, ..., w_path (s - 1)` of `B₀` (`s ≤ L`). -/
def TermArmStage {W₀ : Type u} {U : Type*} {L : ℕ} (B₀ : SimpleGraph W₀) (w_path : Fin L ↪ W₀)
    (A : SimpleGraph U) (s : ℕ) (hs : s ≤ L) :
    SimpleGraph ((Fin s × U) ⊕ RemVert w_path s hs) where
  Adj x y :=
    match x, y with
    | Sum.inl (m₁, u₁), Sum.inl (m₂, u₂) =>
        if m₁ = m₂ then A.Adj u₁ u₂ else B₀.Adj (w_path (slotFinLe hs m₁)) (w_path (slotFinLe hs m₂))
    | _, _ => B₀.Adj (armSlot w_path hs x) (armSlot w_path hs y)
  symm x y := by
    cases x with
    | inl mu₁ =>
      cases y with
      | inl mu₂ =>
        rcases mu₁ with ⟨m₁, u₁⟩
        rcases mu₂ with ⟨m₂, u₂⟩
        by_cases h : m₁ = m₂
        · subst h; simp only [if_pos]; exact fun ha => A.symm ha
        · have h' : m₂ ≠ m₁ := fun e => h e.symm
          simp only [if_neg h, if_neg h']
          exact fun hb => B₀.symm hb
      | inr z₂ => exact fun hb => B₀.symm hb
    | inr z₁ =>
      cases y with
      | inl mu₂ => exact fun hb => B₀.symm hb
      | inr z₂ => exact fun hb => B₀.symm hb
  loopless x := by
    cases x with
    | inl mu => simp
    | inr z => exact B₀.loopless z.1

/-- Recursive pure-substitution arm graph $\operatorname{Arm}_r(B_0)$ (`TermArmGraph B₀ w_path r`,
`Lemma 14(1)` of `main.tex`). -/
def TermArmGraph {W₀ : Type u} {L : ℕ} (B₀ : SimpleGraph W₀) (w_path : Fin L ↪ W₀) :
    ∀ r : ℕ, SimpleGraph (TermArmVert W₀ w_path r)
  | 0 => ⊥
  | 1 => ⊥
  | r + 2 =>
      TermArmStage B₀ w_path (TermArmGraph B₀ w_path (r + 1))
        (min (r + 2) L) (Nat.min_le_right (r + 2) L)

/-- Boolean predicate characterizing special vertices $S_r(B_0) \subseteq V(\operatorname{Arm}_r(B_0))$. -/
def isTermArmSpec {W₀ : Type u} {L : ℕ} (w_path : Fin L ↪ W₀) :
    ∀ {r : ℕ}, TermArmVert W₀ w_path r → Bool
  | 0, u => u.down == 0
  | 1, u => u.down == 0
  | _ + 2, Sum.inl (_, u) => isTermArmSpec w_path u
  | _ + 2, Sum.inr _ => false

/-- Special vertex finset $S_r(B_0) \subseteq V(\operatorname{Arm}_r(B_0))$ (`Lemma 14(1)` of `main.tex`). -/
def TermArmSpec {W₀ : Type u} [Fintype W₀] [DecidableEq W₀] {L : ℕ}
    (w_path : Fin L ↪ W₀) (r : ℕ) : Finset (TermArmVert W₀ w_path r) :=
  Finset.univ.filter (fun x => isTermArmSpec w_path x = true)

@[simp]
theorem mem_termArmSpec_iff {W₀ : Type u} [Fintype W₀] [DecidableEq W₀] {L : ℕ}
    (w_path : Fin L ↪ W₀) {r : ℕ} (x : TermArmVert W₀ w_path r) :
    x ∈ TermArmSpec w_path r ↔ isTermArmSpec w_path x = true := by
  simp [TermArmSpec]

/-- Stage `0` of `TermArmStage B₀ w_path A 0` is isomorphic to `B₀`. -/
def termArmStageZeroIso {W₀ : Type u} {U : Type*} {L : ℕ} (B₀ : SimpleGraph W₀)
    (w_path : Fin L ↪ W₀) (A : SimpleGraph U) :
    B₀ ≃g TermArmStage B₀ w_path A 0 (Nat.zero_le L) where
  toFun z := Sum.inr ⟨z, fun m => m.elim0⟩
  invFun
    | Sum.inl (m, _) => m.elim0
    | Sum.inr z => z.1
  left_inv _ := rfl
  right_inv x := by
    cases x with
    | inl mu => exact mu.1.elim0
    | inr _ => rfl
  map_rel_iff' := by
    intro _ _
    rfl

/-- Target vertex in `TermArmStage B₀ w_path A s hs` corresponding to `w_path ⟨s, hs'⟩` (`s + 1 ≤ L`). -/
def termArmStageNextTarget {W₀ : Type u} {U : Type*} {L s : ℕ} (w_path : Fin L ↪ W₀)
    (hs : s ≤ L) (hs' : s + 1 ≤ L) :
    (Fin s × U) ⊕ RemVert w_path s hs :=
  Sum.inr ⟨w_path ⟨s, hs'⟩, fun m h => by
    have hv := congrArg Fin.val (w_path.injective h)
    dsimp [slotFinLe] at hv
    omega⟩

/-- Stage `s + 1` of `TermArmStage` is isomorphic to substituting `A` into `termArmStageNextTarget`
of stage `s`. -/
def termArmStageSuccIso {W₀ : Type u} {U : Type*} [DecidableEq W₀] {L s : ℕ} (B₀ : SimpleGraph W₀)
    (w_path : Fin L ↪ W₀) (A : SimpleGraph U) (hs : s ≤ L) (hs' : s + 1 ≤ L) :
    substGraph (TermArmStage B₀ w_path A s hs) (termArmStageNextTarget w_path hs hs') A ≃g
      TermArmStage B₀ w_path A (s + 1) hs' where
  toFun
    | Sum.inl ⟨Sum.inl (m, u), _⟩ => Sum.inl (m.castSucc, u)
    | Sum.inl ⟨Sum.inr z, hne⟩ =>
        Sum.inr ⟨z.1, fun m hm => by
          by_cases hms : m.1 < s
          · exact z.2 ⟨m.1, hms⟩ hm
          · have hm_eq : m.1 = s := by omega
            apply hne
            apply congrArg Sum.inr
            apply Subtype.ext
            simpa [termArmStageNextTarget, slotFinLe, hm_eq] using hm⟩
    | Sum.inr u => Sum.inl (Fin.last s, u)
  invFun
    | Sum.inl (m, u) =>
        if hms : m.1 < s then
          Sum.inl ⟨Sum.inl (⟨m.1, hms⟩, u), by simp [termArmStageNextTarget]⟩
        else
          Sum.inr u
    | Sum.inr z =>
        Sum.inl ⟨Sum.inr ⟨z.1, fun m hm => z.2 m.castSucc hm⟩, by
          intro h
          have hv : z.1 = w_path ⟨s, hs'⟩ := congrArg (fun q => q.1) (Sum.inr.inj h)
          exact z.2 (Fin.last s) hv⟩
  left_inv x := by
    rcases x with ⟨w, hw⟩ | u
    · rcases w with ⟨m, u⟩ | z
      · simp [m.2]
      · rfl
    · simp
  right_inv y := by
    rcases y with ⟨m, u⟩ | z
    · by_cases hms : m.1 < s
      · simp [hms]
      · have hm_eq : m = Fin.last s := Fin.ext (by dsimp; omega)
        subst hm_eq
        simp
    · rfl
  map_rel_iff' := by
    intro a b
    rcases a with ⟨w₁, hw₁⟩ | u₁ <;> rcases b with ⟨w₂, hw₂⟩ | u₂
    · rcases w₁ with ⟨m₁, x₁⟩ | z₁ <;> rcases w₂ with ⟨m₂, x₂⟩ | z₂
      · simp only [substGraph, TermArmStage, Fin.ext_iff, Fin.val_castSucc]
        rfl
      · rfl
      · rfl
      · rfl
    · rcases w₁ with ⟨m₁, x₁⟩ | z₁
      · have hne : m₁.castSucc ≠ Fin.last s := by
          intro h; have := congrArg Fin.val h; simp at this; omega
        simp only [substGraph, TermArmStage, if_neg hne]
        rfl
      · rfl
    · rcases w₂ with ⟨m₂, x₂⟩ | z₂
      · have hne : Fin.last s ≠ m₂.castSucc := by
          intro h; have := congrArg Fin.val h; simp at this; omega
        simp only [substGraph, TermArmStage, if_neg hne]
        rfl
      · rfl
    · simp [substGraph, TermArmStage]

/-- Isomorphism `(⊥ : SimpleGraph (Fin 2)) ≃g (⊥ : SimpleGraph (ULift (Fin 2)))`. -/
def botFin2IsoULift : (⊥ : SimpleGraph (Fin 2)) ≃g (⊥ : SimpleGraph (ULift.{0} (Fin 2))) where
  toEquiv := Equiv.ulift.symm
  map_rel_iff' := by simp

/-- **Pure-Substitution Closure of `TermArmGraph` (`Lemma 14(1)` of `main.tex`)**:
If `HasErdosHajnalProp B₀` holds, then `HasErdosHajnalProp (TermArmGraph B₀ w_path r)` holds
unconditionally for every $r \in \mathbb{N}$. -/
theorem hasErdosHajnalProp_termArmGraph {W₀ : Type} [Fintype W₀] [DecidableEq W₀]
    {L : ℕ} (B₀ : SimpleGraph W₀) (w_path : Fin L ↪ W₀)
    (hB₀ : HasErdosHajnalProp B₀) :
    ∀ r : ℕ, HasErdosHajnalProp (TermArmGraph B₀ w_path r)
  | 0 => hasErdosHajnalProp_of_iso botFin2IsoULift hasErdosHajnalProp_bot_fin2
  | 1 => hasErdosHajnalProp_of_iso botFin2IsoULift hasErdosHajnalProp_bot_fin2
  | r + 2 => by
      have hA : HasErdosHajnalProp (TermArmGraph B₀ w_path (r + 1)) :=
        hasErdosHajnalProp_termArmGraph B₀ w_path hB₀ (r + 1)
      have hStage : ∀ (s : ℕ) (hs : s ≤ L),
          HasErdosHajnalProp (TermArmStage B₀ w_path (TermArmGraph B₀ w_path (r + 1)) s hs) := by
        intro s
        induction s with
        | zero =>
          intro hs
          exact hasErdosHajnalProp_of_iso (termArmStageZeroIso B₀ w_path _) hB₀
        | succ s ih =>
          intro hs'
          have hs : s ≤ L := Nat.le_of_succ_le hs'
          have hprev := ih hs
          have hsub := hasErdosHajnalProp_substGraph_tp _
            (termArmStageNextTarget w_path hs hs') _ hprev hA
          exact hasErdosHajnalProp_of_iso
            (termArmStageSuccIso B₀ w_path _ hs hs') hsub
      exact hStage (min (r + 2) L) (Nat.min_le_right (r + 2) L)

/-- Fiber embedding of copy `m : Fin (min (r + 2) L)` into `TermArmVert W₀ w_path (r + 2)`. -/
def termArmInlEmb {W₀ : Type u} {L r : ℕ} (w_path : Fin L ↪ W₀) (m : Fin (min (r + 2) L)) :
    TermArmVert W₀ w_path (r + 1) ↪ TermArmVert W₀ w_path (r + 2) where
  toFun u := Sum.inl (m, u)
  inj' _ _ h := (Prod.mk.inj (Sum.inl.inj h)).2

/-- Helper embedding an un-substituted terminal path vertex `w_path ⟨a, ha⟩` (`r + 2 ≤ a < L`)
into `RemVert w_path (min (r + 2) L)`. -/
def remVertOfPathIdx {W₀ : Type u} {L r : ℕ} (w_path : Fin L ↪ W₀)
    (a : ℕ) (ha_lo : r + 2 ≤ a) (ha_hi : a < L) :
    RemVert w_path (min (r + 2) L) (Nat.min_le_right (r + 2) L) :=
  ⟨w_path ⟨a, ha_hi⟩, fun m h => by
    have hv := congrArg Fin.val (w_path.injective h)
    have hm : m.1 < r + 2 := Nat.lt_of_lt_of_le m.2 (Nat.min_le_left _ _)
    dsimp [slotFinLe] at hv
    omega⟩

/-- Helper embedding a head vertex `z : W₀` (`∀ a : Fin L, z ≠ w_path a`) into `RemVert`. -/
def remVertOfHead {W₀ : Type u} {L r : ℕ} (w_path : Fin L ↪ W₀)
    (z : W₀) (hz : ∀ a : Fin L, z ≠ w_path a) :
    RemVert w_path (min (r + 2) L) (Nat.min_le_right (r + 2) L) :=
  ⟨z, fun m => hz (slotFinLe _ m)⟩

/-- **Lemma 14(1) (`terminal_path_arm_dichotomy`, Universal Terminal-Path Recursive Pure-Substitution
Arm Dichotomy, `main.tex` lines 1396–1462)**:
Let $G_0$ (`SimpleGraph W₀`) be any finite graph equipped with an induced terminal path
`w_path : Fin L ↪ W₀` ($L \ge 2$) satisfying:
- **(TP-1)**: `∀ a b : Fin L, G₀.Adj (w_path a) (w_path b) ↔ (pathGraph L).Adj a b`; and
- **(TP-2)**: `∀ z : W₀, (∀ a : Fin L, z ≠ w_path a) → ∀ a : Fin L, a.1 + 1 < L → ¬G₀.Adj z (w_path a)`.
Let $1 \le r \le L - 1$, and let `H : SimpleGraph (TermArmVert W₀ w_path r)` represent
$\overline{G}[\{v_u : u \in V(\operatorname{Arm}_r(\overline{G_0}))\}]$ satisfying:
- **(E-Non)**: `∀ x u, (TermArmGraph G₀ᶜ w_path r).Adj x u → ¬H.Adj x u`; and
- **(E-Edge)**: `∀ x u, x ≠ u → (x ∉ TermArmSpec w_path r ∨ u ∉ TermArmSpec w_path r) → ¬(TermArmGraph G₀ᶜ w_path r).Adj x u → H.Adj x u`.
Then either:
- **(Arm-i)**: `H` contains an induced copy of `PlusLeafGraph G₀ (w_path ⟨0, by omega⟩)`; or
- **(Arm-ii)**: `H` contains an induced `(r + 1)`-vertex path `p : pathGraph (r + 1) ↪g H` with
  `p i ∈ TermArmSpec w_path r` for all `i.1 < r` and `p (Fin.last r) ∉ TermArmSpec w_path r`. -/
theorem terminal_path_arm_dichotomy
    {W₀ : Type u} [Fintype W₀] [DecidableEq W₀]
    (G₀ : SimpleGraph W₀) {L : ℕ} (hL : 2 ≤ L) (w_path : Fin L ↪ W₀)
    (hTP1 : ∀ a b : Fin L, G₀.Adj (w_path a) (w_path b) ↔ (pathGraph L).Adj a b)
    (hTP2 : ∀ z : W₀, (∀ a : Fin L, z ≠ w_path a) → ∀ a : Fin L, a.1 + 1 < L → ¬G₀.Adj z (w_path a))
    (r : ℕ) (hr_lo : 1 ≤ r) (hr_hi : r ≤ L - 1)
    (H : SimpleGraph (TermArmVert W₀ w_path r))
    (hNon : ∀ x u, (TermArmGraph G₀ᶜ w_path r).Adj x u → ¬H.Adj x u)
    (hEdge : ∀ x u, x ≠ u →
      (x ∉ TermArmSpec w_path r ∨ u ∉ TermArmSpec w_path r) →
      ¬(TermArmGraph G₀ᶜ w_path r).Adj x u → H.Adj x u) :
    Nonempty (PlusLeafGraph G₀ (w_path ⟨0, by omega⟩) ↪g H) ∨
    ∃ p : pathGraph (r + 1) ↪g H,
      (∀ i : Fin (r + 1), i.1 < r → p i ∈ TermArmSpec w_path r) ∧
      p (Fin.last r) ∉ TermArmSpec w_path r := by
  classical
  induction r with
  | zero => omega
  | succ r_pred ih =>
    rcases eq_or_lt_of_le (Nat.zero_le r_pred) with h0 | hr_pred_pos
    · -- Base case `r = 1` (`r_pred = 0`)
      subst h0
      right
      let v0 : TermArmVert W₀ w_path 1 := ULift.up 0
      let v1 : TermArmVert W₀ w_path 1 := ULift.up 1
      have h0_mem : v0 ∈ TermArmSpec w_path 1 := by simp [v0, isTermArmSpec]
      have h1_not : v1 ∉ TermArmSpec w_path 1 := by simp [v1, isTermArmSpec]
      have hv0_ne_v1 : v0 ≠ v1 := fun h => by
        have hv : (0 : Fin 2) = 1 := congrArg ULift.down h
        exact Fin.zero_ne_one hv
      have hadj01 : H.Adj v0 v1 :=
        hEdge v0 v1 hv0_ne_v1 (Or.inr h1_not) (by simp [TermArmGraph])
      let p : pathGraph 2 ↪g H :=
        { toEmbedding := ⟨fun i => ULift.up i, fun _ _ h => ULift.up.inj h⟩
          map_rel_iff' := by
            intro i j
            fin_cases i <;> fin_cases j
            · simp
            · exact iff_of_true hadj01 (by decide)
            · exact iff_of_true (H.symm hadj01) (by decide)
            · simp }
      refine ⟨p, ?_, ?_⟩
      · intro i hi
        have hi0 : i = 0 := Fin.ext (by dsimp at hi ⊢; omega)
        subst hi0
        exact h0_mem
      · exact h1_not
    · -- Inductive step: set `r₀ := r_pred - 1`, so `r_pred = r₀ + 1 ≥ 1` and depth is `r₀ + 2 ≤ L - 1`.
      obtain ⟨r₀, rfl⟩ : ∃ r₀, r_pred = r₀ + 1 := ⟨r_pred - 1, by omega⟩
      have hr₀_lo : 1 ≤ r₀ + 1 := by omega
      have hr₀_hi : r₀ + 1 ≤ L - 1 := by omega
      let slotOf : TermArmVert W₀ w_path (r₀ + 2) → W₀ := armSlot w_path (Nat.min_le_right _ _)
      let mkSlot : Fin (r₀ + 2) → Fin (min (r₀ + 2) L) := fun a => ⟨a.1, by omega⟩
      have h_sub_or : ∀ a : Fin (r₀ + 2),
          Nonempty (PlusLeafGraph G₀ (w_path ⟨0, by omega⟩) ↪g H) ∨
          ∃ p : pathGraph (r₀ + 2) ↪g H,
            (∀ i : Fin (r₀ + 2), slotOf (p i) = w_path ⟨a.1, by omega⟩) ∧
            (∀ i : Fin (r₀ + 2), i.1 < r₀ + 1 → p i ∈ TermArmSpec w_path (r₀ + 2)) ∧
            p (Fin.last (r₀ + 1)) ∉ TermArmSpec w_path (r₀ + 2) := by
        intro a
        let emb_a := termArmInlEmb w_path (mkSlot a)
        let H_a := H.comap emb_a
        have h_inl_adj : ∀ x u : TermArmVert W₀ w_path (r₀ + 1),
            (TermArmGraph G₀ᶜ w_path (r₀ + 2)).Adj (emb_a x) (emb_a u) ↔
              (TermArmGraph G₀ᶜ w_path (r₀ + 1)).Adj x u := by
          intro x u
          change (if mkSlot a = mkSlot a then _ else _) ↔ _
          rw [if_pos rfl]
        have hNon_a : ∀ x u, (TermArmGraph G₀ᶜ w_path (r₀ + 1)).Adj x u → ¬H_a.Adj x u := by
          intro x u hxu
          exact hNon (emb_a x) (emb_a u) ((h_inl_adj x u).mpr hxu)
        have hEdge_a : ∀ x u, x ≠ u →
            (x ∉ TermArmSpec w_path (r₀ + 1) ∨ u ∉ TermArmSpec w_path (r₀ + 1)) →
            ¬(TermArmGraph G₀ᶜ w_path (r₀ + 1)).Adj x u → H_a.Adj x u := by
          intro x u hne hspec hnadj
          apply hEdge (emb_a x) (emb_a u) (emb_a.injective.ne hne)
          · exact hspec.imp (fun hx hmem => hx (by simpa [emb_a, isTermArmSpec] using hmem))
              (fun hu hmem => hu (by simpa [emb_a, isTermArmSpec] using hmem))
          · exact fun hadj => hnadj ((h_inl_adj x u).mp hadj)
        let emb_rel : H_a ↪g H := { toEmbedding := emb_a, map_rel_iff' := fun {_ _} => Iff.rfl }
        rcases ih hr₀_lo hr₀_hi H_a hNon_a hEdge_a with ⟨⟨g₀⟩⟩ | ⟨p₀, hp₀_spec, hp₀_last⟩
        · exact Or.inl ⟨g₀.trans emb_rel⟩
        · right
          let p : pathGraph (r₀ + 2) ↪g H := p₀.trans emb_rel
          refine ⟨p, ?_, ?_, ?_⟩
          · intro i
            rfl
          · intro i hi
            simpa [p, emb_rel, emb_a, isTermArmSpec] using hp₀_spec i hi
          · simpa [p, emb_rel, emb_a, isTermArmSpec] using hp₀_last
      by_cases h_any_arm1 : Nonempty (PlusLeafGraph G₀ (w_path ⟨0, by omega⟩) ↪g H)
      · exact Or.inl h_any_arm1
      · have h_all_paths : ∀ a : Fin (r₀ + 2),
            ∃ p : pathGraph (r₀ + 2) ↪g H,
              (∀ i : Fin (r₀ + 2), slotOf (p i) = w_path ⟨a.1, by omega⟩) ∧
              (∀ i : Fin (r₀ + 2), i.1 < r₀ + 1 → p i ∈ TermArmSpec w_path (r₀ + 2)) ∧
              p (Fin.last (r₀ + 1)) ∉ TermArmSpec w_path (r₀ + 2) := by
          intro a
          rcases h_sub_or a with h1 | h2
          · exact False.elim (h_any_arm1 h1)
          · exact h2
        choose z hz_slot hz_spec hz_last using h_all_paths
        have h_cross_adj_compl : ∀ x y : TermArmVert W₀ w_path (r₀ + 2),
            slotOf x ≠ slotOf y →
              ((TermArmGraph G₀ᶜ w_path (r₀ + 2)).Adj x y ↔ G₀ᶜ.Adj (slotOf x) (slotOf y)) := by
          intro x y hne_slot
          rcases x with ⟨m₁, u₁⟩ | z₁ <;> rcases y with ⟨m₂, u₂⟩ | z₂
          · have hm_ne : m₁ ≠ m₂ := fun h => hne_slot (by simp [slotOf, armSlot, h])
            change (if m₁ = m₂ then _ else _) ↔ _
            rw [if_neg hm_ne]; rfl
          · rfl
          · rfl
          · rfl
        have h_cross_non : ∀ x y : TermArmVert W₀ w_path (r₀ + 2),
            slotOf x ≠ slotOf y → G₀ᶜ.Adj (slotOf x) (slotOf y) → ¬H.Adj x y := by
          intro x y hne_slot hc
          exact hNon x y ((h_cross_adj_compl x y hne_slot).mpr hc)
        have h_cross_edge : ∀ x y : TermArmVert W₀ w_path (r₀ + 2),
            slotOf x ≠ slotOf y →
            (x ∉ TermArmSpec w_path (r₀ + 2) ∨ y ∉ TermArmSpec w_path (r₀ + 2)) →
            G₀.Adj (slotOf x) (slotOf y) → H.Adj x y := by
          intro x y hne_slot hspec hg₀
          have hxy : x ≠ y := fun h => hne_slot (congrArg slotOf h)
          apply hEdge x y hxy hspec
          rw [h_cross_adj_compl x y hne_slot, SimpleGraph.compl_adj, not_and]
          exact fun _ hnadj => hnadj hg₀
        -- Backward induction over `d : ℕ` (`d ≤ r₀ + 1`)
        have h_back : ∀ d : ℕ, d ≤ r₀ + 1 →
            Nonempty (PlusLeafGraph G₀ (w_path ⟨0, by omega⟩) ↪g H) ∨
            ∃ u : Fin (r₀ + 2) → TermArmVert W₀ w_path (r₀ + 2),
              (∀ a : Fin (r₀ + 2), r₀ + 1 - d ≤ a.1 →
                slotOf (u a) = w_path ⟨a.1, by omega⟩ ∧ u a ∈ TermArmSpec w_path (r₀ + 2)) ∧
              (∀ a : Fin (r₀ + 1), r₀ + 1 - d ≤ a.1 →
                H.Adj (u ⟨a.1, by omega⟩) (u ⟨a.1 + 1, by omega⟩)) := by
          intro d
          induction d with
          | zero =>
            intro _
            right
            refine ⟨fun a => z a 0, ?_, ?_⟩
            · intro a _
              exact ⟨hz_slot a 0, hz_spec a 0 (by dsimp; omega)⟩
            · intro a ha
              omega
          | succ d ih_d =>
            intro hd_le
            rcases ih_d (by omega) with h_arm1 | ⟨u, hu_slot_spec, hu_adj⟩
            · exact Or.inl h_arm1
            · let q : Fin (r₀ + 2) := ⟨r₀ - d, by omega⟩
              let q_next : Fin (r₀ + 2) := ⟨r₀ + 1 - d, by omega⟩
              have hu_next_slot : slotOf (u q_next) = w_path ⟨q.1 + 1, by omega⟩ := by
                rw [(hu_slot_spec q_next le_rfl).1]
                congr 1; apply Fin.ext; dsimp [q, q_next]; omega
              by_cases h_has_spec_nbr : ∃ t : Fin (r₀ + 1),
                  H.Adj (z q t.castSucc) (u q_next)
              · right
                obtain ⟨t, ht_adj⟩ := h_has_spec_nbr
                let u' : Fin (r₀ + 2) → TermArmVert W₀ w_path (r₀ + 2) :=
                  fun a => if a = q then z q t.castSucc else u a
                refine ⟨u', ?_, ?_⟩
                · intro a ha
                  dsimp [u']
                  split_ifs with haq
                  · subst haq
                    exact ⟨hz_slot q t.castSucc, hz_spec q t.castSucc t.2⟩
                  · have hgt : r₀ + 1 - d ≤ a.1 := by
                      have hne : a.1 ≠ r₀ - d := fun h => haq (Fin.ext h)
                      omega
                    exact hu_slot_spec a hgt
                · intro a ha
                  dsimp [u']
                  by_cases ha_eq : a.1 = r₀ - d
                  · have h1 : (⟨a.1, by omega⟩ : Fin (r₀ + 2)) = q := Fin.ext ha_eq
                    have h2_ne : (⟨a.1 + 1, by omega⟩ : Fin (r₀ + 2)) ≠ q := by
                      simp [q, Fin.ext_iff]; omega
                    have h2_eq : (⟨a.1 + 1, by omega⟩ : Fin (r₀ + 2)) = q_next :=
                      Fin.ext (by dsimp [q_next]; omega)
                    rw [if_pos h1, if_neg h2_ne, h2_eq]
                    exact ht_adj
                  · have h1_ne : (⟨a.1, by omega⟩ : Fin (r₀ + 2)) ≠ q :=
                      fun h => ha_eq (congrArg Fin.val h)
                    have h2_ne : (⟨a.1 + 1, by omega⟩ : Fin (r₀ + 2)) ≠ q := by
                      simp [q, Fin.ext_iff]; omega
                    rw [if_neg h1_ne, if_neg h2_ne]
                    exact hu_adj a (by omega)
              · -- Early exit (`t_q = r₀ + 2`): construct induced copy of `PlusLeafGraph G₀ (w_path 0)` in `H`
                left
                push_neg at h_has_spec_nbr
                have hz_last_adj_next : H.Adj (z q (Fin.last (r₀ + 1))) (u q_next) := by
                  apply h_cross_edge (z q (Fin.last (r₀ + 1))) (u q_next)
                  · rw [hz_slot q _, hu_next_slot]
                    intro h; have hv := congrArg Fin.val (w_path.injective h); dsimp at hv; omega
                  · exact Or.inl (hz_last q)
                  · rw [hz_slot q _, hu_next_slot, hTP1]
                    simp [pathGraph_adj]
                let P_tilde : Fin (L + 1) → TermArmVert W₀ w_path (r₀ + 2) := fun s =>
                  if hs1 : s.1 ≤ q.1 + 1 then
                    z q ⟨(r₀ - q.1) + s.1, by dsimp [q] at hs1 ⊢; omega⟩
                  else if s.1 = q.1 + 2 then
                    u q_next
                  else if hs3 : s.1 ≤ r₀ + 2 then
                    z ⟨s.1 - 1, by omega⟩ (Fin.last (r₀ + 1))
                  else
                    Sum.inr (remVertOfPathIdx w_path (s.1 - 1) (by omega) (by omega))
                let slotIdx : Fin (L + 1) → Fin L := fun s =>
                  if s.1 ≤ q.1 + 1 then ⟨q.1, by omega⟩ else ⟨s.1 - 1, by omega⟩
                have hP_slot : ∀ s : Fin (L + 1), slotOf (P_tilde s) = w_path (slotIdx s) := by
                  intro s
                  dsimp [P_tilde, slotIdx]
                  split_ifs with hs1 hs2 hs3
                  · exact hz_slot q _
                  · rw [hu_next_slot]
                    congr 1; apply Fin.ext; dsimp; omega
                  · exact hz_slot ⟨s.1 - 1, by omega⟩ _
                  · rfl
                have hP_nonspec_ge3 : ∀ s : Fin (L + 1), q.1 + 3 ≤ s.1 →
                    P_tilde s ∉ TermArmSpec w_path (r₀ + 2) := by
                  intro s hs_ge3
                  dsimp [P_tilde]
                  have hs1 : ¬(s.1 ≤ q.1 + 1) := by omega
                  have hs2 : ¬(s.1 = q.1 + 2) := by omega
                  rw [dif_neg hs1, if_neg hs2]
                  split_ifs with hs3
                  · exact hz_last ⟨s.1 - 1, by omega⟩
                  · simp [isTermArmSpec]
                have hP_inj : Function.Injective P_tilde := by
                  intro s₁ s₂ heq
                  by_cases h1 : s₁.1 ≤ q.1 + 1 <;> by_cases h2 : s₂.1 ≤ q.1 + 1
                  · dsimp [P_tilde] at heq
                    rw [dif_pos h1, dif_pos h2] at heq
                    have hv := congrArg Fin.val ((z q).injective heq)
                    dsimp at hv
                    exact Fin.ext (by omega)
                  · exfalso
                    have hsl := congrArg slotOf heq
                    rw [hP_slot s₁, hP_slot s₂] at hsl
                    have hv := congrArg Fin.val (w_path.injective hsl)
                    dsimp [slotIdx] at hv
                    rw [if_pos h1, if_neg h2] at hv
                    dsimp at hv
                    omega
                  · exfalso
                    have hsl := congrArg slotOf heq
                    rw [hP_slot s₁, hP_slot s₂] at hsl
                    have hv := congrArg Fin.val (w_path.injective hsl)
                    dsimp [slotIdx] at hv
                    rw [if_neg h1, if_pos h2] at hv
                    dsimp at hv
                    omega
                  · have hsl := congrArg slotOf heq
                    rw [hP_slot s₁, hP_slot s₂] at hsl
                    have hv := congrArg Fin.val (w_path.injective hsl)
                    dsimp [slotIdx] at hv
                    rw [if_neg h1, if_neg h2] at hv
                    dsimp at hv
                    exact Fin.ext (by omega)
                have hP_lt_adj : ∀ s₁ s₂ : Fin (L + 1), s₁.1 < s₂.1 →
                    (H.Adj (P_tilde s₁) (P_tilde s₂) ↔ s₁.1 + 1 = s₂.1) := by
                  intro s₁ s₂ hlt
                  by_cases h2_le1 : s₂.1 ≤ q.1 + 1
                  · have h1_le1 : s₁.1 ≤ q.1 + 1 := by omega
                    have he1 : P_tilde s₁ = z q ⟨(r₀ - q.1) + s₁.1, by dsimp [q] at h1_le1 ⊢; omega⟩ := by
                      dsimp [P_tilde]; rw [dif_pos h1_le1]
                    have he2 : P_tilde s₂ = z q ⟨(r₀ - q.1) + s₂.1, by dsimp [q] at h2_le1 ⊢; omega⟩ := by
                      dsimp [P_tilde]; rw [dif_pos h2_le1]
                    rw [he1, he2, (z q).map_adj_iff, pathGraph_adj]
                    dsimp; omega
                  · by_cases h2_eq2 : s₂.1 = q.1 + 2
                    · have h1_le1 : s₁.1 ≤ q.1 + 1 := by omega
                      have he1 : P_tilde s₁ = z q ⟨(r₀ - q.1) + s₁.1, by dsimp [q] at h1_le1 ⊢; omega⟩ := by
                        dsimp [P_tilde]; rw [dif_pos h1_le1]
                      have he2 : P_tilde s₂ = u q_next := by
                        dsimp [P_tilde]; rw [dif_neg h2_le1, if_pos h2_eq2]
                      rw [he1, he2]
                      by_cases hsucc : s₁.1 + 1 = s₂.1
                      · refine iff_of_true ?_ hsucc
                        have hs₁_eq : s₁.1 = q.1 + 1 := by omega
                        have hlast_eq : (⟨(r₀ - q.1) + s₁.1, by dsimp [q] at h1_le1 ⊢; omega⟩ : Fin (r₀ + 2)) =
                            Fin.last (r₀ + 1) := Fin.ext (by
                              dsimp
                              rw [hs₁_eq]
                              dsimp [q]
                              omega)
                        rw [hlast_eq]
                        exact hz_last_adj_next
                      · refine iff_of_false ?_ hsucc
                        have hs₁_le : s₁.1 ≤ q.1 := by omega
                        have hlt_last : (r₀ - q.1) + s₁.1 < r₀ + 1 := by
                          dsimp [q] at hs₁_le ⊢
                          omega
                        exact h_has_spec_nbr ⟨(r₀ - q.1) + s₁.1, hlt_last⟩
                    · have hs₂_ge3 : q.1 + 3 ≤ s₂.1 := by omega
                      have hs₂_nonspec : P_tilde s₂ ∉ TermArmSpec w_path (r₀ + 2) :=
                        hP_nonspec_ge3 s₂ hs₂_ge3
                      have hsl_ne : slotOf (P_tilde s₁) ≠ slotOf (P_tilde s₂) := by
                        rw [hP_slot s₁, hP_slot s₂]
                        intro h
                        have hv := congrArg Fin.val (w_path.injective h)
                        dsimp [slotIdx] at hv
                        split_ifs at hv <;> (dsimp at hv; omega)
                      by_cases hsucc : s₁.1 + 1 = s₂.1
                      · refine iff_of_true ?_ hsucc
                        apply h_cross_edge (P_tilde s₁) (P_tilde s₂) hsl_ne (Or.inr hs₂_nonspec)
                        rw [hP_slot s₁, hP_slot s₂, hTP1]
                        have h1_not : ¬(s₁.1 ≤ q.1 + 1) := by omega
                        have h2_not : ¬(s₂.1 ≤ q.1 + 1) := by omega
                        simp only [slotIdx, if_neg h1_not, if_neg h2_not, pathGraph_adj]
                        omega
                      · refine iff_of_false ?_ hsucc
                        apply h_cross_non (P_tilde s₁) (P_tilde s₂) hsl_ne
                        rw [SimpleGraph.compl_adj]
                        refine ⟨hsl_ne, ?_⟩
                        rw [hP_slot s₁, hP_slot s₂, hTP1]
                        dsimp [slotIdx]
                        split_ifs <;> (simp only [pathGraph_adj]; omega)
                let g_opt : Option W₀ → TermArmVert W₀ w_path (r₀ + 2) := fun opt =>
                  match opt with
                  | none => P_tilde ⟨0, by omega⟩
                  | some w =>
                      if hw : ∃ b : Fin L, w_path b = w then
                        P_tilde ⟨(Classical.choose hw).1 + 1, by omega⟩
                      else
                        Sum.inr (remVertOfHead w_path w (fun b hb => hw ⟨b, hb.symm⟩))
                have hg_some_path : ∀ b : Fin L, g_opt (some (w_path b)) = P_tilde ⟨b.1 + 1, by omega⟩ := by
                  intro b
                  have hex : ∃ b' : Fin L, w_path b' = w_path b := ⟨b, rfl⟩
                  have hchoose : Classical.choose hex = b := w_path.injective (Classical.choose_spec hex)
                  dsimp [g_opt]
                  rw [dif_pos hex]
                  exact congrArg P_tilde (Fin.ext (by dsimp; rw [hchoose]))
                have hg_some_head : ∀ (w : W₀) (hw : ∀ b : Fin L, w ≠ w_path b),
                    g_opt (some w) = Sum.inr (remVertOfHead w_path w hw) := by
                  intro w hw
                  have hnex : ¬∃ b : Fin L, w_path b = w := fun ⟨b, hb⟩ => hw b hb.symm
                  dsimp [g_opt]
                  rw [dif_neg hnex]
                have hP_slot_head_ne : ∀ (s : Fin (L + 1)) (w : W₀) (hw : ∀ b : Fin L, w ≠ w_path b),
                    slotOf (P_tilde s) ≠ w := by
                  intro s w hw h
                  rw [hP_slot s] at h
                  exact hw (slotIdx s) h.symm
                have hg_inj : Function.Injective g_opt := by
                  intro x y hxy
                  cases x with
                  | none =>
                    cases y with
                    | none => rfl
                    | some w =>
                      by_cases hw : ∃ b : Fin L, w_path b = w
                      · obtain ⟨b, rfl⟩ := hw
                        rw [hg_some_path b] at hxy
                        have hv := congrArg Fin.val (hP_inj hxy)
                        dsimp at hv; omega
                      · have hw' : ∀ b : Fin L, w ≠ w_path b := fun b hb => hw ⟨b, hb.symm⟩
                        rw [hg_some_head w hw'] at hxy
                        exact False.elim (hP_slot_head_ne ⟨0, by omega⟩ w hw' (congrArg slotOf hxy))
                  | some w₁ =>
                    cases y with
                    | none =>
                      by_cases hw₁ : ∃ b : Fin L, w_path b = w₁
                      · obtain ⟨b, rfl⟩ := hw₁
                        rw [hg_some_path b] at hxy
                        have hv := congrArg Fin.val (hP_inj hxy)
                        dsimp at hv; omega
                      · have hw₁' : ∀ b : Fin L, w₁ ≠ w_path b := fun b hb => hw₁ ⟨b, hb.symm⟩
                        rw [hg_some_head w₁ hw₁'] at hxy
                        exact False.elim (hP_slot_head_ne ⟨0, by omega⟩ w₁ hw₁' (congrArg slotOf hxy.symm))
                    | some w₂ =>
                      by_cases hw₁ : ∃ b : Fin L, w_path b = w₁ <;> by_cases hw₂ : ∃ b : Fin L, w_path b = w₂
                      · obtain ⟨b₁, rfl⟩ := hw₁
                        obtain ⟨b₂, rfl⟩ := hw₂
                        rw [hg_some_path b₁, hg_some_path b₂] at hxy
                        have hv := congrArg Fin.val (hP_inj hxy)
                        dsimp at hv
                        exact congrArg (some ∘ w_path) (Fin.ext (by omega))
                      · obtain ⟨b₁, rfl⟩ := hw₁
                        have hw₂' : ∀ b : Fin L, w₂ ≠ w_path b := fun b hb => hw₂ ⟨b, hb.symm⟩
                        rw [hg_some_path b₁, hg_some_head w₂ hw₂'] at hxy
                        exact False.elim (hP_slot_head_ne ⟨b₁.1 + 1, by omega⟩ w₂ hw₂' (congrArg slotOf hxy))
                      · obtain ⟨b₂, rfl⟩ := hw₂
                        have hw₁' : ∀ b : Fin L, w₁ ≠ w_path b := fun b hb => hw₁ ⟨b, hb.symm⟩
                        rw [hg_some_head w₁ hw₁', hg_some_path b₂] at hxy
                        exact False.elim (hP_slot_head_ne ⟨b₂.1 + 1, by omega⟩ w₁ hw₁' (congrArg slotOf hxy.symm))
                      · have hw₁' : ∀ b : Fin L, w₁ ≠ w_path b := fun b hb => hw₁ ⟨b, hb.symm⟩
                        have hw₂' : ∀ b : Fin L, w₂ ≠ w_path b := fun b hb => hw₂ ⟨b, hb.symm⟩
                        rw [hg_some_head w₁ hw₁', hg_some_head w₂ hw₂'] at hxy
                        exact congrArg some (congrArg Subtype.val (Sum.inr.inj hxy))
                have hg_path_head_adj : ∀ (s : Fin (L + 1)) (w : W₀) (hw : ∀ b : Fin L, w ≠ w_path b),
                    H.Adj (P_tilde s) (g_opt (some w)) ↔ s.1 = L ∧ G₀.Adj (w_path ⟨L - 1, by omega⟩) w := by
                  intro s w hw
                  rw [hg_some_head w hw]
                  let y_head : TermArmVert W₀ w_path (r₀ + 2) := Sum.inr (remVertOfHead w_path w hw)
                  have hy_nonspec : y_head ∉ TermArmSpec w_path (r₀ + 2) := by simp [y_head, isTermArmSpec]
                  have hsl_ne : slotOf (P_tilde s) ≠ slotOf y_head := hP_slot_head_ne s w hw
                  by_cases hsL : s.1 = L
                  · have hslot_eq : slotIdx s = ⟨L - 1, by omega⟩ := by
                      dsimp [slotIdx]
                      have hnot : ¬(s.1 ≤ q.1 + 1) := by omega
                      rw [if_neg hnot]
                      exact Fin.ext (by dsimp; omega)
                    constructor
                    · intro hadj
                      refine ⟨hsL, ?_⟩
                      by_contra hnadj_g₀
                      apply h_cross_non (P_tilde s) y_head hsl_ne _ hadj
                      rw [SimpleGraph.compl_adj]
                      refine ⟨hsl_ne, ?_⟩
                      rwa [hP_slot s, hslot_eq]
                    · rintro ⟨_, hg₀⟩
                      apply h_cross_edge (P_tilde s) y_head hsl_ne (Or.inr hy_nonspec)
                      rwa [hP_slot s, hslot_eq]
                  · refine iff_of_false ?_ (fun h => hsL h.1)
                    apply h_cross_non (P_tilde s) y_head hsl_ne
                    rw [SimpleGraph.compl_adj]
                    refine ⟨hsl_ne, ?_⟩
                    rw [hP_slot s]
                    intro hadj_g₀
                    have hlt_L : (slotIdx s).1 + 1 < L := by
                      dsimp [slotIdx]
                      split_ifs <;> (dsimp; omega)
                    exact hTP2 w hw (slotIdx s) hlt_L (G₀.symm hadj_g₀)
                refine ⟨{ toEmbedding := ⟨g_opt, hg_inj⟩, map_rel_iff' := ?_ }⟩
                intro x y
                change H.Adj (g_opt x) (g_opt y) ↔ (PlusLeafGraph G₀ (w_path ⟨0, by omega⟩)).Adj x y
                cases x with
                | none =>
                  cases y with
                  | none => simp [PlusLeafGraph]
                  | some w =>
                    by_cases hw : ∃ b : Fin L, w_path b = w
                    · obtain ⟨b, rfl⟩ := hw
                      rw [hg_some_path b]
                      change H.Adj (P_tilde ⟨0, by omega⟩) (P_tilde ⟨b.1 + 1, by omega⟩) ↔
                        w_path b = w_path ⟨0, by omega⟩
                      rw [hP_lt_adj ⟨0, by omega⟩ ⟨b.1 + 1, by omega⟩ (by dsimp; omega)]
                      simp only [w_path.injective.eq_iff, Fin.ext_iff]
                      dsimp; omega
                    · have hw' : ∀ b : Fin L, w ≠ w_path b := fun b hb => hw ⟨b, hb.symm⟩
                      rw [hg_path_head_adj ⟨0, by omega⟩ w hw']
                      simp only [PlusLeafGraph]
                      refine iff_of_false (fun h => ?_) (fun h => hw' ⟨0, by omega⟩ h)
                      have hv : (0 : ℕ) = L := h.1
                      omega
                | some w₁ =>
                  cases y with
                  | none =>
                    by_cases hw₁ : ∃ b : Fin L, w_path b = w₁
                    · obtain ⟨b, rfl⟩ := hw₁
                      rw [hg_some_path b, H.adj_comm]
                      change H.Adj (P_tilde ⟨0, by omega⟩) (P_tilde ⟨b.1 + 1, by omega⟩) ↔
                        w_path b = w_path ⟨0, by omega⟩
                      rw [hP_lt_adj ⟨0, by omega⟩ ⟨b.1 + 1, by omega⟩ (by dsimp; omega)]
                      simp only [w_path.injective.eq_iff, Fin.ext_iff]
                      dsimp; omega
                    · have hw₁' : ∀ b : Fin L, w₁ ≠ w_path b := fun b hb => hw₁ ⟨b, hb.symm⟩
                      rw [H.adj_comm, hg_path_head_adj ⟨0, by omega⟩ w₁ hw₁']
                      simp only [PlusLeafGraph]
                      refine iff_of_false (fun h => ?_) (fun h => hw₁' ⟨0, by omega⟩ h)
                      have hv : (0 : ℕ) = L := h.1
                      omega
                  | some w₂ =>
                    by_cases hw₁ : ∃ b : Fin L, w_path b = w₁ <;> by_cases hw₂ : ∃ b : Fin L, w_path b = w₂
                    · obtain ⟨b₁, rfl⟩ := hw₁
                      obtain ⟨b₂, rfl⟩ := hw₂
                      rw [hg_some_path b₁, hg_some_path b₂]
                      change H.Adj (P_tilde ⟨b₁.1 + 1, by omega⟩) (P_tilde ⟨b₂.1 + 1, by omega⟩) ↔
                        G₀.Adj (w_path b₁) (w_path b₂)
                      rw [hTP1 b₁ b₂]
                      by_cases hb_eq : b₁ = b₂
                      · subst hb_eq; simp
                      · rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hb_eq) with hlt | hgt
                        · rw [hP_lt_adj ⟨b₁.1 + 1, by omega⟩ ⟨b₂.1 + 1, by omega⟩ (by dsimp; omega)]
                          simp only [pathGraph_adj]; omega
                        · rw [H.adj_comm, hP_lt_adj ⟨b₂.1 + 1, by omega⟩ ⟨b₁.1 + 1, by omega⟩ (by dsimp; omega)]
                          simp only [pathGraph_adj]; omega
                    · obtain ⟨b₁, rfl⟩ := hw₁
                      have hw₂' : ∀ b : Fin L, w₂ ≠ w_path b := fun b hb => hw₂ ⟨b, hb.symm⟩
                      rw [hg_some_path b₁, hg_path_head_adj ⟨b₁.1 + 1, by omega⟩ w₂ hw₂']
                      change (b₁.1 + 1 = L ∧ G₀.Adj (w_path ⟨L - 1, by omega⟩) w₂) ↔
                        G₀.Adj (w_path b₁) w₂
                      by_cases hbL : b₁.1 + 1 = L
                      · have hb_eq : b₁ = ⟨L - 1, by omega⟩ := Fin.ext (by dsimp; omega)
                        rw [hb_eq]
                        exact ⟨fun h => h.2, fun h => ⟨by dsimp; omega, h⟩⟩
                      · have hlt_L : b₁.1 + 1 < L := by omega
                        have hnadj : ¬G₀.Adj (w_path b₁) w₂ :=
                          fun h => hTP2 w₂ hw₂' b₁ hlt_L (G₀.symm h)
                        exact iff_of_false (fun h => hbL h.1) hnadj
                    · obtain ⟨b₂, rfl⟩ := hw₂
                      have hw₁' : ∀ b : Fin L, w₁ ≠ w_path b := fun b hb => hw₁ ⟨b, hb.symm⟩
                      rw [H.adj_comm, hg_some_path b₂, hg_path_head_adj ⟨b₂.1 + 1, by omega⟩ w₁ hw₁']
                      change (b₂.1 + 1 = L ∧ G₀.Adj (w_path ⟨L - 1, by omega⟩) w₁) ↔
                        G₀.Adj w₁ (w_path b₂)
                      by_cases hbL : b₂.1 + 1 = L
                      · have hb_eq : b₂ = ⟨L - 1, by omega⟩ := Fin.ext (by dsimp; omega)
                        rw [hb_eq]
                        exact ⟨fun h => G₀.symm h.2, fun h => ⟨by dsimp; omega, G₀.symm h⟩⟩
                      · have hlt_L : b₂.1 + 1 < L := by omega
                        have hnadj : ¬G₀.Adj w₁ (w_path b₂) := hTP2 w₁ hw₁' b₂ hlt_L
                        exact iff_of_false (fun h => hbL h.1) hnadj
                    · have hw₁' : ∀ b : Fin L, w₁ ≠ w_path b := fun b hb => hw₁ ⟨b, hb.symm⟩
                      have hw₂' : ∀ b : Fin L, w₂ ≠ w_path b := fun b hb => hw₂ ⟨b, hb.symm⟩
                      rw [hg_some_head w₁ hw₁', hg_some_head w₂ hw₂']
                      by_cases heq : w₁ = w₂
                      · subst heq; simp [PlusLeafGraph]
                      · let y₁ : TermArmVert W₀ w_path (r₀ + 2) := Sum.inr (remVertOfHead w_path w₁ hw₁')
                        let y₂ : TermArmVert W₀ w_path (r₀ + 2) := Sum.inr (remVertOfHead w_path w₂ hw₂')
                        have hy₁_ns : y₁ ∉ TermArmSpec w_path (r₀ + 2) := by simp [y₁, isTermArmSpec]
                        constructor
                        · intro hadj
                          by_contra hnadj_g₀
                          apply h_cross_non y₁ y₂ heq _ hadj
                          exact ⟨heq, hnadj_g₀⟩
                        · intro hg₀
                          exact h_cross_edge y₁ y₂ heq (Or.inl hy₁_ns) hg₀
        rcases h_back (r₀ + 1) le_rfl with h_arm1 | ⟨u, hu_slot_spec, hu_adj⟩
        · exact Or.inl h_arm1
        · right
          let v_end : TermArmVert W₀ w_path (r₀ + 2) :=
            Sum.inr (remVertOfPathIdx w_path (r₀ + 2) le_rfl (by omega))
          let p_out : Fin (r₀ + 3) → TermArmVert W₀ w_path (r₀ + 2) := fun i =>
            if hi : i.1 < r₀ + 2 then u ⟨i.1, hi⟩ else v_end
          have hp_slot : ∀ i : Fin (r₀ + 3), slotOf (p_out i) = w_path ⟨i.1, by omega⟩ := by
            intro i
            dsimp [p_out]
            split_ifs with hi
            · exact (hu_slot_spec ⟨i.1, hi⟩ (by omega)).1
            · have hi_eq : i.1 = r₀ + 2 := by omega
              dsimp [v_end, slotOf, armSlot, remVertOfPathIdx]
              congr 1; exact Fin.ext hi_eq.symm
          have hp_inj : Function.Injective p_out := by
            intro i j hij
            have hsl := congrArg slotOf hij
            rw [hp_slot i, hp_slot j] at hsl
            have hv := congrArg (fun x => x.1) (w_path.injective hsl)
            dsimp at hv
            exact Fin.ext hv
          have hp_lt_adj : ∀ i j : Fin (r₀ + 3), i.1 < j.1 →
              (H.Adj (p_out i) (p_out j) ↔ i.1 + 1 = j.1) := by
            intro i j hij
            by_cases hsucc : i.1 + 1 = j.1
            · refine iff_of_true ?_ hsucc
              by_cases hj_lt : j.1 < r₀ + 2
              · have hi_lt : i.1 < r₀ + 2 := by omega
                have h1 : p_out i = u ⟨i.1, hi_lt⟩ := by dsimp [p_out]; rw [dif_pos hi_lt]
                have h2 : p_out j = u ⟨i.1 + 1, by omega⟩ := by
                  dsimp [p_out]; rw [dif_pos hj_lt]; congr 1; exact Fin.ext hsucc.symm
                rw [h1, h2]
                exact hu_adj ⟨i.1, by omega⟩ (by omega)
              · have hi_lt : i.1 < r₀ + 2 := by omega
                have h1 : p_out i = u ⟨i.1, hi_lt⟩ := by dsimp [p_out]; rw [dif_pos hi_lt]
                have h2 : p_out j = v_end := by dsimp [p_out]; rw [dif_neg hj_lt]
                rw [h1, h2]
                apply h_cross_edge (u ⟨i.1, hi_lt⟩) v_end
                · rw [(hu_slot_spec ⟨i.1, hi_lt⟩ (by omega)).1]
                  dsimp [v_end, slotOf, armSlot, remVertOfPathIdx]
                  intro h; have hv := congrArg Fin.val (w_path.injective h); dsimp at hv; omega
                · exact Or.inr (by simp [v_end, isTermArmSpec])
                · rw [(hu_slot_spec ⟨i.1, hi_lt⟩ (by omega)).1]
                  dsimp [v_end, slotOf, armSlot, remVertOfPathIdx]
                  rw [hTP1, pathGraph_adj]
                  dsimp; omega
            · refine iff_of_false ?_ hsucc
              apply h_cross_non (p_out i) (p_out j)
              · rw [hp_slot i, hp_slot j]
                intro h; have hv := congrArg Fin.val (w_path.injective h); dsimp at hv; omega
              · rw [SimpleGraph.compl_adj, hp_slot i, hp_slot j]
                refine ⟨fun h => by have hv := congrArg Fin.val (w_path.injective h); dsimp at hv; omega, ?_⟩
                rw [hTP1, pathGraph_adj]
                dsimp; omega
          refine ⟨{ toEmbedding := ⟨p_out, hp_inj⟩, map_rel_iff' := ?_ }, ?_, ?_⟩
          · intro i j
            change H.Adj (p_out i) (p_out j) ↔ (pathGraph (r₀ + 3)).Adj i j
            by_cases hij : i = j
            · subst hij; simp
            · rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hgt
              · rw [hp_lt_adj i j hlt, pathGraph_adj]; omega
              · rw [H.adj_comm, hp_lt_adj j i hgt, pathGraph_adj]; omega
          · intro i hi
            change p_out i ∈ TermArmSpec w_path (r₀ + 2)
            dsimp [p_out]
            rw [dif_pos hi]
            exact (hu_slot_spec ⟨i.1, hi⟩ (by omega)).2
          · change p_out (Fin.last (r₀ + 2)) ∉ TermArmSpec w_path (r₀ + 2)
            simp [p_out, v_end, isTermArmSpec]

/-! ### Section 3: Unified Two-Polarity Pendant-$P_3$ Open-Interval Lifting (`Lemma 14(2)`) -/

/-- Lower open-attachment block index set
$I_{\mathrm{open}}(v_0, \eta_{\mathrm{low}}) := \{i \in [\ell] : \eta_{\mathrm{low}} w_* < |N_{F'}(v_0) \cap B_i| < \frac{1}{2} w_*\}$
(`Lemma 14(2a)` of `main.tex`). -/
noncomputable def lowerOpenAttachmentIndices {V : Type*} [Fintype V] [DecidableEq V]
    (F' : SimpleGraph V) {ℓ : ℕ} (B : Fin ℓ → Finset V) (v₀ : V) (η_low : ℝ) (w_star : ℕ) :
    Finset (Fin ℓ) :=
  by classical exact Finset.univ.filter (fun i =>
    η_low * (w_star : ℝ) < ((neighborFinsetIn F' v₀ (B i)).card : ℝ) ∧
    ((neighborFinsetIn F' v₀ (B i)).card : ℝ) < (1 / 2 : ℝ) * (w_star : ℝ))

/-- Upper open-attachment block index set
$I_{\mathrm{high}}^{\mathrm{open}}(v_0, \eta_{\mathrm{low}}) := \{i \in [\ell] : \frac{1}{2} w_* \le |N_{F'}(v_0) \cap B_i| < (1 - \eta_{\mathrm{low}}) w_*\}$
(`Lemma 14(2b)` of `main.tex`). -/
noncomputable def upperOpenAttachmentIndices {V : Type*} [Fintype V] [DecidableEq V]
    (F' : SimpleGraph V) {ℓ : ℕ} (B : Fin ℓ → Finset V) (v₀ : V) (η_low : ℝ) (w_star : ℕ) :
    Finset (Fin ℓ) :=
  by classical exact Finset.univ.filter (fun i =>
    (1 / 2 : ℝ) * (w_star : ℝ) ≤ ((neighborFinsetIn F' v₀ (B i)).card : ℝ) ∧
    ((neighborFinsetIn F' v₀ (B i)).card : ℝ) < (1 - η_low) * (w_star : ℝ))

/-- Markov high-degree bad set for a single block pair `(A, B)` under graph `H_pair`:
$\{x \in A : |N_{H_{\mathrm{pair}}}(x) \cap B| \ge \frac{\eta_{\mathrm{low}}}{4h} w_*\}$. -/
noncomputable def markovBadPairSet {V : Type*} [Fintype V] [DecidableEq V]
    (H_pair : SimpleGraph V) (A B : Finset V) (η_low : ℝ) (h w_star : ℕ) : Finset V :=
  by classical exact A.filter (fun x =>
    (η_low / (4 * (h : ℝ))) * (w_star : ℝ) ≤ ((neighborFinsetIn H_pair x B).card : ℝ))

/-- Markov bound on `markovBadPairSet`: if `(crossEdgeCount H_pair A B : ℝ) ≤ (η_low ^ 2 / (64 * h ^ 2)) * w_star ^ 2`,
then `(markovBadPairSet H_pair A B η_low h w_star).card ≤ (η_low / (16 * h)) * w_star`. -/
theorem card_markovBadPairSet_le {V : Type*} [Fintype V] [DecidableEq V]
    (H_pair : SimpleGraph V) (A B : Finset V) (η_low : ℝ) (h w_star : ℕ)
    (hη_pos : 0 < η_low) (hh_pos : 1 ≤ h) (hw_pos : 1 ≤ w_star)
    (hcross : (crossEdgeCount H_pair A B : ℝ) ≤
      (η_low ^ 2 / (64 * (h : ℝ) ^ 2)) * (w_star : ℝ) ^ 2) :
    ((markovBadPairSet H_pair A B η_low h w_star).card : ℝ) ≤
      (η_low / (16 * (h : ℝ))) * (w_star : ℝ) := by
  classical
  let τ : ℝ := (η_low / (4 * (h : ℝ))) * (w_star : ℝ)
  have hh_r : (0 : ℝ) < (h : ℝ) := Nat.cast_pos.mpr (by omega)
  have hw_r : (0 : ℝ) < (w_star : ℝ) := Nat.cast_pos.mpr (by omega)
  have hτ_pos : 0 < τ := by dsimp [τ]; positivity
  let Bad := markovBadPairSet H_pair A B η_low h w_star
  have hsum_bad : (Bad.card : ℝ) * τ ≤ (crossEdgeCount H_pair A B : ℝ) := by
    calc (Bad.card : ℝ) * τ
      _ = ∑ _x ∈ Bad, τ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ Bad, ((neighborFinsetIn H_pair x B).card : ℝ) :=
          Finset.sum_le_sum (fun x hx => (Finset.mem_filter.mp hx).2)
      _ ≤ ∑ x ∈ A, ((neighborFinsetIn H_pair x B).card : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.cast_nonneg _)
      _ = (crossEdgeCount H_pair A B : ℝ) := by simp [crossEdgeCount]
  have hprod : (Bad.card : ℝ) * τ ≤ ((η_low / (16 * (h : ℝ))) * (w_star : ℝ)) * τ := by
    calc (Bad.card : ℝ) * τ
      _ ≤ (η_low ^ 2 / (64 * (h : ℝ) ^ 2)) * (w_star : ℝ) ^ 2 := hsum_bad.trans hcross
      _ = ((η_low / (16 * (h : ℝ))) * (w_star : ℝ)) * τ := by
          dsimp [τ]; ring
  exact le_of_mul_le_mul_right hprod hτ_pos

/-- **Unified Tuple Realization Lemma for Weakly Sparse-or-Co-Sparse Blockades (`Lemma 14(2)` of `main.tex`)**:
Given any injective tuple `j : Fin k_tup ↪ Fin ℓ` (`k_tup + 1 ≤ h`) of distinct blocks of cardinality
`w_star ≥ 2`, if for every `m : Fin k_tup` the desired $v_0$-attachment subset `Cand m ⊆ B (j m)`
has cardinality `η_low * w_star < |Cand m|`, then there exists an injective selection
`a : Fin k_tup → V` with `a m ∈ Cand m` (`∀ m`) and `F'.Adj (a q) (a m) ↔ J.Adj (j q) (j m)` for all `q ≠ m`. -/
theorem exists_tuple_realization_in_weak_blockade {V : Type*} [Fintype V] [DecidableEq V]
    (F' : SimpleGraph V) {ℓ h w_star k_tup : ℕ} (J : SimpleGraph (Fin ℓ))
    (B : Fin ℓ → Finset V) (η_low : ℝ)
    (hh_4 : 4 ≤ h) (hk_tup : k_tup + 1 ≤ h) (hw_2 : 2 ≤ w_star)
    (hη_pos : 0 < η_low)
    (hB_disj : ∀ p q : Fin ℓ, p ≠ q → Disjoint (B p) (B q))
    (hcross : ∀ p q : Fin ℓ, p ≠ q →
      ((by classical exact if J.Adj p q then crossEdgeCount F'ᶜ (B p) (B q)
          else crossEdgeCount F' (B p) (B q)) : ℝ) ≤
        (η_low ^ 2 / (64 * (h : ℝ) ^ 2)) * (w_star : ℝ) ^ 2)
    (j : Fin k_tup ↪ Fin ℓ)
    (Cand : Fin k_tup → Finset V)
    (hCand_sub : ∀ m : Fin k_tup, Cand m ⊆ B (j m))
    (hCand_card : ∀ m : Fin k_tup, η_low * (w_star : ℝ) < ((Cand m).card : ℝ)) :
    ∃ a : Fin k_tup → V,
      Function.Injective a ∧
      (∀ m : Fin k_tup, a m ∈ Cand m) ∧
      (∀ q m : Fin k_tup, q ≠ m → (F'.Adj (a q) (a m) ↔ J.Adj (j q) (j m))) := by
  classical
  let H_pair : Fin k_tup → Fin k_tup → SimpleGraph V := fun q m =>
    if J.Adj (j q) (j m) then F'ᶜ else F'
  let Bad : Fin k_tup → Finset V := fun q =>
    (Finset.univ.filter (fun m : Fin k_tup => q.1 < m.1)).biUnion (fun m =>
      markovBadPairSet (H_pair q m) (B (j q)) (B (j m)) η_low h w_star)
  have hh_r : (0 : ℝ) < (h : ℝ) := Nat.cast_pos.mpr (by omega)
  have hw_r : (0 : ℝ) < (w_star : ℝ) := Nat.cast_pos.mpr (by omega)
  have hBad_card : ∀ q : Fin k_tup, ((Bad q).card : ℝ) ≤ (1 / 16 : ℝ) * η_low * (w_star : ℝ) := by
    intro q
    let M_fut := Finset.univ.filter (fun m : Fin k_tup => q.1 < m.1)
    have h1 : (Bad q).card ≤ ∑ m ∈ M_fut,
        (markovBadPairSet (H_pair q m) (B (j q)) (B (j m)) η_low h w_star).card :=
      Finset.card_biUnion_le
    have h1_r : ((Bad q).card : ℝ) ≤ ∑ m ∈ M_fut,
        ((markovBadPairSet (H_pair q m) (B (j q)) (B (j m)) η_low h w_star).card : ℝ) := by
      exact_mod_cast h1
    have h_each : ∀ m ∈ M_fut,
        ((markovBadPairSet (H_pair q m) (B (j q)) (B (j m)) η_low h w_star).card : ℝ) ≤
          (η_low / (16 * (h : ℝ))) * (w_star : ℝ) := by
      intro m hm
      have hqm : q ≠ m := fun e => by
        have hv := congrArg Fin.val e
        have hlt := (Finset.mem_filter.mp hm).2
        omega
      exact card_markovBadPairSet_le (H_pair q m) (B (j q)) (B (j m)) η_low h w_star
        hη_pos (by omega) (by omega)
        (by
          have hc := hcross (j q) (j m) (j.injective.ne hqm)
          dsimp [H_pair]
          split_ifs at hc ⊢ <;> exact hc)
    have hM_le : (M_fut.card : ℝ) ≤ (h : ℝ) := by
      have hnat : M_fut.card ≤ k_tup := (Finset.card_le_univ M_fut).trans_eq (Fintype.card_fin k_tup)
      exact_mod_cast (hnat.trans (by omega : k_tup ≤ h))
    calc ((Bad q).card : ℝ)
      _ ≤ ∑ m ∈ M_fut, ((markovBadPairSet (H_pair q m) (B (j q)) (B (j m)) η_low h w_star).card : ℝ) := h1_r
      _ ≤ ∑ _m ∈ M_fut, ((η_low / (16 * (h : ℝ))) * (w_star : ℝ)) := Finset.sum_le_sum h_each
      _ = (M_fut.card : ℝ) * ((η_low / (16 * (h : ℝ))) * (w_star : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (h : ℝ) * ((η_low / (16 * (h : ℝ))) * (w_star : ℝ)) :=
          mul_le_mul_of_nonneg_right hM_le (by positivity)
      _ = (1 / 16 : ℝ) * η_low * (w_star : ℝ) := by field_simp [hh_r.ne']
  have h_seq : ∀ s : ℕ, s ≤ k_tup →
      ∃ a : Fin k_tup → V,
        (∀ q : Fin k_tup, q.1 < s → a q ∈ Cand q ∧ a q ∉ Bad q) ∧
        (∀ q m : Fin k_tup, q.1 < m.1 → m.1 < s → ¬(H_pair q m).Adj (a q) (a m)) := by
    intro s
    induction s with
    | zero =>
      intro _
      have hex_v : ∀ m : Fin k_tup, (Cand m).Nonempty :=
        fun m => Finset.card_pos.mp (Nat.cast_pos.mp (lt_trans (by positivity) (hCand_card m)))
      by_cases hne_k : 0 < k_tup
      · obtain ⟨v_init, _⟩ := hex_v ⟨0, hne_k⟩
        exact ⟨fun _ => v_init, fun _ hq => by omega, fun _ _ _ hm => by omega⟩
      · exact ⟨fun m => False.elim (by have := m.2; omega),
          fun _ hq => by omega, fun _ _ _ hm => by omega⟩
    | succ s ih =>
      intro hs_le
      obtain ⟨a, ha_mem, ha_pair⟩ := ih (Nat.le_of_succ_le hs_le)
      let m_cur : Fin k_tup := ⟨s, hs_le⟩
      let Q_prev := Finset.univ.filter (fun q : Fin k_tup => q.1 < s)
      let Forb : Finset V := Bad m_cur ∪
        Q_prev.biUnion (fun q => neighborFinsetIn (H_pair q m_cur) (a q) (B (j m_cur)))
      have hForb_lt : ((Forb.card : ℝ)) < η_low * (w_star : ℝ) := by
        have h1 : Forb.card ≤ (Bad m_cur).card +
            ∑ q ∈ Q_prev, (neighborFinsetIn (H_pair q m_cur) (a q) (B (j m_cur))).card :=
          (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _)
        have h1_r : (Forb.card : ℝ) ≤ ((Bad m_cur).card : ℝ) +
            ∑ q ∈ Q_prev, ((neighborFinsetIn (H_pair q m_cur) (a q) (B (j m_cur))).card : ℝ) := by
          exact_mod_cast h1
        have h_each_q : ∀ q ∈ Q_prev,
            ((neighborFinsetIn (H_pair q m_cur) (a q) (B (j m_cur))).card : ℝ) ≤
              (η_low / (4 * (h : ℝ))) * (w_star : ℝ) := by
          intro q hq
          have hq_lt : q.1 < s := (Finset.mem_filter.mp hq).2
          obtain ⟨hq_cand, hq_not_bad⟩ := ha_mem q hq_lt
          have hq_B : a q ∈ B (j q) := hCand_sub q hq_cand
          by_contra h_big
          push_neg at h_big
          apply hq_not_bad
          rw [Finset.mem_biUnion]
          refine ⟨m_cur, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq_lt⟩, ?_⟩
          exact Finset.mem_filter.mpr ⟨hq_B, h_big.le⟩
        have hQ_le : (Q_prev.card : ℝ) ≤ (h : ℝ) := by
          have hnat : Q_prev.card ≤ k_tup := (Finset.card_le_univ Q_prev).trans_eq (Fintype.card_fin k_tup)
          exact_mod_cast (hnat.trans (by omega : k_tup ≤ h))
        have hsum_q : ∑ q ∈ Q_prev, ((neighborFinsetIn (H_pair q m_cur) (a q) (B (j m_cur))).card : ℝ) ≤
            (1 / 4 : ℝ) * η_low * (w_star : ℝ) := by
          calc ∑ q ∈ Q_prev, ((neighborFinsetIn (H_pair q m_cur) (a q) (B (j m_cur))).card : ℝ)
            _ ≤ ∑ _q ∈ Q_prev, ((η_low / (4 * (h : ℝ))) * (w_star : ℝ)) := Finset.sum_le_sum h_each_q
            _ = (Q_prev.card : ℝ) * ((η_low / (4 * (h : ℝ))) * (w_star : ℝ)) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (h : ℝ) * ((η_low / (4 * (h : ℝ))) * (w_star : ℝ)) :=
                mul_le_mul_of_nonneg_right hQ_le (by positivity)
            _ = (1 / 4 : ℝ) * η_low * (w_star : ℝ) := by field_simp [hh_r.ne']
        have hbad_cur := hBad_card m_cur
        have hprod_pos : 0 < η_low * (w_star : ℝ) := mul_pos hη_pos hw_r
        nlinarith
      have h_not_sub : ¬(Cand m_cur ⊆ Forb) := by
        intro hsub
        have hle : ((Cand m_cur).card : ℝ) ≤ (Forb.card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
        linarith [hCand_card m_cur]
      obtain ⟨x_cur, hx_cand, hx_not_forb⟩ := Finset.not_subset.mp h_not_sub
      rw [Finset.mem_union, not_or] at hx_not_forb
      obtain ⟨hx_not_bad, hx_not_prev⟩ := hx_not_forb
      let a' : Fin k_tup → V := fun m => if m = m_cur then x_cur else a m
      refine ⟨a', ?_, ?_⟩
      · intro q hq
        dsimp [a']
        split_ifs with hqm
        · subst hqm; exact ⟨hx_cand, hx_not_bad⟩
        · have hlt : q.1 < s := by
            have hne : q.1 ≠ s := fun h => hqm (Fin.ext h)
            omega
          exact ha_mem q hlt
      · intro q m hqm hm_lt
        dsimp [a']
        by_cases hm_eq : m = m_cur
        · subst hm_eq
          have hq_ne : q ≠ m_cur := fun h => by subst h; exact Nat.lt_irrefl _ hqm
          rw [if_neg hq_ne, if_pos rfl]
          intro hadj_pair
          apply hx_not_prev
          rw [Finset.mem_biUnion]
          refine ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqm⟩, ?_⟩
          rw [mem_neighborFinsetIn]
          exact ⟨hCand_sub m_cur hx_cand, hadj_pair⟩
        · have hne_m : m.1 ≠ s := fun h => hm_eq (Fin.ext h)
          have hq_ne : q ≠ m_cur := fun h => by
            have hqs : q.1 = s := congrArg Fin.val h
            omega
          have hm_lt_s : m.1 < s := by omega
          rw [if_neg hq_ne, if_neg hm_eq]
          exact ha_pair q m hqm hm_lt_s
  obtain ⟨a, ha_mem, ha_pair⟩ := h_seq k_tup le_rfl
  have ha_inj : Function.Injective a := by
    intro q m hqm_eq
    by_contra hne
    exact Finset.disjoint_left.mp (hB_disj (j q) (j m) (j.injective.ne hne))
      (hCand_sub q (ha_mem q q.2).1) (hqm_eq ▸ hCand_sub m (ha_mem m m.2).1)
  refine ⟨a, ha_inj, fun m => (ha_mem m m.2).1, ?_⟩
  intro q m hne
  have hlt_iff : ∀ u v : Fin k_tup, u.1 < v.1 → (F'.Adj (a u) (a v) ↔ J.Adj (j u) (j v)) := by
    intro u v huv
    have hn := ha_pair u v huv v.2
    dsimp [H_pair] at hn
    by_cases hJ : J.Adj (j u) (j v)
    · rw [if_pos hJ, SimpleGraph.compl_adj, not_and] at hn
      refine iff_of_true ?_ hJ
      by_contra hF'
      exact hn (ha_inj.ne (Fin.ne_of_lt huv)) hF'
    · rw [if_neg hJ] at hn
      exact iff_of_false hn hJ
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
  · exact hlt_iff q m hlt
  · rw [F'.adj_comm, J.adj_comm]
    exact hlt_iff m q hgt

/-- **Lemma 14(2) (`pendant_p3_open_interval_lifting`, Unified Two-Polarity Pendant-$P_3$
Open-Interval Lifting with Tuple-Specific Markov Pruning Across All $H_* = G_0 + (y - w_2 - x_2)$,
`main.tex` lines 1422–1480)**:
Let $H_*$ (`SimpleGraph W_star`) be any finite graph of order $h := |W_*| \ge 4$ having a degree-$1$
vertex $x_2 \in W_*$ whose unique neighbor $w_2 \in W_*$ has degree $2$ with $N_{H_*}(w_2) = \{y, x_2\}$.
Set $G_0 := H_* \setminus \{w_2, x_2\}$. Let $F'$ be any $\overline{H_*}$-free graph, $\eta_{\mathrm{low}} \in (0, \frac{1}{8}]$,
and let $B_1, \dots, B_\ell$ be pairwise disjoint blocks of size $w_* \ge 2$ with pattern graph $J$
satisfying $|Q_{F'}(B_p, B_q)| \le \frac{\eta_{\mathrm{low}}^2}{64 h^2} w_*^2$ for all $p \neq q$.
Then for every external vertex $v_0 \notin \bigcup_{i=1}^\ell B_i$:
- **(a)** `J.induce (lowerOpenAttachmentIndices F' B v₀ η_low w_star)` is `(H_* - x₂)ᶜ`-free; and
- **(b)** `J.induce (upperOpenAttachmentIndices F' B v₀ η_low w_star)` is
  `substGraph (⊤ : SimpleGraph (Fin 2)) 1 G₀ᶜ`-free ($K_2[1 \leftarrow K_1,\, 2 \leftarrow \overline{G_0}]$-free). -/
theorem pendant_p3_open_interval_lifting
    {W_star V : Type*} [Fintype W_star] [DecidableEq W_star] [Fintype V] [DecidableEq V]
    (H_star : SimpleGraph W_star)
    (hh_4 : 4 ≤ Fintype.card W_star)
    (x₂ w₂ y : W_star)
    (hx₂_deg1 : ∀ z : W_star, H_star.Adj x₂ z ↔ z = w₂)
    (hw₂_deg2 : y ≠ x₂ ∧ ∀ z : W_star, H_star.Adj w₂ z ↔ z = y ∨ z = x₂)
    {F' : SimpleGraph V} (hF' : IsInducedSubgraphFree F' H_starᶜ)
    {ℓ w_star : ℕ} (hw_2 : 2 ≤ w_star)
    (B : Fin ℓ → Finset V)
    (hB_card : ∀ i : Fin ℓ, (B i).card = w_star)
    (hB_disj : ∀ p q : Fin ℓ, p ≠ q → Disjoint (B p) (B q))
    {η_low : ℝ} (hη_pos : 0 < η_low) (_hη_ub : η_low ≤ 1 / 8)
    (J : SimpleGraph (Fin ℓ))
    (hcross : ∀ p q : Fin ℓ, p ≠ q →
      ((by classical exact if J.Adj p q then crossEdgeCount F'ᶜ (B p) (B q)
          else crossEdgeCount F' (B p) (B q)) : ℝ) ≤
        (η_low ^ 2 / (64 * (Fintype.card W_star : ℝ) ^ 2)) * (w_star : ℝ) ^ 2)
    (v₀ : V) (hv₀_ext : ∀ i : Fin ℓ, v₀ ∉ B i) :
    let H_minus := H_star.comap (Subtype.val : {z : W_star // z ≠ x₂} → W_star)
    let G₀ := H_star.comap (Subtype.val : {z : W_star // z ≠ w₂ ∧ z ≠ x₂} → W_star)
    IsInducedSubgraphFree
      (J.induce (lowerOpenAttachmentIndices F' B v₀ η_low w_star : Set (Fin ℓ)))
      H_minusᶜ ∧
    IsInducedSubgraphFree
      (J.induce (upperOpenAttachmentIndices F' B v₀ η_low w_star : Set (Fin ℓ)))
      (substGraph (⊤ : SimpleGraph (Fin 2)) 1 G₀ᶜ) := by
  classical
  dsimp only
  let H_minus := H_star.comap (Subtype.val : {z : W_star // z ≠ x₂} → W_star)
  let G₀ := H_star.comap (Subtype.val : {z : W_star // z ≠ w₂ ∧ z ≠ x₂} → W_star)
  have hw₂_ne_x₂ : w₂ ≠ x₂ := fun h => H_star.loopless x₂ ((hx₂_deg1 x₂).mpr h.symm)
  have hy_ne_w₂ : y ≠ w₂ := fun h => H_star.loopless w₂ ((hw₂_deg2.2 w₂).mpr (Or.inl h.symm))
  have h_sdiff_card : ∀ i : Fin ℓ,
      ((B i \ neighborFinsetIn F' v₀ (B i)).card : ℝ) +
        ((neighborFinsetIn F' v₀ (B i)).card : ℝ) = (w_star : ℝ) := by
    intro i
    have hsub : neighborFinsetIn F' v₀ (B i) ⊆ B i :=
      fun u hu => (mem_neighborFinsetIn F' v₀ (B i) u |>.mp hu).1
    have hnat := Finset.card_sdiff_add_card_eq_card hsub
    rw [hB_card i] at hnat
    exact_mod_cast hnat
  constructor
  · -- Part (2a): Lower open-attachment interval `(η_low * w_star, 1/2 * w_star)` is `H_minusᶜ`-free
    rintro ⟨emb_ind, hemb_ind⟩
    let e_sub : {z : W_star // z ≠ x₂} ≃ Fin (Fintype.card {z : W_star // z ≠ x₂}) :=
      Fintype.equivFin _
    let k_tup := Fintype.card {z : W_star // z ≠ x₂}
    have hk_tup : k_tup + 1 ≤ Fintype.card W_star := by
      let bij : Option {z : W_star // z ≠ x₂} ≃ W_star :=
        { toFun := fun
            | none => x₂
            | some z => z.1
          invFun := fun z => if hx : z = x₂ then none else some ⟨z, hx⟩
          left_inv := fun
            | none => by simp
            | some z => by simp [z.2]
          right_inv := fun z => by
            by_cases hx : z = x₂ <;> simp [hx] }
      have hcard := Fintype.card_congr bij
      rw [Fintype.card_option] at hcard
      omega
    let emb_fin : Fin k_tup ↪ Fin ℓ :=
      e_sub.symm.toEmbedding.trans (emb_ind.trans (Function.Embedding.subtype _))
    have hemb_apply : ∀ z : {z : W_star // z ≠ x₂}, emb_fin (e_sub z) = (emb_ind z).1 := by
      intro z
      change (emb_ind (e_sub.symm (e_sub z))).1 = (emb_ind z).1
      rw [e_sub.symm_apply_apply]
    have hemb_mem : ∀ m : Fin k_tup,
        emb_fin m ∈ lowerOpenAttachmentIndices F' B v₀ η_low w_star :=
      fun m => (emb_ind (e_sub.symm m)).2
    let Cand : Fin k_tup → Finset V := fun m =>
      if (e_sub.symm m).1 = w₂ then
        B (emb_fin m) \ neighborFinsetIn F' v₀ (B (emb_fin m))
      else
        neighborFinsetIn F' v₀ (B (emb_fin m))
    have hCand_sub : ∀ m : Fin k_tup, Cand m ⊆ B (emb_fin m) := by
      intro m; dsimp [Cand]
      split_ifs
      · exact Finset.sdiff_subset
      · exact fun u hu => (mem_neighborFinsetIn F' v₀ _ u |>.mp hu).1
    have hCand_card : ∀ m : Fin k_tup, η_low * (w_star : ℝ) < ((Cand m).card : ℝ) := by
      intro m
      have hm := Finset.mem_filter.mp (hemb_mem m)
      have hw_r : (2 : ℝ) ≤ (w_star : ℝ) := by exact_mod_cast hw_2
      dsimp [Cand]
      split_ifs
      · have hs := h_sdiff_card (emb_fin m)
        linarith [hm.2.2]
      · exact hm.2.1
    obtain ⟨a, ha_inj, ha_mem, ha_adj⟩ := exists_tuple_realization_in_weak_blockade
      F' J B η_low hh_4 hk_tup hw_2 hη_pos hB_disj hcross emb_fin Cand hCand_sub hCand_card
    let φ : W_star → V := fun z =>
      if hz : z = x₂ then v₀ else a (e_sub ⟨z, hz⟩)
    have hφ_ne_v₀ : ∀ (z : W_star) (hz : z ≠ x₂), a (e_sub ⟨z, hz⟩) ≠ v₀ := by
      intro z hz h
      exact hv₀_ext (emb_fin (e_sub ⟨z, hz⟩)) (h ▸ hCand_sub _ (ha_mem _))
    have hφ_inj : Function.Injective φ := by
      intro z₁ z₂ heq
      dsimp [φ] at heq
      split_ifs at heq with hz₁ hz₂
      · exact hz₁.trans hz₂.symm
      · exact False.elim (hφ_ne_v₀ z₂ hz₂ heq.symm)
      · exact False.elim (hφ_ne_v₀ z₁ hz₁ heq)
      · exact congrArg Subtype.val (e_sub.injective (ha_inj heq))
    apply hF'
    refine ⟨⟨φ, hφ_inj⟩, ?_⟩
    ext z₁ z₂
    change H_starᶜ.Adj z₁ z₂ ↔ F'.Adj (φ z₁) (φ z₂)
    by_cases hzz : z₁ = z₂
    · subst hzz; simp
    · simp only [SimpleGraph.compl_adj, ne_eq, hzz, not_false_eq_true, true_and]
      by_cases hz₁ : z₁ = x₂
      · subst hz₁
        dsimp [φ]
        rw [dif_pos rfl, dif_neg (Ne.symm hzz)]
        let m₂ := e_sub ⟨z₂, Ne.symm hzz⟩
        have hm₂_mem := ha_mem m₂
        dsimp [Cand] at hm₂_mem
        rw [hx₂_deg1 z₂]
        have hs_eq : (e_sub.symm m₂).1 = z₂ := by simp [m₂]
        rw [hs_eq] at hm₂_mem
        by_cases hzw : z₂ = w₂
        · rw [if_pos hzw, Finset.mem_sdiff, mem_neighborFinsetIn] at hm₂_mem
          exact iff_of_false (fun h => h hzw) (fun hadj => hm₂_mem.2 ⟨hm₂_mem.1, hadj⟩)
        · rw [if_neg hzw, mem_neighborFinsetIn] at hm₂_mem
          exact iff_of_true hzw hm₂_mem.2
      · by_cases hz₂ : z₂ = x₂
        · subst hz₂
          dsimp [φ]
          rw [dif_neg hz₁, dif_pos rfl, F'.adj_comm, H_star.adj_comm, hx₂_deg1 z₁]
          let m₁ := e_sub ⟨z₁, hz₁⟩
          have hm₁_mem := ha_mem m₁
          dsimp [Cand] at hm₁_mem
          have hs_eq : (e_sub.symm m₁).1 = z₁ := by simp [m₁]
          rw [hs_eq] at hm₁_mem
          by_cases hzw : z₁ = w₂
          · rw [if_pos hzw, Finset.mem_sdiff, mem_neighborFinsetIn] at hm₁_mem
            exact iff_of_false (fun h => h hzw) (fun hadj => hm₁_mem.2 ⟨hm₁_mem.1, hadj⟩)
          · rw [if_neg hzw, mem_neighborFinsetIn] at hm₁_mem
            exact iff_of_true hzw hm₁_mem.2
        · dsimp [φ]
          rw [dif_neg hz₁, dif_neg hz₂]
          have hne_sub : (⟨z₁, hz₁⟩ : {z : W_star // z ≠ x₂}) ≠ ⟨z₂, hz₂⟩ :=
            fun h => hzz (congrArg Subtype.val h)
          have hne_m : e_sub ⟨z₁, hz₁⟩ ≠ e_sub ⟨z₂, hz₂⟩ := e_sub.injective.ne hne_sub
          rw [ha_adj _ _ hne_m, hemb_apply ⟨z₁, hz₁⟩, hemb_apply ⟨z₂, hz₂⟩]
          have hcomap := congrArg (fun K => K.Adj ⟨z₁, hz₁⟩ ⟨z₂, hz₂⟩) hemb_ind
          simp only [SimpleGraph.compl_adj, comap_adj, ne_eq, hne_sub, not_false_eq_true,
            true_and] at hcomap
          exact hcomap.to_iff
  · -- Part (2b): Upper open-attachment interval `[1/2 * w_star, (1 - η_low) * w_star)` is
    -- `substGraph (⊤ : SimpleGraph (Fin 2)) 1 G₀ᶜ`-free ($K_2[1 \leftarrow K_1, 2 \leftarrow \overline{G_0}]$-free)!
    rintro ⟨emb_ind, hemb_ind⟩
    let U_pat := {v : Fin 2 // v ≠ 1} ⊕ {z : W_star // z ≠ w₂ ∧ z ≠ x₂}
    let e_pat : U_pat ≃ Fin (Fintype.card U_pat) := Fintype.equivFin U_pat
    let k_tup := Fintype.card U_pat
    have hk_tup : k_tup + 1 ≤ Fintype.card W_star := by
      let bij : Option U_pat ≃ W_star :=
        { toFun := fun
            | none => w₂
            | some (Sum.inl _) => x₂
            | some (Sum.inr z) => z.1
          invFun := fun z =>
            if hw : z = w₂ then none
            else if hx : z = x₂ then some (Sum.inl ⟨0, by decide⟩)
            else some (Sum.inr ⟨z, hw, hx⟩)
          left_inv := fun
            | none => by simp
            | some (Sum.inl ⟨i, hi⟩) => by
                fin_cases i
                · simp [hw₂_ne_x₂.symm]
                · exact False.elim (hi rfl)
            | some (Sum.inr z) => by simp [z.2.1, z.2.2]
          right_inv := fun z => by
            by_cases hw : z = w₂
            · subst hw; simp
            · by_cases hx : z = x₂
              · subst hx; simp [hw₂_ne_x₂.symm]
              · simp [hw, hx] }
      have hcard := Fintype.card_congr bij
      rw [Fintype.card_option] at hcard
      omega
    let emb_fin : Fin k_tup ↪ Fin ℓ :=
      e_pat.symm.toEmbedding.trans (emb_ind.trans (Function.Embedding.subtype _))
    have hemb_apply : ∀ u : U_pat, emb_fin (e_pat u) = (emb_ind u).1 := by
      intro u
      change (emb_ind (e_pat.symm (e_pat u))).1 = (emb_ind u).1
      rw [e_pat.symm_apply_apply]
    have hemb_mem : ∀ m : Fin k_tup,
        emb_fin m ∈ upperOpenAttachmentIndices F' B v₀ η_low w_star :=
      fun m => (emb_ind (e_pat.symm m)).2
    let wantNonAdjV0 : U_pat → Bool
      | Sum.inl _ => true
      | Sum.inr z => decide (z.1 = y)
    let Cand : Fin k_tup → Finset V := fun m =>
      if wantNonAdjV0 (e_pat.symm m) = true then
        B (emb_fin m) \ neighborFinsetIn F' v₀ (B (emb_fin m))
      else
        neighborFinsetIn F' v₀ (B (emb_fin m))
    have hCand_sub : ∀ m : Fin k_tup, Cand m ⊆ B (emb_fin m) := by
      intro m; dsimp [Cand]
      split_ifs
      · exact Finset.sdiff_subset
      · exact fun u hu => (mem_neighborFinsetIn F' v₀ _ u |>.mp hu).1
    have hCand_card : ∀ m : Fin k_tup, η_low * (w_star : ℝ) < ((Cand m).card : ℝ) := by
      intro m
      have hm := Finset.mem_filter.mp (hemb_mem m)
      have hw_r : (2 : ℝ) ≤ (w_star : ℝ) := by exact_mod_cast hw_2
      dsimp [Cand]
      split_ifs
      · have hs := h_sdiff_card (emb_fin m)
        linarith [hm.2.2]
      · linarith [hm.2.1]
    obtain ⟨a, ha_inj, ha_mem, ha_adj⟩ := exists_tuple_realization_in_weak_blockade
      F' J B η_low hh_4 hk_tup hw_2 hη_pos hB_disj hcross emb_fin Cand hCand_sub hCand_card
    let patOf : {z : W_star // z ≠ w₂} → U_pat := fun z =>
      if hx : z.1 = x₂ then Sum.inl ⟨0, by decide⟩
      else Sum.inr ⟨z.1, z.2, hx⟩
    have hpatOf_inj : Function.Injective patOf := by
      intro z₁ z₂ heq
      by_cases hx₁ : z₁.1 = x₂ <;> by_cases hx₂ : z₂.1 = x₂
      · exact Subtype.ext (hx₁.trans hx₂.symm)
      · simp only [patOf, dif_pos hx₁, dif_neg hx₂] at heq
        exact False.elim (by cases heq)
      · simp only [patOf, dif_neg hx₁, dif_pos hx₂] at heq
        exact False.elim (by cases heq)
      · simp only [patOf, dif_neg hx₁, dif_neg hx₂] at heq
        have hv : z₁.1 = z₂.1 := congrArg (fun p => p.1) (Sum.inr.inj heq)
        exact Subtype.ext hv
    let φ : W_star → V := fun z =>
      if hw : z = w₂ then v₀ else a (e_pat (patOf ⟨z, hw⟩))
    have hφ_ne_v₀ : ∀ (z : W_star) (hw : z ≠ w₂), a (e_pat (patOf ⟨z, hw⟩)) ≠ v₀ := by
      intro z hw h
      exact hv₀_ext (emb_fin (e_pat (patOf ⟨z, hw⟩))) (h ▸ hCand_sub _ (ha_mem _))
    have hφ_inj : Function.Injective φ := by
      intro z₁ z₂ heq
      dsimp [φ] at heq
      split_ifs at heq with hw₁ hw₂
      · exact hw₁.trans hw₂.symm
      · exact False.elim (hφ_ne_v₀ z₂ hw₂ heq.symm)
      · exact False.elim (hφ_ne_v₀ z₁ hw₁ heq)
      · exact congrArg Subtype.val (hpatOf_inj (e_pat.injective (ha_inj heq)))
    apply hF'
    refine ⟨⟨φ, hφ_inj⟩, ?_⟩
    ext z₁ z₂
    change H_starᶜ.Adj z₁ z₂ ↔ F'.Adj (φ z₁) (φ z₂)
    by_cases hzz : z₁ = z₂
    · subst hzz; simp
    · simp only [SimpleGraph.compl_adj, ne_eq, hzz, not_false_eq_true, true_and]
      have h_w₂_adj : ∀ (z : W_star) (hw : z ≠ w₂),
          (¬H_star.Adj w₂ z) ↔ F'.Adj v₀ (a (e_pat (patOf ⟨z, hw⟩))) := by
        intro z hw
        let m := e_pat (patOf ⟨z, hw⟩)
        have hm_mem := ha_mem m
        dsimp [Cand] at hm_mem
        have hs_eq : e_pat.symm m = patOf ⟨z, hw⟩ := by simp [m]
        rw [hs_eq] at hm_mem
        rw [hw₂_deg2.2 z]
        by_cases hx : z = x₂
        · subst hx
          simp only [patOf, dif_pos rfl, wantNonAdjV0, if_true, Finset.mem_sdiff,
            mem_neighborFinsetIn] at hm_mem
          exact iff_of_false (fun h => h (Or.inr rfl)) (fun hadj => hm_mem.2 ⟨hm_mem.1, hadj⟩)
        · simp only [patOf, dif_neg hx, wantNonAdjV0] at hm_mem
          by_cases hzy : z = y
          · subst hzy
            simp only [decide_true, if_true, Finset.mem_sdiff, mem_neighborFinsetIn] at hm_mem
            exact iff_of_false (fun h => h (Or.inl rfl)) (fun hadj => hm_mem.2 ⟨hm_mem.1, hadj⟩)
          · simp only [decide_eq_false hzy, Bool.false_eq_true, if_false,
              mem_neighborFinsetIn] at hm_mem
            exact iff_of_true (fun h => h.elim hzy hx) hm_mem.2
      by_cases hw₁ : z₁ = w₂
      · subst hw₁
        dsimp [φ]
        rw [dif_pos rfl, dif_neg (Ne.symm hzz)]
        exact h_w₂_adj z₂ (Ne.symm hzz)
      · by_cases hw₂ : z₂ = w₂
        · subst hw₂
          dsimp [φ]
          rw [dif_neg hw₁, dif_pos rfl, F'.adj_comm, H_star.adj_comm]
          exact h_w₂_adj z₁ hw₁
        · dsimp [φ]
          rw [dif_neg hw₁, dif_neg hw₂]
          let u₁ := patOf ⟨z₁, hw₁⟩
          let u₂ := patOf ⟨z₂, hw₂⟩
          have hu_ne : u₁ ≠ u₂ := fun h => hzz (congrArg Subtype.val (hpatOf_inj h))
          rw [ha_adj (e_pat u₁) (e_pat u₂) (e_pat.injective.ne hu_ne),
            hemb_apply u₁, hemb_apply u₂]
          have hcomap : (substGraph (⊤ : SimpleGraph (Fin 2)) 1 G₀ᶜ).Adj u₁ u₂ ↔
              J.Adj (emb_ind u₁).1 (emb_ind u₂).1 :=
            (congrArg (fun K => K.Adj u₁ u₂) hemb_ind).to_iff
          rw [← hcomap]
          by_cases hx₁ : z₁ = x₂
          · subst hx₁
            have hx₂ : z₂ ≠ z₁ := Ne.symm hzz
            simp only [u₁, u₂, patOf, dif_pos rfl, dif_neg hx₂, substGraph]
            have htop : (⊤ : SimpleGraph (Fin 2)).Adj 0 1 := by decide
            exact iff_of_true (fun h => hw₂ ((hx₂_deg1 z₂).mp h)) htop
          · by_cases hx₂ : z₂ = x₂
            · subst hx₂
              simp only [u₁, u₂, patOf, dif_neg hx₁, dif_pos rfl, substGraph]
              have htop : (⊤ : SimpleGraph (Fin 2)).Adj 1 0 := by decide
              exact iff_of_true (fun h => hw₁ ((hx₂_deg1 z₁).mp (H_star.symm h))) htop
            · simp only [u₁, u₂, patOf, dif_neg hx₁, dif_neg hx₂, substGraph, G₀,
                SimpleGraph.compl_adj, comap_adj, ne_eq]
              have hsub_ne : (⟨z₁, hw₁, hx₁⟩ : {z : W_star // z ≠ w₂ ∧ z ≠ x₂}) ≠
                  ⟨z₂, hw₂, hx₂⟩ := fun h => hzz (congrArg Subtype.val h)
              simp [hsub_ne]

/-- Canonical pattern graph specialization of `pendant_p3_open_interval_lifting` using
`canonicalSymmPatternGraph F' (η_low ^ 2 / (64 * h ^ 2)) B`. -/
theorem pendant_p3_open_interval_lifting_canonical
    {W_star V : Type*} [Fintype W_star] [DecidableEq W_star] [Fintype V] [DecidableEq V]
    (H_star : SimpleGraph W_star)
    (hh_4 : 4 ≤ Fintype.card W_star)
    (x₂ w₂ y : W_star)
    (hx₂_deg1 : ∀ z : W_star, H_star.Adj x₂ z ↔ z = w₂)
    (hw₂_deg2 : y ≠ x₂ ∧ ∀ z : W_star, H_star.Adj w₂ z ↔ z = y ∨ z = x₂)
    {F' : SimpleGraph V} (hF' : IsInducedSubgraphFree F' H_starᶜ)
    {S : Finset V} {ℓ w_star : ℕ} (hw_2 : 2 ≤ w_star)
    {B : Fin ℓ → Finset V}
    {η_low : ℝ} (hη_pos : 0 < η_low) (hη_ub : η_low ≤ 1 / 8)
    (hB : IsWeaklySparseOrCoSparseBlockadeIn F' S ℓ (w_star : ℝ)
      (η_low ^ 2 / (64 * (Fintype.card W_star : ℝ) ^ 2)) B)
    (hB_card : ∀ i : Fin ℓ, (B i).card = w_star)
    (v₀ : V) (hv₀_ext : ∀ i : Fin ℓ, v₀ ∉ B i) :
    let δ := η_low ^ 2 / (64 * (Fintype.card W_star : ℝ) ^ 2)
    let J := canonicalSymmPatternGraph F' δ B
    let H_minus := H_star.comap (Subtype.val : {z : W_star // z ≠ x₂} → W_star)
    let G₀ := H_star.comap (Subtype.val : {z : W_star // z ≠ w₂ ∧ z ≠ x₂} → W_star)
    IsInducedSubgraphFree
      (J.induce (lowerOpenAttachmentIndices F' B v₀ η_low w_star : Set (Fin ℓ)))
      H_minusᶜ ∧
    IsInducedSubgraphFree
      (J.induce (upperOpenAttachmentIndices F' B v₀ η_low w_star : Set (Fin ℓ)))
      (substGraph (⊤ : SimpleGraph (Fin 2)) 1 G₀ᶜ) := by
  classical
  refine pendant_p3_open_interval_lifting H_star hh_4 x₂ w₂ y hx₂_deg1 hw₂_deg2 hF' hw_2
    B hB_card hB.1.pairwise_disjoint hη_pos hη_ub _ ?_ v₀ hv₀_ext
  intro p q hpq
  have h1 := symmPairWrongCount_canonical_le hB hpq
  unfold symmPairWrongCount at h1
  rw [if_pos hpq, hB_card p, hB_card q] at h1
  split_ifs at h1 ⊢ <;> nlinarith

/-! ### Section 4: Proposition 8(1) — Zero-Defect Thresholded Wonderfulness of All Paths $P_k$ ($k \ge 6$) -/

/-- Two-arm pure-substitution witness graph
$H_{\mathrm{TP}}^{(k)} := K_2\bigl[1 \leftarrow \operatorname{Arm}_{r_L}(\overline{P_{k-1}}),\, 2 \leftarrow \operatorname{Arm}_{r_R}(\overline{P_{k-1}})\bigr]$
for `pathGraph k` (`Proposition 8(1)` of `main.tex`), where $r_L = \lfloor (k - 2) / 2 \rfloor = \lceil (k - 3) / 2 \rceil$
and $r_R = \lfloor (k - 3) / 2 \rfloor$. -/
def TermPathWitnessGraph (k : ℕ) :
    SimpleGraph (TermArmVert (Fin (k - 1)) (Function.Embedding.refl _) ((k - 2) / 2) ⊕
      TermArmVert (Fin (k - 1)) (Function.Embedding.refl _) ((k - 3) / 2)) :=
  joinGraph
    (TermArmGraph (pathGraph (k - 1))ᶜ (Function.Embedding.refl _) ((k - 2) / 2))
    (TermArmGraph (pathGraph (k - 1))ᶜ (Function.Embedding.refl _) ((k - 3) / 2))

/-- Special vertex finset $S_{\mathrm{TP}}^{(k)} := S_{r_L}(\overline{P_{k-1}}) \sqcup S_{r_R}(\overline{P_{k-1}})$
for `TermPathWitnessGraph k`. -/
def TermPathWitnessSpec (k : ℕ) :
    Finset (TermArmVert (Fin (k - 1)) (Function.Embedding.refl _) ((k - 2) / 2) ⊕
      TermArmVert (Fin (k - 1)) (Function.Embedding.refl _) ((k - 3) / 2)) :=
  joinSpec
    (TermArmSpec (Function.Embedding.refl (Fin (k - 1))) ((k - 2) / 2))
    (TermArmSpec (Function.Embedding.refl (Fin (k - 1))) ((k - 3) / 2))

/-- **Proposition 8(1) (`isThresholdedWonderful_Pk_of_prev`, Conditional Step on $P_{k-1} \in \mathcal{EH}$,
`main.tex` lines 1487–1505 & 1546–1560)**:
For every integer $k \ge 6$, if `HasErdosHajnalProp (pathGraph (k - 1))` holds, then both
`HasErdosHajnalProp (TermPathWitnessGraph k)` and `IsThresholdedWonderful (pathGraph k)` hold. -/
theorem isThresholdedWonderful_Pk_of_prev (k : ℕ) (hk : 6 ≤ k)
    (h_prev : HasErdosHajnalProp (pathGraph (k - 1))) :
    HasErdosHajnalProp (TermPathWitnessGraph k) ∧
    IsThresholdedWonderful (pathGraph k) := by
  have h_prev_compl : HasErdosHajnalProp (pathGraph (k - 1))ᶜ := h_prev.compl
  let w_id := Function.Embedding.refl (Fin (k - 1))
  let r_L := (k - 2) / 2
  let r_R := (k - 3) / 2
  have hEH_L : HasErdosHajnalProp (TermArmGraph (pathGraph (k - 1))ᶜ w_id r_L) :=
    hasErdosHajnalProp_termArmGraph (pathGraph (k - 1))ᶜ w_id h_prev_compl r_L
  have hEH_R : HasErdosHajnalProp (TermArmGraph (pathGraph (k - 1))ᶜ w_id r_R) :=
    hasErdosHajnalProp_termArmGraph (pathGraph (k - 1))ᶜ w_id h_prev_compl r_R
  have hEH_wit : HasErdosHajnalProp (TermPathWitnessGraph k) :=
    hasErdosHajnalProp_joinGraph hEH_L hEH_R
  refine ⟨hEH_wit, isThresholdedWonderful_of_openIntervalWitness
    (pathGraph k) (TermPathWitnessGraph k) (TermPathWitnessSpec k) hEH_wit ?_⟩
  intro V _ _ G v₀ f hf
  have hf_L := hf.inl_join
  have hf_R := hf.inr_join
  let fL : TermArmVert (Fin (k - 1)) w_id r_L ↪ V := Function.Embedding.inl.trans f
  let fR : TermArmVert (Fin (k - 1)) w_id r_R ↪ V := Function.Embedding.inr.trans f
  have hTP1 : ∀ a b : Fin (k - 1), (pathGraph (k - 1)).Adj (w_id a) (w_id b) ↔ (pathGraph (k - 1)).Adj a b :=
    fun _ _ => Iff.rfl
  have hTP2 : ∀ z : Fin (k - 1), (∀ a : Fin (k - 1), z ≠ w_id a) →
      ∀ a : Fin (k - 1), a.1 + 1 < k - 1 → ¬(pathGraph (k - 1)).Adj z (w_id a) :=
    fun z hz => False.elim (hz z rfl)
  have h_arm_L :
      ¬IsInducedSubgraphFree G (pathGraph k)ᶜ ∨
      ∃ p : pathGraph (r_L + 1) ↪g (Gᶜ.comap fL),
        (∀ i : Fin (r_L + 1), i.1 < r_L → p i ∈ TermArmSpec w_id r_L) ∧
        p (Fin.last r_L) ∉ TermArmSpec w_id r_L := by
    rcases terminal_path_arm_dichotomy (pathGraph (k - 1)) (by omega) w_id hTP1 hTP2
        r_L (by omega) (by omega) (Gᶜ.comap fL)
        (fun x u hxu hc => hc.2 (hf_L.adj_of_wit_adj x u hxu))
        (fun x u hne hspec hnadj =>
          ⟨fL.injective.ne hne, hf_L.nonadj_of_wit_nonadj x u hne hspec hnadj⟩) with
      ⟨⟨g₀⟩⟩ | hp
    · left
      intro hfree
      have e_pk : pathGraph k ↪g Gᶜ :=
        (plusLeafPathIso k (by omega)).symm.toRelEmbedding.trans
          (g₀.trans { toEmbedding := fL, map_rel_iff' := fun {_ _} => Iff.rfl })
      apply hfree
      refine ⟨e_pk.toEmbedding, ?_⟩
      ext a b
      change (pathGraph k)ᶜ.Adj a b ↔ G.Adj (e_pk a) (e_pk b)
      by_cases hab : a = b
      · subst hab; simp
      · have he_ne : e_pk a ≠ e_pk b := e_pk.toEmbedding.injective.ne hab
        have hiff : (pathGraph k).Adj a b ↔ Gᶜ.Adj (e_pk a) (e_pk b) := e_pk.map_rel_iff.symm
        simp only [SimpleGraph.compl_adj, ne_eq, hab, he_ne, not_false_eq_true, true_and] at hiff ⊢
        exact ⟨fun hnA => by_contra fun hnB => hnA (hiff.mpr hnB), fun hB hA => hiff.mp hA hB⟩
    · exact Or.inr hp
  have h_arm_R :
      ¬IsInducedSubgraphFree G (pathGraph k)ᶜ ∨
      ∃ p : pathGraph (r_R + 1) ↪g (Gᶜ.comap fR),
        (∀ i : Fin (r_R + 1), i.1 < r_R → p i ∈ TermArmSpec w_id r_R) ∧
        p (Fin.last r_R) ∉ TermArmSpec w_id r_R := by
    rcases terminal_path_arm_dichotomy (pathGraph (k - 1)) (by omega) w_id hTP1 hTP2
        r_R (by omega) (by omega) (Gᶜ.comap fR)
        (fun x u hxu hc => hc.2 (hf_R.adj_of_wit_adj x u hxu))
        (fun x u hne hspec hnadj =>
          ⟨fR.injective.ne hne, hf_R.nonadj_of_wit_nonadj x u hne hspec hnadj⟩) with
      ⟨⟨g₀⟩⟩ | hp
    · left
      intro hfree
      have e_pk : pathGraph k ↪g Gᶜ :=
        (plusLeafPathIso k (by omega)).symm.toRelEmbedding.trans
          (g₀.trans { toEmbedding := fR, map_rel_iff' := fun {_ _} => Iff.rfl })
      apply hfree
      refine ⟨e_pk.toEmbedding, ?_⟩
      ext a b
      change (pathGraph k)ᶜ.Adj a b ↔ G.Adj (e_pk a) (e_pk b)
      by_cases hab : a = b
      · subst hab; simp
      · have he_ne : e_pk a ≠ e_pk b := e_pk.toEmbedding.injective.ne hab
        have hiff : (pathGraph k).Adj a b ↔ Gᶜ.Adj (e_pk a) (e_pk b) := e_pk.map_rel_iff.symm
        simp only [SimpleGraph.compl_adj, ne_eq, hab, he_ne, not_false_eq_true, true_and] at hiff ⊢
        exact ⟨fun hnA => by_contra fun hnB => hnA (hiff.mpr hnB), fun hB hA => hiff.mp hA hB⟩
    · exact Or.inr hp
  rcases h_arm_L with h_hit | ⟨pL, hpL_spec, hpL_last⟩
  · exact h_hit
  · rcases h_arm_R with h_hit | ⟨pR, hpR_spec, hpR_last⟩
    · exact h_hit
    · intro hfree
      have hk_sum : (r_L + 1) + 1 + (r_R + 1) = k := by
        dsimp [r_L, r_R]
        omega
      let bridge : Fin k → V := fun i =>
        if hiL : i.1 < r_L + 1 then
          fL (pL ⟨i.1, hiL⟩)
        else if _hiM : i.1 = r_L + 1 then
          v₀
        else
          fR (pR ⟨k - 1 - i.1, by omega⟩)
      have hcross_lr : ∀ uL uR, G.Adj (fL uL) (fR uR) :=
        fun uL uR => hf.adj_of_wit_adj (Sum.inl uL) (Sum.inr uR) trivial
      have hbridge_inj : Function.Injective bridge := by
        intro i j hij
        by_cases hiL : i.1 < r_L + 1
        · by_cases hjL : j.1 < r_L + 1
          · simp only [bridge, dif_pos hiL, dif_pos hjL] at hij
            have hv := congrArg (fun x => x.1) (pL.injective (fL.injective hij))
            dsimp at hv
            exact Fin.ext hv
          · by_cases hjM : j.1 = r_L + 1
            · simp only [bridge, dif_pos hiL, dif_neg hjL, dif_pos hjM] at hij
              exact False.elim (hf_L.ne_ext _ hij)
            · simp only [bridge, dif_pos hiL, dif_neg hjL, dif_neg hjM] at hij
              exact False.elim (by cases f.injective hij)
        · by_cases hiM : i.1 = r_L + 1
          · by_cases hjL : j.1 < r_L + 1
            · simp only [bridge, dif_neg hiL, dif_pos hiM, dif_pos hjL] at hij
              exact False.elim (hf_L.ne_ext _ hij.symm)
            · by_cases hjM : j.1 = r_L + 1
              · exact Fin.ext (hiM.trans hjM.symm)
              · simp only [bridge, dif_neg hiL, dif_pos hiM, dif_neg hjL, dif_neg hjM] at hij
                exact False.elim (hf_R.ne_ext _ hij.symm)
          · by_cases hjL : j.1 < r_L + 1
            · simp only [bridge, dif_neg hiL, dif_neg hiM, dif_pos hjL] at hij
              exact False.elim (by cases f.injective hij)
            · by_cases hjM : j.1 = r_L + 1
              · simp only [bridge, dif_neg hiL, dif_neg hiM, dif_neg hjL, dif_pos hjM] at hij
                exact False.elim (hf_R.ne_ext _ hij)
              · simp only [bridge, dif_neg hiL, dif_neg hiM, dif_neg hjL, dif_neg hjM] at hij
                have hv := congrArg Fin.val (pR.injective (fR.injective hij))
                dsimp at hv
                exact Fin.ext (by omega)
      have hbridge_lt_compl : ∀ i j : Fin k, i.1 < j.1 →
          (Gᶜ.Adj (bridge i) (bridge j) ↔ i.1 + 1 = j.1) := by
        intro i j hij
        have hne_v : bridge i ≠ bridge j := hbridge_inj.ne (Fin.ne_of_lt hij)
        simp only [SimpleGraph.compl_adj, ne_eq, hne_v, not_false_eq_true, true_and]
        by_cases hiL : i.1 < r_L + 1
        · by_cases hjL : j.1 < r_L + 1
          · simp only [bridge, dif_pos hiL, dif_pos hjL]
            let i' : Fin (r_L + 1) := ⟨i.1, hiL⟩
            let j' : Fin (r_L + 1) := ⟨j.1, hjL⟩
            have h := pL.map_rel_iff (a := i') (b := j')
            have hne_f : fL (pL i') ≠ fL (pL j') :=
              fL.injective.ne (pL.injective.ne (Fin.ne_of_lt hij))
            simp only [comap_adj, SimpleGraph.compl_adj, ne_eq, hne_f, not_false_eq_true,
              true_and, pathGraph_adj] at h
            dsimp [i', j'] at h
            rw [h]; omega
          · by_cases hjM : j.1 = r_L + 1
            · simp only [bridge, dif_pos hiL, dif_neg hjL, dif_pos hjM]
              by_cases hsucc : i.1 + 1 = j.1
              · refine iff_of_true ?_ hsucc
                have hlast : (⟨i.1, hiL⟩ : Fin (r_L + 1)) = Fin.last r_L :=
                  Fin.ext (by dsimp; omega)
                rw [hlast, G.adj_comm]
                exact hf_L.nonadj_ext_nonspec _ hpL_last
              · refine iff_of_false ?_ hsucc
                have hlt : i.1 < r_L := by omega
                intro hnot
                exact hnot (G.symm (hf_L.adj_ext_spec _ (hpL_spec ⟨i.1, hiL⟩ hlt)))
            · simp only [bridge, dif_pos hiL, dif_neg hjL, dif_neg hjM]
              exact iff_of_false (fun hnot => hnot (hcross_lr _ _)) (by omega)
        · by_cases hiM : i.1 = r_L + 1
          · have hjL : ¬(j.1 < r_L + 1) := by omega
            have hjM : ¬(j.1 = r_L + 1) := by omega
            simp only [bridge, dif_neg hiL, dif_pos hiM, dif_neg hjL, dif_neg hjM]
            by_cases hsucc : i.1 + 1 = j.1
            · refine iff_of_true ?_ hsucc
              have hlast : (⟨k - 1 - j.1, by omega⟩ : Fin (r_R + 1)) = Fin.last r_R :=
                Fin.ext (by dsimp; omega)
              rw [hlast]
              exact hf_R.nonadj_ext_nonspec _ hpR_last
            · refine iff_of_false ?_ hsucc
              have hlt : k - 1 - j.1 < r_R := by omega
              intro hnot
              exact hnot (hf_R.adj_ext_spec _ (hpR_spec ⟨k - 1 - j.1, by omega⟩ hlt))
          · have hjL : ¬(j.1 < r_L + 1) := by omega
            have hjM : ¬(j.1 = r_L + 1) := by omega
            simp only [bridge, dif_neg hiL, dif_neg hiM, dif_neg hjL, dif_neg hjM]
            have hi_r : k - 1 - i.1 < r_R + 1 := by omega
            have hj_r : k - 1 - j.1 < r_R + 1 := by omega
            have hj_lt : j.1 < k := j.2
            have hi_lt : i.1 < k := i.2
            let i' : Fin (r_R + 1) := ⟨k - 1 - i.1, hi_r⟩
            let j' : Fin (r_R + 1) := ⟨k - 1 - j.1, hj_r⟩
            have hne_idx : i' ≠ j' := fun heq => by
              have hv : k - 1 - i.1 = k - 1 - j.1 := congrArg Fin.val heq
              omega
            have hne_f : fR (pR i') ≠ fR (pR j') := fR.injective.ne (pR.injective.ne hne_idx)
            have h := pR.map_rel_iff (a := i') (b := j')
            simp only [comap_adj, SimpleGraph.compl_adj, ne_eq, hne_f, not_false_eq_true,
              true_and, pathGraph_adj] at h
            rw [h]
            change ((k - 1 - i.1) + 1 = k - 1 - j.1 ∨ (k - 1 - j.1) + 1 = k - 1 - i.1) ↔ i.1 + 1 = j.1
            omega
      refine hfree ⟨⟨bridge, hbridge_inj⟩, ?_⟩
      ext i j
      change (pathGraph k)ᶜ.Adj i j ↔ G.Adj (bridge i) (bridge j)
      by_cases hij : i = j
      · subst hij; simp
      · have hne_b : bridge i ≠ bridge j := hbridge_inj.ne hij
        have hcompl_iff : Gᶜ.Adj (bridge i) (bridge j) ↔ (pathGraph k).Adj i j := by
          rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hgt
          · rw [hbridge_lt_compl i j hlt, pathGraph_adj]; omega
          · rw [Gᶜ.adj_comm, hbridge_lt_compl j i hgt, pathGraph_adj]; omega
        simp only [SimpleGraph.compl_adj, ne_eq, hij, hne_b, not_false_eq_true, true_and] at hcompl_iff ⊢
        exact ⟨fun hnA => by_contra fun hnB => hnA (hcompl_iff.mp hnB),
          fun hB hA => hcompl_iff.mpr hA hB⟩

/-! ### Section 5: Theorem 9(1) — All Finite Paths, Linear Forests, Brooms, Double Brooms, Hooked-Claw Pairs, and Forest Pairs -/

/-- Stage-1 comb dichotomy for `pathGraph k` (`k ≥ 6`) at $s = 1$, $L_{\max} = \ell \ge 64$, and
$p_{\mathrm{cap}} = \lceil x^{-2}\rceil$ (`Theorem 7(2)` of `main.tex`). -/
theorem stage1_comb_dichotomy_for_paths_tp {V : Type} [Fintype V] [DecidableEq V]
    {F : SimpleGraph V} {S : Finset V} {k ℓ : ℕ} {x y w : ℝ}
    {a : Fin ℓ → V} {B : Fin ℓ → Finset V} {v : V}
    (hk : 6 ≤ k)
    (hx_pos : 0 < x) (hxy : x ≤ y) (hy_ub : y ≤ (2 : ℝ)⁻¹ ^ 16)
    (hℓ_64 : 64 ≤ ℓ) (hℓ_high : (ℓ : ℝ) ≤ x⁻¹)
    (hfree : IsInducedSubgraphFree F (PkCompl k))
    (hcomb : IsCombIn F S ℓ w a B)
    (hv : IsCombExternalApex F S ℓ a B v)
    (hw_ge_S : (S.card : ℝ) / (ℓ : ℝ) ^ 18 ≤ w) :
    let p_cap := ⌈x ^ (-2 : ℝ)⌉₊
    ∃ k' : ℕ, ℓ ≤ k' ∧ k' ≤ p_cap ∧
      ∃ U : Fin k' → Finset V,
        IsWeaklySparseOrCoSparseBlockadeIn F S k'
          ((S.card : ℝ) / (k' : ℝ) ^ (pathCombExpC k)) x U := by
  intro p_cap
  let r := k - 5
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
  let C := pathCombExpC k
  have hC_eq : C = 3 * capExpE r + 4 * splitTreeD r + 100 := rfl
  by_cases hw_min : combMinWidth r x p_cap ≤ w
  · have hstems := hasPerHandleApexStems_one_of_isCombExternalApex hv
    have hfree_r : IsInducedSubgraphFree F (PkCompl (1 + 4 + r)) := by
      rwa [show 1 + 4 + r = k by omega]
    have hU_sub_S : Finset.univ.biUnion B ⊆ S :=
      Finset.biUnion_subset.mpr (fun i _ => hcomb.is_blockade.subset_ambient i)
    rcases stage1_comb_cocomb_dichotomy_all_r r hr hr V F S 1 ℓ p_cap ℓ x w a B (fun _ _ => v)
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
        ErdosHajnalGen.rpow_neg_natCast (by norm_num) (200 * r ^ 2), ← inv_pow,
        show -(capExpE r : ℝ) = -(((capExpE r : ℕ) : ℝ)) by rfl,
        ErdosHajnalGen.rpow_neg_natCast (le_of_lt hp_pos) (capExpE r), ← inv_pow]
      have h2_p : (p_cap : ℝ)⁻¹ ^ (35 * r ^ 2) ≤ (2 : ℝ)⁻¹ ^ (200 * r ^ 2) := by
        have h64 : (p_cap : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ ^ 6 := by
          have : (2 : ℝ) ^ 6 ≤ (p_cap : ℝ) := by norm_num at hp_r ⊢; exact hp_r
          rw [inv_pow]
          exact inv_anti₀ (by positivity) this
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
        ErdosHajnalGen.rpow_neg_natCast (le_of_lt hx_pos) (3 * r), ← inv_pow] at hw_min
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

/-- Co-sparse complete trigger peeling for $\overline{P_t}$-free graphs ($t \ge 2$, `Lemma 2` of `main.tex`). -/
theorem path_cosparse_peel_tp (t : ℕ) (ht : 2 ≤ t)
    (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (F' : Finset V) (y : ℝ)
    (hG₁ : IsInducedSubgraphFree G (pathGraph t)ᶜ)
    (hy0 : 0 < y) (hy_le : y ≤ (2 : ℝ) ^ (-4 * (3 * (t : ℝ))))
    (hy_F' : 1 ≤ y ^ ((6 : ℝ) + 2) * (F'.card : ℝ))
    (h_cosparse : IsEpsSparseOn Gᶜ F' (y ^ 3)) :
    (∃ U ⊆ F', IsEpsRestrictedOn G U (y ^ 4) ∧
      y ^ (6 : ℝ) * (F'.card : ℝ) ≤ (U.card : ℝ)) ∨
    (∃ X ⊆ F', ∃ Y ⊆ F', Disjoint X Y ∧
      y ^ (6 : ℝ) * (F'.card : ℝ) ≤ (X.card : ℝ) ∧
      (1 - (3 * (t : ℝ)) * y) * (F'.card : ℝ) ≤ (Y.card : ℝ) ∧
      IsCompletePair G X Y) := by
  right
  have hy_le1 : y ≤ 1 := by
    have h1 : (2 : ℝ) ^ (-4 * (3 * (t : ℝ))) ≤ (2 : ℝ) ^ (-24 : ℝ) := by
      have : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
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
  have hcosparse_y : IsEpsSparseOn Gᶜ F' y := h_cosparse.mono (by nlinarith [sq_nonneg y])
  obtain ⟨X, hXF', Y, hYF', hdisj, hX_card, hY_card, hcomp⟩ :=
    pkCompl_free_cosparse_trigger_pair G F' t y ht hG₁ hy0 hy_le_t hy2_F' hcosparse_y
  refine ⟨X, hXF', Y, hYF', hdisj, ?_, hY_card, hcomp⟩
  have hy6_le_y2 : y ^ (6 : ℝ) ≤ y ^ 2 := by
    rw [← Real.rpow_natCast y 2]
    exact Real.rpow_le_rpow_of_exponent_ge hy0 hy_le1 (by norm_num)
  exact (mul_le_mul_of_nonneg_right hy6_le_y2 (Nat.cast_nonneg _)).trans hX_card

/-- Explicit constants $(c_1, \dots, c_9)$ certifying `SatisfiesPairCoupledGenNiceAt (pathGraph k) (pathGraph k)`
for every $k \ge 6$ via `Lemma 7(1)` (`Theorem 7(2)` of `main.tex`). -/
theorem exists_satisfiesPairCoupledGenNiceAt_pathGraph_tp (k : ℕ) (hk : 6 ≤ k) :
    ∃ (c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ : ℝ),
      4 ≤ c₂ ∧ 1 ≤ c₆ ∧ 1 ≤ c₇ ∧ c₇ ≤ 3 * c₂ ∧
      SatisfiesPairCoupledGenNiceAt (pathGraph k) (pathGraph k)
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ := by
  have hk2 : 2 ≤ k := by omega
  have hh₁ : 2 ≤ Fintype.card (Fin k) := by rw [Fintype.card_fin]; exact hk2
  have hb_leaf : 6 ≤ 3 * (k : ℝ) := by
    have : (6 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  let C_comb : ℝ := (pathCombExpC k : ℝ)
  have hC_comb : 18 ≤ C_comb := by
    dsimp [C_comb, pathCombExpC]
    exact_mod_cast (by omega : 18 ≤ 3 * capExpE (k - 5) + 4 * splitTreeD (k - 5) + 100)
  have hGN := pair_coupled_generalized_nice_of_comb_dichotomy_explicit
    (pathGraph k) (pathGraph k) hh₁
    6 (3 * (k : ℝ)) C_comb 2 1 1
    le_rfl hb_leaf hC_comb le_rfl zero_lt_one zero_lt_one
    (fun V _ _ G F' y hG₁ _ => path_cosparse_peel_tp k hk2 V G F' y hG₁)
    (fun V _ _ G F' x y ℓ a B v hG₁ _ hx_pos hxy hy_ub hℓ_lo hℓ_hi hℓ_64 hcomb hapex => by
      right
      have hy0 : 0 < y := hx_pos.trans_le hxy
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
      have hw_ge_S : (F'.card : ℝ) / (ℓ : ℝ) ^ 18 ≤ y ^ 4 * (F'.card : ℝ) / (ℓ : ℝ) ^ 2 := by
        calc (F'.card : ℝ) / (ℓ : ℝ) ^ 18
          _ = ((ℓ : ℝ) ^ 16)⁻¹ * ((F'.card : ℝ) / (ℓ : ℝ) ^ 2) := by
              rw [show (18 : ℕ) = 2 + 16 by rfl, pow_add, ← div_div, div_eq_inv_mul]
          _ ≤ y ^ 4 * ((F'.card : ℝ) / (ℓ : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_right hℓ16_inv_le_y4 (by positivity)
          _ = y ^ 4 * (F'.card : ℝ) / (ℓ : ℝ) ^ 2 := (mul_div_assoc _ _ _).symm
      obtain ⟨k', hℓ_k', hk'_p, U, hU⟩ :=
        stage1_comb_dichotomy_for_paths_tp hk hx_pos hxy hy_ub hℓ_64 hℓ_hi hG₁ hcomb hapex hw_ge_S
      have hk'2 : 2 ≤ k' := by omega
      have hk'_lo : (1 / 2 : ℝ) * (ℓ : ℝ) ^ (1 : ℝ) ≤ (k' : ℝ) := by
        rw [Real.rpow_one]
        have : (ℓ : ℝ) ≤ (k' : ℝ) := by exact_mod_cast hℓ_k'
        linarith
      refine ⟨k', hk'2, hk'_lo, hk'_p, U, Or.inr ?_⟩
      dsimp [C_comb]
      rw [Real.rpow_natCast]
      exact hU)
  dsimp only at hGN
  set δ := symmRodlDeltaGen (Fintype.card (Fin k)) (lambda0Param (2 * (3 * (k : ℝ))))
  set d := symmGenNiceD 6 (3 * (k : ℝ)) C_comb 1 δ
  have hd120 : 120 ≤ d := one_hundred_twenty_le_symmGenNiceD 6 (3 * (k : ℝ)) C_comb 1 δ
  exact ⟨_, d, _, _, _, 2, 6, _, _, by linarith, by norm_num, by norm_num, by linarith, hGN⟩

/-- Inductive step from $P_m \in \mathcal{EH}$ ($m \ge 5$) and `IsThresholdedWonderful (pathGraph (m + 1))`
to $P_{m+1}, \overline{P_{m+1}} \in \mathcal{EH}$ (`Lemma 7(2)` of `main.tex`). -/
theorem hasErdosHajnalProp_pathGraph_succ_tp {m : ℕ} (hm : 5 ≤ m)
    (h_prev : HasErdosHajnalProp (pathGraph m))
    (h_wond : IsThresholdedWonderful (pathGraph (m + 1))) :
    HasErdosHajnalProp (pathGraph (m + 1))ᶜ ∧ HasErdosHajnalProp (pathGraph (m + 1)) := by
  let v₀ : Fin (m + 1) := Fin.last m
  let u₀ : Fin (m + 1) := ⟨m - 1, by omega⟩
  have hu₀_ne : u₀ ≠ v₀ := by simp [u₀, v₀, Fin.ext_iff]; omega
  have hleaf : ∀ w : Fin (m + 1), (pathGraph (m + 1)).Adj v₀ w ↔ w = u₀ := by
    intro w
    simp only [pathGraph_adj, v₀, u₀, Fin.val_last, Fin.ext_iff]
    have hw := w.2
    omega
  have hh : 3 ≤ Fintype.card (Fin (m + 1)) := by rw [Fintype.card_fin]; omega
  have hcast : (pathGraph (m + 1)).comap (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)) = pathGraph m := by
    ext a b; simp [pathGraph_adj]
  have e_sub : (pathGraph (m + 1)).comap (Subtype.val : {w : Fin (m + 1) // w ≠ v₀} → Fin (m + 1)) ≃g
      pathGraph m :=
    hcast ▸ comapSubtypeNeLastIso m (pathGraph (m + 1))
  have h_prev_compl_eh : HasErdosHajnalProp ((pathGraph (m + 1)).comap
      (Subtype.val : {w : Fin (m + 1) // w ≠ v₀} → Fin (m + 1)))ᶜ :=
    hasErdosHajnalProp_of_iso (complIsoTp e_sub).symm h_prev.compl
  haveI : Nonempty {w : Fin (m + 1) // w ≠ v₀} := ⟨⟨u₀, hu₀_ne⟩⟩
  have hviral : IsViral ((pathGraph (m + 1)).comap
      (Subtype.val : {w : Fin (m + 1) // w ≠ v₀} → Fin (m + 1)))ᶜ :=
    isViral_of_hasErdosHajnalProp h_prev_compl_eh
  obtain ⟨c₁, c₂, c₃, c₄, c₅, c₆, c₇, c₈, c₉, hc₂4, hc₆1, hc₇1, hc₇_le, hGN⟩ :=
    exists_satisfiesPairCoupledGenNiceAt_pathGraph_tp (m + 1) (by omega)
  exact master_stage2_eh_of_coupled_gen_nice_and_wonderful
    (pathGraph (m + 1)) v₀ u₀ hu₀_ne hleaf hh hviral h_wond hc₂4 hc₆1 hc₇1 hc₇_le hGN

/-- **Unconditional Single-Graph Erdős–Hajnal Property for Every Finite Path $P_k$ (`pathGraph k`, $k \ge 1$,
`Theorem 9(1)` of `main.tex`)**. -/
theorem hasErdosHajnalProp_pathGraph_all : ∀ k : ℕ, 1 ≤ k → HasErdosHajnalProp (pathGraph k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk1
    by_cases hk9 : k ≤ 9
    · exact (P9Baseline.main_theorem_A_paths_le_9 k hk1 hk9).1
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      have hm6 : 6 ≤ m + 1 := by omega
      have h_prev : HasErdosHajnalProp (pathGraph m) := ih m (Nat.lt_succ_self m) (by omega)
      have h_wond : IsThresholdedWonderful (pathGraph (m + 1)) :=
        (isThresholdedWonderful_Pk_of_prev (m + 1) hm6 h_prev).2
      exact (hasErdosHajnalProp_pathGraph_succ_tp (by omega) h_prev h_wond).2

/-- **Main Theorem (A.1) — Full Equivalence Statement (`HasErdosHajnalProp`, `HasPolyRodlProp`, and
`IsViral`) for All Finite Paths $P_k$ and Co-Paths $\overline{P_k}$ ($k \ge 1$, `Theorem 9(1)` of `main.tex`)**. -/
theorem hasErdosHajnalProp_all_paths :
    ∀ k : ℕ, 1 ≤ k →
      HasErdosHajnalProp (pathGraph k) ∧
      HasErdosHajnalProp (pathGraph k)ᶜ ∧
      HasPolyRodlProp (pathGraph k) ∧
      HasPolyRodlProp (pathGraph k)ᶜ ∧
      IsViral (pathGraph k) ∧
      IsViral (pathGraph k)ᶜ := by
  intro k hk1
  have h_eh := hasErdosHajnalProp_pathGraph_all k hk1
  have h_eh_c := h_eh.compl
  haveI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  have h_equiv := eh_iff_polyRodl_iff_isViral (pathGraph k)
  have h_equiv_c := eh_iff_polyRodl_iff_isViral (pathGraph k)ᶜ
  have h_rodl := h_equiv.1.mp h_eh
  have h_rodl_c := h_equiv_c.1.mp h_eh_c
  have h_viral := h_equiv.2.mp h_rodl
  have h_viral_c := h_equiv_c.2.mp h_rodl_c
  exact ⟨h_eh, h_eh_c, h_rodl, h_rodl_c, h_viral, h_viral_c⟩

/-- **Unconditional Proposition 8(1) (`isThresholdedWonderful_Pk`)**:
Every singleton path `pathGraph k` ($k \ge 6$) is unconditionally thresholded wonderful. -/
theorem isThresholdedWonderful_Pk :
    ∀ k : ℕ, 6 ≤ k → IsThresholdedWonderful (pathGraph k) := by
  intro k hk
  exact (isThresholdedWonderful_Pk_of_prev k hk (hasErdosHajnalProp_pathGraph_all (k - 1) (by omega))).2

/-- **Main Theorem (B)(1)–(2) for All Finite Paths $P_k$ ($k \ge 6$)**:
Unconditional leaf-reducibility, coupled generalized niceness, and thresholded wonderfulness
across all `pathGraph k` ($k \ge 6$). -/
theorem main_theorem_B_paths_all_k :
    ∀ k : ℕ, 6 ≤ k →
      (∃ v₀ : Fin k, (neighborFinsetIn (pathGraph k) v₀ Finset.univ).card ≤ 1 ∧
        HasErdosHajnalProp ((pathGraph k).comap (Subtype.val : {v : Fin k // v ≠ v₀} → Fin k))) ∧
      IsCoupledGeneralizedNice (pathGraph k) ∧
      IsCoupledGeneralizedNice (pathGraph k)ᶜ ∧
      IsThresholdedWonderful (pathGraph k) := by
  intro k hk
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hGN := P9Baseline.main_theorem_B_stage1_generalized_nice_all_paths (m + 1) hk
  refine ⟨⟨Fin.last m, ?_, ?_⟩, hGN.1, hGN.2, isThresholdedWonderful_Pk (m + 1) hk⟩
  · have hsub : neighborFinsetIn (pathGraph (m + 1)) (Fin.last m) Finset.univ ⊆ {⟨m - 1, by omega⟩} := by
      intro w hw
      rw [mem_neighborFinsetIn] at hw
      rw [Finset.mem_singleton, Fin.ext_iff]
      simp only [pathGraph_adj, Fin.val_last] at hw
      have hw_lt := w.2
      dsimp only
      omega
    exact (Finset.card_le_card hsub).trans (by simp)
  · have hcast : (pathGraph (m + 1)).comap (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)) = pathGraph m := by
      ext a b; simp [pathGraph_adj]
    have e_sub : (pathGraph (m + 1)).comap (Subtype.val : {v : Fin (m + 1) // v ≠ Fin.last m} → Fin (m + 1)) ≃g
        pathGraph m :=
      hcast ▸ comapSubtypeNeLastIso m (pathGraph (m + 1))
    exact hasErdosHajnalProp_of_iso e_sub.symm (hasErdosHajnalProp_pathGraph_all m (by omega))

/-- **Main Theorem (A.1) — Universal Statement for All Finite Paths $P_k$ (`erdos_hajnal_all_paths_proof`)**. -/
theorem erdos_hajnal_all_paths_proof :
    ∀ k : ℕ, 1 ≤ k →
      ∃ c > (0 : ℝ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
        IsInducedSubgraphFree G (pathGraph k) →
          (G.cliqueNum : ℝ) ≥ (n : ℝ) ^ c ∨ (G.indepNum : ℝ) ≥ (n : ℝ) ^ c := by
  intro k hk1
  obtain ⟨c₀, hc₀, hprop⟩ := hasErdosHajnalProp_pathGraph_all k hk1
  obtain ⟨c, hc, h1, _, _⟩ := erdos_hajnal_all_n_of_large_n (pathGraph k) (le_refl 2) hc₀
    (fun n _ G hG => by simpa using hprop (Fin n) G hG)
  exact ⟨c, hc, h1⟩

/-- **Erdős Problem 61 (`FormalConjectures` Asymptotic Variant for All Finite Paths $P_k$, $k \ge 1$)**. -/
theorem erdos_61_variants_all_paths_proof :
    ∀ k : ℕ, 1 ≤ k →
      ∃ c > (0 : ℝ), _root_.Erdos61.IsErdosHajnalLowerBound (pathGraph k) (fun n : ℕ => (n : ℝ) ^ c) := by
  intro k hk1
  obtain ⟨c₀, hc₀, hprop⟩ := hasErdosHajnalProp_pathGraph_all k hk1
  obtain ⟨c, hc, _, h2, _⟩ := erdos_hajnal_all_n_of_large_n (pathGraph k) (le_refl 2) hc₀
    (fun n _ G hG => by simpa using hprop (Fin n) G hG)
  exact ⟨c, hc, h2⟩

/-- Recursive path length `linearForestAmbientLen ks ≥ 1` into which `LinearForestGraph ks` embeds
as an induced subgraph. -/
def linearForestAmbientLen : List ℕ → ℕ
  | [] => 1
  | k :: ks => (k + 1) + linearForestAmbientLen ks

theorem linearForestAmbientLen_pos (ks : List ℕ) : 1 ≤ linearForestAmbientLen ks := by
  induction ks with
  | nil => decide
  | cons k ks ih => dsimp [linearForestAmbientLen]; omega

/-- Explicit induced graph embedding `LinearForestGraph ks ↪g pathGraph (linearForestAmbientLen ks)`. -/
def linearForestEmbedPathGraph (ks : List ℕ) :
    LinearForestGraph ks ↪g pathGraph (linearForestAmbientLen ks) := by
  induction ks with
  | nil =>
    exact { toEmbedding := ⟨fun x => x.1.elim0, fun x => x.1.elim0⟩
            map_rel_iff' := fun {a _} => a.1.elim0 }
  | cons k ks ih =>
    let f : LinearForestVert (k :: ks) → Fin ((k + 1) + linearForestAmbientLen ks) :=
      fun ⟨i, y⟩ =>
        Fin.cases
          (motive := fun i : Fin (ks.length + 1) =>
            Fin ((k :: ks).get i) → Fin ((k + 1) + linearForestAmbientLen ks))
          (fun y₀ => ⟨y₀.1, by have hy₀ : y₀.1 < k := y₀.2; omega⟩)
          (fun j yₛ => ⟨(k + 1) + (ih ⟨j, yₛ⟩).1, by omega⟩)
          i y
    refine { toEmbedding := ⟨f, ?_⟩, map_rel_iff' := ?_ }
    · intro ⟨i₁, y₁⟩ ⟨i₂, y₂⟩ hab
      revert y₁
      refine Fin.cases ?_ ?_ i₁
      · intro y₁; revert y₂
        refine Fin.cases ?_ ?_ i₂
        · intro y₂ hab
          have hv := congrArg (fun x => x.1) hab
          dsimp [f] at hv
          exact Sigma.ext rfl (heq_of_eq (Fin.ext hv))
        · intro j₂ y₂ hab
          have hv : y₁.1 = (k + 1) + (ih ⟨j₂, y₂⟩).1 := congrArg Fin.val hab
          have hy₁ : y₁.1 < k := y₁.2
          omega
      · intro j₁ y₁; revert y₂
        refine Fin.cases ?_ ?_ i₂
        · intro y₂ hab
          have hv : (k + 1) + (ih ⟨j₁, y₁⟩).1 = y₂.1 := congrArg Fin.val hab
          have hy₂ : y₂.1 < k := y₂.2
          omega
        · intro j₂ y₂ hab
          have hv : (k + 1) + (ih ⟨j₁, y₁⟩).1 = (k + 1) + (ih ⟨j₂, y₂⟩).1 :=
            congrArg Fin.val hab
          have h_inj := ih.injective (Fin.ext (by omega : (ih ⟨j₁, y₁⟩).1 = (ih ⟨j₂, y₂⟩).1))
          have hj : j₁ = j₂ := congrArg Sigma.fst h_inj
          subst hj
          have hy : y₁ = y₂ := eq_of_heq (Sigma.ext_iff.mp h_inj).2
          subst hy
          rfl
    · intro ⟨i₁, y₁⟩ ⟨i₂, y₂⟩
      revert y₁
      refine Fin.cases ?_ ?_ i₁
      · intro y₁; revert y₂
        refine Fin.cases ?_ ?_ i₂
        · intro y₂
          simp [f, LinearForestGraph, pathGraph_adj]
        · intro j₂ y₂
          have hne : (0 : Fin (ks.length + 1)) ≠ j₂.succ := (Fin.succ_ne_zero j₂).symm
          simp only [f, LinearForestGraph, hne, false_and, iff_false, pathGraph_adj]
          have hy₁ : y₁.1 < k := y₁.2
          dsimp
          omega
      · intro j₁ y₁; revert y₂
        refine Fin.cases ?_ ?_ i₂
        · intro y₂
          simp only [f, LinearForestGraph, Fin.succ_ne_zero, false_and, iff_false, pathGraph_adj]
          have hy₂ : y₂.1 < k := y₂.2
          dsimp
          omega
        · intro j₂ y₂
          have hg := ih.map_rel_iff (a := ⟨j₁, y₁⟩) (b := ⟨j₂, y₂⟩)
          simp only [f, LinearForestGraph, Fin.succ_inj, pathGraph_adj] at hg ⊢
          dsimp at hg ⊢
          omega

/-- Every empty graph `⊥ : SimpleGraph (Fin m)` satisfies `HasErdosHajnalProp`. -/
theorem hasErdosHajnalProp_bot_fin_all (m : ℕ) :
    HasErdosHajnalProp (⊥ : SimpleGraph (Fin m)) := by
  have hm1 : 1 ≤ max (2 * m) 1 := Nat.le_max_right _ _
  have hpath := hasErdosHajnalProp_pathGraph_all (max (2 * m) 1) hm1
  have emb : (⊥ : SimpleGraph (Fin m)) ↪g pathGraph (max (2 * m) 1) :=
    (botFinEmbedPathGraph m).trans (pathGraph_mono_emb_tp (Nat.le_max_left _ _))
  exact hasErdosHajnalProp_of_embedding_tp emb hpath

/-- **Main Theorem (A.2)–(A.3) (`main_theorem_A2_linear_forests_and_brooms_proof`, Theorem 9(1) of `main.tex`)**:
Every non-empty linear forest `LinearForestGraph ks` ($1 \le \text{ks.length}$, $\forall k \in \text{ks}, 1 \le k$),
every $(s, d)$-broom `BroomGraph s d` ($s, d \ge 1$, explicitly including $B(2, 2) = P_4[v_1 \leftarrow \overline{K_2}]$),
and every double broom `DoubleBroomGraph a d b` ($a, d, b \ge 1$), together with all of their complements,
unconditionally satisfy `HasErdosHajnalProp`, `HasPolyRodlProp`, and `IsViral`. -/
theorem main_theorem_A2_linear_forests_and_brooms_proof :
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
      IsViral (DoubleBroomGraph a d b)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ks hlen hpos
    have h_eh : HasErdosHajnalProp (LinearForestGraph ks) :=
      hasErdosHajnalProp_of_embedding_tp (linearForestEmbedPathGraph ks)
        (hasErdosHajnalProp_pathGraph_all (linearForestAmbientLen ks) (linearForestAmbientLen_pos ks))
    have hk0 : 1 ≤ ks.get ⟨0, hlen⟩ := hpos _ (List.get_mem ks ⟨0, hlen⟩)
    haveI : Nonempty (LinearForestVert ks) := ⟨⟨⟨0, hlen⟩, ⟨0, hk0⟩⟩⟩
    have h_equiv := eh_iff_polyRodl_iff_isViral (LinearForestGraph ks)
    have h_rodl := h_equiv.1.mp h_eh
    exact ⟨h_eh, h_eh.compl, h_rodl, h_equiv.2.mp h_rodl⟩
  · intro s d hs hd
    have h_eh : HasErdosHajnalProp (BroomGraph s d) :=
      hasErdosHajnalProp_substGraph_tp (pathGraph (d + 2)) 0 (⊥ : SimpleGraph (Fin s))
        (hasErdosHajnalProp_pathGraph_all (d + 2) (by omega))
        (hasErdosHajnalProp_bot_fin_all s)
    haveI : Nonempty ({v : Fin (d + 2) // v ≠ 0} ⊕ Fin s) := ⟨Sum.inr ⟨0, hs⟩⟩
    have h_equiv := eh_iff_polyRodl_iff_isViral (BroomGraph s d)
    have h_rodl := h_equiv.1.mp h_eh
    exact ⟨h_eh, h_eh.compl, h_rodl, h_equiv.2.mp h_rodl⟩
  · intro a d b ha hd hb
    have h_step1 := hasErdosHajnalProp_substGraph_tp (pathGraph (d + 3)) 0 (⊥ : SimpleGraph (Fin a))
      (hasErdosHajnalProp_pathGraph_all (d + 3) (by omega))
      (hasErdosHajnalProp_bot_fin_all a)
    have h_eh : HasErdosHajnalProp (DoubleBroomGraph a d b) :=
      hasErdosHajnalProp_substGraph_tp _ (doubleBroomRightEnd a d) (⊥ : SimpleGraph (Fin b))
        h_step1 (hasErdosHajnalProp_bot_fin_all b)
    haveI : Nonempty ({v : {v : Fin (d + 3) // v ≠ 0} ⊕ Fin a // v ≠ doubleBroomRightEnd a d} ⊕ Fin b) :=
      ⟨Sum.inr ⟨0, hb⟩⟩
    have h_equiv := eh_iff_polyRodl_iff_isViral (DoubleBroomGraph a d b)
    have h_rodl := h_equiv.1.mp h_eh
    exact ⟨h_eh, h_eh.compl, h_rodl, h_equiv.2.mp h_rodl⟩

/-- **Hooked-Claw Pairs for All Finite Paths $P_t$ (`pair_Pt_Hook4_eh_all_t`, `Theorem 9(3)` of `main.tex`)**:
For every non-empty finite graph $Q \in \mathcal{EH}$, every subset $S \subseteq V(Q)$, and **every integer
$t \ge 1$**, both $\{P_t, \operatorname{Hook}_4(Q, S)\}$ and $\{\overline{P_t}, \overline{\operatorname{Hook}_4(Q, S)}\}$
satisfy `HasPairErdosHajnalProp`, `HasPairPolyRodlProp`, and `IsPairViral`. -/
theorem pair_Pt_Hook4_eh_all_t :
    ∀ (W : Type) [Fintype W] [DecidableEq W] (Q : SimpleGraph W) (S : Set W),
      HasErdosHajnalProp Q → 1 ≤ Fintype.card W →
        ∀ t : ℕ, 1 ≤ t →
          HasPairErdosHajnalProp (pathGraph t) (Hook4Graph Q S) ∧
          HasPairErdosHajnalProp (pathGraph t)ᶜ (Hook4Graph Q S)ᶜ ∧
          HasPairPolyRodlProp (pathGraph t) (Hook4Graph Q S) ∧
          IsPairViral (pathGraph t) (Hook4Graph Q S) := by
  intro W _ _ Q S _hEH _hcard t ht1
  obtain ⟨⟨c, hc, heh⟩, ⟨c', hc', heh_c⟩, ⟨d, hd, hrodl⟩, _, hv, _⟩ :=
    hasErdosHajnalProp_all_paths t ht1
  exact ⟨⟨c, hc, fun V _ _ G hG₁ _ => heh V G hG₁⟩,
    ⟨c', hc', fun V _ _ G hG₁ _ => heh_c V G hG₁⟩,
    ⟨d, hd, fun V _ _ G ε hε0 hε1 hG₁ _ => hrodl V G ε hε0 hε1 hG₁⟩,
    isPairViral_of_isViral_left (Hook4Graph Q S) hv⟩

/-- **Opposite-Chirality Forest Pairs (`opposite_chirality_forest_pairs_eh`, `Theorem 9(3)` of `main.tex`)**:
For all non-empty finite forests $F_1, F_2$, the pair $\{F_1, \overline{F_2}\}$ satisfies
`HasPairErdosHajnalProp`, `HasPairPolyRodlProp`, and `IsPairViral`. -/
theorem opposite_chirality_forest_pairs_eh :
    ∀ (W₁ W₂ : Type) [Fintype W₁] [DecidableEq W₁] [Nonempty W₁]
      [Fintype W₂] [DecidableEq W₂] [Nonempty W₂]
      (F₁ : SimpleGraph W₁) (F₂ : SimpleGraph W₂),
      F₁.IsAcyclic → F₂.IsAcyclic →
        HasPairErdosHajnalProp F₁ F₂ᶜ ∧ HasPairPolyRodlProp F₁ F₂ᶜ ∧ IsPairViral F₁ F₂ᶜ :=
  P9Baseline.main_theorem_C1_forest_pairs_and_closures.2.1

/-- Direct projection alias for Proposition 8(1):
`∀ k : ℕ, 6 ≤ k → HasErdosHajnalProp (pathGraph (k - 1)) → IsThresholdedWonderful (pathGraph k)`. -/
theorem isThresholdedWonderful_Pk_cond :
    ∀ k : ℕ, 6 ≤ k → HasErdosHajnalProp (pathGraph (k - 1)) → IsThresholdedWonderful (pathGraph k) :=
  fun k hk h => (isThresholdedWonderful_Pk_of_prev k hk h).2

/-- Direct re-export alias for Theorem 7(1):
`∀ r : ℕ, 1 ≤ r → Stage1CombCoCombDichotomyAt r`. -/
theorem stage1_comb_cocomb_dichotomy_all_r_proof :
    ∀ r : ℕ, 1 ≤ r → Stage1CombCoCombDichotomyAt r :=
  stage1_comb_cocomb_dichotomy_all_r

/-! ### Axiom Verification Checks -/

#print axioms terminal_path_arm_dichotomy
#print axioms pendant_p3_open_interval_lifting
#print axioms isThresholdedWonderful_Pk_of_prev
#print axioms isThresholdedWonderful_Pk_cond
#print axioms isThresholdedWonderful_Pk
#print axioms stage1_comb_cocomb_dichotomy_all_r_proof
#print axioms hasErdosHajnalProp_all_paths
#print axioms erdos_hajnal_all_paths_proof
#print axioms erdos_61_variants_all_paths_proof
#print axioms main_theorem_A2_linear_forests_and_brooms_proof
#print axioms pair_Pt_Hook4_eh_all_t
#print axioms opposite_chirality_forest_pairs_eh

end ErdosHajnalGen
