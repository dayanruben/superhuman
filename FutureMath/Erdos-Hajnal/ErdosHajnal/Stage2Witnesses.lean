/-
Copyright 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosHajnal.BasicLemmas
import ErdosHajnal.Defs
import ErdosHajnal.GenDefs
import ErdosHajnal.P6Baseline
import ErdosHajnal.WitnessGraph

/-!
# Explicit Pure-Substitution Stage-2 Witnesses $(H_{(7)}, H^{(8)}, H^{(9)})$ and Caterpillar Reduction $T_k$
(Propositions 3 and 5 of `main.tex`)

This file formalizes the Stage-2 open-interval witness machinery and all explicit witness reductions
from Propositions 3 and 5 of `main.tex`:

1. **Section 1 — General Open-Interval Witness-to-Thresholded-Wonderfulness Engine**:
   - `IsOpenIntervalRealization`: Open-interval realization of a witness pair `(W_wit, S_spec)` inside
     a host graph `G` around an external vertex `v₀ ∉ ⋃ᵢ Bᵢ` whose attachment into every block `B_{emb u}`
     lies in the open interval $0 < |N_G(v_0) \cap B_{\mathrm{emb}(u)}| < \frac{1}{2}|B_{\mathrm{emb}(u)}|$.
   - `not_isInducedSubgraphFree_of_pattern_emb` & `isInducedSubgraphFree_patternGraph_induce_of_free`:
     Sequential greedy realization showing that if `G` is `H_pat`-free and the cross-block sparsity
     satisfies $|V(H_{\mathrm{pat}})| \cdot \delta_{\mathrm{cross}} \le 1/2$, then every induced subgraph
     of `blockadePatternGraph G B` is also `H_pat`-free.
   - `exists_openIntervalRealization_of_pattern_emb`: Sequential greedy realization of `(W_wit, S_spec)`
     from an induced copy of `W_wit` in `(blockadePatternGraph G B)[I₀(v₀)]`:
     - **Step A**: For each special vertex $u \in S_{\mathrm{spec}}$, select any single neighbor
       $f(u) \in N_G(v_0) \cap B_{\mathrm{emb}(u)}$ using only $0 < |N_G(v_0) \cap B_{\mathrm{emb}(u)}|$
       (with zero degree pruning).
     - **Step B**: For each non-special vertex $u \notin S_{\mathrm{spec}}$, sequentially select
       $f(u) \in B_{\mathrm{emb}(u)} \setminus N_G(v_0)$ avoiding the sparse neighborhoods of all
       earlier non-adjacent vertices in $W_{\mathrm{wit}}$, using $|N_G(v_0) \cap B_{\mathrm{emb}(u)}| < \frac{1}{2}w$
       and $|V(W_{\mathrm{wit}})| \cdot \delta_{\mathrm{cross}} \le 1/2$.
   - `isThresholdedWonderful_of_openIntervalWitness_pair` & `isThresholdedWonderful_of_openIntervalWitness`:
     Master Stage-2 wonderfulness engine proving `IsThresholdedWonderful H` from `HasPairErdosHajnalProp Hᶜ W_wit`
     (or `HasErdosHajnalProp W_wit`) whenever every open-interval realization of `(W_wit, S_spec)` embeds `Hᶜ`.

2. **Section 2 — Proposition 3 (`hasErdosHajnalProp_witnessH7` & `isThresholdedWonderful_P7`)**:
   - The 10-vertex pure-substitution witness $H_{(7)}$ (`witnessH7 : SimpleGraph (Fin 10)`) with
     4-vertex special set $S_{\mathrm{spec}} = \{1, 2, 3, 4\}$ (`specH7 = {0, 1, 2, 3}`), obtained
     from $H_0 \cong \overline{P_6}$ ($\overline{H_0} = 1 - 2 - 5 - 7 - 3 - 4$) by 4 twin substitutions:
     $\overline{K_2} = \{1, 9\}$ (`{0, 8}`), $K_2 = \{2, 10\}$ (`{1, 9}`), $K_2 = \{3, 8\}$ (`{2, 7}`),
     and $\overline{K_2} = \{4, 6\}$ (`{3, 5}`).
   - Unconditional `HasErdosHajnalProp witnessH7` and `IsThresholdedWonderful (pathGraph 7)`.

3. **Section 3 — Proposition 5(2) (`hasErdosHajnalProp_witnessH8_of_P7` & `isThresholdedWonderful_P8_of_P7`)**:
   - The 11-vertex pure-substitution witness $H^{(8)}$ (`witnessH8 : SimpleGraph (Fin 11)`) with
     5-vertex special set $S^{(8)} = \{p_1, p_2, p_3, 2, 3\}$ (`specH8 = {0, 1, 2, 3, 4}`), obtained
     from $H_0^{(8)} \cong \overline{P_7}$ ($\overline{H_0^{(8)}} = p_1 - p_2 - p_3 - p_4 - 6 - 2 - 3$)
     by 4 twin substitutions: $\overline{K_2} = \{p_1, p_1^*\}$ (`{0, 7}`), $K_2 = \{p_2, p_2'\}$ (`{1, 8}`),
     $K_2 = \{2, 7\}$ (`{3, 9}`), and $\overline{K_2} = \{3, 5\}$ (`{4, 10}`).
   - `HasErdosHajnalProp witnessH8` and `IsThresholdedWonderful (pathGraph 8)` from `HasErdosHajnalProp (pathGraph 7)`.

4. **Section 4 — Proposition 5(3) (`hasErdosHajnalProp_witnessH9_of_P8` & `isThresholdedWonderful_P9_of_P8`)**:
   - The 20-vertex symmetric two-arm pure-substitution witness
     $H^{(9)} = K_2[1 \leftarrow \operatorname{Arm}_L, 2 \leftarrow \operatorname{Arm}_R]$
     (`witnessH9 : SimpleGraph (Fin 20)`) with 6-vertex special set
     $S^{(9)} = \{L_1, L_2, L_3, R_1, R_2, R_3\}$ (`specH9 = {0, 1, 2, 10, 11, 12}`).
   - `HasErdosHajnalProp witnessH9` and `IsThresholdedWonderful (pathGraph 9)` from
     `HasErdosHajnalProp (pathGraph 8)` and substitution closure.

5. **Section 5 — Proposition 5(1) (`caterpillarTree_isAcyclic`, `caterpillarTree_mono_embedding`, & `isThresholdedWonderful_Pk_of_caterpillar_pair`)**:
   - Acyclicity (`(CaterpillarTree k).IsAcyclic`) for all $k \in \mathbb{N}$ via an explicit parent-depth
     tree structure rooted at vertex `6` (`Sum.inr (Sum.inl 0)`).
   - Induced subgraph monotonicity `CaterpillarTree j ↪g CaterpillarTree k` for all $6 \le j \le k$.
   - Exhaustive open-interval boolean routing across $(\sigma_1, \dots, \sigma_{k-6}, \sigma_*) \in \{0, 1\}^{k-5}$
     establishing `IsThresholdedWonderful (pathGraph k)` whenever
     `HasPairErdosHajnalProp (pathGraph k) (CaterpillarTree k)` holds ($k \ge 6$).
-/

set_option linter.unusedSectionVars false

open Filter Finset SimpleGraph Real

namespace ErdosHajnalGen

open ErdosHajnalP6

/-! ### Section 1: General Open-Interval Witness-to-Thresholded-Wonderfulness Engine -/

/--
An open-interval realization of a witness graph `W_wit : SimpleGraph U` with special vertex set
`S_spec : Finset U` inside `G : SimpleGraph V` around an external vertex `v₀ : V`
(Propositions 3 and 5 of `main.tex`):
- `ne_ext`: `f : U ↪ V` embeds `U` disjointly from `v₀`;
- `adj_ext_spec`: `v₀` is adjacent in `G` (non-adjacent in `Gᶜ`) to `f u` for all `u ∈ S_spec`;
- `nonadj_ext_nonspec`: `v₀` is non-adjacent in `G` (adjacent in `Gᶜ`) to `f u` for all `u ∉ S_spec`;
- `adj_of_wit_adj`: every edge of `W_wit` is realized deterministically as an edge of `G` (non-edge of `Gᶜ`);
- `nonadj_of_wit_nonadj`: every non-edge of `W_wit` with at least one endpoint outside `S_spec` is
  realized as a non-edge of `G` (edge of `Gᶜ`).
-/
structure IsOpenIntervalRealization {U V : Type*} (W_wit : SimpleGraph U) (S_spec : Finset U)
    (G : SimpleGraph V) (v₀ : V) (f : U ↪ V) : Prop where
  ne_ext : ∀ u : U, f u ≠ v₀
  adj_ext_spec : ∀ u ∈ S_spec, G.Adj v₀ (f u)
  nonadj_ext_nonspec : ∀ u : U, u ∉ S_spec → ¬G.Adj v₀ (f u)
  adj_of_wit_adj : ∀ u₁ u₂ : U, W_wit.Adj u₁ u₂ → G.Adj (f u₁) (f u₂)
  nonadj_of_wit_nonadj : ∀ u₁ u₂ : U, u₁ ≠ u₂ → (u₁ ∉ S_spec ∨ u₂ ∉ S_spec) →
    ¬W_wit.Adj u₁ u₂ → ¬G.Adj (f u₁) (f u₂)

section GeneralEngine

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
If `emb : U ↪ Fin ℓ` embeds `W_wit` into `blockadePatternGraph G B`, any adjacent pair `(u₁, u₂)`
in `W_wit` corresponds to a $100\%$ complete block pair `(B (emb u₁), B (emb u₂))` in `G`.
-/
theorem adj_of_pattern_comap {U : Type*} {W_wit : SimpleGraph U}
    {G : SimpleGraph V} {ℓ : ℕ} {B : Fin ℓ → Finset V}
    (emb : U ↪ Fin ℓ) (hemb_adj : W_wit = (blockadePatternGraph G B).comap emb)
    {u₁ u₂ : U} (hadj : W_wit.Adj u₁ u₂)
    {x₁ x₂ : V} (hx₁ : x₁ ∈ B (emb u₁)) (hx₂ : x₂ ∈ B (emb u₂)) :
    G.Adj x₁ x₂ := by
  have hJ : (blockadePatternGraph G B).Adj (emb u₁) (emb u₂) := by
    have h := congr_arg (fun H => H.Adj u₁ u₂) hemb_adj
    exact h.mp hadj
  exact hJ.2 x₁ hx₁ x₂ hx₂

/--
If `emb : U ↪ Fin ℓ` embeds `W_wit` into `blockadePatternGraph G B` for a complete-or-`x`-sparse
blockade `B`, any distinct non-adjacent pair `(u₁, u₂)` in `W_wit` corresponds to an `x`-sparse
block pair `(B (emb u₁), B (emb u₂))` in `G`.
-/
theorem sparse_of_not_pattern_comap {U : Type*} {W_wit : SimpleGraph U}
    {G : SimpleGraph V} {S : Finset V} {ℓ : ℕ} {w x : ℝ} {B : Fin ℓ → Finset V}
    (hB : IsCompleteOrXSparseBlockadeIn G S ℓ w x B)
    (emb : U ↪ Fin ℓ) (hemb_adj : W_wit = (blockadePatternGraph G B).comap emb)
    {u₁ u₂ : U} (hne : u₁ ≠ u₂) (hnadj : ¬W_wit.Adj u₁ u₂)
    {x₁ : V} (hx₁ : x₁ ∈ B (emb u₁)) :
    ((neighborFinsetIn G x₁ (B (emb u₂))).card : ℝ) ≤ x * ((B (emb u₂)).card : ℝ) := by
  have hne_emb : emb u₁ ≠ emb u₂ := emb.injective.ne hne
  rcases hB.2 (emb u₁) (emb u₂) hne_emb with hcomp | hsparse
  · exfalso
    have hJ : (blockadePatternGraph G B).Adj (emb u₁) (emb u₂) := ⟨hne_emb, hcomp⟩
    have h := congr_arg (fun H => H.Adj u₁ u₂) hemb_adj
    exact hnadj (h.mpr hJ)
  · exact hsparse.2 x₁ hx₁

/--
**Sequential Realization of Induced Subgraphs of the Pattern Graph** (Proposition 5(1) of `main.tex`):
If `B` is an equal-sized complete-or-`δ_cross`-sparse blockade with block size `w ≥ 1`, `0 ≤ δ_cross`,
and `|U| * δ_cross ≤ 1 / 2`, then any graph `H_pat : SimpleGraph U` that embeds into
`blockadePatternGraph G B` also embeds into `G` as an induced subgraph.
-/
theorem not_isInducedSubgraphFree_of_pattern_emb
    {U : Type*} [Fintype U] [DecidableEq U] {H_pat : SimpleGraph U}
    {G : SimpleGraph V} {S : Finset V} {ℓ w : ℕ} {δ_cross : ℝ} {B : Fin ℓ → Finset V}
    (hB : IsCompleteOrXSparseBlockadeIn G S ℓ (w : ℝ) δ_cross B)
    (hw_pos : 1 ≤ w) (hw_eq : ∀ i : Fin ℓ, (B i).card = w)
    (hδ_nonneg : 0 ≤ δ_cross)
    (hδ_ub : (Fintype.card U : ℝ) * δ_cross ≤ 1 / 2)
    (emb : U ↪ Fin ℓ) (hemb_adj : H_pat = (blockadePatternGraph G B).comap emb) :
    ¬IsInducedSubgraphFree G H_pat := by
  classical
  have h_default : ∀ u : U, (B (emb u)).Nonempty := fun u => hB.1.nonempty_blocks (emb u)
  let f₀ : U → V := fun u => Classical.choose (h_default u)
  have hf₀_mem : ∀ u : U, f₀ u ∈ B (emb u) := fun u => Classical.choose_spec (h_default u)
  -- Inductively select `f u ∈ B (emb u)` for `u ∈ T` avoiding sparse neighborhoods of earlier non-neighbors.
  have h_seq : ∀ T : Finset U, ∃ f : U → V,
      (∀ u : U, f u ∈ B (emb u)) ∧
      (∀ u₁ ∈ T, ∀ u₂ ∈ T, u₁ ≠ u₂ → ¬H_pat.Adj u₁ u₂ → ¬G.Adj (f u₁) (f u₂)) := by
    intro T
    refine Finset.induction_on T ?_ ?_
    · exact ⟨f₀, hf₀_mem, fun _ hu => False.elim (Finset.notMem_empty _ hu)⟩
    · intro u₀ T hu₀_not_T ih
      rcases ih with ⟨f, hf_mem, hf_nonadj⟩
      let P : Finset U := T.filter (fun r => ¬H_pat.Adj u₀ r)
      let Bad : Finset V := P.biUnion (fun r => neighborFinsetIn G (f r) (B (emb u₀)))
      -- Since each `r ∈ P` has at most `δ_cross * w` neighbors in `B (emb u₀)` and `|P| * δ_cross ≤ 1 / 2`,
      -- the union `Bad` has size `≤ w / 2 < w = |B (emb u₀)|`.
      have hBad_card : (Bad.card : ℝ) < ((B (emb u₀)).card : ℝ) := by
        have h1 : Bad.card ≤ ∑ r ∈ P, (neighborFinsetIn G (f r) (B (emb u₀))).card :=
          Finset.card_biUnion_le
        have h1_r : (Bad.card : ℝ) ≤ ∑ r ∈ P, ((neighborFinsetIn G (f r) (B (emb u₀))).card : ℝ) := by
          exact_mod_cast h1
        have h_each : ∀ r ∈ P, ((neighborFinsetIn G (f r) (B (emb u₀))).card : ℝ) ≤ δ_cross * (w : ℝ) := by
          intro r hr
          rw [Finset.mem_filter] at hr
          have hr_ne : r ≠ u₀ := fun h => hu₀_not_T (h ▸ hr.1)
          have hnadj : ¬H_pat.Adj r u₀ := fun h => hr.2 (H_pat.symm h)
          have hsp := sparse_of_not_pattern_comap hB emb hemb_adj hr_ne hnadj (hf_mem r)
          rwa [hw_eq (emb u₀)] at hsp
        have hP_le : (P.card : ℝ) ≤ (Fintype.card U : ℝ) := by
          exact_mod_cast Finset.card_le_univ P
        have hw_r_pos : (1 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw_pos
        have h_sum : ∑ r ∈ P, ((neighborFinsetIn G (f r) (B (emb u₀))).card : ℝ) ≤ (1 / 2) * (w : ℝ) := by
          calc ∑ r ∈ P, ((neighborFinsetIn G (f r) (B (emb u₀))).card : ℝ)
              ≤ ∑ _r ∈ P, (δ_cross * (w : ℝ)) := Finset.sum_le_sum h_each
            _ = (P.card : ℝ) * (δ_cross * (w : ℝ)) := by simp [Finset.sum_const, nsmul_eq_mul]
            _ = ((P.card : ℝ) * δ_cross) * (w : ℝ) := by ring
            _ ≤ ((Fintype.card U : ℝ) * δ_cross) * (w : ℝ) := by
                refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                exact mul_le_mul_of_nonneg_right hP_le hδ_nonneg
            _ ≤ (1 / 2) * (w : ℝ) := mul_le_mul_of_nonneg_right hδ_ub (by positivity)
        rw [hw_eq (emb u₀)]
        linarith
      have h_not_sub : ¬(B (emb u₀) ⊆ Bad) := by
        intro hsub
        have hle : ((B (emb u₀)).card : ℝ) ≤ (Bad.card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
        linarith
      obtain ⟨x, hx_mem, hx_not_bad⟩ := Finset.not_subset.mp h_not_sub
      let f' : U → V := Function.update f u₀ x
      have hf'_mem : ∀ u : U, f' u ∈ B (emb u) := by
        intro u
        by_cases hu : u = u₀
        · subst hu; simpa [f'] using hx_mem
        · simpa [f', hu] using hf_mem u
      refine ⟨f', hf'_mem, ?_⟩
      intro u₁ hu₁ u₂ hu₂ hne hnadj
      rw [Finset.mem_insert] at hu₁ hu₂
      rcases hu₁ with h_eq₁ | hu₁T <;> rcases hu₂ with h_eq₂ | hu₂T
      · exact False.elim (hne (h_eq₁.trans h_eq₂.symm))
      · subst h_eq₁
        have hu₂_ne : u₂ ≠ u₁ := Ne.symm hne
        simp only [f', Function.update_self, Function.update_of_ne hu₂_ne]
        intro hadj
        apply hx_not_bad
        rw [Finset.mem_biUnion]
        refine ⟨u₂, Finset.mem_filter.mpr ⟨hu₂T, hnadj⟩, ?_⟩
        rw [mem_neighborFinsetIn]
        exact ⟨hx_mem, G.symm hadj⟩
      · subst h_eq₂
        have hu₁_ne : u₁ ≠ u₂ := hne
        simp only [f', Function.update_self, Function.update_of_ne hu₁_ne]
        intro hadj
        apply hx_not_bad
        rw [Finset.mem_biUnion]
        refine ⟨u₁, Finset.mem_filter.mpr ⟨hu₁T, fun h => hnadj (H_pat.symm h)⟩, ?_⟩
        rw [mem_neighborFinsetIn]
        exact ⟨hx_mem, hadj⟩
      · have hu₁_ne : u₁ ≠ u₀ := fun h => hu₀_not_T (h ▸ hu₁T)
        have hu₂_ne : u₂ ≠ u₀ := fun h => hu₀_not_T (h ▸ hu₂T)
        simp only [f', Function.update_of_ne hu₁_ne, Function.update_of_ne hu₂_ne]
        exact hf_nonadj u₁ hu₁T u₂ hu₂T hne hnadj
  obtain ⟨f, hf_mem, hf_nonadj⟩ := h_seq Finset.univ
  have hf_inj : Function.Injective f := by
    intro u₁ u₂ heq
    by_contra hne
    have hdisj := hB.1.pairwise_disjoint (emb u₁) (emb u₂) (emb.injective.ne hne)
    exact Finset.disjoint_left.mp hdisj (hf_mem u₁) (heq ▸ hf_mem u₂)
  let g : U ↪ V := ⟨f, hf_inj⟩
  intro hFree
  refine hFree ⟨g, ?_⟩
  ext u₁ u₂
  change H_pat.Adj u₁ u₂ ↔ G.Adj (f u₁) (f u₂)
  by_cases hne : u₁ = u₂
  · subst hne; simp
  · constructor
    · intro hadj
      exact adj_of_pattern_comap emb hemb_adj hadj (hf_mem u₁) (hf_mem u₂)
    · intro hadj
      by_contra hnadj
      exact hf_nonadj u₁ (Finset.mem_univ _) u₂ (Finset.mem_univ _) hne hnadj hadj

/--
**Pattern Graph Freeness Inheritance**:
If `G` is `H_pat`-free, `1 ≤ w`, `0 ≤ δ_cross`, and `(Fintype.card U : ℝ) * δ_cross ≤ 1 / 2`,
then for any index subset `I : Finset (Fin ℓ)`, the induced pattern subgraph
`(blockadePatternGraph G B).induce I` is also `H_pat`-free.
-/
theorem isInducedSubgraphFree_patternGraph_induce_of_free
    {U : Type*} [Fintype U] [DecidableEq U] {H_pat : SimpleGraph U}
    {G : SimpleGraph V} {S : Finset V} {ℓ w : ℕ} {δ_cross : ℝ} {B : Fin ℓ → Finset V}
    (hG : IsInducedSubgraphFree G H_pat)
    (hB : IsCompleteOrXSparseBlockadeIn G S ℓ (w : ℝ) δ_cross B)
    (hw_pos : 1 ≤ w) (hw_eq : ∀ i : Fin ℓ, (B i).card = w)
    (hδ_nonneg : 0 ≤ δ_cross)
    (hδ_ub : (Fintype.card U : ℝ) * δ_cross ≤ 1 / 2)
    (I : Finset (Fin ℓ)) :
    IsInducedSubgraphFree ((blockadePatternGraph G B).induce (I : Set (Fin ℓ))) H_pat := by
  rintro ⟨emb, hemb⟩
  let emb' : U ↪ Fin ℓ := emb.trans (Function.Embedding.subtype _)
  have hemb_adj : H_pat = (blockadePatternGraph G B).comap emb' := by
    ext u₁ u₂
    have h := congr_arg (fun H => H.Adj u₁ u₂) hemb
    simpa [emb', comap_adj] using h
  exact not_isInducedSubgraphFree_of_pattern_emb hB hw_pos hw_eq hδ_nonneg hδ_ub emb' hemb_adj hG

/--
**Sequential Open-Interval Realization Lemma** (Propositions 3 and 5(1)–(3), Steps A–B of `main.tex`):
Suppose `B` is an equal-sized complete-or-`δ_cross`-sparse blockade with block size `w`, `0 ≤ δ_cross`,
`(|U| : ℝ) * δ_cross ≤ 1 / 2`, and `v₀` is an external vertex (`∀ i, v₀ ∉ B i`).
If `emb : U ↪ Fin ℓ` embeds `W_wit` into `blockadePatternGraph G B` with image inside
`openAttachmentIndices G B v₀`, then for any special set `S_spec : Finset U`, there exists an
embedding `f : U ↪ V` satisfying `IsOpenIntervalRealization W_wit S_spec G v₀ f`.
-/
theorem exists_openIntervalRealization_of_pattern_emb
    {U : Type*} [Fintype U] [DecidableEq U]
    (W_wit : SimpleGraph U) (S_spec : Finset U)
    {G : SimpleGraph V} {S : Finset V} {ℓ w : ℕ} {δ_cross : ℝ} {B : Fin ℓ → Finset V}
    (hB : IsCompleteOrXSparseBlockadeIn G S ℓ (w : ℝ) δ_cross B)
    (hw_eq : ∀ i : Fin ℓ, (B i).card = w)
    (hδ_nonneg : 0 ≤ δ_cross)
    (hδ_ub : (Fintype.card U : ℝ) * δ_cross ≤ 1 / 2)
    (v₀ : V) (hv₀_ext : ∀ i : Fin ℓ, v₀ ∉ B i)
    (emb : U ↪ Fin ℓ)
    (hemb_mem : ∀ u : U, emb u ∈ openAttachmentIndices G B v₀)
    (hemb_adj : W_wit = (blockadePatternGraph G B).comap emb) :
    ∃ f : U ↪ V, IsOpenIntervalRealization W_wit S_spec G v₀ f := by
  classical
  -- Step A (Single-Vertex Selection on `S_spec` at Open Lower Threshold `> 0`):
  -- For every `u : U`, pick an initial vertex `f₀ u ∈ N_G(v₀) ∩ B (emb u)`.
  have h_pos_spec : ∀ u : U, ∃ x ∈ B (emb u), G.Adj v₀ x := fun u =>
    exists_adj_in_block_of_pos G (B (emb u)) v₀ ((mem_openAttachmentIndices G B v₀ (emb u)).mp (hemb_mem u)).1
  let f₀ : U → V := fun u => Classical.choose (h_pos_spec u)
  have hf₀_mem : ∀ u : U, f₀ u ∈ B (emb u) := fun u => (Classical.choose_spec (h_pos_spec u)).1
  have hf₀_adj : ∀ u : U, G.Adj v₀ (f₀ u) := fun u => (Classical.choose_spec (h_pos_spec u)).2
  -- Step B (Sequential Selection on `U \ S_spec` at Open Upper Threshold `< w / 2`):
  -- Inductively overwrite `f u₀` for `u₀ ∈ T` (`Disjoint T S_spec`) by choosing
  -- `x ∈ (B (emb u₀) \ N_G(v₀)) \ ⋃_{r ∈ (S_spec ∪ T) : ¬W_wit.Adj u₀ r} N_G(f r)`.
  have h_seq : ∀ T : Finset U, Disjoint T S_spec → ∃ f : U → V,
      (∀ u : U, f u ∈ B (emb u)) ∧
      (∀ u ∈ S_spec, G.Adj v₀ (f u)) ∧
      (∀ u ∈ T, ¬G.Adj v₀ (f u)) ∧
      (∀ u₁ ∈ T, ∀ u₂ ∈ S_spec ∪ T, u₁ ≠ u₂ → ¬W_wit.Adj u₁ u₂ → ¬G.Adj (f u₁) (f u₂)) := by
    intro T
    refine Finset.induction_on T ?_ ?_
    · intro _
      exact ⟨f₀, hf₀_mem, fun u _ => hf₀_adj u,
        fun _ hu => False.elim (Finset.notMem_empty _ hu),
        fun _ hu => False.elim (Finset.notMem_empty _ hu)⟩
    · intro u₀ T hu₀_not_T ih hdisj_ins
      rw [Finset.disjoint_insert_left] at hdisj_ins
      rcases hdisj_ins with ⟨hu₀_not_S, hdisj_T⟩
      obtain ⟨f, hf_mem, hf_spec, hf_nonspec, hf_nonadj⟩ := ih hdisj_T
      let P : Finset U := (S_spec ∪ T).filter (fun r => ¬W_wit.Adj u₀ r)
      let Bad : Finset V := neighborFinsetIn G v₀ (B (emb u₀)) ∪
        P.biUnion (fun r => neighborFinsetIn G (f r) (B (emb u₀)))
      -- Since `|N_G(v₀) ∩ B (emb u₀)| < w / 2` and `∑_{r ∈ P} |N_G(f r) ∩ B (emb u₀)| ≤ |U| * δ_cross * w ≤ w / 2`,
      -- we have `|Bad| < w = |B (emb u₀)|`, so `B (emb u₀) \ Bad` is non-empty.
      have hBad_card : (Bad.card : ℝ) < ((B (emb u₀)).card : ℝ) := by
        have h1 : Bad.card ≤ (neighborFinsetIn G v₀ (B (emb u₀))).card +
            ∑ r ∈ P, (neighborFinsetIn G (f r) (B (emb u₀))).card :=
          (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _)
        have h1_r : (Bad.card : ℝ) ≤ ((neighborFinsetIn G v₀ (B (emb u₀))).card : ℝ) +
            ∑ r ∈ P, ((neighborFinsetIn G (f r) (B (emb u₀))).card : ℝ) := by
          exact_mod_cast h1
        have hv₀_lt : ((neighborFinsetIn G v₀ (B (emb u₀))).card : ℝ) < (1 / 2) * (w : ℝ) := by
          have h := ((mem_openAttachmentIndices G B v₀ (emb u₀)).mp (hemb_mem u₀)).2
          rwa [hw_eq (emb u₀)] at h
        have h_each : ∀ r ∈ P, ((neighborFinsetIn G (f r) (B (emb u₀))).card : ℝ) ≤ δ_cross * (w : ℝ) := by
          intro r hr
          rw [Finset.mem_filter, Finset.mem_union] at hr
          have hr_ne : r ≠ u₀ := by
            rintro rfl
            rcases hr.1 with hS | hT
            · exact hu₀_not_S hS
            · exact hu₀_not_T hT
          have hnadj : ¬W_wit.Adj r u₀ := fun h => hr.2 (W_wit.symm h)
          have hsp := sparse_of_not_pattern_comap hB emb hemb_adj hr_ne hnadj (hf_mem r)
          rwa [hw_eq (emb u₀)] at hsp
        have hP_le : (P.card : ℝ) ≤ (Fintype.card U : ℝ) := by
          exact_mod_cast Finset.card_le_univ P
        have h_sum : ∑ r ∈ P, ((neighborFinsetIn G (f r) (B (emb u₀))).card : ℝ) ≤ (1 / 2) * (w : ℝ) := by
          calc ∑ r ∈ P, ((neighborFinsetIn G (f r) (B (emb u₀))).card : ℝ)
              ≤ ∑ _r ∈ P, (δ_cross * (w : ℝ)) := Finset.sum_le_sum h_each
            _ = (P.card : ℝ) * (δ_cross * (w : ℝ)) := by simp [Finset.sum_const, nsmul_eq_mul]
            _ = ((P.card : ℝ) * δ_cross) * (w : ℝ) := by ring
            _ ≤ ((Fintype.card U : ℝ) * δ_cross) * (w : ℝ) := by
                refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
                exact mul_le_mul_of_nonneg_right hP_le hδ_nonneg
            _ ≤ (1 / 2) * (w : ℝ) := mul_le_mul_of_nonneg_right hδ_ub (Nat.cast_nonneg _)
        rw [hw_eq (emb u₀)]
        linarith
      have h_not_sub : ¬(B (emb u₀) ⊆ Bad) := by
        intro hsub
        have hle : ((B (emb u₀)).card : ℝ) ≤ (Bad.card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
        linarith
      obtain ⟨x, hx_mem, hx_not_bad⟩ := Finset.not_subset.mp h_not_sub
      rw [Finset.mem_union, not_or] at hx_not_bad
      rcases hx_not_bad with ⟨hx_not_v₀, hx_not_P⟩
      have hx_v₀ : ¬G.Adj v₀ x := by
        intro hadj
        exact hx_not_v₀ (mem_neighborFinsetIn G v₀ (B (emb u₀)) x |>.mpr ⟨hx_mem, hadj⟩)
      let f' : U → V := Function.update f u₀ x
      have hf'_mem : ∀ u : U, f' u ∈ B (emb u) := by
        intro u
        by_cases hu : u = u₀
        · subst hu; simpa [f'] using hx_mem
        · simpa [f', hu] using hf_mem u
      have hf'_spec : ∀ u ∈ S_spec, G.Adj v₀ (f' u) := by
        intro u hu
        have hu_ne : u ≠ u₀ := fun h => hu₀_not_S (h ▸ hu)
        simpa [f', hu_ne] using hf_spec u hu
      have hf'_nonspec : ∀ u ∈ insert u₀ T, ¬G.Adj v₀ (f' u) := by
        intro u hu
        rw [Finset.mem_insert] at hu
        rcases hu with rfl | huT
        · simpa [f'] using hx_v₀
        · have hu_ne : u ≠ u₀ := fun h => hu₀_not_T (h ▸ huT)
          simpa [f', hu_ne] using hf_nonspec u huT
      refine ⟨f', hf'_mem, hf'_spec, hf'_nonspec, ?_⟩
      intro u₁ hu₁ u₂ hu₂ hne hnadj
      rw [Finset.mem_insert] at hu₁
      rw [Finset.union_insert, Finset.mem_insert] at hu₂
      rcases hu₁ with h_eq₁ | hu₁T <;> rcases hu₂ with h_eq₂ | hu₂ST
      · exact False.elim (hne (h_eq₁.trans h_eq₂.symm))
      · subst h_eq₁
        have hu₂_ne : u₂ ≠ u₁ := Ne.symm hne
        simp only [f', Function.update_self, Function.update_of_ne hu₂_ne]
        intro hadj
        apply hx_not_P
        rw [Finset.mem_biUnion]
        refine ⟨u₂, Finset.mem_filter.mpr ⟨hu₂ST, hnadj⟩, ?_⟩
        rw [mem_neighborFinsetIn]
        exact ⟨hx_mem, G.symm hadj⟩
      · subst h_eq₂
        have hu₁_ne : u₁ ≠ u₂ := hne
        simp only [f', Function.update_self, Function.update_of_ne hu₁_ne]
        intro hadj
        apply hx_not_P
        rw [Finset.mem_biUnion]
        refine ⟨u₁, Finset.mem_filter.mpr ⟨Finset.mem_union_right _ hu₁T, fun h => hnadj (W_wit.symm h)⟩, ?_⟩
        rw [mem_neighborFinsetIn]
        exact ⟨hx_mem, hadj⟩
      · have hu₁_ne : u₁ ≠ u₀ := fun h => hu₀_not_T (h ▸ hu₁T)
        have hu₂_ne : u₂ ≠ u₀ := by
          rintro rfl
          rcases Finset.mem_union.mp hu₂ST with hS | hT
          · exact hu₀_not_S hS
          · exact hu₀_not_T hT
        simp only [f', Function.update_of_ne hu₁_ne, Function.update_of_ne hu₂_ne]
        exact hf_nonadj u₁ hu₁T u₂ hu₂ST hne hnadj
  have hdisj_compl : Disjoint (Finset.univ \ S_spec) S_spec := disjoint_sdiff_self_left
  obtain ⟨f, hf_mem, hf_spec, hf_nonspec, hf_nonadj⟩ := h_seq (Finset.univ \ S_spec) hdisj_compl
  have hunion_eq : S_spec ∪ (Finset.univ \ S_spec) = Finset.univ := by
    ext u
    by_cases hu : u ∈ S_spec <;> simp [hu]
  have hf_inj : Function.Injective f := by
    intro u₁ u₂ heq
    by_contra hne
    have hdisj := hB.1.pairwise_disjoint (emb u₁) (emb u₂) (emb.injective.ne hne)
    exact Finset.disjoint_left.mp hdisj (hf_mem u₁) (heq ▸ hf_mem u₂)
  let g : U ↪ V := ⟨f, hf_inj⟩
  refine ⟨g, ?_⟩
  refine
    { ne_ext := fun u heq => hv₀_ext (emb u) (heq ▸ hf_mem u)
      adj_ext_spec := hf_spec
      nonadj_ext_nonspec := fun u hu => hf_nonspec u (Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, hu⟩)
      adj_of_wit_adj := fun u₁ u₂ hadj => adj_of_pattern_comap emb hemb_adj hadj (hf_mem u₁) (hf_mem u₂)
      nonadj_of_wit_nonadj := ?_ }
  intro u₁ u₂ hne h_nonspec hnadj
  rcases h_nonspec with hu₁ | hu₂
  · exact hf_nonadj u₁ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ u₁, hu₁⟩) u₂
      (hunion_eq.symm ▸ Finset.mem_univ u₂) hne hnadj
  · intro hadj
    exact hf_nonadj u₂ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ u₂, hu₂⟩) u₁
      (hunion_eq.symm ▸ Finset.mem_univ u₁) hne.symm (fun h => hnadj (W_wit.symm h)) (G.symm hadj)

/--
Extracting a clique or independent set `R ⊆ I` of size `|R| ≥ |I|^c` from
`HasPairErdosHajnalProp H₁ H₂` when the induced pattern subgraph on `I` is both `H₁`-free and `H₂`-free.
-/
theorem exists_pattern_clique_or_indep_of_pair_eh
    {W₁ W₂ : Type*} {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂}
    {G : SimpleGraph V} {ℓ : ℕ} {B : Fin ℓ → Finset V} {c : ℝ}
    (h_eh : ∀ (W : Type) [Fintype W] [DecidableEq W] (J : SimpleGraph W),
      IsInducedSubgraphFree J H₁ → IsInducedSubgraphFree J H₂ →
        (Fintype.card W : ℝ) ^ c ≤ (kappa J : ℝ))
    (I : Finset (Fin ℓ))
    (hFree₁ : IsInducedSubgraphFree ((blockadePatternGraph G B).induce (I : Set (Fin ℓ))) H₁)
    (hFree₂ : IsInducedSubgraphFree ((blockadePatternGraph G B).induce (I : Set (Fin ℓ))) H₂) :
    ∃ R ⊆ I, (I.card : ℝ) ^ c ≤ (R.card : ℝ) ∧
      ((∀ i ∈ R, ∀ j ∈ R, i ≠ j → (blockadePatternGraph G B).Adj i j) ∨
       (∀ i ∈ R, ∀ j ∈ R, i ≠ j → ¬(blockadePatternGraph G B).Adj i j)) := by
  classical
  let P := blockadePatternGraph G B
  let J : SimpleGraph ↥(I : Set (Fin ℓ)) := P.induce (I : Set (Fin ℓ))
  have hcard_J : Fintype.card ↥(I : Set (Fin ℓ)) = I.card := Fintype.card_coe I
  have hkappa : (I.card : ℝ) ^ c ≤ (kappa J : ℝ) := by
    rw [← hcard_J]
    exact h_eh ↥(I : Set (Fin ℓ)) J hFree₁ hFree₂
  rcases (kappa_cast_ge_iff J ((I.card : ℝ) ^ c)).mp hkappa with hclique | hindep
  · obtain ⟨s, hs⟩ := J.exists_isNClique_cliqueNum
    let emb : ↥(I : Set (Fin ℓ)) ↪ Fin ℓ := Function.Embedding.subtype _
    refine ⟨s.map emb, ?_, ?_, Or.inl ?_⟩
    · intro x hx
      rcases Finset.mem_map.mp hx with ⟨a, _, rfl⟩
      exact a.2
    · rw [Finset.card_map, hs.card_eq]
      exact hclique
    · intro i hi j hj hij
      rcases Finset.mem_map.mp hi with ⟨a, ha, rfl⟩
      rcases Finset.mem_map.mp hj with ⟨b, hb, rfl⟩
      exact hs.isClique ha hb (ne_of_apply_ne emb hij)
  · obtain ⟨s, hs⟩ := J.exists_isNIndepSet_indepNum
    let emb : ↥(I : Set (Fin ℓ)) ↪ Fin ℓ := Function.Embedding.subtype _
    refine ⟨s.map emb, ?_, ?_, Or.inr ?_⟩
    · intro x hx
      rcases Finset.mem_map.mp hx with ⟨a, _, rfl⟩
      exact a.2
    · rw [Finset.card_map, hs.card_eq]
      exact hindep
    · intro i hi j hj hij
      rcases Finset.mem_map.mp hi with ⟨a, ha, rfl⟩
      rcases Finset.mem_map.mp hj with ⟨b, hb, rfl⟩
      exact hs.isIndepSet ha hb (ne_of_apply_ne emb hij)

/--
**Master Open-Interval Witness-to-Thresholded-Wonderfulness Engine (`isThresholdedWonderful_of_openIntervalWitness_pair`, Propositions 3 and 5 of `main.tex`)**:
Let `H : SimpleGraph W_H` and `W_wit : SimpleGraph U` (`[Fintype W_H] [DecidableEq W_H] [Fintype U] [DecidableEq U]`)
with special set `S_spec : Finset U`. Suppose:
1. `HasPairErdosHajnalProp Hᶜ W_wit` holds; and
2. every open-interval realization `IsOpenIntervalRealization W_wit S_spec G v₀ f` in a finite graph `G`
   contains an induced copy of `Hᶜ` (`¬IsInducedSubgraphFree G Hᶜ`).
Then `IsThresholdedWonderful H` holds (Definition 2(4) of `main.tex`).
-/
theorem isThresholdedWonderful_of_openIntervalWitness_pair
    {W_H U : Type*} [Fintype W_H] [DecidableEq W_H] [Fintype U] [DecidableEq U]
    (H : SimpleGraph W_H) (W_wit : SimpleGraph U) (S_spec : Finset U)
    (h_pair : HasPairErdosHajnalProp Hᶜ W_wit)
    (h_realize : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (v₀ : V) (f : U ↪ V),
      IsOpenIntervalRealization W_wit S_spec G v₀ f → ¬IsInducedSubgraphFree G Hᶜ) :
    IsThresholdedWonderful H := by
  obtain ⟨c, hc_pos, h_eh⟩ := h_pair
  -- Calibrate exponent `a ≥ max 7 (⌈5 / c⌉₊ + 1)` and threshold `y_thr = min (1 / 4) (1 / (2 * N_tot))`.
  let a : ℕ := max 7 (⌈5 / c⌉₊ + 1)
  let N_tot : ℝ := (Fintype.card U : ℝ) + (Fintype.card W_H : ℝ) + 2
  let y_thr : ℝ := min (1 / 4) (1 / (2 * N_tot))
  have ha7 : 7 ≤ a := le_max_left _ _
  have hN_pos : 0 < N_tot := by
    dsimp [N_tot]
    positivity
  have hy_thr_pos : 0 < y_thr := lt_min (by norm_num) (by positivity)
  have hy_thr_le : y_thr ≤ 1 / 4 := min_le_left _ _
  refine ⟨a, y_thr, ha7, hy_thr_pos, hy_thr_le, ?_⟩
  intro V _ _ G y δ_cross ℓ w B hy_pos hy_le_thr hG hℓ_ge hδ_pos hδ_le hw_pos hB hB_eq
  have hw_card : ∀ i : Fin ℓ, (B i).card = w := fun i => (hB_eq i).1
  have hy_le_half : y ≤ 1 / 2 := le_trans hy_le_thr (by linarith)
  have hy_le_one : y ≤ 1 := by linarith
  have ha_real_7 : (7 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha7
  have ha_c : 5 / c + 1 ≤ (a : ℝ) := by
    have h1 : 5 / c ≤ (⌈5 / c⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈5 / c⌉₊ + 1 : ℕ) ≤ a := le_max_right _ _
    have h2_r : ((⌈5 / c⌉₊ : ℝ) + 1) ≤ (a : ℝ) := by exact_mod_cast h2
    linarith
  obtain ⟨_, hya_le_y4, h_rpow_ge⟩ :=
    wonderful_exponent_bounds hc_pos ha_real_7 ha_c hy_pos hy_le_half hℓ_ge
  have hℓ_pos : 0 < ℓ := by
    have : (0 : ℝ) < (ℓ : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hy_pos (-(a : ℝ))) hℓ_ge
    exact Nat.cast_pos.mp this
  have hδ_le_ya : δ_cross ≤ y ^ (a : ℝ) := by
    rw [Real.rpow_natCast]
    exact hδ_le.trans (min_le_left _ _)
  have hya_le_y : y ^ (a : ℝ) ≤ y := by
    calc y ^ (a : ℝ)
        ≤ y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hy_pos hy_le_one (by linarith)
      _ = y := Real.rpow_one y
  have hδ_le_thr : δ_cross ≤ y_thr := (hδ_le_ya.trans hya_le_y).trans hy_le_thr
  have h_N_thr : N_tot * y_thr ≤ 1 / 2 := by
    have h1 : y_thr ≤ 1 / (2 * N_tot) := min_le_right _ _
    calc N_tot * y_thr
        ≤ N_tot * (1 / (2 * N_tot)) := mul_le_mul_of_nonneg_left h1 hN_pos.le
      _ = 1 / 2 := by field_simp [hN_pos.ne']
  have hδ_U : (Fintype.card U : ℝ) * δ_cross ≤ 1 / 2 := by
    have hU_le : (Fintype.card U : ℝ) ≤ N_tot := by
      dsimp [N_tot]
      have : (0 : ℝ) ≤ (Fintype.card W_H : ℝ) := Nat.cast_nonneg _
      linarith
    calc (Fintype.card U : ℝ) * δ_cross
        ≤ N_tot * y_thr := mul_le_mul hU_le hδ_le_thr hδ_pos.le hN_pos.le
      _ ≤ 1 / 2 := h_N_thr
  have hδ_WH : (Fintype.card W_H : ℝ) * δ_cross ≤ 1 / 2 := by
    have hWH_le : (Fintype.card W_H : ℝ) ≤ N_tot := by
      dsimp [N_tot]
      have : (0 : ℝ) ≤ (Fintype.card U : ℝ) := Nat.cast_nonneg _
      linarith
    calc (Fintype.card W_H : ℝ) * δ_cross
        ≤ N_tot * y_thr := mul_le_mul hWH_le hδ_le_thr hδ_pos.le hN_pos.le
      _ ≤ 1 / 2 := h_N_thr
  -- Case split on whether every external vertex `v ∉ ⋃ᵢ Bᵢ` has `< y * ℓ` open-attachment blocks.
  by_cases hAllSmall : ∀ v ∈ blockadeExternalVerts Finset.univ B,
      ((openAttachmentIndices G B v).card : ℝ) < y * (ℓ : ℝ)
  · -- Outcome (W2): Double-counting cross-incidences yields a block `B_{i_star}` with `≤ y * |G|` mixed external vertices.
    right
    have huniv_ne : (Finset.univ : Finset V).Nonempty := by
      obtain ⟨u, _⟩ := hB.1.nonempty_blocks ⟨0, hℓ_pos⟩
      exact ⟨u, Finset.mem_univ u⟩
    obtain ⟨i_star, hi_star⟩ :=
      exists_block_few_openAttachmentExternalVerts G Finset.univ B hℓ_pos hy_pos huniv_ne hAllSmall
    refine ⟨i_star, ?_⟩
    have h_filter_eq :
        (Finset.univ \ Finset.biUnion Finset.univ B).filter (fun v =>
          0 < (neighborFinsetIn G v (B i_star)).card ∧
          ((neighborFinsetIn G v (B i_star)).card : ℝ) < (1 / 2) * (w : ℝ)) =
        openAttachmentExternalVerts G Finset.univ B i_star := by
      ext v
      simp [openAttachmentExternalVerts, blockadeExternalVerts, openAttachmentIndices, hw_card i_star]
    rw [h_filter_eq]
    have h_univ_card : ((Finset.univ : Finset V).card : ℝ) = (Fintype.card V : ℝ) := by simp
    rw [h_univ_card] at hi_star
    exact hi_star.le
  · -- Outcome (W1): Some external vertex `v₀` has `|I₀(v₀)| ≥ y * ℓ`.
    -- The pattern graph induced on `I = I₀(v₀)` is both `Hᶜ`-free and `W_wit`-free, so it contains
    -- a clique or stable set `R ⊆ I` of size `|R| ≥ (y * ℓ)^c ≥ 2 / y^4`, whose block union is `y^4`-restricted.
    left
    push_neg at hAllSmall
    rcases hAllSmall with ⟨v₀, hv₀_mem, hv₀_large⟩
    have hv₀_ext : ∀ i : Fin ℓ, v₀ ∉ B i := (mem_blockadeExternalVerts Finset.univ B v₀).mp hv₀_mem |>.2
    let I := openAttachmentIndices G B v₀
    have hFree_H : IsInducedSubgraphFree ((blockadePatternGraph G B).induce (I : Set (Fin ℓ))) Hᶜ :=
      isInducedSubgraphFree_patternGraph_induce_of_free hG hB hw_pos hw_card hδ_pos.le hδ_WH I
    have hFree_W : IsInducedSubgraphFree ((blockadePatternGraph G B).induce (I : Set (Fin ℓ))) W_wit := by
      rintro ⟨emb, hemb⟩
      let emb' : U ↪ Fin ℓ := emb.trans (Function.Embedding.subtype _)
      have hemb_mem : ∀ u : U, emb' u ∈ I := fun u => (emb u).2
      have hemb_adj : W_wit = (blockadePatternGraph G B).comap emb' := by
        ext u₁ u₂
        have h := congr_arg (fun K => K.Adj u₁ u₂) hemb
        simpa [emb', comap_adj] using h
      obtain ⟨f, hf_real⟩ := exists_openIntervalRealization_of_pattern_emb W_wit S_spec hB hw_card
        hδ_pos.le hδ_U v₀ hv₀_ext emb' hemb_mem hemb_adj
      exact h_realize V G v₀ f hf_real hG
    obtain ⟨R, _, hR_card, hCliqueOrIndep⟩ :=
      exists_pattern_clique_or_indep_of_pair_eh h_eh I hFree_H hFree_W
    have hyℓ_pos : 0 < y * (ℓ : ℝ) := mul_pos hy_pos (Nat.cast_pos.mpr hℓ_pos)
    have h_rpow_mono : (y * (ℓ : ℝ)) ^ c ≤ (I.card : ℝ) ^ c :=
      Real.rpow_le_rpow hyℓ_pos.le hv₀_large hc_pos.le
    have hR_ge : 2 / (y ^ 4) ≤ (R.card : ℝ) := h_rpow_ge.trans (h_rpow_mono.trans hR_card)
    have hy4_pos : 0 < y ^ 4 := by positivity
    have hR_real_pos : 0 < (R.card : ℝ) := lt_of_lt_of_le (div_pos zero_lt_two hy4_pos) hR_ge
    have hR_ne : R.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hR_real_pos)
    have h1R : 1 / (R.card : ℝ) ≤ (y ^ 4) / 2 := by
      rw [div_le_div_iff₀ hR_real_pos zero_lt_two]
      have h2 : 2 ≤ (R.card : ℝ) * (y ^ 4) := (div_le_iff₀ hy4_pos).mp hR_ge
      linarith
    have hδ_le_y4_half : δ_cross ≤ (y ^ 4) / 2 := hδ_le_ya.trans hya_le_y4
    refine ⟨blockUnion B R, ?_, ?_⟩
    · rcases hCliqueOrIndep with hClique | hIndep
      · right
        exact isEpsSparseOn_compl_blockUnion_of_pattern_clique hB.1.pairwise_disjoint R hR_ne
          w (fun i _ => hw_card i) hClique (by linarith)
      · left
        exact isEpsSparseOn_blockUnion_of_pattern_indep hB hδ_pos.le R hR_ne
          w (fun i _ => hw_card i) hIndep (by linarith)
    · exact_mod_cast width_le_card_blockUnion B hB.1.pairwise_disjoint R hR_ne w (fun i _ => hw_card i)

/--
Single-witness specialization of `isThresholdedWonderful_of_openIntervalWitness_pair`:
if `HasErdosHajnalProp W_wit` holds and every `IsOpenIntervalRealization W_wit S_spec G v₀ f`
violates `IsInducedSubgraphFree G Hᶜ`, then `IsThresholdedWonderful H` holds.
-/
theorem isThresholdedWonderful_of_openIntervalWitness
    {W_H U : Type*} [Fintype W_H] [DecidableEq W_H] [Fintype U] [DecidableEq U]
    (H : SimpleGraph W_H) (W_wit : SimpleGraph U) (S_spec : Finset U)
    (h_eh : HasErdosHajnalProp W_wit)
    (h_realize : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (v₀ : V) (f : U ↪ V),
      IsOpenIntervalRealization W_wit S_spec G v₀ f → ¬IsInducedSubgraphFree G Hᶜ) :
    IsThresholdedWonderful H := by
  have h_pair : HasPairErdosHajnalProp Hᶜ W_wit := by
    obtain ⟨c, hc, h⟩ := h_eh
    exact ⟨c, hc, fun V _ _ G _ hW => h V G hW⟩
  exact isThresholdedWonderful_of_openIntervalWitness_pair H W_wit S_spec h_pair h_realize

/--
Constructing an `(n + 1)`-vertex embedding `Fin.cons v₀ f : Fin (n + 1) ↪ V` from an external vertex `v₀`
and a disjoint `n`-vertex embedding `f : Fin n ↪ V` (`∀ u, f u ≠ v₀`).
-/
def consExtEmb {V : Type*} {n : ℕ} (v₀ : V) (f : Fin n ↪ V) (hne : ∀ u : Fin n, f u ≠ v₀) :
    Fin (n + 1) ↪ V where
  toFun := Fin.cons v₀ f
  inj' a b := by
    refine Fin.cases ?_ ?_ a <;> refine Fin.cases ?_ ?_ b
    · intro _; rfl
    · intro s hs
      simp only [Fin.cons_zero, Fin.cons_succ] at hs
      exact False.elim (hne s hs.symm)
    · intro r hr
      simp only [Fin.cons_zero, Fin.cons_succ] at hr
      exact False.elim (hne r hr)
    · intro r s hrs
      simp only [Fin.cons_succ] at hrs
      exact congr_arg Fin.succ (f.injective hrs)

/-- `consExtEmb v₀ f hne` maps `0 : Fin (n + 1)` to the external anchor `v₀`. -/
@[simp]
theorem consExtEmb_zero {V : Type*} {n : ℕ} (v₀ : V) (f : Fin n ↪ V) (hne : ∀ u : Fin n, f u ≠ v₀) :
    consExtEmb v₀ f hne 0 = v₀ :=
  rfl

/-- `consExtEmb v₀ f hne` maps `u.succ : Fin (n + 1)` to the witness vertex `f u`. -/
@[simp]
theorem consExtEmb_succ {V : Type*} {n : ℕ} (v₀ : V) (f : Fin n ↪ V) (hne : ∀ u : Fin n, f u ≠ v₀)
    (u : Fin n) :
    consExtEmb v₀ f hne u.succ = f u :=
  rfl

end GeneralEngine

/-! ### Section 2: Proposition 3 — `witnessH7` and Unconditional Thresholded Wonderfulness of $P_7$ -/

/-- Decidable adjacency instance for the path complement `(pathGraph k)ᶜ`. -/
instance instDecidableRelPathGraphComplAdj (k : ℕ) : DecidableRel (pathGraph k)ᶜ.Adj :=
  inferInstanceAs (DecidableRel (pathGraph k)ᶜ.Adj)

/-- Decidable adjacency instance for the 10-vertex pure-substitution witness `witnessH7` ($H_{(7)}$). -/
instance instDecidableRelWitnessH7Adj : DecidableRel witnessH7.Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧
    (if projH7 u = projH7 v then (projH7 u = 1 ∨ projH7 u = 4)
     else P6Compl.Adj (projH7 u) (projH7 v))))

/-- Embedding of `P6Compl` (`Fin 6`) into the 7-vertex intermediate graph `witnessH7_7`,
omitting the false twin `5` of vertex `3` (backbone index `5`, $v = 4 \in V(H_0)$). -/
def embH7_6_to_7 : Fin 6 ↪ Fin 7 where
  toFun := ![0, 1, 4, 6, 2, 3]
  inj' u v := by revert u v; decide

/-- Prefix inclusion `Fin 7 ↪ Fin 10` for `witnessH7_7`. -/
def embH7_7_to_10 : Fin 7 ↪ Fin 10 where
  toFun i := ⟨i.1, by omega⟩
  inj' u v h := Fin.ext (Fin.mk.inj h)

/-- Prefix inclusion `Fin 8 ↪ Fin 10` for `witnessH7_8`. -/
def embH7_8_to_10 : Fin 8 ↪ Fin 10 where
  toFun i := ⟨i.1, by omega⟩
  inj' u v h := Fin.ext (Fin.mk.inj h)

/-- Prefix inclusion `Fin 9 ↪ Fin 10` for `witnessH7_9`. -/
def embH7_9_to_10 : Fin 9 ↪ Fin 10 where
  toFun i := ⟨i.1, by omega⟩
  inj' u v h := Fin.ext (Fin.mk.inj h)

/-- Intermediate 7-vertex witness subgraph `witnessH7_7` obtained by restricting `witnessH7` to `0..6`. -/
def witnessH7_7 : SimpleGraph (Fin 7) := witnessH7.comap embH7_7_to_10
/-- Intermediate 8-vertex witness subgraph `witnessH7_8` obtained by restricting `witnessH7` to `0..7`. -/
def witnessH7_8 : SimpleGraph (Fin 8) := witnessH7.comap embH7_8_to_10
/-- Intermediate 9-vertex witness subgraph `witnessH7_9` obtained by restricting `witnessH7` to `0..8`. -/
def witnessH7_9 : SimpleGraph (Fin 9) := witnessH7.comap embH7_9_to_10

instance : DecidableRel witnessH7_7.Adj := inferInstanceAs (DecidableRel (witnessH7.comap _).Adj)
instance : DecidableRel witnessH7_8.Adj := inferInstanceAs (DecidableRel (witnessH7.comap _).Adj)
instance : DecidableRel witnessH7_9.Adj := inferInstanceAs (DecidableRel (witnessH7.comap _).Adj)

/-- Step 1 of the twin-substitution tower for `witnessH7`: `witnessH7_7` is a twin extension of `P6Compl`
adding the false twin `5` ($v = 6$) of vertex `3` ($v = 4$, backbone index `5`). -/
theorem isTwinExtension_witnessH7_7 :
    IsTwinExtension P6Compl witnessH7_7 5 5 embH7_6_to_7 where
  h_miss w := by revert w; decide
  h_comap := by ext u v; revert u v; decide
  h_twin w := by revert w; decide

/-- Step 2 of the twin-substitution tower for `witnessH7`: `witnessH7_8` is a twin extension of `witnessH7_7`
adding the true twin `7` ($v = 8$) of vertex `2` ($v = 3$, backbone index `4`). -/
theorem isTwinExtension_witnessH7_8 :
    IsTwinExtension witnessH7_7 witnessH7_8 2 7 Fin.castSuccEmb where
  h_miss w := by revert w; decide
  h_comap := by ext u v; revert u v; decide
  h_twin w := by revert w; decide

/-- Step 3 of the twin-substitution tower for `witnessH7`: `witnessH7_9` is a twin extension of `witnessH7_8`
adding the false twin `8` ($v = 9$) of vertex `0` ($v = 1$, backbone index `0`). -/
theorem isTwinExtension_witnessH7_9 :
    IsTwinExtension witnessH7_8 witnessH7_9 0 8 Fin.castSuccEmb where
  h_miss w := by revert w; decide
  h_comap := by ext u v; revert u v; decide
  h_twin w := by revert w; decide

/-- Step 4 of the twin-substitution tower for `witnessH7`: `witnessH7` is a twin extension of `witnessH7_9`
adding the true twin `9` ($v = 10$) of vertex `1` ($v = 2$, backbone index `1`). -/
theorem isTwinExtension_witnessH7 :
    IsTwinExtension witnessH7_9 witnessH7 1 9 Fin.castSuccEmb where
  h_miss w := by revert w; decide
  h_comap := by ext u v; revert u v; decide
  h_twin w := by revert w; decide

/--
**Proposition 3 (Part 1, `hasErdosHajnalProp_witnessH7`)**:
The 10-vertex pure-substitution witness graph `witnessH7` ($H_{(7)}$) unconditionally satisfies
the Erdős–Hajnal property via 4 twin substitutions from `P6Compl` (`hasErdosHajnalProp_P6Compl`).
-/
theorem hasErdosHajnalProp_witnessH7 : HasErdosHajnalProp witnessH7 := by
  have h7 : HasErdosHajnalProp witnessH7_7 :=
    erdos_hajnal_twin_substitution (by norm_num) isTwinExtension_witnessH7_7 hasErdosHajnalProp_P6Compl
  have h8 : HasErdosHajnalProp witnessH7_8 :=
    erdos_hajnal_twin_substitution (by norm_num) isTwinExtension_witnessH7_8 h7
  have h9 : HasErdosHajnalProp witnessH7_9 :=
    erdos_hajnal_twin_substitution (by norm_num) isTwinExtension_witnessH7_9 h8
  exact erdos_hajnal_twin_substitution (by norm_num) isTwinExtension_witnessH7 h9

/--
Boolean adjacency function for the parameterized 11-vertex graph `extGraphH7 b₁ b₂` on `Fin 11`
(`0` = external vertex $v_0$, `1..10` = shifted vertices of `witnessH7`), where:
- `b₁ = ¬G.Adj (f 0) (f 1)` ($v_1 v_2 \in E(\overline{G})$),
- `b₂ = ¬G.Adj (f 2) (f 3)` ($v_3 v_4 \in E(\overline{G})$).
-/
def extGraphH7AdjBool (b₁ b₂ : Bool) (x y : Fin 11) : Bool :=
  if x == y then false
  else if x == 0 then decide (y.1 - 1 ∈ ({0, 1, 2, 3} : Finset ℕ))
  else if y == 0 then decide (x.1 - 1 ∈ ({0, 1, 2, 3} : Finset ℕ))
  else if (x == 1 && y == 2) || (x == 2 && y == 1) then !b₁
  else if (x == 3 && y == 4) || (x == 4 && y == 3) then !b₂
  else decide (witnessH7.Adj ⟨x.1 - 1, by omega⟩ ⟨y.1 - 1, by omega⟩)

/-- The parameterized 11-vertex open-interval realization graph `extGraphH7 b₁ b₂` on `Fin 11`. -/
def extGraphH7 (b₁ b₂ : Bool) : SimpleGraph (Fin 11) where
  Adj x y := extGraphH7AdjBool b₁ b₂ x y = true
  symm x y := by revert x y b₁ b₂; decide
  loopless x := by revert x b₁ b₂; decide

instance (b₁ b₂ : Bool) : DecidableRel (extGraphH7 b₁ b₂).Adj :=
  fun x y => inferInstanceAs (Decidable (extGraphH7AdjBool b₁ b₂ x y = true))

/--
Explicit 7-vertex routing embedding `embP7_into_extH7 b₁ b₂ : Fin 7 ↪ Fin 11` for Proposition 3:
- Case 1 (`!b₁`, i.e., $v_1 v_2 \notin E(\overline{G})$): `![1, 9, 2, 5, 7, 3, 6]` = $(v_1, v_9, v_2, v_5, v_7, v_3, v_6)$.
- Case 2 (`b₁ && !b₂`, i.e., $v_3 v_4 \notin E(\overline{G})$): `![4, 6, 3, 7, 5, 2, 9]` = $(v_4, v_6, v_3, v_7, v_5, v_2, v_9)$.
- Case 3 (`b₁ && b₂`, i.e., $v_1 v_2, v_3 v_4 \in E(\overline{G})$): `![2, 1, 10, 0, 8, 4, 3]` = $(v_2, v_1, v_{10}, v_0, v_8, v_4, v_3)$.
-/
def embP7_into_extH7 (b₁ b₂ : Bool) : Fin 7 ↪ Fin 11 where
  toFun :=
    if !b₁ then ![1, 9, 2, 5, 7, 3, 6]
    else if !b₂ then ![4, 6, 3, 7, 5, 2, 9]
    else ![2, 1, 10, 0, 8, 4, 3]
  inj' u v := by revert u v b₁ b₂; decide

/-- Kernel verification (`decide`) that `embP7_into_extH7 b₁ b₂` embeds `(pathGraph 7)ᶜ` as an
induced subgraph into `extGraphH7 b₁ b₂` for all $(b_1, b_2) \in \mathrm{Bool}^2$. -/
theorem extGraphH7_comap_embP7 (b₁ b₂ : Bool) :
    (pathGraph 7)ᶜ = (extGraphH7 b₁ b₂).comap (embP7_into_extH7 b₁ b₂) := by
  ext u v
  revert u v b₁ b₂
  decide

/-- The only non-adjacent pairs inside `specH7 = {0, 1, 2, 3}` in `witnessH7` are `{0, 1}` and `{2, 3}`. -/
theorem witnessH7_spec_nonadj_iff (u₁ u₂ : Fin 10) :
    (u₁ ≠ u₂ ∧ u₁ ∈ specH7 ∧ u₂ ∈ specH7 ∧ ¬witnessH7.Adj u₁ u₂) ↔
      (u₁ = 0 ∧ u₂ = 1) ∨ (u₁ = 1 ∧ u₂ = 0) ∨ (u₁ = 2 ∧ u₂ = 3) ∨ (u₁ = 3 ∧ u₂ = 2) := by
  revert u₁ u₂
  decide

/-- In `extGraphH7 b₁ b₂`, the external vertex `0` is adjacent to `u.succ` iff `u ∈ specH7`. -/
theorem extGraphH7_adj_zero_succ (b₁ b₂ : Bool) (u : Fin 10) :
    (extGraphH7 b₁ b₂).Adj 0 u.succ ↔ u ∈ specH7 := by
  revert u b₁ b₂
  decide

/-- Adjacency between witness vertices `u₁.succ` and `u₂.succ` in `extGraphH7 b₁ b₂`. -/
theorem extGraphH7_adj_succ_succ (b₁ b₂ : Bool) (u₁ u₂ : Fin 10) :
    (extGraphH7 b₁ b₂).Adj u₁.succ u₂.succ ↔
      if (u₁ = 0 ∧ u₂ = 1) ∨ (u₁ = 1 ∧ u₂ = 0) then b₁ = false
      else if (u₁ = 2 ∧ u₂ = 3) ∨ (u₁ = 3 ∧ u₂ = 2) then b₂ = false
      else witnessH7.Adj u₁ u₂ := by
  revert u₁ u₂ b₁ b₂
  decide

/--
Every open-interval realization `(v₀, f)` of `(witnessH7, specH7)` in `G` embeds `(pathGraph 7)ᶜ`
as an induced subgraph of `G`.
-/
theorem witnessH7_openIntervalRealization_embeds_P7Compl
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) (v₀ : V) (f : Fin 10 ↪ V)
    (hf : IsOpenIntervalRealization witnessH7 specH7 G v₀ f) :
    ¬IsInducedSubgraphFree G (pathGraph 7)ᶜ := by
  classical
  -- Step 1: Record the two unconstrained special-pair booleans b₁, b₂ in Gᶜ and identify G.comap f_ext = extGraphH7 b₁ b₂.
  let b₁ : Bool := decide (¬G.Adj (f 0) (f 1))
  let b₂ : Bool := decide (¬G.Adj (f 2) (f 3))
  let f_ext : Fin 11 ↪ V := consExtEmb v₀ f hf.ne_ext
  have h_comap : extGraphH7 b₁ b₂ = G.comap f_ext := by
    ext x y
    refine Fin.cases ?_ (fun u₁ => ?_) x
    · refine Fin.cases ?_ (fun u₂ => ?_) y
      · simp
      · rw [comap_adj, extGraphH7_adj_zero_succ, consExtEmb_zero, consExtEmb_succ]
        exact ⟨fun hu => hf.adj_ext_spec u₂ hu, fun hadj => by
          by_contra hnot
          exact hf.nonadj_ext_nonspec u₂ hnot hadj⟩
    · refine Fin.cases ?_ (fun u₂ => ?_) y
      · rw [comap_adj, (extGraphH7 b₁ b₂).adj_comm, G.adj_comm, extGraphH7_adj_zero_succ,
          consExtEmb_zero, consExtEmb_succ]
        exact ⟨fun hu => hf.adj_ext_spec u₁ hu, fun hadj => by
          by_contra hnot
          exact hf.nonadj_ext_nonspec u₁ hnot hadj⟩
      · rw [comap_adj, extGraphH7_adj_succ_succ, consExtEmb_succ, consExtEmb_succ]
        split_ifs with h01 h23
        · rcases h01 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · simp [b₁]
          · simp [b₁, G.adj_comm]
        · rcases h23 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · simp [b₂]
          · simp [b₂, G.adj_comm]
        · by_cases heq : u₁ = u₂
          · subst heq; simp
          · constructor
            · exact hf.adj_of_wit_adj u₁ u₂
            · intro hadj
              by_contra hnadj
              by_cases h_both : u₁ ∈ specH7 ∧ u₂ ∈ specH7
              · have h_cases := (witnessH7_spec_nonadj_iff u₁ u₂).mp ⟨heq, h_both.1, h_both.2, hnadj⟩
                rcases h_cases with h | h | h | h
                · exact h01 (Or.inl h)
                · exact h01 (Or.inr h)
                · exact h23 (Or.inl h)
                · exact h23 (Or.inr h)
              · rw [not_and_or] at h_both
                exact hf.nonadj_of_wit_nonadj u₁ u₂ heq h_both hnadj hadj
  -- Step 2: Compose `embP7_into_extH7 b₁ b₂` with `f_ext` to embed `(pathGraph 7)ᶜ` into `G`.
  intro hFree
  refine hFree ⟨(embP7_into_extH7 b₁ b₂).trans f_ext, ?_⟩
  ext i j
  have h1 := congr_arg (fun H => H.Adj i j) (extGraphH7_comap_embP7 b₁ b₂)
  have h2 := congr_arg (fun H => H.Adj (embP7_into_extH7 b₁ b₂ i) (embP7_into_extH7 b₁ b₂ j)) h_comap
  exact (h1.trans h2).to_iff

/--
**Proposition 3 (Part 2, `isThresholdedWonderful_P7`)**:
The 7-vertex path $P_7$ (`pathGraph 7`) is unconditionally thresholded wonderful (`IsThresholdedWonderful`).
-/
theorem isThresholdedWonderful_P7 : IsThresholdedWonderful (pathGraph 7) :=
  isThresholdedWonderful_of_openIntervalWitness (pathGraph 7) witnessH7 specH7
    hasErdosHajnalProp_witnessH7
    (fun _ _ _ G v₀ f hf => witnessH7_openIntervalRealization_embeds_P7Compl G v₀ f hf)

/-! ### Section 3: Proposition 5(2) — `witnessH8` and Thresholded Wonderfulness of $P_8$ -/

/-- Decidable adjacency instance for the 11-vertex pure-substitution witness `witnessH8` ($H^{(8)}$). -/
instance instDecidableRelWitnessH8Adj : DecidableRel witnessH8.Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧
    (if projH8 u = projH8 v then (projH8 u = 1 ∨ projH8 u = 5)
     else P7Compl.Adj (projH8 u) (projH8 v))))

/-- Embedding of `P7Compl` (`Fin 7`) into the 8-vertex intermediate graph `witnessH8_8`,
omitting the false twin `7` ($p_1^*$) of vertex `0` ($p_1$). -/
def embH8_7_to_8 : Fin 7 ↪ Fin 8 where
  toFun := ![0, 1, 2, 5, 6, 3, 4]
  inj' u v := by revert u v; decide

/-- Prefix inclusion `Fin 8 ↪ Fin 11` for `witnessH8_8`. -/
def embH8_8_to_11 : Fin 8 ↪ Fin 11 where
  toFun i := ⟨i.1, by omega⟩
  inj' u v h := Fin.ext (Fin.mk.inj h)

/-- Prefix inclusion `Fin 9 ↪ Fin 11` for `witnessH8_9`. -/
def embH8_9_to_11 : Fin 9 ↪ Fin 11 where
  toFun i := ⟨i.1, by omega⟩
  inj' u v h := Fin.ext (Fin.mk.inj h)

/-- Prefix inclusion `Fin 10 ↪ Fin 11` for `witnessH8_10`. -/
def embH8_10_to_11 : Fin 10 ↪ Fin 11 where
  toFun i := ⟨i.1, by omega⟩
  inj' u v h := Fin.ext (Fin.mk.inj h)

/-- Intermediate 8-vertex witness subgraph `witnessH8_8` obtained by restricting `witnessH8` to `0..7`. -/
def witnessH8_8 : SimpleGraph (Fin 8) := witnessH8.comap embH8_8_to_11
/-- Intermediate 9-vertex witness subgraph `witnessH8_9` obtained by restricting `witnessH8` to `0..8`. -/
def witnessH8_9 : SimpleGraph (Fin 9) := witnessH8.comap embH8_9_to_11
/-- Intermediate 10-vertex witness subgraph `witnessH8_10` obtained by restricting `witnessH8` to `0..9`. -/
def witnessH8_10 : SimpleGraph (Fin 10) := witnessH8.comap embH8_10_to_11

instance : DecidableRel witnessH8_8.Adj := inferInstanceAs (DecidableRel (witnessH8.comap _).Adj)
instance : DecidableRel witnessH8_9.Adj := inferInstanceAs (DecidableRel (witnessH8.comap _).Adj)
instance : DecidableRel witnessH8_10.Adj := inferInstanceAs (DecidableRel (witnessH8.comap _).Adj)

/-- Step 1 of the twin-substitution tower for `witnessH8`: `witnessH8_8` is a twin extension of `P7Compl`
adding the false twin `7` ($p_1^*$) of vertex `0` ($p_1$, backbone index `0`). -/
theorem isTwinExtension_witnessH8_8 :
    IsTwinExtension P7Compl witnessH8_8 0 7 embH8_7_to_8 where
  h_miss w := by revert w; decide
  h_comap := by ext u v; revert u v; decide
  h_twin w := by revert w; decide

/-- Step 2 of the twin-substitution tower for `witnessH8`: `witnessH8_9` is a twin extension of `witnessH8_8`
adding the true twin `8` ($p_2'$) of vertex `1` ($p_2$, backbone index `1`). -/
theorem isTwinExtension_witnessH8_9 :
    IsTwinExtension witnessH8_8 witnessH8_9 1 8 Fin.castSuccEmb where
  h_miss w := by revert w; decide
  h_comap := by ext u v; revert u v; decide
  h_twin w := by revert w; decide

/-- Step 3 of the twin-substitution tower for `witnessH8`: `witnessH8_10` is a twin extension of `witnessH8_9`
adding the true twin `9` ($7$) of vertex `3` ($2$, backbone index `5`). -/
theorem isTwinExtension_witnessH8_10 :
    IsTwinExtension witnessH8_9 witnessH8_10 3 9 Fin.castSuccEmb where
  h_miss w := by revert w; decide
  h_comap := by ext u v; revert u v; decide
  h_twin w := by revert w; decide

/-- Step 4 of the twin-substitution tower for `witnessH8`: `witnessH8` is a twin extension of `witnessH8_10`
adding the false twin `10` ($5$) of vertex `4` ($3$, backbone index `6`). -/
theorem isTwinExtension_witnessH8 :
    IsTwinExtension witnessH8_10 witnessH8 4 10 Fin.castSuccEmb where
  h_miss w := by revert w; decide
  h_comap := by ext u v; revert u v; decide
  h_twin w := by revert w; decide

/--
**Proposition 5(2) (Part 1, `hasErdosHajnalProp_witnessH8_of_P7`)**:
Given `HasErdosHajnalProp (pathGraph 7)`, the 11-vertex pure-substitution witness graph `witnessH8` ($H^{(8)}$)
satisfies the Erdős–Hajnal property via 4 twin substitutions from `P7Compl`.
-/
theorem hasErdosHajnalProp_witnessH8_of_P7 (hP7 : HasErdosHajnalProp (pathGraph 7)) :
    HasErdosHajnalProp witnessH8 := by
  have hP7Compl : HasErdosHajnalProp P7Compl := hP7.compl
  have h8 : HasErdosHajnalProp witnessH8_8 :=
    erdos_hajnal_twin_substitution (by norm_num) isTwinExtension_witnessH8_8 hP7Compl
  have h9 : HasErdosHajnalProp witnessH8_9 :=
    erdos_hajnal_twin_substitution (by norm_num) isTwinExtension_witnessH8_9 h8
  have h10 : HasErdosHajnalProp witnessH8_10 :=
    erdos_hajnal_twin_substitution (by norm_num) isTwinExtension_witnessH8_10 h9
  exact erdos_hajnal_twin_substitution (by norm_num) isTwinExtension_witnessH8 h10

/--
Boolean adjacency function for the parameterized 12-vertex graph `extGraphH8 b₁ b₂ b₃` on `Fin 12`
(`0` = external vertex $v_0$, `1..11` = shifted vertices of `witnessH8`), where:
- `b₁ = ¬G.Adj (f 0) (f 1)` ($v_{p_1} v_{p_2} \in E(\overline{G})$),
- `b₂ = ¬G.Adj (f 1) (f 2)` ($v_{p_2} v_{p_3} \in E(\overline{G})$), and
- `b₃ = ¬G.Adj (f 3) (f 4)` ($v_2 v_3 \in E(\overline{G})$).
-/
def extGraphH8AdjBool (b₁ b₂ b₃ : Bool) (x y : Fin 12) : Bool :=
  if x == y then false
  else if x == 0 then decide (y.1 - 1 ∈ ({0, 1, 2, 3, 4} : Finset ℕ))
  else if y == 0 then decide (x.1 - 1 ∈ ({0, 1, 2, 3, 4} : Finset ℕ))
  else if (x == 1 && y == 2) || (x == 2 && y == 1) then !b₁
  else if (x == 2 && y == 3) || (x == 3 && y == 2) then !b₂
  else if (x == 4 && y == 5) || (x == 5 && y == 4) then !b₃
  else decide (witnessH8.Adj ⟨x.1 - 1, by omega⟩ ⟨y.1 - 1, by omega⟩)

/-- The parameterized 12-vertex open-interval realization graph `extGraphH8 b₁ b₂ b₃` on `Fin 12`. -/
def extGraphH8 (b₁ b₂ b₃ : Bool) : SimpleGraph (Fin 12) where
  Adj x y := extGraphH8AdjBool b₁ b₂ b₃ x y = true
  symm x y := by revert x y b₁ b₂ b₃; decide
  loopless x := by revert x b₁ b₂ b₃; decide

instance (b₁ b₂ b₃ : Bool) : DecidableRel (extGraphH8 b₁ b₂ b₃).Adj :=
  fun x y => inferInstanceAs (Decidable (extGraphH8AdjBool b₁ b₂ b₃ x y = true))

/--
Explicit 8-vertex routing embedding `embP8_into_extH8 b₁ b₂ b₃ : Fin 8 ↪ Fin 12` for Proposition 5(2),
matching all 7 case branches across $(b_1, b_2, b_3) \in \{0, 1\}^3$ in `main.tex`:
- When `b₃ = false` ($v_2 v_3 \notin E(\overline{G})$):
  - `b₁ = false`: `![1, 9, 3, 6, 7, 4, 11, 5]` = $(v_{p_1}, v_{p_2'}, v_{p_3}, v_{p_4}, v_6, v_2, v_5, v_3)$.
  - `b₁ = true, b₂ = false`: `![2, 1, 9, 3, 6, 7, 4, 11]` = $(v_{p_2}, v_{p_1}, v_{p_2'}, v_{p_3}, v_{p_4}, v_6, v_2, v_5)$.
  - `b₁ = true, b₂ = true`: `![1, 2, 3, 6, 7, 4, 11, 5]` = $(v_{p_1}, v_{p_2}, v_{p_3}, v_{p_4}, v_6, v_2, v_5, v_3)$.
- When `b₃ = true` ($v_2 v_3 \in E(\overline{G})$):
  - `(0, 0, 1)`: `![2, 8, 9, 3, 6, 7, 4, 5]` = $(v_{p_2}, v_{p_1^*}, v_{p_2'}, v_{p_3}, v_{p_4}, v_6, v_2, v_3)$.
  - `(1, 0, 1)`: `![2, 1, 9, 3, 6, 7, 4, 5]` = $(v_{p_2}, v_{p_1}, v_{p_2'}, v_{p_3}, v_{p_4}, v_6, v_2, v_3)$.
  - `(0, 1, 1)`: `![1, 8, 2, 3, 6, 7, 4, 5]` = $(v_{p_1}, v_{p_1^*}, v_{p_2}, v_{p_3}, v_{p_4}, v_6, v_2, v_3)$.
  - `(1, 1, 1)`: `![1, 2, 3, 6, 0, 10, 5, 4]` = $(v_{p_1}, v_{p_2}, v_{p_3}, v_{p_4}, v_0, v_7, v_3, v_2)$.
-/
def embP8_into_extH8 (b₁ b₂ b₃ : Bool) : Fin 8 ↪ Fin 12 where
  toFun :=
    if !b₃ then
      if !b₁ then ![1, 9, 3, 6, 7, 4, 11, 5]
      else if !b₂ then ![2, 1, 9, 3, 6, 7, 4, 11]
      else ![1, 2, 3, 6, 7, 4, 11, 5]
    else
      if !b₁ && !b₂ then ![2, 8, 9, 3, 6, 7, 4, 5]
      else if b₁ && !b₂ then ![2, 1, 9, 3, 6, 7, 4, 5]
      else if !b₁ && b₂ then ![1, 8, 2, 3, 6, 7, 4, 5]
      else ![1, 2, 3, 6, 0, 10, 5, 4]
  inj' u v := by revert u v b₁ b₂ b₃; decide

/-- Kernel verification (`decide`) that `embP8_into_extH8 b₁ b₂ b₃` embeds `(pathGraph 8)ᶜ` as an
induced subgraph into `extGraphH8 b₁ b₂ b₃` for all $(b_1, b_2, b_3) \in \mathrm{Bool}^3$. -/
theorem extGraphH8_comap_embP8 (b₁ b₂ b₃ : Bool) :
    (pathGraph 8)ᶜ = (extGraphH8 b₁ b₂ b₃).comap (embP8_into_extH8 b₁ b₂ b₃) := by
  ext u v
  revert u v b₁ b₂ b₃
  decide

/-- The only non-adjacent pairs inside `specH8 = {0, 1, 2, 3, 4}` in `witnessH8` are `{0, 1}`, `{1, 2}`, and `{3, 4}`. -/
theorem witnessH8_spec_nonadj_iff (u₁ u₂ : Fin 11) :
    (u₁ ≠ u₂ ∧ u₁ ∈ specH8 ∧ u₂ ∈ specH8 ∧ ¬witnessH8.Adj u₁ u₂) ↔
      (u₁ = 0 ∧ u₂ = 1) ∨ (u₁ = 1 ∧ u₂ = 0) ∨
      (u₁ = 1 ∧ u₂ = 2) ∨ (u₁ = 2 ∧ u₂ = 1) ∨
      (u₁ = 3 ∧ u₂ = 4) ∨ (u₁ = 4 ∧ u₂ = 3) := by
  revert u₁ u₂
  decide

/-- In `extGraphH8 b₁ b₂ b₃`, the external vertex `0` is adjacent to `u.succ` iff `u ∈ specH8`. -/
theorem extGraphH8_adj_zero_succ (b₁ b₂ b₃ : Bool) (u : Fin 11) :
    (extGraphH8 b₁ b₂ b₃).Adj 0 u.succ ↔ u ∈ specH8 := by
  revert u b₁ b₂ b₃
  decide

/-- Adjacency between witness vertices `u₁.succ` and `u₂.succ` in `extGraphH8 b₁ b₂ b₃`. -/
theorem extGraphH8_adj_succ_succ (b₁ b₂ b₃ : Bool) (u₁ u₂ : Fin 11) :
    (extGraphH8 b₁ b₂ b₃).Adj u₁.succ u₂.succ ↔
      if (u₁ = 0 ∧ u₂ = 1) ∨ (u₁ = 1 ∧ u₂ = 0) then b₁ = false
      else if (u₁ = 1 ∧ u₂ = 2) ∨ (u₁ = 2 ∧ u₂ = 1) then b₂ = false
      else if (u₁ = 3 ∧ u₂ = 4) ∨ (u₁ = 4 ∧ u₂ = 3) then b₃ = false
      else witnessH8.Adj u₁ u₂ := by
  revert u₁ u₂ b₁ b₂ b₃
  decide

/--
Every open-interval realization `(v₀, f)` of `(witnessH8, specH8)` in `G` embeds `(pathGraph 8)ᶜ`
as an induced subgraph of `G`.
-/
theorem witnessH8_openIntervalRealization_embeds_P8Compl
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) (v₀ : V) (f : Fin 11 ↪ V)
    (hf : IsOpenIntervalRealization witnessH8 specH8 G v₀ f) :
    ¬IsInducedSubgraphFree G (pathGraph 8)ᶜ := by
  classical
  -- Step 1: Record the three unconstrained special-pair booleans b₁, b₂, b₃ in Gᶜ and identify G.comap f_ext = extGraphH8 b₁ b₂ b₃.
  let b₁ : Bool := decide (¬G.Adj (f 0) (f 1))
  let b₂ : Bool := decide (¬G.Adj (f 1) (f 2))
  let b₃ : Bool := decide (¬G.Adj (f 3) (f 4))
  let f_ext : Fin 12 ↪ V := consExtEmb v₀ f hf.ne_ext
  have h_comap : extGraphH8 b₁ b₂ b₃ = G.comap f_ext := by
    ext x y
    refine Fin.cases ?_ (fun u₁ => ?_) x
    · refine Fin.cases ?_ (fun u₂ => ?_) y
      · simp
      · rw [comap_adj, extGraphH8_adj_zero_succ, consExtEmb_zero, consExtEmb_succ]
        exact ⟨fun hu => hf.adj_ext_spec u₂ hu, fun hadj => by
          by_contra hnot
          exact hf.nonadj_ext_nonspec u₂ hnot hadj⟩
    · refine Fin.cases ?_ (fun u₂ => ?_) y
      · rw [comap_adj, (extGraphH8 b₁ b₂ b₃).adj_comm, G.adj_comm, extGraphH8_adj_zero_succ,
          consExtEmb_zero, consExtEmb_succ]
        exact ⟨fun hu => hf.adj_ext_spec u₁ hu, fun hadj => by
          by_contra hnot
          exact hf.nonadj_ext_nonspec u₁ hnot hadj⟩
      · rw [comap_adj, extGraphH8_adj_succ_succ, consExtEmb_succ, consExtEmb_succ]
        split_ifs with h01 h12 h34
        · rcases h01 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · simp [b₁]
          · simp [b₁, G.adj_comm]
        · rcases h12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · simp [b₂]
          · simp [b₂, G.adj_comm]
        · rcases h34 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · simp [b₃]
          · simp [b₃, G.adj_comm]
        · by_cases heq : u₁ = u₂
          · subst heq; simp
          · constructor
            · exact hf.adj_of_wit_adj u₁ u₂
            · intro hadj
              by_contra hnadj
              by_cases h_both : u₁ ∈ specH8 ∧ u₂ ∈ specH8
              · have h_cases := (witnessH8_spec_nonadj_iff u₁ u₂).mp ⟨heq, h_both.1, h_both.2, hnadj⟩
                rcases h_cases with h | h | h | h | h | h
                · exact h01 (Or.inl h)
                · exact h01 (Or.inr h)
                · exact h12 (Or.inl h)
                · exact h12 (Or.inr h)
                · exact h34 (Or.inl h)
                · exact h34 (Or.inr h)
              · rw [not_and_or] at h_both
                exact hf.nonadj_of_wit_nonadj u₁ u₂ heq h_both hnadj hadj
  -- Step 2: Compose `embP8_into_extH8 b₁ b₂ b₃` with `f_ext` to embed `(pathGraph 8)ᶜ` into `G`.
  intro hFree
  refine hFree ⟨(embP8_into_extH8 b₁ b₂ b₃).trans f_ext, ?_⟩
  ext i j
  have h1 := congr_arg (fun H => H.Adj i j) (extGraphH8_comap_embP8 b₁ b₂ b₃)
  have h2 := congr_arg (fun H => H.Adj (embP8_into_extH8 b₁ b₂ b₃ i) (embP8_into_extH8 b₁ b₂ b₃ j)) h_comap
  exact (h1.trans h2).to_iff

/--
**Proposition 5(2) (Part 2, `isThresholdedWonderful_P8_of_P7`)**:
Given `HasErdosHajnalProp (pathGraph 7)`, the 8-vertex path $P_8$ (`pathGraph 8`) is thresholded wonderful
(`IsThresholdedWonderful`).
-/
theorem isThresholdedWonderful_P8_of_P7 (hP7 : HasErdosHajnalProp (pathGraph 7)) :
    IsThresholdedWonderful (pathGraph 8) :=
  isThresholdedWonderful_of_openIntervalWitness (pathGraph 8) witnessH8 specH8
    (hasErdosHajnalProp_witnessH8_of_P7 hP7)
    (fun _ _ _ G v₀ f hf => witnessH8_openIntervalRealization_embeds_P8Compl G v₀ f hf)

/-! ### Section 4: Proposition 5(3) — `witnessH9` and Thresholded Wonderfulness of $P_9$ -/

/-- Decidable adjacency instance for the 20-vertex two-arm pure-substitution witness `witnessH9` ($H^{(9)}$). -/
instance instDecidableRelWitnessH9Adj : DecidableRel witnessH9.Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧
    (if (u.1 < 10 ↔ v.1 < 10) then
      let u' : Fin 10 := ⟨u.1 % 10, Nat.mod_lt u.1 (by decide)⟩
      let v' : Fin 10 := ⟨v.1 % 10, Nat.mod_lt v.1 (by decide)⟩
      if projArm9 u' = projArm9 v' then projArm9 u' = 1
      else P8Compl.Adj (projArm9 u') (projArm9 v')
     else True)))

/--
Invariance of `HasErdosHajnalProp` under graph isomorphism `≃g`.
-/
theorem hasErdosHajnalProp_of_iso {W₁ W₂ : Type*} {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂}
    (e : H₁ ≃g H₂) (h : HasErdosHajnalProp H₁) : HasErdosHajnalProp H₂ := by
  obtain ⟨c, hc, h_bound⟩ := h
  refine ⟨c, hc, fun V _ _ G hG => h_bound V G ?_⟩
  rintro ⟨g, hg⟩
  refine hG ⟨e.symm.toEquiv.toEmbedding.trans g, ?_⟩
  ext x y
  have h1 := e.symm.map_adj_iff (v := x) (w := y)
  have h2 := congr_arg (fun H => H.Adj (e.symm x) (e.symm y)) hg
  exact h1.symm.trans h2.to_iff

/--
The 2-vertex complete graph $K_2$ (`⊤ : SimpleGraph (Fin 2)`) satisfies `HasErdosHajnalProp` with exponent $c = 1$.
-/
theorem hasErdosHajnalProp_K2 : HasErdosHajnalProp (⊤ : SimpleGraph (Fin 2)) := by
  refine ⟨1, zero_lt_one, fun V _ _ G hG => ?_⟩
  rw [Real.rpow_one]
  have h_indep : Gᶜ.IsClique ((Finset.univ : Finset V) : Set V) := by
    intro u _ v _ hne
    refine ⟨hne, fun hadj => hG ?_⟩
    let g : Fin 2 ↪ V :=
      { toFun := ![u, v]
        inj' := by
          intro a b hab
          fin_cases a <;> fin_cases b
          · rfl
          · exact False.elim (hne hab)
          · exact False.elim (hne hab.symm)
          · rfl }
    refine ⟨g, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;> simp [g, hadj, G.symm hadj]
  have h_le : Fintype.card V ≤ G.indepNum := by
    rw [← cliqueNum_compl, ← Finset.card_univ]
    exact h_indep.card_le_cliqueNum
  exact_mod_cast h_le.trans (indepNum_le_kappa G)

/-- Decidable adjacency instance for vertex substitution `substGraph H₁ v₀ H₂`. -/
instance instDecidableRelSubstGraphAdj {V₁ V₂ : Type*}
    (H₁ : SimpleGraph V₁) (v₀ : V₁) (H₂ : SimpleGraph V₂)
    [DecidableRel H₁.Adj] [DecidableRel H₂.Adj] :
    DecidableRel (substGraph H₁ v₀ H₂).Adj := by
  intro a b
  cases a <;> cases b <;> dsimp [substGraph] <;> infer_instance

/-- Prefix inclusion `Fin 9 ↪ Fin 10` for `armH9_9`. -/
def embArm9_9_to_10 : Fin 9 ↪ Fin 10 where
  toFun i := ⟨i.1, by omega⟩
  inj' u v h := Fin.ext (Fin.mk.inj h)

/-- Prefix inclusion `Fin 10 ↪ Fin 20` selecting the left 10-vertex arm $\operatorname{Arm}_L$ (`0..9`) of `witnessH9`. -/
def embArm9_10_to_20 : Fin 10 ↪ Fin 20 where
  toFun i := ⟨i.1, by omega⟩
  inj' u v h := Fin.ext (Fin.mk.inj h)

/-- Prefix inclusion `Fin 11 ↪ Fin 20` selecting $\operatorname{Arm}_L$ (`0..9`) together with vertex `10` ($R_1$) of $\operatorname{Arm}_R$. -/
def embH9_11_to_20 : Fin 11 ↪ Fin 20 where
  toFun i := ⟨i.1, by omega⟩
  inj' u v h := Fin.ext (Fin.mk.inj h)

/-- The 10-vertex single-arm graph `armH9` ($\operatorname{Arm}_X$) obtained from `P8Compl` by 2 twin substitutions. -/
def armH9 : SimpleGraph (Fin 10) := witnessH9.comap embArm9_10_to_20
/-- Intermediate 9-vertex single-arm subgraph `armH9_9` obtained by restricting `armH9` to `0..8`. -/
def armH9_9 : SimpleGraph (Fin 9) := armH9.comap embArm9_9_to_10
/-- Intermediate 11-vertex graph `witnessH9_11` isomorphic to $K_2[1 \leftarrow \operatorname{Arm}_L]$. -/
def witnessH9_11 : SimpleGraph (Fin 11) := witnessH9.comap embH9_11_to_20

instance : DecidableRel armH9.Adj := inferInstanceAs (DecidableRel (witnessH9.comap _).Adj)
instance : DecidableRel armH9_9.Adj := inferInstanceAs (DecidableRel (armH9.comap _).Adj)
instance : DecidableRel witnessH9_11.Adj := inferInstanceAs (DecidableRel (witnessH9.comap _).Adj)

/-- Step 1 of the twin-substitution tower for `armH9`: `armH9_9` is a twin extension of `P8Compl`
adding the false twin `8` ($X_1^*$) of vertex `0` ($X_1$). -/
theorem isTwinExtension_armH9_9 :
    IsTwinExtension P8Compl armH9_9 0 8 Fin.castSuccEmb where
  h_miss w := by revert w; decide
  h_comap := by ext u v; revert u v; decide
  h_twin w := by revert w; decide

/-- Step 2 of the twin-substitution tower for `armH9`: `armH9` is a twin extension of `armH9_9`
adding the true twin `9` ($X_2'$) of vertex `1` ($X_2$). -/
theorem isTwinExtension_armH9 :
    IsTwinExtension armH9_9 armH9 1 9 Fin.castSuccEmb where
  h_miss w := by revert w; decide
  h_comap := by ext u v; revert u v; decide
  h_twin w := by revert w; decide

/-- Given `HasErdosHajnalProp (pathGraph 8)`, the 10-vertex arm `armH9` satisfies `HasErdosHajnalProp`. -/
theorem hasErdosHajnalProp_armH9_of_P8 (hP8 : HasErdosHajnalProp (pathGraph 8)) :
    HasErdosHajnalProp armH9 := by
  have hP8Compl : HasErdosHajnalProp P8Compl := hP8.compl
  have h9 : HasErdosHajnalProp armH9_9 :=
    erdos_hajnal_twin_substitution (by norm_num) isTwinExtension_armH9_9 hP8Compl
  exact erdos_hajnal_twin_substitution (by norm_num) isTwinExtension_armH9 h9

/-- Vertex equivalence identifying the substitution of `armH9` into vertex `1` of $K_2$ with `Fin 11`. -/
def equivSubstK2ArmH9 : ({v : Fin 2 // v ≠ 1} ⊕ Fin 10) ≃ Fin 11 where
  toFun
    | Sum.inl _ => 10
    | Sum.inr x => ⟨x.1, by omega⟩
  invFun i :=
    if hi : i.1 < 10 then Sum.inr ⟨i.1, hi⟩
    else Sum.inl ⟨0, by decide⟩
  left_inv
    | Sum.inl ⟨v, hv⟩ => by
        fin_cases v
        · simp
        · exact False.elim (hv rfl)
    | Sum.inr x => by simp [x.2]
  right_inv i := by
    by_cases hi : i.1 < 10
    · simp [hi]
    · have hi10 : i = 10 := Fin.ext (by omega)
      subst hi10
      simp

/-- Graph isomorphism `substGraph (⊤ : SimpleGraph (Fin 2)) 1 armH9 ≃g witnessH9_11`. -/
def isoSubstK2ArmH9 : substGraph (⊤ : SimpleGraph (Fin 2)) 1 armH9 ≃g witnessH9_11 where
  toEquiv := equivSubstK2ArmH9
  map_rel_iff' := by
    intro a b
    revert a b
    decide

/-- Vertex equivalence identifying the substitution of `armH9` into vertex `10` of `witnessH9_11` with `Fin 20`. -/
def equivSubstH9_11ArmH9 : ({v : Fin 11 // v ≠ 10} ⊕ Fin 10) ≃ Fin 20 where
  toFun
    | Sum.inl ⟨v, _⟩ => ⟨v.1, by omega⟩
    | Sum.inr y => ⟨y.1 + 10, by omega⟩
  invFun u :=
    if hu : u.1 < 10 then
      Sum.inl ⟨⟨u.1, by omega⟩, by intro h; have : u.1 = 10 := congr_arg Fin.val h; omega⟩
    else Sum.inr ⟨u.1 - 10, by omega⟩
  left_inv
    | Sum.inl ⟨v, hv⟩ => by
        have hv_lt : v.1 < 10 := by
          have := v.2
          have : v.1 ≠ 10 := fun h => hv (Fin.ext h)
          omega
        simp [hv_lt]
    | Sum.inr y => by
        have h_not_lt : ¬(y.1 + 10 < 10) := by omega
        simp [h_not_lt]
  right_inv u := by
    by_cases hu : u.1 < 10
    · simp [hu]
    · simp only [hu, ↓reduceDIte]
      ext
      dsimp
      omega

/-- Graph isomorphism `substGraph witnessH9_11 10 armH9 ≃g witnessH9` ($H^{(9)} \cong K_2[1 \leftarrow \operatorname{Arm}_L, 2 \leftarrow \operatorname{Arm}_R]$). -/
def isoSubstH9_11ArmH9 : substGraph witnessH9_11 10 armH9 ≃g witnessH9 where
  toEquiv := equivSubstH9_11ArmH9
  map_rel_iff' := by
    intro a b
    revert a b
    decide

/--
**Proposition 5(3) (Part 1, `hasErdosHajnalProp_witnessH9_of_P8`)**:
Given `HasErdosHajnalProp (pathGraph 8)` and substitution closure for `HasErdosHajnalProp`,
the 20-vertex two-arm witness graph `witnessH9` ($H^{(9)}$) satisfies `HasErdosHajnalProp`.
-/
theorem hasErdosHajnalProp_witnessH9_of_P8
    (hP8 : HasErdosHajnalProp (pathGraph 8))
    (h_subst : ∀ {W₁ W₂ : Type} [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]
      (H₁ : SimpleGraph W₁) (v₀ : W₁) (H₂ : SimpleGraph W₂),
      HasErdosHajnalProp H₁ → HasErdosHajnalProp H₂ → HasErdosHajnalProp (substGraph H₁ v₀ H₂)) :
    HasErdosHajnalProp witnessH9 := by
  have hArm : HasErdosHajnalProp armH9 := hasErdosHajnalProp_armH9_of_P8 hP8
  have h11 : HasErdosHajnalProp witnessH9_11 :=
    hasErdosHajnalProp_of_iso isoSubstK2ArmH9
      (h_subst (⊤ : SimpleGraph (Fin 2)) 1 armH9 hasErdosHajnalProp_K2 hArm)
  exact hasErdosHajnalProp_of_iso isoSubstH9_11ArmH9
    (h_subst witnessH9_11 10 armH9 h11 hArm)

/--
Boolean adjacency function for the parameterized 21-vertex graph `extGraphH9 b₁ b₂ f₁ f₂` on `Fin 21`
(`0` = external vertex $v_0$, `1..20` = shifted vertices of `witnessH9`), where:
- `b₁ = ¬G.Adj (f 0) (f 1)` ($v_{L_1} v_{L_2} \in E(\overline{G})$),
- `b₂ = ¬G.Adj (f 1) (f 2)` ($v_{L_2} v_{L_3} \in E(\overline{G})$),
- `f₁ = ¬G.Adj (f 10) (f 11)` ($v_{R_1} v_{R_2} \in E(\overline{G})$), and
- `f₂ = ¬G.Adj (f 11) (f 12)` ($v_{R_2} v_{R_3} \in E(\overline{G})$).
-/
def extGraphH9AdjBool (b₁ b₂ f₁ f₂ : Bool) (x y : Fin 21) : Bool :=
  if x == y then false
  else if x == 0 then decide (y.1 - 1 ∈ ({0, 1, 2, 10, 11, 12} : Finset ℕ))
  else if y == 0 then decide (x.1 - 1 ∈ ({0, 1, 2, 10, 11, 12} : Finset ℕ))
  else if (x == 1 && y == 2) || (x == 2 && y == 1) then !b₁
  else if (x == 2 && y == 3) || (x == 3 && y == 2) then !b₂
  else if (x == 11 && y == 12) || (x == 12 && y == 11) then !f₁
  else if (x == 12 && y == 13) || (x == 13 && y == 12) then !f₂
  else decide (witnessH9.Adj ⟨x.1 - 1, by omega⟩ ⟨y.1 - 1, by omega⟩)

/-- The parameterized 21-vertex open-interval realization graph `extGraphH9 b₁ b₂ f₁ f₂` on `Fin 21`. -/
def extGraphH9 (b₁ b₂ f₁ f₂ : Bool) : SimpleGraph (Fin 21) where
  Adj x y := extGraphH9AdjBool b₁ b₂ f₁ f₂ x y = true
  symm x y := by revert x y b₁ b₂ f₁ f₂; decide
  loopless x := by revert x b₁ b₂ f₁ f₂; decide

instance (b₁ b₂ f₁ f₂ : Bool) : DecidableRel (extGraphH9 b₁ b₂ f₁ f₂).Adj :=
  fun x y => inferInstanceAs (Decidable (extGraphH9AdjBool b₁ b₂ f₁ f₂ x y = true))

/--
Explicit 9-vertex routing embedding `embP9_into_extH9 b₁ b₂ f₁ f₂ : Fin 9 ↪ Fin 21` for Proposition 5(3),
matching all 7 branches across $(b_1, b_2, f_1, f_2) \in \{0, 1\}^4$ in `main.tex`:
- Left-arm internal routing (`(b₁, b₂) ≠ (true, true)`):
  1. `(0, 0)`: `![2, 9, 10, 3, 4, 5, 6, 7, 8]` = $(v_{L_2}, v_{L_1^*}, v_{L_2'}, v_{L_3}, v_{L_4}, v_{L_5}, v_{L_6}, v_{L_7}, v_{L_8})$.
  2. `(1, 0)`: `![2, 1, 10, 3, 4, 5, 6, 7, 8]` = $(v_{L_2}, v_{L_1}, v_{L_2'}, v_{L_3}, v_{L_4}, v_{L_5}, v_{L_6}, v_{L_7}, v_{L_8})$.
  3. `(0, 1)`: `![1, 9, 2, 3, 4, 5, 6, 7, 8]` = $(v_{L_1}, v_{L_1^*}, v_{L_2}, v_{L_3}, v_{L_4}, v_{L_5}, v_{L_6}, v_{L_7}, v_{L_8})$.
- Right-arm internal routing (`(f₁, f₂) ≠ (true, true)`):
  4. `(0, 0)`: `![12, 19, 20, 13, 14, 15, 16, 17, 18]` = $(v_{R_2}, v_{R_1^*}, v_{R_2'}, v_{R_3}, v_{R_4}, v_{R_5}, v_{R_6}, v_{R_7}, v_{R_8})$.
  5. `(1, 0)`: `![12, 11, 20, 13, 14, 15, 16, 17, 18]` = $(v_{R_2}, v_{R_1}, v_{R_2'}, v_{R_3}, v_{R_4}, v_{R_5}, v_{R_6}, v_{R_7}, v_{R_8})$.
  6. `(0, 1)`: `![11, 19, 12, 13, 14, 15, 16, 17, 18]` = $(v_{R_1}, v_{R_1^*}, v_{R_2}, v_{R_3}, v_{R_4}, v_{R_5}, v_{R_6}, v_{R_7}, v_{R_8})$.
- Cross-arm routing via $v_0$ (`b₁ = b₂ = f₁ = f₂ = true`):
  7. `(1, 1, 1, 1)`: `![1, 2, 3, 4, 0, 14, 13, 12, 11]` = $(v_{L_1}, v_{L_2}, v_{L_3}, v_{L_4}, v_0, v_{R_4}, v_{R_3}, v_{R_2}, v_{R_1})$.
-/
def embP9_into_extH9 (b₁ b₂ f₁ f₂ : Bool) : Fin 9 ↪ Fin 21 where
  toFun :=
    if !b₁ && !b₂ then ![2, 9, 10, 3, 4, 5, 6, 7, 8]
    else if b₁ && !b₂ then ![2, 1, 10, 3, 4, 5, 6, 7, 8]
    else if !b₁ && b₂ then ![1, 9, 2, 3, 4, 5, 6, 7, 8]
    else if !f₁ && !f₂ then ![12, 19, 20, 13, 14, 15, 16, 17, 18]
    else if f₁ && !f₂ then ![12, 11, 20, 13, 14, 15, 16, 17, 18]
    else if !f₁ && f₂ then ![11, 19, 12, 13, 14, 15, 16, 17, 18]
    else ![1, 2, 3, 4, 0, 14, 13, 12, 11]
  inj' u v := by revert u v b₁ b₂ f₁ f₂; decide

/-- Kernel verification (`decide`) that `embP9_into_extH9 b₁ b₂ f₁ f₂` embeds `(pathGraph 9)ᶜ` as an
induced subgraph into `extGraphH9 b₁ b₂ f₁ f₂` for all $(b_1, b_2, f_1, f_2) \in \mathrm{Bool}^4$. -/
theorem extGraphH9_comap_embP9 (b₁ b₂ f₁ f₂ : Bool) :
    (pathGraph 9)ᶜ = (extGraphH9 b₁ b₂ f₁ f₂).comap (embP9_into_extH9 b₁ b₂ f₁ f₂) := by
  ext u v
  revert u v b₁ b₂ f₁ f₂
  decide

/-- The only non-adjacent pairs inside `specH9 = {0, 1, 2, 10, 11, 12}` in `witnessH9` are
`{0, 1}`, `{1, 2}`, `{10, 11}`, and `{11, 12}`. -/
theorem witnessH9_spec_nonadj_iff (u₁ u₂ : Fin 20) :
    (u₁ ≠ u₂ ∧ u₁ ∈ specH9 ∧ u₂ ∈ specH9 ∧ ¬witnessH9.Adj u₁ u₂) ↔
      (u₁ = 0 ∧ u₂ = 1) ∨ (u₁ = 1 ∧ u₂ = 0) ∨
      (u₁ = 1 ∧ u₂ = 2) ∨ (u₁ = 2 ∧ u₂ = 1) ∨
      (u₁ = 10 ∧ u₂ = 11) ∨ (u₁ = 11 ∧ u₂ = 10) ∨
      (u₁ = 11 ∧ u₂ = 12) ∨ (u₁ = 12 ∧ u₂ = 11) := by
  revert u₁ u₂
  decide

/-- In `extGraphH9 b₁ b₂ f₁ f₂`, the external vertex `0` is adjacent to `u.succ` iff `u ∈ specH9`. -/
theorem extGraphH9_adj_zero_succ (b₁ b₂ f₁ f₂ : Bool) (u : Fin 20) :
    (extGraphH9 b₁ b₂ f₁ f₂).Adj 0 u.succ ↔ u ∈ specH9 := by
  revert u b₁ b₂ f₁ f₂
  decide

/-- Adjacency between witness vertices `u₁.succ` and `u₂.succ` in `extGraphH9 b₁ b₂ f₁ f₂`. -/
theorem extGraphH9_adj_succ_succ (b₁ b₂ f₁ f₂ : Bool) (u₁ u₂ : Fin 20) :
    (extGraphH9 b₁ b₂ f₁ f₂).Adj u₁.succ u₂.succ ↔
      if (u₁ = 0 ∧ u₂ = 1) ∨ (u₁ = 1 ∧ u₂ = 0) then b₁ = false
      else if (u₁ = 1 ∧ u₂ = 2) ∨ (u₁ = 2 ∧ u₂ = 1) then b₂ = false
      else if (u₁ = 10 ∧ u₂ = 11) ∨ (u₁ = 11 ∧ u₂ = 10) then f₁ = false
      else if (u₁ = 11 ∧ u₂ = 12) ∨ (u₁ = 12 ∧ u₂ = 11) then f₂ = false
      else witnessH9.Adj u₁ u₂ := by
  revert u₁ u₂ b₁ b₂ f₁ f₂
  decide

/--
Every open-interval realization `(v₀, f)` of `(witnessH9, specH9)` in `G` embeds `(pathGraph 9)ᶜ`
as an induced subgraph of `G`.
-/
theorem witnessH9_openIntervalRealization_embeds_P9Compl
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) (v₀ : V) (f : Fin 20 ↪ V)
    (hf : IsOpenIntervalRealization witnessH9 specH9 G v₀ f) :
    ¬IsInducedSubgraphFree G (pathGraph 9)ᶜ := by
  classical
  -- Step 1: Record the four unconstrained special-pair booleans b₁, b₂, f₁, f₂ in Gᶜ and identify G.comap f_ext = extGraphH9 b₁ b₂ f₁ f₂.
  let b₁ : Bool := decide (¬G.Adj (f 0) (f 1))
  let b₂ : Bool := decide (¬G.Adj (f 1) (f 2))
  let f₁ : Bool := decide (¬G.Adj (f 10) (f 11))
  let f₂ : Bool := decide (¬G.Adj (f 11) (f 12))
  let f_ext : Fin 21 ↪ V := consExtEmb v₀ f hf.ne_ext
  have h_comap : extGraphH9 b₁ b₂ f₁ f₂ = G.comap f_ext := by
    ext x y
    refine Fin.cases ?_ (fun u₁ => ?_) x
    · refine Fin.cases ?_ (fun u₂ => ?_) y
      · simp
      · rw [comap_adj, extGraphH9_adj_zero_succ, consExtEmb_zero, consExtEmb_succ]
        exact ⟨fun hu => hf.adj_ext_spec u₂ hu, fun hadj => by
          by_contra hnot
          exact hf.nonadj_ext_nonspec u₂ hnot hadj⟩
    · refine Fin.cases ?_ (fun u₂ => ?_) y
      · rw [comap_adj, (extGraphH9 b₁ b₂ f₁ f₂).adj_comm, G.adj_comm, extGraphH9_adj_zero_succ,
          consExtEmb_zero, consExtEmb_succ]
        exact ⟨fun hu => hf.adj_ext_spec u₁ hu, fun hadj => by
          by_contra hnot
          exact hf.nonadj_ext_nonspec u₁ hnot hadj⟩
      · rw [comap_adj, extGraphH9_adj_succ_succ, consExtEmb_succ, consExtEmb_succ]
        split_ifs with h01 h12 h1011 h1112
        · rcases h01 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · simp [b₁]
          · simp [b₁, G.adj_comm]
        · rcases h12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · simp [b₂]
          · simp [b₂, G.adj_comm]
        · rcases h1011 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · simp [f₁]
          · simp [f₁, G.adj_comm]
        · rcases h1112 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · simp [f₂]
          · simp [f₂, G.adj_comm]
        · by_cases heq : u₁ = u₂
          · subst heq; simp
          · constructor
            · exact hf.adj_of_wit_adj u₁ u₂
            · intro hadj
              by_contra hnadj
              by_cases h_both : u₁ ∈ specH9 ∧ u₂ ∈ specH9
              · have h_cases := (witnessH9_spec_nonadj_iff u₁ u₂).mp ⟨heq, h_both.1, h_both.2, hnadj⟩
                rcases h_cases with h | h | h | h | h | h | h | h
                · exact h01 (Or.inl h)
                · exact h01 (Or.inr h)
                · exact h12 (Or.inl h)
                · exact h12 (Or.inr h)
                · exact h1011 (Or.inl h)
                · exact h1011 (Or.inr h)
                · exact h1112 (Or.inl h)
                · exact h1112 (Or.inr h)
              · rw [not_and_or] at h_both
                exact hf.nonadj_of_wit_nonadj u₁ u₂ heq h_both hnadj hadj
  -- Step 2: Compose `embP9_into_extH9 b₁ b₂ f₁ f₂` with `f_ext` to embed `(pathGraph 9)ᶜ` into `G`.
  intro hFree
  refine hFree ⟨(embP9_into_extH9 b₁ b₂ f₁ f₂).trans f_ext, ?_⟩
  ext i j
  have h1 := congr_arg (fun H => H.Adj i j) (extGraphH9_comap_embP9 b₁ b₂ f₁ f₂)
  have h2 := congr_arg (fun H => H.Adj (embP9_into_extH9 b₁ b₂ f₁ f₂ i) (embP9_into_extH9 b₁ b₂ f₁ f₂ j)) h_comap
  exact (h1.trans h2).to_iff

/--
**Proposition 5(3) (Part 2, `isThresholdedWonderful_P9_of_P8`)**:
Given `HasErdosHajnalProp (pathGraph 8)` and substitution closure for `HasErdosHajnalProp`,
the 9-vertex path $P_9$ (`pathGraph 9`) is thresholded wonderful (`IsThresholdedWonderful`).
-/
theorem isThresholdedWonderful_P9_of_P8
    (hP8 : HasErdosHajnalProp (pathGraph 8))
    (h_subst : ∀ {W₁ W₂ : Type} [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]
      (H₁ : SimpleGraph W₁) (v₀ : W₁) (H₂ : SimpleGraph W₂),
      HasErdosHajnalProp H₁ → HasErdosHajnalProp H₂ → HasErdosHajnalProp (substGraph H₁ v₀ H₂)) :
    IsThresholdedWonderful (pathGraph 9) :=
  isThresholdedWonderful_of_openIntervalWitness (pathGraph 9) witnessH9 specH9
    (hasErdosHajnalProp_witnessH9_of_P8 hP8 h_subst)
    (fun _ _ _ G v₀ f hf => witnessH9_openIntervalRealization_embeds_P9Compl G v₀ f hf)

/-! ### Section 5: Proposition 5(1) — Caterpillar Tree $T_k$ Acyclicity, Monotonicity, and Open-Interval Reduction -/

/--
Along any simple path `p` in a graph `G` equipped with `depth` and `parent` functions satisfying `h_pd`,
if the unique parent `x` of the start vertex `y` does not lie in `p.support`, then the depth strictly
increases by `p.length` along `p`.
-/
theorem walk_depth_increase {W : Type*} {G : SimpleGraph W}
    (depth : W → ℕ) (parent : W → W)
    (h_pd : ∀ u v : W, G.Adj u v →
      (u = parent v ∧ depth v = depth u + 1) ∨ (v = parent u ∧ depth u = depth v + 1))
    {y z : W} (p : G.Walk y z) (hp : p.IsPath)
    (x : W) (h_par : x = parent y) (h_dep : depth y = depth x + 1)
    (hx_not_mem : x ∉ p.support) :
    depth z = depth y + p.length := by
  induction p generalizing x with
  | nil => simp
  | @cons y w z hadj p' ih =>
    rw [Walk.cons_isPath_iff] at hp
    rcases hp with ⟨hp', hy_not_mem⟩
    simp only [Walk.support_cons, List.mem_cons, not_or] at hx_not_mem
    have hw_ne_x : w ≠ x := fun h => hx_not_mem.2 (h ▸ p'.start_mem_support)
    rcases h_pd y w hadj with ⟨hy_par, hw_dep⟩ | ⟨hw_par, _⟩
    · have h_rec := ih hp' y hy_par hw_dep hy_not_mem
      simp only [Walk.length_cons]
      omega
    · exact False.elim (hw_ne_x (hw_par.trans h_par.symm))

/--
No simple path `p : G.Walk v u` of length at least 2 can connect a vertex `v` back to its parent `u = parent v`
when `depth` and `parent` satisfy `h_pd`.
-/
theorem false_of_parent_adj_and_long_path {W : Type*} {G : SimpleGraph W}
    (depth : W → ℕ) (parent : W → W)
    (h_pd : ∀ u v : W, G.Adj u v →
      (u = parent v ∧ depth v = depth u + 1) ∨ (v = parent u ∧ depth u = depth v + 1))
    {u v : W} (h_par : u = parent v) (h_dep : depth v = depth u + 1)
    (p : G.Walk v u) (hp : p.IsPath) (hlen : 2 ≤ p.length) :
    False := by
  cases p with
  | nil => simp at hlen
  | @cons v w _ hadj_vw q =>
    rw [Walk.cons_isPath_iff] at hp
    rcases hp with ⟨hq, hv_not_q⟩
    have hq_len : 1 ≤ q.length := by simpa using hlen
    have hw_ne_u : w ≠ u := by
      rintro rfl
      rw [(Walk.isPath_iff_eq_nil q).mp hq] at hq_len
      simp at hq_len
    rcases h_pd v w hadj_vw with ⟨hv_par, hw_dep⟩ | ⟨hw_par, _⟩
    · have h_end := walk_depth_increase depth parent h_pd q hq v hv_par hw_dep hv_not_q
      omega
    · exact hw_ne_u (hw_par.trans h_par.symm)

/--
General acyclicity criterion via parent and depth functions: if every edge `(u, v)` of `G` connects
a vertex to its unique parent at depth minus one, then `G` is acyclic (`G.IsAcyclic`).
-/
theorem isAcyclic_of_parent_depth {W : Type*} {G : SimpleGraph W}
    (depth : W → ℕ) (parent : W → W)
    (h_pd : ∀ u v : W, G.Adj u v →
      (u = parent v ∧ depth v = depth u + 1) ∨ (v = parent u ∧ depth u = depth v + 1)) :
    G.IsAcyclic := by
  intro u c hc
  cases c with
  | nil => exact hc.not_of_nil
  | @cons u v _ hadj c' =>
    have hc'_path : c'.IsPath := ((Walk.cons_isCycle_iff c' hadj).mp hc).1
    have hc_len : 3 ≤ (Walk.cons hadj c').length := hc.three_le_length
    have hc'_len : 2 ≤ c'.length := by simpa using hc_len
    rcases h_pd u v hadj with ⟨hu_par, hv_dep⟩ | ⟨hv_par, hu_dep⟩
    · exact false_of_parent_adj_and_long_path depth parent h_pd hu_par hv_dep c' hc'_path hc'_len
    · exact false_of_parent_adj_and_long_path depth parent h_pd hv_par hu_dep
        c'.reverse hc'_path.reverse (by simpa using hc'_len)

/-- Depth function on the 6 fixed vertices `(6, 2, a₁, a₂, 3, 7)` of `CaterpillarTree k`, rooted at `0` ($6$). -/
def fixedTreeDepth : Fin 6 → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 2
  | 5 => 3

/-- Parent function on the 6 fixed vertices `(6, 2, a₁, a₂, 3, 7)` of `CaterpillarTree k`, rooted at `0` ($6$). -/
def fixedTreeParent : Fin 6 → Fin 6
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | 4 => 1
  | 5 => 4

/-- Depth function on `CaterpillarVert k` rooted at `Sum.inr (Sum.inl 0)` (fixed vertex $6$). -/
def caterpillarDepth (k : ℕ) : CaterpillarVert k → ℕ
  | Sum.inl r => (k - 4) - r.1
  | Sum.inr (Sum.inl x) => fixedTreeDepth x
  | Sum.inr (Sum.inr ⟨⟨r, _⟩, j⟩) => (k - 4) - r.1 + j.1 + 1

/-- Unique parent function on `CaterpillarVert k` rooted at `Sum.inr (Sum.inl 0)` (fixed vertex $6$). -/
def caterpillarParent (k : ℕ) : CaterpillarVert k → CaterpillarVert k
  | Sum.inl r =>
      if hr : r.1 + 1 < k - 4 then Sum.inl ⟨r.1 + 1, hr⟩
      else Sum.inr (Sum.inl 0)
  | Sum.inr (Sum.inl x) => Sum.inr (Sum.inl (fixedTreeParent x))
  | Sum.inr (Sum.inr ⟨⟨r, hr⟩, j⟩) =>
      if _ : j.1 = 0 then Sum.inl r
      else Sum.inr (Sum.inr ⟨⟨r, hr⟩, ⟨j.1 - 1, by omega⟩⟩)

/-- Verification of the parent-depth relation across all edges of the 6-vertex fixed subtree. -/
theorem fixedTree_parent_depth (x y : Fin 6)
    (h : (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) ∨
         (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 1) ∨
         (x = 2 ∧ y = 3) ∨ (x = 3 ∧ y = 2) ∨
         (x = 1 ∧ y = 4) ∨ (x = 4 ∧ y = 1) ∨
         (x = 4 ∧ y = 5) ∨ (x = 5 ∧ y = 4)) :
    (x = fixedTreeParent y ∧ fixedTreeDepth y = fixedTreeDepth x + 1) ∨
    (y = fixedTreeParent x ∧ fixedTreeDepth x = fixedTreeDepth y + 1) := by
  revert x y h
  decide

/--
**Caterpillar Acyclicity (`caterpillarTree_isAcyclic`)**:
For every integer $k$, `CaterpillarTree k` is acyclic (a tree/forest).
-/
theorem caterpillarTree_isAcyclic (k : ℕ) : (CaterpillarTree k).IsAcyclic := by
  refine isAcyclic_of_parent_depth (caterpillarDepth k) (caterpillarParent k) ?_
  intro u v hadj
  rcases u with r₁ | (x₁ | ⟨⟨r₁, hr₁⟩, j₁⟩) <;>
    rcases v with r₂ | (x₂ | ⟨⟨r₂, hr₂⟩, j₂⟩)
  · -- Sum.inl r₁, Sum.inl r₂
    have := r₁.2; have := r₂.2
    dsimp [CaterpillarTree, caterpillarAdjAux] at hadj
    rcases hadj with h12 | h21
    · right
      have hr : r₁.1 + 1 < k - 4 := by omega
      dsimp only [caterpillarParent, caterpillarDepth]
      rw [dif_pos hr]
      exact ⟨congr_arg Sum.inl (Fin.ext h12.symm), by omega⟩
    · left
      have hr : r₂.1 + 1 < k - 4 := by omega
      dsimp only [caterpillarParent, caterpillarDepth]
      rw [dif_pos hr]
      exact ⟨congr_arg Sum.inl (Fin.ext h21.symm), by omega⟩
  · -- Sum.inl r₁, Sum.inr (Sum.inl x₂)
    have := r₁.2
    dsimp [CaterpillarTree, caterpillarAdjAux] at hadj
    rcases hadj with ⟨hr, rfl⟩
    right
    have hnot : ¬(r₁.1 + 1 < k - 4) := by omega
    dsimp only [caterpillarParent, caterpillarDepth, fixedTreeDepth]
    rw [dif_neg hnot]
    exact ⟨rfl, by omega⟩
  · -- Sum.inl r₁, Sum.inr (Sum.inr ⟨⟨r₂, hr₂⟩, j₂⟩)
    have := r₁.2; have := r₂.2; have := j₂.2
    dsimp [CaterpillarTree, caterpillarAdjAux] at hadj
    rcases hadj with ⟨rfl, hj0⟩
    left
    dsimp only [caterpillarParent, caterpillarDepth]
    rw [dif_pos hj0]
    exact ⟨rfl, by omega⟩
  · -- Sum.inr (Sum.inl x₁), Sum.inl r₂
    have := r₂.2
    dsimp [CaterpillarTree, caterpillarAdjAux] at hadj
    rcases hadj with ⟨hr, rfl⟩
    left
    have hnot : ¬(r₂.1 + 1 < k - 4) := by omega
    dsimp only [caterpillarParent, caterpillarDepth, fixedTreeDepth]
    rw [dif_neg hnot]
    exact ⟨rfl, by omega⟩
  · -- Sum.inr (Sum.inl x₁), Sum.inr (Sum.inl x₂)
    dsimp [CaterpillarTree, caterpillarAdjAux] at hadj
    rcases fixedTree_parent_depth x₁ x₂ hadj with ⟨hp, hd⟩ | ⟨hp, hd⟩
    · left
      dsimp only [caterpillarParent, caterpillarDepth]
      exact ⟨congr_arg (fun x => Sum.inr (Sum.inl x)) hp, hd⟩
    · right
      dsimp only [caterpillarParent, caterpillarDepth]
      exact ⟨congr_arg (fun x => Sum.inr (Sum.inl x)) hp, hd⟩
  · -- Sum.inr (Sum.inl _), Sum.inr (Sum.inr _)
    exact False.elim hadj
  · -- Sum.inr (Sum.inr ⟨⟨r₁, hr₁⟩, j₁⟩), Sum.inl r₂
    have := r₁.2; have := r₂.2; have := j₁.2
    dsimp [CaterpillarTree, caterpillarAdjAux] at hadj
    rcases hadj with ⟨rfl, hj0⟩
    right
    dsimp only [caterpillarParent, caterpillarDepth]
    rw [dif_pos hj0]
    exact ⟨rfl, by omega⟩
  · -- Sum.inr (Sum.inr _), Sum.inr (Sum.inl _)
    exact False.elim hadj
  · -- Sum.inr (Sum.inr ⟨⟨r₁, hr₁⟩, j₁⟩), Sum.inr (Sum.inr ⟨⟨r₂, hr₂⟩, j₂⟩)
    have := r₁.2; have := r₂.2; have := j₁.2; have := j₂.2
    dsimp [CaterpillarTree, caterpillarAdjAux] at hadj
    rcases hadj with ⟨rfl, h12 | h21⟩
    · left
      have hj2_ne : j₂.1 ≠ 0 := by omega
      dsimp only [caterpillarParent, caterpillarDepth]
      rw [dif_neg hj2_ne]
      refine ⟨?_, by omega⟩
      congr 3
      ext
      dsimp
      omega
    · right
      have hj1_ne : j₁.1 ≠ 0 := by omega
      dsimp only [caterpillarParent, caterpillarDepth]
      rw [dif_neg hj1_ne]
      refine ⟨?_, by omega⟩
      congr 3
      ext
      dsimp
      omega

/--
Vertex map for induced monotonicity `CaterpillarTree j ↪g CaterpillarTree k` ($6 \le j \le k$),
mapping the spine of $T_j$ onto the last $j - 4$ spine vertices $p_{k-j+1}, \dots, p_{k-4}$ of $T_k$
and each pendant path of $T_j$ onto the initial prefix of the corresponding pendant path of $T_k$.
-/
def caterpillarMonoFun {j k : ℕ} (hj : 6 ≤ j) (hjk : j ≤ k) :
    CaterpillarVert j → CaterpillarVert k
  | Sum.inl r => Sum.inl ⟨r.1 + (k - j), by have := r.2; omega⟩
  | Sum.inr (Sum.inl x) => Sum.inr (Sum.inl x)
  | Sum.inr (Sum.inr ⟨⟨r, hr⟩, m⟩) =>
      Sum.inr (Sum.inr ⟨⟨⟨r.1 + (k - j), by have := r.2; omega⟩, by dsimp; omega⟩,
        ⟨m.1, by have hm : m.1 < r.1 + 1 := m.2; dsimp; omega⟩⟩)

/--
**Caterpillar Induced Monotonicity (`caterpillarTree_mono_embedding`, Theorem 7(3) of `main.tex`)**:
For all integers $6 \le j \le k$, `CaterpillarTree j` embeds as an induced subgraph of `CaterpillarTree k`.
-/
def caterpillarTree_mono_embedding {j k : ℕ} (hj : 6 ≤ j) (hjk : j ≤ k) :
    CaterpillarTree j ↪g CaterpillarTree k where
  toFun := caterpillarMonoFun hj hjk
  inj' := by
    intro u v heq
    rcases u with r₁ | (x₁ | ⟨⟨r₁, hr₁⟩, m₁⟩) <;>
      rcases v with r₂ | (x₂ | ⟨⟨r₂, hr₂⟩, m₂⟩)
    · dsimp [caterpillarMonoFun] at heq
      have hval := congr_arg Fin.val (Sum.inl.inj heq)
      dsimp at hval
      exact congr_arg Sum.inl (Fin.ext (by omega))
    · cases heq
    · cases heq
    · cases heq
    · dsimp [caterpillarMonoFun] at heq
      exact congr_arg (fun x => Sum.inr (Sum.inl x)) (Sum.inl.inj (Sum.inr.inj heq))
    · cases heq
    · cases heq
    · cases heq
    · dsimp [caterpillarMonoFun] at heq
      have h_sig := Sum.inr.inj (Sum.inr.inj heq)
      have h_fst : r₁.1 + (k - j) = r₂.1 + (k - j) :=
        congr_arg (fun s : Σ r : {r : Fin (k - 4) // 1 ≤ r.1}, Fin (r.1.1 + 1) => s.1.1.1) h_sig
      have hr_eq : r₁ = r₂ := Fin.ext (by omega)
      subst hr_eq
      have h_snd : m₁.1 = m₂.1 :=
        congr_arg (fun s : Σ r : {r : Fin (k - 4) // 1 ≤ r.1}, Fin (r.1.1 + 1) => s.2.1) h_sig
      have hm_eq : m₁ = m₂ := Fin.ext h_snd
      subst hm_eq
      rfl
  map_rel_iff' := by
    intro u v
    rcases u with r₁ | (x₁ | ⟨⟨r₁, hr₁⟩, m₁⟩) <;>
      rcases v with r₂ | (x₂ | ⟨⟨r₂, hr₂⟩, m₂⟩)
    · dsimp [caterpillarMonoFun, CaterpillarTree, caterpillarAdjAux]
      omega
    · have := r₁.2
      dsimp [caterpillarMonoFun, CaterpillarTree, caterpillarAdjAux]
      exact and_congr_left (fun _ => by omega)
    · dsimp [caterpillarMonoFun, CaterpillarTree, caterpillarAdjAux]
      refine and_congr_left (fun _ => ?_)
      simp only [Fin.ext_iff]
      omega
    · have := r₂.2
      dsimp [caterpillarMonoFun, CaterpillarTree, caterpillarAdjAux]
      exact and_congr_left (fun _ => by omega)
    · rfl
    · rfl
    · dsimp [caterpillarMonoFun, CaterpillarTree, caterpillarAdjAux]
      refine and_congr_left (fun _ => ?_)
      simp only [Fin.ext_iff]
      omega
    · rfl
    · dsimp [caterpillarMonoFun, CaterpillarTree, caterpillarAdjAux]
      refine and_congr_left (fun _ => ?_)
      simp only [Fin.ext_iff]
      omega

/--
Complementation invariance of `HasPairErdosHajnalProp`.
-/
theorem HasPairErdosHajnalProp.compl {W₁ W₂ : Type*} {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂}
    (h : HasPairErdosHajnalProp H₁ H₂) : HasPairErdosHajnalProp H₁ᶜ H₂ᶜ := by
  obtain ⟨c, hc, h_bound⟩ := h
  refine ⟨c, hc, fun V _ _ G hG₁ hG₂ => ?_⟩
  have hG₁' : IsInducedSubgraphFree Gᶜ H₁ := by
    rwa [isInducedSubgraphFree_compl_iff, compl_compl]
  have hG₂' : IsInducedSubgraphFree Gᶜ H₂ := by
    rwa [isInducedSubgraphFree_compl_iff, compl_compl]
  have h_le := h_bound V Gᶜ hG₁' hG₂'
  rwa [kappa_compl] at h_le

/--
Monotonicity of `HasPairErdosHajnalProp` under graph embeddings.
-/
theorem HasPairErdosHajnalProp.of_embeddings {W₁ W₂ W₁' W₂' : Type*}
    {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂}
    {H₁' : SimpleGraph W₁'} {H₂' : SimpleGraph W₂'}
    (e₁ : H₁' ↪g H₁) (e₂ : H₂' ↪g H₂)
    (h : HasPairErdosHajnalProp H₁ H₂) : HasPairErdosHajnalProp H₁' H₂' := by
  obtain ⟨c, hc, h_bound⟩ := h
  refine ⟨c, hc, fun V _ _ G hG₁' hG₂' => h_bound V G ?_ ?_⟩
  · rintro ⟨g, hg⟩
    refine hG₁' ⟨e₁.toEmbedding.trans g, ?_⟩
    ext x y
    have h1 := e₁.map_adj_iff (v := x) (w := y)
    have h2 := congr_arg (fun H => H.Adj (e₁ x) (e₁ y)) hg
    exact h1.symm.trans h2.to_iff
  · rintro ⟨g, hg⟩
    refine hG₂' ⟨e₂.toEmbedding.trans g, ?_⟩
    ext x y
    have h1 := e₂.map_adj_iff (v := x) (w := y)
    have h2 := congr_arg (fun H => H.Adj (e₂ x) (e₂ y)) hg
    exact h1.symm.trans h2.to_iff

/--
Special vertex predicate for `CaterpillarVert k` (Proposition 5(1) of `main.tex`):
$S^{(k)} = \{p_1, \dots, p_{k-5}, 2, 3\}$.
-/
def isSpecHTree (k : ℕ) : CaterpillarVert k → Prop
  | Sum.inl r => r.1 + 1 < k - 4
  | Sum.inr (Sum.inl x) => x = 1 ∨ x = 4
  | Sum.inr (Sum.inr _) => False

instance (k : ℕ) : DecidablePred (isSpecHTree k) := by
  intro u
  rcases u with r | (x | _) <;> dsimp [isSpecHTree] <;> infer_instance

/--
The $(k - 3)$-vertex special set $S^{(k)} = \{p_1, \dots, p_{k-5}, 2, 3\}$ (`specHTree k`) of `witnessHTree k`.
-/
def specHTree (k : ℕ) : Finset (CaterpillarVert k) :=
  Finset.univ.filter (isSpecHTree k)

@[simp]
theorem mem_specHTree_iff (k : ℕ) (u : CaterpillarVert k) :
    u ∈ specHTree k ↔ isSpecHTree k u := by
  simp [specHTree]

/--
Helper lemma: an injective map `g : Fin k ↪ V` embeds `(pathGraph k)ᶜ` into `G` whenever consecutive
indices are adjacent in `Gᶜ` and non-consecutive indices (`a.1 + 1 < b.1`) are non-adjacent in `Gᶜ`.
-/
theorem comap_eq_pathGraph_compl_of_compl_path {V : Type*} (G : SimpleGraph V) {k : ℕ}
    (g : Fin k ↪ V)
    (h_consec : ∀ (a : Fin k) (ha : a.1 + 1 < k), Gᶜ.Adj (g a) (g ⟨a.1 + 1, ha⟩))
    (h_nonconsec : ∀ a b : Fin k, a.1 + 1 < b.1 → ¬Gᶜ.Adj (g a) (g b)) :
    (pathGraph k)ᶜ = G.comap g := by
  ext a b
  by_cases heq : a = b
  · subst heq; simp
  · have hne_g : g a ≠ g b := g.injective.ne heq
    have h_compl_iff : (pathGraph k)ᶜ.Adj a b ↔ ¬(pathGraph k).Adj a b := by
      simp [compl_adj, heq]
    have h_G_iff : (G.comap g).Adj a b ↔ ¬Gᶜ.Adj (g a) (g b) := by
      simp [comap_adj, compl_adj, hne_g]
    rw [h_compl_iff, h_G_iff]
    apply not_congr
    rw [pathGraph_adj]
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne heq) with hlt | hgt
    · by_cases h1 : a.1 + 1 = b.1
      · have hb_eq : b = ⟨a.1 + 1, h1 ▸ b.2⟩ := Fin.ext h1.symm
        rw [hb_eq]
        exact iff_of_true (Or.inl rfl) (h_consec a (h1 ▸ b.2))
      · have hgt1 : a.1 + 1 < b.1 := by omega
        exact iff_of_false (by omega) (h_nonconsec a b hgt1)
    · by_cases h1 : b.1 + 1 = a.1
      · have ha_eq : a = ⟨b.1 + 1, h1 ▸ a.2⟩ := Fin.ext h1.symm
        rw [ha_eq]
        exact iff_of_true (Or.inr rfl) (Gᶜ.symm (h_consec b (h1 ▸ a.2)))
      · have hgt1 : b.1 + 1 < a.1 := by omega
        exact iff_of_false (by omega) (fun h => h_nonconsec b a hgt1 (Gᶜ.symm h))

section CaterpillarRealization

variable {V : Type*} {k : ℕ} {G : SimpleGraph V} {v₀ : V} {f : CaterpillarVert k ↪ V}

/-- Every tree edge `(u₁, u₂)` of `CaterpillarTree k` with at least one endpoint outside `specHTree k`
is realized as an edge of `Gᶜ` under `f`. -/
theorem compl_adj_of_tree_adj_nonspec
    (hf : IsOpenIntervalRealization (witnessHTree k) (specHTree k) G v₀ f)
    {u₁ u₂ : CaterpillarVert k}
    (hadj : (CaterpillarTree k).Adj u₁ u₂)
    (hnonspec : ¬isSpecHTree k u₁ ∨ ¬isSpecHTree k u₂) :
    Gᶜ.Adj (f u₁) (f u₂) := by
  have hne : u₁ ≠ u₂ := (CaterpillarTree k).ne_of_adj hadj
  have hnot_wit : ¬(witnessHTree k).Adj u₁ u₂ := by
    simp [witnessHTree, compl_adj, hadj]
  have hnonspec' : u₁ ∉ specHTree k ∨ u₂ ∉ specHTree k := by
    simpa [mem_specHTree_iff] using hnonspec
  exact ⟨f.injective.ne hne, hf.nonadj_of_wit_nonadj u₁ u₂ hne hnonspec' hnot_wit⟩

/-- Every non-edge `(u₁, u₂)` of `CaterpillarTree k` is realized as a non-edge of `Gᶜ` under `f`. -/
theorem compl_nonadj_of_tree_nonadj
    (hf : IsOpenIntervalRealization (witnessHTree k) (specHTree k) G v₀ f)
    {u₁ u₂ : CaterpillarVert k}
    (hnonadj : ¬(CaterpillarTree k).Adj u₁ u₂) :
    ¬Gᶜ.Adj (f u₁) (f u₂) := by
  by_cases heq : u₁ = u₂
  · subst heq; exact Gᶜ.loopless _
  · have hwit : (witnessHTree k).Adj u₁ u₂ := ⟨heq, hnonadj⟩
    have hG := hf.adj_of_wit_adj u₁ u₂ hwit
    simp [compl_adj, hG]

/-- Every non-special vertex `u ∉ specHTree k` is adjacent to the external anchor `v₀` in `Gᶜ`. -/
theorem compl_adj_v0_of_nonspec
    (hf : IsOpenIntervalRealization (witnessHTree k) (specHTree k) G v₀ f)
    {u : CaterpillarVert k} (hnonspec : ¬isSpecHTree k u) :
    Gᶜ.Adj v₀ (f u) := by
  have hu_not_mem : u ∉ specHTree k := by simpa [mem_specHTree_iff] using hnonspec
  exact ⟨(hf.ne_ext u).symm, hf.nonadj_ext_nonspec u hu_not_mem⟩

/-- Every special vertex `u ∈ specHTree k` is non-adjacent to the external anchor `v₀` in `Gᶜ`. -/
theorem compl_nonadj_v0_of_spec
    (hf : IsOpenIntervalRealization (witnessHTree k) (specHTree k) G v₀ f)
    {u : CaterpillarVert k} (hspec : isSpecHTree k u) :
    ¬Gᶜ.Adj v₀ (f u) := by
  have hu_mem : u ∈ specHTree k := (mem_specHTree_iff k u).mpr hspec
  have hG := hf.adj_ext_spec u hu_mem
  simp [compl_adj, hG]

/--
**Proposition 5(1), Step C Case 1 (`caterpillarCase1Vert`, $\sigma_* = 0$)**:
For $k \ge 6$, the $k$-vertex sequence $(u_{k-4, k-5} - \dots - u_{k-4, 1} - p_{k-4} - 6 - 2 - a_1 - a_2)$
in `CaterpillarVert k`.
-/
def caterpillarCase1Vert (hk : 6 ≤ k) (t : Fin k) : CaterpillarVert k :=
  if _ : t.1 < k - 5 then
    Sum.inr (Sum.inr ⟨⟨⟨k - 5, by omega⟩, by dsimp; omega⟩, ⟨(k - 6) - t.1, by dsimp; omega⟩⟩)
  else if t.1 = k - 5 then
    Sum.inl ⟨k - 5, by omega⟩
  else if t.1 = k - 4 then
    Sum.inr (Sum.inl 0)
  else if t.1 = k - 3 then
    Sum.inr (Sum.inl 1)
  else if t.1 = k - 2 then
    Sum.inr (Sum.inl 2)
  else
    Sum.inr (Sum.inl 3)

/-- Explicit 6-branch characterization of `caterpillarCase1Vert hk t`. -/
theorem caterpillarCase1Vert_eq (hk : 6 ≤ k) (t : Fin k) :
    (t.1 < k - 5 ∧ caterpillarCase1Vert hk t =
      Sum.inr (Sum.inr ⟨⟨⟨k - 5, by omega⟩, by dsimp; omega⟩, ⟨(k - 6) - t.1, by dsimp; omega⟩⟩)) ∨
    (t.1 = k - 5 ∧ caterpillarCase1Vert hk t = Sum.inl ⟨k - 5, by omega⟩) ∨
    (t.1 = k - 4 ∧ caterpillarCase1Vert hk t = Sum.inr (Sum.inl 0)) ∨
    (t.1 = k - 3 ∧ caterpillarCase1Vert hk t = Sum.inr (Sum.inl 1)) ∨
    (t.1 = k - 2 ∧ caterpillarCase1Vert hk t = Sum.inr (Sum.inl 2)) ∨
    (t.1 = k - 1 ∧ caterpillarCase1Vert hk t = Sum.inr (Sum.inl 3)) := by
  have := t.2
  dsimp [caterpillarCase1Vert]
  split_ifs with h1 h2 h3 h4 h5
  · exact Or.inl ⟨h1, rfl⟩
  · exact Or.inr (Or.inl ⟨h2, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h3, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h4, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h5, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, rfl⟩))))

/-- Left-inverse index function for `caterpillarCase1Vert`. -/
def caterpillarCase1Inv (k : ℕ) : CaterpillarVert k → ℕ
  | Sum.inr (Sum.inr ⟨_, m⟩) => (k - 6) - m.1
  | Sum.inl _ => k - 5
  | Sum.inr (Sum.inl 0) => k - 4
  | Sum.inr (Sum.inl 1) => k - 3
  | Sum.inr (Sum.inl 2) => k - 2
  | _ => k - 1

/-- `caterpillarCase1Inv k` is a left inverse to `caterpillarCase1Vert hk`. -/
theorem caterpillarCase1Inv_leftInverse (hk : 6 ≤ k) (t : Fin k) :
    caterpillarCase1Inv k (caterpillarCase1Vert hk t) = t.1 := by
  rcases caterpillarCase1Vert_eq hk t with
    ⟨ht, h⟩ | ⟨ht, h⟩ | ⟨ht, h⟩ | ⟨ht, h⟩ | ⟨ht, h⟩ | ⟨ht, h⟩ <;>
    rw [h] <;> dsimp [caterpillarCase1Inv] <;> omega

/-- Injectivity of `caterpillarCase1Vert hk`. -/
theorem caterpillarCase1Vert_injective (hk : 6 ≤ k) :
    Function.Injective (caterpillarCase1Vert hk) := by
  intro a b heq
  exact Fin.ext (by rw [← caterpillarCase1Inv_leftInverse hk a,
    ← caterpillarCase1Inv_leftInverse hk b, heq])

/-- Consecutive vertices along `caterpillarCase1Vert` are adjacent in `CaterpillarTree k` and have at least
one non-special endpoint. -/
theorem caterpillarCase1Vert_consec_adj (hk : 6 ≤ k) (a : Fin k) (ha : a.1 + 1 < k) :
    (CaterpillarTree k).Adj (caterpillarCase1Vert hk a) (caterpillarCase1Vert hk ⟨a.1 + 1, ha⟩) ∧
    (¬isSpecHTree k (caterpillarCase1Vert hk a) ∨
     ¬isSpecHTree k (caterpillarCase1Vert hk ⟨a.1 + 1, ha⟩)) := by
  let b : Fin k := ⟨a.1 + 1, ha⟩
  have hba : b.1 = a.1 + 1 := rfl
  rcases caterpillarCase1Vert_eq hk a with
      ⟨ha1, hwa⟩ | ⟨ha1, hwa⟩ | ⟨ha1, hwa⟩ | ⟨ha1, hwa⟩ | ⟨ha1, hwa⟩ | ⟨ha1, hwa⟩ <;>
    rcases caterpillarCase1Vert_eq hk b with
      ⟨hb1, hwb⟩ | ⟨hb1, hwb⟩ | ⟨hb1, hwb⟩ | ⟨hb1, hwb⟩ | ⟨hb1, hwb⟩ | ⟨hb1, hwb⟩ <;>
    try omega
  · rw [hwa, hwb]
    dsimp [CaterpillarTree, caterpillarAdjAux, isSpecHTree]
    exact ⟨⟨rfl, Or.inr (by omega)⟩, Or.inl not_false⟩
  · rw [hwa, hwb]
    dsimp [CaterpillarTree, caterpillarAdjAux, isSpecHTree]
    exact ⟨⟨rfl, by omega⟩, Or.inl not_false⟩
  · rw [hwa, hwb]
    dsimp [CaterpillarTree, caterpillarAdjAux, isSpecHTree]
    exact ⟨⟨by omega, rfl⟩, Or.inl (by omega)⟩
  · rw [hwa, hwb]
    dsimp [CaterpillarTree, caterpillarAdjAux, isSpecHTree]
    decide
  · rw [hwa, hwb]
    dsimp [CaterpillarTree, caterpillarAdjAux, isSpecHTree]
    decide
  · rw [hwa, hwb]
    dsimp [CaterpillarTree, caterpillarAdjAux, isSpecHTree]
    decide

/-- Non-consecutive vertices along `caterpillarCase1Vert` are non-adjacent in `CaterpillarTree k`. -/
theorem caterpillarCase1Vert_nonconsec_nonadj (hk : 6 ≤ k) (a b : Fin k) (hab : a.1 + 1 < b.1) :
    ¬(CaterpillarTree k).Adj (caterpillarCase1Vert hk a) (caterpillarCase1Vert hk b) := by
  rcases caterpillarCase1Vert_eq hk a with
      ⟨ha1, hwa⟩ | ⟨ha1, hwa⟩ | ⟨ha1, hwa⟩ | ⟨ha1, hwa⟩ | ⟨ha1, hwa⟩ | ⟨ha1, hwa⟩ <;>
    rcases caterpillarCase1Vert_eq hk b with
      ⟨hb1, hwb⟩ | ⟨hb1, hwb⟩ | ⟨hb1, hwb⟩ | ⟨hb1, hwb⟩ | ⟨hb1, hwb⟩ | ⟨hb1, hwb⟩ <;>
    try omega
  · rw [hwa, hwb]; dsimp [CaterpillarTree, caterpillarAdjAux]; rintro ⟨_, _⟩; omega
  · rw [hwa, hwb]; dsimp [CaterpillarTree, caterpillarAdjAux]; rintro ⟨_, _⟩; omega
  · rw [hwa, hwb]; exact not_false
  · rw [hwa, hwb]; exact not_false
  · rw [hwa, hwb]; exact not_false
  · rw [hwa, hwb]; exact not_false
  · rw [hwa, hwb]; dsimp [CaterpillarTree, caterpillarAdjAux]; rintro ⟨_, h⟩; cases h
  · rw [hwa, hwb]; dsimp [CaterpillarTree, caterpillarAdjAux]; rintro ⟨_, h⟩; cases h
  · rw [hwa, hwb]; dsimp [CaterpillarTree, caterpillarAdjAux]; rintro ⟨_, h⟩; cases h
  · rw [hwa, hwb]; dsimp [CaterpillarTree, caterpillarAdjAux]; decide
  · rw [hwa, hwb]; dsimp [CaterpillarTree, caterpillarAdjAux]; decide
  · rw [hwa, hwb]; dsimp [CaterpillarTree, caterpillarAdjAux]; decide

/--
**Proposition 5(1), Step C Case 1 (`caterpillar_routing_case1`, $\sigma_* = 0$)**:
For $k \ge 6$, the $k$-vertex sequence $(u_{k-4, k-5} - \dots - u_{k-4, 1} - p_{k-4} - 6 - 2 - a_1 - a_2)$
embeds $P_k$ into $Gᶜ$ (equivalently `(pathGraph k)ᶜ` into `G`), using only forced tree edges of $T_k$.
-/
theorem caterpillar_routing_case1 (hk : 6 ≤ k)
    (hf : IsOpenIntervalRealization (witnessHTree k) (specHTree k) G v₀ f) :
    ¬IsInducedSubgraphFree G (pathGraph k)ᶜ := by
  let w : Fin k ↪ CaterpillarVert k := ⟨caterpillarCase1Vert hk, caterpillarCase1Vert_injective hk⟩
  let g : Fin k ↪ V := w.trans f
  have h_eq : (pathGraph k)ᶜ = G.comap g := by
    refine comap_eq_pathGraph_compl_of_compl_path G g ?_ ?_
    · intro a ha
      obtain ⟨hadj, hns⟩ := caterpillarCase1Vert_consec_adj hk a ha
      exact compl_adj_of_tree_adj_nonspec hf hadj hns
    · intro a b hab
      exact compl_nonadj_of_tree_nonadj hf (caterpillarCase1Vert_nonconsec_nonadj hk a b hab)
  intro hFree
  exact hFree ⟨g, h_eq⟩

/--
**Proposition 5(1), Step C Case 2 (`caterpillarCase2Vert`, $\sigma_* = 1$ and largest $i_0$ with $\sigma_{i_0} = 0$)**:
For $k \ge 6$ and $1 \le r_0 < k - 5$ (where $r_0 = i_0$), the $k$-vertex sequence
$(u_{r_0+1, r_0+1} - \dots - u_{r_0+1, 1} - p_{r_0+1} - \dots - p_{k-4} - 6 - 2 - 3)$ in `CaterpillarVert k`.
-/
def caterpillarCase2Vert (_hk : 6 ≤ k) (r₀ : Fin (k - 4)) (hr₀_ge1 : 1 ≤ r₀.1)
    (_hr₀_lt : r₀.1 < k - 5) (t : Fin k) : CaterpillarVert k :=
  if _ : t.1 ≤ r₀.1 then
    Sum.inr (Sum.inr ⟨⟨r₀, hr₀_ge1⟩, ⟨r₀.1 - t.1, by dsimp; omega⟩⟩)
  else if ht : t.1 < k - 3 then
    Sum.inl ⟨t.1 - 1, by omega⟩
  else if t.1 = k - 3 then
    Sum.inr (Sum.inl 0)
  else if t.1 = k - 2 then
    Sum.inr (Sum.inl 1)
  else
    Sum.inr (Sum.inl 4)

/-- Explicit 5-branch characterization of `caterpillarCase2Vert hk r₀ hr₀_ge1 hr₀_lt t`. -/
theorem caterpillarCase2Vert_eq (hk : 6 ≤ k) (r₀ : Fin (k - 4)) (hr₀_ge1 : 1 ≤ r₀.1)
    (hr₀_lt : r₀.1 < k - 5) (t : Fin k) :
    (t.1 ≤ r₀.1 ∧ caterpillarCase2Vert hk r₀ hr₀_ge1 hr₀_lt t =
      Sum.inr (Sum.inr ⟨⟨r₀, hr₀_ge1⟩, ⟨r₀.1 - t.1, by dsimp; omega⟩⟩)) ∨
    (∃ ht : r₀.1 < t.1 ∧ t.1 < k - 3, caterpillarCase2Vert hk r₀ hr₀_ge1 hr₀_lt t =
      Sum.inl ⟨t.1 - 1, by omega⟩) ∨
    (t.1 = k - 3 ∧ caterpillarCase2Vert hk r₀ hr₀_ge1 hr₀_lt t = Sum.inr (Sum.inl 0)) ∨
    (t.1 = k - 2 ∧ caterpillarCase2Vert hk r₀ hr₀_ge1 hr₀_lt t = Sum.inr (Sum.inl 1)) ∨
    (t.1 = k - 1 ∧ caterpillarCase2Vert hk r₀ hr₀_ge1 hr₀_lt t = Sum.inr (Sum.inl 4)) := by
  have := t.2
  dsimp [caterpillarCase2Vert]
  split_ifs with h1 h2 h3 h4
  · exact Or.inl ⟨h1, rfl⟩
  · exact Or.inr (Or.inl ⟨⟨by omega, h2⟩, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h3, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h4, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, rfl⟩)))

/-- Left-inverse index function for `caterpillarCase2Vert`. -/
def caterpillarCase2Inv (k : ℕ) (r₀ : Fin (k - 4)) : CaterpillarVert k → ℕ
  | Sum.inr (Sum.inr ⟨_, m⟩) => r₀.1 - m.1
  | Sum.inl r => r.1 + 1
  | Sum.inr (Sum.inl 0) => k - 3
  | Sum.inr (Sum.inl 1) => k - 2
  | _ => k - 1

/-- `caterpillarCase2Inv k r₀` is a left inverse to `caterpillarCase2Vert hk r₀ hr₀_ge1 hr₀_lt`. -/
theorem caterpillarCase2Inv_leftInverse (hk : 6 ≤ k) (r₀ : Fin (k - 4)) (hr₀_ge1 : 1 ≤ r₀.1)
    (hr₀_lt : r₀.1 < k - 5) (t : Fin k) :
    caterpillarCase2Inv k r₀ (caterpillarCase2Vert hk r₀ hr₀_ge1 hr₀_lt t) = t.1 := by
  rcases caterpillarCase2Vert_eq hk r₀ hr₀_ge1 hr₀_lt t with
    ⟨ht, h⟩ | ⟨ht, h⟩ | ⟨ht, h⟩ | ⟨ht, h⟩ | ⟨ht, h⟩ <;>
    rw [h] <;> dsimp [caterpillarCase2Inv] <;> omega

/-- Injectivity of `caterpillarCase2Vert hk r₀ hr₀_ge1 hr₀_lt`. -/
theorem caterpillarCase2Vert_injective (hk : 6 ≤ k) (r₀ : Fin (k - 4)) (hr₀_ge1 : 1 ≤ r₀.1)
    (hr₀_lt : r₀.1 < k - 5) :
    Function.Injective (caterpillarCase2Vert hk r₀ hr₀_ge1 hr₀_lt) := by
  intro a b heq
  exact Fin.ext (by rw [← caterpillarCase2Inv_leftInverse hk r₀ hr₀_ge1 hr₀_lt a,
    ← caterpillarCase2Inv_leftInverse hk r₀ hr₀_ge1 hr₀_lt b, heq])

/-- Non-consecutive vertices along `caterpillarCase2Vert` are non-adjacent in `CaterpillarTree k`. -/
theorem caterpillarCase2Vert_nonconsec_nonadj (hk : 6 ≤ k) (r₀ : Fin (k - 4)) (hr₀_ge1 : 1 ≤ r₀.1)
    (hr₀_lt : r₀.1 < k - 5) (a b : Fin k) (hab : a.1 + 1 < b.1) :
    ¬(CaterpillarTree k).Adj (caterpillarCase2Vert hk r₀ hr₀_ge1 hr₀_lt a)
      (caterpillarCase2Vert hk r₀ hr₀_ge1 hr₀_lt b) := by
  rcases caterpillarCase2Vert_eq hk r₀ hr₀_ge1 hr₀_lt a with
      ⟨ha1, hwa⟩ | ⟨ha1, hwa⟩ | ⟨ha1, hwa⟩ | ⟨ha1, hwa⟩ | ⟨ha1, hwa⟩ <;>
    rcases caterpillarCase2Vert_eq hk r₀ hr₀_ge1 hr₀_lt b with
      ⟨hb1, hwb⟩ | ⟨hb1, hwb⟩ | ⟨hb1, hwb⟩ | ⟨hb1, hwb⟩ | ⟨hb1, hwb⟩ <;>
    try omega
  · rw [hwa, hwb]; dsimp [CaterpillarTree, caterpillarAdjAux]; rintro ⟨_, _⟩; omega
  · rw [hwa, hwb]
    dsimp [CaterpillarTree, caterpillarAdjAux]
    rintro ⟨hr_eq, hm0⟩
    have := congr_arg Fin.val hr_eq
    dsimp at this hm0
    omega
  · rw [hwa, hwb]; exact not_false
  · rw [hwa, hwb]; exact not_false
  · rw [hwa, hwb]; exact not_false
  · rw [hwa, hwb]; dsimp [CaterpillarTree, caterpillarAdjAux]; omega
  · rw [hwa, hwb]; dsimp [CaterpillarTree, caterpillarAdjAux]; rintro ⟨h, _⟩; omega
  · rw [hwa, hwb]; dsimp [CaterpillarTree, caterpillarAdjAux]; rintro ⟨_, h⟩; cases h
  · rw [hwa, hwb]; dsimp [CaterpillarTree, caterpillarAdjAux]; rintro ⟨_, h⟩; cases h
  · rw [hwa, hwb]; dsimp [CaterpillarTree, caterpillarAdjAux]; decide

/--
**Proposition 5(1), Step C Case 2 (`caterpillar_routing_case2`, $\sigma_* = 1$ and largest $i_0$ with $\sigma_{i_0} = 0$)**:
For $k \ge 6$ and $1 \le r_0 < k - 5$ with $\sigma_* = 1$ (`h_star`) and $\sigma_q = 1$ for all $q > r_0$ (`h_tail`),
the $k$-vertex sequence $(u_{r_0+1, r_0+1} - \dots - u_{r_0+1, 1} - p_{r_0+1} - \dots - p_{k-4} - 6 - 2 - 3)$
embeds $P_k$ into $Gᶜ$ (equivalently `(pathGraph k)ᶜ` into `G`).
-/
theorem caterpillar_routing_case2 (hk : 6 ≤ k)
    (hf : IsOpenIntervalRealization (witnessHTree k) (specHTree k) G v₀ f)
    (r₀ : Fin (k - 4)) (hr₀_ge1 : 1 ≤ r₀.1) (hr₀_lt : r₀.1 < k - 5)
    (h_star : Gᶜ.Adj (f (Sum.inr (Sum.inl 1))) (f (Sum.inr (Sum.inl 4))))
    (h_tail : ∀ (q : ℕ) (hq : q + 1 < k - 5), r₀.1 ≤ q →
      Gᶜ.Adj (f (Sum.inl ⟨q, by omega⟩)) (f (Sum.inl ⟨q + 1, by omega⟩))) :
    ¬IsInducedSubgraphFree G (pathGraph k)ᶜ := by
  let w : Fin k ↪ CaterpillarVert k :=
    ⟨caterpillarCase2Vert hk r₀ hr₀_ge1 hr₀_lt,
     caterpillarCase2Vert_injective hk r₀ hr₀_ge1 hr₀_lt⟩
  let g : Fin k ↪ V := w.trans f
  have h_eq : (pathGraph k)ᶜ = G.comap g := by
    refine comap_eq_pathGraph_compl_of_compl_path G g ?_ ?_
    · intro a ha
      let b : Fin k := ⟨a.1 + 1, ha⟩
      have hba : b.1 = a.1 + 1 := rfl
      change Gᶜ.Adj (f (caterpillarCase2Vert hk r₀ hr₀_ge1 hr₀_lt a))
        (f (caterpillarCase2Vert hk r₀ hr₀_ge1 hr₀_lt b))
      rcases caterpillarCase2Vert_eq hk r₀ hr₀_ge1 hr₀_lt a with
          ⟨ha1, hwa⟩ | ⟨ha1, hwa⟩ | ⟨ha1, hwa⟩ | ⟨ha1, hwa⟩ | ⟨ha1, hwa⟩ <;>
        rcases caterpillarCase2Vert_eq hk r₀ hr₀_ge1 hr₀_lt b with
          ⟨hb1, hwb⟩ | ⟨hb1, hwb⟩ | ⟨hb1, hwb⟩ | ⟨hb1, hwb⟩ | ⟨hb1, hwb⟩ <;>
        try omega
      · rw [hwa, hwb]
        refine compl_adj_of_tree_adj_nonspec hf ?_ (Or.inl not_false)
        dsimp [CaterpillarTree, caterpillarAdjAux]
        exact ⟨rfl, Or.inr (by omega)⟩
      · rw [hwa, hwb]
        refine compl_adj_of_tree_adj_nonspec hf ?_ (Or.inl not_false)
        dsimp [CaterpillarTree, caterpillarAdjAux]
        exact ⟨Fin.ext (by dsimp; omega), by omega⟩
      · rw [hwa, hwb]
        by_cases h_end : (a.1 - 1) + 1 < k - 5
        · have h_eq_b : (⟨b.1 - 1, by omega⟩ : Fin (k - 4)) = ⟨(a.1 - 1) + 1, by omega⟩ :=
            Fin.ext (by dsimp; omega)
          rw [h_eq_b]
          exact h_tail (a.1 - 1) h_end (by omega)
        · refine compl_adj_of_tree_adj_nonspec hf ?_ (Or.inr ?_)
          · dsimp [CaterpillarTree, caterpillarAdjAux]; left; omega
          · dsimp [isSpecHTree]; omega
      · rw [hwa, hwb]
        refine compl_adj_of_tree_adj_nonspec hf ?_ (Or.inr (by dsimp [isSpecHTree]; decide))
        dsimp [CaterpillarTree, caterpillarAdjAux]
        exact ⟨by omega, rfl⟩
      · rw [hwa, hwb]
        refine compl_adj_of_tree_adj_nonspec hf ?_ (Or.inl (by dsimp [isSpecHTree]; decide))
        dsimp [CaterpillarTree, caterpillarAdjAux]
        decide
      · rw [hwa, hwb]
        exact h_star
    · intro a b hab
      exact compl_nonadj_of_tree_nonadj hf
        (caterpillarCase2Vert_nonconsec_nonadj hk r₀ hr₀_ge1 hr₀_lt a b hab)
  intro hFree
  exact hFree ⟨g, h_eq⟩

/--
**Proposition 5(1), Step C Case 3 (`caterpillarCase3Fun`, $\sigma_1 = \dots = \sigma_{k-6} = \sigma_* = 1$)**:
For $k \ge 6$, the $k$-vertex sequence $(v_{p_1} - \dots - v_{p_{k-4}} - v_0 - v_7 - v_3 - v_2)$ in $V(G)$
routing through the external anchor $v_0$.
-/
def caterpillarCase3Fun (_hk : 6 ≤ k) (v₀ : V) (f : CaterpillarVert k ↪ V) (t : Fin k) : V :=
  if ht : t.1 < k - 4 then
    f (Sum.inl ⟨t.1, ht⟩)
  else if t.1 = k - 4 then
    v₀
  else if t.1 = k - 3 then
    f (Sum.inr (Sum.inl 5))
  else if t.1 = k - 2 then
    f (Sum.inr (Sum.inl 4))
  else
    f (Sum.inr (Sum.inl 1))

/-- Explicit 5-branch characterization of `caterpillarCase3Fun hk v₀ f t`. -/
theorem caterpillarCase3Fun_eq (hk : 6 ≤ k) (v₀ : V) (f : CaterpillarVert k ↪ V) (t : Fin k) :
    (∃ ht : t.1 < k - 4, caterpillarCase3Fun hk v₀ f t = f (Sum.inl ⟨t.1, ht⟩)) ∨
    (t.1 = k - 4 ∧ caterpillarCase3Fun hk v₀ f t = v₀) ∨
    (t.1 = k - 3 ∧ caterpillarCase3Fun hk v₀ f t = f (Sum.inr (Sum.inl 5))) ∨
    (t.1 = k - 2 ∧ caterpillarCase3Fun hk v₀ f t = f (Sum.inr (Sum.inl 4))) ∨
    (t.1 = k - 1 ∧ caterpillarCase3Fun hk v₀ f t = f (Sum.inr (Sum.inl 1))) := by
  have := t.2
  dsimp [caterpillarCase3Fun]
  split_ifs with h1 h2 h3 h4
  · exact Or.inl ⟨h1, rfl⟩
  · exact Or.inr (Or.inl ⟨h2, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h3, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h4, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, rfl⟩)))

/-- Injectivity of `caterpillarCase3Fun hk v₀ f` given `IsOpenIntervalRealization`. -/
theorem caterpillarCase3Fun_injective (hk : 6 ≤ k)
    (hf : IsOpenIntervalRealization (witnessHTree k) (specHTree k) G v₀ f) :
    Function.Injective (caterpillarCase3Fun hk v₀ f) := by
  intro a b heq
  rcases caterpillarCase3Fun_eq hk v₀ f a with
      ⟨ha1, hwa⟩ | ⟨ha1, hwa⟩ | ⟨ha1, hwa⟩ | ⟨ha1, hwa⟩ | ⟨ha1, hwa⟩ <;>
    rcases caterpillarCase3Fun_eq hk v₀ f b with
      ⟨hb1, hwb⟩ | ⟨hb1, hwb⟩ | ⟨hb1, hwb⟩ | ⟨hb1, hwb⟩ | ⟨hb1, hwb⟩ <;>
    rw [hwa, hwb] at heq
  · have h_inl : (⟨a.1, ha1⟩ : Fin (k - 4)) = ⟨b.1, hb1⟩ := Sum.inl.inj (f.injective heq)
    exact Fin.ext (Fin.mk.inj h_inl)
  · exact False.elim (hf.ne_ext _ heq)
  · cases f.injective heq
  · cases f.injective heq
  · cases f.injective heq
  · exact False.elim (hf.ne_ext _ heq.symm)
  · exact Fin.ext (by omega)
  · exact False.elim (hf.ne_ext _ heq.symm)
  · exact False.elim (hf.ne_ext _ heq.symm)
  · exact False.elim (hf.ne_ext _ heq.symm)
  · cases f.injective heq
  · exact False.elim (hf.ne_ext _ heq)
  · exact Fin.ext (by omega)
  · cases f.injective heq
  · cases f.injective heq
  · cases f.injective heq
  · exact False.elim (hf.ne_ext _ heq)
  · cases f.injective heq
  · exact Fin.ext (by omega)
  · cases f.injective heq
  · cases f.injective heq
  · exact False.elim (hf.ne_ext _ heq)
  · cases f.injective heq
  · cases f.injective heq
  · exact Fin.ext (by omega)

/--
**Proposition 5(1), Step C Case 3 (`caterpillar_routing_case3`, $\sigma_1 = \dots = \sigma_{k-6} = \sigma_* = 1$)**:
For $k \ge 6$ with $\sigma_1 = \dots = \sigma_{k-6} = \sigma_* = 1$ (`h_spine`, `h_star`), the $k$-vertex sequence
$(v_{p_1} - \dots - v_{p_{k-4}} - v_0 - v_7 - v_3 - v_2)$ embeds $P_k$ into $Gᶜ$ (equivalently `(pathGraph k)ᶜ` into `G`).
-/
theorem caterpillar_routing_case3 (hk : 6 ≤ k)
    (hf : IsOpenIntervalRealization (witnessHTree k) (specHTree k) G v₀ f)
    (h_star : Gᶜ.Adj (f (Sum.inr (Sum.inl 1))) (f (Sum.inr (Sum.inl 4))))
    (h_spine : ∀ (q : ℕ) (hq : q + 1 < k - 5),
      Gᶜ.Adj (f (Sum.inl ⟨q, by omega⟩)) (f (Sum.inl ⟨q + 1, by omega⟩))) :
    ¬IsInducedSubgraphFree G (pathGraph k)ᶜ := by
  let g : Fin k ↪ V := ⟨caterpillarCase3Fun hk v₀ f, caterpillarCase3Fun_injective hk hf⟩
  have h_eq : (pathGraph k)ᶜ = G.comap g := by
    refine comap_eq_pathGraph_compl_of_compl_path G g ?_ ?_
    · intro a ha
      let b : Fin k := ⟨a.1 + 1, ha⟩
      have hba : b.1 = a.1 + 1 := rfl
      change Gᶜ.Adj (caterpillarCase3Fun hk v₀ f a) (caterpillarCase3Fun hk v₀ f b)
      rcases caterpillarCase3Fun_eq hk v₀ f a with
          ⟨ha1, hwa⟩ | ⟨ha1, hwa⟩ | ⟨ha1, hwa⟩ | ⟨ha1, hwa⟩ | ⟨ha1, hwa⟩ <;>
        rcases caterpillarCase3Fun_eq hk v₀ f b with
          ⟨hb1, hwb⟩ | ⟨hb1, hwb⟩ | ⟨hb1, hwb⟩ | ⟨hb1, hwb⟩ | ⟨hb1, hwb⟩ <;>
        try omega
      · rw [hwa, hwb]
        by_cases h_sp : a.1 + 1 < k - 5
        · exact h_spine a.1 h_sp
        · refine compl_adj_of_tree_adj_nonspec hf ?_ (Or.inr ?_)
          · dsimp [CaterpillarTree, caterpillarAdjAux]; left; rfl
          · dsimp [isSpecHTree]; omega
      · rw [hwa, hwb]
        refine Gᶜ.symm (compl_adj_v0_of_nonspec hf ?_)
        dsimp [isSpecHTree]; omega
      · rw [hwa, hwb]
        refine compl_adj_v0_of_nonspec hf ?_
        dsimp [isSpecHTree]; decide
      · rw [hwa, hwb]
        refine compl_adj_of_tree_adj_nonspec hf ?_ (Or.inl (by dsimp [isSpecHTree]; decide))
        dsimp [CaterpillarTree, caterpillarAdjAux]; decide
      · rw [hwa, hwb]
        exact Gᶜ.symm h_star
    · intro a b hab
      change ¬Gᶜ.Adj (caterpillarCase3Fun hk v₀ f a) (caterpillarCase3Fun hk v₀ f b)
      rcases caterpillarCase3Fun_eq hk v₀ f a with
          ⟨ha1, hwa⟩ | ⟨ha1, hwa⟩ | ⟨ha1, hwa⟩ | ⟨ha1, hwa⟩ | ⟨ha1, hwa⟩ <;>
        rcases caterpillarCase3Fun_eq hk v₀ f b with
          ⟨hb1, hwb⟩ | ⟨hb1, hwb⟩ | ⟨hb1, hwb⟩ | ⟨hb1, hwb⟩ | ⟨hb1, hwb⟩ <;>
        try omega
      · rw [hwa, hwb]
        refine compl_nonadj_of_tree_nonadj hf ?_
        dsimp [CaterpillarTree, caterpillarAdjAux]; omega
      · rw [hwa, hwb]
        intro hadj
        refine compl_nonadj_v0_of_spec hf ?_ (Gᶜ.symm hadj)
        dsimp [isSpecHTree]; omega
      · rw [hwa, hwb]
        refine compl_nonadj_of_tree_nonadj hf ?_
        dsimp [CaterpillarTree, caterpillarAdjAux]; rintro ⟨_, h⟩; cases h
      · rw [hwa, hwb]
        refine compl_nonadj_of_tree_nonadj hf ?_
        dsimp [CaterpillarTree, caterpillarAdjAux]; rintro ⟨_, h⟩; cases h
      · rw [hwa, hwb]
        refine compl_nonadj_of_tree_nonadj hf ?_
        dsimp [CaterpillarTree, caterpillarAdjAux]; rintro ⟨_, h⟩; cases h
      · rw [hwa, hwb]
        refine compl_nonadj_v0_of_spec hf ?_
        dsimp [isSpecHTree]; decide
      · rw [hwa, hwb]
        refine compl_nonadj_v0_of_spec hf ?_
        dsimp [isSpecHTree]; decide
      · rw [hwa, hwb]
        refine compl_nonadj_of_tree_nonadj hf ?_
        dsimp [CaterpillarTree, caterpillarAdjAux]; decide
  intro hFree
  exact hFree ⟨g, h_eq⟩

/--
**Proposition 5(1), Step C Synthesis (`witnessHTree_openIntervalRealization_embeds_PkCompl`)**:
For every integer $k \ge 6$, any open-interval realization of `(witnessHTree k, specHTree k)` around `v₀`
in a graph `G` embeds `(pathGraph k)ᶜ` via exhaustive boolean routing across $(\sigma_1, \dots, \sigma_{k-6}, \sigma_*)$.
-/
theorem witnessHTree_openIntervalRealization_embeds_PkCompl (hk : 6 ≤ k)
    (hf : IsOpenIntervalRealization (witnessHTree k) (specHTree k) G v₀ f) :
    ¬IsInducedSubgraphFree G (pathGraph k)ᶜ := by
  classical
  -- Branch on σ_* = 1 (whether v₂v₃ ∈ E(Gᶜ)).
  by_cases h_star : Gᶜ.Adj (f (Sum.inr (Sum.inl 1))) (f (Sum.inr (Sum.inl 4)))
  · let P_spine (q : ℕ) : Prop :=
      ∀ (hq : q + 1 < k - 5), Gᶜ.Adj (f (Sum.inl ⟨q, by omega⟩)) (f (Sum.inl ⟨q + 1, by omega⟩))
    -- Branch on whether all spine special edges have σ_q = 1 (Case 3) or some σ_q = 0 (Case 2, taking largest i_max).
    by_cases h_all : ∀ q ∈ Finset.range (k - 6), P_spine q
    · refine caterpillar_routing_case3 hk hf h_star (fun q hq => ?_)
      exact h_all q (Finset.mem_range.mpr (by omega)) hq
    · push_neg at h_all
      rcases h_all with ⟨q₀, hq₀_mem, hq₀_not⟩
      let S_zero : Finset ℕ := (Finset.range (k - 6)).filter (fun q => ¬P_spine q)
      have hS_ne : S_zero.Nonempty := ⟨q₀, Finset.mem_filter.mpr ⟨hq₀_mem, hq₀_not⟩⟩
      let i_max : ℕ := S_zero.max' hS_ne
      have hi_mem : i_max ∈ S_zero := S_zero.max'_mem hS_ne
      have hi_lt : i_max < k - 6 := Finset.mem_range.mp (Finset.mem_filter.mp hi_mem).1
      let r₀ : Fin (k - 4) := ⟨i_max + 1, by omega⟩
      have hr₀_ge1 : 1 ≤ r₀.1 := by dsimp [r₀]; omega
      have hr₀_lt : r₀.1 < k - 5 := by dsimp [r₀]; omega
      refine caterpillar_routing_case2 hk hf r₀ hr₀_ge1 hr₀_lt h_star (fun q hq hr₀_le => ?_)
      have hq_gt : i_max < q := by dsimp [r₀] at hr₀_le; omega
      have hq_not_mem : q ∉ S_zero := fun hmem => Nat.not_le.mpr hq_gt (S_zero.le_max' q hmem)
      have hq_range : q ∈ Finset.range (k - 6) := Finset.mem_range.mpr (by omega)
      have hP_q : P_spine q := by
        by_contra hnot
        exact hq_not_mem (Finset.mem_filter.mpr ⟨hq_range, hnot⟩)
      exact hP_q hq
  · -- Case 1: σ_* = 0.
    exact caterpillar_routing_case1 hk hf

end CaterpillarRealization

/--
**Proposition 5(1) (`isThresholdedWonderful_Pk_of_caterpillar_pair`)**:
For every integer $k \ge 6$, whenever `HasPairErdosHajnalProp (pathGraph k) (CaterpillarTree k)` holds,
`IsThresholdedWonderful (pathGraph k)` holds via `witnessHTree k = (CaterpillarTree k)ᶜ`.
-/
theorem isThresholdedWonderful_Pk_of_caterpillar_pair (k : ℕ) (hk : 6 ≤ k)
    (h_pair : HasPairErdosHajnalProp (pathGraph k) (CaterpillarTree k)) :
    IsThresholdedWonderful (pathGraph k) :=
  isThresholdedWonderful_of_openIntervalWitness_pair (pathGraph k) (witnessHTree k) (specHTree k)
    h_pair.compl
    (fun _ _ _ _ _ _ hf => witnessHTree_openIntervalRealization_embeds_PkCompl hk hf)

/-! ### Axiom Verification -/

#print axioms isThresholdedWonderful_of_openIntervalWitness_pair
#print axioms isThresholdedWonderful_of_openIntervalWitness
#print axioms hasErdosHajnalProp_witnessH7
#print axioms isThresholdedWonderful_P7
#print axioms hasErdosHajnalProp_witnessH8_of_P7
#print axioms isThresholdedWonderful_P8_of_P7
#print axioms hasErdosHajnalProp_witnessH9_of_P8
#print axioms isThresholdedWonderful_P9_of_P8
#print axioms caterpillarTree_isAcyclic
#print axioms caterpillarTree_mono_embedding
#print axioms isThresholdedWonderful_Pk_of_caterpillar_pair

end ErdosHajnalGen

