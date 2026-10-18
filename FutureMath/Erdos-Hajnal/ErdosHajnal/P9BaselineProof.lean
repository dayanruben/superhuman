/-
Copyright 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosHajnal.BasicLemmas
import ErdosHajnal.BirdBroomsForestsAndTowers
import ErdosHajnal.CombModules
import ErdosHajnal.Defs
import ErdosHajnal.GallaiAndCombDichotomy
import ErdosHajnal.GenDefs
import ErdosHajnal.LayoutAndSparsification
import ErdosHajnal.P6Baseline
import ErdosHajnal.RecursiveGallaiAndStage1
import ErdosHajnal.Stage2Reduction
import ErdosHajnal.Stage2Witnesses
import ErdosHajnal.SymmetricStage12Interface
import ErdosHajnal.ViralityAndClosures
import ErdosHajnal.WitnessGraph

/-!
# Synthesis of Main Theorem (A), (B), and (C) (`ErdosHajnalGeneralization_readable.tex` & `main.tex`)

This file synthesizes the five self-contained formalization modules (Section 6, `\ref{sec:synthesis}`,
and Theorem 1.1, `\ref{thm:main}`, of `ErdosHajnalGeneralization_readable.tex`; Section 6 of `main.tex`):
- `ViralityAndClosures`: Theorems 2, 3, and 4 (Rödl's Theorem, $\mathcal{EH} \iff \text{Poly-Rödl} \iff \text{Viral}$
  via Kleitman–Winston graph containers, substitution closure, simultaneous leaf/co-leaf viral closure,
  and Master Two-Graph Closure $\mathcal{J}(\mathcal{B}) \times \overline{\mathcal{J}(\mathcal{B})} \subseteq \mathcal{EH}$).
- `SymmetricStage12Interface`: Lemmas 2, 4, 5, and 7 (co-sparse peeling, Seinsche cograph refinement,
  $x_{\mathrm{sp}}$-independent symmetric layout refinement, and one-shot viral purification on `(GN1)`
  at coupled sparsity $x_{\mathrm{sp}} = \varepsilon_{\mathrm{GN}}^{3d} = y^{3ad}$).
- `Stage2Witnesses`: Propositions 3 and 5 (explicit pure-substitution witnesses
  $(H_{(7)}, S_{\mathrm{spec}})$ for $P_7$, $(H^{(8)}, S^{(8)})$ for $P_8$, $(H^{(9)}, S^{(9)})$ for $P_9$,
  and caterpillar co-tree witness $(H_{\mathrm{tree}}^{(k)}, S^{(k)}) = (\overline{T_k}, S^{(k)})$ for all $k \ge 6$).
- `RecursiveGallaiAndStage1`: Lemmas 8–13, Propositions 1, 2, 4, and Theorem 7(1)–(2) ($p_{\mathrm{cap}}$-decoupled
  Gallai core extraction, $\Phi_D$ active-leaf split trees, per-handle $s$-stems, universal depth-$r$
  neighborhood modularity, and Regime A/B stopping threshold $L'_{\max} := k'$).
- `BirdBroomsForestsAndTowers`: Proposition 6 ($\mathrm{Bird}, \overline{\mathrm{Bird}} \in \mathcal{EH}$,
  opposite-chirality forest pairs $\{F_1, \overline{F_2}\}$, hooked-claws $\{P_t, \operatorname{Hook}_4(Q, S)\}$,
  $(s, d)$-brooms $B(s, d)$, and infinite prime non-split towers $\{H_{t+k}^{(t)}\}_{k \ge 0}$).

In `Proof.Erdos61`, we prove all main theorems stated in `Problem.lean` (verified via
`leanprover/comparator` against `comparator.json`):
1. **Part (A) (`erdos_hajnal_p6`..`p9`, `erdos_61.variants.p6`..`p9`, `erdos_hajnal_p6_fintype`..`p9_fintype`,
   `main_theorem_A_paths_le_9`)**: Unconditional single-graph Erdős–Hajnal, polynomial Rödl, and virality
   properties for all paths $P_k$ and co-paths $\overline{P_k}$ ($1 \le k \le 9$).
2. **Part (B) (`main_theorem_B_comb_dichotomy`, `main_theorem_B_stage1_generalized_nice_all_paths`,
   `main_theorem_B_stage2_witnesses_and_caterpillar_iff`)**: Inductive depth-$r$ Stage-1 Comb/Co-Comb Dichotomy
   for all $r \ge 1$, unconditional coupled Stage-1 generalized niceness for all paths $P_k$ ($k \ge 6$),
   Stage-2 witness certifications for $P_7, P_8, P_9$, and exact caterpillar reduction
   $P_k \in \mathcal{EH} \iff \{P_k, T_k\} \in \mathcal{EH}$ for all $k \ge 6$.
3. **Part (C) (`main_theorem_C1_forest_pairs_and_closures`, `main_theorem_C2_hook4_and_brooms`,
   `main_theorem_C3_infinite_prime_towers`)**: $\mathrm{Bird}$, all opposite-chirality forest pairs
   $\{F_1, \overline{F_2}\}$, closures $\mathcal{J}(\mathcal{B}_9^*) \times \overline{\mathcal{J}(\mathcal{B}_9^*)}$
   and $\mathcal{H}(\mathcal{B}_9^*)$, hooked-claws $\operatorname{Hook}_4(Q, S)$, $(s, d)$-brooms $B(s, d)$,
   and infinite prime non-split towers $\{H_{t+k}^{(t)}\}_{k \ge 0}$ above every $P_t$ ($t \in \{6, 7, 8, 9\}$).
-/

open Filter Finset SimpleGraph Real ErdosHajnalP6 ErdosHajnalGen

namespace P9Baseline

/-! ### Section 1: General Monotonicity, Complement Symmetry, and Substitution Helpers -/

/-- Hereditary monotonicity of `HasErdosHajnalProp` along an induced graph embedding $H_1 \hookrightarrow_g H_2$:
if $H_2 \in \mathcal{EH}$ and $H_1$ embeds as an induced subgraph into $H_2$, then $H_1 \in \mathcal{EH}$. -/
private theorem hasErdosHajnalProp_of_embedding {W₁ W₂ : Type*}
    {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂}
    (f : H₁ ↪g H₂) (h₂ : HasErdosHajnalProp H₂) : HasErdosHajnalProp H₁ := by
  obtain ⟨c, hc, hprop⟩ := h₂
  refine ⟨c, hc, fun V _ _ G hG => hprop V G ?_⟩
  rintro ⟨g, hg⟩
  refine hG ⟨f.toEmbedding.trans g, ?_⟩
  ext u v
  exact f.map_rel_iff.symm.trans (congr_arg (fun H : SimpleGraph W₂ => H.Adj (f u) (f v)) hg).to_iff

/-- Hereditary monotonicity of `HasPairErdosHajnalProp` along induced graph embeddings
$H_1 \hookrightarrow_g H_1'$ and $H_2 \hookrightarrow_g H_2'$. -/
private theorem hasPairErdosHajnalProp_of_embeddings {W₁ W₁' W₂ W₂' : Type*}
    {H₁ : SimpleGraph W₁} {H₁' : SimpleGraph W₁'}
    {H₂ : SimpleGraph W₂} {H₂' : SimpleGraph W₂'}
    (f₁ : H₁ ↪g H₁') (f₂ : H₂ ↪g H₂')
    (h : HasPairErdosHajnalProp H₁' H₂') : HasPairErdosHajnalProp H₁ H₂ := by
  obtain ⟨c, hc, hprop⟩ := h
  refine ⟨c, hc, fun V _ _ G hG₁ hG₂ => hprop V G ?_ ?_⟩
  · rintro ⟨g, hg⟩
    refine hG₁ ⟨f₁.toEmbedding.trans g, ?_⟩
    ext u v
    exact f₁.map_rel_iff.symm.trans (congr_arg (fun H : SimpleGraph W₁' => H.Adj (f₁ u) (f₁ v)) hg).to_iff
  · rintro ⟨g, hg⟩
    refine hG₂ ⟨f₂.toEmbedding.trans g, ?_⟩
    ext u v
    exact f₂.map_rel_iff.symm.trans (congr_arg (fun H : SimpleGraph W₂' => H.Adj (f₂ u) (f₂ v)) hg).to_iff

/-- Monotonicity of `HasPairErdosHajnalProp` from the first factor: if $H_1 \in \mathcal{EH}$,
then $\{H_1, H_2\} \in \mathcal{EH}$ for any graph $H_2$. -/
private theorem hasPairErdosHajnalProp_of_left {W₁ W₂ : Type*}
    {H₁ : SimpleGraph W₁} (H₂ : SimpleGraph W₂)
    (h₁ : HasErdosHajnalProp H₁) : HasPairErdosHajnalProp H₁ H₂ := by
  obtain ⟨c, hc, hprop⟩ := h₁
  exact ⟨c, hc, fun V _ _ G hG₁ _ => hprop V G hG₁⟩

/-- Monotonicity of `IsPairCoupledGeneralizedNice` from the first factor: if $H_1$ is coupled
Stage-1 generalized nice, then $\{H_1, H_2\}$ is coupled Stage-1 generalized nice for any $H_2$. -/
private theorem isPairCoupledGeneralizedNice_of_left {W₁ W₂ : Type*}
    {H₁ : SimpleGraph W₁} (H₂ : SimpleGraph W₂)
    (h₁ : IsCoupledGeneralizedNice H₁) : IsPairCoupledGeneralizedNice H₁ H₂ := by
  obtain ⟨c₁, c₂, c₃, c₄, c₅, c₆, c₇, c₈, c₉,
    hc₁, hc₂, hc₃, hc₄, hc₅, hc₆, hc₇, hc₈, hc₉, hprop⟩ := h₁
  refine ⟨c₁, c₂, c₃, c₄, c₅, c₆, c₇, c₈, c₉,
    hc₁, hc₂, hc₃, hc₄, hc₅, hc₆, hc₇, hc₈, hc₉, ?_⟩
  intro V _ _ G ε x_sp hε0 hε_half hx_lo hx_hi hG₁ _
  exact hprop V G ε x_sp hε0 hε_half hx_lo hx_hi hG₁

/-- Vertex substitution closure `HasErdosHajnalProp (substGraph H₁ v₀ H₂)` for arbitrary
finite types `W₁, W₂` (handling empty vertex types alongside Theorem 4(1) of `main.tex`). -/
private theorem hasErdosHajnalProp_substGraph_any
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
      exact hasErdosHajnalProp_of_embedding f h₁
    · haveI : IsEmpty {v : W₁ // v ≠ v₀} := not_nonempty_iff.mp hne₁
      haveI : IsEmpty ({v : W₁ // v ≠ v₀} ⊕ W₂) := instIsEmptySum
      refine ⟨1, zero_lt_one, fun V _ _ G hG => ?_⟩
      exfalso
      refine hG ⟨Function.Embedding.ofIsEmpty, ?_⟩
      ext a b
      exact isEmptyElim a

/-- Complement invariance of pairwise-pure blockades (`IsPureBlockadeIn`): a blockade is pairwise pure
in $\overline{G}$ if and only if it is pairwise pure in $G$. -/
private theorem isPureBlockadeIn_compl_of_pure {V : Type*} [Fintype V] [DecidableEq V]
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

/-- For a pairwise-pure blockade $B$ in $\overline{G}$, the pattern graph of $B$ in $G$ is the
complement of the pattern graph of $B$ in $\overline{G}$. -/
private theorem purePatternGraph_compl_eq {V : Type*} [Fintype V] [DecidableEq V]
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

/-- Complement symmetry of `IsCoupledGeneralizedNice` (using $\overline{P_4} \cong P_4$ on cograph
pattern graphs in `(GN3)`): if $H$ is coupled Stage-1 generalized nice, then so is $\overline{H}$. -/
private theorem isCoupledGeneralizedNice_compl {W : Type*} [Fintype W] [DecidableEq W]
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
    refine ⟨k, hk_lo, hk_hi, B, isPureBlockadeIn_compl_of_pure hB.1, ?_⟩
    rw [purePatternGraph_compl_eq hB.1]
    exact (isInducedSubgraphFree_compl_pathGraph4 (purePatternGraph Gᶜ B)).mpr hB.2
  · right; right; right
    refine ⟨S, ?_, hS_card⟩
    rcases hS_rest with h1 | h2
    · exact Or.inr h1
    · rw [compl_compl] at h2
      exact Or.inl h2

/-- Canonical induced graph embedding $P_j \hookrightarrow_g P_k$ for $j \le k$ via `Fin.castLEEmb`. -/
private def pathGraph_mono_embedding {j k : ℕ} (hjk : j ≤ k) : pathGraph j ↪g pathGraph k where
  toEmbedding := Fin.castLEEmb hjk
  map_rel_iff' := by
    intro a b
    simp [pathGraph_adj]

/-- A graph isomorphism $G_1 \simeq_g G_2$ induces a graph isomorphism $\overline{G_1} \simeq_g \overline{G_2}$
between their complements. -/
private def complIso {W₁ W₂ : Type*} {G₁ : SimpleGraph W₁} {G₂ : SimpleGraph W₂}
    (e : G₁ ≃g G₂) : G₁ᶜ ≃g G₂ᶜ where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro a b
    simp only [RelIso.coe_fn_toEquiv, SimpleGraph.compl_adj, ne_eq,
      EmbeddingLike.apply_eq_iff_eq, e.map_rel_iff]

/-! ### Section 2: Stage-1 Comb Dichotomy and Coupled Generalized Niceness for All Paths $P_k$ ($k \ge 6$) -/

/--
**Main Theorem (B)(1) (`main_theorem_B_comb_dichotomy`, Theorem 1.1(B)(1) & Theorem 4.7(1) of `ErdosHajnalGeneralization_readable.tex`; Theorem 7(1) of `main.tex`)**:
For every integer $r \ge 1$, the parameterized depth-$r$ Stage-1 Comb/Co-Comb Dichotomy
`Stage1CombCoCombDichotomyAt r` (`Proposition 2_r`) holds for all $\overline{P_{s+4+r}}$-free
combs and co-combs equipped with per-handle $s$-vertex external apex stems ($s \ge 1$).
-/
theorem main_theorem_B_comb_dichotomy :
    ∀ r : ℕ, 1 ≤ r → Stage1CombCoCombDichotomyAt r :=
  stage1_comb_cocomb_dichotomy_all_r

/-- Arithmetic lower bound $|F'| / \ell^{18} \le y^4 |F'| / \ell^2$ when $\ell \ge y^{-1/4}$. -/
private theorem comb_width_ge_card_div_pow_18 {V : Type*} (F' : Finset V) {y : ℝ} {ℓ : ℕ}
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

/-- Specialization of `Stage1CombCoCombDichotomyAt (k - 5)` ($k \ge 6$) at $s = 1$, $L_{\max} = \ell \ge 64$,
and standard cap $p_{\mathrm{cap}} = \lceil x^{-2}\rceil$, combined with singleton pure blockade
extraction when $w < w_{\min}$ (Theorem 4.7(2) of `ErdosHajnalGeneralization_readable.tex`;
Theorem 7(2) of `main.tex`). -/
private theorem stage1_comb_dichotomy_for_paths_64 {V : Type} [Fintype V] [DecidableEq V]
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

/-- Co-sparse complete trigger peeling for $\overline{P_t}$-free graphs ($t \ge 2$, Lemma 2.6 of
`ErdosHajnalGeneralization_readable.tex`; Lemma 2 of `main.tex`), packaged with $a_{\mathrm{leaf}} = 6$
and $b_{\mathrm{leaf}} = 3t$ for Lemma 7(1). -/
private theorem path_cosparse_peel (t : ℕ) (ht : 2 ≤ t)
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

/-- Explicit constants $(c_1, \dots, c_9)$ certifying `SatisfiesPairCoupledGenNiceAt (pathGraph k) (pathGraph k)`
for every $k \ge 6$ via Lemma 7(1) (`pair_coupled_generalized_nice_of_comb_dichotomy_explicit`). -/
private theorem exists_satisfiesPairCoupledGenNiceAt_pathGraph (k : ℕ) (hk : 6 ≤ k) :
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
    (fun V _ _ G F' y hG₁ _ => path_cosparse_peel k hk2 V G F' y hG₁)
    (fun V _ _ G F' x y ℓ a B v hG₁ _ hx_pos hxy hy_ub hℓ_lo hℓ_hi hℓ_64 hcomb hapex => by
      right
      have hy0 : 0 < y := hx_pos.trans_le hxy
      have hw_ge_S := comb_width_ge_card_div_pow_18 F' hy0 hℓ_lo
      obtain ⟨k', hℓ_k', hk'_p, U, hU⟩ :=
        stage1_comb_dichotomy_for_paths_64 hk hx_pos hxy hy_ub hℓ_64 hℓ_hi hG₁ hcomb hapex hw_ge_S
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

/--
**Main Theorem (B)(2) (`main_theorem_B_stage1_generalized_nice_all_paths`, Theorem 1.1(B)(2) & Theorem 4.7(2) of `ErdosHajnalGeneralization_readable.tex`; Theorem 7(2) of `main.tex`)**:
For every integer $k \ge 6$, both $P_k$ (`pathGraph k`) and $\overline{P_k}$ (`(pathGraph k)ᶜ`)
are unconditionally coupled Stage-1 generalized nice (`IsCoupledGeneralizedNice`).
-/
theorem main_theorem_B_stage1_generalized_nice_all_paths :
    ∀ k : ℕ, 6 ≤ k →
      IsCoupledGeneralizedNice (pathGraph k) ∧
      IsCoupledGeneralizedNice (pathGraph k)ᶜ := by
  intro k hk
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hGN⟩ :=
    exists_satisfiesPairCoupledGenNiceAt_pathGraph k hk
  have h1 : IsCoupledGeneralizedNice (pathGraph k) :=
    isCoupledGeneralizedNice_of_pair hGN.to_isPairCoupledGeneralizedNice
  exact ⟨h1, isCoupledGeneralizedNice_compl h1⟩

/-! ### Section 3: Master Stage-2 Path Step and Unconditional Erdős–Hajnal for $P_6, P_7, P_8, P_9$ -/

/-- Deleting the last vertex `m : Fin (m + 1)` of $P_{m+1}$ (`Fin.castSuccEmb`) yields $P_m$. -/
private theorem pathGraph_comap_castSuccEmb (m : ℕ) :
    (pathGraph (m + 1)).comap (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)) = pathGraph m := by
  ext a b
  simp [pathGraph_adj]

/-- Master inductive path step (`Lemma 2.11(2)` of `ErdosHajnalGeneralization_readable.tex`;
Lemma 7(2) of `main.tex`): for any $m \ge 5$, if $P_m \in \mathcal{EH}$ and $P_{m+1}$ is
Stage-2 thresholded wonderful (`IsThresholdedWonderful`), then both $\overline{P_{m+1}}$ and
$P_{m+1}$ satisfy the Erdős–Hajnal property. -/
private theorem hasErdosHajnalProp_pathGraph_succ_of_wonderful {m : ℕ} (hm : 5 ≤ m)
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
  have e_sub : (pathGraph (m + 1)).comap (Subtype.val : {w : Fin (m + 1) // w ≠ v₀} → Fin (m + 1)) ≃g
      pathGraph m :=
    pathGraph_comap_castSuccEmb m ▸ comapSubtypeNeLastIso m (pathGraph (m + 1))
  have h_prev_compl_eh : HasErdosHajnalProp ((pathGraph (m + 1)).comap
      (Subtype.val : {w : Fin (m + 1) // w ≠ v₀} → Fin (m + 1)))ᶜ :=
    hasErdosHajnalProp_of_iso (complIso e_sub).symm h_prev.compl
  haveI : Nonempty {w : Fin (m + 1) // w ≠ v₀} := ⟨⟨u₀, hu₀_ne⟩⟩
  have hviral : IsViral ((pathGraph (m + 1)).comap
      (Subtype.val : {w : Fin (m + 1) // w ≠ v₀} → Fin (m + 1)))ᶜ :=
    isViral_of_hasErdosHajnalProp h_prev_compl_eh
  obtain ⟨c₁, c₂, c₃, c₄, c₅, c₆, c₇, c₈, c₉, hc₂4, hc₆1, hc₇1, hc₇_le, hGN⟩ :=
    exists_satisfiesPairCoupledGenNiceAt_pathGraph (m + 1) (by omega)
  exact master_stage2_eh_of_coupled_gen_nice_and_wonderful
    (pathGraph (m + 1)) v₀ u₀ hu₀_ne hleaf hh hviral h_wond hc₂4 hc₆1 hc₇1 hc₇_le hGN

/-- Both $\overline{P_7}$ and $P_7$ satisfy the Erdős–Hajnal property (Theorem 3.11 of
`ErdosHajnalGeneralization_readable.tex`; Theorem 5 of `main.tex`). -/
private theorem hasErdosHajnalProp_P7_both :
    HasErdosHajnalProp (pathGraph 7)ᶜ ∧ HasErdosHajnalProp (pathGraph 7) :=
  hasErdosHajnalProp_pathGraph_succ_of_wonderful (by decide)
    ErdosHajnalP6.hasErdosHajnalProp_P6 isThresholdedWonderful_P7

/-- Unconditional Erdős–Hajnal property for $P_7$ (`pathGraph 7`). -/
private theorem hasErdosHajnalProp_P7 : HasErdosHajnalProp (pathGraph 7) :=
  hasErdosHajnalProp_P7_both.2

/-- The 11-vertex pure-substitution witness $H^{(8)}$ (`witnessH8`) satisfies the Erdős–Hajnal
property (Proposition 4.5(2) of `ErdosHajnalGeneralization_readable.tex`; Proposition 5(2) of `main.tex`). -/
private theorem hasErdosHajnalProp_witnessH8 : HasErdosHajnalProp witnessH8 :=
  hasErdosHajnalProp_witnessH8_of_P7 hasErdosHajnalProp_P7

/-- Unconditional thresholded wonderfulness of $P_8$ (`pathGraph 8`) certified by $(H^{(8)}, S^{(8)})$. -/
private theorem isThresholdedWonderful_P8 : IsThresholdedWonderful (pathGraph 8) :=
  isThresholdedWonderful_P8_of_P7 hasErdosHajnalProp_P7

/-- Both $\overline{P_8}$ and $P_8$ satisfy the Erdős–Hajnal property (Theorem 4.6 of
`ErdosHajnalGeneralization_readable.tex`; Theorem 6 of `main.tex`). -/
private theorem hasErdosHajnalProp_P8_both :
    HasErdosHajnalProp (pathGraph 8)ᶜ ∧ HasErdosHajnalProp (pathGraph 8) :=
  hasErdosHajnalProp_pathGraph_succ_of_wonderful (by decide)
    hasErdosHajnalProp_P7 isThresholdedWonderful_P8

/-- Unconditional Erdős–Hajnal property for $P_8$ (`pathGraph 8`). -/
private theorem hasErdosHajnalProp_P8 : HasErdosHajnalProp (pathGraph 8) :=
  hasErdosHajnalProp_P8_both.2

/-- The 20-vertex symmetric two-arm pure-substitution witness $H^{(9)}$ (`witnessH9`) satisfies the
Erdős–Hajnal property (Proposition 4.5(3) of `ErdosHajnalGeneralization_readable.tex`; Proposition 5(3) of `main.tex`). -/
private theorem hasErdosHajnalProp_witnessH9 : HasErdosHajnalProp witnessH9 :=
  hasErdosHajnalProp_witnessH9_of_P8 hasErdosHajnalProp_P8 hasErdosHajnalProp_substGraph_any

/-- Unconditional thresholded wonderfulness of $P_9$ (`pathGraph 9`) certified by $(H^{(9)}, S^{(9)})$. -/
private theorem isThresholdedWonderful_P9 : IsThresholdedWonderful (pathGraph 9) :=
  isThresholdedWonderful_P9_of_P8 hasErdosHajnalProp_P8 hasErdosHajnalProp_substGraph_any

/-- Both $\overline{P_9}$ and $P_9$ satisfy the Erdős–Hajnal property (Theorem 4.6 of
`ErdosHajnalGeneralization_readable.tex`; Theorem 6 of `main.tex`). -/
private theorem hasErdosHajnalProp_P9_both :
    HasErdosHajnalProp (pathGraph 9)ᶜ ∧ HasErdosHajnalProp (pathGraph 9) :=
  hasErdosHajnalProp_pathGraph_succ_of_wonderful (by decide)
    hasErdosHajnalProp_P8 isThresholdedWonderful_P9

/-- Unconditional Erdős–Hajnal property for $P_9$ (`pathGraph 9`). -/
private theorem hasErdosHajnalProp_P9 : HasErdosHajnalProp (pathGraph 9) :=
  hasErdosHajnalProp_P9_both.2

/-- Universal packaging of `HasErdosHajnalProp (pathGraph k)` into all three formulations of
`Problem.lean` (universal `Fin n`, `Erdos61.IsErdosHajnalLowerBound`, and general `Fintype`). -/
private theorem erdos_hajnal_pk_all_variants {k : ℕ} (h_eh : HasErdosHajnalProp (pathGraph k)) :
    ∃ c > (0 : ℝ),
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)),
        (¬∃ g : Fin k ↪ Fin n, pathGraph k = G.comap g) →
          (G.cliqueNum : ℝ) ≥ (n : ℝ) ^ c ∨ (G.indepNum : ℝ) ≥ (n : ℝ) ^ c) ∧
      _root_.Erdos61.IsErdosHajnalLowerBound (pathGraph k) (fun n : ℕ => (n : ℝ) ^ c) ∧
      (∀ (W : Type) [Fintype W] (G : SimpleGraph W),
        IsEmpty (pathGraph k ↪g G) →
          (G.cliqueNum : ℝ) ≥ (Fintype.card W : ℝ) ^ c ∨
          (G.indepNum : ℝ) ≥ (Fintype.card W : ℝ) ^ c) := by
  obtain ⟨c₀, hc₀, hprop⟩ := h_eh
  refine erdos_hajnal_all_n_of_large_n (pathGraph k) (le_refl 2) hc₀ ?_
  intro n _hn G hG
  simpa using hprop (Fin n) G hG

/--
**Universal Statement for $P_6$ (`erdos_hajnal_p6`, `FMBV4-016` / Theorem 1.1(A) of `ErdosHajnalGeneralization_readable.tex`)**:
Let $P_6$ be the 6-vertex path (`pathGraph 6`). There exists $c > 0$ such that every
induced-$P_6$-free graph $G$ on $n$ vertices (`Fin n`) has a clique or independent set of size at least $n^c$.
-/
theorem erdos_hajnal_p6 :
    ∃ c > (0 : ℝ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      (¬∃ g : Fin 6 ↪ Fin n, pathGraph 6 = G.comap g) →
        (G.cliqueNum : ℝ) ≥ (n : ℝ) ^ c ∨ (G.indepNum : ℝ) ≥ (n : ℝ) ^ c := by
  obtain ⟨c, hc, h1, _, _⟩ := ErdosHajnalP6.erdos_hajnal_p6_all_variants
  exact ⟨c, hc, h1⟩

/--
**Erdős Problem 61 ($P_6$ Variant, `erdos_61.variants.p6`)**:
Asymptotic (`atTop`) Erdős–Hajnal lower bound for `pathGraph 6`, matching the exact statement
format of `FormalConjectures/ErdosProblems/61.lean`.
-/
theorem erdos_61.variants.p6 :
    ∃ c > (0 : ℝ), _root_.Erdos61.IsErdosHajnalLowerBound (pathGraph 6) (fun n : ℕ => (n : ℝ) ^ c) := by
  obtain ⟨c, hc, _, h2, _⟩ := ErdosHajnalP6.erdos_hajnal_p6_all_variants
  exact ⟨c, hc, h2⟩

/--
**General Finite Type Statement for $P_6$ (`erdos_hajnal_p6_fintype`)**:
There exists $c > 0$ such that for any finite vertex type `V` and any graph `G : SimpleGraph V`
with no induced graph embedding of `pathGraph 6` (`IsEmpty (pathGraph 6 ↪g G)`), `G` has a clique
or independent set of size at least `(|V| : ℝ) ^ c`.
-/
theorem erdos_hajnal_p6_fintype :
    ∃ c > (0 : ℝ), ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      IsEmpty (pathGraph 6 ↪g G) →
        (G.cliqueNum : ℝ) ≥ (Fintype.card V : ℝ) ^ c ∨
        (G.indepNum : ℝ) ≥ (Fintype.card V : ℝ) ^ c := by
  obtain ⟨c, hc, _, _, h3⟩ := ErdosHajnalP6.erdos_hajnal_p6_all_variants
  exact ⟨c, hc, h3⟩

/--
**Universal Statement for $P_7$ (`erdos_hajnal_p7`, Theorem 3.11 of `ErdosHajnalGeneralization_readable.tex`; Theorem 5 of `main.tex`)**:
Let $P_7$ be the 7-vertex path (`pathGraph 7`). There exists $c > 0$ such that every
induced-$P_7$-free graph $G$ on $n$ vertices (`Fin n`) has a clique or independent set of size at least $n^c$.
-/
theorem erdos_hajnal_p7 :
    ∃ c > (0 : ℝ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      (¬∃ g : Fin 7 ↪ Fin n, pathGraph 7 = G.comap g) →
        (G.cliqueNum : ℝ) ≥ (n : ℝ) ^ c ∨ (G.indepNum : ℝ) ≥ (n : ℝ) ^ c := by
  obtain ⟨c, hc, h1, _, _⟩ := erdos_hajnal_pk_all_variants hasErdosHajnalProp_P7
  exact ⟨c, hc, h1⟩

/--
**Erdős Problem 61 ($P_7$ Variant, `erdos_61.variants.p7`)**:
Asymptotic (`atTop`) Erdős–Hajnal lower bound for `pathGraph 7` (`IsErdosHajnalLowerBound`).
-/
theorem erdos_61.variants.p7 :
    ∃ c > (0 : ℝ), _root_.Erdos61.IsErdosHajnalLowerBound (pathGraph 7) (fun n : ℕ => (n : ℝ) ^ c) := by
  obtain ⟨c, hc, _, h2, _⟩ := erdos_hajnal_pk_all_variants hasErdosHajnalProp_P7
  exact ⟨c, hc, h2⟩

/--
**General Finite Type Statement for $P_7$ (`erdos_hajnal_p7_fintype`)**:
There exists $c > 0$ such that for any finite vertex type `V` and any graph `G : SimpleGraph V`
with no induced graph embedding of `pathGraph 7` (`IsEmpty (pathGraph 7 ↪g G)`), `G` has a clique
or independent set of size at least `(|V| : ℝ) ^ c`.
-/
theorem erdos_hajnal_p7_fintype :
    ∃ c > (0 : ℝ), ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      IsEmpty (pathGraph 7 ↪g G) →
        (G.cliqueNum : ℝ) ≥ (Fintype.card V : ℝ) ^ c ∨
        (G.indepNum : ℝ) ≥ (Fintype.card V : ℝ) ^ c := by
  obtain ⟨c, hc, _, _, h3⟩ := erdos_hajnal_pk_all_variants hasErdosHajnalProp_P7
  exact ⟨c, hc, h3⟩

/--
**Universal Statement for $P_8$ (`erdos_hajnal_p8`, Theorem 4.6 of `ErdosHajnalGeneralization_readable.tex`; Theorem 6 of `main.tex`)**:
Let $P_8$ be the 8-vertex path (`pathGraph 8`). There exists $c > 0$ such that every
induced-$P_8$-free graph $G$ on $n$ vertices (`Fin n`) has a clique or independent set of size at least $n^c$.
-/
theorem erdos_hajnal_p8 :
    ∃ c > (0 : ℝ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      (¬∃ g : Fin 8 ↪ Fin n, pathGraph 8 = G.comap g) →
        (G.cliqueNum : ℝ) ≥ (n : ℝ) ^ c ∨ (G.indepNum : ℝ) ≥ (n : ℝ) ^ c := by
  obtain ⟨c, hc, h1, _, _⟩ := erdos_hajnal_pk_all_variants hasErdosHajnalProp_P8
  exact ⟨c, hc, h1⟩

/--
**Erdős Problem 61 ($P_8$ Variant, `erdos_61.variants.p8`)**:
Asymptotic (`atTop`) Erdős–Hajnal lower bound for `pathGraph 8` (`IsErdosHajnalLowerBound`).
-/
theorem erdos_61.variants.p8 :
    ∃ c > (0 : ℝ), _root_.Erdos61.IsErdosHajnalLowerBound (pathGraph 8) (fun n : ℕ => (n : ℝ) ^ c) := by
  obtain ⟨c, hc, _, h2, _⟩ := erdos_hajnal_pk_all_variants hasErdosHajnalProp_P8
  exact ⟨c, hc, h2⟩

/--
**General Finite Type Statement for $P_8$ (`erdos_hajnal_p8_fintype`)**:
There exists $c > 0$ such that for any finite vertex type `V` and any graph `G : SimpleGraph V`
with no induced graph embedding of `pathGraph 8` (`IsEmpty (pathGraph 8 ↪g G)`), `G` has a clique
or independent set of size at least `(|V| : ℝ) ^ c`.
-/
theorem erdos_hajnal_p8_fintype :
    ∃ c > (0 : ℝ), ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      IsEmpty (pathGraph 8 ↪g G) →
        (G.cliqueNum : ℝ) ≥ (Fintype.card V : ℝ) ^ c ∨
        (G.indepNum : ℝ) ≥ (Fintype.card V : ℝ) ^ c := by
  obtain ⟨c, hc, _, _, h3⟩ := erdos_hajnal_pk_all_variants hasErdosHajnalProp_P8
  exact ⟨c, hc, h3⟩

/--
**Universal Statement for $P_9$ (`erdos_hajnal_p9`, Theorem 4.6 of `ErdosHajnalGeneralization_readable.tex`; Theorem 6 of `main.tex`)**:
Let $P_9$ be the 9-vertex path (`pathGraph 9`). There exists $c > 0$ such that every
induced-$P_9$-free graph $G$ on $n$ vertices (`Fin n`) has a clique or independent set of size at least $n^c$.
-/
theorem erdos_hajnal_p9 :
    ∃ c > (0 : ℝ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      (¬∃ g : Fin 9 ↪ Fin n, pathGraph 9 = G.comap g) →
        (G.cliqueNum : ℝ) ≥ (n : ℝ) ^ c ∨ (G.indepNum : ℝ) ≥ (n : ℝ) ^ c := by
  obtain ⟨c, hc, h1, _, _⟩ := erdos_hajnal_pk_all_variants hasErdosHajnalProp_P9
  exact ⟨c, hc, h1⟩

/--
**Erdős Problem 61 ($P_9$ Variant, `erdos_61.variants.p9`)**:
Asymptotic (`atTop`) Erdős–Hajnal lower bound for `pathGraph 9` (`IsErdosHajnalLowerBound`).
-/
theorem erdos_61.variants.p9 :
    ∃ c > (0 : ℝ), _root_.Erdos61.IsErdosHajnalLowerBound (pathGraph 9) (fun n : ℕ => (n : ℝ) ^ c) := by
  obtain ⟨c, hc, _, h2, _⟩ := erdos_hajnal_pk_all_variants hasErdosHajnalProp_P9
  exact ⟨c, hc, h2⟩

/--
**General Finite Type Statement for $P_9$ (`erdos_hajnal_p9_fintype`)**:
There exists $c > 0$ such that for any finite vertex type `V` and any graph `G : SimpleGraph V`
with no induced graph embedding of `pathGraph 9` (`IsEmpty (pathGraph 9 ↪g G)`), `G` has a clique
or independent set of size at least `(|V| : ℝ) ^ c`.
-/
theorem erdos_hajnal_p9_fintype :
    ∃ c > (0 : ℝ), ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      IsEmpty (pathGraph 9 ↪g G) →
        (G.cliqueNum : ℝ) ≥ (Fintype.card V : ℝ) ^ c ∨
        (G.indepNum : ℝ) ≥ (Fintype.card V : ℝ) ^ c := by
  obtain ⟨c, hc, _, _, h3⟩ := erdos_hajnal_pk_all_variants hasErdosHajnalProp_P9
  exact ⟨c, hc, h3⟩

/-- Every path $P_k$ (`pathGraph k`) with $k \le 9$ satisfies the Erdős–Hajnal property
(combining $P_6 \in \mathcal{EH}$ with hereditary embedding for $k \le 6$, and $P_7, P_8, P_9 \in \mathcal{EH}$). -/
private theorem hasErdosHajnalProp_pathGraph_le_9 (k : ℕ) (hk : k ≤ 9) :
    HasErdosHajnalProp (pathGraph k) := by
  by_cases hk6 : k ≤ 6
  · exact hasErdosHajnalProp_of_embedding (pathGraph_mono_embedding hk6)
      ErdosHajnalP6.hasErdosHajnalProp_P6
  · have hk_cases : k = 7 ∨ k = 8 ∨ k = 9 := by omega
    rcases hk_cases with rfl | rfl | rfl
    · exact hasErdosHajnalProp_P7
    · exact hasErdosHajnalProp_P8
    · exact hasErdosHajnalProp_P9

/--
**Main Theorem (A) (`main_theorem_A_paths_le_9`, Theorem 1.1(A) & Theorem 4.7(3) of `ErdosHajnalGeneralization_readable.tex`; Section 2 & Theorem 7(3) of `main.tex`)**:
For every integer $k$ with $1 \le k \le 9$, both $P_k$ (`pathGraph k`) and $\overline{P_k}$
(`(pathGraph k)ᶜ`) unconditionally satisfy the Erdős–Hajnal property (`HasErdosHajnalProp`),
the polynomial Rödl property (`HasPolyRodlProp`), and Kleitman–Winston virality (`IsViral`).
-/
theorem main_theorem_A_paths_le_9 :
    ∀ k : ℕ, 1 ≤ k → k ≤ 9 →
      HasErdosHajnalProp (pathGraph k) ∧
      HasErdosHajnalProp (pathGraph k)ᶜ ∧
      HasPolyRodlProp (pathGraph k) ∧
      HasPolyRodlProp (pathGraph k)ᶜ ∧
      IsViral (pathGraph k) ∧
      IsViral (pathGraph k)ᶜ := by
  intro k hk1 hk9
  have h_eh := hasErdosHajnalProp_pathGraph_le_9 k hk9
  have h_eh_c := h_eh.compl
  haveI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  have h_equiv := eh_iff_polyRodl_iff_isViral (pathGraph k)
  have h_equiv_c := eh_iff_polyRodl_iff_isViral (pathGraph k)ᶜ
  have h_rodl := h_equiv.1.mp h_eh
  have h_rodl_c := h_equiv_c.1.mp h_eh_c
  have h_viral := h_equiv.2.mp h_rodl
  have h_viral_c := h_equiv_c.2.mp h_rodl_c
  exact ⟨h_eh, h_eh_c, h_rodl, h_rodl_c, h_viral, h_viral_c⟩

/-! ### Section 4: Stage-2 Witnesses and Caterpillar Equivalence (`main_theorem_B_stage2_witnesses_and_caterpillar_iff`) -/

/-- Reverse direction of the exact Stage-2 caterpillar reduction (Theorem 4.7(3) of
`ErdosHajnalGeneralization_readable.tex`; Theorem 7(3) of `main.tex`): for every $k \ge 6$,
if $\{P_k, T_k\} \in \mathcal{EH}$, then $P_k \in \mathcal{EH}$ by strong induction on $k \ge 6$
using induced monotonicity $P_m \hookrightarrow_g P_{m+1}$ and $T_m \hookrightarrow_g T_{m+1}$. -/
private theorem hasErdosHajnalProp_pathGraph_of_caterpillar_pair :
    ∀ k : ℕ, 6 ≤ k →
      HasPairErdosHajnalProp (pathGraph k) (CaterpillarTree k) →
      HasErdosHajnalProp (pathGraph k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk h_pair
    rcases eq_or_lt_of_le hk with rfl | hk_gt6
    · exact ErdosHajnalP6.hasErdosHajnalProp_P6
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      have hm6 : 6 ≤ m := by omega
      have h_pair_m : HasPairErdosHajnalProp (pathGraph m) (CaterpillarTree m) :=
        hasPairErdosHajnalProp_of_embeddings
          (pathGraph_mono_embedding (Nat.le_succ m))
          (caterpillarTree_mono_embedding hm6 (Nat.le_succ m))
          h_pair
      have h_prev : HasErdosHajnalProp (pathGraph m) := ih m (Nat.lt_succ_self m) hm6 h_pair_m
      have h_wond : IsThresholdedWonderful (pathGraph (m + 1)) :=
        isThresholdedWonderful_Pk_of_caterpillar_pair (m + 1) hk h_pair
      exact (hasErdosHajnalProp_pathGraph_succ_of_wonderful (by omega) h_prev h_wond).2

/--
**Main Theorem (B)(3) (`main_theorem_B_stage2_witnesses_and_caterpillar_iff`, Theorem 1.1(B)(3), Proposition 3.10, Proposition 4.5, & Theorem 4.7(3) of `ErdosHajnalGeneralization_readable.tex`; Propositions 3 & 5 and Theorem 7(3) of `main.tex`)**:
1. The explicit pure-substitution witnesses `witnessH7` ($H_{(7)}$, 10 vertices), `witnessH8`
   ($H^{(8)}$, 11 vertices), and `witnessH9` ($H^{(9)}$, 20 vertices) satisfy `HasErdosHajnalProp`
   and certify that $P_7$, $P_8$, and $P_9$ satisfy `IsThresholdedWonderful`;
2. For every integer $k \ge 6$, $P_k$ (`pathGraph k`) satisfies the Erdős–Hajnal property if and
   only if the two-graph family $\{P_k, T_k\}$ (`pathGraph k` and `CaterpillarTree k`) satisfies
   the Erdős–Hajnal property (`HasPairErdosHajnalProp`).
-/
theorem main_theorem_B_stage2_witnesses_and_caterpillar_iff :
    (HasErdosHajnalProp witnessH7 ∧ IsThresholdedWonderful (pathGraph 7)) ∧
    (HasErdosHajnalProp witnessH8 ∧ IsThresholdedWonderful (pathGraph 8)) ∧
    (HasErdosHajnalProp witnessH9 ∧ IsThresholdedWonderful (pathGraph 9)) ∧
    (∀ k : ℕ, 6 ≤ k →
      (HasErdosHajnalProp (pathGraph k) ↔
       HasPairErdosHajnalProp (pathGraph k) (CaterpillarTree k))) := by
  refine ⟨⟨hasErdosHajnalProp_witnessH7, isThresholdedWonderful_P7⟩,
    ⟨hasErdosHajnalProp_witnessH8, isThresholdedWonderful_P8⟩,
    ⟨hasErdosHajnalProp_witnessH9, isThresholdedWonderful_P9⟩, ?_⟩
  intro k hk
  refine ⟨fun h => hasPairErdosHajnalProp_of_left (CaterpillarTree k) h,
    hasErdosHajnalProp_pathGraph_of_caterpillar_pair k hk⟩

/-! ### Section 5: `BirdGraph`, Opposite-Chirality Forest Pairs, and Closures (`main_theorem_C1_forest_pairs_and_closures`) -/

/-- Explicit graph isomorphism $P_4[0 \leftarrow K_2] \simeq_g \mathrm{Bird} - b_6$
(deleting the degree-$1$ pendant leaf `5 : Fin 6` from `BirdGraph`). -/
private def substP4K2IsoBirdMinus5 :
    substGraph (pathGraph 4) 0 (⊤ : SimpleGraph (Fin 2)) ≃g
      BirdGraph.comap (Fin.castSuccEmb : Fin 5 ↪ Fin 6) where
  toFun
    | Sum.inr 0 => 1
    | Sum.inr 1 => 2
    | Sum.inl ⟨1, _⟩ => 0
    | Sum.inl ⟨2, _⟩ => 3
    | Sum.inl ⟨3, _⟩ => 4
    | Sum.inl ⟨⟨0, _⟩, hne⟩ => False.elim (hne rfl)
  invFun
    | 0 => Sum.inl ⟨1, by decide⟩
    | 1 => Sum.inr 0
    | 2 => Sum.inr 1
    | 3 => Sum.inl ⟨2, by decide⟩
    | 4 => Sum.inl ⟨3, by decide⟩
  left_inv x := by
    rcases x with ⟨u, hu⟩ | r
    · fin_cases u
      · exact False.elim (hu rfl)
      · rfl
      · rfl
      · rfl
    · fin_cases r <;> rfl
  right_inv y := by
    fin_cases y <;> rfl
  map_rel_iff' := by
    intro a b
    rcases a with ⟨u, hu⟩ | r <;> rcases b with ⟨v, hv⟩ | s
    · fin_cases u <;> fin_cases v <;>
        first | exact False.elim (hu rfl) | exact False.elim (hv rfl) | decide +revert
    · fin_cases u <;> fin_cases s <;>
        first | exact False.elim (hu rfl) | decide +revert
    · fin_cases r <;> fin_cases v <;>
        first | exact False.elim (hv rfl) | decide +revert
    · fin_cases r <;> fin_cases s <;> decide

/-- Leaf-reducibility of `BirdGraph`: deleting vertex `5 : Fin 6` ($b_6$) leaves $P_4[0 \leftarrow K_2] \in \mathcal{EH}$,
whose complement is viral (`IsViral`). -/
private theorem isViral_birdMinus5Compl :
    IsViral (BirdGraph.comap (Subtype.val : {w : Fin 6 // w ≠ 5} → Fin 6))ᶜ := by
  have hP4 : HasErdosHajnalProp (pathGraph 4) := hasErdosHajnalProp_pathGraph_le_9 4 (by decide)
  have h_subst : HasErdosHajnalProp (substGraph (pathGraph 4) 0 (⊤ : SimpleGraph (Fin 2))) :=
    hasErdosHajnalProp_substGraph (pathGraph 4) 0 (⊤ : SimpleGraph (Fin 2)) hP4 hasErdosHajnalProp_top_fin2
  have e_sub : BirdGraph.comap (Subtype.val : {w : Fin 6 // w ≠ 5} → Fin 6) ≃g
      substGraph (pathGraph 4) 0 (⊤ : SimpleGraph (Fin 2)) :=
    (comapSubtypeNeLastIso 5 BirdGraph).trans substP4K2IsoBirdMinus5.symm
  have h_eh_compl : HasErdosHajnalProp
      (BirdGraph.comap (Subtype.val : {w : Fin 6 // w ≠ 5} → Fin 6))ᶜ :=
    hasErdosHajnalProp_of_iso (complIso e_sub).symm h_subst.compl
  haveI : Nonempty {w : Fin 6 // w ≠ 5} := ⟨⟨0, by decide⟩⟩
  exact isViral_of_hasErdosHajnalProp h_eh_compl

/-- The 5-vertex Stage-2 witness $H_{\mathrm{Bird}} := \overline{\mathrm{Bird}} - b_1 \cong K_2[1 \leftarrow \overline{K_2}, 2 \leftarrow \overline{P_3}]$
(`witnessHBird`) satisfies the Erdős–Hajnal property (Proposition 5.1(1a) of `ErdosHajnalGeneralization_readable.tex`;
Proposition 6(1a) of `main.tex`). -/
private theorem hasErdosHajnalProp_witnessHBird : HasErdosHajnalProp witnessHBird := by
  have h1 := hasErdosHajnalProp_substGraph (⊤ : SimpleGraph (Fin 2)) 0 (⊥ : SimpleGraph (Fin 2))
    hasErdosHajnalProp_top_fin2 hasErdosHajnalProp_bot_fin2
  have hP3c : HasErdosHajnalProp (pathGraph 3)ᶜ :=
    (hasErdosHajnalProp_pathGraph_le_9 3 (by decide)).compl
  have h2 := hasErdosHajnalProp_substGraph _ (Sum.inl ⟨1, by decide⟩) ((pathGraph 3)ᶜ) h1 hP3c
  exact hasErdosHajnalProp_of_iso substK2ComplP3ComplIsoWitnessHBird h2

/-- Grouping anticonnected components of $M_T \setminus N_F(u)$ (each a proper module of $F[M_T]$
of intersection size $\le \tau$ with $M^*$) into a complete $(\ell, \tau)$-blockade in $F[M^*]$
when $|M^* \setminus N_F(u)| \ge 2 \ell \tau$. -/
private theorem exists_complete_blockade_of_bird_nonneighbor {V : Type*} [Fintype V] [DecidableEq V]
    {F : SimpleGraph V} {M_T M_star : Finset V} {u : V} {ℓ : ℕ} {τ : ℝ}
    (hMs_MT : M_star ⊆ M_T) (hτ_pos : 0 < τ)
    (h_mod : ∀ C : Finset V,
      IsAnticonnectedComponentOf F (M_T \ neighborFinsetIn F u M_T) C → IsProperModuleIn F M_T C)
    (h_small : ∀ X : Finset V,
      IsProperModuleIn F M_T X → (X ∩ M_star).Nonempty → ((X ∩ M_star).card : ℝ) ≤ τ)
    (h_deg : 2 * (ℓ : ℝ) * τ ≤ (((M_star) \ neighborFinsetIn F u M_star).card : ℝ)) :
    ∃ D : Fin ℓ → Finset V, IsCompleteBlockadeIn F M_star ℓ τ D := by
  let Z_T := M_T \ neighborFinsetIn F u M_T
  let Z_star := M_star \ neighborFinsetIn F u M_star
  obtain ⟨q, C, hC_fam⟩ := exists_anticonnectedComponentFamily F Z_T
  let C' : Fin q → Finset V := fun s => C s ∩ M_star
  have hC'_disj : ∀ s t : Fin q, s ≠ t → Disjoint (C' s) (C' t) :=
    fun s t hst => Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left (hC_fam.pairwise_disjoint s t hst))
  have hC'_comp : ∀ s t : Fin q, s ≠ t → IsCompletePair F (C' s) (C' t) := by
    intro s t hst x hx y hy
    have hcomp := (hC_fam.is_component s).isCompletePair_of_disjoint
      (hC_fam.is_component t) (hC_fam.pairwise_disjoint s t hst)
    exact hcomp x (Finset.mem_inter.mp hx).1 y (Finset.mem_inter.mp hy).1
  have hC'_union : Finset.univ.biUnion C' = Z_star := by
    ext x
    simp only [C', Z_star, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_inter, Finset.mem_sdiff, ErdosHajnalP6.mem_neighborFinsetIn_iff]
    constructor
    · rintro ⟨s, hxCs, hxMs⟩
      have hxZT := (hC_fam.is_component s).1 hxCs
      rw [Finset.mem_sdiff, ErdosHajnalP6.mem_neighborFinsetIn_iff] at hxZT
      exact ⟨hxMs, fun h => hxZT.2 ⟨hMs_MT hxMs, h.2⟩⟩
    · rintro ⟨hxMs, hnadj⟩
      have hxZT : x ∈ Z_T := by
        rw [Finset.mem_sdiff, ErdosHajnalP6.mem_neighborFinsetIn_iff]
        exact ⟨hMs_MT hxMs, fun h => hnadj ⟨hxMs, h.2⟩⟩
      rw [← hC_fam.biUnion_eq, Finset.mem_biUnion] at hxZT
      obtain ⟨s, _, hxCs⟩ := hxZT
      exact ⟨s, hxCs, hxMs⟩
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
    (fun s : Fin q => ((C' s).card : ℝ)) τ hτ_pos ℓ Finset.univ hC'_each (by linarith)
  let D : Fin ℓ → Finset V := fun j => (I j).biUnion C'
  have hD_card : ∀ j : Fin ℓ, (D j).card = ∑ s ∈ I j, (C' s).card :=
    fun j => Finset.card_biUnion (fun s _ t _ hst => hC'_disj s t hst)
  have hD_width : ∀ j : Fin ℓ, τ ≤ ((D j).card : ℝ) := by
    intro j
    rw [hD_card j, Nat.cast_sum]
    exact (hI_sub j).2
  have hD_ne : ∀ j : Fin ℓ, (D j).Nonempty := by
    intro j
    rw [← Finset.card_pos, ← @Nat.cast_pos ℝ]
    linarith [hD_width j]
  refine ⟨D, ⟨fun j => Finset.biUnion_subset.mpr (fun s _ => Finset.inter_subset_right),
    hD_ne, ?_, hD_width⟩, ?_⟩
  · intro j₁ j₂ hj
    rw [Finset.disjoint_biUnion_left]
    intro s hs
    rw [Finset.disjoint_biUnion_right]
    intro t ht
    have hst : s ≠ t := fun h => Finset.disjoint_left.mp (hI_disj j₁ j₂ hj) hs (h ▸ ht)
    exact hC'_disj s t hst
  · intro j₁ j₂ hj x hx y hy
    rcases Finset.mem_biUnion.mp hx with ⟨s, hs, hxCs⟩
    rcases Finset.mem_biUnion.mp hy with ⟨t, ht, hyCt⟩
    have hst : s ≠ t := fun h => Finset.disjoint_left.mp (hI_disj j₁ j₂ hj) hs (h ▸ ht)
    exact hC'_comp s t hst x hxCs y hyCt

set_option maxHeartbeats 800000 in
/-- Stage-1 comb dichotomy for $\overline{\mathrm{Bird}}$-free graphs with $C_{\mathrm{comb}} = 60$
and $p_{\mathrm{cap}} = \lceil x^{-2}\rceil$ (Proposition 5.1(1a) of `ErdosHajnalGeneralization_readable.tex`;
Proposition 6(1a) of `main.tex`). -/
private theorem bird_comb_dichotomy_for_stage1 {V : Type} [Fintype V] [DecidableEq V]
    {F : SimpleGraph V} {S : Finset V} {ℓ : ℕ} {x y w : ℝ}
    {a : Fin ℓ → V} {B : Fin ℓ → Finset V} {v : V}
    (hx_pos : 0 < x) (hxy : x ≤ y) (hy_ub : y ≤ (2 : ℝ)⁻¹ ^ 16)
    (hℓ_64 : 64 ≤ ℓ) (hℓ_high : (ℓ : ℝ) ≤ x⁻¹)
    (hfree : IsInducedSubgraphFree F BirdGraphᶜ)
    (hcomb : IsCombIn F S ℓ w a B)
    (hapex : IsCombExternalApex F S ℓ a B v)
    (hw_ge_S : (S.card : ℝ) / (ℓ : ℝ) ^ 18 ≤ w) :
    let p_cap := ⌈x ^ (-2 : ℝ)⌉₊
    ∃ k' : ℕ, ℓ ≤ k' ∧ k' ≤ p_cap ∧
      ∃ U : Fin k' → Finset V,
        IsPureBlockadeIn F S k' ((S.card : ℝ) / (k' : ℝ) ^ 60) U ∨
        IsWeaklySparseOrCoSparseBlockadeIn F S k' ((S.card : ℝ) / (k' : ℝ) ^ 60) x U := by
  intro p_cap
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
  have hℓ_le_pcap : ℓ ≤ p_cap := Nat.cast_le.mp (le_trans hℓ_high hx_inv_le_pcap)
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
  have hℓ_r : (64 : ℝ) ≤ (ℓ : ℝ) := Nat.ofNat_le_cast.mpr hℓ_64
  have hℓ_pos : (0 : ℝ) < (ℓ : ℝ) := by linarith
  have hℓ_p_r : (ℓ : ℝ) ≤ (p_cap : ℝ) := Nat.cast_le.mpr hℓ_le_pcap
  have hℓ_le_S : ℓ ≤ S.card := comb_blockade_card_ge_ell hcomb.is_blockade
  have hw_nn : 0 ≤ w := le_trans (by positivity) hw_ge_S
  let θ₁ : ℝ := x / (128 * (ℓ : ℝ) * (p_cap : ℝ))
  have hθ₁_pos : 0 < θ₁ := by dsimp [θ₁]; positivity
  have hθ₁_ub : θ₁ ≤ 1 / (64 * (ℓ : ℝ) ^ 2) := by
    dsimp [θ₁]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (ℓ : ℝ) ^ 2 ≤ (ℓ : ℝ) * (p_cap : ℝ) := by nlinarith
    nlinarith
  have hθ₁_lb : 1 / (128 * (p_cap : ℝ) ^ 3) ≤ θ₁ := by
    dsimp [θ₁]
    have h_den : 128 * (ℓ : ℝ) * (p_cap : ℝ) ≤ 128 * (p_cap : ℝ) ^ 2 := by nlinarith
    calc 1 / (128 * (p_cap : ℝ) ^ 3)
      _ = (p_cap : ℝ)⁻¹ / (128 * (p_cap : ℝ) ^ 2) := by field_simp
      _ ≤ x / (128 * (p_cap : ℝ) ^ 2) := div_le_div_of_nonneg_right hp_inv_le_x (by positivity)
      _ ≤ x / (128 * (ℓ : ℝ) * (p_cap : ℝ)) :=
        div_le_div_of_nonneg_left hx_pos.le (by positivity) h_den
  let w_min : ℝ := 64 * (p_cap : ℝ) ^ 2 * θ₁⁻¹ * (4 * (ℓ : ℝ)) ^ 16
  by_cases hw_min : w_min ≤ w
  · by_cases h_gc2_cap : ∃ (i : Fin ℓ) (Q : Fin p_cap → Finset V),
        IsPureBlockadeIn F (B i) p_cap
          (min θ₁ (1 / (64 * (p_cap : ℝ) ^ 2)) * (((B i).card : ℝ) / (ℓ : ℝ) ^ 8)) Q
    · obtain ⟨i, Q, hQ⟩ := h_gc2_cap
      refine ⟨p_cap, hℓ_le_pcap, le_rfl, Q, Or.inl ⟨(hQ.1.mono_ambient
        (hcomb.is_blockade.subset_ambient i)).mono_width ?_, hQ.2⟩⟩
      have h_min_ge : 1 / (128 * (p_cap : ℝ) ^ 3) ≤ min θ₁ (1 / (64 * (p_cap : ℝ) ^ 2)) := by
        refine le_min hθ₁_lb ?_
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      have hB_ge_S : (S.card : ℝ) / (p_cap : ℝ) ^ 26 ≤ ((B i).card : ℝ) / (ℓ : ℝ) ^ 8 := by
        have h18 : (S.card : ℝ) / (p_cap : ℝ) ^ 18 ≤ ((B i).card : ℝ) := by
          calc (S.card : ℝ) / (p_cap : ℝ) ^ 18
            _ ≤ (S.card : ℝ) / (ℓ : ℝ) ^ 18 :=
              div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
                (pow_le_pow_left₀ (by positivity) hℓ_p_r 18)
            _ ≤ w := hw_ge_S
            _ ≤ ((B i).card : ℝ) := hcomb.is_blockade.width_ge i
        calc (S.card : ℝ) / (p_cap : ℝ) ^ 26
          _ = ((S.card : ℝ) / (p_cap : ℝ) ^ 18) / (p_cap : ℝ) ^ 8 := by
            rw [div_div, ← pow_add]
          _ ≤ ((B i).card : ℝ) / (p_cap : ℝ) ^ 8 :=
            div_le_div_of_nonneg_right h18 (by positivity)
          _ ≤ ((B i).card : ℝ) / (ℓ : ℝ) ^ 8 :=
            div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
              (pow_le_pow_left₀ (by positivity) hℓ_p_r 8)
      have h128 : (128 : ℝ) * (p_cap : ℝ) ^ 29 ≤ (p_cap : ℝ) ^ 60 := by
        have h2_7 : (128 : ℝ) ≤ (p_cap : ℝ) ^ 2 := by nlinarith
        calc (128 : ℝ) * (p_cap : ℝ) ^ 29
          _ ≤ (p_cap : ℝ) ^ 2 * (p_cap : ℝ) ^ 29 :=
            mul_le_mul_of_nonneg_right h2_7 (by positivity)
          _ = (p_cap : ℝ) ^ 31 := by rw [← pow_add]
          _ ≤ (p_cap : ℝ) ^ 60 := pow_le_pow_right₀ hp_ge1 (by omega)
      calc (S.card : ℝ) / (p_cap : ℝ) ^ 60
        _ ≤ (S.card : ℝ) / (128 * (p_cap : ℝ) ^ 29) :=
          div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) h128
        _ = (1 / (128 * (p_cap : ℝ) ^ 3)) * ((S.card : ℝ) / (p_cap : ℝ) ^ 26) := by
          rw [show (29 : ℕ) = 3 + 26 by rfl, pow_add]; ring
        _ ≤ min θ₁ (1 / (64 * (p_cap : ℝ) ^ 2)) * (((B i).card : ℝ) / (ℓ : ℝ) ^ 8) :=
          mul_le_mul h_min_ge hB_ge_S (by positivity) (by positivity)
    · by_cases h_gc2_split : ∃ (i : Fin ℓ), ℓ < p_cap ∧ ∃ (k' : ℕ) (U : Fin k' → Finset V),
          ℓ ≤ k' ∧ k' < p_cap ∧
          IsPureBlockadeIn F (B i) k' (((B i).card : ℝ) / (64 * (k' : ℝ) ^ 10)) U
      · obtain ⟨i, _, k', U, hℓ_k', hk'_p, hU⟩ := h_gc2_split
        refine ⟨k', hℓ_k', hk'_p.le, U, Or.inl ⟨(hU.1.mono_ambient
          (hcomb.is_blockade.subset_ambient i)).mono_width ?_, hU.2⟩⟩
        have hk'_r : (64 : ℝ) ≤ (k' : ℝ) := Nat.ofNat_le_cast.mpr (le_trans hℓ_64 hℓ_k')
        have hk'_ge1 : (1 : ℝ) ≤ (k' : ℝ) := by linarith
        have hB_ge : (S.card : ℝ) / (k' : ℝ) ^ 18 ≤ ((B i).card : ℝ) := by
          calc (S.card : ℝ) / (k' : ℝ) ^ 18
            _ ≤ (S.card : ℝ) / (ℓ : ℝ) ^ 18 :=
              div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
                (pow_le_pow_left₀ (by positivity) (Nat.cast_le.mpr hℓ_k') 18)
            _ ≤ w := hw_ge_S
            _ ≤ ((B i).card : ℝ) := hcomb.is_blockade.width_ge i
        have h64_k : 64 * (k' : ℝ) ^ 28 ≤ (k' : ℝ) ^ 60 := by
          calc 64 * (k' : ℝ) ^ 28
            _ ≤ (k' : ℝ) * (k' : ℝ) ^ 28 := mul_le_mul_of_nonneg_right hk'_r (by positivity)
            _ = (k' : ℝ) ^ 29 := by ring
            _ ≤ (k' : ℝ) ^ 60 := pow_le_pow_right₀ hk'_ge1 (by omega)
        calc (S.card : ℝ) / (k' : ℝ) ^ 60
          _ ≤ (S.card : ℝ) / (64 * (k' : ℝ) ^ 28) :=
            div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) h64_k
          _ = ((S.card : ℝ) / (k' : ℝ) ^ 18) / (64 * (k' : ℝ) ^ 10) := by
            rw [show (28 : ℕ) = 18 + 10 by rfl, pow_add]; ring
          _ ≤ ((B i).card : ℝ) / (64 * (k' : ℝ) ^ 10) :=
            div_le_div_of_nonneg_right hB_ge (by positivity)
      · have h_all_core : ∀ i : Fin ℓ,
            ∃ M_T : Finset V, M_T ⊆ B i ∧
              ∃ M_star : Finset V, M_star ⊆ M_T ∧
                (15 / 64 : ℝ) * (w / (ℓ : ℝ) ^ 8) < (M_star.card : ℝ) ∧
                (∀ X : Finset V, IsProperModuleIn F M_T X → (X ∩ M_star).Nonempty →
                  X ⊆ M_star ∧ (X.card : ℝ) < 5 * θ₁ * (M_star.card : ℝ)) := by
          intro i
          have hBi_card : w_min ≤ ((B i).card : ℝ) := le_trans hw_min (hcomb.is_blockade.width_ge i)
          rcases iterated_gallai_core_decomposition F (B i) ℓ p_cap ℓ θ₁
              (by omega) hℓ_le_pcap (by omega) le_rfl hθ₁_pos hθ₁_ub hBi_card with
            ⟨W, hWB, hW_gt, M_T, hMT_W, _, _, M_star, hMs_MT, hMs_gt, hMs_prop⟩ | h_sp | ⟨Q, hQ⟩
          · have hW_w : w / (ℓ : ℝ) ^ 8 < (W.card : ℝ) :=
              lt_of_le_of_lt (div_le_div_of_nonneg_right (hcomb.is_blockade.width_ge i) (by positivity)) hW_gt
            exact ⟨M_T, hMT_W.trans hWB, M_star, hMs_MT, by linarith, hMs_prop⟩
          · exact False.elim (h_gc2_split ⟨i, h_sp⟩)
          · exact False.elim (h_gc2_cap ⟨i, Q, hQ⟩)
        obtain ⟨M_T, hMT_all⟩ := Classical.axiomOfChoice h_all_core
        obtain ⟨M_star, hMs_all⟩ := Classical.axiomOfChoice (fun i => (hMT_all i).2)
        have hMT_sub_B : ∀ i : Fin ℓ, M_T i ⊆ B i := fun i => (hMT_all i).1
        have hMs_sub_MT : ∀ i : Fin ℓ, M_star i ⊆ M_T i := fun i => (hMs_all i).1
        have hMs_sub_B : ∀ i : Fin ℓ, M_star i ⊆ B i := fun i => (hMs_sub_MT i).trans (hMT_sub_B i)
        have hMs_gt_w : ∀ i : Fin ℓ, (15 / 64 : ℝ) * (w / (ℓ : ℝ) ^ 8) < ((M_star i).card : ℝ) :=
          fun i => (hMs_all i).2.1
        have hMs_prop : ∀ (i : Fin ℓ) (X : Finset V),
            IsProperModuleIn F (M_T i) X → (X ∩ M_star i).Nonempty →
            X ⊆ M_star i ∧ (X.card : ℝ) < 5 * θ₁ * ((M_star i).card : ℝ) :=
          fun i => (hMs_all i).2.2
        have hMs_ne : ∀ i : Fin ℓ, (M_star i).Nonempty := by
          intro i
          rw [← Finset.card_pos, ← @Nat.cast_pos ℝ]
          have hw_pos : 0 < w := lt_of_lt_of_le (by dsimp [w_min]; positivity) hw_min
          have : 0 < (15 / 64 : ℝ) * (w / (ℓ : ℝ) ^ 8) := by positivity
          linarith [hMs_gt_w i]
        by_cases h_dense_nonadj : ∃ (i j : Fin ℓ), j ≠ i ∧ ∃ u ∈ M_star j,
            (∃ w₀ ∈ M_T i, F.Adj u w₀) ∧
            (x / (4 * (ℓ : ℝ))) * ((M_star i).card : ℝ) ≤
              (((M_star i) \ neighborFinsetIn F u (M_star i)).card : ℝ)
        · obtain ⟨i, j, hji, u, hu_Mj, hu_notanti, hu_deg⟩ := h_dense_nonadj
          let τ_i := 5 * θ₁ * ((M_star i).card : ℝ)
          have hτ_pos : 0 < τ_i := by
            dsimp [τ_i]
            have : 0 < ((M_star i).card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr (hMs_ne i))
            positivity
          have h_2p_le : 2 * (p_cap : ℝ) * τ_i ≤
              (((M_star i) \ neighborFinsetIn F u (M_star i)).card : ℝ) := by
            have h_coef : 2 * (p_cap : ℝ) * τ_i ≤ (x / (4 * (ℓ : ℝ))) * ((M_star i).card : ℝ) := by
              dsimp [τ_i, θ₁]
              have h_eq : 2 * (p_cap : ℝ) * (5 * (x / (128 * (ℓ : ℝ) * (p_cap : ℝ))) * ((M_star i).card : ℝ)) =
                  (10 / 128 : ℝ) * (x / (ℓ : ℝ)) * ((M_star i).card : ℝ) := by
                field_simp; ring
              rw [h_eq]
              have h_10_128 : (10 / 128 : ℝ) ≤ 1 / 4 := by norm_num
              calc (10 / 128 : ℝ) * (x / (ℓ : ℝ)) * ((M_star i).card : ℝ)
                _ ≤ (1 / 4 : ℝ) * (x / (ℓ : ℝ)) * ((M_star i).card : ℝ) :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right h_10_128 (by positivity)) (Nat.cast_nonneg _)
                _ = (x / (4 * (ℓ : ℝ))) * ((M_star i).card : ℝ) := by ring
            exact le_trans h_coef hu_deg
          have h_mod_i : ∀ C : Finset V,
              IsAnticonnectedComponentOf F (M_T i \ neighborFinsetIn F u (M_T i)) C →
              IsProperModuleIn F (M_T i) C :=
            fun C hC => bird_comb_nonneighbor_anticonnectedComponent_isProperModuleIn
              hfree hcomb hapex hji (hMT_sub_B i) (hMs_sub_B j hu_Mj) hu_notanti hC
          have h_small_i : ∀ X : Finset V,
              IsProperModuleIn F (M_T i) X → (X ∩ M_star i).Nonempty →
              ((X ∩ M_star i).card : ℝ) ≤ τ_i := by
            intro X hX hX_ne
            have h1 : ((X ∩ M_star i).card : ℝ) ≤ (X.card : ℝ) :=
              Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_left)
            exact le_trans h1 (le_of_lt (hMs_prop i X hX hX_ne).2)
          obtain ⟨D, hD_comp⟩ := exists_complete_blockade_of_bird_nonneighbor
            (hMs_sub_MT i) hτ_pos h_mod_i h_small_i h_2p_le
          refine ⟨p_cap, hℓ_le_pcap, le_rfl, D, Or.inl ⟨(hD_comp.1.mono_ambient
            ((hMs_sub_B i).trans (hcomb.is_blockade.subset_ambient i))).mono_width ?_,
            fun a b hab => Or.inl (hD_comp.2 a b hab)⟩⟩
          have hMs_ge_p : (1 / 8 : ℝ) * ((S.card : ℝ) / (p_cap : ℝ) ^ 26) ≤ ((M_star i).card : ℝ) := by
            have h15 : (1 / 8 : ℝ) ≤ (15 / 64 : ℝ) := by norm_num
            have hw_p8 : (S.card : ℝ) / (p_cap : ℝ) ^ 26 ≤ w / (ℓ : ℝ) ^ 8 := by
              have h18 : (S.card : ℝ) / (p_cap : ℝ) ^ 18 ≤ w :=
                (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
                  (pow_le_pow_left₀ (by positivity) hℓ_p_r 18)).trans hw_ge_S
              calc (S.card : ℝ) / (p_cap : ℝ) ^ 26
                _ = ((S.card : ℝ) / (p_cap : ℝ) ^ 18) / (p_cap : ℝ) ^ 8 := by
                  rw [div_div, ← pow_add]
                _ ≤ w / (p_cap : ℝ) ^ 8 := div_le_div_of_nonneg_right h18 (by positivity)
                _ ≤ w / (ℓ : ℝ) ^ 8 :=
                  div_le_div_of_nonneg_left hw_nn (by positivity)
                    (pow_le_pow_left₀ (by positivity) hℓ_p_r 8)
            linarith [mul_le_mul h15 hw_p8 (by positivity) (by positivity), hMs_gt_w i]
          have h1024_p : (1024 : ℝ) * (p_cap : ℝ) ^ 29 ≤ (p_cap : ℝ) ^ 60 := by
            have h2_10 : (1024 : ℝ) ≤ (p_cap : ℝ) ^ 2 := by nlinarith
            calc (1024 : ℝ) * (p_cap : ℝ) ^ 29
              _ ≤ (p_cap : ℝ) ^ 2 * (p_cap : ℝ) ^ 29 :=
                mul_le_mul_of_nonneg_right h2_10 (by positivity)
              _ = (p_cap : ℝ) ^ 31 := by rw [← pow_add]
              _ ≤ (p_cap : ℝ) ^ 60 := pow_le_pow_right₀ hp_ge1 (by omega)
          calc (S.card : ℝ) / (p_cap : ℝ) ^ 60
            _ ≤ (S.card : ℝ) / (1024 * (p_cap : ℝ) ^ 29) :=
              div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) h1024_p
            _ ≤ (5 / 1024 : ℝ) * ((S.card : ℝ) / (p_cap : ℝ) ^ 29) := by
              have : (0 : ℝ) ≤ (S.card : ℝ) / (p_cap : ℝ) ^ 29 := by positivity
              linarith [show (S.card : ℝ) / (1024 * (p_cap : ℝ) ^ 29) =
                (1 / 1024 : ℝ) * ((S.card : ℝ) / (p_cap : ℝ) ^ 29) by ring]
            _ = 5 * (1 / (128 * (p_cap : ℝ) ^ 3)) * ((1 / 8 : ℝ) * ((S.card : ℝ) / (p_cap : ℝ) ^ 26)) := by
              rw [show (29 : ℕ) = 3 + 26 by rfl, pow_add]; ring
            _ ≤ 5 * θ₁ * ((M_star i).card : ℝ) := by
              refine mul_le_mul (mul_le_mul_of_nonneg_left hθ₁_lb (by norm_num)) hMs_ge_p
                (by positivity) (by positivity)
        · push_neg at h_dense_nonadj
          have hM_block : IsBlockadeIn F S ℓ ((S.card : ℝ) / (ℓ : ℝ) ^ 60) M_star := by
            refine ⟨fun i => (hMs_sub_B i).trans (hcomb.is_blockade.subset_ambient i),
              hMs_ne, fun i j hij => Finset.disjoint_of_subset_left (hMs_sub_B i)
                (Finset.disjoint_of_subset_right (hMs_sub_B j) (hcomb.is_blockade.pairwise_disjoint i j hij)),
              fun i => ?_⟩
            have h8 : (1 / 8 : ℝ) ≤ (15 / 64 : ℝ) := by norm_num
            have h64_inv : (ℓ : ℝ)⁻¹ ≤ (1 / 8 : ℝ) := by
              rw [inv_le_iff_one_le_mul₀' hℓ_pos]; linarith
            calc (S.card : ℝ) / (ℓ : ℝ) ^ 60
              _ ≤ (S.card : ℝ) / (ℓ : ℝ) ^ 27 :=
                div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
                  (pow_le_pow_right₀ (by linarith) (by omega))
              _ = (ℓ : ℝ)⁻¹ * ((S.card : ℝ) / (ℓ : ℝ) ^ 18 / (ℓ : ℝ) ^ 8) := by
                rw [show (27 : ℕ) = 1 + 18 + 8 by rfl, pow_add, pow_add, pow_one]; ring
              _ ≤ (15 / 64 : ℝ) * (w / (ℓ : ℝ) ^ 8) := by
                refine mul_le_mul (h64_inv.trans h8) ?_ (by positivity) (by positivity)
                exact div_le_div_of_nonneg_right hw_ge_S (by positivity)
              _ ≤ ((M_star i).card : ℝ) := le_of_lt (hMs_gt_w i)
          have h_part : ∀ (i j : Fin ℓ), i ≠ j → ∀ u ∈ M_star j,
              ((neighborFinsetIn F u (M_star i)).card : ℝ) ≤ (x / (4 * (ℓ : ℝ))) * ((M_star i).card : ℝ) ∨
              (((M_star i) \ neighborFinsetIn F u (M_star i)).card : ℝ) ≤
                (x / (4 * (ℓ : ℝ))) * ((M_star i).card : ℝ) := by
            intro i j hij u hu_Mj
            by_cases h_ex : ∃ w₀ ∈ M_T i, F.Adj u w₀
            · exact Or.inr (le_of_lt (h_dense_nonadj i j hij.symm u hu_Mj h_ex))
            · left
              push_neg at h_ex
              have hemp : neighborFinsetIn F u (M_star i) = ∅ := by
                rw [Finset.eq_empty_iff_forall_notMem]
                intro z hz
                rw [ErdosHajnalP6.mem_neighborFinsetIn_iff] at hz
                exact h_ex z (hMs_sub_MT i hz.1) hz.2
              rw [hemp, Finset.card_empty, Nat.cast_zero]
              positivity
          exact ⟨ℓ, le_rfl, hℓ_le_pcap, M_star, Or.inr
            (bipartite_double_counting_dichotomy (by omega) hx_pos hM_block h_part)⟩
  · push_neg at hw_min
    let k' := min S.card p_cap
    have hk'_le_S : k' ≤ S.card := Nat.min_le_left _ _
    have hk'_le_p : k' ≤ p_cap := Nat.min_le_right _ _
    have hℓ_le_k' : ℓ ≤ k' := le_min hℓ_le_S hℓ_le_pcap
    obtain ⟨U, hU_pure⟩ := singleton_pure_blockade_of_card_ge F S hk'_le_S
    refine ⟨k', hℓ_le_k', hk'_le_p, U, Or.inl ⟨hU_pure.1.mono_width ?_, hU_pure.2⟩⟩
    have hk'_pos : (0 : ℝ) < (k' : ℝ) := Nat.cast_pos.mpr (by omega)
    have hk'_ge1 : (1 : ℝ) ≤ (k' : ℝ) := Nat.one_le_cast.mpr (by omega)
    by_cases hS_le_p : S.card ≤ p_cap
    · have hk'_eq : k' = S.card := Nat.min_eq_left hS_le_p
      rw [← hk'_eq, div_le_one (by positivity)]
      simpa using pow_le_pow_right₀ hk'_ge1 (by omega : 1 ≤ 60)
    · push_neg at hS_le_p
      have hk'_eq : k' = p_cap := Nat.min_eq_right (le_of_lt hS_le_p)
      rw [hk'_eq, div_le_one (by positivity)]
      have hθ₁_inv_le : θ₁⁻¹ ≤ 128 * (p_cap : ℝ) ^ 3 := by
        dsimp [θ₁]
        have hℓp : (ℓ : ℝ) * (p_cap : ℝ) ≤ (p_cap : ℝ) ^ 2 := by nlinarith
        calc (x / (128 * (ℓ : ℝ) * (p_cap : ℝ)))⁻¹
          _ = 128 * ((ℓ : ℝ) * (p_cap : ℝ)) * x⁻¹ := by rw [inv_div]; ring
          _ ≤ 128 * (p_cap : ℝ) ^ 2 * (p_cap : ℝ) :=
            mul_le_mul (by linarith) hx_inv_le_pcap (by positivity) (by positivity)
          _ = 128 * (p_cap : ℝ) ^ 3 := by ring
      have h4ℓ_16 : (4 * (ℓ : ℝ)) ^ 16 ≤ (p_cap : ℝ) ^ 22 := by
        have h4 : (4 : ℝ) ^ 16 ≤ (p_cap : ℝ) ^ 6 := by
          have : (64 : ℝ) ≤ (p_cap : ℝ) := hp_r
          calc (4 : ℝ) ^ 16 ≤ (64 : ℝ) ^ 6 := by norm_num
            _ ≤ (p_cap : ℝ) ^ 6 := pow_le_pow_left₀ (by norm_num) this 6
        have hℓ16 : (ℓ : ℝ) ^ 16 ≤ (p_cap : ℝ) ^ 16 :=
          pow_le_pow_left₀ (by positivity) hℓ_p_r 16
        calc (4 * (ℓ : ℝ)) ^ 16 = (4 : ℝ) ^ 16 * (ℓ : ℝ) ^ 16 := mul_pow _ _ _
          _ ≤ (p_cap : ℝ) ^ 6 * (p_cap : ℝ) ^ 16 :=
            mul_le_mul h4 hℓ16 (by positivity) (by positivity)
          _ = (p_cap : ℝ) ^ 22 := by rw [← pow_add]
      have hw_le_p : w ≤ (p_cap : ℝ) ^ 30 := by
        have h64_128 : (64 : ℝ) * 128 ≤ (p_cap : ℝ) ^ 3 := by
          calc (64 : ℝ) * 128 ≤ (64 : ℝ) ^ 3 := by norm_num
            _ ≤ (p_cap : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hp_r 3
        calc w ≤ w_min := le_of_lt hw_min
          _ = 64 * (p_cap : ℝ) ^ 2 * θ₁⁻¹ * (4 * (ℓ : ℝ)) ^ 16 := rfl
          _ ≤ 64 * (p_cap : ℝ) ^ 2 * (128 * (p_cap : ℝ) ^ 3) * (p_cap : ℝ) ^ 22 := by
            refine mul_le_mul ?_ h4ℓ_16 (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_left hθ₁_inv_le (by positivity)
          _ = ((64 : ℝ) * 128) * (p_cap : ℝ) ^ 27 := by ring
          _ ≤ (p_cap : ℝ) ^ 3 * (p_cap : ℝ) ^ 27 :=
            mul_le_mul_of_nonneg_right h64_128 (by positivity)
          _ = (p_cap : ℝ) ^ 30 := by rw [← pow_add]
      have hS_le_p48 : (S.card : ℝ) ≤ (p_cap : ℝ) ^ 48 := by
        have h1 : (S.card : ℝ) ≤ (ℓ : ℝ) ^ 18 * w := by
          have hℓ18_pos : (0 : ℝ) < (ℓ : ℝ) ^ 18 := by positivity
          linarith [(div_le_iff₀ hℓ18_pos).mp hw_ge_S]
        have h2 : (ℓ : ℝ) ^ 18 ≤ (p_cap : ℝ) ^ 18 :=
          pow_le_pow_left₀ (by positivity) hℓ_p_r 18
        calc (S.card : ℝ) ≤ (ℓ : ℝ) ^ 18 * w := h1
          _ ≤ (p_cap : ℝ) ^ 18 * (p_cap : ℝ) ^ 30 :=
            mul_le_mul h2 hw_le_p hw_nn (by positivity)
          _ = (p_cap : ℝ) ^ 48 := by rw [← pow_add]
      exact hS_le_p48.trans (pow_le_pow_right₀ hp_ge1 (by omega))

/-- Unconditional Erdős–Hajnal property for both $\overline{\mathrm{Bird}}$ (`BirdGraphᶜ`) and
$\mathrm{Bird}$ (`BirdGraph`) via Lemma 7(1)–(2) (Proposition 5.1(1a) of
`ErdosHajnalGeneralization_readable.tex`; Proposition 6(1a) of `main.tex`). -/
private theorem hasErdosHajnalProp_birdGraph_both :
    HasErdosHajnalProp BirdGraphᶜ ∧ HasErdosHajnalProp BirdGraph := by
  let v₀ : Fin 6 := 5
  let u₀ : Fin 6 := 1
  have hu₀_ne : u₀ ≠ v₀ := by decide
  have hleaf : ∀ w : Fin 6, BirdGraph.Adj v₀ w ↔ w = u₀ := by
    intro w; fin_cases w <;> decide
  have hh : 3 ≤ Fintype.card (Fin 6) := by decide
  have hviral := isViral_birdMinus5Compl
  have hwond := bird_isThresholdedWonderful hasErdosHajnalProp_witnessHBird
  obtain ⟨d', hd', hviral_prop⟩ := isViral_birdMinus5Compl
  have hpair_viral :
      ∀ (U_type : Type) [Fintype U_type] [DecidableEq U_type]
        (F_G : SimpleGraph U_type) (ε : ℝ),
        0 < ε → ε < 1 / 2 →
        (indCopyCount (BirdGraph.comap (Subtype.val : {w : Fin 6 // w ≠ v₀} → Fin 6))ᶜ F_G : ℝ) ≤
          (ε ^ d' * (Fintype.card U_type : ℝ)) ^ (Fintype.card {w : Fin 6 // w ≠ v₀}) →
        (indCopyCount BirdGraphᶜ F_G : ℝ) ≤
          (ε ^ d' * (Fintype.card U_type : ℝ)) ^ (Fintype.card (Fin 6)) →
        ∃ S : Finset U_type, IsEpsRestrictedOn F_G S ε ∧
          ε ^ d' * (Fintype.card U_type : ℝ) ≤ (S.card : ℝ) :=
    fun U_type _ _ F_G ε hε0 hε_half hc1 _ => hviral_prop U_type F_G ε hε0 hε_half hc1
  let a_leaf : ℝ := 24 * d' + 6
  let b_leaf : ℝ := 12
  have ha_leaf : 6 ≤ a_leaf := by dsimp [a_leaf]; linarith
  have hb_leaf : 6 ≤ b_leaf := by dsimp [b_leaf]; norm_num
  have h_cosparse_peel : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      (F' : Finset V) (y : ℝ),
      IsInducedSubgraphFree G BirdGraphᶜ → IsInducedSubgraphFree G BirdGraphᶜ →
      0 < y → y ≤ (2 : ℝ) ^ (-4 * b_leaf) →
      1 ≤ y ^ (a_leaf + 2) * (F'.card : ℝ) →
      IsEpsSparseOn Gᶜ F' (y ^ 3) →
        (∃ U ⊆ F', IsEpsRestrictedOn G U (y ^ 4) ∧
          y ^ a_leaf * (F'.card : ℝ) ≤ (U.card : ℝ)) ∨
        (∃ X ⊆ F', ∃ Y ⊆ F', Disjoint X Y ∧
          y ^ a_leaf * (F'.card : ℝ) ≤ (X.card : ℝ) ∧
          (1 - b_leaf * y) * (F'.card : ℝ) ≤ (Y.card : ℝ) ∧
          IsCompletePair G X Y) := by
    intro V _ _ G F' y hG₁ hG₂ hy0 hy_le hy_F' h_cosparse
    have hy_half : y < 1 / 2 := by
      have h1 : (2 : ℝ) ^ (-4 * b_leaf) ≤ (2 : ℝ) ^ (-24 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by dsimp [b_leaf]; norm_num)
      have h2 : (2 : ℝ) ^ (-24 : ℝ) < 1 / 2 := by norm_num
      exact hy_le.trans_lt (h1.trans_lt h2)
    have hy_le1 : y ≤ 1 := by linarith
    have hy1_F' : 1 ≤ y * (F'.card : ℝ) := by
      have h1 : y ^ (a_leaf + 2) ≤ y ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hy0 hy_le1 (by linarith)
      rw [Real.rpow_one] at h1
      exact hy_F'.trans (mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _))
    have hF'_ne : F'.Nonempty := by
      rw [← Finset.card_pos]
      have : (0 : ℝ) < (F'.card : ℝ) := by nlinarith
      exact_mod_cast this
    have hcosparse_y : IsEpsSparseOn Gᶜ F' y := by
      refine h_cosparse.mono ?_
      nlinarith [sq_nonneg y]
    rcases leaf_reducible_cosparse_trigger_or_restricted BirdGraph BirdGraph v₀ u₀ hu₀_ne hleaf hh
        hd' hpair_viral G hG₁ hG₂ F' hF'_ne y hy0 hy_half hy1_F' hcosparse_y with
      ⟨U, hUF', hU_rest, hU_card⟩ | ⟨X, hXF', Y, hYF', hdisj, hX_card, hY_card, hcomp⟩
    · left
      refine ⟨U, hUF', hU_rest, ?_⟩
      have hexp : 4 * d' + 1 ≤ a_leaf := by dsimp [a_leaf]; linarith
      have hrpow : y ^ a_leaf ≤ y ^ (4 * d' + 1) :=
        Real.rpow_le_rpow_of_exponent_ge hy0 hy_le1 hexp
      exact (mul_le_mul_of_nonneg_right hrpow (Nat.cast_nonneg _)).trans hU_card
    · right
      refine ⟨X, hXF', Y, hYF', hdisj, ?_, ?_, hcomp⟩
      · have hexp : 4 * d' * ((Fintype.card (Fin 6) - 1 : ℕ) : ℝ) + 1 ≤ a_leaf := by
          dsimp [a_leaf]; rw [Fintype.card_fin]; norm_num; linarith
        have hrpow : y ^ a_leaf ≤ y ^ (4 * d' * ((Fintype.card (Fin 6) - 1 : ℕ) : ℝ) + 1) :=
          Real.rpow_le_rpow_of_exponent_ge hy0 hy_le1 hexp
        exact (mul_le_mul_of_nonneg_right hrpow (Nat.cast_nonneg _)).trans hX_card.le
      · have h1 : (1 - b_leaf * y) * (F'.card : ℝ) ≤
            (1 - (Fintype.card (Fin 6) : ℝ) * y) * (F'.card : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
          dsimp [b_leaf]; rw [Fintype.card_fin]; norm_num; linarith
        exact h1.trans hY_card
  have hGN := pair_coupled_generalized_nice_of_comb_dichotomy_explicit
    BirdGraph BirdGraph (by decide)
    a_leaf b_leaf 60 2 1 1
    ha_leaf hb_leaf (by norm_num) le_rfl zero_lt_one zero_lt_one
    h_cosparse_peel
    (fun V _ _ G F' x y ℓ a B v hG₁ _ hx_pos hxy hy_ub hℓ_lo hℓ_hi hℓ_64 hcomb hapex => by
      right
      have hy0 : 0 < y := hx_pos.trans_le hxy
      have hw_ge_S := comb_width_ge_card_div_pow_18 F' hy0 hℓ_lo
      obtain ⟨k', hℓ_k', hk'_p, U, hU⟩ :=
        bird_comb_dichotomy_for_stage1 hx_pos hxy hy_ub hℓ_64 hℓ_hi hG₁ hcomb hapex hw_ge_S
      have hk'2 : 2 ≤ k' := by omega
      have hk'_lo : (1 / 2 : ℝ) * (ℓ : ℝ) ^ (1 : ℝ) ≤ (k' : ℝ) := by
        rw [Real.rpow_one]
        have : (ℓ : ℝ) ≤ (k' : ℝ) := by exact_mod_cast hℓ_k'
        linarith
      refine ⟨k', hk'2, hk'_lo, hk'_p, U, ?_⟩
      rw [show (60 : ℝ) = ((60 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      exact hU)
  dsimp only at hGN
  set δ := symmRodlDeltaGen (Fintype.card (Fin 6)) (lambda0Param (2 * b_leaf))
  set d := symmGenNiceD a_leaf b_leaf 60 1 δ
  have hd120 : 120 ≤ d := one_hundred_twenty_le_symmGenNiceD a_leaf b_leaf 60 1 δ
  exact master_stage2_eh_of_coupled_gen_nice_and_wonderful
    BirdGraph v₀ u₀ hu₀_ne hleaf hh hviral hwond
    (by linarith) (by norm_num) (by norm_num) (by linarith) hGN

/-- The 1-vertex graph $K_1$ (`⊤ : SimpleGraph (Fin 1)`) satisfies `HasErdosHajnalProp`. -/
private theorem hasErdosHajnalProp_top_fin1 : HasErdosHajnalProp (⊤ : SimpleGraph (Fin 1)) := by
  have e : (⊤ : SimpleGraph (Fin 1)) ≃g pathGraph 1 :=
    { toEquiv := Equiv.refl (Fin 1)
      map_rel_iff' := by intro a b; fin_cases a; fin_cases b; decide }
  exact hasErdosHajnalProp_of_iso e.symm (hasErdosHajnalProp_pathGraph_le_9 1 (by decide))

/-- Every generator $B \in \mathcal{B}_k^*$ (`InBStar k B`) with $k \le 9$ unconditionally satisfies
`HasErdosHajnalProp` (combining $K_1, K_2, \overline{K_2}$, $\mathrm{Bird}, \overline{\mathrm{Bird}}$,
and $P_t, \overline{P_t}$ for $1 \le t \le 9$). -/
private theorem hasErdosHajnalProp_of_inBStar_le_9 {k : ℕ} (hk : k ≤ 9)
    {W : Type} [Fintype W] [DecidableEq W] (B : SimpleGraph W) (hB : InBStar k B) :
    HasErdosHajnalProp B := by
  unfold InBStar at hB
  rcases hB with h1 | h2 | h3 | h4 | h5 | ⟨t, ht1, htk, h6 | h7⟩
  · obtain ⟨e⟩ := h1
    exact hasErdosHajnalProp_of_iso e.symm hasErdosHajnalProp_top_fin1
  · obtain ⟨e⟩ := h2
    exact hasErdosHajnalProp_of_iso e.symm hasErdosHajnalProp_top_fin2
  · obtain ⟨e⟩ := h3
    exact hasErdosHajnalProp_of_iso e.symm hasErdosHajnalProp_bot_fin2
  · obtain ⟨e⟩ := h4
    exact hasErdosHajnalProp_of_iso e.symm hasErdosHajnalProp_birdGraph_both.2
  · obtain ⟨e⟩ := h5
    exact hasErdosHajnalProp_of_iso e.symm hasErdosHajnalProp_birdGraph_both.1
  · obtain ⟨e⟩ := h6
    exact hasErdosHajnalProp_of_iso e.symm (hasErdosHajnalProp_pathGraph_le_9 t (htk.trans hk))
  · obtain ⟨e⟩ := h7
    exact hasErdosHajnalProp_of_iso e.symm (hasErdosHajnalProp_pathGraph_le_9 t (htk.trans hk)).compl

/--
**Main Theorem (C)(1) (`main_theorem_C1_forest_pairs_and_closures`, Theorem 1.1(C)(1) & Proposition 5.1(1a)–(1b) of `ErdosHajnalGeneralization_readable.tex`; Proposition 6(1a)–(1b) of `main.tex`)**:
1. Both `BirdGraph` ($\mathrm{Bird}$) and `BirdGraphᶜ` ($\overline{\mathrm{Bird}}$) satisfy
   `HasErdosHajnalProp`, `HasPolyRodlProp`, and `IsViral`;
2. For every non-empty finite forest $F_1$ (`F₁.IsAcyclic`) and non-empty finite forest $F_2$
   (`F₂.IsAcyclic`), the opposite-chirality pair $\{F_1, \overline{F_2}\}$ satisfies
   `HasPairErdosHajnalProp`, `HasPairPolyRodlProp`, and `IsPairViral`;
3. For every $H_1, H_2 \in \mathcal{J}(\mathcal{B}_9^*)$ (`InJClosure 9`), the pair $\{H_1, \overline{H_2}\}$
   satisfies `HasPairErdosHajnalProp`, `HasPairPolyRodlProp`, and `IsPairViral`; and every single
   graph $H \in \mathcal{H}(\mathcal{B}_9^*)$ (`InHClosure 9`) satisfies `HasErdosHajnalProp`
   (together with its complement), `HasPolyRodlProp`, and `IsViral`.
-/
theorem main_theorem_C1_forest_pairs_and_closures :
    (HasErdosHajnalProp BirdGraph ∧ HasErdosHajnalProp BirdGraphᶜ ∧
     HasPolyRodlProp BirdGraph ∧ HasPolyRodlProp BirdGraphᶜ ∧
     IsViral BirdGraph ∧ IsViral BirdGraphᶜ) ∧
    (∀ (W₁ W₂ : Type) [Fintype W₁] [DecidableEq W₁] [Nonempty W₁]
      [Fintype W₂] [DecidableEq W₂] [Nonempty W₂]
      (F₁ : SimpleGraph W₁) (F₂ : SimpleGraph W₂),
      F₁.IsAcyclic → F₂.IsAcyclic →
        HasPairErdosHajnalProp F₁ F₂ᶜ ∧
        HasPairPolyRodlProp F₁ F₂ᶜ ∧
        IsPairViral F₁ F₂ᶜ) ∧
    (∀ (W₁ W₂ : Type) [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]
      (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂),
      InJClosure 9 H₁ → InJClosure 9 H₂ →
        HasPairErdosHajnalProp H₁ H₂ᶜ ∧
        HasPairPolyRodlProp H₁ H₂ᶜ ∧
        IsPairViral H₁ H₂ᶜ) ∧
    (∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W),
      InHClosure 9 H →
        HasErdosHajnalProp H ∧ HasErdosHajnalProp Hᶜ ∧
        HasPolyRodlProp H ∧ IsViral H) := by
  have hBird_c := hasErdosHajnalProp_birdGraph_both.1
  have hBird := hasErdosHajnalProp_birdGraph_both.2
  have h_equiv_b := eh_iff_polyRodl_iff_isViral BirdGraph
  have h_equiv_bc := eh_iff_polyRodl_iff_isViral BirdGraphᶜ
  have hBird_rodl := h_equiv_b.1.mp hBird
  have hBird_c_rodl := h_equiv_bc.1.mp hBird_c
  have hBird_viral := h_equiv_b.2.mp hBird_rodl
  have hBird_c_viral := h_equiv_bc.2.mp hBird_c_rodl
  have h_J9 : ∀ (W₁ W₂ : Type) [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]
      (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂),
      InJClosure 9 H₁ → InJClosure 9 H₂ →
        HasPairErdosHajnalProp H₁ H₂ᶜ ∧ HasPairPolyRodlProp H₁ H₂ᶜ ∧ IsPairViral H₁ H₂ᶜ := by
    intro W₁ W₂ _ _ _ _ H₁ H₂ hJ₁ hJ₂
    obtain ⟨hv, hr, heh⟩ :=
      inJClosure_pair_viral_of_base 9 (fun B hB => hasErdosHajnalProp_of_inBStar_le_9 le_rfl B hB)
        H₁ H₂ hJ₁ hJ₂
    exact ⟨heh, hr, hv⟩
  refine ⟨⟨hBird, hBird_c, hBird_rodl, hBird_c_rodl, hBird_viral, hBird_c_viral⟩,
    ?_, h_J9, ?_⟩
  · intro W₁ W₂ _ _ _ _ _ _ F₁ F₂ hF₁ hF₂
    exact h_J9 W₁ W₂ F₁ F₂ (forest_in_InJClosure 9 F₁ hF₁) (forest_in_InJClosure 9 F₂ hF₂)
  · intro W _ _ H hH
    exact inHClosure_eh_of_base 9 (fun B hB => hasErdosHajnalProp_of_inBStar_le_9 le_rfl B hB) H hH

/-! ### Section 6: Hooked-Claw Extensions and Brooms (`main_theorem_C2_hook4_and_brooms`) -/

/--
**Main Theorem (C)(2) (`main_theorem_C2_hook4_and_brooms`, Theorem 1.1(C)(2), Proposition 5.1(2a)–(2b), & Remark 5.2 of `ErdosHajnalGeneralization_readable.tex`; Proposition 6(2a)–(2b) of `main.tex`)**:
1. For every finite non-empty graph $Q \in \mathcal{EH}$ (`1 ≤ Fintype.card W`, `HasErdosHajnalProp Q`)
   and every subset $S \subseteq V(Q)$, when $S = V(Q)$ (`∀ x : W, x ∈ S`), the pair
   $\{P_t, \operatorname{Hook}_4(Q, S)\}$ satisfies `IsPairCoupledGeneralizedNice` for all $t \ge 6$;
   and for every arbitrary subset $S \subseteq V(Q)$ and all $1 \le t \le 9$, both
   $\{P_t, \operatorname{Hook}_4(Q, S)\}$ and $\{\overline{P_t}, \overline{\operatorname{Hook}_4(Q, S)}\}$
   satisfy `HasPairErdosHajnalProp` and `IsPairViral`;
2. For all integers $s \ge 1$ and $1 \le d \le 7$, the $(s, d)$-broom `BroomGraph s d`
   ($B(s, d) := P_{d+2}[v_1 \leftarrow \overline{K_s}]$) and its complement `(BroomGraph s d)ᶜ`
   satisfy `HasErdosHajnalProp`, `HasPolyRodlProp`, and `IsViral`.
-/
theorem main_theorem_C2_hook4_and_brooms :
    (∀ (W : Type) [Fintype W] [DecidableEq W] (Q : SimpleGraph W) (S : Set W),
      HasErdosHajnalProp Q → 1 ≤ Fintype.card W →
        ((∀ x : W, x ∈ S) →
          ∀ t : ℕ, 6 ≤ t → IsPairCoupledGeneralizedNice (pathGraph t) (Hook4Graph Q S)) ∧
        (∀ t : ℕ, 1 ≤ t → t ≤ 9 →
          HasPairErdosHajnalProp (pathGraph t) (Hook4Graph Q S) ∧
          HasPairErdosHajnalProp (pathGraph t)ᶜ (Hook4Graph Q S)ᶜ ∧
          IsPairViral (pathGraph t) (Hook4Graph Q S) ∧
          IsPairViral (pathGraph t)ᶜ (Hook4Graph Q S)ᶜ)) ∧
    (∀ (s d : ℕ), 1 ≤ s → 1 ≤ d → d ≤ 7 →
      HasErdosHajnalProp (BroomGraph s d) ∧
      HasErdosHajnalProp (BroomGraph s d)ᶜ ∧
      HasPolyRodlProp (BroomGraph s d) ∧
      IsViral (BroomGraph s d)) := by
  refine ⟨?_, ?_⟩
  · intro W _ _ Q S _hEH_Q _hW_pos
    refine ⟨?_, ?_⟩
    · intro _hS t ht
      have hGN := (main_theorem_B_stage1_generalized_nice_all_paths t ht).1
      exact isPairCoupledGeneralizedNice_of_left (Hook4Graph Q S) hGN
    · intro t ht1 ht9
      obtain ⟨h_eh, h_eh_c, _, _, h_viral, h_viral_c⟩ := main_theorem_A_paths_le_9 t ht1 ht9
      exact ⟨hasPairErdosHajnalProp_of_left (Hook4Graph Q S) h_eh,
        hasPairErdosHajnalProp_of_left (Hook4Graph Q S)ᶜ h_eh_c,
        isPairViral_of_isViral_left (Hook4Graph Q S) h_viral,
        isPairViral_of_isViral_left (Hook4Graph Q S)ᶜ h_viral_c⟩
  · intro s d hs hd1 hd7
    obtain ⟨_, _, h_broom⟩ := broom_in_subst_closure s d hs
    have h_pd2 : HasErdosHajnalProp (pathGraph (d + 2)) :=
      hasErdosHajnalProp_pathGraph_le_9 (d + 2) (by omega)
    obtain ⟨h_eh, h_eh_c⟩ := h_broom h_pd2
    haveI : Nonempty ({v : Fin (d + 2) // v ≠ 0} ⊕ Fin s) := ⟨Sum.inr ⟨0, hs⟩⟩
    have h_equiv := eh_iff_polyRodl_iff_isViral (BroomGraph s d)
    have h_rodl := h_equiv.1.mp h_eh
    have h_viral := h_equiv.2.mp h_rodl
    exact ⟨h_eh, h_eh_c, h_rodl, h_viral⟩

/-! ### Section 7: Infinite Prime Non-Split Towers (`main_theorem_C3_infinite_prime_towers`) -/

/--
**Main Theorem (C)(3) (`main_theorem_C3_infinite_prime_towers`, Theorem 1.1(C)(3), Proposition 5.1(3), & Remark 5.3 of `ErdosHajnalGeneralization_readable.tex`; Proposition 6(3) of `main.tex`)**:
For every $t \in \{6, 7, 8, 9\}$ and every $k \ge 0$, the $(t + k)$-vertex recursive alternating
leaf/co-leaf tower graph `PrimeTowerGraph t k` ($H_{t+k}^{(t)}$) belongs to $\mathcal{H}(\mathcal{B}_t^*)$
(`InHClosure t`), satisfies `HasErdosHajnalProp` (along with its complement) and `IsViral`, is prime
(`IsPrimeGraph`), is non-split (`¬IsSplitGraph`), has complement outside $\mathcal{J}(\{K_1, K_2, \overline{K_2}, C_5\})$
(`¬InJClosureC5 (PrimeTowerGraph t k)ᶜ`, and hence lies outside $\mathcal{H}(\{K_1, K_2, \overline{K_2}, C_5\})$),
and the family $\{H_{t+k}^{(t)}\}_{k \ge 0}$ is pairwise non-isomorphic.
-/
theorem main_theorem_C3_infinite_prime_towers :
    ∀ t : ℕ, 6 ≤ t → t ≤ 9 →
      (∀ k : ℕ,
        InHClosure t (PrimeTowerGraph t k) ∧
        HasErdosHajnalProp (PrimeTowerGraph t k) ∧
        HasErdosHajnalProp (PrimeTowerGraph t k)ᶜ ∧
        IsViral (PrimeTowerGraph t k) ∧
        IsPrimeGraph (PrimeTowerGraph t k) ∧
        ¬IsSplitGraph (PrimeTowerGraph t k) ∧
        ¬InJClosureC5 (PrimeTowerGraph t k)ᶜ ∧
        ¬(InJClosureC5 (PrimeTowerGraph t k) ∧ InJClosureC5 (PrimeTowerGraph t k)ᶜ)) ∧
      (∀ k₁ k₂ : ℕ,
        Nonempty (PrimeTowerGraph t k₁ ≃g PrimeTowerGraph t k₂) ↔ k₁ = k₂) := by
  intro t ht6 ht9
  refine ⟨?_, fun k₁ k₂ => primeTower_iso_iff_eq t k₁ k₂⟩
  intro k
  have hH : InHClosure t (PrimeTowerGraph t k) := primeTower_inHClosure t k ht6
  obtain ⟨h_eh, h_eh_c, _, h_viral⟩ :=
    inHClosure_eh_of_base t (fun B hB => hasErdosHajnalProp_of_inBStar_le_9 ht9 B hB)
      (PrimeTowerGraph t k) hH
  exact ⟨hH, h_eh, h_eh_c, h_viral,
    primeTower_isPrimeGraph t k ht6,
    primeTower_not_isSplitGraph t k ht6,
    primeTowerCompl_not_inJClosureC5 t k ht6,
    primeTower_not_inHClosureC5 t k ht6⟩

end P9Baseline
