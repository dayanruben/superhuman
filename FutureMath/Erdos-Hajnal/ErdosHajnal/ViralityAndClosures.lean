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
# Virality, Polynomial Rödl, and Substitution / Leaf-Attachment Closures
(Theorems 2, 3, and 4 of `main.tex`, Section 2, lines 135–186)

This module establishes the self-contained general closure machinery of Section 2 of `main.tex`,
proving Rödl's theorem for arbitrary finite graphs, the equivalence of the Erdős–Hajnal property,
the polynomial Rödl property, and Kleitman–Winston virality, and the substitution and simultaneous
degree-$\le 1$ leaf/co-leaf viral closure theorems that drive the master two-graph closure
$\mathcal{J}(\mathcal{B}_k^*) \times \overline{\mathcal{J}(\mathcal{B}_k^*)}$.

## Mathematical Overview and Proof Architecture

1. **Section 1 (`BasicHelpers`) — Induced Copy Counts, Duality, and Symmetry**:
   Establishes fundamental properties of $\operatorname{ind}_H(G)$ (`indCopyCount H G`), including
   characterization of induced-$H$-freeness (`indCopyCount_eq_zero_iff`), invariance under graph
   isomorphisms (`indCopyCount_congr_left`, `indCopyCount_congr_right`) and simultaneous
   complementation (`indCopyCount_compl`), monotonicity under induced subgraphs
   (`indCopyCount_comap_le`), and symmetry/duality of `IsPairViral`.

2. **Section 2 (`RodlTheorem`) — Theorem 2 (Rödl's Theorem via Iterative Sparse Bipartite Splitting)**:
   Proves `rodl_theorem_general_subset`, `rodl_theorem_general`, and `rodl_theorem_pair`
   (`main.tex`, lines 135–142) completely from first principles without regularity lemmas:
   - **Step 1 (`induced_fin_free_sparse_or_cosparse_pair`)**: Partitions $S$ into $h_0 = |W|$
     equal parts $T_1, \dots, T_{h_0}$ of size $m_0 = \lfloor |S|/h_0 \rfloor$ and attempts to
     greedily embed $H$ one vertex at a time; failure at step $t$ yields disjoint subsets
     $L, R \subseteq S$ of size $\ge (x_0/(2h_0))^{h_0}|S|$ such that $L$ is $x_0$-sparse to $R$
     in $G$ or $\overline{G}$.
   - **Step 2 (`rodl_ramsey_low_edge_subset_gen`)**: By strong induction on $p + q$ with
     $x_0 = \xi/8$ and $\ell = \lceil 8/\xi \rceil$, extracts $U \subseteq F$ of size $\ell m$
     with at most $(\ell + \ell^2 x_0) m^2 \le \frac{\xi}{4}|U|^2$ ordered edges in $G$ or $\overline{G}$.
   - **Step 3 (`sparse_subset_of_low_edge_subset_gen`)**: Deletes vertices in $U$ of internal
     degree $> \frac{\xi}{2}|U|$ to obtain a $\xi$-restricted subset $F_0 \subseteq F$ with
     $|F_0| \ge \delta(|W|, \xi)|F|$.

3. **Section 3 (`ViralityEquivalence`) — Theorem 3 (Erdős–Hajnal $\iff$ Polynomial Rödl $\iff$ Virality)**:
   Proves `pair_eh_iff_pairPolyRodl_iff_isPairViral` and `eh_iff_polyRodl_iff_isViral`
   (`main.tex`, lines 145–166):
   - **`(3) → (2)` (`hasPairPolyRodlProp_of_isPairViral`)**: Immediate since $\operatorname{ind}_{H_i}(G) = 0$.
   - **`(2) → (1)` (`hasPairErdosHajnalProp_of_hasPairPolyRodlProp`)**: Evaluates the polynomial
     Rödl property at $\varepsilon = \frac{1}{2}|G|^{-c}$ with $c = \frac{1}{2(d+1)}$ and applies
     Turán's theorem (`kappa_ge_inv_two_mul_of_isEpsRestrictedOn`).
   - **`(1) → (3)` (`isPairViral_of_hasPairErdosHajnalProp`)**: Combines the Kleitman–Winston
     container upper bound (`kleitman_winston_container_bound`) with random $2t$-subset sampling
     and greedy copy deletion (`random_sampling_homog_sets_lower_bound`) to force a contradiction
     (`kw_contradiction_of_dense_and_lb`) whenever no large $\varepsilon$-restricted subset exists.

4. **Section 4 (`SubstitutionClosure`) — Theorem 4(1) (Unordered Viral Substitution Closure)**:
   Proves `isPairViral_substGraph`, `isViral_substGraph`, and `hasErdosHajnalProp_substGraph`
   (`main.tex`, lines 171, 177) via the extension-fiber identity
   $\operatorname{ind}_{H_1}(G) = \sum_{\psi} |X_\psi|$ (`indCopyCount_eq_sum_substFiber`) and
   the induced-copy packing inequality
   $\sum_{\psi} \operatorname{ind}_{H_2}(G[X_\psi]) \le \operatorname{ind}_{H_1[v_0 \leftarrow H_2]}(G)$
   (`sum_indCopyCount_substFiber_le`).

5. **Section 5 (`SimultaneousLeafColeaf`) — Theorem 4(2) (Simultaneous Leaf and Co-Leaf Viral Closure)**:
   Proves `isPairViral_simultaneous_leaf_coleaf` (`main.tex`, lines 172, 179–184) by combining
   degree-$0$ substitution reductions (`isPairViral_of_deg_zero_left`), the degree-$1$ leaf
   extension pigeonhole lemma (`leaf_extension_anticomplete_or_viral`), multi-scale geometric
   descent (`leaf_coleaf_multiscale_dichotomy`), and the Stage 2 quantitative reduction engine
   (`stage2_reduction`).

6. **Section 6 (`MasterClosure`) — Theorem 4(3) (Master Two-Graph Closure Theorem)**:
   Proves `inJClosure_pair_viral_of_base` and `inHClosure_eh_of_base` (`main.tex`, lines 173, 185)
   by structural classification (`inJClosure_decomp`) and strong induction on $|V(H_1)| + |V(H_2)|$
   (`inJClosure_isPairViral_aux`).
-/

set_option linter.unusedSectionVars false

open Finset SimpleGraph Real ErdosHajnalP6

namespace ErdosHajnalGen

/-!
### Section 1: Basic Helper Lemmas on `indCopyCount`, Isomorphisms, and Complements
-/

section BasicHelpers

/-- Membership characterization for `neighborFinsetIn G v S`: $u \in N_G(v) \cap S \iff u \in S \land v \sim_G u$. -/
@[simp]
lemma mem_neighborFinsetIn_iff {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v u : V) (S : Finset V) :
    u ∈ neighborFinsetIn G v S ↔ u ∈ S ∧ G.Adj v u := by
  classical
  simp [neighborFinsetIn]

/-- The restricted neighborhood $N_G(v) \cap S$ is always a subset of the ambient vertex set $S$. -/
lemma neighborFinsetIn_subset_ambient {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) (S : Finset V) :
    neighborFinsetIn G v S ⊆ S := by
  intro u hu
  exact ((mem_neighborFinsetIn_iff G v u S).mp hu).1

/-- Monotonicity of `neighborFinsetIn G v` with respect to the ambient vertex set $S \subseteq T$. -/
lemma neighborFinsetIn_mono_ambient {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) {S T : Finset V} (h : S ⊆ T) :
    neighborFinsetIn G v S ⊆ neighborFinsetIn G v T := by
  intro u hu
  rw [mem_neighborFinsetIn_iff] at hu ⊢
  exact ⟨h hu.1, hu.2⟩

/-- `indCopyCount H G = 0` if and only if $G$ is induced-$H$-free. -/
theorem indCopyCount_eq_zero_iff {W V : Type*} [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V] (H : SimpleGraph W) (G : SimpleGraph V) :
    indCopyCount H G = 0 ↔ IsInducedSubgraphFree G H := by
  classical
  unfold indCopyCount IsInducedSubgraphFree
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h ⟨g, hg⟩
    exact h (Finset.mem_univ g) hg.symm
  · intro h g _ hg
    exact h ⟨g, hg.symm⟩

/-- `indCopyCount` is invariant under graph isomorphism in the left argument. -/
theorem indCopyCount_congr_left {W₁ W₂ V : Type*} [Fintype W₁] [DecidableEq W₁]
    [Fintype W₂] [DecidableEq W₂] [Fintype V] [DecidableEq V]
    {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂} (e : H₁ ≃g H₂) (G : SimpleGraph V) :
    indCopyCount H₁ G = indCopyCount H₂ G := by
  classical
  unfold indCopyCount
  refine Finset.card_bij (fun (g : W₁ ↪ V) _ => e.symm.toEquiv.toEmbedding.trans g) ?_ ?_ ?_
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    ext u v
    have h1 := congr_arg (fun (J : SimpleGraph W₁) => J.Adj (e.symm u) (e.symm v)) hg
    simpa [comap_adj, e.symm.map_rel_iff] using h1
  · intro g₁ _ g₂ _ h_eq
    ext w
    have h1 := congr_arg (fun (f : W₂ ↪ V) => f (e w)) h_eq
    simpa using h1
  · intro g' hg'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg'
    refine ⟨e.toEquiv.toEmbedding.trans g', ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      ext u v
      have h1 := congr_arg (fun (J : SimpleGraph W₂) => J.Adj (e u) (e v)) hg'
      simpa [comap_adj, e.map_rel_iff] using h1
    · ext w
      simp

/-- `indCopyCount` is invariant under graph isomorphism in the right argument. -/
theorem indCopyCount_congr_right {W V₁ V₂ : Type*} [Fintype W] [DecidableEq W]
    [Fintype V₁] [DecidableEq V₁] [Fintype V₂] [DecidableEq V₂]
    (H : SimpleGraph W) {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂} (e : G₁ ≃g G₂) :
    indCopyCount H G₁ = indCopyCount H G₂ := by
  classical
  unfold indCopyCount
  refine Finset.card_bij (fun (g : W ↪ V₁) _ => g.trans e.toEquiv.toEmbedding) ?_ ?_ ?_
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    ext u v
    have h1 := congr_arg (fun (J : SimpleGraph W) => J.Adj u v) hg
    simpa [comap_adj, e.map_rel_iff] using h1
  · intro g₁ _ g₂ _ h_eq
    ext w
    have h1 := congr_arg (fun (f : W ↪ V₂) => e.symm (f w)) h_eq
    simpa using h1
  · intro g' hg'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg'
    refine ⟨g'.trans e.symm.toEquiv.toEmbedding, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      ext u v
      have h1 := congr_arg (fun (J : SimpleGraph W) => J.Adj u v) hg'
      simpa [comap_adj, e.symm.map_rel_iff] using h1
    · ext w
      simp

/-- `indCopyCount` is preserved under simultaneous complementation of $H$ and $G$. -/
@[simp]
theorem indCopyCount_compl {W V : Type*} [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V] (H : SimpleGraph W) (G : SimpleGraph V) :
    indCopyCount Hᶜ Gᶜ = indCopyCount H G := by
  classical
  unfold indCopyCount
  congr 1
  ext g
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← comap_compl]
  exact ⟨fun h => by rw [← compl_compl (G.comap g), h, compl_compl], fun h => by rw [h]⟩

/-- `indCopyCount` is monotonic with respect to induced subgraphs. -/
theorem indCopyCount_comap_le {W V₁ V₂ : Type*} [Fintype W] [DecidableEq W]
    [Fintype V₁] [DecidableEq V₁] [Fintype V₂] [DecidableEq V₂]
    (H : SimpleGraph W) (G : SimpleGraph V₂) (f : V₁ ↪ V₂) :
    indCopyCount H (G.comap f) ≤ indCopyCount H G := by
  classical
  unfold indCopyCount
  refine Finset.card_le_card_of_injOn (fun g => g.trans f) ?_ ?_
  · intro g hg
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    ext u v
    have h1 := congr_arg (fun (J : SimpleGraph W) => J.Adj u v) hg
    simpa [comap_adj] using h1
  · intro g₁ _ g₂ _ h_eq
    ext w
    exact f.injective (congr_arg (fun (h : W ↪ V₂) => h w) h_eq)

/-- If $G$ is induced-$H$-free for a graph $H$ on at most $1$ vertex, then $V$ is empty. -/
theorem isEmpty_of_isInducedSubgraphFree_card_le_one {W V : Type*} [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (hW : Fintype.card W ≤ 1)
    (hG : IsInducedSubgraphFree G H) : IsEmpty V := by
  by_contra h_not_empty
  rw [not_isEmpty_iff] at h_not_empty
  obtain ⟨v₀⟩ := h_not_empty
  haveI : Subsingleton W := Fintype.card_le_one_iff_subsingleton.mp hW
  let g : W ↪ V := ⟨fun _ => v₀, fun _ _ _ => Subsingleton.elim _ _⟩
  apply hG
  refine ⟨g, ?_⟩
  ext u w
  have huw : u = w := Subsingleton.elim u w
  subst huw
  simp [g]

/-- A diagonal pair $\{H, H\}$ has the pair Erdős–Hajnal property iff $H$ has the single-graph Erdős–Hajnal property. -/
theorem hasPairErdosHajnalProp_self_iff {W : Type*} (H : SimpleGraph W) :
    HasPairErdosHajnalProp H H ↔ HasErdosHajnalProp H := by
  unfold HasPairErdosHajnalProp HasErdosHajnalProp
  constructor
  · rintro ⟨c, hc, h⟩
    exact ⟨c, hc, fun V _ _ G hG => h V G hG hG⟩
  · rintro ⟨c, hc, h⟩
    exact ⟨c, hc, fun V _ _ G hG _ => h V G hG⟩

/-- A diagonal pair $\{H, H\}$ has the pair polynomial Rödl property iff $H$ has the single-graph polynomial Rödl property. -/
theorem hasPairPolyRodlProp_self_iff {W : Type*} (H : SimpleGraph W) :
    HasPairPolyRodlProp H H ↔ HasPolyRodlProp H := by
  unfold HasPairPolyRodlProp HasPolyRodlProp
  constructor
  · rintro ⟨d, hd, h⟩
    exact ⟨d, hd, fun V _ _ G ε hε0 hε1 hG => h V G ε hε0 hε1 hG hG⟩
  · rintro ⟨d, hd, h⟩
    exact ⟨d, hd, fun V _ _ G ε hε0 hε1 hG _ => h V G ε hε0 hε1 hG⟩

/-- A diagonal pair $\{H, H\}$ is pair-viral iff $H$ is viral. -/
theorem isPairViral_self_iff {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) :
    IsPairViral H H ↔ IsViral H := by
  unfold IsPairViral IsViral
  constructor
  · rintro ⟨d, hd, h⟩
    exact ⟨d, hd, fun V _ _ G ε hε0 hε1 hc => h V G ε hε0 hε1 hc hc⟩
  · rintro ⟨d, hd, h⟩
    exact ⟨d, hd, fun V _ _ G ε hε0 hε1 hc _ => h V G ε hε0 hε1 hc⟩

/-- Symmetry of `IsPairViral`: if $\{H_1, H_2\}$ is viral, then $\{H_2, H_1\}$ is viral. -/
theorem IsPairViral.symm {W₁ W₂ : Type*} [Fintype W₁] [DecidableEq W₁]
    [Fintype W₂] [DecidableEq W₂] {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂}
    (h : IsPairViral H₁ H₂) : IsPairViral H₂ H₁ := by
  obtain ⟨d, hd, h_viral⟩ := h
  exact ⟨d, hd, fun V _ _ G ε hε0 hε1 hc₂ hc₁ => h_viral V G ε hε0 hε1 hc₁ hc₂⟩

/-- Complement duality of `IsPairViral`: if $\{H_1, H_2\}$ is viral, then $\{\overline{H_1}, \overline{H_2}\}$ is viral. -/
theorem IsPairViral.compl {W₁ W₂ : Type*} [Fintype W₁] [DecidableEq W₁]
    [Fintype W₂] [DecidableEq W₂] {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂}
    (h : IsPairViral H₁ H₂) : IsPairViral H₁ᶜ H₂ᶜ := by
  obtain ⟨d, hd, h_viral⟩ := h
  refine ⟨d, hd, fun V _ _ G ε hε0 hε1 hc₁ hc₂ => ?_⟩
  have hc₁' : (indCopyCount H₁ Gᶜ : ℝ) ≤ (ε ^ d * (Fintype.card V : ℝ)) ^ (Fintype.card W₁) := by
    rw [← indCopyCount_compl H₁ Gᶜ, compl_compl]
    exact hc₁
  have hc₂' : (indCopyCount H₂ Gᶜ : ℝ) ≤ (ε ^ d * (Fintype.card V : ℝ)) ^ (Fintype.card W₂) := by
    rw [← indCopyCount_compl H₂ Gᶜ, compl_compl]
    exact hc₂
  obtain ⟨S, hS_rest, hS_card⟩ := h_viral V Gᶜ ε hε0 hε1 hc₁' hc₂'
  refine ⟨S, ?_, hS_card⟩
  rcases hS_rest with h1 | h2
  · exact Or.inr h1
  · rw [compl_compl] at h2
    exact Or.inl h2

/-- Isomorphism invariance of `IsPairViral` in both graph arguments. -/
theorem IsPairViral.congr {W₁ W₁' W₂ W₂' : Type*} [Fintype W₁] [DecidableEq W₁]
    [Fintype W₁'] [DecidableEq W₁'] [Fintype W₂] [DecidableEq W₂] [Fintype W₂'] [DecidableEq W₂']
    {H₁ : SimpleGraph W₁} {H₁' : SimpleGraph W₁'} {H₂ : SimpleGraph W₂} {H₂' : SimpleGraph W₂'}
    (e₁ : H₁ ≃g H₁') (e₂ : H₂ ≃g H₂') (h : IsPairViral H₁ H₂) :
    IsPairViral H₁' H₂' := by
  obtain ⟨d, hd, h_viral⟩ := h
  refine ⟨d, hd, fun V _ _ G ε hε0 hε1 hc₁ hc₂ => ?_⟩
  have hcard₁ : Fintype.card W₁ = Fintype.card W₁' := Fintype.card_congr e₁.toEquiv
  have hcard₂ : Fintype.card W₂ = Fintype.card W₂' := Fintype.card_congr e₂.toEquiv
  rw [← indCopyCount_congr_left e₁ G, ← hcard₁] at hc₁
  rw [← indCopyCount_congr_left e₂ G, ← hcard₂] at hc₂
  exact h_viral V G ε hε0 hε1 hc₁ hc₂

/-- Any single viral graph $H_1$ forms a viral pair $\{H_1, H_2\}$ with any finite graph $H_2$. -/
theorem isPairViral_of_isViral_left {W₁ W₂ : Type*} [Fintype W₁] [DecidableEq W₁]
    [Fintype W₂] [DecidableEq W₂] {H₁ : SimpleGraph W₁} (H₂ : SimpleGraph W₂)
    (h : IsViral H₁) : IsPairViral H₁ H₂ := by
  obtain ⟨d, hd, h_viral⟩ := h
  exact ⟨d, hd, fun V _ _ G ε hε0 hε1 hc₁ _ => h_viral V G ε hε0 hε1 hc₁⟩

/-- Any single viral graph $H_2$ forms a viral pair $\{H_1, H_2\}$ with any finite graph $H_1$. -/
theorem isPairViral_of_isViral_right {W₁ W₂ : Type*} [Fintype W₁] [DecidableEq W₁]
    [Fintype W₂] [DecidableEq W₂] (H₁ : SimpleGraph W₁) {H₂ : SimpleGraph W₂}
    (h : IsViral H₂) : IsPairViral H₁ H₂ :=
  (isPairViral_of_isViral_left H₁ h).symm

end BasicHelpers

/-!
### Section 2: Theorem 2 (Rödl's Theorem via Iterative Sparse Bipartite Splitting)
(Lines 135–142 of `main.tex`)
-/

section RodlTheorem

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- If $k m_0 \le |S|$, then $S$ contains $k$ pairwise disjoint subsets $T_0, \dots, T_{k-1}$ of cardinality $m_0$. -/
private theorem exists_disjoint_subsets_card_eq_gen (S : Finset V) (m₀ : ℕ) :
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

/--
**Step 1 of Rödl's Theorem (General $h_0$-Vertex Graph $H$)**:
If $G$ is induced-$H$-free for $H : \text{SimpleGraph } (\text{Fin } h_0)$ ($h_0 \ge 2$), then for
every $x_0 \in (0, 1]$ and every $S \subseteq V$ with $|S| \ge 2 h_0$, there exist disjoint subsets
$L, R \subseteq S$ with $|L|, |R| \ge (x_0 / (2 h_0))^{h_0} |S|$ such that $L$ is $x_0$-sparse to $R$
in either $G$ or $\overline{G}$.
-/
private theorem induced_fin_free_sparse_or_cosparse_pair (G : SimpleGraph V)
    {h₀ : ℕ} (hh₀ : 2 ≤ h₀) (H : SimpleGraph (Fin h₀)) (hG : IsInducedSubgraphFree G H)
    (S : Finset V) (x₀ : ℝ) (hx₀0 : 0 < x₀) (hx₀1 : x₀ ≤ 1) (hS_card : 2 * h₀ ≤ S.card) :
    ∃ L ⊆ S, ∃ R ⊆ S, Disjoint L R ∧
      (x₀ / (2 * (h₀ : ℝ))) ^ h₀ * (S.card : ℝ) ≤ (L.card : ℝ) ∧
      (x₀ / (2 * (h₀ : ℝ))) ^ h₀ * (S.card : ℝ) ≤ (R.card : ℝ) ∧
      (IsXSparseTo G L R x₀ ∨ IsXSparseTo Gᶜ L R x₀) := by
  classical
  by_contra hno_pair
  let m₀ : ℕ := S.card / h₀
  have hm₀_mul : h₀ * m₀ ≤ S.card := Nat.mul_div_le S.card h₀
  have hm₀_pos : 1 ≤ m₀ := by
    have : h₀ * 2 ≤ S.card := by omega
    exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hm₀_ge : (S.card : ℝ) / (2 * (h₀ : ℝ)) ≤ (m₀ : ℝ) := by
    have hmod : S.card % h₀ < h₀ := Nat.mod_lt S.card (by omega)
    have hdiv : h₀ * m₀ + S.card % h₀ = S.card := Nat.div_add_mod S.card h₀
    have hnat : S.card ≤ 2 * h₀ * m₀ := by nlinarith
    have hreal : (S.card : ℝ) ≤ 2 * (h₀ : ℝ) * (m₀ : ℝ) := by exact_mod_cast hnat
    have hh₀_pos : (0 : ℝ) < 2 * (h₀ : ℝ) := by positivity
    exact (div_le_iff₀ hh₀_pos).mpr (by linarith)
  obtain ⟨T, hTS, hT_disj, hT_card⟩ := exists_disjoint_subsets_card_eq_gen S m₀ h₀ hm₀_mul
  let w₁ : ℝ := (x₀ / (2 * (h₀ : ℝ))) ^ h₀ * (S.card : ℝ)
  have hS_pos : (0 : ℝ) < (S.card : ℝ) := by
    have : 0 < S.card := by omega
    exact_mod_cast this
  have hw₁_pos : 0 < w₁ := by
    dsimp [w₁]
    positivity
  have hh₀_w₁_le : (h₀ : ℝ) * w₁ ≤ x₀ ^ (h₀ - 1) * (m₀ : ℝ) := by
    let h' := h₀ - 1
    have hh₀_r : (2 : ℝ) ≤ (h₀ : ℝ) := by exact_mod_cast hh₀
    have hpow_ge : (h₀ : ℝ) ≤ (2 * (h₀ : ℝ)) ^ h' := by
      have h1 : 1 ≤ h' := by omega
      have h2 : (2 * (h₀ : ℝ)) ^ 1 ≤ (2 * (h₀ : ℝ)) ^ h' :=
        pow_le_pow_right₀ (by linarith) h1
      have h3 : (h₀ : ℝ) ≤ (2 * (h₀ : ℝ)) ^ 1 := by linarith [pow_one (2 * (h₀ : ℝ))]
      exact h3.trans h2
    have hdiv_le_one : (h₀ : ℝ) / (2 * (h₀ : ℝ)) ^ h' ≤ 1 :=
      (div_le_one (by positivity)).mpr hpow_ge
    have hx₀_pow_le : x₀ ^ h₀ ≤ x₀ ^ h' :=
      pow_le_pow_of_le_one hx₀0.le hx₀1 (by omega)
    have h_pow_2h : (2 * (h₀ : ℝ)) ^ h₀ = (2 * (h₀ : ℝ)) ^ h' * (2 * (h₀ : ℝ)) := by
      have hh₀_eq : h₀ = h' + 1 := (Nat.sub_add_cancel (by omega)).symm
      set b : ℝ := 2 * (h₀ : ℝ)
      rw [hh₀_eq, pow_succ]
    have h_step1 : (h₀ : ℝ) * w₁ =
        ((h₀ : ℝ) / (2 * (h₀ : ℝ)) ^ h') * (x₀ ^ h₀ * ((S.card : ℝ) / (2 * (h₀ : ℝ)))) := by
      dsimp [w₁]
      rw [div_pow, h_pow_2h]
      ring
    rw [h_step1]
    calc ((h₀ : ℝ) / (2 * (h₀ : ℝ)) ^ h') * (x₀ ^ h₀ * ((S.card : ℝ) / (2 * (h₀ : ℝ))))
      _ ≤ 1 * (x₀ ^ h₀ * ((S.card : ℝ) / (2 * (h₀ : ℝ)))) :=
        mul_le_mul_of_nonneg_right hdiv_le_one (by positivity)
      _ = x₀ ^ h₀ * ((S.card : ℝ) / (2 * (h₀ : ℝ))) := one_mul _
      _ ≤ x₀ ^ h' * (m₀ : ℝ) :=
        mul_le_mul hx₀_pow_le hm₀_ge (by positivity) (by positivity)
  have hS_nonempty : S.Nonempty := card_pos.mp (by omega)
  obtain ⟨v_dummy, _⟩ := hS_nonempty
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
      have hRt_ge : x₀ ^ (h₀ - 1) * (m₀ : ℝ) ≤ ((R t_fin).card : ℝ) := by
        have hxt : x₀ ^ (h₀ - 1) ≤ x₀ ^ t := pow_le_pow_of_le_one hx₀0.le hx₀1 (by omega)
        calc x₀ ^ (h₀ - 1) * (m₀ : ℝ)
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
            have hxt : x₀ ^ (h₀ - 1) ≤ x₀ ^ t := pow_le_pow_of_le_one hx₀0.le hx₀1 (by omega)
            have h1 : (1 : ℝ) ≤ (h₀ : ℝ) := by exact_mod_cast (by omega : 1 ≤ h₀)
            calc w₁
              _ = 1 * w₁ := (one_mul _).symm
              _ ≤ (h₀ : ℝ) * w₁ := mul_le_mul_of_nonneg_right h1 hw₁_pos.le
              _ ≤ x₀ ^ (h₀ - 1) * (m₀ : ℝ) := hh₀_w₁_le
              _ ≤ x₀ ^ t * (m₀ : ℝ) := mul_le_mul_of_nonneg_right hxt (Nat.cast_nonneg _)
              _ ≤ ((R k).card : ℝ) := hR_card k (by omega)
          let L_k := (R t_fin).filter (fun u =>
            ((neighborFinsetIn (if H.Adj t_fin k then G else Gᶜ) u (R k)).card : ℝ) ≤
              x₀ * ((R k).card : ℝ))
          have hLk_sub : L_k ⊆ S := Subset.trans (filter_subset _ _)
            (Subset.trans (hR_sub t_fin) (hTS t_fin))
          have hRk_sub : R k ⊆ S := Subset.trans (hR_sub k) (hTS k)
          have htk_ne : t_fin ≠ k := fun h => by
            have : t = k.val := congrArg Fin.val h
            omega
          have hdisj_LR : Disjoint L_k (R k) :=
            Disjoint.mono (Subset.trans (filter_subset _ _) (hR_sub t_fin)) (hR_sub k)
              (hT_disj t_fin k htk_ne)
          have hsparse_LR : IsXSparseTo G L_k (R k) x₀ ∨ IsXSparseTo Gᶜ L_k (R k) x₀ := by
            by_cases hadj : H.Adj t_fin k
            · left
              intro u hu
              simp only [L_k, if_pos hadj, mem_filter] at hu
              exact hu.2
            · right
              intro u hu
              simp only [L_k, if_neg hadj, mem_filter] at hu
              exact hu.2
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
        · subst hit
          exact hR_sub t_fin hv_t_R
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
          have h := hR_adj j t_fin hjt_val le_rfl v_t hv_t_R
          exact ⟨fun hadj => (h.mp hadj.symm).symm, fun hadj => (h.mpr hadj.symm).symm⟩
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
          exact Subset.trans (neighborFinsetIn_subset_ambient _ _ _) (hR_sub k)
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
        have hu_Rk : u ∈ R k := neighborFinsetIn_subset_ambient _ _ _ hu
        dsimp [v']
        split_ifs with hit
        · subst hit
          by_cases hadj : H.Adj t_fin k
          · rw [if_pos hadj, mem_neighborFinsetIn_iff] at hu
            exact iff_of_true hu.2 hadj
          · rw [if_neg hadj, mem_neighborFinsetIn_iff, compl_adj] at hu
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

/-- Symmetry of `crossEdgeCount`: $|E_H(A, B)| = |E_H(B, A)|$. -/
private theorem crossEdgeCount_comm_gen (H : SimpleGraph V) (A B : Finset V) :
    crossEdgeCount H A B = crossEdgeCount H B A := by
  classical
  unfold crossEdgeCount neighborFinsetIn
  simp only [card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  refine sum_congr rfl (fun v _ => sum_congr rfl (fun u _ => ?_))
  rw [adj_comm]

/-- Right additivity of `crossEdgeCount` over disjoint unions $B_1 \sqcup B_2$. -/
private theorem crossEdgeCount_union_right_gen (H : SimpleGraph V) (A B₁ B₂ : Finset V)
    (hdisj : Disjoint B₁ B₂) :
    crossEdgeCount H A (B₁ ∪ B₂) = crossEdgeCount H A B₁ + crossEdgeCount H A B₂ := by
  classical
  unfold crossEdgeCount
  rw [← sum_add_distrib]
  refine sum_congr rfl (fun u _ => ?_)
  have heq : neighborFinsetIn H u (B₁ ∪ B₂) =
      neighborFinsetIn H u B₁ ∪ neighborFinsetIn H u B₂ := by
    ext v
    simp only [mem_neighborFinsetIn_iff, mem_union, or_and_right]
  have hdisj' : Disjoint (neighborFinsetIn H u B₁) (neighborFinsetIn H u B₂) :=
    Disjoint.mono (neighborFinsetIn_subset_ambient _ _ _)
      (neighborFinsetIn_subset_ambient _ _ _) hdisj
  rw [heq, card_union_of_disjoint hdisj']

/-- Left additivity of `crossEdgeCount` over disjoint unions $A_1 \sqcup A_2$. -/
private theorem crossEdgeCount_union_left_gen (H : SimpleGraph V) (A₁ A₂ B : Finset V)
    (hdisj : Disjoint A₁ A₂) :
    crossEdgeCount H (A₁ ∪ A₂) B = crossEdgeCount H A₁ B + crossEdgeCount H A₂ B := by
  classical
  unfold crossEdgeCount
  exact sum_union hdisj

/-- Decomposition of internal ordered pairs `crossEdgeCount H (X ∪ U') (X ∪ U')` for disjoint $X, U'$. -/
private theorem crossEdgeCount_union_union_gen (H : SimpleGraph V) (X U' : Finset V)
    (hdisj : Disjoint X U') :
    crossEdgeCount H (X ∪ U') (X ∪ U') =
      crossEdgeCount H X X + 2 * crossEdgeCount H X U' + crossEdgeCount H U' U' := by
  rw [crossEdgeCount_union_left_gen H X U' (X ∪ U') hdisj,
    crossEdgeCount_union_right_gen H X X U' hdisj,
    crossEdgeCount_union_right_gen H U' X U' hdisj,
    crossEdgeCount_comm_gen H U' X]
  ring

/-- Trivial upper bound `crossEdgeCount H X X ≤ |X|^2`. -/
private theorem crossEdgeCount_self_le_gen (H : SimpleGraph V) (X : Finset V) :
    crossEdgeCount H X X ≤ X.card * X.card := by
  unfold crossEdgeCount
  calc ∑ u ∈ X, (neighborFinsetIn H u X).card
    _ ≤ ∑ _u ∈ X, X.card :=
      sum_le_sum (fun u _ => card_le_card (neighborFinsetIn_subset_ambient H u X))
    _ = X.card * X.card := by rw [sum_const, smul_eq_mul]

/--
Inductive extension step for `rodl_ramsey_low_edge_subset_gen`:
Given $U' \subseteq L$ of size $p' m$ with at most $(p' + (p')^2 x_0) m^2$ internal ordered edges in $H$,
and $L$ being $x_0$-sparse to $R$ ($|R| \ge m$), selects an $m$-subset $X \subseteq R$ minimizing
cross-edges to $U'$ to form $U = X \cup U'$ of size $(p'+1)m$ with at most
$((p'+1) + (p'+1)^2 x_0) m^2$ internal ordered edges.
-/
private theorem extend_low_edge_subset_gen (H : SimpleGraph V) (Y L R U' : Finset V)
    (p' m : ℕ) (x₀ : ℝ) (hx₀0 : 0 ≤ x₀) (hm : 1 ≤ m)
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
    rw [crossEdgeCount_comm_gen H R U', crossEdgeCount_eq_sum_left]
    push_cast
    calc ∑ u ∈ U', ((neighborFinsetIn H u R).card : ℝ)
      _ ≤ ∑ _u ∈ U', x₀ * (R.card : ℝ) :=
        sum_le_sum (fun u hu => hLR u (hU'L hu))
      _ = (U'.card : ℝ) * (x₀ * (R.card : ℝ)) := by rw [sum_const, nsmul_eq_mul]
  let w : V → ℝ := fun v => ((neighborFinsetIn H v U').card : ℝ)
  have hw_nonneg : ∀ v ∈ R, 0 ≤ w v := fun v _ => Nat.cast_nonneg _
  obtain ⟨X, hXR, hX_card, hX_sum⟩ := exists_subset_card_eq_sum_le R w hw_nonneg m hR_card
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
          rw [hU'_card]
          push_cast
          ring
    exact le_of_mul_le_mul_left hmul hR_pos
  have hdisj_XU' : Disjoint X U' := Disjoint.mono hXR hU'L hdisj.symm
  let U := X ∪ U'
  have hUY : U ⊆ Y := union_subset (Subset.trans hXR hRY) (Subset.trans hU'L hLY)
  have hU_card : U.card = (p' + 1) * m := by
    dsimp [U]
    rw [card_union_of_disjoint hdisj_XU', hX_card, hU'_card]
    ring
  have hXX : (crossEdgeCount H X X : ℝ) ≤ (m : ℝ) ^ 2 := by
    have hle := crossEdgeCount_self_le_gen H X
    rw [hX_card] at hle
    have hle' : (crossEdgeCount H X X : ℝ) ≤ (m : ℝ) * (m : ℝ) := by exact_mod_cast hle
    linarith [sq (m : ℝ)]
  refine ⟨U, hUY, hU_card, ?_⟩
  dsimp [U]
  have hunion := crossEdgeCount_union_union_gen H X U' hdisj_XU'
  have hunion_real : (crossEdgeCount H (X ∪ U') (X ∪ U') : ℝ) =
      (crossEdgeCount H X X : ℝ) + 2 * (crossEdgeCount H X U' : ℝ) +
        (crossEdgeCount H U' U' : ℝ) := by
    exact_mod_cast hunion
  rw [hunion_real]
  calc (crossEdgeCount H X X : ℝ) + 2 * (crossEdgeCount H X U' : ℝ) +
        (crossEdgeCount H U' U' : ℝ)
    _ ≤ (m : ℝ) ^ 2 + 2 * ((p' : ℝ) * x₀ * (m : ℝ) ^ 2) +
        ((p' : ℝ) + (p' : ℝ) ^ 2 * x₀) * (m : ℝ) ^ 2 := by linarith
    _ ≤ ((p' + 1 : ℕ) : ℝ) * (m : ℝ) ^ 2 +
        ((p' + 1 : ℕ) : ℝ) ^ 2 * x₀ * (m : ℝ) ^ 2 := by
      push_cast
      have : 0 ≤ x₀ * (m : ℝ) ^ 2 := by positivity
      nlinarith
    _ = (((p' + 1 : ℕ) : ℝ) + ((p' + 1 : ℕ) : ℝ) ^ 2 * x₀) * (m : ℝ) ^ 2 := by ring

/--
**Step 2 of Rödl's Theorem (`rodl_ramsey_low_edge_subset_gen`)**:
By strong induction on $N = p + q$, in any induced-$H$-free graph $G$ ($H$ on `Fin h₀`, $h_0 \ge 2$),
every subset $Y \subseteq V$ satisfying $c_1^{p + q - 2}|Y| \ge w_0 \ge 2h_0$ (where
$c_1 = (x_0/(2h_0))^{h_0}$ and $m = \lceil w_0 \rceil$) contains either a subset $U \subseteq Y$
of size $p m$ with at most $(p + p^2 x_0) m^2$ ordered edges in $G$, or a subset $U \subseteq Y$
of size $q m$ with at most $(q + q^2 x_0) m^2$ ordered edges in $\overline{G}$.
-/
private theorem rodl_ramsey_low_edge_subset_gen (G : SimpleGraph V)
    {h₀ : ℕ} (hh₀ : 2 ≤ h₀) (H : SimpleGraph (Fin h₀)) (hG : IsInducedSubgraphFree G H)
    (x₀ w₀ : ℝ) (hx₀0 : 0 < x₀) (hx₀1 : x₀ ≤ 1) (hw₀ : 2 * (h₀ : ℝ) ≤ w₀) :
    let m := Nat.ceil w₀
    let c₁ := (x₀ / (2 * (h₀ : ℝ))) ^ h₀
    ∀ (N : ℕ) (p q : ℕ), 1 ≤ p → 1 ≤ q → p + q = N →
      ∀ Y : Finset V, w₀ ≤ c₁ ^ (p + q - 2) * (Y.card : ℝ) →
        (∃ U ⊆ Y, U.card = p * m ∧
          (crossEdgeCount G U U : ℝ) ≤ ((p : ℝ) + (p : ℝ) ^ 2 * x₀) * (m : ℝ) ^ 2) ∨
        (∃ U ⊆ Y, U.card = q * m ∧
          (crossEdgeCount Gᶜ U U : ℝ) ≤ ((q : ℝ) + (q : ℝ) ^ 2 * x₀) * (m : ℝ) ^ 2) := by
  intro m c₁ N
  have hh₀_real : (2 : ℝ) ≤ (h₀ : ℝ) := by exact_mod_cast hh₀
  have hc₁_pos : 0 < c₁ := by dsimp [c₁]; positivity
  have hc₁_le_one : c₁ ≤ 1 := by
    dsimp [c₁]
    have : x₀ / (2 * (h₀ : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    exact pow_le_one₀ (by positivity) this
  have hm_ge : 1 ≤ m := Nat.ceil_pos.mpr (by linarith)
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro p q hp hq hN Y hY_card
    have hc₁_pow_le_one : c₁ ^ (p + q - 2) ≤ 1 := pow_le_one₀ hc₁_pos.le hc₁_le_one
    have hw₀_le_Y : w₀ ≤ (Y.card : ℝ) := by
      calc w₀
        _ ≤ c₁ ^ (p + q - 2) * (Y.card : ℝ) := hY_card
        _ ≤ 1 * (Y.card : ℝ) := mul_le_mul_of_nonneg_right hc₁_pow_le_one (Nat.cast_nonneg _)
        _ = (Y.card : ℝ) := one_mul _
    have hm_le_Y : m ≤ Y.card := Nat.ceil_le.mpr hw₀_le_Y
    have hY_2h₀ : 2 * h₀ ≤ Y.card := by
      have : ((2 * h₀ : ℕ) : ℝ) ≤ (Y.card : ℝ) := by
        push_cast
        exact le_trans hw₀ hw₀_le_Y
      exact_mod_cast this
    rcases p with _ | p'
    · omega
    · rcases Nat.eq_zero_or_pos p' with rfl | hp'
      · left
        obtain ⟨U, hUY, hU_card⟩ := exists_subset_card_eq hm_le_Y
        refine ⟨U, hUY, by simpa using hU_card, ?_⟩
        have hUU := crossEdgeCount_self_le_gen G U
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
            have hUU := crossEdgeCount_self_le_gen Gᶜ U
            rw [hU_card] at hUU
            have hUU' : (crossEdgeCount Gᶜ U U : ℝ) ≤ (m : ℝ) * (m : ℝ) := by exact_mod_cast hUU
            push_cast
            have : 0 ≤ x₀ * (m : ℝ) ^ 2 := by positivity
            nlinarith [sq (m : ℝ)]
          · obtain ⟨L, hLY, R, hRY, hdisj, hL_card, hR_card, hsparse⟩ :=
              induced_fin_free_sparse_or_cosparse_pair G hh₀ H hG Y x₀ hx₀0 hx₀1 hY_2h₀
            have hexp : p' + 1 + (q' + 1) - 2 = (p' + q' - 1) + 1 := by omega
            have hY_card' : w₀ ≤ c₁ ^ (p' + q' - 1) * (c₁ * (Y.card : ℝ)) := by
              rw [hexp, pow_succ] at hY_card
              linarith
            have hw₀_le_R : w₀ ≤ (R.card : ℝ) := by
              have hpow_le : c₁ ^ (p' + q' - 1) ≤ 1 := pow_le_one₀ hc₁_pos.le hc₁_le_one
              calc w₀
                _ ≤ c₁ ^ (p' + q' - 1) * (c₁ * (Y.card : ℝ)) := hY_card'
                _ ≤ 1 * (c₁ * (Y.card : ℝ)) :=
                  mul_le_mul_of_nonneg_right hpow_le (by positivity)
                _ = c₁ * (Y.card : ℝ) := one_mul _
                _ ≤ (R.card : ℝ) := hR_card
            have hm_le_R : m ≤ R.card := Nat.ceil_le.mpr hw₀_le_R
            have hL_ind : w₀ ≤ c₁ ^ (p' + q' - 1) * (L.card : ℝ) := by
              calc w₀
                _ ≤ c₁ ^ (p' + q' - 1) * (c₁ * (Y.card : ℝ)) := hY_card'
                _ ≤ c₁ ^ (p' + q' - 1) * (L.card : ℝ) :=
                  mul_le_mul_of_nonneg_left hL_card (by positivity)
            rcases hsparse with hLR_G | hLR_Gc
            · have hlt : p' + (q' + 1) < N := by omega
              have hexp_L : p' + (q' + 1) - 2 = p' + q' - 1 := by omega
              have hL_ind' : w₀ ≤ c₁ ^ (p' + (q' + 1) - 2) * (L.card : ℝ) := by rwa [hexp_L]
              rcases ih (p' + (q' + 1)) hlt p' (q' + 1) hp' (by omega) rfl L hL_ind' with
                ⟨U', hU'L, hU'_card, hU'_edges⟩ | ⟨U, hUL, hU_card, hU_edges⟩
              · left
                exact extend_low_edge_subset_gen G Y L R U' p' m x₀ hx₀0.le hm_ge
                  hLY hRY hdisj hm_le_R hLR_G hU'L hU'_card hU'_edges
              · right
                exact ⟨U, Subset.trans hUL hLY, hU_card, hU_edges⟩
            · have hlt : (p' + 1) + q' < N := by omega
              have hexp_L : (p' + 1) + q' - 2 = p' + q' - 1 := by omega
              have hL_ind' : w₀ ≤ c₁ ^ ((p' + 1) + q' - 2) * (L.card : ℝ) := by rwa [hexp_L]
              rcases ih ((p' + 1) + q') hlt (p' + 1) q' (by omega) hq' rfl L hL_ind' with
                ⟨U, hUL, hU_card, hU_edges⟩ | ⟨U', hU'L, hU'_card, hU'_edges⟩
              · left
                exact ⟨U, Subset.trans hUL hLY, hU_card, hU_edges⟩
              · right
                exact extend_low_edge_subset_gen Gᶜ Y L R U' q' m x₀ hx₀0.le hm_ge
                  hLY hRY hdisj hm_le_R hLR_Gc hU'L hU'_card hU'_edges

/--
**Step 3 of Rödl's Theorem (`sparse_subset_of_low_edge_subset_gen`)**:
If $U \subseteq F$ has cardinality $\ell m$ ($\ell \ge 8/\xi, x_0 \le \xi/8$) and at most
$(\ell + \ell^2 x_0) m^2 \le \frac{\xi}{4}|U|^2$ internal ordered edges in $H$, then keeping the
vertices of $U$ with internal degree $\le \frac{\xi}{2}|U|$ produces a $\xi$-sparse subset
$F_0 \subseteq F$ of size $|F_0| \ge |U|/2 \ge m/2$.
-/
private theorem sparse_subset_of_low_edge_subset_gen (H : SimpleGraph V) (F U : Finset V)
    (ℓ m : ℕ) (ξ x₀ : ℝ) (hξ0 : 0 < ξ) (hℓ_ge : 8 / ξ ≤ (ℓ : ℝ)) (hx₀_le : x₀ ≤ ξ / 8)
    (hℓ1 : 1 ≤ ℓ) (hm1 : 1 ≤ m) (hUF : U ⊆ F) (hU_card : U.card = ℓ * m)
    (hU_edges : (crossEdgeCount H U U : ℝ) ≤ ((ℓ : ℝ) + (ℓ : ℝ) ^ 2 * x₀) * (m : ℝ) ^ 2) :
    ∃ F₀ ⊆ F, IsEpsSparseOn H F₀ ξ ∧ (m : ℝ) / 2 ≤ (F₀.card : ℝ) := by
  classical
  have hU_card_real : (U.card : ℝ) = (ℓ : ℝ) * (m : ℝ) := by exact_mod_cast hU_card
  have hℓ_bound : (ℓ : ℝ) ≤ (ξ / 8) * (ℓ : ℝ) ^ 2 := by
    have h1 : 8 ≤ (ℓ : ℝ) * ξ := (div_le_iff₀ hξ0).mp hℓ_ge
    have h2 : 1 ≤ (ξ / 8) * (ℓ : ℝ) := by linarith
    calc (ℓ : ℝ)
      _ = 1 * (ℓ : ℝ) := (one_mul _).symm
      _ ≤ ((ξ / 8) * (ℓ : ℝ)) * (ℓ : ℝ) := mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg _)
      _ = (ξ / 8) * (ℓ : ℝ) ^ 2 := by ring
  have hedges_bound : (crossEdgeCount H U U : ℝ) ≤ (ξ / 4) * (U.card : ℝ) ^ 2 := by
    calc (crossEdgeCount H U U : ℝ)
      _ ≤ ((ℓ : ℝ) + (ℓ : ℝ) ^ 2 * x₀) * (m : ℝ) ^ 2 := hU_edges
      _ ≤ ((ξ / 8) * (ℓ : ℝ) ^ 2 + (ℓ : ℝ) ^ 2 * (ξ / 8)) * (m : ℝ) ^ 2 := by
        have : (ℓ : ℝ) + (ℓ : ℝ) ^ 2 * x₀ ≤ (ξ / 8) * (ℓ : ℝ) ^ 2 + (ℓ : ℝ) ^ 2 * (ξ / 8) := by
          have : (ℓ : ℝ) ^ 2 * x₀ ≤ (ℓ : ℝ) ^ 2 * (ξ / 8) :=
            mul_le_mul_of_nonneg_left hx₀_le (sq_nonneg _)
          linarith
        exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
      _ = (ξ / 4) * ((ℓ : ℝ) * (m : ℝ)) ^ 2 := by ring
      _ = (ξ / 4) * (U.card : ℝ) ^ 2 := by rw [hU_card_real]
  let P : V → Prop := fun v => ((neighborFinsetIn H v U).card : ℝ) ≤ (ξ / 2) * (U.card : ℝ)
  let F₀ := U.filter P
  let B := U.filter (fun v => ¬P v)
  have hsum_cards : (F₀.card : ℝ) + (B.card : ℝ) = (U.card : ℝ) := by
    exact_mod_cast card_filter_add_card_filter_not P
  have hB_edges : (B.card : ℝ) * ((ξ / 2) * (U.card : ℝ)) ≤ (crossEdgeCount H U U : ℝ) := by
    have h1 : (B.card : ℝ) * ((ξ / 2) * (U.card : ℝ)) = ∑ _v ∈ B, (ξ / 2) * (U.card : ℝ) := by
      rw [sum_const, nsmul_eq_mul]
    have h2 : ∑ _v ∈ B, (ξ / 2) * (U.card : ℝ) ≤ ∑ v ∈ B, ((neighborFinsetIn H v U).card : ℝ) := by
      refine sum_le_sum (fun v hv => ?_)
      simp only [B, P, mem_filter, not_le] at hv
      exact hv.2.le
    have h3 : ∑ v ∈ B, ((neighborFinsetIn H v U).card : ℝ) ≤
        ∑ v ∈ U, ((neighborFinsetIn H v U).card : ℝ) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.cast_nonneg _)
    have h4 : ∑ v ∈ U, ((neighborFinsetIn H v U).card : ℝ) = (crossEdgeCount H U U : ℝ) := by
      exact_mod_cast (crossEdgeCount_eq_sum_left H U U).symm
    linarith
  have hU_pos : (0 : ℝ) < (U.card : ℝ) := by
    rw [hU_card_real]
    have : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ1
    have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    positivity
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
  have hF₀_ge_U : (U.card : ℝ) / 2 ≤ (F₀.card : ℝ) := by linarith
  have hF₀_ge_m : (m : ℝ) / 2 ≤ (F₀.card : ℝ) := by
    have hm_le_U : (m : ℝ) ≤ (U.card : ℝ) := by
      rw [hU_card_real]
      have hℓ1' : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ1
      calc (m : ℝ)
        _ = 1 * (m : ℝ) := (one_mul _).symm
        _ ≤ (ℓ : ℝ) * (m : ℝ) := mul_le_mul_of_nonneg_right hℓ1' (Nat.cast_nonneg _)
    linarith
  refine ⟨F₀, Subset.trans (filter_subset _ _) hUF, ?_, hF₀_ge_m⟩
  intro v hv
  have hvU : v ∈ U ∧ ((neighborFinsetIn H v U).card : ℝ) ≤ (ξ / 2) * (U.card : ℝ) := by
    simpa [F₀, P] using hv
  have hsub : neighborFinsetIn H v F₀ ⊆ neighborFinsetIn H v U :=
    neighborFinsetIn_mono_ambient H v (filter_subset _ _)
  have hle_U : ((neighborFinsetIn H v F₀).card : ℝ) ≤ ((neighborFinsetIn H v U).card : ℝ) := by
    exact_mod_cast card_le_card hsub
  calc ((neighborFinsetIn H v F₀).card : ℝ)
    _ ≤ ((neighborFinsetIn H v U).card : ℝ) := hle_U
    _ ≤ (ξ / 2) * (U.card : ℝ) := hvU.2
    _ ≤ (ξ / 2) * (2 * (F₀.card : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = ξ * (F₀.card : ℝ) := by ring

/--
Explicit positive constant $\delta(h_0, \xi)$ for Rödl's theorem on $H$-free graphs ($h_0 = |H|$),
depending only on $h_0$ and $\xi$:
$$\delta(h_0, \xi) := \frac{1}{4 h}\left(\frac{\xi}{16 h}\right)^{2 h \lceil 8 / \xi \rceil}, \quad h := \max(h_0, 2).$$
-/
noncomputable def rodlDeltaGen (h₀ : ℕ) (ξ : ℝ) : ℝ :=
  let h := max h₀ 2
  (((ξ / 8) / (2 * (h : ℝ))) ^ h) ^ (2 * Nat.ceil (8 / ξ)) / (4 * (h : ℝ))

/-- Positivity of `rodlDeltaGen h₀ ξ` for all $h_0 \in \mathbb{N}$ and $\xi > 0$. -/
theorem rodlDeltaGen_pos (h₀ : ℕ) {ξ : ℝ} (hξ0 : 0 < ξ) : 0 < rodlDeltaGen h₀ ξ := by
  unfold rodlDeltaGen
  dsimp only
  have hh : (2 : ℝ) ≤ (max h₀ 2 : ℝ) := by exact_mod_cast le_max_right h₀ 2
  positivity

/--
**Theorem 2 (Subset Version, `rodl_theorem_general_subset`)**:
For every finite graph $H : \text{SimpleGraph } W$, every $\xi \in (0, 1/2)$, every induced-$H$-free
graph $G : \text{SimpleGraph } V$, and every subset $F \subseteq V$, there exists a $\xi$-restricted
subset $F_0 \subseteq F$ with $|F_0| \ge \delta(|W|, \xi) |F|$.
-/
theorem rodl_theorem_general_subset {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (G : SimpleGraph V) (hG : IsInducedSubgraphFree G H)
    (ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ < 1 / 2) (F : Finset V) :
    ∃ F₀ ⊆ F, IsEpsRestrictedOn G F₀ ξ ∧
      rodlDeltaGen (Fintype.card W) ξ * (F.card : ℝ) ≤ (F₀.card : ℝ) := by
  classical
  let h₀ := Fintype.card W
  have hδ_pos : 0 < rodlDeltaGen h₀ ξ := rodlDeltaGen_pos h₀ hξ0
  by_cases hh₀ : h₀ ≤ 1
  · haveI : IsEmpty V := isEmpty_of_isInducedSubgraphFree_card_le_one G H hh₀ hG
    have hF_empty : F = ∅ := Finset.eq_empty_of_isEmpty F
    subst hF_empty
    refine ⟨∅, Subset.rfl, Or.inl (fun u hu => (notMem_empty u hu).elim), ?_⟩
    simp
  · push_neg at hh₀
    have hh₀_2 : 2 ≤ h₀ := hh₀
    have hmax_eq : max h₀ 2 = h₀ := max_eq_left hh₀_2
    let e : Fin h₀ ≃ W := (Fintype.equivFin W).symm
    let H_fin : SimpleGraph (Fin h₀) := H.comap e.toEmbedding
    have hG_fin : IsInducedSubgraphFree G H_fin := by
      rintro ⟨g, hg⟩
      apply hG
      refine ⟨e.symm.toEmbedding.trans g, ?_⟩
      ext u v
      have h1 := congr_arg (fun (J : SimpleGraph (Fin h₀)) => J.Adj (e.symm u) (e.symm v)) hg
      simpa [H_fin, comap_adj] using h1
    let x₀ : ℝ := ξ / 8
    have hx₀0 : 0 < x₀ := by dsimp [x₀]; positivity
    have hx₀1 : x₀ ≤ 1 := by dsimp [x₀]; linarith
    let c₁ : ℝ := (x₀ / (2 * (h₀ : ℝ))) ^ h₀
    have hc₁_pos : 0 < c₁ := by
      dsimp [c₁]
      have : (2 : ℝ) ≤ (h₀ : ℝ) := by exact_mod_cast hh₀_2
      positivity
    have hc₁_le_one : c₁ ≤ 1 := by
      dsimp [c₁, x₀]
      have hh₀_r : (2 : ℝ) ≤ (h₀ : ℝ) := by exact_mod_cast hh₀_2
      have : ξ / 8 / (2 * (h₀ : ℝ)) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith
      exact pow_le_one₀ (by positivity) this
    let ℓ : ℕ := Nat.ceil (8 / ξ)
    have hℓ_ge : 8 / ξ ≤ (ℓ : ℝ) := Nat.le_ceil (8 / ξ)
    have hℓ1 : 1 ≤ ℓ := Nat.ceil_pos.mpr (by positivity)
    let w₀ : ℝ := c₁ ^ (2 * ℓ - 2) * (F.card : ℝ)
    have hdelta_le_w₀ : 4 * (h₀ : ℝ) * rodlDeltaGen h₀ ξ * (F.card : ℝ) ≤ w₀ := by
      have hpow : c₁ ^ (2 * ℓ) ≤ c₁ ^ (2 * ℓ - 2) :=
        pow_le_pow_of_le_one hc₁_pos.le hc₁_le_one (by omega)
      have hh₀_ne : (h₀ : ℝ) ≠ 0 := by
        have : (2 : ℝ) ≤ (h₀ : ℝ) := by exact_mod_cast hh₀_2
        linarith
      calc 4 * (h₀ : ℝ) * rodlDeltaGen h₀ ξ * (F.card : ℝ)
        _ = c₁ ^ (2 * ℓ) * (F.card : ℝ) := by
          unfold rodlDeltaGen
          dsimp only
          rw [hmax_eq]
          change 4 * (h₀ : ℝ) * (c₁ ^ (2 * ℓ) / (4 * (h₀ : ℝ))) * (F.card : ℝ) = _
          field_simp
        _ ≤ c₁ ^ (2 * ℓ - 2) * (F.card : ℝ) :=
          mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _)
        _ = w₀ := rfl
    by_cases hw₀ : 2 * (h₀ : ℝ) ≤ w₀
    · let m : ℕ := Nat.ceil w₀
      have hh₀_r : (2 : ℝ) ≤ (h₀ : ℝ) := by exact_mod_cast hh₀_2
      have hm1 : 1 ≤ m := Nat.ceil_pos.mpr (by linarith)
      have hw₀_le_m : w₀ ≤ (m : ℝ) := Nat.le_ceil w₀
      have hF_ind : w₀ ≤ c₁ ^ (ℓ + ℓ - 2) * (F.card : ℝ) := by
        have : ℓ + ℓ - 2 = 2 * ℓ - 2 := by omega
        rw [this]
      rcases rodl_ramsey_low_edge_subset_gen G hh₀_2 H_fin hG_fin x₀ w₀ hx₀0 hx₀1 hw₀
          (ℓ + ℓ) ℓ ℓ hℓ1 hℓ1 rfl F hF_ind
        with ⟨U, hUF, hU_card, hU_edges⟩ | ⟨U, hUF, hU_card, hU_edges⟩
      · obtain ⟨F₀, hF₀F, hF₀_sparse, hF₀_card⟩ :=
          sparse_subset_of_low_edge_subset_gen G F U ℓ m ξ x₀ hξ0 hℓ_ge le_rfl hℓ1 hm1
            hUF hU_card hU_edges
        refine ⟨F₀, hF₀F, Or.inl hF₀_sparse, ?_⟩
        have hdelta_nonneg : 0 ≤ rodlDeltaGen h₀ ξ * (F.card : ℝ) := by positivity
        nlinarith
      · obtain ⟨F₀, hF₀F, hF₀_sparse, hF₀_card⟩ :=
          sparse_subset_of_low_edge_subset_gen Gᶜ F U ℓ m ξ x₀ hξ0 hℓ_ge le_rfl hℓ1 hm1
            hUF hU_card hU_edges
        refine ⟨F₀, hF₀F, Or.inr hF₀_sparse, ?_⟩
        have hdelta_nonneg : 0 ≤ rodlDeltaGen h₀ ξ * (F.card : ℝ) := by positivity
        nlinarith
    · push_neg at hw₀
      rcases F.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
      · refine ⟨∅, Subset.rfl, Or.inl (fun u hu => (notMem_empty u hu).elim), ?_⟩
        simp
      · refine ⟨{v}, singleton_subset_iff.mpr hv, Or.inl ?_, ?_⟩
        · intro u hu
          rw [mem_singleton] at hu
          subst hu
          have hemp : neighborFinsetIn G u {u} = ∅ := by
            rw [eq_empty_iff_forall_notMem]
            intro w hw
            rw [mem_neighborFinsetIn_iff, mem_singleton] at hw
            exact G.loopless u (hw.1 ▸ hw.2)
          rw [hemp]
          simp [hξ0.le]
        · rw [card_singleton, Nat.cast_one]
          have hh₀_r : (2 : ℝ) ≤ (h₀ : ℝ) := by exact_mod_cast hh₀_2
          have hdelta_nonneg : 0 ≤ rodlDeltaGen h₀ ξ * (F.card : ℝ) := by positivity
          nlinarith

/--
**Theorem 2 (`rodl_theorem_general`, Rödl's Theorem — Single-Graph Version)**:
For every finite graph $H : \text{SimpleGraph } W$ and every $\xi \in (0, 1/2)$, there exists
$\delta = \text{rodlDeltaGen}(|W|, \xi) > 0$ depending only on $|W|$ and $\xi$ such that every
induced-$H$-free graph $G$ contains a $\xi$-restricted subset $S \subseteq V(G)$ with
$|S| \ge \delta |G|$.
-/
theorem rodl_theorem_general {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ < 1 / 2) :
    ∃ δ > (0 : ℝ), ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      IsInducedSubgraphFree G H →
        ∃ S : Finset V, IsEpsRestrictedOn G S ξ ∧ δ * (Fintype.card V : ℝ) ≤ (S.card : ℝ) := by
  refine ⟨rodlDeltaGen (Fintype.card W) ξ, rodlDeltaGen_pos (Fintype.card W) hξ0, ?_⟩
  intro V _ _ G hG
  obtain ⟨S, _, hS_rest, hS_card⟩ :=
    rodl_theorem_general_subset H G hG ξ hξ0 hξ1 Finset.univ
  rw [Finset.card_univ] at hS_card
  exact ⟨S, hS_rest, hS_card⟩

/--
**Theorem 2 (`rodl_theorem_pair`, Rödl's Theorem — Two-Graph Family Version)**:
For every pair of finite graphs $H_1, H_2$ and every $\xi \in (0, 1/2)$, there exists $\delta > 0$
such that every graph $G$ that is both induced-$H_1$-free and induced-$H_2$-free contains a
$\xi$-restricted subset $S \subseteq V(G)$ with $|S| \ge \delta |G|$.
-/
theorem rodl_theorem_pair {W₁ W₂ : Type*} [Fintype W₁] [DecidableEq W₁]
    [Fintype W₂] [DecidableEq W₂]
    (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂) (ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ < 1 / 2) :
    ∃ δ > (0 : ℝ), ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      IsInducedSubgraphFree G H₁ → IsInducedSubgraphFree G H₂ →
        ∃ S : Finset V, IsEpsRestrictedOn G S ξ ∧ δ * (Fintype.card V : ℝ) ≤ (S.card : ℝ) := by
  obtain ⟨δ, hδ, h_rodl⟩ := rodl_theorem_general H₁ ξ hξ0 hξ1
  exact ⟨δ, hδ, fun V _ _ G hG₁ _ => h_rodl V G hG₁⟩

end RodlTheorem

/-!
### Section 3: Theorem 3 (Equivalence of Erdős–Hajnal, Polynomial Rödl, and Virality)
(Lines 145–166 of `main.tex`)
-/

section ViralityEquivalence

/--
**Theorem 3 (`(3) → (2)` for Pairs)**:
Every viral two-graph family $\{H_1, H_2\}$ satisfies the polynomial Rödl property.
-/
theorem hasPairPolyRodlProp_of_isPairViral {W₁ W₂ : Type*} [Fintype W₁] [DecidableEq W₁]
    [Fintype W₂] [DecidableEq W₂] {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂}
    (h : IsPairViral H₁ H₂) : HasPairPolyRodlProp H₁ H₂ := by
  obtain ⟨d, hd, h_viral⟩ := h
  refine ⟨d, hd, fun V _ _ G ε hε0 hε1 hG₁ hG₂ => ?_⟩
  have hc₁ : (indCopyCount H₁ G : ℝ) ≤ (ε ^ d * (Fintype.card V : ℝ)) ^ (Fintype.card W₁) := by
    rw [(indCopyCount_eq_zero_iff H₁ G).mpr hG₁, Nat.cast_zero]
    positivity
  have hc₂ : (indCopyCount H₂ G : ℝ) ≤ (ε ^ d * (Fintype.card V : ℝ)) ^ (Fintype.card W₂) := by
    rw [(indCopyCount_eq_zero_iff H₂ G).mpr hG₂, Nat.cast_zero]
    positivity
  exact h_viral V G ε hε0 hε1 hc₁ hc₂

/--
**Theorem 3 (`(3) → (2)` for Single Graphs)**:
Every viral finite graph $H$ satisfies the polynomial Rödl property.
-/
theorem hasPolyRodlProp_of_isViral {W : Type*} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} (h : IsViral H) : HasPolyRodlProp H := by
  rw [← hasPairPolyRodlProp_self_iff]
  exact hasPairPolyRodlProp_of_isPairViral ((isPairViral_self_iff H).mpr h)

/--
**Theorem 3 (`(2) → (1)` for Pairs)**:
Every two-graph family $\{H_1, H_2\}$ satisfying the polynomial Rödl property satisfies the
Erdős–Hajnal property with $c = \frac{1}{2(d+1)}$.
-/
theorem hasPairErdosHajnalProp_of_hasPairPolyRodlProp {W₁ W₂ : Type*}
    {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂}
    (h : HasPairPolyRodlProp H₁ H₂) : HasPairErdosHajnalProp H₁ H₂ := by
  obtain ⟨d, hd, h_rodl⟩ := h
  let c : ℝ := 1 / (2 * (d + 1))
  have hc_pos : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc_pos, fun V _ _ G hG₁ hG₂ => ?_⟩
  let n := Fintype.card V
  rcases eq_or_ne n 0 with hn0 | hn0
  · change (n : ℝ) ^ c ≤ (kappa G : ℝ)
    rw [hn0, Nat.cast_zero, Real.zero_rpow hc_pos.ne']
    exact Nat.cast_nonneg _
  rcases eq_or_ne n 1 with hn1 | hn1
  · change (n : ℝ) ^ c ≤ (kappa G : ℝ)
    rw [hn1, Nat.cast_one, Real.one_rpow]
    haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    exact_mod_cast kappa_pos_of_nonempty G
  have hn2 : 2 ≤ n := by omega
  by_cases hn_small : (n : ℝ) ≤ (2 : ℝ) ^ (2 * (d + 1))
  · have h1 : (n : ℝ) ^ c ≤ ((2 : ℝ) ^ (2 * (d + 1))) ^ c :=
      Real.rpow_le_rpow (Nat.cast_nonneg n) hn_small hc_pos.le
    have h2 : ((2 : ℝ) ^ (2 * (d + 1))) ^ c = 2 := by
      dsimp [c]
      rw [← Real.rpow_mul two_pos.le, mul_one_div_cancel (by positivity), Real.rpow_one]
    have h3 : (2 : ℝ) ≤ (kappa G : ℝ) := by exact_mod_cast kappa_ge_two_of_two_le_card G hn2
    change (n : ℝ) ^ c ≤ (kappa G : ℝ)
    linarith
  · push_neg at hn_small
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    let ε : ℝ := (1 / 2 : ℝ) * (n : ℝ) ^ (-c)
    have hε0 : 0 < ε := by dsimp [ε]; positivity
    have hnc_gt_two : (2 : ℝ) < (n : ℝ) ^ c := by
      have h1 : ((2 : ℝ) ^ (2 * (d + 1))) ^ c < (n : ℝ) ^ c :=
        Real.rpow_lt_rpow (by positivity) hn_small hc_pos
      have h2 : ((2 : ℝ) ^ (2 * (d + 1))) ^ c = 2 := by
        dsimp [c]
        rw [← Real.rpow_mul two_pos.le, mul_one_div_cancel (by positivity), Real.rpow_one]
      linarith
    have hε_lt_half : ε < 1 / 2 := by
      have h1 : (n : ℝ) ^ (-c) < 1 / 2 := by
        rw [Real.rpow_neg hn_pos.le, inv_lt_comm₀ (by positivity) (by positivity)]
        simpa using hnc_gt_two
      dsimp [ε]
      linarith
    obtain ⟨S, hS_rest, hS_card⟩ := h_rodl V G ε hε0 hε_lt_half hG₁ hG₂
    have hε_inv_le : ε⁻¹ ≤ ε ^ d * (n : ℝ) := by
      rw [inv_le_iff_one_le_mul₀ hε0]
      have h_mul : ε ^ d * (n : ℝ) * ε = ε ^ (d + 1) * (n : ℝ) := by
        rw [Real.rpow_add_one hε0.ne']
        ring
      rw [h_mul]
      have h_ε_d1 : ε ^ (d + 1) * (n : ℝ) = (2 : ℝ) ^ (-(d + 1)) * (n : ℝ) ^ (1 / 2 : ℝ) := by
        dsimp [ε]
        rw [Real.mul_rpow (by positivity) (by positivity)]
        have h_half : (1 / 2 : ℝ) ^ (d + 1) = (2 : ℝ) ^ (-(d + 1)) := by
          rw [one_div, Real.inv_rpow two_pos.le, Real.rpow_neg two_pos.le]
        have h_n_pow : ((n : ℝ) ^ (-c)) ^ (d + 1) * (n : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_mul hn_pos.le, ← Real.rpow_add_one hn_pos.ne']
          congr 1
          dsimp [c]
          have : d + 1 ≠ 0 := by positivity
          field_simp
          ring
        rw [h_half, mul_assoc, h_n_pow]
      rw [h_ε_d1]
      have h_n_half : (2 : ℝ) ^ (d + 1) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
        have h1 : ((2 : ℝ) ^ (2 * (d + 1))) ^ (1 / 2 : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hn_small.le (by positivity)
        have h2 : ((2 : ℝ) ^ (2 * (d + 1))) ^ (1 / 2 : ℝ) = (2 : ℝ) ^ (d + 1) := by
          rw [← Real.rpow_mul two_pos.le]
          congr 1
          ring
        linarith
      calc (1 : ℝ)
        _ = (2 : ℝ) ^ (-(d + 1)) * (2 : ℝ) ^ (d + 1) := by
          rw [← Real.rpow_add two_pos, neg_add_cancel, Real.rpow_zero]
        _ ≤ (2 : ℝ) ^ (-(d + 1)) * (n : ℝ) ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left h_n_half (by positivity)
    have hS_ge_inv : ε⁻¹ ≤ (S.card : ℝ) := hε_inv_le.trans hS_card
    have hkappa_ge := kappa_ge_inv_two_mul_of_isEpsRestrictedOn G S ε hε0 hS_ge_inv hS_rest
    have h_2ε_inv : (2 * ε)⁻¹ = (n : ℝ) ^ c := by
      dsimp [ε]
      have h1 : 2 * ((1 / 2 : ℝ) * (n : ℝ) ^ (-c)) = (n : ℝ) ^ (-c) := by ring
      rw [h1, Real.rpow_neg hn_pos.le, inv_inv]
    change (n : ℝ) ^ c ≤ (kappa G : ℝ)
    rwa [h_2ε_inv] at hkappa_ge

/--
**Theorem 3 (`(2) → (1)` for Single Graphs)**:
Every finite graph $H$ satisfying the polynomial Rödl property satisfies the Erdős–Hajnal property.
-/
theorem hasErdosHajnalProp_of_hasPolyRodlProp {W : Type*} {H : SimpleGraph W}
    (h : HasPolyRodlProp H) : HasErdosHajnalProp H := by
  rw [← hasPairErdosHajnalProp_self_iff]
  exact hasPairErdosHajnalProp_of_hasPairPolyRodlProp ((hasPairPolyRodlProp_self_iff H).mpr h)

/-! #### Theorem 3, Step 1: Kleitman–Winston Container Upper Bound -/

/-- The family of independent sets of cardinality $k$ inside $T \subseteq V(G)$. -/
noncomputable def indepSetsOfCard {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (T : Finset V) (k : ℕ) : Finset (Finset V) :=
  by classical exact (T.powersetCard k).filter (fun I => G.IsIndepSet (I : Set V))

/--
**Theorem 3, Step 1 (`kleitman_winston_container_bound`, Kleitman–Winston Container Upper Bound)**:
By strong induction on $|T| + \ell$: if $0 \le \ell \le k$, $\varepsilon \in (0, 1]$ satisfies
$(1 - \varepsilon)^\ell |T| \le u$, and every subset $S \subseteq T$ with $|S| > u$ is not
$\varepsilon$-sparse in $G$, then the number of independent $k$-sets of $G$ inside $T$ is at most
$\binom{|T|}{\ell}\binom{u}{k - \ell}$.
-/
theorem kleitman_winston_container_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : ℕ) (ε : ℝ) (_hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ (N : ℕ) (T : Finset V) (k ℓ : ℕ),
      T.card + ℓ = N →
      (∀ S ⊆ T, u < S.card → ¬IsEpsSparseOn G S ε) →
      ℓ ≤ k → (1 - ε) ^ ℓ * (T.card : ℝ) ≤ (u : ℝ) →
      (indepSetsOfCard G T k).card ≤ T.card.choose ℓ * u.choose (k - ℓ) := by
  classical
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro T k ℓ hN h_dense hℓk hu_bound
    by_cases hTu : T.card ≤ u
    · have h1 : (indepSetsOfCard G T k).card ≤ T.card.choose k := by
        unfold indepSetsOfCard
        exact (card_filter_le _ _).trans (by rw [card_powersetCard])
      have h2 : T.card.choose k ≤ T.card.choose k * k.choose ℓ :=
        Nat.le_mul_of_pos_right _ (Nat.choose_pos hℓk)
      have h3 : T.card.choose k * k.choose ℓ = T.card.choose ℓ * (T.card - ℓ).choose (k - ℓ) :=
        Nat.choose_mul hℓk
      have h4 : (T.card - ℓ).choose (k - ℓ) ≤ u.choose (k - ℓ) :=
        Nat.choose_le_choose (k - ℓ) (by omega)
      exact h1.trans (h2.trans (h3.trans_le (Nat.mul_le_mul_left _ h4)))
    · push_neg at hTu
      rcases ℓ with _ | ℓ'
      · exfalso
        simp only [pow_zero, one_mul] at hu_bound
        have hTu_r : (u : ℝ) < (T.card : ℝ) := by exact_mod_cast hTu
        linarith
      · rcases k with _ | k'
        · omega
        · have hℓ'k' : ℓ' ≤ k' := by omega
          have hsub_eq : k' - ℓ' = k' + 1 - (ℓ' + 1) := by omega
          have hnot_sparse := h_dense T Subset.rfl hTu
          unfold IsEpsSparseOn at hnot_sparse
          push_neg at hnot_sparse
          obtain ⟨v, hvT, hv_deg⟩ := hnot_sparse
          let T' := T.erase v
          have hT'T : T' ⊆ T := erase_subset v T
          have hT'_card : T'.card = T.card - 1 := card_erase_of_mem hvT
          let N_v := neighborFinsetIn G v T
          have hv_not_Nv : v ∉ N_v := by
            rw [mem_neighborFinsetIn_iff]
            exact fun h => G.loopless v h.2
          have hins_sub : insert v N_v ⊆ T :=
            insert_subset hvT (neighborFinsetIn_subset_ambient G v T)
          let U := T \ insert v N_v
          have hUT' : U ⊆ T' := by
            intro x hx
            rw [mem_sdiff, mem_insert, not_or] at hx
            exact mem_erase.mpr ⟨hx.2.1, hx.1⟩
          have hUT : U ⊆ T := hUT'.trans hT'T
          have hU_card_nat : U.card + (1 + N_v.card) = T.card := by
            have h1 := card_sdiff_add_card_eq_card hins_sub
            rw [card_insert_of_notMem hv_not_Nv, add_comm N_v.card 1] at h1
            exact h1
          have hU_card_real : (U.card : ℝ) ≤ (1 - ε) * (T.card : ℝ) := by
            have h1 : (U.card : ℝ) + (1 + (N_v.card : ℝ)) = (T.card : ℝ) := by
              exact_mod_cast hU_card_nat
            linarith
          have h1_sub_nonneg : 0 ≤ 1 - ε := by linarith
          have hU_bound : (1 - ε) ^ ℓ' * (U.card : ℝ) ≤ (u : ℝ) := by
            calc (1 - ε) ^ ℓ' * (U.card : ℝ)
              _ ≤ (1 - ε) ^ ℓ' * ((1 - ε) * (T.card : ℝ)) :=
                mul_le_mul_of_nonneg_left hU_card_real (by positivity)
              _ = (1 - ε) ^ (ℓ' + 1) * (T.card : ℝ) := by rw [pow_succ]; ring
              _ ≤ (u : ℝ) := hu_bound
          have hT'_bound : (1 - ε) ^ (ℓ' + 1) * (T'.card : ℝ) ≤ (u : ℝ) := by
            have hT'_le : (T'.card : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast card_le_card hT'T
            exact (mul_le_mul_of_nonneg_left hT'_le (by positivity)).trans hu_bound
          have hU_lt : U.card + ℓ' < N := by
            have : U.card ≤ T'.card := card_le_card hUT'
            omega
          have hT'_lt : T'.card + (ℓ' + 1) < N := by omega
          have h_ih_U := ih (U.card + ℓ') hU_lt U k' ℓ' rfl
            (fun S hSU => h_dense S (hSU.trans hUT)) hℓ'k' hU_bound
          have h_ih_T' := ih (T'.card + (ℓ' + 1)) hT'_lt T' (k' + 1) (ℓ' + 1) rfl
            (fun S hST' => h_dense S (hST'.trans hT'T)) hℓk hT'_bound
          let A := (indepSetsOfCard G T (k' + 1)).filter (fun I => v ∈ I)
          let B := (indepSetsOfCard G T (k' + 1)).filter (fun I => ¬v ∈ I)
          have hAB_sum : A.card + B.card = (indepSetsOfCard G T (k' + 1)).card :=
            card_filter_add_card_filter_not (fun I => v ∈ I)
          have hB_sub : B ⊆ indepSetsOfCard G T' (k' + 1) := by
            intro I hI
            simp only [B, indepSetsOfCard, mem_filter, mem_powersetCard] at hI ⊢
            refine ⟨⟨?_, hI.1.1.2⟩, hI.1.2⟩
            intro x hx
            exact mem_erase.mpr ⟨fun hxv => hI.2 (hxv ▸ hx), hI.1.1.1 hx⟩
          have hB_card : B.card ≤ T'.card.choose (ℓ' + 1) * u.choose (k' + 1 - (ℓ' + 1)) :=
            (card_le_card hB_sub).trans h_ih_T'
          have hA_inj : A.card ≤ (indepSetsOfCard G U k').card := by
            refine Finset.card_le_card_of_injOn (fun I => I.erase v) ?_ ?_
            · intro I hI
              simp only [mem_coe, A, indepSetsOfCard, mem_filter, mem_powersetCard] at hI ⊢
              obtain ⟨⟨⟨hIT, hI_card⟩, hI_indep⟩, hvI⟩ := hI
              refine ⟨⟨?_, ?_⟩, ?_⟩
              · intro x hx
                obtain ⟨hxv, hxI⟩ := mem_erase.mp hx
                rw [mem_sdiff, mem_insert, mem_neighborFinsetIn_iff, not_or]
                exact ⟨hIT hxI, hxv, fun h => hI_indep hvI hxI hxv.symm h.2⟩
              · rw [card_erase_of_mem hvI, hI_card, Nat.add_sub_cancel]
              · exact hI_indep.mono (by intro x hx; exact erase_subset v I hx)
            · intro I₁ hI₁ I₂ hI₂ h_eq
              dsimp only at h_eq
              simp only [mem_coe, A, mem_filter] at hI₁ hI₂
              rw [← insert_erase hI₁.2, h_eq, insert_erase hI₂.2]
          have hU_choose_le : U.card.choose ℓ' ≤ T'.card.choose ℓ' :=
            Nat.choose_le_choose ℓ' (card_le_card hUT')
          have hA_card : A.card ≤ T'.card.choose ℓ' * u.choose (k' + 1 - (ℓ' + 1)) := by
            rw [← hsub_eq]
            exact hA_inj.trans (h_ih_U.trans (Nat.mul_le_mul_right _ hU_choose_le))
          have hT_eq : T.card = T'.card + 1 := by omega
          calc (indepSetsOfCard G T (k' + 1)).card
            _ = A.card + B.card := hAB_sum.symm
            _ ≤ T'.card.choose ℓ' * u.choose (k' + 1 - (ℓ' + 1)) +
                  T'.card.choose (ℓ' + 1) * u.choose (k' + 1 - (ℓ' + 1)) :=
              Nat.add_le_add hA_card hB_card
            _ = (T'.card.choose ℓ' + T'.card.choose (ℓ' + 1)) * u.choose (k' + 1 - (ℓ' + 1)) :=
              (Nat.add_mul _ _ _).symm
            _ = (T'.card + 1).choose (ℓ' + 1) * u.choose (k' + 1 - (ℓ' + 1)) := by
              rw [Nat.choose_succ_succ]
            _ = T.card.choose (ℓ' + 1) * u.choose (k' + 1 - (ℓ' + 1)) := by rw [← hT_eq]

/-! #### Theorem 3, Step 2: Random Sampling and Double-Counting Lower Bound -/

/--
Binomial ratio bound in $\mathbb{N}$: for $r \le b \le a$,
$\binom{a - r}{b - r} a^r \le \binom{a}{b} b^r$.
-/
theorem choose_sub_mul_pow_le (r : ℕ) :
    ∀ {a b : ℕ}, r ≤ b → b ≤ a → (a - r).choose (b - r) * a ^ r ≤ a.choose b * b ^ r := by
  induction r with
  | zero =>
    intro a b _ _
    simp
  | succ r ih =>
    intro a b hrb hba
    let a' := a - r
    let b' := b - r
    have hb'_pos : 1 ≤ b' := by dsimp [b']; omega
    have ha'_pos : 1 ≤ a' := by dsimp [a']; omega
    have hb'a' : b' ≤ a' := by dsimp [a', b']; omega
    have ha'_eq : a' = (a' - 1) + 1 := (Nat.sub_add_cancel ha'_pos).symm
    have hb'_eq : b' = (b' - 1) + 1 := (Nat.sub_add_cancel hb'_pos).symm
    have h_step1 : (a' - 1).choose (b' - 1) * a' = a'.choose b' * b' := by
      have h1 := Nat.add_one_mul_choose_eq (a' - 1) (b' - 1)
      rw [← ha'_eq, ← hb'_eq, Nat.mul_comm] at h1
      exact h1
    have h_ba' : b' * a ≤ b * a' := by
      dsimp [a', b']
      rw [Nat.sub_mul, Nat.mul_sub, Nat.mul_comm b r]
      exact Nat.sub_le_sub_left (Nat.mul_le_mul_left r hba) (b * a)
    have h_step2 : ((a' - 1).choose (b' - 1) * a) * a' ≤ (a'.choose b' * b) * a' := by
      calc ((a' - 1).choose (b' - 1) * a) * a'
        _ = ((a' - 1).choose (b' - 1) * a') * a := by ring
        _ = (a'.choose b' * b') * a := by rw [h_step1]
        _ = a'.choose b' * (b' * a) := by ring
        _ ≤ a'.choose b' * (b * a') := Nat.mul_le_mul_left _ h_ba'
        _ = (a'.choose b' * b) * a' := by ring
    have h_step3 : (a' - 1).choose (b' - 1) * a ≤ a'.choose b' * b :=
      Nat.le_of_mul_le_mul_right h_step2 (by omega : 0 < a')
    have h_ih := ih (by omega : r ≤ b) hba
    have ha_sub : a - (r + 1) = a' - 1 := by dsimp [a']; omega
    have hb_sub : b - (r + 1) = b' - 1 := by dsimp [b']; omega
    rw [ha_sub, hb_sub, pow_succ, pow_succ]
    calc (a' - 1).choose (b' - 1) * (a ^ r * a)
      _ = ((a' - 1).choose (b' - 1) * a) * a ^ r := by ring
      _ ≤ (a'.choose b' * b) * a ^ r := Nat.mul_le_mul_right _ h_step3
      _ = (a'.choose b' * a ^ r) * b := by ring
      _ ≤ (a.choose b * b ^ r) * b := Nat.mul_le_mul_right _ h_ih
      _ = a.choose b * (b ^ r * b) := by ring

/--
Upper bound on the number of $m$-element subsets of `Finset.univ : Finset V` containing a fixed
subset $A \subseteq V$:
$|\{S \in \binom{V}{m} : A \subseteq S\}| \cdot |V|^{|A|} \le \binom{|V|}{m} m^{|A|}$.
-/
theorem card_powersetCard_superset_mul_pow_le {V : Type*} [Fintype V] [DecidableEq V]
    (A : Finset V) (m : ℕ) (hm : m ≤ Fintype.card V) :
    (((Finset.univ : Finset V).powersetCard m).filter (fun S => A ⊆ S)).card *
      (Fintype.card V) ^ A.card ≤
      (Fintype.card V).choose m * m ^ A.card := by
  classical
  by_cases hAm : A.card ≤ m
  · have h_bij : (((Finset.univ : Finset V).powersetCard m).filter (fun S => A ⊆ S)).card =
        (Fintype.card V - A.card).choose (m - A.card) := by
      have h_compl_card : (Finset.univ \ A).card = Fintype.card V - A.card := by
        have hsum := card_sdiff_add_card_eq_card (subset_univ A)
        rw [card_univ] at hsum
        omega
      rw [← h_compl_card, ← card_powersetCard]
      refine Finset.card_bij (fun S _ => S \ A) ?_ ?_ ?_
      · intro S hS
        simp only [mem_filter, mem_powersetCard, subset_univ, true_and] at hS ⊢
        refine ⟨sdiff_subset_sdiff (subset_univ S) Subset.rfl, ?_⟩
        have hsum := card_sdiff_add_card_eq_card hS.2
        omega
      · intro S₁ hS₁ S₂ hS₂ h_eq
        dsimp only at h_eq
        simp only [mem_filter, mem_powersetCard, subset_univ, true_and] at hS₁ hS₂
        rw [← sdiff_union_of_subset hS₁.2, h_eq, sdiff_union_of_subset hS₂.2]
      · intro T hT
        simp only [mem_powersetCard] at hT
        refine ⟨T ∪ A, ?_, ?_⟩
        · simp only [mem_filter, mem_powersetCard, subset_univ, true_and]
          have hdisj : Disjoint T A :=
            Disjoint.mono_left hT.1 disjoint_sdiff_self_left
          refine ⟨?_, subset_union_right⟩
          rw [card_union_of_disjoint hdisj, hT.2]
          omega
        · have hdisj : Disjoint T A :=
            Disjoint.mono_left hT.1 disjoint_sdiff_self_left
          exact union_sdiff_cancel_right hdisj
    rw [h_bij]
    exact choose_sub_mul_pow_le A.card hAm hm
  · push_neg at hAm
    have hemp : (((Finset.univ : Finset V).powersetCard m).filter (fun S => A ⊆ S)) = ∅ := by
      rw [filter_eq_empty_iff]
      intro S hS hAS
      rw [mem_powersetCard] at hS
      have := card_le_card hAS
      omega
    rw [hemp, card_empty, zero_mul]
    exact Nat.zero_le _

/-- Induced copies of $H$ in $G$ whose image lies inside $S \subseteq V$. -/
noncomputable def copiesInSubset {W V : Type*} [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V] (H : SimpleGraph W) (G : SimpleGraph V) (S : Finset V) :
    Finset (W ↪ V) :=
  by
    classical
    exact ((Finset.univ.filter (fun g : W ↪ V => G.comap g = H)).filter
      (fun g => Finset.univ.map g ⊆ S))

/--
Double-counting bound on the total number of induced copies of $H$ inside $m$-subsets of $V(G)$:
$\left(\sum_{S \in \binom{V}{m}} |\operatorname{copiesInSubset}(H, G, S)|\right) |V|^{|W|} \le \operatorname{ind}_H(G) \binom{|V|}{m} m^{|W|}$.
-/
theorem sum_card_copiesInSubset_mul_pow_le {W V : Type*} [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V] (H : SimpleGraph W) (G : SimpleGraph V) (m : ℕ)
    (hm : m ≤ Fintype.card V) :
    (∑ S ∈ (Finset.univ : Finset V).powersetCard m, (copiesInSubset H G S).card) *
      (Fintype.card V) ^ (Fintype.card W) ≤
      indCopyCount H G * (Fintype.card V).choose m * m ^ (Fintype.card W) := by
  classical
  let Ω := (Finset.univ : Finset V).powersetCard m
  let Copies := Finset.univ.filter (fun g : W ↪ V => G.comap g = H)
  have h_swap : ∑ S ∈ Ω, (copiesInSubset H G S).card =
      ∑ g ∈ Copies, (Ω.filter (fun S => Finset.univ.map g ⊆ S)).card := by
    unfold copiesInSubset
    have h1 : ∀ S : Finset V,
        ((Copies.filter (fun g => Finset.univ.map g ⊆ S)).card : ℕ) =
          ∑ g ∈ Copies, if Finset.univ.map g ⊆ S then 1 else 0 := by
      intro S
      rw [card_filter]
    have h2 : ∀ g : W ↪ V,
        ((Ω.filter (fun S => Finset.univ.map g ⊆ S)).card : ℕ) =
          ∑ S ∈ Ω, if Finset.univ.map g ⊆ S then 1 else 0 := by
      intro g
      rw [card_filter]
    simp only [Copies] at h1
    simp only [h1, h2]
    exact sum_comm
  rw [h_swap, sum_mul]
  calc ∑ g ∈ Copies, (Ω.filter (fun S => Finset.univ.map g ⊆ S)).card *
        (Fintype.card V) ^ (Fintype.card W)
    _ ≤ ∑ _g ∈ Copies, (Fintype.card V).choose m * m ^ (Fintype.card W) := by
      refine sum_le_sum (fun g _ => ?_)
      have hcard_map : (Finset.univ.map g).card = Fintype.card W := by simp
      have h := card_powersetCard_superset_mul_pow_le (Finset.univ.map g) m hm
      rwa [hcard_map] at h
    _ = indCopyCount H G * (Fintype.card V).choose m * m ^ (Fintype.card W) := by
      unfold indCopyCount
      rw [sum_const, smul_eq_mul, mul_assoc]

/--
If $\operatorname{ind}_H(G) \le (|V|/(8t))^{|W|}$, then the average number of induced copies of $H$
in a $2t$-subset of $V(G)$ is at most $t/4$.
-/
private theorem sum_copiesInSubset_le_quarter_t
    {W V : Type*} [Fintype W] [DecidableEq W] [Nonempty W] [Fintype V] [DecidableEq V]
    (H : SimpleGraph W) (G : SimpleGraph V) (t : ℕ)
    (ht_pos : 1 ≤ t) (h2tn : 2 * t ≤ Fintype.card V)
    (hc : (indCopyCount H G : ℝ) ≤ ((Fintype.card V : ℝ) / (8 * (t : ℝ))) ^ (Fintype.card W)) :
    ∑ S ∈ (Finset.univ : Finset V).powersetCard (2 * t), ((copiesInSubset H G S).card : ℝ) ≤
      ((t : ℝ) / 4) * ((Fintype.card V).choose (2 * t) : ℝ) := by
  classical
  let n := Fintype.card V
  let r := Fintype.card W
  have hr1 : 1 ≤ r := Fintype.card_pos
  have ht_pos_r : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht_pos
  have hn_pos : 1 ≤ n := by omega
  have hn_pos_r : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have h_nat := sum_card_copiesInSubset_mul_pow_le H G (2 * t) h2tn
  have h_real : (∑ S ∈ (Finset.univ : Finset V).powersetCard (2 * t),
      ((copiesInSubset H G S).card : ℝ)) * (n : ℝ) ^ r ≤
      (indCopyCount H G : ℝ) * (n.choose (2 * t) : ℝ) * (2 * (t : ℝ)) ^ r := by
    exact_mod_cast h_nat
  have h_quarter_pow : (1 / 4 : ℝ) ^ r ≤ 1 / 4 := by
    have h1 : (1 / 4 : ℝ) ^ r ≤ (1 / 4 : ℝ) ^ 1 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hr1
    simpa using h1
  have ht1_r : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht_pos
  have h_prod : (indCopyCount H G : ℝ) * (2 * (t : ℝ)) ^ r ≤ ((t : ℝ) / 4) * (n : ℝ) ^ r := by
    calc (indCopyCount H G : ℝ) * (2 * (t : ℝ)) ^ r
      _ ≤ ((n : ℝ) / (8 * (t : ℝ))) ^ r * (2 * (t : ℝ)) ^ r :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ = (((n : ℝ) / (8 * (t : ℝ))) * (2 * (t : ℝ))) ^ r := (mul_pow _ _ r).symm
      _ = ((1 / 4 : ℝ) * (n : ℝ)) ^ r := by
        congr 1
        have : (t : ℝ) ≠ 0 := ht_pos_r.ne'
        field_simp
        ring
      _ = (1 / 4 : ℝ) ^ r * (n : ℝ) ^ r := mul_pow _ _ r
      _ ≤ (1 / 4 : ℝ) * (n : ℝ) ^ r :=
        mul_le_mul_of_nonneg_right h_quarter_pow (by positivity)
      _ ≤ ((t : ℝ) / 4) * (n : ℝ) ^ r := by
        have : (1 / 4 : ℝ) ≤ (t : ℝ) / 4 := by linarith
        exact mul_le_mul_of_nonneg_right this (by positivity)
  have h_mul_le : (∑ S ∈ (Finset.univ : Finset V).powersetCard (2 * t),
      ((copiesInSubset H G S).card : ℝ)) * (n : ℝ) ^ r ≤
      (((t : ℝ) / 4) * (n.choose (2 * t) : ℝ)) * (n : ℝ) ^ r := by
    calc (∑ S ∈ (Finset.univ : Finset V).powersetCard (2 * t),
          ((copiesInSubset H G S).card : ℝ)) * (n : ℝ) ^ r
      _ ≤ (n.choose (2 * t) : ℝ) * ((indCopyCount H G : ℝ) * (2 * (t : ℝ)) ^ r) := by
        linarith [h_real]
      _ ≤ (n.choose (2 * t) : ℝ) * (((t : ℝ) / 4) * (n : ℝ) ^ r) :=
        mul_le_mul_of_nonneg_left h_prod (by positivity)
      _ = (((t : ℝ) / 4) * (n.choose (2 * t) : ℝ)) * (n : ℝ) ^ r := by ring
  exact le_of_mul_le_mul_right h_mul_le (by positivity : (0 : ℝ) < (n : ℝ) ^ r)

/--
**Theorem 3, Step 2 (`random_sampling_homog_sets_lower_bound`)**:
If $1 \le k \le t$, $2t \le |V|$, every $\{H_1, H_2\}$-free induced subgraph $G[U]$ on $|U| \ge t$
vertices satisfies $\kappa(G[U]) \ge k$, and $\operatorname{ind}_{H_i}(G) \le (|V| / (8t))^{|W_i|}$
for $i = 1, 2$, then either $G$ or $\overline{G}$ contains at least $\frac{1}{4}(|V| / (2t))^k$
independent sets of size $k$.
-/
theorem random_sampling_homog_sets_lower_bound
    {W₁ W₂ V : Type*} [Fintype W₁] [DecidableEq W₁] [Nonempty W₁]
    [Fintype W₂] [DecidableEq W₂] [Nonempty W₂] [Fintype V] [DecidableEq V]
    (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂) (G : SimpleGraph V)
    (k t : ℕ) (hk1 : 1 ≤ k) (hkt : k ≤ t) (h2tn : 2 * t ≤ Fintype.card V)
    (h_eh_t : ∀ U : Finset V, t ≤ U.card →
      IsInducedSubgraphFree (G.induce (U : Set V)) H₁ →
      IsInducedSubgraphFree (G.induce (U : Set V)) H₂ →
      (k : ℝ) ≤ (kappa (G.induce (U : Set V)) : ℝ))
    (hc₁ : (indCopyCount H₁ G : ℝ) ≤ ((Fintype.card V : ℝ) / (8 * (t : ℝ))) ^ (Fintype.card W₁))
    (hc₂ : (indCopyCount H₂ G : ℝ) ≤ ((Fintype.card V : ℝ) / (8 * (t : ℝ))) ^ (Fintype.card W₂)) :
    (Fintype.card V : ℝ) ^ k ≤
      4 * ((indepSetsOfCard G Finset.univ k).card : ℝ) * (2 * (t : ℝ)) ^ k ∨
    (Fintype.card V : ℝ) ^ k ≤
      4 * ((indepSetsOfCard Gᶜ Finset.univ k).card : ℝ) * (2 * (t : ℝ)) ^ k := by
  classical
  let n := Fintype.card V
  have ht_pos : 1 ≤ t := hk1.trans hkt
  have ht_pos_r : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht_pos
  let Ω := (Finset.univ : Finset V).powersetCard (2 * t)
  have hΩ_card : Ω.card = n.choose (2 * t) := by simp [Ω, n]
  have hΩ_pos : 0 < n.choose (2 * t) := Nat.choose_pos h2tn
  have hΩ_pos_r : (0 : ℝ) < (n.choose (2 * t) : ℝ) := by exact_mod_cast hΩ_pos
  have h_sum1 := sum_copiesInSubset_le_quarter_t H₁ G t ht_pos h2tn hc₁
  have h_sum2 := sum_copiesInSubset_le_quarter_t H₂ G t ht_pos h2tn hc₂
  let P_bad : Finset V → Prop := fun S => t < (copiesInSubset H₁ G S).card + (copiesInSubset H₂ G S).card
  let BadS := Ω.filter P_bad
  let GoodS := Ω.filter (fun S => ¬P_bad S)
  have h_part : (GoodS.card : ℝ) + (BadS.card : ℝ) = (n.choose (2 * t) : ℝ) := by
    have h1 := card_filter_add_card_filter_not P_bad (s := Ω)
    rw [hΩ_card, add_comm] at h1
    exact_mod_cast h1
  have hBad_markov : (BadS.card : ℝ) * (t : ℝ) ≤
      ∑ S ∈ Ω, (((copiesInSubset H₁ G S).card : ℝ) + ((copiesInSubset H₂ G S).card : ℝ)) := by
    calc (BadS.card : ℝ) * (t : ℝ)
      _ = ∑ _S ∈ BadS, (t : ℝ) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ S ∈ BadS, (((copiesInSubset H₁ G S).card : ℝ) + ((copiesInSubset H₂ G S).card : ℝ)) := by
        refine sum_le_sum (fun S hS => ?_)
        simp only [BadS, P_bad, mem_filter] at hS
        have : t ≤ (copiesInSubset H₁ G S).card + (copiesInSubset H₂ G S).card := hS.2.le
        exact_mod_cast this
      _ ≤ ∑ S ∈ Ω, (((copiesInSubset H₁ G S).card : ℝ) + ((copiesInSubset H₂ G S).card : ℝ)) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
  have hBad_le : (BadS.card : ℝ) ≤ (1 / 2 : ℝ) * (n.choose (2 * t) : ℝ) := by
    rw [sum_add_distrib] at hBad_markov
    have h1 : (BadS.card : ℝ) * (t : ℝ) ≤ ((1 / 2 : ℝ) * (n.choose (2 * t) : ℝ)) * (t : ℝ) := by
      linarith
    exact le_of_mul_le_mul_right h1 ht_pos_r
  have hGood_ge : (1 / 2 : ℝ) * (n.choose (2 * t) : ℝ) ≤ (GoodS.card : ℝ) := by linarith
  let Hom := indepSetsOfCard G Finset.univ k ∪ indepSetsOfCard Gᶜ Finset.univ k
  have hGood_in_Hom : ∀ S ∈ GoodS, ∃ I ∈ Hom, I ⊆ S := by
    intro S hS
    simp only [GoodS, Ω, P_bad, mem_filter, mem_powersetCard, subset_univ, true_and, not_lt] at hS
    obtain ⟨hS_card, hS_copies⟩ := hS
    obtain ⟨w₁₀⟩ := ‹Nonempty W₁›
    obtain ⟨w₂₀⟩ := ‹Nonempty W₂›
    let D₁ := (copiesInSubset H₁ G S).image (fun g => g w₁₀)
    let D₂ := (copiesInSubset H₂ G S).image (fun g => g w₂₀)
    let D := D₁ ∪ D₂
    have hD_card : D.card ≤ t := by
      calc D.card
        _ ≤ D₁.card + D₂.card := card_union_le D₁ D₂
        _ ≤ (copiesInSubset H₁ G S).card + (copiesInSubset H₂ G S).card :=
          Nat.add_le_add card_image_le card_image_le
        _ ≤ t := hS_copies
    let U := S \ D
    have hUS : U ⊆ S := sdiff_subset
    have hU_card : t ≤ U.card := by
      have hle := card_le_card_sdiff_add_card (s := S) (t := D)
      change t ≤ (S \ D).card
      omega
    have hU_free₁ : IsInducedSubgraphFree (G.induce (U : Set V)) H₁ := by
      rintro ⟨f, hf⟩
      let g : W₁ ↪ V := f.trans (Function.Embedding.subtype _)
      have hg_in : g ∈ copiesInSubset H₁ G S := by
        simp only [copiesInSubset, mem_filter, mem_univ, true_and]
        refine ⟨?_, ?_⟩
        · ext u v
          have h1 := congr_arg (fun (J : SimpleGraph W₁) => J.Adj u v) hf
          simpa [g, comap_adj] using h1.symm
        · intro x hx
          rcases mem_map.mp hx with ⟨w, _, rfl⟩
          exact hUS (f w).2
      have h_mem_D : g w₁₀ ∈ D :=
        mem_union_left D₂ (mem_image.mpr ⟨g, hg_in, rfl⟩)
      have h_mem_U : g w₁₀ ∈ U := (f w₁₀).2
      exact (mem_sdiff.mp h_mem_U).2 h_mem_D
    have hU_free₂ : IsInducedSubgraphFree (G.induce (U : Set V)) H₂ := by
      rintro ⟨f, hf⟩
      let g : W₂ ↪ V := f.trans (Function.Embedding.subtype _)
      have hg_in : g ∈ copiesInSubset H₂ G S := by
        simp only [copiesInSubset, mem_filter, mem_univ, true_and]
        refine ⟨?_, ?_⟩
        · ext u v
          have h1 := congr_arg (fun (J : SimpleGraph W₂) => J.Adj u v) hf
          simpa [g, comap_adj] using h1.symm
        · intro x hx
          rcases mem_map.mp hx with ⟨w, _, rfl⟩
          exact hUS (f w).2
      have h_mem_D : g w₂₀ ∈ D :=
        mem_union_right D₁ (mem_image.mpr ⟨g, hg_in, rfl⟩)
      have h_mem_U : g w₂₀ ∈ U := (f w₂₀).2
      exact (mem_sdiff.mp h_mem_U).2 h_mem_D
    have hkappa := h_eh_t U hU_card hU_free₁ hU_free₂
    rcases (kappa_cast_ge_iff (G.induce (U : Set V)) (k : ℝ)).mp hkappa with hclq | hind
    · have hk_clq : k ≤ (G.induce (U : Set V)).cliqueNum := by exact_mod_cast hclq
      obtain ⟨C₀, hC₀⟩ := (G.induce (U : Set V)).exists_isNClique_cliqueNum
      rw [← hC₀.card_eq] at hk_clq
      obtain ⟨C₁, hC₁_sub, hC₁_card⟩ := exists_subset_card_eq hk_clq
      let emb : ↥(U : Set V) ↪ V := Function.Embedding.subtype _
      let I := C₁.map emb
      refine ⟨I, mem_union_right _ ?_, ?_⟩
      · simp only [indepSetsOfCard, mem_filter, mem_powersetCard, subset_univ, true_and]
        refine ⟨by rw [card_map, hC₁_card], ?_⟩
        intro x hx y hy hxy
        rcases mem_map.mp (mem_coe.mp hx) with ⟨a, ha, rfl⟩
        rcases mem_map.mp (mem_coe.mp hy) with ⟨b, hb, rfl⟩
        have hab : a ≠ b := ne_of_apply_ne emb hxy
        have hadj : G.Adj (emb a) (emb b) := hC₀.isClique (hC₁_sub ha) (hC₁_sub hb) hab
        rw [compl_adj]
        exact fun h => h.2 hadj
      · intro x hx
        rcases mem_map.mp hx with ⟨a, _, rfl⟩
        exact hUS a.2
    · have hk_ind : k ≤ (G.induce (U : Set V)).indepNum := by exact_mod_cast hind
      obtain ⟨I₀, hI₀⟩ := (G.induce (U : Set V)).exists_isNIndepSet_indepNum
      rw [← hI₀.card_eq] at hk_ind
      obtain ⟨I₁, hI₁_sub, hI₁_card⟩ := exists_subset_card_eq hk_ind
      let emb : ↥(U : Set V) ↪ V := Function.Embedding.subtype _
      let I := I₁.map emb
      refine ⟨I, mem_union_left _ ?_, ?_⟩
      · simp only [indepSetsOfCard, mem_filter, mem_powersetCard, subset_univ, true_and]
        refine ⟨by rw [card_map, hI₁_card], ?_⟩
        intro x hx y hy hxy
        rcases mem_map.mp (mem_coe.mp hx) with ⟨a, ha, rfl⟩
        rcases mem_map.mp (mem_coe.mp hy) with ⟨b, hb, rfl⟩
        have hab : a ≠ b := ne_of_apply_ne emb hxy
        exact hI₀.isIndepSet (hI₁_sub ha) (hI₁_sub hb) hab
      · intro x hx
        rcases mem_map.mp hx with ⟨a, _, rfl⟩
        exact hUS a.2
  have hGood_sub : GoodS ⊆ Hom.biUnion (fun I => Ω.filter (fun S => I ⊆ S)) := by
    intro S hS
    obtain ⟨I, hI_Hom, hIS⟩ := hGood_in_Hom S hS
    exact mem_biUnion.mpr ⟨I, hI_Hom, mem_filter.mpr ⟨(filter_subset _ _ hS), hIS⟩⟩
  have hGood_double_count : GoodS.card * n ^ k ≤ Hom.card * n.choose (2 * t) * (2 * t) ^ k := by
    have h1 : GoodS.card ≤ ∑ I ∈ Hom, (Ω.filter (fun S => I ⊆ S)).card :=
      (card_le_card hGood_sub).trans card_biUnion_le
    calc GoodS.card * n ^ k
      _ ≤ (∑ I ∈ Hom, (Ω.filter (fun S => I ⊆ S)).card) * n ^ k :=
        Nat.mul_le_mul_right (n ^ k) h1
      _ = ∑ I ∈ Hom, (Ω.filter (fun S => I ⊆ S)).card * n ^ k := sum_mul _ _ _
      _ ≤ ∑ _I ∈ Hom, n.choose (2 * t) * (2 * t) ^ k := by
        refine sum_le_sum (fun I hI => ?_)
        have hI_card : I.card = k := by
          rcases mem_union.mp hI with hG | hGc
          · simp only [indepSetsOfCard, mem_filter, mem_powersetCard] at hG
            exact hG.1.2
          · simp only [indepSetsOfCard, mem_filter, mem_powersetCard] at hGc
            exact hGc.1.2
        have h := card_powersetCard_superset_mul_pow_le I (2 * t) h2tn
        rwa [hI_card] at h
      _ = Hom.card * n.choose (2 * t) * (2 * t) ^ k := by
        rw [sum_const, smul_eq_mul, mul_assoc]
  have hHom_real : (n : ℝ) ^ k ≤ 2 * (Hom.card : ℝ) * (2 * (t : ℝ)) ^ k := by
    have h_dc_r : (GoodS.card : ℝ) * (n : ℝ) ^ k ≤
        (Hom.card : ℝ) * (n.choose (2 * t) : ℝ) * (2 * (t : ℝ)) ^ k := by
      exact_mod_cast hGood_double_count
    have h_mul : (n.choose (2 * t) : ℝ) * (n : ℝ) ^ k ≤
        (n.choose (2 * t) : ℝ) * (2 * (Hom.card : ℝ) * (2 * (t : ℝ)) ^ k) := by
      calc (n.choose (2 * t) : ℝ) * (n : ℝ) ^ k
        _ ≤ (2 * (GoodS.card : ℝ)) * (n : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = 2 * ((GoodS.card : ℝ) * (n : ℝ) ^ k) := by ring
        _ ≤ 2 * ((Hom.card : ℝ) * (n.choose (2 * t) : ℝ) * (2 * (t : ℝ)) ^ k) :=
          mul_le_mul_of_nonneg_left h_dc_r (by norm_num)
        _ = (n.choose (2 * t) : ℝ) * (2 * (Hom.card : ℝ) * (2 * (t : ℝ)) ^ k) := by ring
    exact le_of_mul_le_mul_left h_mul hΩ_pos_r
  have hHom_union : (Hom.card : ℝ) ≤
      ((indepSetsOfCard G Finset.univ k).card : ℝ) +
      ((indepSetsOfCard Gᶜ Finset.univ k).card : ℝ) := by
    exact_mod_cast card_union_le (indepSetsOfCard G Finset.univ k) (indepSetsOfCard Gᶜ Finset.univ k)
  by_cases hG_ge : ((indepSetsOfCard Gᶜ Finset.univ k).card : ℝ) ≤
      ((indepSetsOfCard G Finset.univ k).card : ℝ)
  · left
    have h2 : (Hom.card : ℝ) ≤ 2 * ((indepSetsOfCard G Finset.univ k).card : ℝ) := by linarith
    calc (n : ℝ) ^ k
      _ ≤ 2 * (Hom.card : ℝ) * (2 * (t : ℝ)) ^ k := hHom_real
      _ ≤ 2 * (2 * ((indepSetsOfCard G Finset.univ k).card : ℝ)) * (2 * (t : ℝ)) ^ k := by
        have : 0 ≤ (2 * (t : ℝ)) ^ k := by positivity
        nlinarith
      _ = 4 * ((indepSetsOfCard G Finset.univ k).card : ℝ) * (2 * (t : ℝ)) ^ k := by ring
  · right
    push_neg at hG_ge
    have h2 : (Hom.card : ℝ) ≤ 2 * ((indepSetsOfCard Gᶜ Finset.univ k).card : ℝ) := by linarith
    calc (n : ℝ) ^ k
      _ ≤ 2 * (Hom.card : ℝ) * (2 * (t : ℝ)) ^ k := hHom_real
      _ ≤ 2 * (2 * ((indepSetsOfCard Gᶜ Finset.univ k).card : ℝ)) * (2 * (t : ℝ)) ^ k := by
        have : 0 ≤ (2 * (t : ℝ)) ^ k := by positivity
        nlinarith
      _ = 4 * ((indepSetsOfCard Gᶜ Finset.univ k).card : ℝ) * (2 * (t : ℝ)) ^ k := by ring

/-! #### Theorem 3, Step 3: Deduction of Virality -/

/-- Elementary binomial-factorial bound $\binom{a}{b} b! \le a^b$. -/
private theorem choose_mul_factorial_le_pow (a b : ℕ) : a.choose b * b.factorial ≤ a ^ b := by
  induction b generalizing a with
  | zero => simp
  | succ b ih =>
    rcases a with _ | a
    · simp
    · rw [Nat.choose_succ_succ, Nat.factorial_succ]
      have h_id : (a + 1).choose (b + 1) * (b + 1) = (a + 1) * a.choose b := by
        have h1 := Nat.add_one_mul_choose_eq a b
        linarith
      calc (a.choose b + a.choose (b + 1)) * ((b + 1) * b.factorial)
        _ = ((a + 1).choose (b + 1) * (b + 1)) * b.factorial := by
          rw [← Nat.choose_succ_succ, mul_assoc]
        _ = (a + 1) * (a.choose b * b.factorial) := by rw [h_id, mul_assoc]
        _ ≤ (a + 1) * a ^ b := Nat.mul_le_mul_left (a + 1) (ih a)
        _ ≤ (a + 1) * (a + 1) ^ b :=
          Nat.mul_le_mul_left (a + 1) (Nat.pow_le_pow_left (Nat.le_succ a) b)
        _ = (a + 1) ^ (b + 1) := by rw [pow_succ']

/-- Product binomial bound $\binom{n}{\ell}\binom{u}{k-\ell} k! \le 2^k n^\ell u^{k-\ell}$. -/
private theorem choose_mul_choose_mul_factorial_le (n u k ℓ : ℕ) (hℓk : ℓ ≤ k) :
    (n.choose ℓ * u.choose (k - ℓ)) * k.factorial ≤ 2 ^ k * n ^ ℓ * u ^ (k - ℓ) := by
  have hk_eq : k = ℓ + (k - ℓ) := (Nat.add_sub_of_le hℓk).symm
  have h_fact : k.factorial = k.choose (k - ℓ) * ℓ.factorial * (k - ℓ).factorial := by
    have h1 := Nat.add_choose_mul_factorial_mul_factorial ℓ (k - ℓ)
    rwa [← hk_eq, eq_comm] at h1
  have h1 := choose_mul_factorial_le_pow n ℓ
  have h2 := choose_mul_factorial_le_pow u (k - ℓ)
  have h3 : k.choose (k - ℓ) ≤ 2 ^ k := Nat.choose_le_two_pow k (k - ℓ)
  calc (n.choose ℓ * u.choose (k - ℓ)) * k.factorial
    _ = k.choose (k - ℓ) * (n.choose ℓ * ℓ.factorial) * (u.choose (k - ℓ) * (k - ℓ).factorial) := by
      rw [h_fact]
      ring
    _ ≤ 2 ^ k * n ^ ℓ * u ^ (k - ℓ) :=
      Nat.mul_le_mul (Nat.mul_le_mul h3 h1) h2

/-- Elementary bound $(k + 1)^k \le 4 k^k$ via $\log(1 + 1/k) \le 1/k$ and $e < 4$. -/
private theorem succ_pow_le_four_mul_pow (k : ℕ) : (k + 1) ^ k ≤ 4 * k ^ k := by
  rcases eq_or_ne k 0 with rfl | hk0
  · simp
  · have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
    have h1_pos : (0 : ℝ) < 1 + 1 / (k : ℝ) := by positivity
    have hlog_step : Real.log ((1 + 1 / (k : ℝ)) ^ k) ≤ 1 := by
      rw [Real.log_pow]
      have h1 : Real.log (1 + 1 / (k : ℝ)) ≤ (1 + 1 / (k : ℝ)) - 1 :=
        Real.log_le_sub_one_of_pos h1_pos
      have h2 : (k : ℝ) * ((1 + 1 / (k : ℝ)) - 1) = 1 := by
        field_simp [hk_pos.ne']
        ring
      nlinarith
    have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
      have hlog2 := log_two_ge_seven_twelfths
      have h4 : (4 : ℝ) = 2 * 2 := by norm_num
      rw [h4, Real.log_mul two_pos.ne' two_pos.ne']
      linarith
    have hpow_le_four : (1 + 1 / (k : ℝ)) ^ k ≤ 4 :=
      (Real.log_le_log_iff (by positivity) (by norm_num)).mp (hlog_step.trans hlog4)
    have h_real : ((k + 1 : ℕ) : ℝ) ^ k ≤ 4 * (k : ℝ) ^ k := by
      have h_id : ((k + 1 : ℕ) : ℝ) = (1 + 1 / (k : ℝ)) * (k : ℝ) := by
        push_cast
        field_simp [hk_pos.ne']
      rw [h_id, mul_pow]
      exact mul_le_mul_of_nonneg_right hpow_le_four (by positivity)
    exact_mod_cast h_real

/-- Stirling-type upper bound $k^k \le 4^k k!$. -/
private theorem pow_self_le_four_pow_mul_factorial (k : ℕ) : k ^ k ≤ 4 ^ k * k.factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := succ_pow_le_four_mul_pow k
    calc (k + 1) ^ (k + 1)
      _ = (k + 1) * (k + 1) ^ k := by rw [pow_succ']
      _ ≤ (k + 1) * (4 * k ^ k) := Nat.mul_le_mul_left (k + 1) h1
      _ = 4 * (k + 1) * k ^ k := by ring
      _ ≤ 4 * (k + 1) * (4 ^ k * k.factorial) := Nat.mul_le_mul_left _ ih
      _ = 4 ^ (k + 1) * (k + 1).factorial := by
        rw [pow_succ', Nat.factorial_succ]
        ring

/-- Container binomial-to-power inequality $\binom{n}{\ell}\binom{u}{k-\ell} k^k \le 8^k n^\ell u^{k-\ell}$. -/
private theorem choose_mul_choose_mul_pow_self_le (n u k ℓ : ℕ) (hℓk : ℓ ≤ k) :
    (n.choose ℓ * u.choose (k - ℓ)) * k ^ k ≤ 8 ^ k * n ^ ℓ * u ^ (k - ℓ) := by
  have h1 := choose_mul_choose_mul_factorial_le n u k ℓ hℓk
  have h2 := pow_self_le_four_pow_mul_factorial k
  have h8 : (8 : ℕ) ^ k = 4 ^ k * 2 ^ k := by
    rw [← mul_pow]
    rfl
  calc (n.choose ℓ * u.choose (k - ℓ)) * k ^ k
    _ ≤ (n.choose ℓ * u.choose (k - ℓ)) * (4 ^ k * k.factorial) := Nat.mul_le_mul_left _ h2
    _ = 4 ^ k * ((n.choose ℓ * u.choose (k - ℓ)) * k.factorial) := by ring
    _ ≤ 4 ^ k * (2 ^ k * n ^ ℓ * u ^ (k - ℓ)) := Nat.mul_le_mul_left _ h1
    _ = 8 ^ k * n ^ ℓ * u ^ (k - ℓ) := by rw [h8]; ring

/-- Exponential decay bound: if $\ell \ge \varepsilon^{-1} \log(2/\delta)$, then $(1 - \varepsilon)^\ell \le \delta / 2$. -/
private theorem one_sub_pow_le_half_delta {ε δ : ℝ} {ℓ : ℕ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ)
    (hℓ : (1 / ε) * Real.log (2 / δ) ≤ (ℓ : ℝ)) :
    (1 - ε) ^ ℓ ≤ δ / 2 := by
  have h1_sub_pos : 0 < 1 - ε := by linarith
  have hlog_step : Real.log (1 - ε) ≤ -ε := by
    have h := Real.log_le_sub_one_of_pos h1_sub_pos
    linarith
  have hε_ℓ : Real.log (2 / δ) ≤ (ℓ : ℝ) * ε := by
    have h1 := mul_le_mul_of_nonneg_right hℓ hε0.le
    have h2 : (1 / ε) * Real.log (2 / δ) * ε = Real.log (2 / δ) := by
      field_simp [hε0.ne']
    rwa [h2] at h1
  have hlog_pow : Real.log ((1 - ε) ^ ℓ) ≤ Real.log (δ / 2) := by
    rw [Real.log_pow]
    have h_inv : Real.log (δ / 2) = -Real.log (2 / δ) := by
      rw [← Real.log_inv, inv_div]
    rw [h_inv]
    have hℓ_nonneg : (0 : ℝ) ≤ (ℓ : ℝ) := Nat.cast_nonneg ℓ
    nlinarith
  exact (Real.log_le_log_iff (by positivity) (by positivity)).mp hlog_pow

/-- For $\varepsilon \le 2^{-32f}$ and $k \ge \varepsilon^{-2}$, the container depth $\ell = \lceil \varepsilon^{-1}\log(2/\delta)\rceil$ satisfies $2\ell \le k$. -/
private theorem two_mul_ceil_log_le_k
    {f ε δ : ℝ} {k : ℕ} (hf_ge : 2 ≤ f) (hε0 : 0 < ε) (hε_small : ε ≤ (2 : ℝ) ^ (-32 * f))
    (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (h_two_div_delta_le : 2 / δ ≤ ε ^ (-(6 * f + 3)))
    (hk_ge_r : ε ^ (-2 : ℝ) ≤ (k : ℝ)) (hk16_r : (16 : ℝ) ≤ (k : ℝ)) :
    2 * ⌈(1 / ε) * Real.log (2 / δ)⌉₊ ≤ k := by
  have hf_pos : 0 < f := by linarith
  have hε_le_64 : ε ≤ (2 : ℝ) ^ (-64 : ℝ) :=
    hε_small.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
  have hε_lt_one : ε < 1 := by
    have : (2 : ℝ) ^ (-64 : ℝ) < 1 := by norm_num
    linarith
  have h_2_div_δ_8f : 2 / δ ≤ ε ^ (-8 * f) := by
    refine h_two_div_delta_le.trans ?_
    exact Real.rpow_le_rpow_of_exponent_ge hε0 hε_lt_one.le (by linarith)
  let X := (2 / δ) ^ (1 / (16 * f))
  have hX_pos : 0 < X := by dsimp [X]; positivity
  have hX_le : X ≤ ε ^ (-1 / 2 : ℝ) := by
    calc X
      _ ≤ (ε ^ (-8 * f)) ^ (1 / (16 * f)) :=
        Real.rpow_le_rpow (by positivity) h_2_div_δ_8f (by positivity)
      _ = ε ^ (-1 / 2 : ℝ) := by
        rw [← Real.rpow_mul hε0.le]
        congr 1
        field_simp [hf_pos.ne']
        ring
  have hlog_X : Real.log X ≤ ε ^ (-1 / 2 : ℝ) := by
    have h1 := Real.log_le_sub_one_of_pos hX_pos
    linarith
  have hlog_2_δ : Real.log (2 / δ) ≤ 16 * f * ε ^ (-1 / 2 : ℝ) := by
    have h1 : Real.log X = (1 / (16 * f)) * Real.log (2 / δ) := by
      dsimp [X]
      rw [Real.log_rpow (by positivity)]
    have h2 : (1 / (16 * f)) * Real.log (2 / δ) ≤ ε ^ (-1 / 2 : ℝ) := h1 ▸ hlog_X
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 16 * f)
    have h4 : 16 * f * ((1 / (16 * f)) * Real.log (2 / δ)) = Real.log (2 / δ) := by
      field_simp [hf_pos.ne']
    rwa [h4] at h3
  have h16f_le : 16 * f ≤ (1 / 4 : ℝ) * ε ^ (-1 / 2 : ℝ) := by
    have hb := mul_rpow_neg_four_le_eighth (b := 2 * f) (by linarith)
    have h_pow_le : (2 : ℝ) ^ (16 * f) ≤ ε ^ (-1 / 2 : ℝ) := by
      have h1 : ((2 : ℝ) ^ (-32 * f)) ^ (-1 / 2 : ℝ) ≤ ε ^ (-1 / 2 : ℝ) := by
        have h_eq1 : ((2 : ℝ) ^ (-32 * f)) ^ (-1 / 2 : ℝ) = (((2 : ℝ) ^ (-32 * f)) ^ (1 / 2 : ℝ))⁻¹ := by
          rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring,
            Real.rpow_neg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (-32 * f))]
        have h_eq2 : ε ^ (-1 / 2 : ℝ) = (ε ^ (1 / 2 : ℝ))⁻¹ := by
          rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hε0.le]
        rw [h_eq1, h_eq2]
        exact inv_anti₀ (by positivity) (Real.rpow_le_rpow hε0.le hε_small (by positivity))
      have h2 : ((2 : ℝ) ^ (-32 * f)) ^ (-1 / 2 : ℝ) = (2 : ℝ) ^ (16 * f) := by
        rw [← Real.rpow_mul two_pos.le]
        congr 1; ring
      linarith
    have h_prod : (2 * f) * (2 : ℝ) ^ (-8 * f) ≤ 1 / 8 := by
      convert hb using 2
      ring
    have h_mul := mul_le_mul_of_nonneg_right h_prod (by positivity : (0 : ℝ) ≤ 8 * (2 : ℝ) ^ (8 * f))
    have h_cancel : (2 * f) * (2 : ℝ) ^ (-8 * f) * (8 * (2 : ℝ) ^ (8 * f)) = 16 * f := by
      have : (2 : ℝ) ^ (-8 * f) * (2 : ℝ) ^ (8 * f) = 1 := by
        rw [← Real.rpow_add two_pos]
        have h0 : -8 * f + 8 * f = 0 := by ring
        rw [h0, Real.rpow_zero]
      calc (2 * f) * (2 : ℝ) ^ (-8 * f) * (8 * (2 : ℝ) ^ (8 * f))
        _ = 16 * f * ((2 : ℝ) ^ (-8 * f) * (2 : ℝ) ^ (8 * f)) := by ring
        _ = 16 * f := by rw [this, mul_one]
    have h_rhs : (1 / 8 : ℝ) * (8 * (2 : ℝ) ^ (8 * f)) = (2 : ℝ) ^ (8 * f) := by ring
    rw [h_cancel, h_rhs] at h_mul
    have h4_le_8f : (4 : ℝ) ≤ (2 : ℝ) ^ (8 * f) := by
      calc (4 : ℝ)
        _ = (2 : ℝ) ^ (2 : ℝ) := by norm_num
        _ ≤ (2 : ℝ) ^ (8 * f) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h64f : 64 * f ≤ (2 : ℝ) ^ (16 * f) := by
      have h_split : (2 : ℝ) ^ (8 * f) * (2 : ℝ) ^ (8 * f) = (2 : ℝ) ^ (16 * f) := by
        rw [← Real.rpow_add two_pos]
        congr 1; ring
      nlinarith
    linarith
  have hlog_div_eps : (1 / ε) * Real.log (2 / δ) ≤ (1 / 4 : ℝ) * ε ^ (-2 : ℝ) := by
    have h1 : Real.log (2 / δ) ≤ (1 / 4 : ℝ) * ε ^ (-1 : ℝ) := by
      have h_prod : ε ^ (-1 / 2 : ℝ) * ε ^ (-1 / 2 : ℝ) = ε ^ (-1 : ℝ) := by
        rw [← Real.rpow_add hε0]
        norm_num
      calc Real.log (2 / δ)
        _ ≤ 16 * f * ε ^ (-1 / 2 : ℝ) := hlog_2_δ
        _ ≤ ((1 / 4 : ℝ) * ε ^ (-1 / 2 : ℝ)) * ε ^ (-1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right h16f_le (by positivity)
        _ = (1 / 4 : ℝ) * (ε ^ (-1 / 2 : ℝ) * ε ^ (-1 / 2 : ℝ)) := by ring
        _ = (1 / 4 : ℝ) * ε ^ (-1 : ℝ) := by rw [h_prod]
    calc (1 / ε) * Real.log (2 / δ)
      _ = ε ^ (-1 : ℝ) * Real.log (2 / δ) := by rw [Real.rpow_neg_one, one_div]
      _ ≤ ε ^ (-1 : ℝ) * ((1 / 4 : ℝ) * ε ^ (-1 : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (1 / 4 : ℝ) * (ε ^ (-1 : ℝ) * ε ^ (-1 : ℝ)) := by ring
      _ = (1 / 4 : ℝ) * ε ^ (-2 : ℝ) := by
        rw [← Real.rpow_add hε0]
        norm_num
  let ℓ := ⌈(1 / ε) * Real.log (2 / δ)⌉₊
  have hℓ_lt : (ℓ : ℝ) < (1 / 4 : ℝ) * ε ^ (-2 : ℝ) + 1 := by
    have h_nonneg : 0 ≤ (1 / ε) * Real.log (2 / δ) := by
      have : 1 ≤ 2 / δ := (one_le_div hδ_pos).mpr (by linarith)
      have : 0 ≤ Real.log (2 / δ) := Real.log_nonneg this
      positivity
    exact (Nat.ceil_lt_add_one h_nonneg).trans_le (by linarith)
  have h2ℓ_r : 2 * (ℓ : ℝ) < (k : ℝ) + 1 := by linarith
  have h2ℓ_nat : 2 * ℓ < k + 1 := by exact_mod_cast h2ℓ_r
  omega

/--
Core Kleitman–Winston container vs. sampling contradiction (`main.tex`, lines 161–165):
Combining the container upper bound $\binom{n}{\ell}\binom{u}{k-\ell}$ (`kleitman_winston_container_bound`)
with the sampling lower bound $\frac{1}{4}(n/(2t))^k$ (`random_sampling_homog_sets_lower_bound`)
at $\delta = \frac{k^2}{4096 t^2}$ forces $k \le 32 \delta^{1/2} t = k/2$, contradicting $k \ge 16$.
-/
private theorem kw_contradiction_of_dense_and_lb
    {V : Type*} [Fintype V] [DecidableEq V] (G_star : SimpleGraph V)
    {u k t ℓ : ℕ} {ε δ : ℝ}
    (hk16 : 16 ≤ k) (ht_pos : 1 ≤ t) (h2tn : 2 * t ≤ Fintype.card V)
    (hε0 : 0 < ε) (hε1 : ε < 1)
    (hδ_def : δ = (k : ℝ) ^ 2 / (4096 * (t : ℝ) ^ 2))
    (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hu_le_delta_n : (u : ℝ) ≤ δ * (Fintype.card V : ℝ))
    (h_1_sub_pow : (1 - ε) ^ ℓ * (Fintype.card V : ℝ) ≤ (u : ℝ))
    (h2ℓ_le_k : 2 * ℓ ≤ k)
    (h_dense : ∀ S : Finset V, u < S.card → ¬IsEpsSparseOn G_star S ε)
    (h_lb : (Fintype.card V : ℝ) ^ k ≤
      4 * ((indepSetsOfCard G_star Finset.univ k).card : ℝ) * (2 * (t : ℝ)) ^ k) :
    False := by
  let n := Fintype.card V
  have hℓk : ℓ ≤ k := by omega
  have hk16_r : (16 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk16
  have ht_pos_r : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht_pos
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have h_ub_nat := kleitman_winston_container_bound G_star u ε hε0 hε1.le
    (n + ℓ) Finset.univ k ℓ (by simp [n]) (fun S _ => h_dense S) hℓk (by simpa [n] using h_1_sub_pow)
  rw [card_univ] at h_ub_nat
  have h_ub_pow_nat := (Nat.mul_le_mul_right (k ^ k) h_ub_nat).trans
    (choose_mul_choose_mul_pow_self_le n u k ℓ hℓk)
  have h_ub_pow_r : ((indepSetsOfCard G_star Finset.univ k).card : ℝ) * (k : ℝ) ^ k ≤
      8 ^ k * (n : ℝ) ^ ℓ * (u : ℝ) ^ (k - ℓ) := by exact_mod_cast h_ub_pow_nat
  have h_u_pow : (u : ℝ) ^ (k - ℓ) ≤ δ ^ (k - ℓ) * (n : ℝ) ^ (k - ℓ) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg u) hu_le_delta_n (k - ℓ)
  have h_n_split : (n : ℝ) ^ ℓ * (n : ℝ) ^ (k - ℓ) = (n : ℝ) ^ k := by
    rw [← pow_add, Nat.add_sub_of_le hℓk]
  have h_δ_pow : δ ^ (k - ℓ) ≤ (δ ^ (1 / 2 : ℝ)) ^ k := by
    rw [← Real.rpow_natCast δ (k - ℓ), ← Real.rpow_natCast (δ ^ (1 / 2 : ℝ)) k,
      ← Real.rpow_mul hδ_pos.le]
    refine Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_le_one ?_
    have : 2 * (ℓ : ℝ) ≤ (k : ℝ) := by exact_mod_cast h2ℓ_le_k
    have hsub : ((k - ℓ : ℕ) : ℝ) = (k : ℝ) - (ℓ : ℝ) := Nat.cast_sub hℓk
    rw [hsub]
    linarith
  have h_ub_clean : ((indepSetsOfCard G_star Finset.univ k).card : ℝ) * (k : ℝ) ^ k ≤
      (8 * δ ^ (1 / 2 : ℝ) * (n : ℝ)) ^ k := by
    calc ((indepSetsOfCard G_star Finset.univ k).card : ℝ) * (k : ℝ) ^ k
      _ ≤ 8 ^ k * (n : ℝ) ^ ℓ * (u : ℝ) ^ (k - ℓ) := h_ub_pow_r
      _ ≤ 8 ^ k * (n : ℝ) ^ ℓ * (δ ^ (k - ℓ) * (n : ℝ) ^ (k - ℓ)) :=
        mul_le_mul_of_nonneg_left h_u_pow (by positivity)
      _ = 8 ^ k * δ ^ (k - ℓ) * ((n : ℝ) ^ ℓ * (n : ℝ) ^ (k - ℓ)) := by ring
      _ = 8 ^ k * δ ^ (k - ℓ) * (n : ℝ) ^ k := by rw [h_n_split]
      _ ≤ 8 ^ k * (δ ^ (1 / 2 : ℝ)) ^ k * (n : ℝ) ^ k :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h_δ_pow (by positivity)) (by positivity)
      _ = (8 * δ ^ (1 / 2 : ℝ) * (n : ℝ)) ^ k := by rw [mul_pow, mul_pow]
  have h_lb_clean : ((n : ℝ) * (k : ℝ)) ^ k ≤
      (32 * δ ^ (1 / 2 : ℝ) * (t : ℝ) * (n : ℝ)) ^ k := by
    have h4_le_2k : (4 : ℝ) ≤ 2 ^ k := by
      have : 2 ≤ k := by omega
      calc (4 : ℝ)
        _ = (2 : ℝ) ^ 2 := by norm_num
        _ ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) this
    calc ((n : ℝ) * (k : ℝ)) ^ k
      _ = (n : ℝ) ^ k * (k : ℝ) ^ k := mul_pow _ _ _
      _ ≤ (4 * ((indepSetsOfCard G_star Finset.univ k).card : ℝ) * (2 * (t : ℝ)) ^ k) *
            (k : ℝ) ^ k :=
        mul_le_mul_of_nonneg_right h_lb (by positivity)
      _ ≤ (2 ^ k * ((indepSetsOfCard G_star Finset.univ k).card : ℝ) * (2 * (t : ℝ)) ^ k) *
            (k : ℝ) ^ k := by
        have : 0 ≤ ((indepSetsOfCard G_star Finset.univ k).card : ℝ) *
            (2 * (t : ℝ)) ^ k * (k : ℝ) ^ k := by positivity
        nlinarith
      _ = (4 * (t : ℝ)) ^ k * (((indepSetsOfCard G_star Finset.univ k).card : ℝ) * (k : ℝ) ^ k) := by
        rw [show (4 * (t : ℝ)) ^ k = 2 ^ k * (2 * (t : ℝ)) ^ k by
          rw [← mul_pow]; congr 1; ring]
        ring
      _ ≤ (4 * (t : ℝ)) ^ k * (8 * δ ^ (1 / 2 : ℝ) * (n : ℝ)) ^ k :=
        mul_le_mul_of_nonneg_left h_ub_clean (by positivity)
      _ = (32 * δ ^ (1 / 2 : ℝ) * (t : ℝ) * (n : ℝ)) ^ k := by
        rw [← mul_pow]
        congr 1; ring
  have h_base_le : (n : ℝ) * (k : ℝ) ≤ 32 * δ ^ (1 / 2 : ℝ) * (t : ℝ) * (n : ℝ) :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by omega : k ≠ 0)).mp h_lb_clean
  have hk_le_32 : (k : ℝ) ≤ 32 * δ ^ (1 / 2 : ℝ) * (t : ℝ) :=
    le_of_mul_le_mul_right (by linarith) hn_pos
  have hk2_le : (k : ℝ) ^ 2 ≤ (32 * δ ^ (1 / 2 : ℝ) * (t : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hk_le_32 2
  have h_rhs_sq : (32 * δ ^ (1 / 2 : ℝ) * (t : ℝ)) ^ 2 = (1 / 4 : ℝ) * (k : ℝ) ^ 2 := by
    have h_δ_sq : (δ ^ (1 / 2 : ℝ)) ^ 2 = δ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hδ_pos.le]
      norm_num
    calc (32 * δ ^ (1 / 2 : ℝ) * (t : ℝ)) ^ 2
      _ = 1024 * (δ ^ (1 / 2 : ℝ)) ^ 2 * (t : ℝ) ^ 2 := by ring
      _ = 1024 * δ * (t : ℝ) ^ 2 := by rw [h_δ_sq]
      _ = (1 / 4 : ℝ) * (k : ℝ) ^ 2 := by
        rw [hδ_def]
        field_simp [ht_pos_r.ne']
        ring
  rw [h_rhs_sq] at hk2_le
  nlinarith

/--
Small-$\varepsilon$ Kleitman–Winston viral deduction (`0 < ε ≤ 2^(-32 f)`):
with $d_0 = 6 f + 6$, if $\operatorname{ind}_{H_i}(G) \le (\varepsilon^{d_0} |G|)^{|H_i|}$ for $i = 1, 2$,
then $G$ contains an $\varepsilon$-restricted subset $S \subseteq V(G)$ with $|S| \ge \varepsilon^{d_0} |G|$.
-/
private theorem isPairViral_small_eps
    {W₁ W₂ : Type*} {V : Type} [Fintype W₁] [DecidableEq W₁] [Nonempty W₁]
    [Fintype W₂] [DecidableEq W₂] [Nonempty W₂] [Fintype V] [DecidableEq V]
    (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂) (G : SimpleGraph V)
    {c f ε : ℝ} (hc_pos : 0 < c) (hf_def : f = 1 / c) (hf_ge : 2 ≤ f)
    (h_eh : ∀ (U_type : Type) [Fintype U_type] [DecidableEq U_type] (J : SimpleGraph U_type),
      IsInducedSubgraphFree J H₁ → IsInducedSubgraphFree J H₂ →
      (Fintype.card U_type : ℝ) ^ c ≤ (kappa J : ℝ))
    (hε0 : 0 < ε) (hε_small : ε ≤ (2 : ℝ) ^ (-32 * f))
    (hc₁ : (indCopyCount H₁ G : ℝ) ≤ (ε ^ (6 * f + 6) * (Fintype.card V : ℝ)) ^ (Fintype.card W₁))
    (hc₂ : (indCopyCount H₂ G : ℝ) ≤ (ε ^ (6 * f + 6) * (Fintype.card V : ℝ)) ^ (Fintype.card W₂)) :
    ∃ S : Finset V, IsEpsRestrictedOn G S ε ∧
      ε ^ (6 * f + 6) * (Fintype.card V : ℝ) ≤ (S.card : ℝ) := by
  classical
  let d₀ := 6 * f + 6
  let n := Fintype.card V
  have hf_pos : 0 < f := by linarith
  have hε_le_64 : ε ≤ (2 : ℝ) ^ (-64 : ℝ) :=
    hε_small.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
  have hε_lt_one : ε < 1 := by
    have : (2 : ℝ) ^ (-64 : ℝ) < 1 := by norm_num
    linarith
  have hε_inv_ge : (2 : ℝ) ^ (64 : ℝ) ≤ ε ^ (-1 : ℝ) := by
    have h_eq1 : (2 : ℝ) ^ (64 : ℝ) = ((2 : ℝ) ^ (-64 : ℝ))⁻¹ := by
      rw [show (-64 : ℝ) = -(64 : ℝ) by ring, Real.rpow_neg two_pos.le, inv_inv]
    rw [Real.rpow_neg_one, h_eq1]
    exact inv_anti₀ hε0 hε_le_64
  have hε_inv_ge_8192 : (8192 : ℝ) ≤ ε ^ (-1 : ℝ) := by
    have : (8192 : ℝ) ≤ (2 : ℝ) ^ (64 : ℝ) := by norm_num
    linarith
  let k : ℕ := ⌈ε ^ (-2 : ℝ)⌉₊
  have hk_ge_r : ε ^ (-2 : ℝ) ≤ (k : ℝ) := Nat.le_ceil _
  have hk16_r : (16 : ℝ) ≤ (k : ℝ) := by
    have h1 : (16 : ℝ) ≤ (ε ^ (-1 : ℝ)) * (ε ^ (-1 : ℝ)) := by nlinarith
    have h2 : (ε ^ (-1 : ℝ)) * (ε ^ (-1 : ℝ)) = ε ^ (-2 : ℝ) := by
      rw [← Real.rpow_add hε0]
      norm_num
    linarith
  have hk16 : 16 ≤ k := by exact_mod_cast hk16_r
  have hk_pos : 1 ≤ k := by omega
  have hk_pos_r : (0 : ℝ) < (k : ℝ) := by positivity
  have hk_le_r : (k : ℝ) ≤ 2 * ε ^ (-2 : ℝ) := by
    have hlt := Nat.ceil_lt_add_one (by positivity : 0 ≤ ε ^ (-2 : ℝ))
    linarith
  have hk_le_eps3 : (k : ℝ) ≤ ε ^ (-3 : ℝ) := by
    have h2_le : (2 : ℝ) ≤ ε ^ (-1 : ℝ) := by linarith
    have h_eq : ε ^ (-1 : ℝ) * ε ^ (-2 : ℝ) = ε ^ (-3 : ℝ) := by
      rw [← Real.rpow_add hε0]
      norm_num
    nlinarith [Real.rpow_pos_of_pos hε0 (-2 : ℝ)]
  let t : ℕ := ⌈(k : ℝ) ^ f⌉₊
  have ht_ge_r : (k : ℝ) ^ f ≤ (t : ℝ) := Nat.le_ceil _
  have hkt_r : (k : ℝ) ≤ (t : ℝ) := by
    have h1 : (k : ℝ) ^ (1 : ℝ) ≤ (k : ℝ) ^ f :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    rw [Real.rpow_one] at h1
    exact h1.trans ht_ge_r
  have hkt : k ≤ t := by exact_mod_cast hkt_r
  have ht_pos : 1 ≤ t := hk_pos.trans hkt
  have ht_pos_r : (0 : ℝ) < (t : ℝ) := by positivity
  have ht_le_r : (t : ℝ) ≤ 2 * (k : ℝ) ^ f := by
    have h1 : (1 : ℝ) ≤ (k : ℝ) ^ f := Real.one_le_rpow (by linarith) hf_pos.le
    have hlt := Nat.ceil_lt_add_one (by positivity : 0 ≤ (k : ℝ) ^ f)
    linarith
  have ht_le_eps : (t : ℝ) ≤ ε ^ (-(3 * f + 1)) := by
    have h1 : (k : ℝ) ^ f ≤ (ε ^ (-3 : ℝ)) ^ f :=
      Real.rpow_le_rpow (by positivity) hk_le_eps3 hf_pos.le
    have h2 : (ε ^ (-3 : ℝ)) ^ f = ε ^ (-3 * f) := by
      rw [← Real.rpow_mul hε0.le]
    have h2_le : (2 : ℝ) ≤ ε ^ (-1 : ℝ) := by linarith
    calc (t : ℝ)
      _ ≤ 2 * (k : ℝ) ^ f := ht_le_r
      _ ≤ ε ^ (-1 : ℝ) * ε ^ (-3 * f) := by
        rw [← h2]
        exact mul_le_mul h2_le h1 (by positivity) (by positivity)
      _ = ε ^ (-(3 * f + 1)) := by
        rw [← Real.rpow_add hε0]
        congr 1; ring
  let δ : ℝ := (k : ℝ) ^ 2 / (4096 * (t : ℝ) ^ 2)
  have hδ_pos : 0 < δ := by dsimp [δ]; positivity
  have hδ_le_one : δ ≤ 1 := by
    dsimp [δ]
    rw [div_le_one (by positivity)]
    have : (k : ℝ) ^ 2 ≤ (t : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hkt_r 2
    nlinarith
  have h_two_div_delta_le : 2 / δ ≤ ε ^ (-(6 * f + 3)) := by
    have h1 : 2 / δ = 8192 * (t : ℝ) ^ 2 / (k : ℝ) ^ 2 := by
      dsimp [δ]
      field_simp [hk_pos_r.ne', ht_pos_r.ne']
      ring
    have h2 : 8192 * (t : ℝ) ^ 2 / (k : ℝ) ^ 2 ≤ 8192 * (t : ℝ) ^ 2 := by
      have hk2_ge_one : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
      exact div_le_self (by positivity) hk2_ge_one
    have h3 : (t : ℝ) ^ 2 ≤ ε ^ (-(6 * f + 2)) := by
      calc (t : ℝ) ^ 2
        _ ≤ (ε ^ (-(3 * f + 1))) ^ 2 := pow_le_pow_left₀ (by positivity) ht_le_eps 2
        _ = ε ^ (-(6 * f + 2)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hε0.le]
          congr 1; push_cast; ring
    calc 2 / δ
      _ ≤ 8192 * (t : ℝ) ^ 2 := h1.trans_le h2
      _ ≤ ε ^ (-1 : ℝ) * ε ^ (-(6 * f + 2)) :=
        mul_le_mul hε_inv_ge_8192 h3 (by positivity) (by positivity)
      _ = ε ^ (-(6 * f + 3)) := by
        rw [← Real.rpow_add hε0]
        congr 1; ring
  have h_eps_d0_le_half_delta : ε ^ d₀ ≤ δ / 2 := by
    have h1 : ε ^ d₀ ≤ ε ^ (6 * f + 3) :=
      Real.rpow_le_rpow_of_exponent_ge hε0 hε_lt_one.le (by dsimp [d₀]; linarith)
    have h2 : ε ^ (6 * f + 3) ≤ δ / 2 := by
      have h_eq : ε ^ (6 * f + 3) = (ε ^ (-(6 * f + 3)))⁻¹ := by
        rw [Real.rpow_neg hε0.le, inv_inv]
      have h_inv : (2 / δ)⁻¹ = δ / 2 := inv_div 2 δ
      rw [h_eq, ← h_inv]
      exact inv_anti₀ (by positivity) h_two_div_delta_le
    exact h1.trans h2
  have h_eps_d0_le_8t : ε ^ d₀ ≤ 1 / (8 * (t : ℝ)) := by
    have h1 : 8 * (t : ℝ) ≤ ε ^ (-(3 * f + 2)) := by
      have h8 : (8 : ℝ) ≤ ε ^ (-1 : ℝ) := by linarith
      calc 8 * (t : ℝ)
        _ ≤ ε ^ (-1 : ℝ) * ε ^ (-(3 * f + 1)) :=
          mul_le_mul h8 ht_le_eps (by positivity) (by positivity)
        _ = ε ^ (-(3 * f + 2)) := by
          rw [← Real.rpow_add hε0]
          congr 1; ring
    have h2 : ε ^ d₀ ≤ ε ^ (3 * f + 2) :=
      Real.rpow_le_rpow_of_exponent_ge hε0 hε_lt_one.le (by dsimp [d₀]; linarith)
    have h3 : ε ^ (3 * f + 2) ≤ 1 / (8 * (t : ℝ)) := by
      have h_eq : ε ^ (3 * f + 2) = (ε ^ (-(3 * f + 2)))⁻¹ := by
        rw [Real.rpow_neg hε0.le, inv_inv]
      rw [h_eq, one_div]
      exact inv_anti₀ (by positivity) h1
    exact h2.trans h3
  by_cases h_small_n : ε ^ d₀ * (n : ℝ) ≤ 1
  · rcases eq_or_ne n 0 with hn0 | hn0
    · refine ⟨∅, Or.inl (fun u hu => (notMem_empty u hu).elim), ?_⟩
      change ε ^ d₀ * (n : ℝ) ≤ (∅ : Finset V).card
      simp [hn0]
    · haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
      obtain ⟨v⟩ := ‹Nonempty V›
      refine ⟨{v}, Or.inl ?_, ?_⟩
      · intro u hu
        rw [mem_singleton] at hu
        subst hu
        have hemp : neighborFinsetIn G u {u} = ∅ := by
          rw [eq_empty_iff_forall_notMem]
          intro w hw
          rw [mem_neighborFinsetIn_iff, mem_singleton] at hw
          exact G.loopless u (hw.1 ▸ hw.2)
        rw [hemp]
        simp [hε0.le]
      · rw [card_singleton, Nat.cast_one]
        exact h_small_n
  · push_neg at h_small_n
    by_contra h_no_rest
    push_neg at h_no_rest
    have h_8t_lt_n : 8 * (t : ℝ) < (n : ℝ) := by
      have h1 : 1 < (1 / (8 * (t : ℝ))) * (n : ℝ) :=
        h_small_n.trans_le (mul_le_mul_of_nonneg_right h_eps_d0_le_8t (Nat.cast_nonneg n))
      rwa [one_div_mul_eq_div, one_lt_div (by positivity)] at h1
    have h2tn : 2 * t ≤ n := by
      have : ((2 * t : ℕ) : ℝ) ≤ (n : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have h_2_lt_delta_n : 2 < δ * (n : ℝ) := by
      have h1 : 1 < (δ / 2) * (n : ℝ) :=
        h_small_n.trans_le (mul_le_mul_of_nonneg_right h_eps_d0_le_half_delta (Nat.cast_nonneg n))
      linarith
    let u : ℕ := ⌊δ * (n : ℝ)⌋₊
    have hu_le_delta_n : (u : ℝ) ≤ δ * (n : ℝ) := Nat.floor_le (by positivity)
    have hu_ge_half_delta_n : (δ / 2) * (n : ℝ) ≤ (u : ℝ) := by
      have hlt := Nat.sub_one_lt_floor (δ * (n : ℝ))
      linarith
    have h_dense_G : ∀ S : Finset V, u < S.card → ¬IsEpsSparseOn G S ε := by
      intro S hSu hsparse
      have hS_gt : δ * (n : ℝ) < (S.card : ℝ) := by
        have h1 : (u : ℝ) + 1 ≤ (S.card : ℝ) := by exact_mod_cast hSu
        have hlt := Nat.lt_floor_add_one (δ * (n : ℝ))
        linarith
      have hS_ge_d0 : ε ^ d₀ * (n : ℝ) ≤ (S.card : ℝ) := by
        have : ε ^ d₀ * (n : ℝ) ≤ δ * (n : ℝ) := by
          have : ε ^ d₀ ≤ δ := by linarith [h_eps_d0_le_half_delta, hδ_pos]
          exact mul_le_mul_of_nonneg_right this (Nat.cast_nonneg n)
        linarith
      linarith [h_no_rest S (Or.inl hsparse), hS_ge_d0]
    have h_dense_Gc : ∀ S : Finset V, u < S.card → ¬IsEpsSparseOn Gᶜ S ε := by
      intro S hSu hsparse
      have hS_gt : δ * (n : ℝ) < (S.card : ℝ) := by
        have h1 : (u : ℝ) + 1 ≤ (S.card : ℝ) := by exact_mod_cast hSu
        have hlt := Nat.lt_floor_add_one (δ * (n : ℝ))
        linarith
      have hS_ge_d0 : ε ^ d₀ * (n : ℝ) ≤ (S.card : ℝ) := by
        have : ε ^ d₀ * (n : ℝ) ≤ δ * (n : ℝ) := by
          have : ε ^ d₀ ≤ δ := by linarith [h_eps_d0_le_half_delta, hδ_pos]
          exact mul_le_mul_of_nonneg_right this (Nat.cast_nonneg n)
        linarith
      linarith [h_no_rest S (Or.inr hsparse), hS_ge_d0]
    let ℓ : ℕ := ⌈(1 / ε) * Real.log (2 / δ)⌉₊
    have hℓ_ge : (1 / ε) * Real.log (2 / δ) ≤ (ℓ : ℝ) := Nat.le_ceil _
    have h_1_sub_pow : (1 - ε) ^ ℓ * (n : ℝ) ≤ (u : ℝ) := by
      have h1 := one_sub_pow_le_half_delta hε0 hε_lt_one hδ_pos hℓ_ge
      calc (1 - ε) ^ ℓ * (n : ℝ)
        _ ≤ (δ / 2) * (n : ℝ) := mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg n)
        _ ≤ (u : ℝ) := hu_ge_half_delta_n
    have h2ℓ_le_k : 2 * ℓ ≤ k :=
      two_mul_ceil_log_le_k hf_ge hε0 hε_small hδ_pos hδ_le_one h_two_div_delta_le hk_ge_r hk16_r
    have h_eh_t : ∀ U : Finset V, t ≤ U.card →
        IsInducedSubgraphFree (G.induce (U : Set V)) H₁ →
        IsInducedSubgraphFree (G.induce (U : Set V)) H₂ →
        (k : ℝ) ≤ (kappa (G.induce (U : Set V)) : ℝ) := by
      intro U hUt hU₁ hU₂
      have h_card : Fintype.card ↥(U : Set V) = U.card := Fintype.card_coe U
      have h_eh_U := h_eh ↥(U : Set V) (G.induce (U : Set V)) hU₁ hU₂
      rw [h_card] at h_eh_U
      have hUt_r : (t : ℝ) ≤ (U.card : ℝ) := by exact_mod_cast hUt
      have hk_le_Uc : (k : ℝ) ≤ (U.card : ℝ) ^ c := by
        have h1 : (k : ℝ) = ((k : ℝ) ^ f) ^ c := by
          rw [← Real.rpow_mul hk_pos_r.le, hf_def, one_div_mul_cancel hc_pos.ne', Real.rpow_one]
        rw [h1]
        exact Real.rpow_le_rpow (by positivity) (ht_ge_r.trans hUt_r) hc_pos.le
      exact hk_le_Uc.trans h_eh_U
    have hc₁_step2 : (indCopyCount H₁ G : ℝ) ≤ ((n : ℝ) / (8 * (t : ℝ))) ^ (Fintype.card W₁) := by
      refine hc₁.trans (pow_le_pow_left₀ (by positivity) ?_ _)
      calc ε ^ d₀ * (n : ℝ)
        _ ≤ (1 / (8 * (t : ℝ))) * (n : ℝ) :=
          mul_le_mul_of_nonneg_right h_eps_d0_le_8t (Nat.cast_nonneg n)
        _ = (n : ℝ) / (8 * (t : ℝ)) := one_div_mul_eq_div _ _
    have hc₂_step2 : (indCopyCount H₂ G : ℝ) ≤ ((n : ℝ) / (8 * (t : ℝ))) ^ (Fintype.card W₂) := by
      refine hc₂.trans (pow_le_pow_left₀ (by positivity) ?_ _)
      calc ε ^ d₀ * (n : ℝ)
        _ ≤ (1 / (8 * (t : ℝ))) * (n : ℝ) :=
          mul_le_mul_of_nonneg_right h_eps_d0_le_8t (Nat.cast_nonneg n)
        _ = (n : ℝ) / (8 * (t : ℝ)) := one_div_mul_eq_div _ _
    rcases random_sampling_homog_sets_lower_bound H₁ H₂ G k t hk_pos hkt h2tn
        h_eh_t hc₁_step2 hc₂_step2 with hG | hGc
    · exact kw_contradiction_of_dense_and_lb G hk16 ht_pos h2tn hε0 hε_lt_one rfl
        hδ_pos hδ_le_one hu_le_delta_n h_1_sub_pow h2ℓ_le_k h_dense_G hG
    · exact kw_contradiction_of_dense_and_lb Gᶜ hk16 ht_pos h2tn hε0 hε_lt_one rfl
        hδ_pos hδ_le_one hu_le_delta_n h_1_sub_pow h2ℓ_le_k h_dense_Gc hGc

/--
**Theorem 3 (`(1) → (3)` for Pairs, `isPairViral_of_hasPairErdosHajnalProp`)**:
Every two-graph family $\{H_1, H_2\}$ (with non-empty vertex sets) satisfying the Erdős–Hajnal
property is viral (`IsPairViral H₁ H₂`).
-/
theorem isPairViral_of_hasPairErdosHajnalProp
    {W₁ W₂ : Type*} [Fintype W₁] [DecidableEq W₁] [Nonempty W₁]
    [Fintype W₂] [DecidableEq W₂] [Nonempty W₂]
    {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂}
    (h : HasPairErdosHajnalProp H₁ H₂) : IsPairViral H₁ H₂ := by
  obtain ⟨c₀, hc₀, h_eh₀⟩ := h
  let c : ℝ := min c₀ (1 / 2)
  have hc_pos : 0 < c := lt_min hc₀ (by norm_num)
  have hc_le_c₀ : c ≤ c₀ := min_le_left _ _
  have hc_le_half : c ≤ 1 / 2 := min_le_right _ _
  let f : ℝ := 1 / c
  have hf_ge : 2 ≤ f := by
    dsimp [f]
    rw [le_one_div (by norm_num) hc_pos]
    exact hc_le_half
  have h_eh : ∀ (U_type : Type) [Fintype U_type] [DecidableEq U_type] (J : SimpleGraph U_type),
      IsInducedSubgraphFree J H₁ → IsInducedSubgraphFree J H₂ →
      (Fintype.card U_type : ℝ) ^ c ≤ (kappa J : ℝ) := by
    intro U_type _ _ J hJ₁ hJ₂
    rcases eq_or_ne (Fintype.card U_type) 0 with h0 | h0
    · rw [h0, Nat.cast_zero, Real.zero_rpow hc_pos.ne']
      exact Nat.cast_nonneg _
    · have h1 : (1 : ℝ) ≤ (Fintype.card U_type : ℝ) := by
        have : 1 ≤ Fintype.card U_type := by omega
        exact_mod_cast this
      exact (Real.rpow_le_rpow_of_exponent_le h1 hc_le_c₀).trans (h_eh₀ U_type J hJ₁ hJ₂)
  let d₀ : ℝ := 6 * f + 6
  let d : ℝ := (32 * f + 1) * d₀
  have hd_pos : 0 < d := by dsimp [d, d₀]; positivity
  refine ⟨d, hd_pos, fun V _ _ G ε hε0 hε1 hc₁ hc₂ => ?_⟩
  let ε₀ : ℝ := (2 : ℝ) ^ (-32 * f)
  let ε' : ℝ := ε₀ * ε
  have hε'_pos : 0 < ε' := by dsimp [ε', ε₀]; positivity
  have hε'_small : ε' ≤ ε₀ := by
    dsimp [ε']
    have : ε ≤ 1 := by linarith
    exact mul_le_of_le_one_right (by dsimp [ε₀]; positivity) this
  have hε'_le_ε : ε' ≤ ε := by
    dsimp [ε', ε₀]
    have h1 : (2 : ℝ) ^ (-32 * f) ≤ (2 : ℝ) ^ (0 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    rw [Real.rpow_zero] at h1
    nlinarith
  have hε_d_le : ε ^ d ≤ ε' ^ d₀ := by
    have h1 : ε ^ (32 * f + 1) ≤ ε' := by
      dsimp [ε', ε₀]
      rw [Real.rpow_add_one hε0.ne']
      have h2 : ε ^ (32 * f) ≤ (1 / 2 : ℝ) ^ (32 * f) :=
        Real.rpow_le_rpow hε0.le hε1.le (by positivity)
      have h3 : (1 / 2 : ℝ) ^ (32 * f) = (2 : ℝ) ^ (-32 * f) := by
        rw [one_div, Real.inv_rpow two_pos.le, ← Real.rpow_neg two_pos.le, neg_mul]
      rw [← h3]
      exact mul_le_mul_of_nonneg_right h2 hε0.le
    dsimp [d]
    rw [Real.rpow_mul hε0.le]
    exact Real.rpow_le_rpow (by positivity) h1 (by dsimp [d₀]; positivity)
  have hc₁' : (indCopyCount H₁ G : ℝ) ≤ (ε' ^ d₀ * (Fintype.card V : ℝ)) ^ (Fintype.card W₁) :=
    hc₁.trans (pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_right hε_d_le (Nat.cast_nonneg _)) _)
  have hc₂' : (indCopyCount H₂ G : ℝ) ≤ (ε' ^ d₀ * (Fintype.card V : ℝ)) ^ (Fintype.card W₂) :=
    hc₂.trans (pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_right hε_d_le (Nat.cast_nonneg _)) _)
  obtain ⟨S, hS_rest, hS_card⟩ :=
    isPairViral_small_eps H₁ H₂ G hc_pos rfl hf_ge h_eh hε'_pos hε'_small hc₁' hc₂'
  refine ⟨S, hS_rest.mono hε'_le_ε, ?_⟩
  exact (mul_le_mul_of_nonneg_right hε_d_le (Nat.cast_nonneg _)).trans hS_card

/--
**Theorem 3 (`(1) → (3)` for Single Graphs, `isViral_of_hasErdosHajnalProp`)**:
Every finite graph $H$ (with non-empty vertex set) satisfying the Erdős–Hajnal property is viral.
-/
theorem isViral_of_hasErdosHajnalProp
    {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    {H : SimpleGraph W} (h : HasErdosHajnalProp H) : IsViral H := by
  rw [← isPairViral_self_iff]
  exact isPairViral_of_hasPairErdosHajnalProp ((hasPairErdosHajnalProp_self_iff H).mpr h)

/--
**Theorem 3 (`pair_eh_iff_pairPolyRodl_iff_isPairViral`, Two-Graph Equivalence)**:
For any two finite graphs $H_1, H_2$ on non-empty vertex types $W_1, W_2$:
`(1) HasPairErdosHajnalProp H₁ H₂ ↔ (2) HasPairPolyRodlProp H₁ H₂` and
`(2) HasPairPolyRodlProp H₁ H₂ ↔ (3) IsPairViral H₁ H₂`.
-/
theorem pair_eh_iff_pairPolyRodl_iff_isPairViral
    {W₁ W₂ : Type*} [Fintype W₁] [DecidableEq W₁] [Nonempty W₁]
    [Fintype W₂] [DecidableEq W₂] [Nonempty W₂]
    (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂) :
    (HasPairErdosHajnalProp H₁ H₂ ↔ HasPairPolyRodlProp H₁ H₂) ∧
    (HasPairPolyRodlProp H₁ H₂ ↔ IsPairViral H₁ H₂) := by
  refine ⟨⟨fun h => hasPairPolyRodlProp_of_isPairViral (isPairViral_of_hasPairErdosHajnalProp h),
          hasPairErdosHajnalProp_of_hasPairPolyRodlProp⟩,
         ⟨fun h => isPairViral_of_hasPairErdosHajnalProp (hasPairErdosHajnalProp_of_hasPairPolyRodlProp h),
          hasPairPolyRodlProp_of_isPairViral⟩⟩

/--
**Theorem 3 (`eh_iff_polyRodl_iff_isViral`, Single-Graph Equivalence)**:
For any finite graph $H$ on a non-empty vertex type $W$:
`(1) HasErdosHajnalProp H ↔ (2) HasPolyRodlProp H` and
`(2) HasPolyRodlProp H ↔ (3) IsViral H`.
-/
theorem eh_iff_polyRodl_iff_isViral
    {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (H : SimpleGraph W) :
    (HasErdosHajnalProp H ↔ HasPolyRodlProp H) ∧
    (HasPolyRodlProp H ↔ IsViral H) := by
  refine ⟨⟨fun h => hasPolyRodlProp_of_isViral (isViral_of_hasErdosHajnalProp h),
          hasErdosHajnalProp_of_hasPolyRodlProp⟩,
         ⟨fun h => isViral_of_hasErdosHajnalProp (hasErdosHajnalProp_of_hasPolyRodlProp h),
          hasPolyRodlProp_of_isViral⟩⟩

end ViralityEquivalence

/-!
### Section 4: Theorem 4(1) (Unordered Viral Substitution Closure)
(Lines 171, 177 of `main.tex`)
-/

section SubstitutionClosure

/-- Vertex substitution commutes with graph complementation: $\overline{H_1[v_0 \leftarrow H_2]} = \overline{H_1}[v_0 \leftarrow \overline{H_2}]$. -/
theorem substGraph_compl {W₁ W₂ : Type*} (H₁ : SimpleGraph W₁) (v₀ : W₁) (H₂ : SimpleGraph W₂) :
    (substGraph H₁ v₀ H₂)ᶜ = substGraph H₁ᶜ v₀ H₂ᶜ := by
  ext a b
  rcases a with u | x <;> rcases b with w | y
  · simp [substGraph, compl_adj, Subtype.ext_iff]
  · simp [substGraph, compl_adj, u.2]
  · simp [substGraph, compl_adj, w.2.symm]
  · simp [substGraph, compl_adj]

/-- Cardinality of the complement of a singleton vertex $v_0 \in W$: $|\{v \in W : v \neq v_0\}| = |W| - 1$. -/
theorem card_subtype_ne {W : Type*} [Fintype W] [DecidableEq W] (v₀ : W) :
    Fintype.card {v : W // v ≠ v₀} = Fintype.card W - 1 := by
  rw [Fintype.card_subtype]
  have h : (Finset.univ.filter (fun v : W => v ≠ v₀)) = Finset.univ.erase v₀ := by
    ext v
    simp
  rw [h, Finset.card_erase_of_mem (Finset.mem_univ v₀), Finset.card_univ]

/-- Vertex count of the substitution graph $H_1[v_0 \leftarrow H_2]$: $|W_1| - 1 + |W_2|$. -/
theorem card_substGraph_vert {W₁ W₂ : Type*} [Fintype W₁] [DecidableEq W₁]
    [Fintype W₂] (v₀ : W₁) :
    Fintype.card ({v : W₁ // v ≠ v₀} ⊕ W₂) = Fintype.card W₁ - 1 + Fintype.card W₂ := by
  rw [Fintype.card_sum, card_subtype_ne v₀]

/-- When $|W_1| = 1$, $H_1[v_0 \leftarrow H_2] \cong H_2$. -/
def substGraphIsoOfCardOne {W₁ W₂ : Type*} [Fintype W₁] [DecidableEq W₁]
    (H₁ : SimpleGraph W₁) (v₀ : W₁) (H₂ : SimpleGraph W₂) (hW₁ : Fintype.card W₁ = 1) :
    substGraph H₁ v₀ H₂ ≃g H₂ where
  toFun a :=
    match a with
    | Sum.inl u =>
      False.elim (by
        haveI : Subsingleton W₁ := Fintype.card_le_one_iff_subsingleton.mp hW₁.le
        exact u.2 (Subsingleton.elim u.1 v₀))
    | Sum.inr x => x
  invFun := Sum.inr
  left_inv a := by
    rcases a with u | x
    · haveI : Subsingleton W₁ := Fintype.card_le_one_iff_subsingleton.mp hW₁.le
      exact False.elim (u.2 (Subsingleton.elim u.1 v₀))
    · rfl
  right_inv x := rfl
  map_rel_iff' := by
    rintro (u | x) (w | y)
    · haveI : Subsingleton W₁ := Fintype.card_le_one_iff_subsingleton.mp hW₁.le
      exact False.elim (u.2 (Subsingleton.elim u.1 v₀))
    · haveI : Subsingleton W₁ := Fintype.card_le_one_iff_subsingleton.mp hW₁.le
      exact False.elim (u.2 (Subsingleton.elim u.1 v₀))
    · haveI : Subsingleton W₁ := Fintype.card_le_one_iff_subsingleton.mp hW₁.le
      exact False.elim (w.2 (Subsingleton.elim w.1 v₀))
    · rfl

/-- Explicit-exponent formulation of `IsPairViral`. -/
def IsPairViralWithExp {W₁ W₂ : Type*} [Fintype W₁] [DecidableEq W₁]
    [Fintype W₂] [DecidableEq W₂] (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂) (d : ℝ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (ε : ℝ),
    0 < ε → ε < 1 / 2 →
      (indCopyCount H₁ G : ℝ) ≤ (ε ^ d * (Fintype.card V : ℝ)) ^ (Fintype.card W₁) →
      (indCopyCount H₂ G : ℝ) ≤ (ε ^ d * (Fintype.card V : ℝ)) ^ (Fintype.card W₂) →
        ∃ S : Finset V, IsEpsRestrictedOn G S ε ∧ ε ^ d * (Fintype.card V : ℝ) ≤ (S.card : ℝ)

/-- Equivalence between `IsPairViral` and existence of a positive exponent $d > 0$ for `IsPairViralWithExp`. -/
theorem isPairViral_iff_exists_exp {W₁ W₂ : Type*} [Fintype W₁] [DecidableEq W₁]
    [Fintype W₂] [DecidableEq W₂] (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂) :
    IsPairViral H₁ H₂ ↔ ∃ d > (0 : ℝ), IsPairViralWithExp H₁ H₂ d :=
  Iff.rfl

/-- Upward monotonicity of `IsPairViralWithExp` in the exponent $d_1 \le d_2$. -/
theorem IsPairViralWithExp.mono {W₁ W₂ : Type*} [Fintype W₁] [DecidableEq W₁]
    [Fintype W₂] [DecidableEq W₂] {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂}
    {d₁ d₂ : ℝ} (hd₁₂ : d₁ ≤ d₂) (h : IsPairViralWithExp H₁ H₂ d₁) :
    IsPairViralWithExp H₁ H₂ d₂ := by
  intro V _ _ G ε hε0 hε1 hc₁ hc₂
  have hε_le_one : ε ≤ 1 := by linarith
  have hpow : ε ^ d₂ ≤ ε ^ d₁ := Real.rpow_le_rpow_of_exponent_ge hε0 hε_le_one hd₁₂
  have hmul : ε ^ d₂ * (Fintype.card V : ℝ) ≤ ε ^ d₁ * (Fintype.card V : ℝ) :=
    mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _)
  have hc₁' : (indCopyCount H₁ G : ℝ) ≤ (ε ^ d₁ * (Fintype.card V : ℝ)) ^ (Fintype.card W₁) :=
    hc₁.trans (pow_le_pow_left₀ (by positivity) hmul _)
  have hc₂' : (indCopyCount H₂ G : ℝ) ≤ (ε ^ d₁ * (Fintype.card V : ℝ)) ^ (Fintype.card W₂) :=
    hc₂.trans (pow_le_pow_left₀ (by positivity) hmul _)
  obtain ⟨S, hS_rest, hS_card⟩ := h V G ε hε0 hε1 hc₁' hc₂'
  exact ⟨S, hS_rest, hmul.trans hS_card⟩

/-- Lifting $\varepsilon$-sparseness from an induced subgraph $H[X]$ to the ambient graph $H$. -/
theorem isEpsSparseOn_map_subtype {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (S_X : Finset ↥(X : Set V)) (ε : ℝ)
    (h : IsEpsSparseOn (H.induce (X : Set V)) S_X ε) :
    IsEpsSparseOn H (S_X.map (Function.Embedding.subtype _)) ε := by
  classical
  let emb : ↥(X : Set V) ↪ V := Function.Embedding.subtype _
  intro v hv
  rcases mem_map.mp hv with ⟨v_sub, hv_sub, rfl⟩
  have h_neigh : neighborFinsetIn H (emb v_sub) (S_X.map emb) =
      (neighborFinsetIn (H.induce (X : Set V)) v_sub S_X).map emb := by
    ext w
    simp only [mem_neighborFinsetIn_iff, mem_map]
    constructor
    · rintro ⟨⟨w_sub, hw_sub, rfl⟩, hadj⟩
      exact ⟨w_sub, ⟨hw_sub, hadj⟩, rfl⟩
    · rintro ⟨w_sub, ⟨hw_sub, hadj⟩, rfl⟩
      exact ⟨⟨w_sub, hw_sub, rfl⟩, hadj⟩
  rw [h_neigh, card_map, card_map]
  exact h v_sub hv_sub

/-- Lifting $\varepsilon$-restrictedness from an induced subgraph $G[X]$ to the ambient graph $G$. -/
theorem isEpsRestrictedOn_map_subtype {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (X : Finset V) (S_X : Finset ↥(X : Set V)) (ε : ℝ)
    (h : IsEpsRestrictedOn (G.induce (X : Set V)) S_X ε) :
    IsEpsRestrictedOn G (S_X.map (Function.Embedding.subtype _)) ε := by
  rcases h with hG | hGc
  · exact Or.inl (isEpsSparseOn_map_subtype G X S_X ε hG)
  · right
    have h_ind_compl : (G.induce (X : Set V))ᶜ = Gᶜ.induce (X : Set V) := by
      ext a b
      exact ⟨fun ⟨hne, hnad⟩ => ⟨Subtype.ext_iff.not.mp hne, hnad⟩,
             fun ⟨hne, hnad⟩ => ⟨Subtype.ext_iff.not.mpr hne, hnad⟩⟩
    rw [h_ind_compl] at hGc
    exact isEpsSparseOn_map_subtype Gᶜ X S_X ε hGc

/-- Induced embeddings of $H_1 - v_0$ into $G$. -/
noncomputable def baseCopies {W₁ V : Type*} [Fintype W₁] [DecidableEq W₁]
    [Fintype V] [DecidableEq V] (H₁ : SimpleGraph W₁) (v₀ : W₁) (G : SimpleGraph V) :
    Finset ({v : W₁ // v ≠ v₀} ↪ V) :=
  by
    classical
    exact Finset.univ.filter (fun ψ : {v : W₁ // v ≠ v₀} ↪ V =>
      G.comap ψ = H₁.comap (Subtype.val : {v : W₁ // v ≠ v₀} → W₁))

/--
Extension fiber $X_\psi \subseteq V(G)$ of an embedding $\psi : V(H_1) \setminus \{v_0\} \hookrightarrow V(G)$:
the set of vertices $w \in V(G)$ disjoint from $\psi(V(H_1) \setminus \{v_0\})$ whose adjacency to
$\psi(u)$ in $G$ matches the adjacency of $v_0$ to $u$ in $H_1$.
-/
noncomputable def substFiber {W₁ V : Type*} [Fintype W₁] [DecidableEq W₁]
    [Fintype V] [DecidableEq V] (H₁ : SimpleGraph W₁) (v₀ : W₁) (G : SimpleGraph V)
    (ψ : {v : W₁ // v ≠ v₀} ↪ V) : Finset V :=
  by
    classical
    exact Finset.univ.filter (fun w : V =>
      (∀ u : {v : W₁ // v ≠ v₀}, w ≠ ψ u) ∧
      (∀ u : {v : W₁ // v ≠ v₀}, G.Adj (ψ u) w ↔ H₁.Adj u.1 v₀))

/--
**Fiber Decomposition of `indCopyCount H₁ G`**:
$\operatorname{ind}_{H_1}(G) = \sum_{\psi \in \text{baseCopies}} |X_\psi|$.
-/
theorem indCopyCount_eq_sum_substFiber {W₁ V : Type*} [Fintype W₁] [DecidableEq W₁]
    [Fintype V] [DecidableEq V] (H₁ : SimpleGraph W₁) (v₀ : W₁) (G : SimpleGraph V) :
    indCopyCount H₁ G = ∑ ψ ∈ baseCopies H₁ v₀ G, (substFiber H₁ v₀ G ψ).card := by
  classical
  rw [← Finset.card_sigma]
  unfold indCopyCount
  let subEmb : {v : W₁ // v ≠ v₀} ↪ W₁ := Function.Embedding.subtype _
  refine Finset.card_bij
    (fun (φ : W₁ ↪ V) _ => ⟨subEmb.trans φ, φ v₀⟩) ?_ ?_ ?_
  · intro φ hφ
    simp only [mem_filter, mem_univ, true_and] at hφ
    simp only [mem_sigma, baseCopies, substFiber, mem_filter, mem_univ, true_and]
    refine ⟨?_, ?_, ?_⟩
    · ext u w
      have h1 := congr_arg (fun (J : SimpleGraph W₁) => J.Adj u.1 w.1) hφ
      simpa [subEmb, comap_adj] using h1
    · intro u h_eq
      exact u.2 (φ.injective h_eq.symm)
    · intro u
      have h1 := congr_arg (fun (J : SimpleGraph W₁) => J.Adj u.1 v₀) hφ
      simpa [subEmb, comap_adj] using h1
  · intro φ₁ _ φ₂ _ h_eq
    simp only [Sigma.mk.inj_iff] at h_eq
    obtain ⟨h_ψ, h_v0⟩ := h_eq
    have h_v0' : φ₁ v₀ = φ₂ v₀ := eq_of_heq h_v0
    ext x
    by_cases hx : x = v₀
    · subst hx; exact h_v0'
    · have h1 := congr_arg (fun (f : {v : W₁ // v ≠ v₀} ↪ V) => f ⟨x, hx⟩) h_ψ
      simpa [subEmb] using h1
  · rintro ⟨ψ, w⟩ h_mem
    simp only [mem_sigma, baseCopies, substFiber, mem_filter, mem_univ, true_and] at h_mem
    obtain ⟨hψ_comap, hw_ne, hw_adj⟩ := h_mem
    let φ_fun : W₁ → V := fun x => if hx : x = v₀ then w else ψ ⟨x, hx⟩
    have hφ_inj : Function.Injective φ_fun := by
      intro x y hxy
      dsimp [φ_fun] at hxy
      split_ifs at hxy with hx hy hy
      · rw [hx, hy]
      · exact False.elim (hw_ne ⟨y, hy⟩ hxy)
      · exact False.elim (hw_ne ⟨x, hx⟩ hxy.symm)
      · exact congr_arg Subtype.val (ψ.injective hxy)
    let φ : W₁ ↪ V := ⟨φ_fun, hφ_inj⟩
    refine ⟨φ, ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and]
      ext x y
      change G.Adj (φ_fun x) (φ_fun y) ↔ H₁.Adj x y
      dsimp [φ_fun]
      split_ifs with hx hy hy
      · subst hx; subst hy
        simp
      · subst hx
        rw [G.adj_comm, H₁.adj_comm]
        exact hw_adj ⟨y, hy⟩
      · subst hy
        exact hw_adj ⟨x, hx⟩
      · have h1 := congr_arg (fun (J : SimpleGraph {v : W₁ // v ≠ v₀}) =>
          J.Adj ⟨x, hx⟩ ⟨y, hy⟩) hψ_comap
        simpa [comap_adj] using h1
    · refine Sigma.ext ?_ (heq_of_eq ?_)
      · ext ⟨x, hx⟩
        change φ_fun x = ψ ⟨x, hx⟩
        dsimp [φ_fun]
        rw [dif_neg hx]
      · change φ_fun v₀ = w
        dsimp [φ_fun]
        rw [dif_pos rfl]

/--
**Induced Embedding Packing into `substGraph H₁ v₀ H₂`**:
$\sum_{\psi \in \text{baseCopies}} \operatorname{ind}_{H_2}(G[X_\psi]) \le \operatorname{ind}_{H_1[v_0 \leftarrow H_2]}(G)$.
-/
theorem sum_indCopyCount_substFiber_le {W₁ W₂ V : Type*} [Fintype W₁] [DecidableEq W₁]
    [Fintype W₂] [DecidableEq W₂] [Fintype V] [DecidableEq V]
    (H₁ : SimpleGraph W₁) (v₀ : W₁) (H₂ : SimpleGraph W₂) (G : SimpleGraph V) :
    ∑ ψ ∈ baseCopies H₁ v₀ G,
      indCopyCount H₂ (G.induce (substFiber H₁ v₀ G ψ : Set V)) ≤
      indCopyCount (substGraph H₁ v₀ H₂) G := by
  classical
  let F_copies := fun ψ : {v : W₁ // v ≠ v₀} ↪ V =>
    Finset.univ.filter (fun φ₂ : W₂ ↪ ↥(substFiber H₁ v₀ G ψ : Set V) =>
      (G.induce (substFiber H₁ v₀ G ψ : Set V)).comap φ₂ = H₂)
  have h_sum_eq : (∑ ψ ∈ baseCopies H₁ v₀ G,
      indCopyCount H₂ (G.induce (substFiber H₁ v₀ G ψ : Set V))) =
      ((baseCopies H₁ v₀ G).sigma F_copies).card := by
    rw [Finset.card_sigma]
    rfl
  rw [h_sum_eq]
  unfold indCopyCount
  let glueFun : (Σ ψ : {v : W₁ // v ≠ v₀} ↪ V, W₂ ↪ ↥(substFiber H₁ v₀ G ψ : Set V)) →
      ({v : W₁ // v ≠ v₀} ⊕ W₂ → V) :=
    fun p a =>
      match a with
      | Sum.inl u => p.1 u
      | Sum.inr x => (p.2 x).1
  have h_glue_inj_all : ∀ p : (Σ ψ : {v : W₁ // v ≠ v₀} ↪ V, W₂ ↪ ↥(substFiber H₁ v₀ G ψ : Set V)),
      Function.Injective (glueFun p) := by
    rintro ⟨ψ, φ₂⟩ a b hab
    rcases a with u | x <;> rcases b with w | y
    · exact congr_arg Sum.inl (ψ.injective hab)
    · have hy_mem : (φ₂ y).1 ∈ substFiber H₁ v₀ G ψ := (φ₂ y).2
      simp only [substFiber, mem_filter, mem_univ, true_and] at hy_mem
      exact False.elim (hy_mem.1 u hab.symm)
    · have hx_mem : (φ₂ x).1 ∈ substFiber H₁ v₀ G ψ := (φ₂ x).2
      simp only [substFiber, mem_filter, mem_univ, true_and] at hx_mem
      exact False.elim (hx_mem.1 w hab)
    · exact congr_arg Sum.inr (φ₂.injective (Subtype.ext hab))
  refine Finset.card_le_card_of_injOn (fun p => ⟨glueFun p, h_glue_inj_all p⟩) ?_ ?_
  · rintro ⟨ψ, φ₂⟩ hp
    simp only [mem_coe, mem_sigma, baseCopies, F_copies, mem_filter, mem_univ, true_and] at hp ⊢
    obtain ⟨hψ_comap, hφ₂_comap⟩ := hp
    ext a b
    rcases a with u | x <;> rcases b with w | y
    · have h1 := congr_arg (fun (J : SimpleGraph {v : W₁ // v ≠ v₀}) => J.Adj u w) hψ_comap
      simpa [glueFun, substGraph, comap_adj] using h1
    · have hy_mem : (φ₂ y).1 ∈ substFiber H₁ v₀ G ψ := (φ₂ y).2
      simp only [substFiber, mem_filter, mem_univ, true_and] at hy_mem
      simpa [glueFun, substGraph, comap_adj] using hy_mem.2 u
    · have hx_mem : (φ₂ x).1 ∈ substFiber H₁ v₀ G ψ := (φ₂ x).2
      simp only [substFiber, mem_filter, mem_univ, true_and] at hx_mem
      change G.Adj (φ₂ x).1 (ψ w) ↔ H₁.Adj v₀ w.1
      rw [G.adj_comm, H₁.adj_comm]
      exact hx_mem.2 w
    · have h1 := congr_arg (fun (J : SimpleGraph W₂) => J.Adj x y) hφ₂_comap
      simpa [glueFun, substGraph, comap_adj] using h1
  · rintro ⟨ψ₁, φ₁⟩ _ ⟨ψ₂, φ₂⟩ _ h_eq
    have h_inl : ψ₁ = ψ₂ := by
      ext u
      exact congr_arg (fun (f : {v : W₁ // v ≠ v₀} ⊕ W₂ ↪ V) => f (Sum.inl u)) h_eq
    subst h_inl
    simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and]
    ext x
    exact congr_arg (fun (f : {v : W₁ // v ≠ v₀} ⊕ W₂ ↪ V) => f (Sum.inr x)) h_eq

/--
Averaging-to-fiber inequality for Theorem 4(1) (`main.tex`, line 177):
With $d' = d + |H_1|d + |H_1|$, if $|\Psi_{\mathrm{large}}| > \frac{1}{2}\varepsilon^{|H_1|d}n^{|H_1|-1}$,
$|X_{\psi^*}| \ge \varepsilon^{|H_1|d+1}n$, and $|\Psi_{\mathrm{large}}| \cdot \operatorname{ind}_{H_2}(F) \le (\varepsilon^{d'} n)^{|H_1|-1+|H_2|}$,
then $\operatorname{ind}_{H_2}(F) \le (\varepsilon^d |X_{\psi^*}|)^{|H_2|}$.
-/
private theorem substGraph_avg_bound_to_fiber
    {h1_card h2_card n : ℕ} {d d' ε X_card Ψ_card ind_F : ℝ}
    (hh1_ge_two : 2 ≤ h1_card) (hh2_pos : 1 ≤ h2_card) (hn_pos : 1 ≤ n)
    (hd_ge_one : 1 ≤ d) (hd'_def : d' = d + (h1_card : ℝ) * d + (h1_card : ℝ))
    (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    (hind_nonneg : 0 ≤ ind_F)
    (hX_ge : ε ^ ((h1_card : ℝ) * d + 1) * (n : ℝ) ≤ X_card)
    (hΨ_gt : (1 / 2 : ℝ) * ε ^ ((h1_card : ℝ) * d) * (n : ℝ) ^ (h1_card - 1) < Ψ_card)
    (h_avg : Ψ_card * ind_F ≤ (ε ^ d' * (n : ℝ)) ^ (h1_card - 1 + h2_card)) :
    ind_F ≤ (ε ^ d * X_card) ^ h2_card := by
  have hh1_pos : 1 ≤ h1_card := by omega
  have hd_pos : 0 < d := by linarith
  have hε_le_one : ε ≤ 1 := by linarith
  have hn_pos_r : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  let h_tot := h1_card - 1 + h2_card
  have h_rhs_split : (ε ^ d' * (n : ℝ)) ^ h_tot =
      ((1 / 2 : ℝ) * ε ^ ((h1_card : ℝ) * d) * (n : ℝ) ^ (h1_card - 1)) *
      (2 * ε ^ ((h_tot : ℝ) * d' - (h1_card : ℝ) * d) * (n : ℝ) ^ h2_card) := by
    have h_n_split : (n : ℝ) ^ h_tot = (n : ℝ) ^ (h1_card - 1) * (n : ℝ) ^ h2_card := by
      dsimp [h_tot]
      rw [pow_add]
    have h_ε_split : (ε ^ d') ^ h_tot =
        ε ^ ((h1_card : ℝ) * d) * ε ^ ((h_tot : ℝ) * d' - (h1_card : ℝ) * d) := by
      rw [← Real.rpow_natCast (ε ^ d') h_tot, ← Real.rpow_mul hε0.le, ← Real.rpow_add hε0]
      congr 1; ring
    rw [mul_pow, h_n_split, h_ε_split]
    ring
  have h_2_le_inv : (2 : ℝ) ≤ ε ^ (-1 : ℝ) := by
    rw [Real.rpow_neg_one, le_inv_comm₀ (by norm_num) hε0]
    linarith
  have h_exp_ge : (h2_card : ℝ) * (d + (h1_card : ℝ) * d + 1) ≤
      (h_tot : ℝ) * d' - (h1_card : ℝ) * d - 1 := by
    have hh1_sub_r : ((h1_card - 1 : ℕ) : ℝ) = (h1_card : ℝ) - 1 := by
      rw [Nat.cast_sub hh1_pos, Nat.cast_one]
    have hh_tot_r : (h_tot : ℝ) = (h1_card : ℝ) - 1 + (h2_card : ℝ) := by
      dsimp [h_tot]
      rw [Nat.cast_add, hh1_sub_r]
    have hh1_ge2_r : (2 : ℝ) ≤ (h1_card : ℝ) := by exact_mod_cast hh1_ge_two
    have hh2_ge1_r : (1 : ℝ) ≤ (h2_card : ℝ) := by exact_mod_cast hh2_pos
    rw [hh_tot_r, hd'_def]
    have h_diff : ((h1_card : ℝ) - 1 + (h2_card : ℝ)) * (d + (h1_card : ℝ) * d + (h1_card : ℝ)) -
        (h1_card : ℝ) * d - 1 - (h2_card : ℝ) * (d + (h1_card : ℝ) * d + 1) =
        ((h1_card : ℝ) - 1) * d + ((h1_card : ℝ) - 2) * ((h1_card : ℝ) * d) +
        (((h1_card : ℝ) - 1) * (h1_card : ℝ) - 1) + (h2_card : ℝ) * ((h1_card : ℝ) - 1) := by ring
    have h1 : 0 ≤ ((h1_card : ℝ) - 1) * d := mul_nonneg (by linarith) (by linarith)
    have h2 : 0 ≤ ((h1_card : ℝ) - 2) * ((h1_card : ℝ) * d) := mul_nonneg (by linarith) (by positivity)
    have h3 : 0 ≤ ((h1_card : ℝ) - 1) * (h1_card : ℝ) - 1 := by nlinarith
    have h4 : 0 ≤ (h2_card : ℝ) * ((h1_card : ℝ) - 1) := mul_nonneg (by linarith) (by linarith)
    linarith
  have h_factor_le :
      2 * ε ^ ((h_tot : ℝ) * d' - (h1_card : ℝ) * d) * (n : ℝ) ^ h2_card ≤
      (ε ^ d * X_card) ^ h2_card := by
    calc 2 * ε ^ ((h_tot : ℝ) * d' - (h1_card : ℝ) * d) * (n : ℝ) ^ h2_card
      _ ≤ ε ^ (-1 : ℝ) * ε ^ ((h_tot : ℝ) * d' - (h1_card : ℝ) * d) * (n : ℝ) ^ h2_card := by
        have : 0 ≤ ε ^ ((h_tot : ℝ) * d' - (h1_card : ℝ) * d) * (n : ℝ) ^ h2_card := by positivity
        nlinarith
      _ = ε ^ ((h_tot : ℝ) * d' - (h1_card : ℝ) * d - 1) * (n : ℝ) ^ h2_card := by
        rw [← Real.rpow_add hε0]
        congr 2; ring
      _ ≤ ε ^ ((h2_card : ℝ) * (d + (h1_card : ℝ) * d + 1)) * (n : ℝ) ^ h2_card :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_ge hε0 hε_le_one h_exp_ge) (by positivity)
      _ = (ε ^ (d + (h1_card : ℝ) * d + 1) * (n : ℝ)) ^ h2_card := by
        conv_rhs => rw [mul_pow, ← Real.rpow_natCast _ h2_card, ← Real.rpow_mul hε0.le]
        rw [mul_comm (h2_card : ℝ)]
      _ ≤ (ε ^ d * X_card) ^ h2_card := by
        refine pow_le_pow_left₀ (by positivity) ?_ h2_card
        have h_add : ε ^ (d + (h1_card : ℝ) * d + 1) = ε ^ d * ε ^ ((h1_card : ℝ) * d + 1) := by
          rw [← Real.rpow_add hε0]
          congr 1; ring
        rw [h_add, mul_assoc]
        exact mul_le_mul_of_nonneg_left hX_ge (by positivity)
  have h_denom_pos : 0 < (1 / 2 : ℝ) * ε ^ ((h1_card : ℝ) * d) * (n : ℝ) ^ (h1_card - 1) := by
    positivity
  have h_mul_le :
      ((1 / 2 : ℝ) * ε ^ ((h1_card : ℝ) * d) * (n : ℝ) ^ (h1_card - 1)) * ind_F ≤
      ((1 / 2 : ℝ) * ε ^ ((h1_card : ℝ) * d) * (n : ℝ) ^ (h1_card - 1)) *
      (ε ^ d * X_card) ^ h2_card := by
    calc ((1 / 2 : ℝ) * ε ^ ((h1_card : ℝ) * d) * (n : ℝ) ^ (h1_card - 1)) * ind_F
      _ ≤ Ψ_card * ind_F := mul_le_mul_of_nonneg_right hΨ_gt.le hind_nonneg
      _ ≤ (ε ^ d' * (n : ℝ)) ^ h_tot := h_avg
      _ = ((1 / 2 : ℝ) * ε ^ ((h1_card : ℝ) * d) * (n : ℝ) ^ (h1_card - 1)) *
          (2 * ε ^ ((h_tot : ℝ) * d' - (h1_card : ℝ) * d) * (n : ℝ) ^ h2_card) := h_rhs_split
      _ ≤ ((1 / 2 : ℝ) * ε ^ ((h1_card : ℝ) * d) * (n : ℝ) ^ (h1_card - 1)) *
          (ε ^ d * X_card) ^ h2_card :=
        mul_le_mul_of_nonneg_left h_factor_le h_denom_pos.le
  exact le_of_mul_le_mul_left h_mul_le h_denom_pos

/--
**Theorem 4(1) (`isPairViral_substGraph`, Unordered Viral Substitution Closure for Pairs)**:
If $\{H_1, K\}$ and $\{H_2, K\}$ are both viral (`IsPairViral`), then
$\{H_1[v_0 \leftarrow H_2], K\}$ (`IsPairViral (substGraph H₁ v₀ H₂) K`) is viral.
-/
theorem isPairViral_substGraph {W₁ W₂ W₃ : Type*} [Fintype W₁] [DecidableEq W₁]
    [Fintype W₂] [DecidableEq W₂] [Fintype W₃] [DecidableEq W₃]
    (H₁ : SimpleGraph W₁) (v₀ : W₁) (H₂ : SimpleGraph W₂) (K : SimpleGraph W₃)
    (h₁ : IsPairViral H₁ K) (h₂ : IsPairViral H₂ K) :
    IsPairViral (substGraph H₁ v₀ H₂) K := by
  classical
  haveI : Nonempty W₁ := ⟨v₀⟩
  let h1_card := Fintype.card W₁
  let h2_card := Fintype.card W₂
  let h3_card := Fintype.card W₃
  have hh1_pos : 1 ≤ h1_card := Fintype.card_pos
  rcases eq_or_ne h1_card 1 with hh1_one | hh1_gt_one
  · exact IsPairViral.congr (substGraphIsoOfCardOne H₁ v₀ H₂ hh1_one).symm (SimpleGraph.Iso.refl) h₂
  rcases eq_or_ne h2_card 0 with hh2_zero | hh2_pos_ne
  · obtain ⟨d₂, hd₂, h_viral₂⟩ := h₂
    refine ⟨d₂, hd₂, fun V _ _ G ε hε0 hε1 _ hc_K => ?_⟩
    have hc_H₂ : (indCopyCount H₂ G : ℝ) ≤ (ε ^ d₂ * (Fintype.card V : ℝ)) ^ h2_card := by
      rw [hh2_zero, pow_zero]
      have h_le_one : indCopyCount H₂ G ≤ 1 := by
        calc indCopyCount H₂ G
          _ ≤ Fintype.card (W₂ ↪ V) := Finset.card_le_univ _
          _ ≤ Fintype.card (W₂ → V) := Fintype.card_le_of_injective _ DFunLike.coe_injective
          _ = 1 := by
            rw [Fintype.card_fun]
            change Fintype.card V ^ h2_card = 1
            rw [hh2_zero, pow_zero]
      exact_mod_cast h_le_one
    exact h_viral₂ V G ε hε0 hε1 hc_H₂ hc_K
  have hh1_ge_two : 2 ≤ h1_card := by omega
  have hh2_pos : 1 ≤ h2_card := by omega
  obtain ⟨d₁, hd₁, h_exp₁⟩ := (isPairViral_iff_exists_exp H₁ K).mp h₁
  obtain ⟨d₂, hd₂, h_exp₂⟩ := (isPairViral_iff_exists_exp H₂ K).mp h₂
  let d : ℝ := max (max d₁ d₂) 1
  have hd_ge_one : 1 ≤ d := le_max_right _ _
  have hd_pos : 0 < d := by linarith
  have h_v1 : IsPairViralWithExp H₁ K d :=
    IsPairViralWithExp.mono ((le_max_left d₁ d₂).trans (le_max_left _ _)) h_exp₁
  have h_v2 : IsPairViralWithExp H₂ K d :=
    IsPairViralWithExp.mono ((le_max_right d₁ d₂).trans (le_max_left _ _)) h_exp₂
  let d' : ℝ := d + (h1_card : ℝ) * d + (h1_card : ℝ)
  have hd_le_d' : d ≤ d' := by
    dsimp [d']
    have : 0 ≤ (h1_card : ℝ) * d + (h1_card : ℝ) := by positivity
    linarith
  have hd'_pos : 0 < d' := lt_of_lt_of_le hd_pos hd_le_d'
  refine ⟨d', hd'_pos, fun V _ _ G ε hε0 hε1 hc_H hc_K => ?_⟩
  let n := Fintype.card V
  have hε_le_one : ε ≤ 1 := by linarith
  have hpow_d'_le_d : ε ^ d' ≤ ε ^ d := Real.rpow_le_rpow_of_exponent_ge hε0 hε_le_one hd_le_d'
  by_cases hc_H1 : (indCopyCount H₁ G : ℝ) ≤ (ε ^ d * (n : ℝ)) ^ h1_card
  · have hc_K_d : (indCopyCount K G : ℝ) ≤ (ε ^ d * (n : ℝ)) ^ h3_card :=
      hc_K.trans (pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_right hpow_d'_le_d (Nat.cast_nonneg n)) _)
    obtain ⟨S, hS_rest, hS_card⟩ := h_v1 V G ε hε0 hε1 hc_H1 hc_K_d
    refine ⟨S, hS_rest, ?_⟩
    exact (mul_le_mul_of_nonneg_right hpow_d'_le_d (Nat.cast_nonneg n)).trans hS_card
  · push_neg at hc_H1
    have hn_pos : 1 ≤ n := by
      by_contra hn0
      have hn_eq0 : n = 0 := by omega
      haveI : IsEmpty V := Fintype.card_eq_zero_iff.mp hn_eq0
      haveI : IsEmpty (W₁ ↪ V) := ⟨fun f => IsEmpty.false (f v₀)⟩
      have h_zero : indCopyCount H₁ G = 0 := by
        unfold indCopyCount
        simp
      rw [h_zero, Nat.cast_zero, hn_eq0, Nat.cast_zero, mul_zero, zero_pow (by omega)] at hc_H1
      exact lt_irrefl 0 hc_H1
    have hn_pos_r : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
    let W₁' := {v : W₁ // v ≠ v₀}
    have hW₁'_card : Fintype.card W₁' = h1_card - 1 := card_subtype_ne v₀
    let Base := baseCopies H₁ v₀ G
    let τ : ℝ := (1 / 2 : ℝ) * ε ^ ((h1_card : ℝ) * d) * (n : ℝ)
    let Ψ_large := Base.filter (fun ψ => τ ≤ ((substFiber H₁ v₀ G ψ).card : ℝ))
    let Ψ_small := Base.filter (fun ψ => ¬(τ ≤ ((substFiber H₁ v₀ G ψ).card : ℝ)))
    have hBase_card_le : (Base.card : ℝ) ≤ (n : ℝ) ^ (h1_card - 1) := by
      have h1 : Base.card ≤ Fintype.card (W₁' ↪ V) := card_filter_le _ _
      have h2 : Fintype.card (W₁' ↪ V) ≤ Fintype.card (W₁' → V) :=
        Fintype.card_le_of_injective _ DFunLike.coe_injective
      have h3 : Fintype.card (W₁' → V) = n ^ (h1_card - 1) := by
        rw [Fintype.card_fun, hW₁'_card]
      exact_mod_cast (h1.trans (h2.trans_eq h3))
    have h_sum_total : (indCopyCount H₁ G : ℝ) =
        ∑ ψ ∈ Ψ_large, ((substFiber H₁ v₀ G ψ).card : ℝ) +
        ∑ ψ ∈ Ψ_small, ((substFiber H₁ v₀ G ψ).card : ℝ) := by
      have h1 : (indCopyCount H₁ G : ℝ) = ∑ ψ ∈ Base, ((substFiber H₁ v₀ G ψ).card : ℝ) := by
        exact_mod_cast indCopyCount_eq_sum_substFiber H₁ v₀ G
      rw [h1, ← sum_filter_add_sum_filter_not Base
        (fun ψ => τ ≤ ((substFiber H₁ v₀ G ψ).card : ℝ))]
    have h_pow_h1_eq : (ε ^ d * (n : ℝ)) ^ h1_card =
        ε ^ ((h1_card : ℝ) * d) * (n : ℝ) ^ (h1_card - 1) * (n : ℝ) := by
      have hh1_sub : h1_card = (h1_card - 1) + 1 := (Nat.sub_add_cancel hh1_pos).symm
      rw [mul_pow, ← Real.rpow_natCast (ε ^ d) h1_card, ← Real.rpow_mul hε0.le, mul_comm d]
      conv_lhs => rhs; rw [hh1_sub, pow_succ]
      ring
    have h_sum_small : ∑ ψ ∈ Ψ_small, ((substFiber H₁ v₀ G ψ).card : ℝ) ≤
        (1 / 2 : ℝ) * (ε ^ d * (n : ℝ)) ^ h1_card := by
      calc ∑ ψ ∈ Ψ_small, ((substFiber H₁ v₀ G ψ).card : ℝ)
        _ ≤ ∑ _ψ ∈ Ψ_small, τ := by
          refine sum_le_sum (fun ψ hψ => ?_)
          simp only [Ψ_small, mem_filter, not_le] at hψ
          exact hψ.2.le
        _ = (Ψ_small.card : ℝ) * τ := by rw [sum_const, nsmul_eq_mul]
        _ ≤ (Base.card : ℝ) * τ := by
          have : (Ψ_small.card : ℝ) ≤ (Base.card : ℝ) := by
            exact_mod_cast card_filter_le _ _
          exact mul_le_mul_of_nonneg_right this (by dsimp [τ]; positivity)
        _ ≤ (n : ℝ) ^ (h1_card - 1) * ((1 / 2 : ℝ) * ε ^ ((h1_card : ℝ) * d) * (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hBase_card_le (by dsimp [τ]; positivity)
        _ = (1 / 2 : ℝ) * (ε ^ ((h1_card : ℝ) * d) * (n : ℝ) ^ (h1_card - 1) * (n : ℝ)) := by ring
        _ = (1 / 2 : ℝ) * (ε ^ d * (n : ℝ)) ^ h1_card := by rw [← h_pow_h1_eq]
    have h_sum_large_gt : (1 / 2 : ℝ) * (ε ^ d * (n : ℝ)) ^ h1_card <
        ∑ ψ ∈ Ψ_large, ((substFiber H₁ v₀ G ψ).card : ℝ) := by linarith
    have h_sum_large_le : ∑ ψ ∈ Ψ_large, ((substFiber H₁ v₀ G ψ).card : ℝ) ≤
        (Ψ_large.card : ℝ) * (n : ℝ) := by
      calc ∑ ψ ∈ Ψ_large, ((substFiber H₁ v₀ G ψ).card : ℝ)
        _ ≤ ∑ _ψ ∈ Ψ_large, (n : ℝ) := by
          refine sum_le_sum (fun ψ _ => ?_)
          have : (substFiber H₁ v₀ G ψ).card ≤ n := card_le_univ _
          exact_mod_cast this
        _ = (Ψ_large.card : ℝ) * (n : ℝ) := by rw [sum_const, nsmul_eq_mul]
    have h_Ψ_large_card_gt :
        (1 / 2 : ℝ) * ε ^ ((h1_card : ℝ) * d) * (n : ℝ) ^ (h1_card - 1) < (Ψ_large.card : ℝ) := by
      have h1 : ((1 / 2 : ℝ) * ε ^ ((h1_card : ℝ) * d) * (n : ℝ) ^ (h1_card - 1)) * (n : ℝ) <
          (Ψ_large.card : ℝ) * (n : ℝ) := by
        calc ((1 / 2 : ℝ) * ε ^ ((h1_card : ℝ) * d) * (n : ℝ) ^ (h1_card - 1)) * (n : ℝ)
          _ = (1 / 2 : ℝ) * (ε ^ d * (n : ℝ)) ^ h1_card := by rw [h_pow_h1_eq]; ring
          _ < ∑ ψ ∈ Ψ_large, ((substFiber H₁ v₀ G ψ).card : ℝ) := h_sum_large_gt
          _ ≤ (Ψ_large.card : ℝ) * (n : ℝ) := h_sum_large_le
      exact lt_of_mul_lt_mul_right h1 hn_pos_r.le
    have hΨ_large_ne : Ψ_large.Nonempty := by
      have : (0 : ℝ) < (Ψ_large.card : ℝ) := lt_trans (by positivity) h_Ψ_large_card_gt
      exact card_pos.mp (by exact_mod_cast this)
    obtain ⟨ψ_star, hψ_star_mem, hψ_star_min⟩ :=
      Finset.exists_min_image Ψ_large
        (fun ψ => indCopyCount H₂ (G.induce (substFiber H₁ v₀ G ψ : Set V))) hΨ_large_ne
    let X_star := substFiber H₁ v₀ G ψ_star
    let F := G.induce (X_star : Set V)
    have hX_star_ge_τ : (1 / 2 : ℝ) * ε ^ ((h1_card : ℝ) * d) * (n : ℝ) ≤ (X_star.card : ℝ) := by
      simp only [Ψ_large, mem_filter] at hψ_star_mem
      exact hψ_star_mem.2
    have hX_star_ge_eps : ε ^ ((h1_card : ℝ) * d + 1) * (n : ℝ) ≤ (X_star.card : ℝ) := by
      have h1 : ε ^ ((h1_card : ℝ) * d + 1) ≤ (1 / 2 : ℝ) * ε ^ ((h1_card : ℝ) * d) := by
        rw [Real.rpow_add_one hε0.ne', mul_comm _ ε]
        exact mul_le_mul_of_nonneg_right hε1.le (by positivity)
      exact (mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg n)).trans hX_star_ge_τ
    have h_card_subst : Fintype.card ({v : W₁ // v ≠ v₀} ⊕ W₂) = h1_card - 1 + h2_card :=
      card_substGraph_vert v₀
    have h_avg_bound : (Ψ_large.card : ℝ) * (indCopyCount H₂ F : ℝ) ≤
        (ε ^ d' * (n : ℝ)) ^ (h1_card - 1 + h2_card) := by
      have h_min_sum : Ψ_large.card * indCopyCount H₂ F ≤
          ∑ ψ ∈ Ψ_large, indCopyCount H₂ (G.induce (substFiber H₁ v₀ G ψ : Set V)) := by
        calc Ψ_large.card * indCopyCount H₂ F
          _ = ∑ _ψ ∈ Ψ_large, indCopyCount H₂ F := by rw [sum_const, smul_eq_mul]
          _ ≤ ∑ ψ ∈ Ψ_large, indCopyCount H₂ (G.induce (substFiber H₁ v₀ G ψ : Set V)) :=
            sum_le_sum (fun ψ hψ => hψ_star_min ψ hψ)
      have h_sub_sum : ∑ ψ ∈ Ψ_large, indCopyCount H₂ (G.induce (substFiber H₁ v₀ G ψ : Set V)) ≤
          ∑ ψ ∈ Base, indCopyCount H₂ (G.induce (substFiber H₁ v₀ G ψ : Set V)) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
      have h_le_H := (h_min_sum.trans h_sub_sum).trans (sum_indCopyCount_substFiber_le H₁ v₀ H₂ G)
      have h_le_H_r : (Ψ_large.card : ℝ) * (indCopyCount H₂ F : ℝ) ≤
          (indCopyCount (substGraph H₁ v₀ H₂) G : ℝ) := by exact_mod_cast h_le_H
      rw [h_card_subst] at hc_H
      exact h_le_H_r.trans hc_H
    have hc_H₂_F : (indCopyCount H₂ F : ℝ) ≤ (ε ^ d * (X_star.card : ℝ)) ^ h2_card :=
      substGraph_avg_bound_to_fiber hh1_ge_two hh2_pos hn_pos hd_ge_one rfl hε0 hε1
        (Nat.cast_nonneg _) hX_star_ge_eps h_Ψ_large_card_gt h_avg_bound
    have h_d'_le_d_X : ε ^ d' * (n : ℝ) ≤ ε ^ d * (X_star.card : ℝ) := by
      have h1 : ε ^ d' ≤ ε ^ (d + (h1_card : ℝ) * d + 1) := by
        refine Real.rpow_le_rpow_of_exponent_ge hε0 hε_le_one ?_
        dsimp [d']
        have : (1 : ℝ) ≤ (h1_card : ℝ) := by exact_mod_cast hh1_pos
        linarith
      have h2 : ε ^ (d + (h1_card : ℝ) * d + 1) * (n : ℝ) =
          ε ^ d * (ε ^ ((h1_card : ℝ) * d + 1) * (n : ℝ)) := by
        rw [← mul_assoc, ← Real.rpow_add hε0]
        congr 2; ring
      calc ε ^ d' * (n : ℝ)
        _ ≤ ε ^ (d + (h1_card : ℝ) * d + 1) * (n : ℝ) :=
          mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg n)
        _ = ε ^ d * (ε ^ ((h1_card : ℝ) * d + 1) * (n : ℝ)) := h2
        _ ≤ ε ^ d * (X_star.card : ℝ) :=
          mul_le_mul_of_nonneg_left hX_star_ge_eps (by positivity)
    have hc_K_F : (indCopyCount K F : ℝ) ≤ (ε ^ d * (X_star.card : ℝ)) ^ h3_card := by
      have h_le : indCopyCount K F ≤ indCopyCount K G :=
        indCopyCount_comap_le K G (Function.Embedding.subtype _)
      have h_le_r : (indCopyCount K F : ℝ) ≤ (indCopyCount K G : ℝ) := by exact_mod_cast h_le
      exact h_le_r.trans (hc_K.trans (pow_le_pow_left₀ (by positivity) h_d'_le_d_X h3_card))
    have hcard_F : Fintype.card ↥(X_star : Set V) = X_star.card := Fintype.card_coe X_star
    rw [← hcard_F] at hc_H₂_F hc_K_F
    obtain ⟨S_F, hS_F_rest, hS_F_card⟩ := h_v2 ↥(X_star : Set V) F ε hε0 hε1 hc_H₂_F hc_K_F
    rw [hcard_F] at hS_F_card
    let emb : ↥(X_star : Set V) ↪ V := Function.Embedding.subtype _
    refine ⟨S_F.map emb, isEpsRestrictedOn_map_subtype G X_star S_F ε hS_F_rest, ?_⟩
    rw [card_map]
    exact h_d'_le_d_X.trans hS_F_card

/--
**Theorem 4(1) (`isViral_substGraph`, Unordered Viral Substitution Closure for Single Graphs)**:
If $H_1$ and $H_2$ are viral, then $H_1[v_0 \leftarrow H_2]$ (`substGraph H₁ v₀ H₂`) is viral.
-/
theorem isViral_substGraph {W₁ W₂ : Type*} [Fintype W₁] [DecidableEq W₁]
    [Fintype W₂] [DecidableEq W₂]
    (H₁ : SimpleGraph W₁) (v₀ : W₁) (H₂ : SimpleGraph W₂)
    (h₁ : IsViral H₁) (h₂ : IsViral H₂) :
    IsViral (substGraph H₁ v₀ H₂) := by
  rw [← isPairViral_self_iff]
  exact isPairViral_substGraph H₁ v₀ H₂ (substGraph H₁ v₀ H₂)
    (isPairViral_of_isViral_left _ h₁) (isPairViral_of_isViral_left _ h₂)

/--
**Theorem 4(1) (`hasErdosHajnalProp_substGraph`, Erdős–Hajnal Substitution Closure)**:
If $H_1$ and $H_2$ (with non-empty $W_2$) satisfy the Erdős–Hajnal property, then
$H_1[v_0 \leftarrow H_2]$ satisfies the Erdős–Hajnal property.
-/
theorem hasErdosHajnalProp_substGraph {W₁ W₂ : Type*} [Fintype W₁] [DecidableEq W₁]
    [Fintype W₂] [DecidableEq W₂] [Nonempty W₂]
    (H₁ : SimpleGraph W₁) (v₀ : W₁) (H₂ : SimpleGraph W₂)
    (h₁ : HasErdosHajnalProp H₁) (h₂ : HasErdosHajnalProp H₂) :
    HasErdosHajnalProp (substGraph H₁ v₀ H₂) := by
  haveI : Nonempty W₁ := ⟨v₀⟩
  have hv₁ : IsViral H₁ := isViral_of_hasErdosHajnalProp h₁
  have hv₂ : IsViral H₂ := isViral_of_hasErdosHajnalProp h₂
  exact hasErdosHajnalProp_of_hasPolyRodlProp
    (hasPolyRodlProp_of_isViral (isViral_substGraph H₁ v₀ H₂ hv₁ hv₂))

end SubstitutionClosure

/-!
### Section 5: Theorem 4(2) (Unordered Simultaneous Leaf and Co-Leaf Viral Closure)
(Lines 172, 179–184 of `main.tex`)
-/

section SimultaneousLeafColeaf

/-- $\overline{K_2} = \bot$ on `Fin 2` satisfies the Erdős–Hajnal property with $c = 1$. -/
theorem hasErdosHajnalProp_bot_fin2 : HasErdosHajnalProp (⊥ : SimpleGraph (Fin 2)) := by
  refine ⟨1, zero_lt_one, fun V _ _ G hG => ?_⟩
  rw [Real.rpow_one]
  have h_clique : G.IsClique ((Finset.univ : Finset V) : Set V) := by
    intro u _ v _ huv
    by_contra hnad
    have hnad_symm : ¬G.Adj v u := fun h => hnad h.symm
    apply hG
    let g : Fin 2 ↪ V :=
      ⟨![u, v], by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp at hij ⊢
        · exact False.elim (huv hij)
        · exact False.elim (huv hij.symm)⟩
    refine ⟨g, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [g, comap_adj, hnad, hnad_symm]
  have h1 : Fintype.card V ≤ G.cliqueNum := by
    simpa using h_clique.card_le_cliqueNum
  exact_mod_cast (h1.trans (cliqueNum_le_kappa G))

/-- $K_2 = \top$ on `Fin 2` satisfies the Erdős–Hajnal property with $c = 1$. -/
theorem hasErdosHajnalProp_top_fin2 : HasErdosHajnalProp (⊤ : SimpleGraph (Fin 2)) := by
  have h := hasErdosHajnalProp_bot_fin2.compl
  rwa [compl_bot] at h

/-- $\overline{K_2}$ (`⊥ : SimpleGraph (Fin 2)`) is viral. -/
theorem isViral_bot_fin2 : IsViral (⊥ : SimpleGraph (Fin 2)) :=
  isViral_of_hasErdosHajnalProp hasErdosHajnalProp_bot_fin2

/-- $K_2$ (`⊤ : SimpleGraph (Fin 2)`) is viral. -/
theorem isViral_top_fin2 : IsViral (⊤ : SimpleGraph (Fin 2)) :=
  isViral_of_hasErdosHajnalProp hasErdosHajnalProp_top_fin2

/--
If vertex $v_0 \in W$ has degree $0$ in $H$, then $H \cong \overline{K_2}[0 \leftarrow (H - v_0)]$.
-/
def degZeroSubstGraphIso {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (v₀ : W)
    (hdeg0 : (neighborFinsetIn H v₀ Finset.univ).card = 0) :
    substGraph (⊥ : SimpleGraph (Fin 2)) 0 (H.comap (Subtype.val : {v : W // v ≠ v₀} → W)) ≃g H where
  toFun a :=
    match a with
    | Sum.inl _ => v₀
    | Sum.inr u => u.1
  invFun w :=
    if hw : w = v₀ then
      Sum.inl ⟨1, by decide⟩
    else
      Sum.inr ⟨w, hw⟩
  left_inv a := by
    rcases a with ⟨i, hi⟩ | ⟨u, hu⟩
    · have hi1 : i = 1 := by fin_cases i <;> first | contradiction | rfl
      subst hi1
      simp
    · simp [hu]
  right_inv w := by
    by_cases hw : w = v₀
    · subst hw; simp
    · simp [hw]
  map_rel_iff' := by
    have h_no_adj : ∀ u : W, ¬H.Adj v₀ u := by
      intro u hadj
      have h_empty : neighborFinsetIn H v₀ Finset.univ = ∅ := card_eq_zero.mp hdeg0
      have hu_mem : u ∈ neighborFinsetIn H v₀ Finset.univ :=
        (mem_neighborFinsetIn_iff H v₀ u Finset.univ).mpr ⟨mem_univ u, hadj⟩
      rw [h_empty] at hu_mem
      exact notMem_empty u hu_mem
    rintro (⟨i, hi⟩ | ⟨u, hu⟩) (⟨j, hj⟩ | ⟨w, hw⟩)
    · have hi1 : i = 1 := by fin_cases i <;> first | contradiction | rfl
      have hj1 : j = 1 := by fin_cases j <;> first | contradiction | rfl
      subst hi1; subst hj1
      simp [substGraph]
    · simp [substGraph, h_no_adj w]
    · have h_no_symm : ¬H.Adj u v₀ := fun h => h_no_adj u h.symm
      simp [substGraph, h_no_symm]
    · simp [substGraph, comap_adj]

/--
Degree-$0$ left reduction: if $v_0$ has degree $0$ in $H$ and $\{H - v_0, K\}$ is viral, then
$\{H, K\}$ is viral.
-/
theorem isPairViral_of_deg_zero_left {W₁ W₂ : Type*} [Fintype W₁] [DecidableEq W₁]
    [Fintype W₂] [DecidableEq W₂]
    (H : SimpleGraph W₁) (v₀ : W₁) (K : SimpleGraph W₂)
    (hdeg0 : (neighborFinsetIn H v₀ Finset.univ).card = 0)
    (h_viral : IsPairViral (H.comap (Subtype.val : {v : W₁ // v ≠ v₀} → W₁)) K) :
    IsPairViral H K := by
  have h_bot_K : IsPairViral (⊥ : SimpleGraph (Fin 2)) K :=
    isPairViral_of_isViral_left K isViral_bot_fin2
  have h_subst := isPairViral_substGraph (⊥ : SimpleGraph (Fin 2)) 0
    (H.comap (Subtype.val : {v : W₁ // v ≠ v₀} → W₁)) K h_bot_K h_viral
  exact IsPairViral.congr (degZeroSubstGraphIso H v₀ hdeg0) (SimpleGraph.Iso.refl) h_subst

/--
Degree-$0$ right co-leaf reduction: if $w_0$ has degree $0$ in $J$ and $\{H, (J - w_0)ᶜ\}$ is viral,
then $\{H, Jᶜ\}$ is viral.
-/
theorem isPairViral_of_deg_zero_right_compl {W₁ W₂ : Type*} [Fintype W₁] [DecidableEq W₁]
    [Fintype W₂] [DecidableEq W₂]
    (H : SimpleGraph W₁) (J : SimpleGraph W₂) (w₀ : W₂)
    (hdeg0 : (neighborFinsetIn J w₀ Finset.univ).card = 0)
    (h_viral : IsPairViral H (J.comap (Subtype.val : {w : W₂ // w ≠ w₀} → W₂))ᶜ) :
    IsPairViral H Jᶜ := by
  let J' := J.comap (Subtype.val : {w : W₂ // w ≠ w₀} → W₂)
  have h_viral_dual : IsPairViral J' Hᶜ := by
    have h1 := h_viral.compl.symm
    rwa [compl_compl] at h1
  have h_J_Hc := isPairViral_of_deg_zero_left J w₀ Hᶜ hdeg0 h_viral_dual
  have h_res := h_J_Hc.compl.symm
  rwa [compl_compl] at h_res

/-! #### Part 5.2: Degree-1 Leaf Extension Pigeonhole Lemma -/

/--
Embedding glue helper for `leaf_extension_anticomplete_or_viral`:
If $v_0$ has unique neighbor $u_0$ in $H$, $\varphi$ embeds $H - \{v_0, u_0\}$ into $G[S]$,
$x \in \text{substFiber } H'\ u_0'\ G[S]\ \varphi$ extends $\varphi$ at $u_0$ to an induced copy of
$H - v_0$ in $G[S]$, and $z \notin S$ is adjacent in $G$ to $x$ and non-adjacent in $G$ to
$\varphi(V(H) \setminus \{v_0, u_0\})$, then $G$ contains an induced copy of $H$.
-/
private theorem not_isInducedSubgraphFree_of_leaf_extension
    {W₁ V : Type*} [Fintype W₁] [DecidableEq W₁] [Fintype V] [DecidableEq V]
    (H : SimpleGraph W₁) (v₀ u₀ : W₁) (hu₀_ne : u₀ ≠ v₀)
    (hv₀_adj : ∀ w : W₁, H.Adj v₀ w ↔ w = u₀)
    (G : SimpleGraph V) (S : Finset V)
    (φ : {u : {v : W₁ // v ≠ v₀} // u ≠ ⟨u₀, hu₀_ne⟩} ↪ ↥(S : Set V))
    (hφ_base : φ ∈ baseCopies (H.comap (Subtype.val : {v : W₁ // v ≠ v₀} → W₁)) ⟨u₀, hu₀_ne⟩
      (G.induce (S : Set V)))
    (x_sub : ↥(S : Set V))
    (hx_fiber : x_sub ∈ substFiber (H.comap (Subtype.val : {v : W₁ // v ≠ v₀} → W₁)) ⟨u₀, hu₀_ne⟩
      (G.induce (S : Set V)) φ)
    (z : V) (hz_not_S : z ∉ S)
    (hz_no_adj : ∀ u : {u : {v : W₁ // v ≠ v₀} // u ≠ ⟨u₀, hu₀_ne⟩}, ¬G.Adj (φ u).1 z)
    (hxz_adj : G.Adj x_sub.1 z) :
    ¬IsInducedSubgraphFree G H := by
  classical
  let H' := H.comap (Subtype.val : {v : W₁ // v ≠ v₀} → W₁)
  let u₀' : {v : W₁ // v ≠ v₀} := ⟨u₀, hu₀_ne⟩
  simp only [baseCopies, mem_filter, mem_univ, true_and] at hφ_base
  simp only [substFiber, mem_filter, mem_univ, true_and] at hx_fiber
  obtain ⟨hx_ne_φ, hx_adj_φ⟩ := hx_fiber
  let g_fun : W₁ → V := fun w =>
    if hw_v : w = v₀ then z
    else if hw_u : w = u₀ then x_sub.1
    else (φ ⟨⟨w, hw_v⟩, fun h => hw_u (congr_arg Subtype.val h)⟩).1
  have hg_v : g_fun v₀ = z := by simp [g_fun]
  have hg_u : g_fun u₀ = x_sub.1 := by simp [g_fun, hu₀_ne]
  have hg_other : ∀ (w : W₁) (hv : w ≠ v₀) (hu : w ≠ u₀),
      g_fun w = (φ ⟨⟨w, hv⟩, fun h => hu (congr_arg Subtype.val h)⟩).1 := by
    intro w hv hu
    simp [g_fun, hv, hu]
  have hg_inj : Function.Injective g_fun := by
    intro w₁ w₂ h_eq
    by_cases hv₁ : w₁ = v₀
    · subst w₁
      rw [hg_v] at h_eq
      by_cases hv₂ : w₂ = v₀
      · exact hv₂.symm
      · by_cases hu₂ : w₂ = u₀
        · subst w₂; rw [hg_u] at h_eq; exact False.elim (hz_not_S (h_eq ▸ x_sub.2))
        · rw [hg_other w₂ hv₂ hu₂] at h_eq; exact False.elim (hz_not_S (h_eq ▸ (φ _).2))
    · by_cases hu₁ : w₁ = u₀
      · subst w₁
        rw [hg_u] at h_eq
        by_cases hv₂ : w₂ = v₀
        · subst w₂; rw [hg_v] at h_eq; exact False.elim (hz_not_S (h_eq.symm ▸ x_sub.2))
        · by_cases hu₂ : w₂ = u₀
          · exact hu₂.symm
          · rw [hg_other w₂ hv₂ hu₂] at h_eq
            exact False.elim (hx_ne_φ _ (Subtype.ext h_eq))
      · rw [hg_other w₁ hv₁ hu₁] at h_eq
        by_cases hv₂ : w₂ = v₀
        · subst w₂; rw [hg_v] at h_eq; exact False.elim (hz_not_S (h_eq.symm ▸ (φ _).2))
        · by_cases hu₂ : w₂ = u₀
          · subst w₂; rw [hg_u] at h_eq
            exact False.elim (hx_ne_φ _ (Subtype.ext h_eq.symm))
          · rw [hg_other w₂ hv₂ hu₂] at h_eq
            exact congr_arg (fun q => q.1.1) (φ.injective (Subtype.ext h_eq))
  intro hG_free
  apply hG_free
  refine ⟨⟨g_fun, hg_inj⟩, ?_⟩
  ext w₁ w₂
  change H.Adj w₁ w₂ ↔ G.Adj (g_fun w₁) (g_fun w₂)
  by_cases hv₁ : w₁ = v₀
  · subst w₁
    rw [hg_v]
    by_cases hv₂ : w₂ = v₀
    · subst w₂; rw [hg_v]; simp
    · by_cases hu₂ : w₂ = u₀
      · subst w₂; rw [hg_u, hv₀_adj u₀, G.adj_comm]; exact iff_of_true rfl hxz_adj
      · rw [hg_other w₂ hv₂ hu₂, hv₀_adj w₂, G.adj_comm]; exact iff_of_false hu₂ (hz_no_adj _)
  · by_cases hu₁ : w₁ = u₀
    · subst w₁
      rw [hg_u]
      by_cases hv₂ : w₂ = v₀
      · subst w₂; rw [hg_v, H.adj_comm, hv₀_adj u₀]; exact iff_of_true rfl hxz_adj
      · by_cases hu₂ : w₂ = u₀
        · subst w₂; rw [hg_u]; simp
        · rw [hg_other w₂ hv₂ hu₂]
          have h_iff := hx_adj_φ ⟨⟨w₂, hv₂⟩, fun h => hu₂ (congr_arg Subtype.val h)⟩
          change G.Adj (φ ⟨⟨w₂, hv₂⟩, _⟩).1 x_sub.1 ↔ H.Adj w₂ u₀ at h_iff
          rw [G.adj_comm, H.adj_comm]
          exact h_iff.symm
    · rw [hg_other w₁ hv₁ hu₁]
      by_cases hv₂ : w₂ = v₀
      · subst w₂; rw [hg_v, H.adj_comm, hv₀_adj w₁]; exact iff_of_false hu₁ (hz_no_adj _)
      · by_cases hu₂ : w₂ = u₀
        · subst w₂; rw [hg_u]
          have h_iff := hx_adj_φ ⟨⟨w₁, hv₁⟩, fun h => hu₁ (congr_arg Subtype.val h)⟩
          change G.Adj (φ ⟨⟨w₁, hv₁⟩, _⟩).1 x_sub.1 ↔ H.Adj w₁ u₀ at h_iff
          exact h_iff.symm
        · rw [hg_other w₂ hv₂ hu₂]
          have h1 := congr_arg (fun (J : SimpleGraph {u : {v : W₁ // v ≠ v₀} // u ≠ u₀'}) =>
            J.Adj ⟨⟨w₁, hv₁⟩, fun h => hu₁ (congr_arg Subtype.val h)⟩
                  ⟨⟨w₂, hv₂⟩, fun h => hu₂ (congr_arg Subtype.val h)⟩) hφ_base
          simpa [H', comap_adj] using h1.symm

/--
**Degree-1 Leaf Extension Pigeonhole Lemma (`leaf_extension_anticomplete_or_viral`)**:
Let $H$ have $|W_1| \ge 3$ and a degree-$1$ leaf $v_0 \in W_1$, and let $\{H - v_0, K\}$ satisfy
`IsPairViralWithExp` with exponent $d \ge 4$. For any $\{H, K\}$-free graph $G$, any $y \in (0, 1/4]$,
and any $y$-sparse subset $F' \subseteq V(G)$ with $y|F'| \ge 1$, either:
- **(Viral)** $F'$ contains a $y^2$-restricted subset $U \subseteq F'$ with $|U| \ge y^{2d+1}|F'|$; or
- **(Pigeonhole)** $F'$ contains disjoint subsets $X, Y \subseteq F'$ with
  $|X| \ge y^{2d|W_1|}|F'|$, $|Y| \ge (1 - |W_1|y)|F'|$, and $(X, Y)$ anticomplete (`IsPurePair`) in $G$.
-/
theorem leaf_extension_anticomplete_or_viral
    {W₁ W₂ : Type*} {V : Type} [Fintype W₁] [DecidableEq W₁]
    [Fintype W₂] [DecidableEq W₂] [Fintype V] [DecidableEq V]
    (H : SimpleGraph W₁) (v₀ : W₁) (K : SimpleGraph W₂) (G : SimpleGraph V)
    (F' : Finset V) {d y : ℝ}
    (hcard₁ : 3 ≤ Fintype.card W₁)
    (hdeg₁ : (neighborFinsetIn H v₀ Finset.univ).card = 1)
    (hd_ge : 4 ≤ d) (hy0 : 0 < y) (hy_quarter : y ≤ 1 / 4)
    (hyF' : 1 ≤ y * (F'.card : ℝ))
    (hG_H : IsInducedSubgraphFree G H) (hG_K : IsInducedSubgraphFree G K)
    (hF'_sparse : IsEpsSparseOn G F' y)
    (h_viral : IsPairViralWithExp (H.comap (Subtype.val : {v : W₁ // v ≠ v₀} → W₁)) K d) :
    (∃ U ⊆ F', IsEpsRestrictedOn G U (y ^ 2) ∧ y ^ (2 * d + 1) * (F'.card : ℝ) ≤ (U.card : ℝ)) ∨
    (∃ X ⊆ F', ∃ Y ⊆ F', Disjoint X Y ∧
      y ^ (2 * d * (Fintype.card W₁ : ℝ)) * (F'.card : ℝ) ≤ (X.card : ℝ) ∧
      (1 - (Fintype.card W₁ : ℝ) * y) * (F'.card : ℝ) ≤ (Y.card : ℝ) ∧
      IsPurePair G X Y) := by
  classical
  let h₁ := Fintype.card W₁
  let H' := H.comap (Subtype.val : {v : W₁ // v ≠ v₀} → W₁)
  have hH'_card : Fintype.card {v : W₁ // v ≠ v₀} = h₁ - 1 := card_subtype_ne v₀
  obtain ⟨u₀, hu₀_singleton⟩ := Finset.card_eq_one.mp hdeg₁
  have hu₀_mem : u₀ ∈ neighborFinsetIn H v₀ Finset.univ := by
    rw [hu₀_singleton]
    exact mem_singleton_self u₀
  have hv₀_u₀_adj : H.Adj v₀ u₀ := ((mem_neighborFinsetIn_iff H v₀ u₀ Finset.univ).mp hu₀_mem).2
  have hu₀_ne : u₀ ≠ v₀ := (H.ne_of_adj hv₀_u₀_adj).symm
  have hv₀_adj : ∀ w : W₁, H.Adj v₀ w ↔ w = u₀ := by
    intro w
    constructor
    · intro hadj
      have hw_mem : w ∈ neighborFinsetIn H v₀ Finset.univ :=
        (mem_neighborFinsetIn_iff H v₀ w Finset.univ).mpr ⟨mem_univ w, hadj⟩
      rw [hu₀_singleton, mem_singleton] at hw_mem
      exact hw_mem
    · rintro rfl
      exact hv₀_u₀_adj
  let m_S : ℕ := ⌈y * (F'.card : ℝ)⌉₊
  have hm_S_ge : y * (F'.card : ℝ) ≤ (m_S : ℝ) := Nat.le_ceil _
  have hm_S_pos : 1 ≤ m_S := Nat.ceil_pos.mpr (by linarith)
  have hm_S_le_2y : (m_S : ℝ) ≤ 2 * y * (F'.card : ℝ) := by
    have hlt := Nat.ceil_lt_add_one (by positivity : 0 ≤ y * (F'.card : ℝ))
    linarith
  have hm_S_le_F' : m_S ≤ F'.card := by
    have h1 : (m_S : ℝ) ≤ (F'.card : ℝ) := by
      have : 2 * y ≤ 1 := by linarith
      nlinarith
    exact_mod_cast h1
  obtain ⟨S, hSF', hS_card⟩ := exists_subset_card_eq hm_S_le_F'
  have hS_card_r : (S.card : ℝ) = (m_S : ℝ) := by exact_mod_cast hS_card
  have hS_pos_r : (0 : ℝ) < (S.card : ℝ) := by
    rw [hS_card_r]
    exact_mod_cast hm_S_pos
  let G_S := G.induce (S : Set V)
  have hG_S_card : Fintype.card ↥(S : Set V) = S.card := Fintype.card_coe S
  have hy2_pos : 0 < y ^ 2 := by positivity
  have hy2_lt_half : y ^ 2 < 1 / 2 := by nlinarith
  by_cases hc_H' : (indCopyCount H' G_S : ℝ) ≤ ((y ^ 2) ^ d * (S.card : ℝ)) ^ (h₁ - 1)
  · left
    have hG_S_K : IsInducedSubgraphFree G_S K := by
      rintro ⟨f, hf⟩
      apply hG_K
      refine ⟨f.trans (Function.Embedding.subtype _), ?_⟩
      ext a b
      have h1 := congr_arg (fun (J : SimpleGraph W₂) => J.Adj a b) hf
      simpa [G_S, comap_adj] using h1
    have hc_K : (indCopyCount K G_S : ℝ) ≤ ((y ^ 2) ^ d * (Fintype.card ↥(S : Set V) : ℝ)) ^ (Fintype.card W₂) := by
      rw [(indCopyCount_eq_zero_iff K G_S).mpr hG_S_K, Nat.cast_zero]
      positivity
    have hc_H'_coe : (indCopyCount H' G_S : ℝ) ≤
        ((y ^ 2) ^ d * (Fintype.card ↥(S : Set V) : ℝ)) ^ (Fintype.card {v : W₁ // v ≠ v₀}) := by
      rwa [hG_S_card, hH'_card]
    obtain ⟨S_sub, hS_sub_rest, hS_sub_card⟩ :=
      h_viral ↥(S : Set V) G_S (y ^ 2) hy2_pos hy2_lt_half hc_H'_coe hc_K
    rw [hG_S_card] at hS_sub_card
    let emb : ↥(S : Set V) ↪ V := Function.Embedding.subtype _
    let U := S_sub.map emb
    have hUS : U ⊆ S := by
      intro x hx
      rcases mem_map.mp hx with ⟨a, _, rfl⟩
      exact a.2
    refine ⟨U, hUS.trans hSF', isEpsRestrictedOn_map_subtype G S S_sub (y ^ 2) hS_sub_rest, ?_⟩
    rw [card_map]
    have h_pow : y ^ (2 * d + 1) * (F'.card : ℝ) ≤ (y ^ 2) ^ d * (S.card : ℝ) := by
      have h1 : (y ^ 2) ^ d = y ^ (2 * d) := by
        rw [← Real.rpow_natCast y 2, ← Real.rpow_mul hy0.le]
        congr 1
      have h2 : y ^ (2 * d + 1) = y ^ (2 * d) * y := Real.rpow_add_one hy0.ne' (2 * d)
      rw [h1, h2, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hm_S_ge.trans_eq hS_card_r.symm) (by positivity)
    exact h_pow.trans hS_sub_card
  · right
    push_neg at hc_H'
    let u₀' : {v : W₁ // v ≠ v₀} := ⟨u₀, hu₀_ne⟩
    let W₁'' := {u : {v : W₁ // v ≠ v₀} // u ≠ u₀'}
    have hW₁''_card : Fintype.card W₁'' = h₁ - 2 := by
      rw [card_subtype_ne u₀', hH'_card]
      omega
    let Base := baseCopies H' u₀' G_S
    have hBase_card_le : (Base.card : ℝ) ≤ (S.card : ℝ) ^ (h₁ - 2) := by
      have h1 : Base.card ≤ Fintype.card (W₁'' ↪ ↥(S : Set V)) := card_filter_le _ _
      have h2 : Fintype.card (W₁'' ↪ ↥(S : Set V)) ≤ Fintype.card (W₁'' → ↥(S : Set V)) :=
        Fintype.card_le_of_injective _ DFunLike.coe_injective
      have h3 : Fintype.card (W₁'' → ↥(S : Set V)) = S.card ^ (h₁ - 2) := by
        rw [Fintype.card_fun, hG_S_card, hW₁''_card]
      exact_mod_cast (h1.trans (h2.trans_eq h3))
    have h_sum_eq : (indCopyCount H' G_S : ℝ) =
        ∑ φ ∈ Base, ((substFiber H' u₀' G_S φ).card : ℝ) := by
      exact_mod_cast indCopyCount_eq_sum_substFiber H' u₀' G_S
    have hBase_ne : Base.Nonempty := by
      by_contra h_empty
      rw [not_nonempty_iff_eq_empty] at h_empty
      rw [h_empty, sum_empty] at h_sum_eq
      have : 0 ≤ ((y ^ 2) ^ d * (S.card : ℝ)) ^ (h₁ - 1) := by positivity
      linarith
    obtain ⟨φ_star, hφ_star_mem, hφ_star_max⟩ :=
      Finset.exists_max_image Base (fun φ => (substFiber H' u₀' G_S φ).card) hBase_ne
    let X_sub := substFiber H' u₀' G_S φ_star
    have h_sum_le_max : (indCopyCount H' G_S : ℝ) ≤ (S.card : ℝ) ^ (h₁ - 2) * (X_sub.card : ℝ) := by
      rw [h_sum_eq]
      calc ∑ φ ∈ Base, ((substFiber H' u₀' G_S φ).card : ℝ)
        _ ≤ ∑ _φ ∈ Base, (X_sub.card : ℝ) := by
          refine sum_le_sum (fun φ hφ => ?_)
          exact_mod_cast hφ_star_max φ hφ
        _ = (Base.card : ℝ) * (X_sub.card : ℝ) := by rw [sum_const, nsmul_eq_mul]
        _ ≤ (S.card : ℝ) ^ (h₁ - 2) * (X_sub.card : ℝ) :=
          mul_le_mul_of_nonneg_right hBase_card_le (Nat.cast_nonneg _)
    have hX_sub_ge : ((y ^ 2) ^ d) ^ (h₁ - 1) * (S.card : ℝ) ≤ (X_sub.card : ℝ) := by
      have hh₁_split : h₁ - 1 = (h₁ - 2) + 1 := by omega
      have h_lhs_split : ((y ^ 2) ^ d * (S.card : ℝ)) ^ (h₁ - 1) =
          (S.card : ℝ) ^ (h₁ - 2) * (((y ^ 2) ^ d) ^ (h₁ - 1) * (S.card : ℝ)) := by
        rw [mul_pow]
        conv_lhs => rhs; rw [hh₁_split, pow_succ]
        ring
      have h_lt : (S.card : ℝ) ^ (h₁ - 2) * (((y ^ 2) ^ d) ^ (h₁ - 1) * (S.card : ℝ)) <
          (S.card : ℝ) ^ (h₁ - 2) * (X_sub.card : ℝ) := by
        linarith [hc_H', h_sum_le_max]
      exact (lt_of_mul_lt_mul_left h_lt (by positivity)).le
    have hX_ge_F' : y ^ (2 * d * (h₁ : ℝ)) * (F'.card : ℝ) ≤ (X_sub.card : ℝ) := by
      have hy_le_one : y ≤ 1 := by linarith
      have h_pow_eq : ((y ^ 2) ^ d) ^ (h₁ - 1) * y = y ^ (2 * d * ((h₁ - 1 : ℕ) : ℝ) + 1) := by
        rw [← Real.rpow_natCast y 2, ← Real.rpow_mul hy0.le, ← Real.rpow_natCast _ (h₁ - 1),
          ← Real.rpow_mul hy0.le, ← Real.rpow_add_one hy0.ne']
        congr 1
      have h_exp_le : 2 * d * ((h₁ - 1 : ℕ) : ℝ) + 1 ≤ 2 * d * (h₁ : ℝ) := by
        have : ((h₁ - 1 : ℕ) : ℝ) = (h₁ : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ h₁), Nat.cast_one]
        rw [this]
        linarith
      calc y ^ (2 * d * (h₁ : ℝ)) * (F'.card : ℝ)
        _ ≤ y ^ (2 * d * ((h₁ - 1 : ℕ) : ℝ) + 1) * (F'.card : ℝ) :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_exponent_ge hy0 hy_le_one h_exp_le) (Nat.cast_nonneg _)
        _ = ((y ^ 2) ^ d) ^ (h₁ - 1) * (y * (F'.card : ℝ)) := by rw [← h_pow_eq]; ring
        _ ≤ ((y ^ 2) ^ d) ^ (h₁ - 1) * (S.card : ℝ) :=
          mul_le_mul_of_nonneg_left (hm_S_ge.trans_eq hS_card_r.symm) (by positivity)
        _ ≤ (X_sub.card : ℝ) := hX_sub_ge
    let emb : ↥(S : Set V) ↪ V := Function.Embedding.subtype _
    let X := X_sub.map emb
    have hXS : X ⊆ S := by
      intro v hv
      rcases mem_map.mp hv with ⟨a, _, rfl⟩
      exact a.2
    let Im_φ := (Finset.univ : Finset W₁'').map (φ_star.trans emb)
    have hIm_φ_S : Im_φ ⊆ S := by
      intro v hv
      rcases mem_map.mp hv with ⟨a, _, rfl⟩
      exact (φ_star a).2
    have hIm_φ_F' : Im_φ ⊆ F' := hIm_φ_S.trans hSF'
    have hIm_φ_card : Im_φ.card = h₁ - 2 := by
      rw [card_map, card_univ, hW₁''_card]
    let Bad_Y := Im_φ.biUnion (fun w => neighborFinsetIn G w F')
    have hBad_Y_card : (Bad_Y.card : ℝ) ≤ ((h₁ - 2 : ℕ) : ℝ) * (y * (F'.card : ℝ)) := by
      have h1 : (Bad_Y.card : ℝ) ≤ ∑ w ∈ Im_φ, ((neighborFinsetIn G w F').card : ℝ) := by
        exact_mod_cast card_biUnion_le
      calc (Bad_Y.card : ℝ)
        _ ≤ ∑ w ∈ Im_φ, ((neighborFinsetIn G w F').card : ℝ) := h1
        _ ≤ ∑ _w ∈ Im_φ, y * (F'.card : ℝ) :=
          sum_le_sum (fun w hw => hF'_sparse w (hIm_φ_F' hw))
        _ = (Im_φ.card : ℝ) * (y * (F'.card : ℝ)) := by rw [sum_const, nsmul_eq_mul]
        _ = ((h₁ - 2 : ℕ) : ℝ) * (y * (F'.card : ℝ)) := by rw [hIm_φ_card]
    let Y := (F' \ S) \ Bad_Y
    have hYF' : Y ⊆ F' := sdiff_subset.trans sdiff_subset
    have hdisj_XY : Disjoint X Y := by
      rw [Finset.disjoint_left]
      intro v hvX hvY
      have hvS : v ∈ S := hXS hvX
      have hv_not_S : v ∉ S := (mem_sdiff.mp (sdiff_subset hvY)).2
      exact hv_not_S hvS
    have hY_card : (1 - (h₁ : ℝ) * y) * (F'.card : ℝ) ≤ (Y.card : ℝ) := by
      have h_sub : F' ⊆ Y ∪ (S ∪ Bad_Y) := by
        intro v hvF'
        rw [mem_union, mem_union]
        by_cases hvS : v ∈ S
        · exact Or.inr (Or.inl hvS)
        · by_cases hvBad : v ∈ Bad_Y
          · exact Or.inr (Or.inr hvBad)
          · exact Or.inl (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hvF', hvS⟩, hvBad⟩)
      have h_nat : F'.card ≤ Y.card + S.card + Bad_Y.card := by
        calc F'.card
          _ ≤ (Y ∪ (S ∪ Bad_Y)).card := card_le_card h_sub
          _ ≤ Y.card + (S ∪ Bad_Y).card := card_union_le _ _
          _ ≤ Y.card + (S.card + Bad_Y.card) := Nat.add_le_add_left (card_union_le _ _) _
          _ = Y.card + S.card + Bad_Y.card := by omega
      have h_real : (F'.card : ℝ) ≤ (Y.card : ℝ) + (S.card : ℝ) + (Bad_Y.card : ℝ) := by
        exact_mod_cast h_nat
      have hh₁_sub2 : ((h₁ - 2 : ℕ) : ℝ) = (h₁ : ℝ) - 2 := by
        rw [Nat.cast_sub (by omega : 2 ≤ h₁), Nat.cast_two]
      rw [hh₁_sub2] at hBad_Y_card
      rw [hS_card_r] at h_real
      linarith
    have hanti_XY : IsAnticompletePair G X Y := by
      intro x hxX z hzY hxz_adj
      rcases mem_map.mp hxX with ⟨x_sub, hx_sub, rfl⟩
      simp only [Y, mem_sdiff] at hzY
      obtain ⟨⟨hzF', hz_not_S⟩, hz_not_Bad⟩ := hzY
      have hz_no_adj : ∀ u : W₁'', ¬G.Adj (φ_star u).1 z := by
        intro u hadj
        apply hz_not_Bad
        simp only [Bad_Y, mem_biUnion, mem_neighborFinsetIn_iff]
        refine ⟨(φ_star u).1, ?_, hzF', hadj⟩
        exact mem_map.mpr ⟨u, mem_univ u, rfl⟩
      exact not_isInducedSubgraphFree_of_leaf_extension H v₀ u₀ hu₀_ne hv₀_adj G S
        φ_star hφ_star_mem x_sub hx_sub z hz_not_S hz_no_adj hxz_adj hG_H
    refine ⟨X, hXS.trans hSF', Y, hYF', hdisj_XY, ?_, hY_card, Or.inr hanti_XY⟩
    rw [card_map]
    exact hX_ge_F'

/-! #### Part 5.3: Step 2a (Blockade vs. Deeper Viral Descent) and Step 2b (Multi-Scale Reduction) -/

/--
**Step 2a (`leaf_sparse_blockade_or_viral`)**:
On a $\lambda$-sparse $\{H, K\}$-free subgraph $F_t$ ($\lambda \le 2^{-16b}$, $y = 2^{4b}\lambda$,
$y^{a+2}|F_t| \ge 1$), either $F_t$ contains a $\lambda^{3/2}$-restricted subset $U \subseteq F_t$
of size $\ge \lambda^{2d+2}|F_t|$, or `blockade_iteration_pure` extracts a complete or anticomplete
$(\lceil y^{-1}\rceil, y^{a+2}|F_t|)$-blockade in $F_t$.
-/
private theorem leaf_sparse_blockade_or_viral
    {W₁ W₂ : Type*} {V : Type} [Fintype W₁] [DecidableEq W₁]
    [Fintype W₂] [DecidableEq W₂] [Fintype V] [DecidableEq V]
    (H : SimpleGraph W₁) (v₀ : W₁) (K : SimpleGraph W₂) (G : SimpleGraph V)
    (F_t : Finset V) {d a b lam y : ℝ}
    (hcard₁ : 3 ≤ Fintype.card W₁)
    (hdeg₁ : (neighborFinsetIn H v₀ Finset.univ).card = 1)
    (hd_ge : 4 ≤ d) (hb_ge : (Fintype.card W₁ : ℝ) ≤ b) (ha_def : a = 2 * d * b)
    (hlam_pos : 0 < lam) (hlam_le : lam ≤ (2 : ℝ) ^ (-16 * b))
    (hy_def : y = (2 : ℝ) ^ (4 * b) * lam)
    (hw₀ : 1 ≤ y ^ (a + 2) * (F_t.card : ℝ))
    (hG_H : IsInducedSubgraphFree G H) (hG_K : IsInducedSubgraphFree G K)
    (hFt_sparse : IsEpsSparseOn G F_t lam)
    (h_viral : IsPairViralWithExp (H.comap (Subtype.val : {v : W₁ // v ≠ v₀} → W₁)) K d) :
    (∃ U ⊆ F_t, IsEpsRestrictedOn G U (lam ^ (3 / 2 : ℝ)) ∧
      lam ^ (2 * d + 2) * (F_t.card : ℝ) ≤ (U.card : ℝ)) ∨
    (∃ B : Fin ⌈y⁻¹⌉₊ → Finset V,
      IsCompleteBlockadeIn G F_t ⌈y⁻¹⌉₊ (y ^ (a + 2) * (F_t.card : ℝ)) B ∨
      IsAnticompleteBlockadeIn G F_t ⌈y⁻¹⌉₊ (y ^ (a + 2) * (F_t.card : ℝ)) B) := by
  have hb3 : 3 ≤ b := le_trans (by exact_mod_cast hcard₁) hb_ge
  have ha1 : 1 ≤ a := by rw [ha_def]; nlinarith
  have hy0 : 0 < y := by rw [hy_def]; positivity
  have hy_le_12b : y ≤ (2 : ℝ) ^ (-12 * b) := by
    rw [hy_def]
    calc (2 : ℝ) ^ (4 * b) * lam
      _ ≤ (2 : ℝ) ^ (4 * b) * (2 : ℝ) ^ (-16 * b) :=
        mul_le_mul_of_nonneg_left hlam_le (by positivity)
      _ = (2 : ℝ) ^ (-12 * b) := by
        rw [← Real.rpow_add two_pos]
        congr 1; ring
  have hyc : y ≤ (2 : ℝ) ^ (-4 * b) :=
    hy_le_12b.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
  have hy_quarter : y ≤ 1 / 4 := by
    calc y
      _ ≤ (2 : ℝ) ^ (-4 * b) := hyc
      _ ≤ (2 : ℝ) ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 1 / 4 := by norm_num
  have hy_lt_one : y < 1 := by linarith
  by_cases h_exists_viral : ∃ F' ⊆ F_t, (2 : ℝ) ^ (-4 * b) * (F_t.card : ℝ) ≤ (F'.card : ℝ) ∧
      ∃ U ⊆ F', IsEpsRestrictedOn G U (y ^ 2) ∧ y ^ (2 * d + 1) * (F'.card : ℝ) ≤ (U.card : ℝ)
  · left
    obtain ⟨F', hF'_sub, hF'_card, U, hUF', hU_rest, hU_card⟩ := h_exists_viral
    have hy2_le_lam32 : y ^ 2 ≤ lam ^ (3 / 2 : ℝ) := by
      have h_lam_half : lam ^ (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-8 * b) := by
        calc lam ^ (1 / 2 : ℝ)
          _ ≤ ((2 : ℝ) ^ (-16 * b)) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow hlam_pos.le hlam_le (by positivity)
          _ = (2 : ℝ) ^ (-8 * b) := by
            rw [← Real.rpow_mul two_pos.le]
            congr 1; ring
      have h_prod_one : (2 : ℝ) ^ (8 * b) * lam ^ (1 / 2 : ℝ) ≤ 1 := by
        calc (2 : ℝ) ^ (8 * b) * lam ^ (1 / 2 : ℝ)
          _ ≤ (2 : ℝ) ^ (8 * b) * (2 : ℝ) ^ (-8 * b) :=
            mul_le_mul_of_nonneg_left h_lam_half (by positivity)
          _ = 1 := by
            rw [← Real.rpow_add two_pos]
            have : 8 * b + -8 * b = 0 := by ring
            rw [this, Real.rpow_zero]
      have h_lam2 : lam ^ 2 = lam ^ (1 / 2 : ℝ) * lam ^ (3 / 2 : ℝ) := by
        rw [← Real.rpow_natCast lam 2, ← Real.rpow_add hlam_pos]
        norm_num
      have h_2_8b : ((2 : ℝ) ^ (4 * b)) ^ 2 = (2 : ℝ) ^ (8 * b) := by
        rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul two_pos.le]
        congr 1; push_cast; ring
      calc y ^ 2
        _ = ((2 : ℝ) ^ (4 * b)) ^ 2 * lam ^ 2 := by rw [hy_def, mul_pow]
        _ = ((2 : ℝ) ^ (8 * b) * lam ^ (1 / 2 : ℝ)) * lam ^ (3 / 2 : ℝ) := by
          rw [h_2_8b, h_lam2]
          ring
        _ ≤ 1 * lam ^ (3 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right h_prod_one (by positivity)
        _ = lam ^ (3 / 2 : ℝ) := one_mul _
    have hlam_le_y : lam ≤ y := by
      rw [hy_def]
      have : (1 : ℝ) ≤ (2 : ℝ) ^ (4 * b) := Real.one_le_rpow (by norm_num) (by linarith)
      nlinarith
    have hlam_le_2_4b : lam ≤ (2 : ℝ) ^ (-4 * b) :=
      hlam_le.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
    refine ⟨U, hUF'.trans hF'_sub, hU_rest.mono hy2_le_lam32, ?_⟩
    calc lam ^ (2 * d + 2) * (F_t.card : ℝ)
      _ = lam ^ (2 * d + 1) * (lam * (F_t.card : ℝ)) := by
        rw [show 2 * d + 2 = (2 * d + 1) + 1 by ring, Real.rpow_add_one hlam_pos.ne', mul_assoc]
      _ ≤ y ^ (2 * d + 1) * ((2 : ℝ) ^ (-4 * b) * (F_t.card : ℝ)) := by
        refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
        · exact Real.rpow_le_rpow hlam_pos.le hlam_le_y (by linarith)
        · exact mul_le_mul_of_nonneg_right hlam_le_2_4b (Nat.cast_nonneg _)
      _ ≤ y ^ (2 * d + 1) * (F'.card : ℝ) :=
        mul_le_mul_of_nonneg_left hF'_card (by positivity)
      _ ≤ (U.card : ℝ) := hU_card
  · right
    push_neg at h_exists_viral
    have hstep : ∀ F' ⊆ F_t, (2 : ℝ) ^ (-4 * b) * (F_t.card : ℝ) ≤ (F'.card : ℝ) →
        ∃ X ⊆ F', ∃ Y ⊆ F', Disjoint X Y ∧
          y ^ a * (F'.card : ℝ) ≤ (X.card : ℝ) ∧
          (1 - b * y) * (F'.card : ℝ) ≤ (Y.card : ℝ) ∧
          IsPurePair G X Y := by
      intro F' hF'_sub hF'_card
      have hF'_sparse : IsEpsSparseOn G F' y := by
        intro v hv
        have h_sub_n := neighborFinsetIn_mono_ambient G v hF'_sub
        have h_le : ((neighborFinsetIn G v F').card : ℝ) ≤ ((neighborFinsetIn G v F_t).card : ℝ) := by
          exact_mod_cast card_le_card h_sub_n
        have h_cancel : (2 : ℝ) ^ (4 * b) * (2 : ℝ) ^ (-4 * b) = 1 := by
          rw [← Real.rpow_add two_pos]
          have : 4 * b + -4 * b = 0 := by ring
          rw [this, Real.rpow_zero]
        calc ((neighborFinsetIn G v F').card : ℝ)
          _ ≤ lam * (F_t.card : ℝ) := h_le.trans (hFt_sparse v (hF'_sub hv))
          _ = y * ((2 : ℝ) ^ (-4 * b) * (F_t.card : ℝ)) := by
            rw [hy_def]
            calc lam * (F_t.card : ℝ)
              _ = ((2 : ℝ) ^ (4 * b) * (2 : ℝ) ^ (-4 * b)) * lam * (F_t.card : ℝ) := by
                rw [h_cancel, one_mul]
              _ = ((2 : ℝ) ^ (4 * b) * lam) * ((2 : ℝ) ^ (-4 * b) * (F_t.card : ℝ)) := by ring
          _ ≤ y * (F'.card : ℝ) := mul_le_mul_of_nonneg_left hF'_card hy0.le
      have hyF' : 1 ≤ y * (F'.card : ℝ) := by
        have hya1_le : y ^ (a + 1) ≤ (2 : ℝ) ^ (-4 * b) := by
          have : y ^ (a + 1) ≤ y ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge hy0 hy_lt_one.le (by linarith)
          rw [Real.rpow_one] at this
          exact this.trans hyc
        calc (1 : ℝ)
          _ ≤ y ^ (a + 2) * (F_t.card : ℝ) := hw₀
          _ = y * (y ^ (a + 1) * (F_t.card : ℝ)) := by
            have : a + 2 = (a + 1) + 1 := by ring
            rw [this, Real.rpow_add_one hy0.ne']
            ring
          _ ≤ y * ((2 : ℝ) ^ (-4 * b) * (F_t.card : ℝ)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hya1_le (Nat.cast_nonneg _)) hy0.le
          _ ≤ y * (F'.card : ℝ) := mul_le_mul_of_nonneg_left hF'_card hy0.le
      rcases leaf_extension_anticomplete_or_viral H v₀ K G F' hcard₁ hdeg₁ hd_ge
          hy0 hy_quarter hyF' hG_H hG_K hF'_sparse h_viral with
        ⟨U, hUF', hU_rest, hU_card⟩ | ⟨X, hXF', Y, hYF', hdisj, hX_card, hY_card, hpure⟩
      · linarith [h_exists_viral F' hF'_sub hF'_card U hUF' hU_rest, hU_card]
      · refine ⟨X, hXF', Y, hYF', hdisj, ?_, ?_, hpure⟩
        · have h_exp : 2 * d * (Fintype.card W₁ : ℝ) ≤ a := by
            rw [ha_def]
            exact mul_le_mul_of_nonneg_left hb_ge (by positivity)
          exact (mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_exponent_ge hy0 hy_lt_one.le h_exp)
            (Nat.cast_nonneg _)).trans hX_card
        · have h_coeff : 1 - b * y ≤ 1 - (Fintype.card W₁ : ℝ) * y := by
            nlinarith [hb_ge, hy0]
          exact (mul_le_mul_of_nonneg_right h_coeff (Nat.cast_nonneg _)).trans hY_card
    rcases blockade_iteration_pure G F_t a b y ha1 (by linarith) hy0 hyc hw₀ hstep with
      ⟨B, hB⟩ | ⟨B, hB⟩
    · exact ⟨B, Or.inl hB⟩
    · exact ⟨B, Or.inr hB⟩

/--
Combined Step 2a (`leaf_coleaf_single_scale_step`) for $\lambda$-restricted subsets $F_t$
(handling both $\lambda$-sparse and $\lambda$-co-sparse branches by duality).
-/
private theorem leaf_coleaf_single_scale_step
    {W₁ W₂ : Type*} {V : Type} [Fintype W₁] [DecidableEq W₁]
    [Fintype W₂] [DecidableEq W₂] [Fintype V] [DecidableEq V]
    (H : SimpleGraph W₁) (v₀ : W₁) (J : SimpleGraph W₂) (w₀ : W₂) (G : SimpleGraph V)
    (F_t : Finset V) {d a b lam y : ℝ}
    (hcard₁ : 3 ≤ Fintype.card W₁) (hcard₂ : 3 ≤ Fintype.card W₂)
    (hdeg₁ : (neighborFinsetIn H v₀ Finset.univ).card = 1)
    (hdeg₂ : (neighborFinsetIn J w₀ Finset.univ).card = 1)
    (hd_ge : 4 ≤ d)
    (hb_ge₁ : (Fintype.card W₁ : ℝ) ≤ b) (hb_ge₂ : (Fintype.card W₂ : ℝ) ≤ b)
    (ha_def : a = 2 * d * b)
    (hlam_pos : 0 < lam) (hlam_le : lam ≤ (2 : ℝ) ^ (-16 * b))
    (hy_def : y = (2 : ℝ) ^ (4 * b) * lam)
    (hw₀ : 1 ≤ y ^ (a + 2) * (F_t.card : ℝ))
    (hG_H : IsInducedSubgraphFree G H) (hG_Jc : IsInducedSubgraphFree G Jᶜ)
    (hFt_rest : IsEpsRestrictedOn G F_t lam)
    (h_viral₁ : IsPairViralWithExp (H.comap (Subtype.val : {v : W₁ // v ≠ v₀} → W₁)) Jᶜ d)
    (h_viral₂ : IsPairViralWithExp (J.comap (Subtype.val : {w : W₂ // w ≠ w₀} → W₂)) Hᶜ d) :
    (∃ U ⊆ F_t, IsEpsRestrictedOn G U (lam ^ (3 / 2 : ℝ)) ∧
      lam ^ (2 * d + 2) * (F_t.card : ℝ) ≤ (U.card : ℝ)) ∨
    (∃ B : Fin ⌈y⁻¹⌉₊ → Finset V,
      IsCompleteBlockadeIn G F_t ⌈y⁻¹⌉₊ (y ^ (a + 2) * (F_t.card : ℝ)) B ∨
      IsAnticompleteBlockadeIn G F_t ⌈y⁻¹⌉₊ (y ^ (a + 2) * (F_t.card : ℝ)) B) := by
  rcases hFt_rest with hFt_sp | hFt_cosp
  · exact leaf_sparse_blockade_or_viral H v₀ Jᶜ G F_t hcard₁ hdeg₁ hd_ge hb_ge₁ ha_def
      hlam_pos hlam_le hy_def hw₀ hG_H hG_Jc hFt_sp h_viral₁
  · have hGc_J : IsInducedSubgraphFree Gᶜ J := by
      rwa [isInducedSubgraphFree_compl_iff, compl_compl] at hG_Jc
    have hGc_Hc : IsInducedSubgraphFree Gᶜ Hᶜ :=
      (isInducedSubgraphFree_compl_iff G H).mp hG_H
    rcases leaf_sparse_blockade_or_viral J w₀ Hᶜ Gᶜ F_t hcard₂ hdeg₂ hd_ge hb_ge₂ ha_def
        hlam_pos hlam_le hy_def hw₀ hGc_J hGc_Hc hFt_cosp h_viral₂ with
      ⟨U, hUF_t, hU_rest_c, hU_card⟩ | ⟨B, hB_c⟩
    · left
      refine ⟨U, hUF_t, ?_, hU_card⟩
      rcases hU_rest_c with h1 | h2
      · exact Or.inr h1
      · rw [compl_compl] at h2
        exact Or.inl h2
    · right
      refine ⟨B, ?_⟩
      rcases hB_c with hcomp | hanti
      · exact Or.inr (isAnticompleteBlockadeIn_iff_compl.mpr hcomp)
      · rw [isAnticompleteBlockadeIn_iff_compl, compl_compl] at hanti
        exact Or.inl hanti

/--
Polynomial blockade width upgrade for Step 2b of Theorem 4(2) (`main.tex`, line 183):
For $k = \lceil y^{-1} \rceil \ge 2$ and $C_1 = 32 b b_2 + 6 b b_2 + a + 4$, translates the
local blockade width $y^{a+2}|F_t|$ inside $F_t$ ($\lambda^{b_2}|F_0| \le |F_t|$ and
$\lambda_0^{b_2}|F| \le |F_0|$) into the global polynomial width $|F| / k^{C_1}$.
-/
private theorem leaf_coleaf_blockade_width_upgrade
    {a b b₂ C₁ lam0 lam y F_card F₀_card F_t_card : ℝ} {k : ℕ}
    (hb3 : 3 ≤ b) (ha1 : 1 ≤ a) (hb₂_pos : 0 < b₂)
    (hC₁_def : C₁ = 32 * b * b₂ + 6 * b * b₂ + a + 4)
    (hlam0_def : lam0 = (2 : ℝ) ^ (-16 * b))
    (hlam_pos : 0 < lam) (hy0 : 0 < y)
    (hy_def : y = (2 : ℝ) ^ (4 * b) * lam)
    (hk2 : 2 ≤ k) (hk_ge_inv : y⁻¹ ≤ (k : ℝ))
    (hF_nonneg : 0 ≤ F_card)
    (hF₀_card : lam0 ^ b₂ * F_card ≤ F₀_card)
    (hFt_card : lam ^ b₂ * F₀_card ≤ F_t_card) :
    F_card / (k : ℝ) ^ C₁ ≤ y ^ (a + 2) * F_t_card := by
  have hk_r : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  have hk_inv_le_y : (k : ℝ) ^ (-1 : ℝ) ≤ y := by
    rw [Real.rpow_neg_one]
    exact (inv_le_comm₀ hy0 hk_pos).mp hk_ge_inv
  have hk_4b_le : (k : ℝ) ^ (-4 * b) ≤ (2 : ℝ) ^ (-4 * b) := by
    rw [show -4 * b = -(4 * b) by ring, Real.rpow_neg hk_pos.le, Real.rpow_neg two_pos.le]
    exact inv_anti₀ (by positivity) (Real.rpow_le_rpow two_pos.le hk_r (by linarith))
  have hk_lam : (k : ℝ) ^ (-(4 * b + 1)) ≤ lam := by
    have h1 : (k : ℝ) ^ (-(4 * b + 1)) = (k : ℝ) ^ (-4 * b) * (k : ℝ) ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hk_pos]
      congr 1; ring
    have h2 : (2 : ℝ) ^ (-4 * b) * y = lam := by
      rw [hy_def, ← mul_assoc, ← Real.rpow_add two_pos]
      have : -4 * b + 4 * b = 0 := by ring
      rw [this, Real.rpow_zero, one_mul]
    rw [h1, ← h2]
    exact mul_le_mul hk_4b_le hk_inv_le_y (by positivity) (by positivity)
  have hk_lam0 : (k : ℝ) ^ (-16 * b) ≤ lam0 := by
    rw [hlam0_def, show -16 * b = -(16 * b) by ring,
      Real.rpow_neg hk_pos.le, Real.rpow_neg two_pos.le]
    exact inv_anti₀ (by positivity) (Real.rpow_le_rpow two_pos.le hk_r (by linarith))
  rw [div_le_iff₀ (by positivity)]
  have h_y_a2 : (k : ℝ) ^ (-(a + 2)) ≤ y ^ (a + 2) := by
    have h1 : (k : ℝ) ^ (-(a + 2)) = ((k : ℝ) ^ (-1 : ℝ)) ^ (a + 2) := by
      rw [← Real.rpow_mul hk_pos.le]
      congr 1; ring
    rw [h1]
    exact Real.rpow_le_rpow (by positivity) hk_inv_le_y (by linarith)
  have h_lam_b2 : (k : ℝ) ^ (-(4 * b + 1) * b₂) ≤ lam ^ b₂ := by
    have h1 : (k : ℝ) ^ (-(4 * b + 1) * b₂) = ((k : ℝ) ^ (-(4 * b + 1))) ^ b₂ := by
      rw [← Real.rpow_mul hk_pos.le]
    rw [h1]
    exact Real.rpow_le_rpow (by positivity) hk_lam hb₂_pos.le
  have h_lam0_b2 : (k : ℝ) ^ (-16 * b * b₂) ≤ lam0 ^ b₂ := by
    have h1 : (k : ℝ) ^ (-16 * b * b₂) = ((k : ℝ) ^ (-16 * b)) ^ b₂ := by
      rw [← Real.rpow_mul hk_pos.le]
    rw [h1]
    exact Real.rpow_le_rpow (by positivity) hk_lam0 hb₂_pos.le
  let E := (a + 2) + (4 * b + 1) * b₂ + 16 * b * b₂
  have hE_le_C₁ : E ≤ C₁ := by
    rw [hC₁_def]
    dsimp [E]
    linarith [mul_le_mul_of_nonneg_right hb3 hb₂_pos.le]
  have hk_neg_E_F : (k : ℝ) ^ (-E) * F_card ≤ y ^ (a + 2) * F_t_card := by
    have h_split : (k : ℝ) ^ (-E) =
        (k : ℝ) ^ (-(a + 2)) * ((k : ℝ) ^ (-(4 * b + 1) * b₂) * (k : ℝ) ^ (-16 * b * b₂)) := by
      rw [← Real.rpow_add hk_pos, ← Real.rpow_add hk_pos]
      congr 1; dsimp [E]; ring
    rw [h_split]
    have hp1 := mul_le_mul h_lam_b2 h_lam0_b2 (by positivity) (by positivity)
    have hp2 := mul_le_mul h_y_a2 hp1 (by positivity) (by positivity)
    calc (k : ℝ) ^ (-(a + 2)) * ((k : ℝ) ^ (-(4 * b + 1) * b₂) * (k : ℝ) ^ (-16 * b * b₂)) * F_card
      _ ≤ (y ^ (a + 2) * (lam ^ b₂ * lam0 ^ b₂)) * F_card :=
        mul_le_mul_of_nonneg_right hp2 hF_nonneg
      _ = y ^ (a + 2) * (lam ^ b₂ * (lam0 ^ b₂ * F_card)) := by ring
      _ ≤ y ^ (a + 2) * (lam ^ b₂ * F₀_card) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hF₀_card (by positivity)) (by positivity)
      _ ≤ y ^ (a + 2) * F_t_card :=
        mul_le_mul_of_nonneg_left hFt_card (by positivity)
  have hk_E_C1 : (k : ℝ) ^ E ≤ (k : ℝ) ^ C₁ :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hE_le_C₁
  calc F_card
    _ = ((k : ℝ) ^ (-E) * F_card) * (k : ℝ) ^ E := by
      rw [mul_assoc, mul_comm F_card, ← mul_assoc, ← Real.rpow_add hk_pos,
        neg_add_cancel, Real.rpow_zero, one_mul]
    _ ≤ (y ^ (a + 2) * F_t_card) * (k : ℝ) ^ C₁ :=
      mul_le_mul hk_neg_E_F hk_E_C1 (by positivity)
        ((by positivity : 0 ≤ (k : ℝ) ^ (-E) * F_card).trans hk_neg_E_F)

/--
Multi-scale dichotomy helper for Step 2b: establishes the `h_multiscale` hypothesis of
`stage2_reduction` on every subset $F \subseteq V$ of an $\{H, Jᶜ\}$-free graph $G$ ($|V| \ge 1$).
-/
private theorem leaf_coleaf_multiscale_dichotomy
    {W₁ W₂ : Type*} {V : Type} [Fintype W₁] [DecidableEq W₁]
    [Fintype W₂] [DecidableEq W₂] [Fintype V] [DecidableEq V]
    (H : SimpleGraph W₁) (v₀ : W₁) (J : SimpleGraph W₂) (w₀ : W₂) (G : SimpleGraph V)
    {d a b lam0 b₂_init b₂ C₁ : ℝ}
    (hcard₁ : 3 ≤ Fintype.card W₁) (hcard₂ : 3 ≤ Fintype.card W₂)
    (hdeg₁ : (neighborFinsetIn H v₀ Finset.univ).card = 1)
    (hdeg₂ : (neighborFinsetIn J w₀ Finset.univ).card = 1)
    (hd_ge : 4 ≤ d)
    (hb_ge₁ : (Fintype.card W₁ : ℝ) ≤ b) (hb_ge₂ : (Fintype.card W₂ : ℝ) ≤ b)
    (ha_def : a = 2 * d * b)
    (hlam0_def : lam0 = (2 : ℝ) ^ (-16 * b))
    (h_rodl_b2 : lam0 ^ b₂_init ≤ rodlDeltaGen (Fintype.card W₁) lam0)
    (hb₂_init_pos : 1 ≤ b₂_init)
    (hb₂_def : b₂ = max (2 * (2 * d + 2)) b₂_init)
    (hC₁_def : C₁ = 32 * b * b₂ + 6 * b * b₂ + a + 4)
    (hkappa : 1 ≤ kappa G)
    (hG_H : IsInducedSubgraphFree G H) (hG_Jc : IsInducedSubgraphFree G Jᶜ)
    (h_viral₁ : IsPairViralWithExp (H.comap (Subtype.val : {v : W₁ // v ≠ v₀} → W₁)) Jᶜ d)
    (h_viral₂ : IsPairViralWithExp (J.comap (Subtype.val : {w : W₂ // w ≠ w₀} → W₂)) Hᶜ d) :
    ∀ x : ℝ, 0 < x → x < 1 / 2 → ∀ F ⊆ (Finset.univ : Finset V),
      (∃ S ⊆ F, IsEpsRestrictedOn G S x ∧ x ^ C₁ * (F.card : ℝ) ≤ (S.card : ℝ)) ∨
      (∃ k : ℕ, 2 ≤ k ∧ ∃ B : Fin k → Finset V,
        IsCompleteBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ C₁) B ∨
        IsAnticompleteBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ C₁) B) ∨
      (x ^ C₁ * (F.card : ℝ)) ^ (1 : ℝ) ≤ (kappa G : ℝ) := by
  have hb3 : 3 ≤ b := le_trans (by exact_mod_cast hcard₁) hb_ge₁
  have ha1 : 1 ≤ a := by rw [ha_def]; nlinarith
  have hb₂_ge_init : b₂_init ≤ b₂ := by rw [hb₂_def]; exact le_max_right _ _
  have hb₂_ge_2b₃ : 2 * (2 * d + 2) ≤ b₂ := by rw [hb₂_def]; exact le_max_left _ _
  have hb₂_pos : 0 < b₂ := lt_of_lt_of_le zero_lt_one (hb₂_init_pos.trans hb₂_ge_init)
  have h_bb2 : 0 ≤ b * b₂ := by positivity
  have hlam0_pos : 0 < lam0 := by rw [hlam0_def]; positivity
  have hlam0_lt_half : lam0 < 1 / 2 := by
    rw [hlam0_def]
    calc (2 : ℝ) ^ (-16 * b)
      _ ≤ (2 : ℝ) ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ < 1 / 2 := by norm_num
  have hlam0_le_one : lam0 ≤ 1 := by linarith
  have hkappa_r : (1 : ℝ) ≤ (kappa G : ℝ) := by exact_mod_cast hkappa
  intro x hx_pos hx_half F _hF_univ
  have hx_le_one : x ≤ 1 := by linarith
  obtain ⟨F₀, hF₀_sub, hF₀_rest, hF₀_card_δ⟩ :=
    rodl_theorem_general_subset H G hG_H lam0 hlam0_pos hlam0_lt_half F
  have hF₀_card : lam0 ^ b₂ * (F.card : ℝ) ≤ (F₀.card : ℝ) := by
    have h1 : lam0 ^ b₂ ≤ lam0 ^ b₂_init :=
      Real.rpow_le_rpow_of_exponent_ge hlam0_pos hlam0_le_one hb₂_ge_init
    exact (mul_le_mul_of_nonneg_right (h1.trans h_rodl_b2) (Nat.cast_nonneg _)).trans hF₀_card_δ
  by_cases hx_lt : x < lam0
  · let O : Finset V → Prop := fun _ =>
      (∃ k : ℕ, 2 ≤ k ∧ ∃ B : Fin k → Finset V,
        IsCompleteBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ C₁) B ∨
        IsAnticompleteBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ C₁) B) ∨
      (x ^ C₁ * (F.card : ℝ)) ^ (1 : ℝ) ≤ (kappa G : ℝ)
    have hstep : ∀ lam ∈ Set.Icc x lam0, ∀ F_t ⊆ F₀,
        IsEpsRestrictedOn G F_t lam → lam ^ b₂ * (F₀.card : ℝ) ≤ (F_t.card : ℝ) →
          O F_t ∨ ∃ U ⊆ F_t, IsEpsRestrictedOn G U (lam ^ (3 / 2 : ℝ)) ∧
            lam ^ (2 * d + 2) * (F_t.card : ℝ) ≤ (U.card : ℝ) := by
      intro lam hlam_mem F_t hFt_sub hFt_rest hFt_card
      have hlam_ge_x : x ≤ lam := hlam_mem.1
      have hlam_le_lam0 : lam ≤ lam0 := hlam_mem.2
      have hlam_pos : 0 < lam := hx_pos.trans_le hlam_ge_x
      have hlam_le_one : lam ≤ 1 := hlam_le_lam0.trans hlam0_le_one
      have hlam_le_16b : lam ≤ (2 : ℝ) ^ (-16 * b) := hlam0_def ▸ hlam_le_lam0
      let y := (2 : ℝ) ^ (4 * b) * lam
      have hy0 : 0 < y := by dsimp [y]; positivity
      have hy_le_12b : y ≤ (2 : ℝ) ^ (-12 * b) := by
        dsimp [y]
        calc (2 : ℝ) ^ (4 * b) * lam
          _ ≤ (2 : ℝ) ^ (4 * b) * (2 : ℝ) ^ (-16 * b) :=
            mul_le_mul_of_nonneg_left hlam_le_16b (by positivity)
          _ = (2 : ℝ) ^ (-12 * b) := by
            rw [← Real.rpow_add two_pos]
            congr 1; ring
      have hy_lt_half : y < 1 / 2 := by
        calc y
          _ ≤ (2 : ℝ) ^ (-12 * b) := hy_le_12b
          _ ≤ (2 : ℝ) ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ < 1 / 2 := by norm_num
      have hlam_le_y : lam ≤ y := by
        dsimp [y]
        have : (1 : ℝ) ≤ (2 : ℝ) ^ (4 * b) := Real.one_le_rpow (by norm_num) (by linarith)
        nlinarith
      by_cases hw₀ : 1 ≤ y ^ (a + 2) * (F_t.card : ℝ)
      · rcases leaf_coleaf_single_scale_step H v₀ J w₀ G F_t hcard₁ hcard₂ hdeg₁ hdeg₂
            hd_ge hb_ge₁ hb_ge₂ ha_def hlam_pos hlam_le_16b rfl hw₀ hG_H hG_Jc hFt_rest
            h_viral₁ h_viral₂ with
          ⟨U, hUF_t, hU_rest, hU_card⟩ | ⟨B, hB_pure⟩
        · exact Or.inr ⟨U, hUF_t, hU_rest, hU_card⟩
        · left; left
          let k := ⌈y⁻¹⌉₊
          have hk_ge_inv : y⁻¹ ≤ (k : ℝ) := Nat.le_ceil _
          have hk2 : 2 ≤ k := by
            have h2_lt : (2 : ℝ) < y⁻¹ := by
              rw [lt_inv_comm₀ (by norm_num) hy0]
              simpa using hy_lt_half
            have h2_lt_k : (2 : ℝ) < (k : ℝ) := h2_lt.trans_le hk_ge_inv
            exact_mod_cast h2_lt_k.le
          have hw_ge : (F.card : ℝ) / (k : ℝ) ^ C₁ ≤ y ^ (a + 2) * (F_t.card : ℝ) :=
            leaf_coleaf_blockade_width_upgrade hb3 ha1 hb₂_pos hC₁_def hlam0_def hlam_pos
              hy0 rfl hk2 hk_ge_inv (Nat.cast_nonneg _) hF₀_card hFt_card
          have hFt_F : F_t ⊆ F := hFt_sub.trans hF₀_sub
          refine ⟨k, hk2, B, ?_⟩
          rcases hB_pure with ⟨hB_in, hcomp⟩ | ⟨hB_in, hanti⟩
          · exact Or.inl ⟨⟨fun i => (hB_in.subset_ambient i).trans hFt_F,
              hB_in.nonempty_blocks, hB_in.pairwise_disjoint,
              fun i => hw_ge.trans (hB_in.width_ge i)⟩, hcomp⟩
          · exact Or.inr ⟨⟨fun i => (hB_in.subset_ambient i).trans hFt_F,
              hB_in.nonempty_blocks, hB_in.pairwise_disjoint,
              fun i => hw_ge.trans (hB_in.width_ge i)⟩, hanti⟩
      · left; right
        push_neg at hw₀
        rw [Real.rpow_one]
        have hx_C₁_le : x ^ C₁ ≤ lam ^ (a + 2) * lam ^ b₂ * lam0 ^ b₂ := by
          have h1 : x ^ C₁ ≤ x ^ ((a + 2) + b₂ + b₂) := by
            refine Real.rpow_le_rpow_of_exponent_ge hx_pos hx_le_one ?_
            rw [hC₁_def]
            linarith [mul_le_mul_of_nonneg_right hb3 hb₂_pos.le]
          have h2 : x ^ ((a + 2) + b₂ + b₂) = x ^ (a + 2) * x ^ b₂ * x ^ b₂ := by
            rw [Real.rpow_add hx_pos, Real.rpow_add hx_pos]
          rw [h2] at h1
          have h_x_a2 : x ^ (a + 2) ≤ lam ^ (a + 2) :=
            Real.rpow_le_rpow hx_pos.le hlam_ge_x (by linarith)
          have h_x_b2 : x ^ b₂ ≤ lam ^ b₂ :=
            Real.rpow_le_rpow hx_pos.le hlam_ge_x hb₂_pos.le
          have h_x_lam0 : x ^ b₂ ≤ lam0 ^ b₂ :=
            Real.rpow_le_rpow hx_pos.le hx_lt.le hb₂_pos.le
          exact h1.trans (mul_le_mul (mul_le_mul h_x_a2 h_x_b2 (by positivity) (by positivity))
            h_x_lam0 (by positivity) (by positivity))
        have hlam_a2_le_y : lam ^ (a + 2) ≤ y ^ (a + 2) :=
          Real.rpow_le_rpow hlam_pos.le hlam_le_y (by linarith)
        calc x ^ C₁ * (F.card : ℝ)
          _ ≤ (lam ^ (a + 2) * lam ^ b₂ * lam0 ^ b₂) * (F.card : ℝ) :=
            mul_le_mul_of_nonneg_right hx_C₁_le (Nat.cast_nonneg _)
          _ = lam ^ (a + 2) * (lam ^ b₂ * (lam0 ^ b₂ * (F.card : ℝ))) := by ring
          _ ≤ y ^ (a + 2) * (lam ^ b₂ * (F₀.card : ℝ)) :=
            mul_le_mul hlam_a2_le_y
              (mul_le_mul_of_nonneg_left hF₀_card (by positivity)) (by positivity) (by positivity)
          _ ≤ y ^ (a + 2) * (F_t.card : ℝ) :=
            mul_le_mul_of_nonneg_left hFt_card (by positivity)
          _ ≤ 1 := hw₀.le
          _ ≤ (kappa G : ℝ) := hkappa_r
    rcases lem_multiscale_sparsification G F₀ O hlam0_pos hlam0_lt_half hx_pos hx_lt
        (by norm_num : (1 : ℝ) < 3 / 2) hb₂_pos (by linarith : 0 < 2 * d + 2)
        (by linarith : (3 / 2 - 1) * b₂ ≥ 2 * d + 2) hF₀_rest hstep with
      ⟨_F_t, _, hO⟩ | ⟨S, hS_sub, hS_rest, hS_card⟩
    · exact Or.inr hO
    · left
      refine ⟨S, hS_sub.trans hF₀_sub, hS_rest, ?_⟩
      have hx_C₁_le : x ^ C₁ ≤ x ^ ((3 / 2 : ℝ) * b₂) * lam0 ^ b₂ := by
        have h1 : x ^ C₁ ≤ x ^ ((3 / 2 : ℝ) * b₂ + b₂) := by
          refine Real.rpow_le_rpow_of_exponent_ge hx_pos hx_le_one ?_
          rw [hC₁_def]
          linarith [mul_le_mul_of_nonneg_right hb3 hb₂_pos.le]
        rw [Real.rpow_add hx_pos] at h1
        exact h1.trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hx_pos.le hx_lt.le hb₂_pos.le) (by positivity))
      calc x ^ C₁ * (F.card : ℝ)
        _ ≤ (x ^ ((3 / 2 : ℝ) * b₂) * lam0 ^ b₂) * (F.card : ℝ) :=
          mul_le_mul_of_nonneg_right hx_C₁_le (Nat.cast_nonneg _)
        _ = x ^ ((3 / 2 : ℝ) * b₂) * (lam0 ^ b₂ * (F.card : ℝ)) := by ring
        _ ≤ x ^ ((3 / 2 : ℝ) * b₂) * (F₀.card : ℝ) :=
          mul_le_mul_of_nonneg_left hF₀_card (by positivity)
        _ ≤ (S.card : ℝ) := hS_card
  · push_neg at hx_lt
    left
    refine ⟨F₀, hF₀_sub, hF₀_rest.mono hx_lt, ?_⟩
    have hx_16b : x ^ (16 * b) ≤ lam0 := by
      rw [hlam0_def]
      calc x ^ (16 * b)
        _ ≤ (1 / 2 : ℝ) ^ (16 * b) := Real.rpow_le_rpow hx_pos.le hx_half.le (by positivity)
        _ = (2 : ℝ) ^ (-16 * b) := by
          rw [one_div, Real.inv_rpow two_pos.le, ← Real.rpow_neg two_pos.le, neg_mul]
    have hx_C₁_le : x ^ C₁ ≤ lam0 ^ b₂ := by
      have h1 : x ^ C₁ ≤ x ^ (16 * b * b₂) := by
        refine Real.rpow_le_rpow_of_exponent_ge hx_pos hx_le_one ?_
        rw [hC₁_def]
        linarith
      have h2 : x ^ (16 * b * b₂) = (x ^ (16 * b)) ^ b₂ := Real.rpow_mul hx_pos.le (16 * b) b₂
      rw [h2] at h1
      exact h1.trans (Real.rpow_le_rpow (by positivity) hx_16b hb₂_pos.le)
    exact (mul_le_mul_of_nonneg_right hx_C₁_le (Nat.cast_nonneg _)).trans hF₀_card

/--
**Theorem 4(2) (`isPairViral_simultaneous_leaf_coleaf`, Unordered Simultaneous Leaf and Co-Leaf Viral Closure)**:
Let $H : \text{SimpleGraph } W_1$ and $J : \text{SimpleGraph } W_2$ with $|W_1|, |W_2| \ge 3$.
Suppose $v_0 \in W_1$ has $\deg_H(v_0) \le 1$ and $w_0 \in W_2$ has $\deg_J(w_0) \le 1$.
If both $\{H - v_0, Jᶜ\}$ and $\{H, (J - w_0)ᶜ\}$ are viral (`IsPairViral`), then
$\{H, Jᶜ\}$ is viral (`IsPairViral H Jᶜ`).
-/
theorem isPairViral_simultaneous_leaf_coleaf
    {W₁ W₂ : Type*} [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]
    (H : SimpleGraph W₁) (v₀ : W₁) (J : SimpleGraph W₂) (w₀ : W₂)
    (hcard₁ : 3 ≤ Fintype.card W₁) (hcard₂ : 3 ≤ Fintype.card W₂)
    (hdeg₁ : (neighborFinsetIn H v₀ Finset.univ).card ≤ 1)
    (hdeg₂ : (neighborFinsetIn J w₀ Finset.univ).card ≤ 1)
    (h_viral₁ : IsPairViral (H.comap (Subtype.val : {v : W₁ // v ≠ v₀} → W₁)) Jᶜ)
    (h_viral₂ : IsPairViral H (J.comap (Subtype.val : {w : W₂ // w ≠ w₀} → W₂))ᶜ) :
    IsPairViral H Jᶜ := by
  rcases Nat.eq_zero_or_pos (neighborFinsetIn H v₀ Finset.univ).card with hdeg₁_0 | hdeg₁_pos
  · exact isPairViral_of_deg_zero_left H v₀ Jᶜ hdeg₁_0 h_viral₁
  rcases Nat.eq_zero_or_pos (neighborFinsetIn J w₀ Finset.univ).card with hdeg₂_0 | hdeg₂_pos
  · exact isPairViral_of_deg_zero_right_compl H J w₀ hdeg₂_0 h_viral₂
  have hdeg₁_one : (neighborFinsetIn H v₀ Finset.univ).card = 1 := by omega
  have hdeg₂_one : (neighborFinsetIn J w₀ Finset.univ).card = 1 := by omega
  haveI : Nonempty W₁ := ⟨v₀⟩
  haveI : Nonempty W₂ := ⟨w₀⟩
  let H' := H.comap (Subtype.val : {v : W₁ // v ≠ v₀} → W₁)
  let J' := J.comap (Subtype.val : {w : W₂ // w ≠ w₀} → W₂)
  have h_viral₂_dual : IsPairViral J' Hᶜ := by
    have h1 := h_viral₂.compl.symm
    rwa [compl_compl] at h1
  obtain ⟨d₁, hd₁, h_exp₁⟩ := (isPairViral_iff_exists_exp H' Jᶜ).mp h_viral₁
  obtain ⟨d₂, hd₂, h_exp₂⟩ := (isPairViral_iff_exists_exp J' Hᶜ).mp h_viral₂_dual
  let d : ℝ := max (max d₁ d₂) 4
  have hd_ge_four : 4 ≤ d := le_max_right _ _
  have h_v1 : IsPairViralWithExp H' Jᶜ d :=
    IsPairViralWithExp.mono ((le_max_left d₁ d₂).trans (le_max_left _ _)) h_exp₁
  have h_v2 : IsPairViralWithExp J' Hᶜ d :=
    IsPairViralWithExp.mono ((le_max_right d₁ d₂).trans (le_max_left _ _)) h_exp₂
  let b : ℝ := max (Fintype.card W₁ : ℝ) (Fintype.card W₂ : ℝ)
  have hb_ge₁ : (Fintype.card W₁ : ℝ) ≤ b := le_max_left _ _
  have hb_ge₂ : (Fintype.card W₂ : ℝ) ≤ b := le_max_right _ _
  have hb3 : 3 ≤ b := le_trans (by exact_mod_cast hcard₁) hb_ge₁
  let a : ℝ := 2 * d * b
  let lam0 : ℝ := (2 : ℝ) ^ (-16 * b)
  have hlam0_pos : 0 < lam0 := by dsimp [lam0]; positivity
  have hlam0_lt_one : lam0 < 1 := by
    dsimp [lam0]
    have h1 : (2 : ℝ) ^ (-16 * b) ≤ (2 : ℝ) ^ (-48 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h2 : (2 : ℝ) ^ (-48 : ℝ) < 1 := by norm_num
    linarith
  let δ₀ : ℝ := rodlDeltaGen (Fintype.card W₁) lam0
  have hδ₀_pos : 0 < δ₀ := rodlDeltaGen_pos (Fintype.card W₁) hlam0_pos
  let b₂_init : ℝ := max 1 (⌈Real.log (1 / δ₀) / Real.log (1 / lam0)⌉₊ : ℝ)
  have hb₂_init_ge_one : 1 ≤ b₂_init := le_max_left _ _
  have h_rodl_b2 : lam0 ^ b₂_init ≤ δ₀ := by
    have h_ceil : (⌈Real.log (1 / δ₀) / Real.log (1 / lam0)⌉₊ : ℝ) ≤ b₂_init := le_max_right _ _
    have h_div : Real.log (1 / δ₀) / Real.log (1 / lam0) ≤ b₂_init :=
      (Nat.le_ceil _).trans h_ceil
    have h1_lt_inv : 1 < 1 / lam0 := one_lt_one_div hlam0_pos hlam0_lt_one
    have hlog_inv_pos : 0 < Real.log (1 / lam0) := Real.log_pos h1_lt_inv
    have hmul : Real.log (1 / δ₀) ≤ b₂_init * Real.log (1 / lam0) :=
      (div_le_iff₀ hlog_inv_pos).mp h_div
    rw [one_div, one_div, Real.log_inv, Real.log_inv] at hmul
    have hlog_le : Real.log (lam0 ^ b₂_init) ≤ Real.log δ₀ := by
      rw [Real.log_rpow hlam0_pos]
      linarith
    exact (Real.log_le_log_iff (Real.rpow_pos_of_pos hlam0_pos b₂_init) hδ₀_pos).mp hlog_le
  let b₂ : ℝ := max (2 * (2 * d + 2)) b₂_init
  let C₁ : ℝ := 32 * b * b₂ + 6 * b * b₂ + a + 4
  have hb₂_pos : 0 < b₂ := lt_of_lt_of_le zero_lt_one (hb₂_init_ge_one.trans (le_max_right _ _))
  have ha_pos : 0 < a := by dsimp [a]; positivity
  have hC₁_ge_one : 1 ≤ C₁ := by dsimp [C₁]; nlinarith
  let q : ℝ := 42 * C₁ ^ 2
  have hq_ge : 42 ≤ q := by dsimp [q]; nlinarith
  let c₀ : ℝ := min (q⁻¹) ((1 : ℝ) / 2)
  have hc₀_pos : 0 < c₀ := lt_min (by dsimp [q]; positivity) (by norm_num)
  let N₀_r : ℝ := (2 : ℝ) ^ q
  have hN₀_gt_one : 1 < N₀_r := by
    dsimp [N₀_r]
    calc (1 : ℝ)
      _ = (2 : ℝ) ^ (0 : ℝ) := (Real.rpow_zero 2).symm
      _ < (2 : ℝ) ^ q := Real.rpow_lt_rpow_of_exponent_lt one_lt_two (by linarith)
  have hN₀_pos : 0 < N₀_r := zero_lt_one.trans hN₀_gt_one
  have hlogN₀_pos : 0 < Real.log N₀_r := Real.log_pos hN₀_gt_one
  let c₁ : ℝ := Real.log 2 / Real.log N₀_r
  have hc₁_pos : 0 < c₁ := div_pos (Real.log_pos one_lt_two) hlogN₀_pos
  have h_N₀_c₁ : N₀_r ^ c₁ = 2 := by
    dsimp [c₁]
    rw [Real.rpow_def_of_pos hN₀_pos, mul_div_cancel₀ _ hlogN₀_pos.ne', Real.exp_log zero_lt_two]
  let c : ℝ := min c₀ c₁
  have hc_pos : 0 < c := lt_min hc₀_pos hc₁_pos
  have h_eh : HasPairErdosHajnalProp H Jᶜ := by
    refine ⟨c, hc_pos, fun V _ _ G hG_H hG_Jc => ?_⟩
    let n := Fintype.card V
    rcases eq_or_ne n 0 with hn0 | hn0
    · change (n : ℝ) ^ c ≤ (kappa G : ℝ)
      rw [hn0, Nat.cast_zero, Real.zero_rpow hc_pos.ne']
      exact Nat.cast_nonneg _
    rcases eq_or_ne n 1 with hn1 | hn1
    · change (n : ℝ) ^ c ≤ (kappa G : ℝ)
      rw [hn1, Nat.cast_one, Real.one_rpow]
      haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
      exact_mod_cast kappa_pos_of_nonempty G
    have hn2 : 2 ≤ n := by omega
    have hn_ge_one : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    have hkappa_pos : 1 ≤ kappa G := kappa_pos_of_nonempty G
    by_cases hn_large : N₀_r ≤ (n : ℝ)
    · have h_multi := leaf_coleaf_multiscale_dichotomy H v₀ J w₀ G hcard₁ hcard₂
        hdeg₁_one hdeg₂_one hd_ge_four hb_ge₁ hb_ge₂ rfl rfl h_rodl_b2 hb₂_init_ge_one
        rfl rfl hkappa_pos hG_H hG_Jc h_v1 h_v2
      have h_red := stage2_reduction G Finset.univ C₁ 1 hC₁_ge_one zero_lt_one h_multi
        (by simpa [N₀_r, n] using hn_large)
      rw [Finset.card_univ] at h_red
      have h_c_le_c₀ : (n : ℝ) ^ c ≤ (n : ℝ) ^ c₀ :=
        Real.rpow_le_rpow_of_exponent_le hn_ge_one (min_le_left _ _)
      exact h_c_le_c₀.trans h_red
    · push_neg at hn_large
      have h1 : (n : ℝ) ^ c ≤ (n : ℝ) ^ c₁ :=
        Real.rpow_le_rpow_of_exponent_le hn_ge_one (min_le_right _ _)
      have h2 : (n : ℝ) ^ c₁ ≤ N₀_r ^ c₁ :=
        Real.rpow_le_rpow (Nat.cast_nonneg n) hn_large.le hc₁_pos.le
      have h3 : (2 : ℝ) ≤ (kappa G : ℝ) := by exact_mod_cast kappa_ge_two_of_two_le_card G hn2
      change (n : ℝ) ^ c ≤ (kappa G : ℝ)
      linarith [h_N₀_c₁]
  exact isPairViral_of_hasPairErdosHajnalProp h_eh

end SimultaneousLeafColeaf

/-!
### Section 6: Theorem 4(3) (Master Two-Graph Closure $\mathcal{J}(\mathcal{B}_k^*) \times \overline{\mathcal{J}(\mathcal{B}_k^*)}$ and $\mathcal{H}(\mathcal{B}_k^*)$)
(Lines 173, 185 of `main.tex`)
-/

section MasterClosure

/-- Every generator in `InBStar k` has at least $1$ vertex. -/
theorem inBStar_card_pos {k : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} (h : InBStar k H) : 1 ≤ Fintype.card W := by
  rcases h with he | he | he | he | he | ⟨t, ht1, _, he | he⟩
  · obtain ⟨e⟩ := he; rw [Fintype.card_congr e.toEquiv]; decide
  · obtain ⟨e⟩ := he; rw [Fintype.card_congr e.toEquiv]; decide
  · obtain ⟨e⟩ := he; rw [Fintype.card_congr e.toEquiv]; decide
  · obtain ⟨e⟩ := he; rw [Fintype.card_congr e.toEquiv]; decide
  · obtain ⟨e⟩ := he; rw [Fintype.card_congr e.toEquiv]; decide
  · obtain ⟨e⟩ := he; rw [Fintype.card_congr e.toEquiv, Fintype.card_fin]; exact ht1
  · obtain ⟨e⟩ := he; rw [Fintype.card_congr e.toEquiv, Fintype.card_fin]; exact ht1

/-- Every graph in `InJClosure k` has at least $1$ vertex. -/
theorem inJClosure_card_pos {k : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} (h : InJClosure k H) : 1 ≤ Fintype.card W := by
  induction h with
  | base _ hB => exact inBStar_card_pos hB
  | iso _ _ _ he ih =>
      obtain ⟨e⟩ := he
      rwa [← Fintype.card_congr e.toEquiv]
  | subst _ v₀ _ _ _ _ ih₂ =>
      rw [card_substGraph_vert v₀]
      omega
  | add_leaf _ v₀ _ _ _ =>
      haveI : Nonempty _ := ⟨v₀⟩
      exact Fintype.card_pos

/-- `InBStar k` is closed under graph isomorphism. -/
theorem InBStar.of_iso {k : ℕ} {W₁ W₂ : Type} [Fintype W₁] [DecidableEq W₁]
    [Fintype W₂] [DecidableEq W₂] {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂}
    (e : H₁ ≃g H₂) (h : InBStar k H₁) : InBStar k H₂ := by
  rcases h with he₀ | he₀ | he₀ | he₀ | he₀ | ⟨t, ht1, htk, he₀ | he₀⟩
  · obtain ⟨e₀⟩ := he₀; exact Or.inl ⟨e.symm.trans e₀⟩
  · obtain ⟨e₀⟩ := he₀; exact Or.inr (Or.inl ⟨e.symm.trans e₀⟩)
  · obtain ⟨e₀⟩ := he₀; exact Or.inr (Or.inr (Or.inl ⟨e.symm.trans e₀⟩))
  · obtain ⟨e₀⟩ := he₀; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e.symm.trans e₀⟩)))
  · obtain ⟨e₀⟩ := he₀; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e.symm.trans e₀⟩))))
  · obtain ⟨e₀⟩ := he₀; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨t, ht1, htk, Or.inl ⟨e.symm.trans e₀⟩⟩))))
  · obtain ⟨e₀⟩ := he₀; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨t, ht1, htk, Or.inr ⟨e.symm.trans e₀⟩⟩))))

/-- Every simple graph on $1$ or $2$ vertices belongs to `InBStar k` (as $K_1, K_2$, or $\overline{K_2}$). -/
theorem inBStar_of_card_le_two (k : ℕ) {W : Type} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (hpos : 1 ≤ Fintype.card W) (hle : Fintype.card W ≤ 2) :
    InBStar k H := by
  rcases eq_or_ne (Fintype.card W) 1 with h1 | h1_ne
  · left
    let e_eq : W ≃ Fin 1 := Fintype.equivFinOfCardEq h1
    refine ⟨{ toEquiv := e_eq, map_rel_iff' := ?_ }⟩
    intro u v
    haveI : Subsingleton W := Fintype.card_le_one_iff_subsingleton.mp h1.le
    have huv : u = v := Subsingleton.elim u v
    subst huv
    simp
  · have h2 : Fintype.card W = 2 := by omega
    let e_eq : W ≃ Fin 2 := Fintype.equivFinOfCardEq h2
    let u₀ : W := e_eq.symm 0
    let u₁ : W := e_eq.symm 1
    by_cases hadj : H.Adj u₀ u₁
    · right; left
      refine ⟨{ toEquiv := e_eq, map_rel_iff' := ?_ }⟩
      intro x y
      simp only [top_adj, ne_eq, EmbeddingLike.apply_eq_iff_eq]
      constructor
      · intro hxy
        have h_cases : (x = u₀ ∧ y = u₁) ∨ (x = u₁ ∧ y = u₀) := by
          have hx : e_eq x = 0 ∨ e_eq x = 1 := by
            rcases e_eq x with ⟨i, hi⟩
            omega
          have hy : e_eq y = 0 ∨ e_eq y = 1 := by
            rcases e_eq y with ⟨j, hj⟩
            omega
          rcases hx with hx0 | hx1 <;> rcases hy with hy0 | hy1
          · exact False.elim (hxy (e_eq.injective (hx0.trans hy0.symm)))
          · left
            exact ⟨e_eq.symm_apply_apply x ▸ congr_arg e_eq.symm hx0,
                   e_eq.symm_apply_apply y ▸ congr_arg e_eq.symm hy1⟩
          · right
            exact ⟨e_eq.symm_apply_apply x ▸ congr_arg e_eq.symm hx1,
                   e_eq.symm_apply_apply y ▸ congr_arg e_eq.symm hy0⟩
          · exact False.elim (hxy (e_eq.injective (hx1.trans hy1.symm)))
        rcases h_cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hadj
        · exact hadj.symm
      · exact H.ne_of_adj
    · right; right; left
      refine ⟨{ toEquiv := e_eq, map_rel_iff' := ?_ }⟩
      intro x y
      simp only [bot_adj, false_iff]
      intro hxy_adj
      have hxy : x ≠ y := H.ne_of_adj hxy_adj
      have h_cases : (x = u₀ ∧ y = u₁) ∨ (x = u₁ ∧ y = u₀) := by
        have hx : e_eq x = 0 ∨ e_eq x = 1 := by
          rcases e_eq x with ⟨i, hi⟩
          omega
        have hy : e_eq y = 0 ∨ e_eq y = 1 := by
          rcases e_eq y with ⟨j, hj⟩
          omega
        rcases hx with hx0 | hx1 <;> rcases hy with hy0 | hy1
        · exact False.elim (hxy (e_eq.injective (hx0.trans hy0.symm)))
        · left
          exact ⟨e_eq.symm_apply_apply x ▸ congr_arg e_eq.symm hx0,
                 e_eq.symm_apply_apply y ▸ congr_arg e_eq.symm hy1⟩
        · right
          exact ⟨e_eq.symm_apply_apply x ▸ congr_arg e_eq.symm hx1,
                 e_eq.symm_apply_apply y ▸ congr_arg e_eq.symm hy0⟩
        · exact False.elim (hxy (e_eq.injective (hx1.trans hy1.symm)))
      rcases h_cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hadj hxy_adj
      · exact hadj hxy_adj.symm

/-- When $|W_2| = 1$, $H_1[v_0 \leftarrow H_2] \cong H_1$. -/
noncomputable def substGraphIsoOfCardOneRight {W₁ W₂ : Type*} [Fintype W₁] [DecidableEq W₁]
    [Fintype W₂] [DecidableEq W₂]
    (H₁ : SimpleGraph W₁) (v₀ : W₁) (H₂ : SimpleGraph W₂) (hW₂ : Fintype.card W₂ = 1) :
    substGraph H₁ v₀ H₂ ≃g H₁ where
  toFun a :=
    match a with
    | Sum.inl u => u.1
    | Sum.inr _ => v₀
  invFun w :=
    if hw : w = v₀ then
      Sum.inr ((Fintype.equivFinOfCardEq hW₂).symm 0)
    else
      Sum.inl ⟨w, hw⟩
  left_inv a := by
    rcases a with ⟨u, hu⟩ | x
    · simp [hu]
    · haveI : Subsingleton W₂ := Fintype.card_le_one_iff_subsingleton.mp hW₂.le
      simp [Subsingleton.elim ((Fintype.equivFinOfCardEq hW₂).symm 0) x]
  right_inv w := by
    by_cases hw : w = v₀
    · subst hw; simp
    · simp [hw]
  map_rel_iff' := by
    haveI : Subsingleton W₂ := Fintype.card_le_one_iff_subsingleton.mp hW₂.le
    rintro (⟨u, hu⟩ | x) (⟨w, hw⟩ | y)
    · rfl
    · rfl
    · rfl
    · have hxy : x = y := Subsingleton.elim x y
      subst hxy
      simp [substGraph]

/-- Isomorphism-free structural classification predicate for `InJClosure k`. -/
def InJClosureDecomp (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) : Prop :=
  InBStar k H ∨
  (∃ (W_a W_b : Type) (_ : Fintype W_a) (_ : DecidableEq W_a) (_ : Fintype W_b) (_ : DecidableEq W_b)
      (H_a : SimpleGraph W_a) (v₀ : W_a) (H_b : SimpleGraph W_b),
    2 ≤ Fintype.card W_a ∧ 2 ≤ Fintype.card W_b ∧
    InJClosure k H_a ∧ InJClosure k H_b ∧
    Nonempty (substGraph H_a v₀ H_b ≃g H)) ∨
  (3 ≤ Fintype.card W ∧ ∃ v₀ : W,
    (neighborFinsetIn H v₀ Finset.univ).card ≤ 1 ∧
    InJClosure k (H.comap (Subtype.val : {v : W // v ≠ v₀} → W)))

/-- `InJClosureDecomp k` is preserved under graph isomorphism. -/
theorem InJClosureDecomp.of_iso {k : ℕ} {W₁ W₂ : Type} [Fintype W₁] [DecidableEq W₁]
    [Fintype W₂] [DecidableEq W₂] {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂}
    (e : H₁ ≃g H₂) (h : InJClosureDecomp k H₁) : InJClosureDecomp k H₂ := by
  rcases h with hB | ⟨W_a, W_b, f_a, d_a, f_b, d_b, H_a, v₀, H_b, hcard_a, hcard_b, hJa, hJb, ⟨e₀⟩⟩ |
      ⟨hcard3, v₁, hdeg₁, hJ_sub⟩
  · exact Or.inl (InBStar.of_iso e hB)
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
      exact InJClosure.iso _ _ hJ_sub ⟨e_sub⟩

/--
Every graph in `InJClosure k` satisfies `InJClosureDecomp k`: it is either a generator in
`InBStar k`, isomorphic to a substitution of two strictly smaller graphs in `InJClosure k`,
or has $\ge 3$ vertices and a vertex of degree $\le 1$ whose deletion stays in `InJClosure k`.
-/
theorem inJClosure_decomp {k : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} (hJ : InJClosure k H) : InJClosureDecomp k H := by
  induction hJ with
  | base H hB => exact Or.inl hB
  | iso H₁ H₂ _ he ih =>
      obtain ⟨e⟩ := he
      exact InJClosureDecomp.of_iso e ih
  | @subst W₁ W₂ _ _ _ _ H₁ v₀ H₂ hJ₁ hJ₂ ih₁ ih₂ =>
      have hpos₁ : 1 ≤ Fintype.card W₁ := inJClosure_card_pos hJ₁
      have hpos₂ : 1 ≤ Fintype.card W₂ := inJClosure_card_pos hJ₂
      rcases eq_or_ne (Fintype.card W₁) 1 with h1 | h1_ne
      · exact InJClosureDecomp.of_iso (substGraphIsoOfCardOne H₁ v₀ H₂ h1).symm ih₂
      · rcases eq_or_ne (Fintype.card W₂) 1 with h2 | h2_ne
        · exact InJClosureDecomp.of_iso (substGraphIsoOfCardOneRight H₁ v₀ H₂ h2).symm ih₁
        · exact Or.inr (Or.inl ⟨W₁, W₂, inferInstance, inferInstance, inferInstance, inferInstance,
            H₁, v₀, H₂, by omega, by omega, hJ₁, hJ₂, ⟨SimpleGraph.Iso.refl⟩⟩)
  | @add_leaf W _ _ H v₀ hdeg hJ_sub _ =>
      haveI : Nonempty W := ⟨v₀⟩
      have hpos : 1 ≤ Fintype.card W := Fintype.card_pos
      by_cases hle2 : Fintype.card W ≤ 2
      · exact Or.inl (inBStar_of_card_le_two k H hpos hle2)
      · exact Or.inr (Or.inr ⟨by omega, v₀, hdeg, hJ_sub⟩)

/--
Strong induction helper for Theorem 4(3): under `h_base`, for all $H_1, H_2 \in \mathcal{J}(\mathcal{B}_k^*)$
with $|W_1| + |W_2| = N$, the pair $\{H_1, \overline{H_2}\}$ is viral (`IsPairViral H₁ H₂ᶜ`).
-/
private theorem inJClosure_isPairViral_aux (k : ℕ)
    (h_base : ∀ {W : Type} [Fintype W] [DecidableEq W] (B : SimpleGraph W),
      InBStar k B → HasErdosHajnalProp B) :
    ∀ (N : ℕ) {W₁ W₂ : Type} [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]
      (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂),
      Fintype.card W₁ + Fintype.card W₂ = N →
      InJClosure k H₁ → InJClosure k H₂ →
      IsPairViral H₁ H₂ᶜ := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro W₁ W₂ _ _ _ _ H₁ H₂ hN hJ₁ hJ₂
    have hpos₁ : 1 ≤ Fintype.card W₁ := inJClosure_card_pos hJ₁
    have hpos₂ : 1 ≤ Fintype.card W₂ := inJClosure_card_pos hJ₂
    haveI : Nonempty W₁ := Fintype.card_pos_iff.mp hpos₁
    haveI : Nonempty W₂ := Fintype.card_pos_iff.mp hpos₂
    rcases inJClosure_decomp hJ₁ with
      hB₁ |
      ⟨W_a, W_b, f_a, d_a, f_b, d_b, H_a, v₀, H_b, hcard_a, hcard_b, hJa, hJb, ⟨e₁⟩⟩ |
      ⟨hcard₁_3, v₀, hdeg₁, hJ₁_sub⟩
    · -- Case 1: H₁ ∈ InBStar k
      have h_eh₁ : HasErdosHajnalProp H₁ := h_base H₁ hB₁
      have hv₁ : IsViral H₁ := isViral_of_hasErdosHajnalProp h_eh₁
      exact isPairViral_of_isViral_left H₂ᶜ hv₁
    · -- Case 2: H₁ ≃g substGraph H_a v₀ H_b with |W_a|, |W_b| ≥ 2
      have hW₁_card : Fintype.card W₁ = Fintype.card W_a - 1 + Fintype.card W_b := by
        rw [← Fintype.card_congr e₁.toEquiv, card_substGraph_vert v₀]
      have hlt_a : Fintype.card W_a + Fintype.card W₂ < N := by omega
      have hlt_b : Fintype.card W_b + Fintype.card W₂ < N := by omega
      have hv_a : IsPairViral H_a H₂ᶜ := ih _ hlt_a H_a H₂ rfl hJa hJ₂
      have hv_b : IsPairViral H_b H₂ᶜ := ih _ hlt_b H_b H₂ rfl hJb hJ₂
      have hv_subst := isPairViral_substGraph H_a v₀ H_b H₂ᶜ hv_a hv_b
      exact IsPairViral.congr e₁ (SimpleGraph.Iso.refl) hv_subst
    · -- Case 3: H₁ has ≥ 3 vertices and leaf v₀; inspect H₂
      rcases inJClosure_decomp hJ₂ with
        hB₂ |
        ⟨V_a, V_b, f_va, d_va, f_vb, d_vb, J_a, w₀, J_b, hcard_va, hcard_vb, hJ_va, hJ_vb, ⟨e₂⟩⟩ |
        ⟨hcard₂_3, w₀, hdeg₂, hJ₂_sub⟩
      · -- Subcase 3a: H₂ ∈ InBStar k
        have h_eh₂ : HasErdosHajnalProp H₂ := h_base H₂ hB₂
        have hv₂_c : IsViral H₂ᶜ := isViral_of_hasErdosHajnalProp h_eh₂.compl
        exact isPairViral_of_isViral_right H₁ hv₂_c
      · -- Subcase 3b: H₂ ≃g substGraph J_a w₀ J_b with |V_a|, |V_b| ≥ 2
        have hW₂_card : Fintype.card W₂ = Fintype.card V_a - 1 + Fintype.card V_b := by
          rw [← Fintype.card_congr e₂.toEquiv, card_substGraph_vert w₀]
        have hlt_va : Fintype.card W₁ + Fintype.card V_a < N := by omega
        have hlt_vb : Fintype.card W₁ + Fintype.card V_b < N := by omega
        have hv_va : IsPairViral H₁ J_aᶜ := ih _ hlt_va H₁ J_a rfl hJ₁ hJ_va
        have hv_vb : IsPairViral H₁ J_bᶜ := ih _ hlt_vb H₁ J_b rfl hJ₁ hJ_vb
        have hv_subst_c : IsPairViral (substGraph J_aᶜ w₀ J_bᶜ) H₁ :=
          isPairViral_substGraph J_aᶜ w₀ J_bᶜ H₁ hv_va.symm hv_vb.symm
        rw [← substGraph_compl] at hv_subst_c
        let e₂_c : (substGraph J_a w₀ J_b)ᶜ ≃g H₂ᶜ :=
          { toEquiv := e₂.toEquiv
            map_rel_iff' := by
              intro a b
              simp only [RelIso.coe_fn_toEquiv, compl_adj, ne_eq,
                EmbeddingLike.apply_eq_iff_eq, e₂.map_rel_iff] }
        exact (IsPairViral.congr e₂_c (SimpleGraph.Iso.refl) hv_subst_c).symm
      · -- Subcase 3c: Both H₁ and H₂ have ≥ 3 vertices and degree ≤ 1 leaves v₀, w₀
        have hlt₁ : Fintype.card {v : W₁ // v ≠ v₀} + Fintype.card W₂ < N := by
          rw [card_subtype_ne v₀]
          omega
        have hlt₂ : Fintype.card W₁ + Fintype.card {w : W₂ // w ≠ w₀} < N := by
          rw [card_subtype_ne w₀]
          omega
        have hv_sub₁ : IsPairViral (H₁.comap (Subtype.val : {v : W₁ // v ≠ v₀} → W₁)) H₂ᶜ :=
          ih _ hlt₁ (H₁.comap (Subtype.val : {v : W₁ // v ≠ v₀} → W₁)) H₂ rfl hJ₁_sub hJ₂
        have hv_sub₂ : IsPairViral H₁ (H₂.comap (Subtype.val : {w : W₂ // w ≠ w₀} → W₂))ᶜ :=
          ih _ hlt₂ H₁ (H₂.comap (Subtype.val : {w : W₂ // w ≠ w₀} → W₂)) rfl hJ₁ hJ₂_sub
        exact isPairViral_simultaneous_leaf_coleaf H₁ v₀ H₂ w₀
          hcard₁_3 hcard₂_3 hdeg₁ hdeg₂ hv_sub₁ hv_sub₂

/--
**Theorem 4(3) (`inJClosure_pair_viral_of_base`, Master Two-Graph Closure Theorem)**:
Assuming every generator $B \in \mathcal{B}_k^*$ (`InBStar k B`) satisfies `HasErdosHajnalProp B`,
for all $H_1, H_2 \in \mathcal{J}(\mathcal{B}_k^*)$ (`InJClosure k`), the pair $\{H_1, \overline{H_2}\}$
satisfies `IsPairViral H₁ H₂ᶜ`, `HasPairPolyRodlProp H₁ H₂ᶜ`, and `HasPairErdosHajnalProp H₁ H₂ᶜ`.
-/
theorem inJClosure_pair_viral_of_base (k : ℕ)
    (h_base : ∀ {W : Type} [Fintype W] [DecidableEq W] (B : SimpleGraph W),
      InBStar k B → HasErdosHajnalProp B)
    {W₁ W₂ : Type} [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]
    (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂)
    (hJ₁ : InJClosure k H₁) (hJ₂ : InJClosure k H₂) :
    IsPairViral H₁ H₂ᶜ ∧ HasPairPolyRodlProp H₁ H₂ᶜ ∧ HasPairErdosHajnalProp H₁ H₂ᶜ := by
  have h_viral : IsPairViral H₁ H₂ᶜ :=
    inJClosure_isPairViral_aux k h_base (Fintype.card W₁ + Fintype.card W₂) H₁ H₂ rfl hJ₁ hJ₂
  have h_rodl : HasPairPolyRodlProp H₁ H₂ᶜ := hasPairPolyRodlProp_of_isPairViral h_viral
  have h_eh : HasPairErdosHajnalProp H₁ H₂ᶜ := hasPairErdosHajnalProp_of_hasPairPolyRodlProp h_rodl
  exact ⟨h_viral, h_rodl, h_eh⟩

/--
**Theorem 4(3) (`inHClosure_eh_of_base`, Master Single-Graph Closure Theorem)**:
Assuming every generator $B \in \mathcal{B}_k^*$ (`InBStar k B`) satisfies `HasErdosHajnalProp B`,
every single graph $H \in \mathcal{H}(\mathcal{B}_k^*)$ (`InHClosure k H`) satisfies
`HasErdosHajnalProp H`, `HasErdosHajnalProp Hᶜ`, `HasPolyRodlProp H`, and `IsViral H`.
-/
theorem inHClosure_eh_of_base (k : ℕ)
    (h_base : ∀ {W : Type} [Fintype W] [DecidableEq W] (B : SimpleGraph W),
      InBStar k B → HasErdosHajnalProp B)
    {W : Type} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (hH : InHClosure k H) :
    HasErdosHajnalProp H ∧ HasErdosHajnalProp Hᶜ ∧ HasPolyRodlProp H ∧ IsViral H := by
  obtain ⟨hJ, hJc⟩ := hH
  obtain ⟨h_viral, h_rodl, h_eh⟩ := inJClosure_pair_viral_of_base k h_base H Hᶜ hJ hJc
  rw [compl_compl] at h_viral h_rodl h_eh
  have h_eh_single : HasErdosHajnalProp H := (hasPairErdosHajnalProp_self_iff H).mp h_eh
  have h_rodl_single : HasPolyRodlProp H := (hasPairPolyRodlProp_self_iff H).mp h_rodl
  have h_viral_single : IsViral H := (isPairViral_self_iff H).mp h_viral
  exact ⟨h_eh_single, h_eh_single.compl, h_rodl_single, h_viral_single⟩

end MasterClosure

/-! ### Axiom Verification -/

#print axioms rodl_theorem_general
#print axioms rodl_theorem_pair
#print axioms eh_iff_polyRodl_iff_isViral
#print axioms pair_eh_iff_pairPolyRodl_iff_isPairViral
#print axioms isViral_substGraph
#print axioms isPairViral_substGraph
#print axioms hasErdosHajnalProp_substGraph
#print axioms isPairViral_simultaneous_leaf_coleaf
#print axioms inJClosure_pair_viral_of_base
#print axioms inHClosure_eh_of_base

end ErdosHajnalGen
