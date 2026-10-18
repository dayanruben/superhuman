/-
Copyright 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosHajnal.BasicLemmas
import ErdosHajnal.CombModules
import ErdosHajnal.Defs
import ErdosHajnal.GallaiAndCombDichotomy
import ErdosHajnal.GenDefs
import ErdosHajnal.P6Baseline

/-!
# Recursive Gallai Core Dichotomy, $\Phi_D$ Active-Leaf Split Trees, and Inductive Stage-1 Comb/Co-Comb Dichotomy
(Section 5: Lemmas 8–13, Propositions 1, 2, 4, and Theorem 7(1)–(2) of `main.tex`)

This file formalizes the complete Stage-1 structural comb/co-comb dichotomy engine from Section 5
(`main.tex` lines 416–964):

1. **Module Calculus and Blockade Monotonicity (`Section 1`, Theorem 1(a)–(b))**:
   Module transitivity (`isModuleIn_trans`) and induced restriction (`isModuleIn_inter`), together
   with symmetry and monotonicity helpers for `IsWeaklySparseOrCoSparsePair` and
   `IsWeaklySparseOrCoSparseBlockadeIn`.
2. **Real $1/D$-Power Calculus (`Section 2`)**:
   Exact cancellation and comparison lemmas for $(a^{1/D})^D = a$ used in the $\Phi_D$ tree potential.
3. **Lemma 8(1) (`three_case_gallai_core_extraction`, `Section 3`, `main.tex` lines 421–426)**:
   Single-step three-case $p_{\mathrm{cap}}$-decoupled Gallai core extraction producing an exact
   module $M_T \subseteq W$ of $F[W]$ in **(Case G-Small-$k$)**, **(Case G-Large-$k$)**, or
   **(Case G-Core)**.
4. **Lemma 8(2) (`iterated_gallai_core_decomposition`, `Section 4`, `main.tex` lines 427–432)**:
   Iterated $\Phi_8$-preserving Gallai core decomposition on $F[B]$ with parameterized stopping
   leaf threshold $L_{\max} \in [2, \ell]$ and separated split/cap outcomes **(GC1-Core)**,
   **(GC2-PureSplit)**, and **(GC2-Cap)**.
5. **Lemma 8(3) (`active_leaf_split_tree_dichotomy`, `Section 5`, `main.tex` lines 433–444)**:
   Generalized $\Phi_D(\mathcal{T}) = \sum_{L \in \mathcal{L}(\mathcal{T})} |L|^{1/D}$ active-leaf
   split tree (`ActiveLeafSplitTree`), proving that splitting only active leaves
   ($|W_z| \ge L_{\max}^{-D} |B|$) via **(Split-$D$ Type I)** or **(Split-$D$ Type II)** preserves
   the universal leaf-width lower bound $|L| \ge 2^{-60r} L_{\max}^{-2D} |B|$ with zero leaves pruned.
6. **Unified Handle-Stem Pair Principle and Lemma 9 (`universal_depth_r_neighborhood_modularity`, `Section 6`, `main.tex` lines 90–95 & 473–490)**:
   Simultaneous comb/co-comb handle-stem unification (`isUnifiedHandleStemPair_of_combOrCoComb`),
   universal depth-$r$ anticonnected neighborhood modularity in $\overline{P_{s+5+r}}$-free graphs,
   and greedy anticonnected component grouping (`exists_complete_blockade_of_small_components`).
7. **Lemma 10(1)–(2) (`union_pool_stem_promotion` & `internal_depth_d_stem_promotion`, `Section 7`, `main.tex` lines 517–551)**:
   Reverse-order dyadic bucket pruning on greedy extraction sequences (`greedy_pool_comb_extraction`),
   promoting cross-block union pools $(S_i, D_i)$ to per-handle $(s+1)$-stems and internal depth-$d$
   cutter pools to shared $(s+1+d)$-stems.
8. **Lemma 11 (`bipartite_double_counting_dichotomy`, `Section 8`, `main.tex` lines 555–566)**:
   Bipartite edge double-counting between low-degree and high-degree subsets $S_{i,j}$ and $D_{j,i}$
   at threshold $\frac{\eta_{\mathrm{out}}}{4\ell}$, yielding a weakly $\eta_{\mathrm{out}}$-sparse-or-co-sparse
   $(\ell, w_0)$-blockade.
9. **Proposition 1, Base Case $r = 1$, and Lemma 12 (`prop1_comb_cocomb_dichotomy`, `stage1_comb_cocomb_dichotomy_r1`, & `single_u_level2_core_dichotomy`, `Section 9`, `main.tex` lines 493–509 & 570–577)**:
   Comb/co-comb dichotomy for $\overline{P_{s+5}}$-free graphs ($r = 1$), strong inductive predicate
   `Stage1CombCoCombDichotomyStrongAt`, and general depth-$d$ / single-$u$ Level-2 core dichotomy.
10. **Regime A/B Capped-Comb Resolution, Lemma 13, Propositions 2 & 4, and Theorem 7(1) (`stage1_comb_cocomb_dichotomy_all_r`, `Section 10`, `main.tex` lines 581–670, 697–829, & 899–962)**:
    Unified recursive call resolver (`resolve_recursive_comb_call`) separating **Regime A**
    ($k_{\mathrm{comb}} \le p_{\mathrm{cap}}$, uncapped width) from **Regime B**
    ($k_{\mathrm{comb}} > p_{\mathrm{cap}}$, exact length $L'_{\max} = k' = p_{\mathrm{cap}}$),
    and strong induction on $r \ge 1$ establishing `Stage1CombCoCombDichotomyAt r` for all $r \ge 1$.
11. **Theorem 7(2) (`stage1_comb_dichotomy_condition_for_all_paths`, `Section 11`, `main.tex` lines 907 & 963)**:
    Unconditional Stage-1 Comb Dichotomy `(CD3)` for every path $P_k$ ($k \ge 6$) with explicit
    exponent $C_{\mathrm{comb}}(k) = 3 E_{k-5} + 4 D_{k-5} + 100$.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Classical Filter Finset SimpleGraph Real ErdosHajnalP6

namespace ErdosHajnalGen

variable {V : Type*} [Fintype V] [DecidableEq V]

/-!
## Section 1: Module Calculus (Theorem 1(a)–(b)) and Sparsity/Blockade Monotonicity Helpers

Formalizes module transitivity (`isModuleIn_trans`) and induced module restriction (`isModuleIn_inter`)
from Theorem 1(a)–(b) (`main.tex` lines 122–123), along with symmetry and parameter-monotonicity
lemmas for `crossEdgeCount`, `IsWeaklySparseOrCoSparsePair`, and `IsWeaklySparseOrCoSparseBlockadeIn`.
-/

/-- Every subset $W$ is a module of $F[W]$. -/
theorem isModuleIn_self (F : SimpleGraph V) (W : Finset V) : IsModuleIn F W W :=
  ⟨Finset.Subset.rfl, fun _ hz hnot => False.elim (hnot hz)⟩

/-- **Theorem 1(a) (Module Transitivity)**: If $M \subseteq W$ is a module of $F[W]$ and
$N \subseteq M$ is a module of $F[M]$, then $N$ is a module of $F[W]$. -/
theorem isModuleIn_trans {F : SimpleGraph V} {W M N : Finset V}
    (hWM : IsModuleIn F W M) (hMN : IsModuleIn F M N) : IsModuleIn F W N := by
  refine ⟨hMN.1.trans hWM.1, fun z hzW hzN => ?_⟩
  by_cases hzM : z ∈ M
  · exact hMN.2 z hzM hzN
  · rcases hWM.2 z hzW hzM with hcomp | hanti
    · left; exact fun u hu => hcomp u (hMN.1 hu)
    · right; exact fun u hu => hanti u (hMN.1 hu)

/-- **Theorem 1(b) (Induced Restriction of Modules)**: If $M$ is a module of $F[W]$ and $U \subseteq W$,
then $M \cap U$ is a module of $F[U]$. -/
theorem isModuleIn_inter {F : SimpleGraph V} {W M U : Finset V}
    (hWM : IsModuleIn F W M) (hUW : U ⊆ W) : IsModuleIn F U (M ∩ U) := by
  refine ⟨Finset.inter_subset_right, fun z hzU hzMU => ?_⟩
  have hzM : z ∉ M := fun h => hzMU (Finset.mem_inter.mpr ⟨h, hzU⟩)
  rcases hWM.2 z (hUW hzU) hzM with hcomp | hanti
  · left; exact fun u hu => hcomp u (Finset.mem_inter.mp hu).1
  · right; exact fun u hu => hanti u (Finset.mem_inter.mp hu).1

/-- Symmetry of the cross-edge count $|E_F(A, B)| = |E_F(B, A)|$. -/
theorem crossEdgeCount_comm (F : SimpleGraph V) (A B : Finset V) :
    crossEdgeCount F A B = crossEdgeCount F B A :=
  sum_neighborFinsetIn_card_comm F A B

/-- Monotonicity of $|E_F(A, B)|$ with respect to subset inclusion $A_1 \subseteq A_2$, $B_1 \subseteq B_2$. -/
theorem crossEdgeCount_mono (F : SimpleGraph V) {A₁ A₂ B₁ B₂ : Finset V}
    (hA : A₁ ⊆ A₂) (hB : B₁ ⊆ B₂) :
    crossEdgeCount F A₁ B₁ ≤ crossEdgeCount F A₂ B₂ := by
  unfold crossEdgeCount
  calc ∑ u ∈ A₁, (neighborFinsetIn F u B₁).card
      ≤ ∑ u ∈ A₁, (neighborFinsetIn F u B₂).card :=
        Finset.sum_le_sum (fun u _ => Finset.card_le_card (neighborFinsetIn_mono F u hB))
    _ ≤ ∑ u ∈ A₂, (neighborFinsetIn F u B₂).card :=
        Finset.sum_le_sum_of_subset hA

/-- Symmetry of weak $\varepsilon$-sparsity (`IsWeaklySparsePair`). -/
theorem IsWeaklySparsePair.symm {F : SimpleGraph V} {A B : Finset V} {ε : ℝ}
    (h : IsWeaklySparsePair F A B ε) : IsWeaklySparsePair F B A ε := by
  unfold IsWeaklySparsePair at *
  rw [crossEdgeCount_comm]
  linarith

/-- Symmetry of weak $x$-sparsity-or-co-sparsity (`IsWeaklySparseOrCoSparsePair`). -/
theorem IsWeaklySparseOrCoSparsePair.symm {F : SimpleGraph V} {A B : Finset V} {x : ℝ}
    (h : IsWeaklySparseOrCoSparsePair F A B x) : IsWeaklySparseOrCoSparsePair F B A x :=
  h.elim (fun h1 => Or.inl h1.symm) (fun h2 => Or.inr h2.symm)

/-- Monotonicity of `IsWeaklySparseOrCoSparsePair` in the density parameter $x_1 \le x_2$. -/
theorem IsWeaklySparseOrCoSparsePair.mono {F : SimpleGraph V} {A B : Finset V} {x₁ x₂ : ℝ}
    (h : IsWeaklySparseOrCoSparsePair F A B x₁) (hx : x₁ ≤ x₂) :
    IsWeaklySparseOrCoSparsePair F A B x₂ :=
  h.elim (fun h1 => Or.inl (h1.mono hx)) (fun h2 => Or.inr (h2.mono hx))

/-- Any disjoint pure (complete or anticomplete) pair $(A, B)$ in $F$ is weakly $x$-sparse-or-co-sparse
for every $x \ge 0$ (having $0$ wrong cross-edges in $F^c$ or $F$). -/
theorem isWeaklySparseOrCoSparsePair_of_isPurePair {F : SimpleGraph V} {A B : Finset V}
    {x : ℝ} (hAB : Disjoint A B) (hx : 0 ≤ x) (h : IsPurePair F A B) :
    IsWeaklySparseOrCoSparsePair F A B x := by
  rcases h with hcomp | hanti
  · right
    unfold IsWeaklySparsePair crossEdgeCount
    have h0 : ∑ u ∈ A, (neighborFinsetIn Fᶜ u B).card = 0 := by
      refine Finset.sum_eq_zero (fun u hu => Finset.card_eq_zero.mpr ?_)
      rw [Finset.eq_empty_iff_forall_notMem]
      intro v hv
      obtain ⟨hvB, hadjc⟩ := (mem_neighborFinsetIn_iff Fᶜ u B v).mp hv
      exact hadjc.2 (hcomp u hu v hvB)
    rw [h0, Nat.cast_zero]
    positivity
  · left
    unfold IsWeaklySparsePair crossEdgeCount
    have h0 : ∑ u ∈ A, (neighborFinsetIn F u B).card = 0 := by
      refine Finset.sum_eq_zero (fun u hu => Finset.card_eq_zero.mpr ?_)
      rw [Finset.eq_empty_iff_forall_notMem]
      intro v hv
      obtain ⟨hvB, hadj⟩ := (mem_neighborFinsetIn_iff F u B v).mp hv
      exact hanti u hu v hvB hadj
    rw [h0, Nat.cast_zero]
    positivity

/-- Any disjoint complete-or-$x$-sparse pair $(A, B)$ in $F$ ($x \ge 0$) is weakly $x$-sparse-or-co-sparse. -/
theorem isWeaklySparseOrCoSparsePair_of_isCompleteOrXSparsePair {F : SimpleGraph V}
    {A B : Finset V} {x : ℝ} (hAB : Disjoint A B) (hx : 0 ≤ x)
    (h : IsCompleteOrXSparsePair F A B x) :
    IsWeaklySparseOrCoSparsePair F A B x := by
  rcases h with hcomp | hsp
  · exact isWeaklySparseOrCoSparsePair_of_isPurePair hAB hx (Or.inl hcomp)
  · exact Or.inl hsp.isWeaklySparsePair

/-- Every pairwise-pure $(k, w)$-blockade in $F$ is a weakly $x$-sparse-or-co-sparse $(k, w)$-blockade
for any $x \ge 0$. -/
theorem IsPureBlockadeIn.isWeaklySparseOrCoSparseBlockadeIn {F : SimpleGraph V}
    {S : Finset V} {k : ℕ} {w x : ℝ} {B : Fin k → Finset V}
    (h : IsPureBlockadeIn F S k w B) (hx : 0 ≤ x) :
    IsWeaklySparseOrCoSparseBlockadeIn F S k w x B :=
  ⟨h.1, fun i j hij => isWeaklySparseOrCoSparsePair_of_isPurePair
    (h.1.pairwise_disjoint i j hij) hx (h.2 i j hij)⟩

/-- Every complete $(k, w)$-blockade in $F$ is a pairwise-pure $(k, w)$-blockade. -/
theorem IsCompleteBlockadeIn.isPureBlockadeIn {F : SimpleGraph V}
    {S : Finset V} {k : ℕ} {w : ℝ} {B : Fin k → Finset V}
    (h : IsCompleteBlockadeIn F S k w B) :
    IsPureBlockadeIn F S k w B :=
  ⟨h.1, fun i j hij => Or.inl (h.2 i j hij)⟩

/-- Every complete-or-$x$-sparse $(k, w)$-blockade in $F$ ($x \ge 0$) is weakly $x$-sparse-or-co-sparse. -/
theorem IsCompleteOrXSparseBlockadeIn.isWeaklySparseOrCoSparseBlockadeIn {F : SimpleGraph V}
    {S : Finset V} {k : ℕ} {w x : ℝ} {B : Fin k → Finset V}
    (h : IsCompleteOrXSparseBlockadeIn F S k w x B) (hx : 0 ≤ x) :
    IsWeaklySparseOrCoSparseBlockadeIn F S k w x B :=
  ⟨h.1, fun i j hij => isWeaklySparseOrCoSparsePair_of_isCompleteOrXSparsePair
    (h.1.pairwise_disjoint i j hij) hx (h.2 i j hij)⟩

/-- Simultaneous monotonicity of `IsWeaklySparseOrCoSparseBlockadeIn` in ambient set ($S_1 \subseteq S_2$),
block width ($w_2 \le w_1$), and cross-block sparsity ($x_1 \le x_2$). -/
theorem IsWeaklySparseOrCoSparseBlockadeIn.mono_ambient_width_eps {F : SimpleGraph V}
    {S₁ S₂ : Finset V} {k : ℕ} {w₁ w₂ x₁ x₂ : ℝ} {B : Fin k → Finset V}
    (h : IsWeaklySparseOrCoSparseBlockadeIn F S₁ k w₁ x₁ B)
    (hS : S₁ ⊆ S₂) (hw : w₂ ≤ w₁) (hx : x₁ ≤ x₂) :
    IsWeaklySparseOrCoSparseBlockadeIn F S₂ k w₂ x₂ B :=
  ⟨(h.1.mono_ambient hS).mono_width hw, fun i j hij => (h.2 i j hij).mono hx⟩

/-!
## Section 2: General $1/D$-Power Helpers

Exact power-cancellation identities $(a^{1/D})^D = a$ and $(a^D)^{1/D} = a$ for $a \ge 0$ and $D \ge 1$,
used to analyze the tree potential $\Phi_D(\mathcal{T}) = \sum_{L \in \mathcal{L}(\mathcal{T})} |L|^{1/D}$
in Lemma 8(2)–(3).
-/

/-- For $a \ge 0$ and $D \ge 1$, $(a^{1/D})^D = a$. -/
lemma rpow_inv_nat_pow {a : ℝ} {D : ℕ} (ha : 0 ≤ a) (hD : 1 ≤ D) :
    (a ^ (1 / (D : ℝ))) ^ D = a := by
  have hD_pos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr (by omega)
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha, one_div_mul_cancel (ne_of_gt hD_pos), Real.rpow_one]

/-- For $a \ge 0$ and $D \ge 1$, $(a^D)^{1/D} = a$. -/
lemma pow_rpow_inv_nat {a : ℝ} {D : ℕ} (ha : 0 ≤ a) (hD : 1 ≤ D) :
    (a ^ D) ^ (1 / (D : ℝ)) = a := by
  have hD_pos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr (by omega)
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha, mul_one_div_cancel (ne_of_gt hD_pos), Real.rpow_one]

/-- If $0 \le a, b$, $D \ge 1$, and $a^D \le b$, then $a \le b^{1/D}$. -/
lemma le_rpow_inv_nat_of_pow_le {a b : ℝ} {D : ℕ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hD : 1 ≤ D) (h : a ^ D ≤ b) :
    a ≤ b ^ (1 / (D : ℝ)) := by
  have h1 : (a ^ D) ^ (1 / (D : ℝ)) ≤ b ^ (1 / (D : ℝ)) :=
    Real.rpow_le_rpow (by positivity) h (by positivity)
  rwa [pow_rpow_inv_nat ha hD] at h1

/-- If $0 \le a, b$, $D \ge 1$, and $a < b^D$, then $a^{1/D} < b$. -/
lemma rpow_inv_nat_lt_of_lt_pow {a b : ℝ} {D : ℕ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hD : 1 ≤ D) (h : a < b ^ D) :
    a ^ (1 / (D : ℝ)) < b := by
  have h1 : a ^ (1 / (D : ℝ)) < (b ^ D) ^ (1 / (D : ℝ)) :=
    Real.rpow_lt_rpow ha h (by positivity)
  rwa [pow_rpow_inv_nat hb hD] at h1

/-!
## Section 3: Lemma 8(1) — Single-Step Three-Case $p_{\mathrm{cap}}$-Decoupled Gallai Core Extraction

Formalizes Lemma 8(1) (`main.tex` lines 421–426 & 447–453): running the canonical Gallai module
chain $W = M_0 \supsetneq M_1 \supsetneq \dots \supsetneq M_T$ while $|M_s| > \frac{1}{2}|W|$ and
$m_{\max}(F[M_s]) \ge \frac{1}{64}|W|$ produces an exact module $M_T \subseteq W$ of $F[W]$
(by Theorem 1(a)) satisfying at least one of **(Case G-Small-$k$)**, **(Case G-Large-$k$)**,
or **(Case G-Core)**.
-/

/-- Auxiliary induction for the canonical Gallai proper-module chain in $F[W]$, tracking
that every member $M_s$ of the chain is an exact module of $F[W]$ (`IsModuleIn F W M_s`). -/
lemma gallai_exact_module_chain_aux (F : SimpleGraph V) {W : Finset V} (hW : 64 ≤ W.card) :
    ∀ (n : ℕ) (M_s : Finset V),
      M_s.card ≤ n →
      IsModuleIn F W M_s →
      (W.card : ℝ) / 2 < (M_s.card : ℝ) →
      (∃ M_T : Finset V, IsModuleIn F W M_T ∧
        (W.card : ℝ) / 64 ≤ (M_T.card : ℝ) ∧ (M_T.card : ℝ) ≤ (W.card : ℝ) / 2) ∨
      (∃ M_T : Finset V, IsModuleIn F W M_T ∧
        (W.card : ℝ) / 2 < (M_T.card : ℝ) ∧ (mMax F M_T : ℝ) < (W.card : ℝ) / 64) := by
  intro n
  induction n with
  | zero =>
    intro M_s hMs_0 _ hMs_gt
    have : (M_s.card : ℝ) = 0 := by
      have : M_s.card = 0 := Nat.le_zero.mp hMs_0
      simp [this]
    have hW_pos : (0 : ℝ) < (W.card : ℝ) := Nat.cast_pos.mpr (by omega)
    linarith
  | succ m ih =>
    intro M_s hMs_n hMs_mod hMs_gt
    by_cases hmMax_lt : (mMax F M_s : ℝ) < (W.card : ℝ) / 64
    · exact Or.inr ⟨M_s, hMs_mod, hMs_gt, hmMax_lt⟩
    · push_neg at hmMax_lt
      have hMs_card2 : 2 ≤ M_s.card := by
        have hW_r : (64 : ℝ) ≤ (W.card : ℝ) := Nat.ofNat_le_cast.mpr hW
        exact_mod_cast (by linarith : (2 : ℝ) ≤ (M_s.card : ℝ))
      obtain ⟨M_next, hM_prop, hM_card_eq⟩ := exists_isProperModuleIn_card_eq_mMax hMs_card2
      have hM_mod_W : IsModuleIn F W M_next := isModuleIn_trans hMs_mod hM_prop.2.2
      have hM_ge_64 : (W.card : ℝ) / 64 ≤ (M_next.card : ℝ) := by
        rw [hM_card_eq]
        exact hmMax_lt
      have hM_lt : M_next.card < M_s.card := Finset.card_lt_card hM_prop.2.1
      by_cases hM_le_half : (M_next.card : ℝ) ≤ (W.card : ℝ) / 2
      · exact Or.inl ⟨M_next, hM_mod_W, hM_ge_64, hM_le_half⟩
      · push_neg at hM_le_half
        exact ih M_next (by omega) hM_mod_W hM_le_half

/-- If $M_T \subseteq W$ is an exact module of $F[W]$ with $\frac{1}{64}|W| \le |M_T| \le \frac{1}{2}|W|$,
then $W$ contains a 2-block pure blockade of width at least $\frac{|W|}{64 \cdot 2^2}$ preserving $\Phi_8$. -/
lemma pure_two_blockade_of_exact_module {F : SimpleGraph V} {W M_T : Finset V}
    (hW : 64 ≤ W.card) (hmod : IsModuleIn F W M_T)
    (hMT_low : (W.card : ℝ) / 64 ≤ (M_T.card : ℝ))
    (hMT_high : (M_T.card : ℝ) ≤ (W.card : ℝ) / 2) :
    ∃ U : Fin 2 → Finset V,
      IsPureBlockadeIn F W 2 ((W.card : ℝ) / (64 * (2 : ℝ) ^ 2)) U ∧
      (W.card : ℝ) ^ (1 / 8 : ℝ) ≤ ∑ j : Fin 2, ((U j).card : ℝ) ^ (1 / 8 : ℝ) := by
  let R := W \ M_T
  let R_pos := R.filter (fun z => ∀ u ∈ M_T, F.Adj z u)
  let R_neg := R \ R_pos
  have hR_pos_sub : R_pos ⊆ R := Finset.filter_subset _ _
  have hR_neg_sub : R_neg ⊆ R := Finset.sdiff_subset
  have hR_pos_W : R_pos ⊆ W := hR_pos_sub.trans Finset.sdiff_subset
  have hR_neg_W : R_neg ⊆ W := hR_neg_sub.trans Finset.sdiff_subset
  have hR_pos_disj : Disjoint R_pos M_T :=
    Finset.disjoint_of_subset_left hR_pos_sub Finset.sdiff_disjoint
  have hR_neg_disj : Disjoint R_neg M_T :=
    Finset.disjoint_of_subset_left hR_neg_sub Finset.sdiff_disjoint
  have hR_pos_comp : IsCompletePair F R_pos M_T :=
    fun z hz u hu => (Finset.mem_filter.mp hz).2 u hu
  have hR_neg_anti : IsAnticompletePair F R_neg M_T := by
    intro z hz u hu
    obtain ⟨hzR, hz_not⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨hzW, hz_notM⟩ := Finset.mem_sdiff.mp hzR
    rcases hmod.2 z hzW hz_notM with hcomp | hanti
    · exact False.elim (hz_not (Finset.mem_filter.mpr ⟨hzR, hcomp⟩))
    · exact hanti u hu
  have h_cards : (R_pos.card : ℝ) + (R_neg.card : ℝ) + (M_T.card : ℝ) = (W.card : ℝ) := by
    have h1 : (R_neg.card : ℝ) + (R_pos.card : ℝ) = (R.card : ℝ) := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card hR_pos_sub
    have h2 : (R.card : ℝ) + (M_T.card : ℝ) = (W.card : ℝ) := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card hmod.1
    linarith
  by_cases h_half : R_neg.card ≤ R_pos.card
  · have h_r : (R_neg.card : ℝ) ≤ (R_pos.card : ℝ) := Nat.cast_le.mpr h_half
    have h_pure := isPureBlockadeIn_two (by omega) hR_pos_W hmod.1 hR_pos_disj
      (Or.inl hR_pos_comp) (by linarith) (by linarith)
    exact ⟨![R_pos, M_T], h_pure, potential_conservation_of_width le_rfl h_pure.1.width_ge⟩
  · have h_r : (R_pos.card : ℝ) ≤ (R_neg.card : ℝ) := Nat.cast_le.mpr (by omega)
    have h_pure := isPureBlockadeIn_two (by omega) hR_neg_W hmod.1 hR_neg_disj
      (Or.inr hR_neg_anti) (by linarith) (by linarith)
    exact ⟨![R_neg, M_T], h_pure, potential_conservation_of_width le_rfl h_pure.1.width_ge⟩

/-- **Lemma 8(1) (`three_case_gallai_core_extraction`, Single-Step Three-Case $p_{\mathrm{cap}}$-Decoupled Gallai Core Extraction)**:
For $\ell \ge 16$, $p_{\mathrm{cap}} \ge \ell$, $\theta \in (0, \frac{1}{64\ell^2}]$, and $W \subseteq V$
with $|W| \ge 64 p_{\mathrm{cap}}^2 \theta^{-1}$, there exists an exact module $M_T \subseteq W$ of $F[W]$
satisfying at least one of **(Case G-Small-$k$)**, **(Case G-Large-$k$)**, or **(Case G-Core)**. -/
theorem three_case_gallai_core_extraction (F : SimpleGraph V) (W : Finset V)
    (ℓ p_cap : ℕ) (θ : ℝ)
    (hℓ : 16 ≤ ℓ) (hp_cap : ℓ ≤ p_cap)
    (hθ_pos : 0 < θ) (hθ_ub : θ ≤ 1 / (64 * (ℓ : ℝ) ^ 2))
    (hW_card : 64 * (p_cap : ℝ) ^ 2 * θ⁻¹ ≤ (W.card : ℝ)) :
    ∃ M_T ⊆ W, IsModuleIn F W M_T ∧
      (-- (Case G-Small-k)
       (∃ (k : ℕ) (U : Fin k → Finset V),
          2 ≤ k ∧ k < p_cap ∧
          IsPureBlockadeIn F W k ((W.card : ℝ) / (64 * (k : ℝ) ^ 2)) U ∧
          (W.card : ℝ) ^ (1 / 8 : ℝ) ≤ ∑ j : Fin k, ((U j).card : ℝ) ^ (1 / 8 : ℝ)) ∨
       -- (Case G-Large-k)
       (∃ Q : Fin p_cap → Finset V,
          IsPureBlockadeIn F W p_cap (θ * (W.card : ℝ)) Q ∧
          (∀ j : Fin p_cap, IsModuleIn F W (Q j))) ∨
       -- (Case G-Core)
       ((W.card : ℝ) / 2 < (M_T.card : ℝ) ∧
        ∃ M_star ⊆ M_T,
          (15 / 64 : ℝ) * (W.card : ℝ) < (M_star.card : ℝ) ∧
          (∀ X : Finset V, IsProperModuleIn F M_T X → (X ∩ M_star).Nonempty →
            X ⊆ M_star ∧ (X.card : ℝ) < θ * (W.card : ℝ) ∧
            (X.card : ℝ) < 5 * θ * (M_star.card : ℝ)))) := by
  have hp_cap_ge_16 : 16 ≤ p_cap := le_trans hℓ hp_cap
  have hp_cap_r : (16 : ℝ) ≤ (p_cap : ℝ) := Nat.ofNat_le_cast.mpr hp_cap_ge_16
  have hℓ_r : (16 : ℝ) ≤ (ℓ : ℝ) := Nat.ofNat_le_cast.mpr hℓ
  have hθ_inv_ge : 64 * (ℓ : ℝ) ^ 2 ≤ θ⁻¹ := by
    have h1 := one_div_le_one_div_of_le hθ_pos hθ_ub
    simpa using h1
  have hW_ge_64_r : (64 : ℝ) ≤ (W.card : ℝ) := by
    have h1 : (1 : ℝ) ≤ (p_cap : ℝ) ^ 2 * θ⁻¹ := by
      have : (1 : ℝ) ≤ θ⁻¹ := by nlinarith
      have : (1 : ℝ) ≤ (p_cap : ℝ) ^ 2 := by nlinarith
      nlinarith
    nlinarith
  have hW_ge_64 : 64 ≤ W.card := by exact_mod_cast hW_ge_64_r
  have hW_half_lt : (W.card : ℝ) / 2 < (W.card : ℝ) := by linarith
  rcases gallai_exact_module_chain_aux F hW_ge_64 W.card W le_rfl (isModuleIn_self F W) hW_half_lt with
    ⟨M_T, hMT_mod, hMT_low, hMT_high⟩ | ⟨M_T, hMT_mod, hMT_gt, hmMax_lt⟩
  · obtain ⟨U, hU_pure, hU_pot⟩ := pure_two_blockade_of_exact_module hW_ge_64 hMT_mod hMT_low hMT_high
    exact ⟨M_T, hMT_mod.1, hMT_mod, Or.inl ⟨2, U, le_rfl, by omega, hU_pure, hU_pot⟩⟩
  · refine ⟨M_T, hMT_mod.1, hMT_mod, ?_⟩
    have hMT_card2 : 2 ≤ M_T.card := by
      exact_mod_cast (by linarith : (2 : ℝ) ≤ (M_T.card : ℝ))
    have hmMax_2 : 2 * mMax F M_T < M_T.card := by
      exact_mod_cast (by linarith : (2 : ℝ) * (mMax F M_T : ℝ) < (M_T.card : ℝ))
    obtain ⟨hconn, haconn⟩ := connected_and_anticonnected_of_two_mul_mMax_lt hMT_card2 hmMax_2
    obtain ⟨t, Q, hQ_max, hQ_pure, hQ_biUnion, hQ_sum, hQ_mono, hQ_sup⟩ :=
      gallai_prime_partition hMT_card2 hconn haconn
    have hQ_mod_W : ∀ j : Fin t, IsModuleIn F W (Q j) :=
      fun j => isModuleIn_trans hMT_mod (hQ_max j).1.2.2
    have hQ_lt_64 : ∀ j : Fin t, ((Q j).card : ℝ) < (W.card : ℝ) / 64 := by
      intro j
      have hle : (Q j).card ≤ mMax F M_T := card_le_mMax_of_isProperModuleIn (hQ_max j).1
      have hle_r : ((Q j).card : ℝ) ≤ (mMax F M_T : ℝ) := Nat.cast_le.mpr hle
      linarith
    by_cases h_small : ∃ (k : ℕ) (hk : 2 ≤ k ∧ k ≤ min t (p_cap - 1)),
        (W.card : ℝ) / (64 * (k : ℝ) ^ 2) ≤ ((Q ⟨k - 1, by omega⟩).card : ℝ)
    · -- (Case G-Small-k)
      left
      obtain ⟨k, ⟨hk2, hk_min⟩, hk_width⟩ := h_small
      have hkt : k ≤ t := le_trans hk_min (Nat.min_le_left _ _)
      have hkp : k < p_cap := by
        have := le_trans hk_min (Nat.min_le_right t (p_cap - 1))
        omega
      let U : Fin k → Finset V := fun j => Q ⟨j.1, by omega⟩
      have hU_width : ∀ j : Fin k, (W.card : ℝ) / (64 * (k : ℝ) ^ 2) ≤ ((U j).card : ℝ) := by
        intro j
        have hj_le : (⟨j.1, by omega⟩ : Fin t) ≤ ⟨k - 1, by omega⟩ := by
          simp only [Fin.mk_le_mk]; omega
        exact le_trans hk_width (Nat.cast_le.mpr (hQ_mono _ _ hj_le))
      have hU_pure : IsPureBlockadeIn F W k ((W.card : ℝ) / (64 * (k : ℝ) ^ 2)) U := by
        refine ⟨⟨fun j => (hQ_mod_W ⟨j.1, by omega⟩).1, fun j => (hQ_max ⟨j.1, by omega⟩).1.1, ?_, hU_width⟩, ?_⟩
        · intro j₁ j₂ hj
          have hj' : (⟨j₁.1, by omega⟩ : Fin t) ≠ ⟨j₂.1, by omega⟩ :=
            fun h => hj (Fin.ext (Fin.mk.inj_iff.mp h))
          exact (hQ_pure _ _ hj').1
        · intro j₁ j₂ hj
          have hj' : (⟨j₁.1, by omega⟩ : Fin t) ≠ ⟨j₂.1, by omega⟩ :=
            fun h => hj (Fin.ext (Fin.mk.inj_iff.mp h))
          exact (hQ_pure _ _ hj').2
      exact ⟨k, U, hk2, hkp, hU_pure, potential_conservation_of_width hk2 hU_width⟩
    · push_neg at h_small
      by_cases h_large : ∃ hpt : p_cap ≤ t, θ * (W.card : ℝ) ≤ ((Q ⟨p_cap - 1, by omega⟩).card : ℝ)
      · -- (Case G-Large-k)
        right; left
        obtain ⟨hpt, h_width⟩ := h_large
        let Q' : Fin p_cap → Finset V := fun j => Q ⟨j.1, by omega⟩
        have hQ'_width : ∀ j : Fin p_cap, θ * (W.card : ℝ) ≤ ((Q' j).card : ℝ) := by
          intro j
          have hj_le : (⟨j.1, by omega⟩ : Fin t) ≤ ⟨p_cap - 1, by omega⟩ := by
            simp only [Fin.mk_le_mk]; omega
          exact le_trans h_width (Nat.cast_le.mpr (hQ_mono _ _ hj_le))
        refine ⟨Q', ⟨⟨fun j => (hQ_mod_W ⟨j.1, by omega⟩).1, fun j => (hQ_max ⟨j.1, by omega⟩).1.1, ?_, hQ'_width⟩, ?_⟩,
          fun j => hQ_mod_W ⟨j.1, by omega⟩⟩
        · intro j₁ j₂ hj
          have hj' : (⟨j₁.1, by omega⟩ : Fin t) ≠ ⟨j₂.1, by omega⟩ :=
            fun h => hj (Fin.ext (Fin.mk.inj_iff.mp h))
          exact (hQ_pure _ _ hj').1
        · intro j₁ j₂ hj
          have hj' : (⟨j₁.1, by omega⟩ : Fin t) ≠ ⟨j₂.1, by omega⟩ :=
            fun h => hj (Fin.ext (Fin.mk.inj_iff.mp h))
          exact (hQ_pure _ _ hj').2
      · -- (Case G-Core)
        right; right
        push_neg at h_large
        refine ⟨hMT_gt, ?_⟩
        let I_star := Finset.univ.filter (fun j : Fin t => ((Q j).card : ℝ) < θ * (W.card : ℝ))
        let I_bad := Finset.univ.filter (fun j : Fin t => ¬(((Q j).card : ℝ) < θ * (W.card : ℝ)))
        have hI_union : I_bad ∪ I_star = Finset.univ := by
          ext j; simp only [I_star, I_bad, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]; tauto
        have hI_disj : Disjoint I_bad I_star := by
          rw [Finset.disjoint_left]
          intro j hj1 hj2
          exact (Finset.mem_filter.mp hj1).2 (Finset.mem_filter.mp hj2).2
        have h_bad_sub : ∀ j ∈ I_bad, j.1 + 1 ≤ p_cap - 1 ∧
            ((Q j).card : ℝ) ≤ (W.card : ℝ) / 64 * ((1 : ℝ) / ((j.1 + 1 : ℕ) : ℝ) ^ 2) := by
          intro j hj
          have hj_ge_θ : θ * (W.card : ℝ) ≤ ((Q j).card : ℝ) := by
            have := (Finset.mem_filter.mp hj).2; linarith
          have hj_lt_p : j.1 + 1 ≤ p_cap - 1 := by
            by_contra h_ge
            push_neg at h_ge
            have hpt : p_cap ≤ t := by omega
            have hj_ge_idx : (⟨p_cap - 1, by omega⟩ : Fin t) ≤ j := by
              simp only [Fin.le_def]; omega
            have h_mono := Nat.cast_le (α := ℝ).mpr (hQ_mono _ _ hj_ge_idx)
            have h_lt := h_large hpt
            linarith
          refine ⟨hj_lt_p, ?_⟩
          by_cases hj0 : j.1 = 0
          · have h1 := hQ_lt_64 j
            rw [hj0]; norm_num; linarith
          · have hk2 : 2 ≤ j.1 + 1 ∧ j.1 + 1 ≤ min t (p_cap - 1) := ⟨by omega, by omega⟩
            have h1 := h_small (j.1 + 1) hk2
            have hj_eq : (⟨j.1 + 1 - 1, by omega⟩ : Fin t) = j := by ext; dsimp
            rw [hj_eq] at h1
            have h_eq : (W.card : ℝ) / (64 * ((j.1 + 1 : ℕ) : ℝ) ^ 2) =
                (W.card : ℝ) / 64 * ((1 : ℝ) / ((j.1 + 1 : ℕ) : ℝ) ^ 2) := by ring
            linarith
        have h_bad_sum : ∑ j ∈ I_bad, ((Q j).card : ℝ) < (W.card : ℝ) / 32 := by
          have h1 : ∑ j ∈ I_bad, ((Q j).card : ℝ) ≤
              ∑ j ∈ I_bad, (W.card : ℝ) / 64 * ((1 : ℝ) / ((j.1 + 1 : ℕ) : ℝ) ^ 2) :=
            Finset.sum_le_sum (fun j hj => (h_bad_sub j hj).2)
          rw [← Finset.mul_sum] at h1
          have h_inj : ∑ j ∈ I_bad, (1 : ℝ) / ((j.1 + 1 : ℕ) : ℝ) ^ 2 ≤
              ∑ k ∈ Finset.Icc 1 p_cap, (1 : ℝ) / (k : ℝ) ^ 2 := by
            have h_img : Finset.image (fun j : Fin t => j.1 + 1) I_bad ⊆ Finset.Icc 1 p_cap := by
              intro k hk
              obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
              have hj' := (h_bad_sub j hj).1
              simp only [Finset.mem_Icc]; omega
            rw [← Finset.sum_image (f := fun k : ℕ => (1 : ℝ) / (k : ℝ) ^ 2)
              (fun j₁ _ j₂ _ h => by ext; omega)]
            exact Finset.sum_le_sum_of_subset_of_nonneg h_img (fun _ _ _ => by positivity)
          have h_lt2 := sum_inv_sq_Icc_lt_two 0 p_cap
          have h_mul : (W.card : ℝ) / 64 * ∑ j ∈ I_bad, (1 : ℝ) / ((j.1 + 1 : ℕ) : ℝ) ^ 2 <
              (W.card : ℝ) / 64 * 2 :=
            mul_lt_mul_of_pos_left (lt_of_le_of_lt h_inj h_lt2) (by positivity)
          linarith
        let M_star := I_star.biUnion Q
        have hM_star_sub : M_star ⊆ M_T := by
          rw [← hQ_biUnion]
          exact Finset.biUnion_subset_biUnion_of_subset_left Q (Finset.filter_subset _ _)
        have hM_star_card_eq : (M_star.card : ℝ) = ∑ j ∈ I_star, ((Q j).card : ℝ) := by
          unfold M_star
          rw [Finset.card_biUnion (fun i _ j _ hij => (hQ_pure i j hij).1)]
          push_cast; rfl
        have h_total_sum : ∑ j ∈ I_bad, ((Q j).card : ℝ) + ∑ j ∈ I_star, ((Q j).card : ℝ) =
            (M_T.card : ℝ) := by
          rw [← Finset.sum_union hI_disj, hI_union]
          exact_mod_cast hQ_sum
        have hM_star_gt : (15 / 64 : ℝ) * (W.card : ℝ) < (M_star.card : ℝ) := by linarith
        refine ⟨M_star, hM_star_sub, hM_star_gt, ?_⟩
        intro X hX_prop hX_inter
        obtain ⟨j, hj_sup⟩ := hQ_sup X hX_prop
        obtain ⟨x₀, hx₀⟩ := hX_inter
        obtain ⟨hx₀X, hx₀M⟩ := Finset.mem_inter.mp hx₀
        obtain ⟨j', hj'_star, hx₀Qj'⟩ := Finset.mem_biUnion.mp hx₀M
        have hjj' : j = j' := by
          by_contra hne
          exact Finset.disjoint_left.mp (hQ_pure j j' hne).1 (hj_sup hx₀X) hx₀Qj'
        have hj_star : j ∈ I_star := hjj' ▸ hj'_star
        have hX_sub_Mstar : X ⊆ M_star :=
          hj_sup.trans (Finset.subset_biUnion_of_mem Q hj_star)
        have hX_lt_θW : (X.card : ℝ) < θ * (W.card : ℝ) := by
          have h_le : (X.card : ℝ) ≤ ((Q j).card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hj_sup)
          exact lt_of_le_of_lt h_le (Finset.mem_filter.mp hj_star).2
        have hW_lt_5M : (W.card : ℝ) < 5 * (M_star.card : ℝ) := by linarith
        refine ⟨hX_sub_Mstar, hX_lt_θW, ?_⟩
        calc (X.card : ℝ) < θ * (W.card : ℝ) := hX_lt_θW
          _ < θ * (5 * (M_star.card : ℝ)) := mul_lt_mul_of_pos_left hW_lt_5M hθ_pos
          _ = 5 * θ * (M_star.card : ℝ) := by ring

/-!
## Section 4: Lemma 8(2) — Iterated Gallai Core Decomposition with Separated Split and Cap Widths

Formalizes Lemma 8(2) (`main.tex` lines 427–432 & 454–460): iteratively applying Lemma 8(1) to the
largest leaf $W_z$ ($|W_z| > |B| / L_{\max}^8$) of a $\Phi_8$-preserving pairwise-pure partition tree
$\mathcal{T}_0$ while $|\mathcal{L}(\mathcal{T}_0)| < L_{\max}$ yields **(GC1-Core)**,
**(GC2-PureSplit)** (of $\theta$/$p_{\mathrm{cap}}$-independent width $\frac{|B|}{64 k^{10}}$ for
some $k \in [L_{\max}, p_{\mathrm{cap}} - 1]$), or **(GC2-Cap)** (of exact length $p_{\mathrm{cap}}$).
-/

/-- Auxiliary induction growing the partition tree $\mathcal{T}_0$ on $B$ while $|\mathcal{L}(\mathcal{T}_0)| < L_{\max}$. -/
lemma iterated_gallai_core_aux (F : SimpleGraph V) (B : Finset V)
    (ℓ p_cap L_max : ℕ) (θ : ℝ)
    (hℓ : 16 ≤ ℓ) (hp_cap : ℓ ≤ p_cap) (hL_low : 2 ≤ L_max) (hL_high : L_max ≤ ℓ)
    (hθ_pos : 0 < θ) (hθ_ub : θ ≤ 1 / (64 * (ℓ : ℝ) ^ 2))
    (hB_card : 64 * (p_cap : ℝ) ^ 2 * θ⁻¹ * (4 * (ℓ : ℝ)) ^ 16 ≤ (B.card : ℝ)) :
    ∀ (n : ℕ) (L_set : Finset (Finset V)),
      L_max - L_set.card ≤ n →
      L_set.Nonempty →
      (∀ A ∈ L_set, A ⊆ B ∧ A.Nonempty ∧
        (B.card : ℝ) / (64 * (L_max : ℝ) ^ 10) ≤ (A.card : ℝ)) →
      (∀ A ∈ L_set, ∀ B' ∈ L_set, A ≠ B' → Disjoint A B' ∧ IsPurePair F A B') →
      (B.card : ℝ) ^ (1 / 8 : ℝ) ≤ ∑ A ∈ L_set, (A.card : ℝ) ^ (1 / 8 : ℝ) →
      -- (GC1-Core)
      (∃ W ⊆ B, (B.card : ℝ) / (L_max : ℝ) ^ 8 < (W.card : ℝ) ∧
        ∃ M_T ⊆ W, IsModuleIn F W M_T ∧ (W.card : ℝ) / 2 < (M_T.card : ℝ) ∧
        ∃ M_star ⊆ M_T, (15 / 64 : ℝ) * (W.card : ℝ) < (M_star.card : ℝ) ∧
        (∀ X : Finset V, IsProperModuleIn F M_T X → (X ∩ M_star).Nonempty →
          X ⊆ M_star ∧ (X.card : ℝ) < 5 * θ * (M_star.card : ℝ))) ∨
      -- (GC2-PureSplit)
      (L_max < p_cap ∧ ∃ (k : ℕ) (U : Fin k → Finset V),
        L_max ≤ k ∧ k < p_cap ∧
        IsPureBlockadeIn F B k ((B.card : ℝ) / (64 * (k : ℝ) ^ 10)) U) ∨
      -- (GC2-Cap)
      (∃ Q : Fin p_cap → Finset V,
        IsPureBlockadeIn F B p_cap
          (min θ (1 / (64 * (p_cap : ℝ) ^ 2)) * ((B.card : ℝ) / (L_max : ℝ) ^ 8)) Q) := by
  have hℓ_r : (16 : ℝ) ≤ (ℓ : ℝ) := Nat.ofNat_le_cast.mpr hℓ
  have hL_r2 : (2 : ℝ) ≤ (L_max : ℝ) := Nat.ofNat_le_cast.mpr hL_low
  have hL_rℓ : (L_max : ℝ) ≤ (ℓ : ℝ) := Nat.cast_le.mpr hL_high
  have hp_cap_pos : (0 : ℝ) < (p_cap : ℝ) := Nat.cast_pos.mpr (by omega)
  have hℓ_pos : (0 : ℝ) < (ℓ : ℝ) := Nat.cast_pos.mpr (by omega)
  have hB_pos : (0 : ℝ) < (B.card : ℝ) := by
    have : (0 : ℝ) < 64 * (p_cap : ℝ) ^ 2 * θ⁻¹ * (4 * (ℓ : ℝ)) ^ 16 := by positivity
    linarith
  intro n
  induction n with
  | zero =>
    intro L_set h_rem hL_ne hL_sub hL_pair _hL_pot
    have hL_ge : L_max ≤ L_set.card := by omega
    obtain ⟨q, L, hq_eq, hL_inj, _, hL_mem, _, _⟩ := exists_sorted_equiv_of_finset L_set
    have hL_le_q : L_max ≤ q := hq_eq ▸ hL_ge
    by_cases hL_lt_p : L_max < p_cap
    · -- (GC2-PureSplit) with k = L_max
      right; left
      refine ⟨hL_lt_p, L_max, fun j => L ⟨j.1, by omega⟩, le_rfl, hL_lt_p, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · intro j; exact (hL_sub _ (hL_mem ⟨j.1, by omega⟩)).1
      · intro j; exact (hL_sub _ (hL_mem ⟨j.1, by omega⟩)).2.1
      · intro j₁ j₂ hj
        have hj' : (⟨j₁.1, by omega⟩ : Fin q) ≠ ⟨j₂.1, by omega⟩ :=
          fun h => hj (Fin.ext (Fin.mk.inj_iff.mp h))
        exact (hL_pair _ (hL_mem _) _ (hL_mem _) (fun h => hj' (hL_inj h))).1
      · intro j; exact (hL_sub _ (hL_mem ⟨j.1, by omega⟩)).2.2
      · intro j₁ j₂ hj
        have hj' : (⟨j₁.1, by omega⟩ : Fin q) ≠ ⟨j₂.1, by omega⟩ :=
          fun h => hj (Fin.ext (Fin.mk.inj_iff.mp h))
        exact (hL_pair _ (hL_mem _) _ (hL_mem _) (fun h => hj' (hL_inj h))).2
    · -- L_max = p_cap, so (GC2-Cap)
      right; right
      have hL_eq_p : L_max = p_cap := by omega
      have hL_eq_p_r : (L_max : ℝ) = (p_cap : ℝ) := Nat.cast_inj.mpr hL_eq_p
      have hp_le_q : p_cap ≤ q := hL_eq_p ▸ hL_le_q
      refine ⟨fun j => L ⟨j.1, by omega⟩, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · intro j; exact (hL_sub _ (hL_mem ⟨j.1, by omega⟩)).1
      · intro j; exact (hL_sub _ (hL_mem ⟨j.1, by omega⟩)).2.1
      · intro j₁ j₂ hj
        have hj' : (⟨j₁.1, by omega⟩ : Fin q) ≠ ⟨j₂.1, by omega⟩ :=
          fun h => hj (Fin.ext (Fin.mk.inj_iff.mp h))
        exact (hL_pair _ (hL_mem _) _ (hL_mem _) (fun h => hj' (hL_inj h))).1
      · intro j
        have h1 := (hL_sub _ (hL_mem ⟨j.1, by omega⟩)).2.2
        rw [hL_eq_p_r] at h1 ⊢
        have h_min : min θ (1 / (64 * (p_cap : ℝ) ^ 2)) ≤ 1 / (64 * (p_cap : ℝ) ^ 2) := min_le_right _ _
        have h_le : min θ (1 / (64 * (p_cap : ℝ) ^ 2)) * ((B.card : ℝ) / (p_cap : ℝ) ^ 8) ≤
            (B.card : ℝ) / (64 * (p_cap : ℝ) ^ 10) := by
          calc min θ (1 / (64 * (p_cap : ℝ) ^ 2)) * ((B.card : ℝ) / (p_cap : ℝ) ^ 8)
              ≤ (1 / (64 * (p_cap : ℝ) ^ 2)) * ((B.card : ℝ) / (p_cap : ℝ) ^ 8) :=
                mul_le_mul_of_nonneg_right h_min (by positivity)
            _ = (B.card : ℝ) / (64 * (p_cap : ℝ) ^ 10) := by ring
        exact le_trans h_le h1
      · intro j₁ j₂ hj
        have hj' : (⟨j₁.1, by omega⟩ : Fin q) ≠ ⟨j₂.1, by omega⟩ :=
          fun h => hj (Fin.ext (Fin.mk.inj_iff.mp h))
        exact (hL_pair _ (hL_mem _) _ (hL_mem _) (fun h => hj' (hL_inj h))).2
  | succ m ih =>
    intro L_set h_rem hL_ne hL_sub hL_pair hL_pot
    by_cases hL_ge : L_max ≤ L_set.card
    · exact ih L_set (by omega) hL_ne hL_sub hL_pair hL_pot
    · push_neg at hL_ge
      obtain ⟨W, hW_mem, hW_max⟩ := Finset.exists_max_image L_set Finset.card hL_ne
      have hW_gt_Lmax8 : (B.card : ℝ) / (L_max : ℝ) ^ 8 < (W.card : ℝ) := by
        have h_each : ∀ A ∈ L_set, (A.card : ℝ) ^ (1 / 8 : ℝ) ≤ (W.card : ℝ) ^ (1 / 8 : ℝ) := by
          intro A hA
          exact Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr (hW_max A hA)) (by positivity)
        have h_sum_le : ∑ A ∈ L_set, (A.card : ℝ) ^ (1 / 8 : ℝ) ≤
            (L_set.card : ℝ) * (W.card : ℝ) ^ (1 / 8 : ℝ) := by
          calc ∑ A ∈ L_set, (A.card : ℝ) ^ (1 / 8 : ℝ)
              ≤ ∑ _A ∈ L_set, (W.card : ℝ) ^ (1 / 8 : ℝ) := Finset.sum_le_sum h_each
            _ = (L_set.card : ℝ) * (W.card : ℝ) ^ (1 / 8 : ℝ) := by simp
        have h_card_lt : (L_set.card : ℝ) < (L_max : ℝ) := Nat.cast_lt.mpr hL_ge
        have hW_rpow_pos : (0 : ℝ) < (W.card : ℝ) ^ (1 / 8 : ℝ) :=
          Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Finset.card_pos.mpr (hL_sub W hW_mem).2.1)) _
        have h1 : (B.card : ℝ) ^ (1 / 8 : ℝ) < (W.card : ℝ) ^ (1 / 8 : ℝ) * (L_max : ℝ) := by
          calc (B.card : ℝ) ^ (1 / 8 : ℝ)
              ≤ (L_set.card : ℝ) * (W.card : ℝ) ^ (1 / 8 : ℝ) := le_trans hL_pot h_sum_le
            _ < (L_max : ℝ) * (W.card : ℝ) ^ (1 / 8 : ℝ) :=
                mul_lt_mul_of_pos_right h_card_lt hW_rpow_pos
            _ = (W.card : ℝ) ^ (1 / 8 : ℝ) * (L_max : ℝ) := mul_comm _ _
        have h2 : (B.card : ℝ) ^ (1 / 8 : ℝ) / (L_max : ℝ) < (W.card : ℝ) ^ (1 / 8 : ℝ) :=
          (div_lt_iff₀ (by positivity)).mpr h1
        have h3 : ((B.card : ℝ) ^ (1 / 8 : ℝ) / (L_max : ℝ)) ^ 8 < ((W.card : ℝ) ^ (1 / 8 : ℝ)) ^ 8 :=
          pow_lt_pow_left₀ h2 (by positivity) (by omega)
        have hB8 : ((B.card : ℝ) ^ (1 / 8 : ℝ)) ^ 8 = (B.card : ℝ) := by
          rw [show (1 / 8 : ℝ) = 1 / ((8 : ℕ) : ℝ) by norm_num]
          exact rpow_inv_nat_pow (Nat.cast_nonneg _) (by omega)
        have hW8 : ((W.card : ℝ) ^ (1 / 8 : ℝ)) ^ 8 = (W.card : ℝ) := by
          rw [show (1 / 8 : ℝ) = 1 / ((8 : ℕ) : ℝ) by norm_num]
          exact rpow_inv_nat_pow (Nat.cast_nonneg _) (by omega)
        rwa [div_pow, hB8, hW8] at h3
      have hW_precond : 64 * (p_cap : ℝ) ^ 2 * θ⁻¹ ≤ (W.card : ℝ) := by
        have hL8_le : (L_max : ℝ) ^ 8 ≤ (4 * (ℓ : ℝ)) ^ 16 := by
          calc (L_max : ℝ) ^ 8 ≤ (ℓ : ℝ) ^ 8 := pow_le_pow_left₀ (by positivity) hL_rℓ 8
            _ ≤ (4 * (ℓ : ℝ)) ^ 8 := pow_le_pow_left₀ (by positivity) (by linarith) 8
            _ ≤ (4 * (ℓ : ℝ)) ^ 16 := pow_le_pow_right₀ (by linarith) (by omega)
        have h1 : 64 * (p_cap : ℝ) ^ 2 * θ⁻¹ * (L_max : ℝ) ^ 8 ≤ (B.card : ℝ) := by
          calc 64 * (p_cap : ℝ) ^ 2 * θ⁻¹ * (L_max : ℝ) ^ 8
              ≤ 64 * (p_cap : ℝ) ^ 2 * θ⁻¹ * (4 * (ℓ : ℝ)) ^ 16 :=
                mul_le_mul_of_nonneg_left hL8_le (by positivity)
            _ ≤ (B.card : ℝ) := hB_card
        have h2 : 64 * (p_cap : ℝ) ^ 2 * θ⁻¹ ≤ (B.card : ℝ) / (L_max : ℝ) ^ 8 :=
          (le_div_iff₀ (by positivity)).mpr h1
        exact le_trans h2 (le_of_lt hW_gt_Lmax8)
      obtain ⟨M_T, hMT_W, hMT_mod, h_cases⟩ :=
        three_case_gallai_core_extraction F W ℓ p_cap θ hℓ hp_cap hθ_pos hθ_ub hW_precond
      rcases h_cases with ⟨k, U, hk2, hkp, hU_pure, hU_pot⟩ | ⟨Q, hQ_pure, _⟩ | ⟨hMT_gt, M_star, hMs_MT, hMs_gt, hMs_prop⟩
      · -- (Case G-Small-k)
        by_cases hk_ge_L : L_max ≤ k
        · -- k ∈ [L_max, p_cap - 1], giving (GC2-PureSplit)
          right; left
          refine ⟨by omega, k, U, hk_ge_L, hkp,
            ⟨fun j => (hU_pure.1.subset_ambient j).trans (hL_sub W hW_mem).1,
             hU_pure.1.nonempty_blocks, hU_pure.1.pairwise_disjoint, fun j => ?_⟩,
            hU_pure.2⟩
          have hk_r : (L_max : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hk_ge_L
          have hL8_k8 : (L_max : ℝ) ^ 8 ≤ (k : ℝ) ^ 8 := pow_le_pow_left₀ (by positivity) hk_r 8
          have h1 : (B.card : ℝ) / (64 * (k : ℝ) ^ 10) ≤ (W.card : ℝ) / (64 * (k : ℝ) ^ 2) := by
            calc (B.card : ℝ) / (64 * (k : ℝ) ^ 10)
                = ((B.card : ℝ) / (k : ℝ) ^ 8) / (64 * (k : ℝ) ^ 2) := by ring
              _ ≤ ((B.card : ℝ) / (L_max : ℝ) ^ 8) / (64 * (k : ℝ) ^ 2) :=
                  div_le_div_of_nonneg_right
                    (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) hL8_k8) (by positivity)
              _ ≤ (W.card : ℝ) / (64 * (k : ℝ) ^ 2) :=
                  div_le_div_of_nonneg_right (le_of_lt hW_gt_Lmax8) (by positivity)
          exact le_trans h1 (hU_pure.1.width_ge j)
        · -- 2 ≤ k < L_max: split W into U_1, ..., U_k in L_set
          push_neg at hk_ge_L
          have hU_inj : Function.Injective U := by
            intro j₁ j₂ hj
            by_contra hne
            obtain ⟨x, hx⟩ := hU_pure.1.nonempty_blocks j₁
            exact Finset.disjoint_left.mp (hU_pure.1.pairwise_disjoint j₁ j₂ hne) hx (hj ▸ hx)
          let U_set := Finset.univ.image U
          let L_set' := L_set.erase W ∪ U_set
          have h_disj_LU : Disjoint (L_set.erase W) U_set := by
            rw [Finset.disjoint_left]
            intro A hA_er hA_U
            obtain ⟨hAW_ne, hA_mem⟩ := Finset.mem_erase.mp hA_er
            obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hA_U
            obtain ⟨x, hx⟩ := hU_pure.1.nonempty_blocks j
            exact Finset.disjoint_left.mp (hL_pair (U j) hA_mem W hW_mem hAW_ne).1
              hx (hU_pure.1.subset_ambient j hx)
          have hL'_sub : ∀ A ∈ L_set', A ⊆ B ∧ A.Nonempty ∧
              (B.card : ℝ) / (64 * (L_max : ℝ) ^ 10) ≤ (A.card : ℝ) := by
            intro A hA
            rcases Finset.mem_union.mp hA with hA_er | hA_U
            · exact hL_sub A (Finset.erase_subset W L_set hA_er)
            · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hA_U
              refine ⟨(hU_pure.1.subset_ambient j).trans (hL_sub W hW_mem).1,
                hU_pure.1.nonempty_blocks j, ?_⟩
              have hk_L : (k : ℝ) ≤ (L_max : ℝ) := Nat.cast_le.mpr (le_of_lt hk_ge_L)
              have hk2_L2 : (k : ℝ) ^ 2 ≤ (L_max : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hk_L 2
              calc (B.card : ℝ) / (64 * (L_max : ℝ) ^ 10)
                  = ((B.card : ℝ) / (L_max : ℝ) ^ 8) / (64 * (L_max : ℝ) ^ 2) := by ring
                _ ≤ (W.card : ℝ) / (64 * (L_max : ℝ) ^ 2) :=
                    div_le_div_of_nonneg_right (le_of_lt hW_gt_Lmax8) (by positivity)
                _ ≤ (W.card : ℝ) / (64 * (k : ℝ) ^ 2) :=
                    div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
                      (mul_le_mul_of_nonneg_left hk2_L2 (by positivity))
                _ ≤ ((U j).card : ℝ) := hU_pure.1.width_ge j
          have hL'_pair : ∀ A ∈ L_set', ∀ B' ∈ L_set', A ≠ B' → Disjoint A B' ∧ IsPurePair F A B' := by
            intro A hA B' hB' hAB'
            rcases Finset.mem_union.mp hA with hA_er | hA_U <;>
              rcases Finset.mem_union.mp hB' with hB'_er | hB'_U
            · exact hL_pair A (Finset.erase_subset W L_set hA_er)
                B' (Finset.erase_subset W L_set hB'_er) hAB'
            · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hB'_U
              obtain ⟨hAW_ne, hA_mem⟩ := Finset.mem_erase.mp hA_er
              have hAW := hL_pair A hA_mem W hW_mem hAW_ne
              exact ⟨Finset.disjoint_of_subset_right (hU_pure.1.subset_ambient j) hAW.1,
                isPurePair_mono hAW.2 Finset.Subset.rfl (hU_pure.1.subset_ambient j)⟩
            · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hA_U
              obtain ⟨hB'W_ne, hB'_mem⟩ := Finset.mem_erase.mp hB'_er
              have hWB' := hL_pair W hW_mem B' hB'_mem hB'W_ne.symm
              exact ⟨Finset.disjoint_of_subset_left (hU_pure.1.subset_ambient j) hWB'.1,
                isPurePair_mono hWB'.2 (hU_pure.1.subset_ambient j) Finset.Subset.rfl⟩
            · obtain ⟨j₁, _, rfl⟩ := Finset.mem_image.mp hA_U
              obtain ⟨j₂, _, rfl⟩ := Finset.mem_image.mp hB'_U
              have hj₁₂ : j₁ ≠ j₂ := fun h => hAB' (congr_arg U h)
              exact ⟨hU_pure.1.pairwise_disjoint j₁ j₂ hj₁₂, hU_pure.2 j₁ j₂ hj₁₂⟩
          have hL'_pot : (B.card : ℝ) ^ (1 / 8 : ℝ) ≤ ∑ A ∈ L_set', (A.card : ℝ) ^ (1 / 8 : ℝ) := by
            rw [Finset.sum_union h_disj_LU]
            have h_U_sum : ∑ A ∈ U_set, (A.card : ℝ) ^ (1 / 8 : ℝ) =
                ∑ j : Fin k, ((U j).card : ℝ) ^ (1 / 8 : ℝ) :=
              Finset.sum_image (fun j₁ _ j₂ _ h => hU_inj h)
            have h_er_sum := Finset.sum_erase_add L_set (fun A : Finset V => (A.card : ℝ) ^ (1 / 8 : ℝ)) hW_mem
            linarith
          have hL'_card : L_set'.card = L_set.card - 1 + k := by
            rw [Finset.card_union_of_disjoint h_disj_LU, Finset.card_erase_of_mem hW_mem,
              Finset.card_image_of_injective _ hU_inj, Finset.card_univ, Fintype.card_fin]
          have hW_pos_L : 1 ≤ L_set.card := Finset.card_pos.mpr ⟨W, hW_mem⟩
          have hL'_ne : L_set'.Nonempty := Finset.card_pos.mp (by omega)
          exact ih L_set' (by omega) hL'_ne hL'_sub hL'_pair hL'_pot
      · -- (Case G-Large-k) gives (GC2-Cap)
        right; right
        refine ⟨Q, ⟨fun j => (hQ_pure.1.subset_ambient j).trans (hL_sub W hW_mem).1,
          hQ_pure.1.nonempty_blocks, hQ_pure.1.pairwise_disjoint, fun j => ?_⟩, hQ_pure.2⟩
        have h_min : min θ (1 / (64 * (p_cap : ℝ) ^ 2)) ≤ θ := min_le_left _ _
        calc min θ (1 / (64 * (p_cap : ℝ) ^ 2)) * ((B.card : ℝ) / (L_max : ℝ) ^ 8)
            ≤ θ * ((B.card : ℝ) / (L_max : ℝ) ^ 8) :=
              mul_le_mul_of_nonneg_right h_min (by positivity)
          _ ≤ θ * (W.card : ℝ) := mul_le_mul_of_nonneg_left (le_of_lt hW_gt_Lmax8) (le_of_lt hθ_pos)
          _ ≤ ((Q j).card : ℝ) := hQ_pure.1.width_ge j
      · -- (Case G-Core) gives (GC1-Core)
        left
        refine ⟨W, (hL_sub W hW_mem).1, hW_gt_Lmax8, M_T, hMT_W, hMT_mod, hMT_gt,
          M_star, hMs_MT, hMs_gt, fun X hX hX_ne => ⟨(hMs_prop X hX hX_ne).1, (hMs_prop X hX hX_ne).2.2⟩⟩

/-- **Lemma 8(2) (`iterated_gallai_core_decomposition`, Iterated Gallai Core Decomposition on $F[B]$)**:
With parameterized stopping leaf threshold $L_{\max} \in [2, \ell]$ and $|B| \ge 64 p_{\mathrm{cap}}^2 \theta^{-1} (4\ell)^{16}$,
growing $\mathcal{T}_0$ from $W_{\mathrm{root}} = B$ yields **(GC1-Core)**, **(GC2-PureSplit)**, or **(GC2-Cap)**. -/
theorem iterated_gallai_core_decomposition (F : SimpleGraph V) (B : Finset V)
    (ℓ p_cap L_max : ℕ) (θ : ℝ)
    (hℓ : 16 ≤ ℓ) (hp_cap : ℓ ≤ p_cap) (hL_low : 2 ≤ L_max) (hL_high : L_max ≤ ℓ)
    (hθ_pos : 0 < θ) (hθ_ub : θ ≤ 1 / (64 * (ℓ : ℝ) ^ 2))
    (hB_card : 64 * (p_cap : ℝ) ^ 2 * θ⁻¹ * (4 * (ℓ : ℝ)) ^ 16 ≤ (B.card : ℝ)) :
    -- (GC1-Core)
    (∃ W ⊆ B, (B.card : ℝ) / (L_max : ℝ) ^ 8 < (W.card : ℝ) ∧
      ∃ M_T ⊆ W, IsModuleIn F W M_T ∧ (W.card : ℝ) / 2 < (M_T.card : ℝ) ∧
      ∃ M_star ⊆ M_T, (15 / 64 : ℝ) * (W.card : ℝ) < (M_star.card : ℝ) ∧
      (∀ X : Finset V, IsProperModuleIn F M_T X → (X ∩ M_star).Nonempty →
        X ⊆ M_star ∧ (X.card : ℝ) < 5 * θ * (M_star.card : ℝ))) ∨
    -- (GC2-PureSplit)
    (L_max < p_cap ∧ ∃ (k : ℕ) (U : Fin k → Finset V),
      L_max ≤ k ∧ k < p_cap ∧
      IsPureBlockadeIn F B k ((B.card : ℝ) / (64 * (k : ℝ) ^ 10)) U) ∨
    -- (GC2-Cap)
    (∃ Q : Fin p_cap → Finset V,
      IsPureBlockadeIn F B p_cap
        (min θ (1 / (64 * (p_cap : ℝ) ^ 2)) * ((B.card : ℝ) / (L_max : ℝ) ^ 8)) Q) := by
  have hp_cap_pos : (0 : ℝ) < (p_cap : ℝ) := Nat.cast_pos.mpr (by omega)
  have hℓ_pos : (0 : ℝ) < (ℓ : ℝ) := Nat.cast_pos.mpr (by omega)
  have hB_pos : (0 : ℝ) < (B.card : ℝ) := by
    have : (0 : ℝ) < 64 * (p_cap : ℝ) ^ 2 * θ⁻¹ * (4 * (ℓ : ℝ)) ^ 16 := by positivity
    linarith
  have hB_ne : B.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hB_pos)
  have h_L10 : (B.card : ℝ) / (64 * (L_max : ℝ) ^ 10) ≤ (B.card : ℝ) := by
    refine div_le_self (Nat.cast_nonneg _) ?_
    have : (2 : ℝ) ≤ (L_max : ℝ) := Nat.ofNat_le_cast.mpr hL_low
    have : (1 : ℝ) ≤ (L_max : ℝ) ^ 10 := one_le_pow₀ (by linarith)
    nlinarith
  exact iterated_gallai_core_aux F B ℓ p_cap L_max θ hℓ hp_cap hL_low hL_high hθ_pos hθ_ub hB_card
    (L_max - 1) {B} (by simp) (Finset.singleton_nonempty B)
    (fun A hA => by rw [Finset.mem_singleton.mp hA]; exact ⟨Finset.Subset.rfl, hB_ne, h_L10⟩)
    (fun A hA B' hB' hne => False.elim (hne ((Finset.mem_singleton.mp hA).trans (Finset.mem_singleton.mp hB').symm)))
    (by simp)

/-!
## Section 5: Lemma 8(3) — Generalized $\Phi_D$ Hereditary Active-Leaf Split Tree Dichotomy

Formalizes Lemma 8(3) (`main.tex` lines 433–444 & 462–470): maintains a rooted partition tree
`ActiveLeafSplitTree` on $B$ with potential $\Phi_D(\mathcal{T}) = \sum_{L \in \mathcal{L}(\mathcal{T})} |L|^{1/D}$
($D = 8 m \ge 64 r$). Because internal splits are applied **only to active leaves**
($|W_z| \ge L_{\max}^{-D} |B|$) via **(Split-$D$ Type I)** ($k \ge 4$, width $\ge 2^{-60} k^{-5D/8}|W_z|$)
or **(Split-$D$ Type II)** ($k \ge 2$, width $\ge 2^{-60r}|W_z|$), every leaf $L$ satisfies the
universal lower bound $|L| \ge 2^{-60r} L_{\max}^{-2D} |B| =: \beta_{D, L_{\max}} |B|$ with zero
leaves pruned, and hereditary cross-block weak $\eta_0$-sparsity/co-sparsity lifts to weak
$(\eta_0 \beta_{D, L_{\max}}^{-2})$-sparsity/co-sparsity across the first $L_{\max}$ leaves.
-/

/-- State of an active-leaf split tree $\mathcal{T}$ on a vertex subset $B \subseteq V$
(Lemma 8(3) of `main.tex`), parameterized by $r \ge 1$, $D = 8 m \ge 64$, stopping leaf threshold
$L_{\max} \ge 2$, and cross-block sparsity $\eta_0 \ge 0$. -/
structure ActiveLeafSplitTree (F : SimpleGraph V) (B : Finset V) (r D L_max : ℕ) (η₀ : ℝ) where
  leaves : Finset (Finset V)
  leaves_nonempty : leaves.Nonempty
  subset_B : ∀ L ∈ leaves, L ⊆ B ∧ L.Nonempty
  pairwise_disjoint : ∀ L₁ ∈ leaves, ∀ L₂ ∈ leaves, L₁ ≠ L₂ → Disjoint L₁ L₂
  potential_ge : (B.card : ℝ) ^ (1 / (D : ℝ)) ≤ ∑ L ∈ leaves, (L.card : ℝ) ^ (1 / (D : ℝ))
  leaf_width_ge : 2 ≤ leaves.card → ∀ L ∈ leaves,
    (B.card : ℝ) / ((2 : ℝ) ^ (60 * r) * (L_max : ℝ) ^ (2 * D)) ≤ (L.card : ℝ)
  ancestor_pair_sparse : ∀ L₁ ∈ leaves, ∀ L₂ ∈ leaves, L₁ ≠ L₂ →
    ∃ A₁ ⊆ B, ∃ A₂ ⊆ B, L₁ ⊆ A₁ ∧ L₂ ⊆ A₂ ∧ IsWeaklySparseOrCoSparsePair F A₁ A₂ η₀

/-- Root split tree $\mathcal{T}_{\mathrm{root}} = \{B\}$ on any nonempty subset $B \subseteq V$. -/
def ActiveLeafSplitTree.root (F : SimpleGraph V) (B : Finset V) (r D L_max : ℕ) (η₀ : ℝ)
    (hB : B.Nonempty) : ActiveLeafSplitTree F B r D L_max η₀ where
  leaves := {B}
  leaves_nonempty := Finset.singleton_nonempty B
  subset_B L hL := by rw [Finset.mem_singleton.mp hL]; exact ⟨Finset.Subset.rfl, hB⟩
  pairwise_disjoint L₁ hL₁ L₂ hL₂ hne :=
    False.elim (hne ((Finset.mem_singleton.mp hL₁).trans (Finset.mem_singleton.mp hL₂).symm))
  potential_ge := by simp
  leaf_width_ge h2 := by rw [Finset.card_singleton] at h2; omega
  ancestor_pair_sparse L₁ hL₁ L₂ hL₂ hne :=
    False.elim (hne ((Finset.mem_singleton.mp hL₁).trans (Finset.mem_singleton.mp hL₂).symm))

/-- While $|\mathcal{L}(\mathcal{T})| < L_{\max}$, the largest leaf $W_z \in \mathcal{L}(\mathcal{T})$
is active ($|W_z| \ge L_{\max}^{-D} |B|$). -/
lemma ActiveLeafSplitTree.exists_active_leaf {F : SimpleGraph V} {B : Finset V}
    {r D L_max : ℕ} {η₀ : ℝ} (T : ActiveLeafSplitTree F B r D L_max η₀)
    (hD : 1 ≤ D) (hL_lt : T.leaves.card < L_max) :
    ∃ W_z ∈ T.leaves, (B.card : ℝ) / (L_max : ℝ) ^ D ≤ (W_z.card : ℝ) := by
  obtain ⟨W_z, hWz_mem, hWz_max⟩ := Finset.exists_max_image T.leaves Finset.card T.leaves_nonempty
  refine ⟨W_z, hWz_mem, ?_⟩
  have hL_pos : (0 : ℝ) < (L_max : ℝ) := Nat.cast_pos.mpr (by omega)
  have h_each : ∀ A ∈ T.leaves, (A.card : ℝ) ^ (1 / (D : ℝ)) ≤ (W_z.card : ℝ) ^ (1 / (D : ℝ)) :=
    fun A hA => Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr (hWz_max A hA)) (by positivity)
  have h_sum : ∑ A ∈ T.leaves, (A.card : ℝ) ^ (1 / (D : ℝ)) ≤
      (W_z.card : ℝ) ^ (1 / (D : ℝ)) * (L_max : ℝ) := by
    calc ∑ A ∈ T.leaves, (A.card : ℝ) ^ (1 / (D : ℝ))
        ≤ ∑ _A ∈ T.leaves, (W_z.card : ℝ) ^ (1 / (D : ℝ)) := Finset.sum_le_sum h_each
      _ = (T.leaves.card : ℝ) * (W_z.card : ℝ) ^ (1 / (D : ℝ)) := by simp
      _ ≤ (L_max : ℝ) * (W_z.card : ℝ) ^ (1 / (D : ℝ)) :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (le_of_lt hL_lt)) (by positivity)
      _ = (W_z.card : ℝ) ^ (1 / (D : ℝ)) * (L_max : ℝ) := mul_comm _ _
  have h1 : (B.card : ℝ) ^ (1 / (D : ℝ)) / (L_max : ℝ) ≤ (W_z.card : ℝ) ^ (1 / (D : ℝ)) :=
    (div_le_iff₀ hL_pos).mpr (le_trans T.potential_ge h_sum)
  have h2 := pow_le_pow_left₀ (by positivity) h1 D
  rw [div_pow, rpow_inv_nat_pow (Nat.cast_nonneg _) hD, rpow_inv_nat_pow (Nat.cast_nonneg _) hD] at h2
  exact h2

/-- Potential increase for **Split-$D$ Type I** ($4 \le k$ with $k \ge 64$ or $D = 8 m \ge 88$)
and **Split-$D$ Type II** ($k \ge 2$ and $|U_q| \ge 2^{-60 r} |W_z|$ with $D \ge 64 r$). -/
lemma split_potential_increase {W_z : Finset V} {r m k : ℕ} {U : Fin k → Finset V}
    (hr : 1 ≤ r) (hm : 8 ≤ m) (hk2 : 2 ≤ k)
    (h_split :
      (4 ≤ k ∧ (64 ≤ k ∨ 11 ≤ m) ∧ ∀ q : Fin k,
        (W_z.card : ℝ) / ((2 : ℝ) ^ 60 * (k : ℝ) ^ (5 * m)) ≤ ((U q).card : ℝ)) ∨
      (64 * r ≤ 8 * m ∧ ∀ q : Fin k,
        (W_z.card : ℝ) / (2 : ℝ) ^ (60 * r) ≤ ((U q).card : ℝ))) :
    let D := 8 * m
    (16 * (W_z.card : ℝ)) ^ (1 / (D : ℝ)) ≤ ∑ q : Fin k, ((U q).card : ℝ) ^ (1 / (D : ℝ)) := by
  intro D
  have hD : 1 ≤ D := by unfold D; omega
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have h_each : ∀ q : Fin k,
      (16 * (W_z.card : ℝ)) ^ (1 / (D : ℝ)) / (k : ℝ) ≤ ((U q).card : ℝ) ^ (1 / (D : ℝ)) := by
    intro q
    refine le_rpow_inv_nat_of_pow_le (by positivity) (Nat.cast_nonneg _) hD ?_
    rw [div_pow, rpow_inv_nat_pow (by positivity) hD]
    rcases h_split with ⟨hk4, hk_or_m, hU_type1⟩ | ⟨hDr, hU_type2⟩
    · have h3m : (2 : ℝ) ^ 64 ≤ (k : ℝ) ^ (3 * m) := by
        rcases hk_or_m with hk64 | hm11
        · have hk_r : (2 : ℝ) ^ 6 ≤ (k : ℝ) := by
            have : (64 : ℝ) ≤ (k : ℝ) := Nat.ofNat_le_cast.mpr hk64
            norm_num at this ⊢; exact this
          have h1 : ((2 : ℝ) ^ 6) ^ (3 * m) ≤ (k : ℝ) ^ (3 * m) :=
            pow_le_pow_left₀ (by positivity) hk_r (3 * m)
          have h2 : (2 : ℝ) ^ 64 ≤ (2 : ℝ) ^ (18 * m) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          have h3 : ((2 : ℝ) ^ 6) ^ (3 * m) = (2 : ℝ) ^ (18 * m) := by rw [← pow_mul]; ring_nf
          linarith
        · have hk_r : (2 : ℝ) ^ 2 ≤ (k : ℝ) := by
            have : (4 : ℝ) ≤ (k : ℝ) := Nat.ofNat_le_cast.mpr hk4
            norm_num at this ⊢; exact this
          have h1 : ((2 : ℝ) ^ 2) ^ (3 * m) ≤ (k : ℝ) ^ (3 * m) :=
            pow_le_pow_left₀ (by positivity) hk_r (3 * m)
          have h2 : (2 : ℝ) ^ 64 ≤ (2 : ℝ) ^ (6 * m) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          have h3 : ((2 : ℝ) ^ 2) ^ (3 * m) = (2 : ℝ) ^ (6 * m) := by rw [← pow_mul]; ring_nf
          linarith
      have h_denom : 16 * ((2 : ℝ) ^ 60 * (k : ℝ) ^ (5 * m)) ≤ (k : ℝ) ^ D := by
        have h16 : (16 : ℝ) * (2 : ℝ) ^ 60 = (2 : ℝ) ^ 64 := by norm_num
        have hD_eq : D = 3 * m + 5 * m := by unfold D; omega
        calc 16 * ((2 : ℝ) ^ 60 * (k : ℝ) ^ (5 * m))
            = (2 : ℝ) ^ 64 * (k : ℝ) ^ (5 * m) := by rw [← mul_assoc, h16]
          _ ≤ (k : ℝ) ^ (3 * m) * (k : ℝ) ^ (5 * m) :=
              mul_le_mul_of_nonneg_right h3m (by positivity)
          _ = (k : ℝ) ^ D := by rw [← pow_add, ← hD_eq]
      have h_div : 16 * (W_z.card : ℝ) / (k : ℝ) ^ D ≤
          (W_z.card : ℝ) / ((2 : ℝ) ^ 60 * (k : ℝ) ^ (5 * m)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h1 := mul_le_mul_of_nonneg_left h_denom (Nat.cast_nonneg W_z.card)
        linarith
      exact le_trans h_div (hU_type1 q)
    · have hk_r : (2 : ℝ) ≤ (k : ℝ) := Nat.ofNat_le_cast.mpr hk2
      have h_denom : 16 * (2 : ℝ) ^ (60 * r) ≤ (k : ℝ) ^ D := by
        have h16 : (16 : ℝ) * (2 : ℝ) ^ (60 * r) = (2 : ℝ) ^ (60 * r + 4) := by
          rw [pow_add]; norm_num; ring
        have h2D : (2 : ℝ) ^ (60 * r + 4) ≤ (2 : ℝ) ^ D :=
          pow_le_pow_right₀ (by norm_num) (by unfold D; omega)
        have hkD : (2 : ℝ) ^ D ≤ (k : ℝ) ^ D := pow_le_pow_left₀ (by positivity) hk_r D
        linarith
      have h_div : 16 * (W_z.card : ℝ) / (k : ℝ) ^ D ≤
          (W_z.card : ℝ) / (2 : ℝ) ^ (60 * r) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h1 := mul_le_mul_of_nonneg_left h_denom (Nat.cast_nonneg W_z.card)
        linarith
      exact le_trans h_div (hU_type2 q)
  calc (16 * (W_z.card : ℝ)) ^ (1 / (D : ℝ))
      = (k : ℝ) * ((16 * (W_z.card : ℝ)) ^ (1 / (D : ℝ)) / (k : ℝ)) := by
        rw [mul_div_cancel₀ _ (ne_of_gt hk_pos)]
    _ = ∑ _q : Fin k, ((16 * (W_z.card : ℝ)) ^ (1 / (D : ℝ)) / (k : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ ∑ q : Fin k, ((U q).card : ℝ) ^ (1 / (D : ℝ)) :=
        Finset.sum_le_sum (fun q _ => h_each q)

/-- Splitting an active leaf $W_z \in \mathcal{L}(\mathcal{T})$ into $k \in [2, L_{\max} - 1]$
weakly $\eta_0$-sparse-or-co-sparse children via **(Split-$D$ Type I)** or **(Split-$D$ Type II)**
produces a new `ActiveLeafSplitTree` with strictly more leaves ($|\mathcal{L}(\mathcal{T}')| = |\mathcal{L}(\mathcal{T})| + k - 1$). -/
def ActiveLeafSplitTree.split_active_leaf {F : SimpleGraph V} {B : Finset V}
    {r m L_max k : ℕ} {η₀ w_split : ℝ}
    (T : ActiveLeafSplitTree F B r (8 * m) L_max η₀)
    {W_z : Finset V} (hWz_mem : W_z ∈ T.leaves)
    (hWz_active : (B.card : ℝ) / (L_max : ℝ) ^ (8 * m) ≤ (W_z.card : ℝ))
    {U : Fin k → Finset V}
    (hr : 1 ≤ r) (hm : 8 ≤ m) (hk2 : 2 ≤ k) (hkL : k < L_max)
    (hU_block : IsWeaklySparseOrCoSparseBlockadeIn F W_z k w_split η₀ U)
    (h_split :
      (4 ≤ k ∧ (64 ≤ k ∨ 11 ≤ m) ∧ ∀ q : Fin k,
        (W_z.card : ℝ) / ((2 : ℝ) ^ 60 * (k : ℝ) ^ (5 * m)) ≤ ((U q).card : ℝ)) ∨
      (64 * r ≤ 8 * m ∧ ∀ q : Fin k,
        (W_z.card : ℝ) / (2 : ℝ) ^ (60 * r) ≤ ((U q).card : ℝ))) :
    ActiveLeafSplitTree F B r (8 * m) L_max η₀ := by
  have hU_inj : Function.Injective U := by
    intro j₁ j₂ hj
    by_contra hne
    obtain ⟨x, hx⟩ := hU_block.1.nonempty_blocks j₁
    exact Finset.disjoint_left.mp (hU_block.1.pairwise_disjoint j₁ j₂ hne) hx (hj ▸ hx)
  let U_set := Finset.univ.image U
  let leaves' := T.leaves.erase W_z ∪ U_set
  have h_disj_LU : Disjoint (T.leaves.erase W_z) U_set := by
    rw [Finset.disjoint_left]
    intro A hA_er hA_U
    obtain ⟨hAW_ne, hA_mem⟩ := Finset.mem_erase.mp hA_er
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hA_U
    obtain ⟨x, hx⟩ := hU_block.1.nonempty_blocks j
    exact Finset.disjoint_left.mp (T.pairwise_disjoint (U j) hA_mem W_z hWz_mem hAW_ne)
      hx (hU_block.1.subset_ambient j hx)
  have h_card_leaves' : leaves'.card = T.leaves.card - 1 + k := by
    rw [Finset.card_union_of_disjoint h_disj_LU, Finset.card_erase_of_mem hWz_mem,
      Finset.card_image_of_injective _ hU_inj, Finset.card_univ, Fintype.card_fin]
  have h_Wz_pos : 1 ≤ T.leaves.card := Finset.card_pos.mpr ⟨W_z, hWz_mem⟩
  have h_leaves'_ge2 : 2 ≤ leaves'.card := by omega
  have h_child_width : ∀ q : Fin k,
      (B.card : ℝ) / ((2 : ℝ) ^ (60 * r) * (L_max : ℝ) ^ (2 * (8 * m))) ≤ ((U q).card : ℝ) := by
    intro q
    have hk_L : (k : ℝ) ≤ (L_max : ℝ) := Nat.cast_le.mpr (le_of_lt hkL)
    have hL_ge2 : (2 : ℝ) ≤ (L_max : ℝ) := Nat.ofNat_le_cast.mpr (by omega : 2 ≤ L_max)
    have h_step : (W_z.card : ℝ) / ((2 : ℝ) ^ (60 * r) * (L_max : ℝ) ^ (8 * m)) ≤ ((U q).card : ℝ) := by
      rcases h_split with ⟨_, _, hU1⟩ | ⟨_, hU2⟩
      · have h2_60 : (2 : ℝ) ^ 60 ≤ (2 : ℝ) ^ (60 * r) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        have hk_5m : (k : ℝ) ^ (5 * m) ≤ (L_max : ℝ) ^ (8 * m) := by
          calc (k : ℝ) ^ (5 * m) ≤ (L_max : ℝ) ^ (5 * m) := pow_le_pow_left₀ (by positivity) hk_L (5 * m)
            _ ≤ (L_max : ℝ) ^ (8 * m) := pow_le_pow_right₀ (by linarith) (by omega)
        have h_den : (2 : ℝ) ^ 60 * (k : ℝ) ^ (5 * m) ≤ (2 : ℝ) ^ (60 * r) * (L_max : ℝ) ^ (8 * m) :=
          mul_le_mul h2_60 hk_5m (by positivity) (by positivity)
        exact le_trans (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) h_den) (hU1 q)
      · have h1_L : (1 : ℝ) ≤ (L_max : ℝ) ^ (8 * m) := one_le_pow₀ (by linarith)
        have h_den : (2 : ℝ) ^ (60 * r) ≤ (2 : ℝ) ^ (60 * r) * (L_max : ℝ) ^ (8 * m) :=
          le_mul_of_one_le_right (by positivity) h1_L
        exact le_trans (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) h_den) (hU2 q)
    calc (B.card : ℝ) / ((2 : ℝ) ^ (60 * r) * (L_max : ℝ) ^ (2 * (8 * m)))
        = ((B.card : ℝ) / (L_max : ℝ) ^ (8 * m)) / ((2 : ℝ) ^ (60 * r) * (L_max : ℝ) ^ (8 * m)) := by
          rw [show 2 * (8 * m) = 8 * m + 8 * m by omega, pow_add]; ring
      _ ≤ (W_z.card : ℝ) / ((2 : ℝ) ^ (60 * r) * (L_max : ℝ) ^ (8 * m)) :=
          div_le_div_of_nonneg_right hWz_active (by positivity)
      _ ≤ ((U q).card : ℝ) := h_step
  refine
    { leaves := leaves'
      leaves_nonempty := Finset.card_pos.mp (by omega)
      subset_B := ?_
      pairwise_disjoint := ?_
      potential_ge := ?_
      leaf_width_ge := ?_
      ancestor_pair_sparse := ?_ }
  · intro L hL
    rcases Finset.mem_union.mp hL with hL_er | hL_U
    · exact T.subset_B L (Finset.erase_subset W_z T.leaves hL_er)
    · obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hL_U
      exact ⟨(hU_block.1.subset_ambient q).trans (T.subset_B W_z hWz_mem).1,
        hU_block.1.nonempty_blocks q⟩
  · intro L₁ hL₁ L₂ hL₂ hne
    rcases Finset.mem_union.mp hL₁ with hL₁_er | hL₁_U <;>
      rcases Finset.mem_union.mp hL₂ with hL₂_er | hL₂_U
    · exact T.pairwise_disjoint L₁ (Finset.erase_subset W_z T.leaves hL₁_er)
        L₂ (Finset.erase_subset W_z T.leaves hL₂_er) hne
    · obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hL₂_U
      obtain ⟨hL₁W_ne, hL₁_mem⟩ := Finset.mem_erase.mp hL₁_er
      exact Finset.disjoint_of_subset_right (hU_block.1.subset_ambient q)
        (T.pairwise_disjoint L₁ hL₁_mem W_z hWz_mem hL₁W_ne)
    · obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hL₁_U
      obtain ⟨hL₂W_ne, hL₂_mem⟩ := Finset.mem_erase.mp hL₂_er
      exact Finset.disjoint_of_subset_left (hU_block.1.subset_ambient q)
        (T.pairwise_disjoint W_z hWz_mem L₂ hL₂_mem hL₂W_ne.symm)
    · obtain ⟨q₁, _, rfl⟩ := Finset.mem_image.mp hL₁_U
      obtain ⟨q₂, _, rfl⟩ := Finset.mem_image.mp hL₂_U
      exact hU_block.1.pairwise_disjoint q₁ q₂ (fun h => hne (congr_arg U h))
  · rw [Finset.sum_union h_disj_LU]
    have h_U_sum : ∑ A ∈ U_set, (A.card : ℝ) ^ (1 / ((8 * m : ℕ) : ℝ)) =
        ∑ q : Fin k, ((U q).card : ℝ) ^ (1 / ((8 * m : ℕ) : ℝ)) :=
      Finset.sum_image (fun q₁ _ q₂ _ h => hU_inj h)
    have h_er_sum := Finset.sum_erase_add T.leaves
      (fun A : Finset V => (A.card : ℝ) ^ (1 / ((8 * m : ℕ) : ℝ))) hWz_mem
    have h_inc := split_potential_increase hr hm hk2 h_split
    have hWz_nn : (0 : ℝ) ≤ (W_z.card : ℝ) := Nat.cast_nonneg W_z.card
    have h_16 : (W_z.card : ℝ) ^ (1 / ((8 * m : ℕ) : ℝ)) ≤
        (16 * (W_z.card : ℝ)) ^ (1 / ((8 * m : ℕ) : ℝ)) :=
      Real.rpow_le_rpow hWz_nn (by linarith) (by positivity)
    linarith [T.potential_ge]
  · intro _ L hL
    rcases Finset.mem_union.mp hL with hL_er | hL_U
    · obtain ⟨hLW_ne, hL_mem⟩ := Finset.mem_erase.mp hL_er
      have hT_ge2 : 2 ≤ T.leaves.card := by
        exact Finset.one_lt_card.mpr ⟨L, hL_mem, W_z, hWz_mem, hLW_ne⟩
      exact T.leaf_width_ge hT_ge2 L hL_mem
    · obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hL_U
      exact h_child_width q
  · intro L₁ hL₁ L₂ hL₂ hne
    rcases Finset.mem_union.mp hL₁ with hL₁_er | hL₁_U <;>
      rcases Finset.mem_union.mp hL₂ with hL₂_er | hL₂_U
    · exact T.ancestor_pair_sparse L₁ (Finset.erase_subset W_z T.leaves hL₁_er)
        L₂ (Finset.erase_subset W_z T.leaves hL₂_er) hne
    · obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hL₂_U
      obtain ⟨hL₁W_ne, hL₁_mem⟩ := Finset.mem_erase.mp hL₁_er
      obtain ⟨A₁, hA₁B, A₂, hA₂B, hL₁A₁, hWzA₂, h_sp⟩ :=
        T.ancestor_pair_sparse L₁ hL₁_mem W_z hWz_mem hL₁W_ne
      exact ⟨A₁, hA₁B, A₂, hA₂B, hL₁A₁, (hU_block.1.subset_ambient q).trans hWzA₂, h_sp⟩
    · obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hL₁_U
      obtain ⟨hL₂W_ne, hL₂_mem⟩ := Finset.mem_erase.mp hL₂_er
      obtain ⟨A₁, hA₁B, A₂, hA₂B, hWzA₁, hL₂A₂, h_sp⟩ :=
        T.ancestor_pair_sparse W_z hWz_mem L₂ hL₂_mem hL₂W_ne.symm
      exact ⟨A₁, hA₁B, A₂, hA₂B, (hU_block.1.subset_ambient q).trans hWzA₁, hL₂A₂, h_sp⟩
    · obtain ⟨q₁, _, rfl⟩ := Finset.mem_image.mp hL₁_U
      obtain ⟨q₂, _, rfl⟩ := Finset.mem_image.mp hL₂_U
      have hq₁₂ : q₁ ≠ q₂ := fun h => hne (congr_arg U h)
      have hWz_B := (T.subset_B W_z hWz_mem).1
      exact ⟨U q₁, (hU_block.1.subset_ambient q₁).trans hWz_B,
        U q₂, (hU_block.1.subset_ambient q₂).trans hWz_B,
        Finset.Subset.rfl, Finset.Subset.rfl, hU_block.2 q₁ q₂ hq₁₂⟩

/-- Every active-leaf split of arity $k \ge 2$ strictly increases the number of leaves in $\mathcal{T}$. -/
lemma ActiveLeafSplitTree.split_active_leaf_card_gt {F : SimpleGraph V} {B : Finset V}
    {r m L_max k : ℕ} {η₀ w_split : ℝ}
    (T : ActiveLeafSplitTree F B r (8 * m) L_max η₀)
    {W_z : Finset V} (hWz_mem : W_z ∈ T.leaves)
    (hWz_active : (B.card : ℝ) / (L_max : ℝ) ^ (8 * m) ≤ (W_z.card : ℝ))
    {U : Fin k → Finset V}
    (hr : 1 ≤ r) (hm : 8 ≤ m) (hk2 : 2 ≤ k) (hkL : k < L_max)
    (hU_block : IsWeaklySparseOrCoSparseBlockadeIn F W_z k w_split η₀ U)
    (h_split :
      (4 ≤ k ∧ (64 ≤ k ∨ 11 ≤ m) ∧ ∀ q : Fin k,
        (W_z.card : ℝ) / ((2 : ℝ) ^ 60 * (k : ℝ) ^ (5 * m)) ≤ ((U q).card : ℝ)) ∨
      (64 * r ≤ 8 * m ∧ ∀ q : Fin k,
        (W_z.card : ℝ) / (2 : ℝ) ^ (60 * r) ≤ ((U q).card : ℝ))) :
    T.leaves.card <
      (T.split_active_leaf hWz_mem hWz_active hr hm hk2 hkL hU_block h_split).leaves.card := by
  have hU_inj : Function.Injective U := by
    intro j₁ j₂ hj
    by_contra hne
    obtain ⟨x, hx⟩ := hU_block.1.nonempty_blocks j₁
    exact Finset.disjoint_left.mp (hU_block.1.pairwise_disjoint j₁ j₂ hne) hx (hj ▸ hx)
  let U_set := Finset.univ.image U
  have h_disj_LU : Disjoint (T.leaves.erase W_z) U_set := by
    rw [Finset.disjoint_left]
    intro A hA_er hA_U
    obtain ⟨hAW_ne, hA_mem⟩ := Finset.mem_erase.mp hA_er
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hA_U
    obtain ⟨x, hx⟩ := hU_block.1.nonempty_blocks j
    exact Finset.disjoint_left.mp (T.pairwise_disjoint (U j) hA_mem W_z hWz_mem hAW_ne)
      hx (hU_block.1.subset_ambient j hx)
  change T.leaves.card < (T.leaves.erase W_z ∪ U_set).card
  rw [Finset.card_union_of_disjoint h_disj_LU, Finset.card_erase_of_mem hWz_mem,
    Finset.card_image_of_injective _ hU_inj, Finset.card_univ, Fintype.card_fin]
  have : 1 ≤ T.leaves.card := Finset.card_pos.mpr ⟨W_z, hWz_mem⟩
  omega

/-- **Lemma 8(3) (`active_leaf_split_tree_dichotomy`, Generalized $\Phi_D$ Hereditary $\eta_0$-Sparse-or-Co-Sparse Active-Leaf Split Tree Lemma)**:
For any `ActiveLeafSplitTree` $\mathcal{T}$ on $B$:
- If $|\mathcal{L}(\mathcal{T})| < L_{\max}$, $\mathcal{T}$ contains an active leaf $W_z$ ($|W_z| \ge L_{\max}^{-D} |B|$);
- If $|\mathcal{L}(\mathcal{T})| \ge L_{\max}$ ($L_{\max} \ge 2$), the first $L_{\max}$ leaves of $\mathcal{T}$
  (with zero leaves pruned) form an $(L_{\max}, 2^{-60 r} L_{\max}^{-2D} |B|)$-blockade in $F[B]$
  that is weakly $(\eta_0 \beta_{D, L_{\max}}^{-2})$-sparse-or-co-sparse in $F$. -/
theorem active_leaf_split_tree_dichotomy {F : SimpleGraph V} {B : Finset V}
    {r D L_max : ℕ} {η₀ : ℝ}
    (T : ActiveLeafSplitTree F B r D L_max η₀)
    (hD : 1 ≤ D) (hL_low : 2 ≤ L_max) (hη₀ : 0 ≤ η₀) :
    (T.leaves.card < L_max ∧
      ∃ W_z ∈ T.leaves, (B.card : ℝ) / (L_max : ℝ) ^ D ≤ (W_z.card : ℝ)) ∨
    (L_max ≤ T.leaves.card ∧
      let β_inv := (2 : ℝ) ^ (60 * r) * (L_max : ℝ) ^ (2 * D)
      ∃ U : Fin L_max → Finset V,
        IsWeaklySparseOrCoSparseBlockadeIn F B L_max
          ((B.card : ℝ) / β_inv) (η₀ * β_inv ^ 2) U) := by
  by_cases hL_lt : T.leaves.card < L_max
  · left
    exact ⟨hL_lt, T.exists_active_leaf hD hL_lt⟩
  · right
    push_neg at hL_lt
    refine ⟨hL_lt, ?_⟩
    intro β_inv
    have h_ge2 : 2 ≤ T.leaves.card := le_trans hL_low hL_lt
    obtain ⟨q, L, hq_eq, hL_inj, _, hL_mem, _, _⟩ := exists_sorted_equiv_of_finset T.leaves
    have hL_le_q : L_max ≤ q := hq_eq ▸ hL_lt
    let U : Fin L_max → Finset V := fun j => L ⟨j.1, by omega⟩
    have hU_mem : ∀ j : Fin L_max, U j ∈ T.leaves := fun j => hL_mem ⟨j.1, by omega⟩
    have hU_width : ∀ j : Fin L_max, (B.card : ℝ) / β_inv ≤ ((U j).card : ℝ) :=
      fun j => T.leaf_width_ge h_ge2 (U j) (hU_mem j)
    refine ⟨U, ⟨⟨fun j => (T.subset_B (U j) (hU_mem j)).1,
      fun j => (T.subset_B (U j) (hU_mem j)).2, ?_, hU_width⟩, ?_⟩⟩
    · intro j₁ j₂ hj
      have hj' : (⟨j₁.1, by omega⟩ : Fin q) ≠ ⟨j₂.1, by omega⟩ :=
        fun h => hj (Fin.ext (Fin.mk.inj_iff.mp h))
      exact T.pairwise_disjoint (U j₁) (hU_mem j₁) (U j₂) (hU_mem j₂) (fun h => hj' (hL_inj h))
    · intro j₁ j₂ hj
      have hj' : (⟨j₁.1, by omega⟩ : Fin q) ≠ ⟨j₂.1, by omega⟩ :=
        fun h => hj (Fin.ext (Fin.mk.inj_iff.mp h))
      have hU_ne : U j₁ ≠ U j₂ := fun h => hj' (hL_inj h)
      obtain ⟨A₁, hA₁B, A₂, hA₂B, hU₁A₁, hU₂A₂, h_sp⟩ :=
        T.ancestor_pair_sparse (U j₁) (hU_mem j₁) (U j₂) (hU_mem j₂) hU_ne
      have hβ_pos : 0 < β_inv := by unfold β_inv; positivity
      have hA₁_le : (A₁.card : ℝ) ≤ β_inv * ((U j₁).card : ℝ) := by
        have h1 : (A₁.card : ℝ) ≤ (B.card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hA₁B)
        have h2 : (B.card : ℝ) ≤ β_inv * ((U j₁).card : ℝ) := by
          have := (div_le_iff₀ hβ_pos).mp (hU_width j₁)
          linarith
        exact le_trans h1 h2
      have hA₂_le : (A₂.card : ℝ) ≤ β_inv * ((U j₂).card : ℝ) := by
        have h1 : (A₂.card : ℝ) ≤ (B.card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hA₂B)
        have h2 : (B.card : ℝ) ≤ β_inv * ((U j₂).card : ℝ) := by
          have := (div_le_iff₀ hβ_pos).mp (hU_width j₂)
          linarith
        exact le_trans h1 h2
      have h_aux : ∀ (G : SimpleGraph V),
          IsWeaklySparsePair G A₁ A₂ η₀ →
          IsWeaklySparsePair G (U j₁) (U j₂) (η₀ * β_inv ^ 2) := by
        intro G hG
        unfold IsWeaklySparsePair at hG ⊢
        have h_ce : (crossEdgeCount G (U j₁) (U j₂) : ℝ) ≤ (crossEdgeCount G A₁ A₂ : ℝ) :=
          Nat.cast_le.mpr (crossEdgeCount_mono G hU₁A₁ hU₂A₂)
        have h_prod : (A₁.card : ℝ) * (A₂.card : ℝ) ≤
            (β_inv * ((U j₁).card : ℝ)) * (β_inv * ((U j₂).card : ℝ)) :=
          mul_le_mul hA₁_le hA₂_le (Nat.cast_nonneg _) (by positivity)
        calc (crossEdgeCount G (U j₁) (U j₂) : ℝ)
            ≤ η₀ * ((A₁.card : ℝ) * (A₂.card : ℝ)) := by linarith
          _ ≤ η₀ * ((β_inv * ((U j₁).card : ℝ)) * (β_inv * ((U j₂).card : ℝ))) :=
              mul_le_mul_of_nonneg_left h_prod hη₀
          _ = (η₀ * β_inv ^ 2) * ((U j₁).card : ℝ) * ((U j₂).card : ℝ) := by ring
      rcases h_sp with hF | hFc
      · exact Or.inl (h_aux F hF)
      · exact Or.inr (h_aux Fᶜ hFc)

/-!
## Section 6: Unified Handle-Stem Pair Principle, Lemma 9, and Greedy Component Grouping

Formalizes:
- **Unified Handle-Stem Pair Principle (`IsUnifiedHandleStemPair`, `isUnifiedHandleStemPair_of_combOrCoComb`, `main.tex` lines 90–95)**:
  For any distinct $i, j \in [\ell]$ in an $(\ell, w)$-comb or $(\ell, w)$-co-comb equipped with
  per-handle $s$-stems, choosing $(\mathbf{v}^{(i)}, a_i)$ when $(a, B)$ is a comb and
  $(\mathbf{v}^{(j)}, a_j)$ when $(a, B)$ is a co-comb yields a unified $(s+1)$-vertex stem-handle
  pair $(\hat{\mathbf{v}}^{(i,j)}, \hat{a}_{i,j})$ inducing $P_{s+1}$ in $\overline{F}$ such that
  $\hat{a}_{i,j}$ is complete in $F$ to $B_i$ and anticomplete in $F$ to $B_j$.
- **Lemma 9 (`universal_depth_r_neighborhood_modularity`, `main.tex` lines 473–490)**:
  Universal depth-$r$ anticonnected neighborhood modularity in $\overline{P_{s+5+r}}$-free graphs.
- **Greedy Anticonnected Component Grouping (`exists_complete_blockade_of_small_components`)**:
  Partitions heavy incomplete neighborhoods into a complete $(p_{\mathrm{comp}}, \tau)$-blockade.
-/

/-- **Unified Handle-Stem Pair Principle** (Definition 1(4) of `main.tex`):
A stem $\hat{\mathbf{v}} : \text{Fin } s \to V$ and handle $\hat{a} \in S \setminus (B_i \cup B_j)$
for a disjoint pair $(B_i, B_j)$ inside $S$ such that $\hat{\mathbf{v}}$ induces $P_s$ in $\overline{F}$,
$(\hat{\mathbf{v}}, \hat{a})$ induces $P_{s+1}$ in $\overline{F}$, $\hat{\mathbf{v}}$ is complete in $F$
to $B_i \cup B_j$, and $\hat{a}$ is complete in $F$ to $B_i$ and anticomplete in $F$ to $B_j$. -/
structure IsUnifiedHandleStemPair (F : SimpleGraph V) (S : Finset V) (s : ℕ)
    (B_i B_j : Finset V) (v_hat : Fin s → V) (a_hat : V) : Prop where
  stem_pos : 1 ≤ s
  blocks_disjoint : Disjoint B_i B_j
  Bi_sub : B_i ⊆ S
  Bj_sub : B_j ⊆ S
  stem_in_ambient : ∀ p : Fin s, v_hat p ∈ S
  stem_injective : Function.Injective v_hat
  stem_not_handle : ∀ p : Fin s, v_hat p ≠ a_hat
  stem_not_in_Bi : ∀ p : Fin s, v_hat p ∉ B_i
  stem_not_in_Bj : ∀ p : Fin s, v_hat p ∉ B_j
  handle_in_ambient : a_hat ∈ S
  handle_not_in_Bi : a_hat ∉ B_i
  handle_not_in_Bj : a_hat ∉ B_j
  stem_induced_path_compl : ∀ p₁ p₂ : Fin s,
    Fᶜ.Adj (v_hat p₁) (v_hat p₂) ↔ (pathGraph s).Adj p₁ p₂
  stem_last_nonadj_handle : ∀ p : Fin s, p.1 + 1 = s → ¬F.Adj (v_hat p) a_hat
  stem_init_adj_handle : ∀ p : Fin s, p.1 + 1 < s → F.Adj (v_hat p) a_hat
  stem_complete_Bi : ∀ p : Fin s, ∀ u ∈ B_i, F.Adj (v_hat p) u
  stem_complete_Bj : ∀ p : Fin s, ∀ u ∈ B_j, F.Adj (v_hat p) u
  handle_complete_Bi : ∀ u ∈ B_i, F.Adj a_hat u
  handle_anticomplete_Bj : ∀ u ∈ B_j, ¬F.Adj a_hat u

/-- Canonical unified stem $\hat{\mathbf{v}}^{(i,j)}$: uses $\mathbf{v}^{(i)}$ when $(a, B)$ is a comb,
and $\mathbf{v}^{(j)}$ when $(a, B)$ is a co-comb. -/
noncomputable def unifiedStem (F : SimpleGraph V) (S : Finset V) {ℓ s : ℕ} (w : ℝ)
    (a : Fin ℓ → V) (B : Fin ℓ → Finset V) (stems : Fin ℓ → Fin s → V)
    (i j : Fin ℓ) : Fin s → V :=
  if IsCombIn F S ℓ w a B then stems i else stems j

/-- Canonical unified handle $\hat{a}_{i,j}$: uses $a_i$ when $(a, B)$ is a comb,
and $a_j$ when $(a, B)$ is a co-comb. -/
noncomputable def unifiedHandle (F : SimpleGraph V) (S : Finset V) {ℓ : ℕ} (w : ℝ)
    (a : Fin ℓ → V) (B : Fin ℓ → Finset V)
    (i j : Fin ℓ) : V :=
  if IsCombIn F S ℓ w a B then a i else a j

/-- **Unified Handle-Stem Pair Principle**: For any distinct $i, j \in \text{Fin } \ell$ in an
$(\ell, w)$-comb or co-comb $((a_r, B_r) : r \in [\ell])$ equipped with per-handle $s$-stems,
`(unifiedStem, unifiedHandle)` satisfies `IsUnifiedHandleStemPair F S s (B i) (B j)` (and its
stem is complete in $F$ to all teeth $\bigcup_q B_q$). -/
theorem isUnifiedHandleStemPair_of_combOrCoComb {F : SimpleGraph V} {S : Finset V}
    {ℓ s : ℕ} {w : ℝ} {a : Fin ℓ → V} {B : Fin ℓ → Finset V} {stems : Fin ℓ → Fin s → V}
    (hcomb : IsCombOrCoCombIn F S ℓ w a B)
    (hstems : HasPerHandleApexStems F S ℓ s a B stems)
    {i j : Fin ℓ} (hij : i ≠ j) :
    IsUnifiedHandleStemPair F S s (B i) (B j)
      (unifiedStem F S w a B stems i j) (unifiedHandle F S w a B i j) ∧
    (∀ (p : Fin s) (q : Fin ℓ), ∀ u ∈ B q, F.Adj (unifiedStem F S w a B stems i j p) u) ∧
    (∀ q : Fin ℓ, unifiedHandle F S w a B i j ∉ B q) := by
  unfold unifiedStem unifiedHandle
  by_cases hc : IsCombIn F S ℓ w a B
  · simp only [if_pos hc]
    refine ⟨?_, fun p q u hu => hstems.stem_complete_to_blocks i q p u hu,
      fun q => hc.apex_disjoint_blocks i q⟩
    refine
      { stem_pos := hstems.stem_pos
        blocks_disjoint := hc.is_blockade.pairwise_disjoint i j hij
        Bi_sub := hc.is_blockade.subset_ambient i
        Bj_sub := hc.is_blockade.subset_ambient j
        stem_in_ambient := hstems.stem_in_ambient i
        stem_injective := hstems.stem_injective i
        stem_not_handle := fun p => hstems.stem_not_handle i i p
        stem_not_in_Bi := fun p => hstems.stem_not_in_blocks i i p
        stem_not_in_Bj := fun p => hstems.stem_not_in_blocks i j p
        handle_in_ambient := hc.apex_in_ambient i
        handle_not_in_Bi := hc.apex_disjoint_blocks i i
        handle_not_in_Bj := hc.apex_disjoint_blocks i j
        stem_induced_path_compl := hstems.stem_induced_path_compl i
        stem_last_nonadj_handle := hstems.stem_last_nonadj_handle i
        stem_init_adj_handle := hstems.stem_init_adj_handle i
        stem_complete_Bi := fun p u hu => hstems.stem_complete_to_blocks i i p u hu
        stem_complete_Bj := fun p u hu => hstems.stem_complete_to_blocks i j p u hu
        handle_complete_Bi := hc.apex_complete_own i
        handle_anticomplete_Bj := hc.apex_anticomplete_other i j hij }
  · simp only [if_neg hc]
    have hco : IsCoCombIn F S ℓ w a B := hcomb.resolve_left hc
    refine ⟨?_, fun p q u hu => hstems.stem_complete_to_blocks j q p u hu,
      fun q => hco.apex_disjoint_blocks j q⟩
    refine
      { stem_pos := hstems.stem_pos
        blocks_disjoint := hco.is_blockade.pairwise_disjoint i j hij
        Bi_sub := hco.is_blockade.subset_ambient i
        Bj_sub := hco.is_blockade.subset_ambient j
        stem_in_ambient := hstems.stem_in_ambient j
        stem_injective := hstems.stem_injective j
        stem_not_handle := fun p => hstems.stem_not_handle j j p
        stem_not_in_Bi := fun p => hstems.stem_not_in_blocks j i p
        stem_not_in_Bj := fun p => hstems.stem_not_in_blocks j j p
        handle_in_ambient := hco.apex_in_ambient j
        handle_not_in_Bi := hco.apex_disjoint_blocks j i
        handle_not_in_Bj := hco.apex_disjoint_blocks j j
        stem_induced_path_compl := hstems.stem_induced_path_compl j
        stem_last_nonadj_handle := hstems.stem_last_nonadj_handle j
        stem_init_adj_handle := hstems.stem_init_adj_handle j
        stem_complete_Bi := fun p u hu => hstems.stem_complete_to_blocks j i p u hu
        stem_complete_Bj := fun p u hu => hstems.stem_complete_to_blocks j j p u hu
        handle_complete_Bi := hco.apex_complete_other j i hij.symm
        handle_anticomplete_Bj := hco.apex_anticomplete_own j }

/-- General $\overline{P_m}$ embedding criterion: any $m$-tuple $f : \text{Fin } m \to V$ whose consecutive
pairs are distinct and non-adjacent in $F$ and whose non-consecutive pairs are adjacent in $F$
is injective and embeds `PkCompl m` into $F$. -/
theorem not_isInducedSubgraphFree_PkCompl_of_seq {F : SimpleGraph V} {m : ℕ} (f : Fin m → V)
    (h_consec : ∀ p q : Fin m, p.1 + 1 = q.1 → f p ≠ f q ∧ ¬F.Adj (f p) (f q))
    (h_nonconsec : ∀ p q : Fin m, p.1 + 1 < q.1 → F.Adj (f p) (f q)) :
    ¬IsInducedSubgraphFree F (PkCompl m) := by
  have h_ne_lt : ∀ p q : Fin m, p.1 < q.1 → f p ≠ f q := by
    intro p q hpq
    by_cases h1 : p.1 + 1 = q.1
    · exact (h_consec p q h1).1
    · exact F.ne_of_adj (h_nonconsec p q (by omega))
  have hf_inj : Function.Injective f := by
    intro p q hpq
    rcases lt_trichotomy p.1 q.1 with hlt | heq | hgt
    · exact False.elim (h_ne_lt p q hlt hpq)
    · exact Fin.ext heq
    · exact False.elim (h_ne_lt q p hgt hpq.symm)
  have h_adj_lt : ∀ p q : Fin m, p.1 < q.1 → ((PkCompl m).Adj p q ↔ F.Adj (f p) (f q)) := by
    intro p q hpq
    have hp_ne_q : p ≠ q := fun h => by rw [h] at hpq; omega
    simp only [PkCompl, compl_adj, pathGraph_adj]
    have h_not_rev : ¬(q.1 + 1 = p.1) := by omega
    by_cases h1 : p.1 + 1 = q.1
    · simp [hp_ne_q, h1, (h_consec p q h1).2]
    · have hgt : p.1 + 1 < q.1 := by omega
      simp [hp_ne_q, h1, h_not_rev, h_nonconsec p q hgt]
  intro hfree
  apply hfree
  refine ⟨⟨f, hf_inj⟩, ?_⟩
  ext p q
  simp only [comap_adj, Function.Embedding.coeFn_mk]
  rcases lt_trichotomy p.1 q.1 with hlt | heq | hgt
  · exact h_adj_lt p q hlt
  · have hpq : p = q := Fin.ext heq
    subst hpq
    simp
  · rw [(PkCompl m).adj_comm, F.adj_comm]
    exact h_adj_lt q p hgt

/-- **Lemma 9 (`universal_depth_r_neighborhood_modularity`, Universal Depth-$r$ Anticonnected Neighborhood Modularity)**:
For any $\overline{P_{s+5+r}}$-free graph $F$, any $(\ell, w)$-comb or co-comb $((a_i, B_i) : i \in [\ell])$
with per-handle $s$-stems, distinct $i, j \in \text{Fin } \ell$, and any depth-$r$ cutter sequence
$z : \text{Fin } (r + 1) \to V$ and subsets $M : \text{Fin } (r + 1) \to \text{Finset } V$ with:
- $z_0 \in B_j$ and $M_0 \subseteq B_i$,
- $M_{d+1} \subseteq N_F(z_d) \cap M_d$ and $z_{d+1} \in M_d \setminus N_F(z_d)$ for all $0 \le d < r$,
if $z_r$ is not complete in $F$ to $M_r$, then every anticonnected component $C$ of $F[N_F(z_r) \cap M_r]$
is a proper module of $F[M_r]$. -/
theorem universal_depth_r_neighborhood_modularity {F : SimpleGraph V} {S : Finset V}
    {ℓ s r : ℕ} {w : ℝ} {a : Fin ℓ → V} {B : Fin ℓ → Finset V} {stems : Fin ℓ → Fin s → V}
    (hfree : IsInducedSubgraphFree F (PkCompl (s + 5 + r)))
    (hcomb : IsCombOrCoCombIn F S ℓ w a B)
    (hstems : HasPerHandleApexStems F S ℓ s a B stems)
    {i j : Fin ℓ} (hij : i ≠ j)
    (z : Fin (r + 1) → V) (M : Fin (r + 1) → Finset V)
    (hz0 : z 0 ∈ B j) (hM0 : M 0 ⊆ B i)
    (hM_step : ∀ d : Fin r, M d.succ ⊆ neighborFinsetIn F (z d.castSucc) (M d.castSucc))
    (hz_step : ∀ d : Fin r, z d.succ ∈ M d.castSucc ∧ ¬F.Adj (z d.castSucc) (z d.succ))
    (hz_not_comp : ¬∀ u ∈ M (Fin.last r), F.Adj (z (Fin.last r)) u)
    {C : Finset V}
    (hC : IsAnticonnectedComponentOf F (neighborFinsetIn F (z (Fin.last r)) (M (Fin.last r))) C) :
    IsProperModuleIn F (M (Fin.last r)) C := by
  obtain ⟨hunif, _, _⟩ := isUnifiedHandleStemPair_of_combOrCoComb hcomb hstems hij
  set v_hat := unifiedStem F S w a B stems i j
  set a_hat := unifiedHandle F S w a B i j
  have hs_pos : 1 ≤ s := hunif.stem_pos
  have hM_sub : ∀ d : Fin r, M d.succ ⊆ M d.castSucc :=
    fun d => (hM_step d).trans (neighborFinsetIn_subset F _ _)
  have hM_anti : Antitone M := module_chain_antitone hM_sub
  have hM_sub_Bi : ∀ d : Fin (r + 1), M d ⊆ B i :=
    fun d => (hM_anti (Fin.zero_le d)).trans hM0
  have hZ_sub_Mr : neighborFinsetIn F (z (Fin.last r)) (M (Fin.last r)) ⊆ M (Fin.last r) :=
    neighborFinsetIn_subset F _ _
  have hC_sub_Z : C ⊆ neighborFinsetIn F (z (Fin.last r)) (M (Fin.last r)) := hC.1
  have hC_sub_Mr : C ⊆ M (Fin.last r) := hC_sub_Z.trans hZ_sub_Mr
  have hzr_adj_C : ∀ x ∈ C, F.Adj (z (Fin.last r)) x :=
    fun x hx => ((mem_neighborFinsetIn_iff F _ _ x).mp (hC_sub_Z hx)).2
  refine ⟨hC.nonempty, ?_, hC_sub_Mr, ?_⟩
  · rw [Finset.ssubset_iff_of_subset hC_sub_Mr]
    push_neg at hz_not_comp
    obtain ⟨w₀, hw₀M, hw₀n⟩ := hz_not_comp
    exact ⟨w₀, hw₀M, fun hw₀C => hw₀n (hzr_adj_C w₀ hw₀C)⟩
  · intro z_next hz_next_M hz_next_notC
    by_cases hzr_adj : F.Adj (z (Fin.last r)) z_next
    · have hz_in_Z : z_next ∈ neighborFinsetIn F (z (Fin.last r)) (M (Fin.last r)) :=
        (mem_neighborFinsetIn_iff F _ _ z_next).mpr ⟨hz_next_M, hzr_adj⟩
      left
      intro x hxC
      exact (hC.2.2 x hxC z_next hz_in_Z hz_next_notC).symm
    · by_contra hnot_pure
      rw [not_isVertexPureTo_iff_isVertexMixedOn] at hnot_pure
      obtain ⟨x₂, hx₂C, x₃, hx₃C, hx₂_ne_x₃, hx₂x₃_nadj, hzx₂_nadj, hzx₃_adj⟩ :=
        hnot_pure.exists_anticonnected_edge hC.2.1
      have hx₂_Mr : x₂ ∈ M (Fin.last r) := hC_sub_Mr hx₂C
      have hx₃_Mr : x₃ ∈ M (Fin.last r) := hC_sub_Mr hx₃C
      let f : Fin (s + 5 + r) → V := fun p =>
        if hps : p.1 < s then v_hat ⟨p.1, hps⟩
        else if p.1 = s then a_hat
        else if hpr : p.1 ≤ s + 1 + r then z ⟨p.1 - (s + 1), by omega⟩
        else if p.1 = s + 2 + r then z_next
        else if p.1 = s + 3 + r then x₂
        else x₃
      have hf_v : ∀ p : Fin (s + 5 + r), ∀ hps : p.1 < s, f p = v_hat ⟨p.1, hps⟩ := by
        intro p hps; dsimp [f]; rw [dif_pos hps]
      have hf_a : ∀ p : Fin (s + 5 + r), p.1 = s → f p = a_hat := by
        intro p hps; dsimp [f]; rw [dif_neg (by omega), if_pos hps]
      have hf_z : ∀ p : Fin (s + 5 + r), ∀ (h1 : s + 1 ≤ p.1) (h2 : p.1 ≤ s + 1 + r),
          f p = z ⟨p.1 - (s + 1), by omega⟩ := by
        intro p h1 h2; dsimp [f]
        rw [dif_neg (by omega), if_neg (by omega), dif_pos h2]
      have hf_zn : ∀ p : Fin (s + 5 + r), p.1 = s + 2 + r → f p = z_next := by
        intro p hp; dsimp [f]
        rw [dif_neg (by omega), if_neg (by omega), dif_neg (by omega), if_pos hp]
      have hf_x2 : ∀ p : Fin (s + 5 + r), p.1 = s + 3 + r → f p = x₂ := by
        intro p hp; dsimp [f]
        rw [dif_neg (by omega), if_neg (by omega), dif_neg (by omega), if_neg (by omega), if_pos hp]
      have hf_x3 : ∀ p : Fin (s + 5 + r), p.1 = s + 4 + r → f p = x₃ := by
        intro p hp; dsimp [f]
        rw [dif_neg (by omega), if_neg (by omega), dif_neg (by omega), if_neg (by omega), if_neg (by omega)]
      -- Helper: for any q with q.1 ≥ s + 2, f q ∈ M 0 ⊆ B i
      have hf_in_Bi : ∀ q : Fin (s + 5 + r), s + 2 ≤ q.1 → f q ∈ B i := by
        intro q hq
        by_cases hqr : q.1 ≤ s + 1 + r
        · rw [hf_z q (by omega) hqr]
          let d : Fin r := ⟨q.1 - (s + 2), by omega⟩
          have hd_eq : (⟨q.1 - (s + 1), by omega⟩ : Fin (r + 1)) = d.succ := by
            ext; dsimp [d]; omega
          rw [hd_eq]
          exact hM_sub_Bi d.castSucc (hz_step d).1
        · by_cases hq_zn : q.1 = s + 2 + r
          · rw [hf_zn q hq_zn]; exact hM_sub_Bi (Fin.last r) hz_next_M
          · by_cases hq_x2 : q.1 = s + 3 + r
            · rw [hf_x2 q hq_x2]; exact hM_sub_Bi (Fin.last r) hx₂_Mr
            · have hq_x3 : q.1 = s + 4 + r := by omega
              rw [hf_x3 q hq_x3]; exact hM_sub_Bi (Fin.last r) hx₃_Mr
      -- Helper: for any d : Fin r and any q with q.1 ≥ s + 1 + d.1 + 2, f q ∈ M d.succ
      have hf_in_M_succ : ∀ (d : Fin r) (q : Fin (s + 5 + r)),
          s + 1 + d.1 + 2 ≤ q.1 → f q ∈ M d.succ := by
        intro d q hq
        by_cases hqr : q.1 ≤ s + 1 + r
        · rw [hf_z q (by omega) hqr]
          let d' : Fin r := ⟨q.1 - (s + 2), by omega⟩
          have hd'_eq : (⟨q.1 - (s + 1), by omega⟩ : Fin (r + 1)) = d'.succ := by
            ext; dsimp [d']; omega
          rw [hd'_eq]
          have hd_le : d.succ ≤ d'.castSucc := by
            simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc, d']; omega
          exact hM_anti hd_le (hz_step d').1
        · have hd_le_last : d.succ ≤ Fin.last r := Fin.le_last _
          by_cases hq_zn : q.1 = s + 2 + r
          · rw [hf_zn q hq_zn]; exact hM_anti hd_le_last hz_next_M
          · by_cases hq_x2 : q.1 = s + 3 + r
            · rw [hf_x2 q hq_x2]; exact hM_anti hd_le_last hx₂_Mr
            · have hq_x3 : q.1 = s + 4 + r := by omega
              rw [hf_x3 q hq_x3]; exact hM_anti hd_le_last hx₃_Mr
      apply not_isInducedSubgraphFree_PkCompl_of_seq f ?_ ?_ hfree
      · -- Consecutive pairs: p.1 + 1 = q.1 → f p ≠ f q ∧ ¬F.Adj (f p) (f q)
        intro p q hpq
        by_cases hp_lt_s1 : p.1 + 1 < s
        · -- Both in v_hat
          have hp_s : p.1 < s := by omega
          have hq_s : q.1 < s := by omega
          rw [hf_v p hp_s, hf_v q hq_s]
          have hpq_path : (pathGraph s).Adj ⟨p.1, hp_s⟩ ⟨q.1, hq_s⟩ := by
            rw [pathGraph_adj]; left; exact hpq
          have hadjc := (hunif.stem_induced_path_compl ⟨p.1, hp_s⟩ ⟨q.1, hq_s⟩).mpr hpq_path
          exact ⟨hadjc.1, hadjc.2⟩
        · by_cases hp_eq_s1 : p.1 + 1 = s
          · -- v_hat (s - 1) and a_hat
            have hp_s : p.1 < s := by omega
            have hq_s : q.1 = s := by omega
            rw [hf_v p hp_s, hf_a q hq_s]
            exact ⟨hunif.stem_not_handle ⟨p.1, hp_s⟩,
              hunif.stem_last_nonadj_handle ⟨p.1, hp_s⟩ hp_eq_s1⟩
          · by_cases hp_eq_s : p.1 = s
            · -- a_hat and z 0 ∈ B j
              have hq_s1 : q.1 = s + 1 := by omega
              rw [hf_a p hp_eq_s, hf_z q (by omega) (by omega)]
              have h0_eq : (⟨q.1 - (s + 1), by omega⟩ : Fin (r + 1)) = 0 := by ext; dsimp; omega
              rw [h0_eq]
              exact ⟨fun h => hunif.handle_not_in_Bj (h ▸ hz0),
                hunif.handle_anticomplete_Bj (z 0) hz0⟩
            · by_cases hp_z_step : p.1 ≤ s + r
              · -- z d.castSucc and z d.succ for some d : Fin r
                have hr_pos : 1 ≤ r := by omega
                let d : Fin r := ⟨p.1 - (s + 1), by omega⟩
                rw [hf_z p (by omega) (by omega), hf_z q (by omega) (by omega)]
                have hp_d : (⟨p.1 - (s + 1), by omega⟩ : Fin (r + 1)) = d.castSucc := by
                  ext; dsimp [d]
                have hq_d : (⟨q.1 - (s + 1), by omega⟩ : Fin (r + 1)) = d.succ := by
                  ext; dsimp [d]; omega
                rw [hp_d, hq_d]
                refine ⟨?_, (hz_step d).2⟩
                by_cases hd0 : d.1 = 0
                · have hc0 : d.castSucc = 0 := by ext; exact hd0
                  rw [hc0]
                  have hz1_Bi : z d.succ ∈ B i := hM_sub_Bi d.castSucc (hz_step d).1
                  exact fun h => Finset.disjoint_right.mp hunif.blocks_disjoint hz0 (h ▸ hz1_Bi)
                · let d_prev : Fin r := ⟨d.1 - 1, by omega⟩
                  have hd_prev_succ : d_prev.succ = d.castSucc := by ext; dsimp [d_prev]; omega
                  have hz_d_nadj : ¬F.Adj (z d_prev.castSucc) (z d.castSucc) := by
                    rw [← hd_prev_succ]; exact (hz_step d_prev).2
                  have hz_succ_in : z d.succ ∈ M d_prev.succ := by
                    rw [hd_prev_succ]; exact (hz_step d).1
                  have hz_succ_adj : F.Adj (z d_prev.castSucc) (z d.succ) :=
                    ((mem_neighborFinsetIn_iff F _ _ _).mp (hM_step d_prev hz_succ_in)).2
                  exact fun h => hz_d_nadj (h ▸ hz_succ_adj)
              · by_cases hp_zr : p.1 = s + 1 + r
                · -- z (Fin.last r) and z_next
                  have hq_zn : q.1 = s + 2 + r := by omega
                  rw [hf_z p (by omega) (by omega), hf_zn q hq_zn]
                  have h_last : (⟨p.1 - (s + 1), by omega⟩ : Fin (r + 1)) = Fin.last r := by
                    ext; dsimp; omega
                  rw [h_last]
                  refine ⟨?_, hzr_adj⟩
                  rcases Nat.eq_zero_or_pos r with rfl | hr_pos
                  · have hzn_Bi : z_next ∈ B i := hM0 hz_next_M
                    exact fun h => Finset.disjoint_right.mp hunif.blocks_disjoint hz0 (h ▸ hzn_Bi)
                  · let d_prev : Fin r := ⟨r - 1, by omega⟩
                    have hd_prev_succ : d_prev.succ = Fin.last r := by ext; dsimp [d_prev]; omega
                    have hzr_nadj : ¬F.Adj (z d_prev.castSucc) (z (Fin.last r)) := by
                      rw [← hd_prev_succ]; exact (hz_step d_prev).2
                    have hzn_in : z_next ∈ M d_prev.succ := by
                      rw [hd_prev_succ]; exact hz_next_M
                    have hzn_adj : F.Adj (z d_prev.castSucc) z_next :=
                      ((mem_neighborFinsetIn_iff F _ _ _).mp (hM_step d_prev hzn_in)).2
                    exact fun h => hzr_nadj (h ▸ hzn_adj)
                · by_cases hp_zn : p.1 = s + 2 + r
                  · -- z_next and x₂
                    have hq_x2 : q.1 = s + 3 + r := by omega
                    rw [hf_zn p hp_zn, hf_x2 q hq_x2]
                    exact ⟨fun h => hzr_adj (h ▸ hzr_adj_C x₂ hx₂C), hzx₂_nadj⟩
                  · -- x₂ and x₃
                    have hp_x2 : p.1 = s + 3 + r := by omega
                    have hq_x3 : q.1 = s + 4 + r := by omega
                    rw [hf_x2 p hp_x2, hf_x3 q hq_x3]
                    exact ⟨hx₂_ne_x₃, hx₂x₃_nadj⟩
      · -- Non-consecutive pairs: p.1 + 1 < q.1 → F.Adj (f p) (f q)
        intro p q hpq
        by_cases hp_s : p.1 < s
        · rw [hf_v p hp_s]
          by_cases hq_s : q.1 < s
          · rw [hf_v q hq_s]
            have hp_ne_q : (⟨p.1, hp_s⟩ : Fin s) ≠ ⟨q.1, hq_s⟩ := by
              intro h; have := Fin.mk.inj_iff.mp h; omega
            have h_not_path : ¬(pathGraph s).Adj ⟨p.1, hp_s⟩ ⟨q.1, hq_s⟩ := by
              rw [pathGraph_adj]; dsimp; omega
            have h_not_compl := mt (hunif.stem_induced_path_compl ⟨p.1, hp_s⟩ ⟨q.1, hq_s⟩).mp h_not_path
            have hv_ne : v_hat ⟨p.1, hp_s⟩ ≠ v_hat ⟨q.1, hq_s⟩ := hunif.stem_injective.ne hp_ne_q
            exact Decidable.byContradiction (fun hn => h_not_compl ⟨hv_ne, hn⟩)
          · by_cases hq_eq_s : q.1 = s
            · rw [hf_a q hq_eq_s]
              exact hunif.stem_init_adj_handle ⟨p.1, hp_s⟩ (by dsimp; omega)
            · by_cases hq_eq_s1 : q.1 = s + 1
              · rw [hf_z q (by omega) (by omega)]
                have h0_eq : (⟨q.1 - (s + 1), by omega⟩ : Fin (r + 1)) = 0 := by ext; dsimp; omega
                rw [h0_eq]
                exact hunif.stem_complete_Bj ⟨p.1, hp_s⟩ (z 0) hz0
              · exact hunif.stem_complete_Bi ⟨p.1, hp_s⟩ (f q) (hf_in_Bi q (by omega))
        · by_cases hp_eq_s : p.1 = s
          · rw [hf_a p hp_eq_s]
            exact hunif.handle_complete_Bi (f q) (hf_in_Bi q (by omega))
          · by_cases hp_z_step : p.1 ≤ s + r
            · let d : Fin r := ⟨p.1 - (s + 1), by omega⟩
              rw [hf_z p (by omega) (by omega)]
              have hp_d : (⟨p.1 - (s + 1), by omega⟩ : Fin (r + 1)) = d.castSucc := by
                ext; dsimp [d]
              rw [hp_d]
              have hq_in : f q ∈ M d.succ := hf_in_M_succ d q (by dsimp [d]; omega)
              exact ((mem_neighborFinsetIn_iff F _ _ _).mp (hM_step d hq_in)).2
            · by_cases hp_zr : p.1 = s + 1 + r
              · rw [hf_z p (by omega) (by omega)]
                have h_last : (⟨p.1 - (s + 1), by omega⟩ : Fin (r + 1)) = Fin.last r := by
                  ext; dsimp; omega
                rw [h_last]
                by_cases hq_x2 : q.1 = s + 3 + r
                · rw [hf_x2 q hq_x2]; exact hzr_adj_C x₂ hx₂C
                · have hq_x3 : q.1 = s + 4 + r := by omega
                  rw [hf_x3 q hq_x3]; exact hzr_adj_C x₃ hx₃C
              · have hp_zn : p.1 = s + 2 + r := by omega
                have hq_x3 : q.1 = s + 4 + r := by omega
                rw [hf_zn p hp_zn, hf_x3 q hq_x3]
                exact hzx₃_adj

/-- Auxiliary induction partitioning a weighted finite set into `k` disjoint subsets each of weight $\ge \tau$. -/
lemma exists_disjoint_subsets_sum_ge_aux {α : Type*} [DecidableEq α]
    (f : α → ℝ) (τ : ℝ) (hτ : 0 < τ) :
    ∀ (k : ℕ) (S : Finset α),
      (∀ a ∈ S, 0 ≤ f a ∧ f a ≤ τ) →
      2 * (k : ℝ) * τ ≤ ∑ a ∈ S, f a →
      ∃ I : Fin k → Finset α,
        (∀ j : Fin k, I j ⊆ S ∧ τ ≤ ∑ a ∈ I j, f a) ∧
        (∀ j₁ j₂ : Fin k, j₁ ≠ j₂ → Disjoint (I j₁) (I j₂)) := by
  intro k
  induction k with
  | zero =>
    intro S _ _
    refine ⟨Fin.elim0, fun j => Fin.elim0 j, fun j => Fin.elim0 j⟩
  | succ m ih =>
    intro S h_each h_sum
    have h_tau_le : τ ≤ ∑ a ∈ S, f a := by
      have : (0 : ℝ) ≤ (m : ℝ) * τ := by positivity
      push_cast at h_sum
      linarith
    obtain ⟨F₁, hF₁_sub, hF₁_ge, hF₁_le⟩ :=
      exists_subset_sum_Icc S f τ (le_of_lt hτ) (fun a ha => (h_each a ha).2) h_tau_le
    let S' := S \ F₁
    have hS'_sub : S' ⊆ S := Finset.sdiff_subset
    have hF₁_disj : Disjoint F₁ S' := Finset.disjoint_sdiff
    have hS'_sum : 2 * (m : ℝ) * τ ≤ ∑ a ∈ S', f a := by
      have h_sp := Finset.sum_sdiff hF₁_sub (f := f)
      push_cast at h_sum
      linarith
    obtain ⟨I', hI'_sub, hI'_disj⟩ := ih S' (fun a ha => h_each a (hS'_sub ha)) hS'_sum
    refine ⟨Fin.cons F₁ I', ?_, ?_⟩
    · intro j
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · simp [hF₁_sub, hF₁_ge]
      · simp only [Fin.cons_succ]
        exact ⟨(hI'_sub j').1.trans hS'_sub, (hI'_sub j').2⟩
    · intro j₁ j₂ hj
      rcases Fin.eq_zero_or_eq_succ j₁ with rfl | ⟨j₁', rfl⟩ <;>
        rcases Fin.eq_zero_or_eq_succ j₂ with rfl | ⟨j₂', rfl⟩
      · exact False.elim (hj rfl)
      · simp only [Fin.cons_zero, Fin.cons_succ]
        exact Finset.disjoint_of_subset_right (hI'_sub j₂').1 hF₁_disj
      · simp only [Fin.cons_zero, Fin.cons_succ]
        exact (Finset.disjoint_of_subset_right (hI'_sub j₁').1 hF₁_disj).symm
      · simp only [Fin.cons_succ]
        exact hI'_disj j₁' j₂' (fun h => hj (congr_arg Fin.succ h))

/-- **Greedy Anticonnected Component Grouping Lemma** (used in Proposition 1, Lemma 12, Lemma 13, and Theorem 7(1)):
Let $N^* \subseteq N_T$ be subsets of $V$, $\tau > 0$, $p_{\mathrm{comp}} \ge 1$, and $w \in V$ not complete
in $F$ to $N_T$. If every anticonnected component of $F[N_F(w) \cap N_T]$ is a proper module of $F[N_T]$,
every proper module $X$ of $F[N_T]$ intersecting $N^*$ satisfies $|X \cap N^*| \le \tau$, and
$|N_F(w) \cap N^*| \ge 2 p_{\mathrm{comp}} \tau$, then $F[N^*]$ contains a complete
$(p_{\mathrm{comp}}, \tau)$-blockade of exact length $p_{\mathrm{comp}}$. -/
theorem exists_complete_blockade_of_small_components {F : SimpleGraph V}
    {N_T N_star : Finset V} {w : V} {p_comp : ℕ} {τ : ℝ}
    (hNs_NT : N_star ⊆ N_T) (hτ_pos : 0 < τ)
    (h_mod : ∀ C : Finset V,
      IsAnticonnectedComponentOf F (neighborFinsetIn F w N_T) C → IsProperModuleIn F N_T C)
    (h_small : ∀ X : Finset V,
      IsProperModuleIn F N_T X → (X ∩ N_star).Nonempty → ((X ∩ N_star).card : ℝ) ≤ τ)
    (h_deg : 2 * (p_comp : ℝ) * τ ≤ ((neighborFinsetIn F w N_star).card : ℝ)) :
    ∃ D : Fin p_comp → Finset V, IsCompleteBlockadeIn F N_star p_comp τ D := by
  let Z_T := neighborFinsetIn F w N_T
  let Z_star := neighborFinsetIn F w N_star
  obtain ⟨q, C, hC_fam⟩ := exists_anticonnectedComponentFamily F Z_T
  let C' : Fin q → Finset V := fun s => C s ∩ N_star
  have hC'_disj : ∀ s t : Fin q, s ≠ t → Disjoint (C' s) (C' t) :=
    fun s t hst => Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left (hC_fam.pairwise_disjoint s t hst))
  have hC'_comp : ∀ s t : Fin q, s ≠ t → IsCompletePair F (C' s) (C' t) := by
    intro s t hst u hu v hv
    have hcomp := (hC_fam.is_component s).isCompletePair_of_disjoint
      (hC_fam.is_component t) (hC_fam.pairwise_disjoint s t hst)
    exact hcomp u (Finset.mem_inter.mp hu).1 v (Finset.mem_inter.mp hv).1
  have hC'_union : Finset.univ.biUnion C' = Z_star := by
    ext x
    simp only [C', Z_star, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_inter, mem_neighborFinsetIn_iff]
    constructor
    · rintro ⟨s, hxCs, hxNs⟩
      have hxZT := (hC_fam.is_component s).1 hxCs
      exact ⟨hxNs, ((mem_neighborFinsetIn_iff F w N_T x).mp hxZT).2⟩
    · rintro ⟨hxNs, hwx⟩
      have hxZT : x ∈ Z_T := (mem_neighborFinsetIn_iff F w N_T x).mpr ⟨hNs_NT hxNs, hwx⟩
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
    have h_r : ((D j).card : ℝ) = ∑ s ∈ I j, ((C' s).card : ℝ) := by
      exact_mod_cast hD_card j
    rw [h_r]
    exact (hI_sub j).2
  refine ⟨D, ⟨?_, ?_, ?_, hD_width⟩, ?_⟩
  · intro j
    rw [Finset.biUnion_subset]
    intro s _; exact Finset.inter_subset_right
  · intro j
    rw [← Finset.card_pos, ← @Nat.cast_pos ℝ]
    linarith [hD_width j]
  · intro j₁ j₂ hj
    rw [Finset.disjoint_biUnion_left]
    intro s hs
    rw [Finset.disjoint_biUnion_right]
    intro t ht
    have hst : s ≠ t := fun h => Finset.disjoint_left.mp (hI_disj j₁ j₂ hj) hs (h ▸ ht)
    exact hC'_disj s t hst
  · intro j₁ j₂ hj u hu v hv
    obtain ⟨s, hs, hus⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨t, ht, hvt⟩ := Finset.mem_biUnion.mp hv
    have hst : s ≠ t := fun h => Finset.disjoint_left.mp (hI_disj j₁ j₂ hj) hs (h ▸ ht)
    exact hC'_comp s t hst u hus v hvt

/-!
## Section 7: Lemma 10(1)–(2) — Union-Pool and Internal Depth-$d$ Stem Promotions

Formalizes Lemma 10(1)–(2) (`main.tex` lines 517–551):
- **Core Dyadic Pool Extraction (`greedy_pool_comb_extraction`)**: Greedily peeling vertices with
  $> \tau |M|$ neighbors in the residual subset either stops early with residual size $> (1 - \alpha)|M|$
  or removes $\ge \alpha |M| \ge 2^{-4}|M|$ vertices in $m < \tau^{-1}$ steps; pigeonholing into
  dyadic buckets $J_t$ ($t \ge 20$) via $\sum_{t \ge 20} (t+1)^{-2} < 2^{-4}$ and reverse-order
  cleaning (`backwardClean`) extracts a $(k_{\mathrm{comb}}, w_{\mathrm{sub}})$-comb with
  $k_{\mathrm{comb}} \in (512, \tau^{-1})$ and $w_{\mathrm{sub}} \ge \max\bigl(\frac{|M|}{16 k_{\mathrm{comb}}^2}, \frac{\tau}{2}|M|\bigr)$.
- **Lemma 10(1) (`union_pool_stem_promotion`)**: Cross-block promotion from union pools
  $S_i, D_i \subseteq \bigcup_{j \neq i} B_j$ to per-handle $(s+1)$-stems (`hasPerHandleApexStems_succ_of_union_pool`).
- **Lemma 10(2) (`internal_depth_d_stem_promotion`)**: Internal depth-$d$ promotion from cutter
  pools $A \subseteq M_{d-1} \setminus N_F(z_{d-1})$ to shared $(s+1+d)$-stems (`hasPerHandleApexStems_of_internal_depth_d`).
-/

/-- Telescoping bound $\sum_{t=20}^{20+n} \frac{1}{(t+1)^2} \le \frac{1}{20} - \frac{1}{21+n}$. -/
lemma sum_inv_sq_Icc_ge20_le (n : ℕ) :
    ∑ t ∈ Finset.Icc 20 (20 + n), (1 : ℝ) / ((t : ℝ) + 1) ^ 2 ≤
      1 / 20 - 1 / ((20 + n + 1 : ℕ) : ℝ) := by
  induction n with
  | zero =>
    simp
    norm_num
  | succ m ih =>
    rw [show 20 + (m + 1) = (20 + m) + 1 by omega, Finset.sum_Icc_succ_top (by omega)]
    have hm1 : (0 : ℝ) < ((20 + m + 1 : ℕ) : ℝ) := by positivity
    have hm2 : (0 : ℝ) < ((20 + m + 1 + 1 : ℕ) : ℝ) := by positivity
    have hcast : ((20 + m + 1 + 1 : ℕ) : ℝ) = ((20 + m + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
    have hstep : 1 / ((((20 + m + 1 : ℕ) : ℝ)) + 1) ^ 2 ≤
        1 / ((20 + m + 1 : ℕ) : ℝ) - 1 / ((20 + m + 1 + 1 : ℕ) : ℝ) := by
      rw [div_sub_div _ _ (ne_of_gt hm1) (ne_of_gt hm2),
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hcast]
    linarith

/-- For any $N \in \mathbb{N}$, $\sum_{t=20}^N \frac{1}{(t+1)^2} < \frac{1}{16} = 2^{-4}$. -/
lemma sum_inv_sq_Icc_20_lt (N : ℕ) :
    ∑ t ∈ Finset.Icc 20 N, (1 : ℝ) / ((t : ℝ) + 1) ^ 2 < 1 / 16 := by
  by_cases hN : 20 ≤ N
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hN
    have h1 := sum_inv_sq_Icc_ge20_le n
    have h2 : (0 : ℝ) < 1 / ((20 + n + 1 : ℕ) : ℝ) := by positivity
    linarith
  · have h_emp : Finset.Icc 20 N = ∅ := Finset.Icc_eq_empty (by omega)
    rw [h_emp, Finset.sum_empty]
    norm_num

/-- For all $t \ge 20$, $512 (t + 1)^2 \le 2^{t - 1}$. -/
lemma nat_sq_mul_512_le_two_pow {t : ℕ} (ht : 20 ≤ t) :
    512 * (t + 1) ^ 2 ≤ 2 ^ (t - 1) := by
  have haux : ∀ n : ℕ, 512 * (20 + n + 1) ^ 2 ≤ 2 ^ (19 + n) := by
    intro n
    induction n with
    | zero => decide
    | succ m ih =>
      have h_id : 512 * (20 + (m + 1) + 1) ^ 2 + (512 * m ^ 2 + 20480 * m + 203776) =
          2 * (512 * (20 + m + 1) ^ 2) := by ring
      have h_pow : 2 ^ (19 + (m + 1)) = 2 * 2 ^ (19 + m) := by
        rw [show 19 + (m + 1) = (19 + m) + 1 by omega, Nat.pow_succ]; ring
      omega
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le ht
  rw [show 20 + n - 1 = 19 + n by omega]
  exact haux n

/-- For all $t \ge 20$, $(t + 1)^4 \le 2^t$. -/
lemma nat_fourth_le_two_pow_ge20 {t : ℕ} (ht : 20 ≤ t) :
    (t + 1) ^ 4 ≤ 2 ^ t := by
  have haux : ∀ n : ℕ, (20 + n + 1) ^ 4 ≤ 2 ^ (20 + n) := by
    intro n
    induction n with
    | zero => decide
    | succ m ih =>
      have h_id : (20 + (m + 1) + 1) ^ 4 +
          (m ^ 4 + 80 * m ^ 3 + 2388 * m ^ 2 + 31496 * m + 154706) =
          2 * (20 + m + 1) ^ 4 := by ring
      have h_pow : 2 ^ (20 + (m + 1)) = 2 * 2 ^ (20 + m) := by
        rw [show 20 + (m + 1) = (20 + m) + 1 by omega, Nat.pow_succ]; ring
      omega
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le ht
  exact haux n

/-- Extracted dyadic bucket scale bounds for Lemma 10(1) and Lemma 10(2). -/
lemma dyadic_pool_scale_bounds {t k_comb : ℕ} {M_card D₀_card : ℝ}
    (ht_20 : 20 ≤ t) (hM_pos : 0 < M_card)
    (h_vol : (1 / ((t : ℝ) + 1) ^ 2) * M_card < 2 * ((k_comb : ℝ) * D₀_card))
    (h_D₀_ub : (2 : ℝ) ^ t * D₀_card ≤ M_card) :
    512 < k_comb ∧ (2 : ℝ) ^ (t + 2) ≤ 16 * (k_comb : ℝ) ^ 2 := by
  have ht1_pos : (0 : ℝ) < ((t : ℝ) + 1) ^ 2 := by positivity
  have h2t_pos : (0 : ℝ) < (2 : ℝ) ^ t := by positivity
  have h1 : M_card < 2 * (k_comb : ℝ) * D₀_card * ((t : ℝ) + 1) ^ 2 := by
    have hm := mul_lt_mul_of_pos_right h_vol ht1_pos
    have h_lhs : (1 / ((t : ℝ) + 1) ^ 2) * M_card * ((t : ℝ) + 1) ^ 2 = M_card := by field_simp
    linarith
  have h2 : M_card * (2 : ℝ) ^ t <
      2 * (k_comb : ℝ) * ((2 : ℝ) ^ t * D₀_card) * ((t : ℝ) + 1) ^ 2 := by
    calc M_card * (2 : ℝ) ^ t
        < (2 * (k_comb : ℝ) * D₀_card * ((t : ℝ) + 1) ^ 2) * (2 : ℝ) ^ t :=
          mul_lt_mul_of_pos_right h1 h2t_pos
      _ = 2 * (k_comb : ℝ) * ((2 : ℝ) ^ t * D₀_card) * ((t : ℝ) + 1) ^ 2 := by ring
  have h3 : 2 * (k_comb : ℝ) * ((2 : ℝ) ^ t * D₀_card) * ((t : ℝ) + 1) ^ 2 ≤
      M_card * (2 * (k_comb : ℝ) * ((t : ℝ) + 1) ^ 2) := by
    have hk_nn : (0 : ℝ) ≤ 2 * (k_comb : ℝ) := by positivity
    calc 2 * (k_comb : ℝ) * ((2 : ℝ) ^ t * D₀_card) * ((t : ℝ) + 1) ^ 2
        ≤ 2 * (k_comb : ℝ) * M_card * ((t : ℝ) + 1) ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h_D₀_ub hk_nn) (by positivity)
      _ = M_card * (2 * (k_comb : ℝ) * ((t : ℝ) + 1) ^ 2) := by ring
  have h4 : (2 : ℝ) ^ t < 2 * (k_comb : ℝ) * ((t : ℝ) + 1) ^ 2 :=
    lt_of_mul_lt_mul_left (lt_of_lt_of_le h2 h3) (le_of_lt hM_pos)
  have h_pow_t : (2 : ℝ) ^ t = 2 * (2 : ℝ) ^ (t - 1) := by
    conv_lhs => rw [show t = (t - 1) + 1 by omega, pow_succ]
    ring
  have hk_comb_lb : (2 : ℝ) ^ (t - 1) < (k_comb : ℝ) * ((t : ℝ) + 1) ^ 2 := by linarith
  have hk_gt_512 : 512 < k_comb := by
    have h_512 : 512 * ((t : ℝ) + 1) ^ 2 ≤ (2 : ℝ) ^ (t - 1) := by
      exact_mod_cast nat_sq_mul_512_le_two_pow ht_20
    have h_lt : 512 * ((t : ℝ) + 1) ^ 2 < (k_comb : ℝ) * ((t : ℝ) + 1) ^ 2 :=
      lt_of_le_of_lt h_512 hk_comb_lb
    have h_r : (512 : ℝ) < (k_comb : ℝ) := lt_of_mul_lt_mul_right h_lt (by positivity)
    exact_mod_cast h_r
  have h_2t2_le : (2 : ℝ) ^ (t + 2) ≤ 16 * (k_comb : ℝ) ^ 2 := by
    have h_sq := pow_le_pow_left₀ (by positivity) (le_of_lt hk_comb_lb) 2
    have h_lhs : ((2 : ℝ) ^ (t - 1)) ^ 2 = (2 : ℝ) ^ (t - 2) * (2 : ℝ) ^ t := by
      rw [← pow_mul, ← pow_add, show (t - 1) * 2 = (t - 2) + t by omega]
    have h_rhs : ((k_comb : ℝ) * ((t : ℝ) + 1) ^ 2) ^ 2 = (k_comb : ℝ) ^ 2 * ((t : ℝ) + 1) ^ 4 := by ring
    rw [h_lhs, h_rhs] at h_sq
    have h_t4 : ((t : ℝ) + 1) ^ 4 ≤ (2 : ℝ) ^ t := by
      exact_mod_cast nat_fourth_le_two_pow_ge20 ht_20
    have h_mul : (2 : ℝ) ^ (t - 2) * ((t : ℝ) + 1) ^ 4 ≤ (k_comb : ℝ) ^ 2 * ((t : ℝ) + 1) ^ 4 := by
      calc (2 : ℝ) ^ (t - 2) * ((t : ℝ) + 1) ^ 4
          ≤ (2 : ℝ) ^ (t - 2) * (2 : ℝ) ^ t := mul_le_mul_of_nonneg_left h_t4 (by positivity)
        _ ≤ (k_comb : ℝ) ^ 2 * ((t : ℝ) + 1) ^ 4 := h_sq
    have h_t2 : (2 : ℝ) ^ (t - 2) ≤ (k_comb : ℝ) ^ 2 :=
      le_of_mul_le_mul_right h_mul (by positivity)
    calc (2 : ℝ) ^ (t + 2) = 16 * (2 : ℝ) ^ (t - 2) := by
          rw [show t + 2 = (t - 2) + 4 by omega, pow_add]; norm_num; ring
      _ ≤ 16 * (k_comb : ℝ) ^ 2 := mul_le_mul_of_nonneg_left h_t2 (by positivity)
  exact ⟨hk_gt_512, h_2t2_le⟩

/-- Equivalence between an $(\ell, w)$-comb in $F^c$ and an $(\ell, w)$-co-comb in $F$. -/
theorem isCoCombIn_of_isCombIn_compl {F : SimpleGraph V} {S : Finset V} {ℓ : ℕ} {w : ℝ}
    {a : Fin ℓ → V} {B : Fin ℓ → Finset V} (h : IsCombIn Fᶜ S ℓ w a B) :
    IsCoCombIn F S ℓ w a B where
  is_blockade :=
    { subset_ambient := h.is_blockade.subset_ambient
      nonempty_blocks := h.is_blockade.nonempty_blocks
      pairwise_disjoint := h.is_blockade.pairwise_disjoint
      width_ge := h.is_blockade.width_ge }
  apex_in_ambient := h.apex_in_ambient
  apex_injective := h.apex_injective
  apex_disjoint_blocks := h.apex_disjoint_blocks
  apex_anticomplete_own i u hu := (h.apex_complete_own i u hu).2
  apex_complete_other i j hij u hu := by
    have hne : a i ≠ u := fun heq => h.apex_disjoint_blocks i j (heq ▸ hu)
    exact Decidable.byContradiction (fun hn => h.apex_anticomplete_other i j hij u hu ⟨hne, hn⟩)

/-- Greedy pool extraction with fixed degree threshold `τ_abs` and stopping size `minA`. -/
noncomputable def greedyPoolSteps (G : SimpleGraph V) (P : Finset V) (τ_abs minA : ℝ) :
    ℕ → Finset V → List (StepData V) × Finset V
  | 0, A => ([], A)
  | k + 1, A =>
    if h : minA < (A.card : ℝ) ∧ ∃ u ∈ P, τ_abs < ((neighborFinsetIn G u A).card : ℝ) then
      let hP : P.Nonempty := let ⟨u, hu, _⟩ := h.2; ⟨u, hu⟩
      let a := Classical.choose (Finset.exists_max_image P (fun u => (neighborFinsetIn G u A).card) hP)
      let D := neighborFinsetIn G a A
      let res := greedyPoolSteps G P τ_abs minA k (A \ D)
      (⟨a, D, A⟩ :: res.1, res.2)
    else
      ([], A)

/-- Subset invariants $A_{\mathrm{end}} \subseteq A$ and $s.D \subseteq s.A \subseteq A$ for `greedyPoolSteps`. -/
lemma greedyPoolSteps_subset (G : SimpleGraph V) (P : Finset V) (τ_abs minA : ℝ)
    (k : ℕ) (A : Finset V) :
    (greedyPoolSteps G P τ_abs minA k A).2 ⊆ A ∧
    ∀ s ∈ (greedyPoolSteps G P τ_abs minA k A).1, s.D ⊆ s.A ∧ s.A ⊆ A := by
  induction k generalizing A with
  | zero => simp [greedyPoolSteps]
  | succ k ih =>
    unfold greedyPoolSteps
    split_ifs with h
    · dsimp only
      obtain ⟨h_end, h_steps⟩ := ih (A \ neighborFinsetIn G
        (Classical.choose (Finset.exists_max_image P (fun u => (neighborFinsetIn G u A).card)
          ⟨h.2.choose, h.2.choose_spec.1⟩)) A)
      refine ⟨h_end.trans sdiff_subset, ?_⟩
      intro s hs
      simp only [List.mem_cons] at hs
      rcases hs with rfl | hs
      · exact ⟨neighborFinsetIn_subset G _ A, Subset.rfl⟩
      · obtain ⟨hD, hA⟩ := h_steps s hs
        exact ⟨hD, hA.trans sdiff_subset⟩
    · simp

/-- Greedy maximality and threshold invariants at each step $s$ of `greedyPoolSteps`. -/
lemma greedyPoolSteps_props (G : SimpleGraph V) (P : Finset V) (τ_abs minA : ℝ)
    (k : ℕ) (A : Finset V) :
    ∀ s ∈ (greedyPoolSteps G P τ_abs minA k A).1,
      s.a ∈ P ∧
      s.D = neighborFinsetIn G s.a s.A ∧
      minA < (s.A.card : ℝ) ∧
      τ_abs < (s.D.card : ℝ) ∧
      ∀ u ∈ P, (neighborFinsetIn G u s.A).card ≤ s.D.card := by
  induction k generalizing A with
  | zero => simp [greedyPoolSteps]
  | succ k ih =>
    unfold greedyPoolSteps
    split_ifs with h
    · dsimp only
      have hP : P.Nonempty := let ⟨u, hu, _⟩ := h.2; ⟨u, hu⟩
      have ha_spec := Classical.choose_spec
        (Finset.exists_max_image P (fun u => (neighborFinsetIn G u A).card) hP)
      intro s hs
      simp only [List.mem_cons] at hs
      rcases hs with rfl | hs
      · obtain ⟨u₀, hu₀, h_gt⟩ := h.2
        have h_le : (neighborFinsetIn G u₀ A).card ≤
            (neighborFinsetIn G (Classical.choose
              (Finset.exists_max_image P (fun u => (neighborFinsetIn G u A).card) hP)) A).card :=
          ha_spec.2 u₀ hu₀
        have h_le_r : ((neighborFinsetIn G u₀ A).card : ℝ) ≤
            ((neighborFinsetIn G (Classical.choose
              (Finset.exists_max_image P (fun u => (neighborFinsetIn G u A).card) hP)) A).card : ℝ) := by
          exact_mod_cast h_le
        exact ⟨ha_spec.1, rfl, h.1, h_gt.trans_le h_le_r, ha_spec.2⟩
      · exact ih _ s hs
    · simp

/-- Volume conservation $\sum_s |s.D| + |A_{\mathrm{end}}| = |A|$ and stopping condition for `greedyPoolSteps`. -/
lemma greedyPoolSteps_sum_and_terminal (G : SimpleGraph V) (P : Finset V) (τ_abs minA : ℝ)
    (hτ : 0 ≤ τ_abs) (hminA : 0 ≤ minA) (k : ℕ) (A : Finset V) (hk : A.card ≤ k) :
    ((greedyPoolSteps G P τ_abs minA k A).1.map (fun s => s.D.card)).sum +
      (greedyPoolSteps G P τ_abs minA k A).2.card = A.card ∧
    ¬(minA < ((greedyPoolSteps G P τ_abs minA k A).2.card : ℝ) ∧
      ∃ u ∈ P, τ_abs < ((neighborFinsetIn G u (greedyPoolSteps G P τ_abs minA k A).2).card : ℝ)) := by
  induction k generalizing A with
  | zero =>
    have hA0 : A.card = 0 := Nat.eq_zero_of_le_zero hk
    simp only [greedyPoolSteps, List.map_nil, List.sum_nil, zero_add, hA0, Nat.cast_zero, true_and]
    intro h; linarith
  | succ k ih =>
    unfold greedyPoolSteps
    split_ifs with h
    · dsimp only
      have hP : P.Nonempty := let ⟨u, hu, _⟩ := h.2; ⟨u, hu⟩
      set a := Classical.choose (Finset.exists_max_image P (fun u => (neighborFinsetIn G u A).card) hP)
      have ha_spec := Classical.choose_spec (Finset.exists_max_image P (fun u => (neighborFinsetIn G u A).card) hP)
      set D := neighborFinsetIn G a A
      obtain ⟨u₀, hu₀, h_gt⟩ := h.2
      have h_le : (neighborFinsetIn G u₀ A).card ≤ D.card := ha_spec.2 u₀ hu₀
      have hD_pos_r : (0 : ℝ) < (D.card : ℝ) := by
        have h_le_r : ((neighborFinsetIn G u₀ A).card : ℝ) ≤ (D.card : ℝ) := by exact_mod_cast h_le
        linarith
      have hD_pos : 1 ≤ D.card := by exact_mod_cast hD_pos_r
      have hD_sub : D ⊆ A := neighborFinsetIn_subset G a A
      have h_sdiff_card : (A \ D).card + D.card = A.card := card_sdiff_add_card_eq_card hD_sub
      have hk' : (A \ D).card ≤ k := by omega
      obtain ⟨h_sum, h_term⟩ := ih (A \ D) hk'
      simp only [List.map_cons, List.sum_cons]
      exact ⟨by omega, h_term⟩
    · simp [h]

/-- Pairwise disjointness / containment $s_2.D \subseteq s_1.A \setminus s_1.D$ along `greedyPoolSteps`. -/
lemma greedyPoolSteps_pairwise (G : SimpleGraph V) (P : Finset V) (τ_abs minA : ℝ)
    (k : ℕ) (A : Finset V) :
    (greedyPoolSteps G P τ_abs minA k A).1.Pairwise (fun s₁ s₂ => s₂.D ⊆ s₁.A \ s₁.D) := by
  induction k generalizing A with
  | zero => simp [greedyPoolSteps]
  | succ k ih =>
    unfold greedyPoolSteps
    split_ifs with h
    · dsimp only
      rw [List.pairwise_cons]
      refine ⟨?_, ih _⟩
      intro s₂ hs₂
      obtain ⟨_, h_steps⟩ := greedyPoolSteps_subset G P τ_abs minA k _
      obtain ⟨hD₂, hA₂⟩ := h_steps s₂ hs₂
      exact hD₂.trans hA₂
    · simp

/-- **Core Dyadic Pool Extraction Lemma** (shared by Lemma 10(1) and Lemma 10(2)):
Given $A_0 \subseteq M \subseteq S$, external pool $P \subseteq S$ disjoint from $M$ with
$|N_G(u) \cap A_0| < 2^{-20} |M|$ for all $u \in P$, threshold $\tau \in (0, 2^{-20}]$, and
removal fraction $\alpha \ge 2^{-4}$ ($\alpha |M| \le |A_0|$), either:
1. **(Stops Early)**: there exists $A_{\mathrm{end}} \subseteq A_0$ with
   $|A_{\mathrm{end}}| > |A_0| - \alpha |M|$ and $|N_G(u) \cap A_{\mathrm{end}}| \le \tau |M|$ for all $u \in P$; or
2. **(Dyadic Sub-Comb Extraction)**: there exist $k_{\mathrm{comb}} \in (512, \tau^{-1})$ ($k_{\mathrm{comb}} > 64$),
   handles $u : \text{Fin } k_{\mathrm{comb}} \to V$ in $P$, and teeth $B' : \text{Fin } k_{\mathrm{comb}} \to \text{Finset } V$
   in $A_0$ forming an $(k_{\mathrm{comb}}, w_{\mathrm{sub}})$-comb in $G$ inside $S$ with
   $w_{\mathrm{sub}} = \max(\frac{|M|}{16 k_{\mathrm{comb}}^2}, \frac{\tau}{2} |M|)$. -/
theorem greedy_pool_comb_extraction (G : SimpleGraph V) (S M A₀ P : Finset V)
    (τ α : ℝ) (hA₀_M : A₀ ⊆ M) (hM_S : M ⊆ S) (hP_S : P ⊆ S) (hPM_disj : Disjoint P M)
    (hM_pos : 0 < M.card)
    (hτ_pos : 0 < τ) (hτ_ub : τ ≤ (2 : ℝ)⁻¹ ^ 20)
    (hα_lb : (1 / 16 : ℝ) ≤ α) (hα_A₀ : α * (M.card : ℝ) ≤ (A₀.card : ℝ))
    (hP_deg : ∀ u ∈ P, ((neighborFinsetIn G u A₀).card : ℝ) < (2 : ℝ)⁻¹ ^ 20 * (M.card : ℝ)) :
    (∃ A_end ⊆ A₀, (A₀.card : ℝ) - α * (M.card : ℝ) < (A_end.card : ℝ) ∧
      ∀ u ∈ P, ((neighborFinsetIn G u A_end).card : ℝ) ≤ τ * (M.card : ℝ)) ∨
    (∃ (k_comb : ℕ) (u : Fin k_comb → V) (B' : Fin k_comb → Finset V),
      512 < k_comb ∧ (k_comb : ℝ) < τ⁻¹ ∧
      (∀ q : Fin k_comb, u q ∈ P ∧ B' q ⊆ A₀) ∧
      IsCombIn G S k_comb
        (max ((M.card : ℝ) / (16 * (k_comb : ℝ) ^ 2)) ((τ / 2) * (M.card : ℝ))) u B') := by
  have hM_r_pos : (0 : ℝ) < (M.card : ℝ) := Nat.cast_pos.mpr hM_pos
  set τ_abs := τ * (M.card : ℝ)
  set minA := (A₀.card : ℝ) - α * (M.card : ℝ)
  have hτ_abs_pos : 0 < τ_abs := by positivity
  have hminA_nn : 0 ≤ minA := by linarith
  set res := greedyPoolSteps G P τ_abs minA A₀.card A₀
  set steps := res.1
  set A_end := res.2
  obtain ⟨hA_end_sub, h_steps_sub⟩ := greedyPoolSteps_subset G P τ_abs minA A₀.card A₀
  have h_steps_props := greedyPoolSteps_props G P τ_abs minA A₀.card A₀
  obtain ⟨h_sum_eq, h_term⟩ := greedyPoolSteps_sum_and_terminal G P τ_abs minA
    (le_of_lt hτ_abs_pos) hminA_nn A₀.card A₀ le_rfl
  by_cases h_stop : minA < (A_end.card : ℝ)
  · left
    refine ⟨A_end, hA_end_sub, h_stop, fun u hu => ?_⟩
    by_contra h_gt
    push_neg at h_gt
    exact h_term ⟨h_stop, u, hu, h_gt⟩
  · right
    push_neg at h_stop
    have h_sum_ge_α : α * (M.card : ℝ) ≤ (((steps.map (fun s => s.D.card)).sum : ℕ) : ℝ) := by
      have h_sum_r : (((steps.map (fun s => s.D.card)).sum : ℕ) : ℝ) + (A_end.card : ℝ) = (A₀.card : ℝ) := by
        exact_mod_cast h_sum_eq
      linarith
    have h_sum_ge_16 : (1 / 16 : ℝ) * (M.card : ℝ) ≤ (((steps.map (fun s => s.D.card)).sum : ℕ) : ℝ) :=
      le_trans (mul_le_mul_of_nonneg_right hα_lb (le_of_lt hM_r_pos)) h_sum_ge_α
    have h_each_s : ∀ s ∈ steps, 1 ≤ s.D.card ∧ τ_abs < (s.D.card : ℝ) ∧
        (s.D.card : ℝ) < (2 : ℝ)⁻¹ ^ 20 * (M.card : ℝ) ∧ (∀ u ∈ s.D, G.Adj s.a u) := by
      intro s hs
      obtain ⟨ha, hD_eq, _, hD_gt, _⟩ := h_steps_props s hs
      obtain ⟨hD_sub_A, hA_sub_A₀⟩ := h_steps_sub s hs
      have hD_pos_r : (0 : ℝ) < (s.D.card : ℝ) := lt_trans hτ_abs_pos hD_gt
      have hD_ge_1 : 1 ≤ s.D.card := by exact_mod_cast hD_pos_r
      have hD_sub_A₀ : s.D ⊆ neighborFinsetIn G s.a A₀ := by
        rw [hD_eq]; exact neighborFinsetIn_mono G s.a hA_sub_A₀
      have hD_lt : (s.D.card : ℝ) < (2 : ℝ)⁻¹ ^ 20 * (M.card : ℝ) := by
        have h_le : (s.D.card : ℝ) ≤ ((neighborFinsetIn G s.a A₀).card : ℝ) :=
          Nat.cast_le.mpr (Finset.card_le_card hD_sub_A₀)
        exact lt_of_le_of_lt h_le (hP_deg s.a ha)
      have h_adj : ∀ u ∈ s.D, G.Adj s.a u := by
        intro u hu; rw [hD_eq, mem_neighborFinsetIn_iff] at hu; exact hu.2
      exact ⟨hD_ge_1, hD_gt, hD_lt, h_adj⟩
    -- Step count bound: steps.length * τ_abs < M.card, so steps.length < τ⁻¹
    have h_steps_len_lt : (steps.length : ℝ) < τ⁻¹ := by
      have h_sum_le_M : (steps.map (fun s => s.D.card)).sum ≤ M.card := by
        have h1 : A₀.card ≤ M.card := Finset.card_le_card hA₀_M
        change (steps.map (fun s => s.D.card)).sum + A_end.card = A₀.card at h_sum_eq
        omega
      have h_sum_gt_len : (steps.length : ℝ) * τ_abs < (((steps.map (fun s => s.D.card)).sum : ℕ) : ℝ) := by
        have h_ne : steps ≠ [] := by
          intro hnil
          rw [hnil] at h_sum_ge_16
          simp at h_sum_ge_16
          linarith
        have h_ind : ∀ L : List (StepData V), L ≠ [] → (∀ s ∈ L, τ_abs < (s.D.card : ℝ)) →
            (L.length : ℝ) * τ_abs < (((L.map (fun s => s.D.card)).sum : ℕ) : ℝ) := by
          intro L
          induction L with
          | nil => intro h; exact False.elim (h rfl)
          | cons s rest ih =>
            intro _ hL
            have hs_gt := hL s List.mem_cons_self
            by_cases hrest : rest = []
            · subst hrest; simp; linarith
            · have h_ih := ih hrest (fun s' hs' => hL s' (List.mem_cons_of_mem _ hs'))
              simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_one]
              linarith
        exact h_ind steps h_ne (fun s hs => (h_each_s s hs).2.1)
      have h_lt_M : ((steps.length : ℝ) * τ) * (M.card : ℝ) < 1 * (M.card : ℝ) := by
        have h1 : (steps.length : ℝ) * (τ * (M.card : ℝ)) < (M.card : ℝ) :=
          lt_of_lt_of_le h_sum_gt_len (Nat.cast_le.mpr h_sum_le_M)
        linarith
      have h_lt_1 : (steps.length : ℝ) * τ < 1 := lt_of_mul_lt_mul_right h_lt_M (le_of_lt hM_r_pos)
      rw [inv_eq_one_div, lt_div_iff₀ hτ_pos]
      exact h_lt_1
    -- Dyadic buckets J_t for t ∈ [20, M.card]
    let P_buck (t : ℕ) (s : StepData V) : Bool :=
      decide (20 ≤ t ∧ (2 : ℝ) ^ t * (s.D.card : ℝ) ≤ (M.card : ℝ) ∧
        (M.card : ℝ) < (2 : ℝ) ^ (t + 1) * (s.D.card : ℝ))
    have h_cov : ∀ s ∈ steps, ∃ t ∈ Finset.range (M.card + 1), P_buck t s = true := by
      intro s hs
      obtain ⟨h1_s, _, hlt_s, _⟩ := h_each_s s hs
      have h1_r : (1 : ℝ) ≤ (s.D.card : ℝ) := Nat.one_le_cast.mpr h1_s
      have h_le_M : (s.D.card : ℝ) ≤ (M.card : ℝ) := by
        have : (2 : ℝ)⁻¹ ^ 20 ≤ 1 := by norm_num
        nlinarith
      obtain ⟨t, ht_mem, ht_lb, ht_ub⟩ := exists_dyadic_bucket h1_r h_le_M le_rfl
      have ht_ge_20 : 20 ≤ t := by
        by_contra ht_lt
        have ht1 : t + 1 ≤ 20 := by omega
        have h_pow : (2 : ℝ) ^ (t + 1) ≤ (2 : ℝ) ^ 20 := pow_le_pow_right₀ (by norm_num) ht1
        have h_mul : (2 : ℝ) ^ (t + 1) * (s.D.card : ℝ) ≤ (2 : ℝ) ^ 20 * (s.D.card : ℝ) :=
          mul_le_mul_of_nonneg_right h_pow (Nat.cast_nonneg _)
        have h_lt20 : (2 : ℝ) ^ 20 * (s.D.card : ℝ) < (M.card : ℝ) := by
          have : (2 : ℝ) ^ 20 * (2 : ℝ)⁻¹ ^ 20 = 1 := by norm_num
          nlinarith
        linarith
      exact ⟨t, ht_mem, decide_eq_true ⟨ht_ge_20, ht_lb, ht_ub⟩⟩
    have h_sum_buckets : (((steps.map (fun s => s.D.card)).sum : ℕ) : ℝ) ≤
        ∑ t ∈ Finset.range (M.card + 1),
          ((((steps.filter (fun s => P_buck t s)).map (fun s => s.D.card)).sum : ℕ) : ℝ) := by
      exact_mod_cast list_sum_le_sum_range_filter steps M.card P_buck h_cov
    have h_inv_sum : ∑ t ∈ Finset.range (M.card + 1),
        (if 20 ≤ t then (1 / ((t : ℝ) + 1) ^ 2) * (M.card : ℝ) else 0) <
        (1 / 16 : ℝ) * (M.card : ℝ) := by
      have h_eq : ∑ t ∈ Finset.range (M.card + 1),
          (if 20 ≤ t then (1 / ((t : ℝ) + 1) ^ 2) * (M.card : ℝ) else 0) =
          (∑ t ∈ Finset.Icc 20 M.card, (1 : ℝ) / ((t : ℝ) + 1) ^ 2) * (M.card : ℝ) := by
        rw [Finset.sum_mul, ← Finset.sum_filter]
        refine Finset.sum_congr ?_ (fun _ _ => rfl)
        ext t
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
        omega
      rw [h_eq]
      exact mul_lt_mul_of_pos_right (sum_inv_sq_Icc_20_lt M.card) hM_r_pos
    have h_sum_buckets_20 :
        ∑ t ∈ Finset.range (M.card + 1),
          ((((steps.filter (fun s => P_buck t s)).map (fun s => s.D.card)).sum : ℕ) : ℝ) =
        ∑ t ∈ Finset.range (M.card + 1),
          (if 20 ≤ t then ((((steps.filter (fun s => P_buck t s)).map (fun s => s.D.card)).sum : ℕ) : ℝ) else 0) := by
      refine Finset.sum_congr rfl (fun t _ => ?_)
      by_cases ht : 20 ≤ t
      · simp [ht]
      · rw [if_neg ht]
        have h_emp : steps.filter (fun s => P_buck t s) = [] := by
          rw [List.filter_eq_nil_iff]
          intro s _ hP
          exact ht (of_decide_eq_true hP).1
        simp [h_emp]
    rw [h_sum_buckets_20] at h_sum_buckets
    obtain ⟨t, ht_mem, ht_gt⟩ :=
      Finset.exists_lt_of_sum_lt (lt_of_lt_of_le h_inv_sum (le_trans h_sum_ge_16 h_sum_buckets))
    have ht_20 : 20 ≤ t := by
      by_contra hnot
      rw [if_neg hnot, if_neg hnot] at ht_gt
      exact lt_irrefl 0 ht_gt
    rw [if_pos ht_20, if_pos ht_20] at ht_gt
    set J := steps.filter (fun s => P_buck t s)
    have hJ_sub : ∀ s ∈ J, s ∈ steps ∧
        ((2 : ℝ) ^ t * (s.D.card : ℝ) ≤ (M.card : ℝ) ∧
         (M.card : ℝ) < (2 : ℝ) ^ (t + 1) * (s.D.card : ℝ)) := by
      intro s hs
      rw [List.mem_filter] at hs
      exact ⟨hs.1, (of_decide_eq_true hs.2).2⟩
    have h_pw_steps : steps.Pairwise (fun s₁ s₂ =>
        s₁.a ≠ s₂.a ∧ Disjoint s₁.D s₂.D ∧ s₂.D ⊆ s₁.A ∧ ∀ u ∈ s₂.D, ¬G.Adj s₁.a u) := by
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      have h_sub_ij := List.pairwise_iff_getElem.mp (greedyPoolSteps_pairwise G P τ_abs minA A₀.card A₀) i j hi hj hij
      have hi_mem : steps[i] ∈ steps := List.getElem_mem _
      have hj_mem : steps[j] ∈ steps := List.getElem_mem _
      exact stepData_rel_props G (h_steps_props _ hi_mem).2.1 (h_steps_props _ hj_mem).2.1
        (h_each_s _ hj_mem).1 h_sub_ij
    have h_pw_J := h_pw_steps.filter (fun s => P_buck t s)
    cases hJ_eq : J with
    | nil =>
      rw [hJ_eq] at ht_gt
      simp only [List.map_nil, List.sum_nil, Nat.cast_zero] at ht_gt
      have : (0 : ℝ) < (1 / ((t : ℝ) + 1) ^ 2) * (M.card : ℝ) := by positivity
      linarith
    | cons s₀ J_rest =>
      have h_vol_nat : ((s₀ :: J_rest).map (fun s => s.D.card)).sum ≤
          2 * ((backwardClean G (s₀ :: J_rest)).length * s₀.D.card) := by
        apply bucket_volume_le_two_mul_length_mul_head G P s₀ J_rest
        · rw [← hJ_eq]; exact h_pw_J.imp (fun h => ⟨h.2.1, h.2.2.1⟩)
        · intro s hs
          rw [← hJ_eq] at hs
          have hs_steps := (hJ_sub s hs).1
          exact ⟨(h_steps_props s hs_steps).1, (h_steps_sub s hs_steps).1,
            (h_each_s s hs_steps).2.2.2, (h_steps_props s hs_steps).2.2.2.2⟩
      set tail := backwardClean G (s₀ :: J_rest)
      set k_comb := tail.length
      have h_vol_r : ((((s₀ :: J_rest).map (fun s => s.D.card)).sum : ℕ) : ℝ) ≤
          2 * ((k_comb : ℝ) * (s₀.D.card : ℝ)) := by exact_mod_cast h_vol_nat
      rw [hJ_eq] at ht_gt
      have hs₀_P := (hJ_sub s₀ (hJ_eq ▸ List.mem_cons_self)).2
      obtain ⟨hk_gt_512, h_2t2_le⟩ :=
        dyadic_pool_scale_bounds ht_20 hM_r_pos (lt_of_lt_of_le ht_gt h_vol_r) hs₀_P.1
      have hk_lt_inv : (k_comb : ℝ) < τ⁻¹ := by
        have h_len1 : tail.length ≤ (s₀ :: J_rest).length := by
          have h_gen : ∀ L : List (StepData V), (backwardClean G L).length ≤ L.length := by
            intro L; induction L with
            | nil => simp [backwardClean]
            | cons s rest ih =>
              unfold backwardClean; dsimp only; split_ifs <;> simp <;> omega
          exact h_gen _
        have h_len2 : (s₀ :: J_rest).length ≤ steps.length := by
          rw [← hJ_eq]; exact List.length_filter_le _ _
        have h_le_r : (k_comb : ℝ) ≤ (steps.length : ℝ) := Nat.cast_le.mpr (le_trans h_len1 h_len2)
        exact lt_of_le_of_lt h_le_r h_steps_len_lt
      have h_pw_tail : tail.Pairwise (fun q₁ q₂ =>
          q₁.a ≠ q₂.a ∧ Disjoint q₁.D q₂.D ∧
          (∀ u ∈ q₂.D, ¬G.Adj q₁.a u) ∧ (∀ u ∈ q₁.D, ¬G.Adj q₂.a u)) := by
        apply backwardClean_pairwise G (s₀ :: J_rest)
        rw [← hJ_eq]
        exact h_pw_J.imp (fun h => ⟨h.1, h.2.1, h.2.2.2⟩)
      let u : Fin k_comb → V := fun i => (tail[i.1]'i.2).a
      let B' : Fin k_comb → Finset V := fun i => (tail[i.1]'i.2).D
      have h_mem_tail : ∀ i : Fin k_comb, tail[i.1]'i.2 ∈ tail := fun i => List.getElem_mem _
      have h_q_props : ∀ q ∈ tail,
          q.a ∈ P ∧ q.D ⊆ A₀ ∧ q.D.Nonempty ∧
          max ((M.card : ℝ) / (16 * (k_comb : ℝ) ^ 2)) ((τ / 2) * (M.card : ℝ)) ≤ (q.D.card : ℝ) ∧
          (∀ v ∈ q.D, G.Adj q.a v) := by
        intro q hq
        obtain ⟨s, hs_mem, ha_eq, _, hD_sub, hD_card⟩ := backwardClean_sub G (s₀ :: J_rest) q hq
        rw [← hJ_eq] at hs_mem
        obtain ⟨hs_steps, hs_Pt⟩ := hJ_sub s hs_mem
        obtain ⟨hs_ge1, hs_gt_τ, _, hs_adj⟩ := h_each_s s hs_steps
        have hq_2 : (s.D.card : ℝ) ≤ 2 * (q.D.card : ℝ) := by exact_mod_cast hD_card
        have h_w1 : (M.card : ℝ) / (16 * (k_comb : ℝ) ^ 2) ≤ (q.D.card : ℝ) := by
          have h1 : (M.card : ℝ) / (2 : ℝ) ^ (t + 2) ≤ (q.D.card : ℝ) := by
            rw [div_le_iff₀ (by positivity)]
            calc (M.card : ℝ) ≤ (2 : ℝ) ^ (t + 1) * (s.D.card : ℝ) := le_of_lt hs_Pt.2
              _ ≤ (2 : ℝ) ^ (t + 1) * (2 * (q.D.card : ℝ)) :=
                  mul_le_mul_of_nonneg_left hq_2 (by positivity)
              _ = (q.D.card : ℝ) * (2 : ℝ) ^ (t + 2) := by
                  rw [show t + 2 = (t + 1) + 1 by omega, pow_succ]; ring
          exact le_trans (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) h_2t2_le) h1
        have h_w2 : (τ / 2) * (M.card : ℝ) ≤ (q.D.card : ℝ) := by linarith
        have hq_pos : 0 < q.D.card := by
          have : (0 : ℝ) < (q.D.card : ℝ) := lt_of_lt_of_le (by positivity) h_w2
          exact_mod_cast this
        refine ⟨ha_eq ▸ (h_steps_props s hs_steps).1,
          hD_sub.trans ((h_steps_sub s hs_steps).1.trans (h_steps_sub s hs_steps).2),
          Finset.card_pos.mp hq_pos, max_le h_w1 h_w2,
          fun v hv => ha_eq ▸ hs_adj v (hD_sub hv)⟩
      have h_rel : ∀ i j : Fin k_comb, i ≠ j →
          u i ≠ u j ∧ Disjoint (B' i) (B' j) ∧ ∀ v ∈ B' j, ¬G.Adj (u i) v := by
        intro i j hij
        have hij_val : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
        rcases lt_or_gt_of_ne hij_val with hlt | hgt
        · obtain ⟨hne, hdisj, hnot1, _⟩ := List.pairwise_iff_getElem.mp h_pw_tail i.1 j.1 i.2 j.2 hlt
          exact ⟨hne, hdisj, hnot1⟩
        · obtain ⟨hne, hdisj, _, hnot2⟩ := List.pairwise_iff_getElem.mp h_pw_tail j.1 i.1 j.2 i.2 hgt
          exact ⟨hne.symm, hdisj.symm, hnot2⟩
      refine ⟨k_comb, u, B', hk_gt_512, hk_lt_inv,
        fun q => ⟨(h_q_props _ (h_mem_tail q)).1, (h_q_props _ (h_mem_tail q)).2.1⟩, ?_⟩
      refine
        { is_blockade :=
            { subset_ambient := fun q => ((h_q_props _ (h_mem_tail q)).2.1.trans hA₀_M).trans hM_S
              nonempty_blocks := fun q => (h_q_props _ (h_mem_tail q)).2.2.1
              pairwise_disjoint := fun q₁ q₂ hq => (h_rel q₁ q₂ hq).2.1
              width_ge := fun q => (h_q_props _ (h_mem_tail q)).2.2.2.1 }
          apex_in_ambient := fun q => hP_S (h_q_props _ (h_mem_tail q)).1
          apex_injective := fun q₁ q₂ hq => Decidable.byContradiction (fun hne => (h_rel q₁ q₂ hne).1 hq)
          apex_disjoint_blocks := fun q₁ q₂ h_in =>
            Finset.disjoint_left.mp hPM_disj (h_q_props _ (h_mem_tail q₁)).1
              (hA₀_M ((h_q_props _ (h_mem_tail q₂)).2.1 h_in))
          apex_complete_own := fun q v hv => (h_q_props _ (h_mem_tail q)).2.2.2.2 v hv
          apex_anticomplete_other := fun q₁ q₂ hq v hv => (h_rel q₁ q₂ hq).2.2 v hv }

/-- **Stem Extension for Lemma 10(1)**: Extending per-handle $s$-stems of $((a_r, B_r) : r \in [\ell])$
to per-handle $(s+1)$-stems for a sub-comb or sub-co-comb $((u_q, B'_q) : q \in \text{Fin } k_{\mathrm{comb}})$
whose handles satisfy $u_q \in B_{j(q)}$ ($j(q) \neq i$) and teeth satisfy $B'_q \subseteq B_i$. -/
theorem hasPerHandleApexStems_succ_of_union_pool {F : SimpleGraph V} {S : Finset V}
    {ℓ s k_comb : ℕ} {w : ℝ} {a : Fin ℓ → V} {B : Fin ℓ → Finset V}
    {stems : Fin ℓ → Fin s → V} {i : Fin ℓ}
    (hcomb : IsCombOrCoCombIn F S ℓ w a B)
    (hstems : HasPerHandleApexStems F S ℓ s a B stems)
    {u : Fin k_comb → V} {B' : Fin k_comb → Finset V}
    (j_idx : Fin k_comb → Fin ℓ)
    (hj_ne : ∀ q : Fin k_comb, j_idx q ≠ i)
    (hu_in : ∀ q : Fin k_comb, u q ∈ B (j_idx q))
    (hB'_sub : ∀ q : Fin k_comb, B' q ⊆ B i) :
    ∃ stems' : Fin k_comb → Fin (s + 1) → V,
      HasPerHandleApexStems F S k_comb (s + 1) u B' stems' := by
  let stems' : Fin k_comb → Fin (s + 1) → V := fun q p =>
    if hps : p.1 < s then
      unifiedStem F S w a B stems i (j_idx q) ⟨p.1, hps⟩
    else
      unifiedHandle F S w a B i (j_idx q)
  refine ⟨stems', ?_⟩
  have h_unif : ∀ q : Fin k_comb,
      IsUnifiedHandleStemPair F S s (B i) (B (j_idx q))
        (unifiedStem F S w a B stems i (j_idx q)) (unifiedHandle F S w a B i (j_idx q)) ∧
      (∀ (p : Fin s) (r : Fin ℓ), ∀ x ∈ B r, F.Adj (unifiedStem F S w a B stems i (j_idx q) p) x) ∧
      (∀ r : Fin ℓ, unifiedHandle F S w a B i (j_idx q) ∉ B r) :=
    fun q => isUnifiedHandleStemPair_of_combOrCoComb hcomb hstems (hj_ne q).symm
  refine
    { stem_pos := by omega
      stem_in_ambient := ?_
      stem_injective := ?_
      stem_not_handle := ?_
      stem_not_in_blocks := ?_
      stem_induced_path_compl := ?_
      stem_last_nonadj_handle := ?_
      stem_init_adj_handle := ?_
      stem_complete_to_blocks := ?_ }
  · intro q p
    dsimp [stems']; split_ifs with hps
    · exact (h_unif q).1.stem_in_ambient ⟨p.1, hps⟩
    · exact (h_unif q).1.handle_in_ambient
  · intro q p₁ p₂ h_eq
    dsimp [stems'] at h_eq
    by_cases hp₁ : p₁.1 < s <;> by_cases hp₂ : p₂.1 < s
    · rw [dif_pos hp₁, dif_pos hp₂] at h_eq
      have := (h_unif q).1.stem_injective h_eq
      exact Fin.ext (Fin.mk.inj_iff.mp this)
    · rw [dif_pos hp₁, dif_neg hp₂] at h_eq
      exact False.elim ((h_unif q).1.stem_not_handle ⟨p₁.1, hp₁⟩ h_eq)
    · rw [dif_neg hp₁, dif_pos hp₂] at h_eq
      exact False.elim ((h_unif q).1.stem_not_handle ⟨p₂.1, hp₂⟩ h_eq.symm)
    · exact Fin.ext (by omega)
  · intro q₁ q₂ p h_eq
    dsimp [stems'] at h_eq
    split_ifs at h_eq with hps
    · have h_adj := (h_unif q₁).2.1 ⟨p.1, hps⟩ (j_idx q₂) (u q₂) (hu_in q₂)
      exact F.loopless (u q₂) (h_eq ▸ h_adj)
    · exact (h_unif q₁).2.2 (j_idx q₂) (h_eq ▸ hu_in q₂)
  · intro q₁ q₂ p h_in
    have h_Bi := hB'_sub q₂ h_in
    dsimp [stems'] at h_Bi
    split_ifs at h_Bi with hps
    · exact (h_unif q₁).1.stem_not_in_Bi ⟨p.1, hps⟩ h_Bi
    · exact (h_unif q₁).1.handle_not_in_Bi h_Bi
  · intro q p₁ p₂
    dsimp [stems']
    by_cases hp₁ : p₁.1 < s <;> by_cases hp₂ : p₂.1 < s
    · rw [dif_pos hp₁, dif_pos hp₂]
      rw [(h_unif q).1.stem_induced_path_compl ⟨p₁.1, hp₁⟩ ⟨p₂.1, hp₂⟩]
      simp [pathGraph_adj]
    · have hp₂_eq : p₂.1 = s := by omega
      rw [dif_pos hp₁, dif_neg hp₂]
      by_cases hp₁_last : p₁.1 + 1 = s
      · have h_path : (pathGraph (s + 1)).Adj p₁ p₂ := by rw [pathGraph_adj]; left; omega
        have h_compl : Fᶜ.Adj (unifiedStem F S w a B stems i (j_idx q) ⟨p₁.1, hp₁⟩)
            (unifiedHandle F S w a B i (j_idx q)) :=
          ⟨(h_unif q).1.stem_not_handle ⟨p₁.1, hp₁⟩,
           (h_unif q).1.stem_last_nonadj_handle ⟨p₁.1, hp₁⟩ hp₁_last⟩
        simp [h_path, h_compl]
      · have h_npath : ¬(pathGraph (s + 1)).Adj p₁ p₂ := by rw [pathGraph_adj]; omega
        have h_adj : F.Adj (unifiedStem F S w a B stems i (j_idx q) ⟨p₁.1, hp₁⟩)
            (unifiedHandle F S w a B i (j_idx q)) :=
          (h_unif q).1.stem_init_adj_handle ⟨p₁.1, hp₁⟩ (by dsimp; omega)
        have h_ncompl : ¬Fᶜ.Adj (unifiedStem F S w a B stems i (j_idx q) ⟨p₁.1, hp₁⟩)
            (unifiedHandle F S w a B i (j_idx q)) := fun hc => hc.2 h_adj
        simp [h_npath, h_ncompl]
    · have hp₁_eq : p₁.1 = s := by omega
      rw [dif_neg hp₁, dif_pos hp₂]
      by_cases hp₂_last : p₂.1 + 1 = s
      · have h_path : (pathGraph (s + 1)).Adj p₁ p₂ := by rw [pathGraph_adj]; right; omega
        have h_compl : Fᶜ.Adj (unifiedHandle F S w a B i (j_idx q))
            (unifiedStem F S w a B stems i (j_idx q) ⟨p₂.1, hp₂⟩) :=
          ⟨((h_unif q).1.stem_not_handle ⟨p₂.1, hp₂⟩).symm,
           fun h => (h_unif q).1.stem_last_nonadj_handle ⟨p₂.1, hp₂⟩ hp₂_last (F.symm h)⟩
        simp [h_path, h_compl]
      · have h_npath : ¬(pathGraph (s + 1)).Adj p₁ p₂ := by rw [pathGraph_adj]; omega
        have h_adj : F.Adj (unifiedStem F S w a B stems i (j_idx q) ⟨p₂.1, hp₂⟩)
            (unifiedHandle F S w a B i (j_idx q)) :=
          (h_unif q).1.stem_init_adj_handle ⟨p₂.1, hp₂⟩ (by dsimp; omega)
        have h_ncompl : ¬Fᶜ.Adj (unifiedHandle F S w a B i (j_idx q))
            (unifiedStem F S w a B stems i (j_idx q) ⟨p₂.1, hp₂⟩) := fun hc => hc.2 (F.symm h_adj)
        simp [h_npath, h_ncompl]
    · have hp₁₂ : p₁ = p₂ := Fin.ext (by omega)
      subst hp₁₂; simp
  · intro q p hp_last
    have hp_eq : p.1 = s := by omega
    dsimp [stems']; rw [dif_neg (by omega)]
    exact (h_unif q).1.handle_anticomplete_Bj (u q) (hu_in q)
  · intro q p hp_lt
    have hps : p.1 < s := by omega
    dsimp [stems']; rw [dif_pos hps]
    exact (h_unif q).1.stem_complete_Bj ⟨p.1, hps⟩ (u q) (hu_in q)
  · intro q₁ q₂ p x hx
    have hx_Bi := hB'_sub q₂ hx
    dsimp [stems']; split_ifs with hps
    · exact (h_unif q₁).1.stem_complete_Bi ⟨p.1, hps⟩ x hx_Bi
    · exact (h_unif q₁).1.handle_complete_Bi x hx_Bi

/-- **Lemma 10(1) (`union_pool_stem_promotion`, Cross-Block Union-Pool Comb and Co-Comb Promotion to Per-Handle $(s+1)$-Stems)**:
Given an $(\ell, w)$-comb or co-comb $((a_r, B_r) : r \in [\ell])$ in $F$ inside $S$ with per-handle $s$-stems,
a subset $M_i \subseteq B_i$ ($M_i \neq \emptyset$), threshold $\tau \in (0, 2^{-20}]$, and external pools
$S_i, D_i \subseteq \bigcup_{j \neq i} B_j$ with $|N_F(u) \cap M_i| < 2^{-20} |M_i|$ for all $u \in S_i$
and $|M_i \setminus N_F(u)| < 2^{-20} |M_i|$ for all $u \in D_i$, either:
1. **(Stops for Both Pools)**: there exists $M'_i \subseteq M_i$ of size $|M'_i| > \frac{7}{8} |M_i|$
   such that $|N_F(u) \cap M'_i| \le \tau |M_i|$ for all $u \in S_i$ and
   $|M'_i \setminus N_F(u)| \le \tau |M_i|$ for all $u \in D_i$; or
2. **(Per-Handle $(s+1)$-Stem Promotion)**: there exist $k_{\mathrm{comb}} \in (512, \tau^{-1})$ ($k_{\mathrm{comb}} > 64$),
   handles $u : \text{Fin } k_{\mathrm{comb}} \to V$ in $\bigcup_{j \neq i} B_j$, teeth
   $B' : \text{Fin } k_{\mathrm{comb}} \to \text{Finset } V$ in $M_i$, and per-handle $(s+1)$-stems `stems'`
   forming an $(k_{\mathrm{comb}}, \max(\frac{|M_i|}{16 k_{\mathrm{comb}}^2}, \frac{\tau}{2} |M_i|))$-comb or co-comb in $F$ inside $S$. -/
theorem union_pool_stem_promotion {F : SimpleGraph V} {S : Finset V}
    {ℓ s : ℕ} {w τ : ℝ} {a : Fin ℓ → V} {B : Fin ℓ → Finset V}
    {stems : Fin ℓ → Fin s → V} {i : Fin ℓ} {M_i S_i D_i : Finset V}
    (hcomb : IsCombOrCoCombIn F S ℓ w a B)
    (hstems : HasPerHandleApexStems F S ℓ s a B stems)
    (hMi_sub : M_i ⊆ B i) (hMi_ne : M_i.Nonempty)
    (hτ_pos : 0 < τ) (hτ_ub : τ ≤ (2 : ℝ)⁻¹ ^ 20)
    (hSi_sub : S_i ⊆ (Finset.univ.erase i).biUnion B)
    (hDi_sub : D_i ⊆ (Finset.univ.erase i).biUnion B)
    (hSi_deg : ∀ u ∈ S_i, ((neighborFinsetIn F u M_i).card : ℝ) < (2 : ℝ)⁻¹ ^ 20 * (M_i.card : ℝ))
    (hDi_deg : ∀ u ∈ D_i, ((M_i \ neighborFinsetIn F u M_i).card : ℝ) < (2 : ℝ)⁻¹ ^ 20 * (M_i.card : ℝ)) :
    (∃ M_i' ⊆ M_i, (7 / 8 : ℝ) * (M_i.card : ℝ) < (M_i'.card : ℝ) ∧
      (∀ u ∈ S_i, ((neighborFinsetIn F u M_i').card : ℝ) ≤ τ * (M_i.card : ℝ)) ∧
      (∀ u ∈ D_i, ((M_i' \ neighborFinsetIn F u M_i').card : ℝ) ≤ τ * (M_i.card : ℝ))) ∨
    (∃ (k_comb : ℕ) (u : Fin k_comb → V) (B' : Fin k_comb → Finset V)
       (stems' : Fin k_comb → Fin (s + 1) → V),
      512 < k_comb ∧ (k_comb : ℝ) < τ⁻¹ ∧
      (∀ q : Fin k_comb, B' q ⊆ M_i) ∧
      IsCombOrCoCombIn F S k_comb
        (max ((M_i.card : ℝ) / (16 * (k_comb : ℝ) ^ 2)) ((τ / 2) * (M_i.card : ℝ))) u B' ∧
      HasPerHandleApexStems F S k_comb (s + 1) u B' stems') := by
  have hB_block : IsBlockadeIn F S ℓ w B := by
    rcases hcomb with hc | hco
    · exact hc.is_blockade
    · exact hco.is_blockade
  have hMi_S : M_i ⊆ S := hMi_sub.trans (hB_block.subset_ambient i)
  have h_other_S : (Finset.univ.erase i).biUnion B ⊆ S :=
    Finset.biUnion_subset.mpr (fun j _ => hB_block.subset_ambient j)
  have h_other_disj : Disjoint ((Finset.univ.erase i).biUnion B) M_i := by
    rw [Finset.disjoint_biUnion_left]
    intro j hj
    exact Finset.disjoint_of_subset_right hMi_sub
      (hB_block.pairwise_disjoint j i (Finset.mem_erase.mp hj).1)
  have hSi_S : S_i ⊆ S := hSi_sub.trans h_other_S
  have hDi_S : D_i ⊆ S := hDi_sub.trans h_other_S
  have hSi_disj : Disjoint S_i M_i := Finset.disjoint_of_subset_left hSi_sub h_other_disj
  have hDi_disj : Disjoint D_i M_i := Finset.disjoint_of_subset_left hDi_sub h_other_disj
  have hMi_pos : 0 < M_i.card := Finset.card_pos.mpr hMi_ne
  have hMi_r_pos : (0 : ℝ) < (M_i.card : ℝ) := Nat.cast_pos.mpr hMi_pos
  -- Step (a): Apply greedy_pool_comb_extraction to (F, S_i, M_i) at α = 1 / 16
  rcases greedy_pool_comb_extraction F S M_i M_i S_i τ (1 / 16)
      Finset.Subset.rfl hMi_S hSi_S hSi_disj hMi_pos hτ_pos hτ_ub le_rfl (by linarith) hSi_deg with
    ⟨A_i_S, hAi_sub, hAi_card, hAi_deg⟩ | ⟨k_comb, u, B', hk_512, hk_lt, huB', h_subcomb⟩
  · -- Step (b): Apply greedy_pool_comb_extraction to (Fᶜ, D_i, A_i_S ⊆ M_i) at α = 1 / 16
    have hDi_deg_compl : ∀ u ∈ D_i,
        ((neighborFinsetIn Fᶜ u A_i_S).card : ℝ) < (2 : ℝ)⁻¹ ^ 20 * (M_i.card : ℝ) := by
      intro u hu
      have h_sub : neighborFinsetIn Fᶜ u A_i_S ⊆ M_i \ neighborFinsetIn F u M_i := by
        intro v hv
        obtain ⟨hvA, hadjc⟩ := (mem_neighborFinsetIn_iff Fᶜ u A_i_S v).mp hv
        exact Finset.mem_sdiff.mpr ⟨hAi_sub hvA,
          fun hadj => hadjc.2 ((mem_neighborFinsetIn_iff F u M_i v).mp hadj).2⟩
      exact lt_of_le_of_lt (Nat.cast_le.mpr (Finset.card_le_card h_sub)) (hDi_deg u hu)
    rcases greedy_pool_comb_extraction Fᶜ S M_i A_i_S D_i τ (1 / 16)
        hAi_sub hMi_S hDi_S hDi_disj hMi_pos hτ_pos hτ_ub le_rfl (by linarith) hDi_deg_compl with
      ⟨M_i', hMi'_Ai, hMi'_card, hMi'_deg_compl⟩ | ⟨k_comb, u, B', hk_512, hk_lt, huB', h_subcomb_c⟩
    · -- Both pools stopped!
      left
      refine ⟨M_i', hMi'_Ai.trans hAi_sub, by linarith, ?_, ?_⟩
      · intro u hu
        have h_sub : neighborFinsetIn F u M_i' ⊆ neighborFinsetIn F u A_i_S :=
          neighborFinsetIn_mono F u hMi'_Ai
        exact le_trans (Nat.cast_le.mpr (Finset.card_le_card h_sub)) (hAi_deg u hu)
      · intro u hu
        have h_eq : M_i' \ neighborFinsetIn F u M_i' = neighborFinsetIn Fᶜ u M_i' := by
          ext v
          simp only [Finset.mem_sdiff, mem_neighborFinsetIn_iff, compl_adj]
          constructor
          · rintro ⟨hv, hn⟩
            have hne : u ≠ v := fun h => Finset.disjoint_left.mp hDi_disj hu (h ▸ hMi'_Ai.trans hAi_sub hv)
            exact ⟨hv, hne, fun hadj => hn ⟨hv, hadj⟩⟩
          · rintro ⟨hv, _, hn⟩
            exact ⟨hv, fun ⟨_, hadj⟩ => hn hadj⟩
        rw [h_eq]
        exact hMi'_deg_compl u hu
    · -- Pool D_i promoted to a co-comb!
      right
      have h_mem_other : ∀ q : Fin k_comb, ∃ j ∈ Finset.univ.erase i, u q ∈ B j :=
        fun q => Finset.mem_biUnion.mp (hDi_sub (huB' q).1)
      let j_idx : Fin k_comb → Fin ℓ := fun q => Classical.choose (h_mem_other q)
      have hj_spec : ∀ q : Fin k_comb, j_idx q ≠ i ∧ u q ∈ B (j_idx q) := by
        intro q
        have h := Classical.choose_spec (h_mem_other q)
        exact ⟨(Finset.mem_erase.mp h.1).1, h.2⟩
      obtain ⟨stems', hstems'⟩ := hasPerHandleApexStems_succ_of_union_pool hcomb hstems
        j_idx (fun q => (hj_spec q).1) (fun q => (hj_spec q).2)
        (fun q => ((huB' q).2.trans hAi_sub).trans hMi_sub)
      exact ⟨k_comb, u, B', stems', hk_512, hk_lt, fun q => (huB' q).2.trans hAi_sub,
        Or.inr (isCoCombIn_of_isCombIn_compl h_subcomb_c), hstems'⟩
  · -- Pool S_i promoted to a comb!
    right
    have h_mem_other : ∀ q : Fin k_comb, ∃ j ∈ Finset.univ.erase i, u q ∈ B j :=
      fun q => Finset.mem_biUnion.mp (hSi_sub (huB' q).1)
    let j_idx : Fin k_comb → Fin ℓ := fun q => Classical.choose (h_mem_other q)
    have hj_spec : ∀ q : Fin k_comb, j_idx q ≠ i ∧ u q ∈ B (j_idx q) := by
      intro q
      have h := Classical.choose_spec (h_mem_other q)
      exact ⟨(Finset.mem_erase.mp h.1).1, h.2⟩
    obtain ⟨stems', hstems'⟩ := hasPerHandleApexStems_succ_of_union_pool hcomb hstems
      j_idx (fun q => (hj_spec q).1) (fun q => (hj_spec q).2)
      (fun q => (huB' q).2.trans hMi_sub)
    exact ⟨k_comb, u, B', stems', hk_512, hk_lt, fun q => (huB' q).2,
      Or.inl h_subcomb, hstems'⟩

/-- **Stem Extension for Lemma 10(2)**: Extending per-handle $s$-stems of $((a_r, B_r) : r \in [\ell])$
and a depth-$d$ cutter chain $z_0, \dots, z_{d-1}$ ($d \ge 1$) to a shared $(s + 1 + d)$-vertex stem
$\mathbf{v}'' = (\hat{v}_1^{(i,j)}, \dots, \hat{v}_s^{(i,j)}, \hat{a}_{i,j}, z_0, \dots, z_{d-1})$
for an internal sub-comb or sub-co-comb with handles in $M_{d-1} \setminus N_F(z_{d-1})$ and teeth in $M_d$. -/
theorem hasPerHandleApexStems_of_internal_depth_d {F : SimpleGraph V} {S : Finset V}
    {ℓ s d k_comb : ℕ} {w : ℝ} {a : Fin ℓ → V} {B : Fin ℓ → Finset V}
    {stems : Fin ℓ → Fin s → V} {i j : Fin ℓ}
    (hij : i ≠ j) (hd : 1 ≤ d)
    (hcomb : IsCombOrCoCombIn F S ℓ w a B)
    (hstems : HasPerHandleApexStems F S ℓ s a B stems)
    (z : Fin d → V) (M : Fin (d + 1) → Finset V)
    (hz0 : z ⟨0, hd⟩ ∈ B j) (hM0 : M 0 ⊆ B i)
    (hM_step : ∀ c : Fin d, M c.succ ⊆ neighborFinsetIn F (z c) (M c.castSucc))
    (hz_step : ∀ c : Fin d, ∀ hc1 : 1 ≤ c.1,
      z c ∈ M ⟨c.1 - 1, by omega⟩ ∧ ¬F.Adj (z ⟨c.1 - 1, by omega⟩) (z c))
    {u : Fin k_comb → V} {N' : Fin k_comb → Finset V}
    (hu_in : ∀ q : Fin k_comb, u q ∈ M ⟨d - 1, by omega⟩ ∧ ¬F.Adj (z ⟨d - 1, by omega⟩) (u q))
    (hN'_sub : ∀ q : Fin k_comb, N' q ⊆ M (Fin.last d)) :
    ∃ stems'' : Fin k_comb → Fin (s + 1 + d) → V,
      HasPerHandleApexStems F S k_comb (s + 1 + d) u N' stems'' := by
  obtain ⟨hunif, _, _⟩ := isUnifiedHandleStemPair_of_combOrCoComb hcomb hstems hij
  set v_hat := unifiedStem F S w a B stems i j
  set a_hat := unifiedHandle F S w a B i j
  have hM_sub : ∀ c : Fin d, M c.succ ⊆ M c.castSucc :=
    fun c => (hM_step c).trans (neighborFinsetIn_subset F _ _)
  have hM_anti : Antitone M := module_chain_antitone hM_sub
  have hM_sub_Bi : ∀ c : Fin (d + 1), M c ⊆ B i :=
    fun c => (hM_anti (Fin.zero_le c)).trans hM0
  let v_shared : Fin (s + 1 + d) → V := fun p =>
    if hps : p.1 < s then v_hat ⟨p.1, hps⟩
    else if p.1 = s then a_hat
    else z ⟨p.1 - (s + 1), by omega⟩
  have hv_v : ∀ p : Fin (s + 1 + d), ∀ hps : p.1 < s, v_shared p = v_hat ⟨p.1, hps⟩ := by
    intro p hps; dsimp [v_shared]; rw [dif_pos hps]
  have hv_a : ∀ p : Fin (s + 1 + d), p.1 = s → v_shared p = a_hat := by
    intro p hps; dsimp [v_shared]; rw [dif_neg (by omega), if_pos hps]
  have hv_z : ∀ p : Fin (s + 1 + d), s + 1 ≤ p.1 → v_shared p = z ⟨p.1 - (s + 1), by omega⟩ := by
    intro p hp; dsimp [v_shared]; rw [dif_neg (by omega), if_neg (by omega)]
  -- Every z c with 1 ≤ c.1 lies in M ⟨c.1 - 1, _⟩ ⊆ B i
  have hz_in_Bi : ∀ c : Fin d, 1 ≤ c.1 → z c ∈ B i := by
    intro c hc1
    exact hM_sub_Bi ⟨c.1 - 1, by omega⟩ (hz_step c hc1).1
  -- For any c : Fin d and c' : Fin d with c.1 + 2 ≤ c'.1, z c' ∈ M c.succ
  have hz_in_M_succ : ∀ c c' : Fin d, c.1 + 2 ≤ c'.1 → z c' ∈ M c.succ := by
    intro c c' hcc'
    have hc'_1 : 1 ≤ c'.1 := by omega
    have hle : c.succ ≤ (⟨c'.1 - 1, by omega⟩ : Fin (d + 1)) := by
      simp only [Fin.le_def, Fin.val_succ]; omega
    exact hM_anti hle (hz_step c' hc'_1).1
  -- Consecutive non-adjacency and non-consecutive adjacency on v_shared
  have h_consec : ∀ p q : Fin (s + 1 + d), p.1 + 1 = q.1 →
      v_shared p ≠ v_shared q ∧ ¬F.Adj (v_shared p) (v_shared q) := by
    intro p q hpq
    by_cases hp_lt_s1 : p.1 + 1 < s
    · have hp_s : p.1 < s := by omega
      have hq_s : q.1 < s := by omega
      rw [hv_v p hp_s, hv_v q hq_s]
      have hpq_path : (pathGraph s).Adj ⟨p.1, hp_s⟩ ⟨q.1, hq_s⟩ := by rw [pathGraph_adj]; left; exact hpq
      have hadjc := (hunif.stem_induced_path_compl ⟨p.1, hp_s⟩ ⟨q.1, hq_s⟩).mpr hpq_path
      exact ⟨hadjc.1, hadjc.2⟩
    · by_cases hp_eq_s1 : p.1 + 1 = s
      · have hp_s : p.1 < s := by omega
        rw [hv_v p hp_s, hv_a q (by omega)]
        exact ⟨hunif.stem_not_handle ⟨p.1, hp_s⟩,
          hunif.stem_last_nonadj_handle ⟨p.1, hp_s⟩ hp_eq_s1⟩
      · by_cases hp_eq_s : p.1 = s
        · rw [hv_a p hp_eq_s, hv_z q (by omega)]
          have h0 : (⟨q.1 - (s + 1), by omega⟩ : Fin d) = ⟨0, hd⟩ := by ext; dsimp; omega
          rw [h0]
          exact ⟨fun h => hunif.handle_not_in_Bj (h ▸ hz0), hunif.handle_anticomplete_Bj _ hz0⟩
        · rw [hv_z p (by omega), hv_z q (by omega)]
          let c : Fin d := ⟨q.1 - (s + 1), by omega⟩
          have hc1 : 1 ≤ c.1 := by dsimp [c]; omega
          have hp_c : (⟨p.1 - (s + 1), by omega⟩ : Fin d) = ⟨c.1 - 1, by omega⟩ := by
            ext; dsimp [c]; omega
          have hq_c : (⟨q.1 - (s + 1), by omega⟩ : Fin d) = c := rfl
          rw [hp_c, hq_c]
          refine ⟨?_, (hz_step c hc1).2⟩
          by_cases hc1_eq : c.1 = 1
          · have hc0 : (⟨c.1 - 1, by omega⟩ : Fin d) = ⟨0, hd⟩ := by ext; dsimp; omega
            rw [hc0]
            exact fun h => Finset.disjoint_right.mp hunif.blocks_disjoint hz0 (h ▸ hz_in_Bi c hc1)
          · let c_prev : Fin d := ⟨c.1 - 2, by omega⟩
            have hc_prev_nadj : ¬F.Adj (z c_prev) (z ⟨c.1 - 1, by omega⟩) := by
              have h_eq : (⟨(⟨c.1 - 1, by omega⟩ : Fin d).1 - 1, by omega⟩ : Fin d) = c_prev := by
                ext; dsimp [c_prev]; omega
              have h_st := (hz_step ⟨c.1 - 1, by omega⟩ (by dsimp; omega)).2
              rwa [h_eq] at h_st
            have hc_in : z c ∈ M c_prev.succ := hz_in_M_succ c_prev c (by dsimp [c_prev]; omega)
            have hc_adj : F.Adj (z c_prev) (z c) :=
              ((mem_neighborFinsetIn_iff F _ _ _).mp (hM_step c_prev hc_in)).2
            exact fun h => hc_prev_nadj (h ▸ hc_adj)
  have h_nonconsec : ∀ p q : Fin (s + 1 + d), p.1 + 1 < q.1 →
      F.Adj (v_shared p) (v_shared q) := by
    intro p q hpq
    by_cases hp_s : p.1 < s
    · rw [hv_v p hp_s]
      by_cases hq_s : q.1 < s
      · rw [hv_v q hq_s]
        have hp_ne_q : (⟨p.1, hp_s⟩ : Fin s) ≠ ⟨q.1, hq_s⟩ := by
          intro h; have := Fin.mk.inj_iff.mp h; omega
        have h_not_path : ¬(pathGraph s).Adj ⟨p.1, hp_s⟩ ⟨q.1, hq_s⟩ := by
          rw [pathGraph_adj]; dsimp; omega
        have h_not_compl := mt (hunif.stem_induced_path_compl ⟨p.1, hp_s⟩ ⟨q.1, hq_s⟩).mp h_not_path
        have hv_ne := hunif.stem_injective.ne hp_ne_q
        exact Decidable.byContradiction (fun hn => h_not_compl ⟨hv_ne, hn⟩)
      · by_cases hq_eq_s : q.1 = s
        · rw [hv_a q hq_eq_s]
          exact hunif.stem_init_adj_handle ⟨p.1, hp_s⟩ (by dsimp; omega)
        · rw [hv_z q (by omega)]
          by_cases hq_s1 : q.1 = s + 1
          · have h0 : (⟨q.1 - (s + 1), by omega⟩ : Fin d) = ⟨0, hd⟩ := by ext; dsimp; omega
            rw [h0]
            exact hunif.stem_complete_Bj ⟨p.1, hp_s⟩ _ hz0
          · exact hunif.stem_complete_Bi ⟨p.1, hp_s⟩ _ (hz_in_Bi _ (by dsimp; omega))
    · by_cases hp_eq_s : p.1 = s
      · rw [hv_a p hp_eq_s, hv_z q (by omega)]
        exact hunif.handle_complete_Bi _ (hz_in_Bi _ (by dsimp; omega))
      · rw [hv_z p (by omega), hv_z q (by omega)]
        let c : Fin d := ⟨p.1 - (s + 1), by omega⟩
        let c' : Fin d := ⟨q.1 - (s + 1), by omega⟩
        have hc_in : z c' ∈ M c.succ := hz_in_M_succ c c' (by dsimp [c, c']; omega)
        exact ((mem_neighborFinsetIn_iff F _ _ _).mp (hM_step c hc_in)).2
  have hv_inj : Function.Injective v_shared := by
    intro p q hpq
    rcases lt_trichotomy p.1 q.1 with hlt | heq | hgt
    · by_cases h1 : p.1 + 1 = q.1
      · exact False.elim ((h_consec p q h1).1 hpq)
      · exact False.elim (F.ne_of_adj (h_nonconsec p q (by omega)) hpq)
    · exact Fin.ext heq
    · by_cases h1 : q.1 + 1 = p.1
      · exact False.elim ((h_consec q p h1).1 hpq.symm)
      · exact False.elim (F.ne_of_adj (h_nonconsec q p (by omega)) hpq.symm)
  -- Check F.Adj (v_shared p) (u q) for p.1 + 1 < s + 1 + d
  have hv_init_adj_u : ∀ (q : Fin k_comb) (p : Fin (s + 1 + d)),
      p.1 + 1 < s + 1 + d → F.Adj (v_shared p) (u q) := by
    intro q p hp_lt
    have hu_Bi : u q ∈ B i := hM_sub_Bi ⟨d - 1, by omega⟩ (hu_in q).1
    by_cases hp_s : p.1 < s
    · rw [hv_v p hp_s]; exact hunif.stem_complete_Bi ⟨p.1, hp_s⟩ (u q) hu_Bi
    · by_cases hp_eq_s : p.1 = s
      · rw [hv_a p hp_eq_s]; exact hunif.handle_complete_Bi (u q) hu_Bi
      · rw [hv_z p (by omega)]
        let c : Fin d := ⟨p.1 - (s + 1), by omega⟩
        have hc_le : c.succ ≤ (⟨d - 1, by omega⟩ : Fin (d + 1)) := by
          simp only [Fin.le_def, Fin.val_succ]; dsimp [c]; omega
        have hu_in_Mc : u q ∈ M c.succ := hM_anti hc_le (hu_in q).1
        exact ((mem_neighborFinsetIn_iff F _ _ _).mp (hM_step c hu_in_Mc)).2
  -- Check F.Adj (v_shared p) x for all x ∈ N' q₂ ⊆ M (Fin.last d)
  have hv_comp_Md : ∀ (p : Fin (s + 1 + d)) (x : V), x ∈ M (Fin.last d) → F.Adj (v_shared p) x := by
    intro p x hx
    have hx_Bi : x ∈ B i := hM_sub_Bi (Fin.last d) hx
    by_cases hp_s : p.1 < s
    · rw [hv_v p hp_s]; exact hunif.stem_complete_Bi ⟨p.1, hp_s⟩ x hx_Bi
    · by_cases hp_eq_s : p.1 = s
      · rw [hv_a p hp_eq_s]; exact hunif.handle_complete_Bi x hx_Bi
      · rw [hv_z p (by omega)]
        let c : Fin d := ⟨p.1 - (s + 1), by omega⟩
        have hc_le : c.succ ≤ Fin.last d := Fin.le_last _
        have hx_in_Mc : x ∈ M c.succ := hM_anti hc_le hx
        exact ((mem_neighborFinsetIn_iff F _ _ _).mp (hM_step c hx_in_Mc)).2
  refine ⟨fun _ => v_shared, ?_⟩
  refine
    { stem_pos := by omega
      stem_in_ambient := ?_
      stem_injective := fun _ => hv_inj
      stem_not_handle := ?_
      stem_not_in_blocks := ?_
      stem_induced_path_compl := ?_
      stem_last_nonadj_handle := ?_
      stem_init_adj_handle := hv_init_adj_u
      stem_complete_to_blocks := fun _ q₂ p x hx => hv_comp_Md p x (hN'_sub q₂ hx) }
  · intro _ p
    by_cases hp_s : p.1 < s
    · rw [hv_v p hp_s]; exact hunif.stem_in_ambient ⟨p.1, hp_s⟩
    · by_cases hp_eq_s : p.1 = s
      · rw [hv_a p hp_eq_s]; exact hunif.handle_in_ambient
      · rw [hv_z p (by omega)]
        let c : Fin d := ⟨p.1 - (s + 1), by omega⟩
        change z c ∈ S
        by_cases hc0 : c.1 = 0
        · have hc_eq : c = ⟨0, hd⟩ := by ext; exact hc0
          rw [hc_eq]; exact hunif.Bj_sub hz0
        · exact hunif.Bi_sub (hz_in_Bi c (by omega))
  · intro _ q p h_eq
    by_cases hp_last : p.1 + 1 = s + 1 + d
    · rw [hv_z p (by omega)] at h_eq
      have hc_last : (⟨p.1 - (s + 1), by omega⟩ : Fin d) = ⟨d - 1, by omega⟩ := by
        ext; dsimp; omega
      rw [hc_last] at h_eq
      rcases Nat.eq_or_lt_of_le hd with rfl | hd2
      · have hu_Bi : u q ∈ B i := hM_sub_Bi ⟨0, by omega⟩ (hu_in q).1
        exact Finset.disjoint_right.mp hunif.blocks_disjoint hz0 (h_eq ▸ hu_Bi)
      · let c_prev : Fin d := ⟨d - 2, by omega⟩
        have hz_nadj : ¬F.Adj (z c_prev) (z ⟨d - 1, by omega⟩) := by
          have h_eq' : (⟨(⟨d - 1, by omega⟩ : Fin d).1 - 1, by omega⟩ : Fin d) = c_prev := by
            ext; dsimp [c_prev]; omega
          have h_st := (hz_step ⟨d - 1, by omega⟩ (by dsimp; omega)).2
          rwa [h_eq'] at h_st
        have hu_in_Mc : u q ∈ M c_prev.succ := by
          have hc_eq : c_prev.succ = (⟨d - 1, by omega⟩ : Fin (d + 1)) := by
            ext; dsimp [c_prev]; omega
          rw [hc_eq]; exact (hu_in q).1
        have hu_adj : F.Adj (z c_prev) (u q) :=
          ((mem_neighborFinsetIn_iff F _ _ _).mp (hM_step c_prev hu_in_Mc)).2
        exact hz_nadj (h_eq ▸ hu_adj)
    · exact F.ne_of_adj (hv_init_adj_u q p (by omega)) h_eq
  · intro _ q₂ p h_in
    exact F.loopless (v_shared p) (hv_comp_Md p (v_shared p) (hN'_sub q₂ h_in))
  · intro _ p₁ p₂
    have h_lt : ∀ a b : Fin (s + 1 + d), a.1 < b.1 →
        (Fᶜ.Adj (v_shared a) (v_shared b) ↔ (pathGraph (s + 1 + d)).Adj a b) := by
      intro a b hab
      have ha_ne_b : a ≠ b := fun h => by rw [h] at hab; omega
      have h_vne : v_shared a ≠ v_shared b := hv_inj.ne ha_ne_b
      simp only [compl_adj, pathGraph_adj]
      have h_not_rev : ¬(b.1 + 1 = a.1) := by omega
      by_cases h1 : a.1 + 1 = b.1
      · simp [h_vne, h1, (h_consec a b h1).2]
      · simp [h_vne, h1, h_not_rev, h_nonconsec a b (by omega)]
    rcases lt_trichotomy p₁.1 p₂.1 with h1 | heq | h2
    · exact h_lt p₁ p₂ h1
    · have hp₁₂ : p₁ = p₂ := Fin.ext heq; subst hp₁₂; simp
    · rw [Fᶜ.adj_comm, (pathGraph (s + 1 + d)).adj_comm]
      exact h_lt p₂ p₁ h2
  · intro q p hp_last
    rw [hv_z p (by omega)]
    have hc_last : (⟨p.1 - (s + 1), by omega⟩ : Fin d) = ⟨d - 1, by omega⟩ := by
      ext; dsimp; omega
    rw [hc_last]
    exact (hu_in q).2

/-- **Lemma 10(2) (`internal_depth_d_stem_promotion`, Internal Depth-$d$ $(s+1+d)$-Vertex Apex-Stem Promotion)**:
For $d \ge 1$, distinct $i, j \in \text{Fin } \ell$, depth-$d$ cutter chain $z_0, \dots, z_{d-1}$ and
subsets $M_0, \dots, M_d$ ($M_d \neq \emptyset$), a pool $A \subseteq M_{d-1} \setminus N_F(z_{d-1})$
such that either (Sparse Pool) $|N_F(z) \cap M_d| < 2^{-20} |M_d|$ for all $z \in A$, or
(Co-Sparse Pool) $|M_d \setminus N_F(z)| < 2^{-20} |M_d|$ for all $z \in A$, and $\tau \in (0, 2^{-20}]$,
either:
1. **(Stops Early with Residual $R_{\mathrm{end}} \subseteq M_d$)**: $|R_{\mathrm{end}}| > \frac{1}{2} |M_d|$
   and $A$ is one-sided $2\tau$-sparse (resp. $2\tau$-co-sparse) to $R_{\mathrm{end}}$ in $F$
   (hence $(R_{\mathrm{end}}, A)$ is weakly $2\tau$-sparse-or-co-sparse in $F$); or
2. **(Internal $(s+1+d)$-Stem Promotion)**: there exist $k_{\mathrm{comb}} \in (512, \tau^{-1})$ ($k_{\mathrm{comb}} > 64$),
   handles $u : \text{Fin } k_{\mathrm{comb}} \to V$ in $A$, teeth $N' : \text{Fin } k_{\mathrm{comb}} \to \text{Finset } V$
   in $M_d$, and a shared $(s + 1 + d)$-stem forming an
   $(k_{\mathrm{comb}}, \max(\frac{|M_d|}{16 k_{\mathrm{comb}}^2}, \frac{\tau}{2} |M_d|))$-comb or co-comb in $F$ inside $S$. -/
theorem internal_depth_d_stem_promotion {F : SimpleGraph V} {S : Finset V}
    {ℓ s d : ℕ} {w τ : ℝ} {a : Fin ℓ → V} {B : Fin ℓ → Finset V}
    {stems : Fin ℓ → Fin s → V} {i j : Fin ℓ}
    (hij : i ≠ j) (hd : 1 ≤ d)
    (hcomb : IsCombOrCoCombIn F S ℓ w a B)
    (hstems : HasPerHandleApexStems F S ℓ s a B stems)
    (z : Fin d → V) (M : Fin (d + 1) → Finset V)
    (hz0 : z ⟨0, hd⟩ ∈ B j) (hM0 : M 0 ⊆ B i)
    (hM_step : ∀ c : Fin d, M c.succ ⊆ neighborFinsetIn F (z c) (M c.castSucc))
    (hz_step : ∀ c : Fin d, ∀ hc1 : 1 ≤ c.1,
      z c ∈ M ⟨c.1 - 1, by omega⟩ ∧ ¬F.Adj (z ⟨c.1 - 1, by omega⟩) (z c))
    (hMd_ne : (M (Fin.last d)).Nonempty)
    {A : Finset V}
    (hA_in : ∀ v ∈ A, v ∈ M ⟨d - 1, by omega⟩ ∧ ¬F.Adj (z ⟨d - 1, by omega⟩) v)
    (hτ_pos : 0 < τ) (hτ_ub : τ ≤ (2 : ℝ)⁻¹ ^ 20)
    (hA_pool :
      (∀ v ∈ A, ((neighborFinsetIn F v (M (Fin.last d))).card : ℝ) <
        (2 : ℝ)⁻¹ ^ 20 * ((M (Fin.last d)).card : ℝ)) ∨
      (∀ v ∈ A, (((M (Fin.last d)) \ neighborFinsetIn F v (M (Fin.last d))).card : ℝ) <
        (2 : ℝ)⁻¹ ^ 20 * ((M (Fin.last d)).card : ℝ))) :
    (∃ R_end ⊆ M (Fin.last d),
      ((M (Fin.last d)).card : ℝ) / 2 < (R_end.card : ℝ) ∧
      Disjoint R_end A ∧
      IsWeaklySparseOrCoSparsePair F R_end A (2 * τ)) ∨
    (∃ (k_comb : ℕ) (u : Fin k_comb → V) (N' : Fin k_comb → Finset V)
       (stems'' : Fin k_comb → Fin (s + 1 + d) → V),
      512 < k_comb ∧ (k_comb : ℝ) < τ⁻¹ ∧
      (∀ q : Fin k_comb, N' q ⊆ M (Fin.last d)) ∧
      IsCombOrCoCombIn F S k_comb
        (max (((M (Fin.last d)).card : ℝ) / (16 * (k_comb : ℝ) ^ 2))
          ((τ / 2) * ((M (Fin.last d)).card : ℝ))) u N' ∧
      HasPerHandleApexStems F S k_comb (s + 1 + d) u N' stems'') := by
  have hB_block : IsBlockadeIn F S ℓ w B := by
    rcases hcomb with hc | hco
    · exact hc.is_blockade
    · exact hco.is_blockade
  have hM_sub : ∀ c : Fin d, M c.succ ⊆ M c.castSucc :=
    fun c => (hM_step c).trans (neighborFinsetIn_subset F _ _)
  have hM_anti : Antitone M := module_chain_antitone hM_sub
  have hM_sub_Bi : ∀ c : Fin (d + 1), M c ⊆ B i :=
    fun c => (hM_anti (Fin.zero_le c)).trans hM0
  set M_d := M (Fin.last d)
  have hMd_S : M_d ⊆ S := (hM_sub_Bi (Fin.last d)).trans (hB_block.subset_ambient i)
  have hA_S : A ⊆ S := by
    intro v hv
    exact (hB_block.subset_ambient i) (hM_sub_Bi ⟨d - 1, by omega⟩ (hA_in v hv).1)
  have hAMd_disj : Disjoint A M_d := by
    rw [Finset.disjoint_left]
    intro v hvA hvMd
    have hc_last : (⟨d - 1, by omega⟩ : Fin d).succ = Fin.last d := by ext; dsimp; omega
    have hv_in_Z : v ∈ neighborFinsetIn F (z ⟨d - 1, by omega⟩) (M ⟨d - 1, by omega⟩) := by
      have : M_d ⊆ neighborFinsetIn F (z ⟨d - 1, by omega⟩) (M ⟨d - 1, by omega⟩) := by
        unfold M_d; rw [← hc_last]; exact hM_step ⟨d - 1, by omega⟩
      exact this hvMd
    exact (hA_in v hvA).2 ((mem_neighborFinsetIn_iff F _ _ v).mp hv_in_Z).2
  have hMd_pos : 0 < M_d.card := Finset.card_pos.mpr hMd_ne
  have hMd_r_pos : (0 : ℝ) < (M_d.card : ℝ) := Nat.cast_pos.mpr hMd_pos
  rcases hA_pool with hA_sparse | hA_cosparse
  · -- Sparse pool in F
    rcases greedy_pool_comb_extraction F S M_d M_d A τ (1 / 2)
        Finset.Subset.rfl hMd_S hA_S hAMd_disj hMd_pos hτ_pos hτ_ub (by norm_num) (by linarith) hA_sparse with
      ⟨R_end, hR_sub, hR_card, hR_deg⟩ | ⟨k_comb, u, N', hk_512, hk_lt, huN', h_subcomb⟩
    · left
      have hR_half : (M_d.card : ℝ) / 2 < (R_end.card : ℝ) := by linarith
      have hRA_disj : Disjoint R_end A := (Finset.disjoint_of_subset_right hR_sub hAMd_disj).symm
      have h_xsp : IsXSparseTo F A R_end (2 * τ) := by
        intro v hv
        calc ((neighborFinsetIn F v R_end).card : ℝ)
            ≤ τ * (M_d.card : ℝ) := hR_deg v hv
          _ ≤ τ * (2 * (R_end.card : ℝ)) := mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hτ_pos)
          _ = (2 * τ) * (R_end.card : ℝ) := by ring
      exact ⟨R_end, hR_sub, hR_half, hRA_disj,
        Or.inl (IsWeaklySparsePair.symm (crossEdgeCount_le_of_isXSparseTo F A R_end (2 * τ) h_xsp))⟩
    · right
      obtain ⟨stems'', hstems''⟩ := hasPerHandleApexStems_of_internal_depth_d hij hd hcomb hstems
        z M hz0 hM0 hM_step hz_step (fun q => hA_in (u q) (huN' q).1) (fun q => (huN' q).2)
      exact ⟨k_comb, u, N', stems'', hk_512, hk_lt, fun q => (huN' q).2, Or.inl h_subcomb, hstems''⟩
  · -- Co-sparse pool in F (sparse pool in Fᶜ)
    have hA_deg_compl : ∀ v ∈ A,
        ((neighborFinsetIn Fᶜ v M_d).card : ℝ) < (2 : ℝ)⁻¹ ^ 20 * (M_d.card : ℝ) := by
      intro v hv
      have h_sub : neighborFinsetIn Fᶜ v M_d ⊆ M_d \ neighborFinsetIn F v M_d := by
        intro x hx
        obtain ⟨hxM, hadjc⟩ := (mem_neighborFinsetIn_iff Fᶜ v M_d x).mp hx
        exact Finset.mem_sdiff.mpr ⟨hxM, fun h => hadjc.2 ((mem_neighborFinsetIn_iff F v M_d x).mp h).2⟩
      exact lt_of_le_of_lt (Nat.cast_le.mpr (Finset.card_le_card h_sub)) (hA_cosparse v hv)
    rcases greedy_pool_comb_extraction Fᶜ S M_d M_d A τ (1 / 2)
        Finset.Subset.rfl hMd_S hA_S hAMd_disj hMd_pos hτ_pos hτ_ub (by norm_num) (by linarith) hA_deg_compl with
      ⟨R_end, hR_sub, hR_card, hR_deg_compl⟩ | ⟨k_comb, u, N', hk_512, hk_lt, huN', h_subcomb_c⟩
    · left
      have hR_half : (M_d.card : ℝ) / 2 < (R_end.card : ℝ) := by linarith
      have hRA_disj : Disjoint R_end A := (Finset.disjoint_of_subset_right hR_sub hAMd_disj).symm
      have h_xsp_c : IsXSparseTo Fᶜ A R_end (2 * τ) := by
        intro v hv
        calc ((neighborFinsetIn Fᶜ v R_end).card : ℝ)
            ≤ τ * (M_d.card : ℝ) := hR_deg_compl v hv
          _ ≤ τ * (2 * (R_end.card : ℝ)) := mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hτ_pos)
          _ = (2 * τ) * (R_end.card : ℝ) := by ring
      exact ⟨R_end, hR_sub, hR_half, hRA_disj,
        Or.inr (IsWeaklySparsePair.symm (crossEdgeCount_le_of_isXSparseTo Fᶜ A R_end (2 * τ) h_xsp_c))⟩
    · right
      obtain ⟨stems'', hstems''⟩ := hasPerHandleApexStems_of_internal_depth_d hij hd hcomb hstems
        z M hz0 hM0 hM_step hz_step (fun q => hA_in (u q) (huN' q).1) (fun q => (huN' q).2)
      exact ⟨k_comb, u, N', stems'', hk_512, hk_lt, fun q => (huN' q).2,
        Or.inr (isCoCombIn_of_isCombIn_compl h_subcomb_c), hstems''⟩

/-!
## Section 8: Lemma 11 — Bipartite Double-Counting Dichotomy at Threshold $\frac{\eta_{\mathrm{out}}}{4\ell}$

Formalizes Lemma 11 (`main.tex` lines 555–566): if every block $M_j$ partitions into a low-degree
part $S_{j,i}$ ($|N_F(u) \cap M_i| \le \frac{\eta_{\mathrm{out}}}{4\ell}|M_i|$) and a high-degree
part $D_{j,i}$ ($|M_i \setminus N_F(u)| \le \frac{\eta_{\mathrm{out}}}{4\ell}|M_i|$), double-counting
the bipartite cross-edge set $E_F(D_{j,i}, S_{i,j})$ forces $\min\bigl(\frac{|D_{j,i}|}{|M_j|}, \frac{|S_{i,j}|}{|M_i|}\bigr) \le \frac{\eta_{\mathrm{out}}}{2\ell}$,
which implies that $(M_i, M_j)$ is weakly $\eta_{\mathrm{out}}$-sparse-or-co-sparse in $F$.
-/

/-- **Lemma 11 (`bipartite_double_counting_dichotomy`, Bipartite Double-Counting Dichotomy at Threshold $\frac{\eta_{\mathrm{out}}}{4\ell}$)**:
Let $0 < \eta_{\mathrm{out}} \le 2^{-16}$ and $\ell \ge 16$. Let $M : \text{Fin } \ell \to \text{Finset } V$
be an $(\ell, w_0)$-blockade in $F$ inside $S$. If for all distinct $i, j \in \text{Fin } \ell$,
every $u \in M_j$ satisfies either $|N_F(u) \cap M_i| \le \frac{\eta_{\mathrm{out}}}{4\ell} |M_i|$ or
$|M_i \setminus N_F(u)| \le \frac{\eta_{\mathrm{out}}}{4\ell} |M_i|$, then $M$ is a weakly
$\eta_{\mathrm{out}}$-sparse-or-co-sparse $(\ell, w_0)$-blockade in $F$ inside $S$. -/
theorem bipartite_double_counting_dichotomy {F : SimpleGraph V} {S : Finset V}
    {ℓ : ℕ} {w₀ η_out : ℝ} {M : Fin ℓ → Finset V}
    (hℓ : 16 ≤ ℓ) (hη_pos : 0 < η_out)
    (hblock : IsBlockadeIn F S ℓ w₀ M)
    (h_part : ∀ (i j : Fin ℓ), i ≠ j → ∀ u ∈ M j,
      ((neighborFinsetIn F u (M i)).card : ℝ) ≤ (η_out / (4 * (ℓ : ℝ))) * ((M i).card : ℝ) ∨
      (((M i) \ neighborFinsetIn F u (M i)).card : ℝ) ≤ (η_out / (4 * (ℓ : ℝ))) * ((M i).card : ℝ)) :
    IsWeaklySparseOrCoSparseBlockadeIn F S ℓ w₀ η_out M := by
  have hℓ_r : (16 : ℝ) ≤ (ℓ : ℝ) := Nat.ofNat_le_cast.mpr hℓ
  refine ⟨hblock, fun i j hij => ?_⟩
  set δ := η_out / (4 * (ℓ : ℝ))
  have hδ_pos : 0 < δ := by unfold δ; positivity
  let S_pair (a b : Fin ℓ) : Finset V :=
    (M a).filter (fun u => ((neighborFinsetIn F u (M b)).card : ℝ) ≤ δ * ((M b).card : ℝ))
  let D_pair (a b : Fin ℓ) : Finset V := M a \ S_pair a b
  have hS_sub : ∀ a b : Fin ℓ, S_pair a b ⊆ M a := fun _ _ => Finset.filter_subset _ _
  have hD_sub : ∀ a b : Fin ℓ, D_pair a b ⊆ M a := fun _ _ => Finset.sdiff_subset
  have hSD_disj : ∀ a b : Fin ℓ, Disjoint (S_pair a b) (D_pair a b) := fun _ _ => Finset.disjoint_sdiff
  have hSD_union : ∀ a b : Fin ℓ, S_pair a b ∪ D_pair a b = M a :=
    fun a b => Finset.union_sdiff_of_subset (hS_sub a b)
  have hSD_card : ∀ a b : Fin ℓ, ((S_pair a b).card : ℝ) + ((D_pair a b).card : ℝ) = ((M a).card : ℝ) := by
    intro a b
    have h_eq := Finset.card_sdiff_add_card_eq_card (hS_sub a b)
    change (D_pair a b).card + (S_pair a b).card = (M a).card at h_eq
    exact_mod_cast (by omega : (S_pair a b).card + (D_pair a b).card = (M a).card)
  have hD_deg : ∀ (a b : Fin ℓ), a ≠ b → ∀ u ∈ D_pair a b,
      (((M b) \ neighborFinsetIn F u (M b)).card : ℝ) ≤ δ * ((M b).card : ℝ) := by
    intro a b hab u hu
    obtain ⟨huM, hu_notS⟩ := Finset.mem_sdiff.mp hu
    rcases h_part b a hab.symm u huM with h1 | h2
    · exact False.elim (hu_notS (Finset.mem_filter.mpr ⟨huM, h1⟩))
    · exact h2
  -- Double-count E_F(D_{j,i}, S_{i,j})
  let D_ji := D_pair j i
  let S_ij := S_pair i j
  have h_upper : (crossEdgeCount F D_ji S_ij : ℝ) ≤ ((S_ij.card : ℝ) * δ) * ((M j).card : ℝ) := by
    rw [crossEdgeCount_comm]
    unfold crossEdgeCount; push_cast
    have h_each : ∀ w ∈ S_ij, ((neighborFinsetIn F w D_ji).card : ℝ) ≤ δ * ((M j).card : ℝ) := by
      intro w hw
      have h_sub : neighborFinsetIn F w D_ji ⊆ neighborFinsetIn F w (M j) :=
        neighborFinsetIn_mono F w (hD_sub j i)
      exact le_trans (Nat.cast_le.mpr (Finset.card_le_card h_sub)) (Finset.mem_filter.mp hw).2
    calc ∑ w ∈ S_ij, ((neighborFinsetIn F w D_ji).card : ℝ)
        ≤ ∑ _w ∈ S_ij, (δ * ((M j).card : ℝ)) := Finset.sum_le_sum h_each
      _ = ((S_ij.card : ℝ) * δ) * ((M j).card : ℝ) := by simp [Finset.sum_const, nsmul_eq_mul]; ring
  have h_lower : (D_ji.card : ℝ) * (S_ij.card : ℝ) - ((D_ji.card : ℝ) * δ) * ((M i).card : ℝ) ≤
      (crossEdgeCount F D_ji S_ij : ℝ) := by
    unfold crossEdgeCount; push_cast
    have h_each : ∀ u ∈ D_ji,
        (S_ij.card : ℝ) - δ * ((M i).card : ℝ) ≤ ((neighborFinsetIn F u S_ij).card : ℝ) := by
      intro u hu
      have h_part_u : (S_ij \ neighborFinsetIn F u S_ij).card + (neighborFinsetIn F u S_ij).card = S_ij.card :=
        Finset.card_sdiff_add_card_eq_card (neighborFinsetIn_subset F u S_ij)
      have h_sdiff_sub : S_ij \ neighborFinsetIn F u S_ij ⊆ (M i) \ neighborFinsetIn F u (M i) := by
        intro x hx
        obtain ⟨hxS, hx_not⟩ := Finset.mem_sdiff.mp hx
        exact Finset.mem_sdiff.mpr ⟨hS_sub i j hxS,
          fun h => hx_not ((mem_neighborFinsetIn_iff F u S_ij x).mpr
            ⟨hxS, ((mem_neighborFinsetIn_iff F u (M i) x).mp h).2⟩)⟩
      have h_sdiff_le : ((S_ij \ neighborFinsetIn F u S_ij).card : ℝ) ≤ δ * ((M i).card : ℝ) :=
        le_trans (Nat.cast_le.mpr (Finset.card_le_card h_sdiff_sub)) (hD_deg j i hij.symm u hu)
      have h_part_r : ((S_ij \ neighborFinsetIn F u S_ij).card : ℝ) +
          ((neighborFinsetIn F u S_ij).card : ℝ) = (S_ij.card : ℝ) := by exact_mod_cast h_part_u
      linarith
    calc (D_ji.card : ℝ) * (S_ij.card : ℝ) - ((D_ji.card : ℝ) * δ) * ((M i).card : ℝ)
        = ∑ _u ∈ D_ji, ((S_ij.card : ℝ) - δ * ((M i).card : ℝ)) := by
          simp [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ u ∈ D_ji, ((neighborFinsetIn F u S_ij).card : ℝ) := Finset.sum_le_sum h_each
  -- Deduce that either |D_{j,i}| ≤ 2 δ |M_j| or |S_{i,j}| ≤ 2 δ |M_i|
  have h_min_le : (D_ji.card : ℝ) ≤ 2 * δ * ((M j).card : ℝ) ∨
      (S_ij.card : ℝ) ≤ 2 * δ * ((M i).card : ℝ) := by
    by_contra! h_both
    obtain ⟨hD_gt, hS_gt⟩ := h_both
    have hD_pos : (0 : ℝ) < (D_ji.card : ℝ) := lt_of_le_of_lt (by positivity) hD_gt
    have hS_pos : (0 : ℝ) < (S_ij.card : ℝ) := lt_of_le_of_lt (by positivity) hS_gt
    have h1 := mul_lt_mul_of_pos_right hD_gt hS_pos
    have h2 := mul_lt_mul_of_pos_left hS_gt hD_pos
    nlinarith [h_upper, h_lower]
  rcases h_min_le with hD_small | hS_small
  · -- |D_{j,i}| ≤ 2 δ |M_j| → (M_i, M_j) is weakly η_out-sparse in F
    left
    apply IsWeaklySparsePair.symm
    unfold IsWeaklySparsePair
    have h_split_ce : crossEdgeCount F (M j) (M i) =
        crossEdgeCount F (S_pair j i) (M i) + crossEdgeCount F D_ji (M i) := by
      unfold crossEdgeCount
      rw [← Finset.sum_union (hSD_disj j i), hSD_union j i]
    have h_ce_S : (crossEdgeCount F (S_pair j i) (M i) : ℝ) ≤
        ((S_pair j i).card : ℝ) * (δ * ((M i).card : ℝ)) := by
      unfold crossEdgeCount; push_cast
      calc ∑ u ∈ S_pair j i, ((neighborFinsetIn F u (M i)).card : ℝ)
          ≤ ∑ _u ∈ S_pair j i, (δ * ((M i).card : ℝ)) :=
            Finset.sum_le_sum (fun u hu => (Finset.mem_filter.mp hu).2)
        _ = ((S_pair j i).card : ℝ) * (δ * ((M i).card : ℝ)) := by simp [Finset.sum_const, nsmul_eq_mul]
    have h_ce_D : (crossEdgeCount F D_ji (M i) : ℝ) ≤ (D_ji.card : ℝ) * ((M i).card : ℝ) := by
      unfold crossEdgeCount; push_cast
      calc ∑ u ∈ D_ji, ((neighborFinsetIn F u (M i)).card : ℝ)
          ≤ ∑ _u ∈ D_ji, ((M i).card : ℝ) :=
            Finset.sum_le_sum (fun u _ => Nat.cast_le.mpr (Finset.card_le_card (neighborFinsetIn_subset F u (M i))))
        _ = (D_ji.card : ℝ) * ((M i).card : ℝ) := by simp [Finset.sum_const, nsmul_eq_mul]
    have h_S_le_Mj : ((S_pair j i).card : ℝ) ≤ ((M j).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card (hS_sub j i))
    have h_3δ_le : 3 * δ ≤ η_out := by
      unfold δ
      rw [show 3 * (η_out / (4 * (ℓ : ℝ))) = η_out * (3 / (4 * (ℓ : ℝ))) by ring]
      have : 3 / (4 * (ℓ : ℝ)) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      nlinarith
    have h_split_r : (crossEdgeCount F (M j) (M i) : ℝ) =
        (crossEdgeCount F (S_pair j i) (M i) : ℝ) + (crossEdgeCount F D_ji (M i) : ℝ) := by
      exact_mod_cast h_split_ce
    calc (crossEdgeCount F (M j) (M i) : ℝ)
        ≤ ((S_pair j i).card : ℝ) * (δ * ((M i).card : ℝ)) + (D_ji.card : ℝ) * ((M i).card : ℝ) := by
          linarith
      _ ≤ ((M j).card : ℝ) * (δ * ((M i).card : ℝ)) + (2 * δ * ((M j).card : ℝ)) * ((M i).card : ℝ) := by
          refine add_le_add (mul_le_mul_of_nonneg_right h_S_le_Mj (by positivity))
            (mul_le_mul_of_nonneg_right hD_small (Nat.cast_nonneg _))
      _ = (3 * δ) * (((M j).card : ℝ) * ((M i).card : ℝ)) := by ring
      _ ≤ η_out * (((M j).card : ℝ) * ((M i).card : ℝ)) :=
          mul_le_mul_of_nonneg_right h_3δ_le (by positivity)
      _ = η_out * ((M j).card : ℝ) * ((M i).card : ℝ) := by ring
  · -- |S_{i,j}| ≤ 2 δ |M_i| → (M_i, M_j) is weakly η_out-co-sparse in F
    right
    unfold IsWeaklySparsePair
    have h_split_ce : crossEdgeCount Fᶜ (M i) (M j) =
        crossEdgeCount Fᶜ (D_pair i j) (M j) + crossEdgeCount Fᶜ S_ij (M j) := by
      unfold crossEdgeCount
      rw [← Finset.sum_union (hSD_disj i j).symm, Finset.union_comm, hSD_union i j]
    have h_ce_D : (crossEdgeCount Fᶜ (D_pair i j) (M j) : ℝ) ≤
        ((D_pair i j).card : ℝ) * (δ * ((M j).card : ℝ)) := by
      unfold crossEdgeCount; push_cast
      have h_each : ∀ u ∈ D_pair i j, ((neighborFinsetIn Fᶜ u (M j)).card : ℝ) ≤ δ * ((M j).card : ℝ) := by
        intro u hu
        have h_sub : neighborFinsetIn Fᶜ u (M j) ⊆ (M j) \ neighborFinsetIn F u (M j) := by
          intro v hv
          obtain ⟨hvM, hadjc⟩ := (mem_neighborFinsetIn_iff Fᶜ u (M j) v).mp hv
          exact Finset.mem_sdiff.mpr ⟨hvM, fun h => hadjc.2 ((mem_neighborFinsetIn_iff F u (M j) v).mp h).2⟩
        exact le_trans (Nat.cast_le.mpr (Finset.card_le_card h_sub)) (hD_deg i j hij u hu)
      calc ∑ u ∈ D_pair i j, ((neighborFinsetIn Fᶜ u (M j)).card : ℝ)
          ≤ ∑ _u ∈ D_pair i j, (δ * ((M j).card : ℝ)) := Finset.sum_le_sum h_each
        _ = ((D_pair i j).card : ℝ) * (δ * ((M j).card : ℝ)) := by simp [Finset.sum_const, nsmul_eq_mul]
    have h_ce_S : (crossEdgeCount Fᶜ S_ij (M j) : ℝ) ≤ (S_ij.card : ℝ) * ((M j).card : ℝ) := by
      unfold crossEdgeCount; push_cast
      calc ∑ u ∈ S_ij, ((neighborFinsetIn Fᶜ u (M j)).card : ℝ)
          ≤ ∑ _u ∈ S_ij, ((M j).card : ℝ) :=
            Finset.sum_le_sum (fun u _ => Nat.cast_le.mpr (Finset.card_le_card (neighborFinsetIn_subset Fᶜ u (M j))))
        _ = (S_ij.card : ℝ) * ((M j).card : ℝ) := by simp [Finset.sum_const, nsmul_eq_mul]
    have h_D_le_Mi : ((D_pair i j).card : ℝ) ≤ ((M i).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card (hD_sub i j))
    have h_3δ_le : 3 * δ ≤ η_out := by
      unfold δ
      rw [show 3 * (η_out / (4 * (ℓ : ℝ))) = η_out * (3 / (4 * (ℓ : ℝ))) by ring]
      have : 3 / (4 * (ℓ : ℝ)) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      nlinarith
    have h_split_r : (crossEdgeCount Fᶜ (M i) (M j) : ℝ) =
        (crossEdgeCount Fᶜ (D_pair i j) (M j) : ℝ) + (crossEdgeCount Fᶜ S_ij (M j) : ℝ) := by
      exact_mod_cast h_split_ce
    calc (crossEdgeCount Fᶜ (M i) (M j) : ℝ)
        ≤ ((D_pair i j).card : ℝ) * (δ * ((M j).card : ℝ)) + (S_ij.card : ℝ) * ((M j).card : ℝ) := by
          linarith
      _ ≤ ((M i).card : ℝ) * (δ * ((M j).card : ℝ)) + (2 * δ * ((M i).card : ℝ)) * ((M j).card : ℝ) := by
          refine add_le_add (mul_le_mul_of_nonneg_right h_D_le_Mi (by positivity))
            (mul_le_mul_of_nonneg_right hS_small (Nat.cast_nonneg _))
      _ = (3 * δ) * (((M i).card : ℝ) * ((M j).card : ℝ)) := by ring
      _ ≤ η_out * (((M i).card : ℝ) * ((M i).card : ℝ) * 0 + ((M i).card : ℝ) * ((M j).card : ℝ)) := by
          rw [mul_zero, zero_add]
          exact mul_le_mul_of_nonneg_right h_3δ_le (by positivity)
      _ = η_out * ((M i).card : ℝ) * ((M j).card : ℝ) := by ring

/-!
## Section 9: Proposition 1, Base Case $r = 1$, and Lemma 12 (`single_u_level2_core_dichotomy`)

Formalizes:
- **Strong Inductive Dichotomy Predicate (`Stage1CombCoCombDichotomyStrongAt r`)**: Strengthens
  outcome **(P2$_r$-SplitOrCross)** from exponent $3 D_r$ (`Stage1CombCoCombDichotomyAt r`) to
  $2 D_r$ so that recursive calls satisfy $2 D_{r'} + 2 + 10 r \le \frac{5}{8} D_r$.
- **Proposition 1 (`prop1_comb_cocomb_dichotomy`, `main.tex` lines 493–509)** and the base case
  $r = 1$ (`stage1_comb_cocomb_dichotomy_strong_r1` / `stage1_comb_cocomb_dichotomy_r1`).
- **General Depth-$d$ Core Dichotomy (`general_depth_d_core_dichotomy`) and Lemma 12
  (`single_u_level2_core_dichotomy`, `main.tex` lines 570–577)**.
-/

/-- Stronger inductive depth-$r$ Stage-1 Comb/Co-Comb Dichotomy with split-width exponent $2 D_r$
(which is $\le 3 D_r$ and satisfies $2 D_{r-1} + 2 \le \frac{5}{8} D_r$ for all $r \ge 2$). -/
def Stage1CombCoCombDichotomyStrongAt (r : ℕ) : Prop :=
  1 ≤ r →
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : SimpleGraph V) (S : Finset V)
    (s ℓ p_cap L_max : ℕ) (η_out w : ℝ)
    (a : Fin ℓ → V) (B : Fin ℓ → Finset V) (stems : Fin ℓ → Fin s → V),
    1 ≤ s → 64 ≤ ℓ → ℓ ≤ p_cap → 2 ≤ L_max → L_max ≤ ℓ →
    0 < η_out → η_out ≤ (2 : ℝ)⁻¹ ^ 16 →
    IsInducedSubgraphFree F (PkCompl (s + 4 + r)) →
    IsCombOrCoCombIn F S ℓ w a B →
    HasPerHandleApexStems F S ℓ s a B stems →
    combMinWidth r η_out p_cap ≤ w →
      let U_ambient := Finset.biUnion Finset.univ B
      -- (P2_r-SplitOrCross) with exponent 2 * splitTreeD r
      (∃ k : ℕ, L_max ≤ k ∧ k ≤ p_cap ∧
        ∃ U : Fin k → Finset V,
          IsWeaklySparseOrCoSparseBlockadeIn F U_ambient k
            (w / ((2 : ℝ) ^ (60 * r) * (k : ℝ) ^ (2 * splitTreeD r))) η_out U) ∨
      -- (P2_r-Cap)
      (∃ U : Fin p_cap → Finset V,
        IsWeaklySparseOrCoSparseBlockadeIn F U_ambient p_cap
          ((2 : ℝ) ^ (-(200 * (r : ℝ) ^ 2)) * η_out ^ r * (p_cap : ℝ) ^ (-(capExpE r : ℝ)) * w)
          η_out U)

/-- `Stage1CombCoCombDichotomyStrongAt r` implies `Stage1CombCoCombDichotomyAt r` because
$k^{2 D_r} \le k^{3 D_r}$ for all $k \ge 1$. -/
theorem Stage1CombCoCombDichotomyStrongAt.to_weak {r : ℕ}
    (h : Stage1CombCoCombDichotomyStrongAt r) : Stage1CombCoCombDichotomyAt r := by
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
    have hk_ge1 : (1 : ℝ) ≤ (k : ℝ) := by
      have : 1 ≤ k := by omega
      exact Nat.one_le_cast.mpr this
    have hk_pow : (k : ℝ) ^ (2 * splitTreeD r) ≤ (k : ℝ) ^ (3 * splitTreeD r) :=
      pow_le_pow_right₀ hk_ge1 (by omega)
    exact div_le_div_of_nonneg_left hw_nn (by positivity)
      (mul_le_mul_of_nonneg_left hk_pow (by positivity))
  · right; exact ⟨U, hU⟩

/-- Cross-block complete-or-$\eta_0$-sparse purification helper for Proposition 1:
if every incomplete external attachment from $M_j^*$ into $M_i^*$ has size $< \frac{\eta_0}{2\ell_1} |M_i^*|$,
deleting complete vertices for all incomplete pairs yields a complete-or-$\eta_0$-sparse blockade
$D_i \subseteq M_i^*$ of width $> \frac{1}{2}|M_i^*|$. -/
lemma prop1_cross_block_purification {F : SimpleGraph V} {U_ambient : Finset V}
    {ℓ₁ : ℕ} {η₀ w_core : ℝ} {B M_star : Fin ℓ₁ → Finset V}
    (hℓ₁ : 16 ≤ ℓ₁) (hη₀_pos : 0 < η₀) (hη₀_ub : η₀ ≤ (2 : ℝ)⁻¹ ^ 16)
    (hB_sub : ∀ i : Fin ℓ₁, B i ⊆ U_ambient)
    (hB_disj : ∀ i j : Fin ℓ₁, i ≠ j → Disjoint (B i) (B j))
    (hM_sub : ∀ i : Fin ℓ₁, M_star i ⊆ B i)
    (hM_ne : ∀ i : Fin ℓ₁, (M_star i).Nonempty)
    (hM_width : ∀ i : Fin ℓ₁, w_core ≤ ((M_star i).card : ℝ))
    (h_sparse_att : ∀ (i j : Fin ℓ₁), j ≠ i → ∀ u ∈ M_star j,
      (¬∀ z ∈ M_star i, F.Adj u z) →
      ((neighborFinsetIn F u (M_star i)).card : ℝ) < (η₀ / (2 * (ℓ₁ : ℝ))) * ((M_star i).card : ℝ)) :
    ∃ D : Fin ℓ₁ → Finset V,
      (∀ i : Fin ℓ₁, D i ⊆ B i) ∧
      IsCompleteOrXSparseBlockadeIn F U_ambient ℓ₁ (w_core / 2) η₀ D := by
  have hℓ₁_r : (16 : ℝ) ≤ (ℓ₁ : ℝ) := Nat.ofNat_le_cast.mpr hℓ₁
  let B_comp (i j : Fin ℓ₁) : Finset V :=
    (M_star i).filter (fun z => ∀ u ∈ M_star j, F.Adj z u)
  let J_incomp (i : Fin ℓ₁) : Finset (Fin ℓ₁) :=
    Finset.univ.filter (fun j : Fin ℓ₁ => j ≠ i ∧ ¬IsCompletePair F (M_star i) (M_star j))
  let D (i : Fin ℓ₁) : Finset V :=
    M_star i \ (J_incomp i).biUnion (B_comp i)
  have hB_comp_lt : ∀ (i j : Fin ℓ₁), j ∈ J_incomp i →
      ((B_comp i j).card : ℝ) < (η₀ / (2 * (ℓ₁ : ℝ))) * ((M_star i).card : ℝ) := by
    intro i j hj
    obtain ⟨hji, h_not_comp⟩ := (Finset.mem_filter.mp hj).2
    unfold IsCompletePair at h_not_comp
    push_neg at h_not_comp
    obtain ⟨z₀, hz₀, u₀, hu₀, h_nadj⟩ := h_not_comp
    have hu₀_not_comp : ¬∀ z ∈ M_star i, F.Adj u₀ z :=
      fun h => h_nadj (F.symm (h z₀ hz₀))
    have h_sub : B_comp i j ⊆ neighborFinsetIn F u₀ (M_star i) := by
      intro z hz
      obtain ⟨hz_Mi, hz_comp⟩ := Finset.mem_filter.mp hz
      exact (mem_neighborFinsetIn_iff F u₀ (M_star i) z).mpr ⟨hz_Mi, F.symm (hz_comp u₀ hu₀)⟩
    exact lt_of_le_of_lt (Nat.cast_le.mpr (Finset.card_le_card h_sub))
      (h_sparse_att i j hji u₀ hu₀ hu₀_not_comp)
  have hD_half : ∀ i : Fin ℓ₁, ((M_star i).card : ℝ) / 2 < ((D i).card : ℝ) := by
    intro i
    have h_sub : M_star i ⊆ D i ∪ (J_incomp i).biUnion (B_comp i) := by
      intro z hz
      by_cases hz_in : z ∈ (J_incomp i).biUnion (B_comp i)
      · exact Finset.mem_union_right _ hz_in
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hz, hz_in⟩)
    have h_card_le : (M_star i).card ≤ (D i).card + ∑ j ∈ J_incomp i, (B_comp i j).card := by
      calc (M_star i).card
          ≤ (D i ∪ (J_incomp i).biUnion (B_comp i)).card := Finset.card_le_card h_sub
        _ ≤ (D i).card + ((J_incomp i).biUnion (B_comp i)).card := Finset.card_union_le _ _
        _ ≤ (D i).card + ∑ j ∈ J_incomp i, (B_comp i j).card :=
            Nat.add_le_add_left Finset.card_biUnion_le _
    have h_card_r : ((M_star i).card : ℝ) ≤
        ((D i).card : ℝ) + ∑ j ∈ J_incomp i, ((B_comp i j).card : ℝ) := by exact_mod_cast h_card_le
    have h_J_card : ((J_incomp i).card : ℝ) ≤ (ℓ₁ : ℝ) := by
      have : (J_incomp i).card ≤ (Finset.univ : Finset (Fin ℓ₁)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      rw [Finset.card_univ, Fintype.card_fin] at this
      exact Nat.cast_le.mpr this
    have h_sum_le : ∑ j ∈ J_incomp i, ((B_comp i j).card : ℝ) ≤
        (η₀ / 2) * ((M_star i).card : ℝ) := by
      calc ∑ j ∈ J_incomp i, ((B_comp i j).card : ℝ)
          ≤ ∑ _j ∈ J_incomp i, ((η₀ / (2 * (ℓ₁ : ℝ))) * ((M_star i).card : ℝ)) :=
            Finset.sum_le_sum (fun j hj => le_of_lt (hB_comp_lt i j hj))
        _ = ((J_incomp i).card : ℝ) * ((η₀ / (2 * (ℓ₁ : ℝ))) * ((M_star i).card : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (ℓ₁ : ℝ) * ((η₀ / (2 * (ℓ₁ : ℝ))) * ((M_star i).card : ℝ)) :=
            mul_le_mul_of_nonneg_right h_J_card (by positivity)
        _ = ((ℓ₁ : ℝ) / (ℓ₁ : ℝ)) * ((η₀ / 2) * ((M_star i).card : ℝ)) := by ring
        _ = (η₀ / 2) * ((M_star i).card : ℝ) := by rw [div_self (by linarith), one_mul]
    have hM_pos : 0 < ((M_star i).card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr (hM_ne i))
    have hη_lt1 : η₀ < 1 := lt_of_le_of_lt hη₀_ub (by norm_num)
    nlinarith
  have hD_sparse : ∀ (p q : Fin ℓ₁), p ≠ q → ¬IsCompletePair F (M_star p) (M_star q) →
      IsXSparseTo F (D p) (D q) η₀ := by
    intro p q hpq h_not_comp z hz
    obtain ⟨hz_Mp, hz_not_bi⟩ := Finset.mem_sdiff.mp hz
    have hq_mem : q ∈ J_incomp p :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ q, hpq.symm, h_not_comp⟩
    have hz_not_B : z ∉ B_comp p q :=
      fun h => hz_not_bi (Finset.mem_biUnion.mpr ⟨q, hq_mem, h⟩)
    have hz_not_comp : ¬∀ u ∈ M_star q, F.Adj z u :=
      fun h => hz_not_B (Finset.mem_filter.mpr ⟨hz_Mp, h⟩)
    have h_deg := h_sparse_att q p hpq z hz_Mp hz_not_comp
    have h_sub : neighborFinsetIn F z (D q) ⊆ neighborFinsetIn F z (M_star q) :=
      neighborFinsetIn_mono F z Finset.sdiff_subset
    have h_le1 : ((neighborFinsetIn F z (D q)).card : ℝ) ≤
        (η₀ / (2 * (ℓ₁ : ℝ))) * ((M_star q).card : ℝ) :=
      le_trans (Nat.cast_le.mpr (Finset.card_le_card h_sub)) (le_of_lt h_deg)
    have h_le2 : (η₀ / (2 * (ℓ₁ : ℝ))) * ((M_star q).card : ℝ) ≤ (η₀ / 2) * ((M_star q).card : ℝ) := by
      refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
      exact div_le_div_of_nonneg_left (le_of_lt hη₀_pos) (by positivity) (by linarith)
    have h_half_q := hD_half q
    nlinarith
  refine ⟨D, fun i => Finset.sdiff_subset.trans (hM_sub i), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i; exact (Finset.sdiff_subset.trans (hM_sub i)).trans (hB_sub i)
  · intro i
    rw [← Finset.card_pos, ← @Nat.cast_pos ℝ]
    have hM_pos : 0 < ((M_star i).card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr (hM_ne i))
    linarith [hD_half i]
  · intro i j hij
    exact Finset.disjoint_of_subset_left (Finset.sdiff_subset.trans (hM_sub i))
      (Finset.disjoint_of_subset_right (Finset.sdiff_subset.trans (hM_sub j)) (hB_disj i j hij))
  · intro i
    have h1 := hM_width i
    have h2 := hD_half i
    linarith
  · intro i j hij
    by_cases h_comp : IsCompletePair F (M_star i) (M_star j)
    · exact Or.inl (fun u hu v hv => h_comp u (Finset.sdiff_subset hu) v (Finset.sdiff_subset hv))
    · have h_comp_symm : ¬IsCompletePair F (M_star j) (M_star i) :=
        fun h => h_comp (fun u hu v hv => F.symm (h v hv u hu))
      exact Or.inr ⟨hD_sparse j i hij.symm h_comp_symm, hD_sparse i j hij h_comp⟩

/-- Width lower-bound helper for Proposition 1 when $p_{\mathrm{comp}} < p_{\mathrm{cap}}$:
shows that $\theta_1 \frac{w_1}{L_{\max}^8} \ge \frac{w_1}{64 p_{\mathrm{comp}}^{10}}$ (which is
independent of $\eta_0$ and $p_{\mathrm{cap}}$). -/
lemma prop1_pure_split_width_bound {ℓ₁ L_max p_comp : ℕ} {η₀ w₁ θ₁ τ_i : ℝ}
    (hℓ₁ : 16 ≤ ℓ₁) (hL_low : 2 ≤ L_max) (hL_high : L_max ≤ ℓ₁) (hL_le_comp : L_max ≤ p_comp)
    (hη₀_pos : 0 < η₀) (hw₁_pos : 0 ≤ w₁)
    (h_ceil_le : 8 * (ℓ₁ : ℝ) ^ 2 * η₀⁻¹ ≤ (p_comp : ℝ))
    (hθ₁_def : θ₁ = η₀ / (64 * (ℓ₁ : ℝ) * (p_comp : ℝ) ^ 2))
    (hτ_ge : θ₁ * (w₁ / (L_max : ℝ) ^ 8) ≤ τ_i) :
    w₁ / (64 * (p_comp : ℝ) ^ 10) ≤ τ_i := by
  have hℓ₁_r : (16 : ℝ) ≤ (ℓ₁ : ℝ) := Nat.ofNat_le_cast.mpr hℓ₁
  have hL_r : (2 : ℝ) ≤ (L_max : ℝ) := Nat.ofNat_le_cast.mpr hL_low
  have hp_r : (2 : ℝ) ≤ (p_comp : ℝ) := le_trans hL_r (Nat.cast_le.mpr hL_le_comp)
  have h_θ1_ge : (L_max : ℝ) / (8 * (p_comp : ℝ) ^ 3) ≤ θ₁ := by
    rw [hθ₁_def, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : 8 * (ℓ₁ : ℝ) ^ 2 ≤ (p_comp : ℝ) * η₀ := by
      have h_mul := mul_le_mul_of_nonneg_right h_ceil_le (le_of_lt hη₀_pos)
      rwa [mul_assoc, inv_mul_cancel₀ (ne_of_gt hη₀_pos), mul_one] at h_mul
    have h2 : (L_max : ℝ) * (ℓ₁ : ℝ) ≤ (ℓ₁ : ℝ) ^ 2 := by
      have : (L_max : ℝ) ≤ (ℓ₁ : ℝ) := Nat.cast_le.mpr hL_high
      nlinarith
    calc (L_max : ℝ) * (64 * (ℓ₁ : ℝ) * (p_comp : ℝ) ^ 2)
        = 8 * (p_comp : ℝ) ^ 2 * (8 * ((L_max : ℝ) * (ℓ₁ : ℝ))) := by ring
      _ ≤ 8 * (p_comp : ℝ) ^ 2 * (8 * (ℓ₁ : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ 8 * (p_comp : ℝ) ^ 2 * ((p_comp : ℝ) * η₀) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = η₀ * (8 * (p_comp : ℝ) ^ 3) := by ring
  have hL7_k7 : (L_max : ℝ) ^ 7 ≤ (p_comp : ℝ) ^ 7 :=
    pow_le_pow_left₀ (by positivity) (Nat.cast_le.mpr hL_le_comp) 7
  have h_den : 8 * (p_comp : ℝ) ^ 3 * (L_max : ℝ) ^ 7 ≤ 64 * (p_comp : ℝ) ^ 10 := by
    calc 8 * (p_comp : ℝ) ^ 3 * (L_max : ℝ) ^ 7
        ≤ 64 * (p_comp : ℝ) ^ 3 * (p_comp : ℝ) ^ 7 := by
          refine mul_le_mul (by linarith [show (0 : ℝ) < (p_comp : ℝ) ^ 3 by positivity])
            hL7_k7 (by positivity) (by positivity)
      _ = 64 * (p_comp : ℝ) ^ 10 := by ring
  calc w₁ / (64 * (p_comp : ℝ) ^ 10)
      ≤ w₁ / (8 * (p_comp : ℝ) ^ 3 * (L_max : ℝ) ^ 7) :=
        div_le_div_of_nonneg_left hw₁_pos (by positivity) h_den
    _ = ((L_max : ℝ) / (8 * (p_comp : ℝ) ^ 3)) * (w₁ / (L_max : ℝ) ^ 8) := by
        field_simp
    _ ≤ θ₁ * (w₁ / (L_max : ℝ) ^ 8) :=
        mul_le_mul_of_nonneg_right h_θ1_ge (by positivity)
    _ ≤ τ_i := hτ_ge

/-- **Proposition 1 (`prop1_comb_cocomb_dichotomy`, Comb/Co-Comb Dichotomy for $\overline{P_{s+5}}$-Free Graphs)**:
Let $s \ge 1$, $p_{\mathrm{cap}} \ge \ell_1 \ge 16$, $L_{\max} \in [2, \ell_1]$, $\eta_0 \in (0, 2^{-16}]$,
and let $F$ be a $\overline{P_{s+5}}$-free graph containing an $(\ell_1, w_1)$-comb or co-comb
$((a_i, B_i) : i \in [\ell_1])$ inside $S$ with per-handle $s$-stems and
$w_1 \ge 2^{44} \eta_0^{-1} p_{\mathrm{cap}}^{22}$. Then inside $U_{\mathrm{ambient}} := \bigsqcup_{i=1}^{\ell_1} B_i$,
at least one of **(P1-Cap)**, **(P1-PureSplit)**, or **(P1-CrossBlock)** holds. -/
theorem prop1_comb_cocomb_dichotomy {F : SimpleGraph V} {S : Finset V}
    {s ℓ₁ p_cap L_max : ℕ} {η₀ w₁ : ℝ}
    {a : Fin ℓ₁ → V} {B : Fin ℓ₁ → Finset V} {stems : Fin ℓ₁ → Fin s → V}
    (hs : 1 ≤ s) (hℓ₁ : 16 ≤ ℓ₁) (hp_cap : ℓ₁ ≤ p_cap)
    (hL_low : 2 ≤ L_max) (hL_high : L_max ≤ ℓ₁)
    (hη₀_pos : 0 < η₀) (hη₀_ub : η₀ ≤ (2 : ℝ)⁻¹ ^ 16)
    (hfree : IsInducedSubgraphFree F (PkCompl (s + 5)))
    (hcomb : IsCombOrCoCombIn F S ℓ₁ w₁ a B)
    (hstems : HasPerHandleApexStems F S ℓ₁ s a B stems)
    (hw₁ : (2 : ℝ) ^ 44 * η₀⁻¹ * (p_cap : ℝ) ^ 22 ≤ w₁) :
    let U_ambient := Finset.biUnion Finset.univ B
    -- (P1-Cap)
    (∃ Q : Fin p_cap → Finset V,
      IsPureBlockadeIn F U_ambient p_cap
        ((η₀ / (64 * (p_cap : ℝ) ^ 4)) * (w₁ / (L_max : ℝ) ^ 8)) Q) ∨
    -- (P1-PureSplit)
    (L_max < p_cap ∧ ∃ (k : ℕ) (D : Fin k → Finset V),
      L_max ≤ k ∧ k < p_cap ∧
      IsPureBlockadeIn F U_ambient k (w₁ / (64 * (k : ℝ) ^ 10)) D) ∨
    -- (P1-CrossBlock)
    (∃ D : Fin ℓ₁ → Finset V,
      (∀ i : Fin ℓ₁, D i ⊆ B i) ∧
      IsCompleteOrXSparseBlockadeIn F U_ambient ℓ₁
        ((2 : ℝ)⁻¹ ^ 4 * (L_max : ℝ)⁻¹ ^ 8 * w₁) η₀ D) := by
  intro U_ambient
  have hB_block : IsBlockadeIn F S ℓ₁ w₁ B := by
    rcases hcomb with hc | hco
    · exact hc.is_blockade
    · exact hco.is_blockade
  have hB_sub_U : ∀ i : Fin ℓ₁, B i ⊆ U_ambient :=
    fun i => Finset.subset_biUnion_of_mem B (Finset.mem_univ i)
  have hℓ₁_r : (16 : ℝ) ≤ (ℓ₁ : ℝ) := Nat.ofNat_le_cast.mpr hℓ₁
  have hp_cap_r : (16 : ℝ) ≤ (p_cap : ℝ) := Nat.ofNat_le_cast.mpr (le_trans hℓ₁ hp_cap)
  have hp_cap_pos : (0 : ℝ) < (p_cap : ℝ) := by linarith
  have hL_r : (2 : ℝ) ≤ (L_max : ℝ) := Nat.ofNat_le_cast.mpr hL_low
  have hη₀_le1 : η₀ ≤ 1 := le_trans hη₀_ub (by norm_num)
  have hη₀_inv_ge1 : 1 ≤ η₀⁻¹ := one_le_inv₀ hη₀_pos |>.mpr hη₀_le1
  have hw₁_pos : 0 < w₁ := lt_of_lt_of_le (by positivity) hw₁
  let p_comp : ℕ := min p_cap ⌈8 * (ℓ₁ : ℝ) ^ 2 * η₀⁻¹⌉₊
  have hp_comp_le_p : p_comp ≤ p_cap := Nat.min_le_left _ _
  have hℓ₁_le_comp : ℓ₁ ≤ p_comp := by
    refine le_min hp_cap ?_
    have h1 : (ℓ₁ : ℝ) ≤ 8 * (ℓ₁ : ℝ) ^ 2 * 1 := by nlinarith
    have h2 : 8 * (ℓ₁ : ℝ) ^ 2 * 1 ≤ 8 * (ℓ₁ : ℝ) ^ 2 * η₀⁻¹ :=
      mul_le_mul_of_nonneg_left hη₀_inv_ge1 (by positivity)
    have h3 : (ℓ₁ : ℝ) ≤ (⌈8 * (ℓ₁ : ℝ) ^ 2 * η₀⁻¹⌉₊ : ℝ) :=
      le_trans (by linarith) (Nat.le_ceil (8 * (ℓ₁ : ℝ) ^ 2 * η₀⁻¹))
    exact Nat.cast_le.mp h3
  have hp_comp_pos : (0 : ℝ) < (p_comp : ℝ) := Nat.cast_pos.mpr (by omega)
  let θ₁ : ℝ := η₀ / (64 * (ℓ₁ : ℝ) * (p_comp : ℝ) ^ 2)
  have hθ₁_pos : 0 < θ₁ := by unfold θ₁; positivity
  have hθ₁_ub : θ₁ ≤ 1 / (64 * (ℓ₁ : ℝ) ^ 2) := by
    unfold θ₁
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (ℓ₁ : ℝ) ≤ (p_comp : ℝ) := Nat.cast_le.mpr hℓ₁_le_comp
    have h2 : (ℓ₁ : ℝ) ^ 2 ≤ (p_comp : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    nlinarith
  have hθ₁_lb : η₀ / (64 * (p_cap : ℝ) ^ 3) ≤ θ₁ := by
    unfold θ₁
    refine div_le_div_of_nonneg_left (le_of_lt hη₀_pos) (by positivity) ?_
    have h1 : (ℓ₁ : ℝ) ≤ (p_cap : ℝ) := Nat.cast_le.mpr hp_cap
    have h2 : (p_comp : ℝ) ^ 2 ≤ (p_cap : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (Nat.cast_le.mpr hp_comp_le_p) 2
    calc 64 * (ℓ₁ : ℝ) * (p_comp : ℝ) ^ 2
        ≤ 64 * (p_cap : ℝ) * (p_cap : ℝ) ^ 2 := by
          refine mul_le_mul (by linarith) h2 (by positivity) (by positivity)
      _ = 64 * (p_cap : ℝ) ^ 3 := by ring
  have h_min_θ₁ : η₀ / (64 * (p_cap : ℝ) ^ 4) ≤ min θ₁ (1 / (64 * (p_cap : ℝ) ^ 2)) := by
    refine le_min ?_ ?_
    · refine le_trans ?_ hθ₁_lb
      refine div_le_div_of_nonneg_left (le_of_lt hη₀_pos) (by positivity) ?_
      have : (1 : ℝ) ≤ (p_cap : ℝ) := by linarith
      calc 64 * (p_cap : ℝ) ^ 3 = 64 * (p_cap : ℝ) ^ 3 * 1 := by ring
        _ ≤ 64 * (p_cap : ℝ) ^ 3 * (p_cap : ℝ) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = 64 * (p_cap : ℝ) ^ 4 := by ring
    · rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : (1 : ℝ) ≤ (p_cap : ℝ) ^ 2 := by nlinarith
      nlinarith
  have hw₁_precond : 64 * (p_cap : ℝ) ^ 2 * θ₁⁻¹ * (4 * (ℓ₁ : ℝ)) ^ 16 ≤ w₁ := by
    have hθ₁_inv_ub : θ₁⁻¹ ≤ 64 * (p_cap : ℝ) ^ 3 * η₀⁻¹ := by
      have h1 := one_div_le_one_div_of_le (by positivity : 0 < η₀ / (64 * (p_cap : ℝ) ^ 3)) hθ₁_lb
      rw [one_div, one_div_div] at h1
      calc θ₁⁻¹ ≤ 64 * (p_cap : ℝ) ^ 3 / η₀ := h1
        _ = 64 * (p_cap : ℝ) ^ 3 * η₀⁻¹ := div_eq_mul_inv _ _
    have h4ℓ_le : (4 * (ℓ₁ : ℝ)) ^ 16 ≤ (2 : ℝ) ^ 32 * (p_cap : ℝ) ^ 16 := by
      have h1 : (ℓ₁ : ℝ) ^ 16 ≤ (p_cap : ℝ) ^ 16 :=
        pow_le_pow_left₀ (by positivity) (Nat.cast_le.mpr hp_cap) 16
      calc (4 * (ℓ₁ : ℝ)) ^ 16 = (2 : ℝ) ^ 32 * (ℓ₁ : ℝ) ^ 16 := by ring
        _ ≤ (2 : ℝ) ^ 32 * (p_cap : ℝ) ^ 16 := mul_le_mul_of_nonneg_left h1 (by positivity)
    have hp21_22 : (p_cap : ℝ) ^ 21 ≤ (p_cap : ℝ) ^ 22 :=
      pow_le_pow_right₀ (by linarith) (by omega)
    calc 64 * (p_cap : ℝ) ^ 2 * θ₁⁻¹ * (4 * (ℓ₁ : ℝ)) ^ 16
        ≤ 64 * (p_cap : ℝ) ^ 2 * (64 * (p_cap : ℝ) ^ 3 * η₀⁻¹) * ((2 : ℝ) ^ 32 * (p_cap : ℝ) ^ 16) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hθ₁_inv_ub (by positivity))
            h4ℓ_le (by positivity) (by positivity)
      _ = (2 : ℝ) ^ 44 * η₀⁻¹ * (p_cap : ℝ) ^ 21 := by ring
      _ ≤ (2 : ℝ) ^ 44 * η₀⁻¹ * (p_cap : ℝ) ^ 22 :=
          mul_le_mul_of_nonneg_left hp21_22 (by positivity)
      _ ≤ w₁ := hw₁
  -- Apply Lemma 8(2) to each tooth B_i
  by_cases h_gc2_cap : ∃ (i : Fin ℓ₁) (Q : Fin p_cap → Finset V),
      IsPureBlockadeIn F (B i) p_cap
        (min θ₁ (1 / (64 * (p_cap : ℝ) ^ 2)) * (((B i).card : ℝ) / (L_max : ℝ) ^ 8)) Q
  · left
    obtain ⟨i, Q, hQ⟩ := h_gc2_cap
    refine ⟨Q, ⟨(hQ.1.mono_ambient (hB_sub_U i)).mono_width ?_, hQ.2⟩⟩
    exact mul_le_mul h_min_θ₁
      (div_le_div_of_nonneg_right (hB_block.width_ge i) (by positivity))
      (by positivity) (by positivity)
  · by_cases h_gc2_split : ∃ (i : Fin ℓ₁), L_max < p_cap ∧ ∃ (k : ℕ) (U : Fin k → Finset V),
        L_max ≤ k ∧ k < p_cap ∧
        IsPureBlockadeIn F (B i) k (((B i).card : ℝ) / (64 * (k : ℝ) ^ 10)) U
    · right; left
      obtain ⟨i, hL_lt_p, k, U, hkL, hkp, hU⟩ := h_gc2_split
      refine ⟨hL_lt_p, k, U, hkL, hkp, ⟨(hU.1.mono_ambient (hB_sub_U i)).mono_width ?_, hU.2⟩⟩
      exact div_le_div_of_nonneg_right (hB_block.width_ge i) (by positivity)
    · -- Every tooth B_i is in (GC1-Core); extract M_T and M_star via Classical.axiomOfChoice
      have h_all_core : ∀ i : Fin ℓ₁,
          ∃ M_T : Finset V, M_T ⊆ B i ∧
            ∃ M_star : Finset V, M_star ⊆ M_T ∧
              (15 / 64 : ℝ) * (w₁ / (L_max : ℝ) ^ 8) < (M_star.card : ℝ) ∧
              (∀ X : Finset V, IsProperModuleIn F M_T X → (X ∩ M_star).Nonempty →
                X ⊆ M_star ∧ (X.card : ℝ) < 5 * θ₁ * (M_star.card : ℝ)) := by
        intro i
        have hBi_card : 64 * (p_cap : ℝ) ^ 2 * θ₁⁻¹ * (4 * (ℓ₁ : ℝ)) ^ 16 ≤ ((B i).card : ℝ) :=
          le_trans hw₁_precond (hB_block.width_ge i)
        rcases iterated_gallai_core_decomposition F (B i) ℓ₁ p_cap L_max θ₁
            hℓ₁ hp_cap hL_low hL_high hθ₁_pos hθ₁_ub hBi_card with
          ⟨W, hWB, hW_gt, M_T, hMT_W, _, _, M_star, hMs_MT, hMs_gt, hMs_prop⟩ | h_sp | ⟨Q, hQ⟩
        · have hW_w1 : w₁ / (L_max : ℝ) ^ 8 < (W.card : ℝ) :=
            lt_of_le_of_lt (div_le_div_of_nonneg_right (hB_block.width_ge i) (by positivity)) hW_gt
          exact ⟨M_T, hMT_W.trans hWB, M_star, hMs_MT, by linarith, hMs_prop⟩
        · exact False.elim (h_gc2_split ⟨i, h_sp⟩)
        · exact False.elim (h_gc2_cap ⟨i, Q, hQ⟩)
      obtain ⟨M_T, hMT_all⟩ := Classical.axiomOfChoice h_all_core
      obtain ⟨M_star, hMs_all⟩ := Classical.axiomOfChoice (fun i => (hMT_all i).2)
      have hMT_sub_B : ∀ i : Fin ℓ₁, M_T i ⊆ B i := fun i => (hMT_all i).1
      have hMs_sub_MT : ∀ i : Fin ℓ₁, M_star i ⊆ M_T i := fun i => (hMs_all i).1
      have hMs_sub_B : ∀ i : Fin ℓ₁, M_star i ⊆ B i := fun i => (hMs_sub_MT i).trans (hMT_sub_B i)
      have hMs_gt_w1 : ∀ i : Fin ℓ₁,
          (15 / 64 : ℝ) * (w₁ / (L_max : ℝ) ^ 8) < ((M_star i).card : ℝ) :=
        fun i => (hMs_all i).2.1
      have hMs_prop : ∀ (i : Fin ℓ₁) (X : Finset V),
          IsProperModuleIn F (M_T i) X → (X ∩ M_star i).Nonempty →
          X ⊆ M_star i ∧ (X.card : ℝ) < 5 * θ₁ * ((M_star i).card : ℝ) :=
        fun i => (hMs_all i).2.2
      have hMs_ne : ∀ i : Fin ℓ₁, (M_star i).Nonempty := by
        intro i
        rw [← Finset.card_pos, ← @Nat.cast_pos ℝ]
        have : 0 < (15 / 64 : ℝ) * (w₁ / (L_max : ℝ) ^ 8) := by positivity
        linarith [hMs_gt_w1 i]
      by_cases h_dense_att : ∃ (i j : Fin ℓ₁), j ≠ i ∧ ∃ u ∈ M_star j,
          (¬∀ z ∈ M_T i, F.Adj u z) ∧
          (η₀ / (2 * (ℓ₁ : ℝ))) * ((M_star i).card : ℝ) ≤ ((neighborFinsetIn F u (M_star i)).card : ℝ)
      · -- Dense incomplete attachment yields a complete p_comp-blockade via Lemma 9(1) + greedy grouping
        obtain ⟨i, j, hji, u, hu_Mj, hu_not_comp, hu_deg⟩ := h_dense_att
        let τ_i := 5 * θ₁ * ((M_star i).card : ℝ)
        have hτ_pos : 0 < τ_i := by
          unfold τ_i
          have : 0 < ((M_star i).card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr (hMs_ne i))
          positivity
        have h_2p_le : 2 * (p_comp : ℝ) * τ_i ≤ ((neighborFinsetIn F u (M_star i)).card : ℝ) := by
          have h_coef : 2 * (p_comp : ℝ) * τ_i ≤ (η₀ / (2 * (ℓ₁ : ℝ))) * ((M_star i).card : ℝ) := by
            unfold τ_i θ₁
            have h1 : (1 : ℝ) ≤ (p_comp : ℝ) := Nat.one_le_cast.mpr (by omega)
            have h_eq : 2 * (p_comp : ℝ) * (5 * (η₀ / (64 * (ℓ₁ : ℝ) * (p_comp : ℝ) ^ 2)) * ((M_star i).card : ℝ)) =
                ((p_comp : ℝ) / (p_comp : ℝ)) * ((10 / (64 * (p_comp : ℝ))) * (η₀ / (ℓ₁ : ℝ)) * ((M_star i).card : ℝ)) := by ring
            rw [h_eq, div_self (by linarith), one_mul]
            have h_10_64 : 10 / (64 * (p_comp : ℝ)) ≤ 1 / 2 := by
              rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
            calc (10 / (64 * (p_comp : ℝ))) * (η₀ / (ℓ₁ : ℝ)) * ((M_star i).card : ℝ)
                ≤ (1 / 2) * (η₀ / (ℓ₁ : ℝ)) * ((M_star i).card : ℝ) :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right h_10_64 (by positivity)) (Nat.cast_nonneg _)
              _ = (η₀ / (2 * (ℓ₁ : ℝ))) * ((M_star i).card : ℝ) := by ring
          exact le_trans h_coef hu_deg
        have h_mod_r0 : ∀ C : Finset V,
            IsAnticonnectedComponentOf F (neighborFinsetIn F u (M_T i)) C →
            IsProperModuleIn F (M_T i) C := by
          intro C hC
          have hfree0 : IsInducedSubgraphFree F (PkCompl (s + 5 + 0)) := hfree
          exact universal_depth_r_neighborhood_modularity hfree0 hcomb hstems hji.symm
            (fun _ => u) (fun _ => M_T i) (hMs_sub_B j hu_Mj) (hMT_sub_B i)
            (fun d => Fin.elim0 d) (fun d => Fin.elim0 d) hu_not_comp hC
        have h_small_i : ∀ X : Finset V,
            IsProperModuleIn F (M_T i) X → (X ∩ M_star i).Nonempty → ((X ∩ M_star i).card : ℝ) ≤ τ_i := by
          intro X hX hX_ne
          have h1 : ((X ∩ M_star i).card : ℝ) ≤ (X.card : ℝ) :=
            Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_left)
          exact le_trans h1 (le_of_lt (hMs_prop i X hX hX_ne).2)
        obtain ⟨D, hD_comp⟩ := exists_complete_blockade_of_small_components
          (hMs_sub_MT i) hτ_pos h_mod_r0 h_small_i h_2p_le
        have hD_pure : IsPureBlockadeIn F U_ambient p_comp τ_i D :=
          ⟨hD_comp.1.mono_ambient ((hMs_sub_B i).trans (hB_sub_U i)),
           fun a b hab => Or.inl (hD_comp.2 a b hab)⟩
        have hτ_gt_θ1 : θ₁ * (w₁ / (L_max : ℝ) ^ 8) < τ_i := by
          unfold τ_i
          have := hMs_gt_w1 i
          nlinarith
        by_cases hp_eq : p_comp = p_cap
        · -- p_comp = p_cap → (P1-Cap)
          left
          have hp_eq_r : (p_comp : ℝ) = (p_cap : ℝ) := Nat.cast_inj.mpr hp_eq
          refine ⟨fun j => D (Fin.cast hp_eq.symm j),
            ⟨⟨fun j => hD_pure.1.subset_ambient (Fin.cast hp_eq.symm j),
              fun j => hD_pure.1.nonempty_blocks (Fin.cast hp_eq.symm j),
              fun j₁ j₂ hj => hD_pure.1.pairwise_disjoint _ _ (by intro h; apply hj; simpa using h),
              fun j => ?_⟩,
             fun j₁ j₂ hj => hD_pure.2 _ _ (by intro h; apply hj; simpa using h)⟩⟩
          have h_w := hD_pure.1.width_ge (Fin.cast hp_eq.symm j)
          calc (η₀ / (64 * (p_cap : ℝ) ^ 4)) * (w₁ / (L_max : ℝ) ^ 8)
              ≤ min θ₁ (1 / (64 * (p_cap : ℝ) ^ 2)) * (w₁ / (L_max : ℝ) ^ 8) :=
                mul_le_mul_of_nonneg_right h_min_θ₁ (by positivity)
            _ ≤ θ₁ * (w₁ / (L_max : ℝ) ^ 8) :=
                mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
            _ ≤ τ_i := le_of_lt hτ_gt_θ1
            _ ≤ ((D (Fin.cast hp_eq.symm j)).card : ℝ) := h_w
        · -- p_comp < p_cap → (P1-PureSplit) with k = p_comp
          right; left
          have hp_lt : p_comp < p_cap := lt_of_le_of_ne hp_comp_le_p hp_eq
          have hL_le_comp : L_max ≤ p_comp := le_trans hL_high hℓ₁_le_comp
          have hp_ceil : p_comp = ⌈8 * (ℓ₁ : ℝ) ^ 2 * η₀⁻¹⌉₊ :=
            Nat.min_eq_right (le_of_lt (by omega : ⌈8 * (ℓ₁ : ℝ) ^ 2 * η₀⁻¹⌉₊ < p_cap))
          have h_ceil_le : 8 * (ℓ₁ : ℝ) ^ 2 * η₀⁻¹ ≤ (p_comp : ℝ) := by
            rw [hp_ceil]; exact Nat.le_ceil _
          refine ⟨by omega, p_comp, D, hL_le_comp, hp_lt, ⟨hD_pure.1.mono_width ?_, hD_pure.2⟩⟩
          exact prop1_pure_split_width_bound hℓ₁ hL_low hL_high hL_le_comp
            hη₀_pos (le_of_lt hw₁_pos) h_ceil_le rfl (le_of_lt hτ_gt_θ1)
      · -- Sparse incomplete attachments → (P1-CrossBlock)
        right; right
        push_neg at h_dense_att
        have h_sparse_att : ∀ (i j : Fin ℓ₁), j ≠ i → ∀ u ∈ M_star j,
            (¬∀ z ∈ M_star i, F.Adj u z) →
            ((neighborFinsetIn F u (M_star i)).card : ℝ) < (η₀ / (2 * (ℓ₁ : ℝ))) * ((M_star i).card : ℝ) := by
          intro i j hji u hu_Mj hu_not_Ms
          have hu_ex_MT : ∃ z ∈ M_T i, ¬F.Adj u z := by
            have hu_not_MT : ¬∀ z ∈ M_T i, F.Adj u z :=
              fun h => hu_not_Ms (fun z hz => h z (hMs_sub_MT i hz))
            push_neg at hu_not_MT
            exact hu_not_MT
          exact h_dense_att i j hji u hu_Mj hu_ex_MT
        have hM_width : ∀ i : Fin ℓ₁, (2 : ℝ)⁻¹ ^ 3 * (L_max : ℝ)⁻¹ ^ 8 * w₁ ≤ ((M_star i).card : ℝ) := by
          intro i
          have h1 := hMs_gt_w1 i
          have h_eq : (2 : ℝ)⁻¹ ^ 3 * (L_max : ℝ)⁻¹ ^ 8 * w₁ = (8 / 64 : ℝ) * (w₁ / (L_max : ℝ) ^ 8) := by
            rw [inv_pow]; norm_num; ring
          have h_pos : 0 ≤ w₁ / (L_max : ℝ) ^ 8 := by positivity
          linarith
        obtain ⟨D, hD_sub_B, hD_block⟩ := prop1_cross_block_purification
          hℓ₁ hη₀_pos hη₀_ub hB_sub_U hB_block.pairwise_disjoint hMs_sub_B hMs_ne hM_width h_sparse_att
        refine ⟨D, hD_sub_B, ⟨hD_block.1.mono_width ?_, hD_block.2⟩⟩
        norm_num; ring_nf; exact le_rfl

/-- **Base Case $r = 1$ of Theorem 7(1)** (`stage1_comb_cocomb_dichotomy_strong_r1`):
`Stage1CombCoCombDichotomyStrongAt 1` holds (deduced directly from Proposition 1). -/
theorem stage1_comb_cocomb_dichotomy_strong_r1 : Stage1CombCoCombDichotomyStrongAt 1 := by
  intro _ V _ _ F S s ℓ p_cap L_max η_out w a B stems
    hs hℓ hp_cap hL_low hL_high hη_pos hη_ub hfree hcomb hstems hw U_ambient
  have hℓ_16 : 16 ≤ ℓ := by omega
  have hp_cap_r : (64 : ℝ) ≤ (p_cap : ℝ) := Nat.ofNat_le_cast.mpr (le_trans hℓ hp_cap)
  have hp_pos : (0 : ℝ) < (p_cap : ℝ) := by linarith
  have hη_le1 : η_out ≤ 1 := le_trans hη_ub (by norm_num)
  have hη_inv_ge1 : 1 ≤ η_out⁻¹ := one_le_inv₀ hη_pos |>.mpr hη_le1
  have hw_pos : 0 ≤ w := by
    have : 0 < combMinWidth 1 η_out p_cap := by unfold combMinWidth; positivity
    linarith
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
  rcases prop1_comb_cocomb_dichotomy hs hℓ_16 hp_cap hL_low hL_high hη_pos hη_ub
      (by simpa using hfree) hcomb hstems hw_p1 with
    ⟨Q, hQ_pure⟩ | ⟨_, k, D, hkL, hkp, hD_pure⟩ | ⟨D, _, hD_cross⟩
  · -- (P1-Cap) → (P2_1-Cap)
    right
    refine ⟨Q, (IsPureBlockadeIn.isWeaklySparseOrCoSparseBlockadeIn hQ_pure (le_of_lt hη_pos)).mono_ambient_width_eps
      Finset.Subset.rfl ?_ le_rfl⟩
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
          refine mul_le_mul_of_nonneg_right ?_ hw_pos
          refine mul_le_mul (mul_le_mul_of_nonneg_right h_2 (le_of_lt hη_pos))
            (inv_anti₀ (by positivity) h_p12) (by positivity) (by positivity)
      _ = (η_out / (64 * (p_cap : ℝ) ^ 4)) * (w / (p_cap : ℝ) ^ 8) := by ring
      _ ≤ (η_out / (64 * (p_cap : ℝ) ^ 4)) * (w / (L_max : ℝ) ^ 8) :=
          mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_left hw_pos (by positivity) hL8_p8) (by positivity)
  · -- (P1-PureSplit) → (P2_1-SplitOrCross)
    left
    refine ⟨k, hkL, le_of_lt hkp, D,
      (IsPureBlockadeIn.isWeaklySparseOrCoSparseBlockadeIn hD_pure (le_of_lt hη_pos)).mono_ambient_width_eps
        Finset.Subset.rfl ?_ le_rfl⟩
    unfold splitTreeD
    rw [show 60 * 1 = 60 by omega, show 2 * 8 = 16 by omega]
    have hk_ge1 : (1 : ℝ) ≤ (k : ℝ) := Nat.one_le_cast.mpr (by omega)
    have hk_10_16 : (k : ℝ) ^ 10 ≤ (k : ℝ) ^ 16 := pow_le_pow_right₀ hk_ge1 (by omega)
    have h64 : (64 : ℝ) ≤ (2 : ℝ) ^ 60 := by norm_num
    exact div_le_div_of_nonneg_left hw_pos (by positivity)
      (mul_le_mul h64 hk_10_16 (by positivity) (by positivity))
  · -- (P1-CrossBlock) → (P2_1-SplitOrCross) with k = ℓ
    left
    refine ⟨ℓ, hL_high, hp_cap, D,
      (IsCompleteOrXSparseBlockadeIn.isWeaklySparseOrCoSparseBlockadeIn hD_cross (le_of_lt hη_pos)).mono_ambient_width_eps
        Finset.Subset.rfl ?_ le_rfl⟩
    unfold splitTreeD
    rw [show 60 * 1 = 60 by omega, show 2 * 8 = 16 by omega]
    have hL_le_ℓ : (L_max : ℝ) ^ 8 ≤ (ℓ : ℝ) ^ 16 := by
      calc (L_max : ℝ) ^ 8 ≤ (ℓ : ℝ) ^ 8 :=
            pow_le_pow_left₀ (by positivity) (Nat.cast_le.mpr hL_high) 8
        _ ≤ (ℓ : ℝ) ^ 16 := pow_le_pow_right₀ (by linarith [Nat.ofNat_le_cast (α := ℝ).mpr hℓ]) (by omega)
    have h_2 : (2 : ℝ) ^ 4 ≤ (2 : ℝ) ^ 60 := by norm_num
    have h_eq : (2 : ℝ)⁻¹ ^ 4 * (L_max : ℝ)⁻¹ ^ 8 * w = w / ((2 : ℝ) ^ 4 * (L_max : ℝ) ^ 8) := by
      rw [inv_pow, inv_pow]; ring
    rw [h_eq]
    exact div_le_div_of_nonneg_left hw_pos (by positivity)
      (mul_le_mul h_2 hL_le_ℓ (by positivity) (by positivity))

/-- **Base Case $r = 1$ of Theorem 7(1)** (`stage1_comb_cocomb_dichotomy_r1`):
`Stage1CombCoCombDichotomyAt 1` holds unconditionally for all $\overline{P_{s+5}}$-free combs and co-combs. -/
theorem stage1_comb_cocomb_dichotomy_r1 : Stage1CombCoCombDichotomyAt 1 :=
  stage1_comb_cocomb_dichotomy_strong_r1.to_weak

/-- **General Depth-$d$ Core Dichotomy** (`general_depth_d_core_dichotomy`, generalizing Lemma 12 to arbitrary depth $d \ge 1$):
In a $\overline{P_{s+5+d}}$-free graph $F$ with an $(\ell, w)$-comb or co-comb $((a_r, B_r) : r \in [\ell])$
and per-handle $s$-stems, given a depth-$d$ cutter chain $z_0 \in B_j, M_0 \subseteq B_i$,
$z_c \in M_{c-1} \setminus N_F(z_{c-1})$ and $M_c \subseteq N_F(z_{c-1}) \cap M_{c-1}$ ($1 \le c \le d$),
where $M_d = N_T$ contains a nonempty core $N^* \subseteq N_T$ such that every proper module of
$F[N_T]$ intersecting $N^*$ has size $< 5 \theta |N^*|$, and a cutter pool $A_{d-1} \subseteq M_{d-1} \setminus N_F(z_{d-1})$,
either:
1. $F[N^*]$ contains a complete $(p_{\mathrm{comp}}, 5 \theta |N^*|)$-blockade of exact length $p_{\mathrm{comp}}$; or
2. there exists $A_* \subseteq A_{d-1}$ with $|A_*| \ge \frac{1}{2} |A_{d-1}|$ such that either $(N^*, A_*)$
   is complete in $F$ or $A_*$ is one-sided $10 p_{\mathrm{comp}} \theta$-sparse to $N^*$ in $F$
   (hence $(N^*, A_*)$ is weakly $10 p_{\mathrm{comp}} \theta$-sparse-or-co-sparse in $F$). -/
theorem general_depth_d_core_dichotomy {F : SimpleGraph V} {S : Finset V}
    {ℓ s d p_comp : ℕ} {w θ : ℝ} {a : Fin ℓ → V} {B : Fin ℓ → Finset V}
    {stems : Fin ℓ → Fin s → V} {i j : Fin ℓ}
    (hij : i ≠ j) (hd : 1 ≤ d) (hθ_pos : 0 < θ)
    (hfree : IsInducedSubgraphFree F (PkCompl (s + 5 + d)))
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
      IsCompleteBlockadeIn F N_star p_comp (5 * θ * (N_star.card : ℝ)) D) ∨
    (∃ A_star ⊆ A_pool,
      (A_pool.card : ℝ) / 2 ≤ (A_star.card : ℝ) ∧
      Disjoint N_star A_star ∧
      (IsCompletePair F N_star A_star ∨
       IsXSparseTo F A_star N_star (10 * (p_comp : ℝ) * θ))) := by
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
    exact (hA_in x hxA).2 ((mem_neighborFinsetIn_iff F _ _ x).mp hx_in_Z).2
  by_cases h_dense : ∃ w_cut ∈ A_pool,
      (¬∀ x ∈ M (Fin.last d), F.Adj w_cut x) ∧
      2 * (p_comp : ℝ) * τ ≤ ((neighborFinsetIn F w_cut N_star).card : ℝ)
  · left
    obtain ⟨w_cut, hw_in, hw_not_comp, hw_deg⟩ := h_dense
    -- Construct depth-d sequence z_full : Fin (d + 1) → V for Lemma 9
    let z_full : Fin (d + 1) → V := fun c =>
      if hcd : c.1 < d then z ⟨c.1, hcd⟩ else w_cut
    have hz_full_lt : ∀ c : Fin (d + 1), ∀ hcd : c.1 < d, z_full c = z ⟨c.1, hcd⟩ :=
      fun c hcd => dif_pos hcd
    have hz_full_last : z_full (Fin.last d) = w_cut := dif_neg (by dsimp; omega)
    have hz_full_0 : z_full 0 ∈ B j := by
      rw [hz_full_lt 0 (by dsimp; omega)]; exact hz0
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
        have h_st := hz_step ⟨c.1 + 1, hc1⟩ (by dsimp; omega)
        have h_eq : (⟨(⟨c.1 + 1, hc1⟩ : Fin d).1 - 1, by omega⟩ : Fin d) = c := by ext; dsimp
        have h_eqM : (⟨(⟨c.1 + 1, hc1⟩ : Fin d).1 - 1, by omega⟩ : Fin (d + 1)) = c.castSucc := by ext; dsimp
        rwa [h_eq, h_eqM] at h_st
      · have hc_succ_last : c.succ = Fin.last d := by ext; dsimp; omega
        rw [hc_succ_last, hz_full_last]
        have hc_eq : c = ⟨d - 1, by omega⟩ := by ext; dsimp; omega
        rw [hc_eq]
        exact hA_in w_cut hw_in
    have h_mod_w : ∀ C : Finset V,
        IsAnticonnectedComponentOf F (neighborFinsetIn F w_cut (M (Fin.last d))) C →
        IsProperModuleIn F (M (Fin.last d)) C := by
      intro C hC
      have hw_not_comp' : ¬∀ x ∈ M (Fin.last d), F.Adj (z_full (Fin.last d)) x := by
        rwa [hz_full_last]
      have hC' : IsAnticonnectedComponentOf F
          (neighborFinsetIn F (z_full (Fin.last d)) (M (Fin.last d))) C := by
        rwa [hz_full_last]
      exact universal_depth_r_neighborhood_modularity hfree hcomb hstems hij
        z_full M hz_full_0 hM0 hM_full_step hz_full_step hw_not_comp' hC'
    have h_small_w : ∀ X : Finset V,
        IsProperModuleIn F (M (Fin.last d)) X → (X ∩ N_star).Nonempty →
        ((X ∩ N_star).card : ℝ) ≤ τ := by
      intro X hX hX_ne
      have h1 : ((X ∩ N_star).card : ℝ) ≤ (X.card : ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_left)
      exact le_trans h1 (le_of_lt (hNs_small X hX hX_ne))
    exact exists_complete_blockade_of_small_components hNs_sub hτ_pos h_mod_w h_small_w hw_deg
  · right
    push_neg at h_dense
    let A_comp := A_pool.filter (fun v => ∀ x ∈ N_star, F.Adj v x)
    let A_sp := A_pool \ A_comp
    have hA_comp_sub : A_comp ⊆ A_pool := Finset.filter_subset _ _
    have hA_sp_sub : A_sp ⊆ A_pool := Finset.sdiff_subset
    have hA_sum : (A_sp.card : ℝ) + (A_comp.card : ℝ) = (A_pool.card : ℝ) := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card hA_comp_sub
    have hA_sp_sparse : IsXSparseTo F A_sp N_star (10 * (p_comp : ℝ) * θ) := by
      intro v hv
      obtain ⟨hvA, hv_not_comp⟩ := Finset.mem_sdiff.mp hv
      have hv_not_Ns : ¬∀ x ∈ N_star, F.Adj v x :=
        fun h => hv_not_comp (Finset.mem_filter.mpr ⟨hvA, h⟩)
      have hv_ex_Md : ∃ x ∈ M (Fin.last d), ¬F.Adj v x := by
        have hv_not_Md : ¬∀ x ∈ M (Fin.last d), F.Adj v x :=
          fun h => hv_not_Ns (fun x hx => h x (hNs_sub hx))
        push_neg at hv_not_Md
        exact hv_not_Md
      have h_lt := h_dense v hvA hv_ex_Md
      have h_eq : 2 * (p_comp : ℝ) * τ = (10 * (p_comp : ℝ) * θ) * (N_star.card : ℝ) := by
        unfold τ; ring
      linarith
    by_cases h_half : A_sp.card ≤ A_comp.card
    · have h_r : (A_sp.card : ℝ) ≤ (A_comp.card : ℝ) := Nat.cast_le.mpr h_half
      refine ⟨A_comp, hA_comp_sub, by linarith,
        Finset.disjoint_of_subset_right hA_comp_sub hNA_disj,
        Or.inl (fun x hx v hv => F.symm ((Finset.mem_filter.mp hv).2 x hx))⟩
    · have h_r : (A_comp.card : ℝ) ≤ (A_sp.card : ℝ) := Nat.cast_le.mpr (by omega)
      refine ⟨A_sp, hA_sp_sub, by linarith,
        Finset.disjoint_of_subset_right hA_sp_sub hNA_disj,
        Or.inr hA_sp_sparse⟩

/-- **Lemma 12 (`single_u_level2_core_dichotomy`, Single-$u$ Level-2 Core Dichotomy in $\overline{P_{s+6}}$-Free Combs and Co-Combs)**:
Specialization of `general_depth_d_core_dichotomy` at depth $d = 1$. -/
theorem single_u_level2_core_dichotomy {F : SimpleGraph V} {S : Finset V}
    {ℓ s p_comp : ℕ} {w θ₂ : ℝ} {a : Fin ℓ → V} {B : Fin ℓ → Finset V}
    {stems : Fin ℓ → Fin s → V} {i j : Fin ℓ}
    (hij : i ≠ j) (hθ₂_pos : 0 < θ₂)
    (hfree : IsInducedSubgraphFree F (PkCompl (s + 6)))
    (hcomb : IsCombOrCoCombIn F S ℓ w a B)
    (hstems : HasPerHandleApexStems F S ℓ s a B stems)
    {M_sub N_T N_star : Finset V} {u : V}
    (hM_sub : M_sub ⊆ B i) (hu : u ∈ B j)
    (hNT_sub : N_T ⊆ neighborFinsetIn F u M_sub)
    (hNs_sub : N_star ⊆ N_T) (hNs_ne : N_star.Nonempty)
    (hNs_small : ∀ X : Finset V,
      IsProperModuleIn F N_T X → (X ∩ N_star).Nonempty →
      (X.card : ℝ) < 5 * θ₂ * (N_star.card : ℝ)) :
    let R := M_sub \ neighborFinsetIn F u M_sub
    (∃ D : Fin p_comp → Finset V,
      IsCompleteBlockadeIn F N_star p_comp (5 * θ₂ * (N_star.card : ℝ)) D) ∨
    (∃ A_star ⊆ R,
      (R.card : ℝ) / 2 ≤ (A_star.card : ℝ) ∧
      Disjoint N_star A_star ∧
      (IsCompletePair F N_star A_star ∨
       IsXSparseTo F A_star N_star (10 * (p_comp : ℝ) * θ₂))) := by
  intro R
  let M_seq : Fin 2 → Finset V := ![M_sub, N_T]
  have hfree1 : IsInducedSubgraphFree F (PkCompl (s + 5 + 1)) := hfree
  exact general_depth_d_core_dichotomy hij le_rfl hθ₂_pos hfree1 hcomb hstems
    (fun _ => u) M_seq hu hM_sub
    (fun c => by fin_cases c; exact hNT_sub)
    (fun c hc1 => by fin_cases c; omega)
    hNs_sub hNs_ne hNs_small
    (fun v hv => by
      obtain ⟨hvM, hv_notN⟩ := Finset.mem_sdiff.mp hv
      exact ⟨hvM, fun hadj => hv_notN ((mem_neighborFinsetIn_iff F u M_sub v).mpr ⟨hvM, hadj⟩)⟩)

/-!
## Section 10: Exponent Calculus, Regime A/B Recursive Resolution, and Inductive Proof of Theorem 7(1)

Formalizes the inductive depth-$r$ Stage-1 Comb/Co-Comb Dichotomy (Propositions 2 & 4, Lemma 13,
and Theorem 7(1) of `main.tex`, lines 581–670, 697–829, & 899–962):
- **Exponent Calculus (`splitTreeD`, `capExpE`, `treeParamR`)**: Proves the recursive growth bounds
  $D_r = 8 m \ge 64 r_{\mathrm{tree}}(r)$, $2 D_{r'} + 2 + 10 r \le \frac{5}{8} D_r$, and
  $E_{r'} + 2 D_{r'} + 12 r' D_r + 5 D_r + 100 r^2 + 4 \le E_r$ for $1 \le r' < r$.
- **Regime A vs. Regime B Recursive Call Resolver (`resolve_recursive_comb_call`)**: Passing
  $k' := \min(k_{\mathrm{comb}}, p_{\mathrm{cap}}) \ge 64$ and $L'_{\max} := k'$ to the induction
  hypothesis at depth $r' < r$ ensures that in **Regime A ($k_{\mathrm{comb}} \le p_{\mathrm{cap}}$)**,
  the width $w_{\mathrm{sub}} \ge \frac{|M_{\mathrm{base}}|}{16 (k')^2}$ is independent of $\eta_{\mathrm{out}}$
  and $p_{\mathrm{cap}}$ and yields either a **(Split-$D_r$ Type I)** active-leaf split or **(Global SplitOrCross)**,
  while in **Regime B ($k_{\mathrm{comb}} > p_{\mathrm{cap}}$)**, $L'_{\max} = k' = p_{\mathrm{cap}}$
  forces exact length $k = p_{\mathrm{cap}}$ and terminates globally via **(Global Cap)**.
- **Inductive Step (`stage1_comb_cocomb_dichotomy_strong_step`) and Unconditional Theorem 7(1)
  (`stage1_comb_cocomb_dichotomy_all_r`)**: Combines Step 1 (Level-1 Gallai core extraction),
  Step 2 (depth-$(r-1)$ recursive cutter-chain split `single_u_depth_r_pred_split`), and Step 3
  (union-pool $(s+1)$-stem promotion vs. Lemma 11 bipartite double-counting) inside an active-leaf
  split tree $\mathcal{T}_i$ on each tooth $B_i$.
-/

/-- Tree parameter $r_{\mathrm{tree}}(r)$ for `ActiveLeafSplitTree` at depth $r$:
equals $1$ when $r \le 2$ (where $D_2 = 64 = 64 \cdot 1$) and $r$ when $r \ge 3$ (where $D_r = 256 \cdot 8^{r-3} \ge 64 r$). -/
def treeParamR (r : ℕ) : ℕ :=
  if r ≤ 2 then 1 else r

@[simp]
lemma splitTreeD_add_three (n : ℕ) : splitTreeD (n + 3) = 256 * 8 ^ n := rfl

/-- Divisibility and lower-bound properties of $D_r = 8 (D_r / 8)$ for $r \ge 2$. -/
lemma splitTreeD_eq_eight_mul (r : ℕ) (hr : 2 ≤ r) :
    splitTreeD r = 8 * (splitTreeD r / 8) ∧ 8 ≤ splitTreeD r / 8 ∧
    (3 ≤ r → 11 ≤ splitTreeD r / 8) := by
  rcases r with _ | _ | _ | n
  · omega
  · omega
  · decide
  · change splitTreeD (n + 3) = 8 * (splitTreeD (n + 3) / 8) ∧
      8 ≤ splitTreeD (n + 3) / 8 ∧ (3 ≤ n + 3 → 11 ≤ splitTreeD (n + 3) / 8)
    rw [splitTreeD_add_three]
    have h2 : (256 * 8 ^ n) / 8 = 32 * 8 ^ n := by omega
    have h3 : 1 ≤ 8 ^ n := Nat.one_le_pow n 8 (by omega)
    rw [h2]
    exact ⟨by omega, by omega, fun _ => by omega⟩

/-- Bounds $1 \le r_{\mathrm{tree}}(r) \le r$, $64 r_{\mathrm{tree}}(r) \le D_r$, and $25 r \le 60 r_{\mathrm{tree}}(r)$
for $r \ge 2$. -/
lemma treeParamR_bounds (r : ℕ) (hr : 2 ≤ r) :
    1 ≤ treeParamR r ∧ treeParamR r ≤ r ∧
    64 * treeParamR r ≤ splitTreeD r ∧ 25 * r ≤ 60 * treeParamR r := by
  by_cases hr2 : r = 2
  · subst hr2; decide
  · have hr3 : 3 ≤ r := by omega
    have h_tr : treeParamR r = r := if_neg (by omega)
    rw [h_tr]
    refine ⟨by omega, le_rfl, ?_, by omega⟩
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hr3
    rw [Nat.add_comm 3 n, splitTreeD_add_three]
    have h_ind : ∀ m : ℕ, 64 * (m + 3) ≤ 256 * 8 ^ m := by
      intro m; induction m with
      | zero => decide
      | succ k ih =>
        rw [Nat.pow_succ]
        omega
    exact h_ind n

/-- Monotonicity of the split-tree exponent sequence $D_r$ (`splitTreeD`). -/
lemma splitTreeD_mono {a b : ℕ} (hab : a ≤ b) : splitTreeD a ≤ splitTreeD b := by
  have h_step : ∀ n : ℕ, splitTreeD n ≤ splitTreeD (n + 1) := by
    intro n
    rcases n with _ | _ | _ | k
    · decide
    · decide
    · decide
    · change splitTreeD (k + 3) ≤ splitTreeD ((k + 1) + 3)
      rw [splitTreeD_add_three, splitTreeD_add_three, Nat.pow_succ]
      omega
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  clear hab
  induction d with
  | zero => rfl
  | succ d ih => exact le_trans ih (h_step (a + d))

/-- Monotonicity of the decoupled cap exponent $E_r = 8 r \cdot 16^r$ (`capExpE`). -/
lemma capExpE_mono {a b : ℕ} (hab : a ≤ b) : capExpE a ≤ capExpE b := by
  unfold capExpE
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 8 hab) (Nat.pow_le_pow_right (by omega) hab)

/-- Upper bound $D_r \le 16^{r-1}$ for all $r \ge 3$. -/
lemma splitTreeD_le_pow_sixteen (r : ℕ) (hr : 3 ≤ r) :
    splitTreeD r ≤ 16 ^ (r - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hr
  have h1 : 3 + n - 1 = n + 2 := by omega
  have h2 : splitTreeD (3 + n) = 256 * 8 ^ n := by
    rw [Nat.add_comm 3 n]; rfl
  rw [h1, h2, Nat.pow_add]
  have h_8_16 : 8 ^ n ≤ 16 ^ n := Nat.pow_le_pow_left (by omega) n
  have h_256 : 256 = 16 ^ 2 := by decide
  rw [h_256, Nat.mul_comm]
  exact Nat.mul_le_mul_right (16 ^ 2) h_8_16

/-- Quadratic-vs-exponential bound $100 r^2 + 4 \le 16^r$ for all $r \ge 4$. -/
lemma hundred_sq_add_four_le_pow_sixteen (r : ℕ) (hr : 4 ≤ r) :
    100 * r ^ 2 + 4 ≤ 16 ^ r := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hr
  induction n with
  | zero => decide
  | succ m ih =>
    have h_id : 100 * (4 + (m + 1)) ^ 2 + 4 +
        (1500 * m ^ 2 + 11800 * m + 23160) =
        16 * (100 * (4 + m) ^ 2 + 4) := by ring
    have h_pow : 16 ^ (4 + (m + 1)) = 16 * 16 ^ (4 + m) := by
      rw [show 4 + (m + 1) = (4 + m) + 1 by omega, Nat.pow_succ]; ring
    omega

/-- Master recursive cap-exponent inequality (`main.tex` line 900):
$E_{r'} + 2 D_{r'} + 12 r' D_r + 5 D_r + 100 r^2 + 4 \le E_r$ for $1 \le r' < r$ ($r \ge 2$). -/
lemma capExpE_recursive_bound (r r' : ℕ) (hr : 2 ≤ r) (hr'1 : 1 ≤ r') (hr'r : r' < r) :
    capExpE r' + 2 * splitTreeD r' + 12 * r' * splitTreeD r +
      5 * splitTreeD r + 100 * r ^ 2 + 4 ≤ capExpE r := by
  have hr'_le : r' ≤ r - 1 := by omega
  have h_mono : capExpE r' + 2 * splitTreeD r' + 12 * r' * splitTreeD r ≤
      capExpE (r - 1) + 2 * splitTreeD (r - 1) + 12 * (r - 1) * splitTreeD r := by
    have h1 := capExpE_mono hr'_le
    have h2 := splitTreeD_mono hr'_le
    have h3 : 12 * r' * splitTreeD r ≤ 12 * (r - 1) * splitTreeD r :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 12 hr'_le)
    omega
  have h_step1 : capExpE r' + 2 * splitTreeD r' + 12 * r' * splitTreeD r +
      5 * splitTreeD r + 100 * r ^ 2 + 4 ≤
      capExpE (r - 1) + 2 * splitTreeD (r - 1) + 12 * (r - 1) * splitTreeD r +
      5 * splitTreeD r + 100 * r ^ 2 + 4 := by omega
  refine le_trans h_step1 ?_
  rcases r with _ | _ | _ | _ | n
  · omega
  · omega
  · decide
  · decide
  · set r0 := n + 4
    have hr0_4 : 4 ≤ r0 := by omega
    have h_Dr : splitTreeD r0 ≤ 16 ^ (r0 - 1) := splitTreeD_le_pow_sixteen r0 (by omega)
    have h_Dr1 : 2 * splitTreeD (r0 - 1) ≤ 16 ^ (r0 - 1) := by
      have h1 := splitTreeD_le_pow_sixteen (r0 - 1) (by omega)
      have h2 : 16 ^ (r0 - 1) = 16 ^ (r0 - 1 - 1) * 16 := by
        conv_lhs => rw [show r0 - 1 = (r0 - 1 - 1) + 1 by omega, Nat.pow_succ]
      omega
    have h_100 : 100 * r0 ^ 2 + 4 ≤ 16 * 16 ^ (r0 - 1) := by
      have h1 := hundred_sq_add_four_le_pow_sixteen r0 hr0_4
      have h2 : 16 ^ r0 = 16 * 16 ^ (r0 - 1) := by
        conv_lhs => rw [show r0 = (r0 - 1) + 1 by omega, Nat.pow_succ]
        ring
      omega
    have h_Er1 : capExpE (r0 - 1) = (8 * r0 - 8) * 16 ^ (r0 - 1) := by
      unfold capExpE
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    have h_Er : capExpE r0 = (128 * r0) * 16 ^ (r0 - 1) := by
      unfold capExpE
      conv_lhs => rw [show r0 = (r0 - 1) + 1 by omega, Nat.pow_succ]
      have h_id : 8 * ((r0 - 1) + 1) * (16 ^ (r0 - 1) * 16) = (128 * ((r0 - 1) + 1)) * 16 ^ (r0 - 1) := by ring
      simpa [show (r0 - 1) + 1 = r0 by omega] using h_id
    have h_mid : 12 * (r0 - 1) * splitTreeD r0 + 5 * splitTreeD r0 ≤
        (12 * r0 - 7) * 16 ^ (r0 - 1) := by
      have h_coef : 12 * (r0 - 1) + 5 = 12 * r0 - 7 := by omega
      calc 12 * (r0 - 1) * splitTreeD r0 + 5 * splitTreeD r0
          = (12 * (r0 - 1) + 5) * splitTreeD r0 := by ring
        _ = (12 * r0 - 7) * splitTreeD r0 := by rw [h_coef]
        _ ≤ (12 * r0 - 7) * 16 ^ (r0 - 1) := Nat.mul_le_mul_left _ h_Dr
    have h_sum_coef : (8 * r0 - 8) + 1 + (12 * r0 - 7) + 16 ≤ 128 * r0 := by omega
    calc capExpE (r0 - 1) + 2 * splitTreeD (r0 - 1) + 12 * (r0 - 1) * splitTreeD r0 +
          5 * splitTreeD r0 + 100 * r0 ^ 2 + 4
        ≤ (8 * r0 - 8) * 16 ^ (r0 - 1) + 16 ^ (r0 - 1) +
            (12 * r0 - 7) * 16 ^ (r0 - 1) + 16 * 16 ^ (r0 - 1) := by omega
      _ = ((8 * r0 - 8) + 1 + (12 * r0 - 7) + 16) * 16 ^ (r0 - 1) := by ring
      _ ≤ (128 * r0) * 16 ^ (r0 - 1) := Nat.mul_le_mul_right _ h_sum_coef
      _ = capExpE r0 := h_Er.symm

/-- Type-I split exponent bound $2 D_{r'} + 2 + 10 r \le \frac{5}{8} D_r$ for $r' < r$ ($r \ge 2$). -/
lemma splitTreeD_type1_exp_bound (r r' : ℕ) (hr : 2 ≤ r) (hr'r : r' < r) :
    2 * splitTreeD r' + 2 + 10 * r ≤ 5 * (splitTreeD r / 8) := by
  have hr'_le : r' ≤ r - 1 := by omega
  have h_mono : splitTreeD r' ≤ splitTreeD (r - 1) := splitTreeD_mono hr'_le
  refine le_trans (by omega : 2 * splitTreeD r' + 2 + 10 * r ≤ 2 * splitTreeD (r - 1) + 2 + 10 * r) ?_
  rcases r with _ | _ | _ | _ | n
  · omega
  · omega
  · decide
  · decide
  · have h_Dr1 : splitTreeD (n + 3) = 256 * 8 ^ n := rfl
    have h_Dr : splitTreeD (n + 4) / 8 = 256 * 8 ^ n := by
      change (256 * 8 ^ (n + 1)) / 8 = 256 * 8 ^ n
      rw [Nat.pow_succ]; omega
    rw [show n + 4 - 1 = n + 3 by omega, h_Dr1, h_Dr]
    have h_ind : ∀ m : ℕ, 10 * (m + 4) + 2 ≤ 3 * (256 * 8 ^ m) := by
      intro m; induction m with
      | zero => decide
      | succ k ih =>
        rw [Nat.pow_succ]; omega
    have := h_ind n
    omega

/-- Restricting an $(\ell, w)$-comb or co-comb and its per-handle $s$-stems to the first $k' \le \ell$ pairs. -/
theorem restrict_combOrCoComb_and_stems {F : SimpleGraph V} {S : Finset V}
    {ℓ k' s : ℕ} {w : ℝ} {a : Fin ℓ → V} {B : Fin ℓ → Finset V}
    {stems : Fin ℓ → Fin s → V} (hk' : k' ≤ ℓ)
    (hcomb : IsCombOrCoCombIn F S ℓ w a B)
    (hstems : HasPerHandleApexStems F S ℓ s a B stems) :
    let a' : Fin k' → V := fun i => a (Fin.castLE hk' i)
    let B' : Fin k' → Finset V := fun i => B (Fin.castLE hk' i)
    let stems' : Fin k' → Fin s → V := fun i => stems (Fin.castLE hk' i)
    IsCombOrCoCombIn F S k' w a' B' ∧
    HasPerHandleApexStems F S k' s a' B' stems' ∧
    Finset.univ.biUnion B' ⊆ Finset.univ.biUnion B := by
  intro a' B' stems'
  have h_inj : Function.Injective (Fin.castLE hk') := Fin.castLE_injective hk'
  refine ⟨?_, ?_, ?_⟩
  · rcases hcomb with hc | hco
    · left
      exact
        { is_blockade := hc.is_blockade.restrict hk'
          apex_in_ambient := fun i => hc.apex_in_ambient _
          apex_injective := hc.apex_injective.comp h_inj
          apex_disjoint_blocks := fun i j => hc.apex_disjoint_blocks _ _
          apex_complete_own := fun i => hc.apex_complete_own _
          apex_anticomplete_other := fun i j hij => hc.apex_anticomplete_other _ _ (h_inj.ne hij) }
    · right
      exact
        { is_blockade := hco.is_blockade.restrict hk'
          apex_in_ambient := fun i => hco.apex_in_ambient _
          apex_injective := hco.apex_injective.comp h_inj
          apex_disjoint_blocks := fun i j => hco.apex_disjoint_blocks _ _
          apex_anticomplete_own := fun i => hco.apex_anticomplete_own _
          apex_complete_other := fun i j hij => hco.apex_complete_other _ _ (h_inj.ne hij) }
  · exact
      { stem_pos := hstems.stem_pos
        stem_in_ambient := fun i => hstems.stem_in_ambient _
        stem_injective := fun i => hstems.stem_injective _
        stem_not_handle := fun i j => hstems.stem_not_handle _ _
        stem_not_in_blocks := fun i j => hstems.stem_not_in_blocks _ _
        stem_induced_path_compl := fun i => hstems.stem_induced_path_compl _
        stem_last_nonadj_handle := fun i => hstems.stem_last_nonadj_handle _
        stem_init_adj_handle := fun i => hstems.stem_init_adj_handle _
        stem_complete_to_blocks := fun i q => hstems.stem_complete_to_blocks _ _ }
  · intro x hx
    obtain ⟨i, _, hxi⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_biUnion.mpr ⟨Fin.castLE hk' i, Finset.mem_univ _, hxi⟩

/-- Rewrites $a^{-(n : \mathbb{R})} = (a^n)^{-1}$ for $a \ge 0$ and $n \in \mathbb{N}$. -/
lemma rpow_neg_natCast {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    a ^ (-(n : ℝ)) = (a ^ n)⁻¹ := by
  rw [Real.rpow_neg ha, Real.rpow_natCast]

/-- Exponent bound $2 D_r \le E_r$ for all $r \ge 1$. -/
lemma two_mul_splitTreeD_le_capExpE (r : ℕ) (hr : 1 ≤ r) :
    2 * splitTreeD r ≤ capExpE r := by
  rcases r with _ | _ | _ | n
  · omega
  · decide
  · decide
  · change 2 * splitTreeD (n + 3) ≤ capExpE (n + 3)
    have h_Dr : splitTreeD (n + 3) ≤ 16 ^ (n + 2) := splitTreeD_le_pow_sixteen (n + 3) (by omega)
    unfold capExpE
    have h_pow : 16 ^ (n + 3) = 16 * 16 ^ (n + 2) := by rw [Nat.pow_succ]; ring
    rw [h_pow]
    nlinarith

/-- Width precondition bound for recursive calls in Step 2 and Step 3a of Theorem 7(1):
`combMinWidth r' η₀ p_cap ≤ w_sub`. -/
lemma combMinWidth_recursive_le {r r' p_cap : ℕ} {η_out η₀ w w_sub : ℝ}
    (hr : 2 ≤ r) (hr'1 : 1 ≤ r') (hr'r : r' < r) (hp_cap : 64 ≤ p_cap)
    (hη_pos : 0 < η_out) (hη_ub : η_out ≤ 1)
    (hη₀_pos : 0 < η₀)
    (hη₀_lb : (2 : ℝ)⁻¹ ^ (120 * r + 2) * (p_cap : ℝ)⁻¹ ^ (4 * splitTreeD r) * η_out ≤ η₀)
    (hw_ge : combMinWidth r η_out p_cap ≤ w)
    (hw_sub_lb : (2 : ℝ)⁻¹ ^ (145 * r + 10) * (p_cap : ℝ)⁻¹ ^ (5 * splitTreeD r + 2) * η_out * w ≤ w_sub) :
    combMinWidth r' η₀ p_cap ≤ w_sub := by
  have hp_r : (64 : ℝ) ≤ (p_cap : ℝ) := Nat.ofNat_le_cast.mpr hp_cap
  have hp_pos : (0 : ℝ) < (p_cap : ℝ) := by linarith
  have hη_inv_ge1 : 1 ≤ η_out⁻¹ := one_le_inv₀ hη_pos |>.mpr hη_ub
  unfold combMinWidth at hw_ge ⊢
  rw [show -(3 * (r : ℝ)) = -(((3 * r : ℕ) : ℝ)) by push_cast; ring,
    rpow_neg_natCast (le_of_lt hη_pos) (3 * r), ← inv_pow] at hw_ge
  rw [show -(3 * (r' : ℝ)) = -(((3 * r' : ℕ) : ℝ)) by push_cast; ring,
    rpow_neg_natCast (le_of_lt hη₀_pos) (3 * r'), ← inv_pow]
  -- Bound η₀⁻¹ ≤ 2^(120*r+2) * p_cap^(4*D_r) * η_out⁻¹
  have hη₀_inv_ub : η₀⁻¹ ≤ (2 : ℝ) ^ (120 * r + 2) * (p_cap : ℝ) ^ (4 * splitTreeD r) * η_out⁻¹ := by
    have h_lhs_pos : 0 < (2 : ℝ)⁻¹ ^ (120 * r + 2) * (p_cap : ℝ)⁻¹ ^ (4 * splitTreeD r) * η_out := by positivity
    have h1 := inv_anti₀ h_lhs_pos hη₀_lb
    calc η₀⁻¹ ≤ ((2 : ℝ)⁻¹ ^ (120 * r + 2) * (p_cap : ℝ)⁻¹ ^ (4 * splitTreeD r) * η_out)⁻¹ := h1
      _ = (2 : ℝ) ^ (120 * r + 2) * (p_cap : ℝ) ^ (4 * splitTreeD r) * η_out⁻¹ := by
          rw [mul_inv_rev, mul_inv_rev, inv_pow, inv_inv, inv_pow, inv_inv]; ring
  have h_η₀_3r' : (η₀⁻¹) ^ (3 * r') ≤
      (2 : ℝ) ^ ((120 * r + 2) * (3 * r')) *
      (p_cap : ℝ) ^ (12 * r' * splitTreeD r) * (η_out⁻¹) ^ (3 * r - 1) := by
    have h1 := pow_le_pow_left₀ (by positivity) hη₀_inv_ub (3 * r')
    have h_id : ((2 : ℝ) ^ (120 * r + 2) * (p_cap : ℝ) ^ (4 * splitTreeD r) * η_out⁻¹) ^ (3 * r') =
        (2 : ℝ) ^ ((120 * r + 2) * (3 * r')) *
        (p_cap : ℝ) ^ (12 * r' * splitTreeD r) * (η_out⁻¹) ^ (3 * r') := by
      rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
      congr 2; rw [show 4 * splitTreeD r * (3 * r') = 12 * r' * splitTreeD r by ring]
    rw [h_id] at h1
    have h_3r : (η_out⁻¹) ^ (3 * r') ≤ (η_out⁻¹) ^ (3 * r - 1) :=
      pow_le_pow_right₀ hη_inv_ge1 (by omega)
    exact le_trans h1 (mul_le_mul_of_nonneg_left h_3r (by positivity))
  -- Factor p_cap^(100 * r^2) ≥ 64^(100 * r^2) = 2^(600 * r^2)
  have hp_to_2 : (2 : ℝ) ^ (600 * r ^ 2) ≤ (p_cap : ℝ) ^ (100 * r ^ 2) := by
    have h64 : (2 : ℝ) ^ 6 ≤ (p_cap : ℝ) := by norm_num at hp_r ⊢; exact hp_r
    have h1 := pow_le_pow_left₀ (by positivity) h64 (100 * r ^ 2)
    rwa [← pow_mul, show 6 * (100 * r ^ 2) = 600 * r ^ 2 by ring] at h1
  -- Exponent comparison on base 2: 400*(r')^2 + (120*r+2)*(3*r') + (145*r+10) ≤ 400*r^2 + 600*r^2
  have h_exp2 : 400 * r' ^ 2 + (120 * r + 2) * (3 * r') + (145 * r + 10) ≤
      400 * r ^ 2 + 600 * r ^ 2 := by
    have hr'_le : r' ≤ r - 1 := by omega
    have h_r'2 : r' ^ 2 ≤ (r - 1) ^ 2 := Nat.pow_le_pow_left hr'_le 2
    have h_3r' : (120 * r + 2) * (3 * r') ≤ (120 * r + 2) * (3 * (r - 1)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 3 hr'_le)
    have h_quad : 400 * (r - 1) ^ 2 + (120 * r + 2) * (3 * (r - 1)) + (145 * r + 10) ≤
        1000 * r ^ 2 := by
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hr
      have h_id : 400 * (2 + n - 1) ^ 2 + (120 * (2 + n) + 2) * (3 * (2 + n - 1)) +
          (145 * (2 + n) + 10) + (240 * n ^ 2 + 1969 * n + 2574) = 1000 * (2 + n) ^ 2 := by
        rw [show 2 + n - 1 = n + 1 by omega]; ring
      omega
    omega
  have h_2_pow : (2 : ℝ) ^ (400 * r' ^ 2) * (2 : ℝ) ^ ((120 * r + 2) * (3 * r')) ≤
      (2 : ℝ) ^ (400 * r ^ 2) * (2 : ℝ)⁻¹ ^ (145 * r + 10) * (p_cap : ℝ) ^ (100 * r ^ 2) := by
    have h1 : (2 : ℝ) ^ (400 * r' ^ 2 + (120 * r + 2) * (3 * r') + (145 * r + 10)) ≤
        (2 : ℝ) ^ (400 * r ^ 2 + 600 * r ^ 2) :=
      pow_le_pow_right₀ (by norm_num) h_exp2
    rw [pow_add (a := 2) (m := 400 * r' ^ 2 + (120 * r + 2) * (3 * r')) (n := 145 * r + 10),
      pow_add (a := 2) (m := 400 * r' ^ 2) (n := (120 * r + 2) * (3 * r')),
      pow_add (a := 2) (m := 400 * r ^ 2) (n := 600 * r ^ 2)] at h1
    have h2 : (2 : ℝ) ^ (400 * r' ^ 2) * (2 : ℝ) ^ ((120 * r + 2) * (3 * r')) * (2 : ℝ) ^ (145 * r + 10) ≤
        (2 : ℝ) ^ (400 * r ^ 2) * (p_cap : ℝ) ^ (100 * r ^ 2) :=
      le_trans h1 (mul_le_mul_of_nonneg_left hp_to_2 (by positivity))
    have h3 := mul_le_mul_of_nonneg_right h2 (show (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ (145 * r + 10) by positivity)
    have h_canc : (2 : ℝ) ^ (145 * r + 10) * (2 : ℝ)⁻¹ ^ (145 * r + 10) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ (by norm_num), one_pow]
    calc (2 : ℝ) ^ (400 * r' ^ 2) * (2 : ℝ) ^ ((120 * r + 2) * (3 * r'))
        = (2 : ℝ) ^ (400 * r' ^ 2) * (2 : ℝ) ^ ((120 * r + 2) * (3 * r')) *
            ((2 : ℝ) ^ (145 * r + 10) * (2 : ℝ)⁻¹ ^ (145 * r + 10)) := by rw [h_canc, mul_one]
      _ = (2 : ℝ) ^ (400 * r' ^ 2) * (2 : ℝ) ^ ((120 * r + 2) * (3 * r')) *
            (2 : ℝ) ^ (145 * r + 10) * (2 : ℝ)⁻¹ ^ (145 * r + 10) := by ring
      _ ≤ (2 : ℝ) ^ (400 * r ^ 2) * (p_cap : ℝ) ^ (100 * r ^ 2) * (2 : ℝ)⁻¹ ^ (145 * r + 10) := h3
      _ = (2 : ℝ) ^ (400 * r ^ 2) * (2 : ℝ)⁻¹ ^ (145 * r + 10) * (p_cap : ℝ) ^ (100 * r ^ 2) := by ring
  -- Exponent comparison on p_cap
  have h_exp_p := capExpE_recursive_bound r r' hr hr'1 hr'r
  have h_p_pow : (p_cap : ℝ) ^ (100 * r ^ 2) * (p_cap : ℝ) ^ (12 * r' * splitTreeD r) *
      (p_cap : ℝ) ^ (capExpE r' + 2 * splitTreeD r') ≤
      (p_cap : ℝ)⁻¹ ^ (5 * splitTreeD r + 2) * (p_cap : ℝ) ^ (capExpE r + 2 * splitTreeD r) := by
    have h_le : (100 * r ^ 2 + 12 * r' * splitTreeD r + (capExpE r' + 2 * splitTreeD r')) +
        (5 * splitTreeD r + 2) ≤ capExpE r + 2 * splitTreeD r := by omega
    have h1 : (p_cap : ℝ) ^ ((100 * r ^ 2 + 12 * r' * splitTreeD r + (capExpE r' + 2 * splitTreeD r')) +
        (5 * splitTreeD r + 2)) ≤ (p_cap : ℝ) ^ (capExpE r + 2 * splitTreeD r) :=
      pow_le_pow_right₀ (by linarith) h_le
    rw [pow_add, pow_add, pow_add] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ (p_cap : ℝ)⁻¹ ^ (5 * splitTreeD r + 2) by positivity)
    have h_canc : (p_cap : ℝ)⁻¹ ^ (5 * splitTreeD r + 2) * (p_cap : ℝ) ^ (5 * splitTreeD r + 2) = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt hp_pos), one_pow]
    calc (p_cap : ℝ) ^ (100 * r ^ 2) * (p_cap : ℝ) ^ (12 * r' * splitTreeD r) *
          (p_cap : ℝ) ^ (capExpE r' + 2 * splitTreeD r')
        = ((p_cap : ℝ)⁻¹ ^ (5 * splitTreeD r + 2) * (p_cap : ℝ) ^ (5 * splitTreeD r + 2)) *
          ((p_cap : ℝ) ^ (100 * r ^ 2) * (p_cap : ℝ) ^ (12 * r' * splitTreeD r) *
          (p_cap : ℝ) ^ (capExpE r' + 2 * splitTreeD r')) := by rw [h_canc, one_mul]
      _ = (p_cap : ℝ)⁻¹ ^ (5 * splitTreeD r + 2) *
          ((p_cap : ℝ) ^ (100 * r ^ 2) * (p_cap : ℝ) ^ (12 * r' * splitTreeD r) *
          (p_cap : ℝ) ^ (capExpE r' + 2 * splitTreeD r') * (p_cap : ℝ) ^ (5 * splitTreeD r + 2)) := by ring
      _ ≤ (p_cap : ℝ)⁻¹ ^ (5 * splitTreeD r + 2) * (p_cap : ℝ) ^ (capExpE r + 2 * splitTreeD r) := h2
  -- Combine all factors
  have h_η_canc : η_out * (η_out⁻¹) ^ (3 * r) = (η_out⁻¹) ^ (3 * r - 1) := by
    calc η_out * (η_out⁻¹) ^ (3 * r)
        = η_out * ((η_out⁻¹) ^ (3 * r - 1) * η_out⁻¹) := by
          conv_lhs => rw [show 3 * r = (3 * r - 1) + 1 by omega, pow_succ]
      _ = (η_out⁻¹) ^ (3 * r - 1) * (η_out * η_out⁻¹) := by ring
      _ = (η_out⁻¹) ^ (3 * r - 1) := by rw [mul_inv_cancel₀ (ne_of_gt hη_pos), mul_one]
  calc (2 : ℝ) ^ (400 * r' ^ 2) * (η₀⁻¹) ^ (3 * r') * (p_cap : ℝ) ^ (capExpE r' + 2 * splitTreeD r')
      ≤ (2 : ℝ) ^ (400 * r' ^ 2) *
          ((2 : ℝ) ^ ((120 * r + 2) * (3 * r')) * (p_cap : ℝ) ^ (12 * r' * splitTreeD r) *
           (η_out⁻¹) ^ (3 * r - 1)) *
          (p_cap : ℝ) ^ (capExpE r' + 2 * splitTreeD r') :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h_η₀_3r' (by positivity)) (by positivity)
    _ = ((2 : ℝ) ^ (400 * r' ^ 2) * (2 : ℝ) ^ ((120 * r + 2) * (3 * r'))) *
          (p_cap : ℝ) ^ (12 * r' * splitTreeD r) *
          (p_cap : ℝ) ^ (capExpE r' + 2 * splitTreeD r') * (η_out⁻¹) ^ (3 * r - 1) := by ring
    _ ≤ ((2 : ℝ) ^ (400 * r ^ 2) * (2 : ℝ)⁻¹ ^ (145 * r + 10) * (p_cap : ℝ) ^ (100 * r ^ 2)) *
          (p_cap : ℝ) ^ (12 * r' * splitTreeD r) *
          (p_cap : ℝ) ^ (capExpE r' + 2 * splitTreeD r') * (η_out⁻¹) ^ (3 * r - 1) := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right h_2_pow (by positivity)) (by positivity)) (by positivity)
    _ = (2 : ℝ) ^ (400 * r ^ 2) * (2 : ℝ)⁻¹ ^ (145 * r + 10) * (η_out⁻¹) ^ (3 * r - 1) *
          ((p_cap : ℝ) ^ (100 * r ^ 2) * (p_cap : ℝ) ^ (12 * r' * splitTreeD r) *
           (p_cap : ℝ) ^ (capExpE r' + 2 * splitTreeD r')) := by ring
    _ ≤ (2 : ℝ) ^ (400 * r ^ 2) * (2 : ℝ)⁻¹ ^ (145 * r + 10) * (η_out⁻¹) ^ (3 * r - 1) *
          ((p_cap : ℝ)⁻¹ ^ (5 * splitTreeD r + 2) * (p_cap : ℝ) ^ (capExpE r + 2 * splitTreeD r)) :=
        mul_le_mul_of_nonneg_left h_p_pow (by positivity)
    _ = (2 : ℝ)⁻¹ ^ (145 * r + 10) * (p_cap : ℝ)⁻¹ ^ (5 * splitTreeD r + 2) *
          (η_out * (η_out⁻¹) ^ (3 * r)) *
          ((2 : ℝ) ^ (400 * r ^ 2) * (p_cap : ℝ) ^ (capExpE r + 2 * splitTreeD r)) := by
        rw [h_η_canc]; ring
    _ = (2 : ℝ)⁻¹ ^ (145 * r + 10) * (p_cap : ℝ)⁻¹ ^ (5 * splitTreeD r + 2) * η_out *
          ((2 : ℝ) ^ (400 * r ^ 2) * (η_out⁻¹) ^ (3 * r) * (p_cap : ℝ) ^ (capExpE r + 2 * splitTreeD r)) := by ring
    _ ≤ (2 : ℝ)⁻¹ ^ (145 * r + 10) * (p_cap : ℝ)⁻¹ ^ (5 * splitTreeD r + 2) * η_out * w :=
        mul_le_mul_of_nonneg_left hw_ge (by positivity)
    _ ≤ w_sub := hw_sub_lb

/-- Cap width bound for recursive calls in Step 2 and Step 3a of Theorem 7(1):
`2^(-200 r^2) η_out^r p_cap^(-E_r) w ≤ 2^(-200 (r')^2) η₀^r' p_cap^(-E_r') w_sub`. -/
lemma cap_width_recursive_le {r r' p_cap : ℕ} {η_out η₀ w w_sub : ℝ}
    (hr : 2 ≤ r) (hr'1 : 1 ≤ r') (hr'r : r' < r) (hp_cap : 64 ≤ p_cap)
    (hη_pos : 0 < η_out) (hw_pos : 0 ≤ w)
    (hw_sub_cap :
      (2 : ℝ)⁻¹ ^ ((120 * r + 2) * (r - 1) + 25 * r + 10) *
      (p_cap : ℝ)⁻¹ ^ ((4 * r' + 5) * splitTreeD r + 2) *
      η_out ^ r * w ≤ η₀ ^ r' * w_sub) :
    (2 : ℝ) ^ (-(200 * (r : ℝ) ^ 2)) * η_out ^ r * (p_cap : ℝ) ^ (-(capExpE r : ℝ)) * w ≤
      (2 : ℝ) ^ (-(200 * (r' : ℝ) ^ 2)) * η₀ ^ r' * (p_cap : ℝ) ^ (-(capExpE r' : ℝ)) * w_sub := by
  have hp_r : (64 : ℝ) ≤ (p_cap : ℝ) := Nat.ofNat_le_cast.mpr hp_cap
  have hp_pos : (0 : ℝ) < (p_cap : ℝ) := by linarith
  rw [show -(200 * (r : ℝ) ^ 2) = -(((200 * r ^ 2 : ℕ) : ℝ)) by push_cast; ring,
    rpow_neg_natCast (by norm_num) (200 * r ^ 2), ← inv_pow,
    show -(capExpE r : ℝ) = -(((capExpE r : ℕ) : ℝ)) by rfl,
    rpow_neg_natCast (le_of_lt hp_pos) (capExpE r), ← inv_pow,
    show -(200 * (r' : ℝ) ^ 2) = -(((200 * r' ^ 2 : ℕ) : ℝ)) by push_cast; ring,
    rpow_neg_natCast (by norm_num) (200 * r' ^ 2), ← inv_pow,
    show -(capExpE r' : ℝ) = -(((capExpE r' : ℕ) : ℝ)) by rfl,
    rpow_neg_natCast (le_of_lt hp_pos) (capExpE r'), ← inv_pow]
  -- Absorb 2^(-((120*r+2)*(r-1) + 25*r + 10)) into p_cap^(-30*r^2) since p_cap^30 ≥ 2^180
  have h_2_exp : (120 * r + 2) * (r - 1) + 25 * r + 10 ≤ 180 * r ^ 2 := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hr
    have h_id : (120 * (2 + n) + 2) * (2 + n - 1) + 25 * (2 + n) + 10 +
        (60 * n ^ 2 + 333 * n + 418) = 180 * (2 + n) ^ 2 := by
      rw [show 2 + n - 1 = n + 1 by omega]; ring
    omega
  have h_p30_2 : (p_cap : ℝ)⁻¹ ^ (30 * r ^ 2) ≤ (2 : ℝ)⁻¹ ^ ((120 * r + 2) * (r - 1) + 25 * r + 10) := by
    have h64 : (p_cap : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ ^ 6 := by
      have : (2 : ℝ) ^ 6 ≤ (p_cap : ℝ) := by norm_num at hp_r ⊢; exact hp_r
      rw [inv_pow]
      exact inv_anti₀ (by positivity) this
    have h1 := pow_le_pow_left₀ (by positivity) h64 (30 * r ^ 2)
    rw [← pow_mul, show 6 * (30 * r ^ 2) = 180 * r ^ 2 by ring] at h1
    have h2 : (2 : ℝ)⁻¹ ^ (180 * r ^ 2) ≤ (2 : ℝ)⁻¹ ^ ((120 * r + 2) * (r - 1) + 25 * r + 10) :=
      pow_le_pow_of_le_one (by positivity) (by norm_num) h_2_exp
    exact le_trans h1 h2
  have h_200_le : (2 : ℝ)⁻¹ ^ (200 * r ^ 2) ≤ (2 : ℝ)⁻¹ ^ (200 * r' ^ 2) := by
    have : 200 * r' ^ 2 ≤ 200 * r ^ 2 :=
      Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left (le_of_lt hr'r) 2)
    exact pow_le_pow_of_le_one (by positivity) (by norm_num) this
  have h_p_exp : capExpE r' + ((4 * r' + 5) * splitTreeD r + 2) + 30 * r ^ 2 ≤ capExpE r := by
    have h_rec := capExpE_recursive_bound r r' hr hr'1 hr'r
    have h_4_12 : (4 * r' + 5) * splitTreeD r ≤ 12 * r' * splitTreeD r + 5 * splitTreeD r := by
      calc (4 * r' + 5) * splitTreeD r
          ≤ (12 * r' + 5) * splitTreeD r := Nat.mul_le_mul_right _ (by omega)
        _ = 12 * r' * splitTreeD r + 5 * splitTreeD r := by ring
    omega
  have h_p_pow : (p_cap : ℝ)⁻¹ ^ (capExpE r) ≤
      (p_cap : ℝ)⁻¹ ^ (capExpE r') *
      (p_cap : ℝ)⁻¹ ^ ((4 * r' + 5) * splitTreeD r + 2) *
      (p_cap : ℝ)⁻¹ ^ (30 * r ^ 2) := by
    rw [← pow_add, ← pow_add]
    have hp_inv_le1 : (p_cap : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    exact pow_le_pow_of_le_one (by positivity) hp_inv_le1 h_p_exp
  calc (2 : ℝ)⁻¹ ^ (200 * r ^ 2) * η_out ^ r * (p_cap : ℝ)⁻¹ ^ (capExpE r) * w
      ≤ (2 : ℝ)⁻¹ ^ (200 * r' ^ 2) * η_out ^ r *
          ((p_cap : ℝ)⁻¹ ^ (capExpE r') *
           (p_cap : ℝ)⁻¹ ^ ((4 * r' + 5) * splitTreeD r + 2) *
           (p_cap : ℝ)⁻¹ ^ (30 * r ^ 2)) * w := by
        refine mul_le_mul_of_nonneg_right ?_ hw_pos
        exact mul_le_mul (mul_le_mul_of_nonneg_right h_200_le (by positivity))
          h_p_pow (by positivity) (by positivity)
    _ ≤ (2 : ℝ)⁻¹ ^ (200 * r' ^ 2) * η_out ^ r *
          ((p_cap : ℝ)⁻¹ ^ (capExpE r') *
           (p_cap : ℝ)⁻¹ ^ ((4 * r' + 5) * splitTreeD r + 2) *
           (2 : ℝ)⁻¹ ^ ((120 * r + 2) * (r - 1) + 25 * r + 10)) * w := by
        refine mul_le_mul_of_nonneg_right ?_ hw_pos
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left h_p30_2 (by positivity)
    _ = (2 : ℝ)⁻¹ ^ (200 * r' ^ 2) * (p_cap : ℝ)⁻¹ ^ (capExpE r') *
          ((2 : ℝ)⁻¹ ^ ((120 * r + 2) * (r - 1) + 25 * r + 10) *
           (p_cap : ℝ)⁻¹ ^ ((4 * r' + 5) * splitTreeD r + 2) *
           η_out ^ r * w) := by ring
    _ ≤ (2 : ℝ)⁻¹ ^ (200 * r' ^ 2) * (p_cap : ℝ)⁻¹ ^ (capExpE r') * (η₀ ^ r' * w_sub) :=
        mul_le_mul_of_nonneg_left hw_sub_cap (by positivity)
    _ = (2 : ℝ)⁻¹ ^ (200 * r' ^ 2) * η₀ ^ r' * (p_cap : ℝ)⁻¹ ^ (capExpE r') * w_sub := by ring

/-- At $k = p_{\mathrm{cap}}$, the split-or-cross width $\frac{w_{\mathrm{sub}}}{2^{60 r'} p_{\mathrm{cap}}^{2 D_{r'}}}$
is at least the cap width $2^{-200(r')^2} \eta_0^{r'} p_{\mathrm{cap}}^{-E_{r'}} w_{\mathrm{sub}}$. -/
lemma split_or_cross_at_pcap_ge_cap_width {r' p_cap : ℕ} {η₀ w_sub : ℝ}
    (hr'1 : 1 ≤ r') (hp_cap : 64 ≤ p_cap)
    (hη₀_pos : 0 < η₀) (hη₀_ub : η₀ ≤ 1) (hw_sub_nn : 0 ≤ w_sub) :
    (2 : ℝ) ^ (-(200 * (r' : ℝ) ^ 2)) * η₀ ^ r' * (p_cap : ℝ) ^ (-(capExpE r' : ℝ)) * w_sub ≤
      w_sub / ((2 : ℝ) ^ (60 * r') * (p_cap : ℝ) ^ (2 * splitTreeD r')) := by
  have hp_r : (64 : ℝ) ≤ (p_cap : ℝ) := Nat.ofNat_le_cast.mpr hp_cap
  have hp_pos : (0 : ℝ) < (p_cap : ℝ) := by linarith
  rw [show -(200 * (r' : ℝ) ^ 2) = -(((200 * r' ^ 2 : ℕ) : ℝ)) by push_cast; ring,
    rpow_neg_natCast (by norm_num) (200 * r' ^ 2), ← inv_pow,
    show -(capExpE r' : ℝ) = -(((capExpE r' : ℕ) : ℝ)) by rfl,
    rpow_neg_natCast (le_of_lt hp_pos) (capExpE r'), ← inv_pow]
  have h1 : (2 : ℝ)⁻¹ ^ (200 * r' ^ 2) ≤ (2 : ℝ)⁻¹ ^ (60 * r') := by
    have : 60 * r' ≤ 200 * r' ^ 2 := by nlinarith
    exact pow_le_pow_of_le_one (by positivity) (by norm_num) this
  have h2 : η₀ ^ r' ≤ 1 := pow_le_one₀ (le_of_lt hη₀_pos) hη₀_ub
  have h3 : (p_cap : ℝ)⁻¹ ^ (capExpE r') ≤ (p_cap : ℝ)⁻¹ ^ (2 * splitTreeD r') := by
    have hp_inv_le1 : (p_cap : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    exact pow_le_pow_of_le_one (by positivity) hp_inv_le1 (two_mul_splitTreeD_le_capExpE r' hr'1)
  calc (2 : ℝ)⁻¹ ^ (200 * r' ^ 2) * η₀ ^ r' * (p_cap : ℝ)⁻¹ ^ (capExpE r') * w_sub
      ≤ (2 : ℝ)⁻¹ ^ (60 * r') * 1 * (p_cap : ℝ)⁻¹ ^ (2 * splitTreeD r') * w_sub := by
        refine mul_le_mul_of_nonneg_right ?_ hw_sub_nn
        exact mul_le_mul (mul_le_mul h1 h2 (by positivity) (by positivity)) h3 (by positivity) (by positivity)
    _ = w_sub / ((2 : ℝ) ^ (60 * r') * (p_cap : ℝ) ^ (2 * splitTreeD r')) := by
        rw [inv_pow, inv_pow]; ring

/-- **Unified Regime A vs. Regime B Recursive Call Resolver** (`resolve_recursive_comb_call`):
Given an induction hypothesis `IH : Stage1CombCoCombDichotomyStrongAt r'` ($1 \le r' < r$, $r' + d + 1 = r$)
and a promoted $(k_{\mathrm{comb}}, w_{\mathrm{sub}})$-comb or co-comb inside $M_{\mathrm{base}} \subseteq W_z \subseteq U_{\mathrm{ambient}}$,
passing $k' := \min(k_{\mathrm{comb}}, p_{\mathrm{cap}}) \ge 64$ and $L'_{\max} := k'$ to `IH` yields either:
1. **(Global Cap)** at length $p_{\mathrm{cap}}$;
2. **(Global SplitOrCross)** at length $k \in [L_{\max}, p_{\mathrm{cap}}]$; or
3. **(Active-Leaf Split-$D_r$ Type I)** of $W_z$ at length $k \in [64, L_{\max} - 1]$. -/
theorem resolve_recursive_comb_call {V : Type} [Fintype V] [DecidableEq V]
    {F : SimpleGraph V} {S U_ambient W_z M_base : Finset V}
    {r r' d s' k_comb p_cap L_max : ℕ} {η_out η₀ w w_sub : ℝ}
    {u : Fin k_comb → V} {B' : Fin k_comb → Finset V}
    {stems' : Fin k_comb → Fin s' → V}
    (hr : 2 ≤ r) (hr'1 : 1 ≤ r') (hr'r : r' < r) (hr_sum : r' + d + 1 = r)
    (hs' : 1 ≤ s') (hp_cap : 64 ≤ p_cap) (hL_low : 2 ≤ L_max) (hL_high : L_max ≤ p_cap)
    (hη_pos : 0 < η_out) (hη_ub : η_out ≤ (2 : ℝ)⁻¹ ^ 16)
    (hη₀_pos : 0 < η₀) (hη₀_le_out : η₀ ≤ η_out)
    (hη₀_lb : (2 : ℝ)⁻¹ ^ (120 * r + 2) * (p_cap : ℝ)⁻¹ ^ (4 * splitTreeD r) * η_out ≤ η₀)
    (hIH : Stage1CombCoCombDichotomyStrongAt r')
    (hfree : IsInducedSubgraphFree F (PkCompl (s' + 4 + r')))
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
    -- (1) Global Cap
    (∃ U : Fin p_cap → Finset V,
      IsWeaklySparseOrCoSparseBlockadeIn F U_ambient p_cap
        ((2 : ℝ) ^ (-(200 * (r : ℝ) ^ 2)) * η_out ^ r * (p_cap : ℝ) ^ (-(capExpE r : ℝ)) * w)
        η_out U) ∨
    -- (2) Global SplitOrCross
    (∃ k : ℕ, L_max ≤ k ∧ k ≤ p_cap ∧
      ∃ U : Fin k → Finset V,
        IsWeaklySparseOrCoSparseBlockadeIn F U_ambient k
          (w / ((2 : ℝ) ^ (60 * r) * (k : ℝ) ^ (2 * splitTreeD r))) η_out U) ∨
    -- (3) Active-Leaf Split-D_r Type I
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
  -- Invoke IH with ℓ' := k' and stopping leaf threshold L'_max := k'
  have h_ih := hIH hr'1 V F S s' k' p_cap k' η₀ w_sub
    (fun i => u (Fin.castLE hk'_le_comb i)) B'_k'
    (fun i => stems' (Fin.castLE hk'_le_comb i))
    hs' hk'_64 hk'_le_pcap (by omega) le_rfl hη₀_pos hη₀_ub hfree hcomb_k' hstems_k' hw_sub_min
  by_cases h_regA : k_comb ≤ p_cap
  · -- Regime A: k_comb ≤ p_cap, so k' = k_comb
    have hk'_eq : k' = k_comb := Nat.min_eq_left h_regA
    rcases h_ih with ⟨k, hk'_le_k, hk_le_pcap, U, hU⟩ | ⟨U, hU_cap⟩
    · -- (P2_{r'}-SplitOrCross) with k ∈ [k_comb, p_cap]
      have hk_comb_le_k : k_comb ≤ k := hk'_eq ▸ hk'_le_k
      have hk_64_out : 64 ≤ k := le_trans hk_64 hk_comb_le_k
      have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
      have hk_ge1 : (1 : ℝ) ≤ (k : ℝ) := Nat.one_le_cast.mpr (by omega)
      -- Prove width ≥ |W_z| / (2^60 * k^(5 * (D_r / 8)))
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
      · -- (3) Active-Leaf Split-D_r Type I
        right; right
        exact ⟨k, U, hk_64_out, hk_lt_L,
          hU.mono_ambient_width_eps hUk'_sub_Wz h_width_Wz le_rfl⟩
      · -- (2) Global SplitOrCross (k ≥ L_max)
        right; left
        push_neg at hk_lt_L
        refine ⟨k, hk_lt_L, hk_le_pcap, U,
          hU.mono_ambient_width_eps (hUk'_sub_Wz.trans hWz_sub) ?_ hη₀_le_out⟩
        have hL_le_k_D : (L_max : ℝ) ^ (splitTreeD r) ≤ (k : ℝ) ^ (splitTreeD r) :=
          pow_le_pow_left₀ (by positivity) (Nat.cast_le.mpr hk_lt_L) (splitTreeD r)
        have h_Dr_sum : splitTreeD r + 5 * (splitTreeD r / 8) ≤ 2 * splitTreeD r := by
          have := (splitTreeD_eq_eight_mul r hr).1
          omega
        have hk_sum_le : (k : ℝ) ^ (splitTreeD r) * (k : ℝ) ^ (5 * (splitTreeD r / 8)) ≤
            (k : ℝ) ^ (2 * splitTreeD r) := by
          rw [← pow_add]
          exact pow_le_pow_right₀ hk_ge1 h_Dr_sum
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
    · -- (P2_{r'}-Cap) → (1) Global Cap
      left
      exact ⟨U, hU_cap.mono_ambient_width_eps (hUk'_sub_Wz.trans hWz_sub) h_cap_le hη₀_le_out⟩
  · -- Regime B: k_comb > p_cap, so k' = L'_max = p_cap, forcing exact length k = p_cap!
    push_neg at h_regA
    have hk'_eq : k' = p_cap := Nat.min_eq_right (le_of_lt h_regA)
    left
    rcases h_ih with ⟨k, hk'_le_k, hk_le_pcap, U, hU⟩ | ⟨U, hU_cap⟩
    · have hk_eq_p : k = p_cap := by omega
      subst hk_eq_p
      have h_ge_cap := split_or_cross_at_pcap_ge_cap_width hr'1 hp_cap hη₀_pos hη₀_le1 hw_sub_nn
      exact ⟨U, hU.mono_ambient_width_eps (hUk'_sub_Wz.trans hWz_sub)
        (le_trans h_cap_le h_ge_cap) hη₀_le_out⟩
    · exact ⟨U, hU_cap.mono_ambient_width_eps (hUk'_sub_Wz.trans hWz_sub) h_cap_le hη₀_le_out⟩

/-- Active-leaf split condition on $W_z$ compatible with `ActiveLeafSplitTree.split_active_leaf`
at parameters `r_tree = treeParamR r` and `D_r = splitTreeD r = 8 * (splitTreeD r / 8)`. -/
def HasActiveLeafSplit {V : Type*} [DecidableEq V]
    (F : SimpleGraph V) (r L_max : ℕ) (η₀ : ℝ) (W_z : Finset V) : Prop :=
  ∃ (k : ℕ) (w_split : ℝ) (U : Fin k → Finset V),
    2 ≤ k ∧ k < L_max ∧
    IsWeaklySparseOrCoSparseBlockadeIn F W_z k w_split η₀ U ∧
    ((4 ≤ k ∧ (64 ≤ k ∨ 11 ≤ splitTreeD r / 8) ∧ ∀ q : Fin k,
        (W_z.card : ℝ) / ((2 : ℝ) ^ 60 * (k : ℝ) ^ (5 * (splitTreeD r / 8))) ≤ ((U q).card : ℝ)) ∨
     (64 * treeParamR r ≤ 8 * (splitTreeD r / 8) ∧ ∀ q : Fin k,
        (W_z.card : ℝ) / (2 : ℝ) ^ (60 * treeParamR r) ≤ ((U q).card : ℝ)))

/-- Outcome (3) of `resolve_recursive_comb_call` immediately satisfies `HasActiveLeafSplit`. -/
lemma hasActiveLeafSplit_of_type1 {V : Type*} [DecidableEq V]
    {F : SimpleGraph V} {r k L_max : ℕ} {η₀ : ℝ} {W_z : Finset V} {U : Fin k → Finset V}
    (hk64 : 64 ≤ k) (hkL : k < L_max)
    (hU : IsWeaklySparseOrCoSparseBlockadeIn F W_z k
      ((W_z.card : ℝ) / ((2 : ℝ) ^ 60 * (k : ℝ) ^ (5 * (splitTreeD r / 8)))) η₀ U) :
    HasActiveLeafSplit F r L_max η₀ W_z :=
  ⟨k, _, U, by omega, hkL, hU, Or.inl ⟨by omega, Or.inl hk64, hU.1.width_ge⟩⟩

/-- A 2-block Type II split $(X_0, X_1)$ inside $W_z$ of width $\ge |W_z| / 2^{25 r}$ and weak
$\eta_0$-sparsity/co-sparsity yields either **(Global SplitOrCross)** (when $L_{\max} = 2$) or
`HasActiveLeafSplit F r L_max η₀ W_z` (when $L_{\max} > 2$). -/
lemma two_block_type2_split_or_global {V : Type*} [Fintype V] [DecidableEq V]
    {F : SimpleGraph V} {U_ambient W_z X₀ X₁ : Finset V}
    {r L_max p_cap : ℕ} {η_out η₀ w : ℝ}
    (hr : 2 ≤ r) (hL_low : 2 ≤ L_max) (hL_high : L_max ≤ p_cap)
    (hη₀_le_out : η₀ ≤ η_out) (hw_nn : 0 ≤ w)
    (hWz_sub : W_z ⊆ U_ambient) (hWz_pos : 0 < W_z.card)
    (hWz_active : w / (L_max : ℝ) ^ (splitTreeD r) ≤ (W_z.card : ℝ))
    (hX₀_sub : X₀ ⊆ W_z) (hX₁_sub : X₁ ⊆ W_z) (hX_disj : Disjoint X₀ X₁)
    (hX₀_card : (W_z.card : ℝ) / (2 : ℝ) ^ (25 * r) ≤ (X₀.card : ℝ))
    (hX₁_card : (W_z.card : ℝ) / (2 : ℝ) ^ (25 * r) ≤ (X₁.card : ℝ))
    (h_sp : IsWeaklySparseOrCoSparsePair F X₀ X₁ η₀) :
    (∃ k : ℕ, L_max ≤ k ∧ k ≤ p_cap ∧
      ∃ U : Fin k → Finset V,
        IsWeaklySparseOrCoSparseBlockadeIn F U_ambient k
          (w / ((2 : ℝ) ^ (60 * r) * (k : ℝ) ^ (2 * splitTreeD r))) η_out U) ∨
    HasActiveLeafSplit F r L_max η₀ W_z := by
  have hWz_r_pos : (0 : ℝ) < (W_z.card : ℝ) := Nat.cast_pos.mpr hWz_pos
  have hw_split_pos : 0 < (W_z.card : ℝ) / (2 : ℝ) ^ (25 * r) := by positivity
  have hX₀_ne : X₀.Nonempty := by
    rw [← Finset.card_pos, ← @Nat.cast_pos ℝ]; linarith
  have hX₁_ne : X₁.Nonempty := by
    rw [← Finset.card_pos, ← @Nat.cast_pos ℝ]; linarith
  let U₂ : Fin 2 → Finset V := ![X₀, X₁]
  have hU₂_block : IsWeaklySparseOrCoSparseBlockadeIn F W_z 2
      ((W_z.card : ℝ) / (2 : ℝ) ^ (25 * r)) η₀ U₂ := by
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · intro q; fin_cases q <;> simp [U₂, hX₀_sub, hX₁_sub]
    · intro q; fin_cases q <;> simp [U₂, hX₀_ne, hX₁_ne]
    · intro q₁ q₂ hne
      fin_cases q₁ <;> fin_cases q₂
      · exact False.elim (hne rfl)
      · exact hX_disj
      · exact hX_disj.symm
      · exact False.elim (hne rfl)
    · intro q; fin_cases q <;> simp [U₂, hX₀_card, hX₁_card]
    · intro q₁ q₂ hne
      fin_cases q₁ <;> fin_cases q₂
      · exact False.elim (hne rfl)
      · exact h_sp
      · exact h_sp.symm
      · exact False.elim (hne rfl)
  by_cases hL2 : L_max = 2
  · left
    refine ⟨2, by omega, by omega, U₂,
      hU₂_block.mono_ambient_width_eps hWz_sub ?_ hη₀_le_out⟩
    have hL_eq : (L_max : ℝ) = 2 := by rw [hL2]; norm_num
    have h1 : (2 : ℝ) ^ (25 * r) * (2 : ℝ) ^ (splitTreeD r) ≤
        (2 : ℝ) ^ (60 * r) * (2 : ℝ) ^ (2 * splitTreeD r) := by
      refine mul_le_mul (pow_le_pow_right₀ (by norm_num) (by omega))
        (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity) (by positivity)
    calc w / ((2 : ℝ) ^ (60 * r) * ((2 : ℕ) : ℝ) ^ (2 * splitTreeD r))
        = w / ((2 : ℝ) ^ (60 * r) * (2 : ℝ) ^ (2 * splitTreeD r)) := by norm_num
      _ ≤ w / ((2 : ℝ) ^ (25 * r) * (2 : ℝ) ^ (splitTreeD r)) :=
          div_le_div_of_nonneg_left hw_nn (by positivity) h1
      _ = (w / (L_max : ℝ) ^ (splitTreeD r)) / (2 : ℝ) ^ (25 * r) := by rw [hL_eq]; ring
      _ ≤ (W_z.card : ℝ) / (2 : ℝ) ^ (25 * r) :=
          div_le_div_of_nonneg_right hWz_active (by positivity)
  · right
    have hL_gt2 : 2 < L_max := by omega
    have h_tr := treeParamR_bounds r hr
    have h_Dr := (splitTreeD_eq_eight_mul r hr).1
    refine ⟨2, (W_z.card : ℝ) / (2 : ℝ) ^ (25 * r), U₂, le_rfl, hL_gt2, hU₂_block, Or.inr ⟨?_, ?_⟩⟩
    · omega
    · intro q
      have h2_pow : (2 : ℝ) ^ (25 * r) ≤ (2 : ℝ) ^ (60 * treeParamR r) :=
        pow_le_pow_right₀ (by norm_num) h_tr.2.2.2
      exact le_trans (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) h2_pow)
        (hU₂_block.1.width_ge q)

/-- Exponent bound $5 D_r + 3 \le E_r$ for all $r \ge 2$. -/
lemma five_mul_splitTreeD_add_three_le_capExpE (r : ℕ) (hr : 2 ≤ r) :
    5 * splitTreeD r + 3 ≤ capExpE r := by
  rcases r with _ | _ | _ | n
  · omega
  · omega
  · decide
  · change 5 * splitTreeD (n + 3) + 3 ≤ capExpE (n + 3)
    have h_Dr : splitTreeD (n + 3) ≤ 16 ^ (n + 2) := splitTreeD_le_pow_sixteen (n + 3) (by omega)
    unfold capExpE
    have h_pow : 16 ^ (n + 3) = 16 * 16 ^ (n + 2) := by rw [Nat.pow_succ]; ring
    rw [h_pow]
    have h_16_pos : 1 ≤ 16 ^ (n + 2) := Nat.one_le_pow _ 16 (by omega)
    nlinarith

/-- Verifies the cardinality precondition $|N_d| \ge 64 p_{\mathrm{cap}}^2 \theta_r^{-1}$ of Lemma 8(1)
for any depth-$d$ slice $N_d \subseteq W_z$ ($d \le r - 1$) satisfying $|N_d| \ge 2^{-23 d} |W_z|$. -/
lemma theta_r_precond_card {r d p_cap : ℕ} {η_out θ_r w : ℝ} {W_z N_d : Finset V}
    (hr : 2 ≤ r) (hd : d ≤ r - 1) (hp_cap : 64 ≤ p_cap)
    (hη_pos : 0 < η_out) (hη_ub : η_out ≤ 1)
    (hθ_pos : 0 < θ_r)
    (hθ_lb : (2 : ℝ)⁻¹ ^ (120 * r + 8) * (p_cap : ℝ)⁻¹ ^ (4 * splitTreeD r + 3) * η_out ≤ θ_r)
    (hw_ge : combMinWidth r η_out p_cap ≤ w)
    (hWz_card : w / (p_cap : ℝ) ^ (splitTreeD r) ≤ (W_z.card : ℝ))
    (hNd_card : (W_z.card : ℝ) / (2 : ℝ) ^ (23 * d) ≤ (N_d.card : ℝ)) :
    64 * (p_cap : ℝ) ^ 2 * θ_r⁻¹ ≤ (N_d.card : ℝ) := by
  have hp_r : (64 : ℝ) ≤ (p_cap : ℝ) := Nat.ofNat_le_cast.mpr hp_cap
  have hp_pos : (0 : ℝ) < (p_cap : ℝ) := by linarith
  have hη_inv_ge1 : 1 ≤ η_out⁻¹ := one_le_inv₀ hη_pos |>.mpr hη_ub
  unfold combMinWidth at hw_ge
  rw [show -(3 * (r : ℝ)) = -(((3 * r : ℕ) : ℝ)) by push_cast; ring,
    rpow_neg_natCast (le_of_lt hη_pos) (3 * r), ← inv_pow] at hw_ge
  have hθ_inv_ub : θ_r⁻¹ ≤ (2 : ℝ) ^ (120 * r + 8) * (p_cap : ℝ) ^ (4 * splitTreeD r + 3) * η_out⁻¹ := by
    have h_lhs_pos : 0 < (2 : ℝ)⁻¹ ^ (120 * r + 8) * (p_cap : ℝ)⁻¹ ^ (4 * splitTreeD r + 3) * η_out := by positivity
    have h1 := inv_anti₀ h_lhs_pos hθ_lb
    calc θ_r⁻¹ ≤ ((2 : ℝ)⁻¹ ^ (120 * r + 8) * (p_cap : ℝ)⁻¹ ^ (4 * splitTreeD r + 3) * η_out)⁻¹ := h1
      _ = (2 : ℝ) ^ (120 * r + 8) * (p_cap : ℝ) ^ (4 * splitTreeD r + 3) * η_out⁻¹ := by
          rw [mul_inv_rev, mul_inv_rev, inv_pow, inv_inv, inv_pow, inv_inv]; ring
  have h_2_exp : (120 * r + 14) + 23 * d ≤ 400 * r ^ 2 := by
    have : 23 * d ≤ 23 * r := Nat.mul_le_mul_left 23 (by omega)
    nlinarith
  have h_p_exp : (4 * splitTreeD r + 5) + splitTreeD r ≤ capExpE r + 2 * splitTreeD r := by
    have := five_mul_splitTreeD_add_three_le_capExpE r hr
    have := (splitTreeD_eq_eight_mul r hr).2.1
    omega
  have h_2_pow : (2 : ℝ) ^ (120 * r + 14) * (2 : ℝ) ^ (23 * d) ≤ (2 : ℝ) ^ (400 * r ^ 2) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) h_2_exp
  have h_p_pow : (p_cap : ℝ) ^ (4 * splitTreeD r + 5) * (p_cap : ℝ) ^ (splitTreeD r) ≤
      (p_cap : ℝ) ^ (capExpE r + 2 * splitTreeD r) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by linarith) h_p_exp
  have h_η_pow : η_out⁻¹ ≤ (η_out⁻¹) ^ (3 * r) := by
    simpa using pow_le_pow_right₀ hη_inv_ge1 (by omega : 1 ≤ 3 * r)
  have h_prod : 64 * (p_cap : ℝ) ^ 2 * θ_r⁻¹ * ((2 : ℝ) ^ (23 * d) * (p_cap : ℝ) ^ (splitTreeD r)) ≤ w := by
    calc 64 * (p_cap : ℝ) ^ 2 * θ_r⁻¹ * ((2 : ℝ) ^ (23 * d) * (p_cap : ℝ) ^ (splitTreeD r))
        ≤ 64 * (p_cap : ℝ) ^ 2 *
            ((2 : ℝ) ^ (120 * r + 8) * (p_cap : ℝ) ^ (4 * splitTreeD r + 3) * η_out⁻¹) *
            ((2 : ℝ) ^ (23 * d) * (p_cap : ℝ) ^ (splitTreeD r)) := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hθ_inv_ub (by positivity)) (by positivity)
      _ = ((2 : ℝ) ^ (120 * r + 14) * (2 : ℝ) ^ (23 * d)) * η_out⁻¹ *
            ((p_cap : ℝ) ^ (4 * splitTreeD r + 5) * (p_cap : ℝ) ^ (splitTreeD r)) := by
          have h64 : (64 : ℝ) * (2 : ℝ) ^ (120 * r + 8) = (2 : ℝ) ^ (120 * r + 14) := by
            rw [show 120 * r + 14 = (120 * r + 8) + 6 by omega, pow_add]; norm_num; ring
          have hp2 : (p_cap : ℝ) ^ 2 * (p_cap : ℝ) ^ (4 * splitTreeD r + 3) =
              (p_cap : ℝ) ^ (4 * splitTreeD r + 5) := by
            rw [← pow_add, show 2 + (4 * splitTreeD r + 3) = 4 * splitTreeD r + 5 by omega]
          calc 64 * (p_cap : ℝ) ^ 2 *
                ((2 : ℝ) ^ (120 * r + 8) * (p_cap : ℝ) ^ (4 * splitTreeD r + 3) * η_out⁻¹) *
                ((2 : ℝ) ^ (23 * d) * (p_cap : ℝ) ^ (splitTreeD r))
              = (64 * (2 : ℝ) ^ (120 * r + 8)) * (2 : ℝ) ^ (23 * d) * η_out⁻¹ *
                (((p_cap : ℝ) ^ 2 * (p_cap : ℝ) ^ (4 * splitTreeD r + 3)) * (p_cap : ℝ) ^ (splitTreeD r)) := by ring
            _ = ((2 : ℝ) ^ (120 * r + 14) * (2 : ℝ) ^ (23 * d)) * η_out⁻¹ *
                ((p_cap : ℝ) ^ (4 * splitTreeD r + 5) * (p_cap : ℝ) ^ (splitTreeD r)) := by
                rw [h64, hp2]
      _ ≤ (2 : ℝ) ^ (400 * r ^ 2) * (η_out⁻¹) ^ (3 * r) * (p_cap : ℝ) ^ (capExpE r + 2 * splitTreeD r) := by
          refine mul_le_mul (mul_le_mul h_2_pow h_η_pow (by positivity) (by positivity))
            h_p_pow (by positivity) (by positivity)
      _ ≤ w := hw_ge
  have h_div1 : 64 * (p_cap : ℝ) ^ 2 * θ_r⁻¹ * (2 : ℝ) ^ (23 * d) ≤ (W_z.card : ℝ) := by
    have h1 : 64 * (p_cap : ℝ) ^ 2 * θ_r⁻¹ * (2 : ℝ) ^ (23 * d) ≤ w / (p_cap : ℝ) ^ (splitTreeD r) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    exact le_trans h1 hWz_card
  have h_div2 : 64 * (p_cap : ℝ) ^ 2 * θ_r⁻¹ ≤ (W_z.card : ℝ) / (2 : ℝ) ^ (23 * d) :=
    (le_div_iff₀ (by positivity)).mpr h_div1
  exact le_trans h_div2 hNd_card

/-- Verifies that the **(Case G-Large-$k$)** blockade width $\theta_r |N_d| \ge \theta_r \cdot 2^{-(23d+1)} |W_z|$
exceeds the global cap width $2^{-200 r^2} \eta_{\mathrm{out}}^r p_{\mathrm{cap}}^{-E_r} w$. -/
lemma theta_r_cap_width_le {r d p_cap : ℕ} {η_out θ_r w : ℝ} {W_z : Finset V}
    (hr : 2 ≤ r) (hd : d ≤ r - 1) (hp_cap : 64 ≤ p_cap)
    (hη_pos : 0 < η_out) (hη_ub : η_out ≤ 1) (hw_nn : 0 ≤ w)
    (hθ_lb : (2 : ℝ)⁻¹ ^ (120 * r + 8) * (p_cap : ℝ)⁻¹ ^ (4 * splitTreeD r + 3) * η_out ≤ θ_r)
    (hWz_card : w / (p_cap : ℝ) ^ (splitTreeD r) ≤ (W_z.card : ℝ)) :
    (2 : ℝ) ^ (-(200 * (r : ℝ) ^ 2)) * η_out ^ r * (p_cap : ℝ) ^ (-(capExpE r : ℝ)) * w ≤
      θ_r * ((W_z.card : ℝ) / (2 : ℝ) ^ (23 * d + 1)) := by
  have hp_r : (64 : ℝ) ≤ (p_cap : ℝ) := Nat.ofNat_le_cast.mpr hp_cap
  have hp_pos : (0 : ℝ) < (p_cap : ℝ) := by linarith
  rw [show -(200 * (r : ℝ) ^ 2) = -(((200 * r ^ 2 : ℕ) : ℝ)) by push_cast; ring,
    rpow_neg_natCast (by norm_num) (200 * r ^ 2), ← inv_pow,
    show -(capExpE r : ℝ) = -(((capExpE r : ℕ) : ℝ)) by rfl,
    rpow_neg_natCast (le_of_lt hp_pos) (capExpE r), ← inv_pow]
  have h_2_exp : (120 * r + 8) + (23 * d + 1) ≤ 200 * r ^ 2 := by
    have : 23 * d ≤ 23 * r := Nat.mul_le_mul_left 23 (by omega)
    nlinarith
  have h_p_exp : (4 * splitTreeD r + 3) + splitTreeD r ≤ capExpE r := by
    have := five_mul_splitTreeD_add_three_le_capExpE r hr
    omega
  have h_2_pow : (2 : ℝ)⁻¹ ^ (200 * r ^ 2) ≤
      (2 : ℝ)⁻¹ ^ (120 * r + 8) * (2 : ℝ)⁻¹ ^ (23 * d + 1) := by
    rw [← pow_add]
    exact pow_le_pow_of_le_one (by positivity) (by norm_num) h_2_exp
  have h_p_pow : (p_cap : ℝ)⁻¹ ^ (capExpE r) ≤
      (p_cap : ℝ)⁻¹ ^ (4 * splitTreeD r + 3) * (p_cap : ℝ)⁻¹ ^ (splitTreeD r) := by
    rw [← pow_add]
    have hp_inv_le1 : (p_cap : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    exact pow_le_pow_of_le_one (by positivity) hp_inv_le1 h_p_exp
  have h_η_pow : η_out ^ r ≤ η_out := by
    simpa using pow_le_pow_of_le_one (le_of_lt hη_pos) hη_ub (by omega : 1 ≤ r)
  calc (2 : ℝ)⁻¹ ^ (200 * r ^ 2) * η_out ^ r * (p_cap : ℝ)⁻¹ ^ (capExpE r) * w
      ≤ ((2 : ℝ)⁻¹ ^ (120 * r + 8) * (2 : ℝ)⁻¹ ^ (23 * d + 1)) * η_out *
          ((p_cap : ℝ)⁻¹ ^ (4 * splitTreeD r + 3) * (p_cap : ℝ)⁻¹ ^ (splitTreeD r)) * w := by
        refine mul_le_mul_of_nonneg_right ?_ hw_nn
        exact mul_le_mul (mul_le_mul h_2_pow h_η_pow (by positivity) (by positivity))
          h_p_pow (by positivity) (by positivity)
    _ = ((2 : ℝ)⁻¹ ^ (120 * r + 8) * (p_cap : ℝ)⁻¹ ^ (4 * splitTreeD r + 3) * η_out) *
          ((w / (p_cap : ℝ) ^ (splitTreeD r)) / (2 : ℝ) ^ (23 * d + 1)) := by
        rw [inv_pow (a := (p_cap : ℝ)) (n := splitTreeD r),
          inv_pow (a := (2 : ℝ)) (n := 23 * d + 1)]; ring
    _ ≤ θ_r * ((W_z.card : ℝ) / (2 : ℝ) ^ (23 * d + 1)) := by
        refine mul_le_mul hθ_lb ?_ (by positivity) (by linarith [hθ_lb, show (0 : ℝ) < (2 : ℝ)⁻¹ ^ (120 * r + 8) * (p_cap : ℝ)⁻¹ ^ (4 * splitTreeD r + 3) * η_out by positivity])
        exact div_le_div_of_nonneg_right hWz_card (by positivity)

/-- **Unified Gallai Core Extraction or Active-Leaf Split at Depth $d \in [0, r-1]$**:
Given an active leaf $W_z \subseteq U_{\mathrm{ambient}}$ and a depth-$d$ slice $N_d \subseteq W_z$
with $|N_d| \ge 2^{-23 d} |W_z|$, applying `three_case_gallai_core_extraction` at threshold $\theta_r$
yields either:
1. **(Global Cap)** at length $p_{\mathrm{cap}}$;
2. **(Global SplitOrCross)** at length $k \in [L_{\max}, p_{\mathrm{cap}}]$;
3. **(Active-Leaf Split)** `HasActiveLeafSplit F r L_max η₀ W_z`; or
4. **(Case G-Core)**: an exact module $N_T \subseteq N_d$ and core $N^* \subseteq N_T$ with
   $|N^*| \ge 2^{-(23 d + 3)} |W_z|$ and every proper module $X$ of $F[N_T]$ intersecting $N^*$
   satisfying $X \subseteq N^*$, $|X| < \theta_r |N_d|$, and $|X| < 5 \theta_r |N^*|$. -/
theorem gallai_core_or_split_at_depth_d {V : Type*} [Fintype V] [DecidableEq V]
    {F : SimpleGraph V} {U_ambient W_z N_d : Finset V}
    {r d ℓ p_cap L_max : ℕ} {η_out η₀ θ_r w : ℝ}
    (hr : 2 ≤ r) (hd : d ≤ r - 1) (hℓ : 64 ≤ ℓ) (hp_cap : ℓ ≤ p_cap)
    (hL_low : 2 ≤ L_max) (hL_high : L_max ≤ p_cap)
    (hη_pos : 0 < η_out) (hη_ub : η_out ≤ 1)
    (hη₀_pos : 0 < η₀)
    (hθ_pos : 0 < θ_r) (hθ_ub : θ_r ≤ 1 / (64 * (ℓ : ℝ) ^ 2))
    (hθ_lb : (2 : ℝ)⁻¹ ^ (120 * r + 8) * (p_cap : ℝ)⁻¹ ^ (4 * splitTreeD r + 3) * η_out ≤ θ_r)
    (hw_ge : combMinWidth r η_out p_cap ≤ w)
    (hWz_sub : W_z ⊆ U_ambient)
    (hWz_active : w / (L_max : ℝ) ^ (splitTreeD r) ≤ (W_z.card : ℝ))
    (hNd_sub : N_d ⊆ W_z)
    (hNd_card : (W_z.card : ℝ) / (2 : ℝ) ^ (23 * d) ≤ (N_d.card : ℝ)) :
    (∃ U : Fin p_cap → Finset V,
      IsWeaklySparseOrCoSparseBlockadeIn F U_ambient p_cap
        ((2 : ℝ) ^ (-(200 * (r : ℝ) ^ 2)) * η_out ^ r * (p_cap : ℝ) ^ (-(capExpE r : ℝ)) * w)
        η_out U) ∨
    (∃ k : ℕ, L_max ≤ k ∧ k ≤ p_cap ∧
      ∃ U : Fin k → Finset V,
        IsWeaklySparseOrCoSparseBlockadeIn F U_ambient k
          (w / ((2 : ℝ) ^ (60 * r) * (k : ℝ) ^ (2 * splitTreeD r))) η_out U) ∨
    HasActiveLeafSplit F r L_max η₀ W_z ∨
    (∃ N_T ⊆ N_d, IsModuleIn F N_d N_T ∧
      (N_d.card : ℝ) / 2 < (N_T.card : ℝ) ∧
      ∃ N_star ⊆ N_T,
        (15 / 64 : ℝ) * (N_d.card : ℝ) < (N_star.card : ℝ) ∧
        (W_z.card : ℝ) / (2 : ℝ) ^ (23 * d + 3) ≤ (N_star.card : ℝ) ∧
        (∀ X : Finset V, IsProperModuleIn F N_T X → (X ∩ N_star).Nonempty →
          X ⊆ N_star ∧ (X.card : ℝ) < θ_r * (N_d.card : ℝ) ∧
          (X.card : ℝ) < 5 * θ_r * (N_star.card : ℝ))) := by
  have hp_64 : 64 ≤ p_cap := le_trans hℓ hp_cap
  have hp_pos : (0 : ℝ) < (p_cap : ℝ) := Nat.cast_pos.mpr (by omega)
  have hw_nn : 0 ≤ w := by
    have : 0 < combMinWidth r η_out p_cap := by unfold combMinWidth; positivity
    linarith
  have hWz_pcap : w / (p_cap : ℝ) ^ (splitTreeD r) ≤ (W_z.card : ℝ) := by
    have hL_p : (L_max : ℝ) ^ (splitTreeD r) ≤ (p_cap : ℝ) ^ (splitTreeD r) :=
      pow_le_pow_left₀ (by positivity) (Nat.cast_le.mpr hL_high) (splitTreeD r)
    exact le_trans (div_le_div_of_nonneg_left hw_nn (by positivity) hL_p) hWz_active
  have hNd_precond : 64 * (p_cap : ℝ) ^ 2 * θ_r⁻¹ ≤ (N_d.card : ℝ) :=
    theta_r_precond_card hr hd hp_64 hη_pos hη_ub hθ_pos hθ_lb hw_ge hWz_pcap hNd_card
  obtain ⟨N_T, hNT_Nd, hNT_mod, h_cases⟩ :=
    three_case_gallai_core_extraction F N_d ℓ p_cap θ_r (by omega) hp_cap hθ_pos hθ_ub hNd_precond
  rcases h_cases with ⟨k, U, hk2, hkp, hU_pure, _⟩ | ⟨Q, hQ_pure, _⟩ | ⟨hNT_gt, N_star, hNs_NT, hNs_gt, hNs_prop⟩
  · -- (Case G-Small-k)
    by_cases hk_lt_L : k < L_max
    · -- 2 ≤ k < L_max → HasActiveLeafSplit
      right; right; left
      have hU_weak := (IsPureBlockadeIn.isWeaklySparseOrCoSparseBlockadeIn hU_pure (le_of_lt hη₀_pos)).mono_ambient_width_eps
        hNd_sub le_rfl le_rfl
      by_cases hk64 : 64 ≤ k
      · -- Type I active-leaf split
        refine ⟨k, _, U, hk2, hk_lt_L, hU_weak, Or.inl ⟨by omega, Or.inl hk64, fun q => ?_⟩⟩
        have hk_ge1 : (1 : ℝ) ≤ (k : ℝ) := Nat.one_le_cast.mpr (by omega)
        have h64_k : (2 : ℝ) ^ 6 ≤ (k : ℝ) := by
          have : (64 : ℝ) ≤ (k : ℝ) := Nat.ofNat_le_cast.mpr hk64
          norm_num at this ⊢; exact this
        have h_2_k : (2 : ℝ) ^ (23 * d + 6) ≤ (k : ℝ) ^ (4 * r) := by
          have h1 : (2 : ℝ) ^ (23 * d + 6) ≤ (2 : ℝ) ^ (24 * r) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          have h2 : ((2 : ℝ) ^ 6) ^ (4 * r) ≤ (k : ℝ) ^ (4 * r) :=
            pow_le_pow_left₀ (by positivity) h64_k (4 * r)
          rw [← pow_mul, show 6 * (4 * r) = 24 * r by ring] at h2
          exact le_trans h1 h2
        have h_4r_5m : 4 * r + 2 ≤ 5 * (splitTreeD r / 8) := by
          rcases r with _ | _ | _ | n
          · omega
          · omega
          · decide
          · change 4 * (n + 3) + 2 ≤ 5 * (splitTreeD (n + 3) / 8)
            rw [splitTreeD_add_three]
            have h1 : (256 * 8 ^ n) / 8 = 32 * 8 ^ n := by omega
            have h2 : ∀ m : ℕ, m + 1 ≤ 8 ^ m := by
              intro m; induction m with
              | zero => decide
              | succ m ih =>
                have : 1 ≤ 8 ^ m := Nat.one_le_pow m 8 (by omega)
                rw [Nat.pow_succ]; omega
            have h2n := h2 n
            rw [h1]; omega
        have h_den : (2 : ℝ) ^ (23 * d + 6) * (k : ℝ) ^ 2 ≤
            (2 : ℝ) ^ 60 * (k : ℝ) ^ (5 * (splitTreeD r / 8)) := by
          calc (2 : ℝ) ^ (23 * d + 6) * (k : ℝ) ^ 2
              ≤ (k : ℝ) ^ (4 * r) * (k : ℝ) ^ 2 := mul_le_mul_of_nonneg_right h_2_k (by positivity)
            _ = 1 * (k : ℝ) ^ (4 * r + 2) := by rw [← pow_add]; ring
            _ ≤ (2 : ℝ) ^ 60 * (k : ℝ) ^ (5 * (splitTreeD r / 8)) :=
                mul_le_mul (by norm_num) (pow_le_pow_right₀ hk_ge1 h_4r_5m) (by positivity) (by positivity)
        calc (W_z.card : ℝ) / ((2 : ℝ) ^ 60 * (k : ℝ) ^ (5 * (splitTreeD r / 8)))
            ≤ (W_z.card : ℝ) / ((2 : ℝ) ^ (23 * d + 6) * (k : ℝ) ^ 2) :=
              div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) h_den
          _ = ((W_z.card : ℝ) / (2 : ℝ) ^ (23 * d)) / (64 * (k : ℝ) ^ 2) := by
              rw [show 23 * d + 6 = 23 * d + 6 by rfl, pow_add]; ring
          _ ≤ (N_d.card : ℝ) / (64 * (k : ℝ) ^ 2) :=
              div_le_div_of_nonneg_right hNd_card (by positivity)
          _ ≤ ((U q).card : ℝ) := hU_pure.1.width_ge q
      · -- k < 64 → Type II active-leaf split
        push_neg at hk64
        have h_tr := treeParamR_bounds r hr
        have h_Dr := (splitTreeD_eq_eight_mul r hr).1
        refine ⟨k, _, U, hk2, hk_lt_L, hU_weak, Or.inr ⟨by omega, fun q => ?_⟩⟩
        have hk_le_64 : (k : ℝ) ^ 2 ≤ (2 : ℝ) ^ 12 := by
          have hk_r : (k : ℝ) ≤ (64 : ℝ) := by exact_mod_cast (le_of_lt hk64)
          calc (k : ℝ) ^ 2 ≤ (64 : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hk_r 2
            _ = (2 : ℝ) ^ 12 := by norm_num
        have h_den : (2 : ℝ) ^ (23 * d) * (64 * (k : ℝ) ^ 2) ≤ (2 : ℝ) ^ (60 * treeParamR r) := by
          calc (2 : ℝ) ^ (23 * d) * (64 * (k : ℝ) ^ 2)
              ≤ (2 : ℝ) ^ (23 * d) * (64 * (2 : ℝ) ^ 12) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hk_le_64 (by positivity)) (by positivity)
            _ = (2 : ℝ) ^ (23 * d + 18) := by rw [pow_add]; ring
            _ ≤ (2 : ℝ) ^ (25 * r) := pow_le_pow_right₀ (by norm_num) (by omega)
            _ ≤ (2 : ℝ) ^ (60 * treeParamR r) := pow_le_pow_right₀ (by norm_num) h_tr.2.2.2
        calc (W_z.card : ℝ) / (2 : ℝ) ^ (60 * treeParamR r)
            ≤ (W_z.card : ℝ) / ((2 : ℝ) ^ (23 * d) * (64 * (k : ℝ) ^ 2)) :=
              div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) h_den
          _ = ((W_z.card : ℝ) / (2 : ℝ) ^ (23 * d)) / (64 * (k : ℝ) ^ 2) := by ring
          _ ≤ (N_d.card : ℝ) / (64 * (k : ℝ) ^ 2) :=
              div_le_div_of_nonneg_right hNd_card (by positivity)
          _ ≤ ((U q).card : ℝ) := hU_pure.1.width_ge q
    · -- L_max ≤ k < p_cap → Global SplitOrCross
      right; left
      push_neg at hk_lt_L
      refine ⟨k, hk_lt_L, le_of_lt hkp, U,
        (IsPureBlockadeIn.isWeaklySparseOrCoSparseBlockadeIn hU_pure (le_of_lt hη_pos)).mono_ambient_width_eps
          (hNd_sub.trans hWz_sub) ?_ le_rfl⟩
      have hk_ge1 : (1 : ℝ) ≤ (k : ℝ) := Nat.one_le_cast.mpr (by omega)
      have hL_k_D : (L_max : ℝ) ^ (splitTreeD r) ≤ (k : ℝ) ^ (splitTreeD r) :=
        pow_le_pow_left₀ (by positivity) (Nat.cast_le.mpr hk_lt_L) (splitTreeD r)
      have h2_pow : (2 : ℝ) ^ (23 * d + 6) ≤ (2 : ℝ) ^ (60 * r) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have hk_pow : (k : ℝ) ^ (splitTreeD r) * (k : ℝ) ^ 2 ≤ (k : ℝ) ^ (2 * splitTreeD r) := by
        rw [← pow_add]
        have : 8 ≤ splitTreeD r := by
          have := (splitTreeD_eq_eight_mul r hr).2.1; omega
        exact pow_le_pow_right₀ hk_ge1 (by omega)
      calc w / ((2 : ℝ) ^ (60 * r) * (k : ℝ) ^ (2 * splitTreeD r))
          ≤ w / ((2 : ℝ) ^ (23 * d + 6) * ((k : ℝ) ^ (splitTreeD r) * (k : ℝ) ^ 2)) :=
            div_le_div_of_nonneg_left hw_nn (by positivity)
              (mul_le_mul h2_pow hk_pow (by positivity) (by positivity))
        _ = ((w / (k : ℝ) ^ (splitTreeD r)) / (2 : ℝ) ^ (23 * d)) / (64 * (k : ℝ) ^ 2) := by
            rw [pow_add (a := (2 : ℝ)) (m := 23 * d) (n := 6)]; norm_num; ring
        _ ≤ ((w / (L_max : ℝ) ^ (splitTreeD r)) / (2 : ℝ) ^ (23 * d)) / (64 * (k : ℝ) ^ 2) :=
            div_le_div_of_nonneg_right
              (div_le_div_of_nonneg_right
                (div_le_div_of_nonneg_left hw_nn (by positivity) hL_k_D) (by positivity)) (by positivity)
        _ ≤ ((W_z.card : ℝ) / (2 : ℝ) ^ (23 * d)) / (64 * (k : ℝ) ^ 2) :=
            div_le_div_of_nonneg_right
              (div_le_div_of_nonneg_right hWz_active (by positivity)) (by positivity)
        _ ≤ (N_d.card : ℝ) / (64 * (k : ℝ) ^ 2) :=
            div_le_div_of_nonneg_right hNd_card (by positivity)
  · -- (Case G-Large-k) → Global Cap
    left
    refine ⟨Q, (IsPureBlockadeIn.isWeaklySparseOrCoSparseBlockadeIn hQ_pure (le_of_lt hη_pos)).mono_ambient_width_eps
      (hNd_sub.trans hWz_sub) ?_ le_rfl⟩
    have h_cap := theta_r_cap_width_le hr hd hp_64 hη_pos hη_ub hw_nn hθ_lb hWz_pcap
    have h_Nd_ge : (W_z.card : ℝ) / (2 : ℝ) ^ (23 * d + 1) ≤ (N_d.card : ℝ) := by
      have : (2 : ℝ) ^ (23 * d) ≤ (2 : ℝ) ^ (23 * d + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      exact le_trans (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) this) hNd_card
    exact le_trans h_cap (mul_le_mul_of_nonneg_left h_Nd_ge (le_of_lt hθ_pos))
  · -- (Case G-Core)
    right; right; right
    refine ⟨N_T, hNT_Nd, hNT_mod, hNT_gt, N_star, hNs_NT, hNs_gt, ?_, hNs_prop⟩
    calc (W_z.card : ℝ) / (2 : ℝ) ^ (23 * d + 3)
        = (1 / 8 : ℝ) * ((W_z.card : ℝ) / (2 : ℝ) ^ (23 * d)) := by
          rw [pow_add (a := (2 : ℝ)) (m := 23 * d) (n := 3)]; norm_num; ring
      _ ≤ (15 / 64 : ℝ) * (N_d.card : ℝ) := by
          have : (1 / 8 : ℝ) ≤ 15 / 64 := by norm_num
          exact mul_le_mul this hNd_card (by positivity) (by positivity)
      _ ≤ (N_star.card : ℝ) := le_of_lt hNs_gt

/-- Resolves Branch 1 of `general_depth_d_core_dichotomy` at depth $d \le r - 1$:
a complete $(p_{\mathrm{comp}}, 5 \theta_r |N^*|)$-blockade inside $N^* \subseteq W_z \subseteq U_{\mathrm{ambient}}$
yields **(Global Cap)** when $p_{\mathrm{comp}} = p_{\mathrm{cap}}$, or **(Global SplitOrCross)**
when $p_{\mathrm{comp}} < p_{\mathrm{cap}}$ and $8 \ell^2 \eta_0^{-1} \le p_{\mathrm{comp}}$. -/
lemma complete_blockade_at_pcomp_global {V : Type*} [Fintype V] [DecidableEq V]
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
    (hD_comp : IsCompleteBlockadeIn F N_star p_comp (5 * θ_r * (N_star.card : ℝ)) D) :
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
    (IsCompleteBlockadeIn.isPureBlockadeIn hD_comp) (le_of_lt hη_pos)).mono_ambient_width_eps
    (hNs_sub.trans hWz_sub) le_rfl le_rfl
  rcases hp_comp_cases with rfl | ⟨hp_lt_cap, hp_ge_ceil⟩
  · -- p_comp = p_cap → Global Cap
    left
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
  · -- p_comp < p_cap → Global SplitOrCross at k = p_comp
    right
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
    -- Lower-bound θ_r ≥ 1 / p_comp^3 using p_comp ≥ 8 ℓ^2 η₀⁻¹
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
      have : 8 ≤ splitTreeD r := by
        have := (splitTreeD_eq_eight_mul r hr).2.1; omega
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

/-- Width lower bounds (`hw_sub_lb` and `hw_sub_cap`) for `resolve_recursive_comb_call` when
`internal_depth_d_stem_promotion` promotes at $\tau = \eta_0 / 2$ ($w_{\mathrm{sub}} \ge \frac{\eta_0}{4} |N^*|$). -/
lemma internal_promo_width_bounds {r r' d p_cap L_max : ℕ} {η_out η₀ w w_sub : ℝ}
    {W_z N_star : Finset V}
    (hr : 2 ≤ r) (hd1 : 1 ≤ d) (hr'1 : 1 ≤ r') (hr_sum : r' + d + 1 = r)
    (hp_cap : 64 ≤ p_cap) (hL_low : 2 ≤ L_max) (hL_high : L_max ≤ p_cap)
    (hη_pos : 0 < η_out) (hη_ub : η_out ≤ 1)
    (hη₀_pos : 0 < η₀)
    (hη₀_lb : (2 : ℝ)⁻¹ ^ (120 * r + 2) * (p_cap : ℝ)⁻¹ ^ (4 * splitTreeD r) * η_out ≤ η₀)
    (hw_nn : 0 ≤ w)
    (hWz_active : w / (L_max : ℝ) ^ (splitTreeD r) ≤ (W_z.card : ℝ))
    (hNs_card : (W_z.card : ℝ) / (2 : ℝ) ^ (23 * d + 3) ≤ (N_star.card : ℝ))
    (hw_sub_ge : (η₀ / 4) * (N_star.card : ℝ) ≤ w_sub) :
    ((2 : ℝ)⁻¹ ^ (145 * r + 10) * (p_cap : ℝ)⁻¹ ^ (5 * splitTreeD r + 2) * η_out * w ≤ w_sub) ∧
    ((2 : ℝ)⁻¹ ^ ((120 * r + 2) * (r - 1) + 25 * r + 10) *
      (p_cap : ℝ)⁻¹ ^ ((4 * r' + 5) * splitTreeD r + 2) *
      η_out ^ r * w ≤ η₀ ^ r' * w_sub) := by
  have hp_pos : (0 : ℝ) < (p_cap : ℝ) := Nat.cast_pos.mpr (by omega)
  have hL_pos : (0 : ℝ) < (L_max : ℝ) := Nat.cast_pos.mpr (by omega)
  have hp_inv_le1 : (p_cap : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr (by omega))
  have hL_p : (L_max : ℝ) ^ (splitTreeD r) ≤ (p_cap : ℝ) ^ (splitTreeD r) :=
    pow_le_pow_left₀ (by positivity) (Nat.cast_le.mpr hL_high) (splitTreeD r)
  have hWz_pcap : (p_cap : ℝ)⁻¹ ^ (splitTreeD r) * w ≤ (W_z.card : ℝ) := by
    rw [inv_pow, ← div_eq_inv_mul]
    exact le_trans (div_le_div_of_nonneg_left hw_nn (by positivity) hL_p) hWz_active
  have hNs_lb : (2 : ℝ)⁻¹ ^ (23 * d + 3) * (p_cap : ℝ)⁻¹ ^ (splitTreeD r) * w ≤ (N_star.card : ℝ) := by
    calc (2 : ℝ)⁻¹ ^ (23 * d + 3) * (p_cap : ℝ)⁻¹ ^ (splitTreeD r) * w
        = ((p_cap : ℝ)⁻¹ ^ (splitTreeD r) * w) / (2 : ℝ) ^ (23 * d + 3) := by
          rw [inv_pow (a := (2 : ℝ))]; ring
      _ ≤ (W_z.card : ℝ) / (2 : ℝ) ^ (23 * d + 3) :=
          div_le_div_of_nonneg_right hWz_pcap (by positivity)
      _ ≤ (N_star.card : ℝ) := hNs_card
  constructor
  · -- Part 1: hw_sub_lb
    have h2_le : (2 : ℝ)⁻¹ ^ (145 * r + 10) ≤
        (2 : ℝ)⁻¹ ^ 2 * (2 : ℝ)⁻¹ ^ (120 * r + 2) * (2 : ℝ)⁻¹ ^ (23 * d + 3) := by
      rw [← pow_add, ← pow_add]
      exact pow_le_pow_of_le_one (by positivity) (by norm_num) (by omega)
    have hp_le : (p_cap : ℝ)⁻¹ ^ (5 * splitTreeD r + 2) ≤
        (p_cap : ℝ)⁻¹ ^ (4 * splitTreeD r) * (p_cap : ℝ)⁻¹ ^ (splitTreeD r) := by
      rw [← pow_add]
      exact pow_le_pow_of_le_one (by positivity) hp_inv_le1 (by omega)
    calc (2 : ℝ)⁻¹ ^ (145 * r + 10) * (p_cap : ℝ)⁻¹ ^ (5 * splitTreeD r + 2) * η_out * w
        ≤ ((2 : ℝ)⁻¹ ^ 2 * (2 : ℝ)⁻¹ ^ (120 * r + 2) * (2 : ℝ)⁻¹ ^ (23 * d + 3)) *
            ((p_cap : ℝ)⁻¹ ^ (4 * splitTreeD r) * (p_cap : ℝ)⁻¹ ^ (splitTreeD r)) * η_out * w := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul h2_le hp_le (by positivity) (by positivity))
              (le_of_lt hη_pos)) hw_nn
      _ = ((2 : ℝ)⁻¹ ^ 2 * ((2 : ℝ)⁻¹ ^ (120 * r + 2) * (p_cap : ℝ)⁻¹ ^ (4 * splitTreeD r) * η_out)) *
            ((2 : ℝ)⁻¹ ^ (23 * d + 3) * (p_cap : ℝ)⁻¹ ^ (splitTreeD r) * w) := by ring
      _ ≤ ((2 : ℝ)⁻¹ ^ 2 * η₀) * (N_star.card : ℝ) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hη₀_lb (by positivity))
            hNs_lb (by positivity) (by positivity)
      _ = (η₀ / 4) * (N_star.card : ℝ) := by ring
      _ ≤ w_sub := hw_sub_ge
  · -- Part 2: hw_sub_cap
    have h_η₀_r'1 : ((2 : ℝ)⁻¹ ^ (120 * r + 2)) ^ (r' + 1) *
        ((p_cap : ℝ)⁻¹ ^ (4 * splitTreeD r)) ^ (r' + 1) * η_out ^ (r' + 1) ≤ η₀ ^ (r' + 1) := by
      have h1 := pow_le_pow_left₀ (by positivity) hη₀_lb (r' + 1)
      rwa [mul_pow, mul_pow] at h1
    rw [← pow_mul, ← pow_mul] at h_η₀_r'1
    have h2_le : (2 : ℝ)⁻¹ ^ ((120 * r + 2) * (r - 1) + 25 * r + 10) ≤
        (2 : ℝ)⁻¹ ^ 2 * (2 : ℝ)⁻¹ ^ ((120 * r + 2) * (r' + 1)) * (2 : ℝ)⁻¹ ^ (23 * d + 3) := by
      rw [← pow_add, ← pow_add]
      have h_exp : 2 + (120 * r + 2) * (r' + 1) + (23 * d + 3) ≤
          (120 * r + 2) * (r - 1) + 25 * r + 10 := by
        have h1 : (120 * r + 2) * (r' + 1) ≤ (120 * r + 2) * (r - 1) :=
          Nat.mul_le_mul_left _ (by omega)
        omega
      exact pow_le_pow_of_le_one (by positivity) (by norm_num) h_exp
    have hp_le : (p_cap : ℝ)⁻¹ ^ ((4 * r' + 5) * splitTreeD r + 2) ≤
        (p_cap : ℝ)⁻¹ ^ (4 * splitTreeD r * (r' + 1)) * (p_cap : ℝ)⁻¹ ^ (splitTreeD r) := by
      rw [← pow_add]
      have h_exp : 4 * splitTreeD r * (r' + 1) + splitTreeD r ≤
          (4 * r' + 5) * splitTreeD r + 2 := by
        have : 4 * splitTreeD r * (r' + 1) + splitTreeD r = (4 * r' + 5) * splitTreeD r := by ring
        omega
      exact pow_le_pow_of_le_one (by positivity) hp_inv_le1 h_exp
    have hη_le : η_out ^ r ≤ η_out ^ (r' + 1) :=
      pow_le_pow_of_le_one (le_of_lt hη_pos) hη_ub (by omega)
    calc (2 : ℝ)⁻¹ ^ ((120 * r + 2) * (r - 1) + 25 * r + 10) *
          (p_cap : ℝ)⁻¹ ^ ((4 * r' + 5) * splitTreeD r + 2) * η_out ^ r * w
        ≤ ((2 : ℝ)⁻¹ ^ 2 * (2 : ℝ)⁻¹ ^ ((120 * r + 2) * (r' + 1)) * (2 : ℝ)⁻¹ ^ (23 * d + 3)) *
            ((p_cap : ℝ)⁻¹ ^ (4 * splitTreeD r * (r' + 1)) * (p_cap : ℝ)⁻¹ ^ (splitTreeD r)) *
            η_out ^ (r' + 1) * w := by
          refine mul_le_mul_of_nonneg_right ?_ hw_nn
          exact mul_le_mul (mul_le_mul h2_le hp_le (by positivity) (by positivity))
            hη_le (by positivity) (by positivity)
      _ = (2 : ℝ)⁻¹ ^ 2 *
            ((2 : ℝ)⁻¹ ^ ((120 * r + 2) * (r' + 1)) *
             (p_cap : ℝ)⁻¹ ^ (4 * splitTreeD r * (r' + 1)) * η_out ^ (r' + 1)) *
            ((2 : ℝ)⁻¹ ^ (23 * d + 3) * (p_cap : ℝ)⁻¹ ^ (splitTreeD r) * w) := by ring
      _ ≤ (2 : ℝ)⁻¹ ^ 2 * η₀ ^ (r' + 1) * (N_star.card : ℝ) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left h_η₀_r'1 (by positivity))
            hNs_lb (by positivity) (by positivity)
      _ = η₀ ^ r' * ((η₀ / 4) * (N_star.card : ℝ)) := by rw [pow_succ]; ring
      _ ≤ η₀ ^ r' * w_sub := mul_le_mul_of_nonneg_left hw_sub_ge (by positivity)

/-- Base case $d = r - 1$ (`rem = 0`) of the Step 2 cutter-chain dichotomy. -/
theorem depth_r_minus_1_cutter_chain {V : Type} [Fintype V] [DecidableEq V]
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
    (hfree : IsInducedSubgraphFree F (PkCompl (s + 4 + r)))
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
      exact (hM_step c hc1).trans ((neighborFinsetIn_subset F _ _).trans
        (ih_m ⟨c.1 - 1, by omega⟩ (by dsimp; omega)))
  have hM_last_sub_Wz : M_core ⟨d - 1, by omega⟩ ⊆ W_z := hM_core_sub_Wz ⟨d - 1, by omega⟩
  let N_d := neighborFinsetIn F (z ⟨d - 1, by omega⟩) (M_core ⟨d - 1, by omega⟩)
  let A_d := M_core ⟨d - 1, by omega⟩ \ N_d
  have hNd_sub_Wz : N_d ⊆ W_z := (neighborFinsetIn_subset F _ _).trans hM_last_sub_Wz
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
      rw [hM_seq_lt 0 (by dsimp; omega)]
      exact hM0_sub.trans hWz_sub_Bi
    have hM_seq_step : ∀ c : Fin d, M_seq c.succ ⊆ neighborFinsetIn F (z c) (M_seq c.castSucc) := by
      intro c
      rw [hM_seq_lt c.castSucc c.2]
      by_cases hc1 : c.1 + 1 < d
      · rw [hM_seq_lt c.succ hc1]
        have h_st := hM_step ⟨c.1 + 1, hc1⟩ (by dsimp; omega)
        have h_eq : (⟨(⟨c.1 + 1, hc1⟩ : Fin d).1 - 1, by omega⟩ : Fin d) = c := by ext; dsimp
        rwa [h_eq] at h_st
      · have hc_last : c.succ = Fin.last d := by ext; dsimp; omega
        have hc_eq : c = ⟨d - 1, by omega⟩ := by ext; dsimp; omega
        rw [hc_last, hM_seq_last, hc_eq]
        exact hNT_Nd
    have hz_seq_step : ∀ c : Fin d, ∀ hc1 : 1 ≤ c.1,
        z c ∈ M_seq ⟨c.1 - 1, by omega⟩ ∧ ¬F.Adj (z ⟨c.1 - 1, by omega⟩) (z c) := by
      intro c hc1
      rw [hM_seq_lt ⟨c.1 - 1, by omega⟩ (by dsimp; omega)]
      exact hz_step c hc1
    have hfree_d : IsInducedSubgraphFree F (PkCompl (s + 5 + d)) := by
      rwa [show s + 5 + d = s + 4 + r by omega]
    have hNs_sub_last : N_star ⊆ M_seq (Fin.last d) := by rw [hM_seq_last]; exact hNs_NT
    have hNs_small : ∀ X : Finset V,
        IsProperModuleIn F (M_seq (Fin.last d)) X → (X ∩ N_star).Nonempty →
        (X.card : ℝ) < 5 * θ_r * (N_star.card : ℝ) := by
      rw [hM_seq_last]
      exact fun X hX hX_ne => (hNs_prop X hX hX_ne).2.2
    have hAd_in : ∀ v ∈ A_d, v ∈ M_seq ⟨d - 1, by omega⟩ ∧ ¬F.Adj (z ⟨d - 1, by omega⟩) v := by
      intro v hv
      rw [hM_seq_lt ⟨d - 1, by omega⟩ (by dsimp; omega)]
      obtain ⟨hvM, hv_notN⟩ := Finset.mem_sdiff.mp hv
      exact ⟨hvM, fun hadj => hv_notN ((mem_neighborFinsetIn_iff F _ _ v).mpr ⟨hvM, hadj⟩)⟩
    rcases general_depth_d_core_dichotomy (p_comp := p_comp) hij hd1 hθ_pos hfree_d hcomb hstems
        z M_seq hz0 hM_seq_0 hM_seq_step hz_seq_step hNs_sub_last hNs_ne hNs_small hAd_in with
      ⟨D, hD_comp⟩ | ⟨A_star, hAs_sub, hAs_card, hNA_disj, h_comp_or_sp⟩
    · rcases complete_blockade_at_pcomp_global hr (by omega) hℓ hp_cap hL_low hL_high hp_comp_cases
          hη_pos hη_le1 hη₀_pos hη₀_le1 hθ_def hθ_pos hθ_lb hw_nn hWz_sub hWz_active
          (hNs_NT.trans (hNT_Nd.trans hNd_sub_Wz)) hNs_card hD_comp with h1 | h2
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
          rw [div_le_one (by positivity)]
          nlinarith
        calc 10 * (p_comp : ℝ) * (η₀ / (64 * (ℓ : ℝ) * (p_comp : ℝ) ^ 2))
            = η₀ * (10 * (p_comp : ℝ) / (64 * (ℓ : ℝ) * (p_comp : ℝ) ^ 2)) := by ring
          _ ≤ η₀ * 1 := mul_le_mul_of_nonneg_left h_div_le1 (le_of_lt hη₀_pos)
          _ = η₀ := mul_one η₀
      have h_sp_pair : IsWeaklySparseOrCoSparsePair F N_star A_star η₀ := by
        rcases h_comp_or_sp with h_comp | h_xsp
        · exact isWeaklySparseOrCoSparsePair_of_isPurePair hNA_disj (le_of_lt hη₀_pos) (Or.inl h_comp)
        · exact Or.inl ((IsWeaklySparsePair.symm
            (crossEdgeCount_le_of_isXSparseTo F A_star N_star (10 * (p_comp : ℝ) * θ_r) h_xsp)).mono h_10_le)
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

/-- Single inductive step $d \to d + 1$ ($1 \le d \le r - 2$) of the Step 2 cutter-chain dichotomy:
either produces **(Global Cap)**, **(Global SplitOrCross)**, or `HasActiveLeafSplit F r L_max η₀ W_z`,
or extends the cutter chain to depth $d + 1$. -/
theorem depth_d_cutter_chain_step {V : Type} [Fintype V] [DecidableEq V]
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
    (hIH : ∀ r' : ℕ, 1 ≤ r' → r' < r → Stage1CombCoCombDichotomyStrongAt r')
    (hfree : IsInducedSubgraphFree F (PkCompl (s + 4 + r)))
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
      exact (hM_step c hc1).trans ((neighborFinsetIn_subset F _ _).trans
        (ih_m ⟨c.1 - 1, by omega⟩ (by dsimp; omega)))
  have hM_last_sub_Wz : M_core ⟨d - 1, by omega⟩ ⊆ W_z := hM_core_sub_Wz ⟨d - 1, by omega⟩
  let N_d := neighborFinsetIn F (z ⟨d - 1, by omega⟩) (M_core ⟨d - 1, by omega⟩)
  let A_d := M_core ⟨d - 1, by omega⟩ \ N_d
  have hNd_sub_Wz : N_d ⊆ W_z := (neighborFinsetIn_subset F _ _).trans hM_last_sub_Wz
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
    · -- Extend cutter chain to depth d + 1
      right; right; right
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
      · rw [hz'_lt ⟨0, by omega⟩ (by dsimp; omega)]; exact hz0
      · rw [hM'_lt ⟨0, by omega⟩ (by dsimp; omega)]; exact hM0_sub
      · rintro ⟨c_val, hc_lt⟩ hc1
        by_cases hcd : c_val < d
        · rw [hM'_lt ⟨c_val, hc_lt⟩ hcd, hz'_lt ⟨c_val - 1, by omega⟩ (by dsimp; omega),
            hM'_lt ⟨c_val - 1, by omega⟩ (by dsimp; omega)]
          exact hM_step ⟨c_val, hcd⟩ hc1
        · have hc_eq : c_val = d := by dsimp at hc1 hcd; omega
          subst c_val
          rw [hM'_last, hz'_lt ⟨d - 1, by omega⟩ (by dsimp; omega),
            hM'_lt ⟨d - 1, by omega⟩ (by dsimp; omega)]
          exact hNs_sub_Nd
      · rintro ⟨c_val, hc_lt⟩ hc1
        by_cases hcd : c_val < d
        · rw [hz'_lt ⟨c_val, hc_lt⟩ hcd, hz'_lt ⟨c_val - 1, by omega⟩ (by dsimp; omega),
            hM'_lt ⟨c_val - 1, by omega⟩ (by dsimp; omega)]
          exact hz_step ⟨c_val, hcd⟩ hc1
        · have hc_eq : c_val = d := by dsimp at hc1 hcd; omega
          subst c_val
          rw [hz'_last, hz'_lt ⟨d - 1, by omega⟩ (by dsimp; omega),
            hM'_lt ⟨d - 1, by omega⟩ (by dsimp; omega)]
          obtain ⟨hvM, hv_notN⟩ := Finset.mem_sdiff.mp hz_d_in
          exact ⟨hvM, fun hadj => hv_notN ((mem_neighborFinsetIn_iff F _ _ z_d).mpr ⟨hvM, hadj⟩)⟩
      · rw [hM'_last]; exact hNs_card
      · rw [hz'_last, hM'_last]; exact hz_d_low
      · rw [hz'_last, hM'_last]; exact hz_d_high
    · -- No balanced cutter in A_d: apply internal_depth_d_stem_promotion at τ = η₀ / 2
      push_neg at h_bal
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
        rw [hM_seq'_lt 0 (by dsimp; omega)]; exact hM0_sub.trans hWz_sub_Bi
      have hM_seq'_step : ∀ c : Fin d, M_seq' c.succ ⊆ neighborFinsetIn F (z c) (M_seq' c.castSucc) := by
        intro c
        rw [hM_seq'_lt c.castSucc c.2]
        by_cases hc1 : c.1 + 1 < d
        · rw [hM_seq'_lt c.succ hc1]
          have h_st := hM_step ⟨c.1 + 1, hc1⟩ (by dsimp; omega)
          have h_eq : (⟨(⟨c.1 + 1, hc1⟩ : Fin d).1 - 1, by omega⟩ : Fin d) = c := by ext; dsimp
          rwa [h_eq] at h_st
        · have hc_last : c.succ = Fin.last d := by ext; dsimp; omega
          have hc_eq : c = ⟨d - 1, by omega⟩ := by ext; dsimp; omega
          rw [hc_last, hM_seq'_last, hc_eq]
          exact hNs_sub_Nd
      have hz_seq'_step : ∀ c : Fin d, ∀ hc1 : 1 ≤ c.1,
          z c ∈ M_seq' ⟨c.1 - 1, by omega⟩ ∧ ¬F.Adj (z ⟨c.1 - 1, by omega⟩) (z c) := by
        intro c hc1
        rw [hM_seq'_lt ⟨c.1 - 1, by omega⟩ (by dsimp; omega)]
        exact hz_step c hc1
      have hAh_in : ∀ v ∈ A_half, v ∈ M_seq' ⟨d - 1, by omega⟩ ∧ ¬F.Adj (z ⟨d - 1, by omega⟩) v := by
        intro v hv
        rw [hM_seq'_lt ⟨d - 1, by omega⟩ (by dsimp; omega)]
        obtain ⟨hvM, hv_notN⟩ := Finset.mem_sdiff.mp (hAh_sub hv)
        exact ⟨hvM, fun hadj => hv_notN ((mem_neighborFinsetIn_iff F _ _ v).mpr ⟨hvM, hadj⟩)⟩
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
      · -- Stops early: 2-block Type II split (R_end, A_half)
        rw [hM_seq'_last] at hR_sub hR_half
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
      · -- Internal stem promotion: resolve recursive call at r' = r - 1 - d
        rw [hM_seq'_last] at hN'_sub hcomb'
        let r' := r - 1 - d
        have hr'1 : 1 ≤ r' := by omega
        have hr'r : r' < r := by omega
        have hr_sum' : r' + d + 1 = r := by omega
        have hfree_r' : IsInducedSubgraphFree F (PkCompl ((s + 1 + d) + 4 + r')) := by
          rwa [show (s + 1 + d) + 4 + r' = s + 4 + r by omega]
        have hw_sub_ge : (η₀ / 4) * (N_star.card : ℝ) ≤
            max ((N_star.card : ℝ) / (16 * (k_comb : ℝ) ^ 2)) ((η₀ / 2 / 2) * (N_star.card : ℝ)) := by
          rw [show η₀ / 4 = η₀ / 2 / 2 by ring]
          exact le_max_right _ _
        obtain ⟨hw_sub_lb, hw_sub_cap⟩ :=
          internal_promo_width_bounds hr hd1 hr'1 hr_sum' hp_64 hL_low hL_p hη_pos hη_le1 hη₀_pos
            hη₀_lb hw_nn hWz_active hNs_card hw_sub_ge
        rcases resolve_recursive_comb_call hr hr'1 hr'r hr_sum' (by omega) hp_64 hL_low hL_p
            hη_pos hη_ub hη₀_pos hη₀_le_out hη₀_lb (hIH r' hr'1 hr'r) hfree_r' hWz_sub
            hWz_active hNs_sub_Wz hNs_card (by omega) hN'_sub hcomb' hstems'' hw_ge
            (le_max_left _ _) hw_sub_lb hw_sub_cap with
          h_cap | h_soc | ⟨k_sp, U_sp, hk64, hkL, hU_sp⟩
        · exact Or.inl h_cap
        · exact Or.inr (Or.inl h_soc)
        · exact Or.inr (Or.inr (Or.inl (hasActiveLeafSplit_of_type1 hk64 hkL hU_sp)))

/-- **Step 2 Inductive Cutter-Chain Dichotomy** (`depth_d_cutter_chain_dichotomy`):
By induction on `rem = r - 1 - d` ($1 \le d \le r - 1$), any depth-$d$ balanced cutter chain
inside an active leaf $W_z \subseteq B_i$ produces **(Global Cap)**, **(Global SplitOrCross)**,
or `HasActiveLeafSplit F r L_max η₀ W_z`. -/
theorem depth_d_cutter_chain_dichotomy {V : Type} [Fintype V] [DecidableEq V]
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
    (hIH : ∀ r' : ℕ, 1 ≤ r' → r' < r → Stage1CombCoCombDichotomyStrongAt r')
    (hfree : IsInducedSubgraphFree F (PkCompl (s + 4 + r)))
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
    exact depth_r_minus_1_cutter_chain hr hd1 (by omega) hℓ hp_cap hp_comp_cases hL_low hL_high
      hη_pos hη_ub hη₀_pos hη₀_le_out hθ_def hθ_pos hθ_ub hθ_lb hfree hcomb hstems hw_ge hij
      hWz_sub_Bi hWz_sub hWz_active z M_core hz0 hM0_sub hM_step hz_step hM_last_card hNd_low hAd_low
  | succ rem' ih =>
    intro d hd1 h_sum z M_core hz0 hM0_sub hM_step hz_step hM_last_card hNd_low hAd_low
    rcases depth_d_cutter_chain_step hr hd1 (by omega) hs hℓ hp_cap hL_low hL_high hη_pos hη_ub
        hη₀_pos hη₀_le_out hη₀_ub19 hη₀_lb hθ_pos hθ_ub hθ_lb hIH hfree hcomb hstems hw_ge hij
        hWz_sub_Bi hWz_sub hWz_active z M_core hz0 hM0_sub hM_step hz_step hM_last_card hNd_low hAd_low with
      h_cap | h_soc | h_split | ⟨z', M_core', hz0', hM0', hM_st', hz_st', hM_card', hN_low', hA_low'⟩
    · exact Or.inl h_cap
    · exact Or.inr (Or.inl h_soc)
    · exact Or.inr (Or.inr h_split)
    · exact ih (d + 1) (by omega) (by omega) z' M_core' hz0' hM0' hM_st' hz_st'
        (by simpa using hM_card') (by simpa using hN_low') (by simpa using hA_low')

/-- **Step 2 Entry Point (`single_u_depth_r_pred_split`)**:
Given an active leaf $W_z \subseteq B_i$, a core $M_i^* \subseteq W_z$ with $|M_i^*| \ge 2^{-3} |W_z|$,
and a $2^{-20}$-balanced cutter $u \in B_j$ ($j \neq i$) on $M_i^*$, we obtain either **(Global Cap)**,
**(Global SplitOrCross)**, or `HasActiveLeafSplit F r L_max η₀ W_z`. -/
theorem single_u_depth_r_pred_split {V : Type} [Fintype V] [DecidableEq V]
    {F : SimpleGraph V} {S U_ambient W_z M_i_star : Finset V}
    {r s ℓ p_cap p_comp L_max : ℕ} {η_out η₀ θ_r w : ℝ}
    {a : Fin ℓ → V} {B : Fin ℓ → Finset V} {stems : Fin ℓ → Fin s → V}
    {i j : Fin ℓ} {u : V}
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
    (hIH : ∀ r' : ℕ, 1 ≤ r' → r' < r → Stage1CombCoCombDichotomyStrongAt r')
    (hfree : IsInducedSubgraphFree F (PkCompl (s + 4 + r)))
    (hcomb : IsCombOrCoCombIn F S ℓ w a B)
    (hstems : HasPerHandleApexStems F S ℓ s a B stems)
    (hw_ge : combMinWidth r η_out p_cap ≤ w)
    (hij : i ≠ j) (hu_Bj : u ∈ B j)
    (hWz_sub_Bi : W_z ⊆ B i) (hWz_sub : W_z ⊆ U_ambient)
    (hWz_active : w / (L_max : ℝ) ^ (splitTreeD r) ≤ (W_z.card : ℝ))
    (hMi_sub : M_i_star ⊆ W_z)
    (hMi_card : (W_z.card : ℝ) / (2 : ℝ) ^ 3 ≤ (M_i_star.card : ℝ))
    (hu_low : (2 : ℝ)⁻¹ ^ 20 * (M_i_star.card : ℝ) ≤ ((neighborFinsetIn F u M_i_star).card : ℝ))
    (hu_high : (2 : ℝ)⁻¹ ^ 20 * (M_i_star.card : ℝ) ≤ ((M_i_star \ neighborFinsetIn F u M_i_star).card : ℝ)) :
    (∃ U : Fin p_cap → Finset V,
      IsWeaklySparseOrCoSparseBlockadeIn F U_ambient p_cap
        ((2 : ℝ) ^ (-(200 * (r : ℝ) ^ 2)) * η_out ^ r * (p_cap : ℝ) ^ (-(capExpE r : ℝ)) * w)
        η_out U) ∨
    (∃ k : ℕ, L_max ≤ k ∧ k ≤ p_cap ∧
      ∃ U : Fin k → Finset V,
        IsWeaklySparseOrCoSparseBlockadeIn F U_ambient k
          (w / ((2 : ℝ) ^ (60 * r) * (k : ℝ) ^ (2 * splitTreeD r))) η_out U) ∨
    HasActiveLeafSplit F r L_max η₀ W_z := by
  exact depth_d_cutter_chain_dichotomy hr hs hℓ hp_cap hp_comp_cases hL_low hL_high hη_pos hη_ub
    hη₀_pos hη₀_le_out hη₀_ub19 hη₀_lb hθ_def hθ_pos hθ_ub hθ_lb hIH hfree hcomb hstems hw_ge
    hij hWz_sub_Bi hWz_sub hWz_active (r - 2) 1 le_rfl (by omega)
    (fun _ => u) (fun _ => M_i_star) hu_Bj hMi_sub
    (fun c hc1 => by fin_cases c; omega)
    (fun c hc1 => by fin_cases c; omega)
    (by simpa using hMi_card) hu_low hu_high

/-- Width lower bounds (`hw_sub_lb` and `hw_sub_cap`) for `resolve_recursive_comb_call` when
`union_pool_stem_promotion` promotes at $\tau = \frac{\eta_{\mathrm{out}}}{8 \ell}$ ($w_{\mathrm{sub}} \ge \frac{\eta_{\mathrm{out}}}{16 \ell} |M_i^*|$). -/
lemma union_promo_width_bounds {r ℓ p_cap L_max : ℕ} {η_out η₀ w w_sub : ℝ}
    {W_z M_i : Finset V}
    (hr : 2 ≤ r) (hℓ : 64 ≤ ℓ) (hp_cap : ℓ ≤ p_cap)
    (hL_low : 2 ≤ L_max) (hL_high : L_max ≤ ℓ)
    (hη_pos : 0 < η_out)
    (hη₀_lb : (2 : ℝ)⁻¹ ^ (120 * r + 2) * (p_cap : ℝ)⁻¹ ^ (4 * splitTreeD r) * η_out ≤ η₀)
    (hw_nn : 0 ≤ w)
    (hWz_active : w / (L_max : ℝ) ^ (splitTreeD r) ≤ (W_z.card : ℝ))
    (hMi_card : (W_z.card : ℝ) / (2 : ℝ) ^ 3 ≤ (M_i.card : ℝ))
    (hw_sub_ge : (η_out / (16 * (ℓ : ℝ))) * (M_i.card : ℝ) ≤ w_sub) :
    ((2 : ℝ)⁻¹ ^ (145 * r + 10) * (p_cap : ℝ)⁻¹ ^ (5 * splitTreeD r + 2) * η_out * w ≤ w_sub) ∧
    ((2 : ℝ)⁻¹ ^ ((120 * r + 2) * (r - 1) + 25 * r + 10) *
      (p_cap : ℝ)⁻¹ ^ ((4 * (r - 1) + 5) * splitTreeD r + 2) *
      η_out ^ r * w ≤ η₀ ^ (r - 1) * w_sub) := by
  have hp_pos : (0 : ℝ) < (p_cap : ℝ) := Nat.cast_pos.mpr (by omega)
  have hℓ_pos : (0 : ℝ) < (ℓ : ℝ) := Nat.cast_pos.mpr (by omega)
  have hL_pos : (0 : ℝ) < (L_max : ℝ) := Nat.cast_pos.mpr (by omega)
  have hp_inv_le1 : (p_cap : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr (by omega))
  have hL_p : (L_max : ℝ) ^ (splitTreeD r) ≤ (p_cap : ℝ) ^ (splitTreeD r) :=
    pow_le_pow_left₀ (by positivity) (Nat.cast_le.mpr (le_trans hL_high hp_cap)) (splitTreeD r)
  have hWz_pcap : (p_cap : ℝ)⁻¹ ^ (splitTreeD r) * w ≤ (W_z.card : ℝ) := by
    rw [inv_pow, ← div_eq_inv_mul]
    exact le_trans (div_le_div_of_nonneg_left hw_nn (by positivity) hL_p) hWz_active
  have hMi_lb : (2 : ℝ)⁻¹ ^ 3 * (p_cap : ℝ)⁻¹ ^ (splitTreeD r) * w ≤ (M_i.card : ℝ) := by
    calc (2 : ℝ)⁻¹ ^ 3 * (p_cap : ℝ)⁻¹ ^ (splitTreeD r) * w
        = ((p_cap : ℝ)⁻¹ ^ (splitTreeD r) * w) / (2 : ℝ) ^ 3 := by rw [inv_pow (a := (2 : ℝ))]; ring
      _ ≤ (W_z.card : ℝ) / (2 : ℝ) ^ 3 := div_le_div_of_nonneg_right hWz_pcap (by positivity)
      _ ≤ (M_i.card : ℝ) := hMi_card
  have h_base : (2 : ℝ)⁻¹ ^ 7 * (p_cap : ℝ)⁻¹ ^ (splitTreeD r + 1) * η_out * w ≤ w_sub := by
    have h_ell_inv : (p_cap : ℝ)⁻¹ ≤ (ℓ : ℝ)⁻¹ :=
      inv_anti₀ hℓ_pos (Nat.cast_le.mpr hp_cap)
    have h_16_inv : (2 : ℝ)⁻¹ ^ 4 * (p_cap : ℝ)⁻¹ * η_out ≤ η_out / (16 * (ℓ : ℝ)) := by
      calc (2 : ℝ)⁻¹ ^ 4 * (p_cap : ℝ)⁻¹ * η_out
          ≤ (2 : ℝ)⁻¹ ^ 4 * (ℓ : ℝ)⁻¹ * η_out :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h_ell_inv (by positivity)) (le_of_lt hη_pos)
        _ = η_out / (16 * (ℓ : ℝ)) := by ring
    calc (2 : ℝ)⁻¹ ^ 7 * (p_cap : ℝ)⁻¹ ^ (splitTreeD r + 1) * η_out * w
        = ((2 : ℝ)⁻¹ ^ 4 * (p_cap : ℝ)⁻¹ * η_out) *
            ((2 : ℝ)⁻¹ ^ 3 * (p_cap : ℝ)⁻¹ ^ (splitTreeD r) * w) := by
          rw [show (7 : ℕ) = 4 + 3 by omega, pow_add, pow_succ]; ring
      _ ≤ (η_out / (16 * (ℓ : ℝ))) * (M_i.card : ℝ) :=
          mul_le_mul h_16_inv hMi_lb (by positivity) (by positivity)
      _ ≤ w_sub := hw_sub_ge
  constructor
  · -- Part 1: hw_sub_lb
    have h2_le : (2 : ℝ)⁻¹ ^ (145 * r + 10) ≤ (2 : ℝ)⁻¹ ^ 7 :=
      pow_le_pow_of_le_one (by positivity) (by norm_num) (by omega)
    have hp_le : (p_cap : ℝ)⁻¹ ^ (5 * splitTreeD r + 2) ≤ (p_cap : ℝ)⁻¹ ^ (splitTreeD r + 1) :=
      pow_le_pow_of_le_one (by positivity) hp_inv_le1 (by omega)
    refine le_trans ?_ h_base
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul h2_le hp_le (by positivity) (by positivity)) (le_of_lt hη_pos))
      hw_nn
  · -- Part 2: hw_sub_cap
    have h_η₀_r1 : ((2 : ℝ)⁻¹ ^ (120 * r + 2)) ^ (r - 1) *
        ((p_cap : ℝ)⁻¹ ^ (4 * splitTreeD r)) ^ (r - 1) * η_out ^ (r - 1) ≤ η₀ ^ (r - 1) := by
      have h1 := pow_le_pow_left₀ (by positivity) hη₀_lb (r - 1)
      rwa [mul_pow, mul_pow] at h1
    rw [← pow_mul, ← pow_mul] at h_η₀_r1
    have h2_le : (2 : ℝ)⁻¹ ^ ((120 * r + 2) * (r - 1) + 25 * r + 10) ≤
        (2 : ℝ)⁻¹ ^ ((120 * r + 2) * (r - 1)) * (2 : ℝ)⁻¹ ^ 7 := by
      rw [← pow_add]
      exact pow_le_pow_of_le_one (by positivity) (by norm_num) (by omega)
    have hp_le : (p_cap : ℝ)⁻¹ ^ ((4 * (r - 1) + 5) * splitTreeD r + 2) ≤
        (p_cap : ℝ)⁻¹ ^ (4 * splitTreeD r * (r - 1)) * (p_cap : ℝ)⁻¹ ^ (splitTreeD r + 1) := by
      rw [← pow_add]
      have h_exp : 4 * splitTreeD r * (r - 1) + (splitTreeD r + 1) ≤
          (4 * (r - 1) + 5) * splitTreeD r + 2 := by
        have : 4 * splitTreeD r * (r - 1) + splitTreeD r = (4 * (r - 1) + 1) * splitTreeD r := by ring
        have : (4 * (r - 1) + 1) * splitTreeD r ≤ (4 * (r - 1) + 5) * splitTreeD r :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      exact pow_le_pow_of_le_one (by positivity) hp_inv_le1 h_exp
    have hη_eq : η_out ^ r = η_out ^ (r - 1) * η_out := by
      conv_lhs => rw [show r = (r - 1) + 1 by omega, pow_succ]
    calc (2 : ℝ)⁻¹ ^ ((120 * r + 2) * (r - 1) + 25 * r + 10) *
          (p_cap : ℝ)⁻¹ ^ ((4 * (r - 1) + 5) * splitTreeD r + 2) * η_out ^ r * w
        ≤ ((2 : ℝ)⁻¹ ^ ((120 * r + 2) * (r - 1)) * (2 : ℝ)⁻¹ ^ 7) *
            ((p_cap : ℝ)⁻¹ ^ (4 * splitTreeD r * (r - 1)) * (p_cap : ℝ)⁻¹ ^ (splitTreeD r + 1)) *
            (η_out ^ (r - 1) * η_out) * w := by
          rw [hη_eq]
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul h2_le hp_le (by positivity) (by positivity))
              (by positivity)) hw_nn
      _ = ((2 : ℝ)⁻¹ ^ ((120 * r + 2) * (r - 1)) *
            (p_cap : ℝ)⁻¹ ^ (4 * splitTreeD r * (r - 1)) * η_out ^ (r - 1)) *
            ((2 : ℝ)⁻¹ ^ 7 * (p_cap : ℝ)⁻¹ ^ (splitTreeD r + 1) * η_out * w) := by ring
      _ ≤ η₀ ^ (r - 1) * w_sub := by
          have hη₀_pos : 0 < η₀ := lt_of_lt_of_le (by positivity) hη₀_lb
          exact mul_le_mul h_η₀_r1 h_base (by positivity) (by positivity)

/-- **Single Iteration on Active Leaves (`active_leaves_step_or_global`)**:
Given active leaves $W_z : \text{Fin } \ell \to \text{Finset } V$ ($W_z\, i \subseteq B\, i$,
$|W_z\, i| \ge w / L_{\max}^{D_r}$), Steps 1, 2, 3a, and 3b yield either **(Global Cap)**,
**(Global SplitOrCross)**, or `HasActiveLeafSplit F r L_max η₀ (W_z i)` for some $i \in \text{Fin } \ell$. -/
theorem active_leaves_step_or_global {V : Type} [Fintype V] [DecidableEq V]
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
    (hIH : ∀ r' : ℕ, 1 ≤ r' → r' < r → Stage1CombCoCombDichotomyStrongAt r')
    (hfree : IsInducedSubgraphFree F (PkCompl (s + 4 + r)))
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
  have hp_64 : 64 ≤ p_cap := le_trans hℓ hp_cap
  have hL_p : L_max ≤ p_cap := le_trans hL_high hp_cap
  have hη_le1 : η_out ≤ 1 := le_trans hη_ub (by norm_num)
  have hw_pos : 0 < w := by
    have : 0 < combMinWidth r η_out p_cap := by unfold combMinWidth; positivity
    linarith
  have hw_nn : 0 ≤ w := le_of_lt hw_pos
  have hL_pos : (0 : ℝ) < (L_max : ℝ) := Nat.cast_pos.mpr (by omega)
  have hWz_sub_U : ∀ i : Fin ℓ, W_z i ⊆ U_ambient := fun i => (hWz_sub_B i).trans (hB_sub i)
  -- Step 1: Level-1 Gallai Core Extraction on each W_z i (at d = 0)
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
    -- Step 2: Check if any external vertex u ∈ M_star j is 2^-20-balanced on M_star i
    by_cases h_step2 : ∃ (i j : Fin ℓ), i ≠ j ∧ ∃ u ∈ M_star j,
        (2 : ℝ)⁻¹ ^ 20 * ((M_star i).card : ℝ) ≤ ((neighborFinsetIn F u (M_star i)).card : ℝ) ∧
        (2 : ℝ)⁻¹ ^ 20 * ((M_star i).card : ℝ) ≤ (((M_star i) \ neighborFinsetIn F u (M_star i)).card : ℝ)
    · obtain ⟨i, j, hij, u, hu_Mj, hu_low, hu_high⟩ := h_step2
      rcases single_u_depth_r_pred_split hr hs hℓ hp_cap hp_comp_cases hL_low hL_high hη_pos hη_ub
          hη₀_pos hη₀_le_out hη₀_ub19 hη₀_lb hθ_def hθ_pos hθ_ub hθ_lb hIH hfree hcomb hstems hw_ge
          hij (hMs_sub_B j hu_Mj) (hWz_sub_B i) (hWz_sub_U i) (hWz_active i)
          (hMs_sub_Wz i) (hMs_card i) hu_low hu_high with
        h_cap | h_soc | h_split
      · exact Or.inl h_cap
      · exact Or.inr (Or.inl h_soc)
      · exact Or.inr (Or.inr ⟨i, h_split⟩)
    · -- Step 3: No balanced external cutter exists; apply union_pool_stem_promotion on each M_star i
      push_neg at h_step2
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
            HasPerHandleApexStems F S k_comb (s + 1) u B' stems') := by
        intro i
        rcases union_pool_stem_promotion hcomb hstems (hMs_sub_B i) (hMs_ne i) hτ_pos hτ_ub
            ((Finset.filter_subset _ _).trans (hU_ext_sub i))
            (Finset.sdiff_subset.trans (hU_ext_sub i))
            (fun u hu => (Finset.mem_filter.mp hu).2) (hD_pool_deg i) with
          ⟨M_i', h1, h2, h3, h4⟩ | h_pr
        · exact Or.inl ⟨M_i', h1, h2, h3, h4⟩
        · exact Or.inr h_pr
      by_cases h_promo : ∃ i : Fin ℓ,
          ∃ (k_comb : ℕ) (u : Fin k_comb → V) (B' : Fin k_comb → Finset V)
             (stems' : Fin k_comb → Fin (s + 1) → V),
            512 < k_comb ∧ (k_comb : ℝ) < τ⁻¹ ∧
            (∀ q : Fin k_comb, B' q ⊆ M_star i) ∧
            IsCombOrCoCombIn F S k_comb
              (max (((M_star i).card : ℝ) / (16 * (k_comb : ℝ) ^ 2)) ((τ / 2) * ((M_star i).card : ℝ))) u B' ∧
            HasPerHandleApexStems F S k_comb (s + 1) u B' stems'
      · -- Case 3a: Promotion on some i → resolve_recursive_comb_call at r' = r - 1, d = 0
        obtain ⟨i, k_comb, u_c, B', stems', hk_512, _, hB'_sub, hcomb', hstems'⟩ := h_promo
        have hr'1 : 1 ≤ r - 1 := by omega
        have hr'r : r - 1 < r := by omega
        have hr_sum : (r - 1) + 0 + 1 = r := by omega
        have hfree_r' : IsInducedSubgraphFree F (PkCompl ((s + 1) + 4 + (r - 1))) := by
          rwa [show (s + 1) + 4 + (r - 1) = s + 4 + r by omega]
        have hw_sub_ge : (η_out / (16 * (ℓ : ℝ))) * ((M_star i).card : ℝ) ≤
            max (((M_star i).card : ℝ) / (16 * (k_comb : ℝ) ^ 2)) ((τ / 2) * ((M_star i).card : ℝ)) := by
          have h_eq : η_out / (16 * (ℓ : ℝ)) = τ / 2 := by unfold τ; ring
          rw [h_eq]
          exact le_max_right _ _
        obtain ⟨hw_sub_lb, hw_sub_cap⟩ :=
          union_promo_width_bounds hr hℓ hp_cap hL_low hL_high hη_pos hη₀_lb hw_nn
            (hWz_active i) (hMs_card i) hw_sub_ge
        rcases resolve_recursive_comb_call (d := 0) hr hr'1 hr'r hr_sum (by omega) hp_64 hL_low hL_p
            hη_pos hη_ub hη₀_pos hη₀_le_out hη₀_lb (hIH (r - 1) hr'1 hr'r) hfree_r' (hWz_sub_U i)
            (hWz_active i) (hMs_sub_Wz i) (by simpa using hMs_card i) (by omega)
            hB'_sub hcomb' hstems' hw_ge (le_max_left _ _) hw_sub_lb hw_sub_cap with
          h_cap | h_soc | ⟨k_sp, U_sp, hk64, hkL, hU_sp⟩
        · exact Or.inl h_cap
        · exact Or.inr (Or.inl h_soc)
        · exact Or.inr (Or.inr ⟨i, hasActiveLeafSplit_of_type1 hk64 hkL hU_sp⟩)
      · -- Case 3b: All i stop → bipartite_double_counting_dichotomy gives Global SplitOrCross at k = ℓ
        right; left
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
          · left
            exact le_trans ((hM' i).2.2.1 u hu_S) h_τ_bound
          · right
            have hu_D : u ∈ D_pool i := Finset.mem_sdiff.mpr ⟨hu_ext, hu_S⟩
            exact le_trans ((hM' i).2.2.2 u hu_D) h_τ_bound
        exact ⟨ℓ, hL_high, hp_cap, M',
          bipartite_double_counting_dichotomy (by omega) hη_pos hM'_block hM'_part⟩

/-- **Main Inductive Step (`stage1_comb_cocomb_dichotomy_strong_step`)**:
Assuming `Stage1CombCoCombDichotomyStrongAt r'` holds for all $1 \le r' < r$ ($r \ge 2$),
`Stage1CombCoCombDichotomyStrongAt r` holds! -/
theorem stage1_comb_cocomb_dichotomy_strong_step {r : ℕ} (hr : 2 ≤ r)
    (hIH : ∀ r' : ℕ, 1 ≤ r' → r' < r → Stage1CombCoCombDichotomyStrongAt r') :
    Stage1CombCoCombDichotomyStrongAt r := by
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
    have h_eq : η_out / (4 * β_inv ^ 2) * β_inv ^ 2 = η_out / 4 := by
      field_simp
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
  -- Component cap p_comp and Gallai core parameter θ_r
  let p_raw := ⌈8 * (ℓ : ℝ) ^ 2 * η₀⁻¹⌉₊
  let p_comp := min p_raw p_cap
  have hp_comp_cases : p_comp = p_cap ∨ (p_comp < p_cap ∧ 8 * (ℓ : ℝ) ^ 2 * η₀⁻¹ ≤ (p_comp : ℝ)) := by
    by_cases h_cmp : p_cap ≤ p_raw
    · exact Or.inl (Nat.min_eq_right h_cmp)
    · push_neg at h_cmp
      have h_eq : p_comp = p_raw := Nat.min_eq_left (le_of_lt h_cmp)
      refine Or.inr ⟨by omega, ?_⟩
      rw [h_eq]
      exact Nat.le_ceil _
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
  -- Outer loop by induction on N ≥ ∑ i : Fin ℓ, (L_max - (T i).leaves.card)
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
      · -- Every T i has < L_max leaves, so each T i has an active leaf W_z i
        push_neg at h_some_ge
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
        rcases active_leaves_step_or_global hr hs hℓ hp_cap hp_comp_cases hL_low hL_high
            hη_pos hη_ub hη₀_pos hη₀_le_out hη₀_ub19 hη₀_lb rfl hθ_pos hθ_ub hθ_lb hIH
            hfree hcomb hstems hw_ge hB_sub_U hWz_sub_B hWz_active_w with
          h_cap | h_soc | ⟨i₀, k_sp, w_sp, U_sp, hk2, hkL, hU_sp, h_split⟩
        · exact Or.inr h_cap
        · exact Or.inl h_soc
        · -- Active leaf W_z i₀ splits in T i₀, strictly decreasing ∑ i, (L_max - (T i).leaves.card)!
          let T_new_i₀ := (T i₀).split_active_leaf (hWz_mem i₀) (hWz_active_B i₀)
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

/-- **Strong Inductive Stage-1 Comb/Co-Comb Dichotomy for All $r \ge 1$**:
`Stage1CombCoCombDichotomyStrongAt r` holds for every integer $r \ge 1$. -/
theorem stage1_comb_cocomb_dichotomy_strong_all_r (r : ℕ) (hr : 1 ≤ r) :
    Stage1CombCoCombDichotomyStrongAt r := by
  induction r using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn1 : n = 1
    · subst hn1; exact stage1_comb_cocomb_dichotomy_strong_r1
    · have hn2 : 2 ≤ n := by omega
      exact stage1_comb_cocomb_dichotomy_strong_step hn2 (fun r' hr'1 hr'n => ih r' hr'n hr'1)

/-- **Theorem 7(1) (`stage1_comb_cocomb_dichotomy_all_r`, Inductive Depth-$r$ Stage-1 Comb/Co-Comb Dichotomy)**:
For every integer $r \ge 1$, `Stage1CombCoCombDichotomyAt r` (`Proposition 2_r` of `main.tex`) holds. -/
theorem stage1_comb_cocomb_dichotomy_all_r (r : ℕ) (hr : 1 ≤ r) :
    Stage1CombCoCombDichotomyAt r :=
  (stage1_comb_cocomb_dichotomy_strong_all_r r hr).to_weak

/-- **Proposition 2(1) (`prop2_comb_cocomb_dichotomy`, Simultaneous Comb/Co-Comb Dichotomy for $\overline{P_{s+6}}$-Free Graphs)**:
Specialization of Theorem 7(1) at depth $r = 2$. -/
theorem prop2_comb_cocomb_dichotomy : Stage1CombCoCombDichotomyAt 2 :=
  stage1_comb_cocomb_dichotomy_all_r 2 (by decide)

/-- **Proposition 4(1) (`prop4_comb_cocomb_dichotomy`, Simultaneous Comb/Co-Comb Dichotomy for $\overline{P_{s+7}}$-Free Graphs)**:
Specialization of Theorem 7(1) at depth $r = 3$. -/
theorem prop4_comb_cocomb_dichotomy : Stage1CombCoCombDichotomyAt 3 :=
  stage1_comb_cocomb_dichotomy_all_r 3 (by decide)

/-- **Lemma 13 (`level3_recursive_gallai_core_split`, Level-3 Recursive Gallai Core Split for $\overline{P_{s+7}}$-Free Combs and Co-Combs)**:
Specialization of `single_u_depth_r_pred_split` at depth $r = 3$ (discharging `hIH` unconditionally
via `stage1_comb_cocomb_dichotomy_strong_all_r`). -/
theorem level3_recursive_gallai_core_split {V : Type} [Fintype V] [DecidableEq V]
    {F : SimpleGraph V} {S U_ambient W_z M_i_star : Finset V}
    {s ℓ p_cap p_comp L_max : ℕ} {η_out η₀ θ₃ w : ℝ}
    {a : Fin ℓ → V} {B : Fin ℓ → Finset V} {stems : Fin ℓ → Fin s → V}
    {i j : Fin ℓ} {u : V}
    (hs : 1 ≤ s) (hℓ : 64 ≤ ℓ) (hp_cap : ℓ ≤ p_cap)
    (hp_comp_cases : p_comp = p_cap ∨ (p_comp < p_cap ∧ 8 * (ℓ : ℝ) ^ 2 * η₀⁻¹ ≤ (p_comp : ℝ)))
    (hL_low : 2 ≤ L_max) (hL_high : L_max ≤ ℓ)
    (hη_pos : 0 < η_out) (hη_ub : η_out ≤ (2 : ℝ)⁻¹ ^ 16)
    (hη₀_pos : 0 < η₀) (hη₀_le_out : η₀ ≤ η_out)
    (hη₀_ub19 : η₀ ≤ (2 : ℝ)⁻¹ ^ 19)
    (hη₀_lb : (2 : ℝ)⁻¹ ^ (120 * 3 + 2) * (p_cap : ℝ)⁻¹ ^ (4 * splitTreeD 3) * η_out ≤ η₀)
    (hθ_def : θ₃ = η₀ / (64 * (ℓ : ℝ) * (p_comp : ℝ) ^ 2))
    (hθ_pos : 0 < θ₃) (hθ_ub : θ₃ ≤ 1 / (64 * (ℓ : ℝ) ^ 2))
    (hθ_lb : (2 : ℝ)⁻¹ ^ (120 * 3 + 8) * (p_cap : ℝ)⁻¹ ^ (4 * splitTreeD 3 + 3) * η_out ≤ θ₃)
    (hfree : IsInducedSubgraphFree F (PkCompl (s + 4 + 3)))
    (hcomb : IsCombOrCoCombIn F S ℓ w a B)
    (hstems : HasPerHandleApexStems F S ℓ s a B stems)
    (hw_ge : combMinWidth 3 η_out p_cap ≤ w)
    (hij : i ≠ j) (hu_Bj : u ∈ B j)
    (hWz_sub_Bi : W_z ⊆ B i) (hWz_sub : W_z ⊆ U_ambient)
    (hWz_active : w / (L_max : ℝ) ^ (splitTreeD 3) ≤ (W_z.card : ℝ))
    (hMi_sub : M_i_star ⊆ W_z)
    (hMi_card : (W_z.card : ℝ) / (2 : ℝ) ^ 3 ≤ (M_i_star.card : ℝ))
    (hu_low : (2 : ℝ)⁻¹ ^ 20 * (M_i_star.card : ℝ) ≤ ((neighborFinsetIn F u M_i_star).card : ℝ))
    (hu_high : (2 : ℝ)⁻¹ ^ 20 * (M_i_star.card : ℝ) ≤ ((M_i_star \ neighborFinsetIn F u M_i_star).card : ℝ)) :
    (∃ U : Fin p_cap → Finset V,
      IsWeaklySparseOrCoSparseBlockadeIn F U_ambient p_cap
        ((2 : ℝ) ^ (-(200 * (3 : ℝ) ^ 2)) * η_out ^ 3 * (p_cap : ℝ) ^ (-(capExpE 3 : ℝ)) * w)
        η_out U) ∨
    (∃ k : ℕ, L_max ≤ k ∧ k ≤ p_cap ∧
      ∃ U : Fin k → Finset V,
        IsWeaklySparseOrCoSparseBlockadeIn F U_ambient k
          (w / ((2 : ℝ) ^ (60 * 3) * (k : ℝ) ^ (2 * splitTreeD 3))) η_out U) ∨
    HasActiveLeafSplit F 3 L_max η₀ W_z :=
  single_u_depth_r_pred_split (by decide) hs hℓ hp_cap hp_comp_cases hL_low hL_high hη_pos hη_ub
    hη₀_pos hη₀_le_out hη₀_ub19 hη₀_lb hθ_def hθ_pos hθ_ub hθ_lb
    (fun r' hr'1 _ => stage1_comb_cocomb_dichotomy_strong_all_r r' hr'1)
    hfree hcomb hstems hw_ge hij hu_Bj hWz_sub_Bi hWz_sub hWz_active hMi_sub hMi_card hu_low hu_high

/-!
## Section 11: Theorem 7(2) — Unconditional Stage-1 Comb Dichotomy for All Paths $P_k$ ($k \ge 6$)

Formalizes Theorem 7(2) (`main.tex` lines 907 & 963): for every integer $k \ge 6$ ($r := k - 5 \ge 1$),
applying Theorem 7(1) (`stage1_comb_cocomb_dichotomy_all_r`) at $s = 1$, $L_{\max} = \ell$, and
$\eta_{\mathrm{out}} = x$ when $w \ge w_{\min}(r, x, p_{\mathrm{cap}})$, together with a singleton
pairwise-pure blockade $(\{v_1\}, \dots, \{v_{k'}\})$ of length $k' = \min(|S|, p_{\mathrm{cap}}) \in [\ell, p_{\mathrm{cap}}]$
when $w < w_{\min}(r, x, p_{\mathrm{cap}})$, unconditionally establishes condition `(CD3)` of
Lemma 7(1) with $C_{\mathrm{comb}}(k) = 3 E_{k-5} + 4 D_{k-5} + 100$, $c_{\mathrm{B}} = 1$, and
$C_{\mathrm{cap}} = 2$.
-/

/-- Any $(\ell, w)$-comb with a shared 1-vertex external apex $v$ (`IsCombExternalApex F S ℓ a B v`)
carries per-handle 1-stems `fun _ _ => v` (`HasPerHandleApexStems F S ℓ 1 a B (fun _ _ => v)`). -/
lemma hasPerHandleApexStems_one_of_isCombExternalApex {V : Type*} [Fintype V] [DecidableEq V]
    {F : SimpleGraph V} {S : Finset V} {ℓ : ℕ} {a : Fin ℓ → V} {B : Fin ℓ → Finset V} {v : V}
    (hv : IsCombExternalApex F S ℓ a B v) :
    HasPerHandleApexStems F S ℓ 1 a B (fun _ _ => v) where
  stem_pos := le_rfl
  stem_in_ambient _ _ := hv.mem_ambient
  stem_injective _ r₁ r₂ _ := Subsingleton.elim r₁ r₂
  stem_not_handle _ j _ := hv.not_apex j
  stem_not_in_blocks _ j _ := hv.not_in_blocks j
  stem_induced_path_compl _ r₁ r₂ := by
    have h_eq : r₁ = r₂ := Subsingleton.elim r₁ r₂
    subst h_eq
    simp
  stem_last_nonadj_handle i _ _ := hv.anticomplete_to_apices i
  stem_init_adj_handle _ r hr := by omega
  stem_complete_to_blocks _ q _ u hu := hv.complete_to_blocks q u hu

/-- Given any subset $S \subseteq V$ and $1 \le k' \le |S|$, taking $k'$ distinct singleton blocks
$\{s_1\}, \dots, \{s_{k'}\} \subseteq S$ yields a pairwise-pure $(k', 1)$-blockade in $F$ inside $S$. -/
lemma singleton_pure_blockade_of_card_ge {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (S : Finset V) {k' : ℕ} (hk' : k' ≤ S.card) :
    ∃ U : Fin k' → Finset V, IsPureBlockadeIn F S k' 1 U := by
  let e := S.equivFin.symm
  let f : Fin k' → V := fun j => (e (Fin.castLE hk' j)).1
  have hf_in_S : ∀ j : Fin k', f j ∈ S := fun j => (e (Fin.castLE hk' j)).2
  have hf_inj : Function.Injective f := by
    intro j₁ j₂ hj
    have h1 : e (Fin.castLE hk' j₁) = e (Fin.castLE hk' j₂) := Subtype.ext hj
    have h2 : Fin.castLE hk' j₁ = Fin.castLE hk' j₂ := e.injective h1
    exact Fin.ext (by simpa using congr_arg Fin.val h2)
  refine ⟨fun j => {f j}, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro j; exact Finset.singleton_subset_iff.mpr (hf_in_S j)
  · intro j; exact Finset.singleton_nonempty (f j)
  · intro j₁ j₂ hj
    exact Finset.disjoint_singleton.mpr (hf_inj.ne hj)
  · intro j; simp
  · intro j₁ j₂ hj
    by_cases hadj : F.Adj (f j₁) (f j₂)
    · left
      intro u hu v hv
      rw [Finset.mem_singleton.mp hu, Finset.mem_singleton.mp hv]
      exact hadj
    · right
      intro u hu v hv
      rw [Finset.mem_singleton.mp hu, Finset.mem_singleton.mp hv]
      exact hadj

/-- Exponent $C_{\mathrm{comb}}(k) := 3 E_{k-5} + 4 D_{k-5} + 100$ for the Stage-1 Comb Dichotomy
of $\overline{P_k}$-free graphs ($k \ge 6$, Theorem 7(2) of `main.tex`). -/
def pathCombExpC (k : ℕ) : ℕ :=
  3 * capExpE (k - 5) + 4 * splitTreeD (k - 5) + 100

/-- Numerical bound $70 r^2 + 3 r + 18 \le 2 E_r + 100$ for all $r \ge 1$, used to absorb
$w_{\min}(r, x, p_{\mathrm{cap}})$ and the cap width into $p_{\mathrm{cap}}^{C_{\mathrm{comb}}(k)}$. -/
lemma seventy_sq_le_two_mul_capExpE (r : ℕ) (hr : 1 ≤ r) :
    70 * r ^ 2 + 3 * r + 18 ≤ 2 * capExpE r + 100 := by
  rcases r with _ | _ | _ | _ | n
  · omega
  · decide
  · decide
  · decide
  · have h16 := hundred_sq_add_four_le_pow_sixteen (n + 4) (by omega)
    have h_Er : capExpE (n + 4) = 8 * (n + 4) * 16 ^ (n + 4) := rfl
    rw [h_Er]
    nlinarith

/-- Since every block of an $(\ell, w)$-blockade inside $S$ is nonempty and pairwise disjoint,
$\ell \le |S|$. -/
lemma comb_blockade_card_ge_ell {V : Type*} [DecidableEq V]
    {F : SimpleGraph V} {S : Finset V} {ℓ : ℕ} {w : ℝ} {B : Fin ℓ → Finset V}
    (hB : IsBlockadeIn F S ℓ w B) :
    ℓ ≤ S.card := by
  have h_sub : Finset.univ.biUnion B ⊆ S :=
    Finset.biUnion_subset.mpr (fun i _ => hB.subset_ambient i)
  calc ℓ = ∑ _i : Fin ℓ, 1 := by simp
    _ ≤ ∑ i : Fin ℓ, (B i).card :=
        Finset.sum_le_sum (fun i _ => Finset.card_pos.mpr (hB.nonempty_blocks i))
    _ = (Finset.univ.biUnion B).card :=
        (Finset.card_biUnion (fun i _ j _ hij => hB.pairwise_disjoint i j hij)).symm
    _ ≤ S.card := Finset.card_le_card h_sub

/-- **Theorem 7(2) (`stage1_comb_dichotomy_condition_for_all_paths`, Unconditional Stage-1 Comb Dichotomy for All Paths $P_k$, $k \ge 6$)**:
For every integer $k \ge 6$ ($r := k - 5 \ge 1$), every $0 < x \le y \le 2^{-16}$, standard cap
$p_{\mathrm{cap}} := \lceil x^{-2} \rceil_+$, every $\ell \in [\lceil \frac{1}{2} y^{-1} \rceil_+, \lfloor x^{-1} \rfloor_+]$,
every $\overline{P_k}$-free graph $F$, and every $(\ell, w)$-comb $((a_i, B_i) : i \in \text{Fin } \ell)$
in $F$ inside $S$ with external apex $v$ (`IsCombExternalApex F S ℓ a B v`) and $w \ge |S| / \ell^{18}$,
$F[S]$ contains a weakly $x$-sparse-or-co-sparse $(k', |S| / (k')^{C_{\mathrm{comb}}(k)})$-blockade
for some integer $k' \in [\ell, p_{\mathrm{cap}}]$ (`C_comb(k) = pathCombExpC k = 3 E_{k-5} + 4 D_{k-5} + 100`),
establishing condition `(CD3)` of Lemma 7(1) with $c_{\mathrm{B}} = 1$ and $C_{\mathrm{cap}} = 2$. -/
theorem stage1_comb_dichotomy_condition_for_all_paths {V : Type} [Fintype V] [DecidableEq V]
    {F : SimpleGraph V} {S : Finset V} {k ℓ : ℕ} {x y w : ℝ}
    {a : Fin ℓ → V} {B : Fin ℓ → Finset V} {v : V}
    (hk : 6 ≤ k)
    (hx_pos : 0 < x) (hxy : x ≤ y) (hy_ub : y ≤ (2 : ℝ)⁻¹ ^ 16)
    (hℓ_low : ⌈(1 / 2 : ℝ) * y⁻¹⌉₊ ≤ ℓ) (hℓ_high : ℓ ≤ ⌊x⁻¹⌋₊)
    (hfree : IsInducedSubgraphFree F (PkCompl k))
    (hcomb : IsCombIn F S ℓ w a B)
    (hv : IsCombExternalApex F S ℓ a B v)
    (hw_ge_S : (S.card : ℝ) / (ℓ : ℝ) ^ 18 ≤ w) :
    let p_cap := ⌈x⁻¹ ^ 2⌉₊
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
  -- Show 64 ≤ ℓ ≤ p_cap and x⁻¹ ≤ p_cap and p_cap⁻¹ ≤ x
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
  let C := pathCombExpC k
  have hC_eq : C = 3 * capExpE r + 4 * splitTreeD r + 100 := rfl
  by_cases hw_min : combMinWidth r x p_cap ≤ w
  · -- Case 2: w ≥ combMinWidth r x p_cap → invoke Theorem 7(1) at s = 1, L_max = ℓ, η_out = x
    have hstems := hasPerHandleApexStems_one_of_isCombExternalApex hv
    have hfree_r : IsInducedSubgraphFree F (PkCompl (1 + 4 + r)) := by
      rwa [show 1 + 4 + r = k by omega]
    have hU_sub_S : Finset.univ.biUnion B ⊆ S :=
      Finset.biUnion_subset.mpr (fun i _ => hcomb.is_blockade.subset_ambient i)
    rcases stage1_comb_cocomb_dichotomy_all_r r hr hr V F S 1 ℓ p_cap ℓ x w a B (fun _ _ => v)
        le_rfl hℓ_64 hℓ_le_pcap (by omega) le_rfl hx_pos hx_ub hfree_r (Or.inl hcomb) hstems hw_min with
      ⟨k', hℓ_k', hk'_p, U, hU⟩ | ⟨U, hU_cap⟩
    · -- (P2_r-SplitOrCross) at length k' ∈ [ℓ, p_cap]
      refine ⟨k', hℓ_k', hk'_p, U, hU.mono_ambient_width_eps hU_sub_S ?_ le_rfl⟩
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
    · -- (P2_r-Cap) at length p_cap
      refine ⟨p_cap, hℓ_le_pcap, le_rfl, U, hU_cap.mono_ambient_width_eps hU_sub_S ?_ le_rfl⟩
      rw [show -(200 * (r : ℝ) ^ 2) = -(((200 * r ^ 2 : ℕ) : ℝ)) by push_cast; ring,
        rpow_neg_natCast (by norm_num) (200 * r ^ 2), ← inv_pow,
        show -(capExpE r : ℝ) = -(((capExpE r : ℕ) : ℝ)) by rfl,
        rpow_neg_natCast (le_of_lt hp_pos) (capExpE r), ← inv_pow]
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
  · -- Case 1: w < combMinWidth r x p_cap → singleton pure blockade of length k' = min S.card p_cap
    push_neg at hw_min
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
    · -- k' = S.card, so |S| / (k')^C ≤ |S| / k' = 1
      have hk'_eq : k' = S.card := Nat.min_eq_left hS_le_p
      rw [← hk'_eq, div_le_one (by positivity)]
      have hC_pos : 1 ≤ C := by rw [hC_eq]; omega
      simpa using pow_le_pow_right₀ hk'_ge1 hC_pos
    · -- S.card > p_cap, so k' = p_cap; bound |S| ≤ ℓ^18 w < p_cap^C
      push_neg at hS_le_p
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

/-!
## Axiom Verification for All Main Theorems

Verifies that every main lemma, proposition, and theorem in `RecursiveGallaiAndStage1.lean` depends
only on standard Lean 4 foundational axioms (`propext`, `Classical.choice`, `Quot.sound`).
-/

#print axioms three_case_gallai_core_extraction
#print axioms iterated_gallai_core_decomposition
#print axioms active_leaf_split_tree_dichotomy
#print axioms universal_depth_r_neighborhood_modularity
#print axioms union_pool_stem_promotion
#print axioms internal_depth_d_stem_promotion
#print axioms bipartite_double_counting_dichotomy
#print axioms prop1_comb_cocomb_dichotomy
#print axioms single_u_level2_core_dichotomy
#print axioms level3_recursive_gallai_core_split
#print axioms prop2_comb_cocomb_dichotomy
#print axioms prop4_comb_cocomb_dichotomy
#print axioms stage1_comb_cocomb_dichotomy_all_r
#print axioms stage1_comb_dichotomy_condition_for_all_paths

end ErdosHajnalGen
