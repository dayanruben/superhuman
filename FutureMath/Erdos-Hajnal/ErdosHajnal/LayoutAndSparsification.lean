/-
Copyright 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosHajnal.BasicLemmas
import ErdosHajnal.CombModules
import ErdosHajnal.Defs
import ErdosHajnal.GallaiAndCombDichotomy
import ErdosHajnal.WitnessGraph
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Layout Refinement, Multi-Scale Sparsification, and Generalized Niceness
(Lemma 5.1, Lemma 5.2, and Proposition 5.3 of `FMBV4-016_readable.tex`)

This file formalizes:
- **Lemma 5.1 (`lem:layout-refinement`)**: Self-Contained Layout Refinement for
  Complete-or-$x$-Sparse Blockades.
- **Lemma 5.2 (`lem:multiscale`)**: Multi-Scale Iterative Sparsification Lemma.
- **Proposition 5.3 (`prop:gen-nice`)**: Generalized Niceness of $\{P_6\}$.
-/

open Finset SimpleGraph Real

namespace ErdosHajnalP6

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.unusedSectionVars false

/-!
## Section 1: Monotonicity and Cross-Edge Lemmas for Sparsity and Blockades
-/

/-- Monotonicity of `IsEpsSparseOn` in the sparsity parameter $\varepsilon$. -/
theorem IsEpsSparseOn.mono {G : SimpleGraph V} {S : Finset V} {ε₁ ε₂ : ℝ}
    (h : IsEpsSparseOn G S ε₁) (hle : ε₁ ≤ ε₂) : IsEpsSparseOn G S ε₂ := by
  intro v hv
  exact (h v hv).trans (mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg S.card))

/-- Monotonicity of `IsEpsRestrictedOn` in the restriction parameter $\varepsilon$. -/
theorem IsEpsRestrictedOn.mono {G : SimpleGraph V} {S : Finset V} {ε₁ ε₂ : ℝ}
    (h : IsEpsRestrictedOn G S ε₁) (hle : ε₁ ≤ ε₂) : IsEpsRestrictedOn G S ε₂ := by
  rcases h with hG | hGc
  · exact Or.inl (hG.mono hle)
  · exact Or.inr (hGc.mono hle)

/-- Monotonicity of `IsBlockadeIn` when decreasing the width lower bound. -/
theorem IsBlockadeIn.mono_width {G : SimpleGraph V} {S : Finset V} {k : ℕ} {w₁ w₂ : ℝ}
    {B : Fin k → Finset V} (h : IsBlockadeIn G S k w₁ B) (hw : w₂ ≤ w₁) :
    IsBlockadeIn G S k w₂ B :=
  ⟨h.subset_ambient, h.nonempty_blocks, h.pairwise_disjoint, fun i => hw.trans (h.width_ge i)⟩

/-- Monotonicity of `IsBlockadeIn` when enlarging the ambient vertex set. -/
theorem IsBlockadeIn.mono_ambient {G : SimpleGraph V} {S₁ S₂ : Finset V} {k : ℕ} {w : ℝ}
    {B : Fin k → Finset V} (h : IsBlockadeIn G S₁ k w B) (hS : S₁ ⊆ S₂) :
    IsBlockadeIn G S₂ k w B :=
  ⟨fun i => (h.subset_ambient i).trans hS, h.nonempty_blocks, h.pairwise_disjoint, h.width_ge⟩

/-- Restricting a blockade of length $k$ to the first $\ell \le k$ blocks. -/
def restrictBlockade {k ℓ : ℕ} (hℓ : ℓ ≤ k) (B : Fin k → Finset V) : Fin ℓ → Finset V :=
  fun i => B (Fin.castLE hℓ i)

theorem IsBlockadeIn.restrict {G : SimpleGraph V} {S : Finset V} {k ℓ : ℕ} {w : ℝ}
    {B : Fin k → Finset V} (h : IsBlockadeIn G S k w B) (hℓ : ℓ ≤ k) :
    IsBlockadeIn G S ℓ w (restrictBlockade hℓ B) where
  subset_ambient i := h.subset_ambient (Fin.castLE hℓ i)
  nonempty_blocks i := h.nonempty_blocks (Fin.castLE hℓ i)
  pairwise_disjoint _ _ hij :=
    h.pairwise_disjoint _ _ (fun heq => hij ((Fin.castLE_injective hℓ) heq))
  width_ge i := h.width_ge (Fin.castLE hℓ i)

/-- If $A$ is $x$-sparse to $B$ in $G$, then $|E_G(A, B)| \le x |A| |B|$. -/
theorem crossEdgeCount_le_of_isXSparseTo (G : SimpleGraph V) (A B : Finset V) (x : ℝ)
    (h : IsXSparseTo G A B x) :
    (crossEdgeCount G A B : ℝ) ≤ x * (A.card : ℝ) * (B.card : ℝ) := by
  unfold crossEdgeCount
  push_cast
  calc ∑ u ∈ A, ((neighborFinsetIn G u B).card : ℝ)
      ≤ ∑ _u ∈ A, (x * (B.card : ℝ)) := Finset.sum_le_sum (fun u hu => h u hu)
    _ = (A.card : ℝ) * (x * (B.card : ℝ)) := by simp [Finset.sum_const, nsmul_eq_mul]
    _ = x * (A.card : ℝ) * (B.card : ℝ) := by ring

/-- Any $x$-sparse pair is weakly $x$-sparse. -/
theorem IsXSparsePair.isWeaklySparsePair {G : SimpleGraph V} {A B : Finset V} {x : ℝ}
    (h : IsXSparsePair G A B x) : IsWeaklySparsePair G A B x :=
  crossEdgeCount_le_of_isXSparseTo G A B x h.2

/-- Monotonicity of `IsWeaklySparsePair` in the sparsity parameter. -/
theorem IsWeaklySparsePair.mono {G : SimpleGraph V} {A B : Finset V} {ε₁ ε₂ : ℝ}
    (h : IsWeaklySparsePair G A B ε₁) (hle : ε₁ ≤ ε₂) : IsWeaklySparsePair G A B ε₂ := by
  unfold IsWeaklySparsePair at *
  have hAB : 0 ≤ (A.card : ℝ) * (B.card : ℝ) := by positivity
  calc (crossEdgeCount G A B : ℝ)
      ≤ ε₁ * (A.card : ℝ) * (B.card : ℝ) := h
    _ = ε₁ * ((A.card : ℝ) * (B.card : ℝ)) := by ring
    _ ≤ ε₂ * ((A.card : ℝ) * (B.card : ℝ)) := mul_le_mul_of_nonneg_right hle hAB
    _ = ε₂ * (A.card : ℝ) * (B.card : ℝ) := by ring

/-- Sum of cardinalities of pairwise disjoint subsets of $A_0$ is at most $|A_0|$. -/
theorem sum_card_le_of_pairwise_disjoint {I : Type*} [Fintype I] [DecidableEq I]
    {A₀ : Finset V} {B : I → Finset V}
    (hsub : ∀ p : I, B p ⊆ A₀) (hdisj : ∀ p q : I, p ≠ q → Disjoint (B p) (B q)) :
    (∑ p : I, (B p).card) ≤ A₀.card := by
  have hd : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint B :=
    fun p _ q _ hpq => hdisj p q hpq
  rw [← Finset.card_biUnion hd]
  exact Finset.card_le_card (Finset.biUnion_subset.mpr (fun p _ => hsub p))

/--
Off-diagonal product sum bound for pairwise disjoint subsets of $A_0$:
$\sum_{p \neq q} |B_p| |B_q| \le |A_0|^2 - \sum_p |B_p|^2$.
-/
theorem sum_offDiag_card_mul_le_sq_sub {I : Type*} [Fintype I] [DecidableEq I]
    {A₀ : Finset V} {B : I → Finset V}
    (hsub : ∀ p : I, B p ⊆ A₀) (hdisj : ∀ p q : I, p ≠ q → Disjoint (B p) (B q)) :
    (∑ p : I, ∑ q : I, if p ≠ q then ((B p).card : ℝ) * ((B q).card : ℝ) else 0) ≤
      (A₀.card : ℝ) ^ 2 - ∑ p : I, ((B p).card : ℝ) ^ 2 := by
  have hsum_le : (∑ p : I, ((B p).card : ℝ)) ≤ (A₀.card : ℝ) := by
    exact_mod_cast sum_card_le_of_pairwise_disjoint hsub hdisj
  have hsum_nonneg : 0 ≤ ∑ p : I, ((B p).card : ℝ) :=
    Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hsq_le : (∑ p : I, ((B p).card : ℝ)) ^ 2 ≤ (A₀.card : ℝ) ^ 2 :=
    pow_le_pow_left₀ hsum_nonneg hsum_le 2
  have hdecomp : (∑ p : I, ((B p).card : ℝ)) ^ 2 =
      (∑ p : I, ((B p).card : ℝ) ^ 2) +
      ∑ p : I, ∑ q : I, if p ≠ q then ((B p).card : ℝ) * ((B q).card : ℝ) else 0 := by
    rw [sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p), sq]
    congr 1
    rw [← Finset.add_sum_erase _ (fun q => if p ≠ q then ((B p).card : ℝ) * ((B q).card : ℝ) else 0)
      (Finset.mem_univ p)]
    simp only [ne_eq, not_true_eq_false, ↓reduceIte, zero_add]
    refine Finset.sum_congr rfl (fun q hq => ?_)
    have hne : p ≠ q := (Finset.mem_erase.mp hq).1.symm
    simp [hne]
  linarith

/--
Subadditivity of `crossEdgeCount` in the first argument over pairwise disjoint subsets $B_p \subseteq A_0$.
-/
theorem sum_crossEdgeCount_left_le {I : Type*} [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (C A₀ : Finset V) (B : I → Finset V)
    (hsub : ∀ p : I, B p ⊆ A₀) (hdisj : ∀ p q : I, p ≠ q → Disjoint (B p) (B q)) :
    (∑ p : I, crossEdgeCount G (B p) C) ≤ crossEdgeCount G A₀ C := by
  unfold crossEdgeCount
  have hd : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint B :=
    fun p _ q _ hpq => hdisj p q hpq
  rw [← Finset.sum_biUnion hd]
  exact Finset.sum_le_sum_of_subset (Finset.biUnion_subset.mpr (fun p _ => hsub p))

/--
Subadditivity of `crossEdgeCount` in the second argument over pairwise disjoint subsets $B_p \subseteq A_0$.
-/
theorem sum_crossEdgeCount_right_le {I : Type*} [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (C A₀ : Finset V) (B : I → Finset V)
    (hsub : ∀ p : I, B p ⊆ A₀) (hdisj : ∀ p q : I, p ≠ q → Disjoint (B p) (B q)) :
    (∑ p : I, crossEdgeCount G C (B p)) ≤ crossEdgeCount G C A₀ := by
  classical
  unfold crossEdgeCount
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun u _ => ?_)
  refine sum_card_le_of_pairwise_disjoint (fun p => ?_) (fun p q hpq => ?_)
  · intro v hv
    simp only [neighborFinsetIn, Finset.mem_filter] at hv ⊢
    exact ⟨hsub p hv.1, hv.2⟩
  · refine Disjoint.mono ?_ ?_ (hdisj p q hpq) <;>
      exact Finset.filter_subset _ _

/-!
## Section 2: Multi-Scale Iterative Sparsification (Lemma 5.2, `lem:multiscale`)
-/

/--
The multi-scale density sequence $\lambda_t := \lambda_0^{b_1^t}$ for integers $t \ge 0$
(Lemma 5.2 of `FMBV4-016_readable.tex`).
-/
noncomputable def multiscaleLambda (lam0 b₁ : ℝ) (t : ℕ) : ℝ :=
  lam0 ^ (b₁ ^ t)

@[simp]
theorem multiscaleLambda_zero (lam0 b₁ : ℝ) :
    multiscaleLambda lam0 b₁ 0 = lam0 := by
  simp [multiscaleLambda]

theorem multiscaleLambda_succ {lam0 b₁ : ℝ} (hlam0 : 0 ≤ lam0) (t : ℕ) :
    multiscaleLambda lam0 b₁ (t + 1) = (multiscaleLambda lam0 b₁ t) ^ b₁ := by
  unfold multiscaleLambda
  rw [pow_succ, Real.rpow_mul hlam0]

theorem multiscaleLambda_pos {lam0 b₁ : ℝ} (hlam0 : 0 < lam0) (t : ℕ) :
    0 < multiscaleLambda lam0 b₁ t :=
  Real.rpow_pos_of_pos hlam0 _

theorem multiscaleLambda_lt_one {lam0 b₁ : ℝ} (hlam0 : 0 < lam0) (hlam01 : lam0 < 1)
    (hb₁ : 0 < b₁) (t : ℕ) :
    multiscaleLambda lam0 b₁ t < 1 :=
  Real.rpow_lt_one hlam0.le hlam01 (pow_pos hb₁ t)

theorem multiscaleLambda_le_self {lam0 b₁ : ℝ} (hlam0 : 0 < lam0) (hlam01 : lam0 < 1)
    (hb₁ : 1 ≤ b₁) (t : ℕ) :
    multiscaleLambda lam0 b₁ t ≤ lam0 := by
  unfold multiscaleLambda
  have hpow : (1 : ℝ) ≤ b₁ ^ t := one_le_pow₀ hb₁
  calc lam0 ^ (b₁ ^ t) ≤ lam0 ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hlam0 hlam01.le hpow
    _ = lam0 := Real.rpow_one lam0

/-- Bernoulli lower bound $1 + t (b_1 - 1) \le b_1^t$ for $b_1 \ge 1$. -/
theorem one_add_mul_sub_one_le_pow {b₁ : ℝ} (hb₁ : 1 ≤ b₁) (t : ℕ) :
    1 + (t : ℝ) * (b₁ - 1) ≤ b₁ ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    push_cast
    rw [pow_succ]
    have h1 : 0 ≤ b₁ - 1 := sub_nonneg.mpr hb₁
    have h2 : 0 ≤ (t : ℝ) * (b₁ - 1) * (b₁ - 1) := by positivity
    calc 1 + ((t : ℝ) + 1) * (b₁ - 1)
        ≤ (1 + (t : ℝ) * (b₁ - 1)) * b₁ := by linarith
      _ ≤ b₁ ^ t * b₁ := mul_le_mul_of_nonneg_right ih (by linarith)

/-- Elementary bound $n + 1 \le 2^n$ in $\mathbb{R}$. -/
theorem nat_add_one_le_two_pow (n : ℕ) : (n : ℝ) + 1 ≤ (2 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    push_cast
    rw [pow_succ]
    have hpos : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    linarith

/--
Existence of a scale $t \ge 1$ where $\lambda_t = \lambda_0^{b_1^t} \le x$
for $\lambda_0 \in (0, 1/2)$, $x > 0$, and $b_1 > 1$.
-/
theorem exists_multiscaleLambda_le {lam0 b₁ x : ℝ} (hlam0 : 0 < lam0) (hlam0_half : lam0 < 1 / 2)
    (hx : 0 < x) (hb₁ : 1 < b₁) :
    ∃ t : ℕ, 1 ≤ t ∧ multiscaleLambda lam0 b₁ t ≤ x := by
  let N : ℕ := ⌈1 / x⌉₊
  let t : ℕ := ⌈(N : ℝ) / (b₁ - 1)⌉₊ + 1
  refine ⟨t, Nat.le_add_left 1 _, ?_⟩
  have hb₁_sub : 0 < b₁ - 1 := sub_pos.mpr hb₁
  have ht_ge : (N : ℝ) ≤ (t : ℝ) * (b₁ - 1) := by
    have hceil : (N : ℝ) / (b₁ - 1) ≤ (⌈(N : ℝ) / (b₁ - 1)⌉₊ : ℝ) := Nat.le_ceil _
    have hmul : (N : ℝ) ≤ (⌈(N : ℝ) / (b₁ - 1)⌉₊ : ℝ) * (b₁ - 1) :=
      (div_le_iff₀ hb₁_sub).mp hceil
    have ht_cast : (⌈(N : ℝ) / (b₁ - 1)⌉₊ : ℝ) ≤ (t : ℝ) := by
      exact_mod_cast Nat.le_succ _
    exact hmul.trans (mul_le_mul_of_nonneg_right ht_cast hb₁_sub.le)
  have hpow_ge : (N : ℝ) ≤ b₁ ^ t := by
    have hbern := one_add_mul_sub_one_le_pow hb₁.le t
    linarith
  have hlam0_one : lam0 ≤ 1 := by linarith
  have h1 : multiscaleLambda lam0 b₁ t ≤ lam0 ^ (N : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hlam0 hlam0_one hpow_ge
  rw [Real.rpow_natCast] at h1
  have h2 : lam0 ^ N ≤ (1 / 2 : ℝ) ^ N := pow_le_pow_left₀ hlam0.le hlam0_half.le N
  have h3 : (1 / 2 : ℝ) ^ N ≤ 1 / ((N : ℝ) + 1) := by
    rw [one_div_pow, one_div_le_one_div (by positivity) (by positivity)]
    exact nat_add_one_le_two_pow N
  have hN : 1 / x ≤ (N : ℝ) + 1 := by
    have : 1 / x ≤ (N : ℝ) := Nat.le_ceil (1 / x)
    linarith
  have h4 : 1 / ((N : ℝ) + 1) ≤ x := by
    rw [one_div_le (by positivity) hx]
    exact hN
  exact h1.trans (h2.trans (h3.trans h4))

/--
Key exponent inequality for Step (I2) of Lemma 5.2 (`lem:multiscale`):
If $\lambda_t \in (0, 1)$ and $(b_1 - 1) b_2 \ge b_3$, then
$\lambda_{t+1}^{b_2} = (\lambda_t^{b_1})^{b_2} \le \lambda_t^{b_2 + b_3} = \lambda_t^{b_3} \lambda_t^{b_2}$.
-/
theorem multiscaleLambda_rpow_step {lam0 b₁ b₂ b₃ : ℝ} (hlam0 : 0 < lam0) (hlam01 : lam0 < 1)
    (hb₁ : 0 < b₁) (hexp : (b₁ - 1) * b₂ ≥ b₃) (t : ℕ) :
    (multiscaleLambda lam0 b₁ (t + 1)) ^ b₂ ≤
      (multiscaleLambda lam0 b₁ t) ^ b₃ * (multiscaleLambda lam0 b₁ t) ^ b₂ := by
  set lam_t := multiscaleLambda lam0 b₁ t
  have hlam_pos : 0 < lam_t := multiscaleLambda_pos hlam0 t
  have hlam_lt : lam_t < 1 := multiscaleLambda_lt_one hlam0 hlam01 hb₁ t
  rw [multiscaleLambda_succ hlam0.le t, ← Real.rpow_mul hlam_pos.le, ← Real.rpow_add hlam_pos]
  exact Real.rpow_le_rpow_of_exponent_ge hlam_pos hlam_lt.le (by linarith)

/--
Finite-step induction of Lemma 5.2 (`lem:multiscale`):
For any $t \in \mathbb{N}$ such that $\lambda_s \ge x$ for all $s < t$, either $F_0$ contains
an induced subgraph $F \subseteq F_0$ satisfying $\mathcal{O}$, or there exists $F_t \subseteq F_0$
satisfying (I1) $F_t$ is $\lambda_t$-restricted and (I2) $|F_t| \ge \lambda_t^{b_2} |F_0|$.
-/
theorem multiscale_sparsification_loop (G : SimpleGraph V) (F₀ : Finset V) (O : Finset V → Prop)
    {lam0 x b₁ b₂ b₃ : ℝ} (hlam0 : 0 < lam0) (hlam0_half : lam0 < 1 / 2)
    (hb₁ : 1 < b₁) (hb₂ : 0 < b₂) (hexp : (b₁ - 1) * b₂ ≥ b₃)
    (hF₀ : IsEpsRestrictedOn G F₀ lam0)
    (hstep : ∀ lam ∈ Set.Icc x lam0, ∀ F ⊆ F₀,
      IsEpsRestrictedOn G F lam → lam ^ b₂ * (F₀.card : ℝ) ≤ (F.card : ℝ) →
        O F ∨ ∃ F' ⊆ F, IsEpsRestrictedOn G F' (lam ^ b₁) ∧
          lam ^ b₃ * (F.card : ℝ) ≤ (F'.card : ℝ)) :
    ∀ t : ℕ, (∀ s < t, x ≤ multiscaleLambda lam0 b₁ s) →
      (∃ F ⊆ F₀, O F) ∨
      (∃ F_t ⊆ F₀, IsEpsRestrictedOn G F_t (multiscaleLambda lam0 b₁ t) ∧
        (multiscaleLambda lam0 b₁ t) ^ b₂ * (F₀.card : ℝ) ≤ (F_t.card : ℝ)) := by
  have hlam01 : lam0 < 1 := by linarith
  have hb₁_pos : 0 < b₁ := by linarith
  intro t
  induction t with
  | zero =>
    intro _
    refine Or.inr ⟨F₀, Subset.rfl, ?_, ?_⟩
    · simpa [multiscaleLambda_zero] using hF₀
    · rw [multiscaleLambda_zero]
      have hle1 : lam0 ^ b₂ ≤ 1 := Real.rpow_le_one hlam0.le hlam01.le hb₂.le
      calc lam0 ^ b₂ * (F₀.card : ℝ)
          ≤ 1 * (F₀.card : ℝ) := mul_le_mul_of_nonneg_right hle1 (Nat.cast_nonneg _)
        _ = (F₀.card : ℝ) := one_mul _
  | succ t ih =>
    intro hscale
    rcases ih (fun s hs => hscale s (Nat.lt_succ_of_lt hs)) with hO | ⟨F_t, hF_t_sub, hI1, hI2⟩
    · exact Or.inl hO
    · have hlam_ge_x : x ≤ multiscaleLambda lam0 b₁ t := hscale t (Nat.lt_succ_self t)
      have hlam_le_lam0 : multiscaleLambda lam0 b₁ t ≤ lam0 :=
        multiscaleLambda_le_self hlam0 hlam01 hb₁.le t
      rcases hstep (multiscaleLambda lam0 b₁ t) ⟨hlam_ge_x, hlam_le_lam0⟩ F_t hF_t_sub hI1 hI2 with
        hOF_t | ⟨F', hF'_sub, hF'_rest, hF'_card⟩
      · exact Or.inl ⟨F_t, hF_t_sub, hOF_t⟩
      · refine Or.inr ⟨F', hF'_sub.trans hF_t_sub, ?_, ?_⟩
        · rwa [multiscaleLambda_succ hlam0.le t]
        · have hstep_exp := multiscaleLambda_rpow_step hlam0 hlam01 hb₁_pos hexp t
          have hlamb₃_pos : 0 ≤ (multiscaleLambda lam0 b₁ t) ^ b₃ :=
            Real.rpow_nonneg (multiscaleLambda_pos hlam0 t).le b₃
          calc (multiscaleLambda lam0 b₁ (t + 1)) ^ b₂ * (F₀.card : ℝ)
              ≤ ((multiscaleLambda lam0 b₁ t) ^ b₃ * (multiscaleLambda lam0 b₁ t) ^ b₂) *
                  (F₀.card : ℝ) :=
                mul_le_mul_of_nonneg_right hstep_exp (Nat.cast_nonneg _)
            _ = (multiscaleLambda lam0 b₁ t) ^ b₃ *
                  ((multiscaleLambda lam0 b₁ t) ^ b₂ * (F₀.card : ℝ)) := by ring
            _ ≤ (multiscaleLambda lam0 b₁ t) ^ b₃ * (F_t.card : ℝ) :=
                mul_le_mul_of_nonneg_left hI2 hlamb₃_pos
            _ ≤ (F'.card : ℝ) := hF'_card

/--
**Lemma 5.2 (`lem:multiscale`, Multi-Scale Iterative Sparsification Lemma)**:
Let $\lambda_0 \in (0, 1/2)$, $x \in (0, \lambda_0)$, and $b_1 > 1, b_2 > 0, b_3 > 0$ with
$(b_1 - 1) b_2 \ge b_3$. Let $F_0$ be a $\lambda_0$-restricted induced subgraph of $G$.
If for every $\lambda \in [x, \lambda_0]$ and every $\lambda$-restricted $F \subseteq F_0$
with $|F| \ge \lambda^{b_2} |F_0|$, either $F$ satisfies $\mathcal{O}$ or $F$ contains a
$\lambda^{b_1}$-restricted $F' \subseteq F$ with $|F'| \ge \lambda^{b_3} |F|$, then either
$F_0$ contains an induced subgraph satisfying $\mathcal{O}$, or $F_0$ contains an
$x$-restricted induced subgraph $S \subseteq F_0$ with $|S| \ge x^{b_1 b_2} |F_0|$.
-/
theorem lem_multiscale_sparsification (G : SimpleGraph V) (F₀ : Finset V) (O : Finset V → Prop)
    {lam0 x b₁ b₂ b₃ : ℝ} (hlam0 : 0 < lam0) (hlam0_half : lam0 < 1 / 2)
    (hx : 0 < x) (hx_lt : x < lam0)
    (hb₁ : 1 < b₁) (hb₂ : 0 < b₂) (_hb₃ : 0 < b₃) (hexp : (b₁ - 1) * b₂ ≥ b₃)
    (hF₀ : IsEpsRestrictedOn G F₀ lam0)
    (hstep : ∀ lam ∈ Set.Icc x lam0, ∀ F ⊆ F₀,
      IsEpsRestrictedOn G F lam → lam ^ b₂ * (F₀.card : ℝ) ≤ (F.card : ℝ) →
        O F ∨ ∃ F' ⊆ F, IsEpsRestrictedOn G F' (lam ^ b₁) ∧
          lam ^ b₃ * (F.card : ℝ) ≤ (F'.card : ℝ)) :
    (∃ F ⊆ F₀, O F) ∨
    (∃ S ⊆ F₀, IsEpsRestrictedOn G S x ∧ x ^ (b₁ * b₂) * (F₀.card : ℝ) ≤ (S.card : ℝ)) := by
  classical
  have hex : ∃ t : ℕ, 1 ≤ t ∧ multiscaleLambda lam0 b₁ t ≤ x :=
    exists_multiscaleLambda_le hlam0 hlam0_half hx hb₁
  let m : ℕ := Nat.find hex
  have hm_spec : 1 ≤ m ∧ multiscaleLambda lam0 b₁ m ≤ x := Nat.find_spec hex
  have hm_min : ∀ s < m, x ≤ multiscaleLambda lam0 b₁ s := by
    intro s hs
    rcases Nat.eq_zero_or_pos s with rfl | hs_pos
    · simp [multiscaleLambda_zero, hx_lt.le]
    · have hnot := Nat.find_min hex hs
      push_neg at hnot
      exact (hnot hs_pos).le
  rcases multiscale_sparsification_loop G F₀ O hlam0 hlam0_half hb₁ hb₂ hexp hF₀ hstep m hm_min with
    hO | ⟨S, hS_sub, hS_rest, hS_card⟩
  · exact Or.inl hO
  · refine Or.inr ⟨S, hS_sub, hS_rest.mono hm_spec.2, ?_⟩
    have hm_eq : m = (m - 1) + 1 := (Nat.sub_add_cancel hm_spec.1).symm
    have hprev_ge : x ≤ multiscaleLambda lam0 b₁ (m - 1) :=
      hm_min (m - 1) (Nat.sub_lt hm_spec.1 zero_lt_one)
    have hlam_m_ge : x ^ (b₁ * b₂) ≤ (multiscaleLambda lam0 b₁ m) ^ b₂ := by
      rw [hm_eq, multiscaleLambda_succ hlam0.le (m - 1),
        ← Real.rpow_mul (multiscaleLambda_pos hlam0 (m - 1)).le]
      exact Real.rpow_le_rpow hx.le hprev_ge (by positivity)
    calc x ^ (b₁ * b₂) * (F₀.card : ℝ)
        ≤ (multiscaleLambda lam0 b₁ m) ^ b₂ * (F₀.card : ℝ) :=
          mul_le_mul_of_nonneg_right hlam_m_ge (Nat.cast_nonneg _)
      _ ≤ (S.card : ℝ) := hS_card

/-!
## Section 3: Self-Contained Layout Refinement (Lemma 5.1, `lem:layout-refinement`)
-/

/--
Total number of ordered wrong pairs $|Q(\mathcal{L})|$ in a layout $\mathcal{L} = (J, A)$:
$\sum_{i \neq j, ij \notin E(J)} |E_G(A_i, A_j)|$.
-/
noncomputable def wrongEdgeCount {I : Type*} [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (J : SimpleGraph I) (A : I → Finset V) : ℕ :=
  by classical exact
    ∑ i : I, ∑ j : I, if i ≠ j ∧ ¬J.Adj i j then crossEdgeCount G (A i) (A j) else 0

/--
Upper bound potential $|P(\mathcal{L})|$ for decided ordered pairs in a layout $\mathcal{L} = (J, A)$
inside $S \subseteq V(G)$: $|S|^2 - \sum_{i \in I} |A_i|^2$.
-/
noncomputable def decidedBound {I : Type*} [Fintype I]
    (S : Finset V) (A : I → Finset V) : ℝ :=
  (S.card : ℝ) ^ 2 - ∑ i : I, ((A i).card : ℝ) ^ 2

/--
A valid layout $\mathcal{L} = (J, A)$ of index type $I$ inside $S \subseteq V(G)$ with parameters
$(\varepsilon, d, x)$, satisfying structural layout conditions together with:
- **(L1)** $|A_i| \ge \varepsilon^{2d} |S|$ for all $i \in I$;
- **(L2)** $\sum_{i \in I} |A_i|^{1/d} \ge |S|^{1/d}$; and
- **(L3)** $|Q(\mathcal{L})| \le x |P(\mathcal{L})|$.
-/
structure IsValidLayout {I : Type*} [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (S : Finset V) (ε d x : ℝ)
    (J : SimpleGraph I) (A : I → Finset V) : Prop where
  subset_ambient : ∀ i : I, A i ⊆ S
  nonempty_blocks : ∀ i : I, (A i).Nonempty
  pairwise_disjoint : ∀ i j : I, i ≠ j → Disjoint (A i) (A j)
  complete_of_adj : ∀ i j : I, J.Adj i j → IsCompletePair G (A i) (A j)
  L1_width : ∀ i : I, ε ^ (2 * d) * (S.card : ℝ) ≤ ((A i).card : ℝ)
  L2_potential : (S.card : ℝ) ^ (1 / d) ≤ ∑ i : I, ((A i).card : ℝ) ^ (1 / d)
  L3_wrong : (wrongEdgeCount G J A : ℝ) ≤ x * decidedBound S A

/-- Transporting `IsValidLayout` along a bijection of index types $e : I_1 \simeq I_2$. -/
theorem IsValidLayout.reindex {I₁ I₂ : Type*} [Fintype I₁] [DecidableEq I₁]
    [Fintype I₂] [DecidableEq I₂] (e : I₁ ≃ I₂)
    {G : SimpleGraph V} {S : Finset V} {ε d x : ℝ}
    {J : SimpleGraph I₂} {A : I₂ → Finset V}
    (h : IsValidLayout G S ε d x J A) :
    IsValidLayout G S ε d x (J.comap e) (A ∘ e) where
  subset_ambient i := h.subset_ambient (e i)
  nonempty_blocks i := h.nonempty_blocks (e i)
  pairwise_disjoint i j hij := h.pairwise_disjoint (e i) (e j) (e.injective.ne hij)
  complete_of_adj i j hadj := h.complete_of_adj (e i) (e j) hadj
  L1_width i := h.L1_width (e i)
  L2_potential := by
    refine h.L2_potential.trans (le_of_eq ?_)
    exact (Equiv.sum_comp e (fun i => ((A i).card : ℝ) ^ (1 / d))).symm
  L3_wrong := by
    have hW : wrongEdgeCount G (J.comap e) (A ∘ e) = wrongEdgeCount G J A := by
      classical
      unfold wrongEdgeCount
      rw [← Equiv.sum_comp e
        (fun i => ∑ j : I₂, if i ≠ j ∧ ¬J.Adj i j then crossEdgeCount G (A i) (A j) else 0)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Equiv.sum_comp e
        (fun j => if e i ≠ j ∧ ¬J.Adj (e i) j then crossEdgeCount G (A (e i)) (A j) else 0)]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp [Function.comp_apply, e.injective.ne_iff]
    have hD : decidedBound S (A ∘ e) = decidedBound S A := by
      unfold decidedBound
      simp only [Function.comp_apply]
      rw [Equiv.sum_comp e (fun i => ((A i).card : ℝ) ^ 2)]
    rw [hW, hD]
    exact h.L3_wrong

/-- For any non-adjacent distinct pair $(i_0, j_0)$, $|E_G(A_{i_0}, A_{j_0})| \le |Q(\mathcal{L})|$. -/
theorem crossEdgeCount_le_wrongEdgeCount {I : Type*} [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (J : SimpleGraph I) (A : I → Finset V) {i₀ j₀ : I}
    (hne : i₀ ≠ j₀) (hnadj : ¬J.Adj i₀ j₀) :
    crossEdgeCount G (A i₀) (A j₀) ≤ wrongEdgeCount G J A := by
  classical
  unfold wrongEdgeCount
  have h1 : crossEdgeCount G (A i₀) (A j₀) ≤
      ∑ j : I, if i₀ ≠ j ∧ ¬J.Adj i₀ j then crossEdgeCount G (A i₀) (A j) else 0 := by
    have := Finset.single_le_sum
      (f := fun j : I => if i₀ ≠ j ∧ ¬J.Adj i₀ j then crossEdgeCount G (A i₀) (A j) else 0)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j₀)
    simpa [hne, hnadj] using this
  have h2 : (∑ j : I, if i₀ ≠ j ∧ ¬J.Adj i₀ j then crossEdgeCount G (A i₀) (A j) else 0) ≤
      ∑ i : I, ∑ j : I, if i ≠ j ∧ ¬J.Adj i j then crossEdgeCount G (A i) (A j) else 0 :=
    Finset.single_le_sum
      (f := fun i : I => ∑ j : I, if i ≠ j ∧ ¬J.Adj i j then crossEdgeCount G (A i) (A j) else 0)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i₀)
  exact h1.trans h2

/-- `decidedBound S A ≤ |S|^2`. -/
theorem decidedBound_le_sq {I : Type*} [Fintype I] (S : Finset V) (A : I → Finset V) :
    decidedBound S A ≤ (S.card : ℝ) ^ 2 := by
  unfold decidedBound
  have : 0 ≤ ∑ i : I, ((A i).card : ℝ) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  linarith

/--
The trivial 1-vertex layout on `Fin 1` with $A_0 = S$ satisfies (L1)--(L3) with
$Q(\mathcal{L}) = P(\mathcal{L}) = 0$.
-/
theorem isValidLayout_trivial (G : SimpleGraph V) {S : Finset V} (hS : S.Nonempty)
    {ε d x : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hd : 0 < d) :
    IsValidLayout G S ε d x (⊥ : SimpleGraph (Fin 1)) (fun _ => S) where
  subset_ambient _ := Subset.rfl
  nonempty_blocks _ := hS
  pairwise_disjoint i j hij := False.elim (hij (Subsingleton.elim i j))
  complete_of_adj _ _ hadj := False.elim hadj
  L1_width _ := by
    have hpow : ε ^ (2 * d) ≤ 1 := Real.rpow_le_one hε.le hε1.le (by positivity)
    calc ε ^ (2 * d) * (S.card : ℝ)
        ≤ 1 * (S.card : ℝ) := mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _)
      _ = (S.card : ℝ) := one_mul _
  L2_potential := by simp
  L3_wrong := by
    unfold wrongEdgeCount decidedBound
    simp

/--
If a valid layout has $|V(J)| \ge \lceil \varepsilon^{-1} \rceil$, then restricting to the first
$\lceil \varepsilon^{-1} \rceil$ blocks gives an $(\lceil \varepsilon^{-1} \rceil, \lfloor \varepsilon^{200 d^2} |S| \rfloor)$-blockade
whose pairs are complete or weakly $\varepsilon^d$-sparse in $G$ (Lemma 5.1 of `FMBV4-016_readable.tex`).
-/
theorem validLayout_extract_blockade {m : ℕ} {G : SimpleGraph V} {S : Finset V}
    {ε d : ℝ} {J : SimpleGraph (Fin m)} {A : Fin m → Finset V}
    (hL : IsValidLayout G S ε d (ε ^ (10 * d)) J A)
    (hε : 0 < ε) (hε_half : ε < 1 / 2) (hd : 1 ≤ d)
    (hm : ⌈ε⁻¹⌉₊ ≤ m) :
    ∃ B : Fin ⌈ε⁻¹⌉₊ → Finset V,
      IsBlockadeIn G S ⌈ε⁻¹⌉₊ (⌊ε ^ (200 * d ^ 2) * (S.card : ℝ)⌋₊ : ℝ) B ∧
      ∀ i j : Fin ⌈ε⁻¹⌉₊, i ≠ j →
        IsCompletePair G (B i) (B j) ∨ IsWeaklySparsePair G (B i) (B j) (ε ^ d) := by
  have hε1 : ε < 1 := by linarith
  refine ⟨restrictBlockade hm A, ?_, ?_⟩
  · refine {
      subset_ambient := fun i => hL.subset_ambient (Fin.castLE hm i)
      nonempty_blocks := fun i => hL.nonempty_blocks (Fin.castLE hm i)
      pairwise_disjoint := fun i j hij =>
        hL.pairwise_disjoint _ _ (fun heq => hij ((Fin.castLE_injective hm) heq))
      width_ge := fun i => ?_
    }
    have hfloor : (⌊ε ^ (200 * d ^ 2) * (S.card : ℝ)⌋₊ : ℝ) ≤ ε ^ (200 * d ^ 2) * (S.card : ℝ) :=
      Nat.floor_le (by positivity)
    have hexp_le : 2 * d ≤ 200 * d ^ 2 := by nlinarith
    have hrpow : ε ^ (200 * d ^ 2) ≤ ε ^ (2 * d) :=
      Real.rpow_le_rpow_of_exponent_ge hε hε1.le hexp_le
    calc (⌊ε ^ (200 * d ^ 2) * (S.card : ℝ)⌋₊ : ℝ)
        ≤ ε ^ (200 * d ^ 2) * (S.card : ℝ) := hfloor
      _ ≤ ε ^ (2 * d) * (S.card : ℝ) := mul_le_mul_of_nonneg_right hrpow (Nat.cast_nonneg _)
      _ ≤ ((A (Fin.castLE hm i)).card : ℝ) := hL.L1_width (Fin.castLE hm i)
  · intro i j hij
    let i' : Fin m := Fin.castLE hm i
    let j' : Fin m := Fin.castLE hm j
    have hij' : i' ≠ j' := fun heq => hij ((Fin.castLE_injective hm) heq)
    by_cases hadj : J.Adj i' j'
    · exact Or.inl (hL.complete_of_adj i' j' hadj)
    · refine Or.inr ?_
      unfold IsWeaklySparsePair restrictBlockade
      have hcross_le : (crossEdgeCount G (A i') (A j') : ℝ) ≤
          ε ^ (10 * d) * (S.card : ℝ) ^ 2 := by
        have h1 : (crossEdgeCount G (A i') (A j') : ℝ) ≤ (wrongEdgeCount G J A : ℝ) := by
          exact_mod_cast crossEdgeCount_le_wrongEdgeCount G J A hij' hadj
        have h2 := hL.L3_wrong
        have h3 := decidedBound_le_sq S A
        have hx_pos : 0 ≤ ε ^ (10 * d) := by positivity
        linarith [mul_le_mul_of_nonneg_left h3 hx_pos]
      have hAi : ε ^ (2 * d) * (S.card : ℝ) ≤ ((A i').card : ℝ) := hL.L1_width i'
      have hAj : ε ^ (2 * d) * (S.card : ℝ) ≤ ((A j').card : ℝ) := hL.L1_width j'
      have hprod : (ε ^ (2 * d) * (S.card : ℝ)) * (ε ^ (2 * d) * (S.card : ℝ)) ≤
          ((A i').card : ℝ) * ((A j').card : ℝ) :=
        mul_le_mul hAi hAj (by positivity) (by positivity)
      have h4d_pos : 0 < ε ^ (4 * d) := Real.rpow_pos_of_pos hε (4 * d)
      have h4d_eq : ε ^ (4 * d) * (S.card : ℝ) ^ 2 =
          (ε ^ (2 * d) * (S.card : ℝ)) * (ε ^ (2 * d) * (S.card : ℝ)) := by
        have : ε ^ (4 * d) = ε ^ (2 * d) * ε ^ (2 * d) := by
          rw [← Real.rpow_add hε]
          ring_nf
        rw [this]
        ring
      have h10d_le : ε ^ (10 * d) ≤ ε ^ (4 * d) * ε ^ d := by
        rw [← Real.rpow_add hε]
        exact Real.rpow_le_rpow_of_exponent_ge hε hε1.le (by linarith)
      calc (crossEdgeCount G (A i') (A j') : ℝ)
          ≤ ε ^ (10 * d) * (S.card : ℝ) ^ 2 := hcross_le
        _ ≤ (ε ^ (4 * d) * ε ^ d) * (S.card : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right h10d_le (sq_nonneg _)
        _ = ε ^ d * (ε ^ (4 * d) * (S.card : ℝ) ^ 2) := by ring
        _ = ε ^ d * ((ε ^ (2 * d) * (S.card : ℝ)) * (ε ^ (2 * d) * (S.card : ℝ))) := by
            rw [h4d_eq]
        _ ≤ ε ^ d * (((A i').card : ℝ) * ((A j').card : ℝ)) :=
            mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = ε ^ d * ((A i').card : ℝ) * ((A j').card : ℝ) := by ring

/--
When $1 \le m < \lceil \varepsilon^{-1} \rceil$, condition (L2) implies the existence of a block
$A_{j_0}$ with $|A_{j_0}| \ge \varepsilon^d |S|$ (Lemma 5.1 of `FMBV4-016_readable.tex`).
-/
theorem exists_block_card_ge_of_L2 {m : ℕ} {S : Finset V} {ε d : ℝ}
    {A : Fin m → Finset V} (hm_pos : 1 ≤ m) (hm_lt : m < ⌈ε⁻¹⌉₊)
    (hε : 0 < ε) (hd : 1 ≤ d)
    (hL2 : (S.card : ℝ) ^ (1 / d) ≤ ∑ j : Fin m, ((A j).card : ℝ) ^ (1 / d)) :
    ∃ j₀ : Fin m, ε ^ d * (S.card : ℝ) ≤ ((A j₀).card : ℝ) := by
  have hne : (Finset.univ : Finset (Fin m)).Nonempty :=
    ⟨⟨0, hm_pos⟩, Finset.mem_univ _⟩
  obtain ⟨j₀, _, hj₀_max⟩ := Finset.exists_max_image Finset.univ (fun j : Fin m => (A j).card) hne
  refine ⟨j₀, ?_⟩
  have hd_pos : 0 < d := by linarith
  have h1d_nonneg : 0 ≤ 1 / d := by positivity
  have hsum_le : (∑ j : Fin m, ((A j).card : ℝ) ^ (1 / d)) ≤
      (m : ℝ) * ((A j₀).card : ℝ) ^ (1 / d) := by
    calc ∑ j : Fin m, ((A j).card : ℝ) ^ (1 / d)
        ≤ ∑ _j : Fin m, ((A j₀).card : ℝ) ^ (1 / d) := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          exact Real.rpow_le_rpow (Nat.cast_nonneg _)
            (Nat.cast_le.mpr (hj₀_max j (Finset.mem_univ j))) h1d_nonneg
      _ = (m : ℝ) * ((A j₀).card : ℝ) ^ (1 / d) := by
          simp [Finset.sum_const, nsmul_eq_mul]
  have hm_le_inv : (m : ℝ) ≤ ε⁻¹ := (Nat.lt_ceil.mp hm_lt).le
  have hS_1d : (S.card : ℝ) ^ (1 / d) ≤ ε⁻¹ * ((A j₀).card : ℝ) ^ (1 / d) :=
    hL2.trans (hsum_le.trans (mul_le_mul_of_nonneg_right hm_le_inv (by positivity)))
  have hmul_ε : ε * (S.card : ℝ) ^ (1 / d) ≤ ((A j₀).card : ℝ) ^ (1 / d) := by
    calc ε * (S.card : ℝ) ^ (1 / d)
        ≤ ε * (ε⁻¹ * ((A j₀).card : ℝ) ^ (1 / d)) :=
          mul_le_mul_of_nonneg_left hS_1d hε.le
      _ = (ε * ε⁻¹) * ((A j₀).card : ℝ) ^ (1 / d) := by ring
      _ = ((A j₀).card : ℝ) ^ (1 / d) := by rw [mul_inv_cancel₀ hε.ne', one_mul]
  have hrpow_d := Real.rpow_le_rpow (by positivity) hmul_ε hd_pos.le
  have hLHS : (ε * (S.card : ℝ) ^ (1 / d)) ^ d = ε ^ d * (S.card : ℝ) := by
    rw [Real.mul_rpow hε.le (by positivity), ← Real.rpow_mul (Nat.cast_nonneg _),
      one_div_mul_cancel hd_pos.ne', Real.rpow_one]
  have hRHS : (((A j₀).card : ℝ) ^ (1 / d)) ^ d = ((A j₀).card : ℝ) := by
    rw [← Real.rpow_mul (Nat.cast_nonneg _), one_div_mul_cancel hd_pos.ne', Real.rpow_one]
  linarith

/--
**Case 7.1 of Lemma 5.1** ($k \ge \lceil \varepsilon^{-1} \rceil$, `lem:layout-refinement` of `FMBV4-016_readable.tex`):
If $A_{j_0} \subseteq S$ has $|A_{j_0}| \ge \varepsilon^d |S|$ and contains a complete-or-$x$-sparse
$(k, |A_{j_0}| / k^d)$-blockade with $\lceil \varepsilon^{-1} \rceil \le k \le x^{-10}$ where
$x = \varepsilon^{10 d}$, then $S$ contains an $(\lceil \varepsilon^{-1} \rceil, \lfloor \varepsilon^{200 d^2} |S| \rfloor)$-blockade
whose pairs are complete or weakly $\varepsilon^d$-sparse in $G$.
-/
theorem layout_refinement_case_7_1 {G : SimpleGraph V} {S A₀ : Finset V}
    {ε d : ℝ} {k : ℕ} {B : Fin k → Finset V}
    (hA₀_sub : A₀ ⊆ S) (hA₀_card : ε ^ d * (S.card : ℝ) ≤ (A₀.card : ℝ))
    (hε : 0 < ε) (hε_half : ε < 1 / 2) (hd : 1 ≤ d)
    (hk_ge : ⌈ε⁻¹⌉₊ ≤ k) (hk_le : (k : ℝ) ≤ (ε ^ (10 * d)) ^ (-10 : ℝ))
    (hB : IsCompleteOrXSparseBlockadeIn G A₀ k ((A₀.card : ℝ) / (k : ℝ) ^ d) (ε ^ (10 * d)) B) :
    ∃ B' : Fin ⌈ε⁻¹⌉₊ → Finset V,
      IsBlockadeIn G S ⌈ε⁻¹⌉₊ (⌊ε ^ (200 * d ^ 2) * (S.card : ℝ)⌋₊ : ℝ) B' ∧
      ∀ i j : Fin ⌈ε⁻¹⌉₊, i ≠ j →
        IsCompletePair G (B' i) (B' j) ∨ IsWeaklySparsePair G (B' i) (B' j) (ε ^ d) := by
  have hε1 : ε < 1 := by linarith
  have hk_pos : (0 : ℝ) < (k : ℝ) := by
    have : 0 < ⌈ε⁻¹⌉₊ := Nat.ceil_pos.mpr (inv_pos.mpr hε)
    exact_mod_cast this.trans_le hk_ge
  have hkd_pos : 0 < (k : ℝ) ^ d := Real.rpow_pos_of_pos hk_pos d
  have hkd_le : (k : ℝ) ^ d ≤ (ε ^ (100 * d ^ 2))⁻¹ := by
    have h1 : (k : ℝ) ^ d ≤ ((ε ^ (10 * d)) ^ (-10 : ℝ)) ^ d :=
      Real.rpow_le_rpow hk_pos.le hk_le (by linarith)
    have h2 : ((ε ^ (10 * d)) ^ (-10 : ℝ)) ^ d = (ε ^ (100 * d ^ 2))⁻¹ := by
      rw [← Real.rpow_mul hε.le, ← Real.rpow_mul hε.le, ← Real.rpow_neg hε.le]
      congr 1
      ring
    exact h1.trans_eq h2
  have hwidth : (⌊ε ^ (200 * d ^ 2) * (S.card : ℝ)⌋₊ : ℝ) ≤ (A₀.card : ℝ) / (k : ℝ) ^ d := by
    have hfloor : (⌊ε ^ (200 * d ^ 2) * (S.card : ℝ)⌋₊ : ℝ) ≤ ε ^ (200 * d ^ 2) * (S.card : ℝ) :=
      Nat.floor_le (by positivity)
    have hexp : 100 * d ^ 2 + d ≤ 200 * d ^ 2 := by nlinarith
    have hrpow : ε ^ (200 * d ^ 2) ≤ ε ^ (100 * d ^ 2 + d) :=
      Real.rpow_le_rpow_of_exponent_ge hε hε1.le hexp
    have hmul_kd : ε ^ (100 * d ^ 2) * (k : ℝ) ^ d ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hkd_le (by positivity : 0 ≤ ε ^ (100 * d ^ 2))
      rwa [mul_inv_cancel₀ (by positivity)] at this
    have hdiv : ε ^ (100 * d ^ 2 + d) * (S.card : ℝ) ≤ (A₀.card : ℝ) / (k : ℝ) ^ d := by
      rw [le_div_iff₀ hkd_pos, Real.rpow_add hε]
      calc (ε ^ (100 * d ^ 2) * ε ^ d) * (S.card : ℝ) * (k : ℝ) ^ d
          = (ε ^ (100 * d ^ 2) * (k : ℝ) ^ d) * (ε ^ d * (S.card : ℝ)) := by ring
        _ ≤ 1 * (A₀.card : ℝ) :=
            mul_le_mul hmul_kd hA₀_card (by positivity) (by positivity)
        _ = (A₀.card : ℝ) := one_mul _
    exact hfloor.trans ((mul_le_mul_of_nonneg_right hrpow (Nat.cast_nonneg _)).trans hdiv)
  refine ⟨restrictBlockade hk_ge B,
    ((hB.1.mono_ambient hA₀_sub).mono_width hwidth).restrict hk_ge, ?_⟩
  intro i j hij
  have hij' : Fin.castLE hk_ge i ≠ Fin.castLE hk_ge j :=
    fun heq => hij ((Fin.castLE_injective hk_ge) heq)
  rcases hB.2 (Fin.castLE hk_ge i) (Fin.castLE hk_ge j) hij' with hcomp | hsparse
  · exact Or.inl hcomp
  · refine Or.inr (hsparse.isWeaklySparsePair.mono ?_)
    exact Real.rpow_le_rpow_of_exponent_ge hε hε1.le (by linarith)

/-- Splitting a sum over `Fin m` into the term at `j₀` and the subtype `{i : Fin m // i ≠ j₀}`. -/
theorem sum_fin_eq_add_sum_subtype_ne {α : Type*} [AddCommMonoid α] {m : ℕ}
    (j₀ : Fin m) (g : Fin m → α) :
    (∑ i : Fin m, g i) = g j₀ + ∑ i : {i : Fin m // i ≠ j₀}, g i.1 := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀)]
  congr 1
  rw [← Finset.sum_subtype (Finset.univ.erase j₀) (fun i => by simp [Finset.mem_erase])]

/-- Adjacency relation for substituting the pattern graph of $B$ into vertex $j_0$ of $J$. -/
def substPatternAdj {m k : ℕ} (G : SimpleGraph V) (J : SimpleGraph (Fin m)) (j₀ : Fin m)
    (B : Fin k → Finset V) :
    ({i : Fin m // i ≠ j₀} ⊕ Fin k) → ({i : Fin m // i ≠ j₀} ⊕ Fin k) → Prop
  | Sum.inl i, Sum.inl j => J.Adj i.1 j.1
  | Sum.inl i, Sum.inr _ => J.Adj i.1 j₀
  | Sum.inr _, Sum.inl j => J.Adj j₀ j.1
  | Sum.inr p, Sum.inr q => p ≠ q ∧ IsCompletePair G (B p) (B q)

/-- Pattern graph obtained by substituting the pattern graph of $B$ for vertex $j_0$ of $J$. -/
def substPatternGraph {m k : ℕ} (G : SimpleGraph V) (J : SimpleGraph (Fin m)) (j₀ : Fin m)
    (B : Fin k → Finset V) : SimpleGraph ({i : Fin m // i ≠ j₀} ⊕ Fin k) where
  Adj := substPatternAdj G J j₀ B
  symm x y := by
    cases x <;> cases y <;> simp only [substPatternAdj]
    · exact fun h => J.symm h
    · exact fun h => J.symm h
    · exact fun h => J.symm h
    · exact fun ⟨hne, hcomp⟩ => ⟨hne.symm, hcomp.symm⟩
  loopless x := by
    cases x <;> simp only [substPatternAdj]
    · exact J.loopless _
    · exact fun h => h.1 rfl

/--
**Case 7.2 of Lemma 5.1** ($k < \lceil \varepsilon^{-1} \rceil$, `lem:layout-refinement` of `FMBV4-016_readable.tex`):
Substituting a complete-or-$x$-sparse $(k, |A_{j_0}| / k^d)$-blockade $(B_1, \dots, B_k)$ inside
$A_{j_0}$ ($2 \le k < \lceil \varepsilon^{-1} \rceil$) produces a new valid layout on
`{i : Fin m // i ≠ j₀} ⊕ Fin k`.
-/
theorem layout_refinement_case_7_2_sum {m k : ℕ} {G : SimpleGraph V} {S : Finset V}
    {ε d x : ℝ} {J : SimpleGraph (Fin m)} {A : Fin m → Finset V}
    (hL : IsValidLayout G S ε d x J A) (j₀ : Fin m)
    (hε : 0 < ε) (hd : 1 ≤ d) (hx : 0 ≤ x)
    (hk_pos : 1 ≤ k) (hk_lt : k < ⌈ε⁻¹⌉₊)
    (hAj₀ : ε ^ d * (S.card : ℝ) ≤ ((A j₀).card : ℝ))
    {B : Fin k → Finset V}
    (hB : IsCompleteOrXSparseBlockadeIn G (A j₀) k (((A j₀).card : ℝ) / (k : ℝ) ^ d) x B) :
    IsValidLayout G S ε d x (substPatternGraph G J j₀ B)
      (Sum.elim (fun i : {i : Fin m // i ≠ j₀} => A i.1) B) where
  subset_ambient x := by
    cases x with
    | inl i => exact hL.subset_ambient i.1
    | inr p => exact (hB.1.subset_ambient p).trans (hL.subset_ambient j₀)
  nonempty_blocks x := by
    cases x with
    | inl i => exact hL.nonempty_blocks i.1
    | inr p => exact hB.1.nonempty_blocks p
  pairwise_disjoint x y hxy := by
    cases x with
    | inl i =>
      cases y with
      | inl j =>
        exact hL.pairwise_disjoint i.1 j.1 (fun heq => hxy (congrArg Sum.inl (Subtype.ext heq)))
      | inr q =>
        exact Disjoint.mono_right (hB.1.subset_ambient q) (hL.pairwise_disjoint i.1 j₀ i.2)
    | inr p =>
      cases y with
      | inl j =>
        exact Disjoint.mono_left (hB.1.subset_ambient p) (hL.pairwise_disjoint j₀ j.1 j.2.symm)
      | inr q =>
        exact hB.1.pairwise_disjoint p q (fun heq => hxy (congrArg Sum.inr heq))
  complete_of_adj x y hadj := by
    cases x <;> cases y <;> simp only [substPatternGraph, substPatternAdj, Sum.elim_inl, Sum.elim_inr] at hadj ⊢
    · exact hL.complete_of_adj _ _ hadj
    · exact (hL.complete_of_adj _ _ hadj).mono Subset.rfl (hB.1.subset_ambient _)
    · exact (hL.complete_of_adj _ _ hadj).mono (hB.1.subset_ambient _) Subset.rfl
    · exact hadj.2
  L1_width x := by
    cases x with
    | inl i => exact hL.L1_width i.1
    | inr p =>
      simp only [Sum.elim_inr]
      have hk_le_inv : (k : ℝ) ≤ ε⁻¹ := (Nat.lt_ceil.mp hk_lt).le
      have hk_pos_real : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos
      have hkd_pos : 0 < (k : ℝ) ^ d := Real.rpow_pos_of_pos hk_pos_real d
      have hεk_le : ε * (k : ℝ) ≤ 1 := by
        calc ε * (k : ℝ) ≤ ε * ε⁻¹ := mul_le_mul_of_nonneg_left hk_le_inv hε.le
          _ = 1 := mul_inv_cancel₀ hε.ne'
      have hεkd_le : ε ^ d * (k : ℝ) ^ d ≤ 1 := by
        rw [← Real.mul_rpow hε.le hk_pos_real.le]
        exact Real.rpow_le_one (by positivity) hεk_le (by linarith)
      have hstep : ε ^ (2 * d) * (S.card : ℝ) ≤ ((A j₀).card : ℝ) / (k : ℝ) ^ d := by
        rw [le_div_iff₀ hkd_pos]
        have h2d : ε ^ (2 * d) = ε ^ d * ε ^ d := by
          rw [← Real.rpow_add hε]
          ring_nf
        calc ε ^ (2 * d) * (S.card : ℝ) * (k : ℝ) ^ d
            = (ε ^ d * (k : ℝ) ^ d) * (ε ^ d * (S.card : ℝ)) := by rw [h2d]; ring
          _ ≤ 1 * ((A j₀).card : ℝ) :=
              mul_le_mul hεkd_le hAj₀ (by positivity) (by positivity)
          _ = ((A j₀).card : ℝ) := one_mul _
      exact hstep.trans (hB.1.width_ge p)
  L2_potential := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    have hk_pos_real : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos
    have hd_pos : 0 < d := by linarith
    have h1d_nonneg : 0 ≤ 1 / d := by positivity
    have hB_pot : ((A j₀).card : ℝ) ^ (1 / d) ≤ ∑ p : Fin k, ((B p).card : ℝ) ^ (1 / d) := by
      have hterm : ∀ p : Fin k,
          ((A j₀).card : ℝ) ^ (1 / d) / (k : ℝ) ≤ ((B p).card : ℝ) ^ (1 / d) := by
        intro p
        have h1 := Real.rpow_le_rpow (by positivity) (hB.1.width_ge p) h1d_nonneg
        have h2 : (((A j₀).card : ℝ) / (k : ℝ) ^ d) ^ (1 / d) =
            ((A j₀).card : ℝ) ^ (1 / d) / (k : ℝ) := by
          rw [Real.div_rpow (Nat.cast_nonneg _) (by positivity),
            ← Real.rpow_mul hk_pos_real.le, mul_one_div_cancel hd_pos.ne', Real.rpow_one]
        rwa [h2] at h1
      calc ((A j₀).card : ℝ) ^ (1 / d)
          = (k : ℝ) * (((A j₀).card : ℝ) ^ (1 / d) / (k : ℝ)) :=
            (mul_div_cancel₀ _ hk_pos_real.ne').symm
        _ = ∑ _p : Fin k, (((A j₀).card : ℝ) ^ (1 / d) / (k : ℝ)) := by
            simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ p : Fin k, ((B p).card : ℝ) ^ (1 / d) :=
            Finset.sum_le_sum (fun p _ => hterm p)
    have hdecomp := sum_fin_eq_add_sum_subtype_ne j₀ (fun i => ((A i).card : ℝ) ^ (1 / d))
    linarith [hL.L2_potential]
  L3_wrong := by
    classical
    have hW_split :
        wrongEdgeCount G (substPatternGraph G J j₀ B)
          (Sum.elim (fun i : {i : Fin m // i ≠ j₀} => A i.1) B) =
        (∑ i : {i : Fin m // i ≠ j₀}, ∑ j : {i : Fin m // i ≠ j₀},
          if i.1 ≠ j.1 ∧ ¬J.Adj i.1 j.1 then crossEdgeCount G (A i.1) (A j.1) else 0) +
        (∑ i : {i : Fin m // i ≠ j₀}, ∑ p : Fin k,
          if ¬J.Adj i.1 j₀ then crossEdgeCount G (A i.1) (B p) else 0) +
        (∑ p : Fin k, ∑ j : {i : Fin m // i ≠ j₀},
          if ¬J.Adj j₀ j.1 then crossEdgeCount G (B p) (A j.1) else 0) +
        (∑ p : Fin k, ∑ q : Fin k,
          if p ≠ q ∧ ¬IsCompletePair G (B p) (B q) then crossEdgeCount G (B p) (B q) else 0) := by
      unfold wrongEdgeCount
      rw [Fintype.sum_sum_type]
      simp_rw [Fintype.sum_sum_type, Finset.sum_add_distrib]
      have h11 : (∑ x : {i : Fin m // i ≠ j₀}, ∑ y : {i : Fin m // i ≠ j₀},
          if (Sum.inl x : {i : Fin m // i ≠ j₀} ⊕ Fin k) ≠ Sum.inl y ∧
            ¬(substPatternGraph G J j₀ B).Adj (Sum.inl x) (Sum.inl y)
          then crossEdgeCount G
            (Sum.elim (fun i : {i : Fin m // i ≠ j₀} => A i.1) B (Sum.inl x))
            (Sum.elim (fun i : {i : Fin m // i ≠ j₀} => A i.1) B (Sum.inl y))
          else 0) =
          ∑ i : {i : Fin m // i ≠ j₀}, ∑ j : {i : Fin m // i ≠ j₀},
            if i.1 ≠ j.1 ∧ ¬J.Adj i.1 j.1 then crossEdgeCount G (A i.1) (A j.1) else 0 := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        by_cases hij : i = j
        · subst hij
          simp [substPatternGraph]
        · have hval : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
          simp [hij, hval, substPatternGraph, substPatternAdj]
      have h12 : (∑ x : {i : Fin m // i ≠ j₀}, ∑ p : Fin k,
          if (Sum.inl x : {i : Fin m // i ≠ j₀} ⊕ Fin k) ≠ Sum.inr p ∧
            ¬(substPatternGraph G J j₀ B).Adj (Sum.inl x) (Sum.inr p)
          then crossEdgeCount G
            (Sum.elim (fun i : {i : Fin m // i ≠ j₀} => A i.1) B (Sum.inl x))
            (Sum.elim (fun i : {i : Fin m // i ≠ j₀} => A i.1) B (Sum.inr p))
          else 0) =
          ∑ i : {i : Fin m // i ≠ j₀}, ∑ p : Fin k,
            if ¬J.Adj i.1 j₀ then crossEdgeCount G (A i.1) (B p) else 0 := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun p _ => ?_))
        simp [substPatternGraph, substPatternAdj]
      have h21 : (∑ p : Fin k, ∑ y : {i : Fin m // i ≠ j₀},
          if (Sum.inr p : {i : Fin m // i ≠ j₀} ⊕ Fin k) ≠ Sum.inl y ∧
            ¬(substPatternGraph G J j₀ B).Adj (Sum.inr p) (Sum.inl y)
          then crossEdgeCount G
            (Sum.elim (fun i : {i : Fin m // i ≠ j₀} => A i.1) B (Sum.inr p))
            (Sum.elim (fun i : {i : Fin m // i ≠ j₀} => A i.1) B (Sum.inl y))
          else 0) =
          ∑ p : Fin k, ∑ j : {i : Fin m // i ≠ j₀},
            if ¬J.Adj j₀ j.1 then crossEdgeCount G (B p) (A j.1) else 0 := by
        refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun j _ => ?_))
        simp [substPatternGraph, substPatternAdj]
      have h22 : (∑ p : Fin k, ∑ q : Fin k,
          if (Sum.inr p : {i : Fin m // i ≠ j₀} ⊕ Fin k) ≠ Sum.inr q ∧
            ¬(substPatternGraph G J j₀ B).Adj (Sum.inr p) (Sum.inr q)
          then crossEdgeCount G
            (Sum.elim (fun i : {i : Fin m // i ≠ j₀} => A i.1) B (Sum.inr p))
            (Sum.elim (fun i : {i : Fin m // i ≠ j₀} => A i.1) B (Sum.inr q))
          else 0) =
          ∑ p : Fin k, ∑ q : Fin k,
            if p ≠ q ∧ ¬IsCompletePair G (B p) (B q) then crossEdgeCount G (B p) (B q) else 0 := by
        refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
        by_cases hpq : p = q <;> simp [hpq, substPatternGraph, substPatternAdj]
      rw [h11, h12, h21, h22]
      omega
    have h12_le : (∑ i : {i : Fin m // i ≠ j₀}, ∑ p : Fin k,
        if ¬J.Adj i.1 j₀ then crossEdgeCount G (A i.1) (B p) else 0) ≤
        ∑ i : {i : Fin m // i ≠ j₀},
          if i.1 ≠ j₀ ∧ ¬J.Adj i.1 j₀ then crossEdgeCount G (A i.1) (A j₀) else 0 := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      have hi : i.1 ≠ j₀ := i.2
      by_cases hadj : J.Adj i.1 j₀ <;> simp [hi, hadj]
      exact sum_crossEdgeCount_right_le G (A i.1) (A j₀) B hB.1.subset_ambient hB.1.pairwise_disjoint
    have h21_le : (∑ p : Fin k, ∑ j : {i : Fin m // i ≠ j₀},
        if ¬J.Adj j₀ j.1 then crossEdgeCount G (B p) (A j.1) else 0) ≤
        ∑ j : {i : Fin m // i ≠ j₀},
          if j₀ ≠ j.1 ∧ ¬J.Adj j₀ j.1 then crossEdgeCount G (A j₀) (A j.1) else 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_le_sum (fun j _ => ?_)
      have hj : j₀ ≠ j.1 := j.2.symm
      by_cases hadj : J.Adj j₀ j.1 <;> simp [hj, hadj]
      exact sum_crossEdgeCount_left_le G (A j.1) (A j₀) B hB.1.subset_ambient hB.1.pairwise_disjoint
    have hW_old_eq : wrongEdgeCount G J A =
        (∑ i : {i : Fin m // i ≠ j₀}, ∑ j : {i : Fin m // i ≠ j₀},
          if i.1 ≠ j.1 ∧ ¬J.Adj i.1 j.1 then crossEdgeCount G (A i.1) (A j.1) else 0) +
        (∑ i : {i : Fin m // i ≠ j₀},
          if i.1 ≠ j₀ ∧ ¬J.Adj i.1 j₀ then crossEdgeCount G (A i.1) (A j₀) else 0) +
        (∑ j : {i : Fin m // i ≠ j₀},
          if j₀ ≠ j.1 ∧ ¬J.Adj j₀ j.1 then crossEdgeCount G (A j₀) (A j.1) else 0) := by
      unfold wrongEdgeCount
      rw [sum_fin_eq_add_sum_subtype_ne j₀]
      rw [sum_fin_eq_add_sum_subtype_ne j₀
        (fun j => if j₀ ≠ j ∧ ¬J.Adj j₀ j then crossEdgeCount G (A j₀) (A j) else 0)]
      have h_inner : (∑ i : {i : Fin m // i ≠ j₀}, ∑ j : Fin m,
          if i.1 ≠ j ∧ ¬J.Adj i.1 j then crossEdgeCount G (A i.1) (A j) else 0) =
          (∑ i : {i : Fin m // i ≠ j₀},
            if i.1 ≠ j₀ ∧ ¬J.Adj i.1 j₀ then crossEdgeCount G (A i.1) (A j₀) else 0) +
          (∑ i : {i : Fin m // i ≠ j₀}, ∑ j : {i : Fin m // i ≠ j₀},
            if i.1 ≠ j.1 ∧ ¬J.Adj i.1 j.1 then crossEdgeCount G (A i.1) (A j.1) else 0) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        exact sum_fin_eq_add_sum_subtype_ne j₀ _
      rw [h_inner]
      have h_diag : (if j₀ ≠ j₀ ∧ ¬J.Adj j₀ j₀ then crossEdgeCount G (A j₀) (A j₀) else 0) = 0 := by
        simp
      rw [h_diag, zero_add]
      ring
    have h22_le : ((∑ p : Fin k, ∑ q : Fin k,
        if p ≠ q ∧ ¬IsCompletePair G (B p) (B q) then crossEdgeCount G (B p) (B q) else 0 : ℕ) : ℝ) ≤
        x * (((A j₀).card : ℝ) ^ 2 - ∑ p : Fin k, ((B p).card : ℝ) ^ 2) := by
      push_cast
      have hpointwise : (∑ p : Fin k, ∑ q : Fin k,
          (if p ≠ q ∧ ¬IsCompletePair G (B p) (B q) then (crossEdgeCount G (B p) (B q) : ℝ) else 0)) ≤
          ∑ p : Fin k, ∑ q : Fin k, (if p ≠ q then x * ((B p).card : ℝ) * ((B q).card : ℝ) else 0) := by
        refine Finset.sum_le_sum (fun p _ => Finset.sum_le_sum (fun q _ => ?_))
        by_cases hpq : p = q
        · simp [hpq]
        · by_cases hcomp : IsCompletePair G (B p) (B q)
          · simp [hpq, hcomp]
            positivity
          · simp only [ne_eq, hpq, not_false_eq_true, hcomp, and_self, ↓reduceIte]
            rcases hB.2 p q hpq with hc | hs
            · exact False.elim (hcomp hc)
            · exact hs.isWeaklySparsePair
      have hfactor : (∑ p : Fin k, ∑ q : Fin k,
          (if p ≠ q then x * ((B p).card : ℝ) * ((B q).card : ℝ) else 0)) =
          x * (∑ p : Fin k, ∑ q : Fin k, if p ≠ q then ((B p).card : ℝ) * ((B q).card : ℝ) else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun q _ => ?_)
        by_cases hpq : p = q <;> simp [hpq, mul_assoc]
      have hoff := sum_offDiag_card_mul_le_sq_sub hB.1.subset_ambient hB.1.pairwise_disjoint
      calc (∑ p : Fin k, ∑ q : Fin k,
            if p ≠ q ∧ ¬IsCompletePair G (B p) (B q) then (crossEdgeCount G (B p) (B q) : ℝ) else 0)
          ≤ x * (∑ p : Fin k, ∑ q : Fin k, if p ≠ q then ((B p).card : ℝ) * ((B q).card : ℝ) else 0) := by
            rw [← hfactor]
            exact hpointwise
        _ ≤ x * (((A j₀).card : ℝ) ^ 2 - ∑ p : Fin k, ((B p).card : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hoff hx
    have hW_nat :
        wrongEdgeCount G (substPatternGraph G J j₀ B)
          (Sum.elim (fun i : {i : Fin m // i ≠ j₀} => A i.1) B) ≤
        wrongEdgeCount G J A +
        ∑ p : Fin k, ∑ q : Fin k,
          if p ≠ q ∧ ¬IsCompletePair G (B p) (B q) then crossEdgeCount G (B p) (B q) else 0 := by
      omega
    have hW_real :
        (wrongEdgeCount G (substPatternGraph G J j₀ B)
          (Sum.elim (fun i : {i : Fin m // i ≠ j₀} => A i.1) B) : ℝ) ≤
        (wrongEdgeCount G J A : ℝ) +
        ((∑ p : Fin k, ∑ q : Fin k,
          if p ≠ q ∧ ¬IsCompletePair G (B p) (B q) then crossEdgeCount G (B p) (B q) else 0 : ℕ) : ℝ) := by
      exact_mod_cast hW_nat
    have hD_eq :
        decidedBound S (Sum.elim (fun i : {i : Fin m // i ≠ j₀} => A i.1) B) =
        decidedBound S A + (((A j₀).card : ℝ) ^ 2 - ∑ p : Fin k, ((B p).card : ℝ) ^ 2) := by
      unfold decidedBound
      rw [Fintype.sum_sum_type, sum_fin_eq_add_sum_subtype_ne j₀ (fun i => ((A i).card : ℝ) ^ 2)]
      simp only [Sum.elim_inl, Sum.elim_inr]
      ring
    rw [hD_eq, mul_add]
    linarith [hL.L3_wrong]

/--
Cardinality of the substituted index type `{i : Fin m // i ≠ j₀} ⊕ Fin k` is $m - 1 + k$.
-/
theorem card_substIndex {m k : ℕ} (j₀ : Fin m) :
    Fintype.card ({i : Fin m // i ≠ j₀} ⊕ Fin k) = m - 1 + k := by
  have hj₀ := j₀.isLt
  have hm_pos : 1 ≤ m := by omega
  have hsum1 := sum_fin_eq_add_sum_subtype_ne j₀ (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hsum1
  rw [Fintype.card_sum, Fintype.card_fin]
  omega

/--
Inductive Layout Refinement Loop (Lemma 5.1, `lem:layout-refinement` of `FMBV4-016_readable.tex`):
By induction on `rem ≥ ⌈ε⁻¹⌉₊ - m`, any valid layout of size $m \ge 1$ in $S$ can be refined
until either Case 7.1 produces the desired blockade or $m \ge \lceil \varepsilon^{-1} \rceil$
terminates with the desired blockade.
-/
theorem layout_refinement_induction (G : SimpleGraph V) (S : Finset V)
    {ε d : ℝ} (hε : 0 < ε) (hε_half : ε < 1 / 2) (hd : 1 ≤ d)
    (hblockade : ∀ F ⊆ S, ε ^ d * (S.card : ℝ) ≤ (F.card : ℝ) →
      ∃ (k : ℕ) (B : Fin k → Finset V),
        2 ≤ k ∧ (k : ℝ) ≤ (ε ^ (10 * d)) ^ (-10 : ℝ) ∧
        IsCompleteOrXSparseBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ d) (ε ^ (10 * d)) B) :
    ∀ (rem m : ℕ) (J : SimpleGraph (Fin m)) (A : Fin m → Finset V),
      1 ≤ m → ⌈ε⁻¹⌉₊ - m ≤ rem →
      IsValidLayout G S ε d (ε ^ (10 * d)) J A →
      ∃ B : Fin ⌈ε⁻¹⌉₊ → Finset V,
        IsBlockadeIn G S ⌈ε⁻¹⌉₊ (⌊ε ^ (200 * d ^ 2) * (S.card : ℝ)⌋₊ : ℝ) B ∧
        ∀ i j : Fin ⌈ε⁻¹⌉₊, i ≠ j →
          IsCompletePair G (B i) (B j) ∨ IsWeaklySparsePair G (B i) (B j) (ε ^ d) := by
  intro rem
  induction rem with
  | zero =>
    intro m J A _ hrem hL
    have hm : ⌈ε⁻¹⌉₊ ≤ m := Nat.sub_eq_zero_iff_le.mp (Nat.le_zero.mp hrem)
    exact validLayout_extract_blockade hL hε hε_half hd hm
  | succ rem ih =>
    intro m J A hm_pos hrem hL
    by_cases hm_ge : ⌈ε⁻¹⌉₊ ≤ m
    · exact validLayout_extract_blockade hL hε hε_half hd hm_ge
    · push_neg at hm_ge
      obtain ⟨j₀, hj₀_card⟩ := exists_block_card_ge_of_L2 hm_pos hm_ge hε hd hL.L2_potential
      obtain ⟨k, B, hk_two, hk_upper, hB⟩ :=
        hblockade (A j₀) (hL.subset_ambient j₀) hj₀_card
      by_cases hk_ge : ⌈ε⁻¹⌉₊ ≤ k
      · exact layout_refinement_case_7_1 (hL.subset_ambient j₀) hj₀_card
          hε hε_half hd hk_ge hk_upper hB
      · push_neg at hk_ge
        have hL_sum := layout_refinement_case_7_2_sum hL j₀ hε hd (by positivity)
          (by omega) hk_ge hj₀_card hB
        let I' := {i : Fin m // i ≠ j₀} ⊕ Fin k
        let m' := Fintype.card I'
        have hm'_eq : m' = m - 1 + k := card_substIndex j₀
        have hL' : IsValidLayout G S ε d (ε ^ (10 * d))
            ((substPatternGraph G J j₀ B).comap (Fintype.equivFin I').symm)
            ((Sum.elim (fun i : {i : Fin m // i ≠ j₀} => A i.1) B) ∘ (Fintype.equivFin I').symm) :=
          hL_sum.reindex (Fintype.equivFin I').symm
        exact ih m' _ _ (by omega) (by omega) hL'

/--
**Lemma 5.1 (`lem:layout-refinement`, Self-Contained Layout Refinement for Complete-or-$x$-Sparse Blockades)**:
Let $\varepsilon \in (0, 1/2)$, $d \ge 1$, and $x = \varepsilon^{10 d}$. Let $S \subseteq V(G)$
with $|S| \ge \varepsilon^{-200 d^2}$ such that for every $F \subseteq S$ with $|F| \ge \varepsilon^d |S|$,
there exist $k \in [2, x^{-10}]$ and a complete-or-$x$-sparse $(k, |F| / k^d)$-blockade in $F$.
Then $S$ contains an $(\lceil \varepsilon^{-1} \rceil, \lfloor \varepsilon^{200 d^2} |S| \rfloor)$-blockade
whose block pairs are complete or weakly $\varepsilon^d$-sparse in $G$.
-/
theorem lem_layout_refinement (G : SimpleGraph V) (S : Finset V)
    {ε d : ℝ} (hε : 0 < ε) (hε_half : ε < 1 / 2) (hd : 1 ≤ d)
    (hS_card : ε ^ (-200 * d ^ 2) ≤ (S.card : ℝ))
    (hblockade : ∀ F ⊆ S, ε ^ d * (S.card : ℝ) ≤ (F.card : ℝ) →
      ∃ (k : ℕ) (B : Fin k → Finset V),
        2 ≤ k ∧ (k : ℝ) ≤ (ε ^ (10 * d)) ^ (-10 : ℝ) ∧
        IsCompleteOrXSparseBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ d) (ε ^ (10 * d)) B) :
    ∃ B : Fin ⌈ε⁻¹⌉₊ → Finset V,
      IsBlockadeIn G S ⌈ε⁻¹⌉₊ (⌊ε ^ (200 * d ^ 2) * (S.card : ℝ)⌋₊ : ℝ) B ∧
      ∀ i j : Fin ⌈ε⁻¹⌉₊, i ≠ j →
        IsCompletePair G (B i) (B j) ∨ IsWeaklySparsePair G (B i) (B j) (ε ^ d) := by
  have hS_pos : 0 < (S.card : ℝ) :=
    (Real.rpow_pos_of_pos hε (-200 * d ^ 2)).trans_le hS_card
  have hS_ne : S.Nonempty := Finset.card_pos.mp (by exact_mod_cast hS_pos)
  have hL₀ : IsValidLayout G S ε d (ε ^ (10 * d)) (⊥ : SimpleGraph (Fin 1)) (fun _ => S) :=
    isValidLayout_trivial G hS_ne hε (by linarith) (by linarith)
  exact layout_refinement_induction G S hε hε_half hd hblockade
    (⌈ε⁻¹⌉₊ - 1) 1 (⊥ : SimpleGraph (Fin 1)) (fun _ => S) le_rfl le_rfl hL₀

/-!
## Section 4: Generalized Niceness of $\{P_6\}$ (Proposition 5.3, `prop:gen-nice`)
-/

/--
**Outcome (GN1)** of Definition 2.1(2) (`def:framework`):
$S$ contains an $(\lceil \varepsilon^{-1} \rceil, \lfloor \varepsilon^{c_1} |S| \rfloor)$-blockade
whose block pairs are complete or weakly $\varepsilon^{c_2}$-sparse in $G$.
-/
def GenNiceOutcome1 (G : SimpleGraph V) (S : Finset V) (ε c₁ c₂ : ℝ) : Prop :=
  ∃ B : Fin ⌈ε⁻¹⌉₊ → Finset V,
    IsBlockadeIn G S ⌈ε⁻¹⌉₊ (⌊ε ^ c₁ * (S.card : ℝ)⌋₊ : ℝ) B ∧
    ∀ i j : Fin ⌈ε⁻¹⌉₊, i ≠ j →
      IsCompletePair G (B i) (B j) ∨ IsWeaklySparsePair G (B i) (B j) (ε ^ c₂)

/--
**Outcome (GN2)** of Definition 2.1(2) (`def:framework`):
$\kappa(G) \ge (\varepsilon^{c_3} |S|)^{c_4}$.
-/
def GenNiceOutcome2 (G : SimpleGraph V) (S : Finset V) (ε c₃ c₄ : ℝ) : Prop :=
  (ε ^ c₃ * (S.card : ℝ)) ^ c₄ ≤ (kappa G : ℝ)

/--
**Outcome (GN3)** of Definition 2.1(2) (`def:framework`):
$S$ contains a complete or anticomplete $(k, |S| / k^{c_5})$-blockade for some integer
$k \ge \varepsilon^{-c_6}$.
-/
def GenNiceOutcome3 (G : SimpleGraph V) (S : Finset V) (ε c₅ c₆ : ℝ) : Prop :=
  ∃ (k : ℕ) (B : Fin k → Finset V),
    ε ^ (-c₆) ≤ (k : ℝ) ∧
    (IsCompleteBlockadeIn G S k ((S.card : ℝ) / (k : ℝ) ^ c₅) B ∨
     IsAnticompleteBlockadeIn G S k ((S.card : ℝ) / (k : ℝ) ^ c₅) B)

/--
**Outcome (GN4)** of Definition 2.1(2) (`def:framework`):
$S$ contains an $\varepsilon^{c_7}$-restricted induced subgraph $U \subseteq S$ of cardinality
$|U| \ge \varepsilon^{c_8} |S|$.
-/
def GenNiceOutcome4 (G : SimpleGraph V) (S : Finset V) (ε c₇ c₈ : ℝ) : Prop :=
  ∃ U ⊆ S, ε ^ c₈ * (S.card : ℝ) ≤ (U.card : ℝ) ∧ IsEpsRestrictedOn G U (ε ^ c₇)

/--
Disjunction of the four generalized niceness outcomes (GN1)--(GN4) of Definition 2.1(2) (`def:framework`).
-/
def SatisfiesGenNiceAt (G : SimpleGraph V) (S : Finset V)
    (ε c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ : ℝ) : Prop :=
  GenNiceOutcome1 G S ε c₁ c₂ ∨
  GenNiceOutcome2 G S ε c₃ c₄ ∨
  GenNiceOutcome3 G S ε c₅ c₆ ∨
  GenNiceOutcome4 G S ε c₇ c₈

/-- Leaf exponent parameter $c_{\mathrm{leaf}} := \max(4 d_{\mathrm{leaf}} + 1, 4)$ (line 466). -/
noncomputable def cLeaf (d_leaf : ℝ) : ℝ := max (4 * d_leaf + 1) 4

/-- Leaf factor parameter $b_{\mathrm{leaf}} := \max(h_{\mathrm{leaf}}, 4)$ (line 466). -/
noncomputable def bLeaf (h_leaf : ℝ) : ℝ := max h_leaf 4

/-- Base blockade threshold $c := 2^{-4 b_{\mathrm{leaf}}} \le 2^{-16}$ (line 466). -/
noncomputable def cParam (h_leaf : ℝ) : ℝ := (2 : ℝ) ^ (-4 * bLeaf h_leaf)

/-- Initial multi-scale density scale $\lambda_0 := c^{10}$ (line 468). -/
noncomputable def lambda0Param (h_leaf : ℝ) : ℝ := (cParam h_leaf) ^ (10 : ℝ)

/-- Multi-scale exponent $b_1 := 11/10 > 1$ (line 470). -/
noncomputable def b1Param : ℝ := 11 / 10

/--
Multi-scale exponent $b_2 := \max(3(c_{\mathrm{leaf}} + 2), \lceil \log(1/\delta) / \log(1/c^{10}) \rceil)$
(line 470).
-/
noncomputable def b2Param (d_leaf h_leaf δ : ℝ) : ℝ :=
  max (3 * (cLeaf d_leaf + 2))
    (⌈Real.log (1 / δ) / Real.log (1 / lambda0Param h_leaf)⌉₊ : ℝ)

/-- Multi-scale exponent $b_3 := 3(c_{\mathrm{leaf}} + 2) / 10$ (line 470). -/
noncomputable def b3Param (d_leaf : ℝ) : ℝ := 3 * (cLeaf d_leaf + 2) / 10

/--
Calibrated blockade degree exponent $d := 120 + 50 b_2 (b_{\mathrm{leaf}} + 2) + 2 \lceil \log_2(1/\delta) \rceil$
(Proposition 5.3 of `FMBV4-016_readable.tex`).
-/
noncomputable def dParam (d_leaf h_leaf δ : ℝ) : ℝ :=
  120 + 50 * b2Param d_leaf h_leaf δ * (bLeaf h_leaf + 2) +
    2 * (⌈Real.log (1 / δ) / Real.log 2⌉₊ : ℝ)

/-- Local sparsity parameter $y := (\lambda / c)^{1/3}$ at scale $\lambda$ (Proposition 5.3). -/
noncomputable def localSparsityY (h_leaf lam : ℝ) : ℝ :=
  (lam / cParam h_leaf) ^ ((1 : ℝ) / 3)

theorem four_le_cLeaf (d_leaf : ℝ) : 4 ≤ cLeaf d_leaf := le_max_right _ _

theorem four_le_bLeaf (h_leaf : ℝ) : 4 ≤ bLeaf h_leaf := le_max_right _ _

theorem cParam_pos (h_leaf : ℝ) : 0 < cParam h_leaf := by
  unfold cParam
  positivity

theorem cParam_lt_half (h_leaf : ℝ) : cParam h_leaf < 1 / 2 := by
  unfold cParam
  have hb : 4 ≤ bLeaf h_leaf := four_le_bLeaf h_leaf
  rw [show (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) by norm_num]
  exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)

theorem two_mul_cParam_le_one (h_leaf : ℝ) : 2 * cParam h_leaf ≤ 1 := by
  linarith [cParam_lt_half h_leaf]

theorem lambda0Param_pos (h_leaf : ℝ) : 0 < lambda0Param h_leaf := by
  unfold lambda0Param
  exact Real.rpow_pos_of_pos (cParam_pos h_leaf) 10

theorem lambda0Param_lt_half (h_leaf : ℝ) : lambda0Param h_leaf < 1 / 2 := by
  unfold lambda0Param
  have hc_pos : 0 < cParam h_leaf := cParam_pos h_leaf
  have hc_lt : cParam h_leaf < 1 / 2 := cParam_lt_half h_leaf
  have h1 : (cParam h_leaf) ^ (10 : ℝ) ≤ (cParam h_leaf) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hc_pos (by linarith) (by norm_num)
  rw [Real.rpow_one] at h1
  linarith

theorem one_lt_b1Param : 1 < b1Param := by
  unfold b1Param
  norm_num

theorem b2Param_ge_three_cLeaf (d_leaf h_leaf δ : ℝ) :
    3 * (cLeaf d_leaf + 2) ≤ b2Param d_leaf h_leaf δ :=
  le_max_left _ _

theorem b2Param_pos (d_leaf h_leaf δ : ℝ) : 0 < b2Param d_leaf h_leaf δ := by
  have h1 := four_le_cLeaf d_leaf
  have h2 := b2Param_ge_three_cLeaf d_leaf h_leaf δ
  linarith

theorem b3Param_pos (d_leaf : ℝ) : 0 < b3Param d_leaf := by
  unfold b3Param
  have h1 := four_le_cLeaf d_leaf
  linarith

/--
Verification of the multi-scale exponent inequality $(b_1 - 1) b_2 \ge b_3$ in Proposition 5.3
(`FMBV4-016_readable.tex`).
-/
theorem gen_nice_exponent_ineq (d_leaf h_leaf δ : ℝ) :
    (b1Param - 1) * b2Param d_leaf h_leaf δ ≥ b3Param d_leaf := by
  unfold b1Param b3Param
  have h := b2Param_ge_three_cLeaf d_leaf h_leaf δ
  linarith

theorem six_hundred_le_dParam (d_leaf h_leaf δ : ℝ) :
    600 ≤ dParam d_leaf h_leaf δ := by
  unfold dParam
  have hb2 : 18 ≤ b2Param d_leaf h_leaf δ := by
    have := four_le_cLeaf d_leaf
    have := b2Param_ge_three_cLeaf d_leaf h_leaf δ
    linarith
  have hbL : 4 ≤ bLeaf h_leaf := four_le_bLeaf h_leaf
  have hceil : 0 ≤ (⌈Real.log (1 / δ) / Real.log 2⌉₊ : ℝ) := Nat.cast_nonneg _
  nlinarith

theorem one_le_dParam (d_leaf h_leaf δ : ℝ) : 1 ≤ dParam d_leaf h_leaf δ := by
  linarith [six_hundred_le_dParam d_leaf h_leaf δ]

/--
Key local sparsity scaling equations and bounds at scale $\lambda \in (0, \lambda_0]$
(Proposition 5.3 of `FMBV4-016_readable.tex`):
1. $c y^3 = \lambda$;
2. $y \le c^3$;
3. $2 y^4 \le \lambda^{11/10}$ and $y^4 \le \lambda^{11/10}$.
-/
theorem cParam_mul_localSparsityY_cube (h_leaf : ℝ) {lam : ℝ} (hlam : 0 ≤ lam) :
    cParam h_leaf * (localSparsityY h_leaf lam) ^ (3 : ℝ) = lam := by
  unfold localSparsityY
  have hc : 0 < cParam h_leaf := cParam_pos h_leaf
  rw [← Real.rpow_mul (by positivity), one_div_mul_cancel (by norm_num), Real.rpow_one,
    mul_div_cancel₀ _ hc.ne']

theorem localSparsityY_le_cParam_cube (h_leaf : ℝ) {lam : ℝ} (hlam : 0 ≤ lam)
    (hlam_le : lam ≤ lambda0Param h_leaf) :
    localSparsityY h_leaf lam ≤ (cParam h_leaf) ^ (3 : ℝ) := by
  unfold localSparsityY lambda0Param at *
  have hc : 0 < cParam h_leaf := cParam_pos h_leaf
  have h91 : (cParam h_leaf) ^ (9 : ℝ) * cParam h_leaf = (cParam h_leaf) ^ (10 : ℝ) := by
    rw [← Real.rpow_add_one hc.ne']
    congr 1
    norm_num
  have hdiv : lam / cParam h_leaf ≤ (cParam h_leaf) ^ (9 : ℝ) := by
    rw [div_le_iff₀ hc, h91]
    exact hlam_le
  calc (lam / cParam h_leaf) ^ ((1 : ℝ) / 3)
      ≤ ((cParam h_leaf) ^ (9 : ℝ)) ^ ((1 : ℝ) / 3) :=
        Real.rpow_le_rpow (by positivity) hdiv (by positivity)
    _ = (cParam h_leaf) ^ (3 : ℝ) := by
        rw [← Real.rpow_mul hc.le]
        norm_num

theorem two_mul_localSparsityY_pow_four_le (h_leaf : ℝ) {lam : ℝ}
    (hlam : 0 ≤ lam) (hlam_le : lam ≤ lambda0Param h_leaf) :
    2 * (localSparsityY h_leaf lam) ^ (4 : ℝ) ≤ lam ^ b1Param := by
  set c := cParam h_leaf
  set y := localSparsityY h_leaf lam
  have hc_pos : 0 < c := cParam_pos h_leaf
  have hy_nonneg : 0 ≤ y := by
    unfold y localSparsityY
    positivity
  have hy_le : y ≤ c ^ (3 : ℝ) := localSparsityY_le_cParam_cube h_leaf hlam hlam_le
  have hlam_eq : lam = c * y ^ (3 : ℝ) := (cParam_mul_localSparsityY_cube h_leaf hlam).symm
  have h_rhs : lam ^ b1Param = c ^ (11 / 10 : ℝ) * y ^ (33 / 10 : ℝ) := by
    unfold b1Param
    rw [hlam_eq, Real.mul_rpow hc_pos.le (by positivity), ← Real.rpow_mul hy_nonneg]
    norm_num
  have h_y4 : y ^ (4 : ℝ) = y ^ (7 / 10 : ℝ) * y ^ (33 / 10 : ℝ) := by
    rw [← Real.rpow_add' hy_nonneg (by norm_num)]
    norm_num
  have hy_07 : y ^ (7 / 10 : ℝ) ≤ c * c ^ (11 / 10 : ℝ) := by
    calc y ^ (7 / 10 : ℝ)
        ≤ (c ^ (3 : ℝ)) ^ (7 / 10 : ℝ) := Real.rpow_le_rpow hy_nonneg hy_le (by norm_num)
      _ = c ^ (21 / 10 : ℝ) := by rw [← Real.rpow_mul hc_pos.le]; norm_num
      _ = c ^ (1 : ℝ) * c ^ (11 / 10 : ℝ) := by rw [← Real.rpow_add hc_pos]; norm_num
      _ = c * c ^ (11 / 10 : ℝ) := by rw [Real.rpow_one]
  have h2c : 2 * c ≤ 1 := two_mul_cParam_le_one h_leaf
  have h2y_07 : 2 * y ^ (7 / 10 : ℝ) ≤ c ^ (11 / 10 : ℝ) := by
    calc 2 * y ^ (7 / 10 : ℝ)
        ≤ 2 * (c * c ^ (11 / 10 : ℝ)) := mul_le_mul_of_nonneg_left hy_07 (by norm_num)
      _ = (2 * c) * c ^ (11 / 10 : ℝ) := by ring
      _ ≤ 1 * c ^ (11 / 10 : ℝ) := mul_le_mul_of_nonneg_right h2c (by positivity)
      _ = c ^ (11 / 10 : ℝ) := one_mul _
  rw [h_y4, h_rhs]
  calc 2 * (y ^ (7 / 10 : ℝ) * y ^ (33 / 10 : ℝ))
      = (2 * y ^ (7 / 10 : ℝ)) * y ^ (33 / 10 : ℝ) := by ring
    _ ≤ c ^ (11 / 10 : ℝ) * y ^ (33 / 10 : ℝ) :=
        mul_le_mul_of_nonneg_right h2y_07 (by positivity)

theorem localSparsityY_pow_four_le (h_leaf : ℝ) {lam : ℝ}
    (hlam : 0 ≤ lam) (hlam_le : lam ≤ lambda0Param h_leaf) :
    (localSparsityY h_leaf lam) ^ (4 : ℝ) ≤ lam ^ b1Param := by
  have hc_pos : 0 < cParam h_leaf := cParam_pos h_leaf
  have h1 := two_mul_localSparsityY_pow_four_le h_leaf hlam hlam_le
  have h2 : 0 ≤ (localSparsityY h_leaf lam) ^ (4 : ℝ) :=
    Real.rpow_nonneg (by unfold localSparsityY; positivity) 4
  linarith

/--
Unconditional scale separation $x = \varepsilon^{10 d} < \lambda_0 = c^{10}$ for all $\varepsilon \in (0, 1/2)$.
-/
theorem eps_pow_ten_dParam_lt_lambda0Param (d_leaf h_leaf δ : ℝ) {ε : ℝ}
    (hε : 0 < ε) (hε_half : ε < 1 / 2) :
    ε ^ (10 * dParam d_leaf h_leaf δ) < lambda0Param h_leaf := by
  set d := dParam d_leaf h_leaf δ
  have hd_pos : 0 < 10 * d := by linarith [six_hundred_le_dParam d_leaf h_leaf δ]
  have h1 : ε ^ (10 * d) < (1 / 2 : ℝ) ^ (10 * d) :=
    Real.rpow_lt_rpow hε.le hε_half hd_pos
  have h2 : (1 / 2 : ℝ) ^ (10 * d) = (2 : ℝ) ^ (-10 * d) := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  have h3 : lambda0Param h_leaf = (2 : ℝ) ^ (-40 * bLeaf h_leaf) := by
    unfold lambda0Param cParam
    rw [← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  have hb2 : 18 ≤ b2Param d_leaf h_leaf δ := by
    have := four_le_cLeaf d_leaf
    have := b2Param_ge_three_cLeaf d_leaf h_leaf δ
    linarith
  have hbL : 4 ≤ bLeaf h_leaf := four_le_bLeaf h_leaf
  have hceil : 0 ≤ (⌈Real.log (1 / δ) / Real.log 2⌉₊ : ℝ) := Nat.cast_nonneg _
  have hd_ge : 4 * bLeaf h_leaf ≤ d := by
    unfold d dParam
    nlinarith
  have h4 : (2 : ℝ) ^ (-10 * d) ≤ (2 : ℝ) ^ (-40 * bLeaf h_leaf) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  linarith

/--
Unconditional multi-scale termination size bound (Proposition 5.3 of `FMBV4-016_readable.tex`):
If $|F| \ge \varepsilon^d |S|$, $|F_0| \ge \lambda_0^{b_2} |F|$, and $|U| \ge x^{b_1 b_2} |F_0|$
with $x = \varepsilon^{10 d}$, then $|U| \ge \varepsilon^{200 d^2} |S|$.
-/
theorem eps_200_d_sq_le_x_b1_b2_card (d_leaf h_leaf δ : ℝ) {ε : ℝ}
    (hε : 0 < ε) (hε_half : ε < 1 / 2) {S F F₀ : Finset V}
    (hF : ε ^ (dParam d_leaf h_leaf δ) * (S.card : ℝ) ≤ (F.card : ℝ))
    (hF₀ : (lambda0Param h_leaf) ^ (b2Param d_leaf h_leaf δ) * (F.card : ℝ) ≤ (F₀.card : ℝ)) :
    ε ^ (200 * (dParam d_leaf h_leaf δ) ^ 2) * (S.card : ℝ) ≤
      (ε ^ (10 * dParam d_leaf h_leaf δ)) ^ (b1Param * b2Param d_leaf h_leaf δ) * (F₀.card : ℝ) := by
  set d := dParam d_leaf h_leaf δ
  set b₂ := b2Param d_leaf h_leaf δ
  have hε1 : ε < 1 := by linarith
  have hlam0_pos : 0 < lambda0Param h_leaf := lambda0Param_pos h_leaf
  have hb2 : 18 ≤ b₂ := by
    have := four_le_cLeaf d_leaf
    have := b2Param_ge_three_cLeaf d_leaf h_leaf δ
    linarith
  have hbL : 4 ≤ bLeaf h_leaf := four_le_bLeaf h_leaf
  have hceil : 0 ≤ (⌈Real.log (1 / δ) / Real.log 2⌉₊ : ℝ) := Nat.cast_nonneg _
  have hd_ge_40b : 40 * bLeaf h_leaf ≤ d := by
    unfold d dParam
    nlinarith
  have hlam0_ge : ε ^ d ≤ lambda0Param h_leaf := by
    have h1 : ε ^ d ≤ (1 / 2 : ℝ) ^ d :=
      Real.rpow_le_rpow hε.le hε_half.le (by linarith [six_hundred_le_dParam d_leaf h_leaf δ])
    have h2 : (1 / 2 : ℝ) ^ d = (2 : ℝ) ^ (-d) := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      congr 1
      ring
    have h3 : lambda0Param h_leaf = (2 : ℝ) ^ (-40 * bLeaf h_leaf) := by
      unfold lambda0Param cParam
      rw [← Real.rpow_mul (by norm_num)]
      congr 1
      ring
    rw [h2] at h1
    rw [h3]
    exact h1.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
  have hlam0_b2_ge : ε ^ (d * b₂) ≤ (lambda0Param h_leaf) ^ b₂ := by
    rw [Real.rpow_mul hε.le]
    exact Real.rpow_le_rpow (by positivity) hlam0_ge (by linarith)
  have hx_b1b2 : (ε ^ (10 * d)) ^ (b1Param * b₂) = ε ^ (11 * d * b₂) := by
    unfold b1Param
    rw [← Real.rpow_mul hε.le]
    congr 1
    ring
  have hd_ge_b2 : 50 * b₂ ≤ d := by
    unfold d dParam
    nlinarith
  have hexp_le : 11 * d * b₂ + d * b₂ + d ≤ 200 * d ^ 2 := by
    have : 600 ≤ d := six_hundred_le_dParam d_leaf h_leaf δ
    nlinarith
  have hrpow_le : ε ^ (200 * d ^ 2) ≤
      (ε ^ (10 * d)) ^ (b1Param * b₂) * (lambda0Param h_leaf) ^ b₂ * ε ^ d := by
    calc ε ^ (200 * d ^ 2)
        ≤ ε ^ (11 * d * b₂ + d * b₂ + d) :=
          Real.rpow_le_rpow_of_exponent_ge hε hε1.le hexp_le
      _ = ε ^ (11 * d * b₂) * ε ^ (d * b₂) * ε ^ d := by
          rw [Real.rpow_add hε, Real.rpow_add hε]
      _ ≤ (ε ^ (10 * d)) ^ (b1Param * b₂) * (lambda0Param h_leaf) ^ b₂ * ε ^ d := by
          rw [hx_b1b2]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hlam0_b2_ge (by positivity)
  calc ε ^ (200 * d ^ 2) * (S.card : ℝ)
      ≤ ((ε ^ (10 * d)) ^ (b1Param * b₂) * (lambda0Param h_leaf) ^ b₂ * ε ^ d) *
          (S.card : ℝ) := mul_le_mul_of_nonneg_right hrpow_le (Nat.cast_nonneg _)
    _ = (ε ^ (10 * d)) ^ (b1Param * b₂) *
          ((lambda0Param h_leaf) ^ b₂ * (ε ^ d * (S.card : ℝ))) := by ring
    _ ≤ (ε ^ (10 * d)) ^ (b1Param * b₂) *
          ((lambda0Param h_leaf) ^ b₂ * (F.card : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hF (by positivity)
    _ ≤ (ε ^ (10 * d)) ^ (b1Param * b₂) * (F₀.card : ℝ) :=
        mul_le_mul_of_nonneg_left hF₀ (by positivity)

theorem multiscale_terminal_card_ge_eps_200_d_sq (d_leaf h_leaf δ : ℝ) {ε : ℝ}
    (hε : 0 < ε) (hε_half : ε < 1 / 2) {S F F₀ U : Finset V}
    (hF : ε ^ (dParam d_leaf h_leaf δ) * (S.card : ℝ) ≤ (F.card : ℝ))
    (hF₀ : (lambda0Param h_leaf) ^ (b2Param d_leaf h_leaf δ) * (F.card : ℝ) ≤ (F₀.card : ℝ))
    (hU : (ε ^ (10 * dParam d_leaf h_leaf δ)) ^ (b1Param * b2Param d_leaf h_leaf δ) *
      (F₀.card : ℝ) ≤ (U.card : ℝ)) :
    ε ^ (200 * (dParam d_leaf h_leaf δ) ^ 2) * (S.card : ℝ) ≤ (U.card : ℝ) :=
  (eps_200_d_sq_le_x_b1_b2_card d_leaf h_leaf δ hε hε_half hF hF₀).trans hU

/--
Small-$|S|$ base case of Proposition 5.3 (`prop:gen-nice` of `FMBV4-016_readable.tex`):
If $|S| \le \varepsilon^{-200 d^2}$ and $\kappa(G) \ge 1$, then Outcome (GN2) holds with
$c_3 = 200 d^2$ and $c_4 = 1$.
-/
theorem genNiceOutcome2_of_card_le {G : SimpleGraph V} {S : Finset V} {ε d : ℝ}
    (hε : 0 < ε) (hkappa : 1 ≤ kappa G) (hS : (S.card : ℝ) ≤ ε ^ (-200 * d ^ 2)) :
    GenNiceOutcome2 G S ε (200 * d ^ 2) 1 := by
  unfold GenNiceOutcome2
  rw [Real.rpow_one]
  have h1 : ε ^ (200 * d ^ 2) * (S.card : ℝ) ≤ ε ^ (200 * d ^ 2) * ε ^ (-200 * d ^ 2) :=
    mul_le_mul_of_nonneg_left hS (by positivity)
  have h2 : ε ^ (200 * d ^ 2) * ε ^ (-200 * d ^ 2) = 1 := by
    rw [← Real.rpow_add hε]
    norm_num
  have h3 : (1 : ℝ) ≤ (kappa G : ℝ) := by exact_mod_cast hkappa
  linarith

/--
**Proposition 5.3 (`prop:gen-nice`, Generalized Niceness of $\{P_6\}$)**:
Let $d_{\mathrm{leaf}} > 0$, $h_{\mathrm{leaf}} \ge 1$, and $\delta \in (0, 1)$, and let
$d := \mathrm{dParam}(d_{\mathrm{leaf}}, h_{\mathrm{leaf}}, \delta)$.
For every $\varepsilon \in (0, 1/2)$ and every $\overline{P_6}$-free graph $G$ on a nonempty
vertex set $S \subseteq V(G)$ (with $\kappa(G) \ge 1$), if for every $F \subseteq S$ with
$|F| \ge \varepsilon^d |S|$ there exists a $\lambda_0$-restricted $F_0 \subseteq F$ satisfying the
single-scale dichotomy (yielding either Outcome (GN3), a moderate complete-or-$x$-sparse
$(k, |F|/k^d)$-blockade in $F$, or a $\lambda^{b_1}$-restricted subgraph $F' \subseteq F_t$ of size
$\ge \lambda^{b_3} |F_t|$), then $G$ satisfies at least one of Outcomes (GN1)--(GN4) with constants
$c_1 = 200 d^2, c_2 = d, c_3 = 200 d^2, c_4 = 1, c_5 = d + 1, c_6 = 20 d, c_7 = 10 d, c_8 = 200 d^2$.
-/
theorem lem_gen_nice_P6 (G : SimpleGraph V) (S : Finset V)
    {d_leaf h_leaf δ ε : ℝ}
    (hε : 0 < ε) (hε_half : ε < 1 / 2)
    (hkappa : 1 ≤ kappa G)
    (h_multiscale_input :
      let d := dParam d_leaf h_leaf δ
      let x := ε ^ (10 * d)
      let lam0 := lambda0Param h_leaf
      let b₁ := b1Param
      let b₂ := b2Param d_leaf h_leaf δ
      let b₃ := b3Param d_leaf
      ∀ F ⊆ S, ε ^ d * (S.card : ℝ) ≤ (F.card : ℝ) →
        x < lam0 ∧
        ∃ F₀ ⊆ F, IsEpsRestrictedOn G F₀ lam0 ∧
          x ^ (b₁ * b₂) * (F₀.card : ℝ) ≥ ε ^ (200 * d ^ 2) * (S.card : ℝ) ∧
          ∀ lam ∈ Set.Icc x lam0, ∀ F_t ⊆ F₀,
            IsEpsRestrictedOn G F_t lam → lam ^ b₂ * (F₀.card : ℝ) ≤ (F_t.card : ℝ) →
              (GenNiceOutcome3 G S ε (d + 1) (20 * d) ∨
               ∃ (k : ℕ) (B : Fin k → Finset V),
                 2 ≤ k ∧ (k : ℝ) ≤ x ^ (-10 : ℝ) ∧
                 IsCompleteOrXSparseBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ d) x B) ∨
              ∃ F' ⊆ F_t, IsEpsRestrictedOn G F' (lam ^ b₁) ∧
                lam ^ b₃ * (F_t.card : ℝ) ≤ (F'.card : ℝ)) :
    let d := dParam d_leaf h_leaf δ
    SatisfiesGenNiceAt G S ε (200 * d ^ 2) d (200 * d ^ 2) 1 (d + 1) (20 * d) (10 * d) (200 * d ^ 2) := by
  classical
  intro d
  by_cases hS_small : (S.card : ℝ) ≤ ε ^ (-200 * d ^ 2)
  · exact Or.inr (Or.inl (genNiceOutcome2_of_card_le hε hkappa hS_small))
  · push_neg at hS_small
    set x := ε ^ (10 * d)
    set lam0 := lambda0Param h_leaf
    set b₁ := b1Param
    set b₂ := b2Param d_leaf h_leaf δ
    set b₃ := b3Param d_leaf
    by_cases hall_F : ∀ F ⊆ S, ε ^ d * (S.card : ℝ) ≤ (F.card : ℝ) →
        ∃ (k : ℕ) (B : Fin k → Finset V),
          2 ≤ k ∧ (k : ℝ) ≤ x ^ (-10 : ℝ) ∧
          IsCompleteOrXSparseBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ d) x B
    · refine Or.inl ?_
      exact lem_layout_refinement G S hε hε_half (one_le_dParam d_leaf h_leaf δ)
        hS_small.le hall_F
    · push_neg at hall_F
      obtain ⟨F, hF_sub, hF_card, hF_no_blockade⟩ := hall_F
      obtain ⟨hx_lt, F₀, hF₀_sub, hF₀_rest, hF₀_size, hstep⟩ :=
        h_multiscale_input F hF_sub hF_card
      let O : Finset V → Prop := fun _ =>
        GenNiceOutcome3 G S ε (d + 1) (20 * d) ∨
        ∃ (k : ℕ) (B : Fin k → Finset V),
          2 ≤ k ∧ (k : ℝ) ≤ x ^ (-10 : ℝ) ∧
          IsCompleteOrXSparseBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ d) x B
      have hm := lem_multiscale_sparsification G F₀ O
        (lambda0Param_pos h_leaf) (lambda0Param_lt_half h_leaf)
        (Real.rpow_pos_of_pos hε (10 * d)) hx_lt
        one_lt_b1Param (b2Param_pos d_leaf h_leaf δ) (b3Param_pos d_leaf)
        (gen_nice_exponent_ineq d_leaf h_leaf δ) hF₀_rest hstep
      rcases hm with ⟨F_t, _, hOF_t⟩ | ⟨U, hU_sub, hU_rest, hU_card⟩
      · rcases hOF_t with hGN3 | ⟨k, B, hk2, hkup, hB⟩
        · exact Or.inr (Or.inr (Or.inl hGN3))
        · exact False.elim (hF_no_blockade k B hk2 hkup hB)
      · refine Or.inr (Or.inr (Or.inr ?_))
        exact ⟨U, hU_sub.trans (hF₀_sub.trans hF_sub), hF₀_size.trans hU_card, hU_rest⟩

/-!
## Section 5: Single-Scale Sparsification Step of Proposition 5.3 (`single_scale_sparsification_step`)
(`prop:gen-nice` of `FMBV4-016_readable.tex`)
-/

theorem localSparsityY_pos (h_leaf : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    0 < localSparsityY h_leaf lam := by
  unfold localSparsityY
  have hc : 0 < cParam h_leaf := cParam_pos h_leaf
  positivity

theorem localSparsityY_lt_half (h_leaf : ℝ) {lam : ℝ} (hlam : 0 ≤ lam)
    (hlam_le : lam ≤ lambda0Param h_leaf) :
    localSparsityY h_leaf lam < 1 / 2 := by
  have hy_le : localSparsityY h_leaf lam ≤ (cParam h_leaf) ^ (3 : ℝ) :=
    localSparsityY_le_cParam_cube h_leaf hlam hlam_le
  have hc_pos : 0 < cParam h_leaf := cParam_pos h_leaf
  have hc_lt : cParam h_leaf < 1 / 2 := cParam_lt_half h_leaf
  have hc3_le : (cParam h_leaf) ^ (3 : ℝ) ≤ (cParam h_leaf) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hc_pos (by linarith) (by norm_num)
  rw [Real.rpow_one] at hc3_le
  linarith

theorem two_mul_localSparsityY_pow_four_nat_le (h_leaf : ℝ) {lam : ℝ}
    (hlam : 0 ≤ lam) (hlam_le : lam ≤ lambda0Param h_leaf) :
    2 * (localSparsityY h_leaf lam) ^ 4 ≤ lam ^ b1Param := by
  have h := two_mul_localSparsityY_pow_four_le h_leaf hlam hlam_le
  rwa [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h

theorem localSparsityY_pow_four_nat_le (h_leaf : ℝ) {lam : ℝ}
    (hlam : 0 ≤ lam) (hlam_le : lam ≤ lambda0Param h_leaf) :
    (localSparsityY h_leaf lam) ^ 4 ≤ lam ^ b1Param := by
  have h := localSparsityY_pow_four_le h_leaf hlam hlam_le
  rwa [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h

theorem two_mul_localSparsityY_pow_four_le_one (h_leaf : ℝ) {lam : ℝ}
    (hlam : 0 ≤ lam) (hlam_le : lam ≤ lambda0Param h_leaf) :
    2 * (localSparsityY h_leaf lam) ^ 4 ≤ 1 := by
  have h1 := two_mul_localSparsityY_pow_four_nat_le h_leaf hlam hlam_le
  have hlam0 : lambda0Param h_leaf < 1 / 2 := lambda0Param_lt_half h_leaf
  have h2 : lam ^ b1Param ≤ 1 :=
    Real.rpow_le_one hlam (by linarith) (by unfold b1Param; positivity)
  linarith

/--
Monotonicity helper for `GenNiceOutcome3`: a complete or anticomplete $(k, w)$-blockade in
$F' \subseteq S$ with $\varepsilon^{-c_6} \le k$ and $|S| / k^{c_5} \le w$ yields
`GenNiceOutcome3 G S ε c₅ c₆`.
-/
theorem genNiceOutcome3_of_pure_blockade_in_sub {G : SimpleGraph V} {S F' : Finset V}
    {ε c₅ c₆ w : ℝ} {k : ℕ} {B : Fin k → Finset V}
    (hF'_sub : F' ⊆ S) (hk : ε ^ (-c₆) ≤ (k : ℝ))
    (hw : (S.card : ℝ) / (k : ℝ) ^ c₅ ≤ w)
    (hB : IsCompleteBlockadeIn G F' k w B ∨ IsAnticompleteBlockadeIn G F' k w B) :
    GenNiceOutcome3 G S ε c₅ c₆ := by
  refine ⟨k, B, hk, ?_⟩
  rcases hB with ⟨hB_in, hcomp⟩ | ⟨hB_in, hanti⟩
  · exact Or.inl ⟨(hB_in.mono_ambient hF'_sub).mono_width hw, hcomp⟩
  · exact Or.inr ⟨(hB_in.mono_ambient hF'_sub).mono_width hw, hanti⟩

/--
Monotonicity of `IsCompleteOrXSparseBlockadeIn` when enlarging the ambient set and decreasing the
width lower bound.
-/
theorem IsCompleteOrXSparseBlockadeIn.mono_sub_width {G : SimpleGraph V} {F' F : Finset V}
    {k : ℕ} {w₁ w₂ x : ℝ} {B : Fin k → Finset V}
    (hB : IsCompleteOrXSparseBlockadeIn G F' k w₁ x B) (hsub : F' ⊆ F) (hw : w₂ ≤ w₁) :
    IsCompleteOrXSparseBlockadeIn G F k w₂ x B :=
  ⟨(hB.1.mono_ambient hsub).mono_width hw, hB.2⟩

/-- Elementary bound $k^{-e} \le 2^{-e}$ for $k \ge 2$ and $e \ge 0$. -/
theorem rpow_neg_le_two_rpow_neg {k e : ℝ} (hk : 2 ≤ k) (he : 0 ≤ e) :
    k ^ (-e) ≤ (2 : ℝ) ^ (-e) := by
  rw [Real.rpow_neg (by linarith), Real.rpow_neg (by norm_num)]
  exact inv_anti₀ (by positivity) (Real.rpow_le_rpow (by norm_num) hk he)

/--
Width and length calibration for Outcome 1 of Comb Dichotomy (Proposition 5.3 of `FMBV4-016_readable.tex`):
If $k \ge x^{-2}$ with $x = \varepsilon^{10 d}$, $\lambda \ge x$, $|F| \ge \varepsilon^d |S|$,
$|F_0| \ge \lambda_0^{b_2} |F|$, $|F_t| \ge \lambda^{b_2} |F_0|$, and $|F'| \ge c |F_t|$, then
$\varepsilon^{-20 d} \le k$ and $|S| / k^{d + 1} \le |F'| / k^{120}$.
-/
theorem pure_blockade_width_ge_for_gn3 (d_leaf h_leaf δ : ℝ) {ε lam : ℝ} {k : ℕ}
    {S F F₀ F_t F' : Finset V}
    (hε : 0 < ε) (hε_half : ε < 1 / 2)
    (hlam : ε ^ (10 * dParam d_leaf h_leaf δ) ≤ lam)
    (hF : ε ^ (dParam d_leaf h_leaf δ) * (S.card : ℝ) ≤ (F.card : ℝ))
    (hF₀ : (lambda0Param h_leaf) ^ (b2Param d_leaf h_leaf δ) * (F.card : ℝ) ≤ (F₀.card : ℝ))
    (hFt : lam ^ (b2Param d_leaf h_leaf δ) * (F₀.card : ℝ) ≤ (F_t.card : ℝ))
    (hF' : cParam h_leaf * (F_t.card : ℝ) ≤ (F'.card : ℝ))
    (hk_x : (ε ^ (10 * dParam d_leaf h_leaf δ)) ^ (-2 : ℝ) ≤ (k : ℝ)) :
    ε ^ (-(20 * dParam d_leaf h_leaf δ)) ≤ (k : ℝ) ∧
    (S.card : ℝ) / (k : ℝ) ^ (dParam d_leaf h_leaf δ + 1) ≤
      (F'.card : ℝ) / (k : ℝ) ^ (120 : ℝ) := by
  set d := dParam d_leaf h_leaf δ
  set x := ε ^ (10 * d)
  set b₂ := b2Param d_leaf h_leaf δ
  set bL := bLeaf h_leaf
  set c := cParam h_leaf
  set lam0 := lambda0Param h_leaf
  have hd600 : 600 ≤ d := six_hundred_le_dParam d_leaf h_leaf δ
  have hbL4 : 4 ≤ bL := four_le_bLeaf h_leaf
  have hb2_18 : 18 ≤ b₂ := by
    have := four_le_cLeaf d_leaf
    have := b2Param_ge_three_cLeaf d_leaf h_leaf δ
    linarith
  have hx_neg2 : x ^ (-2 : ℝ) = ε ^ (-(20 * d)) := by
    unfold x
    rw [← Real.rpow_mul hε.le]
    congr 1
    ring
  have hk_eps : ε ^ (-(20 * d)) ≤ (k : ℝ) := hx_neg2 ▸ hk_x
  have hε_inv : (2 : ℝ) ≤ ε⁻¹ := by
    rw [← inv_inv (2 : ℝ)]
    exact inv_anti₀ hε (by linarith)
  have hk2 : 2 ≤ (k : ℝ) := by
    have h2_le : (2 : ℝ) ≤ ε ^ (-(20 * d)) := by
      rw [Real.rpow_neg hε.le, ← Real.inv_rpow hε.le]
      calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
        _ ≤ (2 : ℝ) ^ (20 * d) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ ≤ (ε⁻¹) ^ (20 * d) := Real.rpow_le_rpow (by norm_num) hε_inv (by linarith)
    exact h2_le.trans hk_eps
  have hk1 : 1 ≤ (k : ℝ) := by linarith
  have hk_pos : 0 < (k : ℝ) := by linarith
  have hc_pos : 0 < c := cParam_pos h_leaf
  have hlam0_pos : 0 < lam0 := lambda0Param_pos h_leaf
  have hx_pos : 0 < x := Real.rpow_pos_of_pos hε (10 * d)
  have hlam_pos : 0 < lam := hx_pos.trans_le hlam
  have h_eps_neg_d : ε ^ (-d) ≤ (k : ℝ) := by
    calc ε ^ (-d)
        = (ε ^ (-(20 * d))) ^ (1 / 20 : ℝ) := by
          rw [← Real.rpow_mul hε.le]
          congr 1
          ring
      _ ≤ (k : ℝ) ^ (1 / 20 : ℝ) := Real.rpow_le_rpow (by positivity) hk_eps (by norm_num)
      _ ≤ (k : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hk1 (by norm_num)
      _ = (k : ℝ) := Real.rpow_one _
  have hk_inv_eps : (k : ℝ) ^ (-1 : ℝ) ≤ ε ^ d := by
    rw [Real.rpow_neg hk_pos.le, Real.rpow_one, ← inv_inv (ε ^ d), ← Real.rpow_neg hε.le]
    exact inv_anti₀ (by positivity) h_eps_neg_d
  have hx_neg_b2 : x ^ (-b₂) ≤ (k : ℝ) ^ (b₂ / 2) := by
    calc x ^ (-b₂)
        = (x ^ (-2 : ℝ)) ^ (b₂ / 2) := by
          rw [← Real.rpow_mul hx_pos.le]
          congr 1
          ring
      _ ≤ (k : ℝ) ^ (b₂ / 2) := Real.rpow_le_rpow (by positivity) hk_x (by positivity)
  have hk_lam_b2 : (k : ℝ) ^ (-(b₂ / 2)) ≤ lam ^ b₂ := by
    rw [Real.rpow_neg hk_pos.le]
    have h1 : ((k : ℝ) ^ (b₂ / 2))⁻¹ ≤ (x ^ (-b₂))⁻¹ := inv_anti₀ (by positivity) hx_neg_b2
    rw [Real.rpow_neg hx_pos.le, inv_inv] at h1
    exact h1.trans (Real.rpow_le_rpow hx_pos.le hlam (by linarith))
  have hk_c : (k : ℝ) ^ (-(4 * bL)) ≤ c := by
    have h := rpow_neg_le_two_rpow_neg hk2 (by linarith : 0 ≤ 4 * bL)
    have hc_eq : c = (2 : ℝ) ^ (-(4 * bL)) := by
      unfold c cParam bL
      congr 1
      ring
    rwa [hc_eq]
  have hk_lam0_b2 : (k : ℝ) ^ (-(40 * bL * b₂)) ≤ lam0 ^ b₂ := by
    have h := rpow_neg_le_two_rpow_neg hk2 (by positivity : 0 ≤ 40 * bL * b₂)
    have hlam0_eq : lam0 ^ b₂ = (2 : ℝ) ^ (-(40 * bL * b₂)) := by
      unfold lam0 lambda0Param cParam bL
      rw [← Real.rpow_mul (by positivity), ← Real.rpow_mul (by norm_num)]
      congr 1
      ring
    rwa [hlam0_eq]
  have hd_ge : 120 + 4 * bL + b₂ / 2 + 40 * bL * b₂ + 1 ≤ d + 1 := by
    have hceil : 0 ≤ (⌈Real.log (1 / δ) / Real.log 2⌉₊ : ℝ) := Nat.cast_nonneg _
    unfold d dParam
    nlinarith
  have hk_exp : (k : ℝ) ^ (-(d + 1)) ≤
      (k : ℝ) ^ (-120 : ℝ) * (k : ℝ) ^ (-(4 * bL)) * (k : ℝ) ^ (-(b₂ / 2)) *
        (k : ℝ) ^ (-(40 * bL * b₂)) * (k : ℝ) ^ (-1 : ℝ) := by
    calc (k : ℝ) ^ (-(d + 1))
        ≤ (k : ℝ) ^ (-(120 + 4 * bL + b₂ / 2 + 40 * bL * b₂ + 1)) :=
          Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)
      _ = (k : ℝ) ^ (-120 + -(4 * bL) + -(b₂ / 2) + -(40 * bL * b₂) + -1) := by
          congr 1
          ring
      _ = (k : ℝ) ^ (-120 : ℝ) * (k : ℝ) ^ (-(4 * bL)) * (k : ℝ) ^ (-(b₂ / 2)) *
            (k : ℝ) ^ (-(40 * bL * b₂)) * (k : ℝ) ^ (-1 : ℝ) := by
          rw [Real.rpow_add hk_pos, Real.rpow_add hk_pos, Real.rpow_add hk_pos, Real.rpow_add hk_pos]
  have hprod_le : (k : ℝ) ^ (-(d + 1)) ≤
      (k : ℝ) ^ (-120 : ℝ) * c * lam ^ b₂ * lam0 ^ b₂ * ε ^ d := by
    refine hk_exp.trans ?_
    have h1 : (k : ℝ) ^ (-120 : ℝ) * (k : ℝ) ^ (-(4 * bL)) ≤ (k : ℝ) ^ (-120 : ℝ) * c :=
      mul_le_mul_of_nonneg_left hk_c (by positivity)
    have h2 : (k : ℝ) ^ (-120 : ℝ) * (k : ℝ) ^ (-(4 * bL)) * (k : ℝ) ^ (-(b₂ / 2)) ≤
        (k : ℝ) ^ (-120 : ℝ) * c * lam ^ b₂ :=
      mul_le_mul h1 hk_lam_b2 (by positivity) (by positivity)
    have h3 : (k : ℝ) ^ (-120 : ℝ) * (k : ℝ) ^ (-(4 * bL)) * (k : ℝ) ^ (-(b₂ / 2)) *
        (k : ℝ) ^ (-(40 * bL * b₂)) ≤
        (k : ℝ) ^ (-120 : ℝ) * c * lam ^ b₂ * lam0 ^ b₂ :=
      mul_le_mul h2 hk_lam0_b2 (by positivity) (by positivity)
    exact mul_le_mul h3 hk_inv_eps (by positivity) (by positivity)
  refine ⟨hk_eps, ?_⟩
  have h_chain : c * (lam ^ b₂ * (lam0 ^ b₂ * (ε ^ d * (S.card : ℝ)))) ≤ (F'.card : ℝ) := by
    have hlam_b2_pos : 0 ≤ lam ^ b₂ := by positivity
    have hlam0_b2_pos : 0 ≤ lam0 ^ b₂ := by positivity
    calc c * (lam ^ b₂ * (lam0 ^ b₂ * (ε ^ d * (S.card : ℝ))))
        ≤ c * (lam ^ b₂ * (lam0 ^ b₂ * (F.card : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hF hlam0_b2_pos) hlam_b2_pos) hc_pos.le
      _ ≤ c * (lam ^ b₂ * (F₀.card : ℝ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hF₀ hlam_b2_pos) hc_pos.le
      _ ≤ c * (F_t.card : ℝ) := mul_le_mul_of_nonneg_left hFt hc_pos.le
      _ ≤ (F'.card : ℝ) := hF'
  rw [div_eq_mul_inv, div_eq_mul_inv, ← Real.rpow_neg hk_pos.le, ← Real.rpow_neg hk_pos.le]
  calc (S.card : ℝ) * (k : ℝ) ^ (-(d + 1))
      ≤ (S.card : ℝ) * ((k : ℝ) ^ (-120 : ℝ) * c * lam ^ b₂ * lam0 ^ b₂ * ε ^ d) :=
        mul_le_mul_of_nonneg_left hprod_le (Nat.cast_nonneg _)
    _ = (k : ℝ) ^ (-120 : ℝ) * (c * (lam ^ b₂ * (lam0 ^ b₂ * (ε ^ d * (S.card : ℝ))))) := by ring
    _ ≤ (k : ℝ) ^ (-120 : ℝ) * (F'.card : ℝ) :=
        mul_le_mul_of_nonneg_left h_chain (by positivity)
    _ = (F'.card : ℝ) * (k : ℝ) ^ (-120 : ℝ) := by ring

/--
Width calibration for Outcome 2 of Comb Dichotomy (Proposition 5.3 of `FMBV4-016_readable.tex`):
If $k \ge 2$, $y = (\lambda / c)^{1/3} \ge (2k)^{-8}$, $|F_0| \ge \lambda_0^{b_2} |F|$,
$|F_t| \ge \lambda^{b_2} |F_0|$, and $|F'| \ge c |F_t|$, then
$|F| / k^d \le |F'| / k^{120}$.
-/
theorem moderate_blockade_width_ge_for_layout (d_leaf h_leaf δ : ℝ) {lam : ℝ} {k : ℕ}
    {F F₀ F_t F' : Finset V}
    (hlam_pos : 0 < lam)
    (hk2 : 2 ≤ k)
    (hy_ge : (2 * (k : ℝ)) ^ (-8 : ℝ) ≤ localSparsityY h_leaf lam)
    (hF₀ : (lambda0Param h_leaf) ^ (b2Param d_leaf h_leaf δ) * (F.card : ℝ) ≤ (F₀.card : ℝ))
    (hFt : lam ^ (b2Param d_leaf h_leaf δ) * (F₀.card : ℝ) ≤ (F_t.card : ℝ))
    (hF' : cParam h_leaf * (F_t.card : ℝ) ≤ (F'.card : ℝ)) :
    (F.card : ℝ) / (k : ℝ) ^ (dParam d_leaf h_leaf δ) ≤
      (F'.card : ℝ) / (k : ℝ) ^ (120 : ℝ) := by
  set d := dParam d_leaf h_leaf δ
  set b₂ := b2Param d_leaf h_leaf δ
  set bL := bLeaf h_leaf
  set c := cParam h_leaf
  set lam0 := lambda0Param h_leaf
  set y := localSparsityY h_leaf lam
  have hc_pos : 0 < c := cParam_pos h_leaf
  have hlam0_pos : 0 < lam0 := lambda0Param_pos h_leaf
  have hy_pos : 0 < y := localSparsityY_pos h_leaf hlam_pos
  have hbL4 : 4 ≤ bL := four_le_bLeaf h_leaf
  have hb2_18 : 18 ≤ b₂ := by
    have := four_le_cLeaf d_leaf
    have := b2Param_ge_three_cLeaf d_leaf h_leaf δ
    linarith
  have hk2_real : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by linarith
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  have h2k_le_sq : 2 * (k : ℝ) ≤ (k : ℝ) ^ (2 : ℝ) := by
    calc 2 * (k : ℝ)
        ≤ (k : ℝ) * (k : ℝ) := mul_le_mul_of_nonneg_right hk2_real hk_pos.le
      _ = (k : ℝ) ^ (2 : ℕ) := (sq (k : ℝ)).symm
      _ = (k : ℝ) ^ (2 : ℝ) := (Real.rpow_natCast (k : ℝ) 2).symm
  have hk_neg16_le_y : (k : ℝ) ^ (-16 : ℝ) ≤ y := by
    have h1 : (k : ℝ) ^ (-16 : ℝ) = (((k : ℝ) ^ (2 : ℝ)) ^ (8 : ℝ))⁻¹ := by
      rw [← Real.rpow_mul hk_pos.le, ← Real.rpow_neg hk_pos.le]
      norm_num
    have h2 : (2 * (k : ℝ)) ^ (-8 : ℝ) = ((2 * (k : ℝ)) ^ (8 : ℝ))⁻¹ :=
      Real.rpow_neg (by positivity) 8
    rw [h1]
    refine (inv_anti₀ (by positivity)
      (Real.rpow_le_rpow (by positivity) h2k_le_sq (by norm_num))).trans ?_
    linarith
  have hk_neg48_le_y3 : (k : ℝ) ^ (-48 : ℝ) ≤ y ^ (3 : ℝ) := by
    calc (k : ℝ) ^ (-48 : ℝ)
        = ((k : ℝ) ^ (-16 : ℝ)) ^ (3 : ℝ) := by
          rw [← Real.rpow_mul hk_pos.le]
          norm_num
      _ ≤ y ^ (3 : ℝ) := Real.rpow_le_rpow (by positivity) hk_neg16_le_y (by norm_num)
  have hk_c : (k : ℝ) ^ (-(4 * bL)) ≤ c := by
    have h := rpow_neg_le_two_rpow_neg hk2_real (by linarith : 0 ≤ 4 * bL)
    have hc_eq : c = (2 : ℝ) ^ (-(4 * bL)) := by
      unfold c cParam bL
      congr 1
      ring
    rwa [hc_eq]
  have hk_lam : (k : ℝ) ^ (-(4 * bL + 48)) ≤ lam := by
    have hlam_eq : c * y ^ (3 : ℝ) = lam := cParam_mul_localSparsityY_cube h_leaf hlam_pos.le
    calc (k : ℝ) ^ (-(4 * bL + 48))
        = (k : ℝ) ^ (-(4 * bL) + -48) := by congr 1; ring
      _ = (k : ℝ) ^ (-(4 * bL)) * (k : ℝ) ^ (-48 : ℝ) := Real.rpow_add hk_pos _ _
      _ ≤ c * y ^ (3 : ℝ) := mul_le_mul hk_c hk_neg48_le_y3 (by positivity) (by positivity)
      _ = lam := hlam_eq
  have hk_lam_b2 : (k : ℝ) ^ (-((4 * bL + 48) * b₂)) ≤ lam ^ b₂ := by
    calc (k : ℝ) ^ (-((4 * bL + 48) * b₂))
        = ((k : ℝ) ^ (-(4 * bL + 48))) ^ b₂ := by
          rw [← Real.rpow_mul hk_pos.le]
          congr 1
          ring
      _ ≤ lam ^ b₂ := Real.rpow_le_rpow (by positivity) hk_lam (by linarith)
  have hk_lam0_b2 : (k : ℝ) ^ (-(40 * bL * b₂)) ≤ lam0 ^ b₂ := by
    have h := rpow_neg_le_two_rpow_neg hk2_real (by positivity : 0 ≤ 40 * bL * b₂)
    have hlam0_eq : lam0 ^ b₂ = (2 : ℝ) ^ (-(40 * bL * b₂)) := by
      unfold lam0 lambda0Param cParam bL
      rw [← Real.rpow_mul (by positivity), ← Real.rpow_mul (by norm_num)]
      congr 1
      ring
    rwa [hlam0_eq]
  have hd_ge : 120 + 4 * bL + (4 * bL + 48) * b₂ + 40 * bL * b₂ ≤ d := by
    have hceil : 0 ≤ (⌈Real.log (1 / δ) / Real.log 2⌉₊ : ℝ) := Nat.cast_nonneg _
    unfold d dParam
    nlinarith
  have hk_exp : (k : ℝ) ^ (-d) ≤
      (k : ℝ) ^ (-120 : ℝ) * (k : ℝ) ^ (-(4 * bL)) *
        (k : ℝ) ^ (-((4 * bL + 48) * b₂)) * (k : ℝ) ^ (-(40 * bL * b₂)) := by
    calc (k : ℝ) ^ (-d)
        ≤ (k : ℝ) ^ (-(120 + 4 * bL + (4 * bL + 48) * b₂ + 40 * bL * b₂)) :=
          Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)
      _ = (k : ℝ) ^ (-120 + -(4 * bL) + -((4 * bL + 48) * b₂) + -(40 * bL * b₂)) := by
          congr 1
          ring
      _ = (k : ℝ) ^ (-120 : ℝ) * (k : ℝ) ^ (-(4 * bL)) *
            (k : ℝ) ^ (-((4 * bL + 48) * b₂)) * (k : ℝ) ^ (-(40 * bL * b₂)) := by
          rw [Real.rpow_add hk_pos, Real.rpow_add hk_pos, Real.rpow_add hk_pos]
  have hprod_le : (k : ℝ) ^ (-d) ≤ (k : ℝ) ^ (-120 : ℝ) * c * lam ^ b₂ * lam0 ^ b₂ := by
    refine hk_exp.trans ?_
    have h1 : (k : ℝ) ^ (-120 : ℝ) * (k : ℝ) ^ (-(4 * bL)) ≤ (k : ℝ) ^ (-120 : ℝ) * c :=
      mul_le_mul_of_nonneg_left hk_c (by positivity)
    have h2 : (k : ℝ) ^ (-120 : ℝ) * (k : ℝ) ^ (-(4 * bL)) *
        (k : ℝ) ^ (-((4 * bL + 48) * b₂)) ≤ (k : ℝ) ^ (-120 : ℝ) * c * lam ^ b₂ :=
      mul_le_mul h1 hk_lam_b2 (by positivity) (by positivity)
    exact mul_le_mul h2 hk_lam0_b2 (by positivity) (by positivity)
  have h_chain : c * (lam ^ b₂ * (lam0 ^ b₂ * (F.card : ℝ))) ≤ (F'.card : ℝ) := by
    have hlam_b2_pos : 0 ≤ lam ^ b₂ := by positivity
    calc c * (lam ^ b₂ * (lam0 ^ b₂ * (F.card : ℝ)))
        ≤ c * (lam ^ b₂ * (F₀.card : ℝ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hF₀ hlam_b2_pos) hc_pos.le
      _ ≤ c * (F_t.card : ℝ) := mul_le_mul_of_nonneg_left hFt hc_pos.le
      _ ≤ (F'.card : ℝ) := hF'
  rw [div_eq_mul_inv, div_eq_mul_inv, ← Real.rpow_neg hk_pos.le, ← Real.rpow_neg hk_pos.le]
  calc (F.card : ℝ) * (k : ℝ) ^ (-d)
      ≤ (F.card : ℝ) * ((k : ℝ) ^ (-120 : ℝ) * c * lam ^ b₂ * lam0 ^ b₂) :=
        mul_le_mul_of_nonneg_left hprod_le (Nat.cast_nonneg _)
    _ = (k : ℝ) ^ (-120 : ℝ) * (c * (lam ^ b₂ * (lam0 ^ b₂ * (F.card : ℝ)))) := by ring
    _ ≤ (k : ℝ) ^ (-120 : ℝ) * (F'.card : ℝ) :=
        mul_le_mul_of_nonneg_left h_chain (by positivity)
    _ = (F'.card : ℝ) * (k : ℝ) ^ (-120 : ℝ) := by ring

/--
**Single-Scale Sparsification Step of Proposition 5.3 (`single_scale_sparsification_step`,
`prop:gen-nice` of `FMBV4-016_readable.tex`)**:
At each scale $\lambda \in [x, \lambda_0]$ and $\lambda$-restricted $F_t \subseteq F_0$ with
$|F_t| \ge \lambda^{b_2} |F_0|$, let $y := (\lambda / c)^{1/3}$ be the local sparsity scale
(satisfying $2 y^4 \le \lambda^{b_1} \le 1$). Given:
1. Either a pure (complete or anticomplete) $(k, |F_t| / k^{d_{\mathrm{leaf}}})$-blockade in $F_t$
   with $k \ge \varepsilon^{-20 d}$ and $|F_t| / k^{d_{\mathrm{leaf}}} \ge |S| / k^{d + 1}$
   (which yields Outcome (GN3)), or
2. A complete-or-$y^a$-sparse $(\ell, w_{\mathrm{nat}})$-blockade $B$ in $F_t$ with equal block
   widths $w_{\mathrm{nat}} \ge \lambda^{b_3} |F_t|$ to which `p6_is_wonderful` applies:
   - Under **(W1)**, `p6_is_wonderful` produces $U \subseteq F_t$ of size $\ge w_{\mathrm{nat}} \ge \lambda^{b_3} |F_t|$
     that is $y^4$-restricted, hence $\lambda^{b_1}$-restricted by `localSparsityY_pow_four_nat_le`;
   - Under **(W2)**, `p6_is_wonderful` produces a block $B_{i^*}$ with $< y |F_t|$ open-attachment
     external vertices in $F_t$, from which the Comb Dichotomy / External Apex reduction yields
     either Outcome (GN3), a complete-or-$x$-sparse $(k, |F| / k^d)$-blockade in $F$, or a
     $\lambda^{b_1}$-restricted $F' \subseteq F_t$ of size $\ge \lambda^{b_3} |F_t|$.
-/
theorem single_scale_sparsification_step
    (G : SimpleGraph V) (S F F₀ : Finset V)
    {d_leaf h_leaf δ ε a : ℝ}
    (hG : IsInducedSubgraphFree G P6Compl)
    (hε : 0 < ε)
    (hF_sub : F ⊆ S) (hF₀_sub : F₀ ⊆ F)
    (h_local_dichotomy :
      let d := dParam d_leaf h_leaf δ
      let x := ε ^ (10 * d)
      let lam0 := lambda0Param h_leaf
      let b₁ := b1Param
      let b₂ := b2Param d_leaf h_leaf δ
      let b₃ := b3Param d_leaf
      ∀ lam ∈ Set.Icc x lam0, ∀ F_t ⊆ F₀,
        IsEpsRestrictedOn G F_t lam → lam ^ b₂ * (F₀.card : ℝ) ≤ (F_t.card : ℝ) →
        let y := localSparsityY h_leaf lam
        (∃ (k : ℕ) (B : Fin k → Finset V),
          ε ^ (-(20 * d)) ≤ (k : ℝ) ∧
          (S.card : ℝ) / (k : ℝ) ^ (d + 1) ≤ (F_t.card : ℝ) / (k : ℝ) ^ d_leaf ∧
          (IsCompleteBlockadeIn G F_t k ((F_t.card : ℝ) / (k : ℝ) ^ d_leaf) B ∨
           IsAnticompleteBlockadeIn G F_t k ((F_t.card : ℝ) / (k : ℝ) ^ d_leaf) B)) ∨
        (∃ (ℓ w_nat : ℕ) (B : Fin ℓ → Finset V),
          IsCompleteOrXSparseBlockadeIn G F_t ℓ (w_nat : ℝ) (y ^ a) B ∧
          0 < ℓ ∧ 0 < w_nat ∧ (∀ i : Fin ℓ, (B i).card = w_nat) ∧
          lam ^ b₃ * (F_t.card : ℝ) ≤ (w_nat : ℝ) ∧
          6 * (y ^ a) ≤ 1 / 2 ∧
          (∀ v ∈ blockadeExternalVerts F_t B,
            y * (ℓ : ℝ) ≤ ((openAttachmentIndices G B v).card : ℝ) →
            IsInducedSubgraphFree
              ((blockadePatternGraph G B).induce (openAttachmentIndices G B v : Set (Fin ℓ)))
              witnessH →
            ∃ R ⊆ openAttachmentIndices G B v, R.Nonempty ∧
              1 / (R.card : ℝ) + y ^ a ≤ y ^ 4 ∧
              ((∀ i ∈ R, ∀ j ∈ R, i ≠ j → (blockadePatternGraph G B).Adj i j) ∨
               (∀ i ∈ R, ∀ j ∈ R, i ≠ j → ¬(blockadePatternGraph G B).Adj i j))) ∧
          (∀ i : Fin ℓ,
            ((openAttachmentExternalVerts G F_t B i).card : ℝ) < y * (F_t.card : ℝ) →
            (GenNiceOutcome3 G S ε (d + 1) (20 * d) ∨
             ∃ (k : ℕ) (B' : Fin k → Finset V),
               2 ≤ k ∧ (k : ℝ) ≤ x ^ (-10 : ℝ) ∧
               IsCompleteOrXSparseBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ d) x B') ∨
            ∃ F' ⊆ F_t, IsEpsRestrictedOn G F' (lam ^ b₁) ∧
              lam ^ b₃ * (F_t.card : ℝ) ≤ (F'.card : ℝ)))) :
    let d := dParam d_leaf h_leaf δ
    let x := ε ^ (10 * d)
    let lam0 := lambda0Param h_leaf
    let b₁ := b1Param
    let b₂ := b2Param d_leaf h_leaf δ
    let b₃ := b3Param d_leaf
    ∀ lam ∈ Set.Icc x lam0, ∀ F_t ⊆ F₀,
      IsEpsRestrictedOn G F_t lam → lam ^ b₂ * (F₀.card : ℝ) ≤ (F_t.card : ℝ) →
        (GenNiceOutcome3 G S ε (d + 1) (20 * d) ∨
         ∃ (k : ℕ) (B : Fin k → Finset V),
           2 ≤ k ∧ (k : ℝ) ≤ x ^ (-10 : ℝ) ∧
           IsCompleteOrXSparseBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ d) x B) ∨
        ∃ F' ⊆ F_t, IsEpsRestrictedOn G F' (lam ^ b₁) ∧
          lam ^ b₃ * (F_t.card : ℝ) ≤ (F'.card : ℝ) := by
  intro d x lam0 b₁ b₂ b₃ lam hlam_mem F_t hFt_sub hFt_rest hFt_card
  have hx_pos : 0 < x := Real.rpow_pos_of_pos hε (10 * d)
  have hlam_pos : 0 < lam := hx_pos.trans_le hlam_mem.1
  have hlam_le : lam ≤ lam0 := hlam_mem.2
  set y := localSparsityY h_leaf lam
  have hy_pos : 0 < y := localSparsityY_pos h_leaf hlam_pos
  have hy4_le_b1 : y ^ 4 ≤ lam ^ b₁ := localSparsityY_pow_four_nat_le h_leaf hlam_pos.le hlam_le
  have _h2y4_le_one : 2 * y ^ 4 ≤ 1 := two_mul_localSparsityY_pow_four_le_one h_leaf hlam_pos.le hlam_le
  rcases h_local_dichotomy lam hlam_mem F_t hFt_sub hFt_rest hFt_card with
    ⟨k, B, hk_ge, hw_ge, hB_pure⟩ |
    ⟨ℓ, w_nat, B, hB, hℓ_pos, hw_pos, hw_eq, hw_b3, hya_six, hEH_witnessH, hW2_step⟩
  · refine Or.inl (Or.inl ?_)
    exact genNiceOutcome3_of_pure_blockade_in_sub
      (hFt_sub.trans (hF₀_sub.trans hF_sub)) hk_ge hw_ge hB_pure
  · rcases p6_is_wonderful hG hB hℓ_pos hw_pos hw_eq hy_pos hya_six hEH_witnessH with
      ⟨U, hU_sub, hU_card, hU_rest⟩ | ⟨i, hi_open⟩
    · refine Or.inr ⟨U, hU_sub, hU_rest.mono hy4_le_b1, ?_⟩
      have hU_card_real : (w_nat : ℝ) ≤ (U.card : ℝ) := by exact_mod_cast hU_card
      exact hw_b3.trans hU_card_real
    · exact hW2_step i hi_open

/--
**Complete Synthesis of Proposition 5.3 (`lem_gen_nice_P6_complete`, `prop:gen-nice`)**:
Combines `eps_pow_ten_dParam_lt_lambda0Param`, `multiscale_terminal_card_ge_eps_200_d_sq`,
`single_scale_sparsification_step` (via `p6_is_wonderful`), and `lem_gen_nice_P6` to establish
Generalized Niceness of $\{P_6\}$.
-/
theorem lem_gen_nice_P6_complete
    (G : SimpleGraph V) (S : Finset V)
    {d_leaf h_leaf δ ε a : ℝ}
    (hG : IsInducedSubgraphFree G P6Compl)
    (hε : 0 < ε) (hε_half : ε < 1 / 2)
    (hkappa : 1 ≤ kappa G)
    (h_rodl_and_step :
      let d := dParam d_leaf h_leaf δ
      let x := ε ^ (10 * d)
      let lam0 := lambda0Param h_leaf
      let b₁ := b1Param
      let b₂ := b2Param d_leaf h_leaf δ
      let b₃ := b3Param d_leaf
      ∀ F ⊆ S, ε ^ d * (S.card : ℝ) ≤ (F.card : ℝ) →
        ∃ F₀ ⊆ F, IsEpsRestrictedOn G F₀ lam0 ∧
          lam0 ^ b₂ * (F.card : ℝ) ≤ (F₀.card : ℝ) ∧
          ∀ lam ∈ Set.Icc x lam0, ∀ F_t ⊆ F₀,
            IsEpsRestrictedOn G F_t lam → lam ^ b₂ * (F₀.card : ℝ) ≤ (F_t.card : ℝ) →
            let y := localSparsityY h_leaf lam
            (∃ (k : ℕ) (B : Fin k → Finset V),
              ε ^ (-(20 * d)) ≤ (k : ℝ) ∧
              (S.card : ℝ) / (k : ℝ) ^ (d + 1) ≤ (F_t.card : ℝ) / (k : ℝ) ^ d_leaf ∧
              (IsCompleteBlockadeIn G F_t k ((F_t.card : ℝ) / (k : ℝ) ^ d_leaf) B ∨
               IsAnticompleteBlockadeIn G F_t k ((F_t.card : ℝ) / (k : ℝ) ^ d_leaf) B)) ∨
            (∃ (ℓ w_nat : ℕ) (B : Fin ℓ → Finset V),
              IsCompleteOrXSparseBlockadeIn G F_t ℓ (w_nat : ℝ) (y ^ a) B ∧
              0 < ℓ ∧ 0 < w_nat ∧ (∀ i : Fin ℓ, (B i).card = w_nat) ∧
              lam ^ b₃ * (F_t.card : ℝ) ≤ (w_nat : ℝ) ∧
              6 * (y ^ a) ≤ 1 / 2 ∧
              (∀ v ∈ blockadeExternalVerts F_t B,
                y * (ℓ : ℝ) ≤ ((openAttachmentIndices G B v).card : ℝ) →
                IsInducedSubgraphFree
                  ((blockadePatternGraph G B).induce (openAttachmentIndices G B v : Set (Fin ℓ)))
                  witnessH →
                ∃ R ⊆ openAttachmentIndices G B v, R.Nonempty ∧
                  1 / (R.card : ℝ) + y ^ a ≤ y ^ 4 ∧
                  ((∀ i ∈ R, ∀ j ∈ R, i ≠ j → (blockadePatternGraph G B).Adj i j) ∨
                   (∀ i ∈ R, ∀ j ∈ R, i ≠ j → ¬(blockadePatternGraph G B).Adj i j))) ∧
              (∀ i : Fin ℓ,
                ((openAttachmentExternalVerts G F_t B i).card : ℝ) < y * (F_t.card : ℝ) →
                (GenNiceOutcome3 G S ε (d + 1) (20 * d) ∨
                 ∃ (k : ℕ) (B' : Fin k → Finset V),
                   2 ≤ k ∧ (k : ℝ) ≤ x ^ (-10 : ℝ) ∧
                   IsCompleteOrXSparseBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ d) x B') ∨
                ∃ F' ⊆ F_t, IsEpsRestrictedOn G F' (lam ^ b₁) ∧
                  lam ^ b₃ * (F_t.card : ℝ) ≤ (F'.card : ℝ)))) :
    let d := dParam d_leaf h_leaf δ
    SatisfiesGenNiceAt G S ε (200 * d ^ 2) d (200 * d ^ 2) 1 (d + 1) (20 * d) (10 * d) (200 * d ^ 2) := by
  refine lem_gen_nice_P6 G S hε hε_half hkappa ?_
  intro d x lam0 b₁ b₂ b₃ F hF_sub hF_card
  refine ⟨eps_pow_ten_dParam_lt_lambda0Param d_leaf h_leaf δ hε hε_half, ?_⟩
  obtain ⟨F₀, hF₀_sub, hF₀_rest, hF₀_card, h_local⟩ := h_rodl_and_step F hF_sub hF_card
  refine ⟨F₀, hF₀_sub, hF₀_rest, ?_, ?_⟩
  · exact eps_200_d_sq_le_x_b1_b2_card d_leaf h_leaf δ hε hε_half hF_card hF₀_card
  · exact single_scale_sparsification_step G S F F₀ hG hε hF_sub hF₀_sub h_local

end ErdosHajnalP6
