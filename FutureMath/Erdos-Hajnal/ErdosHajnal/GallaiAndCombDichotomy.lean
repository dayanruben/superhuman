/-
Copyright 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosHajnal.BasicLemmas
import ErdosHajnal.CombModules
import ErdosHajnal.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Gallai Tree Decomposition and Comb Dichotomy (Lemma 4.3 and Proposition 4.4 of `FMBV4-016_readable.tex`)

This file formalizes:
1. **Cauchy Series Extraction Lemma**: Extracting a heavy term $a_k \ge \frac{S}{2 k^2}$ from a
   finite tail sum $\sum_{j=p+1}^q a_j \ge S > 0$.
2. **Modular Overlap and Prime Quotient Property (Gallai's Theorem for Prime Nodes)**:
   Disjointness and partition of maximal proper modules when $G[M_s]$ and $Gᶜ[M_s]$ are connected,
   and uniqueness of the maximal proper module containing any proper module $X \subsetneq M_s$.
3. **Lemma 4.3 (`lem:gallai-core`)**: Two-Tier Potential-Preserving Gallai Tree Decomposition
   inside Comb Blocks.
4. **Proposition 4.4 (`prop:comb-dichotomy`)**: Parameter-Free Upside-Down Comb Dichotomy with
   Calibrated Widths ($|S|/k^{120}$).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Classical Finset SimpleGraph Real

namespace ErdosHajnalP6

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Part 1: Cauchy Series Extraction Lemma and Finset Sorting Helpers -/

/-- Telescoping upper bound $\sum_{k=1}^{n+1} \frac{1}{k^2} \le 2 - \frac{1}{n+1}$. -/
theorem sum_inv_sq_Icc_le (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 (n + 1), (1 : ℝ) / (k : ℝ) ^ 2 ≤ 2 - 1 / ((n + 1 : ℕ) : ℝ) := by
  induction n with
  | zero =>
    simp
    norm_num
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1 + 1)]
    have hm1 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    have hm2 : (0 : ℝ) < ((m + 1 + 1 : ℕ) : ℝ) := by positivity
    have hcast : ((m + 1 + 1 : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
    have hstep : 1 / ((m + 1 + 1 : ℕ) : ℝ) ^ 2 ≤
        1 / ((m + 1 : ℕ) : ℝ) - 1 / ((m + 1 + 1 : ℕ) : ℝ) := by
      rw [div_sub_div _ _ (ne_of_gt hm1) (ne_of_gt hm2),
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hcast]
    linarith

/-- For any $p, q \in \mathbb{N}$, $\sum_{k=p+1}^q \frac{1}{k^2} < 2$. -/
theorem sum_inv_sq_Icc_lt_two (p q : ℕ) :
    ∑ k ∈ Finset.Icc (p + 1) q, (1 : ℝ) / (k : ℝ) ^ 2 < 2 := by
  have hsub : Finset.Icc (p + 1) q ⊆ Finset.Icc 1 q :=
    Finset.Icc_subset_Icc (by omega) le_rfl
  have hle : ∑ k ∈ Finset.Icc (p + 1) q, (1 : ℝ) / (k : ℝ) ^ 2 ≤
      ∑ k ∈ Finset.Icc 1 q, (1 : ℝ) / (k : ℝ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  rcases q with _ | n
  · simp at hle ⊢
  · have h1 := sum_inv_sq_Icc_le n
    have hpos : (0 : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) := by positivity
    linarith

/--
**Cauchy Series Extraction Lemma**:
For any sequence $a : \mathbb{N} \to \mathbb{R}$ and any $p, q \in \mathbb{N}$, if
$\sum_{j=p+1}^q a_j \ge S > 0$, then there exists $k \in [p+1, q]$ such that
$a_k \ge \frac{S}{2 k^2}$.
-/
theorem cauchy_series_extraction (p q : ℕ) (a : ℕ → ℝ) (S : ℝ)
    (hS : 0 < S) (hsum : S ≤ ∑ j ∈ Finset.Icc (p + 1) q, a j) :
    ∃ k ∈ Finset.Icc (p + 1) q, S / (2 * (k : ℝ) ^ 2) ≤ a k := by
  by_contra! hlt
  have hne : (Finset.Icc (p + 1) q).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty.mp hemp, Finset.sum_empty] at hsum
    linarith
  have hsum_lt : ∑ j ∈ Finset.Icc (p + 1) q, a j <
      ∑ j ∈ Finset.Icc (p + 1) q, (S / 2) * ((1 : ℝ) / (j : ℝ) ^ 2) := by
    refine Finset.sum_lt_sum_of_nonempty hne (fun j hj => ?_)
    have hj_lt := hlt j hj
    have h_eq : S / (2 * (j : ℝ) ^ 2) = (S / 2) * ((1 : ℝ) / (j : ℝ) ^ 2) := by ring
    linarith
  rw [← Finset.mul_sum] at hsum_lt
  have h_inv := sum_inv_sq_Icc_lt_two p q
  have h_prod : (S / 2) * ∑ j ∈ Finset.Icc (p + 1) q, (1 : ℝ) / (j : ℝ) ^ 2 < (S / 2) * 2 :=
    mul_lt_mul_of_pos_left h_inv (by linarith)
  linarith

/-- Splitting a sum over `Icc 1 q` at `p ≤ q`. -/
lemma sum_Icc_split (p q : ℕ) (hpq : p ≤ q) (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 q, f k =
      ∑ k ∈ Finset.Icc 1 p, f k + ∑ k ∈ Finset.Icc (p + 1) q, f k := by
  have hunion : Finset.Icc 1 p ∪ Finset.Icc (p + 1) q = Finset.Icc 1 q := by
    ext k
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 p) (Finset.Icc (p + 1) q) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [Finset.mem_Icc] at hk1 hk2
    omega
  rw [← hunion, Finset.sum_union hdisj]

/-- Re-indexing a sum over `Fin q` to `Finset.Icc 1 q`. -/
lemma sum_fin_eq_sum_Icc (q : ℕ) (g : Fin q → ℝ) :
    ∑ j : Fin q, g j =
      ∑ k ∈ Finset.Icc 1 q, (if h : 1 ≤ k ∧ k ≤ q then g ⟨k - 1, by omega⟩ else 0) := by
  refine Finset.sum_bij (fun (j : Fin q) _ => j.1 + 1) ?_ ?_ ?_ ?_
  · intro j _
    simp only [Finset.mem_Icc]
    omega
  · intro j₁ _ j₂ _ h
    dsimp only at h
    ext
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    refine ⟨⟨k - 1, by omega⟩, Finset.mem_univ _, ?_⟩
    dsimp only
    omega
  · intro j _
    have hj : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ q := ⟨by omega, by omega⟩
    rw [dif_pos hj]
    congr 1

/-- Auxiliary induction sorting a finite family of finsets in non-increasing order of cardinality. -/
lemma exists_sorted_equiv_of_finset_aux :
    ∀ (n : ℕ) (F : Finset (Finset V)), F.card = n →
      ∃ (P : Fin n → Finset V),
        Function.Injective P ∧
        (∀ j : Fin n, P j ∈ F) ∧
        (∀ A ∈ F, ∃ j : Fin n, P j = A) ∧
        (∀ i j : Fin n, i ≤ j → (P j).card ≤ (P i).card) := by
  intro n
  induction n with
  | zero =>
    intro F hF
    have hF_emp : F = ∅ := Finset.card_eq_zero.mp hF
    refine ⟨Fin.elim0, ?_, ?_, ?_, ?_⟩
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
    · intro A hA; rw [hF_emp] at hA; exact False.elim (Finset.notMem_empty A hA)
    · intro i; exact Fin.elim0 i
  | succ m ih =>
    intro F hF
    have hF_ne : F.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨A₀, hA₀_mem, hA₀_max⟩ := Finset.exists_max_image F Finset.card hF_ne
    let F' := F.erase A₀
    have hF'_card : F'.card = m := by
      rw [Finset.card_erase_of_mem hA₀_mem, hF]
      omega
    obtain ⟨P', hP'_inj, hP'_mem, hP'_surj, hP'_mono⟩ := ih F' hF'_card
    refine ⟨Fin.cons A₀ P', ?_, ?_, ?_, ?_⟩
    · intro i j hij
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩ <;>
        rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · rfl
      · simp only [Fin.cons_zero, Fin.cons_succ] at hij
        have hmem := hP'_mem j'
        rw [← hij] at hmem
        exact False.elim ((Finset.mem_erase.mp hmem).1 rfl)
      · simp only [Fin.cons_zero, Fin.cons_succ] at hij
        have hmem := hP'_mem i'
        rw [hij] at hmem
        exact False.elim ((Finset.mem_erase.mp hmem).1 rfl)
      · simp only [Fin.cons_succ] at hij
        rw [hP'_inj hij]
    · intro j
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · simp [hA₀_mem]
      · simp only [Fin.cons_succ]
        exact Finset.erase_subset A₀ F (hP'_mem j')
    · intro A hA
      by_cases hAA₀ : A = A₀
      · exact ⟨0, by simp [hAA₀]⟩
      · obtain ⟨j', hj'⟩ := hP'_surj A (Finset.mem_erase.mpr ⟨hAA₀, hA⟩)
        exact ⟨j'.succ, by simp [hj']⟩
    · intro i j hij
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩ <;>
        rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · exact le_rfl
      · simp only [Fin.cons_zero, Fin.cons_succ]
        exact hA₀_max (P' j') (Finset.erase_subset A₀ F (hP'_mem j'))
      · exact False.elim (Nat.not_succ_le_zero i'.1 hij)
      · simp only [Fin.cons_succ]
        exact hP'_mono i' j' (Fin.succ_le_succ_iff.mp hij)

/-- Every finite family `F : Finset (Finset V)` can be indexed as `P : Fin t → Finset V`
in non-increasing order of cardinality. -/
lemma exists_sorted_equiv_of_finset (F : Finset (Finset V)) :
    ∃ (t : ℕ) (P : Fin t → Finset V),
      t = F.card ∧
      Function.Injective P ∧
      Finset.univ.image P = F ∧
      (∀ j : Fin t, P j ∈ F) ∧
      (∀ A ∈ F, ∃ j : Fin t, P j = A) ∧
      (∀ i j : Fin t, i ≤ j → (P j).card ≤ (P i).card) := by
  obtain ⟨P, hinj, hmem, hsurj, hmono⟩ := exists_sorted_equiv_of_finset_aux F.card F rfl
  refine ⟨F.card, P, rfl, hinj, ?_, hmem, hsurj, hmono⟩
  ext A
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨fun ⟨j, hj⟩ => hj ▸ hmem j, hsurj A⟩

/-! ### Part 2: Modular Overlap & Prime Quotient Property (Gallai's Theorem for Prime Nodes) -/

/-- Family of all proper modules of $G[M]$. -/
noncomputable def properModulesFinset (G : SimpleGraph V) (M : Finset V) : Finset (Finset V) :=
  M.powerset.filter (fun N => IsProperModuleIn G M N)

/-- $m_{\max}(G[M])$, the maximum cardinality of a proper module of $G[M]$ (0 if none exist). -/
noncomputable def mMax (G : SimpleGraph V) (M : Finset V) : ℕ :=
  (properModulesFinset G M).sup Finset.card

lemma mem_properModulesFinset_iff {G : SimpleGraph V} {M N : Finset V} :
    N ∈ properModulesFinset G M ↔ IsProperModuleIn G M N := by
  unfold properModulesFinset
  simp only [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun h => h.2, fun h => ⟨h.2.1.subset, h⟩⟩

lemma card_le_mMax_of_isProperModuleIn {G : SimpleGraph V} {M N : Finset V}
    (h : IsProperModuleIn G M N) : N.card ≤ mMax G M := by
  unfold mMax
  exact Finset.le_sup (f := Finset.card) (mem_properModulesFinset_iff.mpr h)

lemma isProperModuleIn_singleton {G : SimpleGraph V} {M : Finset V} {x : V}
    (hx : x ∈ M) (hcard : 2 ≤ M.card) : IsProperModuleIn G M {x} := by
  refine ⟨Finset.singleton_nonempty x, ?_, ?_⟩
  · refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.singleton_subset_iff.mpr hx, ?_⟩
    intro h_eq
    have h_c : ({x} : Finset V).card = M.card := congr_arg Finset.card h_eq
    rw [Finset.card_singleton] at h_c
    omega
  · refine ⟨Finset.singleton_subset_iff.mpr hx, fun z _ _ => ?_⟩
    unfold IsVertexPureTo
    by_cases h : G.Adj z x
    · left; intro u hu; rw [Finset.mem_singleton.mp hu]; exact h
    · right; intro u hu; rw [Finset.mem_singleton.mp hu]; exact h

lemma exists_isProperModuleIn_card_eq_mMax {G : SimpleGraph V} {M : Finset V}
    (hcard : 2 ≤ M.card) :
    ∃ N, IsProperModuleIn G M N ∧ N.card = mMax G M := by
  have hne : M.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hx⟩ := hne
  have hx_mem : {x} ∈ properModulesFinset G M :=
    mem_properModulesFinset_iff.mpr (isProperModuleIn_singleton hx hcard)
  obtain ⟨N, hN_mem, hN_sup⟩ :=
    Finset.exists_mem_eq_sup (properModulesFinset G M) ⟨{x}, hx_mem⟩ Finset.card
  exact ⟨N, mem_properModulesFinset_iff.mp hN_mem, hN_sup.symm⟩

lemma isVertexPureTo_compl_iff {G : SimpleGraph V} {z : V} {A : Finset V} (hz : z ∉ A) :
    IsVertexPureTo Gᶜ z A ↔ IsVertexPureTo G z A := by
  unfold IsVertexPureTo
  constructor
  · rintro (h | h)
    · right; intro u hu; exact (h u hu).2
    · left; intro u hu
      have hne : z ≠ u := fun hzu => hz (hzu ▸ hu)
      exact Decidable.byContradiction (fun hn => h u hu ⟨hne, hn⟩)
  · rintro (h | h)
    · right; intro u hu; exact fun hc => hc.2 (h u hu)
    · left; intro u hu
      have hne : z ≠ u := fun hzu => hz (hzu ▸ hu)
      exact ⟨hne, h u hu⟩

lemma isProperModuleIn_compl_iff {G : SimpleGraph V} {M A : Finset V} :
    IsProperModuleIn Gᶜ M A ↔ IsProperModuleIn G M A := by
  unfold IsProperModuleIn IsModuleIn
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => ?_
  refine forall₂_congr fun z _ => forall_congr' fun hzA => isVertexPureTo_compl_iff hzA

/-- If $A, B$ are modules of $G[M_s]$ with $A \cap B \neq \emptyset$, then $A \cup B$ is a module of $G[M_s]$. -/
theorem isModuleIn_union_of_inter_nonempty {G : SimpleGraph V} {M_s A B : Finset V}
    (hA : IsModuleIn G M_s A) (hB : IsModuleIn G M_s B) (hAB : (A ∩ B).Nonempty) :
    IsModuleIn G M_s (A ∪ B) := by
  refine ⟨Finset.union_subset hA.1 hB.1, fun z hzM hzAB => ?_⟩
  have hzA : z ∉ A := fun h => hzAB (Finset.mem_union_left B h)
  have hzB : z ∉ B := fun h => hzAB (Finset.mem_union_right A h)
  obtain ⟨w₀, hw₀⟩ := hAB
  obtain ⟨hw₀A, hw₀B⟩ := Finset.mem_inter.mp hw₀
  rcases hA.2 z hzM hzA with hA_comp | hA_anti <;> rcases hB.2 z hzM hzB with hB_comp | hB_anti
  · left
    intro u hu
    rcases Finset.mem_union.mp hu with huA | huB
    · exact hA_comp u huA
    · exact hB_comp u huB
  · exact False.elim (hB_anti w₀ hw₀B (hA_comp w₀ hw₀A))
  · exact False.elim (hA_anti w₀ hw₀A (hB_comp w₀ hw₀B))
  · right
    intro u hu
    rcases Finset.mem_union.mp hu with huA | huB
    · exact hA_anti u huA
    · exact hB_anti u huB

/-- Along any walk in $H[M]$, if there are no edges between $A$ and $M \setminus A$,
every vertex visited by a walk starting in $A$ remains in $A$. -/
lemma walk_mem_of_isAnticompletePair {H : SimpleGraph V} {M A : Finset V}
    (hA : IsAnticompletePair H A (M \ A)) {u v : (M : Set V)}
    (p : (H.induce (M : Set V)).Walk u v) (hu : u.1 ∈ A) : v.1 ∈ A := by
  induction p with
  | nil => exact hu
  | @cons u w v hadj p ih =>
    apply ih
    by_contra hw
    exact hA u.1 hu w.1 (Finset.mem_sdiff.mpr ⟨w.2, hw⟩) hadj

/-- If $A \subseteq M$ has $A \neq \emptyset$, $M \setminus A \neq \emptyset$, and no edges
between $A$ and $M \setminus A$ in $H$, then $H[M]$ is not connected. -/
lemma not_connected_of_isAnticompletePair_sdiff {H : SimpleGraph V} {M A : Finset V}
    (hAM : A ⊆ M) (hA_ne : A.Nonempty) (hMA_ne : (M \ A).Nonempty)
    (h_anti : IsAnticompletePair H A (M \ A)) :
    ¬(H.induce (M : Set V)).Connected := by
  intro hconn
  obtain ⟨a, ha⟩ := hA_ne
  obtain ⟨b, hb⟩ := hMA_ne
  obtain ⟨hbM, hbA⟩ := Finset.mem_sdiff.mp hb
  obtain ⟨p⟩ := hconn ⟨a, hAM ha⟩ ⟨b, hbM⟩
  exact hbA (walk_mem_of_isAnticompletePair h_anti p ha)

lemma sdiff_nonempty_of_ssubset {A B : Finset V} (h : A ⊂ B) : (B \ A).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty, Ne, Finset.sdiff_eq_empty_iff_subset]
  exact h.not_subset

/-- If both $G[M_s]$ and $Gᶜ[M_s]$ are connected, then the union of any two proper modules
$A, B \subsetneq M_s$ cannot equal $M_s$. -/
theorem union_ne_of_isProperModuleIn_of_connected {G : SimpleGraph V} {M_s A B : Finset V}
    (hconn : (G.induce (M_s : Set V)).Connected)
    (haconn : (Gᶜ.induce (M_s : Set V)).Connected)
    (hA : IsProperModuleIn G M_s A) (hB : IsProperModuleIn G M_s B) :
    A ∪ B ≠ M_s := by
  intro hunion
  have hAB_sub : M_s \ B ⊆ A := by
    intro x hx
    obtain ⟨hxM, hxB⟩ := Finset.mem_sdiff.mp hx
    rw [← hunion] at hxM
    rcases Finset.mem_union.mp hxM with hxA | hxB'
    · exact hxA
    · exact False.elim (hxB hxB')
  have hBA_sub : M_s \ A ⊆ B := by
    intro x hx
    obtain ⟨hxM, hxA⟩ := Finset.mem_sdiff.mp hx
    rw [← hunion] at hxM
    rcases Finset.mem_union.mp hxM with hxA' | hxB
    · exact False.elim (hxA hxA')
    · exact hxB
  obtain ⟨a₀, ha₀⟩ := sdiff_nonempty_of_ssubset hB.2.1
  obtain ⟨b₀, hb₀⟩ := sdiff_nonempty_of_ssubset hA.2.1
  have ha₀A : a₀ ∈ A := hAB_sub ha₀
  have hb₀B : b₀ ∈ B := hBA_sub hb₀
  obtain ⟨ha₀M, ha₀_notB⟩ := Finset.mem_sdiff.mp ha₀
  obtain ⟨hb₀M, hb₀_notA⟩ := Finset.mem_sdiff.mp hb₀
  have hB_sdiff : M_s \ (M_s \ B) = B := Finset.sdiff_sdiff_eq_self hB.2.2.1
  by_cases hadj : G.Adj a₀ b₀
  · have hb₀_comp : ∀ a ∈ A, G.Adj b₀ a := by
      rcases hA.2.2.2 b₀ hb₀M hb₀_notA with hcomp | hanti
      · exact hcomp
      · exact False.elim (hanti a₀ ha₀A hadj.symm)
    have h_anti_compl : IsAnticompletePair Gᶜ (M_s \ B) (M_s \ (M_s \ B)) := by
      rw [hB_sdiff]
      intro x hx y hy hxy_compl
      obtain ⟨hxM, hx_notB⟩ := Finset.mem_sdiff.mp hx
      have hxA : x ∈ A := hAB_sub hx
      have hbx : G.Adj x b₀ := (hb₀_comp x hxA).symm
      rcases hB.2.2.2 x hxM hx_notB with hcomp | hanti
      · exact hxy_compl.2 (hcomp y hy)
      · exact hanti b₀ hb₀B hbx
    exact not_connected_of_isAnticompletePair_sdiff Finset.sdiff_subset ⟨a₀, ha₀⟩
      (by rw [hB_sdiff]; exact hB.1) h_anti_compl haconn
  · have hb₀_anti : ∀ a ∈ A, ¬G.Adj b₀ a := by
      rcases hA.2.2.2 b₀ hb₀M hb₀_notA with hcomp | hanti
      · exact False.elim (hadj (hcomp a₀ ha₀A).symm)
      · exact hanti
    have h_anti : IsAnticompletePair G (M_s \ B) (M_s \ (M_s \ B)) := by
      rw [hB_sdiff]
      intro x hx y hy
      obtain ⟨hxM, hx_notB⟩ := Finset.mem_sdiff.mp hx
      have hxA : x ∈ A := hAB_sub hx
      have hbx : ¬G.Adj x b₀ := fun h => hb₀_anti x hxA h.symm
      rcases hB.2.2.2 x hxM hx_notB with hcomp | hanti
      · exact False.elim (hbx (hcomp b₀ hb₀B))
      · exact hanti y hy
    exact not_connected_of_isAnticompletePair_sdiff Finset.sdiff_subset ⟨a₀, ha₀⟩
      (by rw [hB_sdiff]; exact hB.1) h_anti hconn

/-- If $G[M_s]$ and $Gᶜ[M_s]$ are connected and $A, B \subsetneq M_s$ are overlapping proper modules,
then $A \cup B$ is a proper module of $G[M_s]$. -/
theorem isProperModuleIn_union_of_inter_nonempty {G : SimpleGraph V} {M_s A B : Finset V}
    (hconn : (G.induce (M_s : Set V)).Connected)
    (haconn : (Gᶜ.induce (M_s : Set V)).Connected)
    (hA : IsProperModuleIn G M_s A) (hB : IsProperModuleIn G M_s B)
    (hAB : (A ∩ B).Nonempty) :
    IsProperModuleIn G M_s (A ∪ B) := by
  have hmod := isModuleIn_union_of_inter_nonempty hA.2.2 hB.2.2 hAB
  have hne := union_ne_of_isProperModuleIn_of_connected hconn haconn hA hB
  exact ⟨hA.1.mono Finset.subset_union_left, Finset.ssubset_iff_subset_ne.mpr ⟨hmod.1, hne⟩, hmod⟩

/-- A proper module $A$ of $G[M_s]$ is maximal if no strictly larger proper module contains it. -/
def IsMaximalProperModuleIn (G : SimpleGraph V) (M_s A : Finset V) : Prop :=
  IsProperModuleIn G M_s A ∧ ∀ B, IsProperModuleIn G M_s B → A ⊆ B → A = B

/-- Any proper module $X$ overlapping a maximal proper module $B$ of a prime node $M_s$
is contained in $B$. -/
theorem subset_of_isProperModuleIn_of_isMaximalProperModuleIn_of_inter_nonempty
    {G : SimpleGraph V} {M_s X B : Finset V}
    (hconn : (G.induce (M_s : Set V)).Connected)
    (haconn : (Gᶜ.induce (M_s : Set V)).Connected)
    (hX : IsProperModuleIn G M_s X) (hB : IsMaximalProperModuleIn G M_s B)
    (hXB : (X ∩ B).Nonempty) :
    X ⊆ B := by
  have hunion := isProperModuleIn_union_of_inter_nonempty hconn haconn hX hB.1 hXB
  have hB_eq := hB.2 (X ∪ B) hunion Finset.subset_union_right
  rw [hB_eq]
  exact Finset.subset_union_left

/-- Distinct maximal proper modules of a prime node $M_s$ are disjoint. -/
theorem eq_of_isMaximalProperModuleIn_of_inter_nonempty
    {G : SimpleGraph V} {M_s A B : Finset V}
    (hconn : (G.induce (M_s : Set V)).Connected)
    (haconn : (Gᶜ.induce (M_s : Set V)).Connected)
    (hA : IsMaximalProperModuleIn G M_s A) (hB : IsMaximalProperModuleIn G M_s B)
    (hAB : (A ∩ B).Nonempty) :
    A = B := by
  have hAB_sub := subset_of_isProperModuleIn_of_isMaximalProperModuleIn_of_inter_nonempty
    hconn haconn hA.1 hB hAB
  have hBA_sub := subset_of_isProperModuleIn_of_isMaximalProperModuleIn_of_inter_nonempty
    hconn haconn hB.1 hA (by rwa [Finset.inter_comm])
  exact Finset.Subset.antisymm hAB_sub hBA_sub

/-- Every proper module $X$ of $G[M_s]$ is contained in a maximal proper module of $G[M_s]$. -/
theorem exists_isMaximalProperModuleIn_superset {G : SimpleGraph V} {M_s X : Finset V}
    (hX : IsProperModuleIn G M_s X) :
    ∃ A, IsMaximalProperModuleIn G M_s A ∧ X ⊆ A := by
  let F := (properModulesFinset G M_s).filter (fun A => X ⊆ A)
  have hX_mem : X ∈ F := Finset.mem_filter.mpr ⟨mem_properModulesFinset_iff.mpr hX, Finset.Subset.rfl⟩
  obtain ⟨A, hA_mem, hA_max⟩ := Finset.exists_max_image F Finset.card ⟨X, hX_mem⟩
  obtain ⟨hA_prop, hXA⟩ := Finset.mem_filter.mp hA_mem
  have hA_mod := mem_properModulesFinset_iff.mp hA_prop
  refine ⟨A, ⟨hA_mod, fun B hB hAB => ?_⟩, hXA⟩
  have hB_mem : B ∈ F := Finset.mem_filter.mpr ⟨mem_properModulesFinset_iff.mpr hB, hXA.trans hAB⟩
  exact Finset.eq_of_subset_of_card_le hAB (hA_max B hB_mem)

/-- Any two disjoint modules of $G[M_s]$ form a pure pair in $G$. -/
theorem isPurePair_of_isModuleIn_disjoint {G : SimpleGraph V} {M_s A B : Finset V}
    (hA : IsModuleIn G M_s A) (hB : IsModuleIn G M_s B) (hdisj : Disjoint A B) :
    IsPurePair G A B := by
  by_cases h_ex : ∃ a ∈ A, ∃ b ∈ B, G.Adj a b
  · left
    obtain ⟨a₀, ha₀A, b₀, hb₀B, hadj⟩ := h_ex
    have ha₀_notB : a₀ ∉ B := Finset.disjoint_left.mp hdisj ha₀A
    have ha₀_comp : ∀ b ∈ B, G.Adj a₀ b := by
      rcases hB.2 a₀ (hA.1 ha₀A) ha₀_notB with hcomp | hanti
      · exact hcomp
      · exact False.elim (hanti b₀ hb₀B hadj)
    intro a ha b hb
    have hb_notA : b ∉ A := Finset.disjoint_right.mp hdisj hb
    rcases hA.2 b (hB.1 hb) hb_notA with hcomp | hanti
    · exact (hcomp a ha).symm
    · exact False.elim (hanti a₀ ha₀A (ha₀_comp b hb).symm)
  · right
    push_neg at h_ex
    exact h_ex

/-- Reachable component of $x_0 \in M$ inside $H[M]$. -/
noncomputable def reachableComponentIn (H : SimpleGraph V) (M : Finset V) (x₀ : (M : Set V)) :
    Finset V :=
  M.filter (fun y => ∃ hy : y ∈ M, (H.induce (M : Set V)).Reachable x₀ ⟨y, hy⟩)

lemma reachableComponentIn_subset (H : SimpleGraph V) (M : Finset V) (x₀ : (M : Set V)) :
    reachableComponentIn H M x₀ ⊆ M :=
  Finset.filter_subset _ _

lemma mem_reachableComponentIn_self (H : SimpleGraph V) (M : Finset V) (x₀ : (M : Set V)) :
    x₀.1 ∈ reachableComponentIn H M x₀ := by
  unfold reachableComponentIn
  simp only [Finset.mem_filter]
  exact ⟨x₀.2, x₀.2, SimpleGraph.Reachable.refl x₀⟩

lemma isAnticompletePair_reachableComponentIn_sdiff (H : SimpleGraph V) (M : Finset V)
    (x₀ : (M : Set V)) :
    IsAnticompletePair H (reachableComponentIn H M x₀) (M \ reachableComponentIn H M x₀) := by
  intro u hu v hv hadj
  unfold reachableComponentIn at hu hv
  obtain ⟨huM, _, hru⟩ := Finset.mem_filter.mp hu
  obtain ⟨hvM, hv_not⟩ := Finset.mem_sdiff.mp hv
  simp only [Finset.mem_filter, not_and, not_exists] at hv_not
  have hadj_ind : (H.induce (M : Set V)).Adj ⟨u, huM⟩ ⟨v, hvM⟩ := hadj
  exact hv_not hvM hvM (hru.trans (SimpleGraph.Adj.reachable hadj_ind))

lemma reachable_induce_of_isAnticompletePair_sdiff {H : SimpleGraph V} {M C : Finset V}
    (h_anti : IsAnticompletePair H C (M \ C))
    {u v : (M : Set V)} (p : (H.induce (M : Set V)).Walk u v)
    (hu : u.1 ∈ C) (hv : v.1 ∈ C) :
    (H.induce (C : Set V)).Reachable ⟨u.1, hu⟩ ⟨v.1, hv⟩ := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons u w v hadj p ih =>
    have hw : w.1 ∈ C := by
      by_contra hw_not
      exact h_anti u.1 hu w.1 (Finset.mem_sdiff.mpr ⟨w.2, hw_not⟩) hadj
    have hadj' : (H.induce (C : Set V)).Adj ⟨u.1, hu⟩ ⟨w.1, hw⟩ := hadj
    exact (SimpleGraph.Adj.reachable hadj').trans (ih hw hv)

lemma connected_reachableComponentIn (H : SimpleGraph V) (M : Finset V) (x₀ : (M : Set V)) :
    (H.induce (reachableComponentIn H M x₀ : Set V)).Connected := by
  let C := reachableComponentIn H M x₀
  have hx₀C : x₀.1 ∈ C := mem_reachableComponentIn_self H M x₀
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨x₀.1, hx₀C⟩, fun y => ?_⟩
  have hyC : y.1 ∈ C := y.2
  unfold C reachableComponentIn at hyC
  obtain ⟨_, hyM, ⟨p⟩⟩ := Finset.mem_filter.mp hyC
  exact reachable_induce_of_isAnticompletePair_sdiff
    (isAnticompletePair_reachableComponentIn_sdiff H M x₀) p hx₀C y.2

/-- If $m_{\max}(G[M_s]) < \frac{1}{2}|M_s|$ and $|M_s| \ge 2$, then both $G[M_s]$ and
$Gᶜ[M_s]$ are connected. -/
theorem connected_and_anticonnected_of_two_mul_mMax_lt {G : SimpleGraph V} {M_s : Finset V}
    (hcard : 2 ≤ M_s.card) (hmMax : 2 * mMax G M_s < M_s.card) :
    (G.induce (M_s : Set V)).Connected ∧ (Gᶜ.induce (M_s : Set V)).Connected := by
  have haux : ∀ (H : SimpleGraph V),
      (∀ A, IsProperModuleIn H M_s A → A.card ≤ mMax G M_s) →
      (H.induce (M_s : Set V)).Connected := by
    intro H hH_le
    by_contra hnot_conn
    have hne : M_s.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x₀, hx₀⟩ := hne
    let C := reachableComponentIn H M_s ⟨x₀, hx₀⟩
    have hCM : C ⊆ M_s := reachableComponentIn_subset H M_s ⟨x₀, hx₀⟩
    have hx₀C : x₀ ∈ C := mem_reachableComponentIn_self H M_s ⟨x₀, hx₀⟩
    have h_anti : IsAnticompletePair H C (M_s \ C) :=
      isAnticompletePair_reachableComponentIn_sdiff H M_s ⟨x₀, hx₀⟩
    have hMC_ne : (M_s \ C).Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hemp
      apply hnot_conn
      rw [SimpleGraph.connected_iff_exists_forall_reachable]
      refine ⟨⟨x₀, hx₀⟩, fun y => ?_⟩
      have hyC : y.1 ∈ C := hemp y.2
      unfold C reachableComponentIn at hyC
      obtain ⟨_, _, hr⟩ := Finset.mem_filter.mp hyC
      exact hr
    have hC_ne_M : C ≠ M_s := by
      intro h_eq
      rw [h_eq, Finset.sdiff_self] at hMC_ne
      exact Finset.not_nonempty_empty hMC_ne
    have hC_prop : IsProperModuleIn H M_s C := by
      refine ⟨⟨x₀, hx₀C⟩, Finset.ssubset_iff_subset_ne.mpr ⟨hCM, hC_ne_M⟩, hCM, ?_⟩
      intro z hzM hzC
      right
      intro u hu hzu
      exact h_anti u hu z (Finset.mem_sdiff.mpr ⟨hzM, hzC⟩) hzu.symm
    have hMC_ne_M : M_s \ C ≠ M_s := by
      intro h_eq
      have hx₀_not : x₀ ∉ M_s \ C := fun h => (Finset.mem_sdiff.mp h).2 hx₀C
      rw [h_eq] at hx₀_not
      exact hx₀_not hx₀
    have hMC_prop : IsProperModuleIn H M_s (M_s \ C) := by
      refine ⟨hMC_ne, Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, hMC_ne_M⟩,
        Finset.sdiff_subset, ?_⟩
      intro z hzM hzMC
      have hzC : z ∈ C := by
        by_contra hnot
        exact hzMC (Finset.mem_sdiff.mpr ⟨hzM, hnot⟩)
      right
      intro u hu
      exact h_anti z hzC u hu
    have h1 := hH_le C hC_prop
    have h2 := hH_le (M_s \ C) hMC_prop
    have hsum : (M_s \ C).card + C.card = M_s.card := Finset.card_sdiff_add_card_eq_card hCM
    omega
  refine ⟨haux G (fun _ h => card_le_mMax_of_isProperModuleIn h),
    haux Gᶜ (fun _ h => card_le_mMax_of_isProperModuleIn (isProperModuleIn_compl_iff.mp h))⟩

/-- Gallai's Theorem for Prime Nodes: if $G[M_s]$ and $Gᶜ[M_s]$ are connected and $|M_s| \ge 2$,
then the maximal proper modules of $G[M_s]$ can be ordered $P_1, \dots, P_t$ ($|P_1| \ge \dots \ge |P_t|$)
so that they partition $M_s$ into a pure blockade and every proper module $X \subsetneq M_s$
is contained in some $P_j$. -/
theorem gallai_prime_partition {G : SimpleGraph V} {M_s : Finset V}
    (hcard : 2 ≤ M_s.card)
    (hconn : (G.induce (M_s : Set V)).Connected)
    (haconn : (Gᶜ.induce (M_s : Set V)).Connected) :
    ∃ (t : ℕ) (P : Fin t → Finset V),
      (∀ j : Fin t, IsMaximalProperModuleIn G M_s (P j)) ∧
      (∀ i j : Fin t, i ≠ j → Disjoint (P i) (P j) ∧ IsPurePair G (P i) (P j)) ∧
      Finset.univ.biUnion P = M_s ∧
      ∑ j : Fin t, (P j).card = M_s.card ∧
      (∀ i j : Fin t, i ≤ j → (P j).card ≤ (P i).card) ∧
      (∀ X, IsProperModuleIn G M_s X → ∃ j : Fin t, X ⊆ P j) := by
  let F := (properModulesFinset G M_s).filter (fun A => IsMaximalProperModuleIn G M_s A)
  have hF_max : ∀ A ∈ F, IsMaximalProperModuleIn G M_s A :=
    fun _ hA => (Finset.mem_filter.mp hA).2
  have hF_disj : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → Disjoint A B := by
    intro A hA B hB hne
    rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.not_nonempty_iff_eq_empty]
    intro h_inter
    exact hne (eq_of_isMaximalProperModuleIn_of_inter_nonempty hconn haconn
      (hF_max A hA) (hF_max B hB) h_inter)
  obtain ⟨t, P, _, hP_inj, hP_img, hP_mem, hP_surj, hP_mono⟩ := exists_sorted_equiv_of_finset F
  have hP_max : ∀ j : Fin t, IsMaximalProperModuleIn G M_s (P j) :=
    fun j => hF_max (P j) (hP_mem j)
  have hP_disj : ∀ i j : Fin t, i ≠ j → Disjoint (P i) (P j) :=
    fun i j hij => hF_disj (P i) (hP_mem i) (P j) (hP_mem j) (fun h => hij (hP_inj h))
  have hP_pure : ∀ i j : Fin t, i ≠ j → Disjoint (P i) (P j) ∧ IsPurePair G (P i) (P j) := by
    intro i j hij
    have hd := hP_disj i j hij
    exact ⟨hd, isPurePair_of_isModuleIn_disjoint (hP_max i).1.2.2 (hP_max j).1.2.2 hd⟩
  have hP_sup : ∀ X, IsProperModuleIn G M_s X → ∃ j : Fin t, X ⊆ P j := by
    intro X hX
    obtain ⟨A, hA_max, hXA⟩ := exists_isMaximalProperModuleIn_superset hX
    have hA_F : A ∈ F := Finset.mem_filter.mpr ⟨mem_properModulesFinset_iff.mpr hA_max.1, hA_max⟩
    obtain ⟨j, hj⟩ := hP_surj A hA_F
    exact ⟨j, hj ▸ hXA⟩
  have hP_biUnion : Finset.univ.biUnion P = M_s := by
    refine Finset.Subset.antisymm ?_ ?_
    · rw [Finset.biUnion_subset]
      intro j _
      exact (hP_max j).1.2.2.1
    · intro x hx
      obtain ⟨j, hj⟩ := hP_sup {x} (isProperModuleIn_singleton hx hcard)
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hj (Finset.mem_singleton_self x)⟩
  have hP_sum : ∑ j : Fin t, (P j).card = M_s.card := by
    rw [← hP_biUnion, Finset.card_biUnion]
    intro i _ j _ hij
    exact hP_disj i j hij
  exact ⟨t, P, hP_max, hP_pure, hP_biUnion, hP_sum, hP_mono, hP_sup⟩

/-! ### Anticonnected Components and Lemma 4.1 (`lem:anticonn-module`) -/

/-- Auxiliary induction decomposing any vertex subset $Z$ into anticonnected components. -/
lemma exists_anticonnected_components_finset_aux (G : SimpleGraph V) :
    ∀ (n : ℕ) (Z : Finset V), Z.card ≤ n →
      ∃ (C_fam : Finset (Finset V)),
        (∀ A ∈ C_fam, A ⊆ Z ∧ A.Nonempty ∧ IsAnticonnected G A) ∧
        (∀ A ∈ C_fam, ∀ B ∈ C_fam, A ≠ B → Disjoint A B ∧ IsCompletePair G A B) ∧
        C_fam.biUnion id = Z := by
  intro n
  induction n with
  | zero =>
    intro Z hZ
    have hZ_emp : Z = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hZ)
    refine ⟨∅, ?_, ?_, ?_⟩
    · intro A hA; exact False.elim (Finset.notMem_empty A hA)
    · intro A hA; exact False.elim (Finset.notMem_empty A hA)
    · simp [hZ_emp]
  | succ m ih =>
    intro Z hZ
    by_cases hZ_ne : Z.Nonempty
    · obtain ⟨x₀, hx₀⟩ := hZ_ne
      let C := reachableComponentIn Gᶜ Z ⟨x₀, hx₀⟩
      have hCZ : C ⊆ Z := reachableComponentIn_subset Gᶜ Z ⟨x₀, hx₀⟩
      have hx₀C : x₀ ∈ C := mem_reachableComponentIn_self Gᶜ Z ⟨x₀, hx₀⟩
      have hC_aconn : IsAnticonnected G C := connected_reachableComponentIn Gᶜ Z ⟨x₀, hx₀⟩
      have h_anti_compl := isAnticompletePair_reachableComponentIn_sdiff Gᶜ Z ⟨x₀, hx₀⟩
      have h_comp : IsCompletePair G C (Z \ C) := by
        intro u hu v hv
        have hne : u ≠ v := fun huv => (Finset.mem_sdiff.mp hv).2 (huv ▸ hu)
        exact Decidable.byContradiction (fun hn => h_anti_compl u hu v hv ⟨hne, hn⟩)
      have hZC_card : (Z \ C).card ≤ m := by
        have hsum := Finset.card_sdiff_add_card_eq_card hCZ
        have hC_pos : 1 ≤ C.card := Finset.card_pos.mpr ⟨x₀, hx₀C⟩
        omega
      obtain ⟨C_fam', h_prop', h_pair', h_union'⟩ := ih (Z \ C) hZC_card
      refine ⟨insert C C_fam', ?_, ?_, ?_⟩
      · intro A hA
        rcases Finset.mem_insert.mp hA with rfl | hA'
        · exact ⟨hCZ, ⟨x₀, hx₀C⟩, hC_aconn⟩
        · obtain ⟨hsub, hne, haconn⟩ := h_prop' A hA'
          exact ⟨hsub.trans Finset.sdiff_subset, hne, haconn⟩
      · intro A hA B hB hAB
        rcases Finset.mem_insert.mp hA with rfl | hA' <;>
          rcases Finset.mem_insert.mp hB with rfl | hB'
        · exact False.elim (hAB rfl)
        · have hB_sub : B ⊆ Z \ C := (h_prop' B hB').1
          refine ⟨Finset.disjoint_left.mpr (fun x hxC hxB => (Finset.mem_sdiff.mp (hB_sub hxB)).2 hxC),
            fun u hu v hv => h_comp u hu v (hB_sub hv)⟩
        · have hA_sub : A ⊆ Z \ C := (h_prop' A hA').1
          refine ⟨Finset.disjoint_right.mpr (fun x hxC hxA => (Finset.mem_sdiff.mp (hA_sub hxA)).2 hxC),
            fun u hu v hv => (h_comp v hv u (hA_sub hu)).symm⟩
        · exact h_pair' A hA' B hB' hAB
      · rw [Finset.biUnion_insert, id_eq, h_union', Finset.union_sdiff_of_subset hCZ]
    · have hZ_emp : Z = ∅ := Finset.not_nonempty_iff_eq_empty.mp hZ_ne
      refine ⟨∅, ?_, ?_, ?_⟩
      · intro A hA; exact False.elim (Finset.notMem_empty A hA)
      · intro A hA; exact False.elim (Finset.notMem_empty A hA)
      · simp [hZ_emp]

/-- Along a walk in $Gᶜ[C]$ from $y_1$ ($\neg G.\text{Adj } z y_1$) to $y_2$ ($G.\text{Adj } z y_2$),
there is an edge $x_2 x_3$ in $Gᶜ[C]$ with $\neg G.\text{Adj } z x_2$ and $G.\text{Adj } z x_3$. -/
lemma exists_mixed_edge_of_walk {G : SimpleGraph V} {C : Finset V} {z : V}
    {y₁ y₂ : (C : Set V)} (p : (Gᶜ.induce (C : Set V)).Walk y₁ y₂)
    (hy₁ : ¬G.Adj z y₁.1) (hy₂ : G.Adj z y₂.1) :
    ∃ x₂ ∈ C, ∃ x₃ ∈ C, Gᶜ.Adj x₂ x₃ ∧ ¬G.Adj z x₂ ∧ G.Adj z x₃ := by
  induction p with
  | nil => exact False.elim (hy₁ hy₂)
  | @cons a b c hadj p ih =>
    by_cases hb : G.Adj z b.1
    · exact ⟨a.1, a.2, b.1, b.2, hadj, hy₁, hb⟩
    · exact ih hb hy₂

/-- Explicit 6-vertex witness showing that $(x_0, x_1, x_2, x_3, x_4, x_5)$ induces $\overline{P_6}$
in $G$ when consecutive pairs are non-adjacent and non-consecutive pairs are adjacent. -/
lemma not_isInducedSubgraphFree_P6Compl {G : SimpleGraph V}
    (x₀ x₁ x₂ x₃ x₄ x₅ : V)
    (hne01 : x₀ ≠ x₁)
    (hn01 : ¬G.Adj x₀ x₁) (hn12 : ¬G.Adj x₁ x₂) (hn23 : ¬G.Adj x₂ x₃)
    (hn34 : ¬G.Adj x₃ x₄) (hn45 : ¬G.Adj x₄ x₅)
    (ha02 : G.Adj x₀ x₂) (ha03 : G.Adj x₀ x₃) (ha04 : G.Adj x₀ x₄) (ha05 : G.Adj x₀ x₅)
    (ha13 : G.Adj x₁ x₃) (ha14 : G.Adj x₁ x₄) (ha15 : G.Adj x₁ x₅)
    (ha24 : G.Adj x₂ x₄) (ha25 : G.Adj x₂ x₅)
    (ha35 : G.Adj x₃ x₅) :
    ¬IsInducedSubgraphFree G P6Compl := by
  intro hfree
  apply hfree
  let f : Fin 6 → V := ![x₀, x₁, x₂, x₃, x₄, x₅]
  have hne12 : x₁ ≠ x₂ := fun h => hn01 (h ▸ ha02)
  have hne23 : x₂ ≠ x₃ := fun h => hn12 (h ▸ ha13)
  have hne34 : x₃ ≠ x₄ := fun h => hn23 (h ▸ ha24)
  have hne45 : x₄ ≠ x₅ := fun h => hn34 (h ▸ ha35)
  have hne02 : x₀ ≠ x₂ := G.ne_of_adj ha02
  have hne03 : x₀ ≠ x₃ := G.ne_of_adj ha03
  have hne04 : x₀ ≠ x₄ := G.ne_of_adj ha04
  have hne05 : x₀ ≠ x₅ := G.ne_of_adj ha05
  have hne13 : x₁ ≠ x₃ := G.ne_of_adj ha13
  have hne14 : x₁ ≠ x₄ := G.ne_of_adj ha14
  have hne15 : x₁ ≠ x₅ := G.ne_of_adj ha15
  have hne24 : x₂ ≠ x₄ := G.ne_of_adj ha24
  have hne25 : x₂ ≠ x₅ := G.ne_of_adj ha25
  have hne35 : x₃ ≠ x₅ := G.ne_of_adj ha35
  have hf_inj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [f] at hij ⊢ <;>
      first | exact False.elim (hne01 hij) | exact False.elim (hne01 hij.symm)
            | exact False.elim (hne12 hij) | exact False.elim (hne12 hij.symm)
            | exact False.elim (hne23 hij) | exact False.elim (hne23 hij.symm)
            | exact False.elim (hne34 hij) | exact False.elim (hne34 hij.symm)
            | exact False.elim (hne45 hij) | exact False.elim (hne45 hij.symm)
            | exact False.elim (hne02 hij) | exact False.elim (hne02 hij.symm)
            | exact False.elim (hne03 hij) | exact False.elim (hne03 hij.symm)
            | exact False.elim (hne04 hij) | exact False.elim (hne04 hij.symm)
            | exact False.elim (hne05 hij) | exact False.elim (hne05 hij.symm)
            | exact False.elim (hne13 hij) | exact False.elim (hne13 hij.symm)
            | exact False.elim (hne14 hij) | exact False.elim (hne14 hij.symm)
            | exact False.elim (hne15 hij) | exact False.elim (hne15 hij.symm)
            | exact False.elim (hne24 hij) | exact False.elim (hne24 hij.symm)
            | exact False.elim (hne25 hij) | exact False.elim (hne25 hij.symm)
            | exact False.elim (hne35 hij) | exact False.elim (hne35 hij.symm)
  refine ⟨⟨f, hf_inj⟩, ?_⟩
  ext i j
  simp only [P6Compl, compl_adj, pathGraph_adj, comap_adj, Function.Embedding.coeFn_mk]
  fin_cases i <;> fin_cases j <;> simp [f] <;>
    first | exact ha02 | exact ha02.symm | exact ha03 | exact ha03.symm
          | exact ha04 | exact ha04.symm | exact ha05 | exact ha05.symm
          | exact ha13 | exact ha13.symm | exact ha14 | exact ha14.symm
          | exact ha15 | exact ha15.symm | exact ha24 | exact ha24.symm
          | exact ha25 | exact ha25.symm | exact ha35 | exact ha35.symm
          | exact hn01 | exact fun h => hn01 h.symm
          | exact hn12 | exact fun h => hn12 h.symm
          | exact hn23 | exact fun h => hn23 h.symm
          | exact hn34 | exact fun h => hn34 h.symm
          | exact hn45 | exact fun h => hn45 h.symm

/-- **Lemma 4.1 (`lem:anticonn-module`)**:
In a $\overline{P_6}$-free graph $G$ with an $(\ell, w)$-comb $(a, B)$ and external apex $v$,
for any $M \subseteq B_i$ and any external comb vertex $u \in B_r$ ($r \neq i$) not complete
to $M$, every anticonnected component $C$ of $N_G(u) \cap M$ is a proper module of $G[M]$,
and the anticonnected components of $N_G(u) \cap M$ can be ordered $C_1, \dots, C_q$
($|C_1| \ge \dots \ge |C_q|$) as a complete blockade partitioning $N_G(u) \cap M$. -/
theorem anticonnected_neighborhood_modules {G : SimpleGraph V} {S : Finset V} {ℓ : ℕ} {w : ℝ}
    {a : Fin ℓ → V} {B : Fin ℓ → Finset V} {v : V}
    (hG : IsInducedSubgraphFree G P6Compl)
    (hcomb : IsCombIn G S ℓ w a B)
    (hapex : IsCombExternalApex G S ℓ a B v)
    {i r : Fin ℓ} (hri : r ≠ i) {M : Finset V} (hMB : M ⊆ B i)
    {u : V} (huB : u ∈ B r) (hu_not_comp : ¬∀ z ∈ M, G.Adj u z) :
    let Z := neighborFinsetIn G u M
    ∃ (q : ℕ) (C : Fin q → Finset V),
      (∀ s : Fin q, C s ⊆ Z ∧ (C s).Nonempty ∧ IsAnticonnected G (C s) ∧ IsProperModuleIn G M (C s)) ∧
      (∀ s t : Fin q, s ≠ t → Disjoint (C s) (C t) ∧ IsCompletePair G (C s) (C t)) ∧
      Finset.univ.biUnion C = Z ∧
      ∑ s : Fin q, (C s).card = Z.card ∧
      (∀ s t : Fin q, s ≤ t → (C t).card ≤ (C s).card) := by
  intro Z
  obtain ⟨C_fam, hC_prop, hC_pair, hC_union⟩ :=
    exists_anticonnected_components_finset_aux G Z.card Z le_rfl
  obtain ⟨q, C, _, hC_inj, _, hC_mem, _, hC_mono⟩ := exists_sorted_equiv_of_finset C_fam
  have hZ_sub_M : Z ⊆ M := by
    unfold Z neighborFinsetIn
    exact Finset.filter_subset _ _
  have hC_disj_comp : ∀ s t : Fin q, s ≠ t → Disjoint (C s) (C t) ∧ IsCompletePair G (C s) (C t) :=
    fun s t hst => hC_pair (C s) (hC_mem s) (C t) (hC_mem t) (fun h => hst (hC_inj h))
  have hC_biUnion : Finset.univ.biUnion C = Z := by
    rw [← hC_union]
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, id_eq]
    constructor
    · rintro ⟨s, hx⟩
      exact ⟨C s, hC_mem s, hx⟩
    · rintro ⟨A, hA, hx⟩
      obtain ⟨s, rfl⟩ := ‹∀ A ∈ C_fam, ∃ j : Fin q, C j = A› A hA
      exact ⟨s, hx⟩
  have hC_sum : ∑ s : Fin q, (C s).card = Z.card := by
    rw [← hC_biUnion, Finset.card_biUnion]
    intro s _ t _ hst
    exact (hC_disj_comp s t hst).1
  refine ⟨q, C, ?_, hC_disj_comp, hC_biUnion, hC_sum, hC_mono⟩
  intro s
  obtain ⟨hCs_Z, hCs_ne, hCs_aconn⟩ := hC_prop (C s) (hC_mem s)
  refine ⟨hCs_Z, hCs_ne, hCs_aconn, hCs_ne, ?_, hCs_Z.trans hZ_sub_M, ?_⟩
  · refine Finset.ssubset_iff_subset_ne.mpr ⟨hCs_Z.trans hZ_sub_M, ?_⟩
    intro h_eq
    apply hu_not_comp
    intro z hzM
    rw [← h_eq] at hzM
    have hzZ : z ∈ Z := hCs_Z hzM
    unfold Z neighborFinsetIn at hzZ
    exact (Finset.mem_filter.mp hzZ).2
  · intro z hzM hzCs
    by_cases hzZ : z ∈ Z
    · rw [← hC_biUnion, Finset.mem_biUnion] at hzZ
      obtain ⟨t, _, hzt⟩ := hzZ
      have hts : t ≠ s := fun h => hzCs (h ▸ hzt)
      left
      intro y hy
      exact (hC_disj_comp t s hts).2 z hzt y hy
    · unfold Z neighborFinsetIn at hzZ
      simp only [Finset.mem_filter, hzM, true_and] at hzZ
      by_contra hnot_pure
      unfold IsVertexPureTo at hnot_pure
      push_neg at hnot_pure
      obtain ⟨⟨y₁, hy₁C, hzy₁⟩, ⟨y₂, hy₂C, hzy₂⟩⟩ := hnot_pure
      obtain ⟨p⟩ := hCs_aconn.preconnected ⟨y₁, hy₁C⟩ ⟨y₂, hy₂C⟩
      obtain ⟨x₂, hx₂C, x₃, hx₃C, hx₂x₃_compl, hzx₂, hzx₃⟩ :=
        exists_mixed_edge_of_walk p hzy₁ hzy₂
      have hx₂Z : x₂ ∈ Z := hCs_Z hx₂C
      have hx₃Z : x₃ ∈ Z := hCs_Z hx₃C
      unfold Z neighborFinsetIn at hx₂Z hx₃Z
      obtain ⟨hx₂M, hux₂⟩ := Finset.mem_filter.mp hx₂Z
      obtain ⟨hx₃M, hux₃⟩ := Finset.mem_filter.mp hx₃Z
      have hzBi : z ∈ B i := hMB hzM
      have hx₂Bi : x₂ ∈ B i := hMB hx₂M
      have hx₃Bi : x₃ ∈ B i := hMB hx₃M
      exact not_isInducedSubgraphFree_P6Compl v (a i) u z x₂ x₃
        (hapex.not_apex i)
        (hapex.anticomplete_to_apices i)
        (hcomb.apex_anticomplete_other i r hri.symm u huB)
        hzZ
        hzx₂
        hx₂x₃_compl.2
        (hapex.complete_to_blocks r u huB)
        (hapex.complete_to_blocks i z hzBi)
        (hapex.complete_to_blocks i x₂ hx₂Bi)
        (hapex.complete_to_blocks i x₃ hx₃Bi)
        (hcomb.apex_complete_own i z hzBi)
        (hcomb.apex_complete_own i x₂ hx₂Bi)
        (hcomb.apex_complete_own i x₃ hx₃Bi)
        hux₂
        hux₃
        hzx₃
        hG

/-! ### Part 3: Lemma 4.3 (`lem:gallai-core`): Two-Tier Potential-Preserving Gallai Tree Decomposition -/

/--
A subset $M^* \subseteq B_i$ is a $\theta$-small-attachment core (`IsSmallAttachmentCore G B i θ M_star`)
if $M^* \subseteq B_i$ is nonempty and for every external comb vertex $u \in B_r$ ($r \neq i$)
not complete to $M^*$ in $G$, the anticonnected components $C_1, \dots, C_q$ ($|C_1| \ge \dots \ge |C_q|$)
of $N_G(u) \cap M^*$ form a complete blockade partitioning $N_G(u) \cap M^*$ with $|C_s| \le \theta |M^*|$.
-/
def IsSmallAttachmentCore (G : SimpleGraph V) {ℓ : ℕ} (B : Fin ℓ → Finset V) (i : Fin ℓ)
    (θ : ℝ) (M_star : Finset V) : Prop :=
  M_star ⊆ B i ∧ M_star.Nonempty ∧
  ∀ (r : Fin ℓ), r ≠ i → ∀ u ∈ B r, (¬∀ z ∈ M_star, G.Adj u z) →
    let Z := neighborFinsetIn G u M_star
    ∃ (q : ℕ) (C : Fin q → Finset V),
      (∀ s : Fin q, C s ⊆ Z ∧ (C s).Nonempty ∧ IsAnticonnected G (C s)) ∧
      (∀ s t : Fin q, s ≠ t → Disjoint (C s) (C t) ∧ IsCompletePair G (C s) (C t)) ∧
      Finset.univ.biUnion C = Z ∧
      ∑ s : Fin q, (C s).card = Z.card ∧
      (∀ s t : Fin q, s ≤ t → (C t).card ≤ (C s).card) ∧
      (∀ s : Fin q, ((C s).card : ℝ) ≤ θ * (M_star.card : ℝ))

/-- Any singleton $\{z_0\} \subseteq B_i$ is trivially a $\theta$-small-attachment core. -/
lemma isSmallAttachmentCore_singleton {G : SimpleGraph V} {ℓ : ℕ} {B : Fin ℓ → Finset V}
    {i : Fin ℓ} {θ : ℝ} {z₀ : V} (hz₀ : z₀ ∈ B i) :
    IsSmallAttachmentCore G B i θ {z₀} := by
  refine ⟨Finset.singleton_subset_iff.mpr hz₀, Finset.singleton_nonempty z₀, ?_⟩
  intro r _ u _ hu_not_comp
  dsimp only
  have hZ_emp : neighborFinsetIn G u {z₀} = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro z hz
    unfold neighborFinsetIn at hz
    obtain ⟨hz_eq, hadj⟩ := Finset.mem_filter.mp hz
    rw [Finset.mem_singleton.mp hz_eq] at hadj
    exact hu_not_comp (fun w hw => Finset.mem_singleton.mp hw ▸ hadj)
  refine ⟨0, Fin.elim0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s; exact Fin.elim0 s
  · intro s; exact Fin.elim0 s
  · simp [hZ_emp]
  · simp [hZ_emp]
  · intro s; exact Fin.elim0 s
  · intro s; exact Fin.elim0 s

/-- If $M_s \subseteq B_i$ is nonempty and $m_{\max}(G[M_s]) \le \theta |M_s|$, then $M_s$ is
a $\theta$-small-attachment core. -/
lemma isSmallAttachmentCore_of_mMax_le {G : SimpleGraph V} {S : Finset V} {ℓ : ℕ} {w : ℝ}
    {a : Fin ℓ → V} {B : Fin ℓ → Finset V} {v : V}
    (hG : IsInducedSubgraphFree G P6Compl)
    (hcomb : IsCombIn G S ℓ w a B)
    (hapex : IsCombExternalApex G S ℓ a B v)
    {i : Fin ℓ} {θ : ℝ} {M_s : Finset V} (hMB : M_s ⊆ B i) (hne : M_s.Nonempty)
    (hmMax : (mMax G M_s : ℝ) ≤ θ * (M_s.card : ℝ)) :
    IsSmallAttachmentCore G B i θ M_s := by
  refine ⟨hMB, hne, ?_⟩
  intro r hri u huB hu_not_comp
  obtain ⟨q, C, hC_prop, hC_pair, hC_union, hC_sum, hC_mono⟩ :=
    anticonnected_neighborhood_modules hG hcomb hapex hri hMB huB hu_not_comp
  refine ⟨q, C, fun s => ⟨(hC_prop s).1, (hC_prop s).2.1, (hC_prop s).2.2.1⟩,
    hC_pair, hC_union, hC_sum, hC_mono, fun s => ?_⟩
  have hle : (C s).card ≤ mMax G M_s := card_le_mMax_of_isProperModuleIn (hC_prop s).2.2.2
  exact le_trans (Nat.cast_le.mpr hle) hmMax

/-- Helper for $1/8$-power lower bounds: $a^8 \le b \implies a \le b^{1/8}$ for $a, b \ge 0$. -/
lemma le_rpow_one_eighth_of_pow_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 8 ≤ b) :
    a ≤ b ^ (1 / 8 : ℝ) := by
  have h1 : (a ^ (8 : ℝ)) ^ (1 / 8 : ℝ) ≤ b ^ (1 / 8 : ℝ) := by
    refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
    rwa [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rwa [← Real.rpow_mul ha, show (8 : ℝ) * (1 / 8 : ℝ) = 1 by norm_num, Real.rpow_one] at h1

/-- Helper for $1/8$-power upper bounds: $a < b^8 \implies a^{1/8} < b$ for $a, b \ge 0$. -/
lemma rpow_one_eighth_lt_of_lt_pow {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a < b ^ 8) :
    a ^ (1 / 8 : ℝ) < b := by
  have h1 : a ^ (1 / 8 : ℝ) < (b ^ (8 : ℝ)) ^ (1 / 8 : ℝ) := by
    refine Real.rpow_lt_rpow ha ?_ (by positivity)
    rwa [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rwa [← Real.rpow_mul hb, show (8 : ℝ) * (1 / 8 : ℝ) = 1 by norm_num, Real.rpow_one] at h1

/-- Potential conservation inequality: if $k \ge 2$ and each block $U_j$ has cardinality
at least $\frac{|W|}{64 k^2}$, then $\sum_{j=1}^k |U_j|^{1/8} \ge |W|^{1/8}$. -/
lemma potential_conservation_of_width {W : Finset V} {k : ℕ} {U : Fin k → Finset V}
    (hk : 2 ≤ k)
    (hw : ∀ j : Fin k, (W.card : ℝ) / (64 * (k : ℝ) ^ 2) ≤ ((U j).card : ℝ)) :
    (W.card : ℝ) ^ (1 / 8 : ℝ) ≤ ∑ j : Fin k, ((U j).card : ℝ) ^ (1 / 8 : ℝ) := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := Nat.ofNat_le_cast.mpr hk
  have hk6 : (64 : ℝ) ≤ (k : ℝ) ^ 6 := by
    have h64 : (64 : ℝ) = (2 : ℝ) ^ 6 := by norm_num
    rw [h64]
    exact pow_le_pow_left₀ (by positivity) hk2 6
  have hk8 : 64 * (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 8 := by
    calc 64 * (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 6 * (k : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hk6 (by positivity)
      _ = (k : ℝ) ^ 8 := by ring
  have h_term : ∀ j : Fin k,
      (W.card : ℝ) ^ (1 / 8 : ℝ) / (k : ℝ) ≤ ((U j).card : ℝ) ^ (1 / 8 : ℝ) := by
    intro j
    refine le_rpow_one_eighth_of_pow_le (by positivity) (by positivity) ?_
    rw [div_pow]
    have hW8 : ((W.card : ℝ) ^ (1 / 8 : ℝ)) ^ 8 = (W.card : ℝ) := by
      rw [← Real.rpow_natCast, show ((8 : ℕ) : ℝ) = 8 by norm_num,
        ← Real.rpow_mul (Nat.cast_nonneg _), show (1 / 8 : ℝ) * 8 = 1 by norm_num, Real.rpow_one]
    rw [hW8]
    have h_div : (W.card : ℝ) / (k : ℝ) ^ 8 ≤ (W.card : ℝ) / (64 * (k : ℝ) ^ 2) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) hk8
    exact le_trans h_div (hw j)
  calc (W.card : ℝ) ^ (1 / 8 : ℝ)
      = (k : ℝ) * ((W.card : ℝ) ^ (1 / 8 : ℝ) / (k : ℝ)) := by
        rw [mul_div_cancel₀ _ (ne_of_gt hk_pos)]
    _ = ∑ _j : Fin k, ((W.card : ℝ) ^ (1 / 8 : ℝ) / (k : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ ∑ j : Fin k, ((U j).card : ℝ) ^ (1 / 8 : ℝ) :=
        Finset.sum_le_sum (fun j _ => h_term j)

private lemma isCompletePair_symm {G : SimpleGraph V} {A B : Finset V} (h : IsCompletePair G A B) :
    IsCompletePair G B A :=
  fun u hu v hv => (h v hv u hu).symm

lemma isAnticompletePair_symm {G : SimpleGraph V} {A B : Finset V} (h : IsAnticompletePair G A B) :
    IsAnticompletePair G B A :=
  fun u hu v hv huv => h v hv u hu huv.symm

lemma isPurePair_symm {G : SimpleGraph V} {A B : Finset V} (h : IsPurePair G A B) :
    IsPurePair G B A :=
  Or.imp isCompletePair_symm isAnticompletePair_symm h

lemma isPurePair_mono {G : SimpleGraph V} {A B A' B' : Finset V}
    (h : IsPurePair G A B) (hA : A' ⊆ A) (hB : B' ⊆ B) :
    IsPurePair G A' B' := by
  rcases h with hcomp | hanti
  · left; exact fun u hu v hv => hcomp u (hA hu) v (hB hv)
  · right; exact fun u hu v hv => hanti u (hA hu) v (hB hv)

/-- Constructing a 2-block pure blockade in $W$ of width $|W|/256$. -/
lemma isPureBlockadeIn_two {G : SimpleGraph V} {W U₀ U₁ : Finset V}
    (hW : 1 ≤ W.card)
    (hU₀_sub : U₀ ⊆ W) (hU₁_sub : U₁ ⊆ W)
    (hdisj : Disjoint U₀ U₁) (hpure : IsPurePair G U₀ U₁)
    (hU₀_card : (W.card : ℝ) / 256 ≤ (U₀.card : ℝ))
    (hU₁_card : (W.card : ℝ) / 256 ≤ (U₁.card : ℝ)) :
    IsPureBlockadeIn G W 2 ((W.card : ℝ) / (64 * (2 : ℝ) ^ 2)) ![U₀, U₁] := by
  have hW_pos : (0 : ℝ) < (W.card : ℝ) := Nat.cast_pos.mpr (by omega)
  have hU₀_ne : U₀.Nonempty := by
    rw [← Finset.card_pos, ← @Nat.cast_pos ℝ]
    linarith
  have hU₁_ne : U₁.Nonempty := by
    rw [← Finset.card_pos, ← @Nat.cast_pos ℝ]
    linarith
  have h256 : (64 : ℝ) * (2 : ℝ) ^ 2 = 256 := by norm_num
  rw [h256]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i; fin_cases i <;> simp [hU₀_sub, hU₁_sub]
  · intro i; fin_cases i <;> simp [hU₀_ne, hU₁_ne]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · exact hdisj
    · exact hdisj.symm
  · intro i; fin_cases i <;> simp [hU₀_card, hU₁_card]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · exact hpure
    · exact isPurePair_symm hpure

/-- Subset sum extraction: if every element has weight $\le B$ and total weight is $\ge B$,
some subset has total weight in $[B, 2B]$. -/
lemma exists_subset_sum_Icc {α : Type*} [DecidableEq α] (F : Finset α) (f : α → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (h_upper : ∀ a ∈ F, f a ≤ B) (h_sum : B ≤ ∑ a ∈ F, f a) :
    ∃ F₁ ⊆ F, B ≤ ∑ a ∈ F₁, f a ∧ ∑ a ∈ F₁, f a ≤ 2 * B := by
  induction F using Finset.induction_on with
  | empty =>
    refine ⟨∅, Finset.Subset.rfl, h_sum, ?_⟩
    simp only [Finset.sum_empty]
    linarith
  | @insert a₀ F' ha₀ ih =>
    by_cases hF' : B ≤ ∑ a ∈ F', f a
    · obtain ⟨F₁, hF₁_sub, h1, h2⟩ := ih (fun a ha => h_upper a (Finset.mem_insert_of_mem ha)) hF'
      exact ⟨F₁, hF₁_sub.trans (Finset.subset_insert a₀ F'), h1, h2⟩
    · refine ⟨insert a₀ F', Finset.Subset.rfl, h_sum, ?_⟩
      rw [Finset.sum_insert ha₀]
      have ha₀_le := h_upper a₀ (Finset.mem_insert_self a₀ F')
      linarith

/-- Splitting a pairwise-complete or pairwise-anticomplete family of small blocks into a pure 2-blockade. -/
lemma exists_pure_two_of_small_family {G : SimpleGraph V} {W : Finset V}
    (hW : 1 ≤ W.card) (F : Finset (Finset V))
    (hF_sub : ∀ A ∈ F, A ⊆ W ∧ (A.card : ℝ) ≤ (W.card : ℝ) / 32)
    (hF_disj : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → Disjoint A B)
    (hF_sum : (W.card : ℝ) / 8 ≤ ∑ A ∈ F, (A.card : ℝ))
    (hF_pure : (∀ A ∈ F, ∀ B ∈ F, A ≠ B → IsCompletePair G A B) ∨
      (∀ A ∈ F, ∀ B ∈ F, A ≠ B → IsAnticompletePair G A B)) :
    ∃ U : Fin 2 → Finset V,
      IsPureBlockadeIn G W 2 ((W.card : ℝ) / (64 * (2 : ℝ) ^ 2)) U := by
  have hW0 : (0 : ℝ) ≤ (W.card : ℝ) := Nat.cast_nonneg _
  have hB_le : (W.card : ℝ) / 32 ≤ ∑ A ∈ F, (A.card : ℝ) := by linarith
  obtain ⟨F₁, hF₁_sub, hF₁_ge, hF₁_le⟩ :=
    exists_subset_sum_Icc F (fun A => (A.card : ℝ)) ((W.card : ℝ) / 32)
      (by positivity) (fun A hA => (hF_sub A hA).2) hB_le
  let F₂ := F \ F₁
  have hF₂_sub : F₂ ⊆ F := Finset.sdiff_subset
  have hF₁₂_disj : Disjoint F₁ F₂ := Finset.disjoint_sdiff
  have hF₂_ge : (W.card : ℝ) / 32 ≤ ∑ A ∈ F₂, (A.card : ℝ) := by
    have h_split := Finset.sum_sdiff hF₁_sub (f := fun A : Finset V => (A.card : ℝ))
    linarith
  let U₀ := F₁.biUnion id
  let U₁ := F₂.biUnion id
  have hU₀_sub : U₀ ⊆ W := by
    rw [Finset.biUnion_subset]
    exact fun A hA => (hF_sub A (hF₁_sub hA)).1
  have hU₁_sub : U₁ ⊆ W := by
    rw [Finset.biUnion_subset]
    exact fun A hA => (hF_sub A (hF₂_sub hA)).1
  have hU₀_card_eq : (U₀.card : ℝ) = ∑ A ∈ F₁, (A.card : ℝ) := by
    have h_nat : U₀.card = ∑ A ∈ F₁, A.card :=
      Finset.card_biUnion (fun A hA B hB hAB => hF_disj A (hF₁_sub hA) B (hF₁_sub hB) hAB)
    exact_mod_cast h_nat
  have hU₁_card_eq : (U₁.card : ℝ) = ∑ A ∈ F₂, (A.card : ℝ) := by
    have h_nat : U₁.card = ∑ A ∈ F₂, A.card :=
      Finset.card_biUnion (fun A hA B hB hAB => hF_disj A (hF₂_sub hA) B (hF₂_sub hB) hAB)
    exact_mod_cast h_nat
  have hdisj : Disjoint U₀ U₁ := by
    rw [Finset.disjoint_biUnion_left]
    intro A hA
    rw [Finset.disjoint_biUnion_right]
    intro B hB
    have hAB : A ≠ B := fun h => Finset.disjoint_left.mp hF₁₂_disj hA (h ▸ hB)
    exact hF_disj A (hF₁_sub hA) B (hF₂_sub hB) hAB
  have hpure : IsPurePair G U₀ U₁ := by
    rcases hF_pure with hcomp | hanti
    · left
      intro u hu v hv
      obtain ⟨A, hA, huA⟩ := Finset.mem_biUnion.mp hu
      obtain ⟨B, hB, hvB⟩ := Finset.mem_biUnion.mp hv
      have hAB : A ≠ B := fun h => Finset.disjoint_left.mp hF₁₂_disj hA (h ▸ hB)
      exact hcomp A (hF₁_sub hA) B (hF₂_sub hB) hAB u huA v hvB
    · right
      intro u hu v hv
      obtain ⟨A, hA, huA⟩ := Finset.mem_biUnion.mp hu
      obtain ⟨B, hB, hvB⟩ := Finset.mem_biUnion.mp hv
      have hAB : A ≠ B := fun h => Finset.disjoint_left.mp hF₁₂_disj hA (h ▸ hB)
      exact hanti A (hF₁_sub hA) B (hF₂_sub hB) hAB u huA v hvB
  refine ⟨![U₀, U₁], isPureBlockadeIn_two hW hU₀_sub hU₁_sub hdisj hpure ?_ ?_⟩ <;> linarith

/-- Auxiliary induction for the greedy proper-module chain in $G[W]$ (Step 1, Subcase 1.1). -/
lemma greedy_module_chain_aux (G : SimpleGraph V) {W : Finset V} (hW : 64 ≤ W.card) :
    ∀ (n : ℕ) (M_s : Finset V) (S_pos S_neg : Finset (Finset V)),
      M_s.card ≤ n →
      M_s ⊆ W →
      (∀ A ∈ S_pos, A ⊆ W ∧ A.Nonempty ∧ (A.card : ℝ) ≤ (W.card : ℝ) / 32 ∧
        Disjoint A M_s ∧ IsCompletePair G A M_s) →
      (∀ A ∈ S_pos, ∀ B ∈ S_pos, A ≠ B → Disjoint A B ∧ IsCompletePair G A B) →
      (∀ A ∈ S_neg, A ⊆ W ∧ A.Nonempty ∧ (A.card : ℝ) ≤ (W.card : ℝ) / 32 ∧
        Disjoint A M_s ∧ IsAnticompletePair G A M_s) →
      (∀ A ∈ S_neg, ∀ B ∈ S_neg, A ≠ B → Disjoint A B ∧ IsAnticompletePair G A B) →
      (W.card : ℝ) ≤ (M_s.card : ℝ) +
        2 * (∑ A ∈ S_pos, (A.card : ℝ) + ∑ A ∈ S_neg, (A.card : ℝ)) →
      (∃ U : Fin 2 → Finset V,
        IsPureBlockadeIn G W 2 ((W.card : ℝ) / (64 * (2 : ℝ) ^ 2)) U) ∨
      (∃ M_term ⊆ W,
        (W.card : ℝ) / 2 < (M_term.card : ℝ) ∧ (mMax G M_term : ℝ) < (W.card : ℝ) / 64) := by
  intro n
  induction n with
  | zero =>
    intro M_s S_pos S_neg hMs_n _ hpos_prop hpos_pair hneg_prop hneg_pair hsum
    have hMs_zero : (M_s.card : ℝ) = 0 := by
      have : M_s.card = 0 := Nat.le_zero.mp hMs_n
      simp [this]
    left
    by_cases h_pos_ge : (W.card : ℝ) / 8 ≤ ∑ A ∈ S_pos, (A.card : ℝ)
    · exact exists_pure_two_of_small_family (by omega) S_pos
        (fun A hA => ⟨(hpos_prop A hA).1, (hpos_prop A hA).2.2.1⟩)
        (fun A hA B hB hAB => (hpos_pair A hA B hB hAB).1)
        h_pos_ge
        (Or.inl (fun A hA B hB hAB => (hpos_pair A hA B hB hAB).2))
    · have h_neg_ge : (W.card : ℝ) / 8 ≤ ∑ A ∈ S_neg, (A.card : ℝ) := by linarith
      exact exists_pure_two_of_small_family (by omega) S_neg
        (fun A hA => ⟨(hneg_prop A hA).1, (hneg_prop A hA).2.2.1⟩)
        (fun A hA B hB hAB => (hneg_pair A hA B hB hAB).1)
        h_neg_ge
        (Or.inr (fun A hA B hB hAB => (hneg_pair A hA B hB hAB).2))
  | succ m ih =>
    intro M_s S_pos S_neg hMs_n hMs_W hpos_prop hpos_pair hneg_prop hneg_pair hsum
    by_cases hMs_half : (M_s.card : ℝ) ≤ (W.card : ℝ) / 2
    · left
      by_cases h_pos_ge : (W.card : ℝ) / 8 ≤ ∑ A ∈ S_pos, (A.card : ℝ)
      · exact exists_pure_two_of_small_family (by omega) S_pos
          (fun A hA => ⟨(hpos_prop A hA).1, (hpos_prop A hA).2.2.1⟩)
          (fun A hA B hB hAB => (hpos_pair A hA B hB hAB).1)
          h_pos_ge
          (Or.inl (fun A hA B hB hAB => (hpos_pair A hA B hB hAB).2))
      · have h_neg_ge : (W.card : ℝ) / 8 ≤ ∑ A ∈ S_neg, (A.card : ℝ) := by linarith
        exact exists_pure_two_of_small_family (by omega) S_neg
          (fun A hA => ⟨(hneg_prop A hA).1, (hneg_prop A hA).2.2.1⟩)
          (fun A hA B hB hAB => (hneg_pair A hA B hB hAB).1)
          h_neg_ge
          (Or.inr (fun A hA B hB hAB => (hneg_pair A hA B hB hAB).2))
    · push_neg at hMs_half
      by_cases hmMax_lt : (mMax G M_s : ℝ) < (W.card : ℝ) / 64
      · right
        exact ⟨M_s, hMs_W, hMs_half, hmMax_lt⟩
      · push_neg at hmMax_lt
        have hMs_card2 : 2 ≤ M_s.card := by
          have hW_r : (64 : ℝ) ≤ (W.card : ℝ) := Nat.ofNat_le_cast.mpr hW
          have : (32 : ℝ) < (M_s.card : ℝ) := by linarith
          exact_mod_cast (by linarith : (2 : ℝ) ≤ (M_s.card : ℝ))
        obtain ⟨N_s, hNs_prop, hNs_card_eq⟩ := exists_isProperModuleIn_card_eq_mMax hMs_card2
        have hNs_ge : (W.card : ℝ) / 64 ≤ (N_s.card : ℝ) := by
          rw [hNs_card_eq]
          exact hmMax_lt
        have hNs_sub : N_s ⊆ M_s := hNs_prop.2.2.1
        have hNs_lt : N_s.card < M_s.card := Finset.card_lt_card hNs_prop.2.1
        let R_s := M_s \ N_s
        let R_pos := R_s.filter (fun z => ∀ u ∈ N_s, G.Adj z u)
        let R_neg := R_s \ R_pos
        have hR_pos_sub : R_pos ⊆ R_s := Finset.filter_subset _ _
        have hR_neg_sub : R_neg ⊆ R_s := Finset.sdiff_subset
        have hR_pos_Ms : R_pos ⊆ M_s := hR_pos_sub.trans Finset.sdiff_subset
        have hR_neg_Ms : R_neg ⊆ M_s := hR_neg_sub.trans Finset.sdiff_subset
        have hR_pos_disj : Disjoint R_pos N_s :=
          Finset.disjoint_of_subset_left hR_pos_sub Finset.sdiff_disjoint
        have hR_neg_disj : Disjoint R_neg N_s :=
          Finset.disjoint_of_subset_left hR_neg_sub Finset.sdiff_disjoint
        have hR_pos_comp : IsCompletePair G R_pos N_s :=
          fun z hz u hu => (Finset.mem_filter.mp hz).2 u hu
        have hR_neg_anti : IsAnticompletePair G R_neg N_s := by
          intro z hz u hu
          obtain ⟨hzR, hz_not_pos⟩ := Finset.mem_sdiff.mp hz
          obtain ⟨hzM, hz_not_N⟩ := Finset.mem_sdiff.mp hzR
          rcases hNs_prop.2.2.2 z hzM hz_not_N with hcomp | hanti
          · exact False.elim (hz_not_pos (Finset.mem_filter.mpr ⟨hzR, hcomp⟩))
          · exact hanti u hu
        have hR_cards : (R_pos.card : ℝ) + (R_neg.card : ℝ) + (N_s.card : ℝ) = (M_s.card : ℝ) := by
          have h1 : (R_neg.card : ℝ) + (R_pos.card : ℝ) = (R_s.card : ℝ) := by
            exact_mod_cast Finset.card_sdiff_add_card_eq_card hR_pos_sub
          have h2 : (R_s.card : ℝ) + (N_s.card : ℝ) = (M_s.card : ℝ) := by
            exact_mod_cast Finset.card_sdiff_add_card_eq_card hNs_sub
          linarith
        have hRs_pos : 0 < R_pos.card + R_neg.card := by
          have h1 : R_neg.card + R_pos.card = R_s.card :=
            Finset.card_sdiff_add_card_eq_card hR_pos_sub
          have h2 : R_s.card + N_s.card = M_s.card :=
            Finset.card_sdiff_add_card_eq_card hNs_sub
          omega
        by_cases h_half : R_neg.card ≤ R_pos.card
        · have hR_pos_ne : R_pos.Nonempty := Finset.card_pos.mp (by omega)
          have hR_pos_2 : (M_s.card : ℝ) ≤ (N_s.card : ℝ) + 2 * (R_pos.card : ℝ) := by
            have : (R_neg.card : ℝ) ≤ (R_pos.card : ℝ) := Nat.cast_le.mpr h_half
            linarith
          by_cases hR_big : (W.card : ℝ) / 32 < (R_pos.card : ℝ)
          · left
            exact ⟨![R_pos, N_s], isPureBlockadeIn_two (by omega)
              (hR_pos_Ms.trans hMs_W) (hNs_sub.trans hMs_W)
              hR_pos_disj (Or.inl hR_pos_comp) (by linarith) (by linarith)⟩
          · push_neg at hR_big
            have hR_not_mem : R_pos ∉ S_pos := by
              intro hmem
              obtain ⟨x, hx⟩ := hR_pos_ne
              exact Finset.disjoint_left.mp (hpos_prop R_pos hmem).2.2.2.1 hx (hR_pos_Ms hx)
            refine ih N_s (insert R_pos S_pos) S_neg (by omega) (hNs_sub.trans hMs_W)
              ?_ ?_ ?_ hneg_pair ?_
            · intro A hA
              rcases Finset.mem_insert.mp hA with rfl | hA'
              · exact ⟨hR_pos_Ms.trans hMs_W, hR_pos_ne, hR_big, hR_pos_disj, hR_pos_comp⟩
              · obtain ⟨hAW, hAne, hA32, hAdisj, hAcomp⟩ := hpos_prop A hA'
                exact ⟨hAW, hAne, hA32, Finset.disjoint_of_subset_right hNs_sub hAdisj,
                  fun u hu v hv => hAcomp u hu v (hNs_sub hv)⟩
            · intro A hA B hB hAB
              rcases Finset.mem_insert.mp hA with rfl | hA' <;>
                rcases Finset.mem_insert.mp hB with rfl | hB'
              · exact False.elim (hAB rfl)
              · obtain ⟨_, _, _, hBdisj, hBcomp⟩ := hpos_prop B hB'
                exact ⟨ (Finset.disjoint_of_subset_right hR_pos_Ms hBdisj).symm,
                  isCompletePair_symm (fun u hu v hv => hBcomp u hu v (hR_pos_Ms hv))⟩
              · obtain ⟨_, _, _, hAdisj, hAcomp⟩ := hpos_prop A hA'
                exact ⟨Finset.disjoint_of_subset_right hR_pos_Ms hAdisj,
                  fun u hu v hv => hAcomp u hu v (hR_pos_Ms hv)⟩
              · exact hpos_pair A hA' B hB' hAB
            · intro A hA
              obtain ⟨hAW, hAne, hA32, hAdisj, hAanti⟩ := hneg_prop A hA
              exact ⟨hAW, hAne, hA32, Finset.disjoint_of_subset_right hNs_sub hAdisj,
                fun u hu v hv => hAanti u hu v (hNs_sub hv)⟩
            · rw [Finset.sum_insert hR_not_mem]
              linarith
        · have h_half' : R_pos.card ≤ R_neg.card := by omega
          have hR_neg_ne : R_neg.Nonempty := Finset.card_pos.mp (by omega)
          have hR_neg_2 : (M_s.card : ℝ) ≤ (N_s.card : ℝ) + 2 * (R_neg.card : ℝ) := by
            have : (R_pos.card : ℝ) ≤ (R_neg.card : ℝ) := Nat.cast_le.mpr h_half'
            linarith
          by_cases hR_big : (W.card : ℝ) / 32 < (R_neg.card : ℝ)
          · left
            exact ⟨![R_neg, N_s], isPureBlockadeIn_two (by omega)
              (hR_neg_Ms.trans hMs_W) (hNs_sub.trans hMs_W)
              hR_neg_disj (Or.inr hR_neg_anti) (by linarith) (by linarith)⟩
          · push_neg at hR_big
            have hR_not_mem : R_neg ∉ S_neg := by
              intro hmem
              obtain ⟨x, hx⟩ := hR_neg_ne
              exact Finset.disjoint_left.mp (hneg_prop R_neg hmem).2.2.2.1 hx (hR_neg_Ms hx)
            refine ih N_s S_pos (insert R_neg S_neg) (by omega) (hNs_sub.trans hMs_W)
              ?_ hpos_pair ?_ ?_ ?_
            · intro A hA
              obtain ⟨hAW, hAne, hA32, hAdisj, hAcomp⟩ := hpos_prop A hA
              exact ⟨hAW, hAne, hA32, Finset.disjoint_of_subset_right hNs_sub hAdisj,
                fun u hu v hv => hAcomp u hu v (hNs_sub hv)⟩
            · intro A hA
              rcases Finset.mem_insert.mp hA with rfl | hA'
              · exact ⟨hR_neg_Ms.trans hMs_W, hR_neg_ne, hR_big, hR_neg_disj, hR_neg_anti⟩
              · obtain ⟨hAW, hAne, hA32, hAdisj, hAanti⟩ := hneg_prop A hA'
                exact ⟨hAW, hAne, hA32, Finset.disjoint_of_subset_right hNs_sub hAdisj,
                  fun u hu v hv => hAanti u hu v (hNs_sub hv)⟩
            · intro A hA B hB hAB
              rcases Finset.mem_insert.mp hA with rfl | hA' <;>
                rcases Finset.mem_insert.mp hB with rfl | hB'
              · exact False.elim (hAB rfl)
              · obtain ⟨_, _, _, hBdisj, hBanti⟩ := hneg_prop B hB'
                exact ⟨(Finset.disjoint_of_subset_right hR_neg_Ms hBdisj).symm,
                  isAnticompletePair_symm (fun u hu v hv => hBanti u hu v (hR_neg_Ms hv))⟩
              · obtain ⟨_, _, _, hAdisj, hAanti⟩ := hneg_prop A hA'
                exact ⟨Finset.disjoint_of_subset_right hR_neg_Ms hAdisj,
                  fun u hu v hv => hAanti u hu v (hR_neg_Ms hv)⟩
              · exact hneg_pair A hA' B hB' hAB
            · rw [Finset.sum_insert hR_not_mem]
              linarith

/-- Any anticonnected subset $C \subseteq Z$ intersecting a component $D \subseteq Z$ with
`IsCompletePair G D (Z \ D)` is completely contained in $D$. -/
lemma subset_of_isAnticonnected_of_isCompletePair_sdiff {G : SimpleGraph V}
    {Z C D : Finset V} (hCZ : C ⊆ Z)
    (hC_aconn : IsAnticonnected G C) (hD_comp : IsCompletePair G D (Z \ D))
    {x₀ : V} (hx₀C : x₀ ∈ C) (hx₀D : x₀ ∈ D) :
    C ⊆ D := by
  intro y hyC
  obtain ⟨p⟩ := hC_aconn.preconnected ⟨x₀, hx₀C⟩ ⟨y, hyC⟩
  have h_walk : ∀ (u v : (C : Set V)), (Gᶜ.induce (C : Set V)).Walk u v → u.1 ∈ D → v.1 ∈ D := by
    intro u v q huD
    induction q with
    | nil => exact huD
    | @cons a b c hadj q ih =>
      apply ih
      by_contra hbD
      have hb_sdiff : b.1 ∈ Z \ D := Finset.mem_sdiff.mpr ⟨hCZ b.2, hbD⟩
      exact hadj.2 (hD_comp a.1 huD b.1 hb_sdiff)
  exact h_walk ⟨x₀, hx₀C⟩ ⟨y, hyC⟩ p hx₀D

/-- **Step 1 of Lemma 4.3 (`local_splitting_dichotomy`, `lem:gallai-core`)**:
For any $W \subseteq B_i$ with $|W| \ge 64$, either:
- (a) $W$ contains a $\theta$-small-attachment core $M^* \subseteq W$ with $|M^*| \ge \frac{1}{4}|W|$; or
- (b) $W$ contains a pure $(k, \frac{|W|}{64 k^2})$-blockade $(U_1, \dots, U_k)$ with $k \in [2, K_0]$
  and $\sum_{j=1}^k |U_j|^{1/8} \ge |W|^{1/8}$. -/
theorem local_splitting_dichotomy {G : SimpleGraph V} {S : Finset V} {ℓ : ℕ} {w : ℝ}
    {a : Fin ℓ → V} {B : Fin ℓ → Finset V} {v : V}
    (hG : IsInducedSubgraphFree G P6Compl)
    (hcomb : IsCombIn G S ℓ w a B)
    (hapex : IsCombExternalApex G S ℓ a B v)
    {i : Fin ℓ} {θ : ℝ} {K₀ : ℕ}
    (hθ_pos : 0 < θ) (hK₀_ge : 4 ≤ K₀) (hK₀_gt : θ⁻¹ < (K₀ : ℝ) + 1)
    {W : Finset V} (hWB : W ⊆ B i) (hW_card : 64 ≤ W.card) :
    (∃ M_star ⊆ W, (W.card : ℝ) / 4 ≤ (M_star.card : ℝ) ∧
      IsSmallAttachmentCore G B i θ M_star) ∨
    (∃ (k : ℕ) (U : Fin k → Finset V),
      2 ≤ k ∧ k ≤ K₀ ∧
      IsPureBlockadeIn G W k ((W.card : ℝ) / (64 * (k : ℝ) ^ 2)) U ∧
      (W.card : ℝ) ^ (1 / 8 : ℝ) ≤ ∑ j : Fin k, ((U j).card : ℝ) ^ (1 / 8 : ℝ)) := by
  have h_chain := greedy_module_chain_aux G hW_card W.card W ∅ ∅ le_rfl Finset.Subset.rfl
    (by simp) (by simp) (by simp) (by simp) (by simp)
  rcases h_chain with ⟨U, hU⟩ | ⟨M_s, hMs_W, hMs_gt, hmMax_lt⟩
  · right
    exact ⟨2, U, le_rfl, by omega, hU, potential_conservation_of_width le_rfl hU.1.width_ge⟩
  · have hW_r : (64 : ℝ) ≤ (W.card : ℝ) := Nat.ofNat_le_cast.mpr hW_card
    have hMs_ne : M_s.Nonempty := by
      rw [← Finset.card_pos, ← @Nat.cast_pos ℝ]
      linarith
    by_cases hmMax_θ : (mMax G M_s : ℝ) ≤ θ * (M_s.card : ℝ)
    · left
      refine ⟨M_s, hMs_W, by linarith,
        isSmallAttachmentCore_of_mMax_le hG hcomb hapex (hMs_W.trans hWB) hMs_ne hmMax_θ⟩
    · push_neg at hmMax_θ
      have hMs_card2 : 2 ≤ M_s.card := by
        exact_mod_cast (by linarith : (2 : ℝ) ≤ (M_s.card : ℝ))
      have hmMax_2 : 2 * mMax G M_s < M_s.card := by
        exact_mod_cast (by linarith : (2 : ℝ) * (mMax G M_s : ℝ) < (M_s.card : ℝ))
      obtain ⟨hconn, haconn⟩ := connected_and_anticonnected_of_two_mul_mMax_lt hMs_card2 hmMax_2
      obtain ⟨t, P, hP_max, hP_pure, hP_biUnion, hP_sum, hP_mono, hP_sup⟩ :=
        gallai_prime_partition hMs_card2 hconn haconn
      have hP_lt_64 : ∀ j : Fin t, ((P j).card : ℝ) < (W.card : ℝ) / 64 := by
        intro j
        have hle : (P j).card ≤ mMax G M_s := card_le_mMax_of_isProperModuleIn (hP_max j).1
        have hle_r : ((P j).card : ℝ) ≤ (mMax G M_s : ℝ) := Nat.cast_le.mpr hle
        linarith
      by_cases h_split : ∃ (k : ℕ) (hk : 2 ≤ k ∧ k ≤ min t K₀),
          (W.card : ℝ) / (64 * (k : ℝ) ^ 2) ≤ ((P ⟨k - 1, by omega⟩).card : ℝ)
      · right
        obtain ⟨k, ⟨hk2, hk_min⟩, hk_width⟩ := h_split
        have hkt : k ≤ t := le_trans hk_min (Nat.min_le_left t K₀)
        have hkK₀ : k ≤ K₀ := le_trans hk_min (Nat.min_le_right t K₀)
        let U : Fin k → Finset V := fun j => P ⟨j.1, by omega⟩
        have hU_width : ∀ j : Fin k, (W.card : ℝ) / (64 * (k : ℝ) ^ 2) ≤ ((U j).card : ℝ) := by
          intro j
          have hj_le : (⟨j.1, by omega⟩ : Fin t) ≤ ⟨k - 1, by omega⟩ := by
            simp only [Fin.mk_le_mk]
            omega
          have h_mono := Nat.cast_le (α := ℝ).mpr (hP_mono ⟨j.1, by omega⟩ ⟨k - 1, by omega⟩ hj_le)
          exact le_trans hk_width h_mono
        have hU_pure : IsPureBlockadeIn G W k ((W.card : ℝ) / (64 * (k : ℝ) ^ 2)) U := by
          refine ⟨⟨?_, ?_, ?_, hU_width⟩, ?_⟩
          · intro j; exact (hP_max ⟨j.1, by omega⟩).1.2.2.1.trans hMs_W
          · intro j; exact (hP_max ⟨j.1, by omega⟩).1.1
          · intro j₁ j₂ hj
            have hj' : (⟨j₁.1, by omega⟩ : Fin t) ≠ ⟨j₂.1, by omega⟩ := by
              intro h; apply hj; ext; exact Fin.mk.inj_iff.mp h
            exact (hP_pure _ _ hj').1
          · intro j₁ j₂ hj
            have hj' : (⟨j₁.1, by omega⟩ : Fin t) ≠ ⟨j₂.1, by omega⟩ := by
              intro h; apply hj; ext; exact Fin.mk.inj_iff.mp h
            exact (hP_pure _ _ hj').2
        exact ⟨k, U, hk2, hkK₀, hU_pure, potential_conservation_of_width hk2 hU_width⟩
      · push_neg at h_split
        left
        have h_head_bound : ∀ j : Fin t, j.1 < K₀ →
            ((P j).card : ℝ) ≤ (W.card : ℝ) / 64 * ((1 : ℝ) / ((j.1 + 1 : ℕ) : ℝ) ^ 2) := by
          intro j hjK₀
          by_cases hj0 : j.1 = 0
          · have h1 := hP_lt_64 j
            rw [hj0]
            norm_num
            linarith
          · have hk2 : 2 ≤ j.1 + 1 ∧ j.1 + 1 ≤ min t K₀ := ⟨by omega, by omega⟩
            have h1 := h_split (j.1 + 1) hk2
            have hj_eq : (⟨j.1 + 1 - 1, by omega⟩ : Fin t) = j := by ext; dsimp
            rw [hj_eq] at h1
            have h_eq : (W.card : ℝ) / (64 * ((j.1 + 1 : ℕ) : ℝ) ^ 2) =
                (W.card : ℝ) / 64 * ((1 : ℝ) / ((j.1 + 1 : ℕ) : ℝ) ^ 2) := by ring
            linarith
        let I_head := Finset.univ.filter (fun j : Fin t => j.1 < K₀)
        let I_tail := Finset.univ.filter (fun j : Fin t => K₀ ≤ j.1)
        have hI_union : I_head ∪ I_tail = Finset.univ := by
          ext j
          simp only [I_head, I_tail, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
            true_and, iff_true]
          omega
        have hI_disj : Disjoint I_head I_tail := by
          rw [Finset.disjoint_left]
          intro j hj1 hj2
          simp only [I_head, I_tail, Finset.mem_filter, Finset.mem_univ, true_and] at hj1 hj2
          omega
        have h_head_sum : ∑ j ∈ I_head, ((P j).card : ℝ) < (W.card : ℝ) / 32 := by
          have h1 : ∑ j ∈ I_head, ((P j).card : ℝ) ≤
              ∑ j ∈ I_head, (W.card : ℝ) / 64 * ((1 : ℝ) / ((j.1 + 1 : ℕ) : ℝ) ^ 2) :=
            Finset.sum_le_sum (fun j hj => h_head_bound j (Finset.mem_filter.mp hj).2)
          rw [← Finset.mul_sum] at h1
          have h_inj : ∑ j ∈ I_head, (1 : ℝ) / ((j.1 + 1 : ℕ) : ℝ) ^ 2 ≤
              ∑ k ∈ Finset.Icc 1 K₀, (1 : ℝ) / (k : ℝ) ^ 2 := by
            have h_img : Finset.image (fun j : Fin t => j.1 + 1) I_head ⊆ Finset.Icc 1 K₀ := by
              intro k hk
              obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
              have hj' := (Finset.mem_filter.mp hj).2
              simp only [Finset.mem_Icc]
              omega
            rw [← Finset.sum_image (f := fun k : ℕ => (1 : ℝ) / (k : ℝ) ^ 2)
              (fun j₁ _ j₂ _ h => by ext; omega)]
            exact Finset.sum_le_sum_of_subset_of_nonneg h_img (fun _ _ _ => by positivity)
          have h_lt2 := sum_inv_sq_Icc_lt_two 0 K₀
          have h_mul : (W.card : ℝ) / 64 * ∑ j ∈ I_head, (1 : ℝ) / ((j.1 + 1 : ℕ) : ℝ) ^ 2 <
              (W.card : ℝ) / 64 * 2 :=
            mul_lt_mul_of_pos_left (lt_of_le_of_lt h_inj h_lt2) (by positivity)
          linarith
        let M_star := I_tail.biUnion P
        have hM_star_sub_Ms : M_star ⊆ M_s := by
          rw [← hP_biUnion]
          exact Finset.biUnion_subset_biUnion_of_subset_left P (Finset.filter_subset _ _)
        have hM_star_sub_W : M_star ⊆ W := hM_star_sub_Ms.trans hMs_W
        have hM_star_card_eq : (M_star.card : ℝ) = ∑ j ∈ I_tail, ((P j).card : ℝ) := by
          unfold M_star
          rw [Finset.card_biUnion (fun i _ j _ hij => (hP_pure i j hij).1)]
          push_cast
          rfl
        have h_total_sum : ∑ j ∈ I_head, ((P j).card : ℝ) + ∑ j ∈ I_tail, ((P j).card : ℝ) =
            (M_s.card : ℝ) := by
          rw [← Finset.sum_union hI_disj, hI_union]
          exact_mod_cast hP_sum
        have hM_star_gt : (W.card : ℝ) / 4 < (M_star.card : ℝ) := by linarith
        have hM_star_ne : M_star.Nonempty := by
          rw [← Finset.card_pos, ← @Nat.cast_pos ℝ]
          linarith
        have hK₀_lt_t : K₀ < t := by
          obtain ⟨x, hx⟩ := hM_star_ne
          obtain ⟨j, hj, _⟩ := Finset.mem_biUnion.mp hx
          have hj' := (Finset.mem_filter.mp hj).2
          omega
        have h_tail_le_θ : ∀ j : Fin t, K₀ ≤ j.1 → ((P j).card : ℝ) ≤ θ * (M_star.card : ℝ) := by
          intro j hjK₀
          have hk_min : 2 ≤ K₀ ∧ K₀ ≤ min t K₀ := ⟨by omega, by omega⟩
          have h_K₀ := h_split K₀ hk_min
          have hj_ge : (⟨K₀ - 1, by omega⟩ : Fin t) ≤ j := by
            rw [Fin.le_def]; dsimp; omega
          have h_mono : ((P j).card : ℝ) ≤ ((P ⟨K₀ - 1, by omega⟩).card : ℝ) :=
            Nat.cast_le.mpr (hP_mono _ _ hj_ge)
          have hK₀_r : (4 : ℝ) ≤ (K₀ : ℝ) := Nat.ofNat_le_cast.mpr hK₀_ge
          have h_inv_le : (K₀ : ℝ) + 1 ≤ 16 * (K₀ : ℝ) ^ 2 := by nlinarith
          have hθ_inv_lt : θ⁻¹ < 16 * (K₀ : ℝ) ^ 2 := lt_of_lt_of_le hK₀_gt h_inv_le
          have h_16K₀_le_θ : 1 / (16 * (K₀ : ℝ) ^ 2) ≤ θ := by
            rw [div_le_iff₀ (by positivity)]
            have h1 : θ * θ⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hθ_pos)
            nlinarith [mul_lt_mul_of_pos_left hθ_inv_lt hθ_pos]
          have h1 : ((P j).card : ℝ) < (W.card : ℝ) / (64 * (K₀ : ℝ) ^ 2) :=
            lt_of_le_of_lt h_mono h_K₀
          have h2 : (W.card : ℝ) / (64 * (K₀ : ℝ) ^ 2) ≤
              (4 * (M_star.card : ℝ)) / (64 * (K₀ : ℝ) ^ 2) :=
            div_le_div_of_nonneg_right (by linarith) (by positivity)
          have h3 : (4 * (M_star.card : ℝ)) / (64 * (K₀ : ℝ) ^ 2) =
              (1 / (16 * (K₀ : ℝ) ^ 2)) * (M_star.card : ℝ) := by ring
          have h4 : (1 / (16 * (K₀ : ℝ) ^ 2)) * (M_star.card : ℝ) ≤ θ * (M_star.card : ℝ) :=
            mul_le_mul_of_nonneg_right h_16K₀_le_θ (Nat.cast_nonneg _)
          linarith
        refine ⟨M_star, hM_star_sub_W, le_of_lt hM_star_gt, hM_star_sub_W.trans hWB, hM_star_ne, ?_⟩
        intro r hri u huB hu_not_comp
        have hu_not_comp_Ms : ¬∀ z ∈ M_s, G.Adj u z :=
          fun h => hu_not_comp (fun z hz => h z (hM_star_sub_Ms hz))
        obtain ⟨q, C, hC_prop, hC_pair, hC_union, hC_sum, hC_mono⟩ :=
          anticonnected_neighborhood_modules hG hcomb hapex hri (hM_star_sub_W.trans hWB) huB hu_not_comp
        obtain ⟨q_D, D, hD_prop, hD_pair, hD_union, _, _⟩ :=
          anticonnected_neighborhood_modules hG hcomb hapex hri (hMs_W.trans hWB) huB hu_not_comp_Ms
        refine ⟨q, C, fun s => ⟨(hC_prop s).1, (hC_prop s).2.1, (hC_prop s).2.2.1⟩,
          hC_pair, hC_union, hC_sum, hC_mono, fun s => ?_⟩
        obtain ⟨x₀, hx₀Cs⟩ := (hC_prop s).2.1
        have hCs_Zstar : C s ⊆ neighborFinsetIn G u M_star := (hC_prop s).1
        have hZstar_Z : neighborFinsetIn G u M_star ⊆ neighborFinsetIn G u M_s := by
          unfold neighborFinsetIn
          exact Finset.filter_subset_filter _ hM_star_sub_Ms
        have hCs_Z : C s ⊆ neighborFinsetIn G u M_s := hCs_Zstar.trans hZstar_Z
        have hx₀Z : x₀ ∈ neighborFinsetIn G u M_s := hCs_Z hx₀Cs
        rw [← hD_union, Finset.mem_biUnion] at hx₀Z
        obtain ⟨r₀, _, hx₀Dr₀⟩ := hx₀Z
        have hDr₀_comp : IsCompletePair G (D r₀) (neighborFinsetIn G u M_s \ D r₀) := by
          intro y hy z hz
          obtain ⟨hzZ, hz_not⟩ := Finset.mem_sdiff.mp hz
          rw [← hD_union, Finset.mem_biUnion] at hzZ
          obtain ⟨r₁, _, hzr₁⟩ := hzZ
          have hr₀₁ : r₀ ≠ r₁ := fun h => hz_not (h ▸ hzr₁)
          exact (hD_pair r₀ r₁ hr₀₁).2 y hy z hzr₁
        have hCs_sub_Dr₀ : C s ⊆ D r₀ :=
          subset_of_isAnticonnected_of_isCompletePair_sdiff hCs_Z (hC_prop s).2.2.1 hDr₀_comp hx₀Cs hx₀Dr₀
        obtain ⟨j, hj_sup⟩ := hP_sup (D r₀) (hD_prop r₀).2.2.2
        have hCs_sub_Pj : C s ⊆ P j := hCs_sub_Dr₀.trans hj_sup
        have hx₀_Mstar : x₀ ∈ M_star := (Finset.mem_filter.mp (hCs_Zstar hx₀Cs)).1
        obtain ⟨j', hj'_tail, hx₀Pj'⟩ := Finset.mem_biUnion.mp hx₀_Mstar
        have hjj' : j = j' := by
          by_contra hne
          exact Finset.disjoint_left.mp (hP_pure j j' hne).1 (hCs_sub_Pj hx₀Cs) hx₀Pj'
        have hj_K₀ : K₀ ≤ j.1 := hjj' ▸ (Finset.mem_filter.mp hj'_tail).2
        have h_card_le : ((C s).card : ℝ) ≤ ((P j).card : ℝ) :=
          Nat.cast_le.mpr (Finset.card_le_card hCs_sub_Pj)
        exact le_trans h_card_le (h_tail_le_θ j hj_K₀)

/-! ### Step 2 of Lemma 4.3 (`lem:gallai-core`): Uncapped Potential-Preserving Tree Refinement -/

/-- Any family of pairwise disjoint nonempty subsets of $B_i$ has cardinality at most $|B_i|$. -/
lemma card_family_le_card_ambient {B_i : Finset V} {L_set : Finset (Finset V)}
    (h_sub : ∀ A ∈ L_set, A ⊆ B_i ∧ A.Nonempty)
    (h_disj : ∀ A ∈ L_set, ∀ B' ∈ L_set, A ≠ B' → Disjoint A B') :
    L_set.card ≤ B_i.card := by
  calc L_set.card = ∑ _A ∈ L_set, 1 := by simp
    _ ≤ ∑ A ∈ L_set, A.card :=
        Finset.sum_le_sum (fun A hA => Finset.card_pos.mpr (h_sub A hA).2)
    _ = (L_set.biUnion id).card := (Finset.card_biUnion h_disj).symm
    _ ≤ B_i.card := Finset.card_le_card (Finset.biUnion_subset.mpr (fun A hA => (h_sub A hA).1))

/-- Every child created by splitting a leaf $W$ of size $\ge w / \ell^8$ into $k \le K_0$ parts
has size at least $w / (4 K_0)^{16}$. -/
lemma leaf_width_lower_bound {ℓ k K₀ : ℕ} {w : ℝ} {W : Finset V}
    (hℓ : 4 ≤ ℓ) (hw_pos : 0 ≤ w) (hk2 : 2 ≤ k) (hkK₀ : k ≤ K₀) (hK₀_ℓ : ℓ ^ 4 ≤ K₀)
    (hW : w / (ℓ : ℝ) ^ 8 ≤ (W.card : ℝ)) :
    w / (4 * (K₀ : ℝ)) ^ 16 ≤ (W.card : ℝ) / (64 * (k : ℝ) ^ 2) := by
  have hℓ_r : (4 : ℝ) ≤ (ℓ : ℝ) := Nat.ofNat_le_cast.mpr hℓ
  have hK₀_r : (1 : ℝ) ≤ (K₀ : ℝ) := by
    have : 1 ≤ K₀ := le_trans (by omega : 1 ≤ 4 ^ 4) (le_trans (Nat.pow_le_pow_left hℓ 4) hK₀_ℓ)
    exact Nat.one_le_cast.mpr this
  have hℓ4_K₀ : (ℓ : ℝ) ^ 4 ≤ (K₀ : ℝ) := by exact_mod_cast hK₀_ℓ
  have hℓ8_K₀2 : (ℓ : ℝ) ^ 8 ≤ (K₀ : ℝ) ^ 2 := by
    calc (ℓ : ℝ) ^ 8 = ((ℓ : ℝ) ^ 4) ^ 2 := by ring
      _ ≤ (K₀ : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hℓ4_K₀ 2
  have hk_K₀ : (k : ℝ) ^ 2 ≤ (K₀ : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (Nat.cast_le.mpr hkK₀) 2
  have h64_le : (64 : ℝ) ≤ 4 ^ 16 * (K₀ : ℝ) ^ 12 := by
    have h1 : (1 : ℝ) ≤ (K₀ : ℝ) ^ 12 := one_le_pow₀ hK₀_r
    nlinarith
  have h_denom : 64 * (k : ℝ) ^ 2 * (ℓ : ℝ) ^ 8 ≤ (4 * (K₀ : ℝ)) ^ 16 := by
    calc 64 * (k : ℝ) ^ 2 * (ℓ : ℝ) ^ 8
        ≤ (4 ^ 16 * (K₀ : ℝ) ^ 12) * (K₀ : ℝ) ^ 2 * (K₀ : ℝ) ^ 2 := by
          refine mul_le_mul (mul_le_mul h64_le hk_K₀ (by positivity) (by positivity))
            hℓ8_K₀2 (by positivity) (by positivity)
      _ = (4 * (K₀ : ℝ)) ^ 16 := by ring
  calc w / (4 * (K₀ : ℝ)) ^ 16
      ≤ w / (64 * (k : ℝ) ^ 2 * (ℓ : ℝ) ^ 8) :=
        div_le_div_of_nonneg_left hw_pos (by positivity) h_denom
    _ = (w / (ℓ : ℝ) ^ 8) / (64 * (k : ℝ) ^ 2) := by ring
    _ ≤ (W.card : ℝ) / (64 * (k : ℝ) ^ 2) :=
        div_le_div_of_nonneg_right hW (by positivity)

/-- Auxiliary induction for the uncapped tree refinement loop in Step 2 of Lemma 4.3 (`lem:gallai-core`). -/
lemma gallai_tree_refinement_aux {G : SimpleGraph V} {S : Finset V} {ℓ : ℕ} {w : ℝ}
    {a : Fin ℓ → V} {B : Fin ℓ → Finset V} {v : V}
    (hG : IsInducedSubgraphFree G P6Compl)
    (hcomb : IsCombIn G S ℓ w a B)
    (hapex : IsCombExternalApex G S ℓ a B v)
    {i : Fin ℓ} {θ : ℝ} {K₀ : ℕ}
    (hℓ : 4 ≤ ℓ) (hw_big : (2 : ℝ) ^ 18 * (ℓ : ℝ) ^ 8 < w)
    (hθ_pos : 0 < θ) (hK₀_ℓ : ℓ ^ 4 ≤ K₀) (hK₀_gt : θ⁻¹ < (K₀ : ℝ) + 1) :
    ∀ (n : ℕ) (L_set : Finset (Finset V)),
      (B i).card - L_set.card ≤ n →
      (∀ A ∈ L_set, A ⊆ B i ∧ A.Nonempty ∧ w / (4 * (K₀ : ℝ)) ^ 16 ≤ (A.card : ℝ)) →
      (∀ A ∈ L_set, ∀ B' ∈ L_set, A ≠ B' → Disjoint A B' ∧ IsPurePair G A B') →
      w ^ (1 / 8 : ℝ) ≤ ∑ A ∈ L_set, (A.card : ℝ) ^ (1 / 8 : ℝ) →
      ∃ L_term : Finset (Finset V),
        (∀ A ∈ L_term, A ⊆ B i ∧ A.Nonempty ∧ w / (4 * (K₀ : ℝ)) ^ 16 ≤ (A.card : ℝ)) ∧
        (∀ A ∈ L_term, ∀ B' ∈ L_term, A ≠ B' → Disjoint A B' ∧ IsPurePair G A B') ∧
        w ^ (1 / 8 : ℝ) ≤ ∑ A ∈ L_term, (A.card : ℝ) ^ (1 / 8 : ℝ) ∧
        (∀ A ∈ L_term,
          (∃ M_star ⊆ A, (A.card : ℝ) / 4 ≤ (M_star.card : ℝ) ∧
            IsSmallAttachmentCore G B i θ M_star) ∨
          (A.card : ℝ) < w / (ℓ : ℝ) ^ 8) := by
  have hK₀_ge : 4 ≤ K₀ :=
    le_trans (by omega : 4 ≤ 4 ^ 4) (le_trans (Nat.pow_le_pow_left hℓ 4) hK₀_ℓ)
  have hw_pos : 0 ≤ w := by
    have : (0 : ℝ) < (2 : ℝ) ^ 18 * (ℓ : ℝ) ^ 8 := by positivity
    linarith
  intro n
  induction n with
  | zero =>
    intro L_set h_rem h_sub h_pair h_pot
    by_cases h_done : ∀ A ∈ L_set,
        (∃ M_star ⊆ A, (A.card : ℝ) / 4 ≤ (M_star.card : ℝ) ∧
          IsSmallAttachmentCore G B i θ M_star) ∨
        (A.card : ℝ) < w / (ℓ : ℝ) ^ 8
    · exact ⟨L_set, h_sub, h_pair, h_pot, h_done⟩
    · push_neg at h_done
      obtain ⟨W, hW_mem, hW_no_core, hW_ge⟩ := h_done
      have hW_card : 64 ≤ W.card := by
        have hℓ_pos : (0 : ℝ) < (ℓ : ℝ) ^ 8 := by positivity
        have h1 : (2 : ℝ) ^ 18 < w / (ℓ : ℝ) ^ 8 := (lt_div_iff₀ hℓ_pos).mpr hw_big
        have h2 : (64 : ℝ) ≤ (W.card : ℝ) := by linarith
        exact_mod_cast h2
      rcases local_splitting_dichotomy hG hcomb hapex hθ_pos hK₀_ge hK₀_gt
          (h_sub W hW_mem).1 hW_card with ⟨M_star, hMW, hM_card, hM_core⟩ | ⟨k, U, hk2, _hkK₀, hU_pure, _⟩
      · exact False.elim (hW_no_core M_star hMW hM_card hM_core)
      · have hU_inj : Function.Injective U := by
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
          exact Finset.disjoint_left.mp (h_pair (U j) hA_mem W hW_mem hAW_ne).1
            hx (hU_pure.1.subset_ambient j hx)
        have hL'_sub : ∀ A ∈ L_set', A ⊆ B i ∧ A.Nonempty := by
          intro A hA
          rcases Finset.mem_union.mp hA with hA_er | hA_U
          · have hA_mem := Finset.erase_subset W L_set hA_er
            exact ⟨(h_sub A hA_mem).1, (h_sub A hA_mem).2.1⟩
          · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hA_U
            exact ⟨(hU_pure.1.subset_ambient j).trans (h_sub W hW_mem).1,
              hU_pure.1.nonempty_blocks j⟩
        have hL'_disj : ∀ A ∈ L_set', ∀ B' ∈ L_set', A ≠ B' → Disjoint A B' := by
          intro A hA B' hB' hAB'
          rcases Finset.mem_union.mp hA with hA_er | hA_U <;>
            rcases Finset.mem_union.mp hB' with hB'_er | hB'_U
          · exact (h_pair A (Finset.erase_subset W L_set hA_er)
              B' (Finset.erase_subset W L_set hB'_er) hAB').1
          · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hB'_U
            obtain ⟨hAW_ne, hA_mem⟩ := Finset.mem_erase.mp hA_er
            exact Finset.disjoint_of_subset_right (hU_pure.1.subset_ambient j)
              (h_pair A hA_mem W hW_mem hAW_ne).1
          · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hA_U
            obtain ⟨hB'W_ne, hB'_mem⟩ := Finset.mem_erase.mp hB'_er
            exact Finset.disjoint_of_subset_left (hU_pure.1.subset_ambient j)
              (h_pair W hW_mem B' hB'_mem hB'W_ne.symm).1
          · obtain ⟨j₁, _, rfl⟩ := Finset.mem_image.mp hA_U
            obtain ⟨j₂, _, rfl⟩ := Finset.mem_image.mp hB'_U
            exact hU_pure.1.pairwise_disjoint j₁ j₂ (fun h => hAB' (congr_arg U h))
        have hL'_le : L_set'.card ≤ (B i).card := card_family_le_card_ambient hL'_sub hL'_disj
        have hL'_card : L_set'.card = L_set.card - 1 + k := by
          rw [Finset.card_union_of_disjoint h_disj_LU, Finset.card_erase_of_mem hW_mem,
            Finset.card_image_of_injective _ hU_inj, Finset.card_univ, Fintype.card_fin]
        have hW_pos : 1 ≤ L_set.card := Finset.card_pos.mpr ⟨W, hW_mem⟩
        omega
  | succ m ih =>
    intro L_set h_rem h_sub h_pair h_pot
    by_cases h_done : ∀ A ∈ L_set,
        (∃ M_star ⊆ A, (A.card : ℝ) / 4 ≤ (M_star.card : ℝ) ∧
          IsSmallAttachmentCore G B i θ M_star) ∨
        (A.card : ℝ) < w / (ℓ : ℝ) ^ 8
    · exact ⟨L_set, h_sub, h_pair, h_pot, h_done⟩
    · push_neg at h_done
      obtain ⟨W, hW_mem, hW_no_core, hW_ge⟩ := h_done
      have hW_card : 64 ≤ W.card := by
        have hℓ_pos : (0 : ℝ) < (ℓ : ℝ) ^ 8 := by positivity
        have h1 : (2 : ℝ) ^ 18 < w / (ℓ : ℝ) ^ 8 := (lt_div_iff₀ hℓ_pos).mpr hw_big
        have h2 : (64 : ℝ) ≤ (W.card : ℝ) := by linarith
        exact_mod_cast h2
      rcases local_splitting_dichotomy hG hcomb hapex hθ_pos hK₀_ge hK₀_gt
          (h_sub W hW_mem).1 hW_card with ⟨M_star, hMW, hM_card, hM_core⟩ | ⟨k, U, hk2, hkK₀, hU_pure, hU_pot⟩
      · exact False.elim (hW_no_core M_star hMW hM_card hM_core)
      · have hU_inj : Function.Injective U := by
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
          exact Finset.disjoint_left.mp (h_pair (U j) hA_mem W hW_mem hAW_ne).1
            hx (hU_pure.1.subset_ambient j hx)
        have hL'_sub : ∀ A ∈ L_set', A ⊆ B i ∧ A.Nonempty ∧
            w / (4 * (K₀ : ℝ)) ^ 16 ≤ (A.card : ℝ) := by
          intro A hA
          rcases Finset.mem_union.mp hA with hA_er | hA_U
          · exact h_sub A (Finset.erase_subset W L_set hA_er)
          · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hA_U
            refine ⟨(hU_pure.1.subset_ambient j).trans (h_sub W hW_mem).1,
              hU_pure.1.nonempty_blocks j, ?_⟩
            exact le_trans (leaf_width_lower_bound hℓ hw_pos hk2 hkK₀ hK₀_ℓ hW_ge)
              (hU_pure.1.width_ge j)
        have hL'_pair : ∀ A ∈ L_set', ∀ B' ∈ L_set', A ≠ B' → Disjoint A B' ∧ IsPurePair G A B' := by
          intro A hA B' hB' hAB'
          rcases Finset.mem_union.mp hA with hA_er | hA_U <;>
            rcases Finset.mem_union.mp hB' with hB'_er | hB'_U
          · exact h_pair A (Finset.erase_subset W L_set hA_er)
              B' (Finset.erase_subset W L_set hB'_er) hAB'
          · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hB'_U
            obtain ⟨hAW_ne, hA_mem⟩ := Finset.mem_erase.mp hA_er
            have hAW := h_pair A hA_mem W hW_mem hAW_ne
            exact ⟨Finset.disjoint_of_subset_right (hU_pure.1.subset_ambient j) hAW.1,
              isPurePair_mono hAW.2 Finset.Subset.rfl (hU_pure.1.subset_ambient j)⟩
          · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hA_U
            obtain ⟨hB'W_ne, hB'_mem⟩ := Finset.mem_erase.mp hB'_er
            have hWB' := h_pair W hW_mem B' hB'_mem hB'W_ne.symm
            exact ⟨Finset.disjoint_of_subset_left (hU_pure.1.subset_ambient j) hWB'.1,
              isPurePair_mono hWB'.2 (hU_pure.1.subset_ambient j) Finset.Subset.rfl⟩
          · obtain ⟨j₁, _, rfl⟩ := Finset.mem_image.mp hA_U
            obtain ⟨j₂, _, rfl⟩ := Finset.mem_image.mp hB'_U
            have hj₁₂ : j₁ ≠ j₂ := fun h => hAB' (congr_arg U h)
            exact ⟨hU_pure.1.pairwise_disjoint j₁ j₂ hj₁₂, hU_pure.2 j₁ j₂ hj₁₂⟩
        have hL'_pot : w ^ (1 / 8 : ℝ) ≤ ∑ A ∈ L_set', (A.card : ℝ) ^ (1 / 8 : ℝ) := by
          rw [Finset.sum_union h_disj_LU]
          have h_U_sum : ∑ A ∈ U_set, (A.card : ℝ) ^ (1 / 8 : ℝ) =
              ∑ j : Fin k, ((U j).card : ℝ) ^ (1 / 8 : ℝ) :=
            Finset.sum_image (fun j₁ _ j₂ _ h => hU_inj h)
          have h_er_sum := Finset.sum_erase_add L_set (fun A : Finset V => (A.card : ℝ) ^ (1 / 8 : ℝ)) hW_mem
          linarith
        have hL_le : L_set.card ≤ (B i).card :=
          card_family_le_card_ambient (fun A hA => ⟨(h_sub A hA).1, (h_sub A hA).2.1⟩)
            (fun A hA B' hB' hAB' => (h_pair A hA B' hB' hAB').1)
        have hL'_le : L_set'.card ≤ (B i).card :=
          card_family_le_card_ambient (fun A hA => ⟨(hL'_sub A hA).1, (hL'_sub A hA).2.1⟩)
            (fun A hA B' hB' hAB' => (hL'_pair A hA B' hB' hAB').1)
        have hL'_card : L_set'.card = L_set.card - 1 + k := by
          rw [Finset.card_union_of_disjoint h_disj_LU, Finset.card_erase_of_mem hW_mem,
            Finset.card_image_of_injective _ hU_inj, Finset.card_univ, Fintype.card_fin]
        have hW_pos : 1 ≤ L_set.card := Finset.card_pos.mpr ⟨W, hW_mem⟩
        exact ih L_set' (by omega) hL'_sub hL'_pair hL'_pot

/-- **Lemma 4.3 (`lem:gallai-core`)**:
Two-Tier Potential-Preserving Gallai Tree Decomposition inside Comb Blocks.
For any $\overline{P_6}$-free graph $G$, any $(\ell, w)$-comb $(a, B)$ in $G$ inside $S$
with $\ell \ge 4$ and $w \ge 1$ and external apex $v$, any $\theta \in (0, 1/4)$, and
$K_0 = \lfloor \theta^{-1} \rfloor \ge \ell^4$, for each block $B_i$ ($i \in \text{Fin } \ell$),
either:
1. **(Small-Attachment Core Outcome)**: $B_i$ contains a $\theta$-small-attachment core
   $M^* \subseteq B_i$ with $|M^*| \ge \frac{w}{2^{18} \ell^8}$; or
2. **(Bounded-Length Pure Blockade Outcome)**: $G[B_i]$ contains a pure
   $(k, \frac{w}{(4 k)^{16}})$-blockade for some integer $k \in [2, K_0]$ with
   $k \ge \frac{\ell^{1/2}}{2}$. -/
theorem gallai_tree_decomposition {G : SimpleGraph V} {S : Finset V} {ℓ : ℕ} {w : ℝ}
    {a : Fin ℓ → V} {B : Fin ℓ → Finset V} {v : V}
    (hG : IsInducedSubgraphFree G P6Compl)
    (hcomb : IsCombIn G S ℓ w a B)
    (hapex : IsCombExternalApex G S ℓ a B v)
    (hℓ : 4 ≤ ℓ) (hw : 1 ≤ w)
    (i : Fin ℓ) {θ : ℝ} {K₀ : ℕ}
    (hθ_pos : 0 < θ) (hK₀_ℓ : ℓ ^ 4 ≤ K₀) (hK₀_gt : θ⁻¹ < (K₀ : ℝ) + 1) :
    (∃ M_star ⊆ B i, w / ((2 : ℝ) ^ 18 * (ℓ : ℝ) ^ 8) ≤ (M_star.card : ℝ) ∧
      IsSmallAttachmentCore G B i θ M_star) ∨
    (∃ (k : ℕ) (U : Fin k → Finset V),
      2 ≤ k ∧ k ≤ K₀ ∧ (ℓ : ℝ) ^ (1 / 2 : ℝ) / 2 ≤ (k : ℝ) ∧
      IsPureBlockadeIn G (B i) k (w / (4 * (k : ℝ)) ^ 16) U) := by
  by_cases hw_small : w ≤ (2 : ℝ) ^ 18 * (ℓ : ℝ) ^ 8
  · left
    obtain ⟨z₀, hz₀⟩ := hcomb.is_blockade.nonempty_blocks i
    refine ⟨{z₀}, Finset.singleton_subset_iff.mpr hz₀, ?_, isSmallAttachmentCore_singleton hz₀⟩
    rw [Finset.card_singleton, Nat.cast_one]
    exact (div_le_one (by positivity)).mpr hw_small
  · push_neg at hw_small
    have hK₀_pos : (0 : ℝ) < (K₀ : ℝ) := by
      have : 1 ≤ K₀ := le_trans (by omega : 1 ≤ 4 ^ 4) (le_trans (Nat.pow_le_pow_left hℓ 4) hK₀_ℓ)
      exact Nat.cast_pos.mpr (by omega)
    have hBi_ge_w : w ≤ ((B i).card : ℝ) := hcomb.is_blockade.width_ge i
    have h_init_sub : ∀ A ∈ ({B i} : Finset (Finset V)),
        A ⊆ B i ∧ A.Nonempty ∧ w / (4 * (K₀ : ℝ)) ^ 16 ≤ (A.card : ℝ) := by
      intro A hA
      rw [Finset.mem_singleton.mp hA]
      refine ⟨Finset.Subset.rfl, hcomb.is_blockade.nonempty_blocks i, ?_⟩
      have h1 : (1 : ℝ) ≤ (4 * (K₀ : ℝ)) ^ 16 := by
        have : (1 : ℝ) ≤ 4 * (K₀ : ℝ) := by
          have : (1 : ℝ) ≤ (K₀ : ℝ) := by
            have : 1 ≤ K₀ := le_trans (by omega : 1 ≤ 4 ^ 4) (le_trans (Nat.pow_le_pow_left hℓ 4) hK₀_ℓ)
            exact Nat.one_le_cast.mpr this
          linarith
        exact one_le_pow₀ this
      exact le_trans (div_le_self (by linarith) h1) hBi_ge_w
    have h_init_pair : ∀ A ∈ ({B i} : Finset (Finset V)), ∀ B' ∈ ({B i} : Finset (Finset V)),
        A ≠ B' → Disjoint A B' ∧ IsPurePair G A B' := by
      intro A hA B' hB' hne
      rw [Finset.mem_singleton.mp hA, Finset.mem_singleton.mp hB'] at hne
      exact False.elim (hne rfl)
    have h_init_pot : w ^ (1 / 8 : ℝ) ≤
        ∑ A ∈ ({B i} : Finset (Finset V)), (A.card : ℝ) ^ (1 / 8 : ℝ) := by
      rw [Finset.sum_singleton]
      exact Real.rpow_le_rpow (by linarith) hBi_ge_w (by positivity)
    obtain ⟨L_term, hL_sub, hL_pair, hL_pot, hL_term⟩ :=
      gallai_tree_refinement_aux hG hcomb hapex hℓ hw_small hθ_pos hK₀_ℓ hK₀_gt
        ((B i).card - 1) {B i} (by simp) h_init_sub h_init_pair h_init_pot
    by_cases h_out1 : ∃ A ∈ L_term,
        (∃ M_star ⊆ A, (A.card : ℝ) / 4 ≤ (M_star.card : ℝ) ∧
          IsSmallAttachmentCore G B i θ M_star) ∧
        w / ((2 : ℝ) ^ 16 * (ℓ : ℝ) ^ 8) ≤ (A.card : ℝ)
    · left
      obtain ⟨A, hA_mem, ⟨M_star, hMA, hM_card, hM_core⟩, hA_ge⟩ := h_out1
      refine ⟨M_star, hMA.trans (hL_sub A hA_mem).1, ?_, hM_core⟩
      have h_eq : w / ((2 : ℝ) ^ 18 * (ℓ : ℝ) ^ 8) = (w / ((2 : ℝ) ^ 16 * (ℓ : ℝ) ^ 8)) / 4 := by ring
      linarith
    · right
      push_neg at h_out1
      have h_all_small : ∀ A ∈ L_term, (A.card : ℝ) < w / (ℓ : ℝ) ^ 8 := by
        intro A hA
        rcases hL_term A hA with h_core | h_lt
        · have h1 := h_out1 A hA h_core
          have h2 : w / ((2 : ℝ) ^ 16 * (ℓ : ℝ) ^ 8) ≤ w / (ℓ : ℝ) ^ 8 := by
            refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
            have : (1 : ℝ) ≤ (2 : ℝ) ^ 16 := by norm_num
            nlinarith [show (0 : ℝ) < (ℓ : ℝ) ^ 8 by positivity]
          linarith
        · exact h_lt
      obtain ⟨q, L, _, hL_inj, hL_img, hL_mem, _, hL_mono⟩ := exists_sorted_equiv_of_finset L_term
      have hL_pot_fin : w ^ (1 / 8 : ℝ) ≤ ∑ j : Fin q, ((L j).card : ℝ) ^ (1 / 8 : ℝ) := by
        rw [← Finset.sum_image (f := fun A : Finset V => (A.card : ℝ) ^ (1 / 8 : ℝ))
          (fun j₁ _ j₂ _ h => hL_inj h), hL_img]
        exact hL_pot
      have hL_rpow_lt : ∀ j : Fin q, ((L j).card : ℝ) ^ (1 / 8 : ℝ) ≤ w ^ (1 / 8 : ℝ) / (ℓ : ℝ) := by
        intro j
        refine le_of_lt (rpow_one_eighth_lt_of_lt_pow (Nat.cast_nonneg _) (by positivity) ?_)
        rw [div_pow]
        have hw8 : (w ^ (1 / 8 : ℝ)) ^ 8 = w := by
          rw [← Real.rpow_natCast, show ((8 : ℕ) : ℝ) = 8 by norm_num,
            ← Real.rpow_mul (by linarith), show (1 / 8 : ℝ) * 8 = 1 by norm_num, Real.rpow_one]
        rw [hw8]
        exact h_all_small (L j) (hL_mem j)
      let p : ℕ := ⌊(ℓ : ℝ) ^ (1 / 2 : ℝ) / 2⌋₊
      have hℓ_r : (4 : ℝ) ≤ (ℓ : ℝ) := Nat.ofNat_le_cast.mpr hℓ
      have h_sqrt_sq : ((ℓ : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = (ℓ : ℝ) := by
        rw [← Real.rpow_natCast, show ((2 : ℕ) : ℝ) = 2 by norm_num,
          ← Real.rpow_mul (by positivity), show (1 / 2 : ℝ) * 2 = 1 by norm_num, Real.rpow_one]
      have h_sqrt_pos : (0 : ℝ) ≤ (ℓ : ℝ) ^ (1 / 2 : ℝ) := by positivity
      have h_sqrt_ge : (2 : ℝ) ≤ (ℓ : ℝ) ^ (1 / 2 : ℝ) := by nlinarith
      have h_sqrt_le : (ℓ : ℝ) ^ (1 / 2 : ℝ) ≤ (ℓ : ℝ) / 2 := by nlinarith
      have hp_ge_1 : 1 ≤ p := Nat.le_floor (by norm_num; linarith)
      have hp_le_quarter : (p : ℝ) ≤ (ℓ : ℝ) / 4 := by
        have hp_le : (p : ℝ) ≤ (ℓ : ℝ) ^ (1 / 2 : ℝ) / 2 := Nat.floor_le (by positivity)
        linarith
      let f : ℕ → ℝ := fun k =>
        if h : 1 ≤ k ∧ k ≤ q then ((L ⟨k - 1, by omega⟩).card : ℝ) ^ (1 / 8 : ℝ) else 0
      have hf_sum : w ^ (1 / 8 : ℝ) ≤ ∑ k ∈ Finset.Icc 1 q, f k := by
        rw [← sum_fin_eq_sum_Icc q (fun j => ((L j).card : ℝ) ^ (1 / 8 : ℝ))]
        exact hL_pot_fin
      have hf_le : ∀ k, f k ≤ w ^ (1 / 8 : ℝ) / (ℓ : ℝ) := by
        intro k
        unfold f
        split_ifs with h
        · exact hL_rpow_lt ⟨k - 1, by omega⟩
        · positivity
      have hp_sum : ∑ k ∈ Finset.Icc 1 p, f k ≤ (1 / 4 : ℝ) * w ^ (1 / 8 : ℝ) := by
        calc ∑ k ∈ Finset.Icc 1 p, f k
            ≤ ∑ _k ∈ Finset.Icc 1 p, (w ^ (1 / 8 : ℝ) / (ℓ : ℝ)) :=
              Finset.sum_le_sum (fun k _ => hf_le k)
          _ = (p : ℝ) * (w ^ (1 / 8 : ℝ) / (ℓ : ℝ)) := by
              rw [Finset.sum_const, Nat.card_Icc, show p + 1 - 1 = p by omega, nsmul_eq_mul]
          _ ≤ ((ℓ : ℝ) / 4) * (w ^ (1 / 8 : ℝ) / (ℓ : ℝ)) :=
              mul_le_mul_of_nonneg_right hp_le_quarter (by positivity)
          _ = (1 / 4 : ℝ) * w ^ (1 / 8 : ℝ) := by
              field_simp
      have hpq : p ≤ q := by
        by_contra hlt
        push_neg at hlt
        have hsub : Finset.Icc 1 q ⊆ Finset.Icc 1 p := Finset.Icc_subset_Icc le_rfl (by omega)
        have h1 : ∑ k ∈ Finset.Icc 1 q, f k ≤ ∑ k ∈ Finset.Icc 1 p, f k :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by unfold f; split_ifs <;> positivity)
        have hw8_pos : (0 : ℝ) < w ^ (1 / 8 : ℝ) := by positivity
        linarith
      have h_tail_sum : (1 / 2 : ℝ) * w ^ (1 / 8 : ℝ) ≤ ∑ k ∈ Finset.Icc (p + 1) q, f k := by
        have h_sp := sum_Icc_split p q hpq f
        have hw8_pos : (0 : ℝ) < w ^ (1 / 8 : ℝ) := by positivity
        linarith
      obtain ⟨k₀, hk₀_mem, hk₀_ge⟩ :=
        cauchy_series_extraction p q f ((1 / 2 : ℝ) * w ^ (1 / 8 : ℝ)) (by positivity) h_tail_sum
      obtain ⟨hk₀_low, hk₀_high⟩ := Finset.mem_Icc.mp hk₀_mem
      have hk₀_pos : 0 < k₀ := by omega
      have hk₀_1 : 1 ≤ k₀ ∧ k₀ ≤ q := ⟨by omega, hk₀_high⟩
      unfold f at hk₀_ge
      rw [dif_pos hk₀_1] at hk₀_ge
      have hk₀_width : w / (4 * (k₀ : ℝ)) ^ 16 ≤ ((L ⟨k₀ - 1, by omega⟩).card : ℝ) := by
        have h1 : w ^ (1 / 8 : ℝ) / (4 * (k₀ : ℝ)) ^ 2 ≤ ((L ⟨k₀ - 1, by omega⟩).card : ℝ) ^ (1 / 8 : ℝ) := by
          have h_pos : (0 : ℝ) < (k₀ : ℝ) ^ 2 := by positivity
          have h_le : w ^ (1 / 8 : ℝ) / (4 * (k₀ : ℝ)) ^ 2 ≤
              ((1 / 2 : ℝ) * w ^ (1 / 8 : ℝ)) / (2 * (k₀ : ℝ) ^ 2) := by
            rw [show (4 * (k₀ : ℝ)) ^ 2 = 16 * (k₀ : ℝ) ^ 2 by ring,
              show ((1 / 2 : ℝ) * w ^ (1 / 8 : ℝ)) / (2 * (k₀ : ℝ) ^ 2) =
                w ^ (1 / 8 : ℝ) / (4 * (k₀ : ℝ) ^ 2) by ring]
            exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
          exact le_trans h_le hk₀_ge
        have h2 := pow_le_pow_left₀ (by positivity) h1 8
        have h_lhs : (w ^ (1 / 8 : ℝ) / (4 * (k₀ : ℝ)) ^ 2) ^ 8 = w / (4 * (k₀ : ℝ)) ^ 16 := by
          rw [div_pow, show ((4 * (k₀ : ℝ)) ^ 2) ^ 8 = (4 * (k₀ : ℝ)) ^ 16 by ring]
          congr 1
          rw [← Real.rpow_natCast, show ((8 : ℕ) : ℝ) = 8 by norm_num,
            ← Real.rpow_mul (by linarith), show (1 / 8 : ℝ) * 8 = 1 by norm_num, Real.rpow_one]
        have h_rhs : (((L ⟨k₀ - 1, by omega⟩).card : ℝ) ^ (1 / 8 : ℝ)) ^ 8 =
            ((L ⟨k₀ - 1, by omega⟩).card : ℝ) := by
          rw [← Real.rpow_natCast, show ((8 : ℕ) : ℝ) = 8 by norm_num,
            ← Real.rpow_mul (Nat.cast_nonneg _), show (1 / 8 : ℝ) * 8 = 1 by norm_num, Real.rpow_one]
        rwa [h_lhs, h_rhs] at h2
      let k := min k₀ K₀
      have hk_2 : 2 ≤ k := by
        have : 4 ≤ K₀ := le_trans (by omega : 4 ≤ 4 ^ 4) (le_trans (Nat.pow_le_pow_left hℓ 4) hK₀_ℓ)
        omega
      have hk_K₀ : k ≤ K₀ := Nat.min_le_right k₀ K₀
      have hk_q : k ≤ q := le_trans (Nat.min_le_left k₀ K₀) hk₀_high
      have hk_sqrt : (ℓ : ℝ) ^ (1 / 2 : ℝ) / 2 ≤ (k : ℝ) := by
        have h_p1 : (ℓ : ℝ) ^ (1 / 2 : ℝ) / 2 ≤ ((p + 1 : ℕ) : ℝ) := by
          rw [Nat.cast_add, Nat.cast_one]
          exact le_of_lt (Nat.lt_floor_add_one _)
        have h_k₀_ge : (ℓ : ℝ) ^ (1 / 2 : ℝ) / 2 ≤ (k₀ : ℝ) :=
          le_trans h_p1 (Nat.cast_le.mpr hk₀_low)
        have h_K₀_ge : (ℓ : ℝ) ^ (1 / 2 : ℝ) / 2 ≤ (K₀ : ℝ) := by
          have : (ℓ : ℝ) ≤ (K₀ : ℝ) := by
            have : ℓ ≤ K₀ := le_trans (Nat.le_self_pow (by omega) ℓ) hK₀_ℓ
            exact Nat.cast_le.mpr this
          linarith
        rcases min_cases k₀ K₀ with ⟨h_eq, _⟩ | ⟨h_eq, _⟩ <;>
          { unfold k; rw [h_eq]; exact_mod_cast (by assumption : _ ≤ _) }
      let U : Fin k → Finset V := fun j => L ⟨j.1, by omega⟩
      refine ⟨k, U, hk_2, hk_K₀, hk_sqrt, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · intro j; exact (hL_sub (U j) (hL_mem ⟨j.1, by omega⟩)).1
      · intro j; exact (hL_sub (U j) (hL_mem ⟨j.1, by omega⟩)).2.1
      · intro j₁ j₂ hj
        have hj' : (⟨j₁.1, by omega⟩ : Fin q) ≠ ⟨j₂.1, by omega⟩ := by
          intro h; apply hj; ext; exact Fin.mk.inj_iff.mp h
        exact (hL_pair (U j₁) (hL_mem _) (U j₂) (hL_mem _) (fun h => hj' (hL_inj h))).1
      · intro j
        by_cases hk₀_le : k₀ ≤ K₀
        · have hk_eq : k = k₀ := Nat.min_eq_left hk₀_le
          have hj_le : (⟨j.1, by omega⟩ : Fin q) ≤ ⟨k₀ - 1, by omega⟩ := by
            simp only [Fin.mk_le_mk]
            omega
          have h_mono : ((L ⟨k₀ - 1, by omega⟩).card : ℝ) ≤ ((U j).card : ℝ) :=
            Nat.cast_le.mpr (hL_mono ⟨j.1, by omega⟩ ⟨k₀ - 1, by omega⟩ hj_le)
          rw [hk_eq]
          exact le_trans hk₀_width h_mono
        · have hk_eq : k = K₀ := Nat.min_eq_right (by omega)
          rw [hk_eq]
          exact (hL_sub (U j) (hL_mem ⟨j.1, by omega⟩)).2.2
      · intro j₁ j₂ hj
        have hj' : (⟨j₁.1, by omega⟩ : Fin q) ≠ ⟨j₂.1, by omega⟩ := by
          intro h; apply hj; ext; exact Fin.mk.inj_iff.mp h
        exact (hL_pair (U j₁) (hL_mem _) (U j₂) (hL_mem _) (fun h => hj' (hL_inj h))).2

/-! ## Part 4: Parameter-Free Upside-Down Comb Dichotomy (Proposition 4.4 `prop:comb-dichotomy`) -/

/-- If $0 \le b$, $0 < n$, and $a^n \le b^n$, then $a \le b$. -/
lemma le_of_pow_le_pow {a b : ℝ} {n : ℕ} (hb : 0 ≤ b) (hn : 0 < n) (h : a ^ n ≤ b ^ n) :
    a ≤ b := by
  by_contra hlt
  push_neg at hlt
  have h1 : b ^ n < a ^ n := pow_lt_pow_left₀ hlt hb (by omega)
  linarith

/-- Every pure pair in $G$ is a fortiori a complete-or-$x$-sparse pair in $G$ for any $x \ge 0$. -/
lemma isCompleteOrXSparsePair_of_isPurePair {G : SimpleGraph V} {A B : Finset V} {x : ℝ}
    (hx : 0 ≤ x) (h : IsPurePair G A B) :
    IsCompleteOrXSparsePair G A B x := by
  rcases h with h_comp | h_anti
  · exact Or.inl h_comp
  · refine Or.inr ⟨fun v hv => ?_, fun u hu => ?_⟩
    · have h_empty : neighborFinsetIn G v A = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro a ha
        obtain ⟨haA, hadj⟩ := Finset.mem_filter.mp ha
        exact h_anti a haA v hv (G.symm hadj)
      rw [h_empty, Finset.card_empty, Nat.cast_zero]
      positivity
    · have h_empty : neighborFinsetIn G u B = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro b hb
        obtain ⟨hbB, hadj⟩ := Finset.mem_filter.mp hb
        exact h_anti u hu b hbB hadj
      rw [h_empty, Finset.card_empty, Nat.cast_zero]
      positivity

/-- Parameter calibration bounds for Proposition 4.4 (`prop:comb-dichotomy`). -/
lemma comb_parameter_bounds {ℓ : ℕ} {x y : ℝ}
    (hx_pos : 0 < x) (hxy : x ≤ y) (hy_max : y ≤ (2 : ℝ) ^ (-8 : ℝ))
    (hℓ_low : y ^ (-1 / 4 : ℝ) ≤ (ℓ : ℝ)) (hℓ_high : (ℓ : ℝ) ≤ x ^ (-2 : ℝ)) :
    let θ := x ^ 3 / (16 * (ℓ : ℝ) ^ 3)
    let K₀ := ⌊θ⁻¹⌋₊
    4 ≤ ℓ ∧ x ≤ 1 / 256 ∧ 0 < θ ∧ ℓ ^ 4 ≤ K₀ ∧ θ⁻¹ < (K₀ : ℝ) + 1 ∧
      (K₀ : ℝ) ≤ x ^ (-10 : ℝ) ∧ (ℓ : ℝ) ≤ x ^ (-10 : ℝ) ∧
      (ℓ : ℝ) ^ (1 / 2 : ℝ) / 2 ≤ (ℓ : ℝ) := by
  intro θ K₀
  have hy_pos : 0 < y := lt_of_lt_of_le hx_pos hxy
  have hy_256 : y ≤ 1 / 256 := by
    have h28 : (2 : ℝ) ^ (-8 : ℝ) ≤ 1 / 256 := by norm_num
    exact le_trans hy_max h28
  have hx_256 : x ≤ 1 / 256 := le_trans hxy hy_256
  have hy_rpow4 : (y ^ (-1 / 4 : ℝ)) ^ 4 = y⁻¹ := by
    rw [← Real.rpow_natCast, show ((4 : ℕ) : ℝ) = 4 by norm_num,
      ← Real.rpow_mul (by positivity), show (-1 / 4 : ℝ) * 4 = -1 by norm_num, Real.rpow_neg_one]
  have hy_inv_ge : (4 : ℝ) ^ 4 ≤ y⁻¹ := by
    have h1 : y * y⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hy_pos)
    have h2 : (4 : ℝ) ^ 4 = 256 := by norm_num
    have h3 : y * 256 ≤ 1 := by linarith
    have h4 : y * 256 ≤ y * y⁻¹ := by linarith
    exact le_of_mul_le_mul_left (by rwa [h2]) hy_pos
  have h4_le_y : (4 : ℝ) ≤ y ^ (-1 / 4 : ℝ) := by
    refine le_of_pow_le_pow (by positivity) (by omega : 0 < 4) ?_
    rw [hy_rpow4]
    exact hy_inv_ge
  have hℓ_r : (4 : ℝ) ≤ (ℓ : ℝ) := le_trans h4_le_y hℓ_low
  have hℓ : 4 ≤ ℓ := by exact_mod_cast hℓ_r
  have hθ_pos : 0 < θ := by unfold θ; positivity
  have hx_neg2 : x ^ (-2 : ℝ) = (x ^ 2)⁻¹ := by
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by positivity), Real.rpow_natCast]
  have hx_neg10 : x ^ (-10 : ℝ) = (x ^ 10)⁻¹ := by
    rw [show (-10 : ℝ) = -((10 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by positivity), Real.rpow_natCast]
  have hℓ_x2 : (ℓ : ℝ) * x ^ 2 ≤ 1 := by
    have h1 : (ℓ : ℝ) ≤ (x ^ 2)⁻¹ := by rwa [← hx_neg2]
    have h2 := mul_le_mul_of_nonneg_right h1 (show (0 : ℝ) ≤ x ^ 2 by positivity)
    rwa [inv_mul_cancel₀ (by positivity)] at h2
  have hK₀_ℓ : ℓ ^ 4 ≤ K₀ := by
    refine Nat.le_floor ?_
    rw [Nat.cast_pow]
    unfold θ
    rw [inv_div, le_div_iff₀ (by positivity)]
    have hx3_le_x2 : x ^ 3 ≤ x ^ 2 := by nlinarith
    have h1 : (ℓ : ℝ) * x ^ 3 ≤ 1 := by
      calc (ℓ : ℝ) * x ^ 3 ≤ (ℓ : ℝ) * x ^ 2 := mul_le_mul_of_nonneg_left hx3_le_x2 (by positivity)
        _ ≤ 1 := hℓ_x2
    calc (ℓ : ℝ) ^ 4 * x ^ 3 = (ℓ : ℝ) ^ 3 * ((ℓ : ℝ) * x ^ 3) := by ring
      _ ≤ (ℓ : ℝ) ^ 3 * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 16 * (ℓ : ℝ) ^ 3 := by linarith [show (0 : ℝ) < (ℓ : ℝ) ^ 3 by positivity]
  have hK₀_gt : θ⁻¹ < (K₀ : ℝ) + 1 := Nat.lt_floor_add_one θ⁻¹
  have hK₀_max : (K₀ : ℝ) ≤ x ^ (-10 : ℝ) := by
    have h1 : (K₀ : ℝ) ≤ θ⁻¹ := Nat.floor_le (by positivity)
    refine le_trans h1 ?_
    unfold θ
    rw [inv_div, hx_neg10, div_le_iff₀ (by positivity)]
    have h2 : ((ℓ : ℝ) * x ^ 2) ^ 3 ≤ 1 ^ 3 := pow_le_pow_left₀ (by positivity) hℓ_x2 3
    have h3 : (ℓ : ℝ) ^ 3 * x ^ 6 ≤ 1 := by
      linarith [show ((ℓ : ℝ) * x ^ 2) ^ 3 = (ℓ : ℝ) ^ 3 * x ^ 6 by ring]
    have h4 : 16 * x ≤ 1 := by linarith
    have h5 : (16 * x) * ((ℓ : ℝ) ^ 3 * x ^ 6) ≤ 1 * 1 :=
      mul_le_mul h4 h3 (by positivity) (by positivity)
    have h6 : 16 * (ℓ : ℝ) ^ 3 * x ^ 7 ≤ 1 := by
      linarith [show (16 * x) * ((ℓ : ℝ) ^ 3 * x ^ 6) = 16 * (ℓ : ℝ) ^ 3 * x ^ 7 by ring]
    have h_id : (16 * (ℓ : ℝ) ^ 3 * x ^ 7) * ((x ^ 10)⁻¹ * x ^ 3) =
        16 * (ℓ : ℝ) ^ 3 * ((x ^ 10)⁻¹ * x ^ 10) := by ring
    rw [inv_mul_cancel₀ (by positivity), mul_one] at h_id
    calc 16 * (ℓ : ℝ) ^ 3
        = (16 * (ℓ : ℝ) ^ 3 * x ^ 7) * ((x ^ 10)⁻¹ * x ^ 3) := h_id.symm
      _ ≤ 1 * ((x ^ 10)⁻¹ * x ^ 3) := mul_le_mul_of_nonneg_right h6 (by positivity)
      _ = (x ^ 10)⁻¹ * x ^ 3 := one_mul _
  have hℓ_max : (ℓ : ℝ) ≤ x ^ (-10 : ℝ) := by
    have : (ℓ : ℝ) ≤ (K₀ : ℝ) := by
      have : ℓ ≤ K₀ := le_trans (Nat.le_self_pow (by omega) ℓ) hK₀_ℓ
      exact Nat.cast_le.mpr this
    exact le_trans this hK₀_max
  have hℓ_sqrt : (ℓ : ℝ) ^ (1 / 2 : ℝ) / 2 ≤ (ℓ : ℝ) := by
    have h_sqrt_sq : ((ℓ : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = (ℓ : ℝ) := by
      rw [← Real.rpow_natCast, show ((2 : ℕ) : ℝ) = 2 by norm_num,
        ← Real.rpow_mul (by positivity), show (1 / 2 : ℝ) * 2 = 1 by norm_num, Real.rpow_one]
    have h_sqrt_pos : (0 : ℝ) ≤ (ℓ : ℝ) ^ (1 / 2 : ℝ) := by positivity
    nlinarith
  exact ⟨hℓ, hx_256, hθ_pos, hK₀_ℓ, hK₀_gt, hK₀_max, hℓ_max, hℓ_sqrt⟩

/-- Width bound for Case 1 of Proposition 4.4 (`prop:comb-dichotomy`). -/
lemma case_6_1_width_bound {ℓ k : ℕ} {S_card w' : ℝ}
    (hS_nonneg : 0 ≤ S_card) (hℓ : 4 ≤ ℓ) (hk2 : 2 ≤ k)
    (hk_sqrt : (ℓ : ℝ) ^ (1 / 2 : ℝ) / 2 ≤ (k : ℝ))
    (hw'_ge : S_card / (ℓ : ℝ) ^ 18 ≤ w') :
    S_card / (k : ℝ) ^ 120 ≤ w' / (4 * (k : ℝ)) ^ 16 := by
  have hℓ_pos : 0 < ℓ := by omega
  have hk_pos : 0 < k := by omega
  have hk_r : (2 : ℝ) ≤ (k : ℝ) := Nat.ofNat_le_cast.mpr hk2
  have hk2_4 : (4 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have h_sqrt_sq : ((ℓ : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = (ℓ : ℝ) := by
    rw [← Real.rpow_natCast, show ((2 : ℕ) : ℝ) = 2 by norm_num,
      ← Real.rpow_mul (by positivity), show (1 / 2 : ℝ) * 2 = 1 by norm_num, Real.rpow_one]
  have hℓ_le_4k2 : (ℓ : ℝ) ≤ 4 * (k : ℝ) ^ 2 := by
    have h1 := pow_le_pow_left₀ (by positivity) hk_sqrt 2
    nlinarith
  have h4k2_k4 : 4 * (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 4 := by
    calc 4 * (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 * (k : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hk2_4 (by positivity)
      _ = (k : ℝ) ^ 4 := by ring
  have hℓ_le_k4 : (ℓ : ℝ) ≤ (k : ℝ) ^ 4 := le_trans hℓ_le_4k2 h4k2_k4
  have h4k_le_k3 : 4 * (k : ℝ) ≤ (k : ℝ) ^ 3 := by
    calc 4 * (k : ℝ) ≤ (k : ℝ) ^ 2 * (k : ℝ) :=
          mul_le_mul_of_nonneg_right hk2_4 (by positivity)
      _ = (k : ℝ) ^ 3 := by ring
  have h1 : (ℓ : ℝ) ^ 18 ≤ ((k : ℝ) ^ 4) ^ 18 := pow_le_pow_left₀ (by positivity) hℓ_le_k4 18
  have h2 : (4 * (k : ℝ)) ^ 16 ≤ ((k : ℝ) ^ 3) ^ 16 := pow_le_pow_left₀ (by positivity) h4k_le_k3 16
  have h3 : (ℓ : ℝ) ^ 18 * (4 * (k : ℝ)) ^ 16 ≤ (k : ℝ) ^ 120 := by
    calc (ℓ : ℝ) ^ 18 * (4 * (k : ℝ)) ^ 16
        ≤ ((k : ℝ) ^ 4) ^ 18 * ((k : ℝ) ^ 3) ^ 16 :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (k : ℝ) ^ 120 := by ring
  calc S_card / (k : ℝ) ^ 120
      ≤ S_card / ((ℓ : ℝ) ^ 18 * (4 * (k : ℝ)) ^ 16) :=
        div_le_div_of_nonneg_left hS_nonneg (by positivity) h3
    _ = (S_card / (ℓ : ℝ) ^ 18) / (4 * (k : ℝ)) ^ 16 := by ring
    _ ≤ w' / (4 * (k : ℝ)) ^ 16 :=
        div_le_div_of_nonneg_right hw'_ge (by positivity)

/-- Width bound for Subcase 2a of Proposition 4.4 (`prop:comb-dichotomy`). -/
lemma subcase_6_2a_width_bound {ℓ k₀ : ℕ} {x S_card w' M_card : ℝ}
    (hS_nonneg : 0 ≤ S_card) (hx_pos : 0 < x) (hx_max : x ≤ 1 / 256)
    (hℓ : 4 ≤ ℓ) (hℓ_high : (ℓ : ℝ) ≤ x ^ (-2 : ℝ))
    (hk₀_gt : x ^ (-2 : ℝ) < (k₀ : ℝ))
    (hw'_ge : S_card / (ℓ : ℝ) ^ 18 ≤ w')
    (hM_card : w' / ((2 : ℝ) ^ 18 * (ℓ : ℝ) ^ 8) ≤ M_card) :
    S_card / (k₀ : ℝ) ^ 120 ≤ (x / (4 * (ℓ : ℝ)) * M_card) / (2 * (k₀ : ℝ) ^ 2) := by
  have hℓ_r : (4 : ℝ) ≤ (ℓ : ℝ) := Nat.ofNat_le_cast.mpr hℓ
  have hℓ_le_k₀ : (ℓ : ℝ) ≤ (k₀ : ℝ) := le_of_lt (lt_of_le_of_lt hℓ_high hk₀_gt)
  have hk₀_ge_2 : (2 : ℝ) ≤ (k₀ : ℝ) := by linarith
  have hx_neg2 : x ^ (-2 : ℝ) = (x ^ 2)⁻¹ := by
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by positivity), Real.rpow_natCast]
  have h_one_le_xk₀ : 1 ≤ x * (k₀ : ℝ) := by
    have h1 : (x ^ 2)⁻¹ ≤ (k₀ : ℝ) := le_of_lt (by rwa [← hx_neg2])
    have h2 : 1 ≤ x ^ 2 * (k₀ : ℝ) := by
      have := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ x ^ 2 by positivity)
      rwa [mul_inv_cancel₀ (by positivity)] at this
    have h3 : x ^ 2 ≤ x := by nlinarith
    have h4 : x ^ 2 * (k₀ : ℝ) ≤ x * (k₀ : ℝ) := mul_le_mul_of_nonneg_right h3 (by positivity)
    exact le_trans h2 h4
  have hM_nonneg : 0 ≤ M_card := by
    have : 0 ≤ S_card / (ℓ : ℝ) ^ 18 := by positivity
    have : 0 ≤ w' := le_trans this hw'_ge
    have : 0 ≤ w' / ((2 : ℝ) ^ 18 * (ℓ : ℝ) ^ 8) := by positivity
    exact le_trans this hM_card
  have hM_ge_S : S_card / ((2 : ℝ) ^ 18 * (ℓ : ℝ) ^ 26) ≤ M_card := by
    calc S_card / ((2 : ℝ) ^ 18 * (ℓ : ℝ) ^ 26)
        = (S_card / (ℓ : ℝ) ^ 18) / ((2 : ℝ) ^ 18 * (ℓ : ℝ) ^ 8) := by ring
      _ ≤ w' / ((2 : ℝ) ^ 18 * (ℓ : ℝ) ^ 8) :=
          div_le_div_of_nonneg_right hw'_ge (by positivity)
      _ ≤ M_card := hM_card
  have h_denom : (2 : ℝ) ^ 18 * (ℓ : ℝ) ^ 26 * (8 * (ℓ : ℝ) * (k₀ : ℝ) ^ 3) ≤ (k₀ : ℝ) ^ 120 := by
    have h2_k₀ : (2 : ℝ) ^ 21 ≤ (k₀ : ℝ) ^ 21 := pow_le_pow_left₀ (by positivity) hk₀_ge_2 21
    have hℓ_k₀ : (ℓ : ℝ) ^ 27 ≤ (k₀ : ℝ) ^ 27 := pow_le_pow_left₀ (by positivity) hℓ_le_k₀ 27
    calc (2 : ℝ) ^ 18 * (ℓ : ℝ) ^ 26 * (8 * (ℓ : ℝ) * (k₀ : ℝ) ^ 3)
        = (2 : ℝ) ^ 21 * (ℓ : ℝ) ^ 27 * (k₀ : ℝ) ^ 3 := by ring
      _ ≤ (k₀ : ℝ) ^ 21 * (k₀ : ℝ) ^ 27 * (k₀ : ℝ) ^ 3 :=
          mul_le_mul_of_nonneg_right (mul_le_mul h2_k₀ hℓ_k₀ (by positivity) (by positivity))
            (by positivity)
      _ = (k₀ : ℝ) ^ 51 := by ring
      _ ≤ (k₀ : ℝ) ^ 120 := pow_le_pow_right₀ (by linarith) (by omega)
  calc S_card / (k₀ : ℝ) ^ 120
      ≤ S_card / ((2 : ℝ) ^ 18 * (ℓ : ℝ) ^ 26 * (8 * (ℓ : ℝ) * (k₀ : ℝ) ^ 3)) :=
        div_le_div_of_nonneg_left hS_nonneg (by positivity) h_denom
    _ = (S_card / ((2 : ℝ) ^ 18 * (ℓ : ℝ) ^ 26)) / (8 * (ℓ : ℝ) * (k₀ : ℝ) ^ 3) := by ring
    _ ≤ (1 * M_card) / (8 * (ℓ : ℝ) * (k₀ : ℝ) ^ 3) := by
        rw [one_mul]
        exact div_le_div_of_nonneg_right hM_ge_S (by positivity)
    _ ≤ ((x * (k₀ : ℝ)) * M_card) / (8 * (ℓ : ℝ) * (k₀ : ℝ) ^ 3) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h_one_le_xk₀ hM_nonneg) (by positivity)
    _ = (k₀ : ℝ) / (k₀ : ℝ) * ((x / (4 * (ℓ : ℝ)) * M_card) / (2 * (k₀ : ℝ) ^ 2)) := by ring
    _ = (x / (4 * (ℓ : ℝ)) * M_card) / (2 * (k₀ : ℝ) ^ 2) := by
        rw [div_self (by linarith), one_mul]

/-- Width bound for Subcase 2b of Proposition 4.4 (`prop:comb-dichotomy`). -/
lemma subcase_6_2b_width_bound {ℓ : ℕ} {S_card w' M_card D_card : ℝ}
    (hS_nonneg : 0 ≤ S_card) (hℓ : 4 ≤ ℓ)
    (hw'_ge : S_card / (ℓ : ℝ) ^ 18 ≤ w')
    (hM_card : w' / ((2 : ℝ) ^ 18 * (ℓ : ℝ) ^ 8) ≤ M_card)
    (hD_card : M_card / 2 ≤ D_card) :
    S_card / (ℓ : ℝ) ^ 120 ≤ D_card := by
  have hℓ_r : (4 : ℝ) ≤ (ℓ : ℝ) := Nat.ofNat_le_cast.mpr hℓ
  have h2_le_ℓ : (2 : ℝ) ≤ (ℓ : ℝ) := by linarith
  have h_denom : (2 : ℝ) ^ 19 * (ℓ : ℝ) ^ 26 ≤ (ℓ : ℝ) ^ 120 := by
    have h1 : (2 : ℝ) ^ 19 ≤ (ℓ : ℝ) ^ 19 := pow_le_pow_left₀ (by positivity) h2_le_ℓ 19
    calc (2 : ℝ) ^ 19 * (ℓ : ℝ) ^ 26
        ≤ (ℓ : ℝ) ^ 19 * (ℓ : ℝ) ^ 26 := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (ℓ : ℝ) ^ 45 := by ring
      _ ≤ (ℓ : ℝ) ^ 120 := pow_le_pow_right₀ (by linarith) (by omega)
  calc S_card / (ℓ : ℝ) ^ 120
      ≤ S_card / ((2 : ℝ) ^ 19 * (ℓ : ℝ) ^ 26) :=
        div_le_div_of_nonneg_left hS_nonneg (by positivity) h_denom
    _ = ((S_card / (ℓ : ℝ) ^ 18) / ((2 : ℝ) ^ 18 * (ℓ : ℝ) ^ 8)) / 2 := by ring
    _ ≤ (w' / ((2 : ℝ) ^ 18 * (ℓ : ℝ) ^ 8)) / 2 :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hw'_ge (by positivity)) (by positivity)
    _ ≤ M_card / 2 := div_le_div_of_nonneg_right hM_card (by positivity)
    _ ≤ D_card := hD_card

/-- Subcase 2a of Proposition 4.4 (`prop:comb-dichotomy`): dense incomplete attachment yields a long
complete blockade via Cauchy series extraction. -/
lemma comb_dichotomy_subcase_6_2a {G : SimpleGraph V} {S : Finset V} {ℓ : ℕ} {w' x : ℝ}
    {B M_star : Fin ℓ → Finset V}
    (hx_pos : 0 < x) (hx_256 : x ≤ 1 / 256) (hℓ : 4 ≤ ℓ) (hℓ_high : (ℓ : ℝ) ≤ x ^ (-2 : ℝ))
    (hw'_ge : (S.card : ℝ) / (ℓ : ℝ) ^ 18 ≤ w')
    (hB_sub : ∀ i, B i ⊆ S)
    (hM_sub : ∀ i, M_star i ⊆ B i)
    (hM_card : ∀ i, w' / ((2 : ℝ) ^ 18 * (ℓ : ℝ) ^ 8) ≤ ((M_star i).card : ℝ))
    (hM_core : ∀ i, IsSmallAttachmentCore G B i (x ^ 3 / (16 * (ℓ : ℝ) ^ 3)) (M_star i))
    {i j : Fin ℓ} (hji : j ≠ i) {u : V} (hu_Mj : u ∈ M_star j)
    (hu_not_comp : ¬∀ z ∈ M_star i, G.Adj u z)
    (hu_deg : x / (2 * (ℓ : ℝ)) * ((M_star i).card : ℝ) ≤ ((neighborFinsetIn G u (M_star i)).card : ℝ)) :
    ∃ (k : ℕ) (D : Fin k → Finset V),
      x ^ (-2 : ℝ) < (k : ℝ) ∧
      IsCompleteBlockadeIn G S k ((S.card : ℝ) / (k : ℝ) ^ 120) D := by
  let θ : ℝ := x ^ 3 / (16 * (ℓ : ℝ) ^ 3)
  have hθ_pos : 0 < θ := by unfold θ; positivity
  obtain ⟨q, C, hC_prop, hC_pair, hC_union, hC_sum, hC_mono, hC_bound⟩ :=
    (hM_core i).2.2 j hji u (hM_sub j hu_Mj) hu_not_comp
  let p : ℕ := ⌈x ^ (-2 : ℝ)⌉₊
  have hx_neg2 : x ^ (-2 : ℝ) = (x ^ 2)⁻¹ := by
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by positivity), Real.rpow_natCast]
  have hℓ_r : (4 : ℝ) ≤ (ℓ : ℝ) := Nat.ofNat_le_cast.mpr hℓ
  have hx_neg2_ge_4 : (4 : ℝ) ≤ x ^ (-2 : ℝ) := le_trans hℓ_r hℓ_high
  have hp_lt : (p : ℝ) < x ^ (-2 : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hp_x2 : (p : ℝ) * x ^ 2 ≤ 2 := by
    have h1 : (p : ℝ) ≤ 2 * (x ^ 2)⁻¹ := by linarith
    calc (p : ℝ) * x ^ 2
        ≤ (2 * (x ^ 2)⁻¹) * x ^ 2 := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 2 * ((x ^ 2)⁻¹ * x ^ 2) := by ring
      _ = 2 := by rw [inv_mul_cancel₀ (by positivity), mul_one]
  have hp_θ : (p : ℝ) * θ ≤ x / (8 * (ℓ : ℝ)) := by
    unfold θ
    have h1 : (p : ℝ) * x ^ 3 ≤ 2 * x := by
      calc (p : ℝ) * x ^ 3 = ((p : ℝ) * x ^ 2) * x := by ring
        _ ≤ 2 * x := mul_le_mul_of_nonneg_right hp_x2 (by positivity)
    have h2 : (ℓ : ℝ) ≤ (ℓ : ℝ) ^ 3 := by
      have : (1 : ℝ) ≤ (ℓ : ℝ) ^ 2 := by nlinarith
      nlinarith
    calc (p : ℝ) * (x ^ 3 / (16 * (ℓ : ℝ) ^ 3))
        = ((p : ℝ) * x ^ 3) / (16 * (ℓ : ℝ) ^ 3) := by ring
      _ ≤ (2 * x) / (16 * (ℓ : ℝ) ^ 3) := div_le_div_of_nonneg_right h1 (by positivity)
      _ ≤ (2 * x) / (16 * (ℓ : ℝ)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
      _ = x / (8 * (ℓ : ℝ)) := by ring
  let f : ℕ → ℝ := fun k =>
    if h : 1 ≤ k ∧ k ≤ q then ((C ⟨k - 1, by omega⟩).card : ℝ) else 0
  have hf_sum : x / (2 * (ℓ : ℝ)) * ((M_star i).card : ℝ) ≤ ∑ k ∈ Finset.Icc 1 q, f k := by
    rw [← sum_fin_eq_sum_Icc q (fun s => ((C s).card : ℝ))]
    have h_sum_r : ∑ s : Fin q, ((C s).card : ℝ) = ((neighborFinsetIn G u (M_star i)).card : ℝ) := by
      exact_mod_cast hC_sum
    linarith
  have hf_le : ∀ k, f k ≤ θ * ((M_star i).card : ℝ) := by
    intro k
    unfold f
    split_ifs with h
    · exact hC_bound ⟨k - 1, by omega⟩
    · positivity
  have hp_sum : ∑ k ∈ Finset.Icc 1 p, f k ≤ x / (8 * (ℓ : ℝ)) * ((M_star i).card : ℝ) := by
    calc ∑ k ∈ Finset.Icc 1 p, f k
        ≤ ∑ _k ∈ Finset.Icc 1 p, (θ * ((M_star i).card : ℝ)) :=
          Finset.sum_le_sum (fun k _ => hf_le k)
      _ = ((p : ℝ) * θ) * ((M_star i).card : ℝ) := by
          rw [Finset.sum_const, Nat.card_Icc, show p + 1 - 1 = p by omega, nsmul_eq_mul, mul_assoc]
      _ ≤ (x / (8 * (ℓ : ℝ))) * ((M_star i).card : ℝ) :=
          mul_le_mul_of_nonneg_right hp_θ (Nat.cast_nonneg _)
  have hM_pos : 0 < ((M_star i).card : ℝ) :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr (hM_core i).2.1)
  have hx_ℓ_pos : 0 < x / (8 * (ℓ : ℝ)) * ((M_star i).card : ℝ) := by positivity
  have hpq : p ≤ q := by
    by_contra hlt
    push_neg at hlt
    have hsub : Finset.Icc 1 q ⊆ Finset.Icc 1 p := Finset.Icc_subset_Icc le_rfl (by omega)
    have h1 : ∑ k ∈ Finset.Icc 1 q, f k ≤ ∑ k ∈ Finset.Icc 1 p, f k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by unfold f; split_ifs <;> positivity)
    have h2 : x / (2 * (ℓ : ℝ)) * ((M_star i).card : ℝ) =
        4 * (x / (8 * (ℓ : ℝ)) * ((M_star i).card : ℝ)) := by ring
    linarith
  have h_tail_sum : x / (4 * (ℓ : ℝ)) * ((M_star i).card : ℝ) ≤
      ∑ k ∈ Finset.Icc (p + 1) q, f k := by
    have h_sp := sum_Icc_split p q hpq f
    have h2 : x / (2 * (ℓ : ℝ)) * ((M_star i).card : ℝ) =
        4 * (x / (8 * (ℓ : ℝ)) * ((M_star i).card : ℝ)) := by ring
    have h3 : x / (4 * (ℓ : ℝ)) * ((M_star i).card : ℝ) =
        2 * (x / (8 * (ℓ : ℝ)) * ((M_star i).card : ℝ)) := by ring
    linarith
  obtain ⟨k₀, hk₀_mem, hk₀_ge⟩ :=
    cauchy_series_extraction p q f (x / (4 * (ℓ : ℝ)) * ((M_star i).card : ℝ))
      (by positivity) h_tail_sum
  obtain ⟨hk₀_low, hk₀_high⟩ := Finset.mem_Icc.mp hk₀_mem
  have hk₀_1 : 1 ≤ k₀ ∧ k₀ ≤ q := ⟨by omega, hk₀_high⟩
  unfold f at hk₀_ge
  rw [dif_pos hk₀_1] at hk₀_ge
  have hk₀_gt : x ^ (-2 : ℝ) < (k₀ : ℝ) := by
    have h1 : x ^ (-2 : ℝ) ≤ (p : ℝ) := Nat.le_ceil _
    have h2 : (p : ℝ) + 1 ≤ (k₀ : ℝ) := by exact_mod_cast hk₀_low
    linarith
  let D : Fin k₀ → Finset V := fun s => C ⟨s.1, by omega⟩
  refine ⟨k₀, D, hk₀_gt, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro s
    have h1 : D s ⊆ neighborFinsetIn G u (M_star i) := (hC_prop ⟨s.1, by omega⟩).1
    have h2 : neighborFinsetIn G u (M_star i) ⊆ M_star i := Finset.filter_subset _ _
    exact (h1.trans h2).trans ((hM_sub i).trans (hB_sub i))
  · intro s; exact (hC_prop ⟨s.1, by omega⟩).2.1
  · intro s₁ s₂ hs
    have hs' : (⟨s₁.1, by omega⟩ : Fin q) ≠ ⟨s₂.1, by omega⟩ := by
      intro h; apply hs; ext; exact Fin.mk.inj_iff.mp h
    exact (hC_pair _ _ hs').1
  · intro s
    have hs_le : (⟨s.1, by omega⟩ : Fin q) ≤ ⟨k₀ - 1, by omega⟩ := by
      rw [Fin.le_def]; dsimp; omega
    have h_mono : ((C ⟨k₀ - 1, by omega⟩).card : ℝ) ≤ ((D s).card : ℝ) :=
      Nat.cast_le.mpr (hC_mono ⟨s.1, by omega⟩ ⟨k₀ - 1, by omega⟩ hs_le)
    exact le_trans
      (le_trans (subcase_6_2a_width_bound (Nat.cast_nonneg _) hx_pos hx_256 hℓ hℓ_high
        hk₀_gt hw'_ge (hM_card i)) hk₀_ge) h_mono
  · intro s₁ s₂ hs
    have hs' : (⟨s₁.1, by omega⟩ : Fin q) ≠ ⟨s₂.1, by omega⟩ := by
      intro h; apply hs; ext; exact Fin.mk.inj_iff.mp h
    exact (hC_pair _ _ hs').2

/-- Subcase 2b of Proposition 4.4 (`prop:comb-dichotomy`): when all incomplete external attachments are
sparse, deleting dense complete vertices yields a complete-or-$x$-sparse blockade of length $\ell$. -/
lemma comb_dichotomy_subcase_6_2b {G : SimpleGraph V} {S : Finset V} {ℓ : ℕ} {w' x : ℝ}
    {B M_star : Fin ℓ → Finset V}
    (hx_pos : 0 < x) (hx_256 : x ≤ 1 / 256) (hℓ : 4 ≤ ℓ)
    (hℓ_max : (ℓ : ℝ) ≤ x ^ (-10 : ℝ)) (hℓ_sqrt : (ℓ : ℝ) ^ (1 / 2 : ℝ) / 2 ≤ (ℓ : ℝ))
    (hw'_ge : (S.card : ℝ) / (ℓ : ℝ) ^ 18 ≤ w')
    (hB_sub : ∀ i, B i ⊆ S)
    (hB_disj : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hM_sub : ∀ i, M_star i ⊆ B i)
    (hM_ne : ∀ i, (M_star i).Nonempty)
    (hM_card : ∀ i, w' / ((2 : ℝ) ^ 18 * (ℓ : ℝ) ^ 8) ≤ ((M_star i).card : ℝ))
    (h_sparse_att : ∀ (i j : Fin ℓ), j ≠ i → ∀ u ∈ M_star j,
      (¬∀ z ∈ M_star i, G.Adj u z) →
      ((neighborFinsetIn G u (M_star i)).card : ℝ) < x / (2 * (ℓ : ℝ)) * ((M_star i).card : ℝ)) :
    ∃ (k : ℕ) (D : Fin k → Finset V),
      2 ≤ k ∧ (k : ℝ) ≤ x ^ (-10 : ℝ) ∧ (ℓ : ℝ) ^ (1 / 2 : ℝ) / 2 ≤ (k : ℝ) ∧
      IsCompleteOrXSparseBlockadeIn G S k ((S.card : ℝ) / (k : ℝ) ^ 120) x D := by
  let B_comp (i j : Fin ℓ) : Finset V :=
    (M_star i).filter (fun z => ∀ u ∈ M_star j, G.Adj z u)
  let J_incomp (i : Fin ℓ) : Finset (Fin ℓ) :=
    Finset.univ.filter (fun j : Fin ℓ => j ≠ i ∧ ¬IsCompletePair G (M_star i) (M_star j))
  let D (i : Fin ℓ) : Finset V :=
    M_star i \ (J_incomp i).biUnion (B_comp i)
  have hB_comp_lt : ∀ (i j : Fin ℓ), j ∈ J_incomp i →
      ((B_comp i j).card : ℝ) < x / (2 * (ℓ : ℝ)) * ((M_star i).card : ℝ) := by
    intro i j hj
    obtain ⟨hji, h_not_comp⟩ := (Finset.mem_filter.mp hj).2
    unfold IsCompletePair at h_not_comp
    push_neg at h_not_comp
    obtain ⟨z₀, hz₀, u₀, hu₀, h_nadj⟩ := h_not_comp
    have hu₀_not_comp : ¬∀ z ∈ M_star i, G.Adj u₀ z :=
      fun h => h_nadj (G.symm (h z₀ hz₀))
    have h_sub : B_comp i j ⊆ neighborFinsetIn G u₀ (M_star i) := by
      intro z hz
      obtain ⟨hz_Mi, hz_comp⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨hz_Mi, G.symm (hz_comp u₀ hu₀)⟩
    exact lt_of_le_of_lt (Nat.cast_le.mpr (Finset.card_le_card h_sub))
      (h_sparse_att i j hji u₀ hu₀ hu₀_not_comp)
  have hD_half : ∀ i : Fin ℓ, ((M_star i).card : ℝ) / 2 < ((D i).card : ℝ) := by
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
            Nat.add_le_add_left (Finset.card_biUnion_le) _
    have h_card_r : ((M_star i).card : ℝ) ≤
        ((D i).card : ℝ) + ∑ j ∈ J_incomp i, ((B_comp i j).card : ℝ) := by
      exact_mod_cast h_card_le
    have h_J_card : ((J_incomp i).card : ℝ) ≤ (ℓ : ℝ) := by
      have : (J_incomp i).card ≤ (Finset.univ : Finset (Fin ℓ)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      rw [Finset.card_univ, Fintype.card_fin] at this
      exact Nat.cast_le.mpr this
    have h_sum_le : ∑ j ∈ J_incomp i, ((B_comp i j).card : ℝ) ≤
        (x / 2) * ((M_star i).card : ℝ) := by
      calc ∑ j ∈ J_incomp i, ((B_comp i j).card : ℝ)
          ≤ ∑ _j ∈ J_incomp i, (x / (2 * (ℓ : ℝ)) * ((M_star i).card : ℝ)) :=
            Finset.sum_le_sum (fun j hj => le_of_lt (hB_comp_lt i j hj))
        _ = (J_incomp i).card * (x / (2 * (ℓ : ℝ)) * ((M_star i).card : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (ℓ : ℝ) * (x / (2 * (ℓ : ℝ)) * ((M_star i).card : ℝ)) :=
            mul_le_mul_of_nonneg_right h_J_card (by positivity)
        _ = (ℓ : ℝ) / (ℓ : ℝ) * ((x / 2) * ((M_star i).card : ℝ)) := by ring
        _ = (x / 2) * ((M_star i).card : ℝ) := by
            have hℓ_r : (4 : ℝ) ≤ (ℓ : ℝ) := Nat.ofNat_le_cast.mpr hℓ
            rw [div_self (by linarith), one_mul]
    have hM_pos : 0 < ((M_star i).card : ℝ) :=
      Nat.cast_pos.mpr (Finset.card_pos.mpr (hM_ne i))
    nlinarith
  have hD_sparse : ∀ (p q : Fin ℓ), p ≠ q → ¬IsCompletePair G (M_star p) (M_star q) →
      IsXSparseTo G (D p) (D q) x := by
    intro p q hpq h_not_comp z hz
    obtain ⟨hz_Mp, hz_not_bi⟩ := Finset.mem_sdiff.mp hz
    have hq_mem : q ∈ J_incomp p :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ q, hpq.symm, h_not_comp⟩
    have hz_not_B : z ∉ B_comp p q :=
      fun h => hz_not_bi (Finset.mem_biUnion.mpr ⟨q, hq_mem, h⟩)
    have hz_not_comp : ¬∀ u ∈ M_star q, G.Adj z u :=
      fun h => hz_not_B (Finset.mem_filter.mpr ⟨hz_Mp, h⟩)
    have h_deg := h_sparse_att q p hpq z hz_Mp hz_not_comp
    have h_sub : neighborFinsetIn G z (D q) ⊆ neighborFinsetIn G z (M_star q) :=
      Finset.filter_subset_filter _ Finset.sdiff_subset
    have h_le1 : ((neighborFinsetIn G z (D q)).card : ℝ) ≤
        x / (2 * (ℓ : ℝ)) * ((M_star q).card : ℝ) :=
      le_trans (Nat.cast_le.mpr (Finset.card_le_card h_sub)) (le_of_lt h_deg)
    have hℓ_r : (4 : ℝ) ≤ (ℓ : ℝ) := Nat.ofNat_le_cast.mpr hℓ
    have h_le2 : x / (2 * (ℓ : ℝ)) * ((M_star q).card : ℝ) ≤ (x / 2) * ((M_star q).card : ℝ) := by
      refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
      exact div_le_div_of_nonneg_left (le_of_lt hx_pos) (by positivity) (by linarith)
    have h_half_q := hD_half q
    nlinarith
  refine ⟨ℓ, D, by omega, hℓ_max, hℓ_sqrt, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i
    exact Finset.sdiff_subset.trans ((hM_sub i).trans (hB_sub i))
  · intro i
    rw [← Finset.card_pos, ← @Nat.cast_pos ℝ]
    have hM_pos : 0 < ((M_star i).card : ℝ) :=
      Nat.cast_pos.mpr (Finset.card_pos.mpr (hM_ne i))
    linarith [hD_half i]
  · intro i j hij
    exact Finset.disjoint_of_subset_left
      (Finset.sdiff_subset.trans (hM_sub i))
      (Finset.disjoint_of_subset_right
        (Finset.sdiff_subset.trans (hM_sub j))
        (hB_disj i j hij))
  · intro i
    exact subcase_6_2b_width_bound (Nat.cast_nonneg _) hℓ hw'_ge
      (hM_card i) (le_of_lt (hD_half i))
  · intro i j hij
    by_cases h_comp : IsCompletePair G (M_star i) (M_star j)
    · exact Or.inl (fun u hu v hv => h_comp u (Finset.sdiff_subset hu) v (Finset.sdiff_subset hv))
    · have h_comp_symm : ¬IsCompletePair G (M_star j) (M_star i) :=
        fun h => h_comp (fun u hu v hv => G.symm (h v hv u hu))
      exact Or.inr ⟨hD_sparse j i hij.symm h_comp_symm, hD_sparse i j hij h_comp⟩

/-- **Proposition 4.4 (`prop:comb-dichotomy`)**:
Parameter-Free Upside-Down Comb Dichotomy with Calibrated Widths.
Let $G$ be a $\overline{P_6}$-free graph, let $0 < x \le y \le 2^{-8}$, let
$\ell \in [y^{-1/4}, x^{-2}]$, and let $(a, B)$ be an $(\ell, w)$-comb in $G$ inside $S$
with external apex $v$ and width $w \ge \frac{|S|}{\ell^{18}}$. Then at least one of the
following two outcomes holds:
1. **(Long Complete Blockade Outcome)**: $G[S]$ contains a complete
   $(k, \frac{|S|}{k^{120}})$-blockade for some integer $k > x^{-2}$; or
2. **(Moderate Complete-or-$x$-Sparse Blockade Outcome)**: $G[S]$ contains a
   complete-or-$x$-sparse $(k, \frac{|S|}{k^{120}})$-blockade for some integer
   $k \in [2, x^{-10}]$ (with $k \ge \frac{\ell^{1/2}}{2}$). -/
theorem comb_dichotomy {G : SimpleGraph V} {S : Finset V} {ℓ : ℕ} {w x y : ℝ}
    {a : Fin ℓ → V} {B : Fin ℓ → Finset V} {v : V}
    (hG : IsInducedSubgraphFree G P6Compl)
    (hcomb : IsCombIn G S ℓ w a B)
    (hapex : IsCombExternalApex G S ℓ a B v)
    (hx_pos : 0 < x) (hxy : x ≤ y) (hy_max : y ≤ (2 : ℝ) ^ (-8 : ℝ))
    (hℓ_low : y ^ (-1 / 4 : ℝ) ≤ (ℓ : ℝ)) (hℓ_high : (ℓ : ℝ) ≤ x ^ (-2 : ℝ))
    (hw_ge : (S.card : ℝ) / (ℓ : ℝ) ^ 18 ≤ w) :
    (∃ (k : ℕ) (D : Fin k → Finset V),
      x ^ (-2 : ℝ) < (k : ℝ) ∧
      IsCompleteBlockadeIn G S k ((S.card : ℝ) / (k : ℝ) ^ 120) D) ∨
    (∃ (k : ℕ) (D : Fin k → Finset V),
      2 ≤ k ∧ (k : ℝ) ≤ x ^ (-10 : ℝ) ∧ (ℓ : ℝ) ^ (1 / 2 : ℝ) / 2 ≤ (k : ℝ) ∧
      IsCompleteOrXSparseBlockadeIn G S k ((S.card : ℝ) / (k : ℝ) ^ 120) x D) := by
  let w' : ℝ := max w 1
  have hw'_1 : 1 ≤ w' := le_max_right w 1
  have hw'_ge : (S.card : ℝ) / (ℓ : ℝ) ^ 18 ≤ w' := le_trans hw_ge (le_max_left w 1)
  have hcomb' : IsCombIn G S ℓ w' a B := by
    refine ⟨⟨hcomb.is_blockade.subset_ambient, hcomb.is_blockade.nonempty_blocks,
      hcomb.is_blockade.pairwise_disjoint, fun i => ?_⟩,
      hcomb.apex_in_ambient, hcomb.apex_injective, hcomb.apex_disjoint_blocks,
      hcomb.apex_complete_own, hcomb.apex_anticomplete_other⟩
    exact max_le (hcomb.is_blockade.width_ge i)
      (Nat.one_le_cast.mpr (Finset.card_pos.mpr (hcomb.is_blockade.nonempty_blocks i)))
  let θ : ℝ := x ^ 3 / (16 * (ℓ : ℝ) ^ 3)
  let K₀ : ℕ := ⌊θ⁻¹⌋₊
  obtain ⟨hℓ, hx_256, hθ_pos, hK₀_ℓ, hK₀_gt, hK₀_max, hℓ_max, hℓ_sqrt⟩ :=
    comb_parameter_bounds hx_pos hxy hy_max hℓ_low hℓ_high
  by_cases h_case1 : ∃ i : Fin ℓ, ∃ (k : ℕ) (U : Fin k → Finset V),
      2 ≤ k ∧ k ≤ K₀ ∧ (ℓ : ℝ) ^ (1 / 2 : ℝ) / 2 ≤ (k : ℝ) ∧
      IsPureBlockadeIn G (B i) k (w' / (4 * (k : ℝ)) ^ 16) U
  · right
    obtain ⟨i, k, U, hk2, hkK₀, hk_sqrt, hU_pure⟩ := h_case1
    refine ⟨k, U, hk2, le_trans (Nat.cast_le.mpr hkK₀) hK₀_max, hk_sqrt,
      ⟨fun j => (hU_pure.1.subset_ambient j).trans (hcomb.is_blockade.subset_ambient i),
       hU_pure.1.nonempty_blocks, hU_pure.1.pairwise_disjoint, fun j => ?_⟩,
      fun j₁ j₂ hj => isCompleteOrXSparsePair_of_isPurePair (le_of_lt hx_pos) (hU_pure.2 j₁ j₂ hj)⟩
    exact le_trans (case_6_1_width_bound (Nat.cast_nonneg _) hℓ hk2 hk_sqrt hw'_ge)
      (hU_pure.1.width_ge j)
  · have h_all_out1 : ∀ i : Fin ℓ, ∃ M_star ⊆ B i,
        w' / ((2 : ℝ) ^ 18 * (ℓ : ℝ) ^ 8) ≤ (M_star.card : ℝ) ∧
        IsSmallAttachmentCore G B i θ M_star := by
      intro i
      rcases gallai_tree_decomposition hG hcomb' hapex hℓ hw'_1 i hθ_pos hK₀_ℓ hK₀_gt with
        h_out1 | h_out2
      · exact h_out1
      · exact False.elim (h_case1 ⟨i, h_out2⟩)
    obtain ⟨M_star, hM_all⟩ := Classical.axiomOfChoice h_all_out1
    have hM_sub : ∀ i, M_star i ⊆ B i := fun i => (hM_all i).1
    have hM_card : ∀ i, w' / ((2 : ℝ) ^ 18 * (ℓ : ℝ) ^ 8) ≤ ((M_star i).card : ℝ) :=
      fun i => (hM_all i).2.1
    have hM_core : ∀ i, IsSmallAttachmentCore G B i θ (M_star i) := fun i => (hM_all i).2.2
    by_cases h_62a : ∃ (i j : Fin ℓ), j ≠ i ∧ ∃ u ∈ M_star j,
        (¬∀ z ∈ M_star i, G.Adj u z) ∧
        x / (2 * (ℓ : ℝ)) * ((M_star i).card : ℝ) ≤ ((neighborFinsetIn G u (M_star i)).card : ℝ)
    · left
      obtain ⟨i, j, hji, u, hu_Mj, hu_not_comp, hu_deg⟩ := h_62a
      exact comb_dichotomy_subcase_6_2a hx_pos hx_256 hℓ hℓ_high hw'_ge
        hcomb.is_blockade.subset_ambient hM_sub hM_card hM_core hji hu_Mj hu_not_comp hu_deg
    · right
      have h_sparse_att : ∀ (i j : Fin ℓ), j ≠ i → ∀ u ∈ M_star j,
          (¬∀ z ∈ M_star i, G.Adj u z) →
          ((neighborFinsetIn G u (M_star i)).card : ℝ) <
            x / (2 * (ℓ : ℝ)) * ((M_star i).card : ℝ) := by
        intro i j hji u hu_Mj hu_not_comp
        by_contra h_ge
        push_neg at h_ge
        exact h_62a ⟨i, j, hji, u, hu_Mj, hu_not_comp, h_ge⟩
      exact comb_dichotomy_subcase_6_2b hx_pos hx_256 hℓ hℓ_max hℓ_sqrt hw'_ge
        hcomb.is_blockade.subset_ambient hcomb.is_blockade.pairwise_disjoint
        hM_sub (fun i => (hM_core i).2.1) hM_card h_sparse_att

end ErdosHajnalP6
