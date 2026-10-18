/-
Copyright 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosHajnal.BasicLemmas
import ErdosHajnal.CombModules
import ErdosHajnal.Defs
import ErdosHajnal.GallaiAndCombDichotomy
import ErdosHajnal.LayoutAndSparsification
import ErdosHajnal.Stage2Reduction
import ErdosHajnal.WitnessGraph

/-!
# Section 2 Lemmas and Proof of Theorem 1.1 (`FMBV4-016_readable.tex`)

This file formalizes the core structural extraction, substitution, and main theorem synthesis:
- Lemma 2.6 (`upside_down_comb_extraction`): Upside-Down Comb Extraction Lemma
- Lemma 2.3 & Proposition 3.2 (`erdos_hajnal_twin_substitution`): 2-Vertex Substitution for Erdős–Hajnal
- Lemma 2.7 (`p6Compl_free_sparse_compl_complete_blockade_cube`): Co-sparse Complete Blockade Lemma
- Theorem 1.1 (`erdos_hajnal_p6`, `erdos_61.variants.p6`, `erdos_hajnal_p6_fintype`)
-/

set_option linter.unusedSectionVars false

open Filter Finset SimpleGraph Real

namespace ErdosHajnalP6

section CombExtraction

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Neighborhood and Cross-Edge Helper Lemmas -/

lemma not_mem_neighborFinsetIn_self (G : SimpleGraph V) (v : V) (S : Finset V) :
    v ∉ neighborFinsetIn G v S := by
  rw [mem_neighborFinsetIn]
  intro h
  exact G.loopless v h.2

lemma sum_neighborFinsetIn_card_comm (G : SimpleGraph V) (A B : Finset V) :
    ∑ u ∈ A, (neighborFinsetIn G u B).card = ∑ w ∈ B, (neighborFinsetIn G w A).card := by
  simp only [neighborFinsetIn, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  refine sum_congr rfl (fun w _ => sum_congr rfl (fun u _ => ?_))
  by_cases h : G.Adj u w
  · simp [h, G.symm h]
  · have h' : ¬G.Adj w u := fun hwu => h (G.symm hwu)
    simp [h, h']

/-! ### Arithmetic and Dyadic Scale Helper Lemmas -/

lemma sum_inv_sq_le (N : ℕ) :
    ∑ s ∈ Finset.range (N + 1), (1 / ((s : ℝ) + 1) ^ 2) ≤ 2 - 1 / ((N : ℝ) + 1) := by
  induction N with
  | zero =>
    norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    push_cast
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < (n : ℝ) + 1 + 1 := by positivity
    have h_step : 1 / ((n : ℝ) + 1 + 1) ^ 2 ≤ 1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 1 + 1) := by
      rw [div_sub_div _ _ h1.ne' h2.ne', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

lemma nat_sq_bound_two_pow (s : ℕ) : 4 * (s + 1) ^ 2 ≤ 9 * 2 ^ s := by
  induction s with
  | zero => decide
  | succ s ih =>
    rcases s with _ | _ | s
    · decide
    · decide
    · have h_id : 4 * (s + 1 + 1 + 1 + 1) ^ 2 + (4 * s ^ 2 + 16 * s + 8) =
          2 * (4 * (s + 1 + 1 + 1) ^ 2) := by ring
      have h_pow : 9 * 2 ^ (s + 1 + 1 + 1) = 2 * (9 * 2 ^ (s + 1 + 1)) := by
        rw [Nat.pow_succ]
        ring
      omega

lemma nat_fourth_bound_two_pow (s : ℕ) : (s + 1) ^ 4 ≤ 1024 * 2 ^ s := by
  induction s with
  | zero => decide
  | succ s ih =>
    rcases s with _ | _ | _ | _ | _ | s
    · decide
    · decide
    · decide
    · decide
    · decide
    · have h_id : (s + 1 + 1 + 1 + 1 + 1 + 1 + 1) ^ 4 +
          (s ^ 4 + 20 * s ^ 3 + 138 * s ^ 2 + 356 * s + 191) =
          2 * (s + 1 + 1 + 1 + 1 + 1 + 1) ^ 4 := by ring
      have h_pow : 1024 * 2 ^ (s + 1 + 1 + 1 + 1 + 1 + 1) =
          2 * (1024 * 2 ^ (s + 1 + 1 + 1 + 1 + 1)) := by
        rw [Nat.pow_succ]
        ring
      omega

lemma exists_dyadic_bucket {W d : ℝ} {N : ℕ} (hd1 : 1 ≤ d) (hdW : d ≤ W) (hWN : W ≤ (N : ℝ)) :
    ∃ t ∈ Finset.range (N + 1), 2 ^ t * d ≤ W ∧ W < 2 ^ (t + 1) * d := by
  by_contra h_none
  push_neg at h_none
  have h_all : ∀ t ≤ N + 1, 2 ^ t * d ≤ W := by
    intro t ht
    induction t with
    | zero => simpa using hdW
    | succ t iht =>
      have htN : t ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
      exact h_none t htN (iht (by omega))
  have h_top := h_all (N + 1) le_rfl
  have h_pow_nat : N + 1 ≤ 2 ^ (N + 1) := Nat.le_of_lt (Nat.lt_two_pow_self)
  have h_pow : ((N : ℝ) + 1) ≤ (2 : ℝ) ^ (N + 1) := by exact_mod_cast h_pow_nat
  nlinarith

/-! ### Greedy Forward Pass and Backward Cleaning -/

structure StepData (V : Type*) where
  a : V
  D : Finset V
  A : Finset V

noncomputable def forwardSteps (G : SimpleGraph V) (R₁ : Finset V) (x minA : ℝ) :
    ℕ → Finset V → List (StepData V) × Finset V
  | 0, A => ([], A)
  | k + 1, A =>
    if h : minA ≤ (A.card : ℝ) ∧ ∃ u ∈ R₁, x * (A.card : ℝ) < ((neighborFinsetIn G u A).card : ℝ) then
      let hR₁ : R₁.Nonempty := let ⟨u, hu, _⟩ := h.2; ⟨u, hu⟩
      let a := Classical.choose (Finset.exists_max_image R₁ (fun u => (neighborFinsetIn G u A).card) hR₁)
      let D := neighborFinsetIn G a A
      let res := forwardSteps G R₁ x minA k (A \ D)
      (⟨a, D, A⟩ :: res.1, res.2)
    else
      ([], A)

lemma forwardSteps_subset (G : SimpleGraph V) (R₁ : Finset V) (x minA : ℝ)
    (k : ℕ) (A : Finset V) :
    (forwardSteps G R₁ x minA k A).2 ⊆ A ∧
    ∀ s ∈ (forwardSteps G R₁ x minA k A).1, s.D ⊆ s.A ∧ s.A ⊆ A := by
  induction k generalizing A with
  | zero => simp [forwardSteps]
  | succ k ih =>
    unfold forwardSteps
    split_ifs with h
    · dsimp only
      obtain ⟨h_end, h_steps⟩ := ih (A \ neighborFinsetIn G
        (Classical.choose (Finset.exists_max_image R₁ (fun u => (neighborFinsetIn G u A).card)
          ⟨h.2.choose, h.2.choose_spec.1⟩)) A)
      refine ⟨h_end.trans sdiff_subset, ?_⟩
      intro s hs
      simp only [List.mem_cons] at hs
      rcases hs with rfl | hs
      · exact ⟨neighborFinsetIn_subset G _ A, Subset.rfl⟩
      · obtain ⟨hD, hA⟩ := h_steps s hs
        exact ⟨hD, hA.trans sdiff_subset⟩
    · simp

lemma forwardSteps_props (G : SimpleGraph V) (R₁ : Finset V) (x minA : ℝ)
    (k : ℕ) (A : Finset V) :
    ∀ s ∈ (forwardSteps G R₁ x minA k A).1,
      s.a ∈ R₁ ∧
      s.D = neighborFinsetIn G s.a s.A ∧
      minA ≤ (s.A.card : ℝ) ∧
      x * (s.A.card : ℝ) < (s.D.card : ℝ) ∧
      ∀ u ∈ R₁, (neighborFinsetIn G u s.A).card ≤ s.D.card := by
  induction k generalizing A with
  | zero => simp [forwardSteps]
  | succ k ih =>
    unfold forwardSteps
    split_ifs with h
    · dsimp only
      have hR₁ : R₁.Nonempty := let ⟨u, hu, _⟩ := h.2; ⟨u, hu⟩
      have ha_spec := Classical.choose_spec
        (Finset.exists_max_image R₁ (fun u => (neighborFinsetIn G u A).card) hR₁)
      intro s hs
      simp only [List.mem_cons] at hs
      rcases hs with rfl | hs
      · obtain ⟨u₀, hu₀, h_gt⟩ := h.2
        have h_le : (neighborFinsetIn G u₀ A).card ≤
            (neighborFinsetIn G (Classical.choose
              (Finset.exists_max_image R₁ (fun u => (neighborFinsetIn G u A).card) hR₁)) A).card :=
          ha_spec.2 u₀ hu₀
        have h_le_r : ((neighborFinsetIn G u₀ A).card : ℝ) ≤
            ((neighborFinsetIn G (Classical.choose
              (Finset.exists_max_image R₁ (fun u => (neighborFinsetIn G u A).card) hR₁)) A).card : ℝ) := by
          exact_mod_cast h_le
        exact ⟨ha_spec.1, rfl, h.1, h_gt.trans_le h_le_r, ha_spec.2⟩
      · exact ih _ s hs
    · simp

lemma forwardSteps_sum_and_terminal (G : SimpleGraph V) (R₁ : Finset V) (x minA : ℝ)
    (hx : 0 < x) (hminA : 0 < minA) (k : ℕ) (A : Finset V) (hk : A.card ≤ k) :
    ((forwardSteps G R₁ x minA k A).1.map (fun s => s.D.card)).sum +
      (forwardSteps G R₁ x minA k A).2.card = A.card ∧
    ¬(minA ≤ ((forwardSteps G R₁ x minA k A).2.card : ℝ) ∧
      ∃ u ∈ R₁, x * ((forwardSteps G R₁ x minA k A).2.card : ℝ) <
        ((neighborFinsetIn G u (forwardSteps G R₁ x minA k A).2).card : ℝ)) := by
  induction k generalizing A with
  | zero =>
    have hA0 : A.card = 0 := Nat.eq_zero_of_le_zero hk
    simp only [forwardSteps, List.map_nil, List.sum_nil, zero_add, hA0, Nat.cast_zero, true_and]
    intro h
    linarith
  | succ k ih =>
    unfold forwardSteps
    split_ifs with h
    · dsimp only
      have hR₁ : R₁.Nonempty := let ⟨u, hu, _⟩ := h.2; ⟨u, hu⟩
      set a := Classical.choose (Finset.exists_max_image R₁ (fun u => (neighborFinsetIn G u A).card) hR₁)
      have ha_spec := Classical.choose_spec (Finset.exists_max_image R₁ (fun u => (neighborFinsetIn G u A).card) hR₁)
      set D := neighborFinsetIn G a A
      obtain ⟨u₀, hu₀, h_gt⟩ := h.2
      have h_le : (neighborFinsetIn G u₀ A).card ≤ D.card := ha_spec.2 u₀ hu₀
      have hD_pos_r : (0 : ℝ) < (D.card : ℝ) := by
        have : (0 : ℝ) < x * (A.card : ℝ) := mul_pos hx (lt_of_lt_of_le hminA h.1)
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

lemma forwardSteps_pairwise (G : SimpleGraph V) (R₁ : Finset V) (x minA : ℝ)
    (k : ℕ) (A : Finset V) :
    (forwardSteps G R₁ x minA k A).1.Pairwise (fun s₁ s₂ => s₂.D ⊆ s₁.A \ s₁.D) := by
  induction k generalizing A with
  | zero => simp [forwardSteps]
  | succ k ih =>
    unfold forwardSteps
    split_ifs with h
    · dsimp only
      rw [List.pairwise_cons]
      refine ⟨?_, ih _⟩
      intro s₂ hs₂
      obtain ⟨_, h_steps⟩ := forwardSteps_subset G R₁ x minA k _
      obtain ⟨hD₂, hA₂⟩ := h_steps s₂ hs₂
      exact hD₂.trans hA₂
    · simp

lemma stepData_rel_props (G : SimpleGraph V) {s₁ s₂ : StepData V}
    (hD₁ : s₁.D = neighborFinsetIn G s₁.a s₁.A)
    (hD₂ : s₂.D = neighborFinsetIn G s₂.a s₂.A)
    (hD₂_pos : 1 ≤ s₂.D.card)
    (h_sub : s₂.D ⊆ s₁.A \ s₁.D) :
    s₁.a ≠ s₂.a ∧ Disjoint s₁.D s₂.D ∧ s₂.D ⊆ s₁.A ∧ ∀ u ∈ s₂.D, ¬G.Adj s₁.a u := by
  have h_disj : Disjoint s₁.D s₂.D := by
    rw [Finset.disjoint_left]
    intro u hu1 hu2
    exact (Finset.mem_sdiff.mp (h_sub hu2)).2 hu1
  have h_subA : s₂.D ⊆ s₁.A := h_sub.trans sdiff_subset
  have h_not_adj : ∀ u ∈ s₂.D, ¬G.Adj s₁.a u := by
    intro u hu2 hadj
    have hu_sdiff := Finset.mem_sdiff.mp (h_sub hu2)
    apply hu_sdiff.2
    rw [hD₁, mem_neighborFinsetIn]
    exact ⟨hu_sdiff.1, hadj⟩
  have h_ne : s₁.a ≠ s₂.a := by
    intro h_eq
    obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < s₂.D.card)
    have hadj2 : G.Adj s₂.a u := by
      rw [hD₂, mem_neighborFinsetIn] at hu
      exact hu.2
    exact h_not_adj u hu (h_eq ▸ hadj2)
  exact ⟨h_ne, h_disj, h_subA, h_not_adj⟩

noncomputable def backwardClean (G : SimpleGraph V) : List (StepData V) → List (StepData V)
  | [] => []
  | s :: rest =>
    let tail := backwardClean G rest
    let B := s.D.filter (fun u => ∀ q ∈ tail, ¬G.Adj q.a u)
    if s.D.card ≤ 2 * B.card then
      ⟨s.a, B, s.A⟩ :: tail
    else
      tail

noncomputable def covered (G : SimpleGraph V) (tail : List (StepData V)) (X : Finset V) : Finset V :=
  X.filter (fun u => ∃ q ∈ tail, G.Adj q.a u)

lemma backwardClean_sub (G : SimpleGraph V) (L : List (StepData V)) :
    ∀ q ∈ backwardClean G L, ∃ s ∈ L,
      q.a = s.a ∧ q.A = s.A ∧ q.D ⊆ s.D ∧ s.D.card ≤ 2 * q.D.card := by
  induction L with
  | nil => simp [backwardClean]
  | cons s rest ih =>
    unfold backwardClean
    dsimp only
    split_ifs with h
    · intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact ⟨s, List.mem_cons_self, rfl, rfl, filter_subset _ _, h⟩
      · obtain ⟨s', hs', h1, h2, h3, h4⟩ := ih q hq
        exact ⟨s', List.mem_cons_of_mem _ hs', h1, h2, h3, h4⟩
    · intro q hq
      obtain ⟨s', hs', h1, h2, h3, h4⟩ := ih q hq
      exact ⟨s', List.mem_cons_of_mem _ hs', h1, h2, h3, h4⟩

lemma backwardClean_pairwise (G : SimpleGraph V) (L : List (StepData V))
    (hL : L.Pairwise (fun s₁ s₂ => s₁.a ≠ s₂.a ∧ Disjoint s₁.D s₂.D ∧ ∀ u ∈ s₂.D, ¬G.Adj s₁.a u)) :
    (backwardClean G L).Pairwise (fun q₁ q₂ =>
      q₁.a ≠ q₂.a ∧ Disjoint q₁.D q₂.D ∧
      (∀ u ∈ q₂.D, ¬G.Adj q₁.a u) ∧ (∀ u ∈ q₁.D, ¬G.Adj q₂.a u)) := by
  induction L with
  | nil => simp [backwardClean]
  | cons s rest ih =>
    rw [List.pairwise_cons] at hL
    unfold backwardClean
    dsimp only
    split_ifs with h
    · rw [List.pairwise_cons]
      refine ⟨?_, ih hL.2⟩
      intro q hq
      obtain ⟨s₂, hs₂, ha_eq, _, hD_sub, _⟩ := backwardClean_sub G rest q hq
      obtain ⟨hne, hdisj, hnot1⟩ := hL.1 s₂ hs₂
      refine ⟨ha_eq ▸ hne, ?_, ?_, ?_⟩
      · exact Disjoint.mono (filter_subset _ _) hD_sub hdisj
      · intro u hu
        exact hnot1 u (hD_sub hu)
      · intro u hu
        rw [mem_filter] at hu
        exact hu.2 q hq
    · exact ih hL.2

lemma covered_mono_tail (G : SimpleGraph V) (t₁ t₂ : List (StepData V)) (ht : ∀ q ∈ t₁, q ∈ t₂)
    (X : Finset V) : covered G t₁ X ⊆ covered G t₂ X := by
  intro u hu
  unfold covered at hu ⊢
  rw [mem_filter] at hu ⊢
  obtain ⟨huX, q, hq, hadj⟩ := hu
  exact ⟨huX, q, ht q hq, hadj⟩

lemma covered_mono_set (G : SimpleGraph V) (tail : List (StepData V)) {X Y : Finset V} (hXY : X ⊆ Y) :
    covered G tail X ⊆ covered G tail Y := by
  intro u hu
  unfold covered at hu ⊢
  rw [mem_filter] at hu ⊢
  exact ⟨hXY hu.1, hu.2⟩

lemma covered_subset (G : SimpleGraph V) (tail : List (StepData V)) (X : Finset V) :
    covered G tail X ⊆ X :=
  filter_subset _ _

lemma backwardClean_covered (G : SimpleGraph V) (L : List (StepData V))
    (h_own : ∀ s ∈ L, ∀ u ∈ s.D, G.Adj s.a u) :
    ∀ s ∈ L, s.D.card ≤ 2 * (covered G (backwardClean G L) s.D).card := by
  induction L with
  | nil => simp
  | cons s rest ih =>
    intro s' hs'
    have h_own_rest : ∀ s'' ∈ rest, ∀ u ∈ s''.D, G.Adj s''.a u :=
      fun s'' hs'' => h_own s'' (List.mem_cons_of_mem _ hs'')
    unfold backwardClean
    dsimp only
    split_ifs with h
    · simp only [List.mem_cons] at hs'
      rcases hs' with rfl | hs'
      · have h_eq : covered G (⟨s'.a, filter (fun u => ∀ q ∈ backwardClean G rest, ¬G.Adj q.a u) s'.D, s'.A⟩ :: backwardClean G rest) s'.D = s'.D := by
          ext u
          unfold covered
          simp only [mem_filter, List.mem_cons, exists_eq_or_imp, and_iff_left_iff_imp]
          intro hu
          exact Or.inl (h_own s' List.mem_cons_self u hu)
        rw [h_eq]
        omega
      · have h_ih := ih h_own_rest s' hs'
        have h_sub := covered_mono_tail G (backwardClean G rest)
          (⟨s.a, filter (fun u => ∀ q ∈ backwardClean G rest, ¬G.Adj q.a u) s.D, s.A⟩ :: backwardClean G rest)
          (fun q hq => List.mem_cons_of_mem _ hq) s'.D
        have h_le := card_le_card h_sub
        omega
    · simp only [List.mem_cons] at hs'
      rcases hs' with rfl | hs'
      · set tail := backwardClean G rest
        set B : Finset V := s'.D.filter (fun u => ∀ q ∈ tail, ¬G.Adj q.a u)
        have h_part : B.card + (covered G tail s'.D).card = s'.D.card := by
          unfold covered
          have h_eq : (s'.D.filter (fun u => ∃ q ∈ tail, G.Adj q.a u)) =
              (s'.D.filter (fun u => ¬∀ q ∈ tail, ¬G.Adj q.a u)) := by
            ext u
            simp
          rw [h_eq]
          exact card_filter_add_card_filter_not _
        omega
      · exact ih h_own_rest s' hs'

lemma list_sum_card_le_of_pairwise_disjoint {L : List (Finset V)} {U : Finset V}
    (h_disj : L.Pairwise Disjoint) (h_sub : ∀ D ∈ L, D ⊆ U) :
    (L.map Finset.card).sum ≤ U.card := by
  induction L generalizing U with
  | nil => simp
  | cons D rest ih =>
    simp only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp, List.map_cons, List.sum_cons] at h_disj h_sub ⊢
    have h_rest : (rest.map Finset.card).sum ≤ (U \ D).card := by
      apply ih h_disj.2
      intro D' hD' u hu
      rw [Finset.mem_sdiff]
      exact ⟨h_sub.2 D' hD' hu, Finset.disjoint_right.mp (h_disj.1 D' hD') hu⟩
    have h_add : (U \ D).card + D.card = U.card := card_sdiff_add_card_eq_card h_sub.1
    omega

lemma covered_card_le (G : SimpleGraph V) (tail : List (StepData V)) (A : Finset V) (M : ℕ)
    (hM : ∀ q ∈ tail, (neighborFinsetIn G q.a A).card ≤ M) :
    (covered G tail A).card ≤ tail.length * M := by
  induction tail with
  | nil =>
    have : covered G [] A = ∅ := by ext u; simp [covered]
    simp [this]
  | cons q rest ih =>
    have h_sub : covered G (q :: rest) A ⊆ neighborFinsetIn G q.a A ∪ covered G rest A := by
      intro u hu
      unfold covered at hu ⊢
      simp only [mem_filter, List.mem_cons, exists_eq_or_imp, mem_union, mem_neighborFinsetIn] at hu ⊢
      rcases hu with ⟨huA, hq | hrest⟩
      · exact Or.inl ⟨huA, hq⟩
      · exact Or.inr ⟨huA, hrest⟩
    have h_le1 := Finset.card_le_card h_sub
    have h_le2 := Finset.card_union_le (neighborFinsetIn G q.a A) (covered G rest A)
    have h_q := hM q List.mem_cons_self
    have h_ih := ih (fun q' hq' => hM q' (List.mem_cons_of_mem _ hq'))
    simp only [List.length_cons]
    nlinarith

lemma list_sum_le_two_mul_sum {α : Type*} (L : List α) (f g : α → ℕ)
    (h : ∀ x ∈ L, f x ≤ 2 * g x) :
    (L.map f).sum ≤ 2 * (L.map g).sum := by
  induction L with
  | nil => simp
  | cons x rest ih =>
    simp only [List.map_cons, List.sum_cons]
    have hx := h x List.mem_cons_self
    have hrest := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    omega

lemma bucket_volume_le_two_mul_length_mul_head (G : SimpleGraph V) (R₁ : Finset V)
    (s₀ : StepData V) (J_rest : List (StepData V))
    (h_pw : (s₀ :: J_rest).Pairwise (fun s₁ s₂ => Disjoint s₁.D s₂.D ∧ s₂.D ⊆ s₁.A))
    (h_props : ∀ s ∈ s₀ :: J_rest, s.a ∈ R₁ ∧ s.D ⊆ s.A ∧ (∀ u ∈ s.D, G.Adj s.a u) ∧
      ∀ u ∈ R₁, (neighborFinsetIn G u s.A).card ≤ s.D.card) :
    ((s₀ :: J_rest).map (fun s => s.D.card)).sum ≤
      2 * ((backwardClean G (s₀ :: J_rest)).length * s₀.D.card) := by
  set J := s₀ :: J_rest
  set tail := backwardClean G J
  have h_cov_each : ∀ s ∈ J, s.D.card ≤ 2 * (covered G tail s.D).card :=
    backwardClean_covered G J (fun s hs => (h_props s hs).2.2.1)
  have h_sum1 : (J.map (fun s => s.D.card)).sum ≤ 2 * (J.map (fun s => (covered G tail s.D).card)).sum :=
    list_sum_le_two_mul_sum J (fun s => s.D.card) (fun s => (covered G tail s.D).card) h_cov_each
  have h_disj_cov : (J.map (fun s => covered G tail s.D)).Pairwise Disjoint := by
    rw [List.pairwise_map]
    refine h_pw.imp (fun {s₁ s₂} h => ?_)
    exact Disjoint.mono (covered_subset G tail s₁.D) (covered_subset G tail s₂.D) h.1
  have h_sub_cov : ∀ C ∈ J.map (fun s => covered G tail s.D), C ⊆ covered G tail s₀.A := by
    intro C hC
    rw [List.mem_map] at hC
    obtain ⟨s, hs, rfl⟩ := hC
    rw [List.pairwise_cons] at h_pw
    rw [List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact covered_mono_set G tail (h_props s List.mem_cons_self).2.1
    · exact covered_mono_set G tail (h_pw.1 s hs).2
  have h_sum2 : (J.map (fun s => (covered G tail s.D).card)).sum ≤ (covered G tail s₀.A).card := by
    have h_map_eq : J.map (fun s => (covered G tail s.D).card) =
        (J.map (fun s => covered G tail s.D)).map Finset.card := by
      rw [List.map_map]
      rfl
    rw [h_map_eq]
    exact list_sum_card_le_of_pairwise_disjoint h_disj_cov h_sub_cov
  have h_cov_A : (covered G tail s₀.A).card ≤ tail.length * s₀.D.card := by
    apply covered_card_le G tail s₀.A s₀.D.card
    intro q hq
    obtain ⟨s', hs', ha_eq, _, _, _⟩ := backwardClean_sub G J q hq
    rw [ha_eq]
    exact (h_props s₀ List.mem_cons_self).2.2.2 s'.a (h_props s' hs').1
  omega

lemma list_sum_le_sum_range_filter (steps : List (StepData V)) (N : ℕ)
    (P : ℕ → StepData V → Bool)
    (h_cov : ∀ s ∈ steps, ∃ t ∈ Finset.range (N + 1), P t s = true) :
    (steps.map (fun s => s.D.card)).sum ≤
      ∑ t ∈ Finset.range (N + 1), ((steps.filter (fun s => P t s)).map (fun s => s.D.card)).sum := by
  induction steps with
  | nil => simp
  | cons s rest ih =>
    simp only [List.map_cons, List.sum_cons]
    obtain ⟨t₀, ht₀, hPt₀⟩ := h_cov s List.mem_cons_self
    have h_ih := ih (fun s' hs' => h_cov s' (List.mem_cons_of_mem _ hs'))
    have h_s : s.D.card ≤ ∑ t ∈ Finset.range (N + 1), (if P t s then s.D.card else 0) := by
      have h_le := Finset.single_le_sum (f := fun t => if P t s then s.D.card else 0)
        (fun t _ => Nat.zero_le _) ht₀
      simpa [hPt₀] using h_le
    have h_split : ∑ t ∈ Finset.range (N + 1),
        (((s :: rest).filter (fun s' => P t s')).map (fun s' => s'.D.card)).sum =
      ∑ t ∈ Finset.range (N + 1), (if P t s then s.D.card else 0) +
      ∑ t ∈ Finset.range (N + 1), ((rest.filter (fun s' => P t s')).map (fun s' => s'.D.card)).sum := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      cases hP : P t s <;> simp [hP]
    omega

lemma comb_of_stepData_list (G : SimpleGraph V) (S : Finset V) (v : V) (hv : v ∈ S)
    (tail : List (StepData V)) (ℓ : ℕ) (hℓ : ℓ ≤ tail.length) (w : ℝ)
    (h_pw : tail.Pairwise (fun q₁ q₂ =>
      q₁.a ≠ q₂.a ∧ Disjoint q₁.D q₂.D ∧
      (∀ u ∈ q₂.D, ¬G.Adj q₁.a u) ∧ (∀ u ∈ q₁.D, ¬G.Adj q₂.a u)))
    (h_q : ∀ q ∈ tail,
      q.a ∈ (S.erase v) \ neighborFinsetIn G v S ∧
      q.D ⊆ neighborFinsetIn G v S ∧
      q.D.Nonempty ∧
      w ≤ (q.D.card : ℝ) ∧
      ∀ u ∈ q.D, G.Adj q.a u) :
    ∃ (a : Fin ℓ → V) (B : Fin ℓ → Finset V),
      IsCombIn G S ℓ w a B ∧ IsCombExternalApex G S ℓ a B v := by
  let a : Fin ℓ → V := fun i => (tail[i.1]'(by omega)).a
  let B : Fin ℓ → Finset V := fun i => (tail[i.1]'(by omega)).D
  have h_mem : ∀ i : Fin ℓ, tail[i.1]'(by omega) ∈ tail := fun i => List.getElem_mem _
  have h_rel : ∀ i j : Fin ℓ, i ≠ j →
      a i ≠ a j ∧ Disjoint (B i) (B j) ∧ ∀ u ∈ B j, ¬G.Adj (a i) u := by
    intro i j hij
    have hij_val : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
    rcases lt_or_gt_of_ne hij_val with hlt | hgt
    · obtain ⟨hne, hdisj, hnot1, _⟩ := List.pairwise_iff_getElem.mp h_pw i.1 j.1 (by omega) (by omega) hlt
      exact ⟨hne, hdisj, hnot1⟩
    · obtain ⟨hne, hdisj, _, hnot2⟩ := List.pairwise_iff_getElem.mp h_pw j.1 i.1 (by omega) (by omega) hgt
      exact ⟨hne.symm, hdisj.symm, hnot2⟩
  refine ⟨a, B, ?_, ?_⟩
  · refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      exact (h_q _ (h_mem i)).2.1.trans (neighborFinsetIn_subset G v S)
    · intro i
      exact (h_q _ (h_mem i)).2.2.1
    · intro i j hij
      exact (h_rel i j hij).2.1
    · intro i
      exact (h_q _ (h_mem i)).2.2.2.1
    · intro i
      have ha := (h_q _ (h_mem i)).1
      exact mem_of_mem_erase (Finset.mem_sdiff.mp ha).1
    · intro i j hij
      by_contra hne
      exact (h_rel i j hne).1 hij
    · intro i j hu
      have ha := (Finset.mem_sdiff.mp (h_q _ (h_mem i)).1).2
      exact ha ((h_q _ (h_mem j)).2.1 hu)
    · intro i u hu
      exact (h_q _ (h_mem i)).2.2.2.2 u hu
    · intro i j hij u hu
      exact (h_rel i j hij).2.2 u hu
  · refine ⟨hv, ?_, ?_, ?_, ?_⟩
    · intro i h_eq
      have ha := (Finset.mem_sdiff.mp (h_q _ (h_mem i)).1).1
      exact (mem_erase.mp ha).1 h_eq.symm
    · intro i hvB
      exact not_mem_neighborFinsetIn_self G v S ((h_q _ (h_mem i)).2.1 hvB)
    · intro i u hu
      exact (mem_neighborFinsetIn G v S u).mp ((h_q _ (h_mem i)).2.1 hu) |>.2
    · intro i hadj
      have ha := Finset.mem_sdiff.mp (h_q _ (h_mem i)).1
      apply ha.2
      rw [mem_neighborFinsetIn]
      exact ⟨mem_of_mem_erase ha.1, hadj⟩

lemma markov_R1_bound (G : SimpleGraph V) (S : Finset V) (v : V) (hv : v ∈ S)
    (y : ℝ) (hy : 0 < y) (hy_ub : y ≤ (2 : ℝ)⁻¹ ^ 8) (hS : y⁻¹ ^ 4 ≤ (S.card : ℝ))
    (h_sparse : IsEpsSparseOn G S (y ^ 3))
    (hA₀_lb : 2 * y ^ 4 * (S.card : ℝ) < ((neighborFinsetIn G v S).card : ℝ)) :
    (1 - 4 * y) * (S.card : ℝ) ≤
      ((((S.erase v) \ neighborFinsetIn G v S).filter (fun u =>
        ((neighborFinsetIn G u (neighborFinsetIn G v S)).card : ℝ) ≤
          (1 / 2) * y ^ 2 * ((neighborFinsetIn G v S).card : ℝ))).card : ℝ) := by
  set A₀ := neighborFinsetIn G v S
  set R₀ := (S.erase v) \ A₀
  set R₁ := R₀.filter (fun u => ((neighborFinsetIn G u A₀).card : ℝ) ≤ (1 / 2) * y ^ 2 * (A₀.card : ℝ))
  set Bad := R₀.filter (fun u => ¬(((neighborFinsetIn G u A₀).card : ℝ) ≤ (1 / 2) * y ^ 2 * (A₀.card : ℝ)))
  have hA₀_sub_erase : A₀ ⊆ S.erase v := by
    intro u hu
    rw [mem_erase]
    refine ⟨?_, neighborFinsetIn_subset G v S hu⟩
    intro h_eq
    rw [h_eq] at hu
    exact not_mem_neighborFinsetIn_self G v S hu
  have h_card_erase : (S.erase v).card + 1 = S.card := card_erase_add_one hv
  have h_card_R₀ : R₀.card + A₀.card = (S.erase v).card := card_sdiff_add_card_eq_card hA₀_sub_erase
  have h_card_part : R₁.card + Bad.card = R₀.card := card_filter_add_card_filter_not _
  have h_cross_le : ((∑ u ∈ R₀, (neighborFinsetIn G u A₀).card : ℕ) : ℝ) ≤ (A₀.card : ℝ) * (y ^ 3 * (S.card : ℝ)) := by
    have h_comm : ∑ u ∈ R₀, (neighborFinsetIn G u A₀).card = ∑ w ∈ A₀, (neighborFinsetIn G w R₀).card :=
      sum_neighborFinsetIn_card_comm G R₀ A₀
    rw [h_comm]
    push_cast
    have h_each : ∀ w ∈ A₀, ((neighborFinsetIn G w R₀).card : ℝ) ≤ y ^ 3 * (S.card : ℝ) := by
      intro w hw
      have h_sub : R₀ ⊆ S := sdiff_subset.trans (erase_subset v S)
      have h_le_nat : (neighborFinsetIn G w R₀).card ≤ (neighborFinsetIn G w S).card :=
        card_le_card (neighborFinsetIn_mono G w h_sub)
      have h_le_r : ((neighborFinsetIn G w R₀).card : ℝ) ≤ ((neighborFinsetIn G w S).card : ℝ) := by
        exact_mod_cast h_le_nat
      exact h_le_r.trans (h_sparse w (neighborFinsetIn_subset G v S hw))
    calc ∑ w ∈ A₀, ((neighborFinsetIn G w R₀).card : ℝ)
        ≤ ∑ _w ∈ A₀, (y ^ 3 * (S.card : ℝ)) := sum_le_sum h_each
      _ = (A₀.card : ℝ) * (y ^ 3 * (S.card : ℝ)) := by simp
  have h_bad_lb : (Bad.card : ℝ) * ((1 / 2) * y ^ 2 * (A₀.card : ℝ)) ≤
      ((∑ u ∈ R₀, (neighborFinsetIn G u A₀).card : ℕ) : ℝ) := by
    have h_each : ∀ u ∈ Bad, (1 / 2) * y ^ 2 * (A₀.card : ℝ) ≤ ((neighborFinsetIn G u A₀).card : ℝ) := by
      intro u hu
      rw [mem_filter] at hu
      linarith
    have h_sub_sum : ∑ u ∈ Bad, ((neighborFinsetIn G u A₀).card : ℝ) ≤
        ∑ u ∈ R₀, ((neighborFinsetIn G u A₀).card : ℝ) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.cast_nonneg _)
    calc (Bad.card : ℝ) * ((1 / 2) * y ^ 2 * (A₀.card : ℝ))
        = ∑ _u ∈ Bad, ((1 / 2) * y ^ 2 * (A₀.card : ℝ)) := by simp
      _ ≤ ∑ u ∈ Bad, ((neighborFinsetIn G u A₀).card : ℝ) := sum_le_sum h_each
      _ ≤ ∑ u ∈ R₀, ((neighborFinsetIn G u A₀).card : ℝ) := h_sub_sum
      _ = ((∑ u ∈ R₀, (neighborFinsetIn G u A₀).card : ℕ) : ℝ) := by push_cast; rfl
  have hS_pos : (0 : ℝ) < (S.card : ℝ) := lt_of_lt_of_le (by positivity) hS
  have hA₀_pos : (0 : ℝ) < (A₀.card : ℝ) := lt_trans (by positivity) hA₀_lb
  have h_bad_ub : (Bad.card : ℝ) ≤ 2 * y * (S.card : ℝ) := by
    have h_prod : ((Bad.card : ℝ) - 2 * y * (S.card : ℝ)) * ((1 / 2) * y ^ 2 * (A₀.card : ℝ)) ≤ 0 := by
      nlinarith
    have h_pos_fac : (0 : ℝ) < (1 / 2) * y ^ 2 * (A₀.card : ℝ) := by positivity
    nlinarith
  have hA₀_ub : (A₀.card : ℝ) ≤ y ^ 3 * (S.card : ℝ) := h_sparse v hv
  have hy4_S : 1 ≤ y ^ 4 * (S.card : ℝ) := by
    have h_inv : y ^ 4 * y⁻¹ ^ 4 = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hy.ne', one_pow]
    nlinarith [pow_pos hy 4]
  have hy_le_one : y ≤ 1 := by linarith [(by norm_num : (2 : ℝ)⁻¹ ^ 8 ≤ 1)]
  have hy3_le_y : y ^ 3 ≤ y := by nlinarith [sq_nonneg y]
  have hy4_le_y : y ^ 4 ≤ y := by nlinarith [pow_nonneg hy.le 3]
  have h_cards_r : (R₁.card : ℝ) + (Bad.card : ℝ) + (A₀.card : ℝ) + 1 = (S.card : ℝ) := by
    exact_mod_cast (by omega : R₁.card + Bad.card + A₀.card + 1 = S.card)
  nlinarith

lemma rpow_neg_quarter_le_half_inv {y : ℝ} (hy : 0 < y) (hy_ub : y ≤ (2 : ℝ)⁻¹ ^ 8) :
    y ^ (-(1 / 4 : ℝ)) ≤ (1 / 2) * y⁻¹ := by
  have hy_4 : y ≤ (1 / 4 : ℝ) ^ (4 : ℝ) := by
    have : ((2 : ℝ)⁻¹ ^ 8 : ℝ) = (1 / 4 : ℝ) ^ (4 : ℝ) := by norm_num
    linarith
  have h_rpow : y ^ (3 / 4 : ℝ) ≤ ((1 / 4 : ℝ) ^ (4 : ℝ)) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow hy.le hy_4 (by norm_num)
  have h_eval : ((1 / 4 : ℝ) ^ (4 : ℝ)) ^ (3 / 4 : ℝ) = 1 / 64 := by
    rw [← Real.rpow_mul (by norm_num)]
    norm_num
  have h_prod : y ^ (-(1 / 4 : ℝ)) * y = y ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_add_one hy.ne']
    ring_nf
  have h_inv_pos : 0 < y⁻¹ := inv_pos.mpr hy
  have h_le : (y ^ (-(1 / 4 : ℝ)) * y) * y⁻¹ ≤ (1 / 2) * y⁻¹ := by
    nlinarith
  rwa [mul_assoc, mul_inv_cancel₀ hy.ne', mul_one] at h_le

lemma dyadic_scale_comb_bounds {x y : ℝ} {S_card A₀_card t L_len D₀_card ℓ : ℕ}
    (hx : 0 < x) (hxy : x ≤ y) (hy_ub : y ≤ (2 : ℝ)⁻¹ ^ 8)
    (hS : y⁻¹ ^ 4 ≤ (S_card : ℝ))
    (hA₀_lb : 2 * y ^ 4 * (S_card : ℝ) < (A₀_card : ℝ))
    (h_bucket_vol : (1 / ((t : ℝ) + 1) ^ 2) * ((1 / 4) * (A₀_card : ℝ)) <
      2 * ((L_len : ℝ) * (D₀_card : ℝ)))
    (h_D₀_ub : (2 : ℝ) ^ t * (D₀_card : ℝ) ≤ (1 / 2) * y ^ 2 * (A₀_card : ℝ))
    (hℓ_def : ℓ = min L_len ⌊x⁻¹⌋₊) :
    ℓ ≤ L_len ∧
    y ^ (-(1 / 4 : ℝ)) ≤ (ℓ : ℝ) ∧
    (ℓ : ℝ) ≤ x⁻¹ ∧
    ∀ (s_D_card q_D_card : ℕ),
      (1 / 2) * y ^ 2 * (A₀_card : ℝ) < (2 : ℝ) ^ (t + 1) * (s_D_card : ℝ) →
      x * (y ^ 4 * (S_card : ℝ)) < (s_D_card : ℝ) →
      s_D_card ≤ 2 * q_D_card →
      1 ≤ q_D_card ∧ y ^ 4 * (S_card : ℝ) / (ℓ : ℝ) ^ 2 ≤ (q_D_card : ℝ) := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hS_pos : (0 : ℝ) < (S_card : ℝ) := lt_of_lt_of_le (by positivity) hS
  have hA₀_pos : (0 : ℝ) < (A₀_card : ℝ) := lt_trans (by positivity) hA₀_lb
  have ht1_pos : (0 : ℝ) < ((t : ℝ) + 1) ^ 2 := by positivity
  have h2t_pos : (0 : ℝ) < (2 : ℝ) ^ t := by positivity
  have h_vol1 : (1 / 4) * (A₀_card : ℝ) * (2 : ℝ) ^ t <
      2 * (L_len : ℝ) * ((2 : ℝ) ^ t * (D₀_card : ℝ)) * ((t : ℝ) + 1) ^ 2 := by
    have h1 := mul_lt_mul_of_pos_right h_bucket_vol (mul_pos ht1_pos h2t_pos)
    have h_lhs : (1 / ((t : ℝ) + 1) ^ 2) * ((1 / 4) * (A₀_card : ℝ)) * (((t : ℝ) + 1) ^ 2 * (2 : ℝ) ^ t) =
        (1 / 4) * (A₀_card : ℝ) * (2 : ℝ) ^ t := by
      field_simp
    linarith
  have h_L_pos_r : 0 ≤ (L_len : ℝ) := Nat.cast_nonneg _
  have h_vol2 : 2 * (L_len : ℝ) * ((2 : ℝ) ^ t * (D₀_card : ℝ)) * ((t : ℝ) + 1) ^ 2 ≤
      (L_len : ℝ) * y ^ 2 * ((t : ℝ) + 1) ^ 2 * (A₀_card : ℝ) := by
    calc 2 * (L_len : ℝ) * ((2 : ℝ) ^ t * (D₀_card : ℝ)) * ((t : ℝ) + 1) ^ 2
        = (2 * (L_len : ℝ) * ((t : ℝ) + 1) ^ 2) * ((2 : ℝ) ^ t * (D₀_card : ℝ)) := by ring
      _ ≤ (2 * (L_len : ℝ) * ((t : ℝ) + 1) ^ 2) * ((1 / 2) * y ^ 2 * (A₀_card : ℝ)) :=
        mul_le_mul_of_nonneg_left h_D₀_ub (by positivity)
      _ = (L_len : ℝ) * y ^ 2 * ((t : ℝ) + 1) ^ 2 * (A₀_card : ℝ) := by ring
  have h_2t_lt : (2 : ℝ) ^ t < 4 * ((t : ℝ) + 1) ^ 2 * y ^ 2 * (L_len : ℝ) := by
    have h_mul : ((1 / 4) * (A₀_card : ℝ)) * (2 : ℝ) ^ t <
        ((1 / 4) * (A₀_card : ℝ)) * (4 * ((t : ℝ) + 1) ^ 2 * y ^ 2 * (L_len : ℝ)) := by
      calc ((1 / 4) * (A₀_card : ℝ)) * (2 : ℝ) ^ t
          < 2 * (L_len : ℝ) * ((2 : ℝ) ^ t * (D₀_card : ℝ)) * ((t : ℝ) + 1) ^ 2 := h_vol1
        _ ≤ (L_len : ℝ) * y ^ 2 * ((t : ℝ) + 1) ^ 2 * (A₀_card : ℝ) := h_vol2
        _ = ((1 / 4) * (A₀_card : ℝ)) * (4 * ((t : ℝ) + 1) ^ 2 * y ^ 2 * (L_len : ℝ)) := by ring
    exact lt_of_mul_lt_mul_left h_mul (by positivity)
  have h_sq_pow : 4 * ((t : ℝ) + 1) ^ 2 ≤ 9 * (2 : ℝ) ^ t := by
    exact_mod_cast nat_sq_bound_two_pow t
  have h_L_lb1 : 1 < 9 * y ^ 2 * (L_len : ℝ) := by
    have h_mul : (2 : ℝ) ^ t * 1 < (2 : ℝ) ^ t * (9 * y ^ 2 * (L_len : ℝ)) := by
      calc (2 : ℝ) ^ t * 1
          = (2 : ℝ) ^ t := by ring
        _ < (4 * ((t : ℝ) + 1) ^ 2) * (y ^ 2 * (L_len : ℝ)) := by
          linarith only [h_2t_lt]
        _ ≤ (9 * (2 : ℝ) ^ t) * (y ^ 2 * (L_len : ℝ)) :=
          mul_le_mul_of_nonneg_right h_sq_pow (by positivity)
        _ = (2 : ℝ) ^ t * (9 * y ^ 2 * (L_len : ℝ)) := by ring
    exact lt_of_mul_lt_mul_left h_mul h2t_pos.le
  have hy_256 : 256 * y ≤ 1 := by
    have : (2 : ℝ)⁻¹ ^ 8 = 1 / 256 := by norm_num
    linarith only [hy_ub, this]
  have h_L_lb2 : (1 / 2) * y⁻¹ ≤ (L_len : ℝ) := by
    have hy_inv_pos : 0 < y⁻¹ := inv_pos.mpr hy
    have h9y : 9 * y ≤ 1 := by linarith only [hy_256, hy]
    have h9y2 : 9 * y ^ 2 * (L_len : ℝ) ≤ y * (L_len : ℝ) := by
      calc 9 * y ^ 2 * (L_len : ℝ)
          = (9 * y) * (y * (L_len : ℝ)) := by ring
        _ ≤ 1 * (y * (L_len : ℝ)) := mul_le_mul_of_nonneg_right h9y (by positivity)
        _ = y * (L_len : ℝ) := by ring
    have h1_lt : 1 < y * (L_len : ℝ) := lt_of_lt_of_le h_L_lb1 h9y2
    have h_mul := mul_lt_mul_of_pos_left h1_lt hy_inv_pos
    rw [← mul_assoc, inv_mul_cancel₀ hy.ne', one_mul] at h_mul
    linarith only [h_mul, hy_inv_pos]
  have hx_256 : 256 ≤ x⁻¹ := by
    have hx_le : x ≤ 256⁻¹ := by linarith only [hxy, hy_256]
    rwa [le_inv_comm₀ (by norm_num) hx]
  have hy_inv_le_x_inv : y⁻¹ ≤ x⁻¹ := inv_anti₀ hx hxy
  have h_floor_gt : x⁻¹ - 1 < (⌊x⁻¹⌋₊ : ℝ) := Nat.sub_one_lt_floor _
  have h_floor_lb : (1 / 2) * x⁻¹ ≤ (⌊x⁻¹⌋₊ : ℝ) := by linarith only [hx_256, h_floor_gt]
  have h_min : ℓ = L_len ∨ ℓ = ⌊x⁻¹⌋₊ := hℓ_def ▸ min_choice L_len ⌊x⁻¹⌋₊
  have h_ell_lb : (1 / 2) * y⁻¹ ≤ (ℓ : ℝ) := by
    rcases h_min with h_eq | h_eq <;> rw [h_eq] <;> linarith only [h_L_lb2, h_floor_lb, hy_inv_le_x_inv]
  have h_rpow_le : y ^ (-(1 / 4 : ℝ)) ≤ (ℓ : ℝ) :=
    (rpow_neg_quarter_le_half_inv hy hy_ub).trans h_ell_lb
  have h_ell_ub : (ℓ : ℝ) ≤ x⁻¹ := by
    have h1 : (ℓ : ℝ) ≤ (⌊x⁻¹⌋₊ : ℝ) := by
      rw [hℓ_def]
      exact_mod_cast Nat.min_le_right L_len ⌊x⁻¹⌋₊
    exact h1.trans (Nat.floor_le (by positivity))
  have hℓ_le_L : ℓ ≤ L_len := hℓ_def ▸ Nat.min_le_left _ _
  refine ⟨hℓ_le_L, h_rpow_le, h_ell_ub, ?_⟩
  intro s_D_card q_D_card hs_lb1 hs_lb2 hq_lb
  have hs_pos_r : (0 : ℝ) < (s_D_card : ℝ) := lt_trans (by positivity) hs_lb2
  have hq_r : (s_D_card : ℝ) ≤ 2 * (q_D_card : ℝ) := by exact_mod_cast hq_lb
  have hq_pos_r : (0 : ℝ) < (q_D_card : ℝ) := by linarith
  have hq_ge_one : 1 ≤ q_D_card := by exact_mod_cast hq_pos_r
  refine ⟨hq_ge_one, ?_⟩
  have h_ell_pos : (0 : ℝ) < (ℓ : ℝ) := by
    have : (0 : ℝ) < (1 / 2) * y⁻¹ := by positivity
    linarith
  rw [div_le_iff₀ (sq_pos_of_pos h_ell_pos)]
  rcases h_min with h_eq | h_eq
  · -- Subcase 1: ℓ = L_len
    rw [h_eq]
    have h_fourth : ((t : ℝ) + 1) ^ 4 ≤ 1024 * (2 : ℝ) ^ t := by
      exact_mod_cast nat_fourth_bound_two_pow t
    have h_64_2t : 64 * (2 : ℝ) ^ t ≤ ((t : ℝ) + 1) ^ 2 * (y * (L_len : ℝ)) := by
      calc 64 * (2 : ℝ) ^ t
          ≤ 64 * (4 * ((t : ℝ) + 1) ^ 2 * y ^ 2 * (L_len : ℝ)) := by linarith only [h_2t_lt]
        _ = (256 * y) * (((t : ℝ) + 1) ^ 2 * (y * (L_len : ℝ))) := by ring
        _ ≤ 1 * (((t : ℝ) + 1) ^ 2 * (y * (L_len : ℝ))) :=
          mul_le_mul_of_nonneg_right hy_256 (by positivity)
        _ = ((t : ℝ) + 1) ^ 2 * (y * (L_len : ℝ)) := by ring
    have h_1024 : (1024 * (2 : ℝ) ^ t) * (4 * (2 : ℝ) ^ t) ≤
        (1024 * (2 : ℝ) ^ t) * (y ^ 2 * (L_len : ℝ) ^ 2) := by
      calc (1024 * (2 : ℝ) ^ t) * (4 * (2 : ℝ) ^ t)
          = (64 * (2 : ℝ) ^ t) * (64 * (2 : ℝ) ^ t) := by ring
        _ ≤ (((t : ℝ) + 1) ^ 2 * (y * (L_len : ℝ))) * (((t : ℝ) + 1) ^ 2 * (y * (L_len : ℝ))) :=
          mul_le_mul h_64_2t h_64_2t (by positivity) (by positivity)
        _ = ((t : ℝ) + 1) ^ 4 * (y ^ 2 * (L_len : ℝ) ^ 2) := by ring
        _ ≤ (1024 * (2 : ℝ) ^ t) * (y ^ 2 * (L_len : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right h_fourth (by positivity)
    have h_4_2t : 4 * (2 : ℝ) ^ t ≤ y ^ 2 * (L_len : ℝ) ^ 2 :=
      le_of_mul_le_mul_left h_1024 (by positivity)
    have h_q_2t : y ^ 6 * (S_card : ℝ) ≤ (4 * (2 : ℝ) ^ t) * (q_D_card : ℝ) := by
      calc y ^ 6 * (S_card : ℝ)
          = (1 / 2) * y ^ 2 * (2 * y ^ 4 * (S_card : ℝ)) := by ring
        _ ≤ (1 / 2) * y ^ 2 * (A₀_card : ℝ) :=
          mul_le_mul_of_nonneg_left hA₀_lb.le (by positivity)
        _ ≤ (2 : ℝ) ^ (t + 1) * (s_D_card : ℝ) := hs_lb1.le
        _ ≤ (2 : ℝ) ^ (t + 1) * (2 * (q_D_card : ℝ)) :=
          mul_le_mul_of_nonneg_left hq_r (by positivity)
        _ = (4 * (2 : ℝ) ^ t) * (q_D_card : ℝ) := by
          rw [pow_succ]
          ring
    have h_y6 : y ^ 2 * (y ^ 4 * (S_card : ℝ)) ≤ y ^ 2 * ((q_D_card : ℝ) * (L_len : ℝ) ^ 2) := by
      calc y ^ 2 * (y ^ 4 * (S_card : ℝ))
          = y ^ 6 * (S_card : ℝ) := by ring
        _ ≤ (4 * (2 : ℝ) ^ t) * (q_D_card : ℝ) := h_q_2t
        _ ≤ (y ^ 2 * (L_len : ℝ) ^ 2) * (q_D_card : ℝ) :=
          mul_le_mul_of_nonneg_right h_4_2t (Nat.cast_nonneg _)
        _ = y ^ 2 * ((q_D_card : ℝ) * (L_len : ℝ) ^ 2) := by ring
    exact le_of_mul_le_mul_left h_y6 (sq_pos_of_pos hy)
  · -- Subcase 2: ℓ = ⌊x⁻¹⌋₊
    rw [h_eq]
    have h_floor_128 : 128 ≤ (⌊x⁻¹⌋₊ : ℝ) := by linarith only [hx_256, h_floor_lb]
    have h_sq_lb : 2 * x⁻¹ ≤ (⌊x⁻¹⌋₊ : ℝ) ^ 2 := by
      calc 2 * x⁻¹
          = 4 * ((1 / 2) * x⁻¹) := by ring
        _ ≤ 128 * (⌊x⁻¹⌋₊ : ℝ) := by linarith only [h_floor_lb, h_floor_128]
        _ ≤ (⌊x⁻¹⌋₊ : ℝ) * (⌊x⁻¹⌋₊ : ℝ) :=
          mul_le_mul_of_nonneg_right h_floor_128 (by positivity)
        _ = (⌊x⁻¹⌋₊ : ℝ) ^ 2 := by ring
    have h_x_inv_pos : 0 < x⁻¹ := inv_pos.mpr hx
    have h_prod : (y ^ 4 * (S_card : ℝ)) ≤ (2 * (q_D_card : ℝ)) * x⁻¹ := by
      have h1 : x * (y ^ 4 * (S_card : ℝ)) ≤ 2 * (q_D_card : ℝ) := by linarith only [hs_lb2, hq_r]
      have h2 := mul_le_mul_of_nonneg_right h1 h_x_inv_pos.le
      rwa [mul_comm x _, mul_assoc, mul_inv_cancel₀ hx.ne', mul_one] at h2
    calc y ^ 4 * (S_card : ℝ)
        ≤ (2 * (q_D_card : ℝ)) * x⁻¹ := h_prod
      _ = (q_D_card : ℝ) * (2 * x⁻¹) := by ring
      _ ≤ (q_D_card : ℝ) * (⌊x⁻¹⌋₊ : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left h_sq_lb (Nat.cast_nonneg _)

/--
**Lemma 2.6 (Upside-Down Comb Extraction Lemma)** (`lem:comb-extraction` in `FMBV4-016_readable.tex`).
Let $0 < x \le y \le 2^{-8}$ and let $G$ be a $y^3$-sparse graph on $S \subseteq V$ with $|S| \ge y^{-4}$.
Then one of the following holds:
1. $S$ is $2 y^4$-sparse in $G$ (`IsEpsSparseOn G S (2 * y ^ 4)`);
2. there exist disjoint subsets $X, Y \subseteq S$ with $|X| \ge y^4 |S|$ and $|Y| \ge (1 - 4 y) |S|$
   such that $Y$ is $x$-sparse to $X$ in $G$ (`IsXSparseTo G Y X x`); or
3. there exist $\ell \in [y^{-1/4}, x^{-1}]$, an $(\ell, \frac{y^4 |S|}{\ell^2})$-comb $(a, B)$ in $S$,
   and an external apex $v \in S$ (`IsCombExternalApex G S ℓ a B v`).
-/
theorem upside_down_comb_extraction (G : SimpleGraph V) (S : Finset V) (x y : ℝ)
    (hx : 0 < x) (hxy : x ≤ y) (hy_ub : y ≤ (2 : ℝ)⁻¹ ^ 8)
    (h_sparse : IsEpsSparseOn G S (y ^ 3))
    (hS : y⁻¹ ^ 4 ≤ (S.card : ℝ)) :
    IsEpsSparseOn G S (2 * y ^ 4) ∨
    (∃ X Y : Finset V, X ⊆ S ∧ Y ⊆ S ∧ Disjoint X Y ∧
      y ^ 4 * (S.card : ℝ) ≤ (X.card : ℝ) ∧
      (1 - 4 * y) * (S.card : ℝ) ≤ (Y.card : ℝ) ∧
      IsXSparseTo G Y X x) ∨
    (∃ (ℓ : ℕ) (a : Fin ℓ → V) (B : Fin ℓ → Finset V) (v : V),
      y ^ (-(1 / 4 : ℝ)) ≤ (ℓ : ℝ) ∧ (ℓ : ℝ) ≤ x⁻¹ ∧
      IsCombIn G S ℓ (y ^ 4 * (S.card : ℝ) / (ℓ : ℝ) ^ 2) a B ∧
      IsCombExternalApex G S ℓ a B v) := by
  by_cases h1 : IsEpsSparseOn G S (2 * y ^ 4)
  · exact Or.inl h1
  right
  unfold IsEpsSparseOn at h1
  push_neg at h1
  obtain ⟨v, hv, hA₀_lb⟩ := h1
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hS_pos : (0 : ℝ) < (S.card : ℝ) := lt_of_lt_of_le (by positivity) hS
  set A₀ := neighborFinsetIn G v S
  set R₀ := (S.erase v) \ A₀
  set R₁ := R₀.filter (fun u => ((neighborFinsetIn G u A₀).card : ℝ) ≤ (1 / 2) * y ^ 2 * (A₀.card : ℝ))
  have hR₁_card : (1 - 4 * y) * (S.card : ℝ) ≤ (R₁.card : ℝ) :=
    markov_R1_bound G S v hv y hy hy_ub hS h_sparse hA₀_lb
  set minA := y ^ 4 * (S.card : ℝ)
  have hminA_pos : 0 < minA := by positivity
  set res := forwardSteps G R₁ x minA A₀.card A₀
  set steps := res.1
  set A_end := res.2
  obtain ⟨hA_end_sub, h_steps_sub⟩ := forwardSteps_subset G R₁ x minA A₀.card A₀
  have h_steps_props := forwardSteps_props G R₁ x minA A₀.card A₀
  obtain ⟨h_sum_eq, h_term⟩ := forwardSteps_sum_and_terminal G R₁ x minA hx hminA_pos A₀.card A₀ le_rfl
  by_cases h2 : minA ≤ (A_end.card : ℝ)
  · left
    refine ⟨A_end, R₁, hA_end_sub.trans (neighborFinsetIn_subset G v S),
      (filter_subset _ _).trans (sdiff_subset.trans (erase_subset v S)), ?_, h2, hR₁_card, ?_⟩
    · exact Disjoint.mono hA_end_sub ((filter_subset _ _).trans Subset.rfl) disjoint_sdiff_self_right
    · intro u hu
      by_contra h_gt
      push_neg at h_gt
      exact h_term ⟨h2, u, hu, h_gt⟩
  · right
    push_neg at h2
    have h_sum_gt : (1 / 2) * (A₀.card : ℝ) < (((steps.map (fun s => s.D.card)).sum : ℕ) : ℝ) := by
      have h_sum_r : (((steps.map (fun s => s.D.card)).sum : ℕ) : ℝ) + (A_end.card : ℝ) = (A₀.card : ℝ) := by
        exact_mod_cast h_sum_eq
      linarith
    set W := (1 / 2) * y ^ 2 * (A₀.card : ℝ)
    let P (t : ℕ) (s : StepData V) : Bool :=
      decide ((2 : ℝ) ^ t * (s.D.card : ℝ) ≤ W ∧ W < (2 : ℝ) ^ (t + 1) * (s.D.card : ℝ))
    have hW_le_A₀ : W ≤ (A₀.card : ℝ) := by
      dsimp only [W]
      have h_y2 : (1 / 2) * y ^ 2 ≤ 1 := by
        have : y ≤ 1 := by linarith [(by norm_num : (2 : ℝ)⁻¹ ^ 8 ≤ 1)]
        nlinarith [sq_nonneg y]
      have hA₀_nn : (0 : ℝ) ≤ (A₀.card : ℝ) := Nat.cast_nonneg _
      nlinarith
    have h_each_s : ∀ s ∈ steps, 1 ≤ s.D.card ∧ x * minA < (s.D.card : ℝ) ∧ (s.D.card : ℝ) ≤ W ∧
        (∀ u ∈ s.D, G.Adj s.a u) := by
      intro s hs
      obtain ⟨ha, hD_eq, hA_ge, hD_gt, _⟩ := h_steps_props s hs
      obtain ⟨hD_sub_A, hA_sub_A₀⟩ := h_steps_sub s hs
      have hD_gt_min : x * minA < (s.D.card : ℝ) := by nlinarith
      have hD_pos_r : (0 : ℝ) < (s.D.card : ℝ) := lt_trans (by positivity) hD_gt_min
      have hD_ge_1 : 1 ≤ s.D.card := by exact_mod_cast hD_pos_r
      have hD_sub_A₀ : s.D ⊆ neighborFinsetIn G s.a A₀ := by
        rw [hD_eq]
        exact neighborFinsetIn_mono G s.a hA_sub_A₀
      have hD_le_W : (s.D.card : ℝ) ≤ W := by
        have h_le_nat : s.D.card ≤ (neighborFinsetIn G s.a A₀).card := card_le_card hD_sub_A₀
        have h_le_r : (s.D.card : ℝ) ≤ ((neighborFinsetIn G s.a A₀).card : ℝ) := by exact_mod_cast h_le_nat
        exact h_le_r.trans (mem_filter.mp ha).2
      have h_adj : ∀ u ∈ s.D, G.Adj s.a u := by
        intro u hu
        rw [hD_eq, mem_neighborFinsetIn] at hu
        exact hu.2
      exact ⟨hD_ge_1, hD_gt_min, hD_le_W, h_adj⟩
    have h_cov : ∀ s ∈ steps, ∃ t ∈ Finset.range (A₀.card + 1), P t s = true := by
      intro s hs
      obtain ⟨h1_s, _, hW_s, _⟩ := h_each_s s hs
      have h1_r : (1 : ℝ) ≤ (s.D.card : ℝ) := by exact_mod_cast h1_s
      obtain ⟨t, ht, hPt⟩ := exists_dyadic_bucket h1_r hW_s hW_le_A₀
      exact ⟨t, ht, decide_eq_true hPt⟩
    have h_sum_buckets_nat := list_sum_le_sum_range_filter steps A₀.card P h_cov
    have h_sum_buckets : (((steps.map (fun s => s.D.card)).sum : ℕ) : ℝ) ≤
        ∑ t ∈ Finset.range (A₀.card + 1), ((((steps.filter (fun s => P t s)).map (fun s => s.D.card)).sum : ℕ) : ℝ) := by
      exact_mod_cast h_sum_buckets_nat
    have h_inv_sum : ∑ t ∈ Finset.range (A₀.card + 1), (1 / ((t : ℝ) + 1) ^ 2) * ((1 / 4) * (A₀.card : ℝ)) <
        (1 / 2) * (A₀.card : ℝ) := by
      rw [← Finset.sum_mul]
      have h_le := sum_inv_sq_le A₀.card
      have hA₀_pos : (0 : ℝ) < (A₀.card : ℝ) := lt_trans (by positivity) hA₀_lb
      have h_pos_inv : (0 : ℝ) < 1 / ((A₀.card : ℝ) + 1) := by positivity
      nlinarith
    obtain ⟨t, ht_mem, ht_gt⟩ := Finset.exists_lt_of_sum_lt (h_inv_sum.trans (h_sum_gt.trans_le h_sum_buckets))
    set J := steps.filter (fun s => P t s)
    have hJ_sub : ∀ s ∈ J, s ∈ steps ∧
        ((2 : ℝ) ^ t * (s.D.card : ℝ) ≤ W ∧ W < (2 : ℝ) ^ (t + 1) * (s.D.card : ℝ)) := by
      intro s hs
      rw [List.mem_filter] at hs
      exact ⟨hs.1, of_decide_eq_true hs.2⟩
    have h_pw_steps : steps.Pairwise (fun s₁ s₂ =>
        s₁.a ≠ s₂.a ∧ Disjoint s₁.D s₂.D ∧ s₂.D ⊆ s₁.A ∧ ∀ u ∈ s₂.D, ¬G.Adj s₁.a u) := by
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      have h_sub_ij := List.pairwise_iff_getElem.mp (forwardSteps_pairwise G R₁ x minA A₀.card A₀) i j hi hj hij
      have hi_mem : steps[i] ∈ steps := List.getElem_mem _
      have hj_mem : steps[j] ∈ steps := List.getElem_mem _
      exact stepData_rel_props G (h_steps_props _ hi_mem).2.1 (h_steps_props _ hj_mem).2.1
        (h_each_s _ hj_mem).1 h_sub_ij
    have h_pw_J := h_pw_steps.filter (fun s => P t s)
    cases hJ_eq : J with
    | nil =>
      rw [hJ_eq] at ht_gt
      simp only [List.map_nil, List.sum_nil] at ht_gt
      push_cast at ht_gt
      have hA₀_pos : (0 : ℝ) < (A₀.card : ℝ) := lt_trans (by positivity) hA₀_lb
      have : (0 : ℝ) < (1 / ((t : ℝ) + 1) ^ 2) * ((1 / 4) * (A₀.card : ℝ)) := by positivity
      linarith
    | cons s₀ J_rest =>
      have h_vol_nat : ((s₀ :: J_rest).map (fun s => s.D.card)).sum ≤
          2 * ((backwardClean G (s₀ :: J_rest)).length * s₀.D.card) := by
        apply bucket_volume_le_two_mul_length_mul_head G R₁ s₀ J_rest
        · rw [← hJ_eq]
          exact h_pw_J.imp (fun h => ⟨h.2.1, h.2.2.1⟩)
        · intro s hs
          rw [← hJ_eq] at hs
          have hs_steps := (hJ_sub s hs).1
          exact ⟨(h_steps_props s hs_steps).1, (h_steps_sub s hs_steps).1,
            (h_each_s s hs_steps).2.2.2, (h_steps_props s hs_steps).2.2.2.2⟩
      set tail := backwardClean G (s₀ :: J_rest)
      have h_vol_r : ((((s₀ :: J_rest).map (fun s => s.D.card)).sum : ℕ) : ℝ) ≤
          2 * ((tail.length : ℝ) * (s₀.D.card : ℝ)) := by
        exact_mod_cast h_vol_nat
      rw [hJ_eq] at ht_gt
      have hs₀_P := (hJ_sub s₀ (hJ_eq ▸ List.mem_cons_self)).2
      set ℓ := min tail.length ⌊x⁻¹⌋₊
      obtain ⟨hℓ_le, hℓ_lb, hℓ_ub, h_q_bounds⟩ := dyadic_scale_comb_bounds hx hxy hy_ub hS hA₀_lb
        (ht_gt.trans_le h_vol_r) hs₀_P.1 rfl
      have h_pw_tail : tail.Pairwise (fun q₁ q₂ =>
          q₁.a ≠ q₂.a ∧ Disjoint q₁.D q₂.D ∧
          (∀ u ∈ q₂.D, ¬G.Adj q₁.a u) ∧ (∀ u ∈ q₁.D, ¬G.Adj q₂.a u)) := by
        apply backwardClean_pairwise G (s₀ :: J_rest)
        rw [← hJ_eq]
        exact h_pw_J.imp (fun h => ⟨h.1, h.2.1, h.2.2.2⟩)
      obtain ⟨a, B, h_comb, h_ext⟩ := comb_of_stepData_list G S v hv tail ℓ hℓ_le
        (y ^ 4 * (S.card : ℝ) / (ℓ : ℝ) ^ 2) h_pw_tail (by
          intro q hq
          obtain ⟨s, hs_mem, ha_eq, _, hD_sub, hD_card⟩ := backwardClean_sub G (s₀ :: J_rest) q hq
          rw [← hJ_eq] at hs_mem
          obtain ⟨hs_steps, hs_Pt⟩ := hJ_sub s hs_mem
          obtain ⟨hq_ge_1, hq_w⟩ := h_q_bounds s.D.card q.D.card hs_Pt.2 (h_each_s s hs_steps).2.1 hD_card
          refine ⟨?_, ?_, Finset.card_pos.mp (by omega), hq_w, ?_⟩
          · rw [ha_eq]
            exact mem_filter.mp (h_steps_props s hs_steps).1 |>.1
          · exact hD_sub.trans ((h_steps_sub s hs_steps).1.trans (h_steps_sub s hs_steps).2)
          · intro u hu
            rw [ha_eq]
            exact (h_each_s s hs_steps).2.2.2 u (hD_sub hu))
      exact ⟨ℓ, a, B, v, hℓ_lb, hℓ_ub, h_comb, h_ext⟩

end CombExtraction

/-! ### Lemma 2.3 & Proposition 3.2: 2-Vertex Twin Substitution and the 7-Vertex Witness Graph -/

/--
If `H` satisfies the Erdős–Hajnal property, then so does its complement `Hᶜ`.
-/
theorem HasErdosHajnalProp.compl {α : Type*} {H : SimpleGraph α}
    (h : HasErdosHajnalProp H) : HasErdosHajnalProp Hᶜ := by
  obtain ⟨c, hc, h_bound⟩ := h
  refine ⟨c, hc, fun V _ _ G hG => ?_⟩
  have hG_compl : IsInducedSubgraphFree Gᶜ H := by
    rw [isInducedSubgraphFree_compl_iff, compl_compl]
    exact hG
  have h_le := h_bound V Gᶜ hG_compl
  rwa [kappa_compl] at h_le

/--
To establish `HasErdosHajnalProp H`, it suffices to prove the bound `(n : ℝ) ^ c₀ ≤ (kappa G : ℝ)`
for all `G : SimpleGraph (Fin n)` with `n ≥ N₀` (where `N₀ ≥ 2` and `c₀ > 0`).
-/
theorem hasErdosHajnalProp_of_large_n {α : Type*} [Fintype α] [DecidableEq α]
    (H : SimpleGraph α) {N₀ : ℕ} (hN₀ : 2 ≤ N₀) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (h_large : ∀ (n : ℕ), N₀ ≤ n → ∀ (G : SimpleGraph (Fin n)),
      IsInducedSubgraphFree G H → (n : ℝ) ^ c₀ ≤ (kappa G : ℝ)) :
    HasErdosHajnalProp H := by
  obtain ⟨c, hc, _, _, h_fintype⟩ := erdos_hajnal_all_n_of_large_n H hN₀ hc₀ h_large
  refine ⟨c, hc, fun V _ _ G hG => ?_⟩
  rw [kappa_cast_ge_iff]
  rcases h_fintype V G ((isInducedSubgraphFree_iff_isEmpty_embedding G H).mp hG) with h1 | h2
  · exact Or.inl h1
  · exact Or.inr h2

theorem cliqueNum_comap_le {α β : Type*} [Fintype α] [Fintype β] (G : SimpleGraph β) (f : α ↪ β) :
    (G.comap f).cliqueNum ≤ G.cliqueNum := by
  obtain ⟨s, hs⟩ := (G.comap f).exists_isNClique_cliqueNum
  have hs' := isNClique_of_comap hs
  exact hs'.card_eq ▸ hs'.isClique.card_le_cliqueNum

theorem indepNum_comap_le {α β : Type*} [Fintype α] [Fintype β] (G : SimpleGraph β) (f : α ↪ β) :
    (G.comap f).indepNum ≤ G.indepNum := by
  rw [← cliqueNum_compl, ← cliqueNum_compl (G := G), comap_compl]
  exact cliqueNum_comap_le Gᶜ f

theorem kappa_comap_le {α β : Type*} [Fintype α] [Fintype β] (G : SimpleGraph β) (f : α ↪ β) :
    kappa (G.comap f) ≤ kappa G :=
  max_le ((cliqueNum_comap_le G f).trans (cliqueNum_le_kappa G))
    ((indepNum_comap_le G f).trans (indepNum_le_kappa G))

/--
`IsTwinExtension H₀ H v₀ u₂ ι` states that `H : SimpleGraph (Fin (k + 1))` is obtained from
`H₀ : SimpleGraph (Fin k)` by substituting a 2-vertex graph ($K_2$ or $\overline{K_2}$) for vertex
`v₀ : Fin k`, producing twin vertices `ι v₀` and `u₂` in `H`.
-/
structure IsTwinExtension {k : ℕ} (H₀ : SimpleGraph (Fin k)) (H : SimpleGraph (Fin (k + 1)))
    (v₀ : Fin k) (u₂ : Fin (k + 1)) (ι : Fin k ↪ Fin (k + 1)) : Prop where
  h_miss : ∀ w : Fin k, ι w ≠ u₂
  h_comap : H.comap ι = H₀
  h_twin : ∀ w : Fin k, w ≠ v₀ → (H.Adj (ι w) u₂ ↔ H₀.Adj w v₀)

theorem IsTwinExtension.eq_or_exists {k : ℕ} {H₀ : SimpleGraph (Fin k)}
    {H : SimpleGraph (Fin (k + 1))} {v₀ : Fin k} {u₂ : Fin (k + 1)} {ι : Fin k ↪ Fin (k + 1)}
    (h_ext : IsTwinExtension H₀ H v₀ u₂ ι) (x : Fin (k + 1)) :
    x = u₂ ∨ ∃ w : Fin k, ι w = x := by
  have h_not_mem : u₂ ∉ (Finset.univ : Finset (Fin k)).map ι := by
    simp only [Finset.mem_map, Finset.mem_univ, true_and, not_exists]
    exact h_ext.h_miss
  have h_card : (insert u₂ ((Finset.univ : Finset (Fin k)).map ι)).card =
      (Finset.univ : Finset (Fin (k + 1))).card := by
    rw [Finset.card_insert_of_notMem h_not_mem, Finset.card_map, Finset.card_fin, Finset.card_fin]
  have h_eq : insert u₂ ((Finset.univ : Finset (Fin k)).map ι) = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (le_of_eq h_card.symm)
  have hx : x ∈ insert u₂ ((Finset.univ : Finset (Fin k)).map ι) := by
    rw [h_eq]
    exact Finset.mem_univ x
  simpa [Finset.mem_insert, Finset.mem_map] using hx

def blockEmb {m s n : ℕ} (hms : m * s ≤ n) (i : Fin m) (j : Fin s) : Fin n :=
  ⟨i.1 * s + j.1, by
    have hi : (i.1 + 1) * s ≤ m * s := Nat.mul_le_mul_right s i.2
    have hj := j.2
    linarith⟩

theorem blockEmb_inj {m s n : ℕ} (hms : m * s ≤ n) {i₁ i₂ : Fin m} {j₁ j₂ : Fin s}
    (h : blockEmb hms i₁ j₁ = blockEmb hms i₂ j₂) : i₁ = i₂ ∧ j₁ = j₂ := by
  have hval : i₁.1 * s + j₁.1 = i₂.1 * s + j₂.1 := Fin.mk.inj h
  have hi : i₁.1 = i₂.1 := by
    rcases lt_trichotomy i₁.1 i₂.1 with hlt | heq | hgt
    · have hle : (i₁.1 + 1) * s ≤ i₂.1 * s := Nat.mul_le_mul_right s hlt
      have hj₁ := j₁.2
      linarith
    · exact heq
    · have hle : (i₂.1 + 1) * s ≤ i₁.1 * s := Nat.mul_le_mul_right s hgt
      have hj₂ := j₂.2
      linarith
  have hj : j₁.1 = j₂.1 := by
    rw [hi] at hval
    exact Nat.add_left_cancel hval
  exact ⟨Fin.ext hi, Fin.ext hj⟩

def transEmb {m s n : ℕ} (hms : m * s ≤ n) (α : Fin m → Fin s) : Fin m ↪ Fin n where
  toFun i := blockEmb hms i (α i)
  inj' _ _ h := (blockEmb_inj hms h).1

def blockRowEmb {m s n : ℕ} (hms : m * s ≤ n) (i₀ : Fin m) : Fin s ↪ Fin n where
  toFun j := blockEmb hms i₀ j
  inj' _ _ h := (blockEmb_inj hms h).2

theorem not_isInducedSubgraphFree_of_twin_pair {k m s n : ℕ} {H₀ : SimpleGraph (Fin k)}
    {H : SimpleGraph (Fin (k + 1))} {v₀ : Fin k} {u₂ : Fin (k + 1)} {ι : Fin k ↪ Fin (k + 1)}
    (h_ext : IsTwinExtension H₀ H v₀ u₂ ι) (hms : m * s ≤ n) (G : SimpleGraph (Fin n))
    (h : Fin k ↪ Fin m) (α : Fin m → Fin s) {j₁ j₂ : Fin s} (hj : j₁ ≠ j₂)
    (hα₁ : H₀ = (G.comap (transEmb hms (Function.update α (h v₀) j₁))).comap h)
    (hα₂ : H₀ = (G.comap (transEmb hms (Function.update α (h v₀) j₂))).comap h)
    (hadj : G.Adj (blockEmb hms (h v₀) j₁) (blockEmb hms (h v₀) j₂) ↔ H.Adj (ι v₀) u₂) :
    ¬IsInducedSubgraphFree G H := by
  classical
  let α₁ := Function.update α (h v₀) j₁
  let α₂ := Function.update α (h v₀) j₂
  let g_fun : Fin (k + 1) → Fin n := fun x =>
    if hx : ∃ w : Fin k, ι w = x then
      transEmb hms α₁ (h (Classical.choose hx))
    else
      transEmb hms α₂ (h v₀)
  have hg_iota : ∀ w : Fin k, g_fun (ι w) = transEmb hms α₁ (h w) := by
    intro w
    have hx : ∃ w' : Fin k, ι w' = ι w := ⟨w, rfl⟩
    have h_choose : Classical.choose hx = w := ι.injective (Classical.choose_spec hx)
    dsimp [g_fun]
    rw [dif_pos hx, h_choose]
  have hg_u2 : g_fun u₂ = transEmb hms α₂ (h v₀) := by
    have hx : ¬∃ w : Fin k, ι w = u₂ := by
      rintro ⟨w, hw⟩
      exact h_ext.h_miss w hw
    dsimp [g_fun]
    rw [dif_neg hx]
  have hg_ne_v0 : ∀ w : Fin k, w ≠ v₀ → transEmb hms α₁ (h w) = transEmb hms α₂ (h w) := by
    intro w hw
    have hne : h w ≠ h v₀ := h.injective.ne hw
    simp [transEmb, α₁, α₂, Function.update_of_ne hne]
  have hg_inj : Function.Injective g_fun := by
    intro x y hxy
    rcases h_ext.eq_or_exists x with rfl | ⟨w₁, rfl⟩ <;>
      rcases h_ext.eq_or_exists y with rfl | ⟨w₂, rfl⟩
    · rfl
    · rw [hg_u2, hg_iota] at hxy
      have h_eq := blockEmb_inj hms hxy
      have hw : w₂ = v₀ := h.injective h_eq.1.symm
      subst hw
      have hj_eq : j₂ = j₁ := by
        simpa [α₁, α₂] using h_eq.2
      exact (hj hj_eq.symm).elim
    · rw [hg_iota, hg_u2] at hxy
      have h_eq := blockEmb_inj hms hxy
      have hw : w₁ = v₀ := h.injective h_eq.1
      subst hw
      have hj_eq : j₁ = j₂ := by
        simpa [α₁, α₂] using h_eq.2
      exact (hj hj_eq).elim
    · rw [hg_iota, hg_iota] at hxy
      rw [h.injective ((transEmb hms α₁).injective hxy)]
  let g : Fin (k + 1) ↪ Fin n := ⟨g_fun, hg_inj⟩
  intro h_free
  apply h_free
  refine ⟨g, ?_⟩
  have h_pair : ∀ (w : Fin k), H.Adj (ι w) u₂ ↔ G.Adj (g (ι w)) (g u₂) := by
    intro w
    change H.Adj (ι w) u₂ ↔ G.Adj (g_fun (ι w)) (g_fun u₂)
    rw [hg_iota, hg_u2]
    by_cases hw : w = v₀
    · subst hw
      simpa [transEmb, α₁, α₂] using hadj.symm
    · rw [hg_ne_v0 w hw, h_ext.h_twin w hw]
      have h_adj₂ := congr_arg (fun (J : SimpleGraph (Fin k)) => J.Adj w v₀) hα₂
      simpa [comap_adj] using h_adj₂
  ext x y
  change H.Adj x y ↔ G.Adj (g x) (g y)
  rcases h_ext.eq_or_exists x with rfl | ⟨w₁, rfl⟩ <;>
    rcases h_ext.eq_or_exists y with rfl | ⟨w₂, rfl⟩
  · simp
  · rw [H.adj_comm, G.adj_comm]
    exact h_pair w₂
  · exact h_pair w₁
  · change H.Adj (ι w₁) (ι w₂) ↔ G.Adj (g_fun (ι w₁)) (g_fun (ι w₂))
    rw [hg_iota, hg_iota]
    have h_comap_adj : H.Adj (ι w₁) (ι w₂) ↔ H₀.Adj w₁ w₂ := by
      rw [← h_ext.h_comap]
      rfl
    rw [h_comap_adj]
    have h_adj₁ := congr_arg (fun (J : SimpleGraph (Fin k)) => J.Adj w₁ w₂) hα₁
    simpa [comap_adj] using h_adj₁

noncomputable def goodTransversals {k m s n : ℕ} (hms : m * s ≤ n) (G : SimpleGraph (Fin n))
    (H₀ : SimpleGraph (Fin k)) (h : Fin k ↪ Fin m) : Finset (Fin m → Fin s) :=
  by classical exact Finset.univ.filter (fun α => H₀ = (G.comap (transEmb hms α)).comap h)

noncomputable def goodFiber {k m s n : ℕ} (hms : m * s ≤ n) (G : SimpleGraph (Fin n))
    (H₀ : SimpleGraph (Fin k)) (v₀ : Fin k) (h : Fin k ↪ Fin m) (α : Fin m → Fin s) :
    Finset (Fin s) :=
  by classical exact Finset.univ.filter (fun j =>
    Function.update α (h v₀) j ∈ goodTransversals hms G H₀ h)

theorem card_goodFiber_le_kappa {k m s n : ℕ} {H₀ : SimpleGraph (Fin k)}
    {H : SimpleGraph (Fin (k + 1))} {v₀ : Fin k} {u₂ : Fin (k + 1)} {ι : Fin k ↪ Fin (k + 1)}
    (h_ext : IsTwinExtension H₀ H v₀ u₂ ι) (hms : m * s ≤ n) (G : SimpleGraph (Fin n))
    (hG : IsInducedSubgraphFree G H) (h : Fin k ↪ Fin m) (α : Fin m → Fin s) :
    (goodFiber hms G H₀ v₀ h α).card ≤ kappa G := by
  classical
  let F := goodFiber hms G H₀ v₀ h α
  let rowEmb := blockRowEmb hms (h v₀)
  let T : Finset (Fin n) := F.map rowEmb
  have hT_card : F.card = T.card := (Finset.card_map rowEmb).symm
  rw [hT_card]
  have h_no_match : ∀ j₁ ∈ F, ∀ j₂ ∈ F, j₁ ≠ j₂ →
      ¬(G.Adj (rowEmb j₁) (rowEmb j₂) ↔ H.Adj (ι v₀) u₂) := by
    intro j₁ hj₁ j₂ hj₂ hj hadj
    have hα₁ : H₀ = (G.comap (transEmb hms (Function.update α (h v₀) j₁))).comap h := by
      simpa [F, goodFiber, goodTransversals] using hj₁
    have hα₂ : H₀ = (G.comap (transEmb hms (Function.update α (h v₀) j₂))).comap h := by
      simpa [F, goodFiber, goodTransversals] using hj₂
    exact not_isInducedSubgraphFree_of_twin_pair h_ext hms G h α hj hα₁ hα₂ hadj hG
  by_cases h_twins : H.Adj (ι v₀) u₂
  · have h_indep : Gᶜ.IsClique (T : Set (Fin n)) := by
      intro x hx y hy hxy
      rcases Finset.mem_map.mp (Finset.mem_coe.mp hx) with ⟨j₁, hj₁, rfl⟩
      rcases Finset.mem_map.mp (Finset.mem_coe.mp hy) with ⟨j₂, hj₂, rfl⟩
      have hj : j₁ ≠ j₂ := ne_of_apply_ne rowEmb hxy
      have h_not_adj : ¬G.Adj (rowEmb j₁) (rowEmb j₂) := by
        intro hadj
        exact h_no_match j₁ hj₁ j₂ hj₂ hj (iff_of_true hadj h_twins)
      exact ⟨hxy, h_not_adj⟩
    have hle : T.card ≤ G.indepNum := by
      rw [← cliqueNum_compl]
      exact h_indep.card_le_cliqueNum
    exact hle.trans (indepNum_le_kappa G)
  · have h_clique : G.IsClique (T : Set (Fin n)) := by
      intro x hx y hy hxy
      rcases Finset.mem_map.mp (Finset.mem_coe.mp hx) with ⟨j₁, hj₁, rfl⟩
      rcases Finset.mem_map.mp (Finset.mem_coe.mp hy) with ⟨j₂, hj₂, rfl⟩
      have hj : j₁ ≠ j₂ := ne_of_apply_ne rowEmb hxy
      by_contra h_not_adj
      exact h_no_match j₁ hj₁ j₂ hj₂ hj (iff_of_false h_not_adj h_twins)
    exact h_clique.card_le_cliqueNum.trans (cliqueNum_le_kappa G)

def swapCoordEquiv {m s : ℕ} (i₀ : Fin m) :
    ((Fin m → Fin s) × Fin s) ≃ ((Fin m → Fin s) × Fin s) where
  toFun p := (Function.update p.1 i₀ p.2, p.1 i₀)
  invFun p := (Function.update p.1 i₀ p.2, p.1 i₀)
  left_inv p := by
    rcases p with ⟨α, j⟩
    ext x
    · by_cases hx : x = i₀
      · subst hx
        simp
      · simp [hx]
    · simp
  right_inv p := by
    rcases p with ⟨α, j⟩
    ext x
    · by_cases hx : x = i₀
      · subst hx
        simp
      · simp [hx]
    · simp

theorem card_mul_eq_sum_fiber {m s : ℕ} (S : Finset (Fin m → Fin s)) (i₀ : Fin m) :
    S.card * s =
      ∑ α : Fin m → Fin s,
        (Finset.univ.filter (fun j : Fin s => Function.update α i₀ j ∈ S)).card := by
  classical
  have h_equiv :
      (∑ p : (Fin m → Fin s) × Fin s, if p.1 ∈ S then (1 : ℕ) else 0) =
      (∑ p : (Fin m → Fin s) × Fin s, if (swapCoordEquiv i₀ p).1 ∈ S then (1 : ℕ) else 0) :=
    Fintype.sum_equiv (swapCoordEquiv i₀)
      (fun p => if p.1 ∈ S then (1 : ℕ) else 0)
      (fun p => if (swapCoordEquiv i₀ p).1 ∈ S then (1 : ℕ) else 0)
      (fun p => by simp [swapCoordEquiv])
  have h_lhs :
      (∑ p : (Fin m → Fin s) × Fin s, if p.1 ∈ S then (1 : ℕ) else 0) = S.card * s := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    have h_inner : (∑ α : Fin m → Fin s, if α ∈ S then (1 : ℕ) else 0) = S.card := by
      rw [← Finset.card_filter]
      congr 1
      ext α
      simp
    simp [h_inner, mul_comm]
  have h_rhs :
      (∑ p : (Fin m → Fin s) × Fin s, if (swapCoordEquiv i₀ p).1 ∈ S then (1 : ℕ) else 0) =
      ∑ α : Fin m → Fin s,
        (Finset.univ.filter (fun j : Fin s => Function.update α i₀ j ∈ S)).card := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [Finset.card_filter]
    rfl
  omega

theorem block_size_le_pow_mul_kappa {k m s n : ℕ} {H₀ : SimpleGraph (Fin k)}
    {H : SimpleGraph (Fin (k + 1))} {v₀ : Fin k} {u₂ : Fin (k + 1)} {ι : Fin k ↪ Fin (k + 1)}
    (h_ext : IsTwinExtension H₀ H v₀ u₂ ι) (hs : 1 ≤ s) (hms : m * s ≤ n)
    (G : SimpleGraph (Fin n)) (hG : IsInducedSubgraphFree G H)
    (h_all : ∀ α : Fin m → Fin s, ¬IsInducedSubgraphFree (G.comap (transEmb hms α)) H₀) :
    s ≤ m ^ k * kappa G := by
  classical
  have h_per_emb : ∀ h : Fin k ↪ Fin m,
      (goodTransversals hms G H₀ h).card * s ≤ Fintype.card (Fin m → Fin s) * kappa G := by
    intro h
    have h_eq := card_mul_eq_sum_fiber (goodTransversals hms G H₀ h) (h v₀)
    have h_sum_le :
        (∑ α : Fin m → Fin s, (goodFiber hms G H₀ v₀ h α).card) ≤
        ∑ _α : Fin m → Fin s, kappa G :=
      Finset.sum_le_sum (fun α _ => card_goodFiber_le_kappa h_ext hms G hG h α)
    simp only [goodFiber] at h_sum_le
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at h_sum_le
    omega
  have h_cover : (Finset.univ : Finset (Fin m → Fin s)) ⊆
      (Finset.univ : Finset (Fin k ↪ Fin m)).biUnion (goodTransversals hms G H₀) := by
    intro α _
    have hα := h_all α
    unfold IsInducedSubgraphFree at hα
    push_neg at hα
    obtain ⟨h, hh⟩ := hα
    exact Finset.mem_biUnion.mpr ⟨h, Finset.mem_univ h, by simpa [goodTransversals] using hh⟩
  have h_card_cover : Fintype.card (Fin m → Fin s) ≤
      ∑ h : Fin k ↪ Fin m, (goodTransversals hms G H₀ h).card := by
    calc Fintype.card (Fin m → Fin s)
      _ = (Finset.univ : Finset (Fin m → Fin s)).card := rfl
      _ ≤ ((Finset.univ : Finset (Fin k ↪ Fin m)).biUnion (goodTransversals hms G H₀)).card :=
        Finset.card_le_card h_cover
      _ ≤ ∑ h : Fin k ↪ Fin m, (goodTransversals hms G H₀ h).card := Finset.card_biUnion_le
  have h_mul_le :
      Fintype.card (Fin m → Fin s) * s ≤
        Fintype.card (Fin k ↪ Fin m) * (Fintype.card (Fin m → Fin s) * kappa G) := by
    calc Fintype.card (Fin m → Fin s) * s
      _ ≤ (∑ h : Fin k ↪ Fin m, (goodTransversals hms G H₀ h).card) * s :=
        Nat.mul_le_mul_right s h_card_cover
      _ = ∑ h : Fin k ↪ Fin m, (goodTransversals hms G H₀ h).card * s := Finset.sum_mul _ _ _
      _ ≤ ∑ _h : Fin k ↪ Fin m, Fintype.card (Fin m → Fin s) * kappa G :=
        Finset.sum_le_sum (fun h _ => h_per_emb h)
      _ = Fintype.card (Fin k ↪ Fin m) * (Fintype.card (Fin m → Fin s) * kappa G) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have h_rearrange :
      Fintype.card (Fin m → Fin s) * s ≤
        Fintype.card (Fin m → Fin s) * (Fintype.card (Fin k ↪ Fin m) * kappa G) := by
    linarith
  haveI : Nonempty (Fin s) := ⟨⟨0, by omega⟩⟩
  have h_pos : 0 < Fintype.card (Fin m → Fin s) := Fintype.card_pos
  have h_s_le : s ≤ Fintype.card (Fin k ↪ Fin m) * kappa G :=
    Nat.le_of_mul_le_mul_left h_rearrange h_pos
  have h_emb_le : Fintype.card (Fin k ↪ Fin m) ≤ m ^ k := by
    have h_inj : Function.Injective (fun (f : Fin k ↪ Fin m) => (f : Fin k → Fin m)) :=
      DFunLike.coe_injective
    calc Fintype.card (Fin k ↪ Fin m)
      _ ≤ Fintype.card (Fin k → Fin m) := Fintype.card_le_of_injective _ h_inj
      _ = m ^ k := by simp
  exact h_s_le.trans (Nat.mul_le_mul_right (kappa G) h_emb_le)

/--
**Lemma 2.3 (`erdos_hajnal_twin_substitution`, `lem:aps`)**:
If `H₀ : SimpleGraph (Fin k)` ($k \ge 1$) satisfies the Erdős–Hajnal property and
`H : SimpleGraph (Fin (k + 1))` is a twin extension of `H₀`, then `H` satisfies the
Erdős–Hajnal property.
-/
theorem erdos_hajnal_twin_substitution {k : ℕ} (hk : 1 ≤ k)
    {H₀ : SimpleGraph (Fin k)} {H : SimpleGraph (Fin (k + 1))}
    {v₀ : Fin k} {u₂ : Fin (k + 1)} {ι : Fin k ↪ Fin (k + 1)}
    (h_ext : IsTwinExtension H₀ H v₀ u₂ ι) (hH₀ : HasErdosHajnalProp H₀) :
    HasErdosHajnalProp H := by
  obtain ⟨c₀, hc₀, h_bound₀⟩ := hH₀
  let c₁ : ℝ := min c₀ 1
  have hc₁_pos : 0 < c₁ := lt_min hc₀ zero_lt_one
  have hc₁_le_c₀ : c₁ ≤ c₀ := min_le_left _ _
  have hc₁_le_one : c₁ ≤ 1 := min_le_right _ _
  let d : ℕ := k + 2
  have hd_ge_three : 3 ≤ d := by omega
  have hd_pos : 0 < (d : ℝ) := by positivity
  have hd_ne_zero : (d : ℝ) ≠ 0 := ne_of_gt hd_pos
  let N₀ : ℕ := d ^ d
  have hN₀_ge_two : 2 ≤ N₀ := by
    have : 2 ≤ 3 ^ 3 := by norm_num
    have hpow : 3 ^ 3 ≤ d ^ d := Nat.pow_le_pow_left hd_ge_three 3 |>.trans
      (Nat.pow_le_pow_right (by omega) hd_ge_three)
    omega
  let c : ℝ := c₁ / (2 * (d : ℝ))
  have hc_pos : 0 < c := div_pos hc₁_pos (by positivity)
  apply hasErdosHajnalProp_of_large_n H hN₀_ge_two hc_pos
  intro n hn G hG
  let r : ℝ := (n : ℝ) ^ (1 / (d : ℝ))
  let m : ℕ := ⌊r⌋₊
  let s : ℕ := n / m
  have hr_nonneg : 0 ≤ r := by positivity
  have hr_pow : r ^ d = (n : ℝ) := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n),
      one_div_mul_cancel hd_ne_zero, Real.rpow_one]
  have hd_le_r : (d : ℝ) ≤ r := by
    have hn_cast : ((d : ℝ) ^ d) ≤ (n : ℝ) := by exact_mod_cast hn
    have h1 : (((d : ℝ) ^ d) ^ (1 / (d : ℝ))) ≤ r :=
      Real.rpow_le_rpow (by positivity) hn_cast (by positivity)
    have h2 : ((d : ℝ) ^ d) ^ (1 / (d : ℝ)) = (d : ℝ) := by
      rw [← Real.rpow_natCast (d : ℝ) d, ← Real.rpow_mul (by positivity),
         mul_one_div_cancel hd_ne_zero, Real.rpow_one]
    linarith
  have hd_le_m : d ≤ m := Nat.le_floor hd_le_r
  have hm_ge_three : 3 ≤ m := le_trans hd_ge_three hd_le_m
  have hm_pos : 0 < m := by omega
  have hm_le_r : (m : ℝ) ≤ r := Nat.floor_le hr_nonneg
  have hm_pow_le_n : m ^ d ≤ n := by
    have h_real : ((m : ℝ) ^ d) ≤ (n : ℝ) := by
      rw [← hr_pow]
      exact pow_le_pow_left₀ (by positivity) hm_le_r d
    exact_mod_cast h_real
  have h_m_pow_le_s : m ^ (k + 1) ≤ s := by
    have h_mul : m ^ (k + 1) * m ≤ n := by
      have h_eq : m ^ (k + 1) * m = m ^ d := by
        dsimp [d]
        rw [← pow_succ]
      omega
    exact (Nat.le_div_iff_mul_le hm_pos).mpr h_mul
  have hs_ge_one : 1 ≤ s := by
    have : 1 ≤ m ^ (k + 1) := Nat.one_le_pow (k + 1) m hm_pos
    omega
  have hms : m * s ≤ n := Nat.mul_div_le n m
  have hm_ge_one_real : (1 : ℝ) ≤ (m : ℝ) := by
    have : 1 ≤ m := by omega
    exact_mod_cast this
  have hm_c1_le_kappa : (m : ℝ) ^ c₁ ≤ (kappa G : ℝ) := by
    by_cases h_case1 : ∃ α : Fin m → Fin s,
        IsInducedSubgraphFree (G.comap (transEmb hms α)) H₀
    · obtain ⟨α, hα⟩ := h_case1
      have h0 := h_bound₀ (Fin m) (G.comap (transEmb hms α)) hα
      rw [Fintype.card_fin] at h0
      have h_c1_c0 : (m : ℝ) ^ c₁ ≤ (m : ℝ) ^ c₀ :=
        Real.rpow_le_rpow_of_exponent_le hm_ge_one_real hc₁_le_c₀
      have h_k : (kappa (G.comap (transEmb hms α)) : ℝ) ≤ (kappa G : ℝ) := by
        exact_mod_cast kappa_comap_le G (transEmb hms α)
      linarith
    · push_neg at h_case1
      have h_s_le := block_size_le_pow_mul_kappa h_ext hs_ge_one hms G hG h_case1
      have h_m_mul : m ^ k * m ≤ m ^ k * kappa G := by
        have h_pow : m ^ k * m = m ^ (k + 1) := (pow_succ m k).symm
        omega
      have hm_pow_pos : 0 < m ^ k := by positivity
      have hm_le_kappa : m ≤ kappa G := Nat.le_of_mul_le_mul_left h_m_mul hm_pow_pos
      have h_c1_one : (m : ℝ) ^ c₁ ≤ (m : ℝ) := by
        calc (m : ℝ) ^ c₁
          _ ≤ (m : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hm_ge_one_real hc₁_le_one
          _ = (m : ℝ) := Real.rpow_one (m : ℝ)
      have hm_le_kappa_real : (m : ℝ) ≤ (kappa G : ℝ) := by exact_mod_cast hm_le_kappa
      linarith
  have hn_le_m_pow : (n : ℝ) ≤ (m : ℝ) ^ (2 * (d : ℝ)) := by
    have hr_lt : r < (m : ℝ) + 1 := Nat.lt_floor_add_one r
    have hm_sq : (m : ℝ) + 1 ≤ (m : ℝ) ^ 2 := by
      have hm3 : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_ge_three
      nlinarith
    have hr_le_sq : r ≤ (m : ℝ) ^ 2 := le_trans (le_of_lt hr_lt) hm_sq
    have h_pow : r ^ d ≤ ((m : ℝ) ^ 2) ^ d := pow_le_pow_left₀ hr_nonneg hr_le_sq d
    rw [hr_pow, ← pow_mul] at h_pow
    have h_rpow_eq : ((m : ℝ) ^ (2 * d : ℕ)) = (m : ℝ) ^ (2 * (d : ℝ)) := by
      rw [← Real.rpow_natCast]
      push_cast
      rfl
    linarith
  have hn_c_le_m_c1 : (n : ℝ) ^ c ≤ (m : ℝ) ^ c₁ := by
    have h1 : (n : ℝ) ^ c ≤ ((m : ℝ) ^ (2 * (d : ℝ))) ^ c :=
      Real.rpow_le_rpow (Nat.cast_nonneg n) hn_le_m_pow (le_of_lt hc_pos)
    have h2 : ((m : ℝ) ^ (2 * (d : ℝ))) ^ c = (m : ℝ) ^ c₁ := by
      dsimp [c]
      rw [← Real.rpow_mul (Nat.cast_nonneg m), mul_div_cancel₀ _ (by positivity)]
    linarith
  exact hn_c_le_m_c1.trans hm_c1_le_kappa

instance {α β : Type*} (G : SimpleGraph β) [DecidableRel G.Adj] (f : α → β) :
    DecidableRel (G.comap f).Adj := fun u v =>
  inferInstanceAs (Decidable (G.Adj (f u) (f v)))

def witnessNonEdge (u v : ℕ) : Bool :=
  (u == 0 && v == 3) || (u == 3 && v == 0) ||
  (u == 3 && v == 5) || (u == 5 && v == 3) ||
  (u == 5 && v == 1) || (u == 1 && v == 5) ||
  (u == 1 && v == 2) || (u == 2 && v == 1) ||
  (u == 1 && v == 4) || (u == 4 && v == 1) ||
  (u == 2 && v == 4) || (u == 4 && v == 2) ||
  (u == 5 && v == 6) || (u == 6 && v == 5) ||
  (u == 2 && v == 6) || (u == 6 && v == 2) ||
  (u == 4 && v == 6) || (u == 6 && v == 4)

def witnessGraphH1 : SimpleGraph (Fin 6) where
  Adj u v := u ≠ v ∧ witnessNonEdge u.1 v.1 = false
  symm u v := by
    revert u v
    decide
  loopless u := by
    revert u
    decide

instance : DecidableRel witnessGraphH1.Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ witnessNonEdge u.1 v.1 = false))

def witnessGraphH : SimpleGraph (Fin 7) where
  Adj u v := u ≠ v ∧ witnessNonEdge u.1 v.1 = false
  symm u v := by
    revert u v
    decide
  loopless u := by
    revert u
    decide

instance : DecidableRel witnessGraphH.Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ witnessNonEdge u.1 v.1 = false))

def witnessEmb1 : Fin 5 ↪ Fin 6 where
  toFun := ![0, 3, 5, 1, 2]
  inj' u v := by
    revert u v
    decide

theorem isTwinExtension_witnessGraphH1 :
    IsTwinExtension P5Compl witnessGraphH1 4 4 witnessEmb1 where
  h_miss w := by
    revert w
    decide
  h_comap := by
    ext u v
    revert u v
    decide
  h_twin w := by
    revert w
    decide

theorem isTwinExtension_witnessGraphH :
    IsTwinExtension witnessGraphH1 witnessGraphH 1 6 Fin.castSuccEmb where
  h_miss w := by
    revert w
    decide
  h_comap := by
    ext u v
    revert u v
    decide
  h_twin w := by
    revert w
    decide

/--
**Proposition 3.2(1) (`witnessGraphH_hasErdosHajnalProp`, `prop:wonderful`)**:
If $P_5$ satisfies the Erdős–Hajnal property, then the 7-vertex witness graph `witnessGraphH`
satisfies the Erdős–Hajnal property.
-/
theorem witnessGraphH_hasErdosHajnalProp (hP5 : HasErdosHajnalProp P5) :
    HasErdosHajnalProp witnessGraphH := by
  have hP5Compl : HasErdosHajnalProp P5Compl := hP5.compl
  have hH1 : HasErdosHajnalProp witnessGraphH1 :=
    erdos_hajnal_twin_substitution (by norm_num) isTwinExtension_witnessGraphH1 hP5Compl
  exact erdos_hajnal_twin_substitution (by norm_num) isTwinExtension_witnessGraphH hH1

def witnessPlusNonEdge (u v : ℕ) : Bool :=
  if (u == 1 && v == 2) || (u == 2 && v == 1) then false
  else if u == 7 then decide (v ∈ ({3, 4, 5, 6} : Finset ℕ))
  else if v == 7 then decide (u ∈ ({3, 4, 5, 6} : Finset ℕ))
  else witnessNonEdge u v

def witnessGraphHPlus : SimpleGraph (Fin 8) where
  Adj u v := u ≠ v ∧ witnessPlusNonEdge u.1 v.1 = false
  symm u v := by
    revert u v
    decide
  loopless u := by
    revert u
    decide

instance : DecidableRel witnessGraphHPlus.Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ witnessPlusNonEdge u.1 v.1 = false))

def witnessMinusNonEdge (u v : ℕ) : Bool :=
  if u == 7 then decide (v ∈ ({3, 4, 5, 6} : Finset ℕ))
  else if v == 7 then decide (u ∈ ({3, 4, 5, 6} : Finset ℕ))
  else witnessNonEdge u v

def witnessGraphHMinus : SimpleGraph (Fin 8) where
  Adj u v := u ≠ v ∧ witnessMinusNonEdge u.1 v.1 = false
  symm u v := by
    revert u v
    decide
  loopless u := by
    revert u
    decide

instance : DecidableRel witnessGraphHMinus.Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ witnessMinusNonEdge u.1 v.1 = false))

def witnessPlusEmb : Fin 6 ↪ Fin 8 where
  toFun := ![0, 3, 5, 1, 4, 2]
  inj' u v := by
    revert u v
    decide

/--
**Proposition 3.2(2) (`prop:wonderful`)**: The induced subgraph of $H^+$ on `![0, 3, 5, 1, 4, 2]` is $\overline{P_6}$.
-/
theorem witnessGraphHPlus_comap_eq_P6Compl :
    witnessGraphHPlus.comap witnessPlusEmb = P6Compl := by
  ext u v
  revert u v
  decide

theorem not_isInducedSubgraphFree_witnessGraphHPlus :
    ¬IsInducedSubgraphFree witnessGraphHPlus P6Compl :=
  fun h => h ⟨witnessPlusEmb, witnessGraphHPlus_comap_eq_P6Compl.symm⟩

def witnessMinusEmb : Fin 6 ↪ Fin 8 where
  toFun := ![0, 3, 7, 6, 2, 1]
  inj' u v := by
    revert u v
    decide

/--
**Proposition 3.2(3) (`prop:wonderful`)**: The induced subgraph of $H^-$ on `![0, 3, 7, 6, 2, 1]` is $\overline{P_6}$.
-/
theorem witnessGraphHMinus_comap_eq_P6Compl :
    witnessGraphHMinus.comap witnessMinusEmb = P6Compl := by
  ext u v
  revert u v
  decide

theorem not_isInducedSubgraphFree_witnessGraphHMinus :
    ¬IsInducedSubgraphFree witnessGraphHMinus P6Compl :=
  fun h => h ⟨witnessMinusEmb, witnessGraphHMinus_comap_eq_P6Compl.symm⟩

/-! ### Part 1 Synthesis: Bridging `witnessH` (`WitnessGraph.lean`) and `witnessGraphH` (`Proof.lean`) -/

/--
The 7-vertex witness graph `witnessH` in `WitnessGraph.lean` is definitionally equal on all
vertex pairs to `witnessGraphH` in `Proof.lean`.
-/
theorem witnessH_eq_witnessGraphH : witnessH = witnessGraphH := by
  ext u v
  revert u v
  decide

/--
**Proposition 3.2(1) (`witnessH_hasErdosHajnalProp`, `prop:wonderful`)**:
If $P_5$ satisfies the Erdős–Hajnal property, then `witnessH` satisfies the Erdős–Hajnal property.
-/
theorem witnessH_hasErdosHajnalProp (hP5 : HasErdosHajnalProp P5) :
    HasErdosHajnalProp witnessH := by
  rw [witnessH_eq_witnessGraphH]
  exact witnessGraphH_hasErdosHajnalProp hP5

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
Bridging `HasErdosHajnalProp witnessH` (with exponent $c_H > 0$) to the induced-subgraph clique or
independent set hypothesis `hEH` of `p6_is_wonderful_of_witnessH_eh`.
-/
theorem exists_pattern_clique_or_indep_of_witnessH_eh
    {G : SimpleGraph V} {ℓ : ℕ} {B : Fin ℓ → Finset V} {c_H : ℝ}
    (h_eh : ∀ (W : Type) [Fintype W] [DecidableEq W] (J : SimpleGraph W),
      IsInducedSubgraphFree J witnessH → (Fintype.card W : ℝ) ^ c_H ≤ (kappa J : ℝ))
    (I : Finset (Fin ℓ)) (_hI : I.Nonempty)
    (hFree : IsInducedSubgraphFree ((blockadePatternGraph G B).induce (I : Set (Fin ℓ))) witnessH) :
    ∃ R ⊆ I, (I.card : ℝ) ^ c_H ≤ (R.card : ℝ) ∧
      ((∀ i ∈ R, ∀ j ∈ R, i ≠ j → (blockadePatternGraph G B).Adj i j) ∨
       (∀ i ∈ R, ∀ j ∈ R, i ≠ j → ¬(blockadePatternGraph G B).Adj i j)) := by
  classical
  let P := blockadePatternGraph G B
  let J : SimpleGraph ↥(I : Set (Fin ℓ)) := P.induce (I : Set (Fin ℓ))
  have hcard_J : Fintype.card ↥(I : Set (Fin ℓ)) = I.card := Fintype.card_coe I
  have hkappa : (I.card : ℝ) ^ c_H ≤ (kappa J : ℝ) := by
    rw [← hcard_J]
    exact h_eh ↥(I : Set (Fin ℓ)) J hFree
  rcases (kappa_cast_ge_iff J ((I.card : ℝ) ^ c_H)).mp hkappa with hclique | hindep
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
**Proposition 3.2 (`p6_is_wonderful_of_hasErdosHajnalProp_witnessH`, `prop:wonderful`)**:
Direct specialization of `p6_is_wonderful_of_witnessH_eh` using `exists_pattern_clique_or_indep_of_witnessH_eh`.
-/
theorem p6_is_wonderful_of_hasErdosHajnalProp_witnessH
    {G : SimpleGraph V} {S : Finset V} {ℓ w_nat : ℕ} {y a c_H : ℝ} {B : Fin ℓ → Finset V}
    (hG : IsInducedSubgraphFree G P6Compl)
    (hB : IsCompleteOrXSparseBlockadeIn G S ℓ (w_nat : ℝ) (y ^ a) B)
    (hw_pos : 0 < w_nat) (hw_eq : ∀ i : Fin ℓ, (B i).card = w_nat)
    (hcH_pos : 0 < c_H)
    (h_eh : ∀ (W : Type) [Fintype W] [DecidableEq W] (J : SimpleGraph W),
      IsInducedSubgraphFree J witnessH → (Fintype.card W : ℝ) ^ c_H ≤ (kappa J : ℝ))
    (ha7 : 7 ≤ a) (ha_cH : 5 / c_H + 1 ≤ a)
    (hy_pos : 0 < y) (hy_le : y ≤ 1 / 2)
    (hℓ_ge : y ^ (-a) ≤ (ℓ : ℝ)) :
    (∃ U ⊆ S, w_nat ≤ U.card ∧ IsEpsRestrictedOn G U (y ^ 4)) ∨
    (∃ i : Fin ℓ, ((openAttachmentExternalVerts G S B i).card : ℝ) < y * (S.card : ℝ)) :=
  p6_is_wonderful_of_witnessH_eh hG hB hw_pos hw_eq hcH_pos ha7 ha_cH hy_pos hy_le hℓ_ge
    (exists_pattern_clique_or_indep_of_witnessH_eh h_eh)

/-!
### Part 2 Synthesis: Single-Scale Sparsification Step & Generalized Niceness of $\{P_6\}$
(Combining `upside_down_comb_extraction`, `comb_dichotomy`, `blockade_iteration_xSparse_four`,
`p6Compl_free_sparse_compl_complete_blockade_cube`, `rodl_theorem_P6Compl`, and `lem_gen_nice_P6`)
-/

/--
Initial post-Rödl scale calibration (Proposition 5.3 of `FMBV4-016_readable.tex`):
Applying `rodl_theorem_P6Compl` at scale $\lambda_0 = c^{10}$ produces a $\lambda_0$-restricted
subset $F_0 \subseteq F$ with $|F_0| \ge \delta |F| \ge \lambda_0^{b_2} |F|$.
-/
theorem rodl_initial_step_for_gen_nice (G : SimpleGraph V) (F : Finset V)
    (d_leaf h_leaf : ℝ) (hG : IsInducedSubgraphFree G P6Compl) :
    let lam0 := lambda0Param h_leaf
    let δ := rodlDelta lam0
    let b₂ := b2Param d_leaf h_leaf δ
    ∃ F₀ ⊆ F, IsEpsRestrictedOn G F₀ lam0 ∧
      lam0 ^ b₂ * (F.card : ℝ) ≤ (F₀.card : ℝ) := by
  intro lam0 δ b₂
  have hlam0_pos : 0 < lam0 := lambda0Param_pos h_leaf
  have hlam0_half : lam0 < 1 / 2 := lambda0Param_lt_half h_leaf
  have hδ_pos : 0 < δ := rodlDelta_pos hlam0_pos hlam0_half
  obtain ⟨F₀, hF₀_sub, hF₀_rest, hF₀_card⟩ :=
    rodl_theorem_P6Compl G hG lam0 hlam0_pos hlam0_half F
  refine ⟨F₀, hF₀_sub, hF₀_rest, ?_⟩
  have hb₂_ceil : (⌈Real.log (1 / δ) / Real.log (1 / lam0)⌉₊ : ℝ) ≤ b₂ := le_max_right _ _
  have hdiv_le : Real.log (1 / δ) / Real.log (1 / lam0) ≤ b₂ :=
    (Nat.le_ceil _).trans hb₂_ceil
  have h1_lt_inv : 1 < 1 / lam0 := one_lt_one_div hlam0_pos (by linarith)
  have hlog_inv_pos : 0 < Real.log (1 / lam0) := Real.log_pos h1_lt_inv
  have hmul : Real.log (1 / δ) ≤ b₂ * Real.log (1 / lam0) :=
    (div_le_iff₀ hlog_inv_pos).mp hdiv_le
  rw [one_div, one_div, Real.log_inv, Real.log_inv] at hmul
  have hlog_le : Real.log (lam0 ^ b₂) ≤ Real.log δ := by
    rw [Real.log_rpow hlam0_pos]
    linarith
  have hpow_le : lam0 ^ b₂ ≤ δ :=
    (Real.log_le_log_iff (Real.rpow_pos_of_pos hlam0_pos b₂) hδ_pos).mp hlog_le
  exact (mul_le_mul_of_nonneg_right hpow_le (Nat.cast_nonneg _)).trans hF₀_card

theorem cParam_le_two_rpow_neg_sixteen (h_leaf : ℝ) :
    cParam h_leaf ≤ (2 : ℝ) ^ (-16 : ℝ) := by
  unfold cParam
  have hb : 4 ≤ bLeaf h_leaf := four_le_bLeaf h_leaf
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

theorem localSparsityY_le_two_rpow_neg_48 (h_leaf : ℝ) {lam : ℝ}
    (hlam : 0 ≤ lam) (hlam_le : lam ≤ lambda0Param h_leaf) :
    localSparsityY h_leaf lam ≤ (2 : ℝ) ^ (-48 : ℝ) := by
  have hy_c3 : localSparsityY h_leaf lam ≤ (cParam h_leaf) ^ (3 : ℝ) :=
    localSparsityY_le_cParam_cube h_leaf hlam hlam_le
  have hc_pos : 0 < cParam h_leaf := cParam_pos h_leaf
  have hc_16 : cParam h_leaf ≤ (2 : ℝ) ^ (-16 : ℝ) := cParam_le_two_rpow_neg_sixteen h_leaf
  calc localSparsityY h_leaf lam
      ≤ (cParam h_leaf) ^ (3 : ℝ) := hy_c3
    _ ≤ ((2 : ℝ) ^ (-16 : ℝ)) ^ (3 : ℝ) := Real.rpow_le_rpow hc_pos.le hc_16 (by norm_num)
    _ = (2 : ℝ) ^ (-48 : ℝ) := by rw [← Real.rpow_mul (by norm_num)]; norm_num

theorem lam_le_localSparsityY (h_leaf : ℝ) {lam : ℝ}
    (hlam : 0 ≤ lam) (hlam_le : lam ≤ lambda0Param h_leaf) :
    lam ≤ localSparsityY h_leaf lam := by
  set y := localSparsityY h_leaf lam
  have hc_pos : 0 < cParam h_leaf := cParam_pos h_leaf
  have hy_nonneg : 0 ≤ y := by unfold y localSparsityY; positivity
  have hy_le_one : y ≤ 1 := by
    have := localSparsityY_lt_half h_leaf hlam hlam_le
    linarith
  have hc_le_one : cParam h_leaf ≤ 1 := by
    have := cParam_lt_half h_leaf
    linarith
  have hy3_le_y : y ^ (3 : ℝ) ≤ y := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    nlinarith [sq_nonneg y]
  calc lam
      = cParam h_leaf * y ^ (3 : ℝ) := (cParam_mul_localSparsityY_cube h_leaf hlam).symm
    _ ≤ 1 * y := mul_le_mul hc_le_one hy3_le_y (Real.rpow_nonneg hy_nonneg 3) zero_le_one
    _ = y := one_mul y

theorem lam_b3Param_le_cParam (d_leaf h_leaf : ℝ) {lam : ℝ}
    (hlam : 0 ≤ lam) (hlam_le : lam ≤ lambda0Param h_leaf) :
    lam ^ (b3Param d_leaf) ≤ cParam h_leaf := by
  have hc_pos : 0 < cParam h_leaf := cParam_pos h_leaf
  have hc_le_one : cParam h_leaf ≤ 1 := (cParam_lt_half h_leaf).le.trans (by norm_num)
  have hb3_pos : 0 < b3Param d_leaf := b3Param_pos d_leaf
  have h1 : lam ^ (b3Param d_leaf) ≤ (lambda0Param h_leaf) ^ (b3Param d_leaf) :=
    Real.rpow_le_rpow hlam hlam_le hb3_pos.le
  have h2 : (lambda0Param h_leaf) ^ (b3Param d_leaf) =
      (cParam h_leaf) ^ (3 * (cLeaf d_leaf + 2)) := by
    unfold lambda0Param b3Param
    rw [← Real.rpow_mul hc_pos.le]
    congr 1
    ring
  have h3 : 1 ≤ 3 * (cLeaf d_leaf + 2) := by
    have := four_le_cLeaf d_leaf
    linarith
  have h4 : (cParam h_leaf) ^ (3 * (cLeaf d_leaf + 2)) ≤ (cParam h_leaf) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hc_pos hc_le_one h3
  rw [Real.rpow_one] at h4
  exact h1.trans (h2.le.trans h4)

/--
If $F_t$ is $\lambda$-restricted and $F' \subseteq F_t$ satisfies $|F'| \ge c |F_t|$, then $F'$ is
$y^3$-restricted for $y = (\lambda / c)^{1/3}$.
-/
theorem isEpsRestrictedOn_localSparsityY_cube_of_subset
    (G : SimpleGraph V) (F_t F' : Finset V) (h_leaf : ℝ) {lam : ℝ}
    (hlam : 0 ≤ lam) (hF'_sub : F' ⊆ F_t)
    (hF'_card : cParam h_leaf * (F_t.card : ℝ) ≤ (F'.card : ℝ))
    (hFt_rest : IsEpsRestrictedOn G F_t lam) :
    IsEpsRestrictedOn G F' ((localSparsityY h_leaf lam) ^ 3) := by
  have hc_pos : 0 < cParam h_leaf := cParam_pos h_leaf
  have h1 := stage2_step2_restricted_sub_of_subset G F_t F' lam (cParam h_leaf)
    hlam hc_pos hF'_sub hF'_card hFt_rest
  have h2 : lam / cParam h_leaf = (localSparsityY h_leaf lam) ^ 3 := by
    have hmul := cParam_mul_localSparsityY_cube h_leaf hlam
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hmul
    exact (div_eq_iff hc_pos.ne').mpr (hmul.symm.trans (mul_comm _ _))
  rwa [h2] at h1

/--
When $|S| \ge \varepsilon^{-200 d^2}$, $|F| \ge \varepsilon^d |S|$, $|F_0| \ge \lambda_0^{b_2} |F|$,
$|F_t| \ge \lambda^{b_2} |F_0|$, and $|F'| \ge c |F_t|$ at scale $\lambda \ge x = \varepsilon^{10 d}$,
specializing `pure_blockade_width_ge_for_gn3` to $k_0 = \lceil x^{-10} \rceil$ yields
$|F'| \ge x^{-1200}$.
-/
theorem sub_card_ge_x_rpow_neg_1200 (d_leaf h_leaf δ : ℝ) {ε lam : ℝ}
    {S F F₀ F_t F' : Finset V}
    (hε : 0 < ε) (hε_half : ε < 1 / 2)
    (hS : ε ^ (-200 * (dParam d_leaf h_leaf δ) ^ 2) ≤ (S.card : ℝ))
    (hlam : ε ^ (10 * dParam d_leaf h_leaf δ) ≤ lam)
    (hF : ε ^ (dParam d_leaf h_leaf δ) * (S.card : ℝ) ≤ (F.card : ℝ))
    (hF₀ : (lambda0Param h_leaf) ^ (b2Param d_leaf h_leaf δ) * (F.card : ℝ) ≤ (F₀.card : ℝ))
    (hFt : lam ^ (b2Param d_leaf h_leaf δ) * (F₀.card : ℝ) ≤ (F_t.card : ℝ))
    (hF' : cParam h_leaf * (F_t.card : ℝ) ≤ (F'.card : ℝ)) :
    (ε ^ (10 * dParam d_leaf h_leaf δ)) ^ (-1200 : ℝ) ≤ (F'.card : ℝ) := by
  set d := dParam d_leaf h_leaf δ
  set x := ε ^ (10 * d)
  have hd600 : 600 ≤ d := six_hundred_le_dParam d_leaf h_leaf δ
  have hε1 : ε ≤ 1 := by linarith
  have hx_pos : 0 < x := Real.rpow_pos_of_pos hε (10 * d)
  have hx_lt_half : x < 1 / 2 := by
    have := eps_pow_ten_dParam_lt_lambda0Param d_leaf h_leaf δ hε hε_half
    have := lambda0Param_lt_half h_leaf
    linarith
  have hx_le_one : x ≤ 1 := by linarith
  have hx_inv_ge2 : (2 : ℝ) ≤ x ^ (-1 : ℝ) := by
    rw [Real.rpow_neg_one, ← inv_inv (2 : ℝ)]
    exact inv_anti₀ hx_pos (by linarith)
  have hx_neg10_ge1 : (1 : ℝ) ≤ x ^ (-10 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx_pos hx_le_one (by norm_num)
  let k₀ : ℕ := ⌈x ^ (-10 : ℝ)⌉₊
  have hk₀_ge10 : x ^ (-10 : ℝ) ≤ (k₀ : ℝ) := Nat.le_ceil _
  have hk₀_ge : x ^ (-2 : ℝ) ≤ (k₀ : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_ge hx_pos hx_le_one (by norm_num)).trans hk₀_ge10
  have hk₀_pos : 0 < (k₀ : ℝ) := lt_of_lt_of_le zero_lt_one (hx_neg10_ge1.trans hk₀_ge10)
  have hk₀_lt : (k₀ : ℝ) < x ^ (-10 : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hk₀_le_x11 : (k₀ : ℝ) ≤ x ^ (-11 : ℝ) := by
    calc (k₀ : ℝ)
        ≤ 2 * x ^ (-10 : ℝ) := by linarith
      _ ≤ x ^ (-1 : ℝ) * x ^ (-10 : ℝ) := mul_le_mul_of_nonneg_right hx_inv_ge2 (by positivity)
      _ = x ^ (-11 : ℝ) := by rw [← Real.rpow_add hx_pos]; norm_num
  have hk₀_d1 : (k₀ : ℝ) ^ (d + 1) ≤ (S.card : ℝ) := by
    calc (k₀ : ℝ) ^ (d + 1)
        ≤ (x ^ (-11 : ℝ)) ^ (d + 1) := Real.rpow_le_rpow hk₀_pos.le hk₀_le_x11 (by linarith)
      _ = ε ^ (-110 * d * (d + 1)) := by
          unfold x
          rw [← Real.rpow_mul hε.le, ← Real.rpow_mul hε.le]
          congr 1
          ring
      _ ≤ ε ^ (-200 * d ^ 2) :=
          Real.rpow_le_rpow_of_exponent_ge hε hε1 (by nlinarith)
      _ ≤ (S.card : ℝ) := hS
  have h1_le_div : 1 ≤ (S.card : ℝ) / (k₀ : ℝ) ^ (d + 1) :=
    (one_le_div (by positivity)).mpr hk₀_d1
  have hgn3 := (pure_blockade_width_ge_for_gn3 d_leaf h_leaf δ hε hε_half hlam hF hF₀ hFt hF' hk₀_ge).2
  have h1_le_F' : 1 ≤ (F'.card : ℝ) / (k₀ : ℝ) ^ (120 : ℝ) := h1_le_div.trans hgn3
  have hk₀_120 : (k₀ : ℝ) ^ (120 : ℝ) ≤ (F'.card : ℝ) :=
    (one_le_div (by positivity)).mp h1_le_F'
  calc x ^ (-1200 : ℝ)
      = (x ^ (-10 : ℝ)) ^ (120 : ℝ) := by rw [← Real.rpow_mul hx_pos.le]; norm_num
    _ ≤ (k₀ : ℝ) ^ (120 : ℝ) := Real.rpow_le_rpow (by positivity) hk₀_ge10 (by norm_num)
    _ ≤ (F'.card : ℝ) := hk₀_120

/--
**Sparse Subcase of Single-Scale Step (`single_scale_sparse_comb_dichotomy`,
Proposition 5.3 of `FMBV4-016_readable.tex`)**:
If $F' \subseteq F_t$ has $|F'| \ge c |F_t|$ and is $y^3$-sparse in $G$, then combining
`upside_down_comb_extraction` (at parameter $x_0 = x^2$) and `comb_dichotomy` yields either:
1. Outcome (GN3), a moderate complete-or-$x$-sparse $(k, |F| / k^d)$-blockade in $F$, or a
   $\lambda^{b_1}$-restricted subset $F'' \subseteq F_t$ of size $\ge \lambda^{b_3} |F_t|$; or
2. Disjoint subsets $X, Y \subseteq F'$ with $|X| \ge y^4 |F'|$, $|Y| \ge (1 - 4y)|F'|$, and
   `IsXSparseTo G Y X (x ^ 2)`.
-/
theorem single_scale_sparse_comb_dichotomy
    (G : SimpleGraph V) (S F F₀ F_t F' : Finset V)
    (d_leaf h_leaf δ ε lam : ℝ)
    (hG : IsInducedSubgraphFree G P6Compl)
    (hε : 0 < ε) (hε_half : ε < 1 / 2)
    (hS : ε ^ (-200 * (dParam d_leaf h_leaf δ) ^ 2) ≤ (S.card : ℝ))
    (hF_sub : F ⊆ S) (hF₀_sub : F₀ ⊆ F) (hFt_sub : F_t ⊆ F₀) (hF'_sub : F' ⊆ F_t)
    (hlam_mem : lam ∈ Set.Icc (ε ^ (10 * dParam d_leaf h_leaf δ)) (lambda0Param h_leaf))
    (hF : ε ^ (dParam d_leaf h_leaf δ) * (S.card : ℝ) ≤ (F.card : ℝ))
    (hF₀ : (lambda0Param h_leaf) ^ (b2Param d_leaf h_leaf δ) * (F.card : ℝ) ≤ (F₀.card : ℝ))
    (hFt : lam ^ (b2Param d_leaf h_leaf δ) * (F₀.card : ℝ) ≤ (F_t.card : ℝ))
    (hF' : cParam h_leaf * (F_t.card : ℝ) ≤ (F'.card : ℝ))
    (h_sparse : IsEpsSparseOn G F' ((localSparsityY h_leaf lam) ^ 3)) :
    let d := dParam d_leaf h_leaf δ
    let x := ε ^ (10 * d)
    let b₁ := b1Param
    let b₃ := b3Param d_leaf
    let y := localSparsityY h_leaf lam
    ((GenNiceOutcome3 G S ε (d + 1) (20 * d) ∨
      ∃ (k : ℕ) (B : Fin k → Finset V),
        2 ≤ k ∧ (k : ℝ) ≤ x ^ (-10 : ℝ) ∧
        IsCompleteOrXSparseBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ d) x B) ∨
     ∃ F'' ⊆ F_t, IsEpsRestrictedOn G F'' (lam ^ b₁) ∧
       lam ^ b₃ * (F_t.card : ℝ) ≤ (F''.card : ℝ)) ∨
    (∃ X ⊆ F', ∃ Y ⊆ F', Disjoint X Y ∧
      y ^ (4 : ℝ) * (F'.card : ℝ) ≤ (X.card : ℝ) ∧
      (1 - 4 * y) * (F'.card : ℝ) ≤ (Y.card : ℝ) ∧
      IsXSparseTo G Y X (x ^ 2)) := by
  intro d x b₁ b₃ y
  have hx_pos : 0 < x := Real.rpow_pos_of_pos hε (10 * d)
  have hlam_pos : 0 < lam := hx_pos.trans_le hlam_mem.1
  have hlam_le : lam ≤ lambda0Param h_leaf := hlam_mem.2
  have hy_pos : 0 < y := localSparsityY_pos h_leaf hlam_pos
  have hy_48 : y ≤ (2 : ℝ) ^ (-48 : ℝ) := localSparsityY_le_two_rpow_neg_48 h_leaf hlam_pos.le hlam_le
  have hy_8 : y ≤ (2 : ℝ) ^ (-8 : ℝ) :=
    hy_48.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num))
  have hy_inv8 : y ≤ (2 : ℝ)⁻¹ ^ 8 := hy_8.trans_eq (by norm_num)
  have hx_le_y : x ≤ y := hlam_mem.1.trans (lam_le_localSparsityY h_leaf hlam_pos.le hlam_le)
  have hy_le_one : y ≤ 1 := by linarith [localSparsityY_lt_half h_leaf hlam_pos.le hlam_le]
  have hx2_pos : 0 < x ^ 2 := sq_pos_of_pos hx_pos
  have hx2_le_x : x ^ 2 ≤ x := by nlinarith [hx_le_y.trans hy_le_one]
  have hx2_le_y : x ^ 2 ≤ y := hx2_le_x.trans hx_le_y
  have hF'_1200 : x ^ (-1200 : ℝ) ≤ (F'.card : ℝ) :=
    sub_card_ge_x_rpow_neg_1200 d_leaf h_leaf δ hε hε_half hS hlam_mem.1 hF hF₀ hFt hF'
  have hF'_y4 : y⁻¹ ^ 4 ≤ (F'.card : ℝ) := by
    have h1 : y⁻¹ ^ 4 ≤ x⁻¹ ^ 4 :=
      pow_le_pow_left₀ (by positivity) (inv_anti₀ hx_pos hx_le_y) 4
    have h2 : x⁻¹ ^ 4 = x ^ (-4 : ℝ) := by
      rw [inv_pow, ← Real.rpow_natCast x 4, ← Real.rpow_neg hx_pos.le]
      norm_num
    have h3 : x ^ (-4 : ℝ) ≤ x ^ (-1200 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hx_pos (hx_le_y.trans hy_le_one) (by norm_num)
    exact (h1.trans_eq h2).trans (h3.trans hF'_1200)
  rcases upside_down_comb_extraction G F' (x ^ 2) y hx2_pos hx2_le_y hy_inv8 h_sparse hF'_y4 with
    h_2y4 | ⟨X, Y, hXF', hYF', hdisj, hX_card, hY_card, hXY_sparse⟩ |
    ⟨ℓ, a, B, v, hℓ_low, hℓ_high, hcomb, hapex⟩
  · refine Or.inl (Or.inr ⟨F', hF'_sub, ?_, ?_⟩)
    · exact Or.inl (h_2y4.mono (two_mul_localSparsityY_pow_four_nat_le h_leaf hlam_pos.le hlam_le))
    · exact (mul_le_mul_of_nonneg_right
        (lam_b3Param_le_cParam d_leaf h_leaf hlam_pos.le hlam_le) (Nat.cast_nonneg _)).trans hF'
  · refine Or.inr ⟨X, hXF', Y, hYF', hdisj, ?_, hY_card, hXY_sparse⟩
    rwa [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  · left
    have hℓ_low' : y ^ (-1 / 4 : ℝ) ≤ (ℓ : ℝ) := by
      convert hℓ_low using 2
      norm_num
    have hℓ_high' : (ℓ : ℝ) ≤ x ^ (-2 : ℝ) := by
      refine hℓ_high.trans_eq ?_
      rw [← Real.rpow_natCast x 2, ← Real.rpow_neg hx_pos.le]
      norm_num
    have hw_ge : (F'.card : ℝ) / (ℓ : ℝ) ^ 18 ≤ y ^ 4 * (F'.card : ℝ) / (ℓ : ℝ) ^ 2 := by
      have hℓ_pos : 0 < (ℓ : ℝ) := lt_of_lt_of_le (by positivity) hℓ_low'
      have hy_inv_le_ℓ4 : y⁻¹ ≤ (ℓ : ℝ) ^ 4 := by
        have hp := pow_le_pow_left₀ (by positivity) hℓ_low' 4
        have h_eq : (y ^ (-1 / 4 : ℝ)) ^ 4 = y⁻¹ := by
          rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul hy_pos.le]
          norm_num
          exact Real.rpow_neg_one y
        rwa [h_eq] at hp
      have hy4_inv_le_ℓ16 : (y ^ 4)⁻¹ ≤ (ℓ : ℝ) ^ 16 := by
        have hp := pow_le_pow_left₀ (by positivity) hy_inv_le_ℓ4 4
        rw [inv_pow, ← pow_mul] at hp
        exact hp
      have hℓ16_inv_le_y4 : ((ℓ : ℝ) ^ 16)⁻¹ ≤ y ^ 4 := by
        rw [← inv_inv (y ^ 4)]
        exact inv_anti₀ (by positivity) hy4_inv_le_ℓ16
      have hℓ_ne : (ℓ : ℝ) ≠ 0 := hℓ_pos.ne'
      calc (F'.card : ℝ) / (ℓ : ℝ) ^ 18
          = ((ℓ : ℝ) ^ 16)⁻¹ * ((F'.card : ℝ) / (ℓ : ℝ) ^ 2) := by
            field_simp
        _ ≤ y ^ 4 * ((F'.card : ℝ) / (ℓ : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_right hℓ16_inv_le_y4 (by positivity)
        _ = y ^ 4 * (F'.card : ℝ) / (ℓ : ℝ) ^ 2 := (mul_div_assoc _ _ _).symm
    rcases comb_dichotomy hG hcomb hapex hx_pos hx_le_y hy_8 hℓ_low' hℓ_high' hw_ge with
      ⟨k, D, hk_gt, hD⟩ | ⟨k, D, hk2, hk_le, hk_sqrt, hD⟩
    · refine Or.inl (Or.inl ?_)
      obtain ⟨hk_eps, hw_gn3⟩ :=
        pure_blockade_width_ge_for_gn3 d_leaf h_leaf δ hε hε_half hlam_mem.1 hF hF₀ hFt hF' hk_gt.le
      rw [show (120 : ℝ) = ((120 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hw_gn3
      exact genNiceOutcome3_of_pure_blockade_in_sub
        (hF'_sub.trans (hFt_sub.trans (hF₀_sub.trans hF_sub))) hk_eps hw_gn3 (Or.inl hD)
    · refine Or.inl (Or.inr ⟨k, D, hk2, hk_le, ?_⟩)
      have hy_ge : (2 * (k : ℝ)) ^ (-8 : ℝ) ≤ y := by
        have h1 : (y ^ (-1 / 4 : ℝ)) ^ (1 / 2 : ℝ) ≤ (ℓ : ℝ) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hℓ_low' (by norm_num)
        have h2 : (y ^ (-1 / 4 : ℝ)) ^ (1 / 2 : ℝ) ≤ 2 * (k : ℝ) := by linarith
        have h3 : ((y ^ (-1 / 4 : ℝ)) ^ (1 / 2 : ℝ)) ^ (8 : ℝ) ≤ (2 * (k : ℝ)) ^ (8 : ℝ) :=
          Real.rpow_le_rpow (by positivity) h2 (by norm_num)
        have h4 : ((y ^ (-1 / 4 : ℝ)) ^ (1 / 2 : ℝ)) ^ (8 : ℝ) = y⁻¹ := by
          rw [← Real.rpow_mul hy_pos.le, ← Real.rpow_mul hy_pos.le]
          norm_num
          exact Real.rpow_neg_one y
        rw [h4] at h3
        rw [Real.rpow_neg (by positivity), ← inv_inv y]
        exact inv_anti₀ (by positivity) h3
      have hw_mod := moderate_blockade_width_ge_for_layout d_leaf h_leaf δ hlam_pos hk2 hy_ge hF₀ hFt hF'
      rw [show (120 : ℝ) = ((120 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hw_mod
      exact hD.mono_sub_width (hF'_sub.trans (hFt_sub.trans hF₀_sub)) hw_mod

/--
**Co-Sparse Subcase of Single-Scale Step (`single_scale_cosparse_blockade_step`)**:
If $F' \subseteq F_t$ has $|F'| \ge c |F_t|$ and is $y^3$-sparse in $Gᶜ$, then
`p6Compl_free_sparse_compl_complete_blockade_cube` and `moderate_blockade_width_ge_for_layout`
produce a complete (hence complete-or-$x$-sparse) $(k, |F| / k^d)$-blockade in $F$ with
$k = \lceil 1 / y \rceil \in [2, x^{-10}]$.
-/
theorem single_scale_cosparse_blockade_step
    (G : SimpleGraph V) (S F F₀ F_t F' : Finset V)
    (d_leaf h_leaf δ ε lam : ℝ)
    (hG : IsInducedSubgraphFree G P6Compl)
    (hε : 0 < ε) (hε_half : ε < 1 / 2)
    (hS : ε ^ (-200 * (dParam d_leaf h_leaf δ) ^ 2) ≤ (S.card : ℝ))
    (hF₀_sub : F₀ ⊆ F) (hFt_sub : F_t ⊆ F₀) (hF'_sub : F' ⊆ F_t)
    (hlam_mem : lam ∈ Set.Icc (ε ^ (10 * dParam d_leaf h_leaf δ)) (lambda0Param h_leaf))
    (hF : ε ^ (dParam d_leaf h_leaf δ) * (S.card : ℝ) ≤ (F.card : ℝ))
    (hF₀ : (lambda0Param h_leaf) ^ (b2Param d_leaf h_leaf δ) * (F.card : ℝ) ≤ (F₀.card : ℝ))
    (hFt : lam ^ (b2Param d_leaf h_leaf δ) * (F₀.card : ℝ) ≤ (F_t.card : ℝ))
    (hF' : cParam h_leaf * (F_t.card : ℝ) ≤ (F'.card : ℝ))
    (h_cosparse : IsEpsSparseOn Gᶜ F' ((localSparsityY h_leaf lam) ^ 3)) :
    let d := dParam d_leaf h_leaf δ
    let x := ε ^ (10 * d)
    ∃ (k : ℕ) (B : Fin k → Finset V),
      2 ≤ k ∧ (k : ℝ) ≤ x ^ (-10 : ℝ) ∧
      IsCompleteOrXSparseBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ d) x B := by
  intro d x
  set y := localSparsityY h_leaf lam
  have hx_pos : 0 < x := Real.rpow_pos_of_pos hε (10 * d)
  have hlam_pos : 0 < lam := hx_pos.trans_le hlam_mem.1
  have hlam_le : lam ≤ lambda0Param h_leaf := hlam_mem.2
  have hy_pos : 0 < y := localSparsityY_pos h_leaf hlam_pos
  have hy_48 : y ≤ (2 : ℝ) ^ (-48 : ℝ) := localSparsityY_le_two_rpow_neg_48 h_leaf hlam_pos.le hlam_le
  have hy_360 : y ≤ 1 / 360 := hy_48.trans (by norm_num)
  have hy_le_one : y ≤ 1 := by linarith
  have hx_le_y : x ≤ y := hlam_mem.1.trans (lam_le_localSparsityY h_leaf hlam_pos.le hlam_le)
  have h_cosparse2 : IsEpsSparseOn Gᶜ F' (y ^ 2) := by
    refine h_cosparse.mono ?_
    nlinarith [sq_nonneg y]
  have hF'_1200 : x ^ (-1200 : ℝ) ≤ (F'.card : ℝ) :=
    sub_card_ge_x_rpow_neg_1200 d_leaf h_leaf δ hε hε_half hS hlam_mem.1 hF hF₀ hFt hF'
  have hF'_y2 : 1 / y ^ 2 ≤ (F'.card : ℝ) := by
    have h1 : 1 / y ^ 2 ≤ 1 / x ^ 2 :=
      one_div_le_one_div_of_le (sq_pos_of_pos hx_pos)
        (pow_le_pow_left₀ hx_pos.le hx_le_y 2)
    have h2 : 1 / x ^ 2 = x ^ (-2 : ℝ) := by
      rw [one_div, ← Real.rpow_natCast x 2, ← Real.rpow_neg hx_pos.le]
      norm_num
    have h3 : x ^ (-2 : ℝ) ≤ x ^ (-1200 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hx_pos (hx_le_y.trans hy_le_one) (by norm_num)
    exact (h1.trans_eq h2).trans (h3.trans hF'_1200)
  obtain ⟨B, hB⟩ :=
    p6Compl_free_sparse_compl_complete_blockade_cube G F' y hG hy_pos hy_360 hF'_y2 h_cosparse2
  let k := ⌈1 / y⌉₊
  have hk_ge_inv : 1 / y ≤ (k : ℝ) := Nat.le_ceil _
  have hy_inv_gt2 : 2 < 1 / y := by
    rw [lt_div_iff₀ hy_pos]
    linarith
  have hk2 : 2 ≤ k := by
    have : (2 : ℝ) < (k : ℝ) := hy_inv_gt2.trans_le hk_ge_inv
    exact_mod_cast this.le
  have hk2_real : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  have hk_lt : (k : ℝ) < 1 / y + 1 := Nat.ceil_lt_add_one (by positivity)
  have hk_le_x10 : (k : ℝ) ≤ x ^ (-10 : ℝ) := by
    have h1 : (k : ℝ) ≤ 2 * (1 / y) := by linarith
    have h2 : 1 / y ≤ x ^ (-1 : ℝ) := by
      rw [one_div, Real.rpow_neg_one]
      exact inv_anti₀ hx_pos hx_le_y
    have h3 : (2 : ℝ) ≤ x ^ (-1 : ℝ) := by
      have : (2 : ℝ) ≤ 1 / y := hy_inv_gt2.le
      exact this.trans h2
    calc (k : ℝ)
        ≤ 2 * (1 / y) := h1
      _ ≤ x ^ (-1 : ℝ) * x ^ (-1 : ℝ) := mul_le_mul h3 h2 (by positivity) (by positivity)
      _ = x ^ (-2 : ℝ) := by rw [← Real.rpow_add hx_pos]; norm_num
      _ ≤ x ^ (-10 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hx_pos (hx_le_y.trans hy_le_one) (by norm_num)
  have hy_ge_2k : (2 * (k : ℝ)) ^ (-8 : ℝ) ≤ y := by
    have h1 : 1 / y ≤ 2 * (k : ℝ) := by linarith
    have h2 : (2 * (k : ℝ)) ^ (-1 : ℝ) ≤ y := by
      rw [Real.rpow_neg_one, ← one_div_one_div y, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by positivity) h1
    have h3 : (2 * (k : ℝ)) ^ (-8 : ℝ) ≤ (2 * (k : ℝ)) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    exact h3.trans h2
  have hw_mod := moderate_blockade_width_ge_for_layout d_leaf h_leaf δ hlam_pos hk2 hy_ge_2k hF₀ hFt hF'
  have hw_3_120 : (F'.card : ℝ) / (k : ℝ) ^ (120 : ℝ) ≤ (F'.card : ℝ) / (k : ℝ) ^ (3 : ℝ) := by
    refine div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) ?_
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  refine ⟨k, B, hk2, hk_le_x10, ?_⟩
  refine ⟨(hB.1.mono_ambient (hF'_sub.trans (hFt_sub.trans hF₀_sub))).mono_width
    (hw_mod.trans hw_3_120), fun i j hij => Or.inl (hB.2 i j hij)⟩

/--
**Complete Single-Scale Step at $d_{\mathrm{leaf}} = 3/4, h_{\mathrm{leaf}} = 4$
(`single_scale_step_of_comb_and_iteration`, Proposition 5.3 of `FMBV4-016_readable.tex`)**:
Combines `blockade_iteration_xSparse_four`, `single_scale_sparse_comb_dichotomy`, and
`single_scale_cosparse_blockade_step` to discharge the single-scale hypothesis of `lem_gen_nice_P6`
unconditionally for every $\overline{P_6}$-free graph $G$.
-/
theorem single_scale_step_of_comb_and_iteration
    (G : SimpleGraph V) (S F F₀ F_t : Finset V) (δ ε lam : ℝ)
    (hG : IsInducedSubgraphFree G P6Compl)
    (hε : 0 < ε) (hε_half : ε < 1 / 2)
    (hS : ε ^ (-200 * (dParam (3 / 4) 4 δ) ^ 2) ≤ (S.card : ℝ))
    (hF_sub : F ⊆ S) (hF₀_sub : F₀ ⊆ F) (hFt_sub : F_t ⊆ F₀)
    (hlam_mem : lam ∈ Set.Icc
      (ε ^ (10 * dParam (3 / 4) 4 δ)) (lambda0Param 4))
    (hF : ε ^ (dParam (3 / 4) 4 δ) * (S.card : ℝ) ≤ (F.card : ℝ))
    (hF₀ : (lambda0Param 4) ^ (b2Param (3 / 4) 4 δ) *
      (F.card : ℝ) ≤ (F₀.card : ℝ))
    (hFt_rest : IsEpsRestrictedOn G F_t lam)
    (hFt : lam ^ (b2Param (3 / 4) 4 δ) *
      (F₀.card : ℝ) ≤ (F_t.card : ℝ)) :
    let d := dParam (3 / 4) 4 δ
    let x := ε ^ (10 * d)
    let b₁ := b1Param
    let b₃ := b3Param (3 / 4)
    (GenNiceOutcome3 G S ε (d + 1) (20 * d) ∨
     ∃ (k : ℕ) (B : Fin k → Finset V),
       2 ≤ k ∧ (k : ℝ) ≤ x ^ (-10 : ℝ) ∧
       IsCompleteOrXSparseBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ d) x B) ∨
    ∃ F' ⊆ F_t, IsEpsRestrictedOn G F' (lam ^ b₁) ∧
      lam ^ b₃ * (F_t.card : ℝ) ≤ (F'.card : ℝ) := by
  classical
  set d := dParam (3 / 4) 4 δ
  set x := ε ^ (10 * d)
  set y := localSparsityY 4 lam
  have hc4_eq : cParam 4 = (2 : ℝ) ^ (-16 : ℝ) := by
    unfold cParam bLeaf
    norm_num
  have hx_pos : 0 < x := Real.rpow_pos_of_pos hε (10 * d)
  have hlam_pos : 0 < lam := hx_pos.trans_le hlam_mem.1
  have hlam_le : lam ≤ lambda0Param 4 := hlam_mem.2
  have hy_pos : 0 < y := localSparsityY_pos 4 hlam_pos
  have hy_48 : y ≤ (2 : ℝ) ^ (-48 : ℝ) := localSparsityY_le_two_rpow_neg_48 4 hlam_pos.le hlam_le
  have hy_16 : y ≤ (2 : ℝ) ^ (-16 : ℝ) :=
    hy_48.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num))
  have hy_lt_half : y < 1 / 2 := localSparsityY_lt_half 4 hlam_pos.le hlam_le
  have hy_le_one : y ≤ 1 := by linarith
  have hx_le_y : x ≤ y := hlam_mem.1.trans (lam_le_localSparsityY 4 hlam_pos.le hlam_le)
  by_cases hall : ∀ F' ⊆ F_t, (2 : ℝ) ^ (-16 : ℝ) * (F_t.card : ℝ) ≤ (F'.card : ℝ) →
      ∃ X ⊆ F', ∃ Y ⊆ F', Disjoint X Y ∧
        y ^ (4 : ℝ) * (F'.card : ℝ) ≤ (X.card : ℝ) ∧
        (1 - 4 * y) * (F'.card : ℝ) ≤ (Y.card : ℝ) ∧
        IsXSparseTo G Y X (x ^ 2)
  · left; right
    have hc4_le_one : cParam 4 ≤ 1 := by rw [hc4_eq]; norm_num
    have hFt_self : cParam 4 * (F_t.card : ℝ) ≤ (F_t.card : ℝ) := by
      nlinarith [(Nat.cast_nonneg F_t.card : (0 : ℝ) ≤ (F_t.card : ℝ))]
    have hFt_1200 : x ^ (-1200 : ℝ) ≤ (F_t.card : ℝ) :=
      sub_card_ge_x_rpow_neg_1200 (3 / 4) 4 δ hε hε_half hS hlam_mem.1 hF hF₀ hFt hFt_self
    set Y6 : ℝ := y ^ ((4 : ℝ) + 2) * (F_t.card : ℝ)
    have hy6_Ft : (2 : ℝ) ≤ Y6 := by
      have hx6_le_y6 : x ^ (6 : ℝ) ≤ y ^ ((4 : ℝ) + 2) := by
        rw [show (4 : ℝ) + 2 = 6 by norm_num]
        exact Real.rpow_le_rpow hx_pos.le hx_le_y (by norm_num)
      have hx_1194 : (2 : ℝ) ≤ x ^ (6 : ℝ) * x ^ (-1200 : ℝ) := by
        rw [← Real.rpow_add hx_pos]
        have h2 : (2 : ℝ) ≤ x ^ (-1 : ℝ) := by
          rw [Real.rpow_neg_one, ← inv_inv (2 : ℝ)]
          have : x ≤ (2 : ℝ)⁻¹ := hx_le_y.trans (by norm_num; linarith)
          exact inv_anti₀ hx_pos this
        exact h2.trans (Real.rpow_le_rpow_of_exponent_ge hx_pos (hx_le_y.trans hy_le_one) (by norm_num))
      exact hx_1194.trans (mul_le_mul hx6_le_y6 hFt_1200 (by positivity) (by positivity))
    let m : ℕ := ⌊Y6⌋₊
    have hm_ge2 : (2 : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast Nat.le_floor (by exact_mod_cast hy6_Ft)
    have hm1 : 1 ≤ m := by
      have : (1 : ℝ) ≤ (m : ℝ) := by linarith
      exact_mod_cast this
    have hm_gt : Y6 - 1 < (m : ℝ) := Nat.sub_one_lt_floor Y6
    have hm_quarter : (1 / 4 : ℝ) * Y6 ≤ (1 / 2 : ℝ) * (m : ℝ) := by
      linarith
    obtain ⟨D, _, hD_block⟩ :=
      blockade_iteration_xSparse_four G F_t 4 y (x ^ 2) m (by norm_num) hy_pos hy_16
        (by positivity) hm1 (Nat.floor_le (by positivity)) hall
    let k := ⌈y⁻¹⌉₊
    have hk_ge_inv : y⁻¹ ≤ (k : ℝ) := Nat.le_ceil _
    have hy_inv_gt2 : 2 < y⁻¹ := by
      rw [lt_inv_comm₀ zero_lt_two hy_pos]
      norm_num
      linarith
    have hk2 : 2 ≤ k := by
      have : (2 : ℝ) < (k : ℝ) := hy_inv_gt2.trans_le hk_ge_inv
      exact_mod_cast this.le
    have hk2_real : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    have hk_lt : (k : ℝ) < y⁻¹ + 1 := Nat.ceil_lt_add_one (by positivity)
    have hk_le_2y : (k : ℝ) ≤ 2 * y⁻¹ := by linarith
    have hk_le_x10 : (k : ℝ) ≤ x ^ (-10 : ℝ) := by
      have h2 : y⁻¹ ≤ x ^ (-1 : ℝ) := by
        rw [Real.rpow_neg_one]
        exact inv_anti₀ hx_pos hx_le_y
      have h3 : (2 : ℝ) ≤ x ^ (-1 : ℝ) := hy_inv_gt2.le.trans h2
      calc (k : ℝ)
          ≤ 2 * y⁻¹ := hk_le_2y
        _ ≤ x ^ (-1 : ℝ) * x ^ (-1 : ℝ) := mul_le_mul h3 h2 (by positivity) (by positivity)
        _ = x ^ (-2 : ℝ) := by rw [← Real.rpow_add hx_pos]; norm_num
        _ ≤ x ^ (-10 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge hx_pos (hx_le_y.trans hy_le_one) (by norm_num)
    have hy_ge_2k : (2 * (k : ℝ)) ^ (-8 : ℝ) ≤ y := by
      have h1 : y⁻¹ ≤ 2 * (k : ℝ) := by linarith
      have h2 : (2 * (k : ℝ)) ^ (-1 : ℝ) ≤ y := by
        rw [Real.rpow_neg_one, ← inv_inv y]
        exact inv_anti₀ (by positivity) h1
      have h3 : (2 * (k : ℝ)) ^ (-8 : ℝ) ≤ (2 * (k : ℝ)) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      exact h3.trans h2
    have hw_mod := moderate_blockade_width_ge_for_layout (3 / 4) 4 δ hlam_pos hk2 hy_ge_2k hF₀ hFt hFt_self
    have hk_120_le_y6 : (k : ℝ) ^ (-120 : ℝ) ≤ (1 / 4 : ℝ) * y ^ ((4 : ℝ) + 2) := by
      have hy_ge_k2 : (k : ℝ) ^ (-2 : ℝ) ≤ y := by
        have h2k_le : 2 * (k : ℝ) ≤ (k : ℝ) ^ (2 : ℝ) := by
          rw [Real.rpow_two]
          nlinarith [hk2_real]
        have hk_le_y_inv : y⁻¹ ≤ (k : ℝ) ^ (2 : ℝ) := by
          have : y⁻¹ ≤ 2 * (k : ℝ) := by linarith
          exact this.trans h2k_le
        rw [Real.rpow_neg (by positivity), ← inv_inv y]
        exact inv_anti₀ (by positivity) hk_le_y_inv
      have hk12_le_y6 : (k : ℝ) ^ (-12 : ℝ) ≤ y ^ ((4 : ℝ) + 2) := by
        rw [show (-12 : ℝ) = (-2) * (4 + 2) by norm_num, Real.rpow_mul (by positivity)]
        exact Real.rpow_le_rpow (by positivity) hy_ge_k2 (by norm_num)
      have hk2_le_quarter : (k : ℝ) ^ (-2 : ℝ) ≤ 1 / 4 := by
        have h := rpow_neg_le_two_rpow_neg hk2_real (by norm_num : (0 : ℝ) ≤ 2)
        have h4 : (2 : ℝ) ^ (-2 : ℝ) = 1 / 4 := by norm_num
        rwa [h4] at h
      calc (k : ℝ) ^ (-120 : ℝ)
          ≤ (k : ℝ) ^ (-14 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
        _ = (k : ℝ) ^ (-2 : ℝ) * (k : ℝ) ^ (-12 : ℝ) := by
            rw [← Real.rpow_add (by linarith)]; norm_num
        _ ≤ (1 / 4 : ℝ) * y ^ ((4 : ℝ) + 2) :=
            mul_le_mul hk2_le_quarter hk12_le_y6 (by positivity) (by positivity)
    have hw_chain : (F.card : ℝ) / (k : ℝ) ^ d ≤ (1 / 2 : ℝ) * (m : ℝ) := by
      refine hw_mod.trans ?_
      rw [div_eq_mul_inv, ← Real.rpow_neg (by positivity)]
      calc (F_t.card : ℝ) * (k : ℝ) ^ (-120 : ℝ)
          ≤ (F_t.card : ℝ) * ((1 / 4 : ℝ) * y ^ ((4 : ℝ) + 2)) :=
            mul_le_mul_of_nonneg_left hk_120_le_y6 (Nat.cast_nonneg _)
        _ = (1 / 4 : ℝ) * Y6 := by unfold Y6; ring
        _ ≤ (1 / 2 : ℝ) * (m : ℝ) := hm_quarter
    have hx_sparse_le : 2 * (k : ℝ) ^ 3 * (x ^ 2) ≤ x := by
      have hk3_le : (k : ℝ) ^ 3 ≤ 8 * (y ^ (3 : ℝ))⁻¹ := by
        calc (k : ℝ) ^ 3
            ≤ (2 * y⁻¹) ^ 3 := pow_le_pow_left₀ (by positivity) hk_le_2y 3
          _ = 8 * (y ^ 3)⁻¹ := by ring
          _ = 8 * (y ^ (3 : ℝ))⁻¹ := by
              rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hy3_ge : x / cParam 4 ≤ y ^ (3 : ℝ) := by
        rw [div_le_iff₀ (cParam_pos 4), mul_comm, cParam_mul_localSparsityY_cube 4 hlam_pos.le]
        exact hlam_mem.1
      have hy3_inv_le : (y ^ (3 : ℝ))⁻¹ ≤ cParam 4 / x := by
        rw [← one_div, one_div_le (by positivity) (by positivity), one_div_div]
        exact hy3_ge
      have h16c : 16 * cParam 4 ≤ 1 := by
        rw [hc4_eq]
        norm_num
      calc 2 * (k : ℝ) ^ 3 * (x ^ 2)
          ≤ 2 * (8 * (y ^ (3 : ℝ))⁻¹) * (x ^ 2) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk3_le zero_le_two) (sq_nonneg x)
        _ ≤ 2 * (8 * (cParam 4 / x)) * (x ^ 2) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hy3_inv_le (by norm_num)) zero_le_two)
              (sq_nonneg x)
        _ = (16 * cParam 4) * (x / x * x) := by ring
        _ = (16 * cParam 4) * x := by rw [div_self hx_pos.ne', one_mul]
        _ ≤ 1 * x := mul_le_mul_of_nonneg_right h16c hx_pos.le
        _ = x := one_mul x
    refine ⟨k, D, hk2, hk_le_x10, ⟨(hD_block.1.mono_ambient (hFt_sub.trans hF₀_sub)).mono_width hw_chain, ?_⟩⟩
    intro i j hij
    rcases hD_block.2 i j hij with hcomp | ⟨hsp1, hsp2⟩
    · exact Or.inl hcomp
    · exact Or.inr ⟨fun u hu => (hsp1 u hu).trans (mul_le_mul_of_nonneg_right hx_sparse_le (Nat.cast_nonneg _)),
        fun u hu => (hsp2 u hu).trans (mul_le_mul_of_nonneg_right hx_sparse_le (Nat.cast_nonneg _))⟩
  · push_neg at hall
    obtain ⟨F', hF'_sub, hF'_card16, hF'_no_XY⟩ := hall
    have hF'_card : cParam 4 * (F_t.card : ℝ) ≤ (F'.card : ℝ) := by
      rwa [hc4_eq]
    rcases isEpsRestrictedOn_localSparsityY_cube_of_subset G F_t F' 4 hlam_pos.le hF'_sub hF'_card hFt_rest with
      h_sparse | h_cosparse
    · rcases single_scale_sparse_comb_dichotomy G S F F₀ F_t F' (3 / 4) 4 δ ε lam hG hε hε_half
        hS hF_sub hF₀_sub hFt_sub hF'_sub hlam_mem hF hF₀ hFt hF'_card h_sparse with
        h_out | ⟨X, hXF', Y, hYF', hdisj, hX_card, hY_card, hXY_sparse⟩
      · exact h_out
      · exact False.elim (hF'_no_XY X hXF' Y hYF' hdisj hX_card hY_card hXY_sparse)
    · refine Or.inl (Or.inr ?_)
      exact single_scale_cosparse_blockade_step G S F F₀ F_t F' (3 / 4) 4 δ ε lam hG hε hε_half
        hS hF₀_sub hFt_sub hF'_sub hlam_mem hF hF₀ hFt hF'_card h_cosparse

/--
**Unconditional Generalized Niceness of $\{P_6\}$ (`gen_nice_P6_unconditional`,
Proposition 5.3, `prop:gen-nice` of `FMBV4-016_readable.tex`)**:
For every $\overline{P_6}$-free graph $G$ on a vertex set $S \subseteq V(G)$ with $\kappa(G) \ge 1$
and every $\varepsilon \in (0, 1/2)$, $G[S]$ satisfies `SatisfiesGenNiceAt` with explicit positive
constants $(200 d^2, d, 200 d^2, 1, d + 1, 20 d, 10 d, 200 d^2)$, where
$d = \mathrm{dParam}(3/4, 4, \mathrm{rodlDelta}(\mathrm{lambda0Param}(4)))$.
-/
theorem gen_nice_P6_unconditional (G : SimpleGraph V) (S : Finset V) {ε : ℝ}
    (hG : IsInducedSubgraphFree G P6Compl)
    (hε : 0 < ε) (hε_half : ε < 1 / 2)
    (hkappa : 1 ≤ kappa G) :
    let d := dParam (3 / 4) 4 (rodlDelta (lambda0Param 4))
    SatisfiesGenNiceAt G S ε (200 * d ^ 2) d (200 * d ^ 2) 1 (d + 1) (20 * d) (10 * d) (200 * d ^ 2) := by
  set δ := rodlDelta (lambda0Param 4)
  set d := dParam (3 / 4) 4 δ
  by_cases hS_small : (S.card : ℝ) ≤ ε ^ (-200 * d ^ 2)
  · exact Or.inr (Or.inl (genNiceOutcome2_of_card_le hε hkappa hS_small))
  · push_neg at hS_small
    refine lem_gen_nice_P6 G S hε hε_half hkappa ?_
    intro d' x lam0 b₁ b₂ b₃ F hF_sub hF_card
    refine ⟨eps_pow_ten_dParam_lt_lambda0Param (3 / 4) 4 δ hε hε_half, ?_⟩
    obtain ⟨F₀, hF₀_sub, hF₀_rest, hF₀_card⟩ :=
      rodl_initial_step_for_gen_nice G F (3 / 4) 4 hG
    refine ⟨F₀, hF₀_sub, hF₀_rest,
      eps_200_d_sq_le_x_b1_b2_card (3 / 4) 4 δ hε hε_half hF_card hF₀_card, ?_⟩
    intro lam hlam_mem F_t hFt_sub hFt_rest hFt_card
    exact single_scale_step_of_comb_and_iteration G S F F₀ F_t δ ε lam hG hε hε_half hS_small.le
      hF_sub hF₀_sub hFt_sub hlam_mem hF_card hF₀_card hFt_rest hFt_card

/-!
### Part 3 Synthesis: Stage 2 Reduction for $P_5$ and $P_6$, and Final Theorem Proofs
(Proposition 5.4 and Theorem 1.1 of `FMBV4-016_readable.tex`)
-/

/--
Predicate stating that a graph $G$ satisfies the wonderful blockade dichotomy (Definition 2.1(3) / Proposition 3.2) with
exponent $a$ on every equal-sized anticonnected complete-or-$y^a$-sparse $(\ell, w)$-blockade.
-/
def HasWonderfulAnticonnectedBlockade (G : SimpleGraph V) (a : ℝ) : Prop :=
  ∀ (F' : Finset V) (ℓ w_nat : ℕ) (y : ℝ) (B : Fin ℓ → Finset V),
    IsCompleteOrXSparseBlockadeIn G F' ℓ (w_nat : ℝ) (y ^ a) B →
    0 < ℓ → 0 < w_nat → (∀ i : Fin ℓ, (B i).card = w_nat) →
    (∀ i : Fin ℓ, IsAnticonnected G (B i)) →
    0 < y → y ≤ 1 / 2 → y ^ (-a) ≤ (ℓ : ℝ) →
    (∃ U ⊆ F', w_nat ≤ U.card ∧ IsEpsRestrictedOn G U (y ^ 4)) ∨
    (∃ i : Fin ℓ, ((openAttachmentExternalVerts G F' B i).card : ℝ) < y * (F'.card : ℝ))

/--
**Base Case of Wonderfulness (`hasWonderfulAnticonnectedBlockade_of_isP5ComplFree`)**:
Every $\overline{P_5}$-free graph $G$ satisfies `HasWonderfulAnticonnectedBlockade G 7`, because by
`p5Compl_free_openAttachment_not_completePair`, for every external vertex $v$, the open attachment
index set $I(v)$ is already an independent set in `blockadePatternGraph G B`.
-/
theorem hasWonderfulAnticonnectedBlockade_of_isP5ComplFree (G : SimpleGraph V)
    (hG : IsInducedSubgraphFree G P5Compl) :
    HasWonderfulAnticonnectedBlockade G 7 := by
  intro F' ℓ w_nat y B hB hℓ hw_pos hw_eq hanti hy_pos hy_le hℓ_ge
  have hG6 : IsInducedSubgraphFree G P6Compl := isP6ComplFree_of_isP5ComplFree G hG
  obtain ⟨hya_six, hya_le, h_rpow_ge⟩ :=
    wonderful_exponent_bounds (c_H := 1) zero_lt_one le_rfl (by norm_num) hy_pos hy_le hℓ_ge
  rw [Real.rpow_one] at h_rpow_ge
  refine p6_is_wonderful hG6 hB hℓ hw_pos hw_eq hy_pos hya_six ?_
  intro v hv_ext hv_large _hFree
  let R := openAttachmentIndices G B v
  have hR_ge : 2 / (y ^ 4) ≤ (R.card : ℝ) := h_rpow_ge.trans hv_large
  have hy4_pos : 0 < y ^ 4 := by positivity
  have hR_pos : 0 < (R.card : ℝ) := lt_of_lt_of_le (div_pos zero_lt_two hy4_pos) hR_ge
  have hR_ne : R.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hR_pos)
  have h1R : 1 / (R.card : ℝ) ≤ (y ^ 4) / 2 := by
    rw [div_le_div_iff₀ hR_pos zero_lt_two]
    have h2 : 2 ≤ (R.card : ℝ) * (y ^ 4) := (div_le_iff₀ hy4_pos).mp hR_ge
    linarith
  refine ⟨R, Subset.rfl, hR_ne, by linarith, Or.inr ?_⟩
  intro i hi j hj hij hadj
  have hv_ext' := (mem_blockadeExternalVerts F' B v).mp hv_ext
  have hv_sdiff : v ∈ F' \ Finset.univ.biUnion B := by
    rw [Finset.mem_sdiff, Finset.mem_biUnion]
    exact ⟨hv_ext'.1, fun ⟨k, _, hvk⟩ => hv_ext'.2 k hvk⟩
  have hi' := (mem_openAttachmentIndices G B v i).mp hi
  have hj' := (mem_openAttachmentIndices G B v j).mp hj
  have hi_lt : (neighborFinsetIn G v (B i)).card < (B i).card := by
    have : ((neighborFinsetIn G v (B i)).card : ℝ) < ((B i).card : ℝ) := by
      linarith [hi'.2, (Nat.cast_nonneg (B i).card : (0 : ℝ) ≤ ((B i).card : ℝ))]
    exact_mod_cast this
  have hj_lt : (neighborFinsetIn G v (B j)).card < (B j).card := by
    have : ((neighborFinsetIn G v (B j)).card : ℝ) < ((B j).card : ℝ) := by
      linarith [hj'.2, (Nat.cast_nonneg (B j).card : (0 : ℝ) ≤ ((B j).card : ℝ))]
    exact_mod_cast this
  exact p5Compl_free_openAttachment_not_completePair G F' B hG hB.1 hanti v hv_sdiff i j hij
    hi'.1 hi_lt hj'.1 hj_lt hadj.2

/--
**Inductive Case of Wonderfulness (`hasWonderfulAnticonnectedBlockade_of_witnessH_eh`)**:
If `witnessH` satisfies the Erdős–Hajnal property with exponent $c_H > 0$, then every
$\overline{P_6}$-free graph $G$ satisfies `HasWonderfulAnticonnectedBlockade G (max 7 (5 / c_H + 1))`.
-/
theorem hasWonderfulAnticonnectedBlockade_of_witnessH_eh (G : SimpleGraph V) {c_H : ℝ}
    (hG : IsInducedSubgraphFree G P6Compl) (hcH_pos : 0 < c_H)
    (h_eh : ∀ (W : Type) [Fintype W] [DecidableEq W] (J : SimpleGraph W),
      IsInducedSubgraphFree J witnessH → (Fintype.card W : ℝ) ^ c_H ≤ (kappa J : ℝ)) :
    HasWonderfulAnticonnectedBlockade G (max 7 (5 / c_H + 1)) := by
  intro F' ℓ w_nat y B hB _hℓ hw_pos hw_eq _hanti hy_pos hy_le hℓ_ge
  exact p6_is_wonderful_of_hasErdosHajnalProp_witnessH hG hB hw_pos hw_eq hcH_pos h_eh
    (le_max_left _ _) (le_max_right _ _) hy_pos hy_le hℓ_ge

/--
Set equality identifying the open-interval attachment filter in `step1d_open_interval_attachment`
with `openAttachmentExternalVerts G F' B istar`.
-/
theorem openAttachmentExternalVerts_eq_filter_sdiff (G : SimpleGraph V) (F' : Finset V)
    {ℓ w_nat : ℕ} (B : Fin ℓ → Finset V) (istar : Fin ℓ)
    (hw_eq : (B istar).card = w_nat) :
    (F' \ (Finset.univ : Finset (Fin ℓ)).biUnion B).filter (fun v =>
      0 < (neighborFinsetIn G v (B istar)).card ∧
      ((neighborFinsetIn G v (B istar)).card : ℝ) < (1 / 2 : ℝ) * (w_nat : ℝ)) =
    openAttachmentExternalVerts G F' B istar := by
  ext v
  simp [mem_openAttachmentExternalVerts, mem_blockadeExternalVerts,
    mem_openAttachmentIndices, hw_eq, and_assoc]

/--
Helper lemma for Case (GN1) of `stage2_step1_dichotomy`, parameterized by plain variables
`a₃ ε : ℝ` and `ℓ m : ℕ` so that `Fin ℓ` is non-dependent and tactics do not unfold ceiling/floor bindings.
-/
private theorem stage2_step1_case_gn1 (G : SimpleGraph V) (F' : Finset V)
    (d a y a₃ ε : ℝ) (ℓ m : ℕ)
    (hd : 600 ≤ d) (hy_pos : 0 < y) (hy_lt_half : y < 1 / 2)
    (hε_pos : 0 < ε) (hε_le_y : ε ≤ y) (hε_le_16 : ε ≤ 1 / 16) (hε_le_one : ε ≤ 1)
    (h16_le_inv : 16 ≤ ε⁻¹) (hy_inv_le_ε_inv : y⁻¹ ≤ ε⁻¹)
    (hε_eq_ya : ε = y ^ a)
    (hya₃_eq : y ^ a₃ = ε ^ (200 * d ^ 2 + 2))
    (hF'_small : 1 < y ^ a₃ * (F'.card : ℝ))
    (hF'_sparse : IsEpsSparseOn G F' y)
    (h_wonderful : HasWonderfulAnticonnectedBlockade G a)
    (hℓ_ge_inv : ε⁻¹ ≤ (ℓ : ℝ))
    (hℓ_lt : (ℓ : ℝ) < ε⁻¹ + 1)
    (hm_gt : ε ^ (200 * d ^ 2) * (F'.card : ℝ) - 1 < (m : ℝ))
    (hm_le_real : (m : ℝ) ≤ ε ^ (200 * d ^ 2) * (F'.card : ℝ))
    (A : Fin ℓ → Finset V)
    (hA_block : IsBlockadeIn G F' ℓ (m : ℝ) A)
    (hA_pairs : ∀ i j : Fin ℓ, i ≠ j → IsCompleteOrWeaklyXSparsePair G (A i) (A j) (ε ^ d)) :
    (y ^ a₃ * (F'.card : ℝ) ≤ (kappa G : ℝ)) ∨
    (∃ k : ℕ, 2 ≤ k ∧ y⁻¹ ≤ (k : ℝ) ∧ ∃ B : Fin k → Finset V,
      IsCompleteBlockadeIn G F' k ((F'.card : ℝ) / (k : ℝ) ^ (200 * d ^ 2 + 4)) B ∨
      IsAnticompleteBlockadeIn G F' k ((F'.card : ℝ) / (k : ℝ) ^ (200 * d ^ 2 + 4)) B) ∨
    (∃ U ⊆ F', y ^ a₃ * (F'.card : ℝ) ≤ (U.card : ℝ) ∧ IsEpsRestrictedOn G U (y ^ (4 : ℝ))) ∨
    (∃ X ⊆ F', ∃ Y ⊆ F', Disjoint X Y ∧
      y ^ a₃ * (F'.card : ℝ) ≤ (X.card : ℝ) ∧
      (1 - 4 * y) * (F'.card : ℝ) ≤ (Y.card : ℝ) ∧
      IsPurePair G X Y) := by
  have hd2_nonneg : 0 ≤ d ^ 2 := sq_nonneg d
  have hd2_ge : 1 ≤ d ^ 2 := by
    calc (1 : ℝ) ≤ 600 * 600 := by norm_num
      _ ≤ d * d := mul_self_le_mul_self (by norm_num) hd
      _ = d ^ 2 := (sq d).symm
  have hℓ_ge_16 : (16 : ℝ) ≤ (ℓ : ℝ) := h16_le_inv.trans hℓ_ge_inv
  have hℓ2 : 2 ≤ ℓ := by
    have : (2 : ℝ) ≤ (ℓ : ℝ) := by linarith
    exact_mod_cast this
  have hℓ_le_2inv : (ℓ : ℝ) ≤ 2 * ε⁻¹ := by linarith
  have hε2_inv : (ε ^ (2 : ℝ))⁻¹ = ε⁻¹ * ε⁻¹ := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq, mul_inv]
  have hℓ_le_ε2_inv : (ℓ : ℝ) ≤ (ε ^ (2 : ℝ))⁻¹ := by
    rw [hε2_inv]
    have h2_le_inv : (2 : ℝ) ≤ ε⁻¹ := by linarith
    calc (ℓ : ℝ) ≤ 2 * ε⁻¹ := hℓ_le_2inv
      _ ≤ ε⁻¹ * ε⁻¹ := mul_le_mul_of_nonneg_right h2_le_inv (by positivity)
  have hε2_pos : 0 < ε ^ (2 : ℝ) := Real.rpow_pos_of_pos hε_pos 2
  have hε2_le_quarter : ε ^ (2 : ℝ) ≤ 1 / 4 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    nlinarith
  have hε200_ge_inv_sq : ε⁻¹ * ε⁻¹ ≤ ε ^ (200 * d ^ 2) * (F'.card : ℝ) := by
    have h1 : 1 ≤ ε ^ (2 : ℝ) * (ε ^ (200 * d ^ 2) * (F'.card : ℝ)) := by
      calc (1 : ℝ) ≤ y ^ a₃ * (F'.card : ℝ) := hF'_small.le
        _ = (ε ^ (2 : ℝ) * ε ^ (200 * d ^ 2)) * (F'.card : ℝ) := by
            rw [hya₃_eq, show 200 * d ^ 2 + 2 = 2 + 200 * d ^ 2 by ring, Real.rpow_add hε_pos]
        _ = ε ^ (2 : ℝ) * (ε ^ (200 * d ^ 2) * (F'.card : ℝ)) := by ring
    have h2 := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hε2_pos.le)
    rwa [mul_one, ← mul_assoc, inv_mul_cancel₀ hε2_pos.ne', one_mul, hε2_inv] at h2
  have h8ℓ_le : 8 * (ℓ : ℝ) ≤ ε⁻¹ * ε⁻¹ := by
    calc 8 * (ℓ : ℝ) ≤ 8 * (2 * ε⁻¹) := mul_le_mul_of_nonneg_left hℓ_le_2inv (by norm_num)
      _ = 16 * ε⁻¹ := by ring
      _ ≤ ε⁻¹ * ε⁻¹ := mul_le_mul_of_nonneg_right h16_le_inv (by positivity)
  have hm_ge : 4 * (ℓ : ℝ) ≤ (m : ℝ) := by linarith
  have hm_half : (1 / 2 : ℝ) * (ε ^ (200 * d ^ 2) * (F'.card : ℝ)) ≤ (m : ℝ) := by
    have : (2 : ℝ) ≤ ε⁻¹ * ε⁻¹ := by nlinarith
    linarith
  have hε2_d2 : (ε ^ (2 : ℝ)) ^ (d / 2) = ε ^ d := by
    rw [← Real.rpow_mul hε_pos.le, mul_div_cancel₀ _ two_ne_zero]
  have hpairs_clean : ∀ i j : Fin ℓ, i ≠ j →
      IsCompleteOrWeaklyXSparsePair G (A i) (A j) ((ε ^ (2 : ℝ)) ^ (d / 2)) := by
    rw [hε2_d2]
    exact hA_pairs
  rcases stage2_step1_sparse_to_blockade_or_anticonnected G F' ℓ m (ε ^ (2 : ℝ)) (d / 2)
      hℓ2 hℓ_le_ε2_inv hε2_pos hε2_le_quarter hm_ge A hA_block hpairs_clean with
    ⟨B, hB_comp⟩ | ⟨w, B, hw1, hw_ge, hw_le, _hB_sub, hB_card, hB_anti, hB_block⟩
  · -- Subcase 1a: Complete (ℓ, m / (2 ℓ^2))-blockade in F'
    right; left
    refine ⟨ℓ, hℓ2, hy_inv_le_ε_inv.trans hℓ_ge_inv, B, Or.inl ⟨hB_comp.1.mono_width ?_, hB_comp.2⟩⟩
    have hℓ_pos : (0 : ℝ) < (ℓ : ℝ) := by linarith
    have h_inv_ℓ : (ℓ : ℝ)⁻¹ ≤ ε := (inv_le_comm₀ hε_pos hℓ_pos).mp hℓ_ge_inv
    have h_rpow_ℓ : ((ℓ : ℝ)⁻¹) ^ (200 * d ^ 2) ≤ ε ^ (200 * d ^ 2) :=
      Real.rpow_le_rpow (by positivity) h_inv_ℓ (by positivity)
    rw [Real.inv_rpow hℓ_pos.le] at h_rpow_ℓ
    have h4_le_ℓ2 : 4 * (ℓ : ℝ) ^ 2 ≤ (ℓ : ℝ) ^ (4 : ℝ) := by
      have h_pow : (ℓ : ℝ) ^ (4 : ℝ) = (ℓ : ℝ) ^ 2 * (ℓ : ℝ) ^ 2 := by
        rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        ring
      rw [h_pow]
      have h4 : (4 : ℝ) ≤ (ℓ : ℝ) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right h4 (sq_nonneg _)
    have h_denom : (4 * (ℓ : ℝ) ^ 2) * (ℓ : ℝ) ^ (200 * d ^ 2) ≤ (ℓ : ℝ) ^ (200 * d ^ 2 + 4) := by
      calc (4 * (ℓ : ℝ) ^ 2) * (ℓ : ℝ) ^ (200 * d ^ 2)
          ≤ (ℓ : ℝ) ^ (4 : ℝ) * (ℓ : ℝ) ^ (200 * d ^ 2) :=
            mul_le_mul_of_nonneg_right h4_le_ℓ2 (Real.rpow_nonneg hℓ_pos.le _)
        _ = (ℓ : ℝ) ^ (200 * d ^ 2 + 4) := by
            rw [← Real.rpow_add hℓ_pos]
            congr 1; ring
    have h_div1 : (F'.card : ℝ) / (ℓ : ℝ) ^ (200 * d ^ 2 + 4) ≤
        (F'.card : ℝ) / ((4 * (ℓ : ℝ) ^ 2) * (ℓ : ℝ) ^ (200 * d ^ 2)) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _)
        (mul_pos (by positivity) (Real.rpow_pos_of_pos hℓ_pos _)) h_denom
    have h_div2 : (F'.card : ℝ) / ((4 * (ℓ : ℝ) ^ 2) * (ℓ : ℝ) ^ (200 * d ^ 2)) =
        ((1 / 2 : ℝ) * (((ℓ : ℝ) ^ (200 * d ^ 2))⁻¹ * (F'.card : ℝ))) / (2 * (ℓ : ℝ) ^ 2) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv,
        show (4 : ℝ) * (ℓ : ℝ) ^ 2 = 2 * (2 * (ℓ : ℝ) ^ 2) by ring, mul_inv]
      ring
    have h_num : (1 / 2 : ℝ) * (((ℓ : ℝ) ^ (200 * d ^ 2))⁻¹ * (F'.card : ℝ)) ≤ (m : ℝ) := by
      calc (1 / 2 : ℝ) * (((ℓ : ℝ) ^ (200 * d ^ 2))⁻¹ * (F'.card : ℝ))
          ≤ (1 / 2 : ℝ) * (ε ^ (200 * d ^ 2) * (F'.card : ℝ)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            exact mul_le_mul_of_nonneg_right h_rpow_ℓ (Nat.cast_nonneg _)
        _ ≤ (m : ℝ) := hm_half
    exact h_div1.trans (h_div2.trans_le (div_le_div_of_nonneg_right h_num (by positivity)))
  · -- Subcase 1b: Equal-sized anticonnected (ℓ, w)-blockade in F'
    have hℓ_pos_real : (0 : ℝ) < (ℓ : ℝ) := by linarith
    have hw_ge_a₃ : y ^ a₃ * (F'.card : ℝ) ≤ (w : ℝ) := by
      have h4ℓ_pos : (0 : ℝ) < 4 * (ℓ : ℝ) := by linarith
      have h4ℓ_le_inv2 : 4 * (ℓ : ℝ) ≤ (ε ^ (2 : ℝ))⁻¹ := by
        rw [hε2_inv]
        linarith
      have hε2_le_4ℓ : ε ^ (2 : ℝ) ≤ (4 * (ℓ : ℝ))⁻¹ :=
        (le_inv_comm₀ h4ℓ_pos hε2_pos).mp h4ℓ_le_inv2
      have hsplit : y ^ a₃ * (F'.card : ℝ) =
          ε ^ (2 : ℝ) * (ε ^ (200 * d ^ 2) * (F'.card : ℝ)) := by
        rw [hya₃_eq, show 200 * d ^ 2 + 2 = 2 + 200 * d ^ 2 by ring, Real.rpow_add hε_pos]
        ring
      have hm_two : ε ^ (200 * d ^ 2) * (F'.card : ℝ) ≤ 2 * (m : ℝ) := by linarith
      have h_step1 : ε ^ (2 : ℝ) * (ε ^ (200 * d ^ 2) * (F'.card : ℝ)) ≤
          (4 * (ℓ : ℝ))⁻¹ * (2 * (m : ℝ)) :=
        mul_le_mul hε2_le_4ℓ hm_two
          (mul_nonneg (Real.rpow_nonneg hε_pos.le _) (Nat.cast_nonneg _))
          (inv_nonneg.mpr h4ℓ_pos.le)
      have h_step2 : (4 * (ℓ : ℝ))⁻¹ * (2 * (m : ℝ)) = (m : ℝ) / (2 * (ℓ : ℝ)) := by
        rw [div_eq_mul_inv, show (4 : ℝ) * (ℓ : ℝ) = 2 * (2 * (ℓ : ℝ)) by ring, mul_inv]
        ring
      exact (hsplit.trans_le h_step1).trans (h_step2.trans_le hw_ge)
    have h_sparse_ya : (ε ^ (2 : ℝ)) ^ (d / 2 - 7) ≤ y ^ a := by
      rw [← Real.rpow_mul hε_pos.le]
      have h1 : 2 * (d / 2 - 7) = d - 14 := by ring
      rw [h1]
      calc ε ^ (d - 14) ≤ ε ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hε_pos hε_le_one (by linarith)
        _ = ε := Real.rpow_one ε
        _ = y ^ a := hε_eq_ya
    have hB_block_ya : IsCompleteOrXSparseBlockadeIn G F' ℓ (w : ℝ) (y ^ a) B := by
      refine ⟨hB_block.1, fun i j hij => ?_⟩
      rcases hB_block.2 i j hij with hcomp | ⟨hsp1, hsp2⟩
      · exact Or.inl hcomp
      · exact Or.inr ⟨fun u hu => (hsp1 u hu).trans (mul_le_mul_of_nonneg_right h_sparse_ya (Nat.cast_nonneg _)),
          fun u hu => (hsp2 u hu).trans (mul_le_mul_of_nonneg_right h_sparse_ya (Nat.cast_nonneg _))⟩
    have hℓ_ge_ya : y ^ (-a) ≤ (ℓ : ℝ) := by
      rw [Real.rpow_neg hy_pos.le, ← hε_eq_ya]
      exact hℓ_ge_inv
    rcases h_wonderful F' ℓ w y B hB_block_ya (by omega) (by omega) hB_card hB_anti
        hy_pos hy_lt_half.le hℓ_ge_ya with
      ⟨U, hU_sub, hw_U, hU_rest⟩ | ⟨istar, histar⟩
    · -- Outcome (W1) -> (R3)
      right; right; left
      have hw_U_real : (w : ℝ) ≤ (U.card : ℝ) := by exact_mod_cast hw_U
      refine ⟨U, hU_sub, hw_ge_a₃.trans hw_U_real, ?_⟩
      rwa [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    · -- Outcome (W2) -> (R4) via step1d_open_interval_attachment
      right; right; right
      have hℓw : ((ℓ * w : ℕ) : ℝ) ≤ y * (F'.card : ℝ) := by
        push_cast
        have h1 : (ℓ : ℝ) * (w : ℝ) ≤ (ε ^ (-2 : ℝ)) * (ε ^ (200 * d ^ 2) * (F'.card : ℝ)) := by
          have hℓ_le_neg2 : (ℓ : ℝ) ≤ ε ^ (-2 : ℝ) := by
            rw [Real.rpow_neg hε_pos.le]
            exact hℓ_le_ε2_inv
          exact mul_le_mul hℓ_le_neg2 (hw_le.trans hm_le_real)
            (Nat.cast_nonneg _) (Real.rpow_nonneg hε_pos.le _)
        have h2 : (ε ^ (-2 : ℝ)) * (ε ^ (200 * d ^ 2) * (F'.card : ℝ)) =
            ε ^ (200 * d ^ 2 - 2) * (F'.card : ℝ) := by
          rw [← mul_assoc, ← Real.rpow_add hε_pos]
          congr 2; ring
        have h3 : ε ^ (200 * d ^ 2 - 2) ≤ y := by
          calc ε ^ (200 * d ^ 2 - 2) ≤ ε ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_ge hε_pos hε_le_one (by linarith)
            _ = ε := Real.rpow_one ε
            _ ≤ y := hε_le_y
        exact (h1.trans_eq h2).trans (mul_le_mul_of_nonneg_right h3 (Nat.cast_nonneg _))
      have hopen : (((F' \ (Finset.univ : Finset (Fin ℓ)).biUnion B).filter (fun v =>
          0 < (neighborFinsetIn G v (B istar)).card ∧
          ((neighborFinsetIn G v (B istar)).card : ℝ) < (1 / 2 : ℝ) * (w : ℝ))).card : ℝ) ≤
            y * (F'.card : ℝ) := by
        rw [openAttachmentExternalVerts_eq_filter_sdiff G F' B istar (hB_card istar)]
        exact histar.le
      obtain ⟨X, hXF', Y, hYF', hdisj, hX_card, hY_card, hanti_XY⟩ :=
        step1d_open_interval_attachment G F' ℓ w y hw1 hy_pos hF'_sparse B
          hB_block.1.subset_ambient hB_card hℓw istar hopen
      refine ⟨X, hXF', Y, hYF', hdisj, ?_, hY_card, Or.inr hanti_XY⟩
      rw [hX_card]
      exact hw_ge_a₃

/--
**Stage 2 Step 1 Dichotomy (`stage2_step1_dichotomy`, Step 1 of Proposition 5.4 of `FMBV4-016_readable.tex`)**:
For any $y$-sparse subset $F'$ ($0 < y \le 2^{-144}$) of a graph $G$ satisfying Generalized Niceness
with parameter $d \ge 600$ and `HasWonderfulAnticonnectedBlockade G a` ($a \ge 7$), setting
$a_3 := a (200 d^2 + 2)$ yields one of the four outcomes **(R1)**–**(R4)**.
-/
theorem stage2_step1_dichotomy (G : SimpleGraph V) (F' : Finset V) (d a y : ℝ)
    (hd : 600 ≤ d) (ha : 7 ≤ a)
    (hy_pos : 0 < y) (hy_le : y ≤ (2 : ℝ) ^ (-144 : ℝ))
    (hkappa : 1 ≤ kappa G)
    (hF'_sparse : IsEpsSparseOn G F' y)
    (h_wonderful : HasWonderfulAnticonnectedBlockade G a)
    (h_gen_nice : ∀ {ε : ℝ}, 0 < ε → ε < 1 / 2 →
      SatisfiesGenNiceAt G F' ε (200 * d ^ 2) d (200 * d ^ 2) 1 (d + 1) (20 * d) (10 * d) (200 * d ^ 2)) :
    let a₃ := a * (200 * d ^ 2 + 2)
    (y ^ a₃ * (F'.card : ℝ) ≤ (kappa G : ℝ)) ∨
    (∃ k : ℕ, 2 ≤ k ∧ y⁻¹ ≤ (k : ℝ) ∧ ∃ B : Fin k → Finset V,
      IsCompleteBlockadeIn G F' k ((F'.card : ℝ) / (k : ℝ) ^ (200 * d ^ 2 + 4)) B ∨
      IsAnticompleteBlockadeIn G F' k ((F'.card : ℝ) / (k : ℝ) ^ (200 * d ^ 2 + 4)) B) ∨
    (∃ U ⊆ F', y ^ a₃ * (F'.card : ℝ) ≤ (U.card : ℝ) ∧ IsEpsRestrictedOn G U (y ^ (4 : ℝ))) ∨
    (∃ X ⊆ F', ∃ Y ⊆ F', Disjoint X Y ∧
      y ^ a₃ * (F'.card : ℝ) ≤ (X.card : ℝ) ∧
      (1 - 4 * y) * (F'.card : ℝ) ≤ (Y.card : ℝ) ∧
      IsPurePair G X Y) := by
  set a₃ := a * (200 * d ^ 2 + 2)
  set ε := y ^ a
  have hkappa_real : (1 : ℝ) ≤ (kappa G : ℝ) := by exact_mod_cast hkappa
  by_cases hF'_small : y ^ a₃ * (F'.card : ℝ) ≤ 1
  · exact Or.inl (hF'_small.trans hkappa_real)
  push_neg at hF'_small
  have hy_le_16 : y ≤ 1 / 16 := by
    have h1 : (2 : ℝ) ^ (-144 : ℝ) ≤ (2 : ℝ) ^ (-4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have h2 : (2 : ℝ) ^ (-4 : ℝ) = 1 / 16 := by norm_num
    exact (hy_le.trans h1).trans_eq h2
  have hy_lt_half : y < 1 / 2 := by linarith
  have hy_le_one : y ≤ 1 := by linarith
  have hε_pos : 0 < ε := Real.rpow_pos_of_pos hy_pos a
  have hε_le_y : ε ≤ y := by
    calc ε = y ^ a := rfl
      _ ≤ y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hy_pos hy_le_one (by linarith)
      _ = y := Real.rpow_one y
  have hε_le_16 : ε ≤ 1 / 16 := hε_le_y.trans hy_le_16
  have hε_lt_half : ε < 1 / 2 := lt_of_le_of_lt hε_le_y hy_lt_half
  have hε_le_one : ε ≤ 1 := by linarith
  have h16_le_inv : 16 ≤ ε⁻¹ := by
    have h1 : 16 * ε ≤ 1 := by linarith
    have h2 := mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr hε_pos.le)
    rwa [mul_assoc, mul_inv_cancel₀ hε_pos.ne', mul_one, one_mul] at h2
  have hy_inv_le_ε_inv : y⁻¹ ≤ ε⁻¹ := inv_anti₀ hε_pos hε_le_y
  have hya₃_eq : y ^ a₃ = ε ^ (200 * d ^ 2 + 2) := by
    dsimp [a₃, ε]
    rw [← Real.rpow_mul hy_pos.le]
  have hya₃_le_ε200 : y ^ a₃ ≤ ε ^ (200 * d ^ 2) := by
    rw [hya₃_eq]
    exact Real.rpow_le_rpow_of_exponent_ge hε_pos hε_le_one (by linarith)
  rcases h_gen_nice hε_pos hε_lt_half with hGN1 | hGN2 | hGN3 | hGN4
  · -- Case (GN1): (⌈ε⁻¹⌉₊, ⌊ε^(200 d^2) |F'|⌋₊)-blockade with complete or weakly ε^d-sparse pairs
    obtain ⟨A, hA_block, hA_pairs⟩ := hGN1
    exact stage2_step1_case_gn1 G F' d a y a₃ ε ⌈ε⁻¹⌉₊ ⌊ε ^ (200 * d ^ 2) * (F'.card : ℝ)⌋₊
      hd hy_pos hy_lt_half hε_pos hε_le_y hε_le_16 hε_le_one h16_le_inv hy_inv_le_ε_inv
      rfl hya₃_eq hF'_small hF'_sparse h_wonderful
      (Nat.le_ceil _) (Nat.ceil_lt_add_one (by positivity))
      (Nat.sub_one_lt_floor _) (Nat.floor_le (by positivity))
      A hA_block hA_pairs
  · -- Case (GN2): (ε^(200 d^2) |F'|)^1 ≤ kappa G -> (R1)
    left
    unfold GenNiceOutcome2 at hGN2
    rw [Real.rpow_one] at hGN2
    exact (mul_le_mul_of_nonneg_right hya₃_le_ε200 (Nat.cast_nonneg _)).trans hGN2
  · -- Case (GN3): pure (k, |F'| / k^(d+1))-blockade with k ≥ ε^(-20 d) -> (R2)
    right; left
    obtain ⟨k, B, hk_ge, hB_pure⟩ := hGN3
    have h_inv_le_20d : ε⁻¹ ≤ ε ^ (-(20 * d)) := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_ge hε_pos hε_le_one (by linarith)
    have hk_ge_inv : ε⁻¹ ≤ (k : ℝ) := h_inv_le_20d.trans hk_ge
    have hk_ge_16 : (16 : ℝ) ≤ (k : ℝ) := h16_le_inv.trans hk_ge_inv
    have hk2 : 2 ≤ k := by
      have : (2 : ℝ) ≤ (k : ℝ) := by linarith
      exact_mod_cast this
    have hw_le : (F'.card : ℝ) / (k : ℝ) ^ (200 * d ^ 2 + 4) ≤ (F'.card : ℝ) / (k : ℝ) ^ (d + 1) := by
      refine div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) ?_
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by nlinarith)
    refine ⟨k, hk2, hy_inv_le_ε_inv.trans hk_ge_inv, B, ?_⟩
    rcases hB_pure with ⟨hB_in, hcomp⟩ | ⟨hB_in, hanti⟩
    · exact Or.inl ⟨hB_in.mono_width hw_le, hcomp⟩
    · exact Or.inr ⟨hB_in.mono_width hw_le, hanti⟩
  · -- Case (GN4): ε^(10 d)-restricted U ⊆ F' of size ≥ ε^(200 d^2) |F'| -> (R3)
    right; right; left
    obtain ⟨U, hU_sub, hU_card, hU_rest⟩ := hGN4
    have hU_card' : y ^ a₃ * (F'.card : ℝ) ≤ (U.card : ℝ) :=
      (mul_le_mul_of_nonneg_right hya₃_le_ε200 (Nat.cast_nonneg _)).trans hU_card
    have h_rest_y4 : ε ^ (10 * d) ≤ y ^ (4 : ℝ) := by
      dsimp [ε]
      rw [← Real.rpow_mul hy_pos.le]
      exact Real.rpow_le_rpow_of_exponent_ge hy_pos hy_le_one (by nlinarith)
    exact ⟨U, hU_sub, hU_card', hU_rest.mono h_rest_y4⟩

/-! #### Stage 2 Multi-Scale Exponents and Helper Bounds (Step 2 of Proposition 5.4 of `FMBV4-016_readable.tex`) -/

/-- Stage 2 exponent $a_3(d, a) := a (200 d^2 + 2)$. -/
noncomputable def stage2A3 (d a : ℝ) : ℝ := a * (200 * d ^ 2 + 2)

/-- Stage 2 multi-scale exponent $b_2(d, b_{2,\mathrm{init}}, a) := \max(a_3(d, a) + 1, b_{2,\mathrm{init}})$. -/
noncomputable def stage2B2 (d b₂_init a : ℝ) : ℝ := max (stage2A3 d a + 1) b₂_init

/-- Stage 2 dichotomy exponent $C_1(d, b_{2,\mathrm{init}}, a) := 200 b_2 + 200 d^2 + 20$. -/
noncomputable def stage2C1 (d b₂_init a : ℝ) : ℝ := 200 * stage2B2 d b₂_init a + 200 * d ^ 2 + 20

theorem lambda0Param_four_eq : lambda0Param 4 = (2 : ℝ) ^ (-160 : ℝ) := by
  unfold lambda0Param cParam bLeaf
  rw [max_self, ← Real.rpow_mul (by norm_num)]
  norm_num

theorem rpow_160_le_lambda0Param_four {x : ℝ} (hx_pos : 0 < x) (hx_half : x < 1 / 2) :
    x ^ (160 : ℝ) ≤ lambda0Param 4 := by
  rw [lambda0Param_four_eq]
  have h1 : x ^ (160 : ℝ) ≤ (1 / 2 : ℝ) ^ (160 : ℝ) :=
    Real.rpow_le_rpow hx_pos.le hx_half.le (by norm_num)
  have h2 : (1 / 2 : ℝ) ^ (160 : ℝ) = (2 : ℝ) ^ (-160 : ℝ) := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  exact h1.trans_eq h2

/--
Unified cardinality lower bound $|F_t| \ge k^{-177 b_2} |F|$ whenever $k \ge 2$ and
$k^{-17} \le \lambda$.
-/
theorem card_Ft_ge_k_rpow_neg_177_b2 {F F₀ F_t : Finset V} {lam b₂ : ℝ} {k : ℕ}
    (hk2 : 2 ≤ k) (hb₂ : 0 < b₂) (hlam_pos : 0 < lam)
    (hk_lam : (k : ℝ) ^ (-17 : ℝ) ≤ lam)
    (hF₀ : (lambda0Param 4) ^ b₂ * (F.card : ℝ) ≤ (F₀.card : ℝ))
    (hFt : lam ^ b₂ * (F₀.card : ℝ) ≤ (F_t.card : ℝ)) :
    (k : ℝ) ^ (-177 * b₂) * (F.card : ℝ) ≤ (F_t.card : ℝ) := by
  have hk_real : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  have hk_lam0 : (k : ℝ) ^ (-160 : ℝ) ≤ lambda0Param 4 := by
    rw [lambda0Param_four_eq]
    exact rpow_neg_le_two_rpow_neg hk_real (by norm_num)
  have hk_160_b2 : (k : ℝ) ^ (-160 * b₂) ≤ (lambda0Param 4) ^ b₂ := by
    rw [show -160 * b₂ = (-160 : ℝ) * b₂ by ring, Real.rpow_mul hk_pos.le]
    exact Real.rpow_le_rpow (by positivity) hk_lam0 hb₂.le
  have hk_17_b2 : (k : ℝ) ^ (-17 * b₂) ≤ lam ^ b₂ := by
    rw [show -17 * b₂ = (-17 : ℝ) * b₂ by ring, Real.rpow_mul hk_pos.le]
    exact Real.rpow_le_rpow (by positivity) hk_lam hb₂.le
  have h_prod : (k : ℝ) ^ (-177 * b₂) = (k : ℝ) ^ (-17 * b₂) * (k : ℝ) ^ (-160 * b₂) := by
    rw [← Real.rpow_add hk_pos]
    congr 1; ring
  calc (k : ℝ) ^ (-177 * b₂) * (F.card : ℝ)
      = (k : ℝ) ^ (-17 * b₂) * ((k : ℝ) ^ (-160 * b₂) * (F.card : ℝ)) := by
        rw [h_prod, mul_assoc]
    _ ≤ lam ^ b₂ * ((lambda0Param 4) ^ b₂ * (F.card : ℝ)) := by
        refine mul_le_mul hk_17_b2 ?_ (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right hk_160_b2 (Nat.cast_nonneg _)
    _ ≤ lam ^ b₂ * (F₀.card : ℝ) := mul_le_mul_of_nonneg_left hF₀ (by positivity)
    _ ≤ (F_t.card : ℝ) := hFt

/--
Unified derivation of Outcome (iii) `(x ^ C₁ * (F.card : ℝ)) ^ 1 ≤ (kappa G : ℝ)` whenever
$\lambda^e |F_t| \le \kappa(G)$ with $e \ge 0$ and $161 b_2 + e \le C_1$.
-/
theorem outcome3_of_lam_rpow_mul_Ft_le_kappa {G : SimpleGraph V} {F F₀ F_t : Finset V}
    {x lam b₂ e C₁ : ℝ}
    (hx_pos : 0 < x) (hx_half : x < 1 / 2) (hx_lam : x ≤ lam)
    (hb₂ : 0 < b₂) (he : 0 ≤ e) (hC₁ : 161 * b₂ + e ≤ C₁)
    (hF₀ : (lambda0Param 4) ^ b₂ * (F.card : ℝ) ≤ (F₀.card : ℝ))
    (hFt : lam ^ b₂ * (F₀.card : ℝ) ≤ (F_t.card : ℝ))
    (h_le_kappa : lam ^ e * (F_t.card : ℝ) ≤ (kappa G : ℝ)) :
    (x ^ C₁ * (F.card : ℝ)) ^ (1 : ℝ) ≤ (kappa G : ℝ) := by
  rw [Real.rpow_one]
  have hlam_pos : 0 < lam := lt_of_lt_of_le hx_pos hx_lam
  have hx1 : x ≤ 1 := by linarith
  have hx_160_b2 : x ^ (160 * b₂) ≤ (lambda0Param 4) ^ b₂ := by
    rw [Real.rpow_mul hx_pos.le]
    exact Real.rpow_le_rpow (by positivity) (rpow_160_le_lambda0Param_four hx_pos hx_half) hb₂.le
  have hx_b2 : x ^ b₂ ≤ lam ^ b₂ := Real.rpow_le_rpow hx_pos.le hx_lam hb₂.le
  have hx_e : x ^ e ≤ lam ^ e := Real.rpow_le_rpow hx_pos.le hx_lam he
  have hFt_ge : x ^ (161 * b₂) * (F.card : ℝ) ≤ (F_t.card : ℝ) := by
    have h_split : x ^ (161 * b₂) = x ^ b₂ * x ^ (160 * b₂) := by
      rw [← Real.rpow_add hx_pos]
      congr 1; ring
    calc x ^ (161 * b₂) * (F.card : ℝ)
        = x ^ b₂ * (x ^ (160 * b₂) * (F.card : ℝ)) := by rw [h_split, mul_assoc]
      _ ≤ lam ^ b₂ * ((lambda0Param 4) ^ b₂ * (F.card : ℝ)) := by
          refine mul_le_mul hx_b2 ?_ (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right hx_160_b2 (Nat.cast_nonneg _)
      _ ≤ lam ^ b₂ * (F₀.card : ℝ) := mul_le_mul_of_nonneg_left hF₀ (by positivity)
      _ ≤ (F_t.card : ℝ) := hFt
  have hx_C₁ : x ^ C₁ ≤ x ^ e * x ^ (161 * b₂) := by
    rw [← Real.rpow_add hx_pos]
    exact Real.rpow_le_rpow_of_exponent_ge hx_pos hx1 (by linarith)
  calc x ^ C₁ * (F.card : ℝ)
      ≤ (x ^ e * x ^ (161 * b₂)) * (F.card : ℝ) :=
        mul_le_mul_of_nonneg_right hx_C₁ (Nat.cast_nonneg _)
    _ = x ^ e * (x ^ (161 * b₂) * (F.card : ℝ)) := by ring
    _ ≤ lam ^ e * (F_t.card : ℝ) :=
        mul_le_mul hx_e hFt_ge (by positivity) (by positivity)
    _ ≤ (kappa G : ℝ) := h_le_kappa

/--
Helper lemma upgrading the pure $(k, y^{a_3+2}|F_t|)$-blockade from `stage2_step2_r4_to_blockade`
to a pure $(k, |F| / k^{C_1})$-blockade in $F$, with $k : \mathbb{N}$ as a plain variable.
-/
private theorem upgrade_r4_blockade_to_F (G : SimpleGraph V) (F F₀ F_t : Finset V)
    (a₃ b₂ C₁ lam y : ℝ) (k : ℕ)
    (ha₃_ge : 1000 ≤ a₃) (hb₂_pos : 0 < b₂) (hC₁_ge : 177 * b₂ + a₃ + 2 ≤ C₁)
    (hlam_pos : 0 < lam) (hy_pos : 0 < y) (hy_le_144 : y ≤ (2 : ℝ) ^ (-144 : ℝ))
    (hy_def : (2 : ℝ) ^ (-16 : ℝ) * y = lam)
    (hFt_sub_F : F_t ⊆ F)
    (hF₀_card : (lambda0Param 4) ^ b₂ * (F.card : ℝ) ≤ (F₀.card : ℝ))
    (hFt_card : lam ^ b₂ * (F₀.card : ℝ) ≤ (F_t.card : ℝ))
    (hy_inv_k : y⁻¹ ≤ (k : ℝ))
    (B : Fin k → Finset V)
    (hB_pure : IsCompleteBlockadeIn G F_t k (y ^ (a₃ + 2) * (F_t.card : ℝ)) B ∨
      IsAnticompleteBlockadeIn G F_t k (y ^ (a₃ + 2) * (F_t.card : ℝ)) B) :
    ∃ k' : ℕ, 2 ≤ k' ∧ ∃ B' : Fin k' → Finset V,
      IsCompleteBlockadeIn G F k' ((F.card : ℝ) / (k' : ℝ) ^ C₁) B' ∨
      IsAnticompleteBlockadeIn G F k' ((F.card : ℝ) / (k' : ℝ) ^ C₁) B' := by
  have h16_y : (16 : ℝ) ≤ y⁻¹ := by
    have h1 : y ≤ 1 / 16 := by
      have h_exp : (2 : ℝ) ^ (-144 : ℝ) ≤ (2 : ℝ) ^ (-4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      have h_val : (2 : ℝ) ^ (-4 : ℝ) = 1 / 16 := by norm_num
      exact (hy_le_144.trans h_exp).trans_eq h_val
    have h2 : 16 * y ≤ 1 := by linarith
    have h3 := mul_le_mul_of_nonneg_right h2 (inv_nonneg.mpr hy_pos.le)
    rwa [mul_assoc, mul_inv_cancel₀ hy_pos.ne', mul_one, one_mul] at h3
  have hk2 : 2 ≤ k := by
    have : (2 : ℝ) ≤ (k : ℝ) := by linarith
    exact_mod_cast this
  have hk_real : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  have hk_inv_y : (k : ℝ) ^ (-1 : ℝ) ≤ y := by
    rw [Real.rpow_neg_one]
    exact (inv_le_comm₀ hy_pos hk_pos).mp hy_inv_k
  have hk_16 : (k : ℝ) ^ (-16 : ℝ) ≤ (2 : ℝ) ^ (-16 : ℝ) :=
    rpow_neg_le_two_rpow_neg hk_real (by norm_num)
  have hk_lam : (k : ℝ) ^ (-17 : ℝ) ≤ lam := by
    have h1 : (k : ℝ) ^ (-17 : ℝ) = (k : ℝ) ^ (-16 : ℝ) * (k : ℝ) ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hk_pos]
      norm_num
    rw [h1, ← hy_def]
    exact mul_le_mul hk_16 hk_inv_y (by positivity) (by positivity)
  have hFt_k := card_Ft_ge_k_rpow_neg_177_b2 hk2 hb₂_pos hlam_pos hk_lam hF₀_card hFt_card
  have hk_a₃2 : (k : ℝ) ^ (-(a₃ + 2)) ≤ y ^ (a₃ + 2) := by
    rw [show -(a₃ + 2) = (-1 : ℝ) * (a₃ + 2) by ring, Real.rpow_mul hk_pos.le]
    exact Real.rpow_le_rpow (by positivity) hk_inv_y (by linarith)
  have hw_le : (F.card : ℝ) / (k : ℝ) ^ C₁ ≤ y ^ (a₃ + 2) * (F_t.card : ℝ) := by
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hk_pos _)]
    have h1 : (F.card : ℝ) =
        ((k : ℝ) ^ (-(a₃ + 2)) * ((k : ℝ) ^ (-177 * b₂) * (F.card : ℝ))) *
          (k : ℝ) ^ (177 * b₂ + a₃ + 2) := by
      calc (F.card : ℝ)
          = (F.card : ℝ) * ((k : ℝ) ^ (-(a₃ + 2) + (-177 * b₂)) *
              (k : ℝ) ^ (177 * b₂ + a₃ + 2)) := by
            rw [← Real.rpow_add hk_pos]
            have : -(a₃ + 2) + (-177 * b₂) + (177 * b₂ + a₃ + 2) = 0 := by ring
            rw [this, Real.rpow_zero, mul_one]
        _ = ((k : ℝ) ^ (-(a₃ + 2)) * ((k : ℝ) ^ (-177 * b₂) * (F.card : ℝ))) *
              (k : ℝ) ^ (177 * b₂ + a₃ + 2) := by
            rw [Real.rpow_add hk_pos]
            ring
    have h2 : (k : ℝ) ^ (-(a₃ + 2)) * ((k : ℝ) ^ (-177 * b₂) * (F.card : ℝ)) ≤
        y ^ (a₃ + 2) * (F_t.card : ℝ) :=
      mul_le_mul hk_a₃2 hFt_k
        (mul_nonneg (Real.rpow_nonneg hk_pos.le _) (Nat.cast_nonneg _))
        (Real.rpow_nonneg hy_pos.le _)
    have h3 : (k : ℝ) ^ (177 * b₂ + a₃ + 2) ≤ (k : ℝ) ^ C₁ :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hC₁_ge
    rw [h1]
    exact mul_le_mul h2 h3
      (Real.rpow_nonneg hk_pos.le _)
      (mul_nonneg (Real.rpow_nonneg hy_pos.le _) (Nat.cast_nonneg _))
  refine ⟨k, hk2, B, ?_⟩
  rcases hB_pure with ⟨hB_in, hcomp⟩ | ⟨hB_in, hanti⟩
  · exact Or.inl ⟨(hB_in.mono_ambient hFt_sub_F).mono_width hw_le, hcomp⟩
  · exact Or.inr ⟨(hB_in.mono_ambient hFt_sub_F).mono_width hw_le, hanti⟩

/--
Helper lemma upgrading the complete $(k, |F_t| / k^3)$-blockade from
`p6Compl_free_sparse_compl_complete_blockade_cube` to a complete $(k, |F| / k^{C_1})$-blockade in $F$,
with $k : \mathbb{N}$ as a plain variable.
-/
private theorem upgrade_cosp_blockade_to_F (G : SimpleGraph V) (F F₀ F_t : Finset V)
    (b₂ C₁ lam z : ℝ) (k : ℕ)
    (hb₂_pos : 0 < b₂) (hC₁_ge : 177 * b₂ + 3 ≤ C₁)
    (hlam_pos : 0 < lam) (hz_pos : 0 < z) (hz_le_360 : z ≤ 1 / 360) (hz_sq : z ^ 2 = lam)
    (hFt_sub_F : F_t ⊆ F)
    (hF₀_card : (lambda0Param 4) ^ b₂ * (F.card : ℝ) ≤ (F₀.card : ℝ))
    (hFt_card : lam ^ b₂ * (F₀.card : ℝ) ≤ (F_t.card : ℝ))
    (hk_ge_z : 1 / z ≤ (k : ℝ))
    (B : Fin k → Finset V)
    (hB_comp : IsCompleteBlockadeIn G F_t k ((F_t.card : ℝ) / (k : ℝ) ^ (3 : ℝ)) B) :
    ∃ k' : ℕ, 2 ≤ k' ∧ ∃ B' : Fin k' → Finset V,
      IsCompleteBlockadeIn G F k' ((F.card : ℝ) / (k' : ℝ) ^ C₁) B' ∨
      IsAnticompleteBlockadeIn G F k' ((F.card : ℝ) / (k' : ℝ) ^ C₁) B' := by
  have h360_z : 360 ≤ 1 / z := by
    rw [le_div_iff₀ hz_pos]
    linarith
  have hk2 : 2 ≤ k := by
    have : (2 : ℝ) ≤ (k : ℝ) := by linarith
    exact_mod_cast this
  have hk_real : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  have hk_inv_z : (k : ℝ)⁻¹ ≤ z := by
    rw [one_div] at hk_ge_z
    exact (inv_le_comm₀ hz_pos hk_pos).mp hk_ge_z
  have hk_neg2_lam : (k : ℝ) ^ (-2 : ℝ) ≤ lam := by
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hk_pos.le,
      Real.rpow_natCast, ← inv_pow, ← hz_sq]
    exact pow_le_pow_left₀ (by positivity) hk_inv_z 2
  have hk_lam : (k : ℝ) ^ (-17 : ℝ) ≤ lam := by
    have : (k : ℝ) ^ (-17 : ℝ) ≤ (k : ℝ) ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    exact this.trans hk_neg2_lam
  have hFt_k := card_Ft_ge_k_rpow_neg_177_b2 hk2 hb₂_pos hlam_pos hk_lam hF₀_card hFt_card
  have hw_le : (F.card : ℝ) / (k : ℝ) ^ C₁ ≤ (F_t.card : ℝ) / (k : ℝ) ^ (3 : ℝ) := by
    rw [div_le_div_iff₀ (Real.rpow_pos_of_pos hk_pos _) (Real.rpow_pos_of_pos hk_pos _)]
    have h1 : (F.card : ℝ) * (k : ℝ) ^ (3 : ℝ) =
        ((k : ℝ) ^ (-177 * b₂) * (F.card : ℝ)) * (k : ℝ) ^ (177 * b₂ + 3) := by
      calc (F.card : ℝ) * (k : ℝ) ^ (3 : ℝ)
          = (F.card : ℝ) * ((k : ℝ) ^ (-177 * b₂) * (k : ℝ) ^ (177 * b₂ + 3)) := by
            rw [← Real.rpow_add hk_pos]
            congr 2; ring
        _ = ((k : ℝ) ^ (-177 * b₂) * (F.card : ℝ)) * (k : ℝ) ^ (177 * b₂ + 3) := by ring
    have h2 : (k : ℝ) ^ (177 * b₂ + 3) ≤ (k : ℝ) ^ C₁ :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hC₁_ge
    rw [h1]
    exact mul_le_mul hFt_k h2
      (Real.rpow_nonneg hk_pos.le _)
      (Nat.cast_nonneg _)
  exact ⟨k, hk2, B, Or.inl ⟨(hB_comp.1.mono_ambient hFt_sub_F).mono_width hw_le, hB_comp.2⟩⟩

/--
**Stage 2 Single-Scale Step (`stage2_single_scale_step`, Step 2 of Proposition 5.4 of `FMBV4-016_readable.tex`)**:
At scale $\lambda \in [x, \lambda_0]$ on a $\lambda$-restricted $F_t \subseteq F_0 \subseteq F$
with $|F_t| \ge \lambda^{b_2} |F_0|$, either Outcome (ii) or Outcome (iii) of `stage2_reduction`
holds on $F$, or $F_t$ contains a $\lambda^2$-restricted subset $U \subseteq F_t$ with
$|U| \ge \lambda^{a_3 + 1} |F_t|$.
-/
theorem stage2_single_scale_step (G : SimpleGraph V) (F F₀ F_t : Finset V)
    (d b₂_init a x lam : ℝ)
    (hd : 600 ≤ d) (_hb₂_init : 18 ≤ b₂_init) (ha : 7 ≤ a)
    (hG : IsInducedSubgraphFree G P6Compl)
    (hkappa : 1 ≤ kappa G)
    (hx_pos : 0 < x) (hx_half : x < 1 / 2)
    (hF₀_sub : F₀ ⊆ F) (hFt_sub : F_t ⊆ F₀)
    (hlam_mem : lam ∈ Set.Icc x (lambda0Param 4))
    (hF₀_card : (lambda0Param 4) ^ (stage2B2 d b₂_init a) * (F.card : ℝ) ≤ (F₀.card : ℝ))
    (hFt_rest : IsEpsRestrictedOn G F_t lam)
    (hFt_card : lam ^ (stage2B2 d b₂_init a) * (F₀.card : ℝ) ≤ (F_t.card : ℝ))
    (h_wonderful : HasWonderfulAnticonnectedBlockade G a)
    (h_gen_nice : ∀ (S : Finset V) {ε : ℝ}, 0 < ε → ε < 1 / 2 →
      SatisfiesGenNiceAt G S ε (200 * d ^ 2) d (200 * d ^ 2) 1 (d + 1) (20 * d) (10 * d) (200 * d ^ 2)) :
    let a₃ := stage2A3 d a
    let C₁ := stage2C1 d b₂_init a
    ((∃ k : ℕ, 2 ≤ k ∧ ∃ B : Fin k → Finset V,
        IsCompleteBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ C₁) B ∨
        IsAnticompleteBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ C₁) B) ∨
      (x ^ C₁ * (F.card : ℝ)) ^ (1 : ℝ) ≤ (kappa G : ℝ)) ∨
    (∃ U ⊆ F_t, IsEpsRestrictedOn G U (lam ^ (2 : ℝ)) ∧
      lam ^ (a₃ + 1) * (F_t.card : ℝ) ≤ (U.card : ℝ)) := by
  set a₃ := stage2A3 d a
  set b₂ := stage2B2 d b₂_init a
  set C₁ := stage2C1 d b₂_init a
  have hd2_nonneg : 0 ≤ d ^ 2 := sq_nonneg d
  have ha₃_ge : 1000 ≤ a₃ := by
    unfold a₃ stage2A3
    nlinarith
  have hb₂_ge_a₃ : a₃ + 1 ≤ b₂ := le_max_left _ _
  have hb₂_pos : 0 < b₂ := by linarith
  have hC₁_eq : C₁ = 200 * b₂ + 200 * d ^ 2 + 20 := rfl
  have hlam_ge_x : x ≤ lam := hlam_mem.1
  have hlam_le_lam0 : lam ≤ lambda0Param 4 := hlam_mem.2
  have hlam_pos : 0 < lam := lt_of_lt_of_le hx_pos hlam_ge_x
  have hlam_le_160 : lam ≤ (2 : ℝ) ^ (-160 : ℝ) := by
    rwa [← lambda0Param_four_eq]
  have hlam_le_one : lam ≤ 1 := by
    have : (2 : ℝ) ^ (-160 : ℝ) ≤ (2 : ℝ) ^ (0 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    linarith [Real.rpow_zero (2 : ℝ)]
  have hkappa_real : (1 : ℝ) ≤ (kappa G : ℝ) := by exact_mod_cast hkappa
  have hFt_sub_F : F_t ⊆ F := hFt_sub.trans hF₀_sub
  rcases hFt_rest with hFt_sp | hFt_cosp
  · -- Branch 1: G[F_t] is lam-sparse
    set y := (2 : ℝ) ^ (16 : ℝ) * lam
    have hy_pos : 0 < y := by positivity
    have hy_le_144 : y ≤ (2 : ℝ) ^ (-144 : ℝ) := by
      calc y = (2 : ℝ) ^ (16 : ℝ) * lam := rfl
        _ ≤ (2 : ℝ) ^ (16 : ℝ) * (2 : ℝ) ^ (-160 : ℝ) :=
            mul_le_mul_of_nonneg_left hlam_le_160 (by positivity)
        _ = (2 : ℝ) ^ (-144 : ℝ) := by
            rw [← Real.rpow_add (by norm_num)]
            norm_num
    have hy_le_16 : y ≤ (2 : ℝ) ^ (-4 * (4 : ℝ)) :=
      hy_le_144.trans (by norm_num)
    have hlam_le_y : lam ≤ y := by
      have : (1 : ℝ) ≤ (2 : ℝ) ^ (16 : ℝ) := by norm_num
      calc lam = 1 * lam := (one_mul lam).symm
        _ ≤ (2 : ℝ) ^ (16 : ℝ) * lam := mul_le_mul_of_nonneg_right this hlam_pos.le
    by_cases hw₀ : 1 ≤ y ^ (a₃ + 2) * (F_t.card : ℝ)
    · -- Subcase 1.1: y^(a₃ + 2) |F_t| ≥ 1, apply stage2_step2_r4_to_blockade
      let P_R123 : Finset V → Prop := fun F' =>
        (y ^ a₃ * (F'.card : ℝ) ≤ (kappa G : ℝ)) ∨
        (∃ k : ℕ, 2 ≤ k ∧ y⁻¹ ≤ (k : ℝ) ∧ ∃ B : Fin k → Finset V,
          IsCompleteBlockadeIn G F' k ((F'.card : ℝ) / (k : ℝ) ^ (200 * d ^ 2 + 4)) B ∨
          IsAnticompleteBlockadeIn G F' k ((F'.card : ℝ) / (k : ℝ) ^ (200 * d ^ 2 + 4)) B) ∨
        (∃ U ⊆ F', y ^ a₃ * (F'.card : ℝ) ≤ (U.card : ℝ) ∧ IsEpsRestrictedOn G U (y ^ (4 : ℝ)))
      have hstep1 : ∀ F' ⊆ F_t, (2 : ℝ) ^ (-4 * (4 : ℝ)) * (F_t.card : ℝ) ≤ (F'.card : ℝ) →
          P_R123 F' ∨
          (∃ X ⊆ F', ∃ Y ⊆ F', Disjoint X Y ∧
            y ^ a₃ * (F'.card : ℝ) ≤ (X.card : ℝ) ∧
            (1 - 4 * y) * (F'.card : ℝ) ≤ (Y.card : ℝ) ∧
            IsPurePair G X Y) := by
        intro F' hF'_sub hF'_card
        have hF'_sp : IsEpsSparseOn G F' y := by
          intro v hv
          have hsub_n : neighborFinsetIn G v F' ⊆ neighborFinsetIn G v F_t :=
            neighborFinsetIn_mono G v hF'_sub
          have hdeg_le : ((neighborFinsetIn G v F').card : ℝ) ≤
              ((neighborFinsetIn G v F_t).card : ℝ) := by
            exact_mod_cast card_le_card hsub_n
          have h16_inv : (2 : ℝ) ^ (16 : ℝ) * (2 : ℝ) ^ (-4 * (4 : ℝ)) = 1 := by
            rw [← Real.rpow_add (by norm_num)]
            norm_num
          calc ((neighborFinsetIn G v F').card : ℝ)
              ≤ ((neighborFinsetIn G v F_t).card : ℝ) := hdeg_le
            _ ≤ lam * (F_t.card : ℝ) := hFt_sp v (hF'_sub hv)
            _ = ((2 : ℝ) ^ (16 : ℝ) * lam) * ((2 : ℝ) ^ (-4 * (4 : ℝ)) * (F_t.card : ℝ)) := by
                calc lam * (F_t.card : ℝ)
                    = ((2 : ℝ) ^ (16 : ℝ) * (2 : ℝ) ^ (-4 * (4 : ℝ))) * lam * (F_t.card : ℝ) := by
                      rw [h16_inv, one_mul]
                  _ = ((2 : ℝ) ^ (16 : ℝ) * lam) * ((2 : ℝ) ^ (-4 * (4 : ℝ)) * (F_t.card : ℝ)) := by ring
            _ ≤ y * (F'.card : ℝ) := mul_le_mul_of_nonneg_left hF'_card hy_pos.le
        rcases stage2_step1_dichotomy G F' d a y hd ha hy_pos hy_le_144 hkappa hF'_sp h_wonderful
            (fun hε hε_half => h_gen_nice F' hε hε_half) with
          hR1 | hR2 | hR3 | hR4
        · exact Or.inl (Or.inl hR1)
        · exact Or.inl (Or.inr (Or.inl hR2))
        · exact Or.inl (Or.inr (Or.inr hR3))
        · exact Or.inr hR4
      rcases stage2_step2_r4_to_blockade G F_t a₃ 4 y (by linarith) (by norm_num) hy_pos hy_le_16
          hw₀ P_R123 hstep1 with
        ⟨F', hF'_sub, hF'_card, hP⟩ | ⟨B, hB_pure⟩
      · rcases hP with hR1 | ⟨k, hk2, hy_inv_k, B, hB_k⟩ | ⟨U, hU_sub, hU_card, hU_rest⟩
        · -- (R1) -> Outcome (iii)
          left; right
          have hlam_16 : lam ≤ (2 : ℝ) ^ (-4 * (4 : ℝ)) := by
            have : (2 : ℝ) ^ (-160 : ℝ) ≤ (2 : ℝ) ^ (-4 * (4 : ℝ)) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            exact hlam_le_160.trans this
          have hlam_F' : lam * (F_t.card : ℝ) ≤ (F'.card : ℝ) :=
            (mul_le_mul_of_nonneg_right hlam_16 (Nat.cast_nonneg _)).trans hF'_card
          have hlam_a₃ : lam ^ a₃ ≤ y ^ a₃ := Real.rpow_le_rpow hlam_pos.le hlam_le_y (by linarith)
          have h_le_kappa : lam ^ (a₃ + 1) * (F_t.card : ℝ) ≤ (kappa G : ℝ) := by
            calc lam ^ (a₃ + 1) * (F_t.card : ℝ)
                = lam ^ a₃ * (lam * (F_t.card : ℝ)) := by
                  rw [Real.rpow_add_one hlam_pos.ne', mul_assoc]
              _ ≤ y ^ a₃ * (F'.card : ℝ) :=
                  mul_le_mul hlam_a₃ hlam_F' (by positivity) (by positivity)
              _ ≤ (kappa G : ℝ) := hR1
          exact outcome3_of_lam_rpow_mul_Ft_le_kappa hx_pos hx_half hlam_ge_x hb₂_pos
            (by linarith) (by linarith) hF₀_card hFt_card h_le_kappa
        · -- (R2) -> Outcome (ii)
          left; left
          have hk_real : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
          have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
          have hk_inv_y : (k : ℝ) ^ (-1 : ℝ) ≤ y := by
            rw [Real.rpow_neg_one]
            exact (inv_le_comm₀ hy_pos hk_pos).mp hy_inv_k
          have hk_16 : (k : ℝ) ^ (-16 : ℝ) ≤ (2 : ℝ) ^ (-16 : ℝ) :=
            rpow_neg_le_two_rpow_neg hk_real (by norm_num)
          have hk_lam : (k : ℝ) ^ (-17 : ℝ) ≤ lam := by
            have h1 : (k : ℝ) ^ (-17 : ℝ) = (k : ℝ) ^ (-16 : ℝ) * (k : ℝ) ^ (-1 : ℝ) := by
              rw [← Real.rpow_add hk_pos]
              norm_num
            have h2 : (2 : ℝ) ^ (-16 : ℝ) * y = lam := by
              dsimp [y]
              rw [← mul_assoc, ← Real.rpow_add (by norm_num)]
              norm_num
            rw [h1, ← h2]
            exact mul_le_mul hk_16 hk_inv_y (by positivity) (by positivity)
          have hFt_k := card_Ft_ge_k_rpow_neg_177_b2 hk2 hb₂_pos hlam_pos hk_lam hF₀_card hFt_card
          have hF'_k : (k : ℝ) ^ (-177 * b₂ - 16) * (F.card : ℝ) ≤ (F'.card : ℝ) := by
            have h_split : (k : ℝ) ^ (-177 * b₂ - 16) =
                (k : ℝ) ^ (-16 : ℝ) * (k : ℝ) ^ (-177 * b₂) := by
              rw [← Real.rpow_add hk_pos]
              congr 1; ring
            have h16_eq : (2 : ℝ) ^ (-16 : ℝ) = (2 : ℝ) ^ (-4 * (4 : ℝ)) := by norm_num
            calc (k : ℝ) ^ (-177 * b₂ - 16) * (F.card : ℝ)
                = (k : ℝ) ^ (-16 : ℝ) * ((k : ℝ) ^ (-177 * b₂) * (F.card : ℝ)) := by
                  rw [h_split, mul_assoc]
              _ ≤ (2 : ℝ) ^ (-4 * (4 : ℝ)) * (F_t.card : ℝ) := by
                  rw [← h16_eq]
                  exact mul_le_mul hk_16 hFt_k (by positivity) (by positivity)
              _ ≤ (F'.card : ℝ) := hF'_card
          have hw_le : (F.card : ℝ) / (k : ℝ) ^ C₁ ≤
              (F'.card : ℝ) / (k : ℝ) ^ (200 * d ^ 2 + 4) := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            have h1 : (F.card : ℝ) * (k : ℝ) ^ (200 * d ^ 2 + 4) =
                ((k : ℝ) ^ (-177 * b₂ - 16) * (F.card : ℝ)) *
                  (k : ℝ) ^ (177 * b₂ + 200 * d ^ 2 + 20) := by
              calc (F.card : ℝ) * (k : ℝ) ^ (200 * d ^ 2 + 4)
                  = (F.card : ℝ) * ((k : ℝ) ^ (-177 * b₂ - 16) *
                      (k : ℝ) ^ (177 * b₂ + 200 * d ^ 2 + 20)) := by
                    rw [← Real.rpow_add hk_pos]
                    congr 2; ring
                _ = ((k : ℝ) ^ (-177 * b₂ - 16) * (F.card : ℝ)) *
                      (k : ℝ) ^ (177 * b₂ + 200 * d ^ 2 + 20) := by ring
            have h2 : (k : ℝ) ^ (177 * b₂ + 200 * d ^ 2 + 20) ≤ (k : ℝ) ^ C₁ :=
              Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
            rw [h1]
            exact mul_le_mul hF'_k h2 (by positivity) (by positivity)
          refine ⟨k, hk2, B, ?_⟩
          rcases hB_k with ⟨hB_in, hcomp⟩ | ⟨hB_in, hanti⟩
          · exact Or.inl ⟨(hB_in.mono_ambient (hF'_sub.trans hFt_sub_F)).mono_width hw_le, hcomp⟩
          · exact Or.inr ⟨(hB_in.mono_ambient (hF'_sub.trans hFt_sub_F)).mono_width hw_le, hanti⟩
        · -- (R3) -> Advance multi-scale iteration with U ⊆ F' ⊆ F_t
          right
          have hy4_le_lam2 : y ^ (4 : ℝ) ≤ lam ^ (2 : ℝ) := by
            dsimp [y]
            rw [Real.mul_rpow (by positivity) hlam_pos.le, ← Real.rpow_mul (by norm_num)]
            have h_lam4 : lam ^ (4 : ℝ) = lam ^ (2 : ℝ) * lam ^ (2 : ℝ) := by
              rw [← Real.rpow_add hlam_pos]
              norm_num
            have h_small : (2 : ℝ) ^ (16 * (4 : ℝ)) * lam ^ (2 : ℝ) ≤ 1 := by
              have h1 : lam ^ (2 : ℝ) ≤ ((2 : ℝ) ^ (-160 : ℝ)) ^ (2 : ℝ) :=
                Real.rpow_le_rpow hlam_pos.le hlam_le_160 (by norm_num)
              have h2 : (2 : ℝ) ^ (16 * (4 : ℝ)) * ((2 : ℝ) ^ (-160 : ℝ)) ^ (2 : ℝ) =
                  (2 : ℝ) ^ (-256 : ℝ) := by
                rw [← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
                norm_num
              have h3 : (2 : ℝ) ^ (-256 : ℝ) ≤ (2 : ℝ) ^ (0 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              have h4 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (16 * (4 : ℝ)))
              linarith [Real.rpow_zero (2 : ℝ)]
            rw [h_lam4, ← mul_assoc]
            calc ((2 : ℝ) ^ (16 * (4 : ℝ)) * lam ^ (2 : ℝ)) * lam ^ (2 : ℝ)
                ≤ 1 * lam ^ (2 : ℝ) := mul_le_mul_of_nonneg_right h_small (by positivity)
              _ = lam ^ (2 : ℝ) := one_mul _
          have hlam_16 : lam ≤ (2 : ℝ) ^ (-4 * (4 : ℝ)) := by
            have : (2 : ℝ) ^ (-160 : ℝ) ≤ (2 : ℝ) ^ (-4 * (4 : ℝ)) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            exact hlam_le_160.trans this
          have hlam_F' : lam * (F_t.card : ℝ) ≤ (F'.card : ℝ) :=
            (mul_le_mul_of_nonneg_right hlam_16 (Nat.cast_nonneg _)).trans hF'_card
          have hlam_a₃ : lam ^ a₃ ≤ y ^ a₃ := Real.rpow_le_rpow hlam_pos.le hlam_le_y (by linarith)
          have hU_card' : lam ^ (a₃ + 1) * (F_t.card : ℝ) ≤ (U.card : ℝ) := by
            calc lam ^ (a₃ + 1) * (F_t.card : ℝ)
                = lam ^ a₃ * (lam * (F_t.card : ℝ)) := by
                  rw [Real.rpow_add_one hlam_pos.ne', mul_assoc]
              _ ≤ y ^ a₃ * (F'.card : ℝ) :=
                  mul_le_mul hlam_a₃ hlam_F' (by positivity) (by positivity)
              _ ≤ (U.card : ℝ) := hU_card
          exact ⟨U, hU_sub.trans hF'_sub, hU_rest.mono hy4_le_lam2, hU_card'⟩
      · -- Blockade from stage2_step2_r4_to_blockade -> Outcome (ii)
        left; left
        have hy_def : (2 : ℝ) ^ (-16 : ℝ) * y = lam := by
          dsimp [y]
          rw [← mul_assoc, ← Real.rpow_add (by norm_num)]
          norm_num
        exact upgrade_r4_blockade_to_F G F F₀ F_t a₃ b₂ C₁ lam y ⌈y⁻¹⌉₊
          ha₃_ge hb₂_pos (by linarith) hlam_pos hy_pos hy_le_144 hy_def
          hFt_sub_F hF₀_card hFt_card (Nat.le_ceil _) B hB_pure
    · -- Subcase 1.2: y^(a₃ + 2) |F_t| < 1 -> Outcome (iii)
      left; right
      push_neg at hw₀
      have hlam_a₃2 : lam ^ (a₃ + 2) ≤ y ^ (a₃ + 2) :=
        Real.rpow_le_rpow hlam_pos.le hlam_le_y (by linarith)
      have h_le_kappa : lam ^ (a₃ + 2) * (F_t.card : ℝ) ≤ (kappa G : ℝ) :=
        ((mul_le_mul_of_nonneg_right hlam_a₃2 (Nat.cast_nonneg _)).trans hw₀.le).trans hkappa_real
      exact outcome3_of_lam_rpow_mul_Ft_le_kappa hx_pos hx_half hlam_ge_x hb₂_pos
        (by linarith) (by linarith) hF₀_card hFt_card h_le_kappa
  · -- Branch 2: Gᶜ[F_t] is lam-sparse
    set z := lam ^ (1 / 2 : ℝ)
    have hz_pos : 0 < z := Real.rpow_pos_of_pos hlam_pos (1 / 2)
    have hz_sq : z ^ 2 = lam := by
      dsimp [z]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hlam_pos.le]
      norm_num
    have hz_le_360 : z ≤ 1 / 360 := by
      have h1 : z ≤ ((2 : ℝ) ^ (-160 : ℝ)) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow hlam_pos.le hlam_le_160 (by positivity)
      have h2 : ((2 : ℝ) ^ (-160 : ℝ)) ^ (1 / 2 : ℝ) = (2 : ℝ) ^ (-80 : ℝ) := by
        rw [← Real.rpow_mul (by norm_num)]
        norm_num
      have h3 : (2 : ℝ) ^ (-80 : ℝ) ≤ (2 : ℝ) ^ (-9 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      have h4 : (2 : ℝ) ^ (-9 : ℝ) ≤ 1 / 360 := by norm_num
      exact (h1.trans_eq h2).trans (h3.trans h4)
    by_cases hFt_z : 1 / z ^ 2 ≤ (F_t.card : ℝ)
    · -- Subcase 2.1: |F_t| ≥ 1 / z^2 -> p6Compl_free_sparse_compl_complete_blockade_cube -> Outcome (ii)
      left; left
      have hFt_cosp_z : IsEpsSparseOn Gᶜ F_t (z ^ 2) := by rwa [hz_sq]
      obtain ⟨B, hB_comp⟩ := p6Compl_free_sparse_compl_complete_blockade_cube G F_t z
        hG hz_pos hz_le_360 hFt_z hFt_cosp_z
      exact upgrade_cosp_blockade_to_F G F F₀ F_t b₂ C₁ lam z ⌈1 / z⌉₊
        hb₂_pos (by linarith) hlam_pos hz_pos hz_le_360 hz_sq
        hFt_sub_F hF₀_card hFt_card (Nat.le_ceil _) B hB_comp
    · -- Subcase 2.2: |F_t| < 1 / z^2 = lam⁻¹ -> Outcome (iii)
      left; right
      push_neg at hFt_z
      rw [hz_sq] at hFt_z
      have h_le_kappa : lam ^ (1 : ℝ) * (F_t.card : ℝ) ≤ (kappa G : ℝ) := by
        rw [Real.rpow_one]
        have h1 : lam * (F_t.card : ℝ) ≤ lam * (1 / lam) :=
          mul_le_mul_of_nonneg_left hFt_z.le hlam_pos.le
        rw [mul_one_div_cancel hlam_pos.ne'] at h1
        exact h1.trans hkappa_real
      exact outcome3_of_lam_rpow_mul_Ft_le_kappa hx_pos hx_half hlam_ge_x hb₂_pos
        (by norm_num) (by linarith) hF₀_card hFt_card h_le_kappa

/--
**Stage 2 Multi-Scale Dichotomy (`stage2_for_wonderful_P6Compl`, Proposition 5.4 of `FMBV4-016_readable.tex`)**:
For any $\overline{P_6}$-free graph $G$ satisfying `HasWonderfulAnticonnectedBlockade G a` ($a \ge 7$),
Rödl's initial step with exponent $b_{2,\mathrm{init}} \ge 18$, and Generalized Niceness with parameter
$d \ge 600$, every $S_0 \subseteq V$, every $x \in (0, 1/2)$, and every $F \subseteq S_0$ satisfies the
`h_multiscale` dichotomy of `stage2_reduction G S₀ (stage2C1 d b₂_init a) 1`.
-/
theorem stage2_for_wonderful_P6Compl (G : SimpleGraph V) (S₀ : Finset V)
    (d b₂_init a : ℝ) (hd : 600 ≤ d) (hb₂_init : 18 ≤ b₂_init) (ha : 7 ≤ a)
    (hG : IsInducedSubgraphFree G P6Compl)
    (hkappa : 1 ≤ kappa G)
    (h_wonderful : HasWonderfulAnticonnectedBlockade G a)
    (h_rodl : ∀ (F : Finset V), ∃ F₀ ⊆ F, IsEpsRestrictedOn G F₀ (lambda0Param 4) ∧
      (lambda0Param 4) ^ b₂_init * (F.card : ℝ) ≤ (F₀.card : ℝ))
    (h_gen_nice : ∀ (S : Finset V) {ε : ℝ}, 0 < ε → ε < 1 / 2 →
      SatisfiesGenNiceAt G S ε (200 * d ^ 2) d (200 * d ^ 2) 1 (d + 1) (20 * d) (10 * d) (200 * d ^ 2)) :
    ∀ x : ℝ, 0 < x → x < 1 / 2 → ∀ F ⊆ S₀,
      (∃ S ⊆ F, IsEpsRestrictedOn G S x ∧ x ^ (stage2C1 d b₂_init a) * (F.card : ℝ) ≤ (S.card : ℝ)) ∨
      (∃ k : ℕ, 2 ≤ k ∧ ∃ B : Fin k → Finset V,
        IsCompleteBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ (stage2C1 d b₂_init a)) B ∨
        IsAnticompleteBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ (stage2C1 d b₂_init a)) B) ∨
      (x ^ (stage2C1 d b₂_init a) * (F.card : ℝ)) ^ (1 : ℝ) ≤ (kappa G : ℝ) := by
  set a₃ := stage2A3 d a
  set b₂ := stage2B2 d b₂_init a
  set C₁ := stage2C1 d b₂_init a
  have hd2_nonneg : 0 ≤ d ^ 2 := sq_nonneg d
  have hC₁_eq : C₁ = 200 * b₂ + 200 * d ^ 2 + 20 := rfl
  have ha₃_ge : 1000 ≤ a₃ := by
    unfold a₃ stage2A3
    nlinarith
  have hb₂_ge_a₃ : a₃ + 1 ≤ b₂ := le_max_left _ _
  have hb₂_ge_init : b₂_init ≤ b₂ := le_max_right _ _
  have hb₂_pos : 0 < b₂ := by linarith
  have hlam0_pos : 0 < lambda0Param 4 := lambda0Param_pos 4
  have hlam0_half : lambda0Param 4 < 1 / 2 := lambda0Param_lt_half 4
  intro x hx_pos hx_half F _hFS₀
  have hx1 : x ≤ 1 := by linarith
  obtain ⟨F₀, hF₀_sub, hF₀_rest, hF₀_card_init⟩ := h_rodl F
  have hF₀_card : (lambda0Param 4) ^ b₂ * (F.card : ℝ) ≤ (F₀.card : ℝ) := by
    have h_le : (lambda0Param 4) ^ b₂ ≤ (lambda0Param 4) ^ b₂_init :=
      Real.rpow_le_rpow_of_exponent_ge hlam0_pos (by linarith) hb₂_ge_init
    exact (mul_le_mul_of_nonneg_right h_le (Nat.cast_nonneg _)).trans hF₀_card_init
  have hx_160_b2 : x ^ (160 * b₂) ≤ (lambda0Param 4) ^ b₂ := by
    rw [Real.rpow_mul hx_pos.le]
    exact Real.rpow_le_rpow (by positivity) (rpow_160_le_lambda0Param_four hx_pos hx_half) hb₂_pos.le
  by_cases hx_lt : x < lambda0Param 4
  · -- Multi-scale iteration from lambda0Param 4 down to x
    let O : Finset V → Prop := fun _ =>
      (∃ k : ℕ, 2 ≤ k ∧ ∃ B : Fin k → Finset V,
        IsCompleteBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ C₁) B ∨
        IsAnticompleteBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ C₁) B) ∨
      (x ^ C₁ * (F.card : ℝ)) ^ (1 : ℝ) ≤ (kappa G : ℝ)
    have hstep : ∀ lam ∈ Set.Icc x (lambda0Param 4), ∀ F_t ⊆ F₀,
        IsEpsRestrictedOn G F_t lam → lam ^ b₂ * (F₀.card : ℝ) ≤ (F_t.card : ℝ) →
          O F_t ∨ ∃ U ⊆ F_t, IsEpsRestrictedOn G U (lam ^ (2 : ℝ)) ∧
            lam ^ (a₃ + 1) * (F_t.card : ℝ) ≤ (U.card : ℝ) :=
      fun lam hlam_mem F_t hFt_sub hFt_rest hFt_card =>
        stage2_single_scale_step G F F₀ F_t d b₂_init a x lam hd hb₂_init ha hG hkappa
          hx_pos hx_half hF₀_sub hFt_sub hlam_mem hF₀_card hFt_rest hFt_card h_wonderful h_gen_nice
    rcases lem_multiscale_sparsification G F₀ O hlam0_pos hlam0_half hx_pos hx_lt
        (by norm_num : (1 : ℝ) < 2) hb₂_pos (by linarith : 0 < a₃ + 1)
        (by linarith : (2 - 1) * b₂ ≥ a₃ + 1) hF₀_rest hstep with
      ⟨_F_t, _, hO⟩ | ⟨S, hS_sub, hS_rest, hS_card⟩
    · exact Or.inr hO
    · left
      refine ⟨S, hS_sub.trans hF₀_sub, hS_rest, ?_⟩
      have hx_C₁ : x ^ C₁ ≤ x ^ ((2 : ℝ) * b₂) * x ^ (160 * b₂) := by
        rw [← Real.rpow_add hx_pos]
        exact Real.rpow_le_rpow_of_exponent_ge hx_pos hx1 (by linarith)
      calc x ^ C₁ * (F.card : ℝ)
          ≤ (x ^ ((2 : ℝ) * b₂) * x ^ (160 * b₂)) * (F.card : ℝ) :=
            mul_le_mul_of_nonneg_right hx_C₁ (Nat.cast_nonneg _)
        _ = x ^ ((2 : ℝ) * b₂) * (x ^ (160 * b₂) * (F.card : ℝ)) := by ring
        _ ≤ x ^ ((2 : ℝ) * b₂) * ((lambda0Param 4) ^ b₂ * (F.card : ℝ)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul_of_nonneg_right hx_160_b2 (Nat.cast_nonneg _)
        _ ≤ x ^ ((2 : ℝ) * b₂) * (F₀.card : ℝ) :=
            mul_le_mul_of_nonneg_left hF₀_card (by positivity)
        _ ≤ (S.card : ℝ) := hS_card
  · -- x ≥ lambda0Param 4: F₀ itself is already x-restricted of size ≥ x^C₁ |F|
    push_neg at hx_lt
    left
    refine ⟨F₀, hF₀_sub, hF₀_rest.mono hx_lt, ?_⟩
    have hx_C₁ : x ^ C₁ ≤ x ^ (160 * b₂) :=
      Real.rpow_le_rpow_of_exponent_ge hx_pos hx1 (by linarith)
    calc x ^ C₁ * (F.card : ℝ)
        ≤ x ^ (160 * b₂) * (F.card : ℝ) :=
          mul_le_mul_of_nonneg_right hx_C₁ (Nat.cast_nonneg _)
      _ ≤ (lambda0Param 4) ^ b₂ * (F.card : ℝ) :=
          mul_le_mul_of_nonneg_right hx_160_b2 (Nat.cast_nonneg _)
      _ ≤ (F₀.card : ℝ) := hF₀_card

/--
**Master Erdős–Hajnal Synthesis (`hasErdosHajnalProp_of_wonderful_P6Compl`)**:
Any finite graph $H$ whose $H$-free graphs are $\overline{P_6}$-free and satisfy
`HasWonderfulAnticonnectedBlockade G a` for some $a \ge 7$ satisfies `HasErdosHajnalProp H`.
-/
theorem hasErdosHajnalProp_of_wonderful_P6Compl {α : Type*} [Fintype α] [DecidableEq α]
    (H : SimpleGraph α) (a : ℝ) (ha : 7 ≤ a)
    (h_class : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), IsInducedSubgraphFree G H →
      IsInducedSubgraphFree G P6Compl ∧ HasWonderfulAnticonnectedBlockade G a) :
    HasErdosHajnalProp H := by
  let δ := rodlDelta (lambda0Param 4)
  let d := dParam (3 / 4) 4 δ
  let b₂_init := b2Param (3 / 4) 4 δ
  have hd : 600 ≤ d := six_hundred_le_dParam (3 / 4) 4 δ
  have hb₂_init : 18 ≤ b₂_init := by
    have h1 := four_le_cLeaf (3 / 4)
    have h2 := b2Param_ge_three_cLeaf (3 / 4) 4 δ
    dsimp [b₂_init]
    linarith
  let C₁ := stage2C1 d b₂_init a
  have hC₁ : 1 ≤ C₁ := by
    unfold C₁ stage2C1 stage2B2 stage2A3
    have : 0 ≤ max (a * (200 * d ^ 2 + 2) + 1) b₂_init := le_trans (by linarith) (le_max_right _ _)
    nlinarith
  let q := 42 * C₁ ^ 2
  let c₀ := min (q⁻¹) ((1 : ℝ) / 2)
  have hc₀_pos : 0 < c₀ := by
    dsimp [c₀, q]
    exact lt_min (by positivity) (by norm_num)
  let N₀ := max 2 ⌈(2 : ℝ) ^ q⌉₊
  have hN₀ : 2 ≤ N₀ := le_max_left 2 ⌈(2 : ℝ) ^ q⌉₊
  refine hasErdosHajnalProp_of_large_n H hN₀ hc₀_pos ?_
  intro n hn G hG
  obtain ⟨hG6, h_wond⟩ := h_class n G hG
  have hn2 : 2 ≤ n := hN₀.trans hn
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hkappa : 1 ≤ kappa G := kappa_pos_of_nonempty G
  let S₀ : Finset (Fin n) := Finset.univ
  have hS₀_card : (S₀.card : ℝ) = (n : ℝ) := by simp [S₀]
  have hS₀_ge : (2 : ℝ) ^ q ≤ (S₀.card : ℝ) := by
    rw [hS₀_card]
    have h1 : (2 : ℝ) ^ q ≤ (⌈(2 : ℝ) ^ q⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈(2 : ℝ) ^ q⌉₊ : ℝ) ≤ (N₀ : ℝ) := by
      exact_mod_cast le_max_right 2 ⌈(2 : ℝ) ^ q⌉₊
    have h3 : (N₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact h1.trans (h2.trans h3)
  have h_multi := stage2_for_wonderful_P6Compl G S₀ d b₂_init a hd hb₂_init ha hG6 hkappa h_wond
    (fun F => rodl_initial_step_for_gen_nice G F (3 / 4) 4 hG6)
    (fun S _ hε hε_half => gen_nice_P6_unconditional G S hG6 hε hε_half hkappa)
  have h_red := stage2_reduction G S₀ C₁ 1 hC₁ zero_lt_one h_multi hS₀_ge
  rwa [hS₀_card] at h_red

/--
**Theorem (`hasErdosHajnalProp_P5Compl`)**:
$\overline{P_5}$ satisfies the Erdős–Hajnal property.
-/
theorem hasErdosHajnalProp_P5Compl : HasErdosHajnalProp P5Compl :=
  hasErdosHajnalProp_of_wonderful_P6Compl P5Compl 7 le_rfl (fun _ G hG =>
    ⟨isP6ComplFree_of_isP5ComplFree G hG, hasWonderfulAnticonnectedBlockade_of_isP5ComplFree G hG⟩)

/--
**Theorem (`hasErdosHajnalProp_P5`)**:
$P_5$ satisfies the Erdős–Hajnal property (Chudnovsky–Scott–Seymour–Spirkl 2023).
-/
theorem hasErdosHajnalProp_P5 : HasErdosHajnalProp P5 := by
  have h := hasErdosHajnalProp_P5Compl.compl
  rwa [P5Compl, compl_compl] at h

/--
**Theorem (`hasErdosHajnalProp_witnessH`, Proposition 3.2(1) of `FMBV4-016_readable.tex`)**:
The 7-vertex substitution witness graph `witnessH` satisfies the Erdős–Hajnal property.
-/
theorem hasErdosHajnalProp_witnessH : HasErdosHajnalProp witnessH :=
  witnessH_hasErdosHajnalProp hasErdosHajnalProp_P5

/--
**Theorem (`hasErdosHajnalProp_P6Compl`)**:
$\overline{P_6}$ satisfies the Erdős–Hajnal property.
-/
theorem hasErdosHajnalProp_P6Compl : HasErdosHajnalProp P6Compl := by
  obtain ⟨c_H, hc_H, h_eh⟩ := hasErdosHajnalProp_witnessH
  exact hasErdosHajnalProp_of_wonderful_P6Compl P6Compl (max 7 (5 / c_H + 1)) (le_max_left _ _)
    (fun _ G hG => ⟨hG, hasWonderfulAnticonnectedBlockade_of_witnessH_eh G hG hc_H h_eh⟩)

/--
**Theorem 1.1 (`hasErdosHajnalProp_P6`, `thm:main`, Main Theorem of `FMBV4-016_readable.tex`)**:
$P_6$ satisfies the Erdős–Hajnal property.
-/
theorem hasErdosHajnalProp_P6 : HasErdosHajnalProp P6 := by
  have h := hasErdosHajnalProp_P6Compl.compl
  rwa [P6Compl, compl_compl] at h

/--
Universal Packaging of the $P_6$ Erdős–Hajnal Theorem across all three formulations of `Problem.lean`.
-/
theorem erdos_hajnal_p6_all_variants :
    ∃ c > (0 : ℝ),
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)),
        (¬∃ g : Fin 6 ↪ Fin n, pathGraph 6 = G.comap g) →
          (G.cliqueNum : ℝ) ≥ (n : ℝ) ^ c ∨ (G.indepNum : ℝ) ≥ (n : ℝ) ^ c) ∧
      _root_.Erdos61.IsErdosHajnalLowerBound (pathGraph 6) (fun n : ℕ => (n : ℝ) ^ c) ∧
      (∀ (W : Type) [Fintype W] (G : SimpleGraph W),
        IsEmpty (pathGraph 6 ↪g G) →
          (G.cliqueNum : ℝ) ≥ (Fintype.card W : ℝ) ^ c ∨
          (G.indepNum : ℝ) ≥ (Fintype.card W : ℝ) ^ c) := by
  obtain ⟨c₀, hc₀, h_eh⟩ := hasErdosHajnalProp_P6
  refine erdos_hajnal_all_n_of_large_n (pathGraph 6) (le_refl 2) hc₀ ?_
  intro n _hn G hG
  simpa using h_eh (Fin n) G hG

end ErdosHajnalP6

