/-
Copyright 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosHajnal.BasicLemmas
import ErdosHajnal.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Stage 2 Reduction to the Erdős–Hajnal Property (Proposition 5.4 of `FMBV4-016_readable.tex`)

This file formalizes:
1. **Sparse Graph Independent Set / Restricted Graph Homogeneous Set Lemma**:
   If $S \subseteq V$ is $x$-sparse in $G$, then $G$ contains an independent set of size
   $\ge \frac{|S|}{x|S| + 1}$. Consequently, if $S$ is $x$-restricted,
   $\kappa(G) \ge \frac{|S|}{x|S| + 1}$.
2. **Anticonnected Component Blockade Lemma (`lem:anticonn-blockade`, Lemma 2.5)**:
   For any graph $G$ on nonempty $S \subseteq V$ and integer $k \ge 2$, either $S$ has an
   anticonnected component $C \subseteq S$ with $|C| \ge |S|/k$, or $S$ contains a complete
   $(k, |S|/k^2)$-blockade in $G$.
3. **Connected Subgraph Pruning Lemma**:
   Any finite connected graph on $\ge w \ge 1$ vertices contains an induced connected subgraph
   on exactly $w$ vertices. Hence any anticonnected set $C$ with $|C| \ge w \ge 1$ contains an
   anticonnected subset $B \subseteq C$ with $|B| = w$.
4. **Blockade Iteration Lemma (`lem:blockade-iter`, Lemma 2.8)** and
   **Blockade-to-Restricted-Subgraph Lemma (`lem:blockade-to-rest`, Lemma 2.9)**.
5. **Stage 2 Reduction (`prop:master-reduction`, Proposition 5.4)**:
   Every finite graph family that is leaf-reducible, wonderful, and generalized nice satisfies
   the Erdős–Hajnal property.
-/

set_option linter.unusedSectionVars false

open Finset SimpleGraph Real

namespace ErdosHajnalP6

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Basic Helper Lemmas on Neighborhoods and Pairs -/

@[simp]
private theorem mem_neighborFinsetIn (G : SimpleGraph V) (v u : V) (S : Finset V) :
    u ∈ neighborFinsetIn G v S ↔ u ∈ S ∧ G.Adj v u := by
  classical
  simp [neighborFinsetIn]

private theorem neighborFinsetIn_subset (G : SimpleGraph V) (v : V) (S : Finset V) :
    neighborFinsetIn G v S ⊆ S := by
  intro u hu
  exact ((mem_neighborFinsetIn G v u S).mp hu).1

private theorem neighborFinsetIn_mono (G : SimpleGraph V) (v : V) {S T : Finset V} (h : S ⊆ T) :
    neighborFinsetIn G v S ⊆ neighborFinsetIn G v T := by
  intro u hu
  rw [mem_neighborFinsetIn] at hu ⊢
  exact ⟨h hu.1, hu.2⟩

private theorem IsCompletePair.symm {G : SimpleGraph V} {A B : Finset V} (h : IsCompletePair G A B) :
    IsCompletePair G B A :=
  fun u hu v hv => (h v hv u hu).symm

private theorem IsCompletePair.mono {G : SimpleGraph V} {A B A' B' : Finset V}
    (hA : A' ⊆ A) (hB : B' ⊆ B) (h : IsCompletePair G A B) :
    IsCompletePair G A' B' :=
  fun u hu v hv => h u (hA hu) v (hB hv)

theorem IsAnticompletePair.symm {G : SimpleGraph V} {A B : Finset V}
    (h : IsAnticompletePair G A B) : IsAnticompletePair G B A :=
  fun u hu v hv hadj => h v hv u hu hadj.symm

theorem IsAnticompletePair.mono {G : SimpleGraph V} {A B A' B' : Finset V}
    (hA : A' ⊆ A) (hB : B' ⊆ B) (h : IsAnticompletePair G A B) :
    IsAnticompletePair G A' B' :=
  fun u hu v hv => h u (hA hu) v (hB hv)

theorem IsPurePair.symm {G : SimpleGraph V} {A B : Finset V} (h : IsPurePair G A B) :
    IsPurePair G B A :=
  h.imp IsCompletePair.symm IsAnticompletePair.symm

theorem IsPurePair.mono {G : SimpleGraph V} {A B A' B' : Finset V}
    (hA : A' ⊆ A) (hB : B' ⊆ B) (h : IsPurePair G A B) :
    IsPurePair G A' B' :=
  h.imp (IsCompletePair.mono hA hB) (IsAnticompletePair.mono hA hB)

theorem isAnticompletePair_iff_isCompletePair_compl {G : SimpleGraph V} {A B : Finset V}
    (hdisj : Disjoint A B) :
    IsAnticompletePair G A B ↔ IsCompletePair Gᶜ A B := by
  constructor
  · intro h u hu v hv
    rw [SimpleGraph.compl_adj]
    exact ⟨fun huv => Finset.disjoint_left.mp hdisj hu (huv ▸ hv), h u hu v hv⟩
  · intro h u hu v hv
    have hadj := h u hu v hv
    rw [SimpleGraph.compl_adj] at hadj
    exact hadj.2

theorem isAnticompleteBlockadeIn_iff_compl {G : SimpleGraph V} {S : Finset V} {k : ℕ} {w : ℝ}
    {B : Fin k → Finset V} :
    IsAnticompleteBlockadeIn G S k w B ↔ IsCompleteBlockadeIn Gᶜ S k w B := by
  constructor
  · rintro ⟨hB, hanti⟩
    refine ⟨⟨hB.subset_ambient, hB.nonempty_blocks, hB.pairwise_disjoint, hB.width_ge⟩, ?_⟩
    intro i j hij
    exact (isAnticompletePair_iff_isCompletePair_compl (hB.pairwise_disjoint i j hij)).mp
      (hanti i j hij)
  · rintro ⟨hB, hcomp⟩
    refine ⟨⟨hB.subset_ambient, hB.nonempty_blocks, hB.pairwise_disjoint, hB.width_ge⟩, ?_⟩
    intro i j hij
    exact (isAnticompletePair_iff_isCompletePair_compl (hB.pairwise_disjoint i j hij)).mpr
      (hcomp i j hij)

private theorem IsBlockadeIn.mono {G : SimpleGraph V} {S S' : Finset V} {k : ℕ} {w w' : ℝ}
    {B : Fin k → Finset V} (hS : S ⊆ S') (hw : w' ≤ w) (hB : IsBlockadeIn G S k w B) :
    IsBlockadeIn G S' k w' B :=
  ⟨fun i => Subset.trans (hB.subset_ambient i) hS,
   hB.nonempty_blocks,
   hB.pairwise_disjoint,
   fun i => le_trans hw (hB.width_ge i)⟩

private theorem IsCompleteBlockadeIn.mono {G : SimpleGraph V} {S S' : Finset V} {k : ℕ} {w w' : ℝ}
    {B : Fin k → Finset V} (hS : S ⊆ S') (hw : w' ≤ w) (hB : IsCompleteBlockadeIn G S k w B) :
    IsCompleteBlockadeIn G S' k w' B :=
  ⟨hB.1.mono hS hw, hB.2⟩

private theorem IsAnticompleteBlockadeIn.mono {G : SimpleGraph V} {S S' : Finset V} {k : ℕ} {w w' : ℝ}
    {B : Fin k → Finset V} (hS : S ⊆ S') (hw : w' ≤ w) (hB : IsAnticompleteBlockadeIn G S k w B) :
    IsAnticompleteBlockadeIn G S' k w' B :=
  ⟨hB.1.mono hS hw, hB.2⟩

/-!
### Part 1: Sparse Graph Independent Set / Restricted Graph Homogeneous Set Lemma
-/

/--
Greedy independent set extraction: if every vertex $v \in S$ has at most $B$ neighbors in $S$,
then any subset $T \subseteq S$ contains an independent set $I \subseteq T$ in $G$ satisfying
$|T| \le (B + 1)|I|$.
-/
theorem exists_indepSet_of_deg_bound (G : SimpleGraph V) (S : Finset V) (B : ℝ)
    (hB : ∀ v ∈ S, ((neighborFinsetIn G v S).card : ℝ) ≤ B) :
    ∀ T ⊆ S, ∃ I ⊆ T, G.IsIndepSet (I : Set V) ∧ (T.card : ℝ) ≤ (B + 1) * (I.card : ℝ) := by
  classical
  intro T hTS
  induction hn : T.card using Nat.strong_induction_on generalizing T with
  | _ n ih =>
    subst hn
    rcases T.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
    · refine ⟨∅, Subset.rfl, by simp, by simp⟩
    · let T' := T.filter (fun u => u ≠ v ∧ ¬G.Adj v u)
      have hT'T : T' ⊆ T := filter_subset _ _
      have hT'S : T' ⊆ S := Subset.trans hT'T hTS
      have hvT' : v ∉ T' := by simp [T']
      have hlt : T'.card < T.card :=
        card_lt_card (ssubset_iff_of_subset hT'T |>.mpr ⟨v, hv, hvT'⟩)
      obtain ⟨I', hI'T', hI'_indep, hI'_card⟩ := ih T'.card hlt T' hT'S rfl
      have hvI' : v ∉ I' := fun h => hvT' (hI'T' h)
      refine ⟨insert v I', insert_subset hv (Subset.trans hI'T' hT'T), ?_, ?_⟩
      · intro x hx y hy hxy
        simp only [coe_insert, Set.mem_insert_iff] at hx hy
        rcases hx with rfl | hxI'
        · rcases hy with rfl | hyI'
          · exact (hxy rfl).elim
          · have hyT' := hI'T' hyI'
            simp only [T', mem_filter] at hyT'
            exact hyT'.2.2
        · rcases hy with rfl | hyI'
          · have hxT' := hI'T' hxI'
            simp only [T', mem_filter] at hxT'
            exact fun hadj => hxT'.2.2 hadj.symm
          · exact hI'_indep hxI' hyI' hxy
      · have hT_sub : T ⊆ insert v (neighborFinsetIn G v S ∪ T') := by
          intro u hu
          rw [mem_insert, mem_union, mem_neighborFinsetIn]
          by_cases huv : u = v
          · exact Or.inl huv
          · by_cases hadj : G.Adj v u
            · exact Or.inr (Or.inl ⟨hTS hu, hadj⟩)
            · right; right
              simp only [T', mem_filter]
              exact ⟨hu, huv, hadj⟩
        have hcard_nat : T.card ≤ (neighborFinsetIn G v S).card + T'.card + 1 := by
          calc T.card
            _ ≤ (insert v (neighborFinsetIn G v S ∪ T')).card := card_le_card hT_sub
            _ ≤ (neighborFinsetIn G v S ∪ T').card + 1 := card_insert_le _ _
            _ ≤ (neighborFinsetIn G v S).card + T'.card + 1 :=
              Nat.add_le_add_right (card_union_le _ _) 1
        have hcard_real :
            (T.card : ℝ) ≤ ((neighborFinsetIn G v S).card : ℝ) + (T'.card : ℝ) + 1 := by
          exact_mod_cast hcard_nat
        have hvB : ((neighborFinsetIn G v S).card : ℝ) ≤ B := hB v (hTS hv)
        have hI_card : ((insert v I').card : ℝ) = (I'.card : ℝ) + 1 := by
          rw [card_insert_of_notMem hvI']
          push_cast
          ring
        rw [hI_card]
        linarith

/--
If $S \subseteq V$ is $x$-sparse in $G$, then $S$ contains an independent set $I \subseteq S$
with $|S| \le (x|S| + 1)|I|$.
-/
private theorem exists_indepSet_of_isEpsSparseOn (G : SimpleGraph V) (S : Finset V) (x : ℝ)
    (hS : IsEpsSparseOn G S x) :
    ∃ I ⊆ S, G.IsIndepSet (I : Set V) ∧ (S.card : ℝ) ≤ (x * (S.card : ℝ) + 1) * (I.card : ℝ) :=
  exists_indepSet_of_deg_bound G S (x * (S.card : ℝ)) hS S Subset.rfl

/--
If $S \subseteq V$ is $x$-sparse in $G$, then $\alpha(G) \ge \frac{|S|}{x|S| + 1}$.
-/
theorem indepNum_ge_of_isEpsSparseOn (G : SimpleGraph V) (S : Finset V) (x : ℝ)
    (hS : IsEpsSparseOn G S x) :
    (S.card : ℝ) / (x * (S.card : ℝ) + 1) ≤ (G.indepNum : ℝ) := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨v₀, hv₀⟩
  · simp
  · have hpos : 0 < x * (S.card : ℝ) + 1 := by
      have h0 : (0 : ℝ) ≤ ((neighborFinsetIn G v₀ S).card : ℝ) := Nat.cast_nonneg _
      have h1 : ((neighborFinsetIn G v₀ S).card : ℝ) ≤ x * (S.card : ℝ) := hS v₀ hv₀
      linarith
    obtain ⟨I, _, hI_indep, hI_card⟩ := exists_indepSet_of_isEpsSparseOn G S x hS
    have hI_le : (I.card : ℝ) ≤ (G.indepNum : ℝ) := by
      exact_mod_cast hI_indep.card_le_indepNum
    rw [div_le_iff₀ hpos]
    calc (S.card : ℝ)
      _ ≤ (x * (S.card : ℝ) + 1) * (I.card : ℝ) := hI_card
      _ ≤ (x * (S.card : ℝ) + 1) * (G.indepNum : ℝ) := by
        exact mul_le_mul_of_nonneg_left hI_le hpos.le
      _ = (G.indepNum : ℝ) * (x * (S.card : ℝ) + 1) := mul_comm _ _

/--
If $S \subseteq V$ is $x$-sparse in $\overline{G}$, then $\omega(G) \ge \frac{|S|}{x|S| + 1}$.
-/
theorem cliqueNum_ge_of_isEpsSparseOn_compl (G : SimpleGraph V) (S : Finset V) (x : ℝ)
    (hS : IsEpsSparseOn Gᶜ S x) :
    (S.card : ℝ) / (x * (S.card : ℝ) + 1) ≤ (G.cliqueNum : ℝ) := by
  have h := indepNum_ge_of_isEpsSparseOn Gᶜ S x hS
  rwa [indepNum_compl] at h

/--
If $S \subseteq V$ is $x$-restricted in $G$ (`IsEpsRestrictedOn G S x`), then
$\kappa(G) \ge \frac{|S|}{x|S| + 1}$.
(Used in Step 3 of Proposition 5.4 of `FMBV4-016_readable.tex`.)
-/
private theorem kappa_ge_of_isEpsRestrictedOn (G : SimpleGraph V) (S : Finset V) (x : ℝ)
    (hS : IsEpsRestrictedOn G S x) :
    (S.card : ℝ) / (x * (S.card : ℝ) + 1) ≤ (kappa G : ℝ) := by
  rcases hS with hsparse | hcosparse
  · refine (indepNum_ge_of_isEpsSparseOn G S x hsparse).trans ?_
    exact_mod_cast indepNum_le_kappa G
  · refine (cliqueNum_ge_of_isEpsSparseOn_compl G S x hcosparse).trans ?_
    exact_mod_cast cliqueNum_le_kappa G

/--
Consequently, if $S \subseteq V$ is $x$-restricted in $G$ with $x > 0$ and $|S| \ge x^{-1}$,
then $\kappa(G) \ge \frac{1}{2x}$.
-/
theorem kappa_ge_inv_two_mul_of_isEpsRestrictedOn (G : SimpleGraph V) (S : Finset V) (x : ℝ)
    (hx : 0 < x) (hcard : x⁻¹ ≤ (S.card : ℝ)) (hS : IsEpsRestrictedOn G S x) :
    (2 * x)⁻¹ ≤ (kappa G : ℝ) := by
  refine le_trans ?_ (kappa_ge_of_isEpsRestrictedOn G S x hS)
  have hxS : 1 ≤ (S.card : ℝ) * x := (inv_le_iff_one_le_mul₀ hx).mp hcard
  have hS_pos : (0 : ℝ) < (S.card : ℝ) := lt_of_lt_of_le (inv_pos.mpr hx) hcard
  rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-!
### Part 2: Anticonnected Component Blockade Lemma (`lem:anticonn-blockade`, Lemma 2.5)
-/

/--
Every nonempty finite vertex set $T$ contains a nonempty anticonnected component $C \subseteq T$
in $G$ (so that $C$ is complete to $T \setminus C$ in $G$).
-/
theorem exists_anticonnected_component_in (G : SimpleGraph V) (T : Finset V) (hT : T.Nonempty) :
    ∃ C ⊆ T, C.Nonempty ∧ IsAnticonnected G C ∧ IsCompletePair G C (T \ C) := by
  classical
  induction hn : T.card using Nat.strong_induction_on generalizing T with
  | _ n ih =>
    subst hn
    by_cases hanti : IsAnticonnected G T
    · refine ⟨T, Subset.rfl, hT, hanti, ?_⟩
      intro u _ v hv
      simp at hv
    · haveI : Nonempty T := hT.coe_sort
      have hnot_pre : ¬(Gᶜ.induce (T : Set V)).Preconnected := by
        intro hpre
        exact hanti ⟨hpre⟩
      unfold SimpleGraph.Preconnected at hnot_pre
      push_neg at hnot_pre
      obtain ⟨u, v, huv⟩ := hnot_pre
      let A := T.filter (fun x => ∃ hx : x ∈ T, (Gᶜ.induce (T : Set V)).Reachable u ⟨x, hx⟩)
      have hAT : A ⊆ T := filter_subset _ _
      have huA : u.1 ∈ A := by
        simp only [A, mem_filter]
        exact ⟨u.2, u.2, Reachable.refl u⟩
      have hvA : v.1 ∉ A := by
        simp only [A, mem_filter, not_and, not_exists]
        intro _ _ hreach
        exact huv hreach
      have hlt : A.card < T.card :=
        card_lt_card (ssubset_iff_of_subset hAT |>.mpr ⟨v.1, v.2, hvA⟩)
      have hcomp_AT : IsCompletePair G A (T \ A) := by
        intro x hx y hy
        simp only [A, mem_filter] at hx
        obtain ⟨hxT, _, hreach⟩ := hx
        rw [mem_sdiff] at hy
        obtain ⟨hyT, hyA⟩ := hy
        have hxy : x ≠ y := by
          rintro rfl
          exact hyA (mem_filter.mpr ⟨hxT, hxT, hreach⟩)
        by_contra hnad
        have hadj_c : (Gᶜ.induce (T : Set V)).Adj ⟨x, hxT⟩ ⟨y, hyT⟩ := ⟨hxy, hnad⟩
        have hreach_y : (Gᶜ.induce (T : Set V)).Reachable u ⟨y, hyT⟩ :=
          hreach.trans (Adj.reachable hadj_c)
        exact hyA (mem_filter.mpr ⟨hyT, hyT, hreach_y⟩)
      obtain ⟨C, hCA, hC_ne, hC_anti, hC_comp⟩ := ih A.card hlt A ⟨u.1, huA⟩ rfl
      refine ⟨C, Subset.trans hCA hAT, hC_ne, hC_anti, ?_⟩
      intro x hx y hy
      rw [mem_sdiff] at hy
      by_cases hyA : y ∈ A
      · exact hC_comp x hx y (mem_sdiff.mpr ⟨hyA, hy.2⟩)
      · exact hcomp_AT x (hCA hx) y (mem_sdiff.mpr ⟨hy.1, hyA⟩)

/--
If every anticonnected component $C \subseteq S$ (complete to $S \setminus C$) has size $< a$,
then any subset $T \subseteq S$ (complete to $S \setminus T$) with $|T| \ge w > 0$ contains a
nonempty subset $B \subseteq T$ (complete to $S \setminus B$) with $w \le |B| < w + a$.
-/
theorem exists_complete_chunk_of_anticonnected_lt (G : SimpleGraph V) (S : Finset V) (w a : ℝ)
    (hw : 0 < w)
    (hsmall : ∀ C ⊆ S, IsAnticonnected G C → IsCompletePair G C (S \ C) → (C.card : ℝ) < a) :
    ∀ T ⊆ S, IsCompletePair G T (S \ T) → w ≤ (T.card : ℝ) →
      ∃ B ⊆ T, B.Nonempty ∧ IsCompletePair G B (S \ B) ∧
        w ≤ (B.card : ℝ) ∧ (B.card : ℝ) < w + a := by
  intro T hTS hT_comp hT_card
  induction hn : T.card using Nat.strong_induction_on generalizing T with
  | _ n ih =>
    subst hn
    have hT_pos : (0 : ℝ) < (T.card : ℝ) := lt_of_lt_of_le hw hT_card
    have hT_ne : T.Nonempty := card_pos.mp (by exact_mod_cast hT_pos)
    by_cases hlt_wa : (T.card : ℝ) < w + a
    · exact ⟨T, Subset.rfl, hT_ne, hT_comp, hT_card, hlt_wa⟩
    · push_neg at hlt_wa
      obtain ⟨C, hCT, hC_ne, hC_anti, hC_comp⟩ := exists_anticonnected_component_in G T hT_ne
      have hCS : C ⊆ S := Subset.trans hCT hTS
      have hC_comp_S : IsCompletePair G C (S \ C) := by
        intro x hx y hy
        rw [mem_sdiff] at hy
        by_cases hyT : y ∈ T
        · exact hC_comp x hx y (mem_sdiff.mpr ⟨hyT, hy.2⟩)
        · exact hT_comp x (hCT hx) y (mem_sdiff.mpr ⟨hy.1, hyT⟩)
      have hC_lt : (C.card : ℝ) < a := hsmall C hCS hC_anti hC_comp_S
      let T' := T \ C
      have hT'T : T' ⊆ T := sdiff_subset
      have hT'_card_eq : (T'.card : ℝ) + (C.card : ℝ) = (T.card : ℝ) := by
        exact_mod_cast card_sdiff_add_card_eq_card hCT
      have hT'_lt : T'.card < T.card := by
        have hC_pos : 0 < C.card := card_pos.mpr hC_ne
        have hsum : T'.card + C.card = T.card := card_sdiff_add_card_eq_card hCT
        omega
      have hT'_comp : IsCompletePair G T' (S \ T') := by
        intro x hx y hy
        rw [mem_sdiff] at hx hy
        by_cases hyT : y ∈ T
        · have hyC : y ∈ C := by
            by_contra hyC
            exact hy.2 (mem_sdiff.mpr ⟨hyT, hyC⟩)
          exact (hC_comp y hyC x (mem_sdiff.mpr ⟨hx.1, hx.2⟩)).symm
        · exact hT_comp x hx.1 y (mem_sdiff.mpr ⟨hy.1, hyT⟩)
      have hT'_ge : w ≤ (T'.card : ℝ) := by linarith
      obtain ⟨B, hBT', hB_ne, hB_comp, hB_ge, hB_lt⟩ :=
        ih T'.card hT'_lt T' (Subset.trans hT'T hTS) hT'_comp hT'_ge rfl
      exact ⟨B, Subset.trans hBT' hT'T, hB_ne, hB_comp, hB_ge, hB_lt⟩

/--
Prepending a block $X \subseteq T$ disjoint from and complete to $T' \subseteq T$ to a complete
$(m, w)$-blockade in $T'$ produces a complete $(m + 1, w)$-blockade in $T$.
-/
theorem IsCompleteBlockadeIn.cons {G : SimpleGraph V} {T T' X : Finset V} {m : ℕ} {w : ℝ}
    {B' : Fin m → Finset V}
    (hXT : X ⊆ T) (hT'T : T' ⊆ T) (hdisj : Disjoint X T') (hX_ne : X.Nonempty)
    (hX_w : w ≤ (X.card : ℝ)) (hX_comp : IsCompletePair G X T')
    (hB' : IsCompleteBlockadeIn G T' m w B') :
    IsCompleteBlockadeIn G T (m + 1) w (Fin.cons X B') := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i
    exact Fin.cases hXT (fun j => Subset.trans (hB'.1.subset_ambient j) hT'T) i
  · intro i
    exact Fin.cases hX_ne hB'.1.nonempty_blocks i
  · intro i j
    refine Fin.cases ?_ ?_ i <;> refine Fin.cases ?_ ?_ j
    · intro hij
      exact (hij rfl).elim
    · intro j' _
      simp only [Fin.cons_zero, Fin.cons_succ]
      exact Disjoint.mono_right (hB'.1.subset_ambient j') hdisj
    · intro i' _
      simp only [Fin.cons_zero, Fin.cons_succ]
      exact (Disjoint.mono_right (hB'.1.subset_ambient i') hdisj).symm
    · intro j' i' hij
      simp only [Fin.cons_succ]
      exact hB'.1.pairwise_disjoint i' j' (fun h => hij (congrArg Fin.succ h))
  · intro i
    exact Fin.cases hX_w hB'.1.width_ge i
  · intro i j
    refine Fin.cases ?_ ?_ i <;> refine Fin.cases ?_ ?_ j
    · intro hij
      exact (hij rfl).elim
    · intro j' _
      simp only [Fin.cons_zero, Fin.cons_succ]
      exact hX_comp.mono Subset.rfl (hB'.1.subset_ambient j')
    · intro i' _
      simp only [Fin.cons_zero, Fin.cons_succ]
      exact (hX_comp.mono Subset.rfl (hB'.1.subset_ambient i')).symm
    · intro j' i' hij
      simp only [Fin.cons_succ]
      exact hB'.2 i' j' (fun h => hij (congrArg Fin.succ h))

theorem IsAnticompleteBlockadeIn.cons {G : SimpleGraph V} {T T' X : Finset V} {m : ℕ} {w : ℝ}
    {B' : Fin m → Finset V}
    (hXT : X ⊆ T) (hT'T : T' ⊆ T) (hdisj : Disjoint X T') (hX_ne : X.Nonempty)
    (hX_w : w ≤ (X.card : ℝ)) (hX_anti : IsAnticompletePair G X T')
    (hB' : IsAnticompleteBlockadeIn G T' m w B') :
    IsAnticompleteBlockadeIn G T (m + 1) w (Fin.cons X B') := by
  rw [isAnticompleteBlockadeIn_iff_compl] at hB' ⊢
  exact IsCompleteBlockadeIn.cons hXT hT'T hdisj hX_ne hX_w
    ((isAnticompletePair_iff_isCompletePair_compl hdisj).mp hX_anti) hB'

/--
Iteratively extracting $m$ chunks of size $\in [w, w + a)$ yields a complete $(m, w)$-blockade.
-/
theorem exists_complete_blockade_of_anticonnected_lt (G : SimpleGraph V) (S : Finset V) (w a : ℝ)
    (hw : 0 < w) (ha : 0 < a)
    (hsmall : ∀ C ⊆ S, IsAnticonnected G C → IsCompletePair G C (S \ C) → (C.card : ℝ) < a) :
    ∀ (m : ℕ), 1 ≤ m → ∀ T ⊆ S, IsCompletePair G T (S \ T) →
      w + ((m : ℝ) - 1) * (w + a) ≤ (T.card : ℝ) →
      ∃ B : Fin m → Finset V, IsCompleteBlockadeIn G T m w B := by
  intro m hm
  induction m with
  | zero => omega
  | succ m ih =>
    intro T hTS hT_comp hT_card
    rcases Nat.eq_zero_or_pos m with rfl | hm_pos
    · have hw_le_T : w ≤ (T.card : ℝ) := by
        push_cast at hT_card
        linarith
      have hT_pos : (0 : ℝ) < (T.card : ℝ) := lt_of_lt_of_le hw hw_le_T
      have hT_ne : T.Nonempty := card_pos.mp (by exact_mod_cast hT_pos)
      refine ⟨fun _ => T, ⟨fun _ => Subset.rfl, fun _ => hT_ne, ?_, fun _ => hw_le_T⟩, ?_⟩
      · intro i j hij
        exact (hij (Fin.ext (by omega))).elim
      · intro i j hij
        exact (hij (Fin.ext (by omega))).elim
    · have hw_le_T : w ≤ (T.card : ℝ) := by
        have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        have hwa_pos : 0 < w + a := by linarith
        push_cast at hT_card
        nlinarith
      obtain ⟨B₀, hB₀T, hB₀_ne, hB₀_comp, hB₀_ge, hB₀_lt⟩ :=
        exists_complete_chunk_of_anticonnected_lt G S w a hw hsmall T hTS hT_comp hw_le_T
      let T' := T \ B₀
      have hT'T : T' ⊆ T := sdiff_subset
      have hT'S : T' ⊆ S := Subset.trans hT'T hTS
      have hT'_card_eq : (T'.card : ℝ) + (B₀.card : ℝ) = (T.card : ℝ) := by
        exact_mod_cast card_sdiff_add_card_eq_card hB₀T
      have hT'_comp : IsCompletePair G T' (S \ T') := by
        intro x hx y hy
        rw [mem_sdiff] at hx hy
        by_cases hyT : y ∈ T
        · have hyB₀ : y ∈ B₀ := by
            by_contra hyB₀
            exact hy.2 (mem_sdiff.mpr ⟨hyT, hyB₀⟩)
          exact (hB₀_comp y hyB₀ x (mem_sdiff.mpr ⟨hTS hx.1, hx.2⟩)).symm
        · exact hT_comp x hx.1 y (mem_sdiff.mpr ⟨hy.1, hyT⟩)
      have hT'_card : w + ((m : ℝ) - 1) * (w + a) ≤ (T'.card : ℝ) := by
        push_cast at hT_card
        linarith
      obtain ⟨B', hB'⟩ := ih hm_pos T' hT'S hT'_comp hT'_card
      have hB₀_T' : IsCompletePair G B₀ T' := by
        intro x hx y hy
        rw [mem_sdiff] at hy
        exact hB₀_comp x hx y (mem_sdiff.mpr ⟨hTS hy.1, hy.2⟩)
      exact ⟨Fin.cons B₀ B',
        IsCompleteBlockadeIn.cons hB₀T hT'T disjoint_sdiff_self_right hB₀_ne hB₀_ge hB₀_T' hB'⟩

/--
**Lemma 2.5 (`lem:anticonn-blockade`, Anticonnected Component Blockade Lemma)**:
Let $G$ be a graph on a nonempty vertex set $S \subseteq V$ and let $k \ge 2$ be an integer.
Either $S$ contains an anticonnected component $C \subseteq S$ (complete to $S \setminus C$)
with $|C| \ge |S|/k$, or $S$ contains a complete $(k, |S|/k^2)$-blockade in $G$.
-/
theorem anticonnected_component_or_complete_blockade (G : SimpleGraph V) (S : Finset V) (k : ℕ)
    (hS : S.Nonempty) (hk : 2 ≤ k) :
    (∃ C ⊆ S, C.Nonempty ∧ IsAnticonnected G C ∧ IsCompletePair G C (S \ C) ∧
      (S.card : ℝ) / (k : ℝ) ≤ (C.card : ℝ)) ∨
    (∃ B : Fin k → Finset V, IsCompleteBlockadeIn G S k ((S.card : ℝ) / (k : ℝ) ^ 2) B) := by
  by_cases hcomp : ∃ C ⊆ S, C.Nonempty ∧ IsAnticonnected G C ∧ IsCompletePair G C (S \ C) ∧
      (S.card : ℝ) / (k : ℝ) ≤ (C.card : ℝ)
  · exact Or.inl hcomp
  · right
    push_neg at hcomp
    let w := (S.card : ℝ) / (k : ℝ) ^ 2
    let a := (S.card : ℝ) / (k : ℝ)
    have hS_pos : (0 : ℝ) < (S.card : ℝ) := Nat.cast_pos.mpr (card_pos.mpr hS)
    have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
    have hw : 0 < w := by positivity
    have ha : 0 < a := by positivity
    have hsmall : ∀ C ⊆ S, IsAnticonnected G C → IsCompletePair G C (S \ C) → (C.card : ℝ) < a := by
      intro C hCS hC_anti hC_pair
      haveI : Nonempty C := hC_anti.nonempty
      have hC_ne : C.Nonempty := Finset.nonempty_coe_sort.mp ‹_›
      exact hcomp C hCS hC_ne hC_anti hC_pair
    have hS_comp : IsCompletePair G S (S \ S) := by
      intro x _ y hy
      simp at hy
    have hcard_eq : w + ((k : ℝ) - 1) * (w + a) ≤ (S.card : ℝ) := by
      have hk_ne : (k : ℝ) ≠ 0 := hk_pos.ne'
      have : w + ((k : ℝ) - 1) * (w + a) = (S.card : ℝ) := by
        dsimp [w, a]
        field_simp
        ring
      linarith
    exact exists_complete_blockade_of_anticonnected_lt G S w a hw ha hsmall k (by omega)
      S Subset.rfl hS_comp hcard_eq

/-!
### Part 3: Connected Subgraph Pruning Lemma (Step 1c, line 567)
-/

/--
Along any walk in $H[C]$ from a vertex $x \in B$ to a vertex $y \in C \setminus B$,
there is an edge of $H$ crossing from some $u \in B$ to some $v \in C \setminus B$.
-/
theorem exists_adj_of_walk_mem_notMem (H : SimpleGraph V) (C B : Finset V) {x y : C}
    (p : (H.induce (C : Set V)).Walk x y) (hx : x.1 ∈ B) (hy : y.1 ∉ B) :
    ∃ u ∈ B, ∃ v ∈ C \ B, H.Adj u v := by
  induction p with
  | nil => exact (hy hx).elim
  | @cons a b c hadj p ih =>
    by_cases hb : b.1 ∈ B
    · exact ih hb hy
    · exact ⟨a.1, hx, b.1, mem_sdiff.mpr ⟨b.2, hb⟩, hadj⟩

/--
Adding a vertex $v$ adjacent in $H$ to some vertex $u \in B$ preserves connectedness of $H[B]$.
-/
theorem connected_induce_insert (H : SimpleGraph V) (B : Finset V) (u v : V)
    (hB : (H.induce (B : Set V)).Connected) (hu : u ∈ B) (hadj : H.Adj u v) :
    (H.induce ((insert v B : Finset V) : Set V)).Connected := by
  rw [connected_iff_exists_forall_reachable]
  have hu' : u ∈ (insert v B : Finset V) := mem_insert_of_mem hu
  refine ⟨⟨u, hu'⟩, ?_⟩
  rintro ⟨x, hx⟩
  simp only [mem_coe, mem_insert] at hx
  rcases hx with rfl | hxB
  · exact Adj.reachable hadj
  · have hreach : (H.induce (B : Set V)).Reachable ⟨u, hu⟩ ⟨x, hxB⟩ := hB ⟨u, hu⟩ ⟨x, hxB⟩
    let φ : H.induce (B : Set V) →g H.induce ((insert v B : Finset V) : Set V) :=
      ⟨fun z => ⟨z.1, mem_insert_of_mem z.2⟩, fun h => h⟩
    exact hreach.map φ

/--
**Connected Subgraph Pruning Lemma**:
Every finite connected induced subgraph $H[C]$ on $|C| \ge w \ge 1$ vertices contains an
induced connected subgraph $H[B]$ ($B \subseteq C$) on exactly $|B| = w$ vertices.
-/
theorem exists_connected_subset_card_eq (H : SimpleGraph V) (C : Finset V) (w : ℕ)
    (hC : (H.induce (C : Set V)).Connected) (hw1 : 1 ≤ w) (hwC : w ≤ C.card) :
    ∃ B ⊆ C, B.card = w ∧ (H.induce (B : Set V)).Connected := by
  induction w with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm_pos
    · obtain ⟨u₀, hu₀⟩ := card_pos.mp hwC
      refine ⟨{u₀}, singleton_subset_iff.mpr hu₀, card_singleton u₀, ?_⟩
      rw [connected_iff_exists_forall_reachable]
      refine ⟨⟨u₀, mem_singleton_self u₀⟩, ?_⟩
      rintro ⟨x, hx⟩
      simp only [mem_coe, mem_singleton] at hx
      subst hx
      exact Reachable.refl _
    · obtain ⟨B, hBC, hB_card, hB_conn⟩ := ih hm_pos (by omega)
      have hB_ne : B.Nonempty := card_pos.mp (by omega)
      have hCB_ne : (C \ B).Nonempty := by
        rw [sdiff_nonempty]
        intro hCB
        have := card_le_card hCB
        omega
      obtain ⟨u₀, hu₀⟩ := hB_ne
      obtain ⟨z₀, hz₀⟩ := hCB_ne
      rw [mem_sdiff] at hz₀
      have hreach : (H.induce (C : Set V)).Reachable ⟨u₀, hBC hu₀⟩ ⟨z₀, hz₀.1⟩ :=
        hC ⟨u₀, hBC hu₀⟩ ⟨z₀, hz₀.1⟩
      obtain ⟨u, huB, v, hvCB, hadj⟩ :=
        exists_adj_of_walk_mem_notMem H C B hreach.some hu₀ hz₀.2
      rw [mem_sdiff] at hvCB
      refine ⟨insert v B, insert_subset hvCB.1 hBC, ?_, ?_⟩
      · rw [card_insert_of_notMem hvCB.2, hB_card]
      · exact connected_induce_insert H B u v hB_conn huB hadj

/--
**Anticonnected Subset Pruning Corollary (Step 1c, line 567)**:
Any anticonnected set $C$ in $G$ with $|C| \ge w \ge 1$ contains an anticonnected subset
$B \subseteq C$ with $|B| = w$.
-/
theorem exists_anticonnected_subset_card_eq (G : SimpleGraph V) (C : Finset V) (w : ℕ)
    (hC : IsAnticonnected G C) (hw1 : 1 ≤ w) (hwC : w ≤ C.card) :
    ∃ B ⊆ C, B.card = w ∧ IsAnticonnected G B :=
  exists_connected_subset_card_eq Gᶜ C w hC hw1 hwC

/-!
### Part 4: Blockade Iteration Lemma (`lem:blockade-iter`, Lemma 2.8) and
Blockade-to-Restricted-Subgraph Lemma (`lem:blockade-to-rest`, Lemma 2.9)
-/

/-- $\ln 2 \ge \frac{7}{12}$, proved via $1 - x^{-1} \le \ln x$ on $4/3$ and $3/2$. -/
theorem log_two_ge_seven_twelfths : (7 : ℝ) / 12 ≤ Real.log 2 := by
  have h1 : (1 : ℝ) - (4 / 3 : ℝ)⁻¹ ≤ Real.log (4 / 3) :=
    Real.one_sub_inv_le_log_of_pos (by norm_num)
  have h2 : (1 : ℝ) - (3 / 2 : ℝ)⁻¹ ≤ Real.log (3 / 2) :=
    Real.one_sub_inv_le_log_of_pos (by norm_num)
  have h3 : Real.log (4 / 3) + Real.log (3 / 2) = Real.log 2 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  linarith

/-- For every $b \ge 1$, $b \cdot 2^{-4 b} \le \frac{1}{8}$. -/
theorem mul_rpow_neg_four_le_eighth {b : ℝ} (hb : 1 ≤ b) :
    b * (2 : ℝ) ^ (-4 * b) ≤ 1 / 8 := by
  by_cases hb32 : b ≤ 3 / 2
  · have hpow_le : (2 : ℝ) ^ (-4 * b) ≤ 1 / 16 := by
      calc (2 : ℝ) ^ (-4 * b)
        _ ≤ (2 : ℝ) ^ (-4 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 1 / 16 := by norm_num
    have hpow_pos : (0 : ℝ) ≤ (2 : ℝ) ^ (-4 * b) := by positivity
    nlinarith
  · push_neg at hb32
    have hb_pos : 0 < b := by linarith
    have hlog2 := log_two_ge_seven_twelfths
    have hlog_b : Real.log b ≤ Real.log ((2 : ℝ) ^ (2 * b)) := by
      have h1 : Real.log b ≤ b - 1 := Real.log_le_sub_one_of_pos hb_pos
      rw [Real.log_rpow two_pos]
      nlinarith
    have hb_le : b ≤ (2 : ℝ) ^ (2 * b) :=
      (Real.log_le_log_iff hb_pos (by positivity)).mp hlog_b
    have hpow_prod : (2 : ℝ) ^ (2 * b) * (2 : ℝ) ^ (-4 * b) = (2 : ℝ) ^ (-2 * b) := by
      rw [← Real.rpow_add two_pos]
      ring_nf
    have hpow_le : (2 : ℝ) ^ (-2 * b) ≤ 1 / 8 := by
      calc (2 : ℝ) ^ (-2 * b)
        _ ≤ (2 : ℝ) ^ (-3 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 1 / 8 := by norm_num
    calc b * (2 : ℝ) ^ (-4 * b)
      _ ≤ (2 : ℝ) ^ (2 * b) * (2 : ℝ) ^ (-4 * b) :=
        mul_le_mul_of_nonneg_right hb_le (by positivity)
      _ = (2 : ℝ) ^ (-2 * b) := hpow_prod
      _ ≤ 1 / 8 := hpow_le

/-- For every $b \ge 1$, $b \cdot 2^{-4 b} \le \frac{1}{4}$. -/
theorem mul_rpow_neg_four_le_quarter {b : ℝ} (hb : 1 ≤ b) :
    b * (2 : ℝ) ^ (-4 * b) ≤ 1 / 4 :=
  (mul_rpow_neg_four_le_eighth hb).trans (by norm_num)

/--
Multiplicative vertex retention inequality (Step 2 of Proposition 5.4 of `FMBV4-016_readable.tex`):
For $b \ge 1$, $0 < y \le 2^{-4b}$, and $s \le 2 y^{-1}$, $(1 - by)^s \ge 2^{-4b}$.
-/
theorem rpow_neg_four_le_one_sub_mul_pow {b y : ℝ} (hb : 1 ≤ b) (hy0 : 0 < y)
    (hyc : y ≤ (2 : ℝ) ^ (-4 * b)) (s : ℕ) (hs : (s : ℝ) ≤ 2 * y⁻¹) :
    (2 : ℝ) ^ (-4 * b) ≤ (1 - b * y) ^ s := by
  have hlog2 := log_two_ge_seven_twelfths
  have hby_nonneg : 0 ≤ b * y := by positivity
  have hby_le : b * y ≤ 1 / 8 :=
    (mul_le_mul_of_nonneg_left hyc (by linarith)).trans (mul_rpow_neg_four_le_eighth hb)
  have h1_sub_pos : 0 < 1 - b * y := by linarith
  have hlog_step : -2 * Real.log 2 * (b * y) ≤ Real.log (1 - b * y) := by
    have h1 : 1 - (1 - b * y)⁻¹ ≤ Real.log (1 - b * y) :=
      Real.one_sub_inv_le_log_of_pos h1_sub_pos
    have h2 : 1 - (1 - b * y)⁻¹ = -(b * y) / (1 - b * y) := by
      have hne : 1 - b * y ≠ 0 := h1_sub_pos.ne'
      field_simp
      ring
    have h3 : -(8 / 7 : ℝ) * (b * y) ≤ -(b * y) / (1 - b * y) := by
      rw [le_div_iff₀ h1_sub_pos]
      nlinarith
    have h4 : -2 * Real.log 2 * (b * y) ≤ -(8 / 7 : ℝ) * (b * y) := by
      nlinarith [hlog2, hby_nonneg]
    linarith
  have hs_by : (s : ℝ) * (b * y) ≤ 2 * b := by
    calc (s : ℝ) * (b * y)
      _ ≤ (2 * y⁻¹) * (b * y) := mul_le_mul_of_nonneg_right hs hby_nonneg
      _ = 2 * b * (y⁻¹ * y) := by ring
      _ = 2 * b := by rw [inv_mul_cancel₀ hy0.ne', mul_one]
  have hlog_pow : Real.log ((2 : ℝ) ^ (-4 * b)) ≤ Real.log ((1 - b * y) ^ s) := by
    rw [Real.log_rpow two_pos, Real.log_pow]
    have hs_nonneg : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
    nlinarith
  exact (Real.log_le_log_iff (by positivity) (by positivity)).mp hlog_pow

/--
Ramsey double-induction helper for the Blockade Iteration Lemma:
given $p, q \ge 1$ and $Y \subseteq F_0$ at step $s$ with $|Y| \ge (1 - by)^s |F_0|$ and
$s + p + q - 2 \le 2 y^{-1}$, $Y$ contains either a complete $(p, w_0)$-blockade
or an anticomplete $(q, w_0)$-blockade in $G$, where $w_0 = y^{a+2}|F_0|$.
-/
theorem blockade_iteration_pure_aux (G : SimpleGraph V) (F₀ : Finset V) (a b y : ℝ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hy0 : 0 < y) (hyc : y ≤ (2 : ℝ) ^ (-4 * b))
    (hw₀ : 1 ≤ y ^ (a + 2) * (F₀.card : ℝ))
    (hstep : ∀ F ⊆ F₀, (2 : ℝ) ^ (-4 * b) * (F₀.card : ℝ) ≤ (F.card : ℝ) →
      ∃ X ⊆ F, ∃ Y ⊆ F, Disjoint X Y ∧
        y ^ a * (F.card : ℝ) ≤ (X.card : ℝ) ∧
        (1 - b * y) * (F.card : ℝ) ≤ (Y.card : ℝ) ∧
        IsPurePair G X Y) :
    ∀ (N : ℕ) (p q s : ℕ), 1 ≤ p → 1 ≤ q → p + q = N →
      (s : ℝ) + (p : ℝ) + (q : ℝ) - 2 ≤ 2 * y⁻¹ →
      ∀ Y ⊆ F₀, (1 - b * y) ^ s * (F₀.card : ℝ) ≤ (Y.card : ℝ) →
        (∃ B : Fin p → Finset V, IsCompleteBlockadeIn G Y p (y ^ (a + 2) * (F₀.card : ℝ)) B) ∨
        (∃ B : Fin q → Finset V,
          IsAnticompleteBlockadeIn G Y q (y ^ (a + 2) * (F₀.card : ℝ)) B) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro p q s hp hq hN hs Y hYF₀ hY_card
    have hs_le : (s : ℝ) ≤ 2 * y⁻¹ := by
      have hp' : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      have hq' : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      linarith
    have hc_le_pow : (2 : ℝ) ^ (-4 * b) ≤ (1 - b * y) ^ s :=
      rpow_neg_four_le_one_sub_mul_pow hb hy0 hyc s hs_le
    have hY_ge_c : (2 : ℝ) ^ (-4 * b) * (F₀.card : ℝ) ≤ (Y.card : ℝ) :=
      le_trans (mul_le_mul_of_nonneg_right hc_le_pow (Nat.cast_nonneg _)) hY_card
    have hy_lt_one : y < 1 := by
      have : (2 : ℝ) ^ (-4 * b) ≤ (2 : ℝ) ^ (-4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      have : (2 : ℝ) ^ (-4 : ℝ) < 1 := by norm_num
      linarith
    have hy2_le_c : y ^ (a + 2) ≤ y ^ a * (2 : ℝ) ^ (-4 * b) := by
      have h1 : y ^ (a + 2) = y ^ a * y * y := by
        rw [Real.rpow_add hy0, Real.rpow_two]
        ring
      have h2 : y * y ≤ (2 : ℝ) ^ (-4 * b) * 1 :=
        mul_le_mul hyc hy_lt_one.le hy0.le (by positivity)
      rw [h1]
      nlinarith [Real.rpow_pos_of_pos hy0 a]
    have hY_ge_w₀ : y ^ (a + 2) * (F₀.card : ℝ) ≤ (Y.card : ℝ) := by
      have hya_le_one : y ^ a ≤ 1 := Real.rpow_le_one hy0.le hy_lt_one.le (by linarith)
      have : y ^ (a + 2) ≤ (2 : ℝ) ^ (-4 * b) := by
        nlinarith [Real.rpow_pos_of_pos two_pos (-4 * b)]
      exact le_trans (mul_le_mul_of_nonneg_right this (Nat.cast_nonneg _)) hY_ge_c
    have hY_ne : Y.Nonempty := by
      have : (1 : ℝ) ≤ (Y.card : ℝ) := le_trans hw₀ hY_ge_w₀
      exact card_pos.mp (by exact_mod_cast this)
    rcases p with _ | p'
    · omega
    · rcases Nat.eq_zero_or_pos p' with rfl | hp'
      · left
        refine ⟨fun _ => Y, ⟨fun _ => Subset.rfl, fun _ => hY_ne, ?_, fun _ => hY_ge_w₀⟩, ?_⟩
        · intro i j hij
          exact (hij (Fin.ext (by omega))).elim
        · intro i j hij
          exact (hij (Fin.ext (by omega))).elim
      · rcases q with _ | q'
        · omega
        · rcases Nat.eq_zero_or_pos q' with rfl | hq'
          · right
            refine ⟨fun _ => Y, ⟨fun _ => Subset.rfl, fun _ => hY_ne, ?_, fun _ => hY_ge_w₀⟩, ?_⟩
            · intro i j hij
              exact (hij (Fin.ext (by omega))).elim
            · intro i j hij
              exact (hij (Fin.ext (by omega))).elim
          · obtain ⟨X, hXY, Y', hY'Y, hdisj, hX_card, hY'_card, hpure⟩ := hstep Y hYF₀ hY_ge_c
            have hY'F₀ : Y' ⊆ F₀ := Subset.trans hY'Y hYF₀
            have hX_w₀ : y ^ (a + 2) * (F₀.card : ℝ) ≤ (X.card : ℝ) := by
              calc y ^ (a + 2) * (F₀.card : ℝ)
                _ ≤ y ^ a * ((2 : ℝ) ^ (-4 * b) * (F₀.card : ℝ)) := by nlinarith
                _ ≤ y ^ a * (Y.card : ℝ) :=
                  mul_le_mul_of_nonneg_left hY_ge_c (by positivity)
                _ ≤ (X.card : ℝ) := hX_card
            have hX_ne : X.Nonempty := by
              have : (1 : ℝ) ≤ (X.card : ℝ) := le_trans hw₀ hX_w₀
              exact card_pos.mp (by exact_mod_cast this)
            have hY'_pow : (1 - b * y) ^ (s + 1) * (F₀.card : ℝ) ≤ (Y'.card : ℝ) := by
              have h1_sub_nonneg : 0 ≤ 1 - b * y := by
                have := mul_rpow_neg_four_le_quarter hb
                have : b * y ≤ 1 / 4 :=
                  (mul_le_mul_of_nonneg_left hyc (by linarith)).trans this
                linarith
              rw [pow_succ']
              calc (1 - b * y) * (1 - b * y) ^ s * (F₀.card : ℝ)
                _ = (1 - b * y) * ((1 - b * y) ^ s * (F₀.card : ℝ)) := by ring
                _ ≤ (1 - b * y) * (Y.card : ℝ) :=
                  mul_le_mul_of_nonneg_left hY_card h1_sub_nonneg
                _ ≤ (Y'.card : ℝ) := hY'_card
            rcases hpure with hcomp | hanti
            · have hlt : p' + (q' + 1) < N := by omega
              have hs' : ((s + 1 : ℕ) : ℝ) + (p' : ℝ) + ((q' + 1 : ℕ) : ℝ) - 2 ≤ 2 * y⁻¹ := by
                push_cast at hs ⊢
                linarith
              rcases ih (p' + (q' + 1)) hlt p' (q' + 1) (s + 1) hp' (by omega) rfl hs'
                Y' hY'F₀ hY'_pow with ⟨B', hB'⟩ | ⟨B', hB'⟩
              · exact Or.inl ⟨Fin.cons X B',
                  IsCompleteBlockadeIn.cons hXY hY'Y hdisj hX_ne hX_w₀ hcomp hB'⟩
              · exact Or.inr ⟨B', hB'.mono hY'Y le_rfl⟩
            · have hlt : (p' + 1) + q' < N := by omega
              have hs' : ((s + 1 : ℕ) : ℝ) + ((p' + 1 : ℕ) : ℝ) + (q' : ℝ) - 2 ≤ 2 * y⁻¹ := by
                push_cast at hs ⊢
                linarith
              rcases ih ((p' + 1) + q') hlt (p' + 1) q' (s + 1) (by omega) hq' rfl hs'
                Y' hY'F₀ hY'_pow with ⟨B', hB'⟩ | ⟨B', hB'⟩
              · exact Or.inl ⟨B', hB'.mono hY'Y le_rfl⟩
              · exact Or.inr ⟨Fin.cons X B',
                  IsAnticompleteBlockadeIn.cons hXY hY'Y hdisj hX_ne hX_w₀ hanti hB'⟩

/--
**Lemma 2.8 (`lem:blockade-iter`, Blockade Iteration Lemma for Pure Pairs)**:
Let $a, b \ge 1$, $c = 2^{-4b}$, and $0 < y \le c$. Let $F_0$ be a vertex set with
$y^{a+2}|F_0| \ge 1$ such that every $F \subseteq F_0$ with $|F| \ge c |F_0|$ contains disjoint
subsets $X, Y \subseteq F$ with $|X| \ge y^a |F|$ and $|Y| \ge (1 - by)|F|$ where $(X, Y)$ is
complete or anticomplete in $G$. Then $F_0$ contains a complete or anticomplete
$(\lceil y^{-1} \rceil, y^{a+2}|F_0|)$-blockade (and hence also of width
$\lfloor y^{a+2}|F_0| \rfloor$).
-/
theorem blockade_iteration_pure (G : SimpleGraph V) (F₀ : Finset V) (a b y : ℝ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hy0 : 0 < y) (hyc : y ≤ (2 : ℝ) ^ (-4 * b))
    (hw₀ : 1 ≤ y ^ (a + 2) * (F₀.card : ℝ))
    (hstep : ∀ F ⊆ F₀, (2 : ℝ) ^ (-4 * b) * (F₀.card : ℝ) ≤ (F.card : ℝ) →
      ∃ X ⊆ F, ∃ Y ⊆ F, Disjoint X Y ∧
        y ^ a * (F.card : ℝ) ≤ (X.card : ℝ) ∧
        (1 - b * y) * (F.card : ℝ) ≤ (Y.card : ℝ) ∧
        IsPurePair G X Y) :
    (∃ B : Fin ⌈y⁻¹⌉₊ → Finset V,
      IsCompleteBlockadeIn G F₀ ⌈y⁻¹⌉₊ (y ^ (a + 2) * (F₀.card : ℝ)) B) ∨
    (∃ B : Fin ⌈y⁻¹⌉₊ → Finset V,
      IsAnticompleteBlockadeIn G F₀ ⌈y⁻¹⌉₊ (y ^ (a + 2) * (F₀.card : ℝ)) B) := by
  let k := ⌈y⁻¹⌉₊
  have hk_pos : 1 ≤ k := Nat.ceil_pos.mpr (inv_pos.mpr hy0)
  have hk_lt : (k : ℝ) < y⁻¹ + 1 := Nat.ceil_lt_add_one (inv_nonneg.mpr hy0.le)
  have hs0 : ((0 : ℕ) : ℝ) + (k : ℝ) + (k : ℝ) - 2 ≤ 2 * y⁻¹ := by
    push_cast
    linarith
  have hF₀_pow : (1 - b * y) ^ 0 * (F₀.card : ℝ) ≤ (F₀.card : ℝ) := by simp
  exact blockade_iteration_pure_aux G F₀ a b y ha hb hy0 hyc hw₀ hstep
    (k + k) k k 0 hk_pos hk_pos rfl hs0 F₀ Subset.rfl hF₀_pow

/-! #### Blockade-to-Restricted-Subgraph Lemma (`lem:blockade-to-rest`, Lemma 2.9) -/

/--
A finite family $\mathcal{A}$ of pairwise disjoint nonempty blocks inside $W$, each of size in
$[w_{\min}, w_{\max}]$, that are pairwise complete in $H$.
-/
structure IsLeafFamily (H : SimpleGraph V) (W : Finset V) (w_min w_max : ℝ)
    (𝒜 : Finset (Finset V)) : Prop where
  nonempty_family : 𝒜.Nonempty
  subset_ambient : ∀ L ∈ 𝒜, L ⊆ W
  nonempty_blocks : ∀ L ∈ 𝒜, L.Nonempty
  pairwise_disjoint : ∀ L₁ ∈ 𝒜, ∀ L₂ ∈ 𝒜, L₁ ≠ L₂ → Disjoint L₁ L₂
  card_ge : ∀ L ∈ 𝒜, w_min ≤ (L.card : ℝ)
  card_le : ∀ L ∈ 𝒜, (L.card : ℝ) ≤ w_max
  pairwise_complete : ∀ L₁ ∈ 𝒜, ∀ L₂ ∈ 𝒜, L₁ ≠ L₂ → IsCompletePair H L₁ L₂

theorem IsLeafFamily.mono {H : SimpleGraph V} {W W' : Finset V} {w_min w_max : ℝ}
    {𝒜 : Finset (Finset V)} (hW : W ⊆ W') (h𝒜 : IsLeafFamily H W w_min w_max 𝒜) :
    IsLeafFamily H W' w_min w_max 𝒜 :=
  ⟨h𝒜.nonempty_family,
   fun L hL => Subset.trans (h𝒜.subset_ambient L hL) hW,
   h𝒜.nonempty_blocks,
   h𝒜.pairwise_disjoint,
   h𝒜.card_ge,
   h𝒜.card_le,
   h𝒜.pairwise_complete⟩

/-- The leaf potential $\Phi_C(\mathcal{A}) := \sum_{L \in \mathcal{A}} |L|^{\frac{1}{2C}}$. -/
noncomputable def leafPotential (C : ℝ) (𝒜 : Finset (Finset V)) : ℝ :=
  ∑ L ∈ 𝒜, (L.card : ℝ) ^ (1 / (2 * C))

theorem leafPotential_nonneg (C : ℝ) (𝒜 : Finset (Finset V)) :
    0 ≤ leafPotential C 𝒜 :=
  sum_nonneg (fun _ _ => by positivity)

/--
Combining child leaf families across a complete $(k, |W|/k^C)$-blockade $U$ in $H$:
taking the disjoint union $\bigcup_i \mathcal{A}_i$ for $H$ and the maximum-potential child
$\mathcal{B}_{i_{\max}}$ for $Hᶜ$ preserves the product potential lower bound $|W|^{1/C}$.
-/
theorem combine_leaf_families (H : SimpleGraph V) (W : Finset V) (C w_min w_max : ℝ)
    (hC : 1 ≤ C) (k : ℕ) (hk : 2 ≤ k) (U : Fin k → Finset V)
    (hU : IsCompleteBlockadeIn H W k ((W.card : ℝ) / (k : ℝ) ^ C) U)
    (𝒜 ℬ : Fin k → Finset (Finset V))
    (h𝒜 : ∀ i : Fin k, IsLeafFamily H (U i) w_min w_max (𝒜 i))
    (hℬ : ∀ i : Fin k, IsLeafFamily Hᶜ (U i) w_min w_max (ℬ i))
    (hpot : ∀ i : Fin k, ((U i).card : ℝ) ^ (1 / C) ≤
      leafPotential C (𝒜 i) * leafPotential C (ℬ i)) :
    ∃ 𝒜_tot ℬ_tot : Finset (Finset V),
      IsLeafFamily H W w_min w_max 𝒜_tot ∧
      IsLeafFamily Hᶜ W w_min w_max ℬ_tot ∧
      (W.card : ℝ) ^ (1 / C) ≤ leafPotential C 𝒜_tot * leafPotential C ℬ_tot := by
  classical
  let 𝒜_tot := (Finset.univ : Finset (Fin k)).biUnion 𝒜
  have huniv_ne : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0, by omega⟩, mem_univ _⟩
  obtain ⟨i_max, _, hi_max⟩ :=
    exists_max_image Finset.univ (fun i => leafPotential C (ℬ i)) huniv_ne
  let ℬ_tot := ℬ i_max
  have hdisj_𝒜 : ∀ i j : Fin k, i ≠ j → Disjoint (𝒜 i) (𝒜 j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro L hLi hLj
    obtain ⟨v, hv⟩ := (h𝒜 i).nonempty_blocks L hLi
    exact Finset.disjoint_left.mp (hU.1.pairwise_disjoint i j hij)
      ((h𝒜 i).subset_ambient L hLi hv) ((h𝒜 j).subset_ambient L hLj hv)
  refine ⟨𝒜_tot, ℬ_tot, ?_, (hℬ i_max).mono (hU.1.subset_ambient i_max), ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨L₀, hL₀⟩ := (h𝒜 ⟨0, by omega⟩).nonempty_family
      exact ⟨L₀, mem_biUnion.mpr ⟨⟨0, by omega⟩, mem_univ _, hL₀⟩⟩
    · intro L hL
      obtain ⟨i, _, hLi⟩ := mem_biUnion.mp hL
      exact Subset.trans ((h𝒜 i).subset_ambient L hLi) (hU.1.subset_ambient i)
    · intro L hL
      obtain ⟨i, _, hLi⟩ := mem_biUnion.mp hL
      exact (h𝒜 i).nonempty_blocks L hLi
    · intro L₁ hL₁ L₂ hL₂ hne
      obtain ⟨i, _, hL₁i⟩ := mem_biUnion.mp hL₁
      obtain ⟨j, _, hL₂j⟩ := mem_biUnion.mp hL₂
      by_cases hij : i = j
      · subst hij
        exact (h𝒜 i).pairwise_disjoint L₁ hL₁i L₂ hL₂j hne
      · exact Disjoint.mono ((h𝒜 i).subset_ambient L₁ hL₁i) ((h𝒜 j).subset_ambient L₂ hL₂j)
          (hU.1.pairwise_disjoint i j hij)
    · intro L hL
      obtain ⟨i, _, hLi⟩ := mem_biUnion.mp hL
      exact (h𝒜 i).card_ge L hLi
    · intro L hL
      obtain ⟨i, _, hLi⟩ := mem_biUnion.mp hL
      exact (h𝒜 i).card_le L hLi
    · intro L₁ hL₁ L₂ hL₂ hne
      obtain ⟨i, _, hL₁i⟩ := mem_biUnion.mp hL₁
      obtain ⟨j, _, hL₂j⟩ := mem_biUnion.mp hL₂
      by_cases hij : i = j
      · subst hij
        exact (h𝒜 i).pairwise_complete L₁ hL₁i L₂ hL₂j hne
      · exact (hU.2 i j hij).mono ((h𝒜 i).subset_ambient L₁ hL₁i) ((h𝒜 j).subset_ambient L₂ hL₂j)
  · have hsum_𝒜 : leafPotential C 𝒜_tot = ∑ i : Fin k, leafPotential C (𝒜 i) := by
      unfold leafPotential
      exact sum_biUnion (fun i _ j _ hij => hdisj_𝒜 i j hij)
    have hC_pos : 0 < C := by linarith
    have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
    have hterm_ge : ∀ i : Fin k,
        (W.card : ℝ) ^ (1 / C) / (k : ℝ) ≤ ((U i).card : ℝ) ^ (1 / C) := by
      intro i
      have hUi_ge : (W.card : ℝ) / (k : ℝ) ^ C ≤ ((U i).card : ℝ) := hU.1.width_ge i
      have hpow_div :
          ((W.card : ℝ) / (k : ℝ) ^ C) ^ (1 / C) = (W.card : ℝ) ^ (1 / C) / (k : ℝ) := by
        rw [Real.div_rpow (Nat.cast_nonneg _) (by positivity), ← Real.rpow_mul hk_pos.le,
          mul_one_div_cancel hC_pos.ne', Real.rpow_one]
      rw [← hpow_div]
      exact Real.rpow_le_rpow (by positivity) hUi_ge (by positivity)
    calc (W.card : ℝ) ^ (1 / C)
      _ = ∑ _i : Fin k, (W.card : ℝ) ^ (1 / C) / (k : ℝ) := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_div_cancel₀ _ hk_pos.ne']
      _ ≤ ∑ i : Fin k, ((U i).card : ℝ) ^ (1 / C) :=
        sum_le_sum (fun i _ => hterm_ge i)
      _ ≤ ∑ i : Fin k, leafPotential C (𝒜 i) * leafPotential C (ℬ i) :=
        sum_le_sum (fun i _ => hpot i)
      _ ≤ ∑ i : Fin k, leafPotential C (𝒜 i) * leafPotential C ℬ_tot :=
        sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hi_max i (mem_univ i))
          (leafPotential_nonneg C (𝒜 i)))
      _ = leafPotential C 𝒜_tot * leafPotential C ℬ_tot := by
        rw [← sum_mul, hsum_𝒜]

/--
Strong induction step for Lemma 2.9 (`lem:blockade-to-rest`): every $W \subseteq S_0$ with $|W| \ge \varepsilon^{3C}|S_0|$
admits both a complete leaf family $\mathcal{C}$ and an anticomplete leaf family $\mathcal{I}$
whose leaf potentials satisfy $\Phi_C(\mathcal{C}) \cdot \Phi_C(\mathcal{I}) \ge |W|^{1/C}$.
-/
theorem exists_cograph_leaf_families (G : SimpleGraph V) (S₀ : Finset V) (C ε : ℝ)
    (hC : 1 ≤ C) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 4) (hS₀ : ε ^ (-3 * C) ≤ (S₀.card : ℝ))
    (hblock : ∀ F ⊆ S₀, ε ^ (2 * C) * (S₀.card : ℝ) ≤ (F.card : ℝ) →
      ∃ k : ℕ, 2 ≤ k ∧ (k : ℝ) ≤ ε⁻¹ ∧
        ∃ B : Fin k → Finset V,
          IsCompleteBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ C) B ∨
          IsAnticompleteBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ C) B) :
    ∀ W ⊆ S₀, ε ^ (3 * C) * (S₀.card : ℝ) ≤ (W.card : ℝ) →
      ∃ 𝒞 ℐ : Finset (Finset V),
        IsLeafFamily G W (ε ^ (3 * C) * (S₀.card : ℝ)) (ε ^ (2 * C) * (S₀.card : ℝ)) 𝒞 ∧
        IsLeafFamily Gᶜ W (ε ^ (3 * C) * (S₀.card : ℝ)) (ε ^ (2 * C) * (S₀.card : ℝ)) ℐ ∧
        (W.card : ℝ) ^ (1 / C) ≤ leafPotential C 𝒞 * leafPotential C ℐ := by
  classical
  let w_min := ε ^ (3 * C) * (S₀.card : ℝ)
  let w_max := ε ^ (2 * C) * (S₀.card : ℝ)
  have hw_min_ge_one : 1 ≤ w_min := by
    dsimp [w_min]
    calc (1 : ℝ)
      _ = ε ^ (3 * C) * ε ^ (-3 * C) := by
        rw [← Real.rpow_add hε0]
        simp
      _ ≤ ε ^ (3 * C) * (S₀.card : ℝ) :=
        mul_le_mul_of_nonneg_left hS₀ (by positivity)
  intro W hWS₀ hW_min
  induction hn : W.card using Nat.strong_induction_on generalizing W with
  | _ n ih =>
    subst hn
    by_cases hW_max : (W.card : ℝ) ≤ w_max
    · have hW_pos : (0 : ℝ) < (W.card : ℝ) := lt_of_lt_of_le (by linarith) hW_min
      have hW_ne : W.Nonempty := by
        have : (1 : ℝ) ≤ (W.card : ℝ) := le_trans hw_min_ge_one hW_min
        exact card_pos.mp (by exact_mod_cast this)
      have hleaf : ∀ H : SimpleGraph V, IsLeafFamily H W w_min w_max {W} := by
        intro H
        refine ⟨singleton_nonempty W, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro L hL; rw [mem_singleton.mp hL]
        · intro L hL; rw [mem_singleton.mp hL]; exact hW_ne
        · intro L₁ hL₁ L₂ hL₂ hne
          exact (hne ((mem_singleton.mp hL₁).trans (mem_singleton.mp hL₂).symm)).elim
        · intro L hL; rw [mem_singleton.mp hL]; exact hW_min
        · intro L hL; rw [mem_singleton.mp hL]; exact hW_max
        · intro L₁ hL₁ L₂ hL₂ hne
          exact (hne ((mem_singleton.mp hL₁).trans (mem_singleton.mp hL₂).symm)).elim
      refine ⟨{W}, {W}, hleaf G, hleaf Gᶜ, ?_⟩
      unfold leafPotential
      rw [sum_singleton, ← Real.rpow_add hW_pos]
      have hC_ne : C ≠ 0 := by linarith
      have : 1 / (2 * C) + 1 / (2 * C) = 1 / C := by
        field_simp
        ring
      rw [this]
    · push_neg at hW_max
      obtain ⟨k, hk2, hk_le, U, hU_pure⟩ := hblock W hWS₀ hW_max.le
      have hU_block : IsBlockadeIn G W k ((W.card : ℝ) / (k : ℝ) ^ C) U := by
        rcases hU_pure with ⟨hB, _⟩ | ⟨hB, _⟩ <;> exact hB
      have hUi_lt : ∀ i : Fin k, (U i).card < W.card := by
        intro i
        let j : Fin k := if i.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
        have hij : i ≠ j := by
          intro h
          have hval : i.val = j.val := congrArg Fin.val h
          by_cases hi0 : i.val = 0 <;> simp [j, hi0] at hval
        obtain ⟨v, hv⟩ := hU_block.nonempty_blocks j
        have hvW : v ∈ W := hU_block.subset_ambient j hv
        have hvUi : v ∉ U i := Finset.disjoint_left.mp (hU_block.pairwise_disjoint j i hij.symm) hv
        exact card_lt_card (ssubset_iff_of_subset (hU_block.subset_ambient i) |>.mpr ⟨v, hvW, hvUi⟩)
      have hUi_min : ∀ i : Fin k, w_min ≤ ((U i).card : ℝ) := by
        intro i
        have hkC_le : (k : ℝ) ^ C ≤ (ε⁻¹) ^ C :=
          Real.rpow_le_rpow (by positivity) hk_le (by linarith)
        have hε_inv_C : (ε⁻¹) ^ C = (ε ^ C)⁻¹ := Real.inv_rpow hε0.le C
        have hεC_W : ε ^ C * w_max ≤ (W.card : ℝ) / (k : ℝ) ^ C := by
          rw [le_div_iff₀ (by positivity)]
          calc ε ^ C * w_max * (k : ℝ) ^ C
            _ ≤ ε ^ C * w_max * (ε ^ C)⁻¹ := by
              rw [← hε_inv_C]
              exact mul_le_mul_of_nonneg_left hkC_le (by positivity)
            _ = w_max * (ε ^ C * (ε ^ C)⁻¹) := by ring
            _ = w_max := by rw [mul_inv_cancel₀ (by positivity), mul_one]
            _ ≤ (W.card : ℝ) := hW_max.le
        have hw_min_eq : w_min = ε ^ C * w_max := by
          dsimp [w_min, w_max]
          rw [← mul_assoc, ← Real.rpow_add hε0]
          ring_nf
        rw [hw_min_eq]
        exact le_trans hεC_W (hU_block.width_ge i)
      have h_ih : ∀ i : Fin k, ∃ 𝒞 ℐ : Finset (Finset V),
          IsLeafFamily G (U i) w_min w_max 𝒞 ∧
          IsLeafFamily Gᶜ (U i) w_min w_max ℐ ∧
          ((U i).card : ℝ) ^ (1 / C) ≤ leafPotential C 𝒞 * leafPotential C ℐ :=
        fun i => ih (U i).card (hUi_lt i) (U i)
          (Subset.trans (hU_block.subset_ambient i) hWS₀) (hUi_min i) rfl
      let 𝒞_sub : Fin k → Finset (Finset V) := fun i => (h_ih i).choose
      let ℐ_sub : Fin k → Finset (Finset V) := fun i => (h_ih i).choose_spec.choose
      have h𝒞_sub : ∀ i, IsLeafFamily G (U i) w_min w_max (𝒞_sub i) :=
        fun i => (h_ih i).choose_spec.choose_spec.1
      have hℐ_sub : ∀ i, IsLeafFamily Gᶜ (U i) w_min w_max (ℐ_sub i) :=
        fun i => (h_ih i).choose_spec.choose_spec.2.1
      have hpot_sub : ∀ i, ((U i).card : ℝ) ^ (1 / C) ≤
          leafPotential C (𝒞_sub i) * leafPotential C (ℐ_sub i) :=
        fun i => (h_ih i).choose_spec.choose_spec.2.2
      rcases hU_pure with hU_comp | hU_anti
      · exact combine_leaf_families G W C w_min w_max hC k hk2 U hU_comp
          𝒞_sub ℐ_sub h𝒞_sub hℐ_sub hpot_sub
      · rw [isAnticompleteBlockadeIn_iff_compl] at hU_anti
        have h𝒞_sub' : ∀ i, IsLeafFamily (Gᶜ)ᶜ (U i) w_min w_max (𝒞_sub i) := by
          simpa only [compl_compl] using h𝒞_sub
        have hpot_sub' : ∀ i, ((U i).card : ℝ) ^ (1 / C) ≤
            leafPotential C (ℐ_sub i) * leafPotential C (𝒞_sub i) := by
          intro i
          rw [mul_comm]
          exact hpot_sub i
        obtain ⟨ℐ_tot, 𝒞_tot, hℐ_tot, h𝒞_tot, hpot_tot⟩ :=
          combine_leaf_families Gᶜ W C w_min w_max hC k hk2 U hU_anti
            ℐ_sub 𝒞_sub hℐ_sub h𝒞_sub' hpot_sub'
        rw [compl_compl] at h𝒞_tot
        exact ⟨𝒞_tot, ℐ_tot, h𝒞_tot, hℐ_tot, by rw [mul_comm]; exact hpot_tot⟩

/--
Extracting an $\varepsilon$-sparse subgraph in $Hᶜ$ of size $\ge \varepsilon^{3C}|S_0|$ from a
leaf family $\mathcal{A}$ in $H$ with $\Phi_C(\mathcal{A}) \ge |S_0|^{\frac{1}{2C}}$.
-/
theorem exists_sparse_compl_of_leaf_family (H : SimpleGraph V) (S₀ : Finset V) (C ε : ℝ)
    (hC : 1 ≤ C) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 4) (hS₀ : ε ^ (-3 * C) ≤ (S₀.card : ℝ))
    (𝒜 : Finset (Finset V))
    (h𝒜 : IsLeafFamily H S₀ (ε ^ (3 * C) * (S₀.card : ℝ)) (ε ^ (2 * C) * (S₀.card : ℝ)) 𝒜)
    (hpot : (S₀.card : ℝ) ^ (1 / (2 * C)) ≤ leafPotential C 𝒜) :
    ∃ S ⊆ S₀, IsEpsSparseOn Hᶜ S ε ∧ ε ^ (3 * C) * (S₀.card : ℝ) ≤ (S.card : ℝ) := by
  classical
  let w_min := ε ^ (3 * C) * (S₀.card : ℝ)
  let w_max := ε ^ (2 * C) * (S₀.card : ℝ)
  have hw_min_ge_one : 1 ≤ w_min := by
    dsimp [w_min]
    calc (1 : ℝ)
      _ = ε ^ (3 * C) * ε ^ (-3 * C) := by
        rw [← Real.rpow_add hε0]
        simp
      _ ≤ ε ^ (3 * C) * (S₀.card : ℝ) :=
        mul_le_mul_of_nonneg_left hS₀ (by positivity)
  have hS₀_pos : (0 : ℝ) < (S₀.card : ℝ) := lt_of_lt_of_le (by positivity) hS₀
  have hC_pos : 0 < C := by linarith
  have hleaf_bound : ∀ L ∈ 𝒜,
      (L.card : ℝ) ^ (1 / (2 * C)) ≤ ε * (S₀.card : ℝ) ^ (1 / (2 * C)) := by
    intro L hL
    have hL_le : (L.card : ℝ) ≤ ε ^ (2 * C) * (S₀.card : ℝ) := h𝒜.card_le L hL
    calc (L.card : ℝ) ^ (1 / (2 * C))
      _ ≤ (ε ^ (2 * C) * (S₀.card : ℝ)) ^ (1 / (2 * C)) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hL_le (by positivity)
      _ = (ε ^ (2 * C)) ^ (1 / (2 * C)) * (S₀.card : ℝ) ^ (1 / (2 * C)) :=
        Real.mul_rpow (by positivity) hS₀_pos.le
      _ = ε * (S₀.card : ℝ) ^ (1 / (2 * C)) := by
        rw [← Real.rpow_mul hε0.le, mul_one_div_cancel (by positivity), Real.rpow_one]
  have h𝒜_card_ge : 1 ≤ (𝒜.card : ℝ) * ε := by
    have hsum_le : leafPotential C 𝒜 ≤ (𝒜.card : ℝ) * (ε * (S₀.card : ℝ) ^ (1 / (2 * C))) := by
      unfold leafPotential
      calc ∑ L ∈ 𝒜, (L.card : ℝ) ^ (1 / (2 * C))
        _ ≤ ∑ _L ∈ 𝒜, ε * (S₀.card : ℝ) ^ (1 / (2 * C)) := sum_le_sum hleaf_bound
        _ = (𝒜.card : ℝ) * (ε * (S₀.card : ℝ) ^ (1 / (2 * C))) := by
          rw [sum_const, nsmul_eq_mul]
    have h1 : (S₀.card : ℝ) ^ (1 / (2 * C)) ≤
        ((𝒜.card : ℝ) * ε) * (S₀.card : ℝ) ^ (1 / (2 * C)) := by
      linarith
    have hpow_pos : 0 < (S₀.card : ℝ) ^ (1 / (2 * C)) := by positivity
    nlinarith
  let w : ℕ := ⌈w_min⌉₊
  have hw_ge_w_min : w_min ≤ (w : ℝ) := Nat.le_ceil w_min
  have hw_le_L : ∀ L ∈ 𝒜, w ≤ L.card := fun L hL => Nat.ceil_le.mpr (h𝒜.card_ge L hL)
  let subL : Finset V → Finset V := fun L =>
    if h : w ≤ L.card then (exists_subset_card_eq h).choose else L
  have hsubL_sub : ∀ L ∈ 𝒜, subL L ⊆ L := by
    intro L hL
    dsimp [subL]
    rw [dif_pos (hw_le_L L hL)]
    exact (exists_subset_card_eq (hw_le_L L hL)).choose_spec.1
  have hsubL_card : ∀ L ∈ 𝒜, (subL L).card = w := by
    intro L hL
    dsimp [subL]
    rw [dif_pos (hw_le_L L hL)]
    exact (exists_subset_card_eq (hw_le_L L hL)).choose_spec.2
  have hsubL_disj : ∀ L₁ ∈ 𝒜, ∀ L₂ ∈ 𝒜, L₁ ≠ L₂ → Disjoint (subL L₁) (subL L₂) :=
    fun L₁ hL₁ L₂ hL₂ hne =>
      Disjoint.mono (hsubL_sub L₁ hL₁) (hsubL_sub L₂ hL₂) (h𝒜.pairwise_disjoint L₁ hL₁ L₂ hL₂ hne)
  let S := 𝒜.biUnion subL
  have hSS₀ : S ⊆ S₀ := by
    intro v hv
    obtain ⟨L, hL, hvL⟩ := mem_biUnion.mp hv
    exact h𝒜.subset_ambient L hL (hsubL_sub L hL hvL)
  have hS_card_nat : S.card = 𝒜.card * w := by
    dsimp [S]
    rw [card_biUnion hsubL_disj]
    calc ∑ L ∈ 𝒜, (subL L).card
      _ = ∑ _L ∈ 𝒜, w := sum_congr rfl hsubL_card
      _ = 𝒜.card * w := by rw [sum_const, smul_eq_mul]
  have hS_card_real : (S.card : ℝ) = (𝒜.card : ℝ) * (w : ℝ) := by exact_mod_cast hS_card_nat
  have h𝒜_ge_one : (1 : ℝ) ≤ (𝒜.card : ℝ) := by
    have : 1 ≤ 𝒜.card := card_pos.mpr h𝒜.nonempty_family
    exact_mod_cast this
  refine ⟨S, hSS₀, ?_, ?_⟩
  · intro v hv
    obtain ⟨L₀, hL₀, hvL₀⟩ := mem_biUnion.mp hv
    have hneigh_sub : neighborFinsetIn Hᶜ v S ⊆ subL L₀ := by
      intro u hu
      rw [mem_neighborFinsetIn] at hu
      obtain ⟨huS, hadj_c⟩ := hu
      obtain ⟨L₁, hL₁, huL₁⟩ := mem_biUnion.mp huS
      by_cases hL₁₀ : L₁ = L₀
      · subst hL₁₀
        exact huL₁
      · exfalso
        have hadj_H : H.Adj v u :=
          h𝒜.pairwise_complete L₀ hL₀ L₁ hL₁ (Ne.symm hL₁₀)
            v (hsubL_sub L₀ hL₀ hvL₀) u (hsubL_sub L₁ hL₁ huL₁)
        rw [SimpleGraph.compl_adj] at hadj_c
        exact hadj_c.2 hadj_H
    have hdeg_le_w : ((neighborFinsetIn Hᶜ v S).card : ℝ) ≤ (w : ℝ) := by
      have : (neighborFinsetIn Hᶜ v S).card ≤ (subL L₀).card := card_le_card hneigh_sub
      rw [hsubL_card L₀ hL₀] at this
      exact_mod_cast this
    calc ((neighborFinsetIn Hᶜ v S).card : ℝ)
      _ ≤ 1 * (w : ℝ) := by linarith
      _ ≤ ((𝒜.card : ℝ) * ε) * (w : ℝ) :=
        mul_le_mul_of_nonneg_right h𝒜_card_ge (Nat.cast_nonneg w)
      _ = ε * ((𝒜.card : ℝ) * (w : ℝ)) := by ring
      _ = ε * (S.card : ℝ) := by rw [hS_card_real]
  · rw [hS_card_real]
    calc w_min
      _ = 1 * w_min := (one_mul w_min).symm
      _ ≤ (𝒜.card : ℝ) * (w : ℝ) :=
        mul_le_mul h𝒜_ge_one hw_ge_w_min (by linarith) (Nat.cast_nonneg _)

/--
**Lemma 2.9 (`lem:blockade-to-rest`, Blockade-to-Restricted-Subgraph Lemma)**:
Let $C \ge 1$ and $\varepsilon \in (0, 1/4]$. Let $S_0 \subseteq V$ with
$|S_0| \ge \varepsilon^{-3C}$ such that every $F \subseteq S_0$ with $|F| \ge \varepsilon^{2C}|S_0|$
contains a complete or anticomplete $(k, |F|/k^C)$-blockade for some integer
$k \in [2, \varepsilon^{-1}]$. Then $S_0$ contains an $\varepsilon$-restricted subset
$S \subseteq S_0$ of cardinality $|S| \ge \varepsilon^{3C}|S_0|$.
-/
theorem blockade_to_restricted_subgraph (G : SimpleGraph V) (S₀ : Finset V) (C ε : ℝ)
    (hC : 1 ≤ C) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 4) (hS₀ : ε ^ (-3 * C) ≤ (S₀.card : ℝ))
    (hblock : ∀ F ⊆ S₀, ε ^ (2 * C) * (S₀.card : ℝ) ≤ (F.card : ℝ) →
      ∃ k : ℕ, 2 ≤ k ∧ (k : ℝ) ≤ ε⁻¹ ∧
        ∃ B : Fin k → Finset V,
          IsCompleteBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ C) B ∨
          IsAnticompleteBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ C) B) :
    ∃ S ⊆ S₀, IsEpsRestrictedOn G S ε ∧ ε ^ (3 * C) * (S₀.card : ℝ) ≤ (S.card : ℝ) := by
  have hS₀_pos : (0 : ℝ) < (S₀.card : ℝ) := lt_of_lt_of_le (by positivity) hS₀
  have hS₀_min : ε ^ (3 * C) * (S₀.card : ℝ) ≤ (S₀.card : ℝ) := by
    have : ε ^ (3 * C) ≤ 1 := Real.rpow_le_one hε0.le (by linarith) (by linarith)
    nlinarith
  obtain ⟨𝒞, ℐ, h𝒞, hℐ, hpot⟩ :=
    exists_cograph_leaf_families G S₀ C ε hC hε0 hε1 hS₀ hblock S₀ Subset.rfl hS₀_min
  have hpot_sq :
      ((S₀.card : ℝ) ^ (1 / (2 * C))) * ((S₀.card : ℝ) ^ (1 / (2 * C))) ≤
        leafPotential C 𝒞 * leafPotential C ℐ := by
    rw [← Real.rpow_add hS₀_pos]
    have hC_ne : C ≠ 0 := by linarith
    have : 1 / (2 * C) + 1 / (2 * C) = 1 / C := by
      field_simp
      ring
    rwa [this]
  by_cases h𝒞_ge : (S₀.card : ℝ) ^ (1 / (2 * C)) ≤ leafPotential C 𝒞
  · obtain ⟨S, hSS₀, hsparse_c, hS_card⟩ :=
      exists_sparse_compl_of_leaf_family G S₀ C ε hC hε0 hε1 hS₀ 𝒞 h𝒞 h𝒞_ge
    exact ⟨S, hSS₀, Or.inr hsparse_c, hS_card⟩
  · push_neg at h𝒞_ge
    have hℐ_ge : (S₀.card : ℝ) ^ (1 / (2 * C)) ≤ leafPotential C ℐ := by
      by_contra! hℐ_lt
      have : leafPotential C 𝒞 * leafPotential C ℐ <
          ((S₀.card : ℝ) ^ (1 / (2 * C))) * ((S₀.card : ℝ) ^ (1 / (2 * C))) :=
        mul_lt_mul'' h𝒞_ge hℐ_lt (leafPotential_nonneg C 𝒞) (leafPotential_nonneg C ℐ)
      linarith
    obtain ⟨S, hSS₀, hsparse_cc, hS_card⟩ :=
      exists_sparse_compl_of_leaf_family Gᶜ S₀ C ε hC hε0 hε1 hS₀ ℐ hℐ hℐ_ge
    rw [compl_compl] at hsparse_cc
    exact ⟨S, hSS₀, Or.inl hsparse_cc, hS_card⟩

/-!
### Part 5: Stage 2 Reduction (`prop:master-reduction`, Proposition 5.4)
-/

/--
Picking one vertex from each block of a complete $(k, w)$-blockade yields a clique of size $k$,
so $\omega(G) \ge k$.
-/
theorem cliqueNum_ge_of_isCompleteBlockadeIn (G : SimpleGraph V) (S : Finset V) (k : ℕ) (w : ℝ)
    (B : Fin k → Finset V) (hB : IsCompleteBlockadeIn G S k w B) :
    k ≤ G.cliqueNum := by
  classical
  let f : Fin k → V := fun i => (hB.1.nonempty_blocks i).choose
  have hf : ∀ i : Fin k, f i ∈ B i := fun i => (hB.1.nonempty_blocks i).choose_spec
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    exact Finset.disjoint_left.mp (hB.1.pairwise_disjoint i j hne) (hf i) (hij ▸ hf j)
  let K := (Finset.univ : Finset (Fin k)).image f
  have hK_card : K.card = k := by
    rw [card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
  have hK_clique : G.IsClique (K : Set V) := by
    intro x hx y hy hxy
    simp only [K, coe_image, coe_univ, Set.image_univ, Set.mem_range] at hx hy
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := hy
    have hij : i ≠ j := fun h => hxy (congrArg f h)
    exact hB.2 i j hij (f i) (hf i) (f j) (hf j)
  rw [← hK_card]
  exact hK_clique.card_le_cliqueNum

/--
Picking one vertex from each block of an anticomplete $(k, w)$-blockade yields an independent set
of size $k$, so $\alpha(G) \ge k$.
-/
theorem indepNum_ge_of_isAnticompleteBlockadeIn (G : SimpleGraph V) (S : Finset V) (k : ℕ) (w : ℝ)
    (B : Fin k → Finset V) (hB : IsAnticompleteBlockadeIn G S k w B) :
    k ≤ G.indepNum := by
  rw [isAnticompleteBlockadeIn_iff_compl] at hB
  have h := cliqueNum_ge_of_isCompleteBlockadeIn Gᶜ S k w B hB
  rwa [cliqueNum_compl] at h

/--
Any complete or anticomplete $(k, w)$-blockade in $G$ witnesses $\kappa(G) \ge k$.
-/
theorem kappa_ge_of_pure_blockade (G : SimpleGraph V) (S : Finset V) (k : ℕ) (w : ℝ)
    (B : Fin k → Finset V)
    (hB : IsCompleteBlockadeIn G S k w B ∨ IsAnticompleteBlockadeIn G S k w B) :
    (k : ℝ) ≤ (kappa G : ℝ) := by
  rcases hB with hcomp | hanti
  · have := le_trans (cliqueNum_ge_of_isCompleteBlockadeIn G S k w B hcomp) (cliqueNum_le_kappa G)
    exact_mod_cast this
  · have := le_trans (indepNum_ge_of_isAnticompleteBlockadeIn G S k w B hanti) (indepNum_le_kappa G)
    exact_mod_cast this

/-! #### Step 1a: Equal-Size Subset Pre-Sampling (lines 553–557) -/

/-- The pair $(A, B)$ is complete or weakly $x$-sparse in $G$. -/
def IsCompleteOrWeaklyXSparsePair (G : SimpleGraph V) (A B : Finset V) (x : ℝ) : Prop :=
  IsCompletePair G A B ∨ IsWeaklySparsePair G A B x

theorem crossEdgeCount_eq_sum_left (G : SimpleGraph V) (A B : Finset V) :
    crossEdgeCount G A B = ∑ u ∈ A, (neighborFinsetIn G u B).card :=
  rfl

private theorem crossEdgeCount_comm (G : SimpleGraph V) (A B : Finset V) :
    crossEdgeCount G A B = crossEdgeCount G B A := by
  classical
  unfold crossEdgeCount neighborFinsetIn
  simp only [card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  refine sum_congr rfl (fun v _ => sum_congr rfl (fun u _ => ?_))
  rw [adj_comm]

/--
Deterministic subset-shrinking lemma: for any finite set $A$, non-negative weight function
$w : \alpha \to \mathbb{R}$, and $m \le |A|$, there exists a subset $X \subseteq A$ with $|X| = m$
whose average weight does not exceed the average weight of $A$:
$|A| \sum_{u \in X} w(u) \le m \sum_{u \in A} w(u)$.
-/
theorem exists_subset_card_eq_sum_le {α : Type*} [DecidableEq α] (A : Finset α)
    (w : α → ℝ) (hw : ∀ a ∈ A, 0 ≤ w a) (m : ℕ) (hm : m ≤ A.card) :
    ∃ X ⊆ A, X.card = m ∧ (A.card : ℝ) * (∑ u ∈ X, w u) ≤ (m : ℝ) * (∑ u ∈ A, w u) := by
  induction hn : A.card using Nat.strong_induction_on generalizing A with
  | _ n ih =>
    subst hn
    rcases Nat.eq_zero_or_pos m with rfl | hm_pos
    · refine ⟨∅, empty_subset A, card_empty, ?_⟩
      simp
    · by_cases hmeq : m = A.card
      · refine ⟨A, Subset.rfl, hmeq.symm, ?_⟩
        rw [hmeq]
      · have hmlt : m < A.card := lt_of_le_of_ne hm hmeq
        have hA_ne : A.Nonempty := card_pos.mp (lt_trans hm_pos hmlt)
        obtain ⟨a₀, ha₀, ha₀_max⟩ := exists_max_image A w hA_ne
        let A' := A.erase a₀
        have hA'A : A' ⊆ A := erase_subset a₀ A
        have hA'_card_add : A'.card + 1 = A.card := card_erase_add_one ha₀
        have hm_le_A' : m ≤ A'.card := by omega
        have hA'_lt : A'.card < A.card := by omega
        have hA'_pos : (0 : ℝ) < (A'.card : ℝ) := by
          have : 0 < A'.card := lt_of_lt_of_le hm_pos hm_le_A'
          exact_mod_cast this
        obtain ⟨X, hXA', hX_card, hX_sum⟩ :=
          ih A'.card hA'_lt A' (fun a ha => hw a (hA'A ha)) hm_le_A' rfl
        have hsum_A : ∑ u ∈ A, w u = (∑ u ∈ A', w u) + w a₀ := by
          rw [← insert_erase ha₀, sum_insert (notMem_erase a₀ A), add_comm]
        have hcard_A : (A.card : ℝ) = (A'.card : ℝ) + 1 := by
          exact_mod_cast hA'_card_add.symm
        have hsum_A'_le : ∑ u ∈ A', w u ≤ (A'.card : ℝ) * w a₀ := by
          calc ∑ u ∈ A', w u
            _ ≤ ∑ _u ∈ A', w a₀ := sum_le_sum (fun u hu => ha₀_max u (hA'A hu))
            _ = (A'.card : ℝ) * w a₀ := by rw [sum_const, nsmul_eq_mul]
        have hstep : (A.card : ℝ) * (∑ u ∈ A', w u) ≤ (A'.card : ℝ) * (∑ u ∈ A, w u) := by
          rw [hcard_A, hsum_A]
          nlinarith
        have hmul : (A'.card : ℝ) * ((A.card : ℝ) * (∑ u ∈ X, w u)) ≤
            (A'.card : ℝ) * ((m : ℝ) * (∑ u ∈ A, w u)) := by
          calc (A'.card : ℝ) * ((A.card : ℝ) * (∑ u ∈ X, w u))
            _ = (A.card : ℝ) * ((A'.card : ℝ) * (∑ u ∈ X, w u)) := by ring
            _ ≤ (A.card : ℝ) * ((m : ℝ) * (∑ u ∈ A', w u)) :=
              mul_le_mul_of_nonneg_left hX_sum (Nat.cast_nonneg _)
            _ = (m : ℝ) * ((A.card : ℝ) * (∑ u ∈ A', w u)) := by ring
            _ ≤ (m : ℝ) * ((A'.card : ℝ) * (∑ u ∈ A, w u)) :=
              mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg _)
            _ = (A'.card : ℝ) * ((m : ℝ) * (∑ u ∈ A, w u)) := by ring
        exact ⟨X, Subset.trans hXA' hA'A, hX_card, le_of_mul_le_mul_left hmul hA'_pos⟩

/--
One-block shrinking step for Step 1a: shrinking block $A_r$ to a subset $X_r \subseteq A_r$ of size
$m$ multiplies the sparse cross-edge density bound for pairs involving $r$ by at most $\ell$.
-/
theorem shrink_one_block (G : SimpleGraph V) (ℓ m : ℕ) (hm : 1 ≤ m)
    (A : Fin ℓ → Finset V) (hA_card : ∀ i : Fin ℓ, m ≤ (A i).card)
    (c : Fin ℓ → Fin ℓ → ℝ) (hc_pos : ∀ i j, 0 < c i j) (hc_symm : ∀ i j, c i j = c j i)
    (hpairs : ∀ i j : Fin ℓ, i ≠ j →
      IsCompletePair G (A i) (A j) ∨
      (crossEdgeCount G (A i) (A j) : ℝ) ≤ c i j * ((A i).card : ℝ) * ((A j).card : ℝ))
    (r : Fin ℓ) :
    ∃ X_r ⊆ A r, X_r.card = m ∧
      ∀ i j : Fin ℓ, i ≠ j →
        let A' := fun t => if t = r then X_r else A t
        let c' := fun s t => if s = r ∨ t = r then (ℓ : ℝ) * c s t else c s t
        IsCompletePair G (A' i) (A' j) ∨
        (crossEdgeCount G (A' i) (A' j) : ℝ) ≤ c' i j * ((A' i).card : ℝ) * ((A' j).card : ℝ) := by
  classical
  have hAr_pos : (0 : ℝ) < ((A r).card : ℝ) := by
    have : 0 < (A r).card := lt_of_lt_of_le (by omega) (hA_card r)
    exact_mod_cast this
  have hAj_pos : ∀ j : Fin ℓ, (0 : ℝ) < ((A j).card : ℝ) := by
    intro j
    have : 0 < (A j).card := lt_of_lt_of_le (by omega) (hA_card j)
    exact_mod_cast this
  let J := (Finset.univ : Finset (Fin ℓ)).filter (fun j =>
    r ≠ j ∧ (crossEdgeCount G (A r) (A j) : ℝ) ≤ c r j * ((A r).card : ℝ) * ((A j).card : ℝ))
  let denom : Fin ℓ → ℝ := fun j => c r j * ((A r).card : ℝ) * ((A j).card : ℝ)
  have hdenom_pos : ∀ j : Fin ℓ, 0 < denom j := by
    intro j
    exact mul_pos (mul_pos (hc_pos r j) hAr_pos) (hAj_pos j)
  let f : Fin ℓ → V → ℝ := fun j u => ((neighborFinsetIn G u (A j)).card : ℝ) * (denom j)⁻¹
  have hf_nonneg : ∀ j u, 0 ≤ f j u :=
    fun j u => mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.mpr (hdenom_pos j).le)
  let w : V → ℝ := fun u => ∑ j ∈ J, f j u
  have hw_nonneg : ∀ u ∈ A r, 0 ≤ w u := fun u _ => sum_nonneg (fun j _ => hf_nonneg j u)
  have hsum_f_le_one : ∀ j ∈ J, ∑ u ∈ A r, f j u ≤ 1 := by
    intro j hj
    simp only [J, mem_filter, mem_univ, true_and] at hj
    dsimp [f]
    rw [← sum_mul]
    have hsum_eq : (∑ u ∈ A r, ((neighborFinsetIn G u (A j)).card : ℝ)) =
        (crossEdgeCount G (A r) (A j) : ℝ) := by
      exact_mod_cast (crossEdgeCount_eq_sum_left G (A r) (A j)).symm
    rw [hsum_eq]
    have h1 := mul_le_mul_of_nonneg_right hj.2 (inv_nonneg.mpr (hdenom_pos j).le)
    rwa [mul_inv_cancel₀ (hdenom_pos j).ne'] at h1
  have hsum_w_le : ∑ u ∈ A r, w u ≤ (ℓ : ℝ) := by
    dsimp [w]
    rw [sum_comm]
    calc ∑ j ∈ J, ∑ u ∈ A r, f j u
      _ ≤ ∑ _j ∈ J, (1 : ℝ) := sum_le_sum hsum_f_le_one
      _ = (J.card : ℝ) := by rw [sum_const, nsmul_eq_mul, mul_one]
      _ ≤ (ℓ : ℝ) := by
        have : J.card ≤ ℓ := by
          calc J.card
            _ ≤ (Finset.univ : Finset (Fin ℓ)).card := card_filter_le _ _
            _ = ℓ := by rw [card_univ, Fintype.card_fin]
        exact_mod_cast this
  obtain ⟨X_r, hXr_sub, hXr_card, hXr_sum⟩ :=
    exists_subset_card_eq_sum_le (A r) w hw_nonneg m (hA_card r)
  have hXr_bound : ∀ j ∈ J,
      (crossEdgeCount G X_r (A j) : ℝ) ≤ ((ℓ : ℝ) * c r j) * (m : ℝ) * ((A j).card : ℝ) := by
    intro j hj
    have hj_le_w : ∑ u ∈ X_r, f j u ≤ ∑ u ∈ X_r, w u := by
      dsimp [w]
      rw [sum_comm]
      exact single_le_sum (fun j' _ => sum_nonneg (fun u _ => hf_nonneg j' u)) hj
    have hsum_Xr : ∑ u ∈ X_r, f j u = (crossEdgeCount G X_r (A j) : ℝ) * (denom j)⁻¹ := by
      dsimp [f]
      rw [← sum_mul]
      congr 1
      exact_mod_cast (crossEdgeCount_eq_sum_left G X_r (A j)).symm
    have h1 : ((A r).card : ℝ) * ((crossEdgeCount G X_r (A j) : ℝ) * (denom j)⁻¹) ≤
        (m : ℝ) * (ℓ : ℝ) := by
      calc ((A r).card : ℝ) * ((crossEdgeCount G X_r (A j) : ℝ) * (denom j)⁻¹)
        _ = ((A r).card : ℝ) * (∑ u ∈ X_r, f j u) := by rw [hsum_Xr]
        _ ≤ ((A r).card : ℝ) * (∑ u ∈ X_r, w u) :=
          mul_le_mul_of_nonneg_left hj_le_w hAr_pos.le
        _ ≤ (m : ℝ) * (∑ u ∈ A r, w u) := hXr_sum
        _ ≤ (m : ℝ) * (ℓ : ℝ) := mul_le_mul_of_nonneg_left hsum_w_le (Nat.cast_nonneg _)
    have hdenom_ne : denom j ≠ 0 := (hdenom_pos j).ne'
    have h2 : ((A r).card : ℝ) * (crossEdgeCount G X_r (A j) : ℝ) ≤
        ((m : ℝ) * (ℓ : ℝ)) * denom j := by
      have hmul := mul_le_mul_of_nonneg_right h1 (hdenom_pos j).le
      have hlhs : ((A r).card : ℝ) * ((crossEdgeCount G X_r (A j) : ℝ) * (denom j)⁻¹) * denom j =
          ((A r).card : ℝ) * (crossEdgeCount G X_r (A j) : ℝ) * ((denom j)⁻¹ * denom j) := by ring
      rw [hlhs, inv_mul_cancel₀ hdenom_ne, mul_one] at hmul
      exact hmul
    have h3 : ((A r).card : ℝ) * (crossEdgeCount G X_r (A j) : ℝ) ≤
        ((A r).card : ℝ) * (((ℓ : ℝ) * c r j) * (m : ℝ) * ((A j).card : ℝ)) := by
      calc ((A r).card : ℝ) * (crossEdgeCount G X_r (A j) : ℝ)
        _ ≤ ((m : ℝ) * (ℓ : ℝ)) * (c r j * ((A r).card : ℝ) * ((A j).card : ℝ)) := h2
        _ = ((A r).card : ℝ) * (((ℓ : ℝ) * c r j) * (m : ℝ) * ((A j).card : ℝ)) := by ring
    exact le_of_mul_le_mul_left h3 hAr_pos
  refine ⟨X_r, hXr_sub, hXr_card, ?_⟩
  intro i j hij
  dsimp only
  by_cases hir : i = r
  · subst hir
    have hjr : j ≠ i := hij.symm
    rw [if_pos rfl, if_neg hjr, if_pos (Or.inl rfl)]
    rcases hpairs i j hij with hcomp | hsparse
    · exact Or.inl (hcomp.mono hXr_sub Subset.rfl)
    · right
      have hjJ : j ∈ J := mem_filter.mpr ⟨mem_univ j, hij, hsparse⟩
      rw [hXr_card]
      exact hXr_bound j hjJ
  · by_cases hjr : j = r
    · subst hjr
      rw [if_neg hir, if_pos rfl, if_pos (Or.inr rfl)]
      rcases hpairs j i hij.symm with hcomp | hsparse
      · exact Or.inl (hcomp.mono hXr_sub Subset.rfl).symm
      · right
        have hiJ : i ∈ J := mem_filter.mpr ⟨mem_univ i, hij.symm, hsparse⟩
        have hb := hXr_bound i hiJ
        rw [crossEdgeCount_comm, hXr_card, hc_symm i j]
        linarith
    · have hor : ¬(i = r ∨ j = r) := not_or.mpr ⟨hir, hjr⟩
      rw [if_neg hir, if_neg hjr, if_neg hor]
      exact hpairs i j hij

/--
**Step 1a (`step1a_equal_size_presampling`, Proposition 5.4 of `FMBV4-016_readable.tex`)**:
Given an $(\ell, m)$-blockade $A$ in $F$ with $\ell \le \varepsilon^{-1}$ whose block pairs are
complete or weakly $\varepsilon^{c_2}$-sparse, there exist equal-sized subsets $X_i \subseteq A_i$
with $|X_i| = m$ forming an $(\ell, m)$-blockade in $F$ whose block pairs are complete or weakly
$\varepsilon^{c_2 - 2}$-sparse.
-/
theorem step1a_equal_size_presampling (G : SimpleGraph V) (F : Finset V) (ℓ m : ℕ) (ε c₂ : ℝ)
    (hℓ : 2 ≤ ℓ) (hℓ_le : (ℓ : ℝ) ≤ ε⁻¹) (hm : 1 ≤ m) (hε0 : 0 < ε)
    (A : Fin ℓ → Finset V) (hA : IsBlockadeIn G F ℓ (m : ℝ) A)
    (hpairs : ∀ i j : Fin ℓ, i ≠ j → IsCompleteOrWeaklyXSparsePair G (A i) (A j) (ε ^ c₂)) :
    ∃ X : Fin ℓ → Finset V,
      (∀ i, X i ⊆ A i) ∧
      (∀ i, (X i).card = m) ∧
      IsBlockadeIn G F ℓ (m : ℝ) X ∧
      (∀ i j : Fin ℓ, i ≠ j → IsCompleteOrWeaklyXSparsePair G (X i) (X j) (ε ^ (c₂ - 2))) := by
  let coeff (k : ℕ) (i j : Fin ℓ) : ℝ :=
    (if i.val < k then (ℓ : ℝ) else 1) * (if j.val < k then (ℓ : ℝ) else 1) * (ε ^ c₂)
  have hcoeff_pos : ∀ k i j, 0 < coeff k i j := by
    intro k i j
    dsimp [coeff]
    have h1 : (0 : ℝ) < if i.val < k then (ℓ : ℝ) else 1 := by split_ifs <;> positivity
    have h2 : (0 : ℝ) < if j.val < k then (ℓ : ℝ) else 1 := by split_ifs <;> positivity
    positivity
  have hcoeff_symm : ∀ k i j, coeff k i j = coeff k j i := by
    intro k i j
    dsimp [coeff]
    ring
  have h_ind : ∀ k : ℕ, k ≤ ℓ →
      ∃ X : Fin ℓ → Finset V,
        (∀ i, X i ⊆ A i) ∧
        (∀ i, m ≤ (X i).card) ∧
        (∀ i : Fin ℓ, i.val < k → (X i).card = m) ∧
        (∀ i j : Fin ℓ, i ≠ j →
          IsCompletePair G (X i) (X j) ∨
          (crossEdgeCount G (X i) (X j) : ℝ) ≤ coeff k i j * ((X i).card : ℝ) * ((X j).card : ℝ)) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨A, fun _ => Subset.rfl, ?_, ?_, ?_⟩
      · intro i
        exact_mod_cast hA.width_ge i
      · intro i hi
        omega
      · intro i j hij
        have h := hpairs i j hij
        dsimp [coeff, IsCompleteOrWeaklyXSparsePair, IsWeaklySparsePair] at h ⊢
        simpa using h
    | succ k ih =>
      intro hk
      obtain ⟨X, hX_sub, hX_ge, hX_eq, hX_pairs⟩ := ih (by omega)
      let r : Fin ℓ := ⟨k, hk⟩
      obtain ⟨X_r, hXr_sub, hXr_card, hXr_pairs⟩ :=
        shrink_one_block G ℓ m hm X hX_ge (coeff k) (hcoeff_pos k) (hcoeff_symm k) hX_pairs r
      let X' : Fin ℓ → Finset V := fun i => if i = r then X_r else X i
      refine ⟨X', ?_, ?_, ?_, ?_⟩
      · intro i
        dsimp [X']
        split_ifs with hir
        · subst hir
          exact Subset.trans hXr_sub (hX_sub r)
        · exact hX_sub i
      · intro i
        dsimp [X']
        split_ifs with hir
        · omega
        · exact hX_ge i
      · intro i hi
        dsimp [X']
        split_ifs with hir
        · exact hXr_card
        · have hik : i.val < k := by
            have : i.val ≠ k := fun h => hir (Fin.ext h)
            omega
          exact hX_eq i hik
      · intro i j hij
        have hp := hXr_pairs i j hij
        dsimp only at hp
        have hcoeff_step :
            (if i = r ∨ j = r then (ℓ : ℝ) * coeff k i j else coeff k i j) = coeff (k + 1) i j := by
          have hij_val : i.val ≠ j.val := fun h => hij (Fin.ext h)
          dsimp [coeff]
          by_cases hir : i = r
          · have hik : i.val = k := congrArg Fin.val hir
            have hjk : j.val ≠ k := fun h => hij_val (hik.trans h.symm)
            have hj_lt : (j.val < k + 1) ↔ (j.val < k) := by omega
            rw [if_pos (Or.inl hir), if_neg (by omega : ¬i.val < k),
              if_pos (by omega : i.val < k + 1)]
            simp only [hj_lt]
            ring
          · have hik : i.val ≠ k := fun h => hir (Fin.ext h)
            by_cases hjr : j = r
            · have hjk : j.val = k := congrArg Fin.val hjr
              have hi_lt : (i.val < k + 1) ↔ (i.val < k) := by omega
              rw [if_pos (Or.inr hjr), if_neg (by omega : ¬j.val < k),
                if_pos (by omega : j.val < k + 1)]
              simp only [hi_lt]
              ring
            · have hjk : j.val ≠ k := fun h => hjr (Fin.ext h)
              have hor : ¬(i = r ∨ j = r) := not_or.mpr ⟨hir, hjr⟩
              have hi_lt : (i.val < k + 1) ↔ (i.val < k) := by omega
              have hj_lt : (j.val < k + 1) ↔ (j.val < k) := by omega
              rw [if_neg hor]
              simp only [hi_lt, hj_lt]
        rwa [hcoeff_step] at hp
  obtain ⟨X, hX_sub, _, hX_eq, hX_pairs⟩ := h_ind ℓ le_rfl
  have hX_card : ∀ i : Fin ℓ, (X i).card = m := fun i => hX_eq i i.isLt
  have hX_block : IsBlockadeIn G F ℓ (m : ℝ) X := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      exact Subset.trans (hX_sub i) (hA.subset_ambient i)
    · intro i
      exact card_pos.mp (by rw [hX_card i]; omega)
    · intro i j hij
      exact Disjoint.mono (hX_sub i) (hX_sub j) (hA.pairwise_disjoint i j hij)
    · intro i
      rw [hX_card i]
  refine ⟨X, hX_sub, hX_card, hX_block, ?_⟩
  intro i j hij
  rcases hX_pairs i j hij with hcomp | hsparse
  · exact Or.inl hcomp
  · right
    have hcoeff_ℓ : coeff ℓ i j ≤ ε ^ (c₂ - 2) := by
      dsimp [coeff]
      rw [if_pos i.isLt, if_pos j.isLt]
      have hℓ_sq : (ℓ : ℝ) * (ℓ : ℝ) ≤ ε⁻¹ * ε⁻¹ :=
        mul_le_mul hℓ_le hℓ_le (by positivity) (by positivity)
      have hε_pow : ε⁻¹ * ε⁻¹ * ε ^ c₂ = ε ^ (c₂ - 2) := by
        rw [← Real.rpow_neg_one ε, ← Real.rpow_add hε0, ← Real.rpow_add hε0]
        ring_nf
      rw [← hε_pow]
      exact mul_le_mul_of_nonneg_right hℓ_sq (by positivity)
    unfold IsWeaklySparsePair
    calc (crossEdgeCount G (X i) (X j) : ℝ)
      _ ≤ coeff ℓ i j * ((X i).card : ℝ) * ((X j).card : ℝ) := hsparse
      _ ≤ ε ^ (c₂ - 2) * ((X i).card : ℝ) * ((X j).card : ℝ) := by
        have : 0 ≤ ((X i).card : ℝ) * ((X j).card : ℝ) := by positivity
        nlinarith

/-! #### Step 1b: Weak-to-Strong Sparsity Cleaning (lines 558–562) -/

/--
**Step 1b (`step1b_weak_to_strong_cleaning`, Proposition 5.4 of `FMBV4-016_readable.tex`)**:
Given equal-sized blocks $X_1, \dots, X_\ell \subseteq F$ with $|X_i| = m \ge 2$, $\ell \le \varepsilon^{-1}$,
and $\varepsilon \in (0, 1/4]$ whose pairs are complete or weakly $\varepsilon^{c_2 - 2}$-sparse,
removing high-degree vertices yields subsets $D_i \subseteq X_i$ with $\frac{1}{2} m \le |D_i| \le m$
such that every distinct pair $(D_i, D_j)$ is complete or $\varepsilon^{c_2 - 5}$-sparse in both
directions (`IsCompleteOrXSparseBlockadeIn`).
-/
theorem step1b_weak_to_strong_cleaning (G : SimpleGraph V) (F : Finset V) (ℓ m : ℕ) (ε c₂ : ℝ)
    (_hℓ : 2 ≤ ℓ) (hℓ_le : (ℓ : ℝ) ≤ ε⁻¹) (hm : 2 ≤ m) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (X : Fin ℓ → Finset V) (hX : IsBlockadeIn G F ℓ (m : ℝ) X) (hX_card : ∀ i, (X i).card = m)
    (hpairs : ∀ i j : Fin ℓ, i ≠ j → IsCompleteOrWeaklyXSparsePair G (X i) (X j) (ε ^ (c₂ - 2))) :
    ∃ D : Fin ℓ → Finset V,
      (∀ i, D i ⊆ X i) ∧
      (∀ i, (1 / 2 : ℝ) * (m : ℝ) ≤ ((D i).card : ℝ) ∧ ((D i).card : ℝ) ≤ (m : ℝ)) ∧
      IsCompleteOrXSparseBlockadeIn G F ℓ ((1 / 2 : ℝ) * (m : ℝ)) (ε ^ (c₂ - 5)) D := by
  classical
  let δ := ε ^ (c₂ - 4)
  have hδ_pos : 0 < δ := by positivity
  let bad (i j : Fin ℓ) : Finset V :=
    if i ≠ j ∧ ¬IsCompletePair G (X i) (X j) then
      (X i).filter (fun u => δ * (m : ℝ) < ((neighborFinsetIn G u (X j)).card : ℝ))
    else ∅
  have hbad_card : ∀ i j : Fin ℓ, ((bad i j).card : ℝ) ≤ ε ^ 2 * (m : ℝ) := by
    intro i j
    dsimp [bad]
    split_ifs with h
    · obtain ⟨hij, hnot_comp⟩ := h
      have hsparse : (crossEdgeCount G (X i) (X j) : ℝ) ≤
          ε ^ (c₂ - 2) * ((X i).card : ℝ) * ((X j).card : ℝ) := by
        rcases hpairs i j hij with hcomp | hsp
        · exact (hnot_comp hcomp).elim
        · exact hsp
      rw [hX_card i, hX_card j] at hsparse
      let B_ij := (X i).filter (fun u => δ * (m : ℝ) < ((neighborFinsetIn G u (X j)).card : ℝ))
      have hmarkov : (B_ij.card : ℝ) * (δ * (m : ℝ)) ≤ (crossEdgeCount G (X i) (X j) : ℝ) := by
        calc (B_ij.card : ℝ) * (δ * (m : ℝ))
          _ = ∑ _u ∈ B_ij, δ * (m : ℝ) := by rw [sum_const, nsmul_eq_mul]
          _ ≤ ∑ u ∈ B_ij, ((neighborFinsetIn G u (X j)).card : ℝ) := by
            refine sum_le_sum (fun u hu => ?_)
            simp only [B_ij, mem_filter] at hu
            exact hu.2.le
          _ ≤ ∑ u ∈ X i, ((neighborFinsetIn G u (X j)).card : ℝ) :=
            sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.cast_nonneg _)
          _ = (crossEdgeCount G (X i) (X j) : ℝ) := by
            exact_mod_cast (crossEdgeCount_eq_sum_left G (X i) (X j)).symm
      have hpow_eq : ε ^ (c₂ - 2) = ε ^ 2 * δ := by
        dsimp [δ]
        rw [← Real.rpow_two, ← Real.rpow_add hε0]
        ring_nf
      have h1 : (B_ij.card : ℝ) * (δ * (m : ℝ)) ≤ (ε ^ 2 * (m : ℝ)) * (δ * (m : ℝ)) := by
        calc (B_ij.card : ℝ) * (δ * (m : ℝ))
          _ ≤ ε ^ (c₂ - 2) * (m : ℝ) * (m : ℝ) := hmarkov.trans hsparse
          _ = (ε ^ 2 * (m : ℝ)) * (δ * (m : ℝ)) := by rw [hpow_eq]; ring
      have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
      exact le_of_mul_le_mul_right h1 (by positivity)
    · simp only [card_empty, Nat.cast_zero]
      positivity
  let D : Fin ℓ → Finset V := fun i => X i \ (Finset.univ : Finset (Fin ℓ)).biUnion (bad i)
  have hD_sub : ∀ i, D i ⊆ X i := fun _ => sdiff_subset
  have hD_bounds : ∀ i, (1 / 2 : ℝ) * (m : ℝ) ≤ ((D i).card : ℝ) ∧ ((D i).card : ℝ) ≤ (m : ℝ) := by
    intro i
    constructor
    · have hbiUnion_le : (((Finset.univ : Finset (Fin ℓ)).biUnion (bad i)).card : ℝ) ≤
          (1 / 2 : ℝ) * (m : ℝ) := by
        have hcard_le_sum : (((Finset.univ : Finset (Fin ℓ)).biUnion (bad i)).card : ℝ) ≤
            ∑ j : Fin ℓ, ((bad i j).card : ℝ) := by
          exact_mod_cast card_biUnion_le
        calc (((Finset.univ : Finset (Fin ℓ)).biUnion (bad i)).card : ℝ)
          _ ≤ ∑ j : Fin ℓ, ((bad i j).card : ℝ) := hcard_le_sum
          _ ≤ ∑ _j : Fin ℓ, ε ^ 2 * (m : ℝ) := sum_le_sum (fun j _ => hbad_card i j)
          _ = (ℓ : ℝ) * (ε ^ 2 * (m : ℝ)) := by
            rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
          _ ≤ ε⁻¹ * (ε ^ 2 * (m : ℝ)) :=
            mul_le_mul_of_nonneg_right hℓ_le (by positivity)
          _ = ε * (m : ℝ) := by
            have h1 : ε⁻¹ * ε ^ 2 = ε := by
              rw [sq, ← mul_assoc, inv_mul_cancel₀ hε0.ne', one_mul]
            rw [← mul_assoc, h1]
          _ ≤ (1 / 2 : ℝ) * (m : ℝ) :=
            mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
      have hsdiff_ge : (X i).card ≤
          (D i).card + ((Finset.univ : Finset (Fin ℓ)).biUnion (bad i)).card :=
        card_le_card_sdiff_add_card
      have hsdiff_real : ((X i).card : ℝ) ≤
          ((D i).card : ℝ) + (((Finset.univ : Finset (Fin ℓ)).biUnion (bad i)).card : ℝ) := by
        exact_mod_cast hsdiff_ge
      rw [hX_card i] at hsdiff_real
      linarith
    · have : (D i).card ≤ (X i).card := card_le_card (hD_sub i)
      rw [hX_card i] at this
      exact_mod_cast this
  have hD_deg : ∀ i j : Fin ℓ, i ≠ j → ¬IsCompletePair G (X i) (X j) →
      ∀ u ∈ D i, ((neighborFinsetIn G u (D j)).card : ℝ) ≤ ε ^ (c₂ - 5) * ((D j).card : ℝ) := by
    intro i j hij hnot_comp u hu
    have hu_not_bad : u ∉ bad i j := by
      simp only [D, mem_sdiff, mem_biUnion, mem_univ, true_and, not_exists] at hu
      exact hu.2 j
    have hu_Xi : u ∈ X i := hD_sub i hu
    have hdeg_Xj : ((neighborFinsetIn G u (X j)).card : ℝ) ≤ δ * (m : ℝ) := by
      by_contra! hgt
      dsimp [bad] at hu_not_bad
      rw [if_pos ⟨hij, hnot_comp⟩, mem_filter] at hu_not_bad
      exact hu_not_bad ⟨hu_Xi, hgt⟩
    have hdeg_Dj_le_Xj : (neighborFinsetIn G u (D j)).card ≤ (neighborFinsetIn G u (X j)).card := by
      apply card_le_card
      intro v hv
      rw [mem_neighborFinsetIn] at hv ⊢
      exact ⟨hD_sub j hv.1, hv.2⟩
    have h2_le_inv : (2 : ℝ) ≤ ε⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) hε0]
      linarith
    have h2δ : 2 * δ ≤ ε ^ (c₂ - 5) := by
      calc 2 * δ
        _ ≤ ε⁻¹ * ε ^ (c₂ - 4) := mul_le_mul_of_nonneg_right h2_le_inv hδ_pos.le
        _ = ε ^ (c₂ - 5) := by
          rw [← Real.rpow_neg_one ε, ← Real.rpow_add hε0]
          ring_nf
    have hDj_ge := (hD_bounds j).1
    calc ((neighborFinsetIn G u (D j)).card : ℝ)
      _ ≤ ((neighborFinsetIn G u (X j)).card : ℝ) := by exact_mod_cast hdeg_Dj_le_Xj
      _ ≤ δ * (m : ℝ) := hdeg_Xj
      _ ≤ (2 * δ) * ((D j).card : ℝ) := by nlinarith
      _ ≤ ε ^ (c₂ - 5) * ((D j).card : ℝ) :=
        mul_le_mul_of_nonneg_right h2δ (Nat.cast_nonneg _)
  refine ⟨D, hD_sub, hD_bounds, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i
    exact Subset.trans (hD_sub i) (hX.subset_ambient i)
  · intro i
    have hpos : (0 : ℝ) < ((D i).card : ℝ) := by
      have hm_pos : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith [(hD_bounds i).1]
    exact card_pos.mp (by exact_mod_cast hpos)
  · intro i j hij
    exact Disjoint.mono (hD_sub i) (hD_sub j) (hX.pairwise_disjoint i j hij)
  · intro i
    exact (hD_bounds i).1
  · intro i j hij
    by_cases hcomp : IsCompletePair G (X i) (X j)
    · exact Or.inl (hcomp.mono (hD_sub i) (hD_sub j))
    · right
      have hnot_symm : ¬IsCompletePair G (X j) (X i) := fun h => hcomp h.symm
      exact ⟨hD_deg j i hij.symm hnot_symm, hD_deg i j hij hcomp⟩

/-! #### Step 1c: Equal-Size Anticonnected Block Pruning (lines 563–567) -/

/--
**Step 1c (`step1c_anticonnected_block_pruning`, Proposition 5.4 of `FMBV4-016_readable.tex`)**:
Given a complete-or-$\varepsilon^{c_2 - 5}$-sparse $(\ell, m/2)$-blockade $D$ in $F$ with
$|D_i| \le m$, $4\ell \le m$, and $\ell \le \varepsilon^{-1}$, either $F$ contains a complete
$(\ell, \frac{m}{2\ell^2})$-blockade, or there exist an integer $w \ge 1$ with
$\frac{m}{2\ell} \le w \le m$ and anticonnected subsets $B_i \subseteq D_i$ of exact size $|B_i| = w$
forming a complete-or-$\varepsilon^{c_2 - 7}$-sparse $(\ell, w)$-blockade in $F$.
-/
theorem step1c_anticonnected_block_pruning (G : SimpleGraph V) (F : Finset V) (ℓ m : ℕ) (ε c₂ : ℝ)
    (hℓ : 2 ≤ ℓ) (hℓ_le : (ℓ : ℝ) ≤ ε⁻¹) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (hm_ge : 4 * (ℓ : ℝ) ≤ (m : ℝ))
    (D : Fin ℓ → Finset V) (hD_le : ∀ i, ((D i).card : ℝ) ≤ (m : ℝ))
    (hD : IsCompleteOrXSparseBlockadeIn G F ℓ ((1 / 2 : ℝ) * (m : ℝ)) (ε ^ (c₂ - 5)) D) :
    (∃ B : Fin ℓ → Finset V, IsCompleteBlockadeIn G F ℓ ((m : ℝ) / (2 * (ℓ : ℝ) ^ 2)) B) ∨
    (∃ (w : ℕ) (B : Fin ℓ → Finset V),
      1 ≤ w ∧
      (m : ℝ) / (2 * (ℓ : ℝ)) ≤ (w : ℝ) ∧
      (w : ℝ) ≤ (m : ℝ) ∧
      (∀ i, B i ⊆ D i) ∧
      (∀ i, (B i).card = w) ∧
      (∀ i, IsAnticonnected G (B i)) ∧
      IsCompleteOrXSparseBlockadeIn G F ℓ (w : ℝ) (ε ^ (c₂ - 7)) B) := by
  classical
  have hℓ_pos : (0 : ℝ) < (ℓ : ℝ) := by positivity
  have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
  by_cases hall_anti : ∀ i : Fin ℓ, ∃ C ⊆ D i, C.Nonempty ∧ IsAnticonnected G C ∧
      ((D i).card : ℝ) / (ℓ : ℝ) ≤ (C.card : ℝ)
  · right
    let w : ℕ := ⌈(m : ℝ) / (2 * (ℓ : ℝ))⌉₊
    have hw_ge : (m : ℝ) / (2 * (ℓ : ℝ)) ≤ (w : ℝ) := Nat.le_ceil _
    have hw_pos : 1 ≤ w := by
      rw [Nat.one_le_iff_ne_zero]
      exact (Nat.ceil_pos.mpr (by positivity)).ne'
    have hw_le_Ci : ∀ i : Fin ℓ, (w : ℝ) ≤ (((hall_anti i).choose).card : ℝ) := by
      intro i
      obtain ⟨_, _, _, hCi_card⟩ := (hall_anti i).choose_spec
      have hDi_div : (m : ℝ) / (2 * (ℓ : ℝ)) ≤ ((D i).card : ℝ) / (ℓ : ℝ) := by
        have hDi_ge : (1 / 2 : ℝ) * (m : ℝ) ≤ ((D i).card : ℝ) := hD.1.width_ge i
        rw [div_le_div_iff₀ (by positivity) hℓ_pos]
        nlinarith
      have hw_nat : w ≤ ((hall_anti i).choose).card :=
        Nat.ceil_le.mpr (le_trans hDi_div hCi_card)
      exact_mod_cast hw_nat
    have hw_le_m : (w : ℝ) ≤ (m : ℝ) := by
      have i₀ : Fin ℓ := ⟨0, by omega⟩
      have hCi_D := (hall_anti i₀).choose_spec.1
      have hCi_le_D : (((hall_anti i₀).choose).card : ℝ) ≤ ((D i₀).card : ℝ) := by
        exact_mod_cast card_le_card hCi_D
      exact (hw_le_Ci i₀).trans (hCi_le_D.trans (hD_le i₀))
    have hB_ex : ∀ i : Fin ℓ, ∃ B_i ⊆ D i, B_i.card = w ∧ IsAnticonnected G B_i := by
      intro i
      let C_i := (hall_anti i).choose
      have hCi_D : C_i ⊆ D i := (hall_anti i).choose_spec.1
      have hCi_anti : IsAnticonnected G C_i := (hall_anti i).choose_spec.2.2.1
      have hw_Ci : w ≤ C_i.card := by exact_mod_cast hw_le_Ci i
      obtain ⟨B_i, hBi_Ci, hBi_card, hBi_anti⟩ :=
        exists_anticonnected_subset_card_eq G C_i w hCi_anti hw_pos hw_Ci
      exact ⟨B_i, Subset.trans hBi_Ci hCi_D, hBi_card, hBi_anti⟩
    let B : Fin ℓ → Finset V := fun i => (hB_ex i).choose
    have hB_sub : ∀ i, B i ⊆ D i := fun i => (hB_ex i).choose_spec.1
    have hB_card : ∀ i, (B i).card = w := fun i => (hB_ex i).choose_spec.2.1
    have hB_anti : ∀ i, IsAnticonnected G (B i) := fun i => (hB_ex i).choose_spec.2.2
    have hB_deg : ∀ i j : Fin ℓ,
        (∀ u ∈ D i, ((neighborFinsetIn G u (D j)).card : ℝ) ≤ ε ^ (c₂ - 5) * ((D j).card : ℝ)) →
        (∀ u ∈ B i, ((neighborFinsetIn G u (B j)).card : ℝ) ≤ ε ^ (c₂ - 7) * ((B j).card : ℝ)) := by
      intro i j hdeg u hu
      have hu_Di : u ∈ D i := hB_sub i hu
      have hsub_Bj : neighborFinsetIn G u (B j) ⊆ neighborFinsetIn G u (D j) := by
        intro v hv
        rw [mem_neighborFinsetIn] at hv ⊢
        exact ⟨hB_sub j hv.1, hv.2⟩
      have hdeg_le : ((neighborFinsetIn G u (B j)).card : ℝ) ≤
          ((neighborFinsetIn G u (D j)).card : ℝ) := by
        exact_mod_cast card_le_card hsub_Bj
      have hm_le_2ℓw : (m : ℝ) ≤ 2 * (ℓ : ℝ) * (w : ℝ) := by
        rw [div_le_iff₀ (by positivity)] at hw_ge
        linarith
      have h2ℓ_le : 2 * (ℓ : ℝ) ≤ ε⁻¹ * ε⁻¹ := by
        have h2_le : (2 : ℝ) ≤ ε⁻¹ := by
          rw [le_inv_comm₀ (by norm_num) hε0]
          linarith
        exact mul_le_mul h2_le hℓ_le (by positivity) (by positivity)
      have hpow_7 : ε ^ (c₂ - 5) * (ε⁻¹ * ε⁻¹) = ε ^ (c₂ - 7) := by
        rw [← Real.rpow_neg_one ε, ← Real.rpow_add hε0, ← Real.rpow_add hε0]
        ring_nf
      rw [hB_card j]
      calc ((neighborFinsetIn G u (B j)).card : ℝ)
        _ ≤ ((neighborFinsetIn G u (D j)).card : ℝ) := hdeg_le
        _ ≤ ε ^ (c₂ - 5) * ((D j).card : ℝ) := hdeg u hu_Di
        _ ≤ ε ^ (c₂ - 5) * (m : ℝ) :=
          mul_le_mul_of_nonneg_left (hD_le j) (by positivity)
        _ ≤ ε ^ (c₂ - 5) * ((2 * (ℓ : ℝ)) * (w : ℝ)) := by
          have : 0 ≤ ε ^ (c₂ - 5) := by positivity
          nlinarith
        _ ≤ ε ^ (c₂ - 5) * ((ε⁻¹ * ε⁻¹) * (w : ℝ)) := by
          have : 0 ≤ ε ^ (c₂ - 5) * (w : ℝ) := by positivity
          nlinarith
        _ = ε ^ (c₂ - 7) * (w : ℝ) := by rw [← hpow_7]; ring
    refine ⟨w, B, hw_pos, hw_ge, hw_le_m, hB_sub, hB_card, hB_anti, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · intro i
      exact Subset.trans (hB_sub i) (hD.1.subset_ambient i)
    · intro i
      exact card_pos.mp (by rw [hB_card i]; omega)
    · intro i j hij
      exact Disjoint.mono (hB_sub i) (hB_sub j) (hD.1.pairwise_disjoint i j hij)
    · intro i
      rw [hB_card i]
    · intro i j hij
      rcases hD.2 i j hij with hcomp | ⟨hdeg_ji, hdeg_ij⟩
      · exact Or.inl (hcomp.mono (hB_sub i) (hB_sub j))
      · exact Or.inr ⟨hB_deg j i hdeg_ji, hB_deg i j hdeg_ij⟩
  · left
    push_neg at hall_anti
    obtain ⟨i₀, hi₀⟩ := hall_anti
    rcases anticonnected_component_or_complete_blockade G (D i₀) ℓ
        (hD.1.nonempty_blocks i₀) hℓ with ⟨C, hC_sub, hC_ne, hC_anti, _, hC_card⟩ | ⟨B, hB⟩
    · linarith [hi₀ C hC_sub hC_ne hC_anti]
    · refine ⟨B, hB.mono (hD.1.subset_ambient i₀) ?_⟩
      have hDi₀_ge : (1 / 2 : ℝ) * (m : ℝ) ≤ ((D i₀).card : ℝ) := hD.1.width_ge i₀
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (ℓ : ℝ)]

/-! #### Step 1d: Open-Interval Attachment Extraction (lines 568–576) -/

/--
**Step 1d (`step1d_open_interval_attachment`, Proposition 5.4 of `FMBV4-016_readable.tex`)**:
Let $F$ be $y$-sparse in $G$, and let $B_1, \dots, B_\ell \subseteq F$ be blocks of size $w \ge 1$
with $\ell w \le y |F|$. If $i^* \in [\ell]$ is an index such that at most $y |F|$ vertices
$v \in F \setminus \bigcup_j B_j$ satisfy $0 < |N_G(v) \cap B_{i^*}| < \frac{1}{2} w$, then
setting $X := B_{i^*}$ and $Y := \{v \in F \setminus \bigcup_j B_j : N_G(v) \cap X = \emptyset\}$
yields disjoint subsets $X, Y \subseteq F$ with $|X| = w$, $|Y| \ge (1 - 4y)|F|$, and $(X, Y)$
anticomplete in $G$.
-/
theorem step1d_open_interval_attachment (G : SimpleGraph V) (F : Finset V) (ℓ w : ℕ) (y : ℝ)
    (hw : 1 ≤ w) (_hy0 : 0 < y) (hF_sparse : IsEpsSparseOn G F y)
    (B : Fin ℓ → Finset V) (hBF : ∀ j, B j ⊆ F) (hB_card : ∀ j, (B j).card = w)
    (hℓw : ((ℓ * w : ℕ) : ℝ) ≤ y * (F.card : ℝ)) (istar : Fin ℓ)
    (hopen : (((F \ (Finset.univ : Finset (Fin ℓ)).biUnion B).filter (fun v =>
      0 < (neighborFinsetIn G v (B istar)).card ∧
      ((neighborFinsetIn G v (B istar)).card : ℝ) < (1 / 2 : ℝ) * (w : ℝ))).card : ℝ) ≤
        y * (F.card : ℝ)) :
    ∃ X ⊆ F, ∃ Y ⊆ F, Disjoint X Y ∧
      X.card = w ∧
      (1 - 4 * y) * (F.card : ℝ) ≤ (Y.card : ℝ) ∧
      IsAnticompletePair G X Y := by
  classical
  let X := B istar
  let U := (Finset.univ : Finset (Fin ℓ)).biUnion B
  let Ext := F \ U
  let Mid := Ext.filter (fun v =>
    0 < (neighborFinsetIn G v X).card ∧
    ((neighborFinsetIn G v X).card : ℝ) < (1 / 2 : ℝ) * (w : ℝ))
  let High := F.filter (fun v => (1 / 2 : ℝ) * (w : ℝ) ≤ ((neighborFinsetIn G v X).card : ℝ))
  let Y := Ext.filter (fun v => (neighborFinsetIn G v X).card = 0)
  have hXF : X ⊆ F := hBF istar
  have hYF : Y ⊆ F := Subset.trans (filter_subset _ _) sdiff_subset
  have hdisj_XY : Disjoint X Y := by
    rw [Finset.disjoint_left]
    intro u huX huY
    simp only [Y, Ext, U, mem_filter, mem_sdiff, mem_biUnion, mem_univ, true_and] at huY
    exact huY.1.2 ⟨istar, huX⟩
  have hanti_XY : IsAnticompletePair G X Y := by
    intro u huX v hvY hadj
    simp only [Y, mem_filter, card_eq_zero] at hvY
    have hu_mem : u ∈ neighborFinsetIn G v X :=
      (mem_neighborFinsetIn G v u X).mpr ⟨huX, hadj.symm⟩
    rw [hvY.2] at hu_mem
    exact notMem_empty u hu_mem
  have hU_card : (U.card : ℝ) ≤ y * (F.card : ℝ) := by
    have h1 : U.card ≤ ℓ * w := by
      calc U.card
        _ ≤ ∑ j : Fin ℓ, (B j).card := card_biUnion_le
        _ = ∑ _j : Fin ℓ, w := sum_congr rfl (fun j _ => hB_card j)
        _ = ℓ * w := by rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    exact le_trans (by exact_mod_cast h1) hℓw
  have hHigh_card : (High.card : ℝ) ≤ 2 * y * (F.card : ℝ) := by
    have he_le : (crossEdgeCount G F X : ℝ) ≤ (w : ℝ) * (y * (F.card : ℝ)) := by
      have h1 : (crossEdgeCount G X F : ℝ) = ∑ u ∈ X, ((neighborFinsetIn G u F).card : ℝ) := by
        exact_mod_cast crossEdgeCount_eq_sum_left G X F
      rw [crossEdgeCount_comm, h1]
      calc ∑ u ∈ X, ((neighborFinsetIn G u F).card : ℝ)
        _ ≤ ∑ _u ∈ X, y * (F.card : ℝ) := sum_le_sum (fun u hu => hF_sparse u (hXF hu))
        _ = (X.card : ℝ) * (y * (F.card : ℝ)) := by rw [sum_const, nsmul_eq_mul]
        _ = (w : ℝ) * (y * (F.card : ℝ)) := by rw [hB_card istar]
    have hmarkov : (High.card : ℝ) * ((1 / 2 : ℝ) * (w : ℝ)) ≤ (crossEdgeCount G F X : ℝ) := by
      calc (High.card : ℝ) * ((1 / 2 : ℝ) * (w : ℝ))
        _ = ∑ _v ∈ High, (1 / 2 : ℝ) * (w : ℝ) := by rw [sum_const, nsmul_eq_mul]
        _ ≤ ∑ v ∈ High, ((neighborFinsetIn G v X).card : ℝ) := by
          refine sum_le_sum (fun v hv => ?_)
          simp only [High, mem_filter] at hv
          exact hv.2
        _ ≤ ∑ v ∈ F, ((neighborFinsetIn G v X).card : ℝ) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.cast_nonneg _)
        _ = (crossEdgeCount G F X : ℝ) := by
          exact_mod_cast (crossEdgeCount_eq_sum_left G F X).symm
    have hw_pos : (0 : ℝ) < (w : ℝ) := by positivity
    nlinarith
  have hF_sub : F ⊆ Y ∪ (U ∪ (Mid ∪ High)) := by
    intro v hvF
    rw [mem_union, mem_union, mem_union]
    by_cases hvU : v ∈ U
    · exact Or.inr (Or.inl hvU)
    · have hvExt : v ∈ Ext := mem_sdiff.mpr ⟨hvF, hvU⟩
      by_cases hdeg0 : (neighborFinsetIn G v X).card = 0
      · exact Or.inl (mem_filter.mpr ⟨hvExt, hdeg0⟩)
      · have hdeg_pos : 0 < (neighborFinsetIn G v X).card := Nat.pos_of_ne_zero hdeg0
        by_cases hdeg_lt : ((neighborFinsetIn G v X).card : ℝ) < (1 / 2 : ℝ) * (w : ℝ)
        · exact Or.inr (Or.inr (Or.inl (mem_filter.mpr ⟨hvExt, hdeg_pos, hdeg_lt⟩)))
        · push_neg at hdeg_lt
          exact Or.inr (Or.inr (Or.inr (mem_filter.mpr ⟨hvF, hdeg_lt⟩)))
  have hF_card_nat : F.card ≤ Y.card + U.card + Mid.card + High.card := by
    calc F.card
      _ ≤ (Y ∪ (U ∪ (Mid ∪ High))).card := card_le_card hF_sub
      _ ≤ Y.card + (U ∪ (Mid ∪ High)).card := card_union_le _ _
      _ ≤ Y.card + (U.card + (Mid ∪ High).card) := Nat.add_le_add_left (card_union_le _ _) _
      _ ≤ Y.card + (U.card + (Mid.card + High.card)) :=
        Nat.add_le_add_left (Nat.add_le_add_left (card_union_le _ _) _) _
      _ = Y.card + U.card + Mid.card + High.card := by omega
  have hF_card_real :
      (F.card : ℝ) ≤ (Y.card : ℝ) + (U.card : ℝ) + (Mid.card : ℝ) + (High.card : ℝ) := by
    exact_mod_cast hF_card_nat
  refine ⟨X, hXF, Y, hYF, hdisj_XY, hB_card istar, ?_, hanti_XY⟩
  linarith

/--
**Combined Steps 1a–1c (`stage2_step1_sparse_to_blockade_or_anticonnected`)**:
Chaining Step 1a (`step1a_equal_size_presampling`), Step 1b (`step1b_weak_to_strong_cleaning`),
and Step 1c (`step1c_anticonnected_block_pruning`): from an $(\ell, m)$-blockade $A$ in $F$ whose
block pairs are complete or weakly $\varepsilon^{c_2}$-sparse, we obtain either a complete
$(\ell, \frac{m}{2\ell^2})$-blockade in $F$, or an equal-sized anticonnected $(\ell, w)$-blockade
$B$ in $F$ with $\frac{m}{2\ell} \le w \le m$ whose block pairs are complete or
$\varepsilon^{c_2 - 7}$-sparse in both directions.
-/
theorem stage2_step1_sparse_to_blockade_or_anticonnected (G : SimpleGraph V) (F : Finset V)
    (ℓ m : ℕ) (ε c₂ : ℝ) (hℓ : 2 ≤ ℓ) (hℓ_le : (ℓ : ℝ) ≤ ε⁻¹)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 4) (hm_ge : 4 * (ℓ : ℝ) ≤ (m : ℝ))
    (A : Fin ℓ → Finset V) (hA : IsBlockadeIn G F ℓ (m : ℝ) A)
    (hpairs : ∀ i j : Fin ℓ, i ≠ j → IsCompleteOrWeaklyXSparsePair G (A i) (A j) (ε ^ c₂)) :
    (∃ B : Fin ℓ → Finset V, IsCompleteBlockadeIn G F ℓ ((m : ℝ) / (2 * (ℓ : ℝ) ^ 2)) B) ∨
    (∃ (w : ℕ) (B : Fin ℓ → Finset V),
      1 ≤ w ∧
      (m : ℝ) / (2 * (ℓ : ℝ)) ≤ (w : ℝ) ∧
      (w : ℝ) ≤ (m : ℝ) ∧
      (∀ i, B i ⊆ A i) ∧
      (∀ i, (B i).card = w) ∧
      (∀ i, IsAnticonnected G (B i)) ∧
      IsCompleteOrXSparseBlockadeIn G F ℓ (w : ℝ) (ε ^ (c₂ - 7)) B) := by
  have hm2 : 2 ≤ m := by
    have hℓ2 : (2 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
    have hm8 : (8 : ℝ) ≤ (m : ℝ) := by linarith
    have hm8_nat : 8 ≤ m := by exact_mod_cast hm8
    omega
  obtain ⟨X, hX_sub, hX_card, hX_block, hX_pairs⟩ :=
    step1a_equal_size_presampling G F ℓ m ε c₂ hℓ hℓ_le (by omega) hε0 A hA hpairs
  obtain ⟨D, hD_sub, hD_bounds, hD_block⟩ :=
    step1b_weak_to_strong_cleaning G F ℓ m ε c₂ hℓ hℓ_le hm2 hε0 hε1 X hX_block hX_card hX_pairs
  rcases step1c_anticonnected_block_pruning G F ℓ m ε c₂ hℓ hℓ_le hε0 hε1 hm_ge
      D (fun i => (hD_bounds i).2) hD_block with ⟨B, hB⟩ |
      ⟨w, B, hw1, hw_ge, hw_le, hB_sub, hB_card, hB_anti, hB_block⟩
  · exact Or.inl ⟨B, hB⟩
  · exact Or.inr ⟨w, B, hw1, hw_ge, hw_le,
      fun i => Subset.trans (hB_sub i) (Subset.trans (hD_sub i) (hX_sub i)),
      hB_card, hB_anti, hB_block⟩

/-! #### Step 2: Single-Scale Scale Substitution and Blockade Iteration (lines 579–616) -/

/--
In Step 2 (Proposition 5.4 of `FMBV4-016_readable.tex`), if $F_t$ is $\lambda$-restricted in $G$ and
$F' \subseteq F_t$ satisfies $|F'| \ge c_0 |F_t|$ with $c_0 > 0$, then $F'$ is
$y$-restricted in $G$ for $y = \lambda / c_0$.
-/
theorem stage2_step2_restricted_sub_of_subset (G : SimpleGraph V) (F_t F' : Finset V)
    (lam c₀ : ℝ) (hlam : 0 ≤ lam) (hc₀ : 0 < c₀) (hsub : F' ⊆ F_t)
    (hcard : c₀ * (F_t.card : ℝ) ≤ (F'.card : ℝ)) (hF_t : IsEpsRestrictedOn G F_t lam) :
    IsEpsRestrictedOn G F' (lam / c₀) := by
  have htransfer : ∀ H : SimpleGraph V, IsEpsSparseOn H F_t lam →
      IsEpsSparseOn H F' (lam / c₀) := by
    intro H hsparse v hv
    have hsub_n : neighborFinsetIn H v F' ⊆ neighborFinsetIn H v F_t := by
      intro u hu
      rw [mem_neighborFinsetIn] at hu ⊢
      exact ⟨hsub hu.1, hu.2⟩
    have hdeg_le : ((neighborFinsetIn H v F').card : ℝ) ≤
        ((neighborFinsetIn H v F_t).card : ℝ) := by
      exact_mod_cast card_le_card hsub_n
    calc ((neighborFinsetIn H v F').card : ℝ)
      _ ≤ ((neighborFinsetIn H v F_t).card : ℝ) := hdeg_le
      _ ≤ lam * (F_t.card : ℝ) := hsparse v (hsub hv)
      _ = (lam / c₀) * (c₀ * (F_t.card : ℝ)) := by
        have hc₀_ne : c₀ ≠ 0 := hc₀.ne'
        field_simp
      _ ≤ (lam / c₀) * (F'.card : ℝ) :=
        mul_le_mul_of_nonneg_left hcard (by positivity)
  rcases hF_t with hsp | hcosp
  · exact Or.inl (htransfer G hsp)
  · exact Or.inr (htransfer Gᶜ hcosp)

/--
In Step 2 (Proposition 5.4 of `FMBV4-016_readable.tex`), iterating Outcome (R4) across all subsets
$F' \subseteq F_t$ with $|F'| \ge 2^{-4 a_5}|F_t|$ via Lemma 2.8 (`blockade_iteration_pure`)
upgrades (R4) into a complete or anticomplete $(\lceil y^{-1} \rceil, y^{a_3 + 2}|F_t|)$-blockade
in $F_t$, leaving only Outcomes (R1), (R2), or (R3).
-/
theorem stage2_step2_r4_to_blockade (G : SimpleGraph V) (F_t : Finset V) (a₃ a₅ y : ℝ)
    (ha₃ : 1 ≤ a₃) (ha₅ : 1 ≤ a₅) (hy0 : 0 < y) (hyc : y ≤ (2 : ℝ) ^ (-4 * a₅))
    (hw₀ : 1 ≤ y ^ (a₃ + 2) * (F_t.card : ℝ))
    (P_R123 : Finset V → Prop)
    (hstep1 : ∀ F' ⊆ F_t, (2 : ℝ) ^ (-4 * a₅) * (F_t.card : ℝ) ≤ (F'.card : ℝ) →
      P_R123 F' ∨
      (∃ X ⊆ F', ∃ Y ⊆ F', Disjoint X Y ∧
        y ^ a₃ * (F'.card : ℝ) ≤ (X.card : ℝ) ∧
        (1 - a₅ * y) * (F'.card : ℝ) ≤ (Y.card : ℝ) ∧
        IsPurePair G X Y)) :
    (∃ F' ⊆ F_t, (2 : ℝ) ^ (-4 * a₅) * (F_t.card : ℝ) ≤ (F'.card : ℝ) ∧ P_R123 F') ∨
    (∃ B : Fin ⌈y⁻¹⌉₊ → Finset V,
      IsCompleteBlockadeIn G F_t ⌈y⁻¹⌉₊ (y ^ (a₃ + 2) * (F_t.card : ℝ)) B ∨
      IsAnticompleteBlockadeIn G F_t ⌈y⁻¹⌉₊ (y ^ (a₃ + 2) * (F_t.card : ℝ)) B) := by
  by_cases hR123 : ∃ F' ⊆ F_t, (2 : ℝ) ^ (-4 * a₅) * (F_t.card : ℝ) ≤ (F'.card : ℝ) ∧ P_R123 F'
  · exact Or.inl hR123
  · right
    push_neg at hR123
    have hR4 : ∀ F' ⊆ F_t, (2 : ℝ) ^ (-4 * a₅) * (F_t.card : ℝ) ≤ (F'.card : ℝ) →
        ∃ X ⊆ F', ∃ Y ⊆ F', Disjoint X Y ∧
          y ^ a₃ * (F'.card : ℝ) ≤ (X.card : ℝ) ∧
          (1 - a₅ * y) * (F'.card : ℝ) ≤ (Y.card : ℝ) ∧
          IsPurePair G X Y := by
      intro F' hF' hcard
      rcases hstep1 F' hF' hcard with h123 | h4
      · exact (hR123 F' hF' hcard h123).elim
      · exact h4
    rcases blockade_iteration_pure G F_t a₃ a₅ y ha₃ ha₅ hy0 hyc hw₀ hR4 with
      ⟨B, hB⟩ | ⟨B, hB⟩
    · exact ⟨B, Or.inl hB⟩
    · exact ⟨B, Or.inr hB⟩

/-! #### Step 3 & Proposition 5.4: Final Erdős–Hajnal Derivation (`prop:master-reduction`) -/

/--
**Step 3 (`stage2_step3_blockade_to_eh`, Proposition 5.4 of `FMBV4-016_readable.tex`)**:
Suppose that for every induced subgraph $F \subseteq S_0$ with $|F| \ge \varepsilon^{2 C_1}|S_0|$,
either:
- **(i)** $F$ contains an $x$-restricted subset $S \subseteq F$ with $|S| \ge x^{-1}$,
- **(ii)** $F$ contains a complete or anticomplete $(k, |F|/k^{C_1})$-blockade for some $k \ge 2$, or
- **(iii)** $\kappa(G) \ge |S_0|^c$.
Then applying Lemma 2.9 (`blockade_to_restricted_subgraph`) and Part 1
(`kappa_ge_inv_two_mul_of_isEpsRestrictedOn`) yields $\kappa(G) \ge |S_0|^c$.
-/
theorem stage2_step3_blockade_to_eh (G : SimpleGraph V) (S₀ : Finset V) (C₁ c x ε : ℝ)
    (hC₁ : 1 ≤ C₁) (hx0 : 0 < x) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (hS₀_card : ε ^ (-3 * C₁) ≤ (S₀.card : ℝ))
    (hc_2x : (S₀.card : ℝ) ^ c ≤ (2 * x)⁻¹)
    (hc_2ε : (S₀.card : ℝ) ^ c ≤ (2 * ε)⁻¹)
    (hc_ε : (S₀.card : ℝ) ^ c ≤ ε⁻¹)
    (hε_S₀ : ε⁻¹ ≤ ε ^ (3 * C₁) * (S₀.card : ℝ))
    (hdichotomy : ∀ F ⊆ S₀, ε ^ (2 * C₁) * (S₀.card : ℝ) ≤ (F.card : ℝ) →
      (∃ S ⊆ F, IsEpsRestrictedOn G S x ∧ x⁻¹ ≤ (S.card : ℝ)) ∨
      (∃ k : ℕ, 2 ≤ k ∧ ∃ B : Fin k → Finset V,
        IsCompleteBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ C₁) B ∨
        IsAnticompleteBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ C₁) B) ∨
      (S₀.card : ℝ) ^ c ≤ (kappa G : ℝ)) :
    (S₀.card : ℝ) ^ c ≤ (kappa G : ℝ) := by
  by_cases h_all_small_block : ∀ F ⊆ S₀, ε ^ (2 * C₁) * (S₀.card : ℝ) ≤ (F.card : ℝ) →
      ∃ k : ℕ, 2 ≤ k ∧ (k : ℝ) ≤ ε⁻¹ ∧
        ∃ B : Fin k → Finset V,
          IsCompleteBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ C₁) B ∨
          IsAnticompleteBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ C₁) B
  · obtain ⟨S, _, hS_rest, hS_card⟩ :=
      blockade_to_restricted_subgraph G S₀ C₁ ε hC₁ hε0 hε1 hS₀_card h_all_small_block
    have hS_ge_inv : ε⁻¹ ≤ (S.card : ℝ) := le_trans hε_S₀ hS_card
    have hkappa_ge : (2 * ε)⁻¹ ≤ (kappa G : ℝ) :=
      kappa_ge_inv_two_mul_of_isEpsRestrictedOn G S ε hε0 hS_ge_inv hS_rest
    exact le_trans hc_2ε hkappa_ge
  · rcases not_forall.mp h_all_small_block with ⟨F, hF⟩
    rcases _root_.not_imp.mp hF with ⟨hFS₀, hF'⟩
    rcases _root_.not_imp.mp hF' with ⟨hF_card, hF_no_small⟩
    rcases hdichotomy F hFS₀ hF_card with
      ⟨S, _, hS_rest, hS_card⟩ | ⟨k, hk2, B, hB⟩ | hkappa
    · exact le_trans hc_2x (kappa_ge_inv_two_mul_of_isEpsRestrictedOn G S x hx0 hS_card hS_rest)
    · by_cases hk_le : (k : ℝ) ≤ ε⁻¹
      · exact (hF_no_small ⟨k, hk2, hk_le, B, hB⟩).elim
      · push_neg at hk_le
        have hkappa_k : (k : ℝ) ≤ (kappa G : ℝ) :=
          kappa_ge_of_pure_blockade G F k ((F.card : ℝ) / (k : ℝ) ^ C₁) B hB
        exact le_trans hc_ε (le_trans hk_le.le hkappa_k)
    · exact hkappa

/--
**Proposition 5.4 (`prop:master-reduction`, Stage 2 Reduction to the Erdős–Hajnal Property)**:
If a graph $G$ on vertex set $S_0 \subseteq V$ satisfies the Stage 2 multi-scale dichotomy with
parameters $C_1, C_2 > 0$ ($C_1 \ge 1$) — namely, for every $x \in (0, 1/2)$ and every $F \subseteq S_0$,
either:
- **(i)** $F$ contains an $x$-restricted subset $S \subseteq F$ with $|S| \ge x^{C_1}|F|$,
- **(ii)** $F$ contains a complete or anticomplete $(k, |F|/k^{C_1})$-blockade for some $k \ge 2$, or
- **(iii)** $\kappa(G) \ge (x^{C_1}|F|)^{C_2}$ —
then for $q = 42 C_1^2$, $c = \min(q^{-1}, C_2 / 2)$, and $|S_0| \ge 2^q$, we have
$\kappa(G) \ge |S_0|^c$.
-/
theorem stage2_reduction (G : SimpleGraph V) (S₀ : Finset V) (C₁ C₂ : ℝ)
    (hC₁ : 1 ≤ C₁) (hC₂ : 0 < C₂)
    (h_multiscale : ∀ x : ℝ, 0 < x → x < 1 / 2 → ∀ F ⊆ S₀,
      (∃ S ⊆ F, IsEpsRestrictedOn G S x ∧ x ^ C₁ * (F.card : ℝ) ≤ (S.card : ℝ)) ∨
      (∃ k : ℕ, 2 ≤ k ∧ ∃ B : Fin k → Finset V,
        IsCompleteBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ C₁) B ∨
        IsAnticompleteBlockadeIn G F k ((F.card : ℝ) / (k : ℝ) ^ C₁) B) ∨
      (x ^ C₁ * (F.card : ℝ)) ^ C₂ ≤ (kappa G : ℝ)) :
    let q := 42 * C₁ ^ 2
    let c := min (q⁻¹) (C₂ / 2)
    (2 : ℝ) ^ q ≤ (S₀.card : ℝ) → (S₀.card : ℝ) ^ c ≤ (kappa G : ℝ) := by
  intro q c hS₀_ge
  have hC₁_pos : 0 < C₁ := by linarith
  have hq_ge : 42 ≤ q := by
    dsimp [q]
    nlinarith
  have hq_pos : 0 < q := by linarith
  have hS₀_pos : (0 : ℝ) < (S₀.card : ℝ) := lt_of_lt_of_le (by positivity) hS₀_ge
  have hS₀_ge_one : (1 : ℝ) ≤ (S₀.card : ℝ) := by
    have : (1 : ℝ) ≤ (2 : ℝ) ^ q := Real.one_le_rpow (by norm_num) hq_pos.le
    linarith
  let x := (S₀.card : ℝ) ^ (-1 / (3 * C₁))
  let ε := (S₀.card : ℝ) ^ (-1 / (21 * C₁ ^ 2))
  have hx0 : 0 < x := by positivity
  have hε0 : 0 < ε := by positivity
  have hN_pow_inv_21 : 4 ≤ (S₀.card : ℝ) ^ (1 / (21 * C₁ ^ 2)) := by
    have h1 : (2 : ℝ) ^ (2 : ℝ) ≤ (S₀.card : ℝ) ^ (1 / (21 * C₁ ^ 2)) := by
      have h2 : (2 : ℝ) ^ (2 : ℝ) = ((2 : ℝ) ^ q) ^ (1 / (21 * C₁ ^ 2)) := by
        rw [← Real.rpow_mul two_pos.le]
        congr 1
        dsimp [q]
        have hC₁_ne : C₁ ≠ 0 := hC₁_pos.ne'
        field_simp
        ring
      rw [h2]
      exact Real.rpow_le_rpow (by positivity) hS₀_ge (by positivity)
    have h4 : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num
    linarith
  have hε_inv_eq : ε⁻¹ = (S₀.card : ℝ) ^ (1 / (21 * C₁ ^ 2)) := by
    dsimp [ε]
    rw [← Real.rpow_neg hS₀_pos.le]
    congr 1
    ring
  have hε1 : ε ≤ 1 / 4 := by
    have h4_le : 4 ≤ ε⁻¹ := by linarith
    have h1 : 4 * ε ≤ ε⁻¹ * ε := mul_le_mul_of_nonneg_right h4_le hε0.le
    rw [inv_mul_cancel₀ hε0.ne'] at h1
    linarith
  have hx_inv_eq : x⁻¹ = (S₀.card : ℝ) ^ (1 / (3 * C₁)) := by
    dsimp [x]
    rw [← Real.rpow_neg hS₀_pos.le]
    congr 1
    ring
  have hx_lt_half : x < 1 / 2 := by
    have h1 : 1 / (21 * C₁ ^ 2) ≤ 1 / (3 * C₁) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have h2 : (4 : ℝ) ≤ x⁻¹ := by
      rw [hx_inv_eq]
      exact le_trans hN_pow_inv_21 (Real.rpow_le_rpow_of_exponent_le hS₀_ge_one h1)
    have h3 : x ≤ 1 / 4 := by
      have h1' : 4 * x ≤ x⁻¹ * x := mul_le_mul_of_nonneg_right h2 hx0.le
      rw [inv_mul_cancel₀ hx0.ne'] at h1'
      linarith
    linarith
  have hS₀_card : ε ^ (-3 * C₁) ≤ (S₀.card : ℝ) := by
    dsimp [ε]
    rw [← Real.rpow_mul hS₀_pos.le]
    have h1 : (-1 / (21 * C₁ ^ 2)) * (-3 * C₁) = 1 / (7 * C₁) := by
      have hC₁_ne : C₁ ≠ 0 := hC₁_pos.ne'
      field_simp
      ring
    rw [h1]
    have h2 : 1 / (7 * C₁) ≤ 1 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    calc (S₀.card : ℝ) ^ (1 / (7 * C₁))
      _ ≤ (S₀.card : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hS₀_ge_one h2
      _ = (S₀.card : ℝ) := Real.rpow_one _
  have hN_c_le_half_21 : (S₀.card : ℝ) ^ c ≤ (1 / 2 : ℝ) * (S₀.card : ℝ) ^ (1 / (21 * C₁ ^ 2)) := by
    have hc_le_q : c ≤ 1 / (42 * C₁ ^ 2) := by
      dsimp [c, q]
      rw [one_div]
      exact min_le_left _ _
    have h2_le : (2 : ℝ) ≤ (S₀.card : ℝ) ^ (1 / (42 * C₁ ^ 2)) := by
      have h1 : (2 : ℝ) = ((2 : ℝ) ^ q) ^ (1 / (42 * C₁ ^ 2)) := by
        rw [← Real.rpow_mul two_pos.le]
        have hq_mul : q * (1 / (42 * C₁ ^ 2)) = 1 := by
          dsimp [q]
          have hC₁_ne : C₁ ≠ 0 := hC₁_pos.ne'
          field_simp
        rw [hq_mul, Real.rpow_one]
      rw [h1]
      exact Real.rpow_le_rpow (by positivity) hS₀_ge (by positivity)
    have hprod : (S₀.card : ℝ) ^ (1 / (42 * C₁ ^ 2)) * (S₀.card : ℝ) ^ (1 / (42 * C₁ ^ 2)) =
        (S₀.card : ℝ) ^ (1 / (21 * C₁ ^ 2)) := by
      rw [← Real.rpow_add hS₀_pos]
      have hC₁_ne : C₁ ≠ 0 := hC₁_pos.ne'
      congr 1
      field_simp
      ring
    have hNc_le : (S₀.card : ℝ) ^ c ≤ (S₀.card : ℝ) ^ (1 / (42 * C₁ ^ 2)) :=
      Real.rpow_le_rpow_of_exponent_le hS₀_ge_one hc_le_q
    have hpos_42 : 0 < (S₀.card : ℝ) ^ (1 / (42 * C₁ ^ 2)) := by positivity
    nlinarith
  have hc_2ε : (S₀.card : ℝ) ^ c ≤ (2 * ε)⁻¹ := by
    rw [mul_inv, hε_inv_eq]
    linarith
  have hc_ε : (S₀.card : ℝ) ^ c ≤ ε⁻¹ := by
    rw [hε_inv_eq]
    have : (0 : ℝ) < (S₀.card : ℝ) ^ (1 / (21 * C₁ ^ 2)) := by positivity
    linarith
  have hc_2x : (S₀.card : ℝ) ^ c ≤ (2 * x)⁻¹ := by
    rw [mul_inv, hx_inv_eq]
    have h1 : 1 / (21 * C₁ ^ 2) ≤ 1 / (3 * C₁) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have h2 : (S₀.card : ℝ) ^ (1 / (21 * C₁ ^ 2)) ≤ (S₀.card : ℝ) ^ (1 / (3 * C₁)) :=
      Real.rpow_le_rpow_of_exponent_le hS₀_ge_one h1
    linarith
  have hε_S₀ : ε⁻¹ ≤ ε ^ (3 * C₁) * (S₀.card : ℝ) := by
    rw [hε_inv_eq]
    have hrhs : ε ^ (3 * C₁) * (S₀.card : ℝ) = (S₀.card : ℝ) ^ (1 - 1 / (7 * C₁)) := by
      have hε3 : ε ^ (3 * C₁) = (S₀.card : ℝ) ^ (-1 / (7 * C₁)) := by
        dsimp [ε]
        rw [← Real.rpow_mul hS₀_pos.le]
        congr 1
        have hC₁_ne : C₁ ≠ 0 := hC₁_pos.ne'
        field_simp
        ring
      rw [hε3]
      calc (S₀.card : ℝ) ^ (-1 / (7 * C₁)) * (S₀.card : ℝ)
        _ = (S₀.card : ℝ) ^ (-1 / (7 * C₁)) * (S₀.card : ℝ) ^ (1 : ℝ) := by
          rw [Real.rpow_one]
        _ = (S₀.card : ℝ) ^ (-1 / (7 * C₁) + 1) := by
          rw [← Real.rpow_add hS₀_pos]
        _ = (S₀.card : ℝ) ^ (1 - 1 / (7 * C₁)) := by
          congr 1
          ring
    rw [hrhs]
    refine Real.rpow_le_rpow_of_exponent_le hS₀_ge_one ?_
    have h21 : 1 / (21 * C₁ ^ 2) ≤ 1 / 21 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have h7 : 1 / (7 * C₁) ≤ 1 / 7 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    linarith
  refine stage2_step3_blockade_to_eh G S₀ C₁ c x ε hC₁ hx0 hε0 hε1 hS₀_card
    hc_2x hc_2ε hc_ε hε_S₀ ?_
  intro F hFS₀ hF_card
  have h_x_ε_F : x ^ C₁ * (ε ^ (2 * C₁) * (S₀.card : ℝ)) =
      (S₀.card : ℝ) ^ (1 - 1 / 3 - 2 / (21 * C₁)) := by
    have hxC : x ^ C₁ = (S₀.card : ℝ) ^ (-1 / 3 : ℝ) := by
      dsimp [x]
      rw [← Real.rpow_mul hS₀_pos.le]
      congr 1
      have hC₁_ne : C₁ ≠ 0 := hC₁_pos.ne'
      field_simp
    have hεC : ε ^ (2 * C₁) = (S₀.card : ℝ) ^ (-2 / (21 * C₁)) := by
      dsimp [ε]
      rw [← Real.rpow_mul hS₀_pos.le]
      congr 1
      have hC₁_ne : C₁ ≠ 0 := hC₁_pos.ne'
      field_simp
    rw [hxC, hεC]
    calc (S₀.card : ℝ) ^ (-1 / 3 : ℝ) * ((S₀.card : ℝ) ^ (-2 / (21 * C₁)) * (S₀.card : ℝ))
      _ = (S₀.card : ℝ) ^ (-1 / 3 : ℝ) *
          ((S₀.card : ℝ) ^ (-2 / (21 * C₁)) * (S₀.card : ℝ) ^ (1 : ℝ)) := by
        rw [Real.rpow_one]
      _ = (S₀.card : ℝ) ^ (-1 / 3 : ℝ) * (S₀.card : ℝ) ^ (-2 / (21 * C₁) + 1) := by
        rw [← Real.rpow_add hS₀_pos]
      _ = (S₀.card : ℝ) ^ ((-1 / 3 : ℝ) + (-2 / (21 * C₁) + 1)) := by
        rw [← Real.rpow_add hS₀_pos]
      _ = (S₀.card : ℝ) ^ (1 - 1 / 3 - 2 / (21 * C₁)) := by
        congr 1
        ring
  have hexp_ge_half : 1 / 2 ≤ 1 - 1 / 3 - 2 / (21 * C₁) := by
    have : 2 / (21 * C₁) ≤ 2 / 21 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    linarith
  have h_base_ge_half : (S₀.card : ℝ) ^ (1 / 2 : ℝ) ≤ x ^ C₁ * (F.card : ℝ) := by
    calc (S₀.card : ℝ) ^ (1 / 2 : ℝ)
      _ ≤ (S₀.card : ℝ) ^ (1 - 1 / 3 - 2 / (21 * C₁)) :=
        Real.rpow_le_rpow_of_exponent_le hS₀_ge_one hexp_ge_half
      _ = x ^ C₁ * (ε ^ (2 * C₁) * (S₀.card : ℝ)) := h_x_ε_F.symm
      _ ≤ x ^ C₁ * (F.card : ℝ) :=
        mul_le_mul_of_nonneg_left hF_card (by positivity)
  rcases h_multiscale x hx0 hx_lt_half F hFS₀ with
    ⟨S, hSF, hS_rest, hS_card⟩ | ⟨k, hk2, B, hB⟩ | hkappa_F
  · left
    refine ⟨S, hSF, hS_rest, ?_⟩
    rw [hx_inv_eq]
    have h1 : 1 / (3 * C₁) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    calc (S₀.card : ℝ) ^ (1 / (3 * C₁))
      _ ≤ (S₀.card : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hS₀_ge_one h1
      _ ≤ x ^ C₁ * (F.card : ℝ) := h_base_ge_half
      _ ≤ (S.card : ℝ) := hS_card
  · exact Or.inr (Or.inl ⟨k, hk2, B, hB⟩)
  · right; right
    have hc_le_C₂ : c ≤ C₂ / 2 := min_le_right _ _
    calc (S₀.card : ℝ) ^ c
      _ ≤ (S₀.card : ℝ) ^ (C₂ / 2) := Real.rpow_le_rpow_of_exponent_le hS₀_ge_one hc_le_C₂
      _ = ((S₀.card : ℝ) ^ (1 / 2 : ℝ)) ^ C₂ := by
        rw [← Real.rpow_mul hS₀_pos.le]
        congr 1
        ring
      _ ≤ (x ^ C₁ * (F.card : ℝ)) ^ C₂ :=
        Real.rpow_le_rpow (by positivity) h_base_ge_half hC₂.le
      _ ≤ (kappa G : ℝ) := hkappa_F

/-!
### Part 7: Rödl's Theorem for $\overline{P_6}$-Free Graphs (`lem:rodl`, Lemma 2.2)
-/

/--
Any finite set $S$ with $|S| \ge k m_0$ contains $k$ pairwise disjoint subsets of cardinality $m_0$.
-/
private theorem exists_disjoint_subsets_card_eq (S : Finset V) (m₀ : ℕ) :
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
    have hdisj_AT' : ∀ j : Fin k, Disjoint A (T' j) := by
      intro j
      exact Disjoint.mono_right (hT'S j) disjoint_sdiff_self_right
    refine ⟨Fin.cons A T', ?_, ?_, ?_⟩
    · intro i
      exact Fin.cases hAS (fun j => Subset.trans (hT'S j) sdiff_subset) i
    · intro i j
      refine Fin.cases ?_ ?_ i <;> refine Fin.cases ?_ ?_ j
      · intro hij
        exact (hij rfl).elim
      · intro j' _
        simp only [Fin.cons_zero, Fin.cons_succ]
        exact hdisj_AT' j'
      · intro i' _
        simp only [Fin.cons_zero, Fin.cons_succ]
        exact (hdisj_AT' i').symm
      · intro j' i' hij
        simp only [Fin.cons_succ]
        exact hT'_disj i' j' (fun h => hij (congrArg Fin.succ h))
    · intro i
      exact Fin.cases hA_card hT'_card i

/--
**Step 1 of Rödl's Theorem**: If $G$ is induced-$H$-free for some $6$-vertex graph $H$, then for
every $x_0 \in (0, 1]$ and every $S \subseteq V$ with $|S| \ge 6$, there exist disjoint subsets
$L, R \subseteq S$ with $|L|, |R| \ge (x_0 / 12)^6 |S|$ such that $L$ is $x_0$-sparse to $R$ in
either $G$ or $\overline{G}$.
-/
private theorem induced_fin6_free_sparse_or_cosparse_pair (G : SimpleGraph V)
    (H : SimpleGraph (Fin 6)) (hG : IsInducedSubgraphFree G H)
    (S : Finset V) (x₀ : ℝ) (hx₀0 : 0 < x₀) (hx₀1 : x₀ ≤ 1) (hS6 : 6 ≤ S.card) :
    ∃ L ⊆ S, ∃ R ⊆ S, Disjoint L R ∧
      (x₀ / 12) ^ 6 * (S.card : ℝ) ≤ (L.card : ℝ) ∧
      (x₀ / 12) ^ 6 * (S.card : ℝ) ≤ (R.card : ℝ) ∧
      (IsXSparseTo G L R x₀ ∨ IsXSparseTo Gᶜ L R x₀) := by
  classical
  by_contra hno_pair
  let m₀ : ℕ := S.card / 6
  have hm₀_mul : 6 * m₀ ≤ S.card := Nat.mul_div_le S.card 6
  have hm₀_ge : (S.card : ℝ) / 12 ≤ (m₀ : ℝ) := by
    have hnat : S.card ≤ 12 * m₀ := by omega
    have hreal : (S.card : ℝ) ≤ 12 * (m₀ : ℝ) := by exact_mod_cast hnat
    linarith
  obtain ⟨T, hTS, hT_disj, hT_card⟩ := exists_disjoint_subsets_card_eq S m₀ 6 hm₀_mul
  let w₁ : ℝ := (x₀ / 12) ^ 6 * (S.card : ℝ)
  have hS_pos : (0 : ℝ) < (S.card : ℝ) := by
    have : 0 < S.card := by omega
    exact_mod_cast this
  have hw₁_pos : 0 < w₁ := by
    dsimp [w₁]
    positivity
  have h6w₁_le : 6 * w₁ ≤ x₀ ^ 5 * (m₀ : ℝ) := by
    have hx₀6_le : x₀ ^ 6 ≤ x₀ ^ 5 := pow_le_pow_of_le_one hx₀0.le hx₀1 (by omega)
    calc 6 * w₁
      _ = (6 / 12 ^ 6) * (x₀ ^ 6 * (S.card : ℝ)) := by
        dsimp [w₁]
        ring
      _ ≤ (1 / 12) * (x₀ ^ 6 * (S.card : ℝ)) := by
        have : (0 : ℝ) ≤ x₀ ^ 6 * (S.card : ℝ) := by positivity
        nlinarith
      _ ≤ (1 / 12) * (x₀ ^ 5 * (S.card : ℝ)) := by
        have : x₀ ^ 6 * (S.card : ℝ) ≤ x₀ ^ 5 * (S.card : ℝ) :=
          mul_le_mul_of_nonneg_right hx₀6_le hS_pos.le
        linarith
      _ = x₀ ^ 5 * ((S.card : ℝ) / 12) := by ring
      _ ≤ x₀ ^ 5 * (m₀ : ℝ) := mul_le_mul_of_nonneg_left hm₀_ge (by positivity)
  have hS_nonempty : S.Nonempty := card_pos.mp (by omega)
  obtain ⟨v_dummy, _⟩ := hS_nonempty
  have h_ind : ∀ t : ℕ, t ≤ 6 →
      ∃ (v : Fin 6 → V) (R : Fin 6 → Finset V),
        (∀ i : Fin 6, i.val < t → v i ∈ T i) ∧
        (∀ i j : Fin 6, i.val < t → j.val < t → (G.Adj (v i) (v j) ↔ H.Adj i j)) ∧
        (∀ k : Fin 6, R k ⊆ T k) ∧
        (∀ k : Fin 6, t ≤ k.val → x₀ ^ t * (m₀ : ℝ) ≤ ((R k).card : ℝ)) ∧
        (∀ i k : Fin 6, i.val < t → t ≤ k.val → ∀ u ∈ R k, (G.Adj (v i) u ↔ H.Adj i k)) := by
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
      let t_fin : Fin 6 := ⟨t, ht1⟩
      have hRt_ge : x₀ ^ 5 * (m₀ : ℝ) ≤ ((R t_fin).card : ℝ) := by
        have hxt : x₀ ^ 5 ≤ x₀ ^ t := pow_le_pow_of_le_one hx₀0.le hx₀1 (by omega)
        calc x₀ ^ 5 * (m₀ : ℝ)
          _ ≤ x₀ ^ t * (m₀ : ℝ) := mul_le_mul_of_nonneg_right hxt (Nat.cast_nonneg _)
          _ ≤ ((R t_fin).card : ℝ) := hR_card t_fin le_rfl
      let Bad : Fin 6 → Finset V := fun k =>
        if t < k.val then
          (R t_fin).filter (fun u =>
            ((neighborFinsetIn (if H.Adj t_fin k then G else Gᶜ) u (R k)).card : ℝ) ≤
              x₀ * ((R k).card : ℝ))
        else ∅
      have hBad_lt : ∀ k : Fin 6, ((Bad k).card : ℝ) < w₁ := by
        intro k
        dsimp [Bad]
        by_cases htk : t < k.val
        · rw [if_pos htk]
          by_contra hge
          push_neg at hge
          have hRk_ge_w₁ : w₁ ≤ ((R k).card : ℝ) := by
            have hxt : x₀ ^ 5 ≤ x₀ ^ t := pow_le_pow_of_le_one hx₀0.le hx₀1 (by omega)
            calc w₁
              _ ≤ 6 * w₁ := by linarith
              _ ≤ x₀ ^ 5 * (m₀ : ℝ) := h6w₁_le
              _ ≤ x₀ ^ t * (m₀ : ℝ) := mul_le_mul_of_nonneg_right hxt (Nat.cast_nonneg _)
              _ ≤ ((R k).card : ℝ) := hR_card k (by omega)
          let L_k := (R t_fin).filter (fun u =>
            ((neighborFinsetIn (if H.Adj t_fin k then G else Gᶜ) u (R k)).card : ℝ) ≤
              x₀ * ((R k).card : ℝ))
          have hLk_sub : L_k ⊆ S := Subset.trans (filter_subset _ _)
            (Subset.trans (hR_sub t_fin) (hTS t_fin))
          have hRk_sub : R k ⊆ S := Subset.trans (hR_sub k) (hTS k)
          have htk_ne : t_fin ≠ k := by
            intro h
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
      have hbiUnion_lt : ((Finset.univ.biUnion Bad).card : ℝ) < ((R t_fin).card : ℝ) := by
        have h1 : ((Finset.univ.biUnion Bad).card : ℝ) ≤ ∑ k : Fin 6, ((Bad k).card : ℝ) := by
          exact_mod_cast card_biUnion_le
        have h2 : ∑ k : Fin 6, ((Bad k).card : ℝ) < ∑ _k : Fin 6, w₁ :=
          sum_lt_sum_of_nonempty univ_nonempty (fun k _ => hBad_lt k)
        have h3 : (∑ _k : Fin 6, w₁) = 6 * w₁ := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
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
      let v' : Fin 6 → V := fun i => if i = t_fin then v_t else v i
      let R' : Fin 6 → Finset V := fun k =>
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
        · subst hit; subst hjt
          simp
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
          exact Subset.trans (neighborFinsetIn_subset _ _ _) (hR_sub k)
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
        have hu_Rk : u ∈ R k := neighborFinsetIn_subset _ _ _ hu
        dsimp [v']
        split_ifs with hit
        · subst hit
          by_cases hadj : H.Adj t_fin k
          · rw [if_pos hadj, mem_neighborFinsetIn] at hu
            exact iff_of_true hu.2 hadj
          · rw [if_neg hadj, mem_neighborFinsetIn, compl_adj] at hu
            exact iff_of_false hu.2.2 hadj
        · have hit_val : i.val < t := by
            have : i.val ≠ t := fun h => hit (Fin.ext h)
            omega
          exact hR_adj i k hit_val (by omega) u hu_Rk
  obtain ⟨v, _, hv_mem, hv_adj, _, _, _⟩ := h_ind 6 le_rfl
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

/--
Additivity of `crossEdgeCount` in the right argument across a disjoint union.
-/
private theorem crossEdgeCount_union_right (H : SimpleGraph V) (A B₁ B₂ : Finset V)
    (hdisj : Disjoint B₁ B₂) :
    crossEdgeCount H A (B₁ ∪ B₂) = crossEdgeCount H A B₁ + crossEdgeCount H A B₂ := by
  classical
  unfold crossEdgeCount
  rw [← sum_add_distrib]
  refine sum_congr rfl (fun u _ => ?_)
  have heq : neighborFinsetIn H u (B₁ ∪ B₂) =
      neighborFinsetIn H u B₁ ∪ neighborFinsetIn H u B₂ := by
    ext v
    simp [mem_neighborFinsetIn, or_and_right]
  have hdisj' : Disjoint (neighborFinsetIn H u B₁) (neighborFinsetIn H u B₂) :=
    Disjoint.mono (neighborFinsetIn_subset _ _ _) (neighborFinsetIn_subset _ _ _) hdisj
  rw [heq, card_union_of_disjoint hdisj']

/--
Additivity of `crossEdgeCount` in the left argument across a disjoint union.
-/
private theorem crossEdgeCount_union_left (H : SimpleGraph V) (A₁ A₂ B : Finset V)
    (hdisj : Disjoint A₁ A₂) :
    crossEdgeCount H (A₁ ∪ A₂) B = crossEdgeCount H A₁ B + crossEdgeCount H A₂ B := by
  classical
  unfold crossEdgeCount
  exact sum_union hdisj

/--
Decomposition of `crossEdgeCount` on a disjoint union `X ∪ U'`.
-/
private theorem crossEdgeCount_union_union (H : SimpleGraph V) (X U' : Finset V)
    (hdisj : Disjoint X U') :
    crossEdgeCount H (X ∪ U') (X ∪ U') =
      crossEdgeCount H X X + 2 * crossEdgeCount H X U' + crossEdgeCount H U' U' := by
  rw [crossEdgeCount_union_left H X U' (X ∪ U') hdisj,
    crossEdgeCount_union_right H X X U' hdisj,
    crossEdgeCount_union_right H U' X U' hdisj,
    crossEdgeCount_comm H U' X]
  ring

/--
Trivial upper bound on internal `crossEdgeCount`: `crossEdgeCount H X X ≤ X.card * X.card`.
-/
private theorem crossEdgeCount_self_le (H : SimpleGraph V) (X : Finset V) :
    crossEdgeCount H X X ≤ X.card * X.card := by
  unfold crossEdgeCount
  calc ∑ u ∈ X, (neighborFinsetIn H u X).card
    _ ≤ ∑ _u ∈ X, X.card :=
      sum_le_sum (fun u _ => card_le_card (neighborFinsetIn_subset H u X))
    _ = X.card * X.card := by rw [sum_const, smul_eq_mul]

/--
Extending a low-edge-density subset `U' ⊆ L` of size `p' * m` by picking an `m`-element subset
`X ⊆ R` via averaging when `IsXSparseTo H L R x₀` holds.
-/
private theorem extend_low_edge_subset (H : SimpleGraph V) (Y L R U' : Finset V)
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
    rw [crossEdgeCount_comm H R U', crossEdgeCount_eq_sum_left]
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
    have hle := crossEdgeCount_self_le H X
    rw [hX_card] at hle
    have hle' : (crossEdgeCount H X X : ℝ) ≤ (m : ℝ) * (m : ℝ) := by exact_mod_cast hle
    linarith [ sq (m : ℝ) ]
  refine ⟨U, hUY, hU_card, ?_⟩
  dsimp [U]
  have hunion := crossEdgeCount_union_union H X U' hdisj_XU'
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
**Steps 2 & 3 of Rödl's Theorem (Ramsey Iteration with Equal-Size Averaging)**:
By strong induction on $N = p + q$, any $Y \subseteq V$ with $w_0 \le c_1^{p + q - 2}|Y|$ (where
$c_1 = (x_0 / 12)^6$, $w_0 \ge 6$, and $m = \lceil w_0 \rceil$) contains either a subset $U$ of size
$p m$ with $|E_G(U, U)| \le (p + p^2 x_0) m^2$, or a subset $U$ of size $q m$ with
$|E_{\overline{G}}(U, U)| \le (q + q^2 x_0) m^2$.
-/
private theorem rodl_ramsey_low_edge_subset (G : SimpleGraph V)
    (hG : IsInducedSubgraphFree G P6Compl)
    (x₀ w₀ : ℝ) (hx₀0 : 0 < x₀) (hx₀1 : x₀ ≤ 1) (hw₀ : 6 ≤ w₀) :
    let m := Nat.ceil w₀
    let c₁ := (x₀ / 12) ^ 6
    ∀ (N : ℕ) (p q : ℕ), 1 ≤ p → 1 ≤ q → p + q = N →
      ∀ Y : Finset V, w₀ ≤ c₁ ^ (p + q - 2) * (Y.card : ℝ) →
        (∃ U ⊆ Y, U.card = p * m ∧
          (crossEdgeCount G U U : ℝ) ≤ ((p : ℝ) + (p : ℝ) ^ 2 * x₀) * (m : ℝ) ^ 2) ∨
        (∃ U ⊆ Y, U.card = q * m ∧
          (crossEdgeCount Gᶜ U U : ℝ) ≤ ((q : ℝ) + (q : ℝ) ^ 2 * x₀) * (m : ℝ) ^ 2) := by
  intro m c₁ N
  have hc₁_pos : 0 < c₁ := by dsimp [c₁]; positivity
  have hc₁_le_one : c₁ ≤ 1 := by
    dsimp [c₁]
    have : x₀ / 12 ≤ 1 := by linarith
    exact pow_le_one₀ (by positivity) this
  have hm_ge : 1 ≤ m := by
    have : (1 : ℝ) ≤ w₀ := by linarith
    exact Nat.ceil_pos.mpr (by linarith)
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro p q hp hq hN Y hY_card
    have hc₁_pow_le_one : c₁ ^ (p + q - 2) ≤ 1 :=
      pow_le_one₀ hc₁_pos.le hc₁_le_one
    have hw₀_le_Y : w₀ ≤ (Y.card : ℝ) := by
      calc w₀
        _ ≤ c₁ ^ (p + q - 2) * (Y.card : ℝ) := hY_card
        _ ≤ 1 * (Y.card : ℝ) := mul_le_mul_of_nonneg_right hc₁_pow_le_one (Nat.cast_nonneg _)
        _ = (Y.card : ℝ) := one_mul _
    have hm_le_Y : m ≤ Y.card := Nat.ceil_le.mpr hw₀_le_Y
    have hY6 : 6 ≤ Y.card := by
      have : (6 : ℝ) ≤ (Y.card : ℝ) := le_trans hw₀ hw₀_le_Y
      exact_mod_cast this
    rcases p with _ | p'
    · omega
    · rcases Nat.eq_zero_or_pos p' with rfl | hp'
      · left
        obtain ⟨U, hUY, hU_card⟩ := exists_subset_card_eq hm_le_Y
        refine ⟨U, hUY, by simpa using hU_card, ?_⟩
        have hUU := crossEdgeCount_self_le G U
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
            have hUU := crossEdgeCount_self_le Gᶜ U
            rw [hU_card] at hUU
            have hUU' : (crossEdgeCount Gᶜ U U : ℝ) ≤ (m : ℝ) * (m : ℝ) := by exact_mod_cast hUU
            push_cast
            have : 0 ≤ x₀ * (m : ℝ) ^ 2 := by positivity
            nlinarith [sq (m : ℝ)]
          · obtain ⟨L, hLY, R, hRY, hdisj, hL_card, hR_card, hsparse⟩ :=
              induced_fin6_free_sparse_or_cosparse_pair G P6Compl hG Y x₀ hx₀0 hx₀1 hY6
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
              have hL_ind' : w₀ ≤ c₁ ^ (p' + (q' + 1) - 2) * (L.card : ℝ) := by
                rwa [hexp_L]
              rcases ih (p' + (q' + 1)) hlt p' (q' + 1) hp' (by omega) rfl L hL_ind' with
                ⟨U', hU'L, hU'_card, hU'_edges⟩ | ⟨U, hUL, hU_card, hU_edges⟩
              · left
                exact extend_low_edge_subset G Y L R U' p' m x₀ hx₀0.le hm_ge
                  hLY hRY hdisj hm_le_R hLR_G hU'L hU'_card hU'_edges
              · right
                exact ⟨U, Subset.trans hUL hLY, hU_card, hU_edges⟩
            · have hlt : (p' + 1) + q' < N := by omega
              have hexp_L : (p' + 1) + q' - 2 = p' + q' - 1 := by omega
              have hL_ind' : w₀ ≤ c₁ ^ ((p' + 1) + q' - 2) * (L.card : ℝ) := by
                rwa [hexp_L]
              rcases ih ((p' + 1) + q') hlt (p' + 1) q' (by omega) hq' rfl L hL_ind' with
                ⟨U, hUL, hU_card, hU_edges⟩ | ⟨U', hU'L, hU'_card, hU'_edges⟩
              · left
                exact ⟨U, Subset.trans hUL hLY, hU_card, hU_edges⟩
              · right
                exact extend_low_edge_subset Gᶜ Y L R U' q' m x₀ hx₀0.le hm_ge
                  hLY hRY hdisj hm_le_R hLR_Gc hU'L hU'_card hU'_edges

/--
**Step 4 of Rödl's Theorem (Markov Filtering)**:
Given $U \subseteq F$ of size $\ell m$ with $|E_H(U, U)| \le (\ell + \ell^2 x_0) m^2$, where
$\ell \ge 8 / \xi$ and $x_0 \le \xi / 8$, the subset $F_0 \subseteq U$ of vertices with at most
$(\xi / 2)|U|$ neighbors in $U$ has size $|F_0| \ge |U| / 2 \ge m / 2$ and induces a $\xi$-sparse
subgraph in $H$.
-/
private theorem sparse_subset_of_low_edge_subset (H : SimpleGraph V) (F U : Finset V)
    (ℓ m : ℕ) (ξ x₀ : ℝ) (hξ0 : 0 < ξ) (hℓ_ge : 8 / ξ ≤ (ℓ : ℝ)) (hx₀_le : x₀ ≤ ξ / 8)
    (hℓ1 : 1 ≤ ℓ) (hm1 : 1 ≤ m) (hUF : U ⊆ F) (hU_card : U.card = ℓ * m)
    (hU_edges : (crossEdgeCount H U U : ℝ) ≤ ((ℓ : ℝ) + (ℓ : ℝ) ^ 2 * x₀) * (m : ℝ) ^ 2) :
    ∃ F₀ ⊆ F, IsEpsSparseOn H F₀ ξ ∧ (m : ℝ) / 2 ≤ (F₀.card : ℝ) := by
  classical
  have hU_card_real : (U.card : ℝ) = (ℓ : ℝ) * (m : ℝ) := by
    exact_mod_cast hU_card
  have hU_pos : (0 : ℝ) < (U.card : ℝ) := by
    rw [hU_card_real]
    have : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ1
    have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    positivity
  have hℓ_bound : (ℓ : ℝ) ≤ (ξ / 8) * (ℓ : ℝ) ^ 2 := by
    have h1 : 8 ≤ (ℓ : ℝ) * ξ := (div_le_iff₀ hξ0).mp hℓ_ge
    have h2 : 1 ≤ (ξ / 8) * (ℓ : ℝ) := by linarith
    have hℓ_nonneg : (0 : ℝ) ≤ (ℓ : ℝ) := Nat.cast_nonneg _
    calc (ℓ : ℝ)
      _ = 1 * (ℓ : ℝ) := (one_mul _).symm
      _ ≤ ((ξ / 8) * (ℓ : ℝ)) * (ℓ : ℝ) := mul_le_mul_of_nonneg_right h2 hℓ_nonneg
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
    neighborFinsetIn_mono H v (filter_subset _ _)
  have hle_U : ((neighborFinsetIn H v F₀).card : ℝ) ≤ ((neighborFinsetIn H v U).card : ℝ) := by
    exact_mod_cast card_le_card hsub
  calc ((neighborFinsetIn H v F₀).card : ℝ)
    _ ≤ ((neighborFinsetIn H v U).card : ℝ) := hle_U
    _ ≤ (ξ / 2) * (U.card : ℝ) := hvU.2
    _ ≤ (ξ / 2) * (2 * (F₀.card : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = ξ * (F₀.card : ℝ) := by ring

/--
Explicit positive constant $\delta(\xi)$ for Rödl's theorem on $\overline{P_6}$-free graphs:
$$\delta(\xi) := \frac{1}{6}\left(\frac{\xi}{96}\right)^{12 \lceil 8 / \xi \rceil}.$$
-/
noncomputable def rodlDelta (ξ : ℝ) : ℝ :=
  ((ξ / 96) ^ 6) ^ (2 * Nat.ceil (8 / ξ)) / 6

/-- `rodlDelta ξ` is strictly positive for all $\xi \in (0, 1/2)$. -/
theorem rodlDelta_pos {ξ : ℝ} (hξ0 : 0 < ξ) (_hξ1 : ξ < 1 / 2) : 0 < rodlDelta ξ := by
  unfold rodlDelta
  positivity

/--
**Lemma 2.2 (`lem:rodl`, Rödl's Theorem for $\overline{P_6}$-Free Graphs)**:
For every $\xi \in (0, 1/2)$, there exists $\delta = \text{rodlDelta}(\xi) > 0$ such that every
$\overline{P_6}$-free graph $G$ and every vertex subset $F \subseteq V(G)$ contains a subset
$F_0 \subseteq F$ with $|F_0| \ge \delta |F|$ such that $G[F_0]$ is $\xi$-restricted.
-/
theorem rodl_theorem_P6Compl (G : SimpleGraph V) (hG : IsInducedSubgraphFree G P6Compl)
    (ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ < 1 / 2) (F : Finset V) :
    ∃ F₀ ⊆ F, IsEpsRestrictedOn G F₀ ξ ∧ rodlDelta ξ * (F.card : ℝ) ≤ (F₀.card : ℝ) := by
  classical
  let x₀ : ℝ := ξ / 8
  have hx₀0 : 0 < x₀ := by dsimp [x₀]; positivity
  have hx₀1 : x₀ ≤ 1 := by dsimp [x₀]; linarith
  let c₁ : ℝ := (x₀ / 12) ^ 6
  have hc₁_eq : c₁ = (ξ / 96) ^ 6 := by dsimp [c₁, x₀]; ring
  have hc₁_pos : 0 < c₁ := by dsimp [c₁]; positivity
  have hc₁_le_one : c₁ ≤ 1 := by
    dsimp [c₁, x₀]
    have : ξ / 8 / 12 ≤ 1 := by linarith
    exact pow_le_one₀ (by positivity) this
  let ℓ : ℕ := Nat.ceil (8 / ξ)
  have hℓ_ge : 8 / ξ ≤ (ℓ : ℝ) := Nat.le_ceil (8 / ξ)
  have hℓ1 : 1 ≤ ℓ := by
    have : 0 < 8 / ξ := by positivity
    exact Nat.ceil_pos.mpr this
  let w₀ : ℝ := c₁ ^ (2 * ℓ - 2) * (F.card : ℝ)
  have hdelta_le_w₀ : 6 * rodlDelta ξ * (F.card : ℝ) ≤ w₀ := by
    have hpow : c₁ ^ (2 * ℓ) ≤ c₁ ^ (2 * ℓ - 2) :=
      pow_le_pow_of_le_one hc₁_pos.le hc₁_le_one (by omega)
    calc 6 * rodlDelta ξ * (F.card : ℝ)
      _ = c₁ ^ (2 * ℓ) * (F.card : ℝ) := by
        dsimp [rodlDelta, ℓ]
        rw [← hc₁_eq]
        ring
      _ ≤ c₁ ^ (2 * ℓ - 2) * (F.card : ℝ) :=
        mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _)
      _ = w₀ := rfl
  by_cases hw₀ : 6 ≤ w₀
  · let m : ℕ := Nat.ceil w₀
    have hm1 : 1 ≤ m := Nat.ceil_pos.mpr (by linarith)
    have hw₀_le_m : w₀ ≤ (m : ℝ) := Nat.le_ceil w₀
    have hF_ind : w₀ ≤ c₁ ^ (ℓ + ℓ - 2) * (F.card : ℝ) := by
      have : ℓ + ℓ - 2 = 2 * ℓ - 2 := by omega
      rw [this]
    rcases rodl_ramsey_low_edge_subset G hG x₀ w₀ hx₀0 hx₀1 hw₀ (ℓ + ℓ) ℓ ℓ hℓ1 hℓ1 rfl F hF_ind
      with ⟨U, hUF, hU_card, hU_edges⟩ | ⟨U, hUF, hU_card, hU_edges⟩
    · obtain ⟨F₀, hF₀F, hF₀_sparse, hF₀_card⟩ :=
        sparse_subset_of_low_edge_subset G F U ℓ m ξ x₀ hξ0 hℓ_ge le_rfl hℓ1 hm1
          hUF hU_card hU_edges
      refine ⟨F₀, hF₀F, Or.inl hF₀_sparse, ?_⟩
      have hdelta_nonneg : 0 ≤ rodlDelta ξ * (F.card : ℝ) := by
        have := rodlDelta_pos hξ0 hξ1
        positivity
      linarith
    · obtain ⟨F₀, hF₀F, hF₀_sparse, hF₀_card⟩ :=
        sparse_subset_of_low_edge_subset Gᶜ F U ℓ m ξ x₀ hξ0 hℓ_ge le_rfl hℓ1 hm1
          hUF hU_card hU_edges
      refine ⟨F₀, hF₀F, Or.inr hF₀_sparse, ?_⟩
      have hdelta_nonneg : 0 ≤ rodlDelta ξ * (F.card : ℝ) := by
        have := rodlDelta_pos hξ0 hξ1
        positivity
      linarith
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
          rw [mem_neighborFinsetIn, mem_singleton] at hw
          exact G.loopless u (hw.1 ▸ hw.2)
        rw [hemp]
        simp [hξ0.le]
      · rw [card_singleton, Nat.cast_one]
        linarith

/-!
### Part 8: Blockade Iteration Lemma for $x$-Sparse Pairs (`lem:blockade-iter`, Lemma 2.8)
-/

/--
Prepending a block $X \subseteq T$ disjoint from $T' \subseteq T$ such that $T'$ is $x_0$-sparse
to $X$ (`IsXSparseTo G T' X x₀`) to a one-way $x_0$-sparse $(m, w)$-blockade in $T'$ produces a
one-way $x_0$-sparse $(m + 1, w)$-blockade in $T$.
-/
theorem IsBlockadeIn.cons_oneWay_xSparse {G : SimpleGraph V} {T T' X : Finset V} {m : ℕ} {w x₀ : ℝ}
    {B' : Fin m → Finset V}
    (hXT : X ⊆ T) (hT'T : T' ⊆ T) (hdisj : Disjoint X T') (hX_ne : X.Nonempty)
    (hX_w : w ≤ (X.card : ℝ)) (hX_sparse : IsXSparseTo G T' X x₀)
    (hB' : IsBlockadeIn G T' m w B')
    (hB'_sparse : ∀ i j : Fin m, i < j → IsXSparseTo G (B' j) (B' i) x₀) :
    IsBlockadeIn G T (m + 1) w (Fin.cons X B') ∧
      ∀ i j : Fin (m + 1), i < j →
        IsXSparseTo G (Fin.cons (α := fun _ => Finset V) X B' j)
          (Fin.cons (α := fun _ => Finset V) X B' i) x₀ := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i
    exact Fin.cases hXT (fun j => Subset.trans (hB'.subset_ambient j) hT'T) i
  · intro i
    exact Fin.cases hX_ne hB'.nonempty_blocks i
  · intro i j
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero =>
        intro hij
        exact (hij rfl).elim
      | succ j' =>
        intro _
        simp only [Fin.cons_zero, Fin.cons_succ]
        exact Disjoint.mono_right (hB'.subset_ambient j') hdisj
    | succ i' =>
      induction j using Fin.cases with
      | zero =>
        intro _
        simp only [Fin.cons_zero, Fin.cons_succ]
        exact (Disjoint.mono_right (hB'.subset_ambient i') hdisj).symm
      | succ j' =>
        intro hij
        simp only [Fin.cons_succ]
        exact hB'.pairwise_disjoint i' j' (fun h => hij (congrArg Fin.succ h))
  · intro i
    exact Fin.cases hX_w hB'.width_ge i
  · intro i j
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero =>
        intro hij
        exact (lt_irrefl _ hij).elim
      | succ j' =>
        intro _
        simp only [Fin.cons_zero, Fin.cons_succ]
        intro v hv
        exact hX_sparse v (hB'.subset_ambient j' hv)
    | succ i' =>
      induction j using Fin.cases with
      | zero =>
        intro hij
        exact (Nat.not_lt_zero _ hij).elim
      | succ j' =>
        intro hij
        simp only [Fin.cons_succ]
        exact hB'_sparse i' j' (Fin.succ_lt_succ_iff.mp hij)

/--
Inductive helper for `blockade_iteration_oneWay_xSparse`:
given $p \ge 1$ and $Y \subseteq F_0$ at step $s$ with $|Y| \ge (1 - by)^s |F_0|$ and
$s + p - 1 \le 2 y^{-1}$, $Y$ contains a $(p, y^{a+2}|F_0|)$-blockade $A$ such that
for all $i < j$, $A_j$ is $x_0$-sparse to $A_i$ in $G$.
-/
theorem blockade_iteration_oneWay_xSparse_aux (G : SimpleGraph V) (F₀ : Finset V) (a b y x₀ : ℝ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hy0 : 0 < y) (hyc : y ≤ (2 : ℝ) ^ (-4 * b))
    (hw₀ : 1 ≤ y ^ (a + 2) * (F₀.card : ℝ))
    (hstep : ∀ F ⊆ F₀, (2 : ℝ) ^ (-4 * b) * (F₀.card : ℝ) ≤ (F.card : ℝ) →
      ∃ X ⊆ F, ∃ Y ⊆ F, Disjoint X Y ∧
        y ^ a * (F.card : ℝ) ≤ (X.card : ℝ) ∧
        (1 - b * y) * (F.card : ℝ) ≤ (Y.card : ℝ) ∧
        IsXSparseTo G Y X x₀) :
    ∀ (p s : ℕ), 1 ≤ p →
      (s : ℝ) + (p : ℝ) - 1 ≤ 2 * y⁻¹ →
      ∀ Y ⊆ F₀, (1 - b * y) ^ s * (F₀.card : ℝ) ≤ (Y.card : ℝ) →
        ∃ A : Fin p → Finset V,
          IsBlockadeIn G Y p (y ^ (a + 2) * (F₀.card : ℝ)) A ∧
          ∀ i j : Fin p, i < j → IsXSparseTo G (A j) (A i) x₀ := by
  intro p
  induction p with
  | zero =>
    intro s hp
    omega
  | succ p' ih =>
    intro s _hp hs Y hYF₀ hY_card
    have hs_le : (s : ℝ) ≤ 2 * y⁻¹ := by
      have hp' : (0 : ℝ) ≤ (p' : ℝ) := Nat.cast_nonneg p'
      push_cast at hs
      linarith
    have hc_le_pow : (2 : ℝ) ^ (-4 * b) ≤ (1 - b * y) ^ s :=
      rpow_neg_four_le_one_sub_mul_pow hb hy0 hyc s hs_le
    have hY_ge_c : (2 : ℝ) ^ (-4 * b) * (F₀.card : ℝ) ≤ (Y.card : ℝ) :=
      le_trans (mul_le_mul_of_nonneg_right hc_le_pow (Nat.cast_nonneg _)) hY_card
    have hy_lt_one : y < 1 := by
      have : (2 : ℝ) ^ (-4 * b) ≤ (2 : ℝ) ^ (-4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      have : (2 : ℝ) ^ (-4 : ℝ) < 1 := by norm_num
      linarith
    have hy2_le_c : y ^ (a + 2) ≤ y ^ a * (2 : ℝ) ^ (-4 * b) := by
      have h1 : y ^ (a + 2) = y ^ a * y * y := by
        rw [Real.rpow_add hy0, Real.rpow_two]
        ring
      have h2 : y * y ≤ (2 : ℝ) ^ (-4 * b) * 1 :=
        mul_le_mul hyc hy_lt_one.le hy0.le (by positivity)
      rw [h1]
      nlinarith [Real.rpow_pos_of_pos hy0 a]
    have hY_ge_w₀ : y ^ (a + 2) * (F₀.card : ℝ) ≤ (Y.card : ℝ) := by
      have hya_le_one : y ^ a ≤ 1 := Real.rpow_le_one hy0.le hy_lt_one.le (by linarith)
      have : y ^ (a + 2) ≤ (2 : ℝ) ^ (-4 * b) := by
        nlinarith [Real.rpow_pos_of_pos two_pos (-4 * b)]
      exact le_trans (mul_le_mul_of_nonneg_right this (Nat.cast_nonneg _)) hY_ge_c
    have hY_ne : Y.Nonempty := by
      have : (1 : ℝ) ≤ (Y.card : ℝ) := le_trans hw₀ hY_ge_w₀
      exact card_pos.mp (by exact_mod_cast this)
    rcases Nat.eq_zero_or_pos p' with rfl | hp'
    · refine ⟨fun _ => Y, ⟨fun _ => Subset.rfl, fun _ => hY_ne, ?_, fun _ => hY_ge_w₀⟩, ?_⟩
      · intro i j hij
        exact (hij (Fin.ext (by omega))).elim
      · intro i j hij
        exact (by omega : ¬i < j).elim hij
    · obtain ⟨X, hXY, Y', hY'Y, hdisj, hX_card, hY'_card, hsparse⟩ := hstep Y hYF₀ hY_ge_c
      have hY'F₀ : Y' ⊆ F₀ := Subset.trans hY'Y hYF₀
      have hX_w₀ : y ^ (a + 2) * (F₀.card : ℝ) ≤ (X.card : ℝ) := by
        calc y ^ (a + 2) * (F₀.card : ℝ)
          _ ≤ y ^ a * ((2 : ℝ) ^ (-4 * b) * (F₀.card : ℝ)) := by nlinarith
          _ ≤ y ^ a * (Y.card : ℝ) :=
            mul_le_mul_of_nonneg_left hY_ge_c (by positivity)
          _ ≤ (X.card : ℝ) := hX_card
      have hX_ne : X.Nonempty := by
        have : (1 : ℝ) ≤ (X.card : ℝ) := le_trans hw₀ hX_w₀
        exact card_pos.mp (by exact_mod_cast this)
      have hY'_pow : (1 - b * y) ^ (s + 1) * (F₀.card : ℝ) ≤ (Y'.card : ℝ) := by
        have h1_sub_nonneg : 0 ≤ 1 - b * y := by
          have := mul_rpow_neg_four_le_quarter hb
          have : b * y ≤ 1 / 4 :=
            (mul_le_mul_of_nonneg_left hyc (by linarith)).trans this
          linarith
        rw [pow_succ']
        calc (1 - b * y) * (1 - b * y) ^ s * (F₀.card : ℝ)
          _ = (1 - b * y) * ((1 - b * y) ^ s * (F₀.card : ℝ)) := by ring
          _ ≤ (1 - b * y) * (Y.card : ℝ) :=
            mul_le_mul_of_nonneg_left hY_card h1_sub_nonneg
          _ ≤ (Y'.card : ℝ) := hY'_card
      have hs' : ((s + 1 : ℕ) : ℝ) + (p' : ℝ) - 1 ≤ 2 * y⁻¹ := by
        push_cast at hs ⊢
        linarith
      obtain ⟨A', hA'_block, hA'_sparse⟩ := ih (s + 1) hp' hs' Y' hY'F₀ hY'_pow
      exact ⟨Fin.cons X A',
        IsBlockadeIn.cons_oneWay_xSparse hXY hY'Y hdisj hX_ne hX_w₀ hsparse hA'_block hA'_sparse⟩

/--
**Lemma 2.8 (One-Way $x_0$-Sparse Blockade Iteration, `blockade_iteration_oneWay_xSparse`, `lem:blockade-iter`)**:
Let $a, b \ge 1$, $c = 2^{-4b}$, and $0 < y \le c$. Let $F_0$ be a vertex set with
$y^{a+2}|F_0| \ge 1$ such that every $F \subseteq F_0$ with $|F| \ge c |F_0|$ contains disjoint
subsets $X, Y \subseteq F$ with $|X| \ge y^a |F|$, $|Y| \ge (1 - by)|F|$, and $Y$ $x_0$-sparse
to $X$ (`IsXSparseTo G Y X x₀`). Then $F_0$ contains a $(\lceil y^{-1} \rceil, y^{a+2}|F_0|)$-blockade
$A$ in $G$ such that for all $i < j$, $A_j$ is $x_0$-sparse to $A_i$.
-/
theorem blockade_iteration_oneWay_xSparse (G : SimpleGraph V) (F₀ : Finset V) (a b y x₀ : ℝ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hy0 : 0 < y) (hyc : y ≤ (2 : ℝ) ^ (-4 * b))
    (hw₀ : 1 ≤ y ^ (a + 2) * (F₀.card : ℝ))
    (hstep : ∀ F ⊆ F₀, (2 : ℝ) ^ (-4 * b) * (F₀.card : ℝ) ≤ (F.card : ℝ) →
      ∃ X ⊆ F, ∃ Y ⊆ F, Disjoint X Y ∧
        y ^ a * (F.card : ℝ) ≤ (X.card : ℝ) ∧
        (1 - b * y) * (F.card : ℝ) ≤ (Y.card : ℝ) ∧
        IsXSparseTo G Y X x₀) :
    ∃ A : Fin ⌈y⁻¹⌉₊ → Finset V,
      IsBlockadeIn G F₀ ⌈y⁻¹⌉₊ (y ^ (a + 2) * (F₀.card : ℝ)) A ∧
      ∀ i j : Fin ⌈y⁻¹⌉₊, i < j → IsXSparseTo G (A j) (A i) x₀ := by
  let k := ⌈y⁻¹⌉₊
  have hk_pos : 1 ≤ k := Nat.ceil_pos.mpr (inv_pos.mpr hy0)
  have hk_lt : (k : ℝ) < y⁻¹ + 1 := Nat.ceil_lt_add_one (inv_nonneg.mpr hy0.le)
  have hy_inv_pos : 0 < y⁻¹ := inv_pos.mpr hy0
  have hs0 : ((0 : ℕ) : ℝ) + (k : ℝ) - 1 ≤ 2 * y⁻¹ := by
    push_cast
    linarith
  have hF₀_pow : (1 - b * y) ^ 0 * (F₀.card : ℝ) ≤ (F₀.card : ℝ) := by simp
  exact blockade_iteration_oneWay_xSparse_aux G F₀ a b y x₀ ha hb hy0 hyc hw₀ hstep
    k 0 hk_pos hs0 F₀ Subset.rfl hF₀_pow

/--
Specialization of `blockade_iteration_oneWay_xSparse` to $b = 4$ ($c = 2^{-16}$ and retention
factor $1 - 4y$, as used in Proposition 5.3 of `FMBV4-016_readable.tex`).
-/
theorem blockade_iteration_oneWay_xSparse_four (G : SimpleGraph V) (S : Finset V) (a₃ y x₀ : ℝ)
    (ha₃ : 1 ≤ a₃) (hy0 : 0 < y) (hyc : y ≤ (2 : ℝ) ^ (-16 : ℝ))
    (hw₀ : 1 ≤ y ^ (a₃ + 2) * (S.card : ℝ))
    (hstep : ∀ F' ⊆ S, (2 : ℝ) ^ (-16 : ℝ) * (S.card : ℝ) ≤ (F'.card : ℝ) →
      ∃ X ⊆ F', ∃ Y ⊆ F', Disjoint X Y ∧
        y ^ a₃ * (F'.card : ℝ) ≤ (X.card : ℝ) ∧
        (1 - 4 * y) * (F'.card : ℝ) ≤ (Y.card : ℝ) ∧
        IsXSparseTo G Y X x₀) :
    ∃ A : Fin ⌈y⁻¹⌉₊ → Finset V,
      IsBlockadeIn G S ⌈y⁻¹⌉₊ (y ^ (a₃ + 2) * (S.card : ℝ)) A ∧
      ∀ i j : Fin ⌈y⁻¹⌉₊, i < j → IsXSparseTo G (A j) (A i) x₀ := by
  have hyc' : y ≤ (2 : ℝ) ^ (-4 * (4 : ℝ)) := by
    convert hyc using 2
    norm_num
  have hstep' : ∀ F' ⊆ S, (2 : ℝ) ^ (-4 * (4 : ℝ)) * (S.card : ℝ) ≤ (F'.card : ℝ) →
      ∃ X ⊆ F', ∃ Y ⊆ F', Disjoint X Y ∧
        y ^ a₃ * (F'.card : ℝ) ≤ (X.card : ℝ) ∧
        (1 - 4 * y) * (F'.card : ℝ) ≤ (Y.card : ℝ) ∧
        IsXSparseTo G Y X x₀ := by
    intro F' hF' hcard
    apply hstep F' hF'
    convert hcard using 2
    norm_num
  exact blockade_iteration_oneWay_xSparse G S a₃ 4 y x₀ ha₃ (by norm_num) hy0 hyc' hw₀ hstep'

/-- If $A$ is $x_0$-sparse to $B$, then $(A, B)$ is weakly $x_0$-sparse. -/
theorem isWeaklySparsePair_of_isXSparseTo {G : SimpleGraph V} {A B : Finset V} {x₀ : ℝ}
    (h : IsXSparseTo G A B x₀) : IsWeaklySparsePair G A B x₀ := by
  unfold IsWeaklySparsePair
  rw [crossEdgeCount_eq_sum_left]
  calc (↑(∑ u ∈ A, (neighborFinsetIn G u B).card) : ℝ)
    _ = ∑ u ∈ A, ((neighborFinsetIn G u B).card : ℝ) := by push_cast; rfl
    _ ≤ ∑ _u ∈ A, x₀ * (B.card : ℝ) := sum_le_sum (fun u hu => h u hu)
    _ = (A.card : ℝ) * (x₀ * (B.card : ℝ)) := by rw [sum_const, nsmul_eq_mul]
    _ = x₀ * (A.card : ℝ) * (B.card : ℝ) := by ring

/-- Symmetry of `IsWeaklySparsePair`. -/
private theorem IsWeaklySparsePair.symm' {G : SimpleGraph V} {A B : Finset V} {x₀ : ℝ}
    (h : IsWeaklySparsePair G A B x₀) : IsWeaklySparsePair G B A x₀ := by
  unfold IsWeaklySparsePair at h ⊢
  rw [crossEdgeCount_comm]
  calc (crossEdgeCount G A B : ℝ)
    _ ≤ x₀ * (A.card : ℝ) * (B.card : ℝ) := h
    _ = x₀ * (B.card : ℝ) * (A.card : ℝ) := by ring

/--
Equal-size subset pre-sampling for a one-way $x_0$-sparse blockade:
given an $(\ell, m)$-blockade $B$ in $F$ ($m \ge 1$, $x_0 \ge 0$) such that $B_i$ is $x_0$-sparse
to $B_j$ for all $i < j$, sequential subset selection produces equal-sized subsets $X_i \subseteq B_i$
with $|X_i| = m$ forming an $(\ell, m)$-blockade in $F$ whose distinct pairs are weakly
$(\ell x_0)$-sparse in $G$.
-/
theorem equal_size_presampling_of_oneWay_xSparse (G : SimpleGraph V) (F : Finset V) (ℓ m : ℕ)
    (x₀ : ℝ) (hm : 1 ≤ m) (hx₀ : 0 ≤ x₀)
    (B : Fin ℓ → Finset V) (hB : IsBlockadeIn G F ℓ (m : ℝ) B)
    (h_oneWay : ∀ i j : Fin ℓ, i < j → IsXSparseTo G (B i) (B j) x₀) :
    ∃ X : Fin ℓ → Finset V,
      (∀ i, X i ⊆ B i) ∧
      (∀ i, (X i).card = m) ∧
      IsBlockadeIn G F ℓ (m : ℝ) X ∧
      (∀ i j : Fin ℓ, i ≠ j → IsWeaklySparsePair G (X i) (X j) ((ℓ : ℝ) * x₀)) := by
  have h_ind : ∀ k : ℕ, k ≤ ℓ →
      ∃ X : Fin ℓ → Finset V,
        (∀ i : Fin ℓ, X i ⊆ B i) ∧
        (∀ i : Fin ℓ, i.val < k → (X i).card = m) ∧
        (∀ i : Fin ℓ, k ≤ i.val → X i = B i) ∧
        (∀ i j : Fin ℓ, i < j → j.val < k →
          IsWeaklySparsePair G (X i) (X j) ((ℓ : ℝ) * x₀)) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨B, fun _ => Subset.rfl, fun _ hi => by omega, fun _ _ => rfl,
        fun _ _ _ hj => by omega⟩
    | succ k ih =>
      intro hk
      obtain ⟨X, hX_sub, hX_card, hX_eq, hX_sparse⟩ := ih (by omega)
      let r : Fin ℓ := ⟨k, hk⟩
      let J := (Finset.univ : Finset (Fin ℓ)).filter (fun i : Fin ℓ => i < r)
      let w : V → ℝ := fun u => ∑ i ∈ J, ((neighborFinsetIn G u (X i)).card : ℝ)
      have hw_nonneg : ∀ u ∈ B r, 0 ≤ w u :=
        fun _ _ => sum_nonneg (fun _ _ => Nat.cast_nonneg _)
      have h_cross_le : ∀ i ∈ J,
          (crossEdgeCount G (B r) (X i) : ℝ) ≤ x₀ * (m : ℝ) * ((B r).card : ℝ) := by
        intro i hi
        simp only [J, mem_filter, mem_univ, true_and] at hi
        rw [crossEdgeCount_comm, crossEdgeCount_eq_sum_left]
        calc (↑(∑ v ∈ X i, (neighborFinsetIn G v (B r)).card) : ℝ)
          _ = ∑ v ∈ X i, ((neighborFinsetIn G v (B r)).card : ℝ) := by push_cast; rfl
          _ ≤ ∑ _v ∈ X i, x₀ * ((B r).card : ℝ) :=
            sum_le_sum (fun v hv => h_oneWay i r hi v (hX_sub i hv))
          _ = ((X i).card : ℝ) * (x₀ * ((B r).card : ℝ)) := by rw [sum_const, nsmul_eq_mul]
          _ = x₀ * (m : ℝ) * ((B r).card : ℝ) := by rw [hX_card i hi]; ring
      have hsum_w : ∑ u ∈ B r, w u ≤ (ℓ : ℝ) * (x₀ * (m : ℝ) * ((B r).card : ℝ)) := by
        dsimp [w]
        rw [sum_comm]
        calc ∑ i ∈ J, ∑ u ∈ B r, ((neighborFinsetIn G u (X i)).card : ℝ)
          _ = ∑ i ∈ J, (crossEdgeCount G (B r) (X i) : ℝ) := by
            refine sum_congr rfl (fun i _ => ?_)
            exact_mod_cast (crossEdgeCount_eq_sum_left G (B r) (X i)).symm
          _ ≤ ∑ _i ∈ J, x₀ * (m : ℝ) * ((B r).card : ℝ) := sum_le_sum h_cross_le
          _ = (J.card : ℝ) * (x₀ * (m : ℝ) * ((B r).card : ℝ)) := by
            rw [sum_const, nsmul_eq_mul]
          _ ≤ (ℓ : ℝ) * (x₀ * (m : ℝ) * ((B r).card : ℝ)) := by
            have hJ_le : (J.card : ℝ) ≤ (ℓ : ℝ) := by
              have : J.card ≤ (Finset.univ : Finset (Fin ℓ)).card := card_filter_le _ _
              rw [card_univ, Fintype.card_fin] at this
              exact_mod_cast this
            exact mul_le_mul_of_nonneg_right hJ_le (by positivity)
      have hm_Br : m ≤ (B r).card := by exact_mod_cast hB.width_ge r
      obtain ⟨X_r, hXr_sub, hXr_card, hXr_sum⟩ :=
        exists_subset_card_eq_sum_le (B r) w hw_nonneg m hm_Br
      have hXr_pair : ∀ i : Fin ℓ, i < r →
          IsWeaklySparsePair G (X i) X_r ((ℓ : ℝ) * x₀) := by
        intro i hir
        have hiJ : i ∈ J := mem_filter.mpr ⟨mem_univ i, hir⟩
        have h_le_w : (crossEdgeCount G X_r (X i) : ℝ) ≤ ∑ u ∈ X_r, w u := by
          dsimp [w]
          rw [sum_comm]
          have h_eq : (crossEdgeCount G X_r (X i) : ℝ) =
              ∑ u ∈ X_r, ((neighborFinsetIn G u (X i)).card : ℝ) := by
            exact_mod_cast crossEdgeCount_eq_sum_left G X_r (X i)
          rw [h_eq]
          exact single_le_sum
            (f := fun i' => ∑ u ∈ X_r, ((neighborFinsetIn G u (X i')).card : ℝ))
            (fun _ _ => sum_nonneg (fun _ _ => Nat.cast_nonneg _)) hiJ
        have hBr_pos : (0 : ℝ) < ((B r).card : ℝ) :=
          lt_of_lt_of_le (by positivity : (0 : ℝ) < (m : ℝ)) (hB.width_ge r)
        have hmul : ((B r).card : ℝ) * (crossEdgeCount G X_r (X i) : ℝ) ≤
            ((B r).card : ℝ) * (((ℓ : ℝ) * x₀) * (m : ℝ) * (m : ℝ)) := by
          calc ((B r).card : ℝ) * (crossEdgeCount G X_r (X i) : ℝ)
            _ ≤ ((B r).card : ℝ) * (∑ u ∈ X_r, w u) :=
              mul_le_mul_of_nonneg_left h_le_w hBr_pos.le
            _ ≤ (m : ℝ) * (∑ u ∈ B r, w u) := hXr_sum
            _ ≤ (m : ℝ) * ((ℓ : ℝ) * (x₀ * (m : ℝ) * ((B r).card : ℝ))) :=
              mul_le_mul_of_nonneg_left hsum_w (Nat.cast_nonneg _)
            _ = ((B r).card : ℝ) * (((ℓ : ℝ) * x₀) * (m : ℝ) * (m : ℝ)) := by ring
        unfold IsWeaklySparsePair
        rw [crossEdgeCount_comm, hX_card i hir, hXr_card]
        exact le_of_mul_le_mul_left hmul hBr_pos
      let X' : Fin ℓ → Finset V := fun i => if i = r then X_r else X i
      refine ⟨X', ?_, ?_, ?_, ?_⟩
      · intro i
        dsimp [X']
        split_ifs with hir
        · subst hir; exact hXr_sub
        · exact hX_sub i
      · intro i hi
        dsimp [X']
        split_ifs with hir
        · exact hXr_card
        · have hik : i.val < k := by
            have : i.val ≠ k := fun h => hir (Fin.ext h)
            omega
          exact hX_card i hik
      · intro i hi
        have hir : i ≠ r := fun h => by
          have : i.val = k := congrArg Fin.val h
          omega
        dsimp [X']
        rw [if_neg hir]
        exact hX_eq i (by omega)
      · intro i j hij hj_lt
        have hir : i ≠ r := fun h => by
          have : i.val = k := congrArg Fin.val h
          have : i.val < j.val := hij
          omega
        dsimp [X']
        rw [if_neg hir]
        split_ifs with hjr
        · subst hjr
          exact hXr_pair i hij
        · have hjk : j.val < k := by
            have : j.val ≠ k := fun h => hjr (Fin.ext h)
            omega
          exact hX_sparse i j hij hjk
  obtain ⟨X, hX_sub, hX_card', _, hX_sparse⟩ := h_ind ℓ le_rfl
  have hX_card : ∀ i : Fin ℓ, (X i).card = m := fun i => hX_card' i i.isLt
  have hX_block : IsBlockadeIn G F ℓ (m : ℝ) X := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      exact Subset.trans (hX_sub i) (hB.subset_ambient i)
    · intro i
      exact card_pos.mp (by rw [hX_card i]; omega)
    · intro i j hij
      exact Disjoint.mono (hX_sub i) (hX_sub j) (hB.pairwise_disjoint i j hij)
    · intro i
      rw [hX_card i]
  refine ⟨X, hX_sub, hX_card, hX_block, ?_⟩
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hX_sparse i j hlt j.isLt
  · exact (hX_sparse j i hgt i.isLt).symm'

/--
Weak-to-strong sparsity cleaning for equal-sized blocks:
given an $(\ell, m)$-blockade $X$ in $F$ with $|X_i| = m \ge 1$ whose distinct block pairs are
weakly $(\ell x_0)$-sparse ($x_0 \ge 0$), removing high-degree vertices yields subsets
$D_i \subseteq X_i$ with $\frac{1}{2} m \le |D_i| \le m$ forming a complete-or-$(2 \ell^3 x_0)$-sparse
$(\ell, \frac{1}{2} m)$-blockade in $F$ (in fact, every distinct pair is $(2 \ell^3 x_0)$-sparse
in both directions).
-/
theorem weak_to_strong_cleaning_of_equal_size (G : SimpleGraph V) (F : Finset V) (ℓ m : ℕ)
    (x₀ : ℝ) (hm : 1 ≤ m) (hx₀ : 0 ≤ x₀)
    (X : Fin ℓ → Finset V) (hX : IsBlockadeIn G F ℓ (m : ℝ) X) (hX_card : ∀ i, (X i).card = m)
    (hpairs : ∀ i j : Fin ℓ, i ≠ j → IsWeaklySparsePair G (X i) (X j) ((ℓ : ℝ) * x₀)) :
    ∃ D : Fin ℓ → Finset V,
      (∀ i, D i ⊆ X i) ∧
      (∀ i, (1 / 2 : ℝ) * (m : ℝ) ≤ ((D i).card : ℝ) ∧ ((D i).card : ℝ) ≤ (m : ℝ)) ∧
      IsCompleteOrXSparseBlockadeIn G F ℓ ((1 / 2 : ℝ) * (m : ℝ)) (2 * (ℓ : ℝ) ^ 3 * x₀) D := by
  classical
  let δ := (ℓ : ℝ) ^ 3 * x₀
  have hδ_nonneg : 0 ≤ δ := by positivity
  let bad (i j : Fin ℓ) : Finset V :=
    if i = j then ∅
    else (X i).filter (fun u => δ * (m : ℝ) < ((neighborFinsetIn G u (X j)).card : ℝ))
  have hbad_card : ∀ i j : Fin ℓ, 2 * (ℓ : ℝ) * ((bad i j).card : ℝ) ≤ (m : ℝ) := by
    intro i j
    dsimp [bad]
    split_ifs with hij
    · simp only [card_empty, Nat.cast_zero, mul_zero]
      positivity
    · have hℓ2 : 2 ≤ ℓ := by
        have : i.val ≠ j.val := fun h => hij (Fin.ext h)
        omega
      have hℓ2_real : (2 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ2
      have hsparse : (crossEdgeCount G (X i) (X j) : ℝ) ≤
          ((ℓ : ℝ) * x₀) * (m : ℝ) * (m : ℝ) := by
        have hsp := hpairs i j hij
        unfold IsWeaklySparsePair at hsp
        rwa [hX_card i, hX_card j] at hsp
      let B_ij := (X i).filter (fun u => δ * (m : ℝ) < ((neighborFinsetIn G u (X j)).card : ℝ))
      have hmarkov : (B_ij.card : ℝ) * (δ * (m : ℝ)) ≤ (crossEdgeCount G (X i) (X j) : ℝ) := by
        calc (B_ij.card : ℝ) * (δ * (m : ℝ))
          _ = ∑ _u ∈ B_ij, δ * (m : ℝ) := by rw [sum_const, nsmul_eq_mul]
          _ ≤ ∑ u ∈ B_ij, ((neighborFinsetIn G u (X j)).card : ℝ) := by
            refine sum_le_sum (fun u hu => ?_)
            simp only [B_ij, mem_filter] at hu
            exact hu.2.le
          _ ≤ ∑ u ∈ X i, ((neighborFinsetIn G u (X j)).card : ℝ) :=
            sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.cast_nonneg _)
          _ = (crossEdgeCount G (X i) (X j) : ℝ) := by
            exact_mod_cast (crossEdgeCount_eq_sum_left G (X i) (X j)).symm
      by_cases hx₀_pos : 0 < x₀
      · have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
        have hdenom_pos : 0 < (ℓ : ℝ) * x₀ * (m : ℝ) := by positivity
        have h2ℓ_le : 2 * (ℓ : ℝ) * ((ℓ : ℝ) * x₀ * (m : ℝ)) ≤ δ * (m : ℝ) := by
          have h2ℓ_le_sq : 2 * (ℓ : ℝ) ≤ (ℓ : ℝ) ^ 2 := by nlinarith
          calc 2 * (ℓ : ℝ) * ((ℓ : ℝ) * x₀ * (m : ℝ))
            _ ≤ (ℓ : ℝ) ^ 2 * ((ℓ : ℝ) * x₀ * (m : ℝ)) :=
              mul_le_mul_of_nonneg_right h2ℓ_le_sq hdenom_pos.le
            _ = δ * (m : ℝ) := by dsimp [δ]; ring
        have h1 : (2 * (ℓ : ℝ) * (B_ij.card : ℝ)) * ((ℓ : ℝ) * x₀ * (m : ℝ)) ≤
            (m : ℝ) * ((ℓ : ℝ) * x₀ * (m : ℝ)) := by
          calc (2 * (ℓ : ℝ) * (B_ij.card : ℝ)) * ((ℓ : ℝ) * x₀ * (m : ℝ))
            _ = (B_ij.card : ℝ) * (2 * (ℓ : ℝ) * ((ℓ : ℝ) * x₀ * (m : ℝ))) := by ring
            _ ≤ (B_ij.card : ℝ) * (δ * (m : ℝ)) :=
              mul_le_mul_of_nonneg_left h2ℓ_le (Nat.cast_nonneg _)
            _ ≤ ((ℓ : ℝ) * x₀) * (m : ℝ) * (m : ℝ) := hmarkov.trans hsparse
            _ = (m : ℝ) * ((ℓ : ℝ) * x₀ * (m : ℝ)) := by ring
        exact le_of_mul_le_mul_right h1 hdenom_pos
      · have hx₀_zero : x₀ = 0 := le_antisymm (not_lt.mp hx₀_pos) hx₀
        have hB_empty : B_ij = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro u hu
          simp only [B_ij, mem_filter] at hu
          have hcross0 : (crossEdgeCount G (X i) (X j) : ℝ) ≤ 0 := by
            linarith [show ((ℓ : ℝ) * x₀) * (m : ℝ) * (m : ℝ) = 0 by rw [hx₀_zero]; ring]
          have hu_le : (neighborFinsetIn G u (X j)).card ≤ crossEdgeCount G (X i) (X j) := by
            rw [crossEdgeCount_eq_sum_left]
            exact single_le_sum
              (f := fun v => (neighborFinsetIn G v (X j)).card)
              (fun _ _ => Nat.zero_le _) hu.1
          have hu_le_real : ((neighborFinsetIn G u (X j)).card : ℝ) ≤
              (crossEdgeCount G (X i) (X j) : ℝ) := by exact_mod_cast hu_le
          have hδ0 : δ * (m : ℝ) = 0 := by dsimp [δ]; rw [hx₀_zero]; ring
          linarith [hu.2]
        change 2 * (ℓ : ℝ) * (B_ij.card : ℝ) ≤ (m : ℝ)
        rw [hB_empty, card_empty, Nat.cast_zero, mul_zero]
        positivity
  let D : Fin ℓ → Finset V := fun i => X i \ (Finset.univ : Finset (Fin ℓ)).biUnion (bad i)
  have hD_sub : ∀ i, D i ⊆ X i := fun _ => sdiff_subset
  have hD_bounds : ∀ i, (1 / 2 : ℝ) * (m : ℝ) ≤ ((D i).card : ℝ) ∧ ((D i).card : ℝ) ≤ (m : ℝ) := by
    intro i
    have hℓ_pos : (0 : ℝ) < (ℓ : ℝ) := by
      have : 0 < ℓ := Nat.pos_of_ne_zero (fun h => Fin.elim0 (h ▸ i))
      exact_mod_cast this
    constructor
    · have hbiUnion_le : (((Finset.univ : Finset (Fin ℓ)).biUnion (bad i)).card : ℝ) ≤
          (1 / 2 : ℝ) * (m : ℝ) := by
        have hcard_le_sum : (((Finset.univ : Finset (Fin ℓ)).biUnion (bad i)).card : ℝ) ≤
            ∑ j : Fin ℓ, ((bad i j).card : ℝ) := by
          exact_mod_cast card_biUnion_le
        have hsum_mul : 2 * (ℓ : ℝ) * (∑ j : Fin ℓ, ((bad i j).card : ℝ)) ≤
            (ℓ : ℝ) * (m : ℝ) := by
          rw [mul_sum]
          calc ∑ j : Fin ℓ, 2 * (ℓ : ℝ) * ((bad i j).card : ℝ)
            _ ≤ ∑ _j : Fin ℓ, (m : ℝ) := sum_le_sum (fun j _ => hbad_card i j)
            _ = (ℓ : ℝ) * (m : ℝ) := by
              rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hsum_le : ∑ j : Fin ℓ, ((bad i j).card : ℝ) ≤ (1 / 2 : ℝ) * (m : ℝ) := by
          have h1 : (ℓ : ℝ) * (2 * ∑ j : Fin ℓ, ((bad i j).card : ℝ)) ≤
              (ℓ : ℝ) * (m : ℝ) := by linarith
          have h2 : 2 * ∑ j : Fin ℓ, ((bad i j).card : ℝ) ≤ (m : ℝ) :=
            le_of_mul_le_mul_left h1 hℓ_pos
          linarith
        exact hcard_le_sum.trans hsum_le
      have hsdiff_ge : (X i).card ≤
          (D i).card + ((Finset.univ : Finset (Fin ℓ)).biUnion (bad i)).card :=
        card_le_card_sdiff_add_card
      have hsdiff_real : ((X i).card : ℝ) ≤
          ((D i).card : ℝ) + (((Finset.univ : Finset (Fin ℓ)).biUnion (bad i)).card : ℝ) := by
        exact_mod_cast hsdiff_ge
      rw [hX_card i] at hsdiff_real
      linarith
    · have : (D i).card ≤ (X i).card := card_le_card (hD_sub i)
      rw [hX_card i] at this
      exact_mod_cast this
  have hD_deg : ∀ i j : Fin ℓ, i ≠ j →
      ∀ u ∈ D i, ((neighborFinsetIn G u (D j)).card : ℝ) ≤
        (2 * (ℓ : ℝ) ^ 3 * x₀) * ((D j).card : ℝ) := by
    intro i j hij u hu
    have hu_not_bad : u ∉ bad i j := by
      simp only [D, mem_sdiff, mem_biUnion, mem_univ, true_and, not_exists] at hu
      exact hu.2 j
    have hu_Xi : u ∈ X i := hD_sub i hu
    have hdeg_Xj : ((neighborFinsetIn G u (X j)).card : ℝ) ≤ δ * (m : ℝ) := by
      by_contra! hgt
      dsimp [bad] at hu_not_bad
      rw [if_neg hij, mem_filter] at hu_not_bad
      exact hu_not_bad ⟨hu_Xi, hgt⟩
    have hdeg_Dj_le_Xj : (neighborFinsetIn G u (D j)).card ≤ (neighborFinsetIn G u (X j)).card := by
      apply card_le_card
      intro v hv
      rw [mem_neighborFinsetIn] at hv ⊢
      exact ⟨hD_sub j hv.1, hv.2⟩
    have hDj_ge := (hD_bounds j).1
    calc ((neighborFinsetIn G u (D j)).card : ℝ)
      _ ≤ ((neighborFinsetIn G u (X j)).card : ℝ) := by exact_mod_cast hdeg_Dj_le_Xj
      _ ≤ δ * (m : ℝ) := hdeg_Xj
      _ ≤ δ * (2 * ((D j).card : ℝ)) := by nlinarith
      _ = (2 * (ℓ : ℝ) ^ 3 * x₀) * ((D j).card : ℝ) := by dsimp [δ]; ring
  refine ⟨D, hD_sub, hD_bounds, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i
    exact Subset.trans (hD_sub i) (hX.subset_ambient i)
  · intro i
    have hpos : (0 : ℝ) < ((D i).card : ℝ) := by
      have hm_pos : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith [(hD_bounds i).1]
    exact card_pos.mp (by exact_mod_cast hpos)
  · intro i j hij
    exact Disjoint.mono (hD_sub i) (hD_sub j) (hX.pairwise_disjoint i j hij)
  · intro i
    exact (hD_bounds i).1
  · intro i j hij
    exact Or.inr ⟨hD_deg j i hij.symm, hD_deg i j hij⟩

/--
Converting any one-way $x_0$-sparse blockade $A$ (with `IsXSparseTo G (A j) (A i) x₀` for $i < j$
and width $\ge m \ge 1$) into a two-way complete-or-$(2 \ell^3 x_0)$-sparse $(\ell, \frac{1}{2}m)$-blockade
$D$ with $D_i \subseteq A_i$ and $\frac{1}{2} m \le |D_i| \le m$.
-/
theorem oneWay_xSparse_to_completeOrXSparseBlockade (G : SimpleGraph V) (S : Finset V) (ℓ m : ℕ)
    (w x₀ : ℝ) (hm : 1 ≤ m) (hm_le : (m : ℝ) ≤ w) (hx₀ : 0 ≤ x₀)
    (A : Fin ℓ → Finset V) (hA : IsBlockadeIn G S ℓ w A)
    (h_oneWay : ∀ i j : Fin ℓ, i < j → IsXSparseTo G (A j) (A i) x₀) :
    ∃ D : Fin ℓ → Finset V,
      (∀ i, D i ⊆ A i) ∧
      (∀ i, (1 / 2 : ℝ) * (m : ℝ) ≤ ((D i).card : ℝ) ∧ ((D i).card : ℝ) ≤ (m : ℝ)) ∧
      IsCompleteOrXSparseBlockadeIn G S ℓ ((1 / 2 : ℝ) * (m : ℝ)) (2 * (ℓ : ℝ) ^ 3 * x₀) D := by
  let B : Fin ℓ → Finset V := fun i => A i.rev
  have hB : IsBlockadeIn G S ℓ (m : ℝ) B := by
    refine ⟨fun i => hA.subset_ambient i.rev, fun i => hA.nonempty_blocks i.rev, ?_, ?_⟩
    · intro i j hij
      exact hA.pairwise_disjoint i.rev j.rev (fun h => hij (Fin.rev_injective h))
    · intro i
      exact le_trans hm_le (hA.width_ge i.rev)
  have hB_oneWay : ∀ i j : Fin ℓ, i < j → IsXSparseTo G (B i) (B j) x₀ := by
    intro i j hij
    exact h_oneWay j.rev i.rev (Fin.rev_lt_rev.mpr hij)
  obtain ⟨X, hX_sub, hX_card, hX_block, hX_pairs⟩ :=
    equal_size_presampling_of_oneWay_xSparse G S ℓ m x₀ hm hx₀ B hB hB_oneWay
  obtain ⟨D', hD'_sub, hD'_bounds, hD'_block⟩ :=
    weak_to_strong_cleaning_of_equal_size G S ℓ m x₀ hm hx₀ X hX_block hX_card hX_pairs
  let D : Fin ℓ → Finset V := fun i => D' i.rev
  refine ⟨D, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i
    have h1 : D i ⊆ B i.rev := Subset.trans (hD'_sub i.rev) (hX_sub i.rev)
    simpa [B, Fin.rev_rev] using h1
  · intro i
    exact hD'_bounds i.rev
  · intro i
    exact hD'_block.1.subset_ambient i.rev
  · intro i
    exact hD'_block.1.nonempty_blocks i.rev
  · intro i j hij
    exact hD'_block.1.pairwise_disjoint i.rev j.rev (fun h => hij (Fin.rev_injective h))
  · intro i
    exact hD'_block.1.width_ge i.rev
  · intro i j hij
    exact hD'_block.2 i.rev j.rev (fun h => hij (Fin.rev_injective h))

/--
**Lemma 2.8 (`lem:blockade-iter`, Blockade Iteration Lemma for $x$-Sparse Pairs,
`blockade_iteration_xSparse`)**:
Let $a, b \ge 1$, $c = 2^{-4b}$, $0 < y \le c$, $x_0 \ge 0$, and $1 \le m \le y^{a+2}|F_0|$.
Suppose every $F \subseteq F_0$ with $|F| \ge c |F_0|$ contains disjoint subsets $X, Y \subseteq F$
with $|X| \ge y^a |F|$, $|Y| \ge (1 - by)|F|$, and $Y$ $x_0$-sparse to $X$ (`IsXSparseTo G Y X x₀`).
Then $F_0$ contains a complete-or-$(2 \lceil y^{-1} \rceil^3 x_0)$-sparse
$(\lceil y^{-1} \rceil, \frac{1}{2} m)$-blockade $D$ with $\frac{1}{2} m \le |D_i| \le m$ for all $i$.
-/
theorem blockade_iteration_xSparse (G : SimpleGraph V) (F₀ : Finset V) (a b y x₀ : ℝ) (m : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hy0 : 0 < y) (hyc : y ≤ (2 : ℝ) ^ (-4 * b))
    (hx₀ : 0 ≤ x₀) (hm : 1 ≤ m) (hm_le : (m : ℝ) ≤ y ^ (a + 2) * (F₀.card : ℝ))
    (hstep : ∀ F ⊆ F₀, (2 : ℝ) ^ (-4 * b) * (F₀.card : ℝ) ≤ (F.card : ℝ) →
      ∃ X ⊆ F, ∃ Y ⊆ F, Disjoint X Y ∧
        y ^ a * (F.card : ℝ) ≤ (X.card : ℝ) ∧
        (1 - b * y) * (F.card : ℝ) ≤ (Y.card : ℝ) ∧
        IsXSparseTo G Y X x₀) :
    ∃ D : Fin ⌈y⁻¹⌉₊ → Finset V,
      (∀ i, (1 / 2 : ℝ) * (m : ℝ) ≤ ((D i).card : ℝ) ∧ ((D i).card : ℝ) ≤ (m : ℝ)) ∧
      IsCompleteOrXSparseBlockadeIn G F₀ ⌈y⁻¹⌉₊ ((1 / 2 : ℝ) * (m : ℝ))
        (2 * (⌈y⁻¹⌉₊ : ℝ) ^ 3 * x₀) D := by
  have hw₀ : 1 ≤ y ^ (a + 2) * (F₀.card : ℝ) :=
    le_trans (by exact_mod_cast hm) hm_le
  obtain ⟨A, hA_block, hA_oneWay⟩ :=
    blockade_iteration_oneWay_xSparse G F₀ a b y x₀ ha hb hy0 hyc hw₀ hstep
  obtain ⟨D, _, hD_bounds, hD_block⟩ :=
    oneWay_xSparse_to_completeOrXSparseBlockade G F₀ ⌈y⁻¹⌉₊ m
      (y ^ (a + 2) * (F₀.card : ℝ)) x₀ hm hm_le hx₀ A hA_block hA_oneWay
  exact ⟨D, hD_bounds, hD_block⟩

/--
Specialization of `blockade_iteration_xSparse` to $b = 4$ ($c = 2^{-16}$ and retention factor
$1 - 4y$, matching Outcome 2 of `upside_down_comb_extraction` in Proposition 5.3 of `FMBV4-016_readable.tex`).
-/
theorem blockade_iteration_xSparse_four (G : SimpleGraph V) (S : Finset V) (a₃ y x₀ : ℝ) (m : ℕ)
    (ha₃ : 1 ≤ a₃) (hy0 : 0 < y) (hyc : y ≤ (2 : ℝ) ^ (-16 : ℝ))
    (hx₀ : 0 ≤ x₀) (hm : 1 ≤ m) (hm_le : (m : ℝ) ≤ y ^ (a₃ + 2) * (S.card : ℝ))
    (hstep : ∀ F' ⊆ S, (2 : ℝ) ^ (-16 : ℝ) * (S.card : ℝ) ≤ (F'.card : ℝ) →
      ∃ X ⊆ F', ∃ Y ⊆ F', Disjoint X Y ∧
        y ^ a₃ * (F'.card : ℝ) ≤ (X.card : ℝ) ∧
        (1 - 4 * y) * (F'.card : ℝ) ≤ (Y.card : ℝ) ∧
        IsXSparseTo G Y X x₀) :
    ∃ D : Fin ⌈y⁻¹⌉₊ → Finset V,
      (∀ i, (1 / 2 : ℝ) * (m : ℝ) ≤ ((D i).card : ℝ) ∧ ((D i).card : ℝ) ≤ (m : ℝ)) ∧
      IsCompleteOrXSparseBlockadeIn G S ⌈y⁻¹⌉₊ ((1 / 2 : ℝ) * (m : ℝ))
        (2 * (⌈y⁻¹⌉₊ : ℝ) ^ 3 * x₀) D := by
  have hyc' : y ≤ (2 : ℝ) ^ (-4 * (4 : ℝ)) := by
    convert hyc using 2
    norm_num
  have hstep' : ∀ F' ⊆ S, (2 : ℝ) ^ (-4 * (4 : ℝ)) * (S.card : ℝ) ≤ (F'.card : ℝ) →
      ∃ X ⊆ F', ∃ Y ⊆ F', Disjoint X Y ∧
        y ^ a₃ * (F'.card : ℝ) ≤ (X.card : ℝ) ∧
        (1 - 4 * y) * (F'.card : ℝ) ≤ (Y.card : ℝ) ∧
        IsXSparseTo G Y X x₀ := by
    intro F' hF' hcard
    apply hstep F' hF'
    convert hcard using 2
    norm_num
  exact blockade_iteration_xSparse G S a₃ 4 y x₀ m ha₃ (by norm_num) hy0 hyc' hx₀ hm hm_le hstep'

/-!
### Part 9: Polynomial Complete Blockade in Co-Sparse $\overline{P_6}$-Free Graphs
(Lemma 3.1 of `arXiv:2307.15032` / Lemma 2.7, `lem:leaf-dense`)
-/

/--
External neighborhood of $A$ inside $U$ in $H$: vertices in $U \setminus A$ adjacent in $H$
to at least one vertex of $A$.
-/
noncomputable def extNeighIn (H : SimpleGraph V) (U A : Finset V) : Finset V :=
  (A.biUnion (fun a => neighborFinsetIn H a U)) \ A

@[simp]
theorem mem_extNeighIn (H : SimpleGraph V) (U A : Finset V) (u : V) :
    u ∈ extNeighIn H U A ↔ (∃ a ∈ A, u ∈ U ∧ H.Adj a u) ∧ u ∉ A := by
  simp only [extNeighIn, mem_sdiff, mem_biUnion, mem_neighborFinsetIn]

theorem extNeighIn_subset_sdiff (H : SimpleGraph V) (U A : Finset V) :
    extNeighIn H U A ⊆ U \ A := by
  intro u hu
  rw [mem_extNeighIn] at hu
  rcases hu with ⟨⟨_, _, huU, _⟩, huA⟩
  exact mem_sdiff.mpr ⟨huU, huA⟩

theorem isCompletePair_of_disjoint_extNeighIn (G : SimpleGraph V) (U A : Finset V) :
    IsCompletePair G A (U \ (A ∪ extNeighIn Gᶜ U A)) := by
  intro a ha u hu
  rw [mem_sdiff, mem_union, not_or] at hu
  obtain ⟨huU, huA, huN⟩ := hu
  have hne : a ≠ u := fun h => huA (h ▸ ha)
  by_contra hnad
  have hadj_c : Gᶜ.Adj a u := (SimpleGraph.compl_adj G a u).mpr ⟨hne, hnad⟩
  exact huN ((mem_extNeighIn Gᶜ U A u).mpr ⟨⟨a, ha, huU, hadj_c⟩, huA⟩)

/--
Peeling poorly expanding sets of size $\le w$ in $Gᶜ$:
For any $U \subseteq V$, there exist a remainder $U_{\mathrm{rem}} \subseteq U$ and a finite family
$\mathcal{A}$ of pairwise disjoint nonempty subsets of $U \setminus U_{\mathrm{rem}}$ of size $\le w$
that are pairwise complete in $G$, such that
$|U \setminus U_{\mathrm{rem}}| \le (1 + \mu) \sum_{A \in \mathcal{A}} |A|$ and $U_{\mathrm{rem}}$
contains no nonempty subset $A \subseteq U_{\mathrm{rem}}$ of size $\le w$ with
$|\text{extNeighIn } Gᶜ\ U_{\mathrm{rem}}\ A| \le \mu |A|$.
-/
theorem peel_poorly_expanding_sets (G : SimpleGraph V) (U : Finset V) (w : ℕ) (μ : ℝ) :
    ∃ (U_rem : Finset V) (𝒜 : Finset (Finset V)),
      U_rem ⊆ U ∧
      (∀ A ∈ 𝒜, A ⊆ U \ U_rem) ∧
      (∀ A ∈ 𝒜, A.Nonempty) ∧
      (∀ A ∈ 𝒜, A.card ≤ w) ∧
      (∀ A₁ ∈ 𝒜, ∀ A₂ ∈ 𝒜, A₁ ≠ A₂ → Disjoint A₁ A₂) ∧
      (∀ A₁ ∈ 𝒜, ∀ A₂ ∈ 𝒜, A₁ ≠ A₂ → IsCompletePair G A₁ A₂) ∧
      ((U \ U_rem).card : ℝ) ≤ (1 + μ) * (∑ A ∈ 𝒜, (A.card : ℝ)) ∧
      (∀ A ⊆ U_rem, A.Nonempty → A.card ≤ w →
        μ * (A.card : ℝ) < ((extNeighIn Gᶜ U_rem A).card : ℝ)) := by
  classical
  induction hn : U.card using Nat.strong_induction_on generalizing U with
  | _ n ih =>
    subst hn
    by_cases hexp : ∀ A ⊆ U, A.Nonempty → A.card ≤ w →
        μ * (A.card : ℝ) < ((extNeighIn Gᶜ U A).card : ℝ)
    · refine ⟨U, ∅, Subset.rfl, ?_, ?_, ?_, ?_, ?_, ?_, hexp⟩ <;> simp
    · push_neg at hexp
      obtain ⟨A₀, hA₀U, hA₀_ne, hA₀_le, hA₀_ext⟩ := hexp
      let N₀ := extNeighIn Gᶜ U A₀
      let U₁ := U \ (A₀ ∪ N₀)
      have hU₁U : U₁ ⊆ U := sdiff_subset
      obtain ⟨a₀, ha₀⟩ := hA₀_ne
      have ha₀_U : a₀ ∈ U := hA₀U ha₀
      have ha₀_not_U₁ : a₀ ∉ U₁ := by
        simp only [U₁, mem_sdiff, mem_union, not_and, not_not]
        intro _
        exact Or.inl ha₀
      have hU₁_lt : U₁.card < U.card :=
        card_lt_card (ssubset_iff_of_subset hU₁U |>.mpr ⟨a₀, ha₀_U, ha₀_not_U₁⟩)
      obtain ⟨U_rem, 𝒜₁, hU_rem_U₁, h𝒜₁_sub, h𝒜₁_ne, h𝒜₁_le, h𝒜₁_disj, h𝒜₁_comp, h𝒜₁_sum, hexp_rem⟩ :=
        ih U₁.card hU₁_lt U₁ rfl
      have hU_rem_U : U_rem ⊆ U := Subset.trans hU_rem_U₁ hU₁U
      have hA₀_disj_U₁ : Disjoint A₀ U₁ := by
        rw [Finset.disjoint_left]
        intro x hxA₀ hxU₁
        simp only [U₁, mem_sdiff, mem_union] at hxU₁
        exact hxU₁.2 (Or.inl hxA₀)
      have hA₀_comp_U₁ : IsCompletePair G A₀ U₁ :=
        isCompletePair_of_disjoint_extNeighIn G U A₀
      have hA₀_disj_𝒜₁ : ∀ A ∈ 𝒜₁, Disjoint A₀ A :=
        fun A hA => Disjoint.mono_right (Subset.trans (h𝒜₁_sub A hA) sdiff_subset) hA₀_disj_U₁
      have hA₀_comp_𝒜₁ : ∀ A ∈ 𝒜₁, IsCompletePair G A₀ A :=
        fun A hA => hA₀_comp_U₁.mono Subset.rfl (Subset.trans (h𝒜₁_sub A hA) sdiff_subset)
      have hA₀_notMem : A₀ ∉ 𝒜₁ := by
        intro hmem
        exact Finset.disjoint_left.mp (hA₀_disj_𝒜₁ A₀ hmem) ha₀ ha₀
      let 𝒜 := insert A₀ 𝒜₁
      refine ⟨U_rem, 𝒜, hU_rem_U, ?_, ?_, ?_, ?_, ?_, ?_, hexp_rem⟩
      · intro A hA
        rcases mem_insert.mp hA with rfl | hA₁
        · intro x hx
          exact mem_sdiff.mpr ⟨hA₀U hx, fun hx_rem =>
            Finset.disjoint_left.mp hA₀_disj_U₁ hx (hU_rem_U₁ hx_rem)⟩
        · intro x hx
          have hx₁ := h𝒜₁_sub A hA₁ hx
          rw [mem_sdiff] at hx₁ ⊢
          exact ⟨hU₁U hx₁.1, hx₁.2⟩
      · intro A hA
        rcases mem_insert.mp hA with rfl | hA₁
        · exact ⟨a₀, ha₀⟩
        · exact h𝒜₁_ne A hA₁
      · intro A hA
        rcases mem_insert.mp hA with rfl | hA₁
        · exact hA₀_le
        · exact h𝒜₁_le A hA₁
      · intro A₁ hA₁ A₂ hA₂ hne
        rcases mem_insert.mp hA₁ with rfl | hA₁'
        · rcases mem_insert.mp hA₂ with rfl | hA₂'
          · exact (hne rfl).elim
          · exact hA₀_disj_𝒜₁ A₂ hA₂'
        · rcases mem_insert.mp hA₂ with rfl | hA₂'
          · exact (hA₀_disj_𝒜₁ A₁ hA₁').symm
          · exact h𝒜₁_disj A₁ hA₁' A₂ hA₂' hne
      · intro A₁ hA₁ A₂ hA₂ hne
        rcases mem_insert.mp hA₁ with rfl | hA₁'
        · rcases mem_insert.mp hA₂ with rfl | hA₂'
          · exact (hne rfl).elim
          · exact hA₀_comp_𝒜₁ A₂ hA₂'
        · rcases mem_insert.mp hA₂ with rfl | hA₂'
          · exact (hA₀_comp_𝒜₁ A₁ hA₁').symm
          · exact h𝒜₁_comp A₁ hA₁' A₂ hA₂' hne
      · have hsdiff_sub : U \ U_rem ⊆ (A₀ ∪ N₀) ∪ (U₁ \ U_rem) := by
          intro x hx
          rw [mem_sdiff] at hx
          rw [mem_union]
          by_cases hx0 : x ∈ A₀ ∪ N₀
          · exact Or.inl hx0
          · exact Or.inr (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hx.1, hx0⟩, hx.2⟩)
        have hcard_nat : (U \ U_rem).card ≤ A₀.card + N₀.card + (U₁ \ U_rem).card := by
          calc (U \ U_rem).card
            _ ≤ ((A₀ ∪ N₀) ∪ (U₁ \ U_rem)).card := card_le_card hsdiff_sub
            _ ≤ (A₀ ∪ N₀).card + (U₁ \ U_rem).card := card_union_le _ _
            _ ≤ A₀.card + N₀.card + (U₁ \ U_rem).card :=
              Nat.add_le_add_right (card_union_le _ _) _
        have hcard_real :
            ((U \ U_rem).card : ℝ) ≤ (A₀.card : ℝ) + (N₀.card : ℝ) + ((U₁ \ U_rem).card : ℝ) := by
          exact_mod_cast hcard_nat
        have hsum_ins : (∑ A ∈ 𝒜, (A.card : ℝ)) = (A₀.card : ℝ) + ∑ A ∈ 𝒜₁, (A.card : ℝ) :=
          sum_insert hA₀_notMem
        rw [hsum_ins]
        linarith

private theorem exists_subset_sum_mem_Icc {α : Type*} [DecidableEq α]
    (R : Finset α) (c : α → ℝ) (w M : ℝ)
    (_hw : 0 ≤ w) (_hM : 0 ≤ M)
    (hc_nonneg : ∀ i ∈ R, 0 ≤ c i) (hc_le : ∀ i ∈ R, c i ≤ M)
    (hsum : w ≤ ∑ i ∈ R, c i) :
    ∃ I ⊆ R, w ≤ ∑ i ∈ I, c i ∧ ∑ i ∈ I, c i ≤ w + M := by
  induction R using Finset.induction_on with
  | empty =>
    refine ⟨∅, Subset.rfl, hsum, ?_⟩
    simp only [sum_empty] at hsum ⊢
    linarith
  | @insert a R ha ih =>
    have hc_nonneg' : ∀ i ∈ R, 0 ≤ c i := fun i hi => hc_nonneg i (mem_insert_of_mem hi)
    have hc_le' : ∀ i ∈ R, c i ≤ M := fun i hi => hc_le i (mem_insert_of_mem hi)
    by_cases hR : w ≤ ∑ i ∈ R, c i
    · obtain ⟨I, hIR, hIw, hIM⟩ := ih hc_nonneg' hc_le' hR
      exact ⟨I, hIR.trans (subset_insert a R), hIw, hIM⟩
    · push_neg at hR
      refine ⟨insert a R, Subset.rfl, hsum, ?_⟩
      rw [sum_insert ha]
      have haM : c a ≤ M := hc_le a (mem_insert_self a R)
      linarith

private theorem exists_disjoint_family_sum_ge {α : Type*} [DecidableEq α]
    (m : ℕ) (hm : 1 ≤ m) (R : Finset α) (c : α → ℝ) (w M : ℝ)
    (hw : 0 ≤ w) (hM : 0 ≤ M)
    (hc_nonneg : ∀ i ∈ R, 0 ≤ c i) (hc_le : ∀ i ∈ R, c i ≤ M)
    (hsum : (m : ℝ) * (w + M) - M ≤ ∑ i ∈ R, c i) :
    ∃ I : Fin m → Finset α,
      (∀ s : Fin m, I s ⊆ R) ∧
      (∀ s t : Fin m, s ≠ t → Disjoint (I s) (I t)) ∧
      (∀ s : Fin m, w ≤ ∑ i ∈ I s, c i) := by
  induction m generalizing R with
  | zero => omega
  | succ n ih =>
    by_cases hn : n = 0
    · subst hn
      refine ⟨fun _ => R, fun _ => Subset.rfl, ?_, ?_⟩
      · intro s t hst
        exact (hst (Fin.ext (by omega))).elim
      · intro _
        push_cast at hsum
        linarith
    · have hn1 : 1 ≤ n := by omega
      have hn_real : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      have hw_sum : w ≤ ∑ i ∈ R, c i := by
        push_cast at hsum
        nlinarith
      obtain ⟨I₀, hI₀R, hI₀_ge, hI₀_le⟩ :=
        exists_subset_sum_mem_Icc R c w M hw hM hc_nonneg hc_le hw_sum
      let R' : Finset α := R \ I₀
      have hsplit : ∑ i ∈ R', c i + ∑ i ∈ I₀, c i = ∑ i ∈ R, c i :=
        sum_sdiff hI₀R
      have hsum' : (n : ℝ) * (w + M) - M ≤ ∑ i ∈ R', c i := by
        push_cast at hsum
        linarith
      obtain ⟨I', hI'R', hI'disj, hI'ge⟩ :=
        ih hn1 R' (fun i hi => hc_nonneg i (sdiff_subset hi))
          (fun i hi => hc_le i (sdiff_subset hi)) hsum'
      let I : Fin (n + 1) → Finset α := fun s =>
        if h : s.val < n then I' ⟨s.val, h⟩ else I₀
      refine ⟨I, ?_, ?_, ?_⟩
      · intro s
        dsimp [I]
        split_ifs with hs
        · exact (hI'R' ⟨s.val, hs⟩).trans sdiff_subset
        · exact hI₀R
      · intro s t hst
        dsimp [I]
        split_ifs with hs ht ht
        · have hne : (⟨s.val, hs⟩ : Fin n) ≠ ⟨t.val, ht⟩ :=
            fun h => hst (Fin.ext (congr_arg (Fin.val : Fin n → ℕ) h))
          exact hI'disj _ _ hne
        · rw [Finset.disjoint_left]
          intro x hx hx0
          exact (mem_sdiff.mp (hI'R' ⟨s.val, hs⟩ hx)).2 hx0
        · rw [Finset.disjoint_right]
          intro x hx hx0
          exact (mem_sdiff.mp (hI'R' ⟨t.val, ht⟩ hx)).2 hx0
        · exact (hst (Fin.ext (by omega))).elim
      · intro s
        dsimp [I]
        split_ifs with hs
        · exact hI'ge ⟨s.val, hs⟩
        · exact hI₀_ge

private theorem exists_minimal_subset_ge {α : Type*} [DecidableEq α] (f : Finset α → ℕ) (w : ℕ)
    (R : Finset α) (hR : w ≤ f R) :
    ∃ R_min ⊆ R, w ≤ f R_min ∧ ∀ r ∈ R_min, f (R_min.erase r) < w := by
  induction hn : R.card using Nat.strong_induction_on generalizing R with
  | _ n ih =>
    subst hn
    by_cases hmin : ∀ r ∈ R, f (R.erase r) < w
    · exact ⟨R, Subset.rfl, hR, hmin⟩
    · push_neg at hmin
      obtain ⟨r, hr, hge⟩ := hmin
      obtain ⟨R_min, hsub, hw_min, hmin'⟩ :=
        ih (R.erase r).card (card_erase_lt_of_mem hr) (R.erase r) hge rfl
      exact ⟨R_min, Subset.trans hsub (erase_subset r R), hw_min, hmin'⟩

/--
Single-layer expansion step for Lemma 2.7 (`lem:leaf-dense` of `FMBV4-016_readable.tex` / Lemma 3.1 of `arXiv:2307.15032`):
Inside an expanding subgraph $H[U]$ of maximum degree $\le w$ where every $w$-subset has external
neighborhood $\ge 11 w$, given previous layers $S_{\mathrm{prev}} \subseteq U$ of total size
$\le 10 w$ and current layer $S_{\mathrm{curr}} \subseteq S_{\mathrm{prev}}$ of size $\ge w$,
there exist a minimal trigger set $R \subseteq S_{\mathrm{curr}}$ and a next layer
$S_{\mathrm{next}} \subseteq U \setminus S_{\mathrm{prev}}$ of size $w \le |S_{\mathrm{next}}| \le 2w$
such that every vertex in $S_{\mathrm{next}}$ has an $H$-neighbor in $R$ and $R$ has no $H$-edges
to $U \setminus (S_{\mathrm{prev}} \cup S_{\mathrm{next}})$.
-/
theorem exists_next_layer (H : SimpleGraph V) (U : Finset V) (w : ℕ) (hw : 1 ≤ w)
    (hdeg : ∀ u ∈ U, (neighborFinsetIn H u U).card ≤ w)
    (hexp : ∀ T ⊆ U, T.card = w → 11 * w ≤ (extNeighIn H U T).card)
    (S_prev S_curr : Finset V) (hprev_U : S_prev ⊆ U) (hcurr_prev : S_curr ⊆ S_prev)
    (hcurr_card : w ≤ S_curr.card) (hprev_card : S_prev.card ≤ 10 * w) :
    ∃ R ⊆ S_curr, ∃ S_next ⊆ U \ S_prev,
      w ≤ S_next.card ∧
      S_next.card ≤ 2 * w ∧
      (∀ v ∈ S_next, ∃ u ∈ R, H.Adj u v) ∧
      (∀ u ∈ R, ∀ z ∈ U \ (S_prev ∪ S_next), ¬H.Adj u z) := by
  classical
  let layerNeigh : Finset V → Finset V :=
    fun X => (X.biUnion (fun u => neighborFinsetIn H u U)) \ S_prev
  obtain ⟨T, hT_curr, hT_card⟩ := exists_subset_card_eq hcurr_card
  have hT_prev : T ⊆ S_prev := Subset.trans hT_curr hcurr_prev
  have hT_U : T ⊆ U := Subset.trans hT_prev hprev_U
  have hext_sub : extNeighIn H U T ⊆ layerNeigh T ∪ S_prev := by
    intro v hv
    rw [mem_extNeighIn] at hv
    rcases hv with ⟨⟨u, huT, hvU, hadj⟩, _⟩
    rw [mem_union]
    by_cases hv_prev : v ∈ S_prev
    · exact Or.inr hv_prev
    · left
      simp only [layerNeigh, mem_sdiff, mem_biUnion, mem_neighborFinsetIn]
      exact ⟨⟨u, huT, hvU, hadj⟩, hv_prev⟩
  have hext_le : (extNeighIn H U T).card ≤ (layerNeigh T).card + S_prev.card :=
    (card_le_card hext_sub).trans (card_union_le _ _)
  have h11 : 11 * w ≤ (extNeighIn H U T).card := hexp T hT_U hT_card
  have hw_layerT : w ≤ (layerNeigh T).card := by omega
  obtain ⟨R, hRT, hw_R, hmin_R⟩ :=
    exists_minimal_subset_ge (fun X => (layerNeigh X).card) w T hw_layerT
  have hR_curr : R ⊆ S_curr := Subset.trans hRT hT_curr
  have hR_U : R ⊆ U := Subset.trans hRT hT_U
  let S_next := layerNeigh R
  have hS_next_sub : S_next ⊆ U \ S_prev := by
    intro v hv
    simp only [S_next, layerNeigh, mem_sdiff, mem_biUnion, mem_neighborFinsetIn] at hv
    rcases hv with ⟨⟨u, _, hvU, _⟩, hv_prev⟩
    exact mem_sdiff.mpr ⟨hvU, hv_prev⟩
  have hR_ne : R.Nonempty := by
    by_contra h_empty
    rw [not_nonempty_iff_eq_empty] at h_empty
    have h0 : (layerNeigh R).card = 0 := by simp [layerNeigh, h_empty]
    omega
  obtain ⟨r₀, hr₀⟩ := hR_ne
  have hS_next_split : S_next ⊆ layerNeigh (R.erase r₀) ∪ neighborFinsetIn H r₀ U := by
    intro v hv
    simp only [S_next, layerNeigh, mem_sdiff, mem_biUnion, mem_neighborFinsetIn] at hv
    rcases hv with ⟨⟨u, huR, hvU, hadj⟩, hv_prev⟩
    rw [mem_union]
    by_cases hur₀ : u = r₀
    · subst hur₀
      exact Or.inr ((mem_neighborFinsetIn H u v U).mpr ⟨hvU, hadj⟩)
    · left
      simp only [layerNeigh, mem_sdiff, mem_biUnion, mem_neighborFinsetIn]
      exact ⟨⟨u, mem_erase.mpr ⟨hur₀, huR⟩, hvU, hadj⟩, hv_prev⟩
  have hS_next_le : S_next.card ≤ 2 * w := by
    have h1 : S_next.card ≤ (layerNeigh (R.erase r₀)).card + (neighborFinsetIn H r₀ U).card :=
      (card_le_card hS_next_split).trans (card_union_le _ _)
    have h2 : (layerNeigh (R.erase r₀)).card < w := hmin_R r₀ hr₀
    have h3 : (neighborFinsetIn H r₀ U).card ≤ w := hdeg r₀ (hR_U hr₀)
    omega
  refine ⟨R, hR_curr, S_next, hS_next_sub, hw_R, hS_next_le, ?_, ?_⟩
  · intro v hv
    simp only [S_next, layerNeigh, mem_sdiff, mem_biUnion, mem_neighborFinsetIn] at hv
    rcases hv with ⟨⟨u, huR, _, hadj⟩, _⟩
    exact ⟨u, huR, hadj⟩
  · intro u huR z hz hadj
    rw [mem_sdiff, mem_union, not_or] at hz
    obtain ⟨hzU, hz_prev, hz_next⟩ := hz
    apply hz_next
    simp only [S_next, layerNeigh, mem_sdiff, mem_biUnion, mem_neighborFinsetIn]
    exact ⟨⟨u, huR, hzU, hadj⟩, hz_prev⟩

/-- Explicit 6-vertex witness showing that $(x_0, x_1, x_2, x_3, x_4, x_5)$ induces $\overline{P_6}$
in $G$ when consecutive pairs are non-adjacent and non-consecutive pairs are adjacent. -/
private lemma not_isInducedSubgraphFree_P6Compl {G : SimpleGraph V}
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

/--
**Lemma 2.7 (`lem:leaf-dense` of `FMBV4-016_readable.tex` / Lemma 3.1 of `arXiv:2307.15032`, `p6Compl_free_sparse_compl_complete_blockade_poly`)**:
If $G$ is $\overline{P_6}$-free (`IsInducedSubgraphFree G P6Compl`) and $\overline{G}[F]$ is
$y^2$-sparse (`IsEpsSparseOn Gᶜ F (y ^ 2)`) with $0 < y \le 1/360$ and $|F| \ge 1/y^2$,
then $G[F]$ contains a complete $(\lceil 1/y \rceil, \lfloor y^2 |F| \rfloor)$-blockade.
-/
theorem p6Compl_free_sparse_compl_complete_blockade_poly
    (G : SimpleGraph V) (F : Finset V) (y : ℝ)
    (hG : IsInducedSubgraphFree G P6Compl)
    (hy0 : 0 < y) (hy_le : y ≤ 1 / 360)
    (hF_card : 1 / y ^ 2 ≤ (F.card : ℝ))
    (hsparse : IsEpsSparseOn Gᶜ F (y ^ 2)) :
    ∃ B : Fin ⌈1 / y⌉₊ → Finset V,
      IsCompleteBlockadeIn G F ⌈1 / y⌉₊ (⌊y ^ 2 * (F.card : ℝ)⌋₊ : ℝ) B := by
  classical
  let w : ℕ := ⌊y ^ 2 * (F.card : ℝ)⌋₊
  let μ : ℝ := 1 / (12 * y)
  have hy2_F : 1 ≤ y ^ 2 * (F.card : ℝ) := by
    have h1 : y ^ 2 * (1 / y ^ 2) ≤ y ^ 2 * (F.card : ℝ) :=
      mul_le_mul_of_nonneg_left hF_card (by positivity)
    rw [mul_one_div_cancel (by positivity)] at h1
    exact h1
  have hw_pos : 1 ≤ w := Nat.floor_pos.mpr hy2_F
  have hw_le_y2F : (w : ℝ) ≤ y ^ 2 * (F.card : ℝ) :=
    Nat.floor_le (by positivity)
  obtain ⟨U_rem, 𝒜, hU_rem_F, h𝒜_sub, h𝒜_ne, h𝒜_le, h𝒜_disj, h𝒜_comp, h𝒜_sum, hexp_rem⟩ :=
    peel_poorly_expanding_sets G F w μ
  by_cases hrem_half : (U_rem.card : ℝ) ≤ (1 / 2 : ℝ) * (F.card : ℝ)
  · -- Case 1: U_rem.card ≤ F.card / 2, so the peeled sets 𝒜 group into a complete blockade
    have hsdiff_eq : ((F \ U_rem).card : ℝ) + (U_rem.card : ℝ) = (F.card : ℝ) := by
      exact_mod_cast card_sdiff_add_card_eq_card hU_rem_F
    have hsdiff_ge : (1 / 2 : ℝ) * (F.card : ℝ) ≤ ((F \ U_rem).card : ℝ) := by linarith
    have hμ_pos : 0 < 1 + μ := by
      dsimp [μ]
      positivity
    have hμ_3y : (1 + μ) * (3 * y * (F.card : ℝ)) ≤ (1 / 2 : ℝ) * (F.card : ℝ) := by
      have h1 : (1 + μ) * (3 * y * (F.card : ℝ)) = (3 * y + 1 / 4) * (F.card : ℝ) := by
        dsimp [μ]
        have hy_ne : y ≠ 0 := hy0.ne'
        field_simp
        ring
      rw [h1]
      have h2 : 3 * y + 1 / 4 ≤ 1 / 2 := by linarith
      exact mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg _)
    have hsum_3y : 3 * y * (F.card : ℝ) ≤ ∑ A ∈ 𝒜, (A.card : ℝ) := by
      have h1 : (1 + μ) * (3 * y * (F.card : ℝ)) ≤ (1 + μ) * (∑ A ∈ 𝒜, (A.card : ℝ)) :=
        hμ_3y.trans (hsdiff_ge.trans h𝒜_sum)
      exact le_of_mul_le_mul_left h1 hμ_pos
    let k : ℕ := ⌈1 / y⌉₊
    have hk_pos : 1 ≤ k := Nat.ceil_pos.mpr (by positivity)
    have hk_lt : (k : ℝ) < 1 / y + 1 := Nat.ceil_lt_add_one (by positivity)
    have hsum_target : (k : ℝ) * ((w : ℝ) + (w : ℝ)) - (w : ℝ) ≤ ∑ A ∈ 𝒜, (A.card : ℝ) := by
      have h1 : (k : ℝ) * ((w : ℝ) + (w : ℝ)) - (w : ℝ) = (2 * (k : ℝ) - 1) * (w : ℝ) := by ring
      have h2 : 2 * (k : ℝ) - 1 ≤ 2 * (1 / y) + 1 := by linarith
      have h2k_nonneg : 0 ≤ 2 * (k : ℝ) - 1 := by
        have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_pos
        linarith
      have h3 : (2 * (k : ℝ) - 1) * (w : ℝ) ≤ (2 * (1 / y) + 1) * (y ^ 2 * (F.card : ℝ)) :=
        mul_le_mul h2 hw_le_y2F (Nat.cast_nonneg _) (by positivity)
      have h4 : (2 * (1 / y) + 1) * (y ^ 2 * (F.card : ℝ)) = (2 * y + y ^ 2) * (F.card : ℝ) := by
        have hy_ne : y ≠ 0 := hy0.ne'
        field_simp
      have h5 : 2 * y + y ^ 2 ≤ 3 * y := by nlinarith
      have h6 : (2 * y + y ^ 2) * (F.card : ℝ) ≤ 3 * y * (F.card : ℝ) :=
        mul_le_mul_of_nonneg_right h5 (Nat.cast_nonneg _)
      linarith
    obtain ⟨I, hI_sub, hI_disj, hI_sum⟩ :=
      exists_disjoint_family_sum_ge k hk_pos 𝒜 (fun A => (A.card : ℝ)) (w : ℝ) (w : ℝ)
        (Nat.cast_nonneg _) (Nat.cast_nonneg _) (fun A _ => Nat.cast_nonneg _)
        (fun A hA => Nat.cast_le.mpr (h𝒜_le A hA)) hsum_target
    let B : Fin k → Finset V := fun s => (I s).biUnion id
    have hB_card : ∀ s : Fin k, ((B s).card : ℝ) = ∑ A ∈ I s, (A.card : ℝ) := by
      intro s
      have hnat : (B s).card = ∑ A ∈ I s, A.card :=
        card_biUnion (fun A₁ hA₁ A₂ hA₂ hne =>
          h𝒜_disj A₁ (hI_sub s hA₁) A₂ (hI_sub s hA₂) hne)
      exact_mod_cast hnat
    have hB_width : ∀ s : Fin k, (w : ℝ) ≤ ((B s).card : ℝ) := by
      intro s
      rw [hB_card s]
      exact hI_sum s
    have hB_ne : ∀ s : Fin k, (B s).Nonempty := by
      intro s
      have hpos : (0 : ℝ) < ((B s).card : ℝ) := by
        have : (0 : ℝ) < (w : ℝ) := by positivity
        linarith [hB_width s]
      exact card_pos.mp (by exact_mod_cast hpos)
    have hB_sub : ∀ s : Fin k, B s ⊆ F := by
      intro s u hu
      obtain ⟨A, hA_Is, huA⟩ := mem_biUnion.mp hu
      exact sdiff_subset (h𝒜_sub A (hI_sub s hA_Is) huA)
    have hB_disj : ∀ s t : Fin k, s ≠ t → Disjoint (B s) (B t) := by
      intro s t hst
      rw [Finset.disjoint_left]
      intro u huBs huBt
      obtain ⟨A₁, hA₁, huA₁⟩ := mem_biUnion.mp huBs
      obtain ⟨A₂, hA₂, huA₂⟩ := mem_biUnion.mp huBt
      have hne : A₁ ≠ A₂ := fun h => Finset.disjoint_left.mp (hI_disj s t hst) hA₁ (h ▸ hA₂)
      exact Finset.disjoint_left.mp (h𝒜_disj A₁ (hI_sub s hA₁) A₂ (hI_sub t hA₂) hne) huA₁ huA₂
    have hB_comp : ∀ s t : Fin k, s ≠ t → IsCompletePair G (B s) (B t) := by
      intro s t hst u huBs v hvBt
      obtain ⟨A₁, hA₁, huA₁⟩ := mem_biUnion.mp huBs
      obtain ⟨A₂, hA₂, hvA₂⟩ := mem_biUnion.mp hvBt
      have hne : A₁ ≠ A₂ := fun h => Finset.disjoint_left.mp (hI_disj s t hst) hA₁ (h ▸ hA₂)
      exact h𝒜_comp A₁ (hI_sub s hA₁) A₂ (hI_sub t hA₂) hne u huA₁ v hvA₂
    exact ⟨B, ⟨hB_sub, hB_ne, hB_disj, hB_width⟩, hB_comp⟩
  · -- Case 2: U_rem.card > F.card / 2, so 6-layer expansion in U_rem constructs an induced P6Compl
    exfalso
    push_neg at hrem_half
    have hdeg_U : ∀ u ∈ U_rem, (neighborFinsetIn Gᶜ u U_rem).card ≤ w := by
      intro u hu
      have hsub : neighborFinsetIn Gᶜ u U_rem ⊆ neighborFinsetIn Gᶜ u F :=
        neighborFinsetIn_mono Gᶜ u hU_rem_F
      have hle_F : ((neighborFinsetIn Gᶜ u U_rem).card : ℝ) ≤ y ^ 2 * (F.card : ℝ) := by
        calc ((neighborFinsetIn Gᶜ u U_rem).card : ℝ)
          _ ≤ ((neighborFinsetIn Gᶜ u F).card : ℝ) := by exact_mod_cast card_le_card hsub
          _ ≤ y ^ 2 * (F.card : ℝ) := hsparse u (hU_rem_F hu)
      exact Nat.le_floor hle_F
    have hμ_ge_30 : 30 ≤ μ := by
      dsimp [μ]
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hexp_11 : ∀ T ⊆ U_rem, T.card = w → 11 * w ≤ (extNeighIn Gᶜ U_rem T).card := by
      intro T hT hT_card
      have hT_ne : T.Nonempty := card_pos.mp (by omega)
      have hlt := hexp_rem T hT hT_ne (by omega)
      rw [hT_card] at hlt
      have h11_real : ((11 * w : ℕ) : ℝ) < ((extNeighIn Gᶜ U_rem T).card : ℝ) := by
        push_cast
        have hw_pos_real : (0 : ℝ) < (w : ℝ) := by positivity
        nlinarith
      have h11_nat : 11 * w < (extNeighIn Gᶜ U_rem T).card := by exact_mod_cast h11_real
      omega
    have hw_le_U : w ≤ U_rem.card := by
      have hy2_le_half : y ^ 2 * (F.card : ℝ) ≤ (1 / 2 : ℝ) * (F.card : ℝ) := by
        have : y ^ 2 ≤ 1 / 2 := by nlinarith
        exact mul_le_mul_of_nonneg_right this (Nat.cast_nonneg _)
      have hw_lt : (w : ℝ) < (U_rem.card : ℝ) := by linarith
      exact_mod_cast hw_lt.le
    obtain ⟨S₀, hS₀_U, hS₀_card⟩ := exists_subset_card_eq hw_le_U
    let P₀ := S₀
    have hP₀_card : P₀.card = w := hS₀_card
    obtain ⟨R₁, hR₁_S₀, S₁, hS₁_sub, hw_S₁, hS₁_le, hS₁_prev, hR₁_no⟩ :=
      exists_next_layer Gᶜ U_rem w hw_pos hdeg_U hexp_11 P₀ S₀ hS₀_U Subset.rfl
        (by omega) (by omega)
    let P₁ := P₀ ∪ S₁
    have hP₁_U : P₁ ⊆ U_rem := union_subset hS₀_U (Subset.trans hS₁_sub sdiff_subset)
    have hP₁_le : P₁.card ≤ 3 * w := by
      have h1 : P₁.card ≤ P₀.card + S₁.card := card_union_le P₀ S₁
      omega
    obtain ⟨R₂, hR₂_S₁, S₂, hS₂_sub, hw_S₂, hS₂_le, hS₂_prev, hR₂_no⟩ :=
      exists_next_layer Gᶜ U_rem w hw_pos hdeg_U hexp_11 P₁ S₁ hP₁_U subset_union_right
        hw_S₁ (by omega)
    let P₂ := P₁ ∪ S₂
    have hP₂_U : P₂ ⊆ U_rem := union_subset hP₁_U (Subset.trans hS₂_sub sdiff_subset)
    have hP₂_le : P₂.card ≤ 5 * w := by
      have h1 : P₂.card ≤ P₁.card + S₂.card := card_union_le P₁ S₂
      omega
    obtain ⟨R₃, hR₃_S₂, S₃, hS₃_sub, hw_S₃, hS₃_le, hS₃_prev, hR₃_no⟩ :=
      exists_next_layer Gᶜ U_rem w hw_pos hdeg_U hexp_11 P₂ S₂ hP₂_U subset_union_right
        hw_S₂ (by omega)
    let P₃ := P₂ ∪ S₃
    have hP₃_U : P₃ ⊆ U_rem := union_subset hP₂_U (Subset.trans hS₃_sub sdiff_subset)
    have hP₃_le : P₃.card ≤ 7 * w := by
      have h1 : P₃.card ≤ P₂.card + S₃.card := card_union_le P₂ S₃
      omega
    obtain ⟨R₄, hR₄_S₃, S₄, hS₄_sub, hw_S₄, hS₄_le, hS₄_prev, hR₄_no⟩ :=
      exists_next_layer Gᶜ U_rem w hw_pos hdeg_U hexp_11 P₃ S₃ hP₃_U subset_union_right
        hw_S₃ (by omega)
    let P₄ := P₃ ∪ S₄
    have hP₄_U : P₄ ⊆ U_rem := union_subset hP₃_U (Subset.trans hS₄_sub sdiff_subset)
    have hP₄_le : P₄.card ≤ 9 * w := by
      have h1 : P₄.card ≤ P₃.card + S₄.card := card_union_le P₃ S₄
      omega
    obtain ⟨R₅, hR₅_S₄, S₅, hS₅_sub, hw_S₅, _, hS₅_prev, _⟩ :=
      exists_next_layer Gᶜ U_rem w hw_pos hdeg_U hexp_11 P₄ S₄ hP₄_U subset_union_right
        hw_S₄ (by omega)
    obtain ⟨v₅, hv₅⟩ := card_pos.mp (lt_of_lt_of_le (by omega) hw_S₅)
    obtain ⟨v₄, hv₄_R₅, hadj45⟩ := hS₅_prev v₅ hv₅
    have hv₄ : v₄ ∈ S₄ := hR₅_S₄ hv₄_R₅
    obtain ⟨v₃, hv₃_R₄, hadj34⟩ := hS₄_prev v₄ hv₄
    have hv₃ : v₃ ∈ S₃ := hR₄_S₃ hv₃_R₄
    obtain ⟨v₂, hv₂_R₃, hadj23⟩ := hS₃_prev v₃ hv₃
    have hv₂ : v₂ ∈ S₂ := hR₃_S₂ hv₂_R₃
    obtain ⟨v₁, hv₁_R₂, hadj12⟩ := hS₂_prev v₂ hv₂
    have hv₁ : v₁ ∈ S₁ := hR₂_S₁ hv₁_R₂
    obtain ⟨v₀, hv₀_R₁, hadj01⟩ := hS₁_prev v₁ hv₁
    have hne01 : v₀ ≠ v₁ := ((SimpleGraph.compl_adj G v₀ v₁).mp hadj01).1
    have hn01 : ¬G.Adj v₀ v₁ := ((SimpleGraph.compl_adj G v₀ v₁).mp hadj01).2
    have hn12 : ¬G.Adj v₁ v₂ := ((SimpleGraph.compl_adj G v₁ v₂).mp hadj12).2
    have hn23 : ¬G.Adj v₂ v₃ := ((SimpleGraph.compl_adj G v₂ v₃).mp hadj23).2
    have hn34 : ¬G.Adj v₃ v₄ := ((SimpleGraph.compl_adj G v₃ v₄).mp hadj34).2
    have hn45 : ¬G.Adj v₄ v₅ := ((SimpleGraph.compl_adj G v₄ v₅).mp hadj45).2
    have hadj_of_layer : ∀ {P S_next R : Finset V} {u z : V},
        (∀ a ∈ R, ∀ b ∈ U_rem \ (P ∪ S_next), ¬Gᶜ.Adj a b) →
        u ∈ R → R ⊆ P ∪ S_next → z ∈ U_rem → z ∉ P ∪ S_next → G.Adj u z := by
      intro P S_next R u z hno hu hRP hzU hz_not
      have hne : u ≠ z := fun h => hz_not (h ▸ hRP hu)
      have hnadj_c : ¬Gᶜ.Adj u z := hno u hu z (mem_sdiff.mpr ⟨hzU, hz_not⟩)
      by_contra hnad
      exact hnadj_c ((SimpleGraph.compl_adj G u z).mpr ⟨hne, hnad⟩)
    have hP12 : P₁ ⊆ P₂ := subset_union_left
    have hP23 : P₂ ⊆ P₃ := subset_union_left
    have hP34 : P₃ ⊆ P₄ := subset_union_left
    have hv₂_sdiff := mem_sdiff.mp (hS₂_sub hv₂)
    have hv₃_sdiff := mem_sdiff.mp (hS₃_sub hv₃)
    have hv₄_sdiff := mem_sdiff.mp (hS₄_sub hv₄)
    have hv₅_sdiff := mem_sdiff.mp (hS₅_sub hv₅)
    have hR₁_P₁ : R₁ ⊆ P₀ ∪ S₁ := Subset.trans hR₁_S₀ subset_union_left
    have hR₂_P₂ : R₂ ⊆ P₁ ∪ S₂ :=
      Subset.trans hR₂_S₁ (Subset.trans subset_union_right subset_union_left)
    have hR₃_P₃ : R₃ ⊆ P₂ ∪ S₃ :=
      Subset.trans hR₃_S₂ (Subset.trans subset_union_right subset_union_left)
    have hR₄_P₄ : R₄ ⊆ P₃ ∪ S₄ :=
      Subset.trans hR₄_S₃ (Subset.trans subset_union_right subset_union_left)
    have ha02 : G.Adj v₀ v₂ :=
      hadj_of_layer hR₁_no hv₀_R₁ hR₁_P₁ hv₂_sdiff.1 hv₂_sdiff.2
    have ha03 : G.Adj v₀ v₃ :=
      hadj_of_layer hR₁_no hv₀_R₁ hR₁_P₁ hv₃_sdiff.1 (fun h => hv₃_sdiff.2 (hP12 h))
    have ha04 : G.Adj v₀ v₄ :=
      hadj_of_layer hR₁_no hv₀_R₁ hR₁_P₁ hv₄_sdiff.1 (fun h => hv₄_sdiff.2 (hP23 (hP12 h)))
    have ha05 : G.Adj v₀ v₅ :=
      hadj_of_layer hR₁_no hv₀_R₁ hR₁_P₁ hv₅_sdiff.1 (fun h => hv₅_sdiff.2 (hP34 (hP23 (hP12 h))))
    have ha13 : G.Adj v₁ v₃ :=
      hadj_of_layer hR₂_no hv₁_R₂ hR₂_P₂ hv₃_sdiff.1 hv₃_sdiff.2
    have ha14 : G.Adj v₁ v₄ :=
      hadj_of_layer hR₂_no hv₁_R₂ hR₂_P₂ hv₄_sdiff.1 (fun h => hv₄_sdiff.2 (hP23 h))
    have ha15 : G.Adj v₁ v₅ :=
      hadj_of_layer hR₂_no hv₁_R₂ hR₂_P₂ hv₅_sdiff.1 (fun h => hv₅_sdiff.2 (hP34 (hP23 h)))
    have ha24 : G.Adj v₂ v₄ :=
      hadj_of_layer hR₃_no hv₂_R₃ hR₃_P₃ hv₄_sdiff.1 hv₄_sdiff.2
    have ha25 : G.Adj v₂ v₅ :=
      hadj_of_layer hR₃_no hv₂_R₃ hR₃_P₃ hv₅_sdiff.1 (fun h => hv₅_sdiff.2 (hP34 h))
    have ha35 : G.Adj v₃ v₅ :=
      hadj_of_layer hR₄_no hv₃_R₄ hR₄_P₄ hv₅_sdiff.1 hv₅_sdiff.2
    exact not_isInducedSubgraphFree_P6Compl v₀ v₁ v₂ v₃ v₄ v₅ hne01
      hn01 hn12 hn23 hn34 hn45 ha02 ha03 ha04 ha05 ha13 ha14 ha15 ha24 ha25 ha35 hG

/--
Real-width corollary of `p6Compl_free_sparse_compl_complete_blockade_poly`:
since $1 \le y^2 |F|$, $\lfloor y^2 |F| \rfloor \ge \frac{1}{2} y^2 |F|$ and
$\lfloor y^2 |F| \rfloor \ge |F| / \lceil 1/y \rceil^3$, so $G[F]$ contains a complete
$(\lceil 1/y \rceil, |F| / \lceil 1/y \rceil^3)$-blockade.
-/
theorem p6Compl_free_sparse_compl_complete_blockade_cube
    (G : SimpleGraph V) (F : Finset V) (y : ℝ)
    (hG : IsInducedSubgraphFree G P6Compl)
    (hy0 : 0 < y) (hy_le : y ≤ 1 / 360)
    (hF_card : 1 / y ^ 2 ≤ (F.card : ℝ))
    (hsparse : IsEpsSparseOn Gᶜ F (y ^ 2)) :
    ∃ B : Fin ⌈1 / y⌉₊ → Finset V,
      IsCompleteBlockadeIn G F ⌈1 / y⌉₊ ((F.card : ℝ) / (⌈1 / y⌉₊ : ℝ) ^ (3 : ℝ)) B := by
  obtain ⟨B, hB⟩ :=
    p6Compl_free_sparse_compl_complete_blockade_poly G F y hG hy0 hy_le hF_card hsparse
  refine ⟨B, hB.mono Subset.rfl ?_⟩
  have hy2_F : 1 ≤ y ^ 2 * (F.card : ℝ) := by
    have h1 : y ^ 2 * (1 / y ^ 2) ≤ y ^ 2 * (F.card : ℝ) :=
      mul_le_mul_of_nonneg_left hF_card (by positivity)
    rw [mul_one_div_cancel (by positivity)] at h1
    exact h1
  have hfloor_ge_one : (1 : ℝ) ≤ (⌊y ^ 2 * (F.card : ℝ)⌋₊ : ℝ) := by
    exact_mod_cast Nat.le_floor (by exact_mod_cast hy2_F)
  have hfloor_gt : y ^ 2 * (F.card : ℝ) - 1 < (⌊y ^ 2 * (F.card : ℝ)⌋₊ : ℝ) :=
    Nat.sub_one_lt_floor _
  have hfloor_ge_half :
      (1 / 2 : ℝ) * (y ^ 2 * (F.card : ℝ)) ≤ (⌊y ^ 2 * (F.card : ℝ)⌋₊ : ℝ) := by
    linarith
  have hk_ge : 1 / y ≤ (⌈1 / y⌉₊ : ℝ) := Nat.le_ceil _
  have hk_pos : (0 : ℝ) < (⌈1 / y⌉₊ : ℝ) := lt_of_lt_of_le (by positivity) hk_ge
  have hk3_ge : (1 / y) ^ 3 ≤ (⌈1 / y⌉₊ : ℝ) ^ (3 : ℝ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact pow_le_pow_left₀ (by positivity) hk_ge 3
  have hdiv_le : (F.card : ℝ) / (⌈1 / y⌉₊ : ℝ) ^ (3 : ℝ) ≤ y ^ 3 * (F.card : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    calc (F.card : ℝ)
      _ = y ^ 3 * (F.card : ℝ) * (1 / y) ^ 3 := by
        have hy_ne : y ≠ 0 := hy0.ne'
        field_simp
      _ ≤ y ^ 3 * (F.card : ℝ) * (⌈1 / y⌉₊ : ℝ) ^ (3 : ℝ) :=
        mul_le_mul_of_nonneg_left hk3_ge (by positivity)
  have hy3_le_half : y ^ 3 * (F.card : ℝ) ≤ (1 / 2 : ℝ) * (y ^ 2 * (F.card : ℝ)) := by
    have : y ^ 3 ≤ (1 / 2 : ℝ) * y ^ 2 := by nlinarith
    calc y ^ 3 * (F.card : ℝ)
      _ ≤ ((1 / 2 : ℝ) * y ^ 2) * (F.card : ℝ) :=
        mul_le_mul_of_nonneg_right this (Nat.cast_nonneg _)
      _ = (1 / 2 : ℝ) * (y ^ 2 * (F.card : ℝ)) := by ring
  linarith

end ErdosHajnalP6

