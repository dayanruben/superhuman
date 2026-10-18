/-
Copyright 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosHajnal.BasicLemmas
import ErdosHajnal.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Witness Graph and Leaf-Reducibility of $P_6$ (Propositions 3.1 and 3.2 of `FMBV4-016_readable.tex`)

This file formalizes:
- **Proposition 3.1 (`prop:leaf-red`)**: Vertex `5 : Fin 6` has unique neighbor `4 : Fin 6` in $P_6$,
  and deleting it yields an induced subgraph isomorphic to $P_5$ (and similarly for $\overline{P_6}$
  and $\overline{P_5}$).
- **Proposition 3.2 (`prop:wonderful`)**:
  1. The 7-vertex substitution witness graph `witnessH : SimpleGraph (Fin 7)` obtained from
     $\overline{P_5}$ by substituting a 2-vertex stable module for vertex 3 and a 2-vertex clique
     module for vertex 2, with special vertices `(0, 1, 2)` (1-indexed `(1, 2, 3)`).
  2. The 8-vertex extension `witnessHPlus : SimpleGraph (Fin 8)` ($H^+$) and the explicit
     6-vertex embedding `gPlus : Fin 6 ↪ Fin 8` (`![1, 4, 6, 2, 5, 3]`) proving that $H^+$
     contains an induced $\overline{P_6}$.
  3. The 8-vertex extension `witnessHMinus : SimpleGraph (Fin 8)` ($H^-$) and the explicit
     6-vertex embedding `gMinus : Fin 6 ↪ Fin 8` (`![1, 4, 0, 7, 3, 2]`) proving that $H^-$
     contains an induced $\overline{P_6}$.
  4. For any $\overline{P_6}$-free graph $G$, any complete-or-$x$-sparse
     blockade $(B_1, \dots, B_\ell)$ with $6 x \le 1/2$, and any external vertex
     $v \notin \bigcup_i B_i$, the pattern graph $J$ induced on the open attachment index set
     $I(v) = \{i : 0 < |N_G(v) \cap B_i| < \frac{1}{2}|B_i|\}$ is `witnessH`-free; plus the
     double-counting outcome (W2) and the clique/stable-set block-union restriction outcome (W1).
-/

open Finset SimpleGraph Real

namespace ErdosHajnalP6

variable {V : Type*}

/-! ### Decidability of `pathGraph` Adjacency and Proposition 3.1 (`prop:leaf-red`) -/

instance instDecidableRelPathGraphAdj (n : ℕ) : DecidableRel (pathGraph n).Adj :=
  fun _ _ => decidable_of_iff' _ pathGraph_adj

instance instDecidableRelP6Adj : DecidableRel P6.Adj :=
  instDecidableRelPathGraphAdj 6

instance instDecidableRelP5Adj : DecidableRel P5.Adj :=
  instDecidableRelPathGraphAdj 5

instance instDecidableRelP6ComplAdj : DecidableRel P6Compl.Adj :=
  inferInstanceAs (DecidableRel (pathGraph 6)ᶜ.Adj)

instance instDecidableRelP5ComplAdj : DecidableRel P5Compl.Adj :=
  inferInstanceAs (DecidableRel (pathGraph 5)ᶜ.Adj)

/--
Deleting the last vertex `5 : Fin 6` of $P_6$ (`Fin.castSuccEmb : Fin 5 ↪ Fin 6`) yields $P_5$.
(Proposition 3.1 of `FMBV4-016_readable.tex`.)
-/
theorem P6_comap_castSuccEmb : P6.comap Fin.castSuccEmb = P5 := by
  ext u v
  simp [P6, P5, pathGraph_adj]

/--
Deleting the last vertex `5 : Fin 6` of $\overline{P_6}$ yields $\overline{P_5}$.
(Proposition 3.1 of `FMBV4-016_readable.tex`.)
-/
theorem P6Compl_comap_castSuccEmb : P6Compl.comap Fin.castSuccEmb = P5Compl := by
  rw [← comap_compl, P6_comap_castSuccEmb]

/--
In $P_6$, the last vertex `5 : Fin 6` has unique neighbor `4 : Fin 6` (so it is a leaf of degree 1).
(Proposition 3.1 of `FMBV4-016_readable.tex`.)
-/
theorem P6_last_unique_neighbor : ∀ u : Fin 6, P6.Adj 5 u ↔ u = 4 := by
  intro u
  fin_cases u <;> decide

/--
In $\overline{P_6}$, the last vertex `5 : Fin 6` is adjacent to every vertex except `4` and `5`.
-/
theorem P6Compl_last_adj : ∀ u : Fin 6, P6Compl.Adj 5 u ↔ u ≠ 5 ∧ u ≠ 4 := by
  intro u
  fin_cases u <;> decide

/-! ### Proposition 3.2: The 7-Vertex Witness Graph $H$ and its 8-Vertex Extensions $H^+, H^-$ -/

/--
Boolean adjacency predicate for the 8-vertex graph $H^-$ (`witnessHMinus : SimpleGraph (Fin 8)`),
where vertex `0` is the external vertex with neighborhood `{1, 2, 3}`, and vertices `1..7`
form the 7-vertex witness graph $H$ (with `{2, 3}` non-adjacent):
- On `{1, 2, 3, 4, 6}`, the non-edges are `{1,4}, {4,6}, {6,2}, {2,3}` (forming $P_5 = 1-4-6-2-3$
  in the complement).
- `{3, 5}` is a stable module substituting for `3` ($35 \notin E(H)$ and $N_H(3) = N_H(5) = \{1, 4, 6\}$).
- `{2, 7}` is a clique module substituting for `2` ($27 \in E(H)$ and $N_H(2)\setminus\{7\} = N_H(7)\setminus\{2\} = \{1, 4\}$).
-/
def witnessHMinusAdjBool (a b : Fin 8) : Bool :=
  (a == 0 && (b == 1 || b == 2 || b == 3)) ||
  (b == 0 && (a == 1 || a == 2 || a == 3)) ||
  (a == 1 && (b == 2 || b == 3 || b == 5 || b == 6 || b == 7)) ||
  (b == 1 && (a == 2 || a == 3 || a == 5 || a == 6 || a == 7)) ||
  (a == 2 && (b == 4 || b == 7)) ||
  (b == 2 && (a == 4 || a == 7)) ||
  (a == 3 && (b == 4 || b == 6)) ||
  (b == 3 && (a == 4 || a == 6)) ||
  (a == 4 && (b == 5 || b == 7)) ||
  (b == 4 && (a == 5 || a == 7)) ||
  (a == 5 && b == 6) ||
  (b == 5 && a == 6)

/--
Boolean adjacency predicate for the 8-vertex graph $H^+$ (`witnessHPlus : SimpleGraph (Fin 8)`),
obtained from $H^-$ by adding the edge `{2, 3}` between special vertices `2` and `3`.
-/
def witnessHPlusAdjBool (a b : Fin 8) : Bool :=
  witnessHMinusAdjBool a b || (a == 2 && b == 3) || (a == 3 && b == 2)

/--
Boolean adjacency predicate for the 7-vertex witness graph $H$ (`witnessH : SimpleGraph (Fin 7)`),
where `r : Fin 7` (0-indexed `0..6`) corresponds to `r.succ : Fin 8` (1-indexed `1..7`).
-/
def witnessHAdjBool (r s : Fin 7) : Bool :=
  witnessHMinusAdjBool r.succ s.succ

/--
The 8-vertex extension $H^-$ (`witnessHMinus : SimpleGraph (Fin 8)`) from Proposition 3.2(3)
of `FMBV4-016_readable.tex`, where $N_{H^-}(0) = \{1, 2, 3\}$ and $\{2, 3\} \notin E(H^-)$.
-/
def witnessHMinus : SimpleGraph (Fin 8) where
  Adj a b := witnessHMinusAdjBool a b = true
  symm := by
    intro a b
    fin_cases a <;> fin_cases b <;> decide
  loopless := by
    intro a
    fin_cases a <;> decide

instance instDecidableRelWitnessHMinusAdj : DecidableRel witnessHMinus.Adj :=
  fun a b => inferInstanceAs (Decidable (witnessHMinusAdjBool a b = true))

/--
The 8-vertex extension $H^+$ (`witnessHPlus : SimpleGraph (Fin 8)`) from Proposition 3.2(2)
of `FMBV4-016_readable.tex`, where $N_{H^+}(0) = \{1, 2, 3\}$ and $\{2, 3\} \in E(H^+)$.
-/
def witnessHPlus : SimpleGraph (Fin 8) where
  Adj a b := witnessHPlusAdjBool a b = true
  symm := by
    intro a b
    fin_cases a <;> fin_cases b <;> decide
  loopless := by
    intro a
    fin_cases a <;> decide

instance instDecidableRelWitnessHPlusAdj : DecidableRel witnessHPlus.Adj :=
  fun a b => inferInstanceAs (Decidable (witnessHPlusAdjBool a b = true))

/--
The 7-vertex substitution witness graph $H$ (`witnessH : SimpleGraph (Fin 7)`) from Proposition 3.2
of `FMBV4-016_readable.tex`, where `0..6 : Fin 7` correspond to vertices `1..7` in the paper.
The three special vertices are `0, 1, 2 : Fin 7` (corresponding to `1, 2, 3` in the paper).
-/
def witnessH : SimpleGraph (Fin 7) where
  Adj r s := witnessHAdjBool r s = true
  symm := by
    intro r s
    fin_cases r <;> fin_cases s <;> decide
  loopless := by
    intro r
    fin_cases r <;> decide

instance instDecidableRelWitnessHAdj : DecidableRel witnessH.Adj :=
  fun r s => inferInstanceAs (Decidable (witnessHAdjBool r s = true))

/--
Pulling back $H^-$ (`witnessHMinus`) along `Fin.succEmb : Fin 7 ↪ Fin 8` (`r ↦ r + 1`)
recovers the 7-vertex witness graph $H$ (`witnessH`).
-/
theorem witnessHMinus_comap_succEmb : witnessHMinus.comap (Fin.succEmb 7) = witnessH := by
  ext r s
  fin_cases r <;> fin_cases s <;> decide

/--
The base 5-vertex subgraph $H_0$ of `witnessH` on `{1, 4, 6, 2, 3}` (0-indexed `![0, 3, 5, 1, 2]`)
is isomorphic to $\overline{P_5}$ (`P5Compl`), matching Proposition 3.2(1) in `FMBV4-016_readable.tex`.
-/
def gBaseP5Compl : Fin 5 ↪ Fin 7 where
  toFun := ![0, 3, 5, 1, 2]
  inj' := by
    intro u v
    fin_cases u <;> fin_cases v <;> decide

theorem witnessH_comap_gBaseP5Compl : P5Compl = witnessH.comap gBaseP5Compl := by
  ext u v
  fin_cases u <;> fin_cases v <;> decide

/-! ### Proposition 3.2(2) and 3.2(3): Explicit $\overline{P_6}$ Embeddings in $H^+$ and $H^-$ -/

/--
The 6-vertex embedding `![1, 4, 6, 2, 5, 3]` into `Fin 8` exhibiting an induced copy of
$\overline{P_6}$ (`P6Compl`) inside $H^+$ (`witnessHPlus`), corresponding to the complement path
$P_6 = 1 - 4 - 6 - 2 - 5 - 3$ on $S_+ = \{1, 2, 3, 4, 5, 6\}$.
(Proposition 3.2(2) in `FMBV4-016_readable.tex`.)
-/
def gPlus : Fin 6 ↪ Fin 8 where
  toFun := ![1, 4, 6, 2, 5, 3]
  inj' := by
    intro u v
    fin_cases u <;> fin_cases v <;> decide

theorem witnessHPlus_comap_gPlus : P6Compl = witnessHPlus.comap gPlus := by
  ext u v
  fin_cases u <;> fin_cases v <;> decide

/--
**Proposition 3.2(2) (`prop:wonderful`)**:
The 8-vertex graph $H^+$ (`witnessHPlus`) contains an induced $\overline{P_6}$ (`P6Compl`).
-/
theorem witnessHPlus_contains_P6Compl : ¬IsInducedSubgraphFree witnessHPlus P6Compl := by
  intro h
  exact h ⟨gPlus, witnessHPlus_comap_gPlus⟩

/--
The 6-vertex embedding `![1, 4, 0, 7, 3, 2]` into `Fin 8` exhibiting an induced copy of
$\overline{P_6}$ (`P6Compl`) inside $H^-$ (`witnessHMinus`), corresponding to the complement path
$P_6 = 1 - 4 - 0 - 7 - 3 - 2$ on $S_- = \{0, 1, 2, 3, 4, 7\}$.
(Proposition 3.2(3) in `FMBV4-016_readable.tex`.)
-/
def gMinus : Fin 6 ↪ Fin 8 where
  toFun := ![1, 4, 0, 7, 3, 2]
  inj' := by
    intro u v
    fin_cases u <;> fin_cases v <;> decide

theorem witnessHMinus_comap_gMinus : P6Compl = witnessHMinus.comap gMinus := by
  ext u v
  fin_cases u <;> fin_cases v <;> decide

/--
**Proposition 3.2(3) (`prop:wonderful`)**:
The 8-vertex graph $H^-$ (`witnessHMinus`) contains an induced $\overline{P_6}$ (`P6Compl`).
-/
theorem witnessHMinus_contains_P6Compl : ¬IsInducedSubgraphFree witnessHMinus P6Compl := by
  intro h
  exact h ⟨gMinus, witnessHMinus_comap_gMinus⟩

/-! ### Finite Structural Characterizations of `witnessH`, `witnessHPlus`, and `witnessHMinus` -/

theorem witnessHPlus_adj_zero_succ (r : Fin 7) :
    witnessHPlus.Adj 0 r.succ ↔ r = 0 ∨ r = 1 ∨ r = 2 := by
  fin_cases r <;> decide

theorem witnessHMinus_adj_zero_succ (r : Fin 7) :
    witnessHMinus.Adj 0 r.succ ↔ r = 0 ∨ r = 1 ∨ r = 2 := by
  fin_cases r <;> decide

theorem fin7_eq_or_ge_three (r : Fin 7) :
    (r = 0 ∨ r = 1 ∨ r = 2) ∨ (r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6) := by
  fin_cases r <;> decide

theorem witnessHPlus_adj_succ_succ (r s : Fin 7) :
    witnessHPlus.Adj r.succ s.succ ↔
      witnessH.Adj r s ∨ (r = 1 ∧ s = 2) ∨ (r = 2 ∧ s = 1) := by
  fin_cases r <;> fin_cases s <;> decide

theorem witnessHMinus_adj_succ_succ (r s : Fin 7) :
    witnessHMinus.Adj r.succ s.succ ↔ witnessH.Adj r s := by
  fin_cases r <;> fin_cases s <;> decide

/--
Exhaustive list of the 9 non-edges (18 ordered distinct non-adjacent pairs) of `witnessH`.
-/
theorem witnessH_nonadj_cases (r s : Fin 7) (hne : r ≠ s) (hn : ¬witnessH.Adj r s) :
    (r = 1 ∧ s = 2) ∨ (r = 2 ∧ s = 1) ∨
    (r = 0 ∧ s = 3) ∨ (r = 3 ∧ s = 0) ∨
    (r = 1 ∧ s = 4) ∨ (r = 4 ∧ s = 1) ∨
    (r = 2 ∧ s = 4) ∨ (r = 4 ∧ s = 2) ∨
    (r = 1 ∧ s = 5) ∨ (r = 5 ∧ s = 1) ∨
    (r = 3 ∧ s = 5) ∨ (r = 5 ∧ s = 3) ∨
    (r = 2 ∧ s = 6) ∨ (r = 6 ∧ s = 2) ∨
    (r = 4 ∧ s = 6) ∨ (r = 6 ∧ s = 4) ∨
    (r = 5 ∧ s = 6) ∨ (r = 6 ∧ s = 5) := by
  fin_cases r <;> fin_cases s <;> revert hne hn <;> decide

/-! ### Blockade Pattern Graph and Open Attachment Index Set (Proposition 3.2(4)) -/

theorem isCompletePair_symm (G : SimpleGraph V) (A B : Finset V) :
    IsCompletePair G A B ↔ IsCompletePair G B A :=
  ⟨fun h u hu v hv => G.symm (h v hv u hu), fun h u hu v hv => G.symm (h v hv u hu)⟩

/--
The pattern graph $J$ of a blockade $B : \text{Fin } \ell \to \text{Finset } V$ in $G$
(Section 2.1 of `FMBV4-016_readable.tex`): distinct indices $i \neq j$ are adjacent in $J$
if and only if $(B_i, B_j)$ is a complete pair in $G$.
-/
def blockadePatternGraph (G : SimpleGraph V) {ℓ : ℕ} (B : Fin ℓ → Finset V) :
    SimpleGraph (Fin ℓ) where
  Adj i j := i ≠ j ∧ IsCompletePair G (B i) (B j)
  symm _ _ := fun ⟨hne, h⟩ => ⟨hne.symm, (isCompletePair_symm G _ _).mp h⟩
  loopless _ h := h.1 rfl

@[simp]
theorem blockadePatternGraph_adj (G : SimpleGraph V) {ℓ : ℕ} (B : Fin ℓ → Finset V)
    (i j : Fin ℓ) :
    (blockadePatternGraph G B).Adj i j ↔ i ≠ j ∧ IsCompletePair G (B i) (B j) :=
  Iff.rfl

/--
The open attachment index set $I(v) = \{i \in [\ell] : 0 < |N_G(v) \cap B_i| < \frac{1}{2}|B_i|\}$
of an external vertex $v$ with respect to a blockade $B$ in $G$
(Proposition 3.2(4) of `FMBV4-016_readable.tex`).
-/
noncomputable def openAttachmentIndices (G : SimpleGraph V) {ℓ : ℕ}
    (B : Fin ℓ → Finset V) (v : V) : Finset (Fin ℓ) :=
  by classical exact Finset.univ.filter (fun i =>
    0 < (neighborFinsetIn G v (B i)).card ∧
    ((neighborFinsetIn G v (B i)).card : ℝ) < (1 / 2 : ℝ) * ((B i).card : ℝ))

@[simp]
theorem mem_openAttachmentIndices (G : SimpleGraph V) {ℓ : ℕ}
    (B : Fin ℓ → Finset V) (v : V) (i : Fin ℓ) :
    i ∈ openAttachmentIndices G B v ↔
      0 < (neighborFinsetIn G v (B i)).card ∧
      ((neighborFinsetIn G v (B i)).card : ℝ) < (1 / 2 : ℝ) * ((B i).card : ℝ) := by
  simp [openAttachmentIndices]

@[simp]
theorem mem_neighborFinsetIn (G : SimpleGraph V) (v : V) (S : Finset V) (u : V) :
    u ∈ neighborFinsetIn G v S ↔ u ∈ S ∧ G.Adj v u := by
  simp [neighborFinsetIn]

/--
If $0 < |N_G(v) \cap B_j|$, there exists a vertex $u \in B_j$ adjacent to $v$ in $G$.
-/
theorem exists_adj_in_block_of_pos (G : SimpleGraph V) (B_j : Finset V) (v : V)
    (hpos : 0 < (neighborFinsetIn G v B_j).card) :
    ∃ u ∈ B_j, G.Adj v u := by
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
  rw [mem_neighborFinsetIn] at hu
  exact ⟨u, hu.1, hu.2⟩

/--
**Pigeonhole Non-Adjacency Selection Lemma** (Proposition 3.2(4) of `FMBV4-016_readable.tex`):
If $|N_G(v) \cap B_j| < \frac{1}{2}|B_j|$, $6 x \le 1/2$, and $u_1, u_2, u_3$ each have at most
$x |B_j|$ neighbors in $B_j$, then there exists $w \in B_j$ non-adjacent in $G$ to $v, u_1, u_2, u_3$.
-/
theorem exists_nonadj_three_in_block (G : SimpleGraph V) {B_j : Finset V} {v u1 u2 u3 : V} {x : ℝ}
    (hx : 6 * x ≤ 1 / 2)
    (hv : ((neighborFinsetIn G v B_j).card : ℝ) < (1 / 2 : ℝ) * (B_j.card : ℝ))
    (hu1 : ((neighborFinsetIn G u1 B_j).card : ℝ) ≤ x * (B_j.card : ℝ))
    (hu2 : ((neighborFinsetIn G u2 B_j).card : ℝ) ≤ x * (B_j.card : ℝ))
    (hu3 : ((neighborFinsetIn G u3 B_j).card : ℝ) ≤ x * (B_j.card : ℝ)) :
    ∃ w ∈ B_j, ¬G.Adj v w ∧ ¬G.Adj u1 w ∧ ¬G.Adj u2 w ∧ ¬G.Adj u3 w := by
  classical
  by_contra! h
  have hsub : B_j ⊆ ((neighborFinsetIn G v B_j ∪ neighborFinsetIn G u1 B_j) ∪
      neighborFinsetIn G u2 B_j) ∪ neighborFinsetIn G u3 B_j := by
    intro w hw
    rw [Finset.mem_union, Finset.mem_union, Finset.mem_union,
      mem_neighborFinsetIn, mem_neighborFinsetIn, mem_neighborFinsetIn, mem_neighborFinsetIn]
    by_cases hvw : G.Adj v w
    · left; left; left; exact ⟨hw, hvw⟩
    · by_cases h1w : G.Adj u1 w
      · left; left; right; exact ⟨hw, h1w⟩
      · by_cases h2w : G.Adj u2 w
        · left; right; exact ⟨hw, h2w⟩
        · right; exact ⟨hw, h w hw hvw h1w h2w⟩
  have hcard_nat : B_j.card ≤ (neighborFinsetIn G v B_j).card +
      (neighborFinsetIn G u1 B_j).card + (neighborFinsetIn G u2 B_j).card +
      (neighborFinsetIn G u3 B_j).card := by
    calc B_j.card
      _ ≤ (((neighborFinsetIn G v B_j ∪ neighborFinsetIn G u1 B_j) ∪
            neighborFinsetIn G u2 B_j) ∪ neighborFinsetIn G u3 B_j).card :=
          Finset.card_le_card hsub
      _ ≤ ((neighborFinsetIn G v B_j ∪ neighborFinsetIn G u1 B_j) ∪
            neighborFinsetIn G u2 B_j).card + (neighborFinsetIn G u3 B_j).card :=
          Finset.card_union_le _ _
      _ ≤ (neighborFinsetIn G v B_j ∪ neighborFinsetIn G u1 B_j).card +
            (neighborFinsetIn G u2 B_j).card + (neighborFinsetIn G u3 B_j).card :=
          Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ (neighborFinsetIn G v B_j).card + (neighborFinsetIn G u1 B_j).card +
            (neighborFinsetIn G u2 B_j).card + (neighborFinsetIn G u3 B_j).card :=
          Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
  have hcard_real : (B_j.card : ℝ) ≤ ((neighborFinsetIn G v B_j).card : ℝ) +
      ((neighborFinsetIn G u1 B_j).card : ℝ) + ((neighborFinsetIn G u2 B_j).card : ℝ) +
      ((neighborFinsetIn G u3 B_j).card : ℝ) := by
    exact_mod_cast hcard_nat
  have hB_nonneg : (0 : ℝ) ≤ (B_j.card : ℝ) := Nat.cast_nonneg _
  have hu1_nonneg : (0 : ℝ) ≤ ((neighborFinsetIn G u1 B_j).card : ℝ) := Nat.cast_nonneg _
  have hx_nonneg : (0 : ℝ) ≤ x * (B_j.card : ℝ) := le_trans hu1_nonneg hu1
  have h3x : 3 * (x * (B_j.card : ℝ)) ≤ (1 / 2 : ℝ) * (B_j.card : ℝ) := by
    have h6 : 6 * (x * (B_j.card : ℝ)) ≤ (1 / 2 : ℝ) * (B_j.card : ℝ) := by
      calc 6 * (x * (B_j.card : ℝ))
        _ = (6 * x) * (B_j.card : ℝ) := by ring
        _ ≤ (1 / 2 : ℝ) * (B_j.card : ℝ) := mul_le_mul_of_nonneg_right hx hB_nonneg
    linarith
  linarith

/--
If `emb : Fin 7 ↪ Fin ℓ` embeds `witnessH` as an induced subgraph of `blockadePatternGraph G B`,
then any `r, s : Fin 7` adjacent in `witnessH` have complete blocks `(B (emb r), B (emb s))` in $G$.
-/
theorem adj_of_witnessH_adj {G : SimpleGraph V} {ℓ : ℕ} {B : Fin ℓ → Finset V}
    (emb : Fin 7 ↪ Fin ℓ)
    (hemb_adj : witnessH = (blockadePatternGraph G B).comap emb)
    {r s : Fin 7} (hadj : witnessH.Adj r s)
    {ur us : V} (hur : ur ∈ B (emb r)) (hus : us ∈ B (emb s)) :
    G.Adj ur us := by
  have hJ : (blockadePatternGraph G B).Adj (emb r) (emb s) := by
    have h := congr_arg (fun H => H.Adj r s) hemb_adj
    exact h.mp hadj
  exact hJ.2 ur hur us hus

/--
If `emb : Fin 7 ↪ Fin ℓ` embeds `witnessH` as an induced subgraph of `blockadePatternGraph G B`
for a complete-or-$x$-sparse blockade $B$, then for any distinct `r ≠ j` non-adjacent in `witnessH`,
any vertex `ur ∈ B (emb r)` has at most $x |B_{\text{emb } j}|$ neighbors in $B_{\text{emb } j}$.
-/
theorem sparse_of_not_witnessH_adj {G : SimpleGraph V} {S : Finset V} {ℓ : ℕ} {w x : ℝ}
    {B : Fin ℓ → Finset V}
    (hB : IsCompleteOrXSparseBlockadeIn G S ℓ w x B)
    (emb : Fin 7 ↪ Fin ℓ)
    (hemb_adj : witnessH = (blockadePatternGraph G B).comap emb)
    {r j : Fin 7} (hne : r ≠ j) (hnadj : ¬witnessH.Adj r j)
    {ur : V} (hur : ur ∈ B (emb r)) :
    ((neighborFinsetIn G ur (B (emb j))).card : ℝ) ≤ x * ((B (emb j)).card : ℝ) := by
  have hne_emb : emb r ≠ emb j := emb.injective.ne hne
  rcases hB.2 (emb r) (emb j) hne_emb with hcomp | hsparse
  · exfalso
    have hJ : (blockadePatternGraph G B).Adj (emb r) (emb j) := ⟨hne_emb, hcomp⟩
    have h := congr_arg (fun H => H.Adj r j) hemb_adj
    exact hnadj (h.mpr hJ)
  · exact hsparse.2 ur hur

/--
Given an external vertex $v$ and vertices $u_0, \dots, u_6$ in disjoint blocks $B_{\text{emb } 0}, \dots, B_{\text{emb } 6}$
matching the adjacency of $H^+$ (if $u_1 u_2 \in E(G)$) or $H^-$ (if $u_1 u_2 \notin E(G)$),
the 8-vertex map `Fin.cons v u : Fin 8 ↪ V` embeds either `witnessHPlus` or `witnessHMinus` into $G$,
contradicting `IsInducedSubgraphFree G P6Compl`.
-/
theorem not_isP6ComplFree_of_witness_tuple {G : SimpleGraph V} {S : Finset V} {ℓ : ℕ} {w : ℝ}
    {B : Fin ℓ → Finset V} (hB_block : IsBlockadeIn G S ℓ w B)
    (v : V) (hv_ext : ∀ i : Fin ℓ, v ∉ B i)
    (emb : Fin 7 ↪ Fin ℓ)
    (hemb_adj : witnessH = (blockadePatternGraph G B).comap emb)
    (u : Fin 7 → V) (hu_mem : ∀ r : Fin 7, u r ∈ B (emb r))
    (hv0 : G.Adj v (u 0)) (hv1 : G.Adj v (u 1)) (hv2 : G.Adj v (u 2))
    (hv3 : ¬G.Adj v (u 3)) (hv4 : ¬G.Adj v (u 4)) (hv5 : ¬G.Adj v (u 5)) (hv6 : ¬G.Adj v (u 6))
    (h03 : ¬G.Adj (u 0) (u 3))
    (h14 : ¬G.Adj (u 1) (u 4)) (h24 : ¬G.Adj (u 2) (u 4))
    (h15 : ¬G.Adj (u 1) (u 5)) (h35 : ¬G.Adj (u 3) (u 5))
    (h26 : ¬G.Adj (u 2) (u 6)) (h46 : ¬G.Adj (u 4) (u 6)) (h56 : ¬G.Adj (u 5) (u 6)) :
    ¬IsInducedSubgraphFree G P6Compl := by
  let f : Fin 8 ↪ V :=
    { toFun := Fin.cons v u
      inj' := by
        intro a b
        refine Fin.cases ?_ ?_ a <;> refine Fin.cases ?_ ?_ b
        · intro _; rfl
        · intro s hs
          simp only [Fin.cons_zero, Fin.cons_succ] at hs
          exfalso
          exact hv_ext (emb s) (hs ▸ hu_mem s)
        · intro r hr
          simp only [Fin.cons_zero, Fin.cons_succ] at hr
          exfalso
          exact hv_ext (emb r) (hr.symm ▸ hu_mem r)
        · intro r s hrs
          simp only [Fin.cons_succ] at hrs
          by_contra hne_fin
          have hne_r : r ≠ s := fun h => hne_fin (congr_arg Fin.succ h.symm)
          have hdisj := hB_block.pairwise_disjoint (emb r) (emb s) (emb.injective.ne hne_r)
          exact Finset.disjoint_left.mp hdisj (hu_mem r) (hrs ▸ hu_mem s) }
  have hf_zero : ∀ r : Fin 7, G.Adj (f 0) (f r.succ) ↔ r = 0 ∨ r = 1 ∨ r = 2 := by
    intro r
    change G.Adj v (u r) ↔ r = 0 ∨ r = 1 ∨ r = 2
    rcases fin7_eq_or_ge_three r with (rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)
    · exact iff_of_true hv0 (Or.inl rfl)
    · exact iff_of_true hv1 (Or.inr (Or.inl rfl))
    · exact iff_of_true hv2 (Or.inr (Or.inr rfl))
    · exact iff_of_false hv3 (by decide)
    · exact iff_of_false hv4 (by decide)
    · exact iff_of_false hv5 (by decide)
    · exact iff_of_false hv6 (by decide)
  have hf_succ : ∀ r s : Fin 7,
      G.Adj (f r.succ) (f s.succ) ↔
        witnessH.Adj r s ∨ ((r = 1 ∧ s = 2 ∨ r = 2 ∧ s = 1) ∧ G.Adj (u 1) (u 2)) := by
    intro r s
    change G.Adj (u r) (u s) ↔ _
    constructor
    · intro hG
      have hne : r ≠ s := fun h => G.loopless (u r) (h ▸ hG)
      by_cases hadj : witnessH.Adj r s
      · exact Or.inl hadj
      · rcases witnessH_nonadj_cases r s hne hadj with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, hG⟩
        · exact Or.inr ⟨Or.inr ⟨rfl, rfl⟩, G.symm hG⟩
        · exact False.elim (h03 hG)
        · exact False.elim (h03 (G.symm hG))
        · exact False.elim (h14 hG)
        · exact False.elim (h14 (G.symm hG))
        · exact False.elim (h24 hG)
        · exact False.elim (h24 (G.symm hG))
        · exact False.elim (h15 hG)
        · exact False.elim (h15 (G.symm hG))
        · exact False.elim (h35 hG)
        · exact False.elim (h35 (G.symm hG))
        · exact False.elim (h26 hG)
        · exact False.elim (h26 (G.symm hG))
        · exact False.elim (h46 hG)
        · exact False.elim (h46 (G.symm hG))
        · exact False.elim (h56 hG)
        · exact False.elim (h56 (G.symm hG))
    · rintro (hadj | ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, h12⟩)
      · exact adj_of_witnessH_adj emb hemb_adj hadj (hu_mem r) (hu_mem s)
      · exact h12
      · exact G.symm h12
  by_cases h12 : G.Adj (u 1) (u 2)
  · have hPlus : witnessHPlus = G.comap f := by
      ext a b
      refine Fin.cases ?_ ?_ a <;> refine Fin.cases ?_ ?_ b
      · simp
      · intro s
        rw [comap_adj, witnessHPlus_adj_zero_succ, hf_zero]
      · intro r
        rw [comap_adj, witnessHPlus.adj_comm, G.adj_comm, witnessHPlus_adj_zero_succ, hf_zero]
      · intro r s
        rw [comap_adj, witnessHPlus_adj_succ_succ, hf_succ]
        simp [h12]
    intro hFree
    refine hFree ⟨gPlus.trans f, ?_⟩
    ext a b
    have h1 := congr_arg (fun H => H.Adj a b) witnessHPlus_comap_gPlus
    have h2 := congr_arg (fun H => H.Adj (gPlus a) (gPlus b)) hPlus
    exact (h1.trans h2).to_iff
  · have hMinus : witnessHMinus = G.comap f := by
      ext a b
      refine Fin.cases ?_ ?_ a <;> refine Fin.cases ?_ ?_ b
      · simp
      · intro s
        rw [comap_adj, witnessHMinus_adj_zero_succ, hf_zero]
      · intro r
        rw [comap_adj, witnessHMinus.adj_comm, G.adj_comm, witnessHMinus_adj_zero_succ, hf_zero]
      · intro r s
        rw [comap_adj, witnessHMinus_adj_succ_succ, hf_succ]
        simp [h12]
    intro hFree
    refine hFree ⟨gMinus.trans f, ?_⟩
    ext a b
    have h1 := congr_arg (fun H => H.Adj a b) witnessHMinus_comap_gMinus
    have h2 := congr_arg (fun H => H.Adj (gMinus a) (gMinus b)) hMinus
    exact (h1.trans h2).to_iff

/--
**Proposition 3.2(4) (`prop:wonderful`, Pattern Graph $H$-Freeness on $I(v)$)**:
Let $G$ be a $\overline{P_6}$-free graph and let $B : \text{Fin } \ell \to \text{Finset } V$ be a
complete-or-$x$-sparse blockade in $G$ with $6 x \le 1/2$. For any external vertex
$v \notin \bigcup_i B_i$, there is no induced embedding `emb : Fin 7 ↪ Fin ℓ` of `witnessH`
into `blockadePatternGraph G B` whose image is contained in `openAttachmentIndices G B v`.
-/
theorem patternGraph_openAttachment_witnessH_free
    {G : SimpleGraph V} {S : Finset V} {ℓ : ℕ} {w x : ℝ} {B : Fin ℓ → Finset V}
    (hG : IsInducedSubgraphFree G P6Compl)
    (hB : IsCompleteOrXSparseBlockadeIn G S ℓ w x B)
    (hx : 6 * x ≤ 1 / 2)
    (v : V) (hv_ext : ∀ i : Fin ℓ, v ∉ B i)
    (emb : Fin 7 ↪ Fin ℓ)
    (hemb_mem : ∀ r : Fin 7, emb r ∈ openAttachmentIndices G B v)
    (hemb_adj : witnessH = (blockadePatternGraph G B).comap emb) :
    False := by
  obtain ⟨u0, hu0_mem, hv0⟩ := exists_adj_in_block_of_pos G (B (emb 0)) v
    ((mem_openAttachmentIndices G B v (emb 0)).mp (hemb_mem 0)).1
  obtain ⟨u1, hu1_mem, hv1⟩ := exists_adj_in_block_of_pos G (B (emb 1)) v
    ((mem_openAttachmentIndices G B v (emb 1)).mp (hemb_mem 1)).1
  obtain ⟨u2, hu2_mem, hv2⟩ := exists_adj_in_block_of_pos G (B (emb 2)) v
    ((mem_openAttachmentIndices G B v (emb 2)).mp (hemb_mem 2)).1
  have hs03 := sparse_of_not_witnessH_adj hB emb hemb_adj (r := 0) (j := 3)
    (by decide) (by decide) hu0_mem
  obtain ⟨u3, hu3_mem, hv3, h03, _, _⟩ := exists_nonadj_three_in_block G hx
    ((mem_openAttachmentIndices G B v (emb 3)).mp (hemb_mem 3)).2 hs03 hs03 hs03
  have hs14 := sparse_of_not_witnessH_adj hB emb hemb_adj (r := 1) (j := 4)
    (by decide) (by decide) hu1_mem
  have hs24 := sparse_of_not_witnessH_adj hB emb hemb_adj (r := 2) (j := 4)
    (by decide) (by decide) hu2_mem
  obtain ⟨u4, hu4_mem, hv4, h14, h24, _⟩ := exists_nonadj_three_in_block G hx
    ((mem_openAttachmentIndices G B v (emb 4)).mp (hemb_mem 4)).2 hs14 hs24 hs24
  have hs15 := sparse_of_not_witnessH_adj hB emb hemb_adj (r := 1) (j := 5)
    (by decide) (by decide) hu1_mem
  have hs35 := sparse_of_not_witnessH_adj hB emb hemb_adj (r := 3) (j := 5)
    (by decide) (by decide) hu3_mem
  obtain ⟨u5, hu5_mem, hv5, h15, h35, _⟩ := exists_nonadj_three_in_block G hx
    ((mem_openAttachmentIndices G B v (emb 5)).mp (hemb_mem 5)).2 hs15 hs35 hs35
  have hs26 := sparse_of_not_witnessH_adj hB emb hemb_adj (r := 2) (j := 6)
    (by decide) (by decide) hu2_mem
  have hs46 := sparse_of_not_witnessH_adj hB emb hemb_adj (r := 4) (j := 6)
    (by decide) (by decide) hu4_mem
  have hs56 := sparse_of_not_witnessH_adj hB emb hemb_adj (r := 5) (j := 6)
    (by decide) (by decide) hu5_mem
  obtain ⟨u6, hu6_mem, hv6, h26, h46, h56⟩ := exists_nonadj_three_in_block G hx
    ((mem_openAttachmentIndices G B v (emb 6)).mp (hemb_mem 6)).2 hs26 hs46 hs56
  let u : Fin 7 → V := ![u0, u1, u2, u3, u4, u5, u6]
  have hu_mem : ∀ r : Fin 7, u r ∈ B (emb r) := by
    intro r
    fin_cases r <;> assumption
  exact not_isP6ComplFree_of_witness_tuple hB.1 v hv_ext emb hemb_adj u hu_mem
    hv0 hv1 hv2 hv3 hv4 hv5 hv6 h03 h14 h24 h15 h35 h26 h46 h56 hG

/--
Induced-subgraph formulation of `patternGraph_openAttachment_witnessH_free`:
the induced subgraph of `blockadePatternGraph G B` on `openAttachmentIndices G B v` is
`witnessH`-free.
-/
theorem isInducedSubgraphFree_patternGraph_induce_openAttachment
    {G : SimpleGraph V} {S : Finset V} {ℓ : ℕ} {w x : ℝ} {B : Fin ℓ → Finset V}
    (hG : IsInducedSubgraphFree G P6Compl)
    (hB : IsCompleteOrXSparseBlockadeIn G S ℓ w x B)
    (hx : 6 * x ≤ 1 / 2)
    (v : V) (hv_ext : ∀ i : Fin ℓ, v ∉ B i) :
    IsInducedSubgraphFree
      ((blockadePatternGraph G B).induce (openAttachmentIndices G B v : Set (Fin ℓ)))
      witnessH := by
  rintro ⟨emb, hemb⟩
  let emb' : Fin 7 ↪ Fin ℓ := emb.trans (Function.Embedding.subtype _)
  have hemb_mem : ∀ r : Fin 7, emb' r ∈ openAttachmentIndices G B v := fun r => (emb r).2
  have hemb_adj : witnessH = (blockadePatternGraph G B).comap emb' := by
    ext r s
    have h := congr_arg (fun H => H.Adj r s) hemb
    simpa [emb', comap_adj] using h
  exact patternGraph_openAttachment_witnessH_free hG hB hx v hv_ext emb' hemb_mem hemb_adj

/-! ### Proposition 3.2(4): Outcome (W2) via Double Counting over External Vertices -/

/--
The set of external vertices $S \setminus \bigcup_{j=1}^\ell B_j$ of a blockade $B$ inside $S$.
-/
noncomputable def blockadeExternalVerts (S : Finset V) {ℓ : ℕ} (B : Fin ℓ → Finset V) :
    Finset V :=
  by classical exact S.filter (fun v => ∀ j : Fin ℓ, v ∉ B j)

@[simp]
theorem mem_blockadeExternalVerts (S : Finset V) {ℓ : ℕ} (B : Fin ℓ → Finset V) (v : V) :
    v ∈ blockadeExternalVerts S B ↔ v ∈ S ∧ ∀ j : Fin ℓ, v ∉ B j := by
  simp [blockadeExternalVerts]

theorem card_blockadeExternalVerts_le (S : Finset V) {ℓ : ℕ} (B : Fin ℓ → Finset V) :
    (blockadeExternalVerts S B).card ≤ S.card := by
  classical exact Finset.card_filter_le _ _

/--
For a block index $i \in [\ell]$, the set of external vertices $v \in S \setminus \bigcup_j B_j$
satisfying $0 < |N_G(v) \cap B_i| < \frac{1}{2}|B_i|$ (i.e., $i \in I(v)$).
-/
noncomputable def openAttachmentExternalVerts (G : SimpleGraph V) (S : Finset V) {ℓ : ℕ}
    (B : Fin ℓ → Finset V) (i : Fin ℓ) : Finset V :=
  by classical exact (blockadeExternalVerts S B).filter (fun v => i ∈ openAttachmentIndices G B v)

@[simp]
theorem mem_openAttachmentExternalVerts (G : SimpleGraph V) (S : Finset V) {ℓ : ℕ}
    (B : Fin ℓ → Finset V) (i : Fin ℓ) (v : V) :
    v ∈ openAttachmentExternalVerts G S B i ↔
      v ∈ blockadeExternalVerts S B ∧ i ∈ openAttachmentIndices G B v := by
  simp [openAttachmentExternalVerts]

/--
**Double-Counting Identity (Proposition 3.2(4) of `FMBV4-016_readable.tex`)**:
\[
\sum_{i \in [\ell]} \left|\left\{v \in S \setminus \bigcup_{j} B_j : i \in I(v)\right\}\right|
= \sum_{v \in S \setminus \bigcup_{j} B_j} |I(v)|.
\]
-/
theorem sum_card_openAttachmentExternalVerts (G : SimpleGraph V) (S : Finset V) {ℓ : ℕ}
    (B : Fin ℓ → Finset V) :
    ∑ i : Fin ℓ, (openAttachmentExternalVerts G S B i).card =
      ∑ v ∈ blockadeExternalVerts S B, (openAttachmentIndices G B v).card := by
  classical
  simp only [openAttachmentExternalVerts, Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← Finset.card_filter]
  congr 1
  ext i
  simp

/--
**Proposition 3.2(4) — Outcome (W2) (`FMBV4-016_readable.tex`)**:
If $\ell \ge 1$, $y > 0$, $S$ is nonempty, and every external vertex
$v \in S \setminus \bigcup_j B_j$ satisfies $|I(v)| < y \ell$, then by the pigeonhole principle
there exists a block index $i^* \in [\ell]$ such that
$|\{v \in S \setminus \bigcup_j B_j : i^* \in I(v)\}| < y |S|$.
-/
theorem exists_block_few_openAttachmentExternalVerts
    (G : SimpleGraph V) (S : Finset V) {ℓ : ℕ} (B : Fin ℓ → Finset V) {y : ℝ}
    (hℓ : 0 < ℓ) (hy : 0 < y) (hS : S.Nonempty)
    (hsmall : ∀ v ∈ blockadeExternalVerts S B,
      ((openAttachmentIndices G B v).card : ℝ) < y * (ℓ : ℝ)) :
    ∃ i : Fin ℓ, ((openAttachmentExternalVerts G S B i).card : ℝ) < y * (S.card : ℝ) := by
  by_contra! hall
  have hS_pos : (0 : ℝ) < (S.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hS)
  rcases (blockadeExternalVerts S B).eq_empty_or_nonempty with hempty | hne
  · let i0 : Fin ℓ := ⟨0, hℓ⟩
    have hcard0 : (openAttachmentExternalVerts G S B i0).card = 0 := by
      simp [openAttachmentExternalVerts, hempty]
    have hi0 := hall i0
    rw [hcard0, Nat.cast_zero] at hi0
    have hyS : 0 < y * (S.card : ℝ) := mul_pos hy hS_pos
    linarith
  · have hsum_eq : ∑ i : Fin ℓ, ((openAttachmentExternalVerts G S B i).card : ℝ) =
        ∑ v ∈ blockadeExternalVerts S B, ((openAttachmentIndices G B v).card : ℝ) := by
      exact_mod_cast sum_card_openAttachmentExternalVerts G S B
    have hsum_lt : ∑ v ∈ blockadeExternalVerts S B, ((openAttachmentIndices G B v).card : ℝ) <
        ((blockadeExternalVerts S B).card : ℝ) * (y * (ℓ : ℝ)) := by
      calc ∑ v ∈ blockadeExternalVerts S B, ((openAttachmentIndices G B v).card : ℝ)
        _ < ∑ _v ∈ blockadeExternalVerts S B, (y * (ℓ : ℝ)) :=
            Finset.sum_lt_sum_of_nonempty hne hsmall
        _ = ((blockadeExternalVerts S B).card : ℝ) * (y * (ℓ : ℝ)) := by
            simp [Finset.sum_const, nsmul_eq_mul]
    have hext_le : ((blockadeExternalVerts S B).card : ℝ) ≤ (S.card : ℝ) := by
      exact_mod_cast card_blockadeExternalVerts_le S B
    have hyℓ_nonneg : (0 : ℝ) ≤ y * (ℓ : ℝ) :=
      mul_nonneg (le_of_lt hy) (Nat.cast_nonneg _)
    have hupper : ((blockadeExternalVerts S B).card : ℝ) * (y * (ℓ : ℝ)) ≤
        (ℓ : ℝ) * (y * (S.card : ℝ)) := by
      calc ((blockadeExternalVerts S B).card : ℝ) * (y * (ℓ : ℝ))
        _ ≤ (S.card : ℝ) * (y * (ℓ : ℝ)) := mul_le_mul_of_nonneg_right hext_le hyℓ_nonneg
        _ = (ℓ : ℝ) * (y * (S.card : ℝ)) := by ring
    have hlower : (ℓ : ℝ) * (y * (S.card : ℝ)) ≤
        ∑ i : Fin ℓ, ((openAttachmentExternalVerts G S B i).card : ℝ) := by
      calc (ℓ : ℝ) * (y * (S.card : ℝ))
        _ = ∑ _i : Fin ℓ, (y * (S.card : ℝ)) := by
            simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ i : Fin ℓ, ((openAttachmentExternalVerts G S B i).card : ℝ) :=
            Finset.sum_le_sum (fun i _ => hall i)
    linarith

/-! ### Proposition 3.2(4): Outcome (W1) via Clique or Independent Set in Pattern Graph -/

/--
The vertex union $S_R := \bigcup_{i \in R} B_i$ of a subset $R \subseteq [\ell]$ of blocks.
-/
noncomputable def blockUnion {ℓ : ℕ} (B : Fin ℓ → Finset V) (R : Finset (Fin ℓ)) : Finset V :=
  by classical exact R.biUnion B

@[simp]
theorem mem_blockUnion {ℓ : ℕ} (B : Fin ℓ → Finset V) (R : Finset (Fin ℓ)) (v : V) :
    v ∈ blockUnion B R ↔ ∃ i ∈ R, v ∈ B i := by
  classical simp [blockUnion]

theorem blockUnion_subset_of_blockade {G : SimpleGraph V} {S : Finset V} {ℓ : ℕ} {w : ℝ}
    {B : Fin ℓ → Finset V} (hB : IsBlockadeIn G S ℓ w B) (R : Finset (Fin ℓ)) :
    blockUnion B R ⊆ S := by
  intro v hv
  rw [mem_blockUnion] at hv
  rcases hv with ⟨i, _, hvi⟩
  exact hB.subset_ambient i hvi

/--
If the blocks $B_i$ are pairwise disjoint and every block $B_i$ ($i \in R$) has equal cardinality
`w_nat`, then $|S_R| = |R| \cdot w_{\text{nat}}$.
-/
theorem card_blockUnion_eq_mul {ℓ : ℕ} (B : Fin ℓ → Finset V)
    (hdisj : ∀ i j : Fin ℓ, i ≠ j → Disjoint (B i) (B j))
    (R : Finset (Fin ℓ)) (w_nat : ℕ) (hw : ∀ i ∈ R, (B i).card = w_nat) :
    (blockUnion B R).card = R.card * w_nat := by
  classical
  change (R.biUnion B).card = R.card * w_nat
  rw [Finset.card_biUnion (fun i _ j _ hij => hdisj i j hij)]
  rw [Finset.sum_congr rfl hw, Finset.sum_const, smul_eq_mul]

/--
If $R$ is nonempty and every block $B_i$ ($i \in R$) has cardinality `w_nat`, then
$w_{\text{nat}} \le |S_R|$.
-/
theorem width_le_card_blockUnion {ℓ : ℕ} (B : Fin ℓ → Finset V)
    (hdisj : ∀ i j : Fin ℓ, i ≠ j → Disjoint (B i) (B j))
    (R : Finset (Fin ℓ)) (hR : R.Nonempty) (w_nat : ℕ) (hw : ∀ i ∈ R, (B i).card = w_nat) :
    w_nat ≤ (blockUnion B R).card := by
  rw [card_blockUnion_eq_mul B hdisj R w_nat hw]
  exact Nat.le_mul_of_pos_left w_nat (Finset.card_pos.mpr hR)

/--
**Outcome (W1), Clique Case (`FMBV4-016_readable.tex`, Proposition 3.2(4))**:
If $R \subseteq [\ell]$ is a nonempty clique in the pattern graph `blockadePatternGraph G B`,
all blocks $B_i$ ($i \in R$) have equal size `w_nat`, and $\frac{1}{|R|} \le \varepsilon$,
then $\overline{G}[S_R]$ is $\varepsilon$-sparse (`IsEpsSparseOn Gᶜ (blockUnion B R) ε`),
and hence $S_R$ is $\varepsilon$-restricted in $G$ (`IsEpsRestrictedOn G (blockUnion B R) ε`).
-/
theorem isEpsSparseOn_compl_blockUnion_of_pattern_clique
    {G : SimpleGraph V} {ℓ : ℕ} {B : Fin ℓ → Finset V}
    (hdisj : ∀ i j : Fin ℓ, i ≠ j → Disjoint (B i) (B j))
    (R : Finset (Fin ℓ)) (hR_ne : R.Nonempty)
    (w_nat : ℕ) (hw : ∀ i ∈ R, (B i).card = w_nat)
    (hClique : ∀ i ∈ R, ∀ j ∈ R, i ≠ j → (blockadePatternGraph G B).Adj i j)
    {ε : ℝ} (hε : 1 / (R.card : ℝ) ≤ ε) :
    IsEpsSparseOn Gᶜ (blockUnion B R) ε := by
  classical
  intro z hz
  have hz' := hz
  rw [mem_blockUnion] at hz'
  rcases hz' with ⟨i, hiR, hzi⟩
  have hsub : neighborFinsetIn Gᶜ z (blockUnion B R) ⊆ B i := by
    intro u hu
    rw [mem_neighborFinsetIn, mem_blockUnion] at hu
    rcases hu with ⟨⟨j, hjR, huj⟩, hcompl⟩
    by_cases hij : i = j
    · exact hij ▸ huj
    · exfalso
      exact hcompl.2 ((hClique i hiR j hjR hij).2 z hzi u huj)
  have hcard_le : (neighborFinsetIn Gᶜ z (blockUnion B R)).card ≤ w_nat := by
    rw [← hw i hiR]
    exact Finset.card_le_card hsub
  have hcard_real : ((neighborFinsetIn Gᶜ z (blockUnion B R)).card : ℝ) ≤ (w_nat : ℝ) := by
    exact_mod_cast hcard_le
  have hU_card : ((blockUnion B R).card : ℝ) = (R.card : ℝ) * (w_nat : ℝ) := by
    exact_mod_cast card_blockUnion_eq_mul B hdisj R w_nat hw
  have hR_pos : (0 : ℝ) < (R.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hR_ne)
  have hR_ne_zero : (R.card : ℝ) ≠ 0 := ne_of_gt hR_pos
  have hw_nonneg : (0 : ℝ) ≤ (w_nat : ℝ) := Nat.cast_nonneg _
  have hU_nonneg : (0 : ℝ) ≤ (R.card : ℝ) * (w_nat : ℝ) :=
    mul_nonneg (le_of_lt hR_pos) hw_nonneg
  calc ((neighborFinsetIn Gᶜ z (blockUnion B R)).card : ℝ)
    _ ≤ (w_nat : ℝ) := hcard_real
    _ = (1 / (R.card : ℝ)) * ((R.card : ℝ) * (w_nat : ℝ)) := by
        field_simp [hR_ne_zero]
    _ ≤ ε * ((R.card : ℝ) * (w_nat : ℝ)) := mul_le_mul_of_nonneg_right hε hU_nonneg
    _ = ε * ((blockUnion B R).card : ℝ) := by rw [hU_card]

/--
**Outcome (W1), Stable Set Case (`FMBV4-016_readable.tex`, Proposition 3.2(4))**:
If $B$ is a complete-or-$x$-sparse blockade in $G$, $R \subseteq [\ell]$ is a nonempty independent
set in `blockadePatternGraph G B`, all blocks $B_i$ ($i \in R$) have equal size `w_nat`, and
$\frac{1}{|R|} + x \le \varepsilon$ (with $x \ge 0$), then $G[S_R]$ is $\varepsilon$-sparse
(`IsEpsSparseOn G (blockUnion B R) ε`), and hence $S_R$ is $\varepsilon$-restricted in $G$.
-/
theorem isEpsSparseOn_blockUnion_of_pattern_indep
    {G : SimpleGraph V} {S : Finset V} {ℓ : ℕ} {w x : ℝ} {B : Fin ℓ → Finset V}
    (hB : IsCompleteOrXSparseBlockadeIn G S ℓ w x B)
    (hx_nonneg : 0 ≤ x)
    (R : Finset (Fin ℓ)) (hR_ne : R.Nonempty)
    (w_nat : ℕ) (hw : ∀ i ∈ R, (B i).card = w_nat)
    (hIndep : ∀ i ∈ R, ∀ j ∈ R, i ≠ j → ¬(blockadePatternGraph G B).Adj i j)
    {ε : ℝ} (hε : 1 / (R.card : ℝ) + x ≤ ε) :
    IsEpsSparseOn G (blockUnion B R) ε := by
  classical
  intro z hz
  have hz' := hz
  rw [mem_blockUnion] at hz'
  rcases hz' with ⟨i, hiR, hzi⟩
  have hsub : neighborFinsetIn G z (blockUnion B R) ⊆
      B i ∪ (R.erase i).biUnion (fun j => neighborFinsetIn G z (B j)) := by
    intro u hu
    rw [mem_neighborFinsetIn, mem_blockUnion] at hu
    rcases hu with ⟨⟨j, hjR, huj⟩, hadj⟩
    rw [Finset.mem_union]
    by_cases hij : j = i
    · left; exact hij ▸ huj
    · right
      rw [Finset.mem_biUnion]
      refine ⟨j, Finset.mem_erase.mpr ⟨hij, hjR⟩, ?_⟩
      rw [mem_neighborFinsetIn]
      exact ⟨huj, hadj⟩
  have hcard_nat : (neighborFinsetIn G z (blockUnion B R)).card ≤
      (B i).card + ∑ j ∈ R.erase i, (neighborFinsetIn G z (B j)).card := by
    calc (neighborFinsetIn G z (blockUnion B R)).card
      _ ≤ (B i ∪ (R.erase i).biUnion (fun j => neighborFinsetIn G z (B j))).card :=
          Finset.card_le_card hsub
      _ ≤ (B i).card + ((R.erase i).biUnion (fun j => neighborFinsetIn G z (B j))).card :=
          Finset.card_union_le _ _
      _ ≤ (B i).card + ∑ j ∈ R.erase i, (neighborFinsetIn G z (B j)).card :=
          Nat.add_le_add_left Finset.card_biUnion_le _
  have hcard_real : ((neighborFinsetIn G z (blockUnion B R)).card : ℝ) ≤
      ((B i).card : ℝ) + ∑ j ∈ R.erase i, ((neighborFinsetIn G z (B j)).card : ℝ) := by
    exact_mod_cast hcard_nat
  have hsparse_term : ∀ j ∈ R.erase i,
      ((neighborFinsetIn G z (B j)).card : ℝ) ≤ x * (w_nat : ℝ) := by
    intro j hj
    rw [Finset.mem_erase] at hj
    have hij : i ≠ j := Ne.symm hj.1
    rcases hB.2 i j hij with hcomp | hsparse
    · exfalso
      exact hIndep i hiR j hj.2 hij ⟨hij, hcomp⟩
    · have h1 := hsparse.2 z hzi
      rw [hw j hj.2] at h1
      exact h1
  have herase_le : ((R.erase i).card : ℝ) ≤ (R.card : ℝ) := by
    exact_mod_cast Finset.card_erase_le
  have hxw_nonneg : (0 : ℝ) ≤ x * (w_nat : ℝ) := mul_nonneg hx_nonneg (Nat.cast_nonneg _)
  have hsum_le : ∑ j ∈ R.erase i, ((neighborFinsetIn G z (B j)).card : ℝ) ≤
      (R.card : ℝ) * (x * (w_nat : ℝ)) := by
    calc ∑ j ∈ R.erase i, ((neighborFinsetIn G z (B j)).card : ℝ)
      _ ≤ ∑ _j ∈ R.erase i, (x * (w_nat : ℝ)) := Finset.sum_le_sum hsparse_term
      _ = ((R.erase i).card : ℝ) * (x * (w_nat : ℝ)) := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (R.card : ℝ) * (x * (w_nat : ℝ)) :=
          mul_le_mul_of_nonneg_right herase_le hxw_nonneg
  have hU_card : ((blockUnion B R).card : ℝ) = (R.card : ℝ) * (w_nat : ℝ) := by
    exact_mod_cast card_blockUnion_eq_mul B hB.1.pairwise_disjoint R w_nat hw
  have hR_pos : (0 : ℝ) < (R.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hR_ne)
  have hR_ne_zero : (R.card : ℝ) ≠ 0 := ne_of_gt hR_pos
  have hU_nonneg : (0 : ℝ) ≤ (R.card : ℝ) * (w_nat : ℝ) :=
    mul_nonneg (le_of_lt hR_pos) (Nat.cast_nonneg _)
  have hBi : ((B i).card : ℝ) = (w_nat : ℝ) := by exact_mod_cast hw i hiR
  calc ((neighborFinsetIn G z (blockUnion B R)).card : ℝ)
    _ ≤ (w_nat : ℝ) + (R.card : ℝ) * (x * (w_nat : ℝ)) := by linarith
    _ = (1 / (R.card : ℝ) + x) * ((R.card : ℝ) * (w_nat : ℝ)) := by
        field_simp [hR_ne_zero]
    _ ≤ ε * ((R.card : ℝ) * (w_nat : ℝ)) := mul_le_mul_of_nonneg_right hε hU_nonneg
    _ = ε * ((blockUnion B R).card : ℝ) := by rw [hU_card]

/--
**Proposition 3.2(4) (`prop:wonderful`, Full Synthesis — Wonderfulness of $\{P_6\}$)**:
Let $G$ be a $\overline{P_6}$-free graph, and let $B : \text{Fin } \ell \to \text{Finset } V$ be a
complete-or-$y^a$-sparse $(\ell, w_{\text{nat}})$-blockade inside $S \subseteq V$ with $\ell \ge 1$,
equal block sizes $|B_i| = w_{\text{nat}} \ge 1$, $y > 0$, and $6 y^a \le 1/2$.
Suppose that for any external vertex $v \in S \setminus \bigcup_j B_j$ with $|I(v)| \ge y \ell$,
the `witnessH`-free pattern graph induced on $I(v)$ contains a nonempty subset $R \subseteq I(v)$
with $\frac{1}{|R|} + y^a \le y^4$ that is either a clique or an independent set in
`blockadePatternGraph G B`.
Then either:
- **(W1)** There exists a subset $U \subseteq S$ of cardinality $|U| \ge w_{\text{nat}}$ such that
  $G[U]$ is $y^4$-restricted (`IsEpsRestrictedOn G U (y ^ 4)`); or
- **(W2)** There exists a block index $i^* \in [\ell]$ such that fewer than $y |S|$ external
  vertices $v \in S \setminus \bigcup_j B_j$ satisfy $0 < |N_G(v) \cap B_{i^*}| < \frac{1}{2}|B_{i^*}|$.
-/
theorem p6_is_wonderful
    {G : SimpleGraph V} {S : Finset V} {ℓ w_nat : ℕ} {y a : ℝ} {B : Fin ℓ → Finset V}
    (hG : IsInducedSubgraphFree G P6Compl)
    (hB : IsCompleteOrXSparseBlockadeIn G S ℓ (w_nat : ℝ) (y ^ a) B)
    (hℓ : 0 < ℓ) (_hw_pos : 0 < w_nat) (hw_eq : ∀ i : Fin ℓ, (B i).card = w_nat)
    (hy_pos : 0 < y) (hya_six : 6 * (y ^ a) ≤ 1 / 2)
    (hEH_witnessH : ∀ v ∈ blockadeExternalVerts S B,
      y * (ℓ : ℝ) ≤ ((openAttachmentIndices G B v).card : ℝ) →
      IsInducedSubgraphFree
        ((blockadePatternGraph G B).induce (openAttachmentIndices G B v : Set (Fin ℓ)))
        witnessH →
      ∃ R ⊆ openAttachmentIndices G B v, R.Nonempty ∧
        1 / (R.card : ℝ) + y ^ a ≤ y ^ 4 ∧
        ((∀ i ∈ R, ∀ j ∈ R, i ≠ j → (blockadePatternGraph G B).Adj i j) ∨
         (∀ i ∈ R, ∀ j ∈ R, i ≠ j → ¬(blockadePatternGraph G B).Adj i j))) :
    (∃ U ⊆ S, w_nat ≤ U.card ∧ IsEpsRestrictedOn G U (y ^ 4)) ∨
    (∃ i : Fin ℓ, ((openAttachmentExternalVerts G S B i).card : ℝ) < y * (S.card : ℝ)) := by
  by_cases hAllSmall : ∀ v ∈ blockadeExternalVerts S B,
      ((openAttachmentIndices G B v).card : ℝ) < y * (ℓ : ℝ)
  · right
    have hS_ne : S.Nonempty := by
      obtain ⟨u, hu⟩ := hB.1.nonempty_blocks ⟨0, hℓ⟩
      exact ⟨u, hB.1.subset_ambient ⟨0, hℓ⟩ hu⟩
    exact exists_block_few_openAttachmentExternalVerts G S B hℓ hy_pos hS_ne hAllSmall
  · left
    push_neg at hAllSmall
    rcases hAllSmall with ⟨v, hv_ext_mem, hv_large⟩
    have hv_ext : ∀ i : Fin ℓ, v ∉ B i := (mem_blockadeExternalVerts S B v).mp hv_ext_mem |>.2
    have hFree := isInducedSubgraphFree_patternGraph_induce_openAttachment hG hB hya_six v hv_ext
    obtain ⟨R, _, hR_ne, hR_bound, hCliqueOrIndep⟩ := hEH_witnessH v hv_ext_mem hv_large hFree
    have hya_nonneg : 0 ≤ y ^ a := Real.rpow_nonneg (le_of_lt hy_pos) a
    refine ⟨blockUnion B R, blockUnion_subset_of_blockade hB.1 R,
      width_le_card_blockUnion B hB.1.pairwise_disjoint R hR_ne w_nat (fun i _ => hw_eq i), ?_⟩
    rcases hCliqueOrIndep with hClique | hIndep
    · right
      have hε_clique : 1 / (R.card : ℝ) ≤ y ^ 4 := by linarith
      exact isEpsSparseOn_compl_blockUnion_of_pattern_clique hB.1.pairwise_disjoint R hR_ne
        w_nat (fun i _ => hw_eq i) hClique hε_clique
    · left
      exact isEpsSparseOn_blockUnion_of_pattern_indep hB hya_nonneg R hR_ne
        w_nat (fun i _ => hw_eq i) hIndep hR_bound

/-! ### Proposition 3.2(1): Modular Substitution Structure of `witnessH` from $\overline{P_5}$ -/

/--
The intermediate 6-vertex graph `witnessH6 : SimpleGraph (Fin 6)` on `0..5 : Fin 7`
(1-indexed `{1, 2, 3, 4, 5, 6}`), obtained from $\overline{P_5}$ (`P5Compl`) by substituting
the 2-vertex stable module `{2, 4}` (1-indexed `{3, 5}`) for the last vertex of `P5Compl`.
-/
def witnessH6 : SimpleGraph (Fin 6) :=
  witnessH.comap Fin.castSuccEmb

instance instDecidableRelWitnessH6Adj : DecidableRel witnessH6.Adj :=
  fun a b => inferInstanceAs (Decidable (witnessH.Adj a.castSucc b.castSucc))

/--
Second projection `pi6_right : Fin 6 ↪ Fin 7` (`![0, 6, 2, 3, 4, 5]`) replacing vertex `1`
(1-indexed `2`) by its clique twin `6` (1-indexed `7`).
-/
def pi6_right : Fin 6 ↪ Fin 7 where
  toFun := ![0, 6, 2, 3, 4, 5]
  inj' := by
    intro u v
    fin_cases u <;> fin_cases v <;> decide

theorem witnessH_comap_castSuccEmb : witnessH.comap Fin.castSuccEmb = witnessH6 :=
  rfl

theorem witnessH_comap_pi6_right : witnessH.comap pi6_right = witnessH6 := by
  ext u v
  fin_cases u <;> fin_cases v <;> decide

/--
First projection `pi5_left : Fin 5 ↪ Fin 6` (`![0, 3, 5, 1, 2]`) embedding $\overline{P_5}$
(`P5Compl`) into `witnessH6` using vertex `2` (1-indexed `3`) from the stable module `{2, 4}`.
-/
def pi5_left : Fin 5 ↪ Fin 6 where
  toFun := ![0, 3, 5, 1, 2]
  inj' := by
    intro u v
    fin_cases u <;> fin_cases v <;> decide

/--
Second projection `pi5_right : Fin 5 ↪ Fin 6` (`![0, 3, 5, 1, 4]`) embedding $\overline{P_5}$
(`P5Compl`) into `witnessH6` using vertex `4` (1-indexed `5`) from the stable module `{2, 4}`.
-/
def pi5_right : Fin 5 ↪ Fin 6 where
  toFun := ![0, 3, 5, 1, 4]
  inj' := by
    intro u v
    fin_cases u <;> fin_cases v <;> decide

theorem witnessH6_comap_pi5_left : witnessH6.comap pi5_left = P5Compl := by
  ext u v
  fin_cases u <;> fin_cases v <;> decide

theorem witnessH6_comap_pi5_right : witnessH6.comap pi5_right = P5Compl := by
  ext u v
  fin_cases u <;> fin_cases v <;> decide

/--
In `witnessH`, `{2, 4}` (1-indexed `{3, 5}`) is a 2-vertex stable twin module
(Proposition 3.2(1) of `FMBV4-016_readable.tex`).
-/
theorem witnessH_stable_twin_2_4 :
    ¬witnessH.Adj 2 4 ∧
    ∀ u : Fin 7, u ≠ 2 → u ≠ 4 → (witnessH.Adj u 2 ↔ witnessH.Adj u 4) := by
  refine ⟨by decide, ?_⟩
  intro u
  fin_cases u <;> decide

/--
In `witnessH`, `{2, 4}` (1-indexed `{3, 5}`) is a proper module of `witnessH`.
-/
theorem witnessH_isProperModuleIn_2_4 :
    IsProperModuleIn witnessH Finset.univ ({2, 4} : Finset (Fin 7)) := by
  refine ⟨⟨2, by decide⟩, ?_, ⟨ Finset.subset_univ _, ?_⟩⟩
  · rw [Finset.ssubset_iff_of_subset (Finset.subset_univ _)]
    exact ⟨0, Finset.mem_univ 0, by decide⟩
  · intro z _ hz
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
    have htwin := witnessH_stable_twin_2_4.2 z hz.1 hz.2
    by_cases h2 : witnessH.Adj z 2
    · left
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact h2
      · exact htwin.mp h2
    · right
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact h2
      · exact fun h4 => h2 (htwin.mpr h4)

/--
In `witnessH`, `{1, 6}` (1-indexed `{2, 7}`) is a 2-vertex clique twin module
(Proposition 3.2(1) of `FMBV4-016_readable.tex`).
-/
theorem witnessH_clique_twin_1_6 :
    witnessH.Adj 1 6 ∧
    ∀ u : Fin 7, u ≠ 1 → u ≠ 6 → (witnessH.Adj u 1 ↔ witnessH.Adj u 6) := by
  refine ⟨by decide, ?_⟩
  intro u
  fin_cases u <;> decide

/--
In `witnessH`, `{1, 6}` (1-indexed `{2, 7}`) is a proper module of `witnessH`.
-/
theorem witnessH_isProperModuleIn_1_6 :
    IsProperModuleIn witnessH Finset.univ ({1, 6} : Finset (Fin 7)) := by
  refine ⟨⟨1, by decide⟩, ?_, ⟨Finset.subset_univ _, ?_⟩⟩
  · rw [Finset.ssubset_iff_of_subset (Finset.subset_univ _)]
    exact ⟨0, Finset.mem_univ 0, by decide⟩
  · intro z _ hz
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
    have htwin := witnessH_clique_twin_1_6.2 z hz.1 hz.2
    by_cases h1 : witnessH.Adj z 1
    · left
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact h1
      · exact htwin.mp h1
    · right
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact h1
      · exact fun h6 => h1 (htwin.mpr h6)

/-! ### Twin-Substitution Lifting Lemmas from `P5Compl` to `witnessH6` to `witnessH` -/

theorem fin6_eq_pi5_left_or_four (a : Fin 6) :
    (∃ i : Fin 5, a = pi5_left i) ∨ a = 4 := by
  fin_cases a
  · exact Or.inl ⟨0, rfl⟩
  · exact Or.inl ⟨3, rfl⟩
  · exact Or.inl ⟨4, rfl⟩
  · exact Or.inl ⟨1, rfl⟩
  · exact Or.inr rfl
  · exact Or.inl ⟨2, rfl⟩

theorem pi5_left_ne_four (i : Fin 5) : pi5_left i ≠ 4 := by
  fin_cases i <;> decide

theorem witnessH6_adj_pi5_left_four (i : Fin 5) :
    witnessH6.Adj (pi5_left i) 4 ↔ i ≠ 4 ∧ P5Compl.Adj i 4 := by
  fin_cases i <;> decide

/--
**First Substitution Lifting Lemma (`P5Compl` $\to$ `witnessH6`)**:
If `g : Fin 5 ↪ V` embeds `P5Compl` as an induced subgraph of `G`, and `w : V` is an external
non-adjacent twin of `g 4` on `g '' {0, 1, 2, 3}`, then `G` contains an induced `witnessH6`.
-/
theorem not_isWitnessH6Free_of_P5Compl_twin {G : SimpleGraph V}
    (g : Fin 5 ↪ V) (hg : P5Compl = G.comap g)
    (w : V) (hw_disj : ∀ i : Fin 5, w ≠ g i)
    (hw_nonadj : ¬G.Adj (g 4) w)
    (hw_twin : ∀ i : Fin 5, i ≠ 4 → (G.Adj (g i) w ↔ G.Adj (g i) (g 4))) :
    ¬IsInducedSubgraphFree G witnessH6 := by
  let f_fun : Fin 6 → V := ![g 0, g 3, g 4, g 1, w, g 2]
  have hf_pi : ∀ i : Fin 5, f_fun (pi5_left i) = g i := by
    intro i
    fin_cases i <;> rfl
  have hf_four : f_fun 4 = w := rfl
  let f : Fin 6 ↪ V :=
    { toFun := f_fun
      inj' := by
        intro a b hab
        rcases fin6_eq_pi5_left_or_four a with ⟨i, rfl⟩ | rfl <;>
          rcases fin6_eq_pi5_left_or_four b with ⟨j, rfl⟩ | rfl
        · rw [hf_pi, hf_pi] at hab
          exact congr_arg pi5_left (g.injective hab)
        · rw [hf_pi, hf_four] at hab
          exact False.elim (hw_disj i hab.symm)
        · rw [hf_four, hf_pi] at hab
          exact False.elim (hw_disj j hab)
        · rfl }
  have hf_eq : witnessH6 = G.comap f := by
    ext a b
    rcases fin6_eq_pi5_left_or_four a with ⟨i, rfl⟩ | rfl <;>
      rcases fin6_eq_pi5_left_or_four b with ⟨j, rfl⟩ | rfl
    · have h1 := congr_arg (fun H => H.Adj i j) witnessH6_comap_pi5_left
      have h2 := congr_arg (fun H => H.Adj i j) hg
      change witnessH6.Adj (pi5_left i) (pi5_left j) ↔ G.Adj (f_fun (pi5_left i)) (f_fun (pi5_left j))
      rw [hf_pi, hf_pi]
      exact (h1.trans h2).to_iff
    · change witnessH6.Adj (pi5_left i) 4 ↔ G.Adj (f_fun (pi5_left i)) (f_fun 4)
      rw [hf_pi, hf_four, witnessH6_adj_pi5_left_four]
      by_cases hi4 : i = 4
      · subst hi4
        exact iff_of_false (fun h => h.1 rfl) hw_nonadj
      · have h2 := (congr_arg (fun H => H.Adj i 4) hg).to_iff
        rw [comap_adj] at h2
        exact ⟨fun h => (hw_twin i hi4).mpr (h2.mp h.2),
          fun h => ⟨hi4, h2.mpr ((hw_twin i hi4).mp h)⟩⟩
    · change witnessH6.Adj 4 (pi5_left j) ↔ G.Adj (f_fun 4) (f_fun (pi5_left j))
      rw [hf_pi, hf_four, witnessH6.adj_comm, G.adj_comm, witnessH6_adj_pi5_left_four]
      by_cases hj4 : j = 4
      · subst hj4
        exact iff_of_false (fun h => h.1 rfl) hw_nonadj
      · have h2 := (congr_arg (fun H => H.Adj j 4) hg).to_iff
        rw [comap_adj] at h2
        exact ⟨fun h => (hw_twin j hj4).mpr (h2.mp h.2),
          fun h => ⟨hj4, h2.mpr ((hw_twin j hj4).mp h)⟩⟩
    · simp
  intro hFree
  exact hFree ⟨f, hf_eq⟩

theorem fin7_eq_castSucc_or_six (a : Fin 7) :
    (∃ i : Fin 6, a = i.castSucc) ∨ a = 6 := by
  fin_cases a
  · exact Or.inl ⟨0, rfl⟩
  · exact Or.inl ⟨1, rfl⟩
  · exact Or.inl ⟨2, rfl⟩
  · exact Or.inl ⟨3, rfl⟩
  · exact Or.inl ⟨4, rfl⟩
  · exact Or.inl ⟨5, rfl⟩
  · exact Or.inr rfl

theorem witnessH_adj_castSucc_six (i : Fin 6) :
    witnessH.Adj i.castSucc 6 ↔ i = 1 ∨ (i ≠ 1 ∧ witnessH6.Adj i 1) := by
  fin_cases i <;> decide

/--
**Second Substitution Lifting Lemma (`witnessH6` $\to$ `witnessH`)**:
If `g : Fin 6 ↪ V` embeds `witnessH6` as an induced subgraph of `G`, and `w : V` is an external
adjacent twin of `g 1` on `g '' ({0..5} \ {1})`, then `G` contains an induced `witnessH`.
-/
theorem not_isWitnessHFree_of_witnessH6_twin {G : SimpleGraph V}
    (g : Fin 6 ↪ V) (hg : witnessH6 = G.comap g)
    (w : V) (hw_disj : ∀ i : Fin 6, w ≠ g i)
    (hw_adj : G.Adj (g 1) w)
    (hw_twin : ∀ i : Fin 6, i ≠ 1 → (G.Adj (g i) w ↔ G.Adj (g i) (g 1))) :
    ¬IsInducedSubgraphFree G witnessH := by
  let f_fun : Fin 7 → V := ![g 0, g 1, g 2, g 3, g 4, g 5, w]
  have hf_cast : ∀ i : Fin 6, f_fun i.castSucc = g i := by
    intro i
    fin_cases i <;> rfl
  have hf_six : f_fun 6 = w := rfl
  let f : Fin 7 ↪ V :=
    { toFun := f_fun
      inj' := by
        intro a b hab
        rcases fin7_eq_castSucc_or_six a with ⟨i, rfl⟩ | rfl <;>
          rcases fin7_eq_castSucc_or_six b with ⟨j, rfl⟩ | rfl
        · rw [hf_cast, hf_cast] at hab
          exact congr_arg Fin.castSucc (g.injective hab)
        · rw [hf_cast, hf_six] at hab
          exact False.elim (hw_disj i hab.symm)
        · rw [hf_six, hf_cast] at hab
          exact False.elim (hw_disj j hab)
        · rfl }
  have hf_eq : witnessH = G.comap f := by
    ext a b
    rcases fin7_eq_castSucc_or_six a with ⟨i, rfl⟩ | rfl <;>
      rcases fin7_eq_castSucc_or_six b with ⟨j, rfl⟩ | rfl
    · have h2 := (congr_arg (fun H => H.Adj i j) hg).to_iff
      change witnessH6.Adj i j ↔ G.Adj (f_fun i.castSucc) (f_fun j.castSucc)
      rw [hf_cast, hf_cast]
      exact h2
    · change witnessH.Adj i.castSucc 6 ↔ G.Adj (f_fun i.castSucc) (f_fun 6)
      rw [hf_cast, hf_six, witnessH_adj_castSucc_six]
      by_cases hi1 : i = 1
      · subst hi1
        exact iff_of_true (Or.inl rfl) hw_adj
      · have h2 := (congr_arg (fun H => H.Adj i 1) hg).to_iff
        rw [comap_adj] at h2
        exact ⟨fun h => (hw_twin i hi1).mpr (h2.mp (h.resolve_left hi1).2),
          fun h => Or.inr ⟨hi1, h2.mpr ((hw_twin i hi1).mp h)⟩⟩
    · change witnessH.Adj 6 j.castSucc ↔ G.Adj (f_fun 6) (f_fun j.castSucc)
      rw [hf_cast, hf_six, witnessH.adj_comm, G.adj_comm, witnessH_adj_castSucc_six]
      by_cases hj1 : j = 1
      · subst hj1
        exact iff_of_true (Or.inl rfl) hw_adj
      · have h2 := (congr_arg (fun H => H.Adj j 1) hg).to_iff
        rw [comap_adj] at h2
        exact ⟨fun h => (hw_twin j hj1).mpr (h2.mp (h.resolve_left hj1).2),
          fun h => Or.inr ⟨hj1, h2.mpr ((hw_twin j hj1).mp h)⟩⟩
    · simp
  intro hFree
  exact hFree ⟨f, hf_eq⟩

/-! ### Erdős–Hajnal Property of `witnessH` Implies `hEH_witnessH` and `p6_is_wonderful` -/

/--
**Bridging Erdős–Hajnal for `witnessH` to `p6_is_wonderful` (`exists_clique_or_indep_of_erdos_hajnal`)**:
If every `witnessH`-free induced subgraph of `blockadePatternGraph G B` on a nonempty vertex subset
$I \subseteq [\ell]$ contains a clique or independent set $R \subseteq I$ of size $|R| \ge |I|^{c_H}$
($c_H > 0$), then whenever $2 / y^4 \le (y \ell)^{c_H}$ and $y^a \le y^4 / 2$, any external vertex
$v$ with $|I(v)| \ge y \ell$ yields a nonempty clique or independent set $R \subseteq I(v)$
satisfying $\frac{1}{|R|} + y^a \le y^4$.
-/
theorem exists_clique_or_indep_of_erdos_hajnal
    {G : SimpleGraph V} {S : Finset V} {ℓ : ℕ} {y a c_H : ℝ} {B : Fin ℓ → Finset V}
    (hcH_pos : 0 < c_H) (hℓ_pos : 0 < ℓ) (hy_pos : 0 < y)
    (h_rpow_ge : 2 / (y ^ 4) ≤ (y * (ℓ : ℝ)) ^ c_H)
    (hya_le : y ^ a ≤ (y ^ 4) / 2)
    (hEH : ∀ I : Finset (Fin ℓ), I.Nonempty →
      IsInducedSubgraphFree ((blockadePatternGraph G B).induce (I : Set (Fin ℓ))) witnessH →
      ∃ R ⊆ I, (I.card : ℝ) ^ c_H ≤ (R.card : ℝ) ∧
        ((∀ i ∈ R, ∀ j ∈ R, i ≠ j → (blockadePatternGraph G B).Adj i j) ∨
         (∀ i ∈ R, ∀ j ∈ R, i ≠ j → ¬(blockadePatternGraph G B).Adj i j))) :
    ∀ v ∈ blockadeExternalVerts S B,
      y * (ℓ : ℝ) ≤ ((openAttachmentIndices G B v).card : ℝ) →
      IsInducedSubgraphFree
        ((blockadePatternGraph G B).induce (openAttachmentIndices G B v : Set (Fin ℓ)))
        witnessH →
      ∃ R ⊆ openAttachmentIndices G B v, R.Nonempty ∧
        1 / (R.card : ℝ) + y ^ a ≤ y ^ 4 ∧
        ((∀ i ∈ R, ∀ j ∈ R, i ≠ j → (blockadePatternGraph G B).Adj i j) ∨
         (∀ i ∈ R, ∀ j ∈ R, i ≠ j → ¬(blockadePatternGraph G B).Adj i j)) := by
  intro v _ hv_large hFree
  have hℓ_real_pos : (0 : ℝ) < (ℓ : ℝ) := Nat.cast_pos.mpr hℓ_pos
  have hyℓ_pos : 0 < y * (ℓ : ℝ) := mul_pos hy_pos hℓ_real_pos
  have hI_pos : 0 < (openAttachmentIndices G B v).card := by
    have : (0 : ℝ) < ((openAttachmentIndices G B v).card : ℝ) := lt_of_lt_of_le hyℓ_pos hv_large
    exact Nat.cast_pos.mp this
  have hI_ne : (openAttachmentIndices G B v).Nonempty := Finset.card_pos.mp hI_pos
  obtain ⟨R, hR_sub, hR_card, hCliqueOrIndep⟩ := hEH (openAttachmentIndices G B v) hI_ne hFree
  have h_rpow_mono : (y * (ℓ : ℝ)) ^ c_H ≤ ((openAttachmentIndices G B v).card : ℝ) ^ c_H :=
    Real.rpow_le_rpow (le_of_lt hyℓ_pos) hv_large (le_of_lt hcH_pos)
  have hR_ge : 2 / (y ^ 4) ≤ (R.card : ℝ) := le_trans h_rpow_ge (le_trans h_rpow_mono hR_card)
  have hy4_pos : 0 < y ^ 4 := by positivity
  have hR_real_pos : 0 < (R.card : ℝ) := lt_of_lt_of_le (div_pos zero_lt_two hy4_pos) hR_ge
  have hR_ne : R.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hR_real_pos)
  have h1R : 1 / (R.card : ℝ) ≤ (y ^ 4) / 2 := by
    rw [div_le_div_iff₀ hR_real_pos zero_lt_two]
    have h2 : 2 ≤ (R.card : ℝ) * (y ^ 4) := (div_le_iff₀ hy4_pos).mp hR_ge
    linarith
  refine ⟨R, hR_sub, hR_ne, by linarith, hCliqueOrIndep⟩

/--
**Exponent Calibration Inequality for Proposition 3.2(4) (`FMBV4-016_readable.tex`)**:
For $c_H > 0$, $a \ge 7$, $a \ge 5 / c_H + 1$, $y \in (0, 1/2]$, and $\ell \ge y^{-a}$, we have:
1. $6 y^a \le 1/2$,
2. $y^a \le y^4 / 2$, and
3. $2 / y^4 \le (y \ell)^{c_H}$.
-/
theorem wonderful_exponent_bounds {y a c_H : ℝ} {ℓ : ℕ}
    (hcH_pos : 0 < c_H) (ha7 : 7 ≤ a) (ha_cH : 5 / c_H + 1 ≤ a)
    (hy_pos : 0 < y) (hy_le : y ≤ 1 / 2)
    (hℓ_ge : y ^ (-a) ≤ (ℓ : ℝ)) :
    6 * (y ^ a) ≤ 1 / 2 ∧ y ^ a ≤ (y ^ 4) / 2 ∧ 2 / (y ^ 4) ≤ (y * (ℓ : ℝ)) ^ c_H := by
  have hy_le_one : y ≤ 1 := by linarith
  have hy_nonneg : 0 ≤ y := le_of_lt hy_pos
  have hya_le_y7 : y ^ a ≤ y ^ (7 : ℕ) := by
    rw [← Real.rpow_natCast y 7]
    exact Real.rpow_le_rpow_of_exponent_ge hy_pos hy_le_one (by norm_num; linarith)
  have hy7_le : y ^ (7 : ℕ) ≤ (1 / 2 : ℝ) ^ (7 : ℕ) :=
    pow_le_pow_left₀ hy_nonneg hy_le 7
  have h1 : 6 * (y ^ a) ≤ 1 / 2 := by
    have : (1 / 2 : ℝ) ^ (7 : ℕ) = 1 / 128 := by norm_num
    linarith
  have hya_le_y5 : y ^ a ≤ y ^ (5 : ℕ) := by
    rw [← Real.rpow_natCast y 5]
    exact Real.rpow_le_rpow_of_exponent_ge hy_pos hy_le_one (by norm_num; linarith)
  have hy5_eq : y ^ (5 : ℕ) = y * (y ^ 4) := by ring
  have hy4_pos : 0 < y ^ 4 := by positivity
  have h2 : y ^ a ≤ (y ^ 4) / 2 := by
    have : y * (y ^ 4) ≤ (1 / 2) * (y ^ 4) :=
      mul_le_mul_of_nonneg_right hy_le (le_of_lt hy4_pos)
    linarith
  have hy1a : y ^ (1 - a) ≤ y * (ℓ : ℝ) := by
    have hmul : y * y ^ (-a) ≤ y * (ℓ : ℝ) :=
      mul_le_mul_of_nonneg_left hℓ_ge hy_nonneg
    have hadd : y ^ (1 - a) = y * y ^ (-a) := by
      rw [show (1 - a : ℝ) = 1 + (-a) by ring, Real.rpow_add hy_pos, Real.rpow_one]
    linarith
  have hy1a_pos : 0 < y ^ (1 - a) := Real.rpow_pos_of_pos hy_pos (1 - a)
  have h_rpow1 : (y ^ (1 - a)) ^ c_H ≤ (y * (ℓ : ℝ)) ^ c_H :=
    Real.rpow_le_rpow (le_of_lt hy1a_pos) hy1a (le_of_lt hcH_pos)
  have h_rpow_mul : (y ^ (1 - a)) ^ c_H = y ^ ((1 - a) * c_H) :=
    (Real.rpow_mul hy_nonneg (1 - a) c_H).symm
  have h_exp_le : (1 - a) * c_H ≤ -((5 : ℕ) : ℝ) := by
    have hdiv : 5 / c_H ≤ a - 1 := by linarith
    have hmul : 5 ≤ (a - 1) * c_H := (div_le_iff₀ hcH_pos).mp hdiv
    norm_num
    linarith
  have h_rpow2 : (y ^ (5 : ℕ))⁻¹ ≤ y ^ ((1 - a) * c_H) := by
    rw [← Real.rpow_natCast y 5, ← Real.rpow_neg hy_nonneg]
    exact Real.rpow_le_rpow_of_exponent_ge hy_pos hy_le_one h_exp_le
  have hy_neg5 : 2 / (y ^ 4) ≤ (y ^ (5 : ℕ))⁻¹ := by
    rw [hy5_eq]
    have hy5_pos : 0 < y * (y ^ 4) := mul_pos hy_pos hy4_pos
    rw [← one_div, div_le_div_iff₀ hy4_pos hy5_pos]
    have : 2 * (y * (y ^ 4)) ≤ 1 * (y ^ 4) := by
      calc 2 * (y * (y ^ 4))
        _ = (2 * y) * (y ^ 4) := by ring
        _ ≤ 1 * (y ^ 4) := mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hy4_pos)
    linarith
  refine ⟨h1, h2, ?_⟩
  linarith

/--
**Proposition 3.2(4) (`p6_is_wonderful_of_witnessH_eh`)**:
Direct synthesis of `p6_is_wonderful`, `exists_clique_or_indep_of_erdos_hajnal`, and
`wonderful_exponent_bounds`: assuming `witnessH` satisfies the Erdős–Hajnal property with
exponent $c_H > 0$, $\{P_6\}$ is wonderful with parameter $a \ge \max(7, 5 / c_H + 1)$.
-/
theorem p6_is_wonderful_of_witnessH_eh
    {G : SimpleGraph V} {S : Finset V} {ℓ w_nat : ℕ} {y a c_H : ℝ} {B : Fin ℓ → Finset V}
    (hG : IsInducedSubgraphFree G P6Compl)
    (hB : IsCompleteOrXSparseBlockadeIn G S ℓ (w_nat : ℝ) (y ^ a) B)
    (hw_pos : 0 < w_nat) (hw_eq : ∀ i : Fin ℓ, (B i).card = w_nat)
    (hcH_pos : 0 < c_H) (ha7 : 7 ≤ a) (ha_cH : 5 / c_H + 1 ≤ a)
    (hy_pos : 0 < y) (hy_le : y ≤ 1 / 2)
    (hℓ_ge : y ^ (-a) ≤ (ℓ : ℝ))
    (hEH : ∀ I : Finset (Fin ℓ), I.Nonempty →
      IsInducedSubgraphFree ((blockadePatternGraph G B).induce (I : Set (Fin ℓ))) witnessH →
      ∃ R ⊆ I, (I.card : ℝ) ^ c_H ≤ (R.card : ℝ) ∧
        ((∀ i ∈ R, ∀ j ∈ R, i ≠ j → (blockadePatternGraph G B).Adj i j) ∨
         (∀ i ∈ R, ∀ j ∈ R, i ≠ j → ¬(blockadePatternGraph G B).Adj i j))) :
    (∃ U ⊆ S, w_nat ≤ U.card ∧ IsEpsRestrictedOn G U (y ^ 4)) ∨
    (∃ i : Fin ℓ, ((openAttachmentExternalVerts G S B i).card : ℝ) < y * (S.card : ℝ)) := by
  have hℓ_pos : 0 < ℓ := by
    have : (0 : ℝ) < (ℓ : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hy_pos (-a)) hℓ_ge
    exact Nat.cast_pos.mp this
  obtain ⟨hya_six, hya_le, h_rpow_ge⟩ :=
    wonderful_exponent_bounds hcH_pos ha7 ha_cH hy_pos hy_le hℓ_ge
  exact p6_is_wonderful hG hB hℓ_pos hw_pos hw_eq hy_pos hya_six
    (exists_clique_or_indep_of_erdos_hajnal hcH_pos hℓ_pos hy_pos h_rpow_ge hya_le hEH)

/-! ### $P_5$ Leaf-Reduction to $P_4$ and Seinsche's Theorem ($P_4$-Free Erdős–Hajnal) -/

/-- The 4-vertex path $P_4$ (`SimpleGraph.pathGraph 4`). -/
abbrev P4 : SimpleGraph (Fin 4) := pathGraph 4

/-- The complement of $P_4$, $\overline{P_4}$. -/
abbrev P4Compl : SimpleGraph (Fin 4) := (pathGraph 4)ᶜ

instance instDecidableRelP4Adj : DecidableRel P4.Adj :=
  instDecidableRelPathGraphAdj 4

instance instDecidableRelP4ComplAdj : DecidableRel P4Compl.Adj :=
  inferInstanceAs (DecidableRel (pathGraph 4)ᶜ.Adj)

/--
Deleting the last vertex `4 : Fin 5` of $P_5$ (`Fin.castSuccEmb : Fin 4 ↪ Fin 5`) yields $P_4$.
-/
theorem P5_comap_castSuccEmb : P5.comap Fin.castSuccEmb = P4 := by
  ext u v
  simp [P5, P4, pathGraph_adj]

/--
Deleting the last vertex `4 : Fin 5` of $\overline{P_5}$ yields $\overline{P_4}$.
-/
theorem P5Compl_comap_castSuccEmb : P5Compl.comap Fin.castSuccEmb = P4Compl := by
  rw [← comap_compl, P5_comap_castSuccEmb]

/--
In $P_5$, the last vertex `4 : Fin 5` has unique neighbor `3 : Fin 5`.
-/
theorem P5_last_unique_neighbor : ∀ u : Fin 5, P5.Adj 4 u ↔ u = 3 := by
  intro u
  fin_cases u <;> decide

/--
Self-complementarity embedding `![1, 3, 0, 2]` of $P_4$ into $\overline{P_4}$:
in $P_4 = 0 - 1 - 2 - 3$, the non-edges form the path $1 - 3 - 0 - 2$.
-/
def gP4SelfCompl : Fin 4 ↪ Fin 4 where
  toFun := ![1, 3, 0, 2]
  inj' := by
    intro u v
    fin_cases u <;> fin_cases v <;> decide

theorem P4Compl_comap_gP4SelfCompl : P4 = P4Compl.comap gP4SelfCompl := by
  ext u v
  fin_cases u <;> fin_cases v <;> decide

/--
Because $P_4$ is self-complementary, if $G$ is $P_4$-free then $Gᶜ$ is also $P_4$-free.
-/
theorem isP4Free_compl_of_isP4Free {G : SimpleGraph V} (hG : IsInducedSubgraphFree G P4) :
    IsInducedSubgraphFree Gᶜ P4 := by
  rintro ⟨f, hf⟩
  have h1 : P4Compl = G.comap f := by
    ext a b
    have h : P4.Adj a b ↔ f a ≠ f b ∧ ¬G.Adj (f a) (f b) := by
      simpa [comap_adj, compl_adj] using (congr_arg (fun H => H.Adj a b) hf).to_iff
    simp only [P4Compl, compl_adj, comap_adj]
    constructor
    · rintro ⟨hne, hnP4⟩
      by_contra hnG
      exact hnP4 (h.mpr ⟨f.injective.ne hne, hnG⟩)
    · intro hG
      exact ⟨fun hab => G.loopless (f a) (hab ▸ hG), fun hP4 => (h.mp hP4).2 hG⟩
  refine hG ⟨gP4SelfCompl.trans f, ?_⟩
  ext a b
  have ha := congr_arg (fun H => H.Adj a b) P4Compl_comap_gP4SelfCompl
  have hb := congr_arg (fun H => H.Adj (gP4SelfCompl a) (gP4SelfCompl b)) h1
  exact (ha.trans hb).to_iff

theorem fin4_pair_cases (i j : Fin 4) :
    i = j ∨
    (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
    (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
    (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨
    (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨
    (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) ∨
    (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) := by
  fin_cases i <;> fin_cases j <;> decide

/--
If four vertices $v_0, v_1, v_2, v_3 \in V$ have edges $v_0 v_1, v_1 v_2, v_2 v_3 \in E(G)$
and non-edges $v_0 v_2, v_0 v_3, v_1 v_3 \notin E(G)$, then $G$ contains an induced $P_4$.
-/
theorem not_isP4Free_of_path4 {G : SimpleGraph V} {v0 v1 v2 v3 : V}
    (h01 : G.Adj v0 v1) (h12 : G.Adj v1 v2) (h23 : G.Adj v2 v3)
    (h02 : ¬G.Adj v0 v2) (h03 : ¬G.Adj v0 v3) (h13 : ¬G.Adj v1 v3) :
    ¬IsInducedSubgraphFree G P4 := by
  let f_fun : Fin 4 → V := ![v0, v1, v2, v3]
  have hf_adj : ∀ i j : Fin 4, P4.Adj i j ↔ G.Adj (f_fun i) (f_fun j) := by
    intro i j
    rcases fin4_pair_cases i j with
      rfl |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact iff_of_false (P4.loopless i) (G.loopless _)
    · exact iff_of_true (by decide) h01
    · exact iff_of_true (by decide) (G.symm h01)
    · exact iff_of_true (by decide) h12
    · exact iff_of_true (by decide) (G.symm h12)
    · exact iff_of_true (by decide) h23
    · exact iff_of_true (by decide) (G.symm h23)
    · exact iff_of_false (by decide) h02
    · exact iff_of_false (by decide) (fun h => h02 (G.symm h))
    · exact iff_of_false (by decide) h03
    · exact iff_of_false (by decide) (fun h => h03 (G.symm h))
    · exact iff_of_false (by decide) h13
    · exact iff_of_false (by decide) (fun h => h13 (G.symm h))
  let f : Fin 4 ↪ V :=
    { toFun := f_fun
      inj' := by
        intro i j hij
        rcases fin4_pair_cases i j with
          rfl |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · dsimp [f_fun] at hij; subst hij; exact False.elim (G.loopless _ h01)
        · dsimp [f_fun] at hij; subst hij; exact False.elim (G.loopless _ h01)
        · dsimp [f_fun] at hij; subst hij; exact False.elim (G.loopless _ h12)
        · dsimp [f_fun] at hij; subst hij; exact False.elim (G.loopless _ h12)
        · dsimp [f_fun] at hij; subst hij; exact False.elim (G.loopless _ h23)
        · dsimp [f_fun] at hij; subst hij; exact False.elim (G.loopless _ h23)
        · dsimp [f_fun] at hij; subst hij; exact False.elim (h03 h23)
        · dsimp [f_fun] at hij; subst hij; exact False.elim (h03 h23)
        · dsimp [f_fun] at hij; subst hij; exact False.elim (h13 (G.symm h01))
        · dsimp [f_fun] at hij; subst hij; exact False.elim (h13 (G.symm h01))
        · dsimp [f_fun] at hij; subst hij; exact False.elim (h03 h01)
        · dsimp [f_fun] at hij; subst hij; exact False.elim (h03 h01) }
  intro hFree
  refine hFree ⟨f, ?_⟩
  ext i j
  exact hf_adj i j

/--
Core inductive step of Seinsche's theorem: if $(A, B)$ is an anticomplete partition of $S'$,
$v \notin A \cup B$ has a neighbor in $A$, and $v$ is mixed on $B$ (has both a neighbor and a
non-neighbor in $B$), then in any $P_4$-free graph $G$, $(B \cap N_G(v), B \setminus N_G(v))$
must be anticomplete, giving an anticomplete partition of $\text{insert } v (A \cup B)$.
-/
theorem exists_anticomplete_partition_of_mixed {G : SimpleGraph V}
    (hG : IsInducedSubgraphFree G P4)
    {A B : Finset V} {v : V}
    (hAB_disj : Disjoint A B) (hvA : v ∉ A) (hvB : v ∉ B)
    (hAB_anti : IsAnticompletePair G A B)
    (ha : ∃ a ∈ A, G.Adj v a)
    (hb1 : ∃ b ∈ B, G.Adj v b)
    (hb2 : ∃ c ∈ B, ¬G.Adj v c) :
    letI := Classical.decEq V
    ∃ X Y : Finset V, X.Nonempty ∧ Y.Nonempty ∧ Disjoint X Y ∧
      X ∪ Y = insert v (A ∪ B) ∧ IsAnticompletePair G X Y := by
  classical
  let B1 := B.filter (fun u => G.Adj v u)
  let B2 := B.filter (fun u => ¬G.Adj v u)
  have hB12_anti : IsAnticompletePair G B1 B2 := by
    intro b hb c hc hbc
    rw [Finset.mem_filter] at hb hc
    rcases ha with ⟨a, haA, hva⟩
    exact not_isP4Free_of_path4 (G.symm hva) hb.2 hbc
      (hAB_anti a haA b hb.1) (hAB_anti a haA c hc.1) hc.2 hG
  rcases hb2 with ⟨c0, hc0B, hvc0⟩
  refine ⟨insert v (A ∪ B1), B2, ⟨v, Finset.mem_insert_self _ _⟩,
    ⟨c0, Finset.mem_filter.mpr ⟨hc0B, hvc0⟩⟩, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_insert_left]
    refine ⟨fun hvB2 => hvB (Finset.mem_filter.mp hvB2).1, ?_⟩
    rw [Finset.disjoint_union_left]
    refine ⟨Finset.disjoint_of_subset_right (Finset.filter_subset _ B) hAB_disj, ?_⟩
    exact Finset.disjoint_filter_filter_not B B (fun u => G.Adj v u)
  · rw [Finset.insert_union, Finset.union_assoc, Finset.filter_union_filter_not_eq]
  · intro x hx y hy
    have hy' := Finset.mem_filter.mp hy
    rw [Finset.mem_insert, Finset.mem_union] at hx
    rcases hx with rfl | hxA | hxB1
    · exact hy'.2
    · exact hAB_anti x hxA y hy'.1
    · exact hB12_anti x hxB1 y hy

/--
One-vertex extension step for Seinsche's theorem: adding a vertex $v$ to an anticomplete
partition $A \sqcup B$ in a $P_4$-free graph $G$ yields a pure partition of $\text{insert } v (A \cup B)$.
-/
theorem exists_pure_partition_insert_of_anticomplete {G : SimpleGraph V}
    (hG : IsInducedSubgraphFree G P4)
    {A B : Finset V} {v : V}
    (hA_ne : A.Nonempty) (hB_ne : B.Nonempty)
    (hAB_disj : Disjoint A B) (hvA : v ∉ A) (hvB : v ∉ B)
    (hAB_anti : IsAnticompletePair G A B) :
    letI := Classical.decEq V
    ∃ X Y : Finset V, X.Nonempty ∧ Y.Nonempty ∧ Disjoint X Y ∧
      X ∪ Y = insert v (A ∪ B) ∧ IsPurePair G X Y := by
  classical
  by_cases ha : ∃ a ∈ A, G.Adj v a
  · by_cases hb : ∃ b ∈ B, G.Adj v b
    · by_cases hb_non : ∃ c ∈ B, ¬G.Adj v c
      · obtain ⟨X, Y, hX, hY, hdisj, hunion, hanti⟩ :=
          exists_anticomplete_partition_of_mixed hG hAB_disj hvA hvB hAB_anti ha hb hb_non
        exact ⟨X, Y, hX, hY, hdisj, hunion, Or.inr hanti⟩
      · by_cases ha_non : ∃ c ∈ A, ¬G.Adj v c
        · have hBA_anti : IsAnticompletePair G B A :=
            fun b hbA a haA hba => hAB_anti a haA b hbA (G.symm hba)
          obtain ⟨X, Y, hX, hY, hdisj, hunion, hanti⟩ :=
            exists_anticomplete_partition_of_mixed hG hAB_disj.symm hvB hvA hBA_anti hb ha ha_non
          rw [Finset.union_comm B A] at hunion
          exact ⟨X, Y, hX, hY, hdisj, hunion, Or.inr hanti⟩
        · push_neg at hb_non ha_non
          refine ⟨{v}, A ∪ B, Finset.singleton_nonempty v, hA_ne.mono Finset.subset_union_left,
            Finset.disjoint_singleton_left.mpr (by simp [hvA, hvB]),
            Finset.singleton_union v (A ∪ B), Or.inl ?_⟩
          intro x hx y hy
          rw [Finset.mem_singleton] at hx
          subst hx
          rw [Finset.mem_union] at hy
          rcases hy with hyA | hyB
          · exact ha_non y hyA
          · exact hb_non y hyB
    · push_neg at hb
      refine ⟨insert v A, B, ⟨v, Finset.mem_insert_self _ _⟩, hB_ne,
        Finset.disjoint_insert_left.mpr ⟨hvB, hAB_disj⟩,
        Finset.insert_union v A B, Or.inr ?_⟩
      intro x hx y hy
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hxA
      · exact hb y hy
      · exact hAB_anti x hxA y hy
  · push_neg at ha
    refine ⟨A, insert v B, hA_ne, ⟨v, Finset.mem_insert_self _ _⟩,
      Finset.disjoint_insert_right.mpr ⟨hvA, hAB_disj⟩, ?_, Or.inr ?_⟩
    · rw [Finset.union_insert]
    · intro x hx y hy
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hyB
      · exact fun hxy => ha x hx (G.symm hxy)
      · exact hAB_anti x hx y hyB

theorem isAnticompletePair_compl_of_isCompletePair {G : SimpleGraph V} {A B : Finset V}
    (h : IsCompletePair G A B) : IsAnticompletePair Gᶜ A B := by
  intro x hx y hy hcompl
  exact hcompl.2 (h x hx y hy)

theorem isPurePair_of_compl {G : SimpleGraph V} {A B : Finset V}
    (hdisj : Disjoint A B) (h : IsPurePair Gᶜ A B) : IsPurePair G A B := by
  rcases h with hcomp | hanti
  · right
    intro x hx y hy hxy
    exact (hcomp x hx y hy).2 hxy
  · left
    intro x hx y hy
    have hne : x ≠ y := fun h => Finset.disjoint_left.mp hdisj hx (h ▸ hy)
    by_contra hnadj
    exact hanti x hx y hy ⟨hne, hnadj⟩

/--
**Seinsche's Theorem (Partition Form)**:
Every $P_4$-free graph $G$ on a finite vertex set $S \subseteq V$ of cardinality $|S| \ge 2$
admits a pure partition $S = X \sqcup Y$ ($X, Y \neq \emptyset$, $X \cap Y = \emptyset$, and
$(X, Y)$ is either complete or anticomplete in $G$).
-/
theorem seinsche_pure_partition {G : SimpleGraph V} (hG : IsInducedSubgraphFree G P4) :
    ∀ (n : ℕ) (S : Finset V), S.card = n → 2 ≤ n →
      letI := Classical.decEq V
      ∃ X Y : Finset V, X.Nonempty ∧ Y.Nonempty ∧ Disjoint X Y ∧
        X ∪ Y = S ∧ IsPurePair G X Y := by
  classical
  intro n
  refine Nat.strongRecOn n (fun n ih => ?_)
  intro S hScard hn2
  have hS_pos : 0 < S.card := by omega
  obtain ⟨v, hvS⟩ := Finset.card_pos.mp hS_pos
  by_cases hn_eq2 : n = 2
  · have herase_card : (S.erase v).card = 1 := by
      rw [Finset.card_erase_of_mem hvS, hScard, hn_eq2]
    obtain ⟨u, hu_eq⟩ := Finset.card_eq_one.mp herase_card
    have hvu : v ≠ u := by
      intro h
      have : v ∈ S.erase v := by rw [hu_eq, h]; exact Finset.mem_singleton_self u
      exact Finset.notMem_erase v S this
    refine ⟨{v}, {u}, Finset.singleton_nonempty v, Finset.singleton_nonempty u,
      Finset.disjoint_singleton.mpr hvu, ?_, ?_⟩
    · rw [← hu_eq, Finset.singleton_union, Finset.insert_erase hvS]
    · by_cases hadj : G.Adj v u
      · left
        intro x hx y hy
        rw [Finset.mem_singleton] at hx hy
        subst hx; subst hy; exact hadj
      · right
        intro x hx y hy
        rw [Finset.mem_singleton] at hx hy
        subst hx; subst hy; exact hadj
  · let S' := S.erase v
    have hS'_card : S'.card = n - 1 := by
      rw [Finset.card_erase_of_mem hvS, hScard]
    obtain ⟨A, B, hA_ne, hB_ne, hAB_disj, hAB_union, hAB_pure⟩ :=
      ih (n - 1) (by omega) S' hS'_card (by omega)
    have hv_not_S' : v ∉ S' := Finset.notMem_erase v S
    rw [← hAB_union, Finset.mem_union, not_or] at hv_not_S'
    have hinsert_eq : insert v (A ∪ B) = S := by
      rw [hAB_union, Finset.insert_erase hvS]
    rcases hAB_pure with hcomp | hanti
    · have hG_compl : IsInducedSubgraphFree Gᶜ P4 := isP4Free_compl_of_isP4Free hG
      have hanti_compl : IsAnticompletePair Gᶜ A B := isAnticompletePair_compl_of_isCompletePair hcomp
      obtain ⟨X, Y, hX, hY, hXY_disj, hXY_union, hXY_pure_compl⟩ :=
        exists_pure_partition_insert_of_anticomplete hG_compl hA_ne hB_ne hAB_disj
          hv_not_S'.1 hv_not_S'.2 hanti_compl
      rw [hinsert_eq] at hXY_union
      exact ⟨X, Y, hX, hY, hXY_disj, hXY_union, isPurePair_of_compl hXY_disj hXY_pure_compl⟩
    · obtain ⟨X, Y, hX, hY, hXY_disj, hXY_union, hXY_pure⟩ :=
        exists_pure_partition_insert_of_anticomplete hG hA_ne hB_ne hAB_disj
          hv_not_S'.1 hv_not_S'.2 hanti
      rw [hinsert_eq] at hXY_union
      exact ⟨X, Y, hX, hY, hXY_disj, hXY_union, hXY_pure⟩

/--
**Cograph Multiplicative Erdős–Hajnal Bound (`exists_clique_and_indep_mul_ge_of_isP4Free`)**:
For every $P_4$-free graph $G$ and every finite subset $S \subseteq V$, there exist a clique
$K \subseteq S$ and an independent set $I \subseteq S$ in $G$ such that $|S| \le |K| \cdot |I|$.
-/
theorem exists_clique_and_indep_mul_ge_of_isP4Free {G : SimpleGraph V}
    (hG : IsInducedSubgraphFree G P4) (S : Finset V) :
    ∃ K ⊆ S, ∃ I ⊆ S,
      (∀ u ∈ K, ∀ v ∈ K, u ≠ v → G.Adj u v) ∧
      (∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬G.Adj u v) ∧
      S.card ≤ K.card * I.card := by
  classical
  suffices h : ∀ (n : ℕ) (T : Finset V), T.card = n →
      ∃ K ⊆ T, ∃ I ⊆ T,
        (∀ u ∈ K, ∀ v ∈ K, u ≠ v → G.Adj u v) ∧
        (∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬G.Adj u v) ∧
        T.card ≤ K.card * I.card from h S.card S rfl
  intro n
  refine Nat.strongRecOn n (fun n ih => ?_)
  intro T hTcard
  rcases Nat.lt_or_ge n 2 with hn_lt2 | hn_ge2
  · rcases Nat.eq_zero_or_pos n with rfl | hn_pos
    · refine ⟨∅, Finset.empty_subset T, ∅, Finset.empty_subset T, ?_, ?_, by omega⟩
      · intro u hu; exact False.elim (Finset.notMem_empty u hu)
      · intro u hu; exact False.elim (Finset.notMem_empty u hu)
    · have hT1 : T.card = 1 := by omega
      obtain ⟨v, hv_eq⟩ := Finset.card_eq_one.mp hT1
      refine ⟨T, Finset.Subset.rfl, T, Finset.Subset.rfl, ?_, ?_, by simp [hT1]⟩
      · intro x hx y hy hne
        rw [hv_eq, Finset.mem_singleton] at hx hy
        exact False.elim (hne (hx.trans hy.symm))
      · intro x hx y hy hne
        rw [hv_eq, Finset.mem_singleton] at hx hy
        exact False.elim (hne (hx.trans hy.symm))
  · obtain ⟨A, B, hA_ne, hB_ne, hAB_disj, hAB_union, hAB_pure⟩ :=
      seinsche_pure_partition hG n T hTcard hn_ge2
    have hA_pos : 0 < A.card := Finset.card_pos.mpr hA_ne
    have hB_pos : 0 < B.card := Finset.card_pos.mpr hB_ne
    have hT_sum : T.card = A.card + B.card := by
      rw [← hAB_union, Finset.card_union_of_disjoint hAB_disj]
    obtain ⟨KA, hKA_sub, IA, hIA_sub, hKA_clique, hIA_indep, hA_le⟩ :=
      ih A.card (by omega) A rfl
    obtain ⟨KB, hKB_sub, IB, hIB_sub, hKB_clique, hIB_indep, hB_le⟩ :=
      ih B.card (by omega) B rfl
    have hA_sub : A ⊆ T := by rw [← hAB_union]; exact Finset.subset_union_left
    have hB_sub : B ⊆ T := by rw [← hAB_union]; exact Finset.subset_union_right
    rcases hAB_pure with hcomp | hanti
    · have hK_disj : Disjoint KA KB :=
        Finset.disjoint_of_subset_left hKA_sub (Finset.disjoint_of_subset_right hKB_sub hAB_disj)
      have hK_clique : ∀ u ∈ KA ∪ KB, ∀ v ∈ KA ∪ KB, u ≠ v → G.Adj u v := by
        intro u hu v hv hne
        rw [Finset.mem_union] at hu hv
        rcases hu with huA | huB <;> rcases hv with hvA | hvB
        · exact hKA_clique u huA v hvA hne
        · exact hcomp u (hKA_sub huA) v (hKB_sub hvB)
        · exact G.symm (hcomp v (hKA_sub hvA) u (hKB_sub huB))
        · exact hKB_clique u huB v hvB hne
      by_cases hI_cmp : IA.card ≤ IB.card
      · refine ⟨KA ∪ KB, Finset.union_subset (hKA_sub.trans hA_sub) (hKB_sub.trans hB_sub),
          IB, hIB_sub.trans hB_sub, hK_clique, hIB_indep, ?_⟩
        rw [Finset.card_union_of_disjoint hK_disj, Nat.add_mul]
        have : KA.card * IA.card ≤ KA.card * IB.card := Nat.mul_le_mul_left KA.card hI_cmp
        omega
      · refine ⟨KA ∪ KB, Finset.union_subset (hKA_sub.trans hA_sub) (hKB_sub.trans hB_sub),
          IA, hIA_sub.trans hA_sub, hK_clique, hIA_indep, ?_⟩
        rw [Finset.card_union_of_disjoint hK_disj, Nat.add_mul]
        have : KB.card * IB.card ≤ KB.card * IA.card :=
          Nat.mul_le_mul_left KB.card (by omega)
        omega
    · have hI_disj : Disjoint IA IB :=
        Finset.disjoint_of_subset_left hIA_sub (Finset.disjoint_of_subset_right hIB_sub hAB_disj)
      have hI_indep : ∀ u ∈ IA ∪ IB, ∀ v ∈ IA ∪ IB, u ≠ v → ¬G.Adj u v := by
        intro u hu v hv hne
        rw [Finset.mem_union] at hu hv
        rcases hu with huA | huB <;> rcases hv with hvA | hvB
        · exact hIA_indep u huA v hvA hne
        · exact hanti u (hIA_sub huA) v (hIB_sub hvB)
        · exact fun huv => hanti v (hIA_sub hvA) u (hIB_sub huB) (G.symm huv)
        · exact hIB_indep u huB v hvB hne
      by_cases hK_cmp : KA.card ≤ KB.card
      · refine ⟨KB, hKB_sub.trans hB_sub,
          IA ∪ IB, Finset.union_subset (hIA_sub.trans hA_sub) (hIB_sub.trans hB_sub),
          hKB_clique, hI_indep, ?_⟩
        rw [Finset.card_union_of_disjoint hI_disj, Nat.mul_add]
        have : KA.card * IA.card ≤ KB.card * IA.card := Nat.mul_le_mul_right IA.card hK_cmp
        omega
      · refine ⟨KA, hKA_sub.trans hA_sub,
          IA ∪ IB, Finset.union_subset (hIA_sub.trans hA_sub) (hIB_sub.trans hB_sub),
          hKA_clique, hI_indep, ?_⟩
        rw [Finset.card_union_of_disjoint hI_disj, Nat.mul_add]
        have : KB.card * IB.card ≤ KA.card * IB.card :=
          Nat.mul_le_mul_right IB.card (by omega)
        omega

/--
**$P_4$-Free Erdős–Hajnal Theorem with Exponent $1/2$ (`exists_clique_or_indep_rpow_half_of_isP4Free`)**:
Every $P_4$-free graph $G$ on a finite vertex set $S \subseteq V$ contains a subset $R \subseteq S$
of cardinality $|R| \ge |S|^{1/2}$ that is either a clique or an independent set in $G$.
-/
theorem exists_clique_or_indep_rpow_half_of_isP4Free {G : SimpleGraph V}
    (hG : IsInducedSubgraphFree G P4) (S : Finset V) :
    ∃ R ⊆ S, (S.card : ℝ) ^ (1 / 2 : ℝ) ≤ (R.card : ℝ) ∧
      ((∀ u ∈ R, ∀ v ∈ R, u ≠ v → G.Adj u v) ∨
       (∀ u ∈ R, ∀ v ∈ R, u ≠ v → ¬G.Adj u v)) := by
  obtain ⟨K, hK_sub, I, hI_sub, hK_clique, hI_indep, hmul⟩ :=
    exists_clique_and_indep_mul_ge_of_isP4Free hG S
  have h_rpow_sq : ∀ m : ℕ, (S.card ≤ m * m) → (S.card : ℝ) ^ (1 / 2 : ℝ) ≤ (m : ℝ) := by
    intro m hm
    have hm_real : (S.card : ℝ) ≤ (m : ℝ) ^ (2 : ℕ) := by
      rw [sq]
      exact_mod_cast hm
    have h1 : (S.card : ℝ) ^ (1 / 2 : ℝ) ≤ ((m : ℝ) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hm_real (by norm_num)
    have h2 : ((m : ℝ) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) = (m : ℝ) := by
      rw [← Real.rpow_natCast (m : ℝ) 2, ← Real.rpow_mul (Nat.cast_nonneg m)]
      norm_num
    linarith
  by_cases hKI : K.card ≤ I.card
  · refine ⟨I, hI_sub, h_rpow_sq I.card ?_, Or.inr hI_indep⟩
    exact le_trans hmul (Nat.mul_le_mul_right I.card hKI)
  · refine ⟨K, hK_sub, h_rpow_sq K.card ?_, Or.inl hK_clique⟩
    exact le_trans hmul (Nat.mul_le_mul_left K.card (by omega))

end ErdosHajnalP6
