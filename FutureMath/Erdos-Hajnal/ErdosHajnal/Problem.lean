/-
Copyright 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosHajnal.AllPathsDefs
import ErdosHajnal.Defs
import ErdosHajnal.GenDefs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Problem Statement: Unconditional Single-Graph Erdős–Hajnal Property for All Finite Paths $P_k$, Spiders $S_{1,2,d}$, Birds $\mathrm{Bird}_d$, Brooms, Double Brooms, Sawtooths, Small Trees, and Prime Towers (`main.tex`)

This file states all parts of the **Main Theorem** (Parts A, B, and C, encompassing Theorems 1–9,
Propositions 1–8, and Lemmas 1–14) of `main.tex` in complete generality:

1. **`erdos_hajnal_all_paths`, `erdos_61.variants.all_paths`, & `erdos_hajnal_all_paths_fintype`
   (Main Theorem Part A.1 / Theorem 9(1))**:
   For **every integer $k \ge 1$**, both the $k$-vertex path $P_k$ (`pathGraph k`) and its
   complement $\overline{P_k}$ (`(pathGraph k)ᶜ`) unconditionally satisfy the Erdős–Hajnal property,
   the polynomial Rödl property, and Kleitman–Winston virality.

2. **`main_theorem_A2_linear_forests_and_brooms` (Main Theorem Part A.2–A.3 / Theorem 9(1))**:
   Every non-empty linear forest $F = \bigsqcup_{r=1}^m P_{k_r}$ (`LinearForestGraph ks`) and
   co-linear forest $\overline{F}$, every $(s, d)$-broom $B(s, d) := P_{d+2}[v_1 \leftarrow \overline{K_s}]$
   (`BroomGraph s d`, $s, d \ge 1$, explicitly including $B(2, 2) = P_4[v_1 \leftarrow \overline{K_2}]$),
   and every double broom $\mathrm{DB}(a, d, b) := P_{d+3}[v_1 \leftarrow \overline{K_a}, v_{d+3} \leftarrow \overline{K_b}]$
   (`DoubleBroomGraph a d b`, $a, d, b \ge 1$), together with all of their complements, unconditionally
   satisfy `HasErdosHajnalProp`, `HasPolyRodlProp`, and `IsViral`.

3. **`main_theorem_A4_spiders_birds_sawtooths` (Main Theorem Part A.4 / Theorem 9(2))**:
   Every subdivided spider $S_{1,2,d}$ (`SpiderGraph d`, $d \ge 2$, explicitly including $S_{1,2,6}$),
   every leaf-substituted spider $S_{1,2,d}[w_1 \leftarrow \overline{K_a}, x_2 \leftarrow \overline{K_b}, u_d \leftarrow \overline{K_c}]$
   (`LeafSubstSpiderGraph d a b c`, $d \ge 2, a, b, c \ge 1$), every unicyclic bird $\mathrm{Bird}_d$
   (`BirdDGraph d`, $d \ge 1$, including `BullGraph = BirdDGraph 1` and `BirdDGraph 2 ≃g BirdGraph`),
   and every bicyclic sawtooth $M_{2,d} := \mathrm{Bird}_d[b_0 \leftarrow K_2]$ (`SawtoothGraph d`,
   $d \ge 1$), together with all of their complements, unconditionally satisfy `HasErdosHajnalProp`,
   `HasPolyRodlProp`, and `IsViral`.

4. **`main_theorem_A5_small_trees_and_forests` (Main Theorem Part A.4 / Theorem 8(1))**:
   Every finite tree $T$ with $1 \le |V(T)| \le 6$, every non-empty finite forest $F$ whose connected
   components each have order $\le 6$, and every finite tree $T$ on $7$ vertices not isomorphic to
   the subdivided claw $S_{2,2,2}$ (`SubdividedClawGraph`, i.e., $10$ of the $11$ non-isomorphic trees
   on $7$ vertices), together with all of their complements, belong to $\mathcal{H}(\mathcal{B}_{\mathrm{new}}^*)$
   (`InHClosureBNew`) and unconditionally satisfy `HasErdosHajnalProp`, `HasPolyRodlProp`, and `IsViral`.

5. **`main_theorem_B_stage1_stage2_all_families` (Main Theorem Part B / Theorem 7, Proposition 7, Lemma 14, Proposition 8)**:
   - `Stage1CombCoCombDichotomyAt r` holds for every integer $r \ge 1$.
   - Every singleton path `pathGraph k` ($k \ge 6$), every singleton spider `SpiderGraph d` ($d \ge 2$),
     and every singleton bird `BirdDGraph d` ($d \ge 2$) is unconditionally leaf-reducible,
     Stage-1 coupled generalized nice (`IsCoupledGeneralizedNice`), and Stage-2 thresholded wonderful
     (`IsThresholdedWonderful`).

6. **`main_theorem_C_closures_forest_pairs_hook4_and_infinite_towers` (Main Theorem Part C / Theorem 8(2), Theorem 9(3), Proposition 6(3))**:
   - Strict containments $\mathcal{H}(\mathcal{B}_9^*) \subsetneq \mathcal{H}(\mathcal{B}_{\mathrm{new}}^*) \subsetneq \mathcal{H}(\mathcal{B}_\infty^*) \subseteq \mathcal{EH}$;
   - Every pair $(H_1, \overline{H_2})$ with $H_1, H_2 \in \mathcal{J}(\mathcal{B}_\infty^*)$ (including
     all opposite-chirality non-empty finite forest pairs $\{F_1, \overline{F_2}\}$) and every hooked-claw
     pair $\{P_t, \operatorname{Hook}_4(Q, S)\}$ ($t \ge 1, Q \in \mathcal{EH}$) satisfies
     `HasPairErdosHajnalProp`, `HasPairPolyRodlProp`, and `IsPairViral`;
   - Countably infinitely many pairwise non-isomorphic infinite prime non-split viral towers
     `GenPrimeTowerGraph G₀ x₀ r` ($r \ge 0$) above every base graph
     $G_0 \in \{P_k : k \ge 6\} \cup \{S_{1,2,d} : d \ge 2\} \cup \{\mathrm{Bird}_d : d \ge 2\}$.
-/

open Filter SimpleGraph Real ErdosHajnalP6 ErdosHajnalGen

namespace Erdos61

/-! ### Part (A): Unconditional Single-Graph Erdős–Hajnal Theorems Across All Infinite Families -/

/-- **Main Theorem (A.1) — Universal Statement for All Finite Paths $P_k$ (`pathGraph k`, $k \ge 1$, Theorem 9(1) of `main.tex`)**:
For every integer $k \ge 1$, there exists a constant $c > 0$ such that every finite graph on $n$
vertices containing no induced copy of $P_k$ (`pathGraph k`) has a clique or stable set of size
at least $n^c$. -/
theorem erdos_hajnal_all_paths :
    ∀ k : ℕ, 1 ≤ k →
      ∃ c > (0 : ℝ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
        IsInducedSubgraphFree G (pathGraph k) →
          (G.cliqueNum : ℝ) ≥ (n : ℝ) ^ c ∨ (G.indepNum : ℝ) ≥ (n : ℝ) ^ c := by
  sorry

/-- **Erdős Problem 61 (`FormalConjectures` Asymptotic Variant for All Finite Paths $P_k$, $k \ge 1$)**. -/
theorem erdos_61.variants.all_paths :
    ∀ k : ℕ, 1 ≤ k →
      ∃ c > (0 : ℝ), IsErdosHajnalLowerBound (pathGraph k) (fun n : ℕ => (n : ℝ) ^ c) := by
  sorry

/-- **Main Theorem (A.1) — Full Equivalence Statement (`HasErdosHajnalProp`, `HasPolyRodlProp`, and
`IsViral`) for All Finite Paths $P_k$ and Co-Paths $\overline{P_k}$ ($k \ge 1$)**. -/
theorem erdos_hajnal_all_paths_fintype :
    ∀ k : ℕ, 1 ≤ k →
      HasErdosHajnalProp (pathGraph k) ∧
      HasErdosHajnalProp (pathGraph k)ᶜ ∧
      HasPolyRodlProp (pathGraph k) ∧
      HasPolyRodlProp (pathGraph k)ᶜ ∧
      IsViral (pathGraph k) ∧
      IsViral (pathGraph k)ᶜ := by
  sorry

/-- **Main Theorem (A.2)–(A.3) — All Linear/Co-Linear Forests, All $(s, d)$-Brooms ($s, d \ge 1$,
Including $B(2, 2) = P_4[v_1 \leftarrow \overline{K_2}]$), and All Double Brooms $\mathrm{DB}(a, d, b)$
($a, d, b \ge 1$) (Theorem 9(1) of `main.tex`)**. -/
theorem main_theorem_A2_linear_forests_and_brooms :
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
  sorry

/-- **Main Theorem (A.4) — All Prime Subdivided Spiders $S_{1,2,d}$ ($d \ge 2$, Including $S_{1,2,6}$),
All Leaf-Substituted Spiders $S_{1,2,d}[w_1 \leftarrow \overline{K_a}, x_2 \leftarrow \overline{K_b}, u_d \leftarrow \overline{K_c}]$
($d \ge 2, a, b, c \ge 1$), All Prime Unicyclic Birds $\mathrm{Bird}_d$ ($d \ge 1$, Including
`BullGraph`), and All Bicyclic Sawtooths $M_{2,d}$ ($d \ge 1$) (Theorem 9(2)–(3) of `main.tex`)**. -/
theorem main_theorem_A4_spiders_birds_sawtooths :
    (∀ d : ℕ, 2 ≤ d →
      HasErdosHajnalProp (SpiderGraph d) ∧
      HasErdosHajnalProp (SpiderGraph d)ᶜ ∧
      HasPolyRodlProp (SpiderGraph d) ∧
      IsViral (SpiderGraph d)) ∧
    (∀ (d a b c : ℕ), 2 ≤ d → 1 ≤ a → 1 ≤ b → 1 ≤ c →
      HasErdosHajnalProp (LeafSubstSpiderGraph d a b c) ∧
      HasErdosHajnalProp (LeafSubstSpiderGraph d a b c)ᶜ ∧
      HasPolyRodlProp (LeafSubstSpiderGraph d a b c) ∧
      IsViral (LeafSubstSpiderGraph d a b c)) ∧
    (∀ d : ℕ, 1 ≤ d →
      HasErdosHajnalProp (BirdDGraph d) ∧
      HasErdosHajnalProp (BirdDGraph d)ᶜ ∧
      HasPolyRodlProp (BirdDGraph d) ∧
      IsViral (BirdDGraph d)) ∧
    (∀ d : ℕ, 1 ≤ d →
      HasErdosHajnalProp (SawtoothGraph d) ∧
      HasErdosHajnalProp (SawtoothGraph d)ᶜ ∧
      HasPolyRodlProp (SawtoothGraph d) ∧
      IsViral (SawtoothGraph d)) := by
  sorry

/-- **Main Theorem (A.5) — All Trees of Order $\le 6$, All Forests of Component Order $\le 6$,
and $10$ of the $11$ Non-Isomorphic Trees on $7$ Vertices (Excluding Solely $S_{2,2,2}$)
(Theorem 8(1) of `main.tex`)**. -/
theorem main_theorem_A5_small_trees_and_forests :
    (∀ (W : Type) [Fintype W] [DecidableEq W] [Nonempty W] (T : SimpleGraph W),
      T.IsTree → Fintype.card W ≤ 6 →
        InHClosureBNew T ∧ HasErdosHajnalProp T ∧ HasErdosHajnalProp Tᶜ ∧
        HasPolyRodlProp T ∧ IsViral T) ∧
    (∀ (W : Type) [Fintype W] [DecidableEq W] [Nonempty W] (F : SimpleGraph W)
      [DecidableRel F.Reachable],
      F.IsAcyclic →
      (∀ u : W, (Finset.univ.filter (fun v : W => F.Reachable u v)).card ≤ 6) →
        InHClosureBNew F ∧ HasErdosHajnalProp F ∧ HasErdosHajnalProp Fᶜ ∧
        HasPolyRodlProp F ∧ IsViral F) ∧
    (∀ (W : Type) [Fintype W] [DecidableEq W] (T : SimpleGraph W),
      T.IsTree → Fintype.card W = 7 → ¬Nonempty (T ≃g SubdividedClawGraph) →
        InHClosureBNew T ∧ HasErdosHajnalProp T ∧ HasErdosHajnalProp Tᶜ ∧
        HasPolyRodlProp T ∧ IsViral T) := by
  sorry

/-! ### Part (B): Unconditional Leaf-Reducibility, Stage-1 Generalized Niceness, and Stage-2 Thresholded Wonderfulness Across All $\{P_k\}$ ($k \ge 6$), $\{S_{1,2,d}\}$ ($d \ge 2$), and $\{\mathrm{Bird}_d\}$ ($d \ge 2$) -/

/-- **Main Theorem (B) (`main_theorem_B_stage1_stage2_all_families`, Theorem 7, Proposition 7,
Lemma 14, & Proposition 8 of `main.tex`)**:
1. For every integer $r \ge 1$, the depth-$r$ Stage-1 Comb/Co-Comb Dichotomy
   `Stage1CombCoCombDichotomyAt r` holds for all $\overline{P_{s+4+r}}$-free combs and co-combs.
2. Every singleton path `pathGraph k` ($k \ge 6$) is unconditionally leaf-reducible, Stage-1 coupled
   generalized nice (`IsCoupledGeneralizedNice`), and Stage-2 thresholded wonderful (`IsThresholdedWonderful`).
3. Every singleton subdivided spider `SpiderGraph d` ($d \ge 2$) is unconditionally leaf-reducible,
   Stage-1 coupled generalized nice (`IsCoupledGeneralizedNice`), and Stage-2 thresholded wonderful
   (`IsThresholdedWonderful`).
4. Every singleton unicyclic bird `BirdDGraph d` ($d \ge 2$) is unconditionally leaf-reducible,
   Stage-1 coupled generalized nice (`IsCoupledGeneralizedNice`), and Stage-2 thresholded wonderful
   (`IsThresholdedWonderful`). -/
theorem main_theorem_B_stage1_stage2_all_families :
    (∀ r : ℕ, 1 ≤ r → Stage1CombCoCombDichotomyAt r) ∧
    (∀ k : ℕ, 6 ≤ k →
      (∃ v₀ : Fin k, (neighborFinsetIn (pathGraph k) v₀ Finset.univ).card ≤ 1 ∧
        HasErdosHajnalProp ((pathGraph k).comap (Subtype.val : {v : Fin k // v ≠ v₀} → Fin k))) ∧
      IsCoupledGeneralizedNice (pathGraph k) ∧
      IsCoupledGeneralizedNice (pathGraph k)ᶜ ∧
      IsThresholdedWonderful (pathGraph k)) ∧
    (∀ d : ℕ, 2 ≤ d →
      (∃ v₀ : Fin (d + 4), (neighborFinsetIn (SpiderGraph d) v₀ Finset.univ).card ≤ 1 ∧
        HasErdosHajnalProp ((SpiderGraph d).comap (Subtype.val : {v : Fin (d + 4) // v ≠ v₀} → Fin (d + 4)))) ∧
      IsCoupledGeneralizedNice (SpiderGraph d) ∧
      IsCoupledGeneralizedNice (SpiderGraph d)ᶜ ∧
      IsThresholdedWonderful (SpiderGraph d)) ∧
    (∀ d : ℕ, 2 ≤ d →
      (∃ v₀ : Fin (d + 4), (neighborFinsetIn (BirdDGraph d) v₀ Finset.univ).card ≤ 1 ∧
        HasErdosHajnalProp ((BirdDGraph d).comap (Subtype.val : {v : Fin (d + 4) // v ≠ v₀} → Fin (d + 4)))) ∧
      IsCoupledGeneralizedNice (BirdDGraph d) ∧
      IsCoupledGeneralizedNice (BirdDGraph d)ᶜ ∧
      IsThresholdedWonderful (BirdDGraph d)) := by
  sorry

/-! ### Part (C): Expanded Viral Closures $\mathcal{H}(\mathcal{B}_9^*) \subsetneq \mathcal{H}(\mathcal{B}_{\mathrm{new}}^*) \subsetneq \mathcal{H}(\mathcal{B}_\infty^*)$, Opposite-Chirality Forest Pairs, Hooked-Claw Pairs, and Countably Infinitely Many Prime Non-Split Viral Towers -/

/-- **Main Theorem (C) (`main_theorem_C_closures_forest_pairs_hook4_and_infinite_towers`,
Proposition 6(3), Proposition 7(1), Theorem 8(2), & Theorem 9(3) of `main.tex`)**:
1. Strict containments $\mathcal{H}(\mathcal{B}_9^*) \subsetneq \mathcal{H}(\mathcal{B}_{\mathrm{new}}^*) \subsetneq \mathcal{H}(\mathcal{B}_\infty^*) \subseteq \mathcal{EH}$:
   every $H \in \mathcal{H}(\mathcal{B}_9^*)$ lies in $\mathcal{H}(\mathcal{B}_{\mathrm{new}}^*)$,
   every $H \in \mathcal{H}(\mathcal{B}_{\mathrm{new}}^*)$ lies in $\mathcal{H}(\mathcal{B}_\infty^*)$,
   `SpiderGraph 2` lies in $\mathcal{H}(\mathcal{B}_{\mathrm{new}}^*) \setminus \mathcal{H}(\mathcal{B}_9^*)$, and
   `SpiderGraph 6` lies in $\mathcal{H}(\mathcal{B}_\infty^*) \setminus \mathcal{H}(\mathcal{B}_{\mathrm{new}}^*)$;
2. For all $H_1, H_2 \in \mathcal{J}(\mathcal{B}_\infty^*)$ (and for all non-empty finite forests
   $F_1, F_2$), $\{H_1, \overline{H_2}\}$ satisfies `HasPairErdosHajnalProp`, `HasPairPolyRodlProp`,
   and `IsPairViral`; and every $H \in \mathcal{H}(\mathcal{B}_\infty^*)$ satisfies `HasErdosHajnalProp`,
   `HasPolyRodlProp`, and `IsViral` (along with its complement);
3. For every non-empty graph $Q \in \mathcal{EH}$, every subset $S \subseteq V(Q)$, and **every integer
   $t \ge 1$**, both $\{P_t, \operatorname{Hook}_4(Q, S)\}$ and $\{\overline{P_t}, \overline{\operatorname{Hook}_4(Q, S)}\}$
   satisfy `HasPairErdosHajnalProp`, `HasPairPolyRodlProp`, and `IsPairViral`;
4. For every base graph $(G_0, x_0)$ in
   $\{(P_k, v_k) : k \ge 6\} \cup \{(S_{1,2,d}, u_d) : d \ge 2\} \cup \{(\mathrm{Bird}_d, u_d) : d \ge 2\}$
   and every integer $r \ge 0$, `GenPrimeTowerGraph G₀ x₀ r` belongs to `InHClosureBInfty`, satisfies
   `HasErdosHajnalProp`, `HasPolyRodlProp`, and `IsViral` (along with its complement), is prime
   (`IsPrimeGraph`), is non-split (`¬IsSplitGraph`), satisfies
   `¬InJClosureC5 (GenPrimeTowerGraph G₀ x₀ r)ᶜ`, and satisfies
   `Nonempty (GenPrimeTowerGraph G₀ x₀ r₁ ≃g GenPrimeTowerGraph G₀ x₀ r₂) ↔ r₁ = r₂`. -/
theorem main_theorem_C_closures_forest_pairs_hook4_and_infinite_towers :
    ((∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W),
        InHClosure 9 H → InHClosureBNew H) ∧
     (InHClosureBNew (SpiderGraph 2) ∧ ¬InHClosure 9 (SpiderGraph 2)) ∧
     (∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W),
        InHClosureBNew H → InHClosureBInfty H) ∧
     (InHClosureBInfty (SpiderGraph 6) ∧ ¬InHClosureBNew (SpiderGraph 6))) ∧
    ((∀ (W₁ W₂ : Type) [Fintype W₁] [DecidableEq W₁] [Nonempty W₁]
        [Fintype W₂] [DecidableEq W₂] [Nonempty W₂]
        (F₁ : SimpleGraph W₁) (F₂ : SimpleGraph W₂),
        F₁.IsAcyclic → F₂.IsAcyclic →
          HasPairErdosHajnalProp F₁ F₂ᶜ ∧ HasPairPolyRodlProp F₁ F₂ᶜ ∧ IsPairViral F₁ F₂ᶜ) ∧
     (∀ (W₁ W₂ : Type) [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]
        (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂),
        InJClosureBInfty H₁ → InJClosureBInfty H₂ →
          HasPairErdosHajnalProp H₁ H₂ᶜ ∧ HasPairPolyRodlProp H₁ H₂ᶜ ∧ IsPairViral H₁ H₂ᶜ) ∧
     (∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W),
        InHClosureBInfty H →
          HasErdosHajnalProp H ∧ HasErdosHajnalProp Hᶜ ∧ HasPolyRodlProp H ∧ IsViral H)) ∧
    (∀ (W : Type) [Fintype W] [DecidableEq W] (Q : SimpleGraph W) (S : Set W),
      HasErdosHajnalProp Q → 1 ≤ Fintype.card W →
        ∀ t : ℕ, 1 ≤ t →
          HasPairErdosHajnalProp (pathGraph t) (Hook4Graph Q S) ∧
          HasPairErdosHajnalProp (pathGraph t)ᶜ (Hook4Graph Q S)ᶜ ∧
          HasPairPolyRodlProp (pathGraph t) (Hook4Graph Q S) ∧
          IsPairViral (pathGraph t) (Hook4Graph Q S)) ∧
    (∀ (W₀ : Type) [Fintype W₀] [DecidableEq W₀] (G₀ : SimpleGraph W₀) (x₀ : W₀),
      (IsPrimeGraph G₀ ∧ 6 ≤ Fintype.card W₀ ∧
       (∀ u : W₀, (neighborFinsetIn G₀ u Finset.univ).card ≤ Fintype.card W₀ - 3) ∧
       (neighborFinsetIn G₀ x₀ Finset.univ).card = 1 ∧
       ¬IsSplitGraph G₀ ∧
       InHClosureBInfty G₀ ∧
       InHClosureBInfty (G₀.comap (Subtype.val : {w : W₀ // w ≠ x₀} → W₀))) →
      (∀ r : ℕ,
        InHClosureBInfty (GenPrimeTowerGraph G₀ x₀ r) ∧
        HasErdosHajnalProp (GenPrimeTowerGraph G₀ x₀ r) ∧
        HasErdosHajnalProp (GenPrimeTowerGraph G₀ x₀ r)ᶜ ∧
        IsViral (GenPrimeTowerGraph G₀ x₀ r) ∧
        IsPrimeGraph (GenPrimeTowerGraph G₀ x₀ r) ∧
        ¬IsSplitGraph (GenPrimeTowerGraph G₀ x₀ r) ∧
        ¬InJClosureC5 (GenPrimeTowerGraph G₀ x₀ r)ᶜ) ∧
      (∀ r₁ r₂ : ℕ,
        Nonempty (GenPrimeTowerGraph G₀ x₀ r₁ ≃g GenPrimeTowerGraph G₀ x₀ r₂) ↔ r₁ = r₂)) ∧
    ((∀ (k : ℕ) (hk : 6 ≤ k) (r : ℕ),
        InHClosureBInfty (GenPrimeTowerGraph (pathGraph k) ⟨k - 1, by omega⟩ r) ∧
        HasErdosHajnalProp (GenPrimeTowerGraph (pathGraph k) ⟨k - 1, by omega⟩ r) ∧
        IsPrimeGraph (GenPrimeTowerGraph (pathGraph k) ⟨k - 1, by omega⟩ r) ∧
        ¬IsSplitGraph (GenPrimeTowerGraph (pathGraph k) ⟨k - 1, by omega⟩ r)) ∧
     (∀ d : ℕ, 2 ≤ d → ∀ r : ℕ,
        InHClosureBInfty (GenPrimeTowerGraph (SpiderGraph d) (Fin.last (d + 3)) r) ∧
        HasErdosHajnalProp (GenPrimeTowerGraph (SpiderGraph d) (Fin.last (d + 3)) r) ∧
        IsPrimeGraph (GenPrimeTowerGraph (SpiderGraph d) (Fin.last (d + 3)) r) ∧
        ¬IsSplitGraph (GenPrimeTowerGraph (SpiderGraph d) (Fin.last (d + 3)) r)) ∧
     (∀ d : ℕ, 2 ≤ d → ∀ r : ℕ,
        InHClosureBInfty (GenPrimeTowerGraph (BirdDGraph d) (Fin.last (d + 3)) r) ∧
        HasErdosHajnalProp (GenPrimeTowerGraph (BirdDGraph d) (Fin.last (d + 3)) r) ∧
        IsPrimeGraph (GenPrimeTowerGraph (BirdDGraph d) (Fin.last (d + 3)) r) ∧
        ¬IsSplitGraph (GenPrimeTowerGraph (BirdDGraph d) (Fin.last (d + 3)) r))) := by
  sorry

end Erdos61
