/-
Copyright 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosHajnal.Defs
import ErdosHajnal.GenDefs
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Definitions for the Unconditional Erdős–Hajnal Generalization Across All Paths $P_k$, Spiders $S_{1,2,d}$, Birds $\mathrm{Bird}_d$, Brooms, Double Brooms, Sawtooths, and Prime Towers (`main.tex`)

This file defines, directly from first principles using Mathlib's `SimpleGraph`, every named graph
family and closure operator in `main.tex`:

1. **Linear Forests, Double Brooms, Subdivided Spiders, Unicyclic Birds, and Bicyclic Sawtooths**
   (`Definition 1(5)` of `main.tex`):
   - `LinearForestGraph ks`: Disjoint union $\bigsqcup_{r=1}^m P_{k_r}$ of finite paths (`pathGraph`).
   - `DoubleBroomGraph a d b`: The $(a + d + b + 1)$-vertex double broom
     $\mathrm{DB}(a, d, b) := P_{d+3}[v_1 \leftarrow \overline{K_a},\, v_{d+3} \leftarrow \overline{K_b}]$.
   - `SpiderGraph d`: The $(d + 4)$-vertex subdivided spider $S_{1,2,d}$ on `Fin (d + 4)`
     (`0 = c`, `1 = w₁`, `2 = w₂`, `3 = x₂`, and `4 + q = u_{q+1}` for $0 \le q < d$).
   - `LeafSubstSpiderGraph d a b c`: The leaf-substituted spider
     $S_{1,2,d}[w_1 \leftarrow \overline{K_a},\, x_2 \leftarrow \overline{K_b},\, u_d \leftarrow \overline{K_c}]$
     ($d \ge 2, a, b, c \ge 1$).
   - `SubdividedClawGraph`: The $7$-vertex subdivided claw $S_{2,2,2}$ on `Fin 7`
     (the unique $7$-vertex tree outside $\mathcal{H}(\mathcal{B}_{\mathrm{new}}^*)$ in Theorem 8).
   - `BirdDGraph d` and `BullGraph`: The $(d + 4)$-vertex unicyclic bird $\mathrm{Bird}_d$ on `Fin (d + 4)`
     (`0 = b₀`, `1 = b₁`, `2 = b₂`, `3 = b₃`, and `4 + q = u_{q+1}` for $0 \le q < d$), with
     `BullGraph := BirdDGraph 1` ($\mathrm{Bull} = \mathrm{Bird}_1$).
   - `SawtoothGraph d`: The $(d + 5)$-vertex bicyclic sawtooth $M_{2,d} := \mathrm{Bird}_d[b_0 \leftarrow K_2]$.

2. **Generalized Canonical Alternating Extension Towers and Expanded Closures**
   (`Definition 1(5)`, `Proposition 6(3)`, `Theorem 8`, `Theorem 9` of `main.tex`):
   - `GenPrimeTowerGraph G₀ x₀ r`: For any graph $G_0$ with designated vertex $x_0 \in V(G_0)$ and
     integer $r \ge 0$, the $(|V(G_0)| + r)$-vertex graph $H_{n_0+r}^{(G_0)}$ on `W₀ ⊕ Fin r` formed
     by alternating co-leaf additions (odd steps) and degree-$1$ leaf additions (even steps).
   - `InBNew`, `InJClosureBNew`, `InHClosureBNew`: The expanded finite generator class
     $\mathcal{B}_{\mathrm{new}}^* := \mathcal{B}_9^* \cup \{\mathrm{Bull}\} \cup \{S_{1,2,d}, \overline{S_{1,2,d}} : 2 \le d \le 5\} \cup \{\mathrm{Bird}_d, \overline{\mathrm{Bird}_d} : 3 \le d \le 6\}$
     and its viral substitution/leaf-attachment closures $\mathcal{J}(\mathcal{B}_{\mathrm{new}}^*)$ and $\mathcal{H}(\mathcal{B}_{\mathrm{new}}^*)$.
   - `InBInfty`, `InJClosureBInfty`, `InHClosureBInfty`: The infinite generator class
     $\mathcal{B}_\infty^* := \mathcal{B}_{\mathrm{new}}^* \cup \{P_k, \overline{P_k} : k \ge 10\} \cup \{S_{1,2,d}, \overline{S_{1,2,d}} : d \ge 6\} \cup \{\mathrm{Bird}_d, \overline{\mathrm{Bird}_d} : d \ge 7\} \cup \{M_{2,d}, \overline{M_{2,d}} : d \ge 1\}$
     and its viral substitution/leaf-attachment closures $\mathcal{J}(\mathcal{B}_\infty^*)$ and $\mathcal{H}(\mathcal{B}_\infty^*)$.
-/

open Finset SimpleGraph ErdosHajnalP6

namespace ErdosHajnalGen

/-! ### 1. Linear Forests, Double Brooms, Subdivided Spiders, Unicyclic Birds, and Sawtooths -/

/-- Vertex type of the linear forest $\bigsqcup_{r=1}^m P_{k_r}$ for a list `ks : List ℕ`. -/
abbrev LinearForestVert (ks : List ℕ) : Type :=
  Σ i : Fin ks.length, Fin (ks.get i)

/-- **Linear Forest (`LinearForestGraph ks`, Definition 1(5) of `main.tex`)**:
Vertex-disjoint union $\bigsqcup_{i < \text{ks.length}} P_{\text{ks}[i]}$ of finite paths. -/
def LinearForestGraph (ks : List ℕ) : SimpleGraph (LinearForestVert ks) where
  Adj a b := a.1 = b.1 ∧ (a.2.1 + 1 = b.2.1 ∨ b.2.1 + 1 = a.2.1)
  symm _ _ h := ⟨h.1.symm, h.2.symm⟩
  loopless _ h := by omega

instance instDecidableRelLinearForestAdj (ks : List ℕ) :
    DecidableRel (LinearForestGraph ks).Adj := by
  intro a b
  dsimp [LinearForestGraph]
  infer_instance

/-- Helper vertex in `substGraph (pathGraph (d + 3)) 0 (⊥ : SimpleGraph (Fin a))` corresponding to $v_{d+3}$. -/
def doubleBroomRightEnd (a d : ℕ) : {v : Fin (d + 3) // v ≠ 0} ⊕ Fin a :=
  Sum.inl ⟨Fin.last (d + 2), by intro h; have := congrArg Fin.val h; simp at this⟩

/-- **Double Broom (`DoubleBroomGraph a d b`, Definition 1(5) of `main.tex`)**:
$\mathrm{DB}(a, d, b) := P_{d+3}[v_1 \leftarrow \overline{K_a},\, v_{d+3} \leftarrow \overline{K_b}]$
on $a + d + b + 1$ vertices ($a, d, b \ge 1$). -/
def DoubleBroomGraph (a d b : ℕ) :
    SimpleGraph ({v : {v : Fin (d + 3) // v ≠ 0} ⊕ Fin a // v ≠ doubleBroomRightEnd a d} ⊕ Fin b) :=
  substGraph
    (substGraph (pathGraph (d + 3)) 0 (⊥ : SimpleGraph (Fin a)))
    (doubleBroomRightEnd a d)
    (⊥ : SimpleGraph (Fin b))

/-- Ordered adjacency helper for `SpiderGraph d` ($S_{1,2,d}$ on `Fin (d + 4)`, where
`0 = c`, `1 = w₁`, `2 = w₂`, `3 = x₂`, and `4 + q = u_{q+1}` for $0 \le q < d$). -/
def spiderAdjLt (i j : ℕ) : Bool :=
  (i == 0 && (j == 1 || j == 2 || j == 4)) ||
  (i == 2 && j == 3) ||
  (4 ≤ i && j == i + 1)

/-- **Subdivided Spider (`SpiderGraph d`, Definition 1(5) of `main.tex`)**:
The $(d + 4)$-vertex tree $S_{1,2,d}$ on `Fin (d + 4)` with center `0` ($c$), short arm `1` ($w_1$),
$2$-edge arm `2 - 3` ($w_2 - x_2$), and $d$-edge arm `4 - 5 - ... - (d + 3)` ($u_1 - \dots - u_d$). -/
def SpiderGraph (d : ℕ) : SimpleGraph (Fin (d + 4)) where
  Adj u v :=
    if u.1 < v.1 then spiderAdjLt u.1 v.1 = true
    else if v.1 < u.1 then spiderAdjLt v.1 u.1 = true
    else False
  symm u v := by
    by_cases huv : u.1 < v.1
    · have hvu : ¬v.1 < u.1 := Nat.not_lt.mpr (Nat.le_of_lt huv)
      simp [huv, hvu]
    · by_cases hvu : v.1 < u.1
      · simp [huv, hvu]
      · simp [huv, hvu]
  loopless u := by simp

instance instDecidableRelSpiderAdj (d : ℕ) : DecidableRel (SpiderGraph d).Adj := by
  intro u v
  dsimp [SpiderGraph]
  infer_instance

/-- Named leaf $w_1 = 1$ in `SpiderGraph (max d 1)`. -/
abbrev spiderLeaf1 (d : ℕ) : Fin (max d 1 + 4) := ⟨1, by omega⟩

/-- Named leaf $x_2 = 3$ inside `substGraph (SpiderGraph (max d 1)) (spiderLeaf1 d) (⊥ : SimpleGraph (Fin a))`. -/
abbrev spiderLeaf2 (d a : ℕ) : {v : Fin (max d 1 + 4) // v ≠ spiderLeaf1 d} ⊕ Fin a :=
  Sum.inl ⟨⟨3, by omega⟩, by
    intro h
    have hv : (3 : ℕ) = 1 := congrArg Fin.val h
    omega⟩

/-- Named leaf $u_d = \max(d, 1) + 3 \ge 4$ inside the two-leaf-substituted spider. -/
abbrev spiderLeaf3 (d a b : ℕ) :
    {v : {v : Fin (max d 1 + 4) // v ≠ spiderLeaf1 d} ⊕ Fin a // v ≠ spiderLeaf2 d a} ⊕ Fin b :=
  Sum.inl ⟨Sum.inl ⟨Fin.last (max d 1 + 3), by
    intro h
    have hv : max d 1 + 3 = 1 := congrArg Fin.val h
    omega⟩,
    by
      intro h
      have hv : max d 1 + 3 = 3 := congrArg (fun x => x.1.1) (Sum.inl.inj h)
      omega⟩

/-- Vertex type of `LeafSubstSpiderGraph d a b c`. -/
abbrev LeafSubstSpiderVert (d a b c : ℕ) : Type :=
  {v : {v : {v : Fin (max d 1 + 4) // v ≠ spiderLeaf1 d} ⊕ Fin a //
    v ≠ spiderLeaf2 d a} ⊕ Fin b // v ≠ spiderLeaf3 d a b} ⊕ Fin c

noncomputable instance instDecidableEqLeafSubstSpiderVert (d a b c : ℕ) :
    DecidableEq (LeafSubstSpiderVert d a b c) :=
  Classical.decEq _

instance instFintypeLeafSubstSpiderVert (d a b c : ℕ) :
    Fintype (LeafSubstSpiderVert d a b c) :=
  inferInstance

/-- **Leaf-Substituted Spider (`LeafSubstSpiderGraph d a b c`, Theorem 8 & Theorem 9 of `main.tex`)**:
$S_{1,2,d}[w_1 \leftarrow \overline{K_a},\, x_2 \leftarrow \overline{K_b},\, u_d \leftarrow \overline{K_c}]$,
obtained by substituting $\overline{K_a}$, $\overline{K_b}$, and $\overline{K_c}$ for the three leaves
$w_1$, $x_2$, and $u_d$ of `SpiderGraph d` ($d \ge 2$). -/
def LeafSubstSpiderGraph (d a b c : ℕ) : SimpleGraph (LeafSubstSpiderVert d a b c) :=
  substGraph
    (substGraph
      (substGraph (SpiderGraph (max d 1)) (spiderLeaf1 d) (⊥ : SimpleGraph (Fin a)))
      (spiderLeaf2 d a)
      (⊥ : SimpleGraph (Fin b)))
    (spiderLeaf3 d a b)
    (⊥ : SimpleGraph (Fin c))

/-- **Subdivided Claw (`SubdividedClawGraph`, Definition 1(5) & Theorem 8 of `main.tex`)**:
The $7$-vertex tree $S_{2,2,2}$ on `Fin 7` (`0 = c`, `1 - 2`, `3 - 4`, `5 - 6`), which is the unique
non-isomorphic tree on $7$ vertices outside $\mathcal{H}(\mathcal{B}_{\mathrm{new}}^*)$. -/
def SubdividedClawGraph : SimpleGraph (Fin 7) where
  Adj u v :=
    (u = 0 ∧ (v = 1 ∨ v = 3 ∨ v = 5)) ∨
    ((u = 1 ∨ u = 3 ∨ u = 5) ∧ v = 0) ∨
    (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1) ∨
    (u = 3 ∧ v = 4) ∨ (u = 4 ∧ v = 3) ∨
    (u = 5 ∧ v = 6) ∨ (u = 6 ∧ v = 5)
  symm _ _ := by tauto
  loopless u := by fin_cases u <;> decide

instance instDecidableRelSubdividedClawAdj : DecidableRel SubdividedClawGraph.Adj := by
  intro u v
  dsimp [SubdividedClawGraph]
  infer_instance

/-- Ordered adjacency helper for `BirdDGraph d` ($\mathrm{Bird}_d$ on `Fin (d + 4)`, where
`0 = b₀`, `1 = b₁`, `2 = b₂`, `3 = b₃`, and `4 + q = u_{q+1}` for $0 \le q < d$). -/
def birdDAdjLt (i j : ℕ) : Bool :=
  (i == 0 && j == 1) ||
  (i == 1 && (j == 2 || j == 3)) ||
  (i == 2 && (j == 3 || j == 4)) ||
  (4 ≤ i && j == i + 1)

/-- **Unicyclic Long-Tail Bird (`BirdDGraph d`, Definition 1(5) of `main.tex`)**:
The $(d + 4)$-vertex unicyclic graph $\mathrm{Bird}_d$ on `Fin (d + 4)` consisting of triangle
`{1, 2, 3}` ($\{b_1, b_2, b_3\}$), pendant leaf `0 - 1` ($b_0 - b_1$), and $d$-edge tail
`2 - 4 - 5 - ... - (d + 3)` ($b_2 - u_1 - \dots - u_d$). -/
def BirdDGraph (d : ℕ) : SimpleGraph (Fin (d + 4)) where
  Adj u v :=
    if u.1 < v.1 then birdDAdjLt u.1 v.1 = true
    else if v.1 < u.1 then birdDAdjLt v.1 u.1 = true
    else False
  symm u v := by
    by_cases huv : u.1 < v.1
    · have hvu : ¬v.1 < u.1 := Nat.not_lt.mpr (Nat.le_of_lt huv)
      simp [huv, hvu]
    · by_cases hvu : v.1 < u.1
      · simp [huv, hvu]
      · simp [huv, hvu]
  loopless u := by simp

instance instDecidableRelBirdDAdj (d : ℕ) : DecidableRel (BirdDGraph d).Adj := by
  intro u v
  dsimp [BirdDGraph]
  infer_instance

/-- **The $5$-Vertex Self-Complementary Bull Graph (`BullGraph := BirdDGraph 1`)**. -/
abbrev BullGraph : SimpleGraph (Fin 5) := BirdDGraph 1

/-- **Bicyclic Sawtooth (`SawtoothGraph d`, Definition 1(5) of `main.tex`)**:
$M_{2,d} := \mathrm{Bird}_d[b_0 \leftarrow K_2]$ on $d + 5$ vertices ($d \ge 1$). -/
def SawtoothGraph (d : ℕ) : SimpleGraph ({v : Fin (d + 4) // v ≠ 0} ⊕ Fin 2) :=
  substGraph (BirdDGraph d) 0 (⊤ : SimpleGraph (Fin 2))

/-! ### 2. Generalized Alternating Prime Extension Towers and Expanded Closures -/

/-- Ordered adjacency helper among tower extension vertices `Fin r` (`0` = step 1 odd co-leaf,
`1` = step 2 even leaf, `2` = step 3 odd co-leaf, etc.). -/
def genTowerStepAdjLt (i j : ℕ) : Prop :=
  if j % 2 = 0 then i + 1 < j else i + 1 = j

/-- Adjacency predicate for `GenPrimeTowerGraph G₀ x₀ r`. -/
def genPrimeTowerAdjAux {W₀ : Type*} (G₀ : SimpleGraph W₀) (x₀ : W₀) (r : ℕ) :
    W₀ ⊕ Fin r → W₀ ⊕ Fin r → Prop
  | Sum.inl w₁, Sum.inl w₂ => G₀.Adj w₁ w₂
  | Sum.inl w, Sum.inr j => j.1 % 2 = 0 ∧ (if j.1 = 0 then w ≠ x₀ else True)
  | Sum.inr j, Sum.inl w => j.1 % 2 = 0 ∧ (if j.1 = 0 then w ≠ x₀ else True)
  | Sum.inr i, Sum.inr j =>
      if i.1 < j.1 then genTowerStepAdjLt i.1 j.1
      else if j.1 < i.1 then genTowerStepAdjLt j.1 i.1
      else False

/-- **Generalized Canonical $(x_k, y_k)$ Extension Tower (`GenPrimeTowerGraph G₀ x₀ r`,
Definition 1(5) & Proposition 6(3) of `main.tex`)**. -/
def GenPrimeTowerGraph {W₀ : Type*} (G₀ : SimpleGraph W₀) (x₀ : W₀) (r : ℕ) :
    SimpleGraph (W₀ ⊕ Fin r) where
  Adj := genPrimeTowerAdjAux G₀ x₀ r
  symm a b := by
    cases a with
    | inl w₁ =>
      cases b with
      | inl w₂ => exact fun h => G₀.symm h
      | inr j => exact id
    | inr i =>
      cases b with
      | inl w => exact id
      | inr j =>
        dsimp only [genPrimeTowerAdjAux]
        by_cases hij : i.1 < j.1
        · have hji : ¬j.1 < i.1 := Nat.not_lt.mpr (Nat.le_of_lt hij)
          simp [hij, hji]
        · by_cases hji : j.1 < i.1
          · simp [hij, hji]
          · simp [hij, hji]
  loopless a := by
    cases a with
    | inl w => exact G₀.loopless w
    | inr i => dsimp only [genPrimeTowerAdjAux]; simp

/-- **Generator Class $\mathcal{B}_{\mathrm{new}}^*$ (`InBNew H`, Definition 1(5) & Theorem 8 of `main.tex`)**. -/
def InBNew {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) : Prop :=
  InBStar 9 H ∨
  Nonempty (H ≃g BullGraph) ∨
  (∃ d : ℕ, 2 ≤ d ∧ d ≤ 5 ∧ (Nonempty (H ≃g SpiderGraph d) ∨ Nonempty (H ≃g (SpiderGraph d)ᶜ))) ∨
  (∃ d : ℕ, 3 ≤ d ∧ d ≤ 6 ∧ (Nonempty (H ≃g BirdDGraph d) ∨ Nonempty (H ≃g (BirdDGraph d)ᶜ)))

/-- **Viral Substitution & Leaf-Addition Closure $\mathcal{J}(\mathcal{B}_{\mathrm{new}}^*)$ (`InJClosureBNew`)**. -/
inductive InJClosureBNew : {W : Type} → [Fintype W] → [DecidableEq W] → SimpleGraph W → Prop where
  | base {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) : InBNew H → InJClosureBNew H
  | iso {W₁ W₂ : Type} [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]
      (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂) :
      InJClosureBNew H₁ → Nonempty (H₁ ≃g H₂) → InJClosureBNew H₂
  | subst {W₁ W₂ : Type} [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]
      (H₁ : SimpleGraph W₁) (v₀ : W₁) (H₂ : SimpleGraph W₂) :
      InJClosureBNew H₁ → InJClosureBNew H₂ → InJClosureBNew (substGraph H₁ v₀ H₂)
  | add_leaf {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) (v₀ : W) :
      (neighborFinsetIn H v₀ Finset.univ).card ≤ 1 →
      InJClosureBNew (H.comap (Subtype.val : {v : W // v ≠ v₀} → W)) →
      InJClosureBNew H

/-- **Symmetric Closure $\mathcal{H}(\mathcal{B}_{\mathrm{new}}^*) := \mathcal{J}(\mathcal{B}_{\mathrm{new}}^*) \cap \overline{\mathcal{J}(\mathcal{B}_{\mathrm{new}}^*)}$**. -/
def InHClosureBNew {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) : Prop :=
  InJClosureBNew H ∧ InJClosureBNew Hᶜ

/-- **Infinite Generator Class $\mathcal{B}_\infty^*$ (`InBInfty H`, Definition 1(5) & Theorem 9 of `main.tex`)**. -/
def InBInfty {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) : Prop :=
  InBNew H ∨
  (∃ k : ℕ, 10 ≤ k ∧ (Nonempty (H ≃g pathGraph k) ∨ Nonempty (H ≃g (pathGraph k)ᶜ))) ∨
  (∃ d : ℕ, 6 ≤ d ∧ (Nonempty (H ≃g SpiderGraph d) ∨ Nonempty (H ≃g (SpiderGraph d)ᶜ))) ∨
  (∃ d : ℕ, 7 ≤ d ∧ (Nonempty (H ≃g BirdDGraph d) ∨ Nonempty (H ≃g (BirdDGraph d)ᶜ))) ∨
  (∃ d : ℕ, 1 ≤ d ∧ (Nonempty (H ≃g SawtoothGraph d) ∨ Nonempty (H ≃g (SawtoothGraph d)ᶜ)))

/-- **Viral Substitution & Leaf-Addition Closure $\mathcal{J}(\mathcal{B}_\infty^*)$ (`InJClosureBInfty`)**. -/
inductive InJClosureBInfty : {W : Type} → [Fintype W] → [DecidableEq W] → SimpleGraph W → Prop where
  | base {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) : InBInfty H → InJClosureBInfty H
  | iso {W₁ W₂ : Type} [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]
      (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂) :
      InJClosureBInfty H₁ → Nonempty (H₁ ≃g H₂) → InJClosureBInfty H₂
  | subst {W₁ W₂ : Type} [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]
      (H₁ : SimpleGraph W₁) (v₀ : W₁) (H₂ : SimpleGraph W₂) :
      InJClosureBInfty H₁ → InJClosureBInfty H₂ → InJClosureBInfty (substGraph H₁ v₀ H₂)
  | add_leaf {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) (v₀ : W) :
      (neighborFinsetIn H v₀ Finset.univ).card ≤ 1 →
      InJClosureBInfty (H.comap (Subtype.val : {v : W // v ≠ v₀} → W)) →
      InJClosureBInfty H

/-- **Symmetric Closure $\mathcal{H}(\mathcal{B}_\infty^*) := \mathcal{J}(\mathcal{B}_\infty^*) \cap \overline{\mathcal{J}(\mathcal{B}_\infty^*)}$**. -/
def InHClosureBInfty {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) : Prop :=
  InJClosureBInfty H ∧ InJClosureBInfty Hᶜ

end ErdosHajnalGen
