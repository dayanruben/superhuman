/-
Copyright 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosHajnal.Defs
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Generalized Definitions for Erdős–Hajnal Beyond $P_6$ (`main.tex`)

This file formalizes the generalized definitions from `main.tex`:
- Paths $P_k$, Co-Paths $\overline{P_k}$, Two-Graph Erdős–Hajnal Property, Polynomial Rödl Property,
  and Kleitman–Winston Virality (`HasPolyRodlProp`, `IsViral`, `HasPairErdosHajnalProp`)
- Vertex Substitution (`substGraph`) and Closures $\mathcal{J}(\mathcal{B}_k^*)$ (`InJClosure`) and
  $\mathcal{H}(\mathcal{B}_k^*)$ (`InHClosure`)
- Co-Combs (`IsCoCombIn`) and Per-Handle $s$-Vertex External Apex Stems (`HasPerHandleApexStems`)
- Coupled Stage-1 Generalized Niceness (`IsCoupledGeneralizedNice`) and Stage-2 Open-Interval
  Thresholded Wonderfulness (`IsThresholdedWonderful`)
- Explicit Pure-Substitution Witnesses $(H_{(7)}, S_{\mathrm{spec}})$, $(H^{(8)}, S^{(8)})$,
  $(H^{(9)}, S^{(9)})$, Caterpillar Co-Tree Witnesses $(H_{\mathrm{tree}}^{(k)}, S^{(k)}) = (\overline{T_k}, S^{(k)})$,
  and $\mathrm{Bird}$ / $E\text{-graph}$ / $H_{\mathrm{Bird}}$
- Hooked-Claw Extensions $\operatorname{Hook}_4(Q)$, $(s, d)$-Brooms $B(s, d)$, and Infinite
  Prime Non-Split Towers $\{H_{t+k}^{(t)}\}_{k \ge 0}$ (`PrimeTowerGraph`, `IsPrimeGraph`, `IsSplitGraph`)
-/

open Filter Finset SimpleGraph Real

namespace ErdosHajnalGen

open ErdosHajnalP6

/-! ### Section 1: Paths, Co-Paths, Polynomial Rödl, and Kleitman–Winston Virality -/

/-- The $k$-vertex path $P_k$ (`SimpleGraph.pathGraph k`). -/
abbrev Pk (k : ℕ) : SimpleGraph (Fin k) := pathGraph k

/-- The complement $\overline{P_k}$ of the $k$-vertex path. -/
abbrev PkCompl (k : ℕ) : SimpleGraph (Fin k) := (pathGraph k)ᶜ

abbrev P7 : SimpleGraph (Fin 7) := pathGraph 7
abbrev P8 : SimpleGraph (Fin 8) := pathGraph 8
abbrev P9 : SimpleGraph (Fin 9) := pathGraph 9

abbrev P7Compl : SimpleGraph (Fin 7) := (pathGraph 7)ᶜ
abbrev P8Compl : SimpleGraph (Fin 8) := (pathGraph 8)ᶜ
abbrev P9Compl : SimpleGraph (Fin 9) := (pathGraph 9)ᶜ

/--
A two-graph family $\{H_1, H_2\}$ satisfies the Erdős–Hajnal property (`HasPairErdosHajnalProp H₁ H₂`)
if there exists $c > 0$ such that every finite graph $G$ that is both induced-$H_1$-free and
induced-$H_2$-free satisfies $\kappa(G) \ge |G|^c$.
-/
def HasPairErdosHajnalProp {W₁ W₂ : Type*} (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂) : Prop :=
  ∃ c > (0 : ℝ), ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    IsInducedSubgraphFree G H₁ → IsInducedSubgraphFree G H₂ →
      (Fintype.card V : ℝ) ^ c ≤ (kappa G : ℝ)

/--
A finite graph $H$ satisfies the polynomial Rödl property (`HasPolyRodlProp H`, Theorem 3(2) of `main.tex`)
if there exists $d > 0$ such that for every $\varepsilon \in (0, 1/2)$ and every induced-$H$-free
finite graph $G$, $G$ contains an $\varepsilon$-restricted vertex subset $S \subseteq V(G)$ of size
$|S| \ge \varepsilon^d |G|$.
-/
def HasPolyRodlProp {W : Type*} (H : SimpleGraph W) : Prop :=
  ∃ d > (0 : ℝ), ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (ε : ℝ),
    0 < ε → ε < 1 / 2 → IsInducedSubgraphFree G H →
      ∃ S : Finset V, IsEpsRestrictedOn G S ε ∧ ε ^ d * (Fintype.card V : ℝ) ≤ (S.card : ℝ)

/--
A two-graph family $\{H_1, H_2\}$ satisfies the polynomial Rödl property (`HasPairPolyRodlProp H₁ H₂`).
-/
def HasPairPolyRodlProp {W₁ W₂ : Type*} (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂) : Prop :=
  ∃ d > (0 : ℝ), ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (ε : ℝ),
    0 < ε → ε < 1 / 2 → IsInducedSubgraphFree G H₁ → IsInducedSubgraphFree G H₂ →
      ∃ S : Finset V, IsEpsRestrictedOn G S ε ∧ ε ^ d * (Fintype.card V : ℝ) ≤ (S.card : ℝ)

/--
`indCopyCount H G` is $\operatorname{ind}_H(G)$ (Theorem 3(3) of `main.tex`): the number of
injective maps $\phi : V(H) \hookrightarrow V(G)$ such that $G.\text{comap } \phi = H$.
-/
noncomputable def indCopyCount {W V : Type*} [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V] (H : SimpleGraph W) (G : SimpleGraph V) : ℕ :=
  by classical exact (Finset.univ.filter (fun g : W ↪ V => G.comap g = H)).card

/--
A finite graph $H$ is viral (`IsViral H`, Theorem 3(3) of `main.tex`) if there exists $d > 0$
such that for every $\varepsilon \in (0, 1/2)$ and every finite graph $G$ satisfying
$\operatorname{ind}_H(G) \le (\varepsilon^d |G|)^{|H|}$, $G$ contains an $\varepsilon$-restricted
vertex subset $S \subseteq V(G)$ with $|S| \ge \varepsilon^d |G|$.
-/
def IsViral {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) : Prop :=
  ∃ d > (0 : ℝ), ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (ε : ℝ),
    0 < ε → ε < 1 / 2 →
      (indCopyCount H G : ℝ) ≤ (ε ^ d * (Fintype.card V : ℝ)) ^ (Fintype.card W) →
        ∃ S : Finset V, IsEpsRestrictedOn G S ε ∧ ε ^ d * (Fintype.card V : ℝ) ≤ (S.card : ℝ)

/--
A two-graph family $\{H_1, H_2\}$ is viral (`IsPairViral H₁ H₂`, Theorem 3(3) of `main.tex`).
-/
def IsPairViral {W₁ W₂ : Type*} [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]
    (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂) : Prop :=
  ∃ d > (0 : ℝ), ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (ε : ℝ),
    0 < ε → ε < 1 / 2 →
      (indCopyCount H₁ G : ℝ) ≤ (ε ^ d * (Fintype.card V : ℝ)) ^ (Fintype.card W₁) →
      (indCopyCount H₂ G : ℝ) ≤ (ε ^ d * (Fintype.card V : ℝ)) ^ (Fintype.card W₂) →
        ∃ S : Finset V, IsEpsRestrictedOn G S ε ∧ ε ^ d * (Fintype.card V : ℝ) ≤ (S.card : ℝ)

/-! ### Section 2: Vertex Substitution $H_1[v_0 \leftarrow H_2]$ (Definition 1(1) of `main.tex`) -/

/--
`substGraph H₁ v₀ H₂` constructs $H_1[v_0 \leftarrow H_2]$ on `{v : V₁ // v ≠ v₀} ⊕ V₂` by replacing
vertex $v_0 \in V_1$ with a disjoint copy of $V_2$ and joining every $x \in V_2$ to $N_{H_1}(v_0)$.
-/
def substGraph {V₁ V₂ : Type*} (H₁ : SimpleGraph V₁) (v₀ : V₁) (H₂ : SimpleGraph V₂) :
    SimpleGraph ({v : V₁ // v ≠ v₀} ⊕ V₂) where
  Adj a b :=
    match a, b with
    | Sum.inl u, Sum.inl w => H₁.Adj u.1 w.1
    | Sum.inr x, Sum.inr y => H₂.Adj x y
    | Sum.inl u, Sum.inr _ => H₁.Adj u.1 v₀
    | Sum.inr _, Sum.inl u => H₁.Adj v₀ u.1
  symm := by
    intro a b h
    cases a <;> cases b <;> first | exact H₁.symm h | exact H₂.symm h
  loopless := by
    intro a
    cases a with
    | inl u => exact H₁.loopless u.1
    | inr x => exact H₂.loopless x

/-! ### Section 3: Weakly Sparse-or-Co-Sparse Blockades, Cograph Patterns, Co-Combs, and Per-Handle $s$-Stems -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
The pair $(A, B)$ is weakly $x$-sparse-or-co-sparse in $G$ (Definition 1(2)-(3) of `main.tex`)
if either $|E_G(A, B)| \le x |A| |B|$ or $|E_{\overline{G}}(A, B)| \le x |A| |B|$.
-/
def IsWeaklySparseOrCoSparsePair (G : SimpleGraph V) (A B : Finset V) (x : ℝ) : Prop :=
  IsWeaklySparsePair G A B x ∨ IsWeaklySparsePair Gᶜ A B x

/--
A blockade $B : \text{Fin } k \to \text{Finset } V$ inside $S \subseteq V$ is weakly
$x$-sparse-or-co-sparse in $G$ (`IsWeaklySparseOrCoSparseBlockadeIn G S k w x B`).
-/
def IsWeaklySparseOrCoSparseBlockadeIn (G : SimpleGraph V) (S : Finset V) (k : ℕ) (w x : ℝ)
    (B : Fin k → Finset V) : Prop :=
  IsBlockadeIn G S k w B ∧ ∀ i j : Fin k, i ≠ j → IsWeaklySparseOrCoSparsePair G (B i) (B j) x

/--
The pattern graph $J$ on $\text{Fin } k$ of a pairwise-pure blockade $B$, where $ij \in E(J)$
if and only if $i \neq j$ and $(B_i, B_j)$ is complete in $G$.
-/
def purePatternGraph (G : SimpleGraph V) {k : ℕ} (B : Fin k → Finset V) : SimpleGraph (Fin k) where
  Adj i j := i ≠ j ∧ IsCompletePair G (B i) (B j)
  symm _ _ := fun ⟨hne, hcomp⟩ => ⟨hne.symm, fun u hu v hv => G.symm (hcomp v hv u hu)⟩
  loopless _ := fun ⟨hne, _⟩ => hne rfl

/--
A pairwise-pure $(k, w)$-blockade in $G$ inside $S$ whose pattern graph is a cograph ($P_4$-free).
-/
def IsPureCographBlockadeIn (G : SimpleGraph V) (S : Finset V) (k : ℕ) (w : ℝ)
    (B : Fin k → Finset V) : Prop :=
  IsPureBlockadeIn G S k w B ∧ IsInducedSubgraphFree (purePatternGraph G B) (pathGraph 4)

/--
An $(\ell, w)$-co-comb in $G$ inside $S \subseteq V$ (Definition 1(4) of `main.tex`):
each handle $a_i$ is anticomplete in $G$ to $B_i$ and complete in $G$ to $B_j$ for all $j \neq i$.
-/
structure IsCoCombIn (G : SimpleGraph V) (S : Finset V) (ℓ : ℕ) (w : ℝ)
    (a : Fin ℓ → V) (B : Fin ℓ → Finset V) : Prop where
  is_blockade : IsBlockadeIn G S ℓ w B
  apex_in_ambient : ∀ i : Fin ℓ, a i ∈ S
  apex_injective : Function.Injective a
  apex_disjoint_blocks : ∀ i j : Fin ℓ, a i ∉ B j
  apex_anticomplete_own : ∀ i : Fin ℓ, ∀ u ∈ B i, ¬G.Adj (a i) u
  apex_complete_other : ∀ i j : Fin ℓ, i ≠ j → ∀ u ∈ B j, G.Adj (a i) u

/--
`IsCombOrCoCombIn G S ℓ w a B` holds when $((a_i, B_i) : i \in [\ell])$ is either an $(\ell, w)$-comb
or an $(\ell, w)$-co-comb in $G$ inside $S$.
-/
def IsCombOrCoCombIn (G : SimpleGraph V) (S : Finset V) (ℓ : ℕ) (w : ℝ)
    (a : Fin ℓ → V) (B : Fin ℓ → Finset V) : Prop :=
  IsCombIn G S ℓ w a B ∨ IsCoCombIn G S ℓ w a B

/--
Per-handle $s$-vertex external apex stems $\{\mathbf{v}^{(i)} = (v_1^{(i)}, \dots, v_s^{(i)}) : i \in [\ell]\}$
for a comb or co-comb $(a, B)$ in $G$ inside $S$ (Definition 1(4) `(Stem-1)`–`(Stem-3)` of `main.tex`):
- Every stem vertex lies in $S \setminus (\{a_1, \dots, a_\ell\} \cup \bigcup_q B_q)$ and each
  $\mathbf{v}^{(i)} : \text{Fin } s \hookrightarrow V$ is injective;
- **(Stem-1)**: $\overline{G}[\{v_1^{(i)}, \dots, v_s^{(i)}\}]$ is the induced path
  $(v_1^{(i)} - \dots - v_s^{(i)}) \cong P_s$;
- **(Stem-2)**: the last stem vertex $v_s^{(i)}$ (`r.1 + 1 = s`) is non-adjacent in $G$ to $a_i$,
  and every earlier stem vertex $v_r^{(i)}$ (`r.1 + 1 < s`) is adjacent in $G$ to $a_i$;
- **(Stem-3)**: every stem vertex $v_r^{(i)}$ is complete in $G$ to $\bigcup_{q=1}^\ell B_q$.
-/
structure HasPerHandleApexStems (G : SimpleGraph V) (S : Finset V) (ℓ s : ℕ)
    (a : Fin ℓ → V) (B : Fin ℓ → Finset V) (stems : Fin ℓ → Fin s → V) : Prop where
  stem_pos : 1 ≤ s
  stem_in_ambient : ∀ (i : Fin ℓ) (r : Fin s), stems i r ∈ S
  stem_injective : ∀ i : Fin ℓ, Function.Injective (stems i)
  stem_not_handle : ∀ (i j : Fin ℓ) (r : Fin s), stems i r ≠ a j
  stem_not_in_blocks : ∀ (i j : Fin ℓ) (r : Fin s), stems i r ∉ B j
  stem_induced_path_compl : ∀ (i : Fin ℓ) (r₁ r₂ : Fin s),
    Gᶜ.Adj (stems i r₁) (stems i r₂) ↔ (pathGraph s).Adj r₁ r₂
  stem_last_nonadj_handle : ∀ (i : Fin ℓ) (r : Fin s), r.1 + 1 = s → ¬G.Adj (stems i r) (a i)
  stem_init_adj_handle : ∀ (i : Fin ℓ) (r : Fin s), r.1 + 1 < s → G.Adj (stems i r) (a i)
  stem_complete_to_blocks : ∀ (i q : Fin ℓ) (r : Fin s), ∀ u ∈ B q, G.Adj (stems i r) u

/-! ### Section 4: Coupled Generalized Niceness and Thresholded Wonderfulness (Definition 2(3)-(4)) -/

/--
Single-graph coupled generalized niceness (`IsCoupledGeneralizedNice H`, Definition 2(3) of `main.tex`):
there exist constants $c_1, \dots, c_9 > 0$ such that for every $\varepsilon \in (0, 1/2)$,
every coupled cross-block sparsity $x_{\mathrm{sp}} \in [\varepsilon^{3 c_2}, \varepsilon^{c_7}]$,
and every $\overline{H}$-free graph $G$, at least one of `(GN1)`–`(GN4)` holds.
-/
def IsCoupledGeneralizedNice {W : Type*} (H : SimpleGraph W) : Prop :=
  ∃ (c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ : ℝ),
    0 < c₁ ∧ 0 < c₂ ∧ 0 < c₃ ∧ 0 < c₄ ∧ 0 < c₅ ∧ 0 < c₆ ∧ 0 < c₇ ∧ 0 < c₈ ∧ 0 < c₉ ∧
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (ε x_sp : ℝ),
      0 < ε → ε < 1 / 2 →
      ε ^ (3 * c₂) ≤ x_sp → x_sp ≤ ε ^ c₇ →
      IsInducedSubgraphFree G Hᶜ →
        -- (GN1)
        (∃ B : Fin ⌈ε⁻¹⌉₊ → Finset V,
          IsWeaklySparseOrCoSparseBlockadeIn G Finset.univ ⌈ε⁻¹⌉₊
            (⌊ε ^ c₁ * (Fintype.card V : ℝ)⌋₊ : ℝ) x_sp B) ∨
        -- (GN2)
        ((ε ^ c₃ * x_sp ^ c₃ * (Fintype.card V : ℝ)) ^ c₄ ≤ (kappa G : ℝ)) ∨
        -- (GN3)
        (∃ k : ℕ, ⌈ε ^ (-c₆)⌉₊ ≤ k ∧ k ≤ ⌈ε ^ (-c₉)⌉₊ ∧
          ∃ B : Fin k → Finset V,
            IsPureCographBlockadeIn G Finset.univ k ((Fintype.card V : ℝ) / (k : ℝ) ^ c₅) B) ∨
        -- (GN4)
        (∃ S : Finset V, IsEpsRestrictedOn G S (2 * ε ^ c₇) ∧
          ε ^ c₈ * (Fintype.card V : ℝ) ≤ (S.card : ℝ))

/--
Two-graph coupled generalized niceness (`IsPairCoupledGeneralizedNice H₁ H₂`, Definition 2(3) of `main.tex`)
for a family $\{H_1, H_2\}$ (so $G$ is $\{\overline{H_1}, \overline{H_2}\}$-free).
-/
def IsPairCoupledGeneralizedNice {W₁ W₂ : Type*} (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂) : Prop :=
  ∃ (c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ : ℝ),
    0 < c₁ ∧ 0 < c₂ ∧ 0 < c₃ ∧ 0 < c₄ ∧ 0 < c₅ ∧ 0 < c₆ ∧ 0 < c₇ ∧ 0 < c₈ ∧ 0 < c₉ ∧
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (ε x_sp : ℝ),
      0 < ε → ε < 1 / 2 →
      ε ^ (3 * c₂) ≤ x_sp → x_sp ≤ ε ^ c₇ →
      IsInducedSubgraphFree G H₁ᶜ → IsInducedSubgraphFree G H₂ᶜ →
        (∃ B : Fin ⌈ε⁻¹⌉₊ → Finset V,
          IsWeaklySparseOrCoSparseBlockadeIn G Finset.univ ⌈ε⁻¹⌉₊
            (⌊ε ^ c₁ * (Fintype.card V : ℝ)⌋₊ : ℝ) x_sp B) ∨
        ((ε ^ c₃ * x_sp ^ c₃ * (Fintype.card V : ℝ)) ^ c₄ ≤ (kappa G : ℝ)) ∨
        (∃ k : ℕ, ⌈ε ^ (-c₆)⌉₊ ≤ k ∧ k ≤ ⌈ε ^ (-c₉)⌉₊ ∧
          ∃ B : Fin k → Finset V,
            IsPureCographBlockadeIn G Finset.univ k ((Fintype.card V : ℝ) / (k : ℝ) ^ c₅) B) ∨
        (∃ S : Finset V, IsEpsRestrictedOn G S (2 * ε ^ c₇) ∧
          ε ^ c₈ * (Fintype.card V : ℝ) ≤ (S.card : ℝ))

/--
Open-interval thresholded wonderfulness (`IsThresholdedWonderful H`, Definition 2(4) of `main.tex`):
there exist $a \ge 7$ and $y_{\mathrm{thr}} \in (0, 1/4]$ such that for every $y \in (0, y_{\mathrm{thr}}]$,
every $\overline{H}$-free graph $G$, and every equal-sized anticonnected complete-or-two-sided-$\delta_{\mathrm{cross}}$-sparse
$(\ell, w)$-blockade $\mathcal{B} = (B_1, \dots, B_\ell)$ in $G$ with $\ell \ge y^{-a}$,
$\delta_{\mathrm{cross}} \in (0, \min(y^a, \frac{1}{8\ell^2})]$, and $w = |B_1| = \dots = |B_\ell| \ge 1$,
either `(W1)` $G$ contains a $y^4$-restricted induced subgraph of order $\ge w$, or `(W2)` there exists
$i^* \in [\ell]$ such that at most $y|G|$ external vertices $v \notin \bigcup_i B_i$ satisfy
$0 < |N_G(v) \cap B_{i^*}| < \frac{1}{2}|B_{i^*}|$.
-/
def IsThresholdedWonderful {W : Type*} (H : SimpleGraph W) : Prop :=
  ∃ (a : ℕ) (y_thr : ℝ), 7 ≤ a ∧ 0 < y_thr ∧ y_thr ≤ 1 / 4 ∧
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      (y δ_cross : ℝ) (ℓ w : ℕ) (B : Fin ℓ → Finset V),
      0 < y → y ≤ y_thr →
      IsInducedSubgraphFree G Hᶜ →
      y ^ (-(a : ℝ)) ≤ (ℓ : ℝ) →
      0 < δ_cross → δ_cross ≤ min (y ^ a) (1 / (8 * (ℓ : ℝ) ^ 2)) →
      1 ≤ w →
      IsCompleteOrXSparseBlockadeIn G Finset.univ ℓ (w : ℝ) δ_cross B →
      (∀ i : Fin ℓ, (B i).card = w ∧ IsAnticonnected G (B i)) →
        -- (W1)
        (∃ S : Finset V, IsEpsRestrictedOn G S (y ^ 4) ∧ (w : ℝ) ≤ (S.card : ℝ)) ∨
        -- (W2)
        (∃ i_star : Fin ℓ,
          (((Finset.univ \ Finset.biUnion Finset.univ B).filter (fun v =>
            0 < (neighborFinsetIn G v (B i_star)).card ∧
            ((neighborFinsetIn G v (B i_star)).card : ℝ) < (1 / 2) * (w : ℝ))).card : ℝ) ≤
            y * (Fintype.card V : ℝ))

/-! ### Section 5: Stage-1 Exponents $D_r$ and $E_r$ and Inductive Depth-$r$ Comb/Co-Comb Dichotomy -/

/--
Split-tree exponent sequence $D_r$ from Theorem 7 of `main.tex`:
$D_1 = 8$, $D_2 = 64$, and $D_r = 256 \cdot 8^{r-3}$ for $r \ge 3$ (with $D_0 := 8$).
-/
def splitTreeD : ℕ → ℕ
  | 0 => 8
  | 1 => 8
  | 2 => 64
  | r + 3 => 256 * 8 ^ r

/--
Decoupled cap exponent $E_r := 8 r \cdot 16^r$ from Theorem 7 of `main.tex`.
-/
def capExpE (r : ℕ) : ℕ :=
  8 * r * 16 ^ r

/--
Minimum tooth width $w_{\min}(r, \eta_{\mathrm{out}}, p_{\mathrm{cap}}) := 2^{400 r^2} \eta_{\mathrm{out}}^{-3r} p_{\mathrm{cap}}^{E_r + 2 D_r}$
from Theorem 7(1) (`Proposition 2_r`) of `main.tex`.
-/
noncomputable def combMinWidth (r : ℕ) (η_out : ℝ) (p_cap : ℕ) : ℝ :=
  (2 : ℝ) ^ (400 * r ^ 2) * η_out ^ (-(3 * (r : ℝ))) * (p_cap : ℝ) ^ (capExpE r + 2 * splitTreeD r)

/--
The inductive depth-$r$ Stage-1 Comb/Co-Comb Dichotomy (`Stage1CombCoCombDichotomyAt r`,
Theorem 7(1) / `Proposition 2_r` of `main.tex`):
For every $s \ge 1$, $p_{\mathrm{cap}} \ge \ell \ge 64$, $L_{\max} \in [2, \ell]$, $\eta_{\mathrm{out}} \in (0, 2^{-16}]$,
and every $\overline{P_{s+4+r}}$-free graph $F$ containing an $(\ell, w)$-comb or $(\ell, w)$-co-comb
$((a_i, B_i) : i \in [\ell])$ inside $S \subseteq V(F)$ equipped with per-handle $s$-vertex external
apex stems and $w \ge w_{\min}(r, \eta_{\mathrm{out}}, p_{\mathrm{cap}})$, the union $\bigsqcup_{i=1}^\ell B_i$
contains either:
- **(P2$_r$-SplitOrCross)**: a weakly $\eta_{\mathrm{out}}$-sparse-or-co-sparse
  $(k, \frac{w}{2^{60r} k^{3 D_r}})$-blockade for some $k \in [L_{\max}, p_{\mathrm{cap}}]$; or
- **(P2$_r$-Cap)**: a weakly $\eta_{\mathrm{out}}$-sparse-or-co-sparse
  $(p_{\mathrm{cap}}, 2^{-200 r^2} \eta_{\mathrm{out}}^r p_{\mathrm{cap}}^{-E_r} w)$-blockade of exact length $p_{\mathrm{cap}}$.
-/
def Stage1CombCoCombDichotomyAt (r : ℕ) : Prop :=
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
      -- (P2_r-SplitOrCross)
      (∃ k : ℕ, L_max ≤ k ∧ k ≤ p_cap ∧
        ∃ U : Fin k → Finset V,
          IsWeaklySparseOrCoSparseBlockadeIn F U_ambient k
            (w / ((2 : ℝ) ^ (60 * r) * (k : ℝ) ^ (3 * splitTreeD r))) η_out U) ∨
      -- (P2_r-Cap)
      (∃ U : Fin p_cap → Finset V,
        IsWeaklySparseOrCoSparseBlockadeIn F U_ambient p_cap
          ((2 : ℝ) ^ (-(200 * (r : ℝ) ^ 2)) * η_out ^ r * (p_cap : ℝ) ^ (-(capExpE r : ℝ)) * w)
          η_out U)

/-! ### Section 6: Explicit Pure-Substitution Witnesses $H_{(7)}, H^{(8)}, H^{(9)}$ and Caterpillar Tree $T_k$ -/

/--
Projection map `projH7 : Fin 10 → Fin 6` for the 10-vertex pure-substitution witness $H_{(7)}$
(Proposition 3 of `main.tex`), mapping 0-indexed `0..9` (representing paper vertices `1..10`)
onto the 6-vertex path $P_6 = (0 - 1 - 2 - 3 - 4 - 5)$ (`1 - 2 - 5 - 7 - 3 - 4`):
- `{0, 8}` (`{1, 9}`) $\mapsto 0$ ($\overline{K_2}$-substitution at `1`)
- `{1, 9}` (`{2, 10}`) $\mapsto 1$ ($K_2$-substitution at `2`)
- `4` (`5`) $\mapsto 2$
- `6` (`7`) $\mapsto 3$
- `{2, 7}` (`{3, 8}`) $\mapsto 4$ ($K_2$-substitution at `3`)
- `{3, 5}` (`{4, 6}`) $\mapsto 5$ ($\overline{K_2}$-substitution at `4`).
-/
def projH7 : Fin 10 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 4
  | 3 => 5
  | 4 => 2
  | 5 => 5
  | 6 => 3
  | 7 => 4
  | 8 => 0
  | 9 => 1

/--
The 10-vertex pure-substitution witness graph $H_{(7)}$ (`witnessH7 : SimpleGraph (Fin 10)`)
from Proposition 3 of `main.tex`, with special vertex set `specH7 = {0, 1, 2, 3}` (`{1, 2, 3, 4}`).
-/
def witnessH7 : SimpleGraph (Fin 10) where
  Adj u v := u ≠ v ∧
    (if projH7 u = projH7 v then (projH7 u = 1 ∨ projH7 u = 4)
     else P6Compl.Adj (projH7 u) (projH7 v))
  symm u v := by
    rintro ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    by_cases heq : projH7 u = projH7 v
    · rw [if_pos heq] at h
      rw [if_pos heq.symm, ← heq]
      exact h
    · rw [if_neg heq] at h
      rw [if_neg (Ne.symm heq)]
      exact P6Compl.symm h
  loopless u := fun ⟨hne, _⟩ => hne rfl

/-- Special vertex set $S_{\mathrm{spec}} = \{1, 2, 3, 4\}$ (`{0, 1, 2, 3 : Fin 10}`) of `witnessH7`. -/
def specH7 : Finset (Fin 10) := {0, 1, 2, 3}

/--
Projection map `projH8 : Fin 11 → Fin 7` for the 11-vertex pure-substitution witness $H^{(8)}$
(Proposition 5(2) of `main.tex`), mapping `{p₁, p₂, p₃, 2, 3, p₄, 6, p₁*, p₂', 7, 5}` (`0..10`)
onto $P_7 = (p_1 - p_2 - p_3 - p_4 - 6 - 2 - 3)$ (`0..6`):
- `{0, 7}` (`{p₁, p₁*}`) $\mapsto 0$ ($\overline{K_2}$-substitution at $p_1$)
- `{1, 8}` (`{p₂, p₂'}`) $\mapsto 1$ ($K_2$-substitution at $p_2$)
- `2` (`p₃`) $\mapsto 2$
- `5` (`p₄`) $\mapsto 3$
- `6` (`6`) $\mapsto 4$
- `{3, 9}` (`{2, 7}`) $\mapsto 5$ ($K_2$-substitution at $2$)
- `{4, 10}` (`{3, 5}`) $\mapsto 6$ ($\overline{K_2}$-substitution at $3$).
-/
def projH8 : Fin 11 → Fin 7
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 5
  | 4 => 6
  | 5 => 3
  | 6 => 4
  | 7 => 0
  | 8 => 1
  | 9 => 5
  | 10 => 6

/--
The 11-vertex pure-substitution witness graph $H^{(8)}$ (`witnessH8 : SimpleGraph (Fin 11)`)
from Proposition 5(2) of `main.tex`, with special vertex set `specH8 = {0, 1, 2, 3, 4}` (`{p₁, p₂, p₃, 2, 3}`).
-/
def witnessH8 : SimpleGraph (Fin 11) where
  Adj u v := u ≠ v ∧
    (if projH8 u = projH8 v then (projH8 u = 1 ∨ projH8 u = 5)
     else P7Compl.Adj (projH8 u) (projH8 v))
  symm u v := by
    rintro ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    by_cases heq : projH8 u = projH8 v
    · rw [if_pos heq] at h
      rw [if_pos heq.symm, ← heq]
      exact h
    · rw [if_neg heq] at h
      rw [if_neg (Ne.symm heq)]
      exact P7Compl.symm h
  loopless u := fun ⟨hne, _⟩ => hne rfl

/-- Special vertex set $S^{(8)} = \{p_1, p_2, p_3, 2, 3\}$ (`{0, 1, 2, 3, 4 : Fin 11}`) of `witnessH8`. -/
def specH8 : Finset (Fin 11) := {0, 1, 2, 3, 4}

/--
Projection map `projArm9 : Fin 10 → Fin 8` for each 10-vertex arm $\operatorname{Arm}_X$ ($X \in \{L, R\}$)
of the 20-vertex two-arm witness $H^{(9)}$ (Proposition 5(3) of `main.tex`), mapping
`{X₁, ..., X₈, X₁*, X₂'}` (`0..9`) onto $P_8 = (X_1 - \dots - X_8)$ (`0..7`):
- `{0, 8}` (`{X₁, X₁*}`) $\mapsto 0$ ($\overline{K_2}$-substitution at $X_1$)
- `{1, 9}` (`{X₂, X₂'}`) $\mapsto 1$ ($K_2$-substitution at $X_2$)
- `r` (`2..7`) $\mapsto r$.
-/
def projArm9 : Fin 10 → Fin 8
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
  | 8 => 0
  | 9 => 1

/--
The 20-vertex symmetric two-arm pure-substitution witness graph
$H^{(9)} := K_2[1 \leftarrow \operatorname{Arm}_L, 2 \leftarrow \operatorname{Arm}_R]$
(`witnessH9 : SimpleGraph (Fin 20)`, Proposition 5(3) of `main.tex`), where `0..9` is $\operatorname{Arm}_L$
and `10..19` is $\operatorname{Arm}_R$, and the two arms are $100\%$ complete to each other in $H^{(9)}$.
-/
def witnessH9 : SimpleGraph (Fin 20) where
  Adj u v := u ≠ v ∧
    (if (u.1 < 10 ↔ v.1 < 10) then
      let u' : Fin 10 := ⟨u.1 % 10, Nat.mod_lt u.1 (by decide)⟩
      let v' : Fin 10 := ⟨v.1 % 10, Nat.mod_lt v.1 (by decide)⟩
      if projArm9 u' = projArm9 v' then projArm9 u' = 1
      else P8Compl.Adj (projArm9 u') (projArm9 v')
     else True)
  symm u v := by
    rintro ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    by_cases h_same : (u.1 < 10 ↔ v.1 < 10)
    · rw [if_pos h_same] at h
      rw [if_pos h_same.symm]
      dsimp only at h ⊢
      set u' : Fin 10 := ⟨u.1 % 10, Nat.mod_lt u.1 (by decide)⟩
      set v' : Fin 10 := ⟨v.1 % 10, Nat.mod_lt v.1 (by decide)⟩
      by_cases heq : projArm9 u' = projArm9 v'
      · rw [if_pos heq] at h
        rw [if_pos heq.symm, ← heq]
        exact h
      · rw [if_neg heq] at h
        rw [if_neg (Ne.symm heq)]
        exact P8Compl.symm h
    · rw [if_neg (fun h' => h_same h'.symm)]
      trivial
  loopless u := fun ⟨hne, _⟩ => hne rfl

/--
The 6-vertex special set $S^{(9)} = \{L_1, L_2, L_3, R_1, R_2, R_3\}$ (`{0, 1, 2, 10, 11, 12 : Fin 20}`)
of `witnessH9` (Proposition 5(3) of `main.tex`).
-/
def specH9 : Finset (Fin 20) := {0, 1, 2, 10, 11, 12}

/--
Vertex type `CaterpillarVert k` of the caterpillar tree $T_k$ ($k \ge 6$, Proposition 5(1) of `main.tex`):
- `Sum.inl (r : Fin (k - 4))`: spine vertices $p_1, \dots, p_{k-4}$ (`r.1 = 0 .. k - 5`)
- `Sum.inr (Sum.inl (x : Fin 6))`: the 6 fixed vertices `(6, 2, a₁, a₂, 3, 7)` (`x = 0..5`)
- `Sum.inr (Sum.inr ⟨⟨r, hr⟩, j⟩)`: pendant path vertices $u_{i, j.1 + 1}$ where $i = r.1 + 1 \in \{2, \dots, k - 4\}$
  (`1 ≤ r.1`) and $1 \le j.1 + 1 \le i$ (`j : Fin (r.1 + 1)`).
For $k \ge 6$, `Fintype.card (CaterpillarVert k) = Nat.choose (k - 2) 2 + 4`.
-/
abbrev CaterpillarVert (k : ℕ) : Type :=
  Fin (k - 4) ⊕ Fin 6 ⊕ Σ r : {r : Fin (k - 4) // 1 ≤ r.1}, Fin (r.1.1 + 1)

/--
Symmetric adjacency predicate for the caterpillar tree $T_k$ (`CaterpillarTree k`, Proposition 5(1) of `main.tex`):
- Spine path: $(p_1 - \dots - p_{k-4} - 6 - 2 - a_1 - a_2)$
- Branch at $2$: $(2 - 3 - 7)$
- Pendant paths: for each $i = r.1 + 1 \in \{2, \dots, k - 4\}$, $(p_i - u_{i,1} - \dots - u_{i,i})$.
-/
def caterpillarAdjAux (k : ℕ) (u v : CaterpillarVert k) : Prop :=
  match u, v with
  | Sum.inl r₁, Sum.inl r₂ => r₁.1 + 1 = r₂.1 ∨ r₂.1 + 1 = r₁.1
  | Sum.inl r, Sum.inr (Sum.inl x) => (r.1 + 1 = k - 4 ∧ x = 0)
  | Sum.inr (Sum.inl x), Sum.inl r => (r.1 + 1 = k - 4 ∧ x = 0)
  | Sum.inr (Sum.inl x), Sum.inr (Sum.inl y) =>
      (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) ∨
      (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 1) ∨
      (x = 2 ∧ y = 3) ∨ (x = 3 ∧ y = 2) ∨
      (x = 1 ∧ y = 4) ∨ (x = 4 ∧ y = 1) ∨
      (x = 4 ∧ y = 5) ∨ (x = 5 ∧ y = 4)
  | Sum.inl r', Sum.inr (Sum.inr ⟨⟨r, _⟩, j⟩) => r' = r ∧ j.1 = 0
  | Sum.inr (Sum.inr ⟨⟨r, _⟩, j⟩), Sum.inl r' => r' = r ∧ j.1 = 0
  | Sum.inr (Sum.inr ⟨⟨r₁, _⟩, j₁⟩), Sum.inr (Sum.inr ⟨⟨r₂, _⟩, j₂⟩) =>
      r₁ = r₂ ∧ (j₁.1 + 1 = j₂.1 ∨ j₂.1 + 1 = j₁.1)
  | _, _ => False

/--
The caterpillar tree $T_k$ (`CaterpillarTree k`, Proposition 5(1) of `main.tex`).
-/
def CaterpillarTree (k : ℕ) : SimpleGraph (CaterpillarVert k) where
  Adj u v := caterpillarAdjAux k u v
  symm := by
    intro u v h
    match u, v with
    | Sum.inl r₁, Sum.inl r₂ => exact h.symm
    | Sum.inl r, Sum.inr (Sum.inl x) => exact h
    | Sum.inr (Sum.inl x), Sum.inl r => exact h
    | Sum.inr (Sum.inl x), Sum.inr (Sum.inl y) =>
        rcases h with h | h | h | h | h | h | h | h | h | h
        · exact Or.inr (Or.inl ⟨h.2, h.1⟩)
        · exact Or.inl ⟨h.2, h.1⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩)))
        · exact Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩)))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h.2, h.1⟩))))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩))))))))
    | Sum.inl r', Sum.inr (Sum.inr ⟨⟨r, _⟩, j⟩) => exact h
    | Sum.inr (Sum.inr ⟨⟨r, _⟩, j⟩), Sum.inl r' => exact h
    | Sum.inr (Sum.inr ⟨⟨r₁, _⟩, j₁⟩), Sum.inr (Sum.inr ⟨⟨r₂, _⟩, j₂⟩) =>
        exact ⟨h.1.symm, h.2.symm⟩
    | Sum.inr (Sum.inl _), Sum.inr (Sum.inr _) => exact False.elim h
    | Sum.inr (Sum.inr _), Sum.inr (Sum.inl _) => exact False.elim h
  loopless := by
    intro u
    rcases u with r | (x | ⟨⟨r, hr⟩, j⟩)
    · simp [caterpillarAdjAux]
    · simp [caterpillarAdjAux]; fin_cases x <;> decide
    · simp [caterpillarAdjAux]

/--
The caterpillar co-tree witness $H_{\mathrm{tree}}^{(k)} := \overline{T_k}$ (`witnessHTree k`).
-/
abbrev witnessHTree (k : ℕ) : SimpleGraph (CaterpillarVert k) := (CaterpillarTree k)ᶜ

/-! ### Section 7: $\mathrm{Bird}$, $E\text{-graph}$, Hooked-Claws, Brooms, Closures, and Prime Towers -/

/--
The 6-vertex prime graph $\mathrm{Bird}$ (`BirdGraph : SimpleGraph (Fin 6)`, Section 2 & Proposition 6(1a) of `main.tex`)
on $\{b_1, b_2, b_3, b_4, b_5, b_6\}$ (`0..5 : Fin 6`), consisting of:
- triangle $\{b_1, b_2, b_3\}$ (`{0, 1, 2}`),
- 2-edge path $b_1 - b_4 - b_5$ (`0 - 3 - 4`), and
- 1-edge pendant leaf $b_2 - b_6$ (`1 - 5`).
-/
def BirdGraph : SimpleGraph (Fin 6) where
  Adj u v :=
    (u = 0 ∧ (v = 1 ∨ v = 2 ∨ v = 3)) ∨
    (v = 0 ∧ (u = 1 ∨ u = 2 ∨ u = 3)) ∨
    (u = 1 ∧ (v = 2 ∨ v = 5)) ∨
    (v = 1 ∧ (u = 2 ∨ u = 5)) ∨
    (u = 3 ∧ v = 4) ∨
    (v = 3 ∧ u = 4)
  symm := by intro u v; tauto
  loopless := by intro u; fin_cases u <;> decide

/--
The 6-vertex tree $E\text{-graph}$ (`EGraph : SimpleGraph (Fin 6)`, Proposition 6(1a) of `main.tex`)
with 5-vertex spine $(v_1 - v_2 - v_3 - v_4 - v_5)$ (`0 - 1 - 2 - 3 - 4`) and pendant leaf $v_3'$ (`5`)
attached at $v_3$ (`2`).
-/
def EGraph : SimpleGraph (Fin 6) where
  Adj u v :=
    (u.1 < 5 ∧ v.1 < 5 ∧ (u.1 + 1 = v.1 ∨ v.1 + 1 = u.1)) ∨
    (u = 2 ∧ v = 5) ∨ (u = 5 ∧ v = 2)
  symm := by intro u v; tauto
  loopless := by intro u; fin_cases u <;> decide

/--
The 5-vertex cycle $C_5$ (`C5Graph : SimpleGraph (Fin 5)`).
-/
def C5Graph : SimpleGraph (Fin 5) where
  Adj u v := (u.1 + 1) % 5 = v.1 ∨ (v.1 + 1) % 5 = u.1
  symm := by intro u v; tauto
  loopless := by intro u; fin_cases u <;> decide

/--
Generator predicate `InBStar k H` for $\mathcal{B}_k^* := \{K_1, K_2, \overline{K_2}, \mathrm{Bird}, \overline{\mathrm{Bird}}\} \cup \{P_t, \overline{P_t} : 1 \le t \le k\}$
(Section 2 of `main.tex`).
-/
def InBStar (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) : Prop :=
  Nonempty (H ≃g (⊤ : SimpleGraph (Fin 1))) ∨
  Nonempty (H ≃g (⊤ : SimpleGraph (Fin 2))) ∨
  Nonempty (H ≃g (⊥ : SimpleGraph (Fin 2))) ∨
  Nonempty (H ≃g BirdGraph) ∨
  Nonempty (H ≃g BirdGraphᶜ) ∨
  ∃ t : ℕ, 1 ≤ t ∧ t ≤ k ∧ (Nonempty (H ≃g pathGraph t) ∨ Nonempty (H ≃g (pathGraph t)ᶜ))

/--
Inductive closure $\mathcal{J}(\mathcal{B}_k^*)$ (`InJClosure k`, Section 2 & Theorem 4(3) of `main.tex`):
the smallest class of finite graphs containing $\mathcal{B}_k^*$, closed under graph isomorphism,
vertex substitution $H_1[v_0 \leftarrow H_2]$ (`substGraph`), and adding a vertex $v_0$ of degree at most $1$.
-/
inductive InJClosure (k : ℕ) : ∀ {W : Type} [Fintype W] [DecidableEq W], SimpleGraph W → Prop
  | base {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) :
      InBStar k H → InJClosure k H
  | iso {W₁ W₂ : Type} [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]
      (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂) :
      InJClosure k H₁ → Nonempty (H₁ ≃g H₂) → InJClosure k H₂
  | subst {W₁ W₂ : Type} [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]
      (H₁ : SimpleGraph W₁) (v₀ : W₁) (H₂ : SimpleGraph W₂) :
      InJClosure k H₁ → InJClosure k H₂ → InJClosure k (substGraph H₁ v₀ H₂)
  | add_leaf {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) (v₀ : W) :
      (neighborFinsetIn H v₀ Finset.univ).card ≤ 1 →
      InJClosure k (H.comap (Subtype.val : {v : W // v ≠ v₀} → W)) →
      InJClosure k H

/--
Single-graph symmetric closure $\mathcal{H}(\mathcal{B}_k^*) := \mathcal{J}(\mathcal{B}_k^*) \cap \overline{\mathcal{J}(\mathcal{B}_k^*)}$
(`InHClosure k`, Section 2 & Proposition 6(1b) of `main.tex`).
-/
def InHClosure (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) : Prop :=
  InJClosure k H ∧ InJClosure k Hᶜ

/--
Inductive closure $\mathcal{J}(\{K_1, K_2, \overline{K_2}, C_5\})$ (`InJClosureC5`, Proposition 6(3) of `main.tex`).
-/
inductive InJClosureC5 : ∀ {W : Type} [Fintype W] [DecidableEq W], SimpleGraph W → Prop
  | k1 : InJClosureC5 (⊤ : SimpleGraph (Fin 1))
  | k2 : InJClosureC5 (⊤ : SimpleGraph (Fin 2))
  | k2_compl : InJClosureC5 (⊥ : SimpleGraph (Fin 2))
  | c5 : InJClosureC5 C5Graph
  | iso {W₁ W₂ : Type} [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]
      (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂) :
      InJClosureC5 H₁ → Nonempty (H₁ ≃g H₂) → InJClosureC5 H₂
  | subst {W₁ W₂ : Type} [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]
      (H₁ : SimpleGraph W₁) (v₀ : W₁) (H₂ : SimpleGraph W₂) :
      InJClosureC5 H₁ → InJClosureC5 H₂ → InJClosureC5 (substGraph H₁ v₀ H₂)
  | add_leaf {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) (v₀ : W) :
      (neighborFinsetIn H v₀ Finset.univ).card ≤ 1 →
      InJClosureC5 (H.comap (Subtype.val : {v : W // v ≠ v₀} → W)) →
      InJClosureC5 H

/--
Hooked-claw extension $\operatorname{Hook}_4(Q)$ (`Hook4Graph Q S`, Section 2 & Proposition 6(2a) of `main.tex`):
disjoint union of $Q$ and a 4-vertex path $(u_1 - u_2 - u_3 - u_4) \cong P_4$ (`Fin 4`), where
$u_1$ (`0 : Fin 4`) is complete to a non-empty subset $S \subseteq V(Q)$ while $u_2, u_3, u_4$
(`1, 2, 3 : Fin 4`) are anticomplete to $V(Q)$.
-/
def Hook4Graph {W : Type*} (Q : SimpleGraph W) (S : Set W) : SimpleGraph (W ⊕ Fin 4) where
  Adj a b :=
    match a, b with
    | Sum.inl x, Sum.inl y => Q.Adj x y
    | Sum.inr i, Sum.inr j => (pathGraph 4).Adj i j
    | Sum.inl x, Sum.inr i => i = 0 ∧ x ∈ S
    | Sum.inr i, Sum.inl x => i = 0 ∧ x ∈ S
  symm := by
    intro a b h
    cases a <;> cases b
    · exact Q.symm h
    · exact h
    · exact h
    · exact (pathGraph 4).symm h
  loopless := by
    intro a
    cases a with
    | inl x => exact Q.loopless x
    | inr i => exact (pathGraph 4).loopless i

/--
The $(s, d)$-broom $B(s, d) := P_{d+2}[v_1 \leftarrow \overline{K_s}]$ (`BroomGraph s d`,
Section 2 & Proposition 6(2b) of `main.tex`), represented directly as `substGraph (pathGraph (d + 2)) 0 ⊥`
on `{v : Fin (d + 2) // v ≠ 0} ⊕ Fin s` (of cardinality $s + d + 1$).
-/
abbrev BroomGraph (s d : ℕ) : SimpleGraph ({v : Fin (d + 2) // v ≠ 0} ⊕ Fin s) :=
  substGraph (pathGraph (d + 2)) 0 (⊥ : SimpleGraph (Fin s))

/--
Recursive infinite tower graph $H_{t+k}^{(t)}$ (`PrimeTowerGraph t k : SimpleGraph (Fin (t + k))`,
Section 2 & Proposition 6(3) of `main.tex`):
- Vertices `0 .. t - 1` span $H_t^{(t)} = P_t = \text{pathGraph } t$ with endpoint $u_t = t - 1$.
- For each step $m = 1, \dots, k$ (adding vertex $u_{t+m}$ at 0-indexed index `j = t + m - 1 ≥ t`
  with previous endpoint $u_{t+m-1}$ at index `j - 1 = t + m - 2`):
  - If $m$ is odd (`(j - t + 1) % 2 = 1`), $u_{t+m}$ is a co-leaf of co-degree $1$ in $H_{t+m}^{(t)}$
    adjacent in $\overline{H_{t+m}^{(t)}}$ solely to $u_{t+m-1}$ (i.e., adjacent in $H_{t+m}^{(t)}$
    to all `i < j - 1` and non-adjacent to `j - 1`);
  - If $m$ is even (`(j - t + 1) % 2 = 0`), $u_{t+m}$ is a degree-$1$ leaf in $H_{t+m}^{(t)}$
    adjacent in $H_{t+m}^{(t)}$ solely to $u_{t+m-1}$ (`i = j - 1`).
-/
def primeTowerAdjLt (t : ℕ) (i j : ℕ) : Prop :=
  if j < t then
    j = i + 1
  else
    if (j - t + 1) % 2 = 1 then
      i + 1 < j
    else
      i + 1 = j

def PrimeTowerGraph (t k : ℕ) : SimpleGraph (Fin (t + k)) where
  Adj u v :=
    if u.1 < v.1 then primeTowerAdjLt t u.1 v.1
    else if v.1 < u.1 then primeTowerAdjLt t v.1 u.1
    else False
  symm := by
    intro u v h
    by_cases huv : u.1 < v.1
    · rw [if_pos huv] at h
      have hvu : ¬v.1 < u.1 := Nat.not_lt.mpr (le_of_lt huv)
      rw [if_neg hvu, if_pos huv]
      exact h
    · by_cases hvu : v.1 < u.1
      · rw [if_neg huv, if_pos hvu] at h
        rw [if_pos hvu]
        exact h
      · rw [if_neg huv, if_neg hvu] at h
        exact False.elim h
  loopless := by intro u; simp

/--
A finite graph $G$ is prime (`IsPrimeGraph G`, Theorem 1 & Proposition 6(3) of `main.tex`)
if $|G| \ge 4$ and every proper module $M$ of $G$ has cardinality $|M| = 1$.
-/
def IsPrimeGraph {W : Type*} [Fintype W] [DecidableEq W] (G : SimpleGraph W) : Prop :=
  4 ≤ Fintype.card W ∧ ∀ M : Finset W, IsProperModuleIn G Finset.univ M → M.card = 1

/--
A finite graph $G$ is a split graph (`IsSplitGraph G`, Proposition 6(3) of `main.tex`)
if $V(G)$ partitions into a clique $C$ and an independent set $I$.
-/
def IsSplitGraph {W : Type*} [Fintype W] [DecidableEq W] (G : SimpleGraph W) : Prop :=
  ∃ C I : Finset W, C ∪ I = Finset.univ ∧ Disjoint C I ∧
    G.IsClique (C : Set W) ∧ Gᶜ.IsClique (I : Set W)

end ErdosHajnalGen
