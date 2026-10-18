/-
Copyright 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosHajnal.BasicLemmas
import ErdosHajnal.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Anticonnected Neighborhood Modules and Module Chains (Lemmas 4.1 and 4.2 of `FMBV4-016_readable.tex`)

This file formalizes:
- **Connected Bipartition Boundary Edge (`anticonnected_mixed_exists_edge`)**: If $C \subseteq V$ is
  anticonnected in $G$ and $z$ is mixed on $C$ in $G$, then walking along $\overline{G}[C]$ from a
  non-neighbor of $z$ to a neighbor of $z$ produces an edge $x_2 x_3 \in E(\overline{G}[C])$ with
  $\neg G.\text{Adj } z\, x_2$ and $G.\text{Adj } z\, x_3$.
- **The 6-Vertex Comb Obstruction (`comb_mixed_forces_P6Compl`)**: Lemma 4.1, showing
  that the 6-tuple $(v, a_i, u, z, x_2, x_3)$ is injective and induces $P_6$ in $\overline{G}$
  ($\overline{P_6}$ in $G$).
- **Lemma 4.1 (`lem:anticonn-module`)**: Anticonnected Neighborhood Module Lemma inside
  Upside-Down Combs.
- **Lemma 4.2 (`lem:module-chain`)**: Nested Proper Module Chain Length Bound
  ($T \le \omega(H) + \alpha(H) \le 2 \kappa(H)$).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open Finset SimpleGraph Real

namespace ErdosHajnalP6

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Section 1: Walk Boundary Edge and Anticonnected Mixed Vertex Lemma -/

/--
Along any walk `p : H.Walk u w` from a vertex `u` with `¬P u` to a vertex `w` with `P w`,
there is an edge `H.Adj a b` crossing the boundary from `¬P a` to `P b`.
-/
theorem walk_exists_adj_of_not_of_prop {α : Type*} {H : SimpleGraph α} (P : α → Prop)
    {u w : α} (p : H.Walk u w) (hu : ¬P u) (hw : P w) :
    ∃ a b : α, H.Adj a b ∧ ¬P a ∧ P b := by
  induction p with
  | nil => exact absurd hw hu
  | @cons u v w h p ih =>
    by_cases hv : P v
    · exact ⟨u, v, h, hu, hv⟩
    · exact ih hv hw

/--
Characterization of `¬IsVertexPureTo G z C` as `IsVertexMixedOn G z C`.
-/
theorem not_isVertexPureTo_iff_isVertexMixedOn (G : SimpleGraph V) (z : V) (C : Finset V) :
    ¬IsVertexPureTo G z C ↔ IsVertexMixedOn G z C := by
  unfold IsVertexPureTo IsVertexMixedOn
  push_neg
  exact and_comm

/--
**Connected Bipartition Boundary Edge (`anticonnected_mixed_exists_edge`)**:
If $C \subseteq V$ is anticonnected in $G$ (`IsAnticonnected G C`) and $z \in V$ has both a
non-neighbor $x \in C$ and a neighbor $y \in C$ in $G$, then there exist $x_2, x_3 \in C$
such that $x_2 \neq x_3$, $\neg G.\text{Adj } x_2\, x_3$, $\neg G.\text{Adj } z\, x_2$, and
$G.\text{Adj } z\, x_3$.
-/
theorem anticonnected_mixed_exists_edge (G : SimpleGraph V) (C : Finset V) (z : V)
    (hC : IsAnticonnected G C)
    (hx : ∃ x ∈ C, ¬G.Adj z x) (hy : ∃ y ∈ C, G.Adj z y) :
    ∃ x₂ ∈ C, ∃ x₃ ∈ C, x₂ ≠ x₃ ∧ ¬G.Adj x₂ x₃ ∧ ¬G.Adj z x₂ ∧ G.Adj z x₃ := by
  rcases hx with ⟨x, hxC, hzx⟩
  rcases hy with ⟨y, hyC, hzy⟩
  have hreach : (Gᶜ.induce (C : Set V)).Reachable ⟨x, hxC⟩ ⟨y, hyC⟩ :=
    hC.preconnected ⟨x, hxC⟩ ⟨y, hyC⟩
  rcases hreach with ⟨p⟩
  obtain ⟨a, b, hab, hza, hzb⟩ :=
    walk_exists_adj_of_not_of_prop (fun u : (C : Set V) => G.Adj z u.val) p hzx hzy
  rw [induce_adj, compl_adj] at hab
  exact ⟨a.val, a.2, b.val, b.2, hab.1, hab.2, hza, hzb⟩

/--
Variant of `anticonnected_mixed_exists_edge` taking `IsVertexMixedOn G z C` directly.
-/
theorem IsVertexMixedOn.exists_anticonnected_edge {G : SimpleGraph V} {C : Finset V} {z : V}
    (hC : IsAnticonnected G C) (hmix : IsVertexMixedOn G z C) :
    ∃ x₂ ∈ C, ∃ x₃ ∈ C, x₂ ≠ x₃ ∧ ¬G.Adj x₂ x₃ ∧ ¬G.Adj z x₂ ∧ G.Adj z x₃ :=
  anticonnected_mixed_exists_edge G C z hC hmix.2 hmix.1

/-! ### Section 2: The 6-Vertex Comb Obstruction (Lemma 4.1, Case 2) -/

/--
In the configuration of Case 2 of Lemma 4.1 (`lem:anticonn-module`), the 6-tuple
`![v, a i, u, z, x₂, x₃] : Fin 6 → V` is injective and pulls back `G` to `P6Compl` (and `Gᶜ` to `P6`).
-/
theorem comb_mixed_exists_P6Compl_embedding
    (G : SimpleGraph V) {S : Finset V} {ℓ : ℕ} {w : ℝ}
    {a : Fin ℓ → V} {B : Fin ℓ → Finset V} {v : V}
    (hcomb : IsCombIn G S ℓ w a B)
    (hv : IsCombExternalApex G S ℓ a B v)
    {i k : Fin ℓ} (hik : i ≠ k)
    {u z x₂ x₃ : V}
    (hu : u ∈ B k) (hz : z ∈ B i) (hx2 : x₂ ∈ B i) (hx3 : x₃ ∈ B i)
    (huz : ¬G.Adj u z) (hux2 : G.Adj u x₂) (hux3 : G.Adj u x₃)
    (hx2x3 : ¬G.Adj x₂ x₃) (hzx2 : ¬G.Adj z x₂) (hzx3 : G.Adj z x₃) :
    ∃ g : Fin 6 ↪ V,
      (∀ p : Fin 6, g p = ![v, a i, u, z, x₂, x₃] p) ∧
      P6Compl = G.comap g ∧ P6 = Gᶜ.comap g := by
  let f : Fin 6 → V := ![v, a i, u, z, x₂, x₃]
  -- Non-consecutive pairs are adjacent in G:
  have h02 : G.Adj v u := hv.complete_to_blocks k u hu
  have h03 : G.Adj v z := hv.complete_to_blocks i z hz
  have h04 : G.Adj v x₂ := hv.complete_to_blocks i x₂ hx2
  have h05 : G.Adj v x₃ := hv.complete_to_blocks i x₃ hx3
  have h13 : G.Adj (a i) z := hcomb.apex_complete_own i z hz
  have h14 : G.Adj (a i) x₂ := hcomb.apex_complete_own i x₂ hx2
  have h15 : G.Adj (a i) x₃ := hcomb.apex_complete_own i x₃ hx3
  have h24 : G.Adj u x₂ := hux2
  have h25 : G.Adj u x₃ := hux3
  have h35 : G.Adj z x₃ := hzx3
  -- Consecutive pairs are distinct and non-adjacent in G:
  have hne01 : v ≠ a i := hv.not_apex i
  have hn01 : ¬G.Adj v (a i) := hv.anticomplete_to_apices i
  have hn10 : ¬G.Adj (a i) v := fun h => hn01 h.symm
  have hne12 : a i ≠ u := fun h => hcomb.apex_disjoint_blocks i k (h ▸ hu)
  have hn12 : ¬G.Adj (a i) u := hcomb.apex_anticomplete_other i k hik u hu
  have hn21 : ¬G.Adj u (a i) := fun h => hn12 h.symm
  have hne23 : u ≠ z := fun h =>
    Finset.disjoint_left.mp (hcomb.is_blockade.pairwise_disjoint k i hik.symm) hu (h ▸ hz)
  have hn23 : ¬G.Adj u z := huz
  have hn32 : ¬G.Adj z u := fun h => hn23 h.symm
  have hne34 : z ≠ x₂ := fun h => huz (h ▸ hux2)
  have hn34 : ¬G.Adj z x₂ := hzx2
  have hn43 : ¬G.Adj x₂ z := fun h => hn34 h.symm
  have hne45 : x₂ ≠ x₃ := fun h => hzx2 (h ▸ hzx3)
  have hn45 : ¬G.Adj x₂ x₃ := hx2x3
  have hn54 : ¬G.Adj x₃ x₂ := fun h => hn45 h.symm
  -- Distinctness for non-consecutive pairs follows immediately from G.ne_of_adj:
  have hne02 : v ≠ u := G.ne_of_adj h02
  have hne03 : v ≠ z := G.ne_of_adj h03
  have hne04 : v ≠ x₂ := G.ne_of_adj h04
  have hne05 : v ≠ x₃ := G.ne_of_adj h05
  have hne13 : a i ≠ z := G.ne_of_adj h13
  have hne14 : a i ≠ x₂ := G.ne_of_adj h14
  have hne15 : a i ≠ x₃ := G.ne_of_adj h15
  have hne24 : u ≠ x₂ := G.ne_of_adj h24
  have hne25 : u ≠ x₃ := G.ne_of_adj h25
  have hne35 : z ≠ x₃ := G.ne_of_adj h35
  have hf_inj : Function.Injective f := by
    intro p q hpq
    fin_cases p <;> fin_cases q <;> first
      | rfl
      | exfalso; exact hne01 hpq
      | exfalso; exact hne01 hpq.symm
      | exfalso; exact hne02 hpq
      | exfalso; exact hne02 hpq.symm
      | exfalso; exact hne03 hpq
      | exfalso; exact hne03 hpq.symm
      | exfalso; exact hne04 hpq
      | exfalso; exact hne04 hpq.symm
      | exfalso; exact hne05 hpq
      | exfalso; exact hne05 hpq.symm
      | exfalso; exact hne12 hpq
      | exfalso; exact hne12 hpq.symm
      | exfalso; exact hne13 hpq
      | exfalso; exact hne13 hpq.symm
      | exfalso; exact hne14 hpq
      | exfalso; exact hne14 hpq.symm
      | exfalso; exact hne15 hpq
      | exfalso; exact hne15 hpq.symm
      | exfalso; exact hne23 hpq
      | exfalso; exact hne23 hpq.symm
      | exfalso; exact hne24 hpq
      | exfalso; exact hne24 hpq.symm
      | exfalso; exact hne25 hpq
      | exfalso; exact hne25 hpq.symm
      | exfalso; exact hne34 hpq
      | exfalso; exact hne34 hpq.symm
      | exfalso; exact hne35 hpq
      | exfalso; exact hne35 hpq.symm
      | exfalso; exact hne45 hpq
      | exfalso; exact hne45 hpq.symm
  let g : Fin 6 ↪ V := ⟨f, hf_inj⟩
  have hP6Compl : P6Compl = G.comap g := by
    ext p q
    simp only [P6Compl, compl_adj, pathGraph_adj, comap_adj, g, Function.Embedding.coeFn_mk]
    fin_cases p <;> fin_cases q <;>
      simp [f, h02, h02.symm, h03, h03.symm, h04, h04.symm, h05, h05.symm,
        h13, h13.symm, h14, h14.symm, h15, h15.symm, h24, h24.symm, h25, h25.symm, h35, h35.symm,
        hn01, hn10, hn12, hn21, hn23, hn32, hn34, hn43, hn45, hn54]
  have hP6 : P6 = Gᶜ.comap g := by
    rw [← comap_compl, ← hP6Compl, P6Compl, compl_compl, P6]
  exact ⟨g, fun _ => rfl, hP6Compl, hP6⟩

/--
**The 6-Vertex Comb Obstruction (`comb_mixed_forces_P6Compl`, Case 2 of Lemma 4.1)**:
Under the hypotheses of Case 2 of Lemma 4.1 (`lem:anticonn-module`), $G$ cannot be induced-$\overline{P_6}$-free.
-/
theorem comb_mixed_forces_P6Compl
    (G : SimpleGraph V) {S : Finset V} {ℓ : ℕ} {w : ℝ}
    {a : Fin ℓ → V} {B : Fin ℓ → Finset V} {v : V}
    (hfree : IsInducedSubgraphFree G P6Compl)
    (hcomb : IsCombIn G S ℓ w a B)
    (hv : IsCombExternalApex G S ℓ a B v)
    {i k : Fin ℓ} (hik : i ≠ k)
    {u z x₂ x₃ : V}
    (hu : u ∈ B k) (hz : z ∈ B i) (hx2 : x₂ ∈ B i) (hx3 : x₃ ∈ B i)
    (huz : ¬G.Adj u z) (hux2 : G.Adj u x₂) (hux3 : G.Adj u x₃)
    (hx2x3 : ¬G.Adj x₂ x₃) (hzx2 : ¬G.Adj z x₂) (hzx3 : G.Adj z x₃) :
    False := by
  obtain ⟨g, -, hP6Compl, -⟩ :=
    comb_mixed_exists_P6Compl_embedding G hcomb hv hik hu hz hx2 hx3 huz hux2 hux3 hx2x3 hzx2 hzx3
  exact hfree ⟨g, hP6Compl⟩

/--
**Case 2 of Lemma 4.1 (`lem:anticonn-module`)**:
In an induced-$\overline{P_6}$-free graph $G$ with an $(\ell, w)$-comb $(a, B)$ and external apex $v$,
if $u \in B_k$ ($k \neq i$), $C \subseteq B_i \cap N_G(u)$ is anticonnected in $G$, and
$z \in B_i \setminus N_G(u)$, then $z$ is pure to $C$ in $G$.
-/
theorem comb_anticonnected_subset_pure_of_not_adj
    (G : SimpleGraph V) {S : Finset V} {ℓ : ℕ} {w : ℝ}
    {a : Fin ℓ → V} {B : Fin ℓ → Finset V} {v : V}
    (hfree : IsInducedSubgraphFree G P6Compl)
    (hcomb : IsCombIn G S ℓ w a B)
    (hv : IsCombExternalApex G S ℓ a B v)
    {i k : Fin ℓ} (hik : i ≠ k)
    {u : V} (hu : u ∈ B k)
    {C : Finset V} (hCB : C ⊆ B i) (huC : ∀ x ∈ C, G.Adj u x) (hC : IsAnticonnected G C)
    {z : V} (hz : z ∈ B i) (huz : ¬G.Adj u z) :
    IsVertexPureTo G z C := by
  by_contra hnotpure
  rw [not_isVertexPureTo_iff_isVertexMixedOn] at hnotpure
  obtain ⟨x₂, hx2C, x₃, hx3C, -, hx2x3, hzx2, hzx3⟩ :=
    hnotpure.exists_anticonnected_edge hC
  exact comb_mixed_forces_P6Compl G hfree hcomb hv hik hu hz
    (hCB hx2C) (hCB hx3C) huz (huC x₂ hx2C) (huC x₃ hx3C) hx2x3 hzx2 hzx3

/-! ### Section 3: Anticonnected Components, Induced Cliques, and Lemma 4.1 (`lem:anticonn-module`) -/

@[simp]
theorem mem_neighborFinsetIn_iff (G : SimpleGraph V) (v : V) (S : Finset V) (u : V) :
    u ∈ neighborFinsetIn G v S ↔ u ∈ S ∧ G.Adj v u := by
  unfold neighborFinsetIn
  simp

theorem neighborFinsetIn_subset (G : SimpleGraph V) (v : V) (S : Finset V) :
    neighborFinsetIn G v S ⊆ S := by
  intro u hu
  exact ((mem_neighborFinsetIn_iff G v S u).mp hu).1

/--
$m_{\max}(G[M])$ (`maxProperModuleCard G M`): the maximum cardinality of a proper module of $G[M]$,
or $0$ if $G[M]$ has no proper module (Section 2.1 of `FMBV4-016_readable.tex`).
-/
noncomputable def maxProperModuleCard (G : SimpleGraph V) (M : Finset V) : ℕ :=
  by classical exact (M.powerset.filter (IsProperModuleIn G M)).sup Finset.card

/--
Every proper module $C$ of $G[M]$ satisfies $|C| \le m_{\max}(G[M])$.
-/
theorem IsProperModuleIn.card_le_maxProperModuleCard {G : SimpleGraph V} {M C : Finset V}
    (hC : IsProperModuleIn G M C) : C.card ≤ maxProperModuleCard G M := by
  classical
  unfold maxProperModuleCard
  apply Finset.le_sup (f := Finset.card)
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hC.2.1.subset, hC⟩

/--
If $m_{\max}(G[M]) > 0$, there exists a proper module $N$ of $G[M]$ attaining $|N| = m_{\max}(G[M])$.
-/
theorem exists_isProperModuleIn_card_eq_maxProperModuleCard {G : SimpleGraph V} {M : Finset V}
    (hpos : 0 < maxProperModuleCard G M) :
    ∃ N : Finset V, IsProperModuleIn G M N ∧ N.card = maxProperModuleCard G M := by
  classical
  unfold maxProperModuleCard at hpos ⊢
  have hne : (M.powerset.filter (IsProperModuleIn G M)).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    simp [hemp] at hpos
  obtain ⟨N, hN, hsup⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  rw [Finset.mem_filter] at hN
  exact ⟨N, hN.2, hsup.symm⟩

/--
A subset $C \subseteq Z$ is an anticonnected component of $G[Z]$ (`IsAnticonnectedComponentOf G Z C`)
if $C \subseteq Z$, $C$ is anticonnected in $G$, and there are no edges in $\overline{G}$ between
$C$ and $Z \setminus C$ (i.e. every $x \in C$ and $y \in Z \setminus C$ are adjacent in $G$).
-/
def IsAnticonnectedComponentOf (G : SimpleGraph V) (Z C : Finset V) : Prop :=
  C ⊆ Z ∧ IsAnticonnected G C ∧ ∀ x ∈ C, ∀ y ∈ Z, y ∉ C → G.Adj x y

theorem IsAnticonnected.nonempty {G : SimpleGraph V} {C : Finset V} (hC : IsAnticonnected G C) :
    C.Nonempty := by
  obtain ⟨⟨x, hx⟩⟩ := SimpleGraph.Connected.nonempty hC
  exact ⟨x, hx⟩

theorem IsAnticonnectedComponentOf.nonempty {G : SimpleGraph V} {Z C : Finset V}
    (hC : IsAnticonnectedComponentOf G Z C) : C.Nonempty :=
  hC.2.1.nonempty

theorem IsAnticonnectedComponentOf.isCompletePair_of_disjoint {G : SimpleGraph V} {Z C₁ C₂ : Finset V}
    (hC₁ : IsAnticonnectedComponentOf G Z C₁) (hC₂ : IsAnticonnectedComponentOf G Z C₂)
    (hdisj : Disjoint C₁ C₂) : IsCompletePair G C₁ C₂ := by
  intro x hx y hy
  exact hC₁.2.2 x hx y (hC₂.1 hy) (Finset.disjoint_right.mp hdisj hy)

/--
A family $C : \text{Fin } r \to \text{Finset } V$ is the partition of $Z$ into anticonnected
components of $G[Z]$ (`IsAnticonnectedComponentFamily G Z r C`).
-/
structure IsAnticonnectedComponentFamily (G : SimpleGraph V) (Z : Finset V) (r : ℕ)
    (C : Fin r → Finset V) : Prop where
  is_component : ∀ s : Fin r, IsAnticonnectedComponentOf G Z (C s)
  pairwise_disjoint : ∀ s t : Fin r, s ≠ t → Disjoint (C s) (C t)
  biUnion_eq : Finset.univ.biUnion C = Z

/--
Precomposing an anticonnected component family with any permutation $\sigma : \text{Fin } r \simeq \text{Fin } r$
preserves `IsAnticonnectedComponentFamily`.
-/
theorem IsAnticonnectedComponentFamily.comp_equiv {G : SimpleGraph V} {Z : Finset V} {r : ℕ}
    {C : Fin r → Finset V} (hC : IsAnticonnectedComponentFamily G Z r C) (σ : Fin r ≃ Fin r) :
    IsAnticonnectedComponentFamily G Z r (C ∘ σ) where
  is_component s := hC.is_component (σ s)
  pairwise_disjoint s t hst := hC.pairwise_disjoint (σ s) (σ t) (σ.injective.ne hst)
  biUnion_eq := by
    rw [← hC.biUnion_eq]
    ext v
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Function.comp_apply]
    exact ⟨fun ⟨s, hs⟩ => ⟨σ s, hs⟩, fun ⟨s, hs⟩ => ⟨σ.symm s, by simpa using hs⟩⟩

/--
Every finite vertex subset $Z \subseteq V$ has a canonical partition into anticonnected components
of $G[Z]$.
-/
theorem exists_anticonnectedComponentFamily (G : SimpleGraph V) (Z : Finset V) :
    ∃ (r : ℕ) (C : Fin r → Finset V), IsAnticonnectedComponentFamily G Z r C := by
  classical
  obtain ⟨r, ⟨e⟩⟩ := Finite.exists_equiv_fin (Gᶜ.induce (Z : Set V)).ConnectedComponent
  let C : Fin r → Finset V := fun s =>
    (Finset.univ.filter (fun x : (Z : Set V) =>
      (Gᶜ.induce (Z : Set V)).connectedComponentMk x = e.symm s)).map
      (Function.Embedding.subtype _)
  have hmem : ∀ (s : Fin r) (v : V),
      v ∈ C s ↔ ∃ hv : v ∈ Z, (Gᶜ.induce (Z : Set V)).connectedComponentMk ⟨v, hv⟩ = e.symm s := by
    intro s v
    simp only [C, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coe_subtype, Subtype.exists]
    constructor
    · rintro ⟨a, haZ, hmk, rfl⟩
      exact ⟨haZ, hmk⟩
    · rintro ⟨hvZ, hmk⟩
      exact ⟨v, hvZ, hmk, rfl⟩
  refine ⟨r, C, ?_, ?_, ?_⟩
  · intro s
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      rcases (hmem s v).mp hv with ⟨hvZ, -⟩
      exact hvZ
    · -- Prove IsAnticonnected G (C s) via graph isomorphism to (e.symm s).toSimpleGraph
      unfold IsAnticonnected
      let φ : (Gᶜ.induce (C s : Set V)) ≃g (e.symm s).toSimpleGraph :=
        { toFun := fun u =>
            ⟨⟨u.val, ((hmem s u.val).mp u.2).fst⟩, ((hmem s u.val).mp u.2).snd⟩
          invFun := fun x =>
            ⟨x.val.val, (hmem s x.val.val).mpr ⟨x.val.2, x.2⟩⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_rel_iff' := Iff.rfl }
      exact φ.connected_iff.mpr (e.symm s).connected_toSimpleGraph
    · intro x hx y hyZ hyC
      rcases (hmem s x).mp hx with ⟨hxZ, hx_mk⟩
      have hy_mk : (Gᶜ.induce (Z : Set V)).connectedComponentMk ⟨y, hyZ⟩ ≠ e.symm s :=
        fun h => hyC ((hmem s y).mpr ⟨hyZ, h⟩)
      have hnot_reach : ¬(Gᶜ.induce (Z : Set V)).Reachable ⟨x, hxZ⟩ ⟨y, hyZ⟩ := by
        intro hr
        exact hy_mk (ConnectedComponent.sound hr.symm ▸ hx_mk)
      have hnot_adj : ¬(Gᶜ.induce (Z : Set V)).Adj ⟨x, hxZ⟩ ⟨y, hyZ⟩ :=
        fun hadj => hnot_reach hadj.reachable
      have hne : x ≠ y := fun hxy => hyC (hxy ▸ hx)
      rw [induce_adj, compl_adj, not_and, not_not] at hnot_adj
      exact hnot_adj hne
  · intro s t hst
    rw [Finset.disjoint_left]
    intro v hvs hvt
    rcases (hmem s v).mp hvs with ⟨hvZ, hs⟩
    rcases (hmem t v).mp hvt with ⟨_, ht⟩
    exact hst (e.symm.injective (hs.symm.trans ht))
  · ext v
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, hmem]
    constructor
    · rintro ⟨_, hvZ, _⟩
      exact hvZ
    · intro hvZ
      exact ⟨e ((Gᶜ.induce (Z : Set V)).connectedComponentMk ⟨v, hvZ⟩), hvZ, by simp⟩

/--
For an anticonnected component family `(C_1, ..., C_r)` of `Z`, the sum of `|C_s|` equals `|Z|`.
-/
theorem IsAnticonnectedComponentFamily.sum_card_eq {G : SimpleGraph V} {Z : Finset V} {r : ℕ}
    {C : Fin r → Finset V} (hC : IsAnticonnectedComponentFamily G Z r C) :
    (∑ s : Fin r, (C s).card) = Z.card := by
  rw [← hC.biUnion_eq, Finset.card_biUnion]
  intro s _ t _ hst
  exact hC.pairwise_disjoint s t hst

/--
Any clique $K \subseteq M$ in $G$ has cardinality at most $\omega(G[M])$.
-/
theorem card_le_induce_cliqueNum {G : SimpleGraph V} {M K : Finset V}
    (hK : G.IsClique K) (hKM : K ⊆ M) :
    K.card ≤ (G.induce (M : Set V)).cliqueNum := by
  let K' : Finset (M : Set V) := K.subtype (· ∈ M)
  have hK'_cliq : (G.induce (M : Set V)).IsClique K' := by
    intro x hx y hy hxy
    simp only [K', Finset.mem_coe, Finset.mem_subtype] at hx hy
    exact hK hx hy (Subtype.ext_iff.not.mp hxy)
  have hcard : K'.card = K.card := by
    simp only [K', Finset.card_subtype]
    rw [Finset.filter_eq_self.mpr (fun x hx => hKM hx)]
  rw [← hcard]
  exact hK'_cliq.card_le_cliqueNum

/--
Any independent set $I \subseteq M$ in $G$ has cardinality at most $\alpha(G[M])$.
-/
theorem card_le_induce_indepNum {G : SimpleGraph V} {M I : Finset V}
    (hI : G.IsIndepSet I) (hIM : I ⊆ M) :
    I.card ≤ (G.induce (M : Set V)).indepNum := by
  let I' : Finset (M : Set V) := I.subtype (· ∈ M)
  have hI'_indep : (G.induce (M : Set V)).IsIndepSet I' := by
    intro x hx y hy hxy
    simp only [I', Finset.mem_coe, Finset.mem_subtype] at hx hy
    exact hI hx hy (Subtype.ext_iff.not.mp hxy)
  have hcard : I'.card = I.card := by
    simp only [I', Finset.card_subtype]
    rw [Finset.filter_eq_self.mpr (fun x hx => hIM hx)]
  rw [← hcard]
  exact hI'_indep.card_le_indepNum

/--
$\omega(G[M]) \le \omega(G)$ for any vertex subset $M \subseteq V$.
-/
theorem induce_cliqueNum_le (G : SimpleGraph V) (M : Finset V) :
    (G.induce (M : Set V)).cliqueNum ≤ G.cliqueNum := by
  obtain ⟨s, hs⟩ := (G.induce (M : Set V)).exists_isNClique_cliqueNum
  let t : Finset V := s.map (Function.Embedding.subtype _)
  have ht_cliq : G.IsClique t := by
    intro x hx y hy hxy
    simp only [t, Finset.mem_coe, Finset.mem_map, Function.Embedding.coe_subtype,
      Subtype.exists] at hx hy
    rcases hx with ⟨x, hxM, hxs, rfl⟩
    rcases hy with ⟨y, hyM, hys, rfl⟩
    have hne : (⟨x, hxM⟩ : (M : Set V)) ≠ ⟨y, hyM⟩ := fun h => hxy (congr_arg Subtype.val h)
    exact hs.isClique hxs hys hne
  have hcard : t.card = (G.induce (M : Set V)).cliqueNum := by
    rw [Finset.card_map, hs.card_eq]
  rw [← hcard]
  exact ht_cliq.card_le_cliqueNum

/--
$\alpha(G[M]) \le \alpha(G)$ for any vertex subset $M \subseteq V$.
-/
theorem induce_indepNum_le (G : SimpleGraph V) (M : Finset V) :
    (G.induce (M : Set V)).indepNum ≤ G.indepNum := by
  obtain ⟨s, hs⟩ := (G.induce (M : Set V)).exists_isNIndepSet_indepNum
  let t : Finset V := s.map (Function.Embedding.subtype _)
  have ht_indep : G.IsIndepSet t := by
    intro x hx y hy hxy
    simp only [t, Finset.mem_coe, Finset.mem_map, Function.Embedding.coe_subtype,
      Subtype.exists] at hx hy
    rcases hx with ⟨x, hxM, hxs, rfl⟩
    rcases hy with ⟨y, hyM, hys, rfl⟩
    have hne : (⟨x, hxM⟩ : (M : Set V)) ≠ ⟨y, hyM⟩ := fun h => hxy (congr_arg Subtype.val h)
    exact hs.isIndepSet hxs hys hne
  have hcard : t.card = (G.induce (M : Set V)).indepNum := by
    rw [Finset.card_map, hs.card_eq]
  rw [← hcard]
  exact ht_indep.card_le_indepNum

/--
$\kappa(G[M]) \le \kappa(G)$ for any vertex subset $M \subseteq V$.
-/
theorem induce_kappa_le (G : SimpleGraph V) (M : Finset V) :
    kappa (G.induce (M : Set V)) ≤ kappa G := by
  unfold kappa
  exact max_le_max (induce_cliqueNum_le G M) (induce_indepNum_le G M)

/--
Any complete blockade $(C_1, \dots, C_r)$ in $G[M]$ has length $r \le \omega(G[M]) \le \omega(G)$.
-/
theorem IsCompleteBlockadeIn.length_le_induce_cliqueNum {G : SimpleGraph V} {M : Finset V}
    {r : ℕ} {w : ℝ} {C : Fin r → Finset V} (hB : IsCompleteBlockadeIn G M r w C) :
    r ≤ (G.induce (M : Set V)).cliqueNum := by
  classical
  let c : Fin r → V := fun s => (hB.1.nonempty_blocks s).choose
  have hc_mem : ∀ s : Fin r, c s ∈ C s := fun s => (hB.1.nonempty_blocks s).choose_spec
  have hc_inj : Function.Injective c := by
    intro s t hst
    by_contra hne
    exact Finset.disjoint_left.mp (hB.1.pairwise_disjoint s t hne) (hc_mem s) (hst ▸ hc_mem t)
  let K : Finset V := Finset.univ.image c
  have hK_card : K.card = r := by
    rw [Finset.card_image_of_injective _ hc_inj, Finset.card_fin]
  have hK_sub : K ⊆ M := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨s, -, rfl⟩
    exact hB.1.subset_ambient s (hc_mem s)
  have hK_cliq : G.IsClique K := by
    intro x hx y hy hxy
    rcases Finset.mem_image.mp (Finset.mem_coe.mp hx) with ⟨s, -, rfl⟩
    rcases Finset.mem_image.mp (Finset.mem_coe.mp hy) with ⟨t, -, rfl⟩
    have hst : s ≠ t := fun h => hxy (congr_arg c h)
    exact hB.2 s t hst (c s) (hc_mem s) (c t) (hc_mem t)
  rw [← hK_card]
  exact card_le_induce_cliqueNum hK_cliq hK_sub

theorem IsCompleteBlockadeIn.length_le_cliqueNum {G : SimpleGraph V} {M : Finset V}
    {r : ℕ} {w : ℝ} {C : Fin r → Finset V} (hB : IsCompleteBlockadeIn G M r w C) :
    r ≤ G.cliqueNum :=
  (hB.length_le_induce_cliqueNum).trans (induce_cliqueNum_le G M)

/--
**Lemma 4.1, Part 1 (`comb_anticonnectedComponent_isProperModuleIn`, `lem:anticonn-module`)**:
Let $G$ be a $\overline{P_6}$-free graph with an $(\ell, w)$-comb $(a, B)$ and external apex $v$.
Let $i, k \in [\ell]$ with $i \neq k$, let $M \subseteq B_i$, and let $u \in B_k$ be not complete
to $M$ in $G$ ($\exists w_0 \in M, \neg G.\text{Adj } u\, w_0$). Then every anticonnected component
$C$ of $G[N_G(u) \cap M]$ is a proper module of $G[M]$ (`IsProperModuleIn G M C`), and hence
$|C| \le m_{\max}(G[M])$.
-/
theorem comb_anticonnectedComponent_isProperModuleIn
    (G : SimpleGraph V) {S : Finset V} {ℓ : ℕ} {w : ℝ}
    {a : Fin ℓ → V} {B : Fin ℓ → Finset V} {v : V}
    (hfree : IsInducedSubgraphFree G P6Compl)
    (hcomb : IsCombIn G S ℓ w a B)
    (hv : IsCombExternalApex G S ℓ a B v)
    {i k : Fin ℓ} (hik : i ≠ k)
    {M : Finset V} (hMB : M ⊆ B i)
    {u : V} (hu : u ∈ B k) (hnotcomp : ∃ w₀ ∈ M, ¬G.Adj u w₀)
    {C : Finset V} (hC : IsAnticonnectedComponentOf G (neighborFinsetIn G u M) C) :
    IsProperModuleIn G M C := by
  have hCZ : C ⊆ neighborFinsetIn G u M := hC.1
  have hZM : neighborFinsetIn G u M ⊆ M := neighborFinsetIn_subset G u M
  have hCM : C ⊆ M := hCZ.trans hZM
  have hCB : C ⊆ B i := hCM.trans hMB
  have huC : ∀ x ∈ C, G.Adj u x := fun x hx =>
    ((mem_neighborFinsetIn_iff G u M x).mp (hCZ hx)).2
  refine ⟨hC.nonempty, ?_, hCM, ?_⟩
  · -- Prove C ⊂ M using w₀ ∈ M \ N_G(u)
    rw [Finset.ssubset_iff_of_subset hCM]
    rcases hnotcomp with ⟨w₀, hw₀M, hw₀u⟩
    exact ⟨w₀, hw₀M, fun hw₀C => hw₀u (huC w₀ hw₀C)⟩
  · -- Prove every z ∈ M \ C is pure to C in G
    intro z hzM hzC
    by_cases huz : G.Adj u z
    · -- Case 1: z ∈ N_G(u) ∩ M \ C, so z is complete to C in G
      have hzZ : z ∈ neighborFinsetIn G u M := (mem_neighborFinsetIn_iff G u M z).mpr ⟨hzM, huz⟩
      left
      intro x hxC
      exact (hC.2.2 x hxC z hzZ hzC).symm
    · -- Case 2: z ∈ M \ N_G(u), so z is pure to C by the 6-vertex comb obstruction
      exact comb_anticonnected_subset_pure_of_not_adj G hfree hcomb hv hik hu hCB huC hC.2.1
        (hMB hzM) huz

/--
Under the hypotheses of Lemma 4.1 (`lem:anticonn-module`), every anticonnected component $C$ of $G[N_G(u) \cap M]$
satisfies $|C| \le m_{\max}(G[M])$.
-/
theorem comb_anticonnectedComponent_card_le_maxProperModuleCard
    (G : SimpleGraph V) {S : Finset V} {ℓ : ℕ} {w : ℝ}
    {a : Fin ℓ → V} {B : Fin ℓ → Finset V} {v : V}
    (hfree : IsInducedSubgraphFree G P6Compl)
    (hcomb : IsCombIn G S ℓ w a B)
    (hv : IsCombExternalApex G S ℓ a B v)
    {i k : Fin ℓ} (hik : i ≠ k)
    {M : Finset V} (hMB : M ⊆ B i)
    {u : V} (hu : u ∈ B k) (hnotcomp : ∃ w₀ ∈ M, ¬G.Adj u w₀)
    {C : Finset V} (hC : IsAnticonnectedComponentOf G (neighborFinsetIn G u M) C) :
    C.card ≤ maxProperModuleCard G M :=
  (comb_anticonnectedComponent_isProperModuleIn G hfree hcomb hv hik hMB hu hnotcomp
    hC).card_le_maxProperModuleCard

/--
Any family of pairwise disjoint anticonnected components of $G[Z]$ inside $M$ forms a complete
$(r, 1)$-blockade in $G[M]$.
-/
theorem IsAnticonnectedComponentFamily.isCompleteBlockadeIn {G : SimpleGraph V} {M Z : Finset V}
    {r : ℕ} {C : Fin r → Finset V} (hZM : Z ⊆ M)
    (hC : IsAnticonnectedComponentFamily G Z r C) :
    IsCompleteBlockadeIn G M r 1 C := by
  refine ⟨⟨?_, ?_, hC.pairwise_disjoint, ?_⟩, ?_⟩
  · intro s
    exact (hC.is_component s).1.trans hZM
  · intro s
    exact (hC.is_component s).nonempty
  · intro s
    have hpos : 1 ≤ (C s).card := Finset.card_pos.mpr (hC.is_component s).nonempty
    exact_mod_cast hpos
  · intro s t hst
    exact (hC.is_component s).isCompletePair_of_disjoint (hC.is_component t)
      (hC.pairwise_disjoint s t hst)

/--
**Lemma 4.1, Full Statement (`comb_anticonnected_neighborhood_modules`, `lem:anticonn-module`)**:
For any $\overline{P_6}$-free graph $G$, any $(\ell, w)$-comb $(a, B)$ with external apex $v$,
any $i \neq k \in [\ell]$, any $M \subseteq B_i$, any $u \in B_k$ not complete to $M$ in $G$,
and any anticonnected component partition $(C_1, \dots, C_r)$ of $G[N_G(u) \cap M]$:
1. Each $C_s$ is a proper module of $G[M]$ with $|C_s| \le m_{\max}(G[M])$;
2. $(C_1, \dots, C_r)$ is a complete $(r, 1)$-blockade in $G[M]$;
3. $r \le \omega(G[M]) \le \omega(G)$; and
4. $|N_G(u) \cap M| \le r \cdot m_{\max}(G[M]) \le \omega(G[M]) \cdot m_{\max}(G[M]) \le \omega(G) \cdot m_{\max}(G[M])$.
-/
theorem comb_anticonnected_neighborhood_modules
    (G : SimpleGraph V) {S : Finset V} {ℓ : ℕ} {w : ℝ}
    {a : Fin ℓ → V} {B : Fin ℓ → Finset V} {v : V}
    (hfree : IsInducedSubgraphFree G P6Compl)
    (hcomb : IsCombIn G S ℓ w a B)
    (hv : IsCombExternalApex G S ℓ a B v)
    {i k : Fin ℓ} (hik : i ≠ k)
    {M : Finset V} (hMB : M ⊆ B i)
    {u : V} (hu : u ∈ B k) (hnotcomp : ∃ w₀ ∈ M, ¬G.Adj u w₀)
    {r : ℕ} {C : Fin r → Finset V}
    (hC : IsAnticonnectedComponentFamily G (neighborFinsetIn G u M) r C) :
    (∀ s : Fin r, IsProperModuleIn G M (C s)) ∧
    (∀ s : Fin r, (C s).card ≤ maxProperModuleCard G M) ∧
    IsCompleteBlockadeIn G M r 1 C ∧
    r ≤ (G.induce (M : Set V)).cliqueNum ∧
    r ≤ G.cliqueNum ∧
    (neighborFinsetIn G u M).card ≤ r * maxProperModuleCard G M ∧
    (neighborFinsetIn G u M).card ≤ (G.induce (M : Set V)).cliqueNum * maxProperModuleCard G M ∧
    (neighborFinsetIn G u M).card ≤ G.cliqueNum * maxProperModuleCard G M := by
  have hprop : ∀ s : Fin r, IsProperModuleIn G M (C s) := fun s =>
    comb_anticonnectedComponent_isProperModuleIn G hfree hcomb hv hik hMB hu hnotcomp
      (hC.is_component s)
  have hcard : ∀ s : Fin r, (C s).card ≤ maxProperModuleCard G M := fun s =>
    (hprop s).card_le_maxProperModuleCard
  have hblock : IsCompleteBlockadeIn G M r 1 C :=
    hC.isCompleteBlockadeIn (neighborFinsetIn_subset G u M)
  have hr_ind : r ≤ (G.induce (M : Set V)).cliqueNum := hblock.length_le_induce_cliqueNum
  have hr_amb : r ≤ G.cliqueNum := hblock.length_le_cliqueNum
  have hsum : (neighborFinsetIn G u M).card ≤ r * maxProperModuleCard G M := by
    rw [← hC.sum_card_eq]
    calc
      (∑ s : Fin r, (C s).card) ≤ ∑ _s : Fin r, maxProperModuleCard G M :=
        Finset.sum_le_sum (fun s _ => hcard s)
      _ = r * maxProperModuleCard G M := by simp
  have hsum_ind :
      (neighborFinsetIn G u M).card ≤ (G.induce (M : Set V)).cliqueNum * maxProperModuleCard G M :=
    hsum.trans (Nat.mul_le_mul_right _ hr_ind)
  have hsum_amb :
      (neighborFinsetIn G u M).card ≤ G.cliqueNum * maxProperModuleCard G M :=
    hsum.trans (Nat.mul_le_mul_right _ hr_amb)
  exact ⟨hprop, hcard, hblock, hr_ind, hr_amb, hsum, hsum_ind, hsum_amb⟩

/-! ### Section 4: Nested Proper Module Chain Length Bound (Lemma 4.2, `lem:module-chain`) -/

/--
If $M : \text{Fin } (T + 1) \to \text{Finset } V$ satisfies $M_{s+1} \subseteq M_s$ for all $s$,
then $M$ is antitone ($i \le j \implies M_j \subseteq M_i$).
-/
theorem module_chain_antitone {T : ℕ} {M : Fin (T + 1) → Finset V}
    (hsub : ∀ s : Fin T, M s.succ ⊆ M s.castSucc) :
    Antitone M := by
  refine Fin.antitone_iff_succ_le.mpr ?_
  intro s
  exact hsub s

/--
In a decreasing chain $M_0 \supseteq M_1 \supseteq \dots \supseteq M_T$, for any $s < t$ in
$\text{Fin } T$, we have $M_t \subseteq M_{s+1}$.
-/
theorem module_chain_subset_succ_of_lt {T : ℕ} {M : Fin (T + 1) → Finset V}
    (hsub : ∀ s : Fin T, M s.succ ⊆ M s.castSucc)
    {s t : Fin T} (hst : s < t) :
    M t.castSucc ⊆ M s.succ := by
  have hle : s.succ ≤ t.castSucc := by
    rw [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc]
    exact Nat.succ_le_of_lt hst
  exact module_chain_antitone hsub hle

/--
**Lemma 4.2 (`module_chain_length_le_induce_cliqueNum_add_indepNum`, `lem:module-chain`)**:
For any strictly decreasing chain $M_0 \supsetneq M_1 \supsetneq \dots \supsetneq M_T$ inside
$W \subseteq V$ such that $M_{s+1}$ is a module of $G[M_s]$ for every $s \in \text{Fin } T$,
we have $T \le \omega(G[W]) + \alpha(G[W])$.
-/
theorem module_chain_length_le_induce_cliqueNum_add_indepNum
    (G : SimpleGraph V) {W : Finset V} {T : ℕ} (M : Fin (T + 1) → Finset V)
    (hW : M 0 ⊆ W)
    (hssub : ∀ s : Fin T, M s.succ ⊂ M s.castSucc)
    (hmod : ∀ s : Fin T, IsModuleIn G (M s.castSucc) (M s.succ)) :
    T ≤ (G.induce (W : Set V)).cliqueNum + (G.induce (W : Set V)).indepNum := by
  classical
  have hsub : ∀ s : Fin T, M s.succ ⊆ M s.castSucc := fun s => (hssub s).subset
  have hex : ∀ s : Fin T, ∃ x ∈ M s.castSucc, x ∉ M s.succ :=
    fun s => Finset.exists_of_ssubset (hssub s)
  let r : Fin T → V := fun s => (hex s).choose
  have hr_mem : ∀ s : Fin T, r s ∈ M s.castSucc := fun s => (hex s).choose_spec.1
  have hr_not_mem : ∀ s : Fin T, r s ∉ M s.succ := fun s => (hex s).choose_spec.2
  -- For s < t, r t ∈ M t.castSucc ⊆ M s.succ:
  have hr_mem_of_lt : ∀ {s t : Fin T}, s < t → r t ∈ M s.succ :=
    fun hst => module_chain_subset_succ_of_lt hsub hst (hr_mem _)
  -- Hence r is injective:
  have hr_inj : Function.Injective r := by
    intro s t hst
    rcases lt_trichotomy s t with hlt | rfl | hgt
    · exfalso; exact hr_not_mem s (hst ▸ hr_mem_of_lt hlt)
    · rfl
    · exfalso; exact hr_not_mem t (hst.symm ▸ hr_mem_of_lt hgt)
  -- Every r s lies in M 0 ⊆ W:
  have hr_in_W : ∀ s : Fin T, r s ∈ W := by
    intro s
    have h0 : (0 : Fin (T + 1)) ≤ s.castSucc := Fin.zero_le _
    exact hW (module_chain_antitone hsub h0 (hr_mem s))
  -- Every r s is pure to M s.succ in G:
  have hr_pure : ∀ s : Fin T, IsVertexPureTo G (r s) (M s.succ) :=
    fun s => (hmod s).2 (r s) (hr_mem s) (hr_not_mem s)
  -- Partition Fin T into S^+ and S^-:
  let P : Fin T → Prop := fun s => ∀ u ∈ M s.succ, G.Adj (r s) u
  let S_pos : Finset (Fin T) := Finset.univ.filter P
  let S_neg : Finset (Fin T) := Finset.univ.filter (fun s => ¬P s)
  have hpart : S_pos.card + S_neg.card = T := by
    have h := Finset.card_filter_add_card_filter_not P (s := (Finset.univ : Finset (Fin T)))
    simpa [S_pos, S_neg] using h
  have hS_neg_anticomp : ∀ s ∈ S_neg, ∀ u ∈ M s.succ, ¬G.Adj (r s) u := by
    intro s hs
    rw [Finset.mem_filter] at hs
    exact (hr_pure s).resolve_left hs.2
  -- Image of S^+ under r is a clique in G[W]:
  let K : Finset V := S_pos.image r
  have hK_card : K.card = S_pos.card := Finset.card_image_of_injective _ hr_inj
  have hK_sub : K ⊆ W := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨s, -, rfl⟩
    exact hr_in_W s
  have hK_cliq : G.IsClique K := by
    intro x hx y hy hxy
    rcases Finset.mem_image.mp (Finset.mem_coe.mp hx) with ⟨s, hs, rfl⟩
    rcases Finset.mem_image.mp (Finset.mem_coe.mp hy) with ⟨t, ht, rfl⟩
    rw [Finset.mem_filter] at hs ht
    rcases lt_trichotomy s t with hlt | rfl | hgt
    · exact hs.2 (r t) (hr_mem_of_lt hlt)
    · exact absurd rfl hxy
    · exact (ht.2 (r s) (hr_mem_of_lt hgt)).symm
  have hpos_le : S_pos.card ≤ (G.induce (W : Set V)).cliqueNum := by
    rw [← hK_card]
    exact card_le_induce_cliqueNum hK_cliq hK_sub
  -- Image of S^- under r is an independent set in G[W]:
  let I : Finset V := S_neg.image r
  have hI_card : I.card = S_neg.card := Finset.card_image_of_injective _ hr_inj
  have hI_sub : I ⊆ W := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨s, -, rfl⟩
    exact hr_in_W s
  have hI_indep : G.IsIndepSet I := by
    intro x hx y hy hxy
    rcases Finset.mem_image.mp (Finset.mem_coe.mp hx) with ⟨s, hs, rfl⟩
    rcases Finset.mem_image.mp (Finset.mem_coe.mp hy) with ⟨t, ht, rfl⟩
    rcases lt_trichotomy s t with hlt | rfl | hgt
    · exact hS_neg_anticomp s hs (r t) (hr_mem_of_lt hlt)
    · exact absurd rfl hxy
    · intro hadj
      exact hS_neg_anticomp t ht (r s) (hr_mem_of_lt hgt) hadj.symm
  have hneg_le : S_neg.card ≤ (G.induce (W : Set V)).indepNum := by
    rw [← hI_card]
    exact card_le_induce_indepNum hI_indep hI_sub
  linarith

/--
**Lemma 4.2 (`module_chain_length_le_two_mul_induce_kappa`, `lem:module-chain`)**:
For any strictly decreasing chain $M_0 \supsetneq M_1 \supsetneq \dots \supsetneq M_T$ inside
$W \subseteq V$ such that $M_{s+1}$ is a module of $G[M_s]$ for every $s \in \text{Fin } T$,
we have $T \le 2 \kappa(G[W])$.
-/
theorem module_chain_length_le_two_mul_induce_kappa
    (G : SimpleGraph V) {W : Finset V} {T : ℕ} (M : Fin (T + 1) → Finset V)
    (hW : M 0 ⊆ W)
    (hssub : ∀ s : Fin T, M s.succ ⊂ M s.castSucc)
    (hmod : ∀ s : Fin T, IsModuleIn G (M s.castSucc) (M s.succ)) :
    T ≤ 2 * kappa (G.induce (W : Set V)) := by
  have h1 := module_chain_length_le_induce_cliqueNum_add_indepNum G M hW hssub hmod
  have h2 := cliqueNum_le_kappa (G.induce (W : Set V))
  have h3 := indepNum_le_kappa (G.induce (W : Set V))
  linarith

/--
**Lemma 4.2 (Ambient Graph Version, `module_chain_length_le_cliqueNum_add_indepNum`)**:
For any strictly decreasing chain $M_0 \supsetneq M_1 \supsetneq \dots \supsetneq M_T$ of subsets
of $V$ such that $M_{s+1}$ is a module of $G[M_s]$ for every $s \in \text{Fin } T$,
we have $T \le \omega(G) + \alpha(G)$.
-/
theorem module_chain_length_le_cliqueNum_add_indepNum
    (G : SimpleGraph V) {T : ℕ} (M : Fin (T + 1) → Finset V)
    (hssub : ∀ s : Fin T, M s.succ ⊂ M s.castSucc)
    (hmod : ∀ s : Fin T, IsModuleIn G (M s.castSucc) (M s.succ)) :
    T ≤ G.cliqueNum + G.indepNum := by
  have h1 := module_chain_length_le_induce_cliqueNum_add_indepNum G M (Subset.refl (M 0)) hssub hmod
  have h2 := induce_cliqueNum_le G (M 0)
  have h3 := induce_indepNum_le G (M 0)
  linarith

/--
**Lemma 4.2 (Ambient Graph Version, `module_chain_length_le_two_mul_kappa`)**:
For any strictly decreasing chain $M_0 \supsetneq M_1 \supsetneq \dots \supsetneq M_T$ of subsets
of $V$ such that $M_{s+1}$ is a module of $G[M_s]$ for every $s \in \text{Fin } T$,
we have $T \le 2 \kappa(G)$.
-/
theorem module_chain_length_le_two_mul_kappa
    (G : SimpleGraph V) {T : ℕ} (M : Fin (T + 1) → Finset V)
    (hssub : ∀ s : Fin T, M s.succ ⊂ M s.castSucc)
    (hmod : ∀ s : Fin T, IsModuleIn G (M s.castSucc) (M s.succ)) :
    T ≤ 2 * kappa G := by
  have h1 := module_chain_length_le_cliqueNum_add_indepNum G M hssub hmod
  have h2 := cliqueNum_le_kappa G
  have h3 := indepNum_le_kappa G
  linarith

/--
**Lemma 4.2 (`proper_module_chain_length_bounds`, `lem:module-chain`)**:
Combined statement of Lemma 4.2 taking `∀ s : Fin T, IsProperModuleIn G (M s.castSucc) (M s.succ)`.
-/
theorem proper_module_chain_length_bounds
    (G : SimpleGraph V) {T : ℕ} (M : Fin (T + 1) → Finset V)
    (hchain : ∀ s : Fin T, IsProperModuleIn G (M s.castSucc) (M s.succ)) :
    T ≤ (G.induce (M 0 : Set V)).cliqueNum + (G.induce (M 0 : Set V)).indepNum ∧
    T ≤ 2 * kappa (G.induce (M 0 : Set V)) ∧
    T ≤ G.cliqueNum + G.indepNum ∧
    T ≤ 2 * kappa G := by
  have hssub : ∀ s : Fin T, M s.succ ⊂ M s.castSucc := fun s => (hchain s).2.1
  have hmod : ∀ s : Fin T, IsModuleIn G (M s.castSucc) (M s.succ) := fun s => (hchain s).2.2
  exact ⟨module_chain_length_le_induce_cliqueNum_add_indepNum G M (Subset.refl _) hssub hmod,
    module_chain_length_le_two_mul_induce_kappa G M (Subset.refl _) hssub hmod,
    module_chain_length_le_cliqueNum_add_indepNum G M hssub hmod,
    module_chain_length_le_two_mul_kappa G M hssub hmod⟩

/-! ### Section 5: Restricted Subgraph Rescaling and Greedy Clique/Stable-Set Extraction -/

theorem neighborFinsetIn_mono (G : SimpleGraph V) (v : V) {S' S : Finset V} (hsub : S' ⊆ S) :
    neighborFinsetIn G v S' ⊆ neighborFinsetIn G v S := by
  intro u hu
  rw [mem_neighborFinsetIn_iff] at hu ⊢
  exact ⟨hsub hu.1, hu.2⟩

theorem IsEpsSparseOn.mono_eps {G : SimpleGraph V} {S : Finset V} {ε ε' : ℝ}
    (h : IsEpsSparseOn G S ε) (hε : ε ≤ ε') : IsEpsSparseOn G S ε' := by
  intro v hv
  calc
    ((neighborFinsetIn G v S).card : ℝ) ≤ ε * (S.card : ℝ) := h v hv
    _ ≤ ε' * (S.card : ℝ) := by
      apply mul_le_mul_of_nonneg_right hε
      exact Nat.cast_nonneg _

theorem IsEpsRestrictedOn.mono_eps {G : SimpleGraph V} {S : Finset V} {ε ε' : ℝ}
    (h : IsEpsRestrictedOn G S ε) (hε : ε ≤ ε') : IsEpsRestrictedOn G S ε' :=
  h.elim (fun h1 => Or.inl (h1.mono_eps hε)) (fun h2 => Or.inr (h2.mono_eps hε))

/--
If $G[S]$ is $\lambda$-sparse and $S' \subseteq S$ satisfies $|S'| \ge c |S|$ with $c > 0$,
then $G[S']$ is $(\lambda / c)$-sparse.
-/
theorem IsEpsSparseOn.subset_div {G : SimpleGraph V} {S S' : Finset V} {lam c : ℝ}
    (h : IsEpsSparseOn G S lam) (hsub : S' ⊆ S) (hc : 0 < c) (hlam : 0 ≤ lam)
    (hcard : c * (S.card : ℝ) ≤ (S'.card : ℝ)) :
    IsEpsSparseOn G S' (lam / c) := by
  intro v hv
  have h1 : ((neighborFinsetIn G v S').card : ℝ) ≤ ((neighborFinsetIn G v S).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (neighborFinsetIn_mono G v hsub)
  have h2 : ((neighborFinsetIn G v S).card : ℝ) ≤ lam * (S.card : ℝ) := h v (hsub hv)
  have h3 : (S.card : ℝ) ≤ (S'.card : ℝ) / c := (le_div_iff₀ hc).mpr (by linarith)
  calc
    ((neighborFinsetIn G v S').card : ℝ) ≤ lam * (S.card : ℝ) := h1.trans h2
    _ ≤ lam * ((S'.card : ℝ) / c) := mul_le_mul_of_nonneg_left h3 hlam
    _ = (lam / c) * (S'.card : ℝ) := by ring

/--
If $G[S]$ is $\lambda$-restricted and $S' \subseteq S$ satisfies $|S'| \ge c |S|$ with $c > 0$,
then $G[S']$ is $(\lambda / c)$-restricted.
-/
theorem IsEpsRestrictedOn.subset_div {G : SimpleGraph V} {S S' : Finset V} {lam c : ℝ}
    (h : IsEpsRestrictedOn G S lam) (hsub : S' ⊆ S) (hc : 0 < c) (hlam : 0 ≤ lam)
    (hcard : c * (S.card : ℝ) ≤ (S'.card : ℝ)) :
    IsEpsRestrictedOn G S' (lam / c) :=
  h.elim (fun h1 => Or.inl (h1.subset_div hsub hc hlam hcard))
    (fun h2 => Or.inr (h2.subset_div hsub hc hlam hcard))

/--
Helper for greedy independent set extraction: for any $R \subseteq S$, if every vertex in $S$
has at most $D$ neighbors in $S$, then $R$ contains an independent set $I \subseteq R$ in $G$
with $|R| \le (D + 1) |I|$.
-/
theorem exists_indepSet_subset_of_deg_le (G : SimpleGraph V) (S : Finset V) (D : ℝ)
    (_hD : 0 ≤ D) (hdeg : ∀ v ∈ S, ((neighborFinsetIn G v S).card : ℝ) ≤ D) :
    ∀ n : ℕ, ∀ R : Finset V, R.card = n → R ⊆ S →
      ∃ I ⊆ R, G.IsIndepSet I ∧ (R.card : ℝ) ≤ (D + 1) * (I.card : ℝ) := by
  classical
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro R hRcard hRS
  by_cases hR : R.Nonempty
  · obtain ⟨v, hvR⟩ := hR
    let Nv : Finset V := insert v (neighborFinsetIn G v S)
    let R' : Finset V := R \ Nv
    have hvNv : v ∈ Nv := Finset.mem_insert_self v _
    have hR'_ssub : R' ⊂ R := by
      rw [Finset.ssubset_iff_of_subset Finset.sdiff_subset]
      exact ⟨v, hvR, fun hvR' => (Finset.mem_sdiff.mp hvR').2 hvNv⟩
    have hR'_lt : R'.card < n := hRcard ▸ Finset.card_lt_card hR'_ssub
    obtain ⟨I', hI'R', hI'_indep, hI'_card⟩ :=
      ih R'.card hR'_lt R' rfl (Finset.sdiff_subset.trans hRS)
    let I : Finset V := insert v I'
    have hvI' : v ∉ I' := fun hv => (Finset.mem_sdiff.mp (hI'R' hv)).2 hvNv
    have hIR : I ⊆ R := Finset.insert_subset_iff.mpr ⟨hvR, hI'R'.trans Finset.sdiff_subset⟩
    have hI_indep : G.IsIndepSet I := by
      intro x hx y hy hxy
      rcases Finset.mem_insert.mp (Finset.mem_coe.mp hx) with rfl | hxI'
      · rcases Finset.mem_insert.mp (Finset.mem_coe.mp hy) with rfl | hyI'
        · exact absurd rfl hxy
        · have hyR' : y ∈ R' := hI'R' hyI'
          have hy_not_Nv : y ∉ Nv := (Finset.mem_sdiff.mp hyR').2
          have hy_not_neigh : y ∉ neighborFinsetIn G x S :=
            fun h => hy_not_Nv (Finset.mem_insert_of_mem h)
          rw [mem_neighborFinsetIn_iff] at hy_not_neigh
          exact fun hadj => hy_not_neigh ⟨hRS (Finset.sdiff_subset hyR'), hadj⟩
      · rcases Finset.mem_insert.mp (Finset.mem_coe.mp hy) with rfl | hyI'
        · have hxR' : x ∈ R' := hI'R' hxI'
          have hx_not_Nv : x ∉ Nv := (Finset.mem_sdiff.mp hxR').2
          have hx_not_neigh : x ∉ neighborFinsetIn G y S :=
            fun h => hx_not_Nv (Finset.mem_insert_of_mem h)
          rw [mem_neighborFinsetIn_iff] at hx_not_neigh
          exact fun hadj => hx_not_neigh ⟨hRS (Finset.sdiff_subset hxR'), hadj.symm⟩
        · exact hI'_indep hxI' hyI' hxy
    have hNv_card : (Nv.card : ℝ) ≤ D + 1 := by
      have h1 : Nv.card ≤ (neighborFinsetIn G v S).card + 1 := Finset.card_insert_le _ _
      have h2 : (Nv.card : ℝ) ≤ ((neighborFinsetIn G v S).card : ℝ) + 1 := by exact_mod_cast h1
      linarith [hdeg v (hRS hvR)]
    have hR_le : R.card ≤ R'.card + Nv.card := by
      have hsub : R ⊆ R' ∪ Nv := by
        intro u hu
        by_cases huNv : u ∈ Nv
        · exact Finset.mem_union_right _ huNv
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hu, huNv⟩)
      exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hR_real : (R.card : ℝ) ≤ (R'.card : ℝ) + (Nv.card : ℝ) := by exact_mod_cast hR_le
    have hI_card : (I.card : ℝ) = (I'.card : ℝ) + 1 := by
      rw [Finset.card_insert_of_notMem hvI']
      push_cast
      ring
    refine ⟨I, hIR, hI_indep, ?_⟩
    calc
      (R.card : ℝ) ≤ (R'.card : ℝ) + (Nv.card : ℝ) := hR_real
      _ ≤ (D + 1) * (I'.card : ℝ) + (D + 1) := by linarith
      _ = (D + 1) * (I.card : ℝ) := by rw [hI_card]; ring
  · rw [Finset.not_nonempty_iff_eq_empty] at hR
    refine ⟨∅, Finset.empty_subset R, by simp, ?_⟩
    simp [hR]

/--
If $G[S]$ is $\varepsilon$-sparse (`IsEpsSparseOn G S ε`) with $\varepsilon \ge 0$, then $S$
contains an independent set $I \subseteq S$ of size at least $\frac{|S|}{\varepsilon |S| + 1}$,
so $\frac{|S|}{\varepsilon |S| + 1} \le \alpha(G[S]) \le \alpha(G)$.
-/
theorem exists_indepSet_of_isEpsSparseOn {G : SimpleGraph V} {S : Finset V} {ε : ℝ}
    (h : IsEpsSparseOn G S ε) (hε : 0 ≤ ε) :
    ∃ I ⊆ S, G.IsIndepSet I ∧ (S.card : ℝ) / (ε * (S.card : ℝ) + 1) ≤ (I.card : ℝ) := by
  have hD : 0 ≤ ε * (S.card : ℝ) := mul_nonneg hε (Nat.cast_nonneg _)
  obtain ⟨I, hIS, hI_indep, hI_card⟩ :=
    exists_indepSet_subset_of_deg_le G S (ε * (S.card : ℝ)) hD h S.card S rfl (Subset.refl S)
  refine ⟨I, hIS, hI_indep, ?_⟩
  rw [div_le_iff₀ (by linarith)]
  linarith

/--
If $\overline{G}[S]$ is $\varepsilon$-sparse (`IsEpsSparseOn Gᶜ S ε`) with $\varepsilon \ge 0$,
then $S$ contains a clique $K \subseteq S$ in $G$ of size at least $\frac{|S|}{\varepsilon |S| + 1}$,
so $\frac{|S|}{\varepsilon |S| + 1} \le \omega(G[S]) \le \omega(G)$.
-/
theorem exists_clique_of_isEpsSparseOn_compl {G : SimpleGraph V} {S : Finset V} {ε : ℝ}
    (h : IsEpsSparseOn Gᶜ S ε) (hε : 0 ≤ ε) :
    ∃ K ⊆ S, G.IsClique K ∧ (S.card : ℝ) / (ε * (S.card : ℝ) + 1) ≤ (K.card : ℝ) := by
  obtain ⟨K, hKS, hK_indep, hK_card⟩ := exists_indepSet_of_isEpsSparseOn h hε
  rw [isIndepSet_compl] at hK_indep
  exact ⟨K, hKS, hK_indep, hK_card⟩

/--
If $G[S]$ is $\varepsilon$-restricted (`IsEpsRestrictedOn G S ε`) with $\varepsilon \ge 0$, then
$\frac{|S|}{\varepsilon |S| + 1} \le \kappa(G[S]) \le \kappa(G)$ (used in Step 3 of Proposition 5.4).
-/
theorem kappa_ge_of_isEpsRestrictedOn {G : SimpleGraph V} {S : Finset V} {ε : ℝ}
    (h : IsEpsRestrictedOn G S ε) (hε : 0 ≤ ε) :
    (S.card : ℝ) / (ε * (S.card : ℝ) + 1) ≤ (kappa (G.induce (S : Set V)) : ℝ) ∧
    (S.card : ℝ) / (ε * (S.card : ℝ) + 1) ≤ (kappa G : ℝ) := by
  have hind : (S.card : ℝ) / (ε * (S.card : ℝ) + 1) ≤ (kappa (G.induce (S : Set V)) : ℝ) := by
    rcases h with hsparse | hcompl
    · obtain ⟨I, hIS, hI_indep, hI_card⟩ := exists_indepSet_of_isEpsSparseOn hsparse hε
      have h1 : I.card ≤ (G.induce (S : Set V)).indepNum := card_le_induce_indepNum hI_indep hIS
      have h2 : (G.induce (S : Set V)).indepNum ≤ kappa (G.induce (S : Set V)) :=
        indepNum_le_kappa _
      exact hI_card.trans (by exact_mod_cast h1.trans h2)
    · obtain ⟨K, hKS, hK_cliq, hK_card⟩ := exists_clique_of_isEpsSparseOn_compl hcompl hε
      have h1 : K.card ≤ (G.induce (S : Set V)).cliqueNum := card_le_induce_cliqueNum hK_cliq hKS
      have h2 : (G.induce (S : Set V)).cliqueNum ≤ kappa (G.induce (S : Set V)) :=
        cliqueNum_le_kappa _
      exact hK_card.trans (by exact_mod_cast h1.trans h2)
  refine ⟨hind, hind.trans ?_⟩
  exact_mod_cast induce_kappa_le G S

/-! ### Section 6: Connected Subgraph Leaf-Pruning and Open-Interval Attachment Extraction -/

/--
If a walk $p : H.\text{Walk } u\, w$ avoids a vertex $x$, and $C \subseteq V$, we can lift $p$
from $H.\text{induce } C$ to $H.\text{induce } (C \setminus \{x\})$.
-/
theorem walk_induce_erase {H : SimpleGraph V} {C : Finset V} {x : V}
    {u w : ↥(C : Set V)} (p : (H.induce (C : Set V)).Walk u w)
    (hu : u.val ∈ C.erase x) (hw : w.val ∈ C.erase x)
    (havoid : ∀ z ∈ p.support, z.val ≠ x) :
    (H.induce ((C.erase x : Finset V) : Set V)).Reachable ⟨u.val, hu⟩ ⟨w.val, hw⟩ := by
  induction p with
  | nil => exact Reachable.refl _
  | @cons a b c hab p ih =>
    have hb_ne : b.val ≠ x := havoid b (List.mem_cons_of_mem a (Walk.start_mem_support p))
    have hb_erase : b.val ∈ C.erase x := Finset.mem_erase.mpr ⟨hb_ne, b.2⟩
    have hab' : (H.induce ((C.erase x : Finset V) : Set V)).Adj ⟨a.val, hu⟩ ⟨b.val, hb_erase⟩ := hab
    have hreach_bc := ih hb_erase hw (fun z hz => havoid z (List.mem_cons_of_mem a hz))
    exact hab'.reachable.trans hreach_bc

/--
Every connected induced subgraph $H[C]$ with $|C| \ge 2$ contains a vertex $x \in C$ such that
$H[C \setminus \{x\}]$ remains connected (obtained by deleting a vertex at maximum shortest-path
distance from a root $r_0 \in C$).
-/
theorem connected_induce_exists_erase {H : SimpleGraph V} {C : Finset V}
    (hconn : (H.induce (C : Set V)).Connected) (hcard : 2 ≤ C.card) :
    ∃ x ∈ C, (H.induce ((C.erase x : Finset V) : Set V)).Connected := by
  classical
  obtain ⟨r₀⟩ := hconn.nonempty
  have hwalk_len_pos : ∀ {u v : ↥(C : Set V)} (q : (H.induce (C : Set V)).Walk u v),
      u ≠ v → 0 < q.length := by
    intro u v q huv
    cases q with
    | nil => exact (huv rfl).elim
    | cons _ _ => simp
  have hex_walk : ∀ u : ↥(C : Set V), ∃ n : ℕ, ∃ p : (H.induce (C : Set V)).Walk r₀ u, p.length = n :=
    fun u => ⟨(hconn.preconnected r₀ u).some.length, (hconn.preconnected r₀ u).some, rfl⟩
  let dist : ↥(C : Set V) → ℕ := fun u => Nat.find (hex_walk u)
  have hdist_spec : ∀ u : ↥(C : Set V), ∃ p : (H.induce (C : Set V)).Walk r₀ u, p.length = dist u :=
    fun u => Nat.find_spec (hex_walk u)
  have hdist_le : ∀ (u : ↥(C : Set V)) (p : (H.induce (C : Set V)).Walk r₀ u), dist u ≤ p.length :=
    fun u p => Nat.find_min' (hex_walk u) ⟨p, rfl⟩
  obtain ⟨x, -, hx_max⟩ :=
    Finset.exists_max_image (Finset.univ : Finset ↥(C : Set V)) dist ⟨r₀, Finset.mem_univ r₀⟩
  have hdist_r₀ : dist r₀ = 0 :=
    Nat.eq_zero_of_le_zero (hdist_le r₀ Walk.nil)
  have hx_ne_r₀ : x.val ≠ r₀.val := by
    have h1lt : 1 < C.card := by omega
    obtain ⟨y, hyC, hy_ne⟩ := Finset.exists_mem_ne h1lt r₀.val
    let y' : ↥(C : Set V) := ⟨y, hyC⟩
    obtain ⟨py, hpy⟩ := hdist_spec y'
    have hy'_ne : r₀ ≠ y' := fun h => hy_ne (congr_arg Subtype.val h).symm
    have hpy_pos : 0 < dist y' := hpy ▸ hwalk_len_pos py hy'_ne
    have hx_pos : 0 < dist x := lt_of_lt_of_le hpy_pos (hx_max y' (Finset.mem_univ y'))
    intro hval
    have hxeq : x = r₀ := Subtype.ext hval
    rw [hxeq, hdist_r₀] at hx_pos
    exact lt_irrefl 0 hx_pos
  have hr₀_erase : r₀.val ∈ C.erase x.val :=
    Finset.mem_erase.mpr ⟨hx_ne_r₀.symm, r₀.2⟩
  have hreach_from_r₀ : ∀ w : ↥((C.erase x.val : Finset V) : Set V),
      (H.induce ((C.erase x.val : Finset V) : Set V)).Reachable ⟨r₀.val, hr₀_erase⟩ w := by
    rintro ⟨u, hu_erase⟩
    have hu_ne_x : u ≠ x.val := (Finset.mem_erase.mp hu_erase).1
    have huC : u ∈ C := (Finset.mem_erase.mp hu_erase).2
    let u' : ↥(C : Set V) := ⟨u, huC⟩
    obtain ⟨p, hp_len⟩ := hdist_spec u'
    have havoid : ∀ z ∈ p.support, z.val ≠ x.val := by
      intro z hz hzx
      have hzx_sub : z = x := Subtype.ext hzx
      subst hzx_sub
      have hmem : z ∈ p.support := hz
      have htake_len := congr_arg Walk.length (Walk.take_spec p hmem)
      rw [Walk.length_append] at htake_len
      have hzu' : z ≠ u' := fun h => hu_ne_x (congr_arg Subtype.val h).symm
      have hdrop_pos : 0 < (p.dropUntil z hmem).length :=
        hwalk_len_pos (p.dropUntil z hmem) hzu'
      have hlt : (p.takeUntil z hmem).length < dist u' := by omega
      have hle1 : dist z ≤ (p.takeUntil z hmem).length := hdist_le z (p.takeUntil z hmem)
      have hle2 : dist u' ≤ dist z := hx_max u' (Finset.mem_univ u')
      omega
    exact walk_induce_erase p hr₀_erase hu_erase havoid
  refine ⟨x.val, x.2, ?_⟩
  exact @Connected.mk _ _ (fun u v => (hreach_from_r₀ u).symm.trans (hreach_from_r₀ v))
    ⟨⟨r₀.val, hr₀_erase⟩⟩

/--
**Connected Subgraph Leaf-Pruning to Exact Target Size (`IsAnticonnected.exists_subset_card_eq`,
Step 1c of Proposition 5.4)**:
If $C \subseteq V$ is anticonnected in $G$ (`IsAnticonnected G C`) and $1 \le w \le |C|$, then
there exists an anticonnected subset $B \subseteq C$ of exact cardinality $|B| = w$.
-/
theorem IsAnticonnected.exists_subset_card_eq {G : SimpleGraph V} {C : Finset V}
    (hC : IsAnticonnected G C) {w : ℕ} (hw1 : 1 ≤ w) (hwC : w ≤ C.card) :
    ∃ B ⊆ C, B.card = w ∧ IsAnticonnected G B := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, C.card = w + k := Nat.exists_eq_add_of_le hwC
  induction k generalizing C with
  | zero => exact ⟨C, Subset.refl C, by omega, hC⟩
  | succ k ih =>
    have hcard2 : 2 ≤ C.card := by omega
    obtain ⟨x, hxC, hconn'⟩ := connected_induce_exists_erase hC hcard2
    have hcard_erase : (C.erase x).card = w + k := by
      have h1 := Finset.card_erase_of_mem hxC
      omega
    obtain ⟨B, hBC', hBcard, hBanti⟩ := ih hconn' (by omega) hcard_erase
    exact ⟨B, hBC'.trans (Finset.erase_subset x C), hBcard, hBanti⟩

/--
Cross-edge counting identity: $\sum_{u \in A} |N_G(u) \cap B| = \sum_{v \in B} |N_G(v) \cap A|$.
-/
theorem sum_card_neighborFinsetIn_comm (G : SimpleGraph V) (A B : Finset V) :
    (∑ u ∈ A, (neighborFinsetIn G u B).card) = ∑ v ∈ B, (neighborFinsetIn G v A).card := by
  classical
  simp only [neighborFinsetIn, Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => ?_
  rw [G.adj_comm]

/--
**Step 1d of Proposition 5.4 (`open_interval_attachment_extraction`, `FMBV4-016_readable.tex`)**:
Let $G$ be $y$-sparse on $S$, let $B : \text{Fin } \ell \to \text{Finset } V$ be a family of subsets
of $S$ with $\sum_{j} |B_j| \le y |S|$, and let $i^* \in [\ell]$ be an index such that $X := B_{i^*}$
is nonempty and at most $y |S|$ external vertices $v \in S \setminus \bigcup_j B_j$ satisfy
$0 < |N_G(v) \cap X| < \frac{1}{2}|X|$. Then the set
$Y := \{v \in S \setminus \bigcup_j B_j : N_G(v) \cap X = \emptyset\}$
is disjoint from $X$, anticomplete to $X$ in $G$, and has cardinality $|Y| \ge (1 - 4 y)|S|$.
-/
theorem open_interval_attachment_extraction
    (G : SimpleGraph V) (S : Finset V) {ℓ : ℕ} (B : Fin ℓ → Finset V) (i_star : Fin ℓ) (y : ℝ)
    (hsparse : IsEpsSparseOn G S y)
    (hBS : ∀ j : Fin ℓ, B j ⊆ S)
    (hB_sum : ((Finset.univ.biUnion B).card : ℝ) ≤ y * (S.card : ℝ))
    (hX_ne : (B i_star).Nonempty)
    (hmid : (((S \ Finset.univ.biUnion B).filter (fun v =>
      0 < (neighborFinsetIn G v (B i_star)).card ∧
      ((neighborFinsetIn G v (B i_star)).card : ℝ) < ((B i_star).card : ℝ) / 2)).card : ℝ) ≤
        y * (S.card : ℝ)) :
    ∃ Y ⊆ S, Disjoint (B i_star) Y ∧ IsAnticompletePair G Y (B i_star) ∧
      (1 - 4 * y) * (S.card : ℝ) ≤ (Y.card : ℝ) := by
  classical
  let X : Finset V := B i_star
  let U_B : Finset V := Finset.univ.biUnion B
  let U_mid : Finset V := (S \ U_B).filter (fun v =>
    0 < (neighborFinsetIn G v X).card ∧
    ((neighborFinsetIn G v X).card : ℝ) < (X.card : ℝ) / 2)
  let U_high : Finset V := S.filter (fun v =>
    (X.card : ℝ) / 2 ≤ ((neighborFinsetIn G v X).card : ℝ))
  let Y : Finset V := (S \ U_B).filter (fun v => (neighborFinsetIn G v X).card = 0)
  have hYS : Y ⊆ S := (Finset.filter_subset _ _).trans Finset.sdiff_subset
  have hX_sub_UB : X ⊆ U_B := Finset.subset_biUnion_of_mem B (Finset.mem_univ i_star)
  have hdisj : Disjoint X Y := by
    rw [Finset.disjoint_left]
    intro u huX huY
    have hu_sdiff : u ∈ S \ U_B := (Finset.mem_filter.mp huY).1
    exact (Finset.mem_sdiff.mp hu_sdiff).2 (hX_sub_UB huX)
  have hanticomp : IsAnticompletePair G Y X := by
    intro v hv x hx hadj
    have h0 : (neighborFinsetIn G v X).card = 0 := (Finset.mem_filter.mp hv).2
    have hmem : x ∈ neighborFinsetIn G v X := (mem_neighborFinsetIn_iff G v X x).mpr ⟨hx, hadj⟩
    exact absurd (Finset.card_pos.mpr ⟨x, hmem⟩) (by omega)
  -- Bound |U_high| ≤ 2 * y * |S| via Markov's inequality:
  have hX_pos : (0 : ℝ) < (X.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hX_ne
  have hsum_high :
      (U_high.card : ℝ) * ((X.card : ℝ) / 2) ≤ (X.card : ℝ) * (y * (S.card : ℝ)) := by
    calc
      (U_high.card : ℝ) * ((X.card : ℝ) / 2)
          = ∑ _v ∈ U_high, ((X.card : ℝ) / 2) := by simp
      _ ≤ ∑ v ∈ U_high, ((neighborFinsetIn G v X).card : ℝ) :=
          Finset.sum_le_sum (fun v hv => (Finset.mem_filter.mp hv).2)
      _ ≤ ∑ v ∈ S, ((neighborFinsetIn G v X).card : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ S)
            (fun _ _ _ => Nat.cast_nonneg _)
      _ = ((∑ v ∈ S, (neighborFinsetIn G v X).card : ℕ) : ℝ) := by push_cast; rfl
      _ = ((∑ x ∈ X, (neighborFinsetIn G x S).card : ℕ) : ℝ) := by
          rw [sum_card_neighborFinsetIn_comm]
      _ = ∑ x ∈ X, ((neighborFinsetIn G x S).card : ℝ) := by push_cast; rfl
      _ ≤ ∑ _x ∈ X, (y * (S.card : ℝ)) :=
          Finset.sum_le_sum (fun x hx => hsparse x (hBS i_star hx))
      _ = (X.card : ℝ) * (y * (S.card : ℝ)) := by simp
  have hhigh_le : (U_high.card : ℝ) ≤ 2 * y * (S.card : ℝ) := by
    nlinarith
  -- Partition S into U_B ∪ U_mid ∪ U_high ∪ Y:
  have hS_cover : S ⊆ ((U_B ∪ U_mid) ∪ U_high) ∪ Y := by
    intro v hvS
    by_cases hvB : v ∈ U_B
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hvB))
    · have hvsdiff : v ∈ S \ U_B := Finset.mem_sdiff.mpr ⟨hvS, hvB⟩
      by_cases h0 : (neighborFinsetIn G v X).card = 0
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hvsdiff, h0⟩)
      · have hpos : 0 < (neighborFinsetIn G v X).card := Nat.pos_of_ne_zero h0
        by_cases hlt : ((neighborFinsetIn G v X).card : ℝ) < (X.card : ℝ) / 2
        · exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hvsdiff, hpos, hlt⟩)))
        · push_neg at hlt
          exact Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨hvS, hlt⟩))
  have hS_card_nat : S.card ≤ U_B.card + U_mid.card + U_high.card + Y.card := by
    calc
      S.card ≤ (((U_B ∪ U_mid) ∪ U_high) ∪ Y).card := Finset.card_le_card hS_cover
      _ ≤ ((U_B ∪ U_mid) ∪ U_high).card + Y.card := Finset.card_union_le _ _
      _ ≤ (U_B ∪ U_mid).card + U_high.card + Y.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ U_B.card + U_mid.card + U_high.card + Y.card :=
        Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
  have hS_card_real :
      (S.card : ℝ) ≤ (U_B.card : ℝ) + (U_mid.card : ℝ) + (U_high.card : ℝ) + (Y.card : ℝ) := by
    exact_mod_cast hS_card_nat
  refine ⟨Y, hYS, hdisj, hanticomp, ?_⟩
  linarith

/-! ### Section 7: Weak-to-Strong Sparsity Cleaning and Dense-Case Leaf Extraction -/

theorem crossEdgeCount_comm (G : SimpleGraph V) (A B : Finset V) :
    crossEdgeCount G A B = crossEdgeCount G B A :=
  sum_card_neighborFinsetIn_comm G A B

theorem IsWeaklySparsePair.symm {G : SimpleGraph V} {A B : Finset V} {ε : ℝ}
    (h : IsWeaklySparsePair G A B ε) : IsWeaklySparsePair G B A ε := by
  unfold IsWeaklySparsePair at h ⊢
  rw [crossEdgeCount_comm]
  calc
    (crossEdgeCount G A B : ℝ) ≤ ε * (A.card : ℝ) * (B.card : ℝ) := h
    _ = ε * (B.card : ℝ) * (A.card : ℝ) := by ring

theorem IsCompletePair.symm {G : SimpleGraph V} {A B : Finset V}
    (h : IsCompletePair G A B) : IsCompletePair G B A :=
  fun u hu v hv => (h v hv u hu).symm

theorem IsCompletePair.mono {G : SimpleGraph V} {A B A' B' : Finset V}
    (h : IsCompletePair G A B) (hA : A' ⊆ A) (hB : B' ⊆ B) : IsCompletePair G A' B' :=
  fun u hu v hv => h u (hA hu) v (hB hv)

/--
Markov's inequality for weakly sparse pairs: if $(A, B)$ is weakly $\eta$-sparse in $G$
with $\eta \ge 0$ and $\delta > 0$, then at most $\delta |A|$ vertices $u \in A$ satisfy
$|N_G(u) \cap B| > (\eta / \delta) |B|$.
-/
theorem card_filter_neighborFinsetIn_gt_le {G : SimpleGraph V} {A B : Finset V} {η δ : ℝ}
    (hsparse : IsWeaklySparsePair G A B η) (hη : 0 ≤ η) (hδ : 0 < δ) :
    (((A.filter (fun u =>
      (η / δ) * (B.card : ℝ) < ((neighborFinsetIn G u B).card : ℝ))).card : ℝ)) ≤
      δ * (A.card : ℝ) := by
  classical
  let F := A.filter (fun u => (η / δ) * (B.card : ℝ) < ((neighborFinsetIn G u B).card : ℝ))
  by_cases hF : F.Nonempty
  · have hnonneg : 0 ≤ (η / δ) * (B.card : ℝ) :=
      mul_nonneg (div_nonneg hη (le_of_lt hδ)) (Nat.cast_nonneg _)
    by_cases hpos : 0 < (η / δ) * (B.card : ℝ)
    · have hsum : (F.card : ℝ) * ((η / δ) * (B.card : ℝ)) ≤
          (δ * (A.card : ℝ)) * ((η / δ) * (B.card : ℝ)) := by
        calc
          (F.card : ℝ) * ((η / δ) * (B.card : ℝ))
              = ∑ _u ∈ F, ((η / δ) * (B.card : ℝ)) := by simp
          _ ≤ ∑ u ∈ F, ((neighborFinsetIn G u B).card : ℝ) :=
              Finset.sum_le_sum (fun u hu => le_of_lt (Finset.mem_filter.mp hu).2)
          _ ≤ ∑ u ∈ A, ((neighborFinsetIn G u B).card : ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ A)
                (fun _ _ _ => Nat.cast_nonneg _)
          _ = (crossEdgeCount G A B : ℝ) := by unfold crossEdgeCount; push_cast; rfl
          _ ≤ η * (A.card : ℝ) * (B.card : ℝ) := hsparse
          _ = (δ * (A.card : ℝ)) * ((η / δ) * (B.card : ℝ)) := by
              have hδ_ne : δ ≠ 0 := ne_of_gt hδ
              field_simp [hδ_ne]
      exact le_of_mul_le_mul_right hsum hpos
    · obtain ⟨u₀, hu₀⟩ := hF
      have hu₀A : u₀ ∈ A := (Finset.mem_filter.mp hu₀).1
      have hu₀_gt : (η / δ) * (B.card : ℝ) < ((neighborFinsetIn G u₀ B).card : ℝ) :=
        (Finset.mem_filter.mp hu₀).2
      have heq0 : (η / δ) * (B.card : ℝ) = 0 := le_antisymm (not_lt.mp hpos) hnonneg
      have hηB0 : η * (B.card : ℝ) = 0 := by
        have hδ_ne : δ ≠ 0 := ne_of_gt hδ
        calc
          η * (B.card : ℝ) = δ * ((η / δ) * (B.card : ℝ)) := by field_simp [hδ_ne]
          _ = 0 := by rw [heq0, mul_zero]
      have hcross0 : (crossEdgeCount G A B : ℝ) ≤ 0 := by
        calc
          (crossEdgeCount G A B : ℝ) ≤ η * (A.card : ℝ) * (B.card : ℝ) := hsparse
          _ = (A.card : ℝ) * (η * (B.card : ℝ)) := by ring
          _ = 0 := by rw [hηB0, mul_zero]
      have hu₀_nat : (neighborFinsetIn G u₀ B).card ≤ crossEdgeCount G A B :=
        Finset.single_le_sum (f := fun u => (neighborFinsetIn G u B).card)
          (fun _ _ => Nat.zero_le _) hu₀A
      have hu₀_le : ((neighborFinsetIn G u₀ B).card : ℝ) ≤ (crossEdgeCount G A B : ℝ) := by
        exact_mod_cast hu₀_nat
      linarith
  · rw [Finset.not_nonempty_iff_eq_empty] at hF
    change (F.card : ℝ) ≤ δ * (A.card : ℝ)
    rw [hF, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (le_of_lt hδ) (Nat.cast_nonneg _)

/--
**Step 1b of Proposition 5.4 (`weaklySparse_to_xSparse_cleaning`, `FMBV4-016_readable.tex`)**:
Given an equal-size family $X : \text{Fin } \ell \to \text{Finset } V$ with $|X_i| = m$ whose
distinct pairs are complete or weakly $\eta$-sparse in $G$, removing high-degree bad vertices for
each non-complete pair yields subsets $D_i \subseteq X_i$ with $(1 - \ell \delta) m \le |D_i| \le m$
(so $|D_i| \ge m / 2$ when $\ell \delta \le 1 / 2$) such that every distinct pair $(D_i, D_j)$ is
complete or $(2 \eta / \delta)$-sparse in both directions in $G$.
-/
theorem weaklySparse_to_xSparse_cleaning
    (G : SimpleGraph V) {ℓ m : ℕ} (X : Fin ℓ → Finset V) (η δ : ℝ)
    (hcard : ∀ i : Fin ℓ, (X i).card = m)
    (hη : 0 ≤ η) (hδ : 0 < δ) (hℓδ : (ℓ : ℝ) * δ ≤ 1 / 2)
    (hpairs : ∀ i j : Fin ℓ, i ≠ j →
      IsCompletePair G (X i) (X j) ∨ IsWeaklySparsePair G (X i) (X j) η) :
    ∃ D : Fin ℓ → Finset V,
      (∀ i : Fin ℓ, D i ⊆ X i) ∧
      (∀ i : Fin ℓ, (1 - (ℓ : ℝ) * δ) * (m : ℝ) ≤ ((D i).card : ℝ)) ∧
      (∀ i : Fin ℓ, (m : ℝ) / 2 ≤ ((D i).card : ℝ)) ∧
      (∀ i j : Fin ℓ, i ≠ j → IsCompleteOrXSparsePair G (D i) (D j) (2 * η / δ)) := by
  classical
  let bad : Fin ℓ → Fin ℓ → Finset V := fun i j =>
    if i ≠ j ∧ ¬IsCompletePair G (X i) (X j) then
      (X i).filter (fun u =>
        (η / δ) * ((X j).card : ℝ) < ((neighborFinsetIn G u (X j)).card : ℝ))
    else ∅
  let D : Fin ℓ → Finset V := fun i => X i \ Finset.univ.biUnion (bad i)
  have hbad_card : ∀ i j : Fin ℓ, ((bad i j).card : ℝ) ≤ δ * (m : ℝ) := by
    intro i j
    dsimp [bad]
    split_ifs with h
    · have hsparse : IsWeaklySparsePair G (X i) (X j) η :=
        (hpairs i j h.1).resolve_left h.2
      have hle := card_filter_neighborFinsetIn_gt_le hsparse hη hδ
      rwa [hcard i] at hle
    · rw [Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg (le_of_lt hδ) (Nat.cast_nonneg _)
  have hD_card : ∀ i : Fin ℓ, (1 - (ℓ : ℝ) * δ) * (m : ℝ) ≤ ((D i).card : ℝ) := by
    intro i
    let U_i := Finset.univ.biUnion (bad i)
    have hU_nat : U_i.card ≤ ∑ j : Fin ℓ, (bad i j).card := Finset.card_biUnion_le
    have hU_real : (U_i.card : ℝ) ≤ (ℓ : ℝ) * (δ * (m : ℝ)) := by
      calc
        (U_i.card : ℝ) ≤ ∑ j : Fin ℓ, ((bad i j).card : ℝ) := by exact_mod_cast hU_nat
        _ ≤ ∑ _j : Fin ℓ, (δ * (m : ℝ)) := Finset.sum_le_sum (fun j _ => hbad_card i j)
        _ = (ℓ : ℝ) * (δ * (m : ℝ)) := by simp
    have hcov : X i ⊆ D i ∪ U_i := by
      intro u hu
      by_cases huU : u ∈ U_i
      · exact Finset.mem_union_right _ huU
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hu, huU⟩)
    have hX_nat : (X i).card ≤ (D i).card + U_i.card :=
      (Finset.card_le_card hcov).trans (Finset.card_union_le _ _)
    have hX_real : (m : ℝ) ≤ ((D i).card : ℝ) + (U_i.card : ℝ) := by
      rw [← hcard i]
      exact_mod_cast hX_nat
    linarith
  have hD_half : ∀ i : Fin ℓ, (m : ℝ) / 2 ≤ ((D i).card : ℝ) := by
    intro i
    have h1 := hD_card i
    have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith
  have hD_sparse_one : ∀ i j : Fin ℓ, i ≠ j → ¬IsCompletePair G (X i) (X j) →
      IsXSparseTo G (D i) (D j) (2 * η / δ) := by
    intro i j hij hnot u huD
    have huX : u ∈ X i := (Finset.mem_sdiff.mp huD).1
    have hu_not_U : u ∉ Finset.univ.biUnion (bad i) := (Finset.mem_sdiff.mp huD).2
    have hu_not_bad : u ∉ bad i j :=
      fun h => hu_not_U (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, h⟩)
    have hcond : i ≠ j ∧ ¬IsCompletePair G (X i) (X j) := ⟨hij, hnot⟩
    have hu_le_X : ((neighborFinsetIn G u (X j)).card : ℝ) ≤ (η / δ) * (m : ℝ) := by
      by_contra hgt
      push_neg at hgt
      apply hu_not_bad
      dsimp [bad]
      rw [if_pos hcond]
      refine Finset.mem_filter.mpr ⟨huX, ?_⟩
      rwa [hcard j]
    have hsub : neighborFinsetIn G u (D j) ⊆ neighborFinsetIn G u (X j) :=
      neighborFinsetIn_mono G u Finset.sdiff_subset
    have hu_le_D : ((neighborFinsetIn G u (D j)).card : ℝ) ≤ ((neighborFinsetIn G u (X j)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hDj : (m : ℝ) ≤ 2 * ((D j).card : ℝ) := by linarith [hD_half j]
    have hηδ : 0 ≤ η / δ := div_nonneg hη (le_of_lt hδ)
    calc
      ((neighborFinsetIn G u (D j)).card : ℝ)
          ≤ (η / δ) * (m : ℝ) := hu_le_D.trans hu_le_X
      _ ≤ (η / δ) * (2 * ((D j).card : ℝ)) := mul_le_mul_of_nonneg_left hDj hηδ
      _ = (2 * η / δ) * ((D j).card : ℝ) := by ring
  refine ⟨D, fun _ => Finset.sdiff_subset, hD_card, hD_half, ?_⟩
  intro i j hij
  by_cases hcomp : IsCompletePair G (X i) (X j)
  · exact Or.inl (hcomp.mono Finset.sdiff_subset Finset.sdiff_subset)
  · have hcomp_ji : ¬IsCompletePair G (X j) (X i) := fun h => hcomp h.symm
    exact Or.inr ⟨hD_sparse_one j i hij.symm hcomp_ji, hD_sparse_one i j hij hcomp⟩

/--
**Step 1a of Proposition 5.4 (`exists_equal_size_weaklySparse_subblockade`, `FMBV4-016_readable.tex`)**:
Given a family $A : \text{Fin } \ell \to \text{Finset } V$ whose distinct pairs are complete or
weakly $\eta$-sparse in $G$, and any target size $m \in \mathbb{N}$ satisfying
$m \le (1 - \ell \delta) |A_i|$ for all $i \in [\ell]$, sequential Markov selection produces
subsets $X_i \subseteq A_i$ of exact size $|X_i| = m$ such that every distinct pair $(X_i, X_j)$
is complete or weakly $(\eta / \delta^2)$-sparse in $G$.
-/
theorem exists_equal_size_weaklySparse_subblockade
    (G : SimpleGraph V) {ℓ m : ℕ} (A : Fin ℓ → Finset V) (η δ : ℝ)
    (hη : 0 ≤ η) (hδ : 0 < δ)
    (hm : ∀ i : Fin ℓ, (m : ℝ) ≤ (1 - (ℓ : ℝ) * δ) * ((A i).card : ℝ))
    (hpairs : ∀ i j : Fin ℓ, i ≠ j →
      IsCompletePair G (A i) (A j) ∨ IsWeaklySparsePair G (A i) (A j) η) :
    ∃ X : Fin ℓ → Finset V,
      (∀ i : Fin ℓ, X i ⊆ A i) ∧
      (∀ i : Fin ℓ, (X i).card = m) ∧
      (∀ i j : Fin ℓ, i ≠ j →
        IsCompletePair G (X i) (X j) ∨ IsWeaklySparsePair G (X i) (X j) (η / δ ^ 2)) := by
  classical
  let scale : ℕ → Fin ℓ → Fin ℓ → ℝ := fun k i j =>
    η * (if i.val < k then δ⁻¹ else 1) * (if j.val < k then δ⁻¹ else 1)
  have hscale_nonneg : ∀ k i j, 0 ≤ scale k i j := by
    intro k i j
    dsimp [scale]
    have h1 : 0 ≤ (if i.val < k then δ⁻¹ else (1 : ℝ)) := by split_ifs <;> positivity
    have h2 : 0 ≤ (if j.val < k then δ⁻¹ else (1 : ℝ)) := by split_ifs <;> positivity
    positivity
  have hscale_symm : ∀ k i j, scale k i j = scale k j i := by
    intro k i j
    dsimp [scale]
    ring
  have hind : ∀ k : ℕ, k ≤ ℓ → ∃ X : Fin ℓ → Finset V,
      (∀ i : Fin ℓ, X i ⊆ A i) ∧
      (∀ i : Fin ℓ, i.val < k → (X i).card = m) ∧
      (∀ i : Fin ℓ, k ≤ i.val → X i = A i) ∧
      (∀ i j : Fin ℓ, i ≠ j → ¬IsCompletePair G (A i) (A j) →
        IsWeaklySparsePair G (X i) (X j) (scale k i j)) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨A, fun _ => Subset.refl _, fun _ hi => (Nat.not_lt_zero _ hi).elim,
        fun _ _ => rfl, ?_⟩
      intro i j hij hnot
      have h0 : scale 0 i j = η := by simp [scale]
      rw [h0]
      exact (hpairs i j hij).resolve_left hnot
    | succ k ih =>
      intro hk1
      obtain ⟨X, hXA, hXcard, hXeq, hXsparse⟩ := ih (by omega)
      let i₀ : Fin ℓ := ⟨k, by omega⟩
      have hXi₀ : X i₀ = A i₀ := hXeq i₀ (le_refl k)
      let bad : Fin ℓ → Finset V := fun j =>
        if j ≠ i₀ ∧ ¬IsCompletePair G (A i₀) (A j) then
          (A i₀).filter (fun u =>
            (scale k i₀ j / δ) * ((X j).card : ℝ) < ((neighborFinsetIn G u (X j)).card : ℝ))
        else ∅
      have hbad_card : ∀ j : Fin ℓ, ((bad j).card : ℝ) ≤ δ * ((A i₀).card : ℝ) := by
        intro j
        dsimp [bad]
        split_ifs with h
        · have hsp : IsWeaklySparsePair G (A i₀) (X j) (scale k i₀ j) := by
            rw [← hXi₀]
            exact hXsparse i₀ j (Ne.symm h.1) h.2
          exact card_filter_neighborFinsetIn_gt_le hsp (hscale_nonneg k i₀ j) hδ
        · rw [Finset.card_empty, Nat.cast_zero]
          exact mul_nonneg (le_of_lt hδ) (Nat.cast_nonneg _)
      let U_bad := Finset.univ.biUnion bad
      have hU_nat : U_bad.card ≤ ∑ j : Fin ℓ, (bad j).card := Finset.card_biUnion_le
      have hU_real : (U_bad.card : ℝ) ≤ (ℓ : ℝ) * (δ * ((A i₀).card : ℝ)) := by
        calc
          (U_bad.card : ℝ) ≤ ∑ j : Fin ℓ, ((bad j).card : ℝ) := by exact_mod_cast hU_nat
          _ ≤ ∑ _j : Fin ℓ, (δ * ((A i₀).card : ℝ)) := Finset.sum_le_sum (fun j _ => hbad_card j)
          _ = (ℓ : ℝ) * (δ * ((A i₀).card : ℝ)) := by simp
      let G_good := A i₀ \ U_bad
      have hcov : A i₀ ⊆ G_good ∪ U_bad := by
        intro u hu
        by_cases huU : u ∈ U_bad
        · exact Finset.mem_union_right _ huU
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hu, huU⟩)
      have hA_nat : (A i₀).card ≤ G_good.card + U_bad.card :=
        (Finset.card_le_card hcov).trans (Finset.card_union_le _ _)
      have hA_real : ((A i₀).card : ℝ) ≤ (G_good.card : ℝ) + (U_bad.card : ℝ) := by
        exact_mod_cast hA_nat
      have hm_le_real : (m : ℝ) ≤ (G_good.card : ℝ) := by
        linarith [hm i₀]
      have hm_le_nat : m ≤ G_good.card := by exact_mod_cast hm_le_real
      obtain ⟨Y₀, hY₀_sub, hY₀_card⟩ := Finset.exists_subset_card_eq hm_le_nat
      let X' : Fin ℓ → Finset V := Function.update X i₀ Y₀
      have hY₀_A : Y₀ ⊆ A i₀ := hY₀_sub.trans Finset.sdiff_subset
      have hX'_sub : ∀ i : Fin ℓ, X' i ⊆ A i := by
        intro i
        dsimp [X']
        by_cases hi : i = i₀
        · subst hi; simp [hY₀_A]
        · simp [hi, hXA i]
      have hX'_card : ∀ i : Fin ℓ, i.val < k + 1 → (X' i).card = m := by
        intro i hi
        dsimp [X']
        by_cases hi₀ : i = i₀
        · subst hi₀; simp [hY₀_card]
        · have hik : i.val < k := by
            have hne : i.val ≠ k := fun h => hi₀ (Fin.ext h)
            omega
          simp [hi₀, hXcard i hik]
      have hX'_eq : ∀ i : Fin ℓ, k + 1 ≤ i.val → X' i = A i := by
        intro i hi
        have hi₀ : i ≠ i₀ := fun h => by
          have : i.val = k := congr_arg Fin.val h
          omega
        dsimp [X']
        rw [Function.update_of_ne hi₀]
        exact hXeq i (by omega)
      have hstep_i₀ : ∀ j : Fin ℓ, j ≠ i₀ → ¬IsCompletePair G (A i₀) (A j) →
          IsWeaklySparsePair G (X' i₀) (X' j) (scale (k + 1) i₀ j) := by
        intro j hj hnot
        have hX'i₀ : X' i₀ = Y₀ := Function.update_self i₀ Y₀ X
        have hX'j : X' j = X j := Function.update_of_ne hj Y₀ X
        rw [hX'i₀, hX'j]
        have hscale_step : scale (k + 1) i₀ j = scale k i₀ j / δ := by
          have hi₀_k : ¬ (i₀.val < k) := Nat.lt_irrefl k
          have hi₀_k1 : i₀.val < k + 1 := Nat.lt_succ_self k
          have hj_ne : j.val ≠ k := fun h => hj (Fin.ext h)
          have hj_iff : (j.val < k + 1) ↔ (j.val < k) := by omega
          dsimp [scale]
          simp only [hi₀_k, hi₀_k1, hj_iff, ↓reduceIte]
          ring
        have hu_bound : ∀ u ∈ Y₀,
            ((neighborFinsetIn G u (X j)).card : ℝ) ≤ scale (k + 1) i₀ j * ((X j).card : ℝ) := by
          intro u huY₀
          have hu_good : u ∈ G_good := hY₀_sub huY₀
          have huA : u ∈ A i₀ := (Finset.mem_sdiff.mp hu_good).1
          have hu_not_U : u ∉ U_bad := (Finset.mem_sdiff.mp hu_good).2
          have hu_not_bad : u ∉ bad j :=
            fun h => hu_not_U (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, h⟩)
          have hcond : j ≠ i₀ ∧ ¬IsCompletePair G (A i₀) (A j) := ⟨hj, hnot⟩
          rw [hscale_step]
          by_contra hgt
          push_neg at hgt
          apply hu_not_bad
          dsimp [bad]
          rw [if_pos hcond]
          exact Finset.mem_filter.mpr ⟨huA, hgt⟩
        unfold IsWeaklySparsePair crossEdgeCount
        calc
          ((∑ u ∈ Y₀, (neighborFinsetIn G u (X j)).card : ℕ) : ℝ)
              = ∑ u ∈ Y₀, ((neighborFinsetIn G u (X j)).card : ℝ) := by push_cast; rfl
          _ ≤ ∑ _u ∈ Y₀, (scale (k + 1) i₀ j * ((X j).card : ℝ)) :=
              Finset.sum_le_sum hu_bound
          _ = (Y₀.card : ℝ) * (scale (k + 1) i₀ j * ((X j).card : ℝ)) := by simp
          _ = scale (k + 1) i₀ j * (Y₀.card : ℝ) * ((X j).card : ℝ) := by ring
      refine ⟨X', hX'_sub, hX'_card, hX'_eq, ?_⟩
      intro i j hij hnot
      by_cases hi : i = i₀
      · subst hi
        exact hstep_i₀ j hij.symm hnot
      · by_cases hj : j = i₀
        · subst hj
          have hnot' : ¬IsCompletePair G (A i₀) (A i) := fun h => hnot h.symm
          rw [hscale_symm (k + 1) i i₀]
          exact (hstep_i₀ i hij hnot').symm
        · have hX'i : X' i = X i := Function.update_of_ne hi Y₀ X
          have hX'j : X' j = X j := Function.update_of_ne hj Y₀ X
          have hi_ne : i.val ≠ k := fun h => hi (Fin.ext h)
          have hj_ne : j.val ≠ k := fun h => hj (Fin.ext h)
          have hi_iff : (i.val < k + 1) ↔ (i.val < k) := by omega
          have hj_iff : (j.val < k + 1) ↔ (j.val < k) := by omega
          have hscale_eq : scale (k + 1) i j = scale k i j := by
            dsimp [scale]
            simp only [hi_iff, hj_iff]
          rw [hX'i, hX'j, hscale_eq]
          exact hXsparse i j hij hnot
  obtain ⟨X, hXA, hXcard, -, hXsparse⟩ := hind ℓ (le_refl ℓ)
  refine ⟨X, hXA, fun i => hXcard i i.isLt, ?_⟩
  intro i j hij
  by_cases hcomp : IsCompletePair G (A i) (A j)
  · exact Or.inl (hcomp.mono (hXA i) (hXA j))
  · right
    have hsp := hXsparse i j hij hcomp
    have hscale_ℓ : scale ℓ i j = η / δ ^ 2 := by
      dsimp [scale]
      simp only [i.isLt, j.isLt, ↓reduceIte]
      ring
    rwa [hscale_ℓ] at hsp

/--
**Dense-Case Common Neighborhood Extraction (`common_neighbors_complete_pair`)**:
Let $\overline{G}[S]$ be $y$-sparse (`IsEpsSparseOn Gᶜ S y`), let $X, R \subseteq S$, and suppose
that every $x \in X$ has $N_{\overline{G}}(x) \cap S \subseteq R \cup \bigcup_{r \in R} (N_{\overline{G}}(r) \cap S)$.
Then the set $Y := S \setminus \bigl(X \cup R \cup \bigcup_{r \in R} (N_{\overline{G}}(r) \cap S)\bigr)$
satisfies $Y \subseteq S$, `Disjoint X Y`, `IsCompletePair G Y X`, and
$|Y| \ge |S| - |X| - |R| (1 + y |S|)$.
-/
theorem common_neighbors_complete_pair
    (G : SimpleGraph V) (S X R : Finset V) (y : ℝ)
    (hsparse : IsEpsSparseOn Gᶜ S y)
    (hRS : R ⊆ S)
    (hcover : ∀ x ∈ X,
      neighborFinsetIn Gᶜ x S ⊆ R ∪ R.biUnion (fun r => neighborFinsetIn Gᶜ r S)) :
    ∃ Y ⊆ S, Disjoint X Y ∧ IsCompletePair G Y X ∧
      (S.card : ℝ) - (X.card : ℝ) - (R.card : ℝ) * (1 + y * (S.card : ℝ)) ≤ (Y.card : ℝ) := by
  classical
  let U : Finset V := R ∪ R.biUnion (fun r => neighborFinsetIn Gᶜ r S)
  let Y : Finset V := S \ (X ∪ U)
  have hYS : Y ⊆ S := Finset.sdiff_subset
  have hdisj : Disjoint X Y := by
    rw [Finset.disjoint_left]
    intro u huX huY
    exact (Finset.mem_sdiff.mp huY).2 (Finset.mem_union_left _ huX)
  have hcomp : IsCompletePair G Y X := by
    intro v hvY x hxX
    have hvS : v ∈ S := (Finset.mem_sdiff.mp hvY).1
    have hv_not : v ∉ X ∪ U := (Finset.mem_sdiff.mp hvY).2
    have hvX : v ∉ X := fun h => hv_not (Finset.mem_union_left _ h)
    have hvU : v ∉ U := fun h => hv_not (Finset.mem_union_right _ h)
    have hv_ne_x : v ≠ x := fun h => hvX (h ▸ hxX)
    by_contra hnot_adj
    have hcompl_adj : Gᶜ.Adj x v := by
      rw [compl_adj]
      exact ⟨hv_ne_x.symm, fun h => hnot_adj h.symm⟩
    have hv_neigh : v ∈ neighborFinsetIn Gᶜ x S :=
      (mem_neighborFinsetIn_iff Gᶜ x S v).mpr ⟨hvS, hcompl_adj⟩
    exact hvU (hcover x hxX hv_neigh)
  have hbiUnion_nat :
      (R.biUnion (fun r => neighborFinsetIn Gᶜ r S)).card ≤
        ∑ r ∈ R, (neighborFinsetIn Gᶜ r S).card := Finset.card_biUnion_le
  have hbiUnion_real :
      ((R.biUnion (fun r => neighborFinsetIn Gᶜ r S)).card : ℝ) ≤
        (R.card : ℝ) * (y * (S.card : ℝ)) := by
    calc
      ((R.biUnion (fun r => neighborFinsetIn Gᶜ r S)).card : ℝ)
          ≤ ∑ r ∈ R, ((neighborFinsetIn Gᶜ r S).card : ℝ) := by exact_mod_cast hbiUnion_nat
      _ ≤ ∑ _r ∈ R, (y * (S.card : ℝ)) := Finset.sum_le_sum (fun r hr => hsparse r (hRS hr))
      _ = (R.card : ℝ) * (y * (S.card : ℝ)) := by simp
  have hU_nat : U.card ≤ R.card + (R.biUnion (fun r => neighborFinsetIn Gᶜ r S)).card :=
    Finset.card_union_le _ _
  have hU_real : (U.card : ℝ) ≤ (R.card : ℝ) * (1 + y * (S.card : ℝ)) := by
    have h1 : (U.card : ℝ) ≤ (R.card : ℝ) + ((R.biUnion (fun r => neighborFinsetIn Gᶜ r S)).card : ℝ) := by
      exact_mod_cast hU_nat
    linarith
  have hS_cov : S ⊆ (X ∪ U) ∪ Y := by
    intro v hvS
    by_cases hv : v ∈ X ∪ U
    · exact Finset.mem_union_left _ hv
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hvS, hv⟩)
  have hS_nat : S.card ≤ X.card + U.card + Y.card := by
    calc
      S.card ≤ ((X ∪ U) ∪ Y).card := Finset.card_le_card hS_cov
      _ ≤ (X ∪ U).card + Y.card := Finset.card_union_le _ _
      _ ≤ X.card + U.card + Y.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
  have hS_real : (S.card : ℝ) ≤ (X.card : ℝ) + (U.card : ℝ) + (Y.card : ℝ) := by
    exact_mod_cast hS_nat
  refine ⟨Y, hYS, hdisj, hcomp, ?_⟩
  linarith

/--
Special case of `common_neighbors_complete_pair` with $R = X$: in any graph $G$ where $\overline{G}[S]$
is $y$-sparse, for any $X \subseteq S$, the common neighborhood of $X$ in $S \setminus X$ has
cardinality at least $|S| - |X|(2 + y |S|)$ and is complete to $X$ in $G$.
-/
theorem common_neighbors_complete_pair_self
    (G : SimpleGraph V) (S X : Finset V) (y : ℝ)
    (hsparse : IsEpsSparseOn Gᶜ S y) (hXS : X ⊆ S) :
    ∃ Y ⊆ S, Disjoint X Y ∧ IsCompletePair G Y X ∧
      (S.card : ℝ) - (X.card : ℝ) * (2 + y * (S.card : ℝ)) ≤ (Y.card : ℝ) := by
  obtain ⟨Y, hYS, hdisj, hcomp, hcard⟩ :=
    common_neighbors_complete_pair G S X X y hsparse hXS (fun x hx =>
      (Finset.subset_biUnion_of_mem (fun r => neighborFinsetIn Gᶜ r S) hx).trans
        Finset.subset_union_right)
  refine ⟨Y, hYS, hdisj, hcomp, ?_⟩
  linarith

/--
Extending an induced copy of $\overline{P_5}$ (`P5Compl`) to $\overline{P_6}$ (`P6Compl`):
if $g : \text{Fin } 5 \hookrightarrow V$ satisfies `P5Compl = G.comap g` and $v \in V$ is distinct
from all $g(i)$, adjacent in $G$ to $g(0), g(1), g(2), g(3)$, and non-adjacent in $G$ to $g(4)$,
then $(g(0), \dots, g(4), v)$ induces `P6Compl` in $G$.
-/
theorem P5Compl_extend_to_P6Compl
    {G : SimpleGraph V} (g : Fin 5 ↪ V) (hg : P5Compl = G.comap g) (v : V)
    (hv_ne : ∀ i : Fin 5, v ≠ g i)
    (hv_adj : ∀ i : Fin 5, i.val < 4 → G.Adj (g i) v)
    (hv_nadj : ¬G.Adj (g 4) v) :
    ∃ g6 : Fin 6 ↪ V, P6Compl = G.comap g6 := by
  let f : Fin 6 → V := fun i => if h : i.val < 5 then g ⟨i.val, h⟩ else v
  have hf_inj : Function.Injective f := by
    intro i j hij
    dsimp [f] at hij
    split_ifs at hij with hi hj hj
    · have heq := g.injective hij
      have hval : i.val = j.val := congr_arg (Fin.val : Fin 5 → ℕ) heq
      exact Fin.ext hval
    · exact (hv_ne ⟨i.val, hi⟩ hij.symm).elim
    · exact (hv_ne ⟨j.val, hj⟩ hij).elim
    · omega
  let g6 : Fin 6 ↪ V := ⟨f, hf_inj⟩
  have hadj_lt : ∀ i j : Fin 6, i.val < j.val → (P6Compl.Adj i j ↔ G.Adj (f i) (f j)) := by
    intro i j hij
    have hi : i.val < 5 := by omega
    by_cases hj : j.val < 5
    · have hfi : f i = g ⟨i.val, hi⟩ := dif_pos hi
      have hfj : f j = g ⟨j.val, hj⟩ := dif_pos hj
      rw [hfi, hfj]
      have hg_iff : P5Compl.Adj ⟨i.val, hi⟩ ⟨j.val, hj⟩ ↔ G.Adj (g ⟨i.val, hi⟩) (g ⟨j.val, hj⟩) := by
        rw [hg]
        rfl
      rw [← hg_iff]
      simp only [P6Compl, P5Compl, compl_adj, pathGraph_adj, ne_eq, Fin.ext_iff, Fin.val_mk]
    · have hfi : f i = g ⟨i.val, hi⟩ := dif_pos hi
      have hfj : f j = v := dif_neg hj
      rw [hfi, hfj]
      have hj5 : j.val = 5 := by omega
      have hP6 : P6Compl.Adj i j ↔ i.val < 4 := by
        simp only [P6Compl, compl_adj, pathGraph_adj, ne_eq, Fin.ext_iff]
        omega
      rw [hP6]
      by_cases hi4 : i.val < 4
      · exact iff_of_true hi4 (hv_adj ⟨i.val, hi⟩ hi4)
      · have hi_eq4 : (⟨i.val, hi⟩ : Fin 5) = 4 := by ext; dsimp; omega
        rw [hi_eq4]
        exact iff_of_false hi4 hv_nadj
  refine ⟨g6, SimpleGraph.ext ?_⟩
  funext i j
  rw [eq_iff_iff]
  change P6Compl.Adj i j ↔ G.Adj (f i) (f j)
  rcases lt_trichotomy i.val j.val with hlt | heq | hgt
  · exact hadj_lt i j hlt
  · have hij : i = j := Fin.ext heq
    subst hij
    simp
  · rw [P6Compl.adj_comm, G.adj_comm]
    exact hadj_lt j i hgt

/--
**$\overline{P_6}$-Free Leaf-Extension Complete Pair Extraction (`P6Compl_free_leaf_complete_pair`,
used in the proof of Lemma 2.7 / `lem:leaf-dense`)**:
Let $G$ be $\overline{P_6}$-free (`IsInducedSubgraphFree G P6Compl`), let $\overline{G}[S]$ be
$y$-sparse (`IsEpsSparseOn Gᶜ S y`), let $u : \text{Fin } 4 \to V$ be a 4-tuple of vertices in $S$,
and let $X \subseteq S$ be any set of vertices such that for every $x \in X$, $(u_0, u_1, u_2, u_3, x)$
induces $\overline{P_5}$ in $G$. Then there exists $Y \subseteq S$ disjoint from $X$ and complete
to $X$ in $G$ (`IsCompletePair G Y X`) with $|Y| \ge |S| - |X| - 4 (1 + y |S|)$.
-/
theorem P6Compl_free_leaf_complete_pair
    {G : SimpleGraph V} (hfree : IsInducedSubgraphFree G P6Compl)
    (S X : Finset V) (u : Fin 4 → V) (y : ℝ)
    (hy : 0 ≤ y)
    (hsparse : IsEpsSparseOn Gᶜ S y)
    (huS : ∀ r : Fin 4, u r ∈ S)
    (hX_ext : ∀ x ∈ X, ∃ g : Fin 5 ↪ V, P5Compl = G.comap g ∧
      (∀ r : Fin 4, g r.castSucc = u r) ∧ g 4 = x) :
    ∃ Y ⊆ S, Disjoint X Y ∧ IsCompletePair G Y X ∧
      (S.card : ℝ) - (X.card : ℝ) - 4 * (1 + y * (S.card : ℝ)) ≤ (Y.card : ℝ) := by
  classical
  let R : Finset V := Finset.univ.image u
  have hRS : R ⊆ S := by
    intro z hz
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hz
    exact huS r
  have hR_card : (R.card : ℝ) ≤ 4 := by
    have h1 : R.card ≤ (Finset.univ : Finset (Fin 4)).card := Finset.card_image_le
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    exact_mod_cast h1
  have hcover : ∀ x ∈ X,
      neighborFinsetIn Gᶜ x S ⊆ R ∪ R.biUnion (fun r => neighborFinsetIn Gᶜ r S) := by
    intro x hx v hv
    have hvS : v ∈ S := (mem_neighborFinsetIn_iff Gᶜ x S v).mp hv |>.1
    have hxv_compl : Gᶜ.Adj x v := (mem_neighborFinsetIn_iff Gᶜ x S v).mp hv |>.2
    have hxv_ne : v ≠ x := (compl_adj G x v).mp hxv_compl |>.1.symm
    have hxv_nadj : ¬G.Adj x v := (compl_adj G x v).mp hxv_compl |>.2
    by_cases hvR : v ∈ R
    · exact Finset.mem_union_left _ hvR
    · refine Finset.mem_union_right _ ?_
      obtain ⟨g, hg, hgu, hgx⟩ := hX_ext x hx
      have hv_ne_g : ∀ i : Fin 5, v ≠ g i := by
        intro i hvi
        by_cases hi4 : i.val < 4
        · have hi_eq : i = (⟨i.val, hi4⟩ : Fin 4).castSucc := by ext; rfl
          rw [hi_eq, hgu] at hvi
          exact hvR (Finset.mem_image.mpr ⟨⟨i.val, hi4⟩, Finset.mem_univ _, hvi.symm⟩)
        · have hi_eq4 : i = 4 := by ext; dsimp; omega
          rw [hi_eq4, hgx] at hvi
          exact hxv_ne hvi
      have hex_not_adj : ∃ r : Fin 4, ¬G.Adj (u r) v := by
        by_contra hall
        push_neg at hall
        have hv_adj_g : ∀ i : Fin 5, i.val < 4 → G.Adj (g i) v := by
          intro i hi4
          have hi_eq : i = (⟨i.val, hi4⟩ : Fin 4).castSucc := by ext; rfl
          rw [hi_eq, hgu]
          exact hall ⟨i.val, hi4⟩
        have hv_nadj_g4 : ¬G.Adj (g 4) v := by
          rwa [hgx]
        exact hfree (P5Compl_extend_to_P6Compl g hg v hv_ne_g hv_adj_g hv_nadj_g4)
      obtain ⟨r, hr_nadj⟩ := hex_not_adj
      have hur_R : u r ∈ R := Finset.mem_image_of_mem u (Finset.mem_univ r)
      have hv_ne_ur : u r ≠ v := fun h => hvR (h ▸ hur_R)
      have hur_compl : Gᶜ.Adj (u r) v := (compl_adj G (u r) v).mpr ⟨hv_ne_ur, hr_nadj⟩
      exact Finset.mem_biUnion.mpr ⟨u r, hur_R,
        (mem_neighborFinsetIn_iff Gᶜ (u r) S v).mpr ⟨hvS, hur_compl⟩⟩
  obtain ⟨Y, hYS, hdisj, hcomp, hY_card⟩ :=
    common_neighbors_complete_pair G S X R y hsparse hRS hcover
  have h1y_nn : 0 ≤ 1 + y * (S.card : ℝ) := by positivity
  have hR_prod : (R.card : ℝ) * (1 + y * (S.card : ℝ)) ≤ 4 * (1 + y * (S.card : ℝ)) :=
    mul_le_mul_of_nonneg_right hR_card h1y_nn
  refine ⟨Y, hYS, hdisj, hcomp, ?_⟩
  linarith

/-! ### Section 8: Anticonnected Component Blockade Lemma (Lemma 2.5 / `lem:anticonn-blockade`) -/

/--
Greedy subset-sum interval lemma: if $0 \le c_i \le M$ for all $i \in R$ and $w \le \sum_{i \in R} c_i$
with $w, M \ge 0$, then there exists a subset $I \subseteq R$ with $w \le \sum_{i \in I} c_i \le w + M$.
-/
theorem exists_subset_sum_mem_Icc {α : Type*} [DecidableEq α]
    (R : Finset α) (c : α → ℝ) (w M : ℝ)
    (hw : 0 ≤ w) (hM : 0 ≤ M)
    (hc_nonneg : ∀ i ∈ R, 0 ≤ c i) (hc_le : ∀ i ∈ R, c i ≤ M)
    (hsum : w ≤ ∑ i ∈ R, c i) :
    ∃ I ⊆ R, w ≤ ∑ i ∈ I, c i ∧ ∑ i ∈ I, c i ≤ w + M := by
  induction R using Finset.induction_on with
  | empty =>
    refine ⟨∅, Subset.refl _, hsum, ?_⟩
    simp only [Finset.sum_empty] at hsum ⊢
    linarith
  | @insert a R ha ih =>
    have hc_nonneg' : ∀ i ∈ R, 0 ≤ c i := fun i hi => hc_nonneg i (Finset.mem_insert_of_mem hi)
    have hc_le' : ∀ i ∈ R, c i ≤ M := fun i hi => hc_le i (Finset.mem_insert_of_mem hi)
    by_cases hR : w ≤ ∑ i ∈ R, c i
    · obtain ⟨I, hIR, hIw, hIM⟩ := ih hc_nonneg' hc_le' hR
      exact ⟨I, hIR.trans (Finset.subset_insert a R), hIw, hIM⟩
    · push_neg at hR
      refine ⟨insert a R, Subset.refl _, hsum, ?_⟩
      rw [Finset.sum_insert ha]
      have haM : c a ≤ M := hc_le a (Finset.mem_insert_self a R)
      linarith

/--
Iterated greedy grouping: if $0 \le c_i \le M$ for all $i \in R$ and
$\sum_{i \in R} c_i \ge m (w + M) - M$ for $m \ge 1$, then $R$ contains $m$ pairwise disjoint
subsets $I_0, \dots, I_{m-1} \subseteq R$ each satisfying $\sum_{i \in I_s} c_i \ge w$.
-/
theorem exists_disjoint_family_sum_ge {α : Type*} [DecidableEq α]
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
      refine ⟨fun _ => R, fun _ => Subset.refl _, ?_, ?_⟩
      · intro s t hst
        exfalso
        apply hst
        ext
        omega
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
        Finset.sum_sdiff hI₀R
      have hsum' : (n : ℝ) * (w + M) - M ≤ ∑ i ∈ R', c i := by
        push_cast at hsum
        linarith
      obtain ⟨I', hI'R', hI'disj, hI'ge⟩ :=
        ih hn1 R' (fun i hi => hc_nonneg i (Finset.sdiff_subset hi))
          (fun i hi => hc_le i (Finset.sdiff_subset hi)) hsum'
      let I : Fin (n + 1) → Finset α := fun s =>
        if h : s.val < n then I' ⟨s.val, h⟩ else I₀
      refine ⟨I, ?_, ?_, ?_⟩
      · intro s
        dsimp [I]
        split_ifs with hs
        · exact (hI'R' ⟨s.val, hs⟩).trans Finset.sdiff_subset
        · exact hI₀R
      · intro s t hst
        dsimp [I]
        split_ifs with hs ht ht
        · have hne : (⟨s.val, hs⟩ : Fin n) ≠ ⟨t.val, ht⟩ :=
            fun h => hst (Fin.ext (congr_arg (Fin.val : Fin n → ℕ) h))
          exact hI'disj _ _ hne
        · rw [Finset.disjoint_left]
          intro x hx hx0
          exact (Finset.mem_sdiff.mp (hI'R' ⟨s.val, hs⟩ hx)).2 hx0
        · rw [Finset.disjoint_right]
          intro x hx hx0
          exact (Finset.mem_sdiff.mp (hI'R' ⟨t.val, ht⟩ hx)).2 hx0
        · exfalso
          apply hst
          ext
          omega
      · intro s
        dsimp [I]
        split_ifs with hs
        · exact hI'ge ⟨s.val, hs⟩
        · exact hI₀_ge

/--
**Anticonnected Component Blockade Lemma (Lemma 2.5 / `lem:anticonn-blockade` of `FMBV4-016_readable.tex`)**:
For any nonempty vertex subset $Z \subseteq V$ and integer $k \ge 1$, either $G[Z]$ contains an
anticonnected component $C \subseteq Z$ with $|C| \ge |Z| / k$, or $G[Z]$ contains a complete
$(k, |Z| / k^2)$-blockade (`IsCompleteBlockadeIn G Z k ((Z.card : ℝ) / (k : ℝ) ^ 2) B`).
-/
theorem anticonnected_component_blockade_lemma
    (G : SimpleGraph V) (Z : Finset V) (k : ℕ) (hk : 1 ≤ k) (hZ : Z.Nonempty) :
    (∃ C ⊆ Z, IsAnticonnectedComponentOf G Z C ∧ (Z.card : ℝ) / (k : ℝ) ≤ (C.card : ℝ)) ∨
    (∃ B : Fin k → Finset V,
      IsCompleteBlockadeIn G Z k ((Z.card : ℝ) / (k : ℝ) ^ 2) B) := by
  classical
  obtain ⟨r, C, hfam⟩ := exists_anticonnectedComponentFamily G Z
  by_cases hex : ∃ i : Fin r, (Z.card : ℝ) / (k : ℝ) ≤ ((C i).card : ℝ)
  · obtain ⟨i, hi⟩ := hex
    exact Or.inl ⟨C i, (hfam.is_component i).1, hfam.is_component i, hi⟩
  · push_neg at hex
    right
    let w : ℝ := (Z.card : ℝ) / (k : ℝ) ^ 2
    let M : ℝ := (Z.card : ℝ) / (k : ℝ)
    have hZ_pos : (0 : ℝ) < (Z.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hZ
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hw_pos : 0 < w := div_pos hZ_pos (sq_pos_of_pos hk_pos)
    have hM_nonneg : 0 ≤ M := div_nonneg (le_of_lt hZ_pos) (le_of_lt hk_pos)
    have hsum_C : ∑ i : Fin r, ((C i).card : ℝ) = (Z.card : ℝ) := by
      exact_mod_cast hfam.sum_card_eq
    have hsum_id : (k : ℝ) * (w + M) - M = ∑ i : Fin r, ((C i).card : ℝ) := by
      rw [hsum_C]
      have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
      dsimp [w, M]
      field_simp [hk_ne]
      ring
    obtain ⟨I, -, hI_disj, hI_sum⟩ :=
      exists_disjoint_family_sum_ge k hk Finset.univ (fun i => ((C i).card : ℝ)) w M
        (le_of_lt hw_pos) hM_nonneg (fun i _ => Nat.cast_nonneg _)
        (fun i _ => le_of_lt (hex i)) hsum_id.le
    let B : Fin k → Finset V := fun s => (I s).biUnion C
    have hB_card : ∀ s : Fin k, ((B s).card : ℝ) = ∑ i ∈ I s, ((C i).card : ℝ) := by
      intro s
      have hcard_nat : (B s).card = ∑ i ∈ I s, (C i).card :=
        Finset.card_biUnion (fun i _ j _ hij => hfam.pairwise_disjoint i j hij)
      exact_mod_cast hcard_nat
    have hB_width : ∀ s : Fin k, w ≤ ((B s).card : ℝ) := by
      intro s
      rw [hB_card s]
      exact hI_sum s
    have hB_nonempty : ∀ s : Fin k, (B s).Nonempty := by
      intro s
      have hpos : (0 : ℝ) < ((B s).card : ℝ) := lt_of_lt_of_le hw_pos (hB_width s)
      have hpos_nat : 0 < (B s).card := by exact_mod_cast hpos
      exact Finset.card_pos.mp hpos_nat
    have hB_sub : ∀ s : Fin k, B s ⊆ Z := by
      intro s u hu
      obtain ⟨i, -, huCi⟩ := Finset.mem_biUnion.mp hu
      exact (hfam.is_component i).1 huCi
    have hC_comp := (hfam.isCompleteBlockadeIn (Subset.refl Z)).2
    have hB_disj : ∀ s t : Fin k, s ≠ t → Disjoint (B s) (B t) := by
      intro s t hst
      rw [Finset.disjoint_left]
      intro u huBs huBt
      obtain ⟨i, hiIs, huCi⟩ := Finset.mem_biUnion.mp huBs
      obtain ⟨j, hjIt, huCj⟩ := Finset.mem_biUnion.mp huBt
      have hij : i ≠ j :=
        fun h => Finset.disjoint_left.mp (hI_disj s t hst) hiIs (h ▸ hjIt)
      exact Finset.disjoint_left.mp (hfam.pairwise_disjoint i j hij) huCi huCj
    have hB_comp : ∀ s t : Fin k, s ≠ t → IsCompletePair G (B s) (B t) := by
      intro s t hst u huBs v hvBt
      obtain ⟨i, hiIs, huCi⟩ := Finset.mem_biUnion.mp huBs
      obtain ⟨j, hjIt, hvCj⟩ := Finset.mem_biUnion.mp hvBt
      have hij : i ≠ j :=
        fun h => Finset.disjoint_left.mp (hI_disj s t hst) hiIs (h ▸ hjIt)
      exact hC_comp i j hij u huCi v hvCj
    exact ⟨B, ⟨hB_sub, hB_nonempty, hB_disj, hB_width⟩, hB_comp⟩

/-! ### Section 9: $\overline{P_5}$-Free Open Attachment and $\overline{P_6}$-Free Dense Blockade Extraction -/

/--
Every $\overline{P_5}$-free graph is $\overline{P_6}$-free, since $\overline{P_5}$ is the induced
subgraph of $\overline{P_6}$ on the first $5$ vertices.
-/
theorem isP6ComplFree_of_isP5ComplFree (G : SimpleGraph V)
    (hG : IsInducedSubgraphFree G P5Compl) :
    IsInducedSubgraphFree G P6Compl := by
  rintro ⟨g, hg⟩
  apply hG
  let emb : Fin 5 ↪ Fin 6 :=
    ⟨Fin.castSucc, fun i j h => Fin.ext (congr_arg (Fin.val : Fin 6 → ℕ) h)⟩
  refine ⟨emb.trans g, SimpleGraph.ext ?_⟩
  funext i j
  rw [eq_iff_iff]
  have h1 : P6Compl.Adj i.castSucc j.castSucc ↔ G.Adj (g i.castSucc) (g j.castSucc) := by
    rw [hg]
    rfl
  change P5Compl.Adj i j ↔ G.Adj (g i.castSucc) (g j.castSucc)
  rw [← h1]
  simp only [P5Compl, P6Compl, compl_adj, pathGraph_adj, ne_eq, Fin.ext_iff, Fin.val_castSucc]

/--
General criterion for embedding $(\text{pathGraph } n)^c$ into $G$: if $f : \text{Fin } n \to V$
maps consecutive indices ($i + 1 = j$) to $G^c$-adjacent vertices and non-consecutive indices
($i + 1 < j$) to $G$-adjacent vertices, then $f$ is an injective induced embedding of
$(\text{pathGraph } n)^c$ into $G$.
-/
theorem exists_pathGraph_compl_embedding {n : ℕ} (G : SimpleGraph V) (f : Fin n → V)
    (h_consec : ∀ i j : Fin n, i.val + 1 = j.val → Gᶜ.Adj (f i) (f j))
    (h_nonconsec : ∀ i j : Fin n, i.val + 1 < j.val → G.Adj (f i) (f j)) :
    ∃ g : Fin n ↪ V, (pathGraph n)ᶜ = G.comap g := by
  have hlt_rel : ∀ i j : Fin n, i.val < j.val →
      f i ≠ f j ∧ (((pathGraph n)ᶜ).Adj i j ↔ G.Adj (f i) (f j)) := by
    intro i j hij
    have hpath : ((pathGraph n)ᶜ).Adj i j ↔ i.val + 1 < j.val := by
      simp only [compl_adj, pathGraph_adj, ne_eq, Fin.ext_iff]
      omega
    by_cases h1 : i.val + 1 < j.val
    · have hadj := h_nonconsec i j h1
      exact ⟨hadj.ne, iff_of_true (hpath.mpr h1) hadj⟩
    · have heq : i.val + 1 = j.val := by omega
      have hcadj := h_consec i j heq
      have hne : f i ≠ f j := ((compl_adj G (f i) (f j)).mp hcadj).1
      have hnadj : ¬G.Adj (f i) (f j) := ((compl_adj G (f i) (f j)).mp hcadj).2
      have hnpath : ¬((pathGraph n)ᶜ).Adj i j := fun h => h1 (hpath.mp h)
      exact ⟨hne, iff_of_false hnpath hnadj⟩
  have hf_inj : Function.Injective f := by
    intro i j hij
    rcases lt_trichotomy i.val j.val with hlt | heq | hgt
    · exact ((hlt_rel i j hlt).1 hij).elim
    · exact Fin.ext heq
    · exact ((hlt_rel j i hgt).1 hij.symm).elim
  refine ⟨⟨f, hf_inj⟩, SimpleGraph.ext ?_⟩
  funext i j
  rw [eq_iff_iff]
  change ((pathGraph n)ᶜ).Adj i j ↔ G.Adj (f i) (f j)
  rcases lt_trichotomy i.val j.val with hlt | heq | hgt
  · exact (hlt_rel i j hlt).2
  · have hij : i = j := Fin.ext heq
    subst hij
    simp
  · rw [((pathGraph n)ᶜ).adj_comm, G.adj_comm]
    exact (hlt_rel j i hgt).2

/--
If $0 < |N_G(v) \cap M| < |M|$, then $v$ is mixed on $M$ in $G$ (`IsVertexMixedOn G v M`).
-/
theorem isVertexMixedOn_of_card_neighborFinsetIn {G : SimpleGraph V} {v : V} {M : Finset V}
    (hpos : 0 < (neighborFinsetIn G v M).card)
    (hlt : (neighborFinsetIn G v M).card < M.card) :
    IsVertexMixedOn G v M := by
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
  rw [mem_neighborFinsetIn_iff] at hu
  have hex_not : ∃ w ∈ M, w ∉ neighborFinsetIn G v M := by
    by_contra hall
    push_neg at hall
    have hle : M.card ≤ (neighborFinsetIn G v M).card := Finset.card_le_card hall
    omega
  obtain ⟨w, hwM, hw_not⟩ := hex_not
  rw [mem_neighborFinsetIn_iff, not_and] at hw_not
  exact ⟨⟨u, hu.1, hu.2⟩, ⟨w, hwM, hw_not hwM⟩⟩

/--
**Claim 7.1.2 of `arXiv:2312.15333` (`p5Compl_free_openAttachment_not_completePair`)**:
In a $\overline{P_5}$-free graph $G$, if $B : \text{Fin } \ell \to \text{Finset } V$ is an
anticonnected blockade in $F$, and an external vertex $v \in F \setminus \bigcup_k B_k$ is mixed
($0 < |N_G(v) \cap B_k| < |B_k|$) on two distinct blocks $B_i$ and $B_j$ ($i \neq j$), then
$(B_i, B_j)$ is not complete in $G$.
-/
theorem p5Compl_free_openAttachment_not_completePair
    (G : SimpleGraph V) (F : Finset V) {ℓ : ℕ} {w : ℝ} (B : Fin ℓ → Finset V)
    (hG : IsInducedSubgraphFree G P5Compl)
    (_hB : IsBlockadeIn G F ℓ w B)
    (hanti : ∀ k : Fin ℓ, IsAnticonnected G (B k))
    (v : V) (hv : v ∈ F \ Finset.univ.biUnion B)
    (i j : Fin ℓ) (_hij : i ≠ j)
    (hvi_pos : 0 < (neighborFinsetIn G v (B i)).card)
    (hvi_lt : (neighborFinsetIn G v (B i)).card < (B i).card)
    (hvj_pos : 0 < (neighborFinsetIn G v (B j)).card)
    (hvj_lt : (neighborFinsetIn G v (B j)).card < (B j).card) :
    ¬IsCompletePair G (B i) (B j) := by
  intro hcomp
  have hv_not_B : ∀ k : Fin ℓ, ∀ x ∈ B k, x ≠ v := by
    intro k x hx hxv
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, hxv ▸ hx⟩)
  have hmix_i : IsVertexMixedOn G v (B i) := isVertexMixedOn_of_card_neighborFinsetIn hvi_pos hvi_lt
  have hmix_j : IsVertexMixedOn G v (B j) := isVertexMixedOn_of_card_neighborFinsetIn hvj_pos hvj_lt
  obtain ⟨w_i, hw_i, u_i, hu_i, h_wi_ui_ne, h_wi_ui_nadj, h_v_wi_nadj, h_v_ui_adj⟩ :=
    hmix_i.exists_anticonnected_edge (hanti i)
  obtain ⟨w_j, hw_j, u_j, hu_j, h_wj_uj_ne, h_wj_uj_nadj, h_v_wj_nadj, h_v_uj_adj⟩ :=
    hmix_j.exists_anticonnected_edge (hanti j)
  have h01 : Gᶜ.Adj u_i w_i :=
    (compl_adj G u_i w_i).mpr ⟨h_wi_ui_ne.symm, fun h => h_wi_ui_nadj h.symm⟩
  have h12 : Gᶜ.Adj w_i v :=
    (compl_adj G w_i v).mpr ⟨hv_not_B i w_i hw_i, fun h => h_v_wi_nadj h.symm⟩
  have h23 : Gᶜ.Adj v w_j :=
    (compl_adj G v w_j).mpr ⟨(hv_not_B j w_j hw_j).symm, h_v_wj_nadj⟩
  have h34 : Gᶜ.Adj w_j u_j :=
    (compl_adj G w_j u_j).mpr ⟨h_wj_uj_ne, h_wj_uj_nadj⟩
  have h02 : G.Adj u_i v := h_v_ui_adj.symm
  have h03 : G.Adj u_i w_j := hcomp u_i hu_i w_j hw_j
  have h04 : G.Adj u_i u_j := hcomp u_i hu_i u_j hu_j
  have h13 : G.Adj w_i w_j := hcomp w_i hw_i w_j hw_j
  have h14 : G.Adj w_i u_j := hcomp w_i hw_i u_j hu_j
  have h24 : G.Adj v u_j := h_v_uj_adj
  apply hG
  refine exists_pathGraph_compl_embedding G ![u_i, w_i, v, w_j, u_j] ?_ ?_
  · intro a b hab
    fin_cases a <;> fin_cases b <;> dsimp at hab <;> try omega
    · exact h01
    · exact h12
    · exact h23
    · exact h34
  · intro a b hab
    fin_cases a <;> fin_cases b <;> dsimp at hab <;> try omega
    · exact h02
    · exact h03
    · exact h04
    · exact h13
    · exact h14
    · exact h24

theorem IsCompleteBlockadeIn.mono {G : SimpleGraph V} {Z F : Finset V} {k : ℕ} {w w' : ℝ}
    {B : Fin k → Finset V}
    (hB : IsCompleteBlockadeIn G Z k w B) (hZF : Z ⊆ F) (hw : w' ≤ w) :
    IsCompleteBlockadeIn G F k w' B :=
  ⟨⟨fun i => (hB.1.subset_ambient i).trans hZF,
    hB.1.nonempty_blocks,
    hB.1.pairwise_disjoint,
    fun i => hw.trans (hB.1.width_ge i)⟩, hB.2⟩

/--
If $F_{\text{prev}}$ is anticonnected in $G$, $A \subseteq F_{\text{prev}}$ is nonempty, and
$F_{\text{next}}$ is an anticonnected component of $F_{\text{prev}} \setminus A$, then there is an
edge in $G^c$ between some $x \in A$ and some $y \in F_{\text{next}}$.
-/
theorem anticonnected_component_sdiff_exists_compl_adj
    {G : SimpleGraph V} {F_prev A F_next : Finset V}
    (hF_prev : IsAnticonnected G F_prev)
    (hA_sub : A ⊆ F_prev) (hA_ne : A.Nonempty)
    (hF_next : IsAnticonnectedComponentOf G (F_prev \ A) F_next) :
    ∃ x ∈ A, ∃ y ∈ F_next, Gᶜ.Adj x y := by
  classical
  obtain ⟨a, haA⟩ := hA_ne
  have haF : a ∈ F_prev := hA_sub haA
  obtain ⟨d, hdF_next⟩ := hF_next.nonempty
  have hd_sdiff : d ∈ F_prev \ A := hF_next.1 hdF_next
  have hdF : d ∈ F_prev := (Finset.mem_sdiff.mp hd_sdiff).1
  have ha_not : a ∉ F_next := fun h => (Finset.mem_sdiff.mp (hF_next.1 h)).2 haA
  obtain ⟨p⟩ := hF_prev.preconnected ⟨a, haF⟩ ⟨d, hdF⟩
  obtain ⟨x, y, hxy_adj, hx_not, hy_in⟩ :=
    walk_exists_adj_of_not_of_prop (fun z : (F_prev : Set V) => z.val ∈ F_next)
      p ha_not hdF_next
  have hxA : x.val ∈ A := by
    by_contra hxA
    have hx_sdiff : x.val ∈ F_prev \ A := Finset.mem_sdiff.mpr ⟨x.2, hxA⟩
    have hadj : G.Adj y.val x.val := hF_next.2.2 y.val hy_in x.val hx_sdiff hx_not
    exact ((compl_adj G x.val y.val).mp hxy_adj).2 hadj.symm
  exact ⟨x.val, hxA, y.val, hy_in, hxy_adj⟩

/--
If $N_{G^c}(v) \cap S \subseteq A$ and $v \notin S \setminus A$, then $v$ is adjacent in $G$
to every vertex $u \in S \setminus A$.
-/
theorem adj_of_mem_sdiff_neighborFinsetIn_compl
    {G : SimpleGraph V} {S A : Finset V} {v u : V}
    (hsub : neighborFinsetIn Gᶜ v S ⊆ A) (hv : v ∉ S \ A) (hu : u ∈ S \ A) :
    G.Adj v u := by
  have hne : v ≠ u := fun h => hv (h ▸ hu)
  have huS : u ∈ S := (Finset.mem_sdiff.mp hu).1
  have huA : u ∉ A := (Finset.mem_sdiff.mp hu).2
  by_contra hnot
  have hcompl : Gᶜ.Adj v u := (compl_adj G v u).mpr ⟨hne, hnot⟩
  exact huA (hsub ((mem_neighborFinsetIn_iff Gᶜ v S u).mpr ⟨huS, hcompl⟩))

/--
**$\overline{P_6}$-Free Dense Complete Blockade Extraction (`p6Compl_free_sparse_compl_complete_blockade`,
the $\overline{P_6}$ version of Lemma 4.4 of `arXiv:2312.15333`)**:
If $G$ is $\overline{P_6}$-free (`IsInducedSubgraphFree G P6Compl`), $\overline{G}[F]$ is
$(1 / 128)$-sparse (`IsEpsSparseOn Gᶜ F (1 / 128)`), and $|F| \ge 128$, then $F$ contains a
complete $(2, |F| / 128)$-blockade in $G$.
-/
theorem p6Compl_free_sparse_compl_complete_blockade (G : SimpleGraph V) (F : Finset V)
    (hG : IsInducedSubgraphFree G P6Compl)
    (h_sparse : IsEpsSparseOn Gᶜ F (1 / 128))
    (hF_card : (128 : ℝ) ≤ (F.card : ℝ)) :
    ∃ B : Fin 2 → Finset V, IsCompleteBlockadeIn G F 2 ((F.card : ℝ) / 128) B := by
  classical
  by_contra hno_blockade
  have hex_comp : ∀ Z ⊆ F, (F.card : ℝ) / 32 ≤ (Z.card : ℝ) →
      ∃ C ⊆ Z, IsAnticonnectedComponentOf G Z C ∧ (Z.card : ℝ) / 2 ≤ (C.card : ℝ) := by
    intro Z hZF hZ_card
    have hZ_pos : (0 : ℝ) < (Z.card : ℝ) := by linarith
    have hZ_pos_nat : 0 < Z.card := by exact_mod_cast hZ_pos
    have hZ_ne : Z.Nonempty := Finset.card_pos.mp hZ_pos_nat
    rcases anticonnected_component_blockade_lemma G Z 2 (by omega) hZ_ne with hcomp | ⟨B, hB⟩
    · exact hcomp
    · exfalso
      apply hno_blockade
      refine ⟨B, hB.mono hZF ?_⟩
      linarith
  have hdeg_le : ∀ v ∈ F, ∀ S ⊆ F, ((neighborFinsetIn Gᶜ v S).card : ℝ) ≤ (F.card : ℝ) / 128 := by
    intro v hvF S hSF
    have h1 : ((neighborFinsetIn Gᶜ v S).card : ℝ) ≤ ((neighborFinsetIn Gᶜ v F).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (neighborFinsetIn_mono Gᶜ v hSF)
    have h2 := h_sparse v hvF
    linarith
  have hcard_sdiff : ∀ S A : Finset V, (S.card : ℝ) - (A.card : ℝ) ≤ ((S \ A).card : ℝ) := by
    intro S A
    have hcov : S ⊆ (S \ A) ∪ A := by
      intro u hu
      by_cases huA : u ∈ A
      · exact Finset.mem_union_right _ huA
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hu, huA⟩)
    have hnat : S.card ≤ (S \ A).card + A.card :=
      (Finset.card_le_card hcov).trans (Finset.card_union_le _ _)
    have hreal : (S.card : ℝ) ≤ ((S \ A).card : ℝ) + (A.card : ℝ) := by exact_mod_cast hnat
    linarith
  -- Step 1: Extract F₁ ⊆ F and pick v₀ ∈ F₁, A₀ = N_{Gᶜ}(v₀) ∩ F₁, S₂ = F₁ \ ({v₀} ∪ A₀)
  obtain ⟨F₁, hF₁F, hF₁_comp, hF₁_card⟩ := hex_comp F (Subset.refl F) (by linarith)
  obtain ⟨v₀, hv₀F₁⟩ := hF₁_comp.nonempty
  have hv₀F : v₀ ∈ F := hF₁F hv₀F₁
  let A₀ : Finset V := neighborFinsetIn Gᶜ v₀ F₁
  let A₀' : Finset V := insert v₀ A₀
  have hA₀'_sub : A₀' ⊆ F₁ :=
    Finset.insert_subset_iff.mpr ⟨hv₀F₁, neighborFinsetIn_subset Gᶜ v₀ F₁⟩
  have hA₀'_card : (A₀'.card : ℝ) ≤ (F.card : ℝ) / 128 + 1 := by
    have h1 : (A₀'.card : ℝ) ≤ (A₀.card : ℝ) + 1 := by
      exact_mod_cast Finset.card_insert_le v₀ A₀
    have h2 := hdeg_le v₀ hv₀F F₁ hF₁F
    linarith
  let S₂ : Finset V := F₁ \ A₀'
  have hS₂F : S₂ ⊆ F := Finset.sdiff_subset.trans hF₁F
  have hS₂_card : (3 / 8) * (F.card : ℝ) ≤ (S₂.card : ℝ) := by
    have h1 := hcard_sdiff F₁ A₀'
    linarith
  -- Step 2: Extract F₂ ⊆ S₂ and v₁ ∈ A₀ with Gᶜ-neighbor u₂ ∈ F₂
  obtain ⟨F₂, hF₂S₂, hF₂_comp, hF₂_card⟩ := hex_comp S₂ hS₂F (by linarith)
  have hF₂F : F₂ ⊆ F := hF₂S₂.trans hS₂F
  obtain ⟨v₁, hv₁A₀', u₂, hu₂F₂, h_v1_u2_compl⟩ :=
    anticonnected_component_sdiff_exists_compl_adj hF₁_comp.2.1 hA₀'_sub
      ⟨v₀, Finset.mem_insert_self v₀ A₀⟩ hF₂_comp
  have hv₁A₀ : v₁ ∈ A₀ := by
    rcases Finset.mem_insert.mp hv₁A₀' with rfl | hv₁A₀
    · exfalso
      have hu₂S₂ : u₂ ∈ S₂ := hF₂S₂ hu₂F₂
      have hu₂F₁ : u₂ ∈ F₁ := (Finset.mem_sdiff.mp hu₂S₂).1
      have hu₂_not_A₀' : u₂ ∉ A₀' := (Finset.mem_sdiff.mp hu₂S₂).2
      have hu₂A₀ : u₂ ∈ A₀ := (mem_neighborFinsetIn_iff Gᶜ v₁ F₁ u₂).mpr ⟨hu₂F₁, h_v1_u2_compl⟩
      exact hu₂_not_A₀' (Finset.mem_insert_of_mem hu₂A₀)
    · exact hv₁A₀
  have hv₁F₁ : v₁ ∈ F₁ := (mem_neighborFinsetIn_iff Gᶜ v₀ F₁ v₁).mp hv₁A₀ |>.1
  have hv₁F : v₁ ∈ F := hF₁F hv₁F₁
  have h01 : Gᶜ.Adj v₀ v₁ := (mem_neighborFinsetIn_iff Gᶜ v₀ F₁ v₁).mp hv₁A₀ |>.2
  let A₁ : Finset V := neighborFinsetIn Gᶜ v₁ F₂
  have hA₁_sub : A₁ ⊆ F₂ := neighborFinsetIn_subset Gᶜ v₁ F₂
  have hu₂A₁ : u₂ ∈ A₁ := (mem_neighborFinsetIn_iff Gᶜ v₁ F₂ u₂).mpr ⟨hu₂F₂, h_v1_u2_compl⟩
  let S₃ : Finset V := F₂ \ A₁
  have hS₃F : S₃ ⊆ F := Finset.sdiff_subset.trans hF₂F
  have hS₃_card : (1 / 8) * (F.card : ℝ) ≤ (S₃.card : ℝ) := by
    have h1 := hcard_sdiff F₂ A₁
    have h2 := hdeg_le v₁ hv₁F F₂ hF₂F
    linarith
  -- Step 3: Extract F₃ ⊆ S₃ and v₂ ∈ A₁ with Gᶜ-neighbor u₃ ∈ F₃
  obtain ⟨F₃, hF₃S₃, hF₃_comp, hF₃_card⟩ := hex_comp S₃ hS₃F (by linarith)
  have hF₃F : F₃ ⊆ F := hF₃S₃.trans hS₃F
  obtain ⟨v₂, hv₂A₁, u₃, hu₃F₃, h_v2_u3_compl⟩ :=
    anticonnected_component_sdiff_exists_compl_adj hF₂_comp.2.1 hA₁_sub ⟨u₂, hu₂A₁⟩ hF₃_comp
  have hv₂F₂ : v₂ ∈ F₂ := hA₁_sub hv₂A₁
  have hv₂F : v₂ ∈ F := hF₂F hv₂F₂
  have h12 : Gᶜ.Adj v₁ v₂ := (mem_neighborFinsetIn_iff Gᶜ v₁ F₂ v₂).mp hv₂A₁ |>.2
  let A₂ : Finset V := neighborFinsetIn Gᶜ v₂ F₃
  have hA₂_sub : A₂ ⊆ F₃ := neighborFinsetIn_subset Gᶜ v₂ F₃
  have hu₃A₂ : u₃ ∈ A₂ := (mem_neighborFinsetIn_iff Gᶜ v₂ F₃ u₃).mpr ⟨hu₃F₃, h_v2_u3_compl⟩
  let S₄ : Finset V := F₃ \ A₂
  have hS₄F : S₄ ⊆ F := Finset.sdiff_subset.trans hF₃F
  have hS₄_card : (1 / 32) * (F.card : ℝ) ≤ (S₄.card : ℝ) := by
    have h1 := hcard_sdiff F₃ A₂
    have h2 := hdeg_le v₂ hv₂F F₃ hF₃F
    linarith
  -- Step 4: Extract F₄ ⊆ S₄, v₃ ∈ A₂ mixed on F₄, and anticonnected edge (v₄, v₅) in F₄
  obtain ⟨F₄, hF₄S₄, hF₄_comp, hF₄_card⟩ := hex_comp S₄ hS₄F (by linarith)
  have hF₄F : F₄ ⊆ F := hF₄S₄.trans hS₄F
  obtain ⟨v₃, hv₃A₂, w, hwF₄, h_v3_w_compl⟩ :=
    anticonnected_component_sdiff_exists_compl_adj hF₃_comp.2.1 hA₂_sub ⟨u₃, hu₃A₂⟩ hF₄_comp
  have hv₃F₃ : v₃ ∈ F₃ := hA₂_sub hv₃A₂
  have hv₃F : v₃ ∈ F := hF₃F hv₃F₃
  have h23 : Gᶜ.Adj v₂ v₃ := (mem_neighborFinsetIn_iff Gᶜ v₂ F₃ v₃).mp hv₃A₂ |>.2
  have hv₃_not_S₄ : v₃ ∉ S₄ := fun h => (Finset.mem_sdiff.mp h).2 hv₃A₂
  have hmix_v₃ : IsVertexMixedOn G v₃ F₄ := by
    have hex_adj : ∃ w' ∈ F₄, G.Adj v₃ w' := by
      have hlt_real : ((neighborFinsetIn Gᶜ v₃ F₄).card : ℝ) < (F₄.card : ℝ) := by
        have h1 := hdeg_le v₃ hv₃F F₄ hF₄F
        linarith
      have hlt_nat : (neighborFinsetIn Gᶜ v₃ F₄).card < F₄.card := by exact_mod_cast hlt_real
      have hex_not : ∃ w' ∈ F₄, w' ∉ neighborFinsetIn Gᶜ v₃ F₄ := by
        by_contra hall
        push_neg at hall
        have hle := Finset.card_le_card hall
        omega
      obtain ⟨w', hw'F₄, hw'_not⟩ := hex_not
      refine ⟨w', hw'F₄, ?_⟩
      have hne : v₃ ≠ w' := fun h => hv₃_not_S₄ (h ▸ hF₄S₄ hw'F₄)
      by_contra hnot
      exact hw'_not ((mem_neighborFinsetIn_iff Gᶜ v₃ F₄ w').mpr
        ⟨hw'F₄, (compl_adj G v₃ w').mpr ⟨hne, hnot⟩⟩)
    exact ⟨hex_adj, ⟨w, hwF₄, ((compl_adj G v₃ w).mp h_v3_w_compl).2⟩⟩
  obtain ⟨v₄, hv₄F₄, v₅, hv₅F₄, h_v4_v5_ne, h_v4_v5_nadj, h_v3_v4_nadj, h35⟩ :=
    hmix_v₃.exists_anticonnected_edge hF₄_comp.2.1
  have hv3_ne_v4 : v₃ ≠ v₄ := fun h => hv₃_not_S₄ (h ▸ hF₄S₄ hv₄F₄)
  have h34 : Gᶜ.Adj v₃ v₄ := (compl_adj G v₃ v₄).mpr ⟨hv3_ne_v4, h_v3_v4_nadj⟩
  have h45 : Gᶜ.Adj v₄ v₅ := (compl_adj G v₄ v₅).mpr ⟨h_v4_v5_ne, h_v4_v5_nadj⟩
  -- Step 5: Verify all 10 non-consecutive G-edges and contradict IsInducedSubgraphFree G P6Compl
  have hadj_v₀ : ∀ u ∈ S₂, G.Adj v₀ u :=
    fun u hu => adj_of_mem_sdiff_neighborFinsetIn_compl (Finset.subset_insert v₀ A₀)
      (fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_insert_self v₀ A₀)) hu
  have hadj_v₁ : ∀ u ∈ S₃, G.Adj v₁ u :=
    fun u hu => adj_of_mem_sdiff_neighborFinsetIn_compl (Subset.refl A₁)
      (fun h => (Finset.mem_sdiff.mp (hF₂S₂ (Finset.sdiff_subset h))).2
        (Finset.mem_insert_of_mem hv₁A₀)) hu
  have hadj_v₂ : ∀ u ∈ S₄, G.Adj v₂ u :=
    fun u hu => adj_of_mem_sdiff_neighborFinsetIn_compl (Subset.refl A₂)
      (fun h => (Finset.mem_sdiff.mp (hF₃S₃ (Finset.sdiff_subset h))).2 hv₂A₁) hu
  have hv₃S₃ : v₃ ∈ S₃ := hF₃S₃ hv₃F₃
  have hv₄S₄ : v₄ ∈ S₄ := hF₄S₄ hv₄F₄
  have hv₅S₄ : v₅ ∈ S₄ := hF₄S₄ hv₅F₄
  have hv₄S₃ : v₄ ∈ S₃ := hF₃S₃ (Finset.sdiff_subset hv₄S₄)
  have hv₅S₃ : v₅ ∈ S₃ := hF₃S₃ (Finset.sdiff_subset hv₅S₄)
  have hv₂S₂ : v₂ ∈ S₂ := hF₂S₂ hv₂F₂
  have hv₃S₂ : v₃ ∈ S₂ := hF₂S₂ (Finset.sdiff_subset hv₃S₃)
  have hv₄S₂ : v₄ ∈ S₂ := hF₂S₂ (Finset.sdiff_subset hv₄S₃)
  have hv₅S₂ : v₅ ∈ S₂ := hF₂S₂ (Finset.sdiff_subset hv₅S₃)
  have h02 : G.Adj v₀ v₂ := hadj_v₀ v₂ hv₂S₂
  have h03 : G.Adj v₀ v₃ := hadj_v₀ v₃ hv₃S₂
  have h04 : G.Adj v₀ v₄ := hadj_v₀ v₄ hv₄S₂
  have h05 : G.Adj v₀ v₅ := hadj_v₀ v₅ hv₅S₂
  have h13 : G.Adj v₁ v₃ := hadj_v₁ v₃ hv₃S₃
  have h14 : G.Adj v₁ v₄ := hadj_v₁ v₄ hv₄S₃
  have h15 : G.Adj v₁ v₅ := hadj_v₁ v₅ hv₅S₃
  have h24 : G.Adj v₂ v₄ := hadj_v₂ v₄ hv₄S₄
  have h25 : G.Adj v₂ v₅ := hadj_v₂ v₅ hv₅S₄
  apply hG
  refine exists_pathGraph_compl_embedding G ![v₀, v₁, v₂, v₃, v₄, v₅] ?_ ?_
  · intro a b hab
    fin_cases a <;> fin_cases b <;> dsimp at hab <;> try omega
    · exact h01
    · exact h12
    · exact h23
    · exact h34
    · exact h45
  · intro a b hab
    fin_cases a <;> fin_cases b <;> dsimp at hab <;> try omega
    · exact h02
    · exact h03
    · exact h04
    · exact h05
    · exact h13
    · exact h14
    · exact h15
    · exact h24
    · exact h25
    · exact h35

end ErdosHajnalP6

