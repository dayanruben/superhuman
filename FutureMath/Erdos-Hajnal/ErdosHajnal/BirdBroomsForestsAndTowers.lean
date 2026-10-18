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
# $\mathrm{Bird}$, Forest Pairs $\{F_1, \overline{F_2}\}$, Hooked-Claws $\operatorname{Hook}_4(Q)$, Brooms $B(s, d)$, and Infinite Prime Non-Split Towers
(Part IV, Proposition 6 of `main.tex`, lines 968–1019)

This file formalizes Proposition 6(1a), (1b), (2a), (2b), and (3) of `main.tex`:
1. **Section 1 — Closure Monotonicity and Proposition 6(1b) (`forest_in_InJClosure`)**:
   - Monotonicity of $\mathcal{B}_k^*$, $\mathcal{J}(\mathcal{B}_k^*)$, and $\mathcal{H}(\mathcal{B}_k^*)$ in $k$,
     and commutativity of graph complementation with vertex substitution (`substGraph_compl`).
   - Every non-empty finite acyclic graph (forest) $F$ belongs to $\mathcal{J}(\mathcal{B}_k^*)$
     (`forest_in_InJClosure`, Proposition 6(1b), `main.tex` line 1003), proved by strong induction
     on $|V(F)|$ deleting a vertex of degree at most $1$ (`forest_exists_vert_degree_le_one`).
   - Explicit derivations `eGraph_in_InJClosure_one` ($E\text{-graph} \in \mathcal{J}(\mathcal{B}_1^*)$)
     and `birdGraph_in_InJClosure_one` ($\mathrm{Bird} \in \mathcal{J}(\mathcal{B}_1^*)$ from
     $K_3 \cong K_2[1 \leftarrow K_2]$ by three degree-$1$ leaf additions).
2. **Section 2 — Proposition 6(1a), Part 1 (`bird_isThresholdedWonderful`)**:
   - The 5-vertex, 7-edge Stage-2 witness graph $H_{\mathrm{Bird}} := \overline{\mathrm{Bird}} - b_1$
     (`witnessHBird : SimpleGraph (Fin 5)`) with special edge $S_0 = \{b_5, b_6\}$ (`specHBird = {3, 4}`),
     its substitution decomposition $H_{\mathrm{Bird}} \cong K_2[0 \leftarrow \overline{K_2}, 1 \leftarrow \overline{P_3}] \in \mathcal{H}(\mathcal{B}_1^*)$
     (`witnessHBird_inHClosure_one`), and deterministic open-interval embedding certifying
     `IsThresholdedWonderful BirdGraph` (`bird_isThresholdedWonderful`, `main.tex` line 986).
3. **Section 3 — Proposition 6(1a), Part 2 (`bird_egraph_pure`, `bird_quotient_descent`, `bird_comb_dichotomy`)**:
   - The 2-vertex apex extension rules **Rule (i)** (`bird_comb_rule1`, forbidding induced $P_2 \sqcup P_1$
     with mixed attachment) and **Rule (ii)** (`bird_comb_rule2`, forbidding induced $P_3 \sqcup P_1$
     with mixed attachment), and the 64-state purity lemma (`bird_egraph_pure`, `main.tex` lines 988–999)
     proving that every apex-cutter vertex $u$ is pure to every induced copy of $E\text{-graph}$.
   - Mixed-equivalence quotient descent $\mathcal{L}^q \to \mathcal{L}^1$ (`bird_quotient_descent`)
     and the Cauchy-bucketed Stage-1 Comb Dichotomy for $\mathrm{Bird}$ (`bird_comb_dichotomy`, `main.tex` line 1001).
4. **Section 4a — Proposition 6(2b) (`bot_inHClosure_one`, `broom_in_subst_closure`)**:
   - Every $(s + d + 1)$-vertex broom $B(s, d) := P_{d+2}[v_1 \leftarrow \overline{K_s}]$ (`BroomGraph s d`)
     belongs to $\mathcal{H}(\mathcal{B}_{d+2}^*)$ and satisfies `HasErdosHajnalProp` (along with its
     complement) whenever $P_{d+2} \in \mathcal{EH}$ via iterated twin substitution (`main.tex` lines 980, 1012).
5. **Section 4b — Proposition 6(2a) (`hook4_defective_neighborhood_module`, `hook4_comb_dichotomy`)**:
   - Depth-$m$ Multi-Stem Defective Neighborhood Module Lemma (`hook4_defective_neighborhood_module`,
     `main.tex` lines 979, 1005–1010) for $\overline{\{P_{6+m}, \operatorname{Hook}_4(Q)\}}$-free combs
     via inductive $(q+4)$-stem extraction against threshold $\tau_r = (2\kappa(F))^r \kappa(F)^{1/c_Q}$,
     potential-preserving $\Phi_8$ Gallai tree decomposition (`hook4_gallai_tree_decomposition`),
     and the resulting Stage-1 Comb Dichotomy (`hook4_comb_dichotomy`).
6. **Section 5 — Proposition 6(3) (`primeTower_isPrimeGraph`, `primeTower_not_isSplitGraph`,
   `primeTower_inHClosure`, `primeTowerCompl_not_inJClosureC5`, `primeTower_iso_iff_eq`)**:
   - Recursive $(t+k)$-vertex prime non-split towers $H_{t+k}^{(t)}$ (`PrimeTowerGraph t k`, $t \ge 6, k \ge 0$)
     above every path $P_t$, proving pairwise non-isomorphism (`primeTower_iso_iff_eq`), non-splitness
     via $P_6 \hookrightarrow_g H_{t+k}^{(t)}$ (`primeTower_not_isSplitGraph`), primality via one-vertex
     leaf/co-leaf primality preservation (`primeTower_isPrimeGraph`), membership in $\mathcal{H}(\mathcal{B}_t^*)$
     (`primeTower_inHClosure`), and exclusion from $\mathcal{J}(\{K_1, K_2, \overline{K_2}, C_5\})$
     (`primeTowerCompl_not_inJClosureC5`, `primeTower_not_inHClosureC5`, `main.tex` lines 982, 1014–1016).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open Filter Finset SimpleGraph Real

namespace ErdosHajnalGen

open ErdosHajnalP6

/-!
### Section 1: Closure Monotonicity and Proposition 6(1b) — Every Finite Forest Belongs to `InJClosure k`
(`main.tex` lines 975, 986, 1003)
-/

/-- Computable `DecidableRel` instance for `BirdGraph.Adj`. -/
instance instDecidableRelBirdGraphAdj : DecidableRel BirdGraph.Adj := fun u v => by
  unfold BirdGraph
  dsimp only
  infer_instance

/-- Computable `DecidableRel` instance for `EGraph.Adj`. -/
instance instDecidableRelEGraphAdj : DecidableRel EGraph.Adj := fun u v => by
  unfold EGraph
  dsimp only
  infer_instance

/-- Computable `DecidableRel` instance for `C5Graph.Adj`. -/
instance instDecidableRelC5GraphAdj : DecidableRel C5Graph.Adj := fun u v => by
  unfold C5Graph
  dsimp only
  infer_instance

/-- Monotonicity of the generator family $\mathcal{B}_k^*$ (`InBStar`): if $k_1 \le k_2$, then $\mathcal{B}_{k_1}^* \subseteq \mathcal{B}_{k_2}^*$. -/
theorem InBStar.mono {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) {W : Type} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} (h : InBStar k₁ H) : InBStar k₂ H := by
  rcases h with h1 | h2 | h3 | h4 | h5 | ⟨t, ht1, htk, ht⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨t, ht1, htk.trans hk, ht⟩))))

/-- Monotonicity of the substitution and leaf-attachment closure $\mathcal{J}(\mathcal{B}_k^*)$ (`InJClosure`) in $k$. -/
theorem InJClosure.mono {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) {W : Type} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} (h : InJClosure k₁ H) : InJClosure k₂ H := by
  induction h with
  | base H hB => exact InJClosure.base H (hB.mono hk)
  | iso H₁ H₂ _ h_iso ih => exact InJClosure.iso H₁ H₂ ih h_iso
  | subst H₁ v₀ H₂ _ _ ih₁ ih₂ => exact InJClosure.subst H₁ v₀ H₂ ih₁ ih₂
  | add_leaf H v₀ hdeg _ ih => exact InJClosure.add_leaf H v₀ hdeg ih

/-- Monotonicity of the symmetric single-graph closure $\mathcal{H}(\mathcal{B}_k^*) := \mathcal{J}(\mathcal{B}_k^*) \cap \overline{\mathcal{J}(\mathcal{B}_k^*)}$ (`InHClosure`) in $k$. -/
theorem InHClosure.mono {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) {W : Type} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} (h : InHClosure k₁ H) : InHClosure k₂ H :=
  ⟨h.1.mono hk, h.2.mono hk⟩

/-- Graph complementation commutes with vertex substitution (`substGraph`):
$\overline{H_1[v_0 \leftarrow H_2]} = \overline{H_1}[v_0 \leftarrow \overline{H_2}]$. -/
private theorem substGraph_compl {V₁ V₂ : Type*} (H₁ : SimpleGraph V₁) (v₀ : V₁) (H₂ : SimpleGraph V₂) :
    (substGraph H₁ v₀ H₂)ᶜ = substGraph H₁ᶜ v₀ H₂ᶜ := by
  ext a b
  cases a with
  | inl u =>
    cases b with
    | inl w =>
      simp [substGraph, compl_adj, Subtype.ext_iff]
    | inr y =>
      simp [substGraph, compl_adj, u.2]
  | inr x =>
    cases b with
    | inl w =>
      simp [substGraph, compl_adj, w.2.symm]
    | inr y =>
      simp [substGraph, compl_adj]

/-- Any two simple graphs on a `Subsingleton` vertex type are equal. -/
theorem simpleGraph_eq_of_subsingleton {W : Type*} [Subsingleton W] (G₁ G₂ : SimpleGraph W) :
    G₁ = G₂ := by
  ext u v
  have h : u = v := Subsingleton.elim u v
  subst h
  simp

/-- Any simple graph on a finite vertex type of cardinality $1$ is isomorphic to $K_1$ (`⊤ : SimpleGraph (Fin 1)`). -/
noncomputable def isoTopFinOneOfCardEqOne {W : Type*} [Fintype W] (G : SimpleGraph W)
    (h : Fintype.card W = 1) : G ≃g (⊤ : SimpleGraph (Fin 1)) := by
  let e : W ≃ Fin 1 := Fintype.equivFinOfCardEq h
  refine ⟨e, ?_⟩
  intro u v
  have huv : u = v := e.injective (Subsingleton.elim (e u) (e v))
  subst huv
  simp

/-- Every simple graph on a $1$-element finite vertex type belongs to $\mathcal{J}(\mathcal{B}_k^*)$ (`InJClosure k`). -/
theorem inJClosure_of_card_eq_one (k : ℕ) {W : Type} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) (h : Fintype.card W = 1) : InJClosure k G :=
  InJClosure.base G (Or.inl ⟨isoTopFinOneOfCardEqOne G h⟩)

/-- If every neighbor of $v_0$ in $G$ equals $u_0$, then $\deg_G(v_0) = |N_G(v_0)| \le 1$. -/
theorem card_neighborFinsetIn_le_one_of_unique {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) (v₀ u₀ : W) (h : ∀ u : W, G.Adj v₀ u → u = u₀) :
    (neighborFinsetIn G v₀ Finset.univ).card ≤ 1 := by
  refine Finset.card_le_one.mpr ?_
  intro x hx y hy
  rw [mem_neighborFinsetIn_iff] at hx hy
  exact (h x hx.2).trans (h y hy.2).symm

/-- Every finite acyclic graph (forest) on at least $2$ vertices contains a vertex $v_0$ of degree at most $1$
(either an isolated vertex of degree $0$ or a pendant leaf of degree $1$ in a non-trivial connected tree component). -/
theorem forest_exists_vert_degree_le_one {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph W) (hF : F.IsAcyclic) (hcard : 2 ≤ Fintype.card W) :
    ∃ v₀ : W, (neighborFinsetIn F v₀ Finset.univ).card ≤ 1 := by
  classical
  haveI : Nonempty W := Fintype.card_pos_iff.mp (by omega)
  let w₀ : W := Classical.arbitrary W
  let c : F.ConnectedComponent := F.connectedComponentMk w₀
  have hTree : c.toSimpleGraph.IsTree := hF.isTree_connectedComponent c
  letI : Fintype ↥c := Fintype.ofFinite ↥c
  letI : DecidableRel c.toSimpleGraph.Adj := Classical.decRel _
  by_cases h_nontriv : Nontrivial ↥c
  · obtain ⟨v_c, hv_deg⟩ := hTree.exists_vert_degree_one_of_nontrivial
    obtain ⟨u_c, _, hu_uniq⟩ := (SimpleGraph.degree_eq_one_iff_existsUnique_adj).mp hv_deg
    refine ⟨v_c.1, Finset.card_le_one.mpr ?_⟩
    intro x₁ hx₁ x₂ hx₂
    rw [mem_neighborFinsetIn_iff] at hx₁ hx₂
    have hx₁_c : x₁ ∈ c := (c.mem_supp_congr_adj hx₁.2).mp v_c.2
    have hx₂_c : x₂ ∈ c := (c.mem_supp_congr_adj hx₂.2).mp v_c.2
    have h₁ : (⟨x₁, hx₁_c⟩ : ↥c) = u_c := hu_uniq ⟨x₁, hx₁_c⟩ hx₁.2
    have h₂ : (⟨x₂, hx₂_c⟩ : ↥c) = u_c := hu_uniq ⟨x₂, hx₂_c⟩ hx₂.2
    exact congr_arg Subtype.val (h₁.trans h₂.symm)
  · rw [not_nontrivial_iff_subsingleton] at h_nontriv
    refine ⟨w₀, Finset.card_le_one.mpr ?_⟩
    intro x₁ hx₁ _ _
    rw [mem_neighborFinsetIn_iff] at hx₁
    have hw₀_c : w₀ ∈ c := ConnectedComponent.connectedComponentMk_mem
    have hx₁_c : x₁ ∈ c := (c.mem_supp_congr_adj hx₁.2).mp hw₀_c
    have heq : (⟨x₁, hx₁_c⟩ : ↥c) = ⟨w₀, hw₀_c⟩ := Subsingleton.elim _ _
    have h_eq_val : x₁ = w₀ := congr_arg Subtype.val heq
    exact False.elim (F.loopless w₀ (h_eq_val ▸ hx₁.2))

/--
**Proposition 6(1b) — Every Finite Forest Belongs to $\mathcal{J}(\mathcal{B}_k^*)$ (`forest_in_InJClosure`, `main.tex` line 1003)**:
For every non-empty finite vertex type `W` and every acyclic graph `F : SimpleGraph W` (`F.IsAcyclic`),
`InJClosure k F` holds for all $k \in \mathbb{N}$, proved by strong induction on $|W|$ via `InJClosure.add_leaf`.
-/
theorem forest_in_InJClosure (k : ℕ) {W : Type} [Fintype W] [DecidableEq W] [Nonempty W]
    (F : SimpleGraph W) (hF : F.IsAcyclic) : InJClosure k F := by
  suffices h_ind : ∀ (n : ℕ) (U : Type) [Fintype U] [DecidableEq U] [Nonempty U]
      (G : SimpleGraph U), Fintype.card U = n → G.IsAcyclic → InJClosure k G from
    h_ind (Fintype.card W) W F rfl hF
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro U _ _ _ G hcard hG
    have hn_pos : 1 ≤ n := by
      rw [← hcard]
      exact Fintype.card_pos
    rcases eq_or_lt_of_le hn_pos with rfl | hn2
    · exact inJClosure_of_card_eq_one k G hcard
    · obtain ⟨v₀, hv₀_deg⟩ := forest_exists_vert_degree_le_one G hG (by omega)
      let U' := {v : U // v ≠ v₀}
      have hcard' : Fintype.card U' = n - 1 := by
        rw [Fintype.card_subtype_compl, Fintype.card_ofSubsingleton, hcard]
      haveI : Nonempty U' := Fintype.card_pos_iff.mp (by omega)
      let G' : SimpleGraph U' := G.comap (Subtype.val : U' → U)
      have hG'_acyc : G'.IsAcyclic := hG.of_comap (Function.Embedding.subtype _)
      have ih_G' : InJClosure k G' := ih (n - 1) (by omega) U' G' hcard' hG'_acyc
      exact InJClosure.add_leaf G v₀ hv₀_deg ih_G'

/-- Helper: lifting a walk avoiding `v₀` into `G.comap Subtype.val`. -/
def liftWalkAvoiding {W : Type*} {G : SimpleGraph W} (v₀ : W) :
    ∀ {a b : W} (p : G.Walk a b) (hp : ∀ z ∈ p.support, z ≠ v₀),
      (G.comap (Subtype.val : {v : W // v ≠ v₀} → W)).Walk
        ⟨a, hp a p.start_mem_support⟩ ⟨b, hp b p.end_mem_support⟩
  | _, _, .nil, _ => .nil
  | a, _, @Walk.cons _ _ _ v _ hadj q, hp =>
      have hp' : ∀ z ∈ q.support, z ≠ v₀ := fun z hz => hp z (List.mem_cons_of_mem a hz)
      have hadj' : (G.comap (Subtype.val : {v : W // v ≠ v₀} → W)).Adj
          ⟨a, hp a (Walk.start_mem_support _)⟩ ⟨v, hp' v q.start_mem_support⟩ := hadj
      .cons hadj' (liftWalkAvoiding v₀ q hp')

@[simp]
theorem map_liftWalkAvoiding {W : Type*} {G : SimpleGraph W} (v₀ : W) {a b : W}
    (p : G.Walk a b) (hp : ∀ z ∈ p.support, z ≠ v₀) :
    (liftWalkAvoiding v₀ p hp).map (SimpleGraph.Embedding.comap (Function.Embedding.subtype _) G).toHom = p := by
  induction p with
  | nil => rfl
  | cons hadj q ih =>
    dsimp [liftWalkAvoiding]
    rw [ih]

/-- Adding a vertex `v₀` of degree at most $1$ to an acyclic graph preserves `IsAcyclic`. -/
theorem isAcyclic_of_add_leaf {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) (v₀ : W)
    (hdeg : (neighborFinsetIn G v₀ Finset.univ).card ≤ 1)
    (h_sub : (G.comap (Subtype.val : {v : W // v ≠ v₀} → W)).IsAcyclic) :
    G.IsAcyclic := by
  intro u c hc
  by_cases hv₀ : v₀ ∈ c.support
  · let c' : G.Walk v₀ v₀ := c.rotate hv₀
    have hc' : c'.IsCycle := hc.rotate hv₀
    have h_ne_nil : ¬c'.Nil := Walk.nil_iff_eq_nil.not.mpr hc'.ne_nil
    have hadj_snd : G.Adj v₀ c'.snd := c'.adj_snd h_ne_nil
    have hadj_pen : G.Adj v₀ c'.penultimate := G.symm (c'.adj_penultimate h_ne_nil)
    have h1 : c'.snd ∈ neighborFinsetIn G v₀ Finset.univ :=
      (mem_neighborFinsetIn_iff G v₀ Finset.univ c'.snd).mpr ⟨Finset.mem_univ _, hadj_snd⟩
    have h2 : c'.penultimate ∈ neighborFinsetIn G v₀ Finset.univ :=
      (mem_neighborFinsetIn_iff G v₀ Finset.univ c'.penultimate).mpr ⟨Finset.mem_univ _, hadj_pen⟩
    exact hc'.snd_ne_penultimate (Finset.card_le_one.mp hdeg _ h1 _ h2)
  · have hp : ∀ z ∈ c.support, z ≠ v₀ := fun z hz h => hv₀ (h ▸ hz)
    let c_lift := liftWalkAvoiding v₀ c hp
    have hc_lift : c_lift.IsCycle := by
      rw [← Walk.map_isCycle_iff_of_injective
        (f := (SimpleGraph.Embedding.comap (Function.Embedding.subtype _) G).toHom)
        Subtype.val_injective]
      rwa [map_liftWalkAvoiding]
    exact h_sub c_lift hc_lift

/-- Equivalence between `{v : Fin (n + 1) // v ≠ Fin.last n}` and `Fin n`. -/
def subtypeNeLastEquivFin (n : ℕ) : {v : Fin (n + 1) // v ≠ Fin.last n} ≃ Fin n where
  toFun u := ⟨u.1.1, Nat.lt_of_le_of_ne (Fin.is_le u.1) (Fin.val_ne_of_ne u.2)⟩
  invFun i := ⟨i.castSucc, Fin.ne_of_lt (Fin.castSucc_lt_last i)⟩
  left_inv u := by ext; rfl
  right_inv i := by ext; rfl

/-- Graph isomorphism between `G.comap Subtype.val` (deleting `Fin.last n`) and `G.comap Fin.castSuccEmb`. -/
def comapSubtypeNeLastIso (n : ℕ) (G : SimpleGraph (Fin (n + 1))) :
    G.comap (Subtype.val : {v : Fin (n + 1) // v ≠ Fin.last n} → Fin (n + 1)) ≃g
      G.comap (Fin.castSuccEmb : Fin n ↪ Fin (n + 1)) where
  toEquiv := subtypeNeLastEquivFin n
  map_rel_iff' := Iff.rfl

/-- The 6-vertex tree `EGraph` ($E\text{-graph}$) is acyclic (`EGraph.IsAcyclic`), proved by five successive
degree-$1$ leaf deletions from `Fin 6` down to `Fin 1`. -/
theorem eGraph_isAcyclic : EGraph.IsAcyclic := by
  let G5 : SimpleGraph (Fin 5) := EGraph.comap Fin.castSuccEmb
  let G4 : SimpleGraph (Fin 4) := G5.comap Fin.castSuccEmb
  let G3 : SimpleGraph (Fin 3) := G4.comap Fin.castSuccEmb
  let G2 : SimpleGraph (Fin 2) := G3.comap Fin.castSuccEmb
  let G1 : SimpleGraph (Fin 1) := G2.comap Fin.castSuccEmb
  have h1 : G1.IsAcyclic := SimpleGraph.IsAcyclic.of_subsingleton
  have h2 : G2.IsAcyclic := by
    refine isAcyclic_of_add_leaf G2 (Fin.last 1)
      (card_neighborFinsetIn_le_one_of_unique G2 (Fin.last 1) 0 (by intro u; fin_cases u <;> decide)) ?_
    exact (comapSubtypeNeLastIso 1 G2).isAcyclic_iff.mpr h1
  have h3 : G3.IsAcyclic := by
    refine isAcyclic_of_add_leaf G3 (Fin.last 2)
      (card_neighborFinsetIn_le_one_of_unique G3 (Fin.last 2) 1 (by intro u; fin_cases u <;> decide)) ?_
    exact (comapSubtypeNeLastIso 2 G3).isAcyclic_iff.mpr h2
  have h4 : G4.IsAcyclic := by
    refine isAcyclic_of_add_leaf G4 (Fin.last 3)
      (card_neighborFinsetIn_le_one_of_unique G4 (Fin.last 3) 2 (by intro u; fin_cases u <;> decide)) ?_
    exact (comapSubtypeNeLastIso 3 G4).isAcyclic_iff.mpr h3
  have h5 : G5.IsAcyclic := by
    refine isAcyclic_of_add_leaf G5 (Fin.last 4)
      (card_neighborFinsetIn_le_one_of_unique G5 (Fin.last 4) 3 (by intro u; fin_cases u <;> decide)) ?_
    exact (comapSubtypeNeLastIso 4 G5).isAcyclic_iff.mpr h4
  refine isAcyclic_of_add_leaf EGraph (Fin.last 5)
    (card_neighborFinsetIn_le_one_of_unique EGraph (Fin.last 5) 2 (by intro u; fin_cases u <;> decide)) ?_
  exact (comapSubtypeNeLastIso 5 EGraph).isAcyclic_iff.mpr h5

/-- `EGraph` ($E\text{-graph}$) belongs to $\mathcal{J}(\mathcal{B}_1^*)$ (`InJClosure 1 EGraph`, `main.tex` line 986). -/
theorem eGraph_in_InJClosure_one : InJClosure 1 EGraph :=
  forest_in_InJClosure 1 EGraph eGraph_isAcyclic

/-- Computable `DecidableRel` instance for vertex substitution `substGraph H₁ v₀ H₂`. -/
private instance instDecidableRelSubstGraphAdj {V₁ V₂ : Type*} (H₁ : SimpleGraph V₁) (v₀ : V₁)
    (H₂ : SimpleGraph V₂) [DecidableRel H₁.Adj] [DecidableRel H₂.Adj] :
    DecidableRel (substGraph H₁ v₀ H₂).Adj := fun a b => by
  cases a <;> cases b <;> dsimp [substGraph] <;> infer_instance

/-- Explicit graph isomorphism $K_2[1 \leftarrow K_2] \simeq_g K_3$ (`substGraph (⊤ : SimpleGraph (Fin 2)) 1 (⊤ : SimpleGraph (Fin 2)) ≃g (⊤ : SimpleGraph (Fin 3))`). -/
def substK2K2IsoK3 :
    substGraph (⊤ : SimpleGraph (Fin 2)) 1 (⊤ : SimpleGraph (Fin 2)) ≃g
      (⊤ : SimpleGraph (Fin 3)) where
  toFun
    | Sum.inl _ => 0
    | Sum.inr 0 => 1
    | Sum.inr 1 => 2
  invFun
    | 0 => Sum.inl ⟨0, by decide⟩
    | 1 => Sum.inr 0
    | 2 => Sum.inr 1
  left_inv x := by
    rcases x with ⟨u, hu⟩ | r
    · fin_cases u
      · rfl
      · exact False.elim (hu rfl)
    · fin_cases r <;> rfl
  right_inv y := by
    fin_cases y <;> rfl
  map_rel_iff' := by
    intro a b
    rcases a with ⟨u, hu⟩ | r <;> rcases b with ⟨w, hw⟩ | s
    · fin_cases u <;> fin_cases w <;> first | exact False.elim (hu rfl) | exact False.elim (hw rfl) | simp [substGraph]
    · fin_cases u <;> fin_cases s <;> first | exact False.elim (hu rfl) | simp [substGraph]
    · fin_cases r <;> fin_cases w <;> first | exact False.elim (hw rfl) | simp [substGraph]
    · fin_cases r <;> fin_cases s <;> simp [substGraph]

/-- `BirdGraph` ($\mathrm{Bird}$) belongs to $\mathcal{J}(\mathcal{B}_1^*)$ (`InJClosure 1 BirdGraph`, `main.tex` line 986),
constructed explicitly from $K_3 \cong K_2[1 \leftarrow K_2]$ by three successive degree-$1$ leaf additions
($b_4, b_5, b_6$, corresponding to indices `3, 4, 5 : Fin 6`). -/
theorem birdGraph_in_InJClosure_one : InJClosure 1 BirdGraph := by
  have hk2 : InJClosure 1 (⊤ : SimpleGraph (Fin 2)) :=
    InJClosure.base _ (Or.inr (Or.inl ⟨SimpleGraph.Iso.refl⟩))
  have hk3_subst : InJClosure 1 (substGraph (⊤ : SimpleGraph (Fin 2)) 1 (⊤ : SimpleGraph (Fin 2))) :=
    InJClosure.subst _ 1 _ hk2 hk2
  have hk3 : InJClosure 1 (⊤ : SimpleGraph (Fin 3)) :=
    InJClosure.iso _ _ hk3_subst ⟨substK2K2IsoK3⟩
  let B5 : SimpleGraph (Fin 5) := BirdGraph.comap Fin.castSuccEmb
  let B4 : SimpleGraph (Fin 4) := B5.comap Fin.castSuccEmb
  let B3 : SimpleGraph (Fin 3) := B4.comap Fin.castSuccEmb
  have hB3_eq : B3 = (⊤ : SimpleGraph (Fin 3)) := by
    ext u v
    fin_cases u <;> fin_cases v <;> decide
  have hB3 : InJClosure 1 B3 := hB3_eq ▸ hk3
  have hB4 : InJClosure 1 B4 := by
    refine InJClosure.add_leaf B4 (Fin.last 3)
      (card_neighborFinsetIn_le_one_of_unique B4 (Fin.last 3) 0 (by intro u; fin_cases u <;> decide)) ?_
    exact InJClosure.iso B3 _ hB3 ⟨(comapSubtypeNeLastIso 3 B4).symm⟩
  have hB5 : InJClosure 1 B5 := by
    refine InJClosure.add_leaf B5 (Fin.last 4)
      (card_neighborFinsetIn_le_one_of_unique B5 (Fin.last 4) 3 (by intro u; fin_cases u <;> decide)) ?_
    exact InJClosure.iso B4 _ hB4 ⟨(comapSubtypeNeLastIso 4 B5).symm⟩
  refine InJClosure.add_leaf BirdGraph (Fin.last 5)
    (card_neighborFinsetIn_le_one_of_unique BirdGraph (Fin.last 5) 1 (by intro u; fin_cases u <;> decide)) ?_
  exact InJClosure.iso B5 _ hB5 ⟨(comapSubtypeNeLastIso 5 BirdGraph).symm⟩

/-!
### Section 2: Proposition 6(1a), Part 1 — `witnessHBird` and Open-Interval Thresholded Wonderfulness of `BirdGraph`
(`main.tex` line 986)

Since $\mathrm{Bird} - b_1 \cong K_2 \sqcup P_3$, its complement $H_{\mathrm{Bird}} := \overline{\mathrm{Bird}} - b_1$
(`witnessHBird`) is the 5-vertex, 7-edge join $K_2[0 \leftarrow \overline{K_2}, 1 \leftarrow \overline{P_3}] \in \mathcal{H}(\mathcal{B}_1^*)$,
whose special set $S_0 = N_{\overline{\mathrm{Bird}}}(b_1) = \{b_5, b_6\}$ (`specHBird = {3, 4}`) spans an edge
with $E_{\mathrm{non}}(S_0) = \emptyset$. On the open interval $0 < |N_G(v) \cap B_i| < \frac{1}{2}|B_i|$,
picking neighbors in $B_{j_{b_5}}, B_{j_{b_6}}$ and sequential non-neighbors in $B_{j_{b_4}}, B_{j_{b_2}}, B_{j_{b_3}}$
deterministically embeds $\overline{\mathrm{Bird}}$ into $G$, certifying `IsThresholdedWonderful BirdGraph`.
-/

/--
The 5-vertex, 7-edge Stage-2 witness graph $H_{\mathrm{Bird}} := \overline{\mathrm{Bird}} - b_1$
(`witnessHBird : SimpleGraph (Fin 5)`, Proposition 6(1a), `main.tex` line 986), where `0..4 : Fin 5`
correspond to `1..5 : Fin 6` ($b_2, b_3, b_4, b_5, b_6$ in `BirdGraph`).
Its special vertex set $S_0 = N_{\overline{\mathrm{Bird}}}(b_1) = \{b_5, b_6\}$ is `{3, 4 : Fin 5}`,
which spans an edge in `witnessHBird` (`witnessHBird.Adj 3 4`).
-/
def witnessHBird : SimpleGraph (Fin 5) :=
  BirdGraphᶜ.comap (Fin.succEmb 5)

/-- Computable `DecidableRel` instance for `witnessHBird.Adj`. -/
instance instDecidableRelWitnessHBirdAdj : DecidableRel witnessHBird.Adj := fun r s =>
  inferInstanceAs (Decidable (BirdGraphᶜ.Adj r.succ s.succ))

/-- Special vertex set $S_0 = N_{\overline{\mathrm{Bird}}}(b_1) = \{b_5, b_6\}$ (`{3, 4 : Fin 5}`) of `witnessHBird`. -/
def specHBird : Finset (Fin 5) := {3, 4}

/-- The special vertex set $S_0 = \{3, 4\}$ spans an edge in `witnessHBird` ($b_5 b_6 \in E(H_{\mathrm{Bird}})$, so $E_{\mathrm{non}}(S_0) = \emptyset$). -/
theorem witnessHBird_adj_spec : witnessHBird.Adj 3 4 := by decide

/-- `(pathGraph 3)ᶜ` is acyclic. -/
theorem pathGraph3Compl_isAcyclic : ((pathGraph 3)ᶜ).IsAcyclic := by
  let P3c := (pathGraph 3)ᶜ
  let G2 : SimpleGraph (Fin 2) := P3c.comap Fin.castSuccEmb
  let G1 : SimpleGraph (Fin 1) := G2.comap Fin.castSuccEmb
  have h1 : G1.IsAcyclic := SimpleGraph.IsAcyclic.of_subsingleton
  have h2 : G2.IsAcyclic := by
    refine isAcyclic_of_add_leaf G2 (Fin.last 1)
      (card_neighborFinsetIn_le_one_of_unique G2 (Fin.last 1) 0 (by intro u; fin_cases u <;> decide)) ?_
    exact (comapSubtypeNeLastIso 1 G2).isAcyclic_iff.mpr h1
  refine isAcyclic_of_add_leaf P3c (Fin.last 2)
    (card_neighborFinsetIn_le_one_of_unique P3c (Fin.last 2) 0 (by intro u; fin_cases u <;> decide)) ?_
  exact (comapSubtypeNeLastIso 2 P3c).isAcyclic_iff.mpr h2

/-- `witnessHBirdᶜ` ($\mathrm{Bird} - b_1 \cong K_2 \sqcup P_3$) is acyclic. -/
theorem witnessHBirdCompl_isAcyclic : (witnessHBirdᶜ).IsAcyclic := by
  let H5 : SimpleGraph (Fin 5) := witnessHBirdᶜ
  let H4 : SimpleGraph (Fin 4) := H5.comap Fin.castSuccEmb
  let H3 : SimpleGraph (Fin 3) := H4.comap Fin.castSuccEmb
  let H2 : SimpleGraph (Fin 2) := H3.comap Fin.castSuccEmb
  let H1 : SimpleGraph (Fin 1) := H2.comap Fin.castSuccEmb
  have h1 : H1.IsAcyclic := SimpleGraph.IsAcyclic.of_subsingleton
  have h2 : H2.IsAcyclic := by
    refine isAcyclic_of_add_leaf H2 (Fin.last 1)
      (card_neighborFinsetIn_le_one_of_unique H2 (Fin.last 1) 0 (by intro u; fin_cases u <;> decide)) ?_
    exact (comapSubtypeNeLastIso 1 H2).isAcyclic_iff.mpr h1
  have h3 : H3.IsAcyclic := by
    refine isAcyclic_of_add_leaf H3 (Fin.last 2)
      (card_neighborFinsetIn_le_one_of_unique H3 (Fin.last 2) 0 (by intro u; fin_cases u <;> decide)) ?_
    exact (comapSubtypeNeLastIso 2 H3).isAcyclic_iff.mpr h2
  have h4 : H4.IsAcyclic := by
    refine isAcyclic_of_add_leaf H4 (Fin.last 3)
      (card_neighborFinsetIn_le_one_of_unique H4 (Fin.last 3) 2 (by intro u; fin_cases u <;> decide)) ?_
    exact (comapSubtypeNeLastIso 3 H4).isAcyclic_iff.mpr h3
  refine isAcyclic_of_add_leaf H5 (Fin.last 4)
    (card_neighborFinsetIn_le_one_of_unique H5 (Fin.last 4) 0 (by intro u; fin_cases u <;> decide)) ?_
  exact (comapSubtypeNeLastIso 4 H5).isAcyclic_iff.mpr h4

/-- Explicit graph isomorphism $K_2[0 \leftarrow \overline{K_2}, 1 \leftarrow \overline{P_3}] \simeq_g H_{\mathrm{Bird}}$
(`main.tex` line 986: $H_{\mathrm{Bird}} \cong K_2\bigl[1 \leftarrow \{b_4, b_5\}_{\overline{K_2}},\, 2 \leftarrow \{b_6, b_2, b_3\}_{\overline{P_3}}\bigr]$). -/
def substK2ComplP3ComplIsoWitnessHBird :
    substGraph
      (substGraph (⊤ : SimpleGraph (Fin 2)) 0 (⊥ : SimpleGraph (Fin 2)))
      (Sum.inl ⟨1, by decide⟩)
      ((pathGraph 3)ᶜ) ≃g witnessHBird where
  toFun
    | Sum.inl ⟨Sum.inl ⟨u, hu⟩, hne⟩ =>
        False.elim (by fin_cases u; exact hu rfl; exact hne rfl)
    | Sum.inl ⟨Sum.inr 0, _⟩ => 2
    | Sum.inl ⟨Sum.inr 1, _⟩ => 3
    | Sum.inr 0 => 1
    | Sum.inr 1 => 0
    | Sum.inr 2 => 4
  invFun
    | 0 => Sum.inr 1
    | 1 => Sum.inr 0
    | 2 => Sum.inl ⟨Sum.inr 0, by decide⟩
    | 3 => Sum.inl ⟨Sum.inr 1, by decide⟩
    | 4 => Sum.inr 2
  left_inv x := by
    rcases x with ⟨⟨⟨u, hu⟩ | r, hne⟩⟩ | s
    · fin_cases u
      · exact False.elim (hu rfl)
      · exact False.elim (hne rfl)
    · fin_cases r <;> rfl
    · fin_cases s <;> rfl
  right_inv y := by
    fin_cases y <;> rfl
  map_rel_iff' := by
    intro a b
    rcases a with ⟨⟨⟨u, hu⟩ | r, hne⟩⟩ | s
    · fin_cases u; exact False.elim (hu rfl); exact False.elim (hne rfl)
    · rcases b with ⟨⟨⟨w, hw⟩ | r', hne'⟩⟩ | s'
      · fin_cases w; exact False.elim (hw rfl); exact False.elim (hne' rfl)
      · fin_cases r <;> fin_cases r' <;> simp [substGraph, witnessHBird, BirdGraph]
      · fin_cases r <;> fin_cases s' <;> simp [substGraph, witnessHBird, BirdGraph]
    · rcases b with ⟨⟨⟨w, hw⟩ | r', hne'⟩⟩ | s'
      · fin_cases w; exact False.elim (hw rfl); exact False.elim (hne' rfl)
      · fin_cases s <;> fin_cases r' <;> simp [substGraph, witnessHBird, BirdGraph]
      · fin_cases s <;> fin_cases s' <;> simp [substGraph, witnessHBird, BirdGraph, pathGraph_adj]

/-- `witnessHBird` ($H_{\mathrm{Bird}}$) belongs to $\mathcal{H}(\mathcal{B}_1^*)$ (`InHClosure 1 witnessHBird`, `main.tex` line 986),
since $H_{\mathrm{Bird}} \cong K_2[0 \leftarrow \overline{K_2}, 1 \leftarrow \overline{P_3}] \in \mathcal{J}(\mathcal{B}_1^*)$
and $\overline{H_{\mathrm{Bird}}} = \mathrm{Bird} - b_1 \cong K_2 \sqcup P_3$ is acyclic. -/
theorem witnessHBird_inHClosure_one : InHClosure 1 witnessHBird := by
  refine ⟨?_, forest_in_InJClosure 1 (witnessHBirdᶜ) witnessHBirdCompl_isAcyclic⟩
  have hk2 : InJClosure 1 (⊤ : SimpleGraph (Fin 2)) :=
    InJClosure.base _ (Or.inr (Or.inl ⟨SimpleGraph.Iso.refl⟩))
  have hk2_compl : InJClosure 1 (⊥ : SimpleGraph (Fin 2)) :=
    InJClosure.base _ (Or.inr (Or.inr (Or.inl ⟨SimpleGraph.Iso.refl⟩)))
  have hp3_compl : InJClosure 1 ((pathGraph 3)ᶜ) :=
    forest_in_InJClosure 1 ((pathGraph 3)ᶜ) pathGraph3Compl_isAcyclic
  have hj1 := InJClosure.subst (⊤ : SimpleGraph (Fin 2)) 0 (⊥ : SimpleGraph (Fin 2)) hk2 hk2_compl
  have hj2 := InJClosure.subst _ (Sum.inl ⟨1, by decide⟩) ((pathGraph 3)ᶜ) hj1 hp3_compl
  exact InJClosure.iso _ witnessHBird hj2 ⟨substK2ComplP3ComplIsoWitnessHBird⟩

/-- Exhaustive classification of the $3$ non-edges ($6$ ordered non-adjacent pairs) of `witnessHBird`:
$\{0, 1\}$ ($b_2 b_3$), $\{0, 4\}$ ($b_2 b_6$), and $\{2, 3\}$ ($b_4 b_5$). -/
theorem witnessHBird_nonadj_cases (r s : Fin 5) (hne : r ≠ s) (hn : ¬witnessHBird.Adj r s) :
    (r = 0 ∧ s = 1) ∨ (r = 1 ∧ s = 0) ∨
    (r = 0 ∧ s = 4) ∨ (r = 4 ∧ s = 0) ∨
    (r = 2 ∧ s = 3) ∨ (r = 3 ∧ s = 2) := by
  fin_cases r <;> fin_cases s <;> revert hne hn <;> decide

/-- Adjacency of `0` ($b_1$) to `r.succ` in `BirdGraphᶜ`: $N_{\overline{\mathrm{Bird}}}(b_1) = \{b_5, b_6\}$ (`r = 3 ∨ r = 4`). -/
theorem birdGraphCompl_adj_zero_succ (r : Fin 5) :
    BirdGraphᶜ.Adj 0 r.succ ↔ r = 3 ∨ r = 4 := by
  fin_cases r <;> decide

/-- Adjacency between `r.succ` and `s.succ` in `BirdGraphᶜ` equals `witnessHBird.Adj r s`. -/
theorem birdGraphCompl_adj_succ_succ (r s : Fin 5) :
    BirdGraphᶜ.Adj r.succ s.succ ↔ witnessHBird.Adj r s :=
  Iff.rfl

/-- If `emb : Fin 5 ↪ Fin ℓ` embeds `witnessHBird` into `blockadePatternGraph G B`,
adjacent indices in `witnessHBird` correspond to $100\%$ complete block pairs in $G$. -/
theorem adj_of_witnessHBird_adj {V : Type*} {G : SimpleGraph V} {ℓ : ℕ} {B : Fin ℓ → Finset V}
    (emb : Fin 5 ↪ Fin ℓ)
    (hemb_adj : witnessHBird = (blockadePatternGraph G B).comap emb)
    {r s : Fin 5} (hadj : witnessHBird.Adj r s)
    {ur us : V} (hur : ur ∈ B (emb r)) (hus : us ∈ B (emb s)) :
    G.Adj ur us := by
  have hJ : (blockadePatternGraph G B).Adj (emb r) (emb s) := by
    have h := congr_arg (fun H => H.Adj r s) hemb_adj
    exact h.mp hadj
  exact hJ.2 ur hur us hus

/-- If `emb : Fin 5 ↪ Fin ℓ` embeds `witnessHBird` into `blockadePatternGraph G B` for a
complete-or-$x$-sparse blockade $B$, distinct non-adjacent indices in `witnessHBird` are two-sided $x$-sparse in $G$. -/
theorem sparse_of_not_witnessHBird_adj {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {S : Finset V} {ℓ : ℕ} {w x : ℝ} {B : Fin ℓ → Finset V}
    (hB : IsCompleteOrXSparseBlockadeIn G S ℓ w x B)
    (emb : Fin 5 ↪ Fin ℓ)
    (hemb_adj : witnessHBird = (blockadePatternGraph G B).comap emb)
    {r j : Fin 5} (hne : r ≠ j) (hnadj : ¬witnessHBird.Adj r j)
    {ur : V} (hur : ur ∈ B (emb r)) :
    ((neighborFinsetIn G ur (B (emb j))).card : ℝ) ≤ x * ((B (emb j)).card : ℝ) := by
  have hne_emb : emb r ≠ emb j := emb.injective.ne hne
  rcases hB.2 (emb r) (emb j) hne_emb with hcomp | hsparse
  · exfalso
    have hJ : (blockadePatternGraph G B).Adj (emb r) (emb j) := ⟨hne_emb, hcomp⟩
    have h := congr_arg (fun H => H.Adj r j) hemb_adj
    exact hnadj (h.mpr hJ)
  · exact hsparse.2 ur hur

/-- **Deterministic Open-Interval Embedding of $\overline{\mathrm{Bird}}$ (`patternGraph_openAttachment_witnessHBird_free`, `main.tex` line 986)**:
In any `BirdGraphᶜ`-free graph $G$ with a complete-or-$x$-sparse blockade $B$ ($6 x \le 1/2$) and external
vertex $v \notin \bigcup_i B_i$, there is no induced embedding of `witnessHBird` into `blockadePatternGraph G B`
on the open-interval attachment set `openAttachmentIndices G B v` ($0 < |N_G(v) \cap B_i| < \frac{1}{2}|B_i|$). -/
theorem patternGraph_openAttachment_witnessHBird_free {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {S : Finset V} {ℓ : ℕ} {w x : ℝ} {B : Fin ℓ → Finset V}
    (hG : IsInducedSubgraphFree G BirdGraphᶜ)
    (hB : IsCompleteOrXSparseBlockadeIn G S ℓ w x B)
    (hx : 6 * x ≤ 1 / 2)
    (v : V) (hv_ext : ∀ i : Fin ℓ, v ∉ B i)
    (emb : Fin 5 ↪ Fin ℓ)
    (hemb_mem : ∀ r : Fin 5, emb r ∈ openAttachmentIndices G B v)
    (hemb_adj : witnessHBird = (blockadePatternGraph G B).comap emb) :
    False := by
  obtain ⟨u3, hu3_mem, hv3⟩ := exists_adj_in_block_of_pos G (B (emb 3)) v
    ((mem_openAttachmentIndices G B v (emb 3)).mp (hemb_mem 3)).1
  obtain ⟨u4, hu4_mem, hv4⟩ := exists_adj_in_block_of_pos G (B (emb 4)) v
    ((mem_openAttachmentIndices G B v (emb 4)).mp (hemb_mem 4)).1
  have hs32 := sparse_of_not_witnessHBird_adj hB emb hemb_adj (r := 3) (j := 2)
    (by decide) (by decide) hu3_mem
  obtain ⟨u2, hu2_mem, hv2, h32, _, _⟩ := exists_nonadj_three_in_block G hx
    ((mem_openAttachmentIndices G B v (emb 2)).mp (hemb_mem 2)).2 hs32 hs32 hs32
  have hs40 := sparse_of_not_witnessHBird_adj hB emb hemb_adj (r := 4) (j := 0)
    (by decide) (by decide) hu4_mem
  obtain ⟨u0, hu0_mem, hv0, h40, _, _⟩ := exists_nonadj_three_in_block G hx
    ((mem_openAttachmentIndices G B v (emb 0)).mp (hemb_mem 0)).2 hs40 hs40 hs40
  have hs01 := sparse_of_not_witnessHBird_adj hB emb hemb_adj (r := 0) (j := 1)
    (by decide) (by decide) hu0_mem
  obtain ⟨u1, hu1_mem, hv1, h01, _, _⟩ := exists_nonadj_three_in_block G hx
    ((mem_openAttachmentIndices G B v (emb 1)).mp (hemb_mem 1)).2 hs01 hs01 hs01
  let u : Fin 5 → V := ![u0, u1, u2, u3, u4]
  have hu_mem : ∀ r : Fin 5, u r ∈ B (emb r) := by
    intro r
    fin_cases r <;> assumption
  let f : Fin 6 ↪ V :=
    { toFun := Fin.cons v u
      inj' := by
        intro a b
        refine Fin.cases ?_ ?_ a <;> refine Fin.cases ?_ ?_ b
        · intro _; rfl
        · intro s hs
          simp only [Fin.cons_zero, Fin.cons_succ] at hs
          exact False.elim (hv_ext (emb s) (hs ▸ hu_mem s))
        · intro r hr
          simp only [Fin.cons_zero, Fin.cons_succ] at hr
          exact False.elim (hv_ext (emb r) (hr.symm ▸ hu_mem r))
        · intro r s hrs
          simp only [Fin.cons_succ] at hrs
          by_contra hne_fin
          have hne_r : r ≠ s := fun h => hne_fin (congr_arg Fin.succ h.symm)
          have hdisj := hB.1.pairwise_disjoint (emb r) (emb s) (emb.injective.ne hne_r)
          exact Finset.disjoint_left.mp hdisj (hu_mem r) (hrs ▸ hu_mem s) }
  have hf_zero : ∀ r : Fin 5, G.Adj (f 0) (f r.succ) ↔ r = 3 ∨ r = 4 := by
    intro r
    change G.Adj v (u r) ↔ r = 3 ∨ r = 4
    fin_cases r
    · exact iff_of_false hv0 (by decide)
    · exact iff_of_false hv1 (by decide)
    · exact iff_of_false hv2 (by decide)
    · exact iff_of_true hv3 (Or.inl rfl)
    · exact iff_of_true hv4 (Or.inr rfl)
  have hf_succ : ∀ r s : Fin 5, G.Adj (f r.succ) (f s.succ) ↔ witnessHBird.Adj r s := by
    intro r s
    change G.Adj (u r) (u s) ↔ witnessHBird.Adj r s
    constructor
    · intro hG_adj
      have hne : r ≠ s := fun h => G.loopless (u r) (h ▸ hG_adj)
      by_contra hnadj
      rcases witnessHBird_nonadj_cases r s hne hnadj with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h01 hG_adj
      · exact h01 (G.symm hG_adj)
      · exact h40 (G.symm hG_adj)
      · exact h40 hG_adj
      · exact h32 (G.symm hG_adj)
      · exact h32 hG_adj
    · intro hadj
      exact adj_of_witnessHBird_adj emb hemb_adj hadj (hu_mem r) (hu_mem s)
  have hBirdCompl : BirdGraphᶜ = G.comap f := by
    ext a b
    refine Fin.cases ?_ ?_ a <;> refine Fin.cases ?_ ?_ b
    · simp
    · intro s
      rw [comap_adj, birdGraphCompl_adj_zero_succ, hf_zero]
    · intro r
      rw [comap_adj, BirdGraphᶜ.adj_comm, G.adj_comm, birdGraphCompl_adj_zero_succ, hf_zero]
    · intro r s
      rw [comap_adj, birdGraphCompl_adj_succ_succ, hf_succ]
  exact hG ⟨f, hBirdCompl⟩

/-- Induced-subgraph formulation of `patternGraph_openAttachment_witnessHBird_free`:
the pattern graph induced on `openAttachmentIndices G B v` is `witnessHBird`-free. -/
theorem isInducedSubgraphFree_patternGraph_induce_openAttachment_witnessHBird
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {S : Finset V} {ℓ : ℕ} {w x : ℝ} {B : Fin ℓ → Finset V}
    (hG : IsInducedSubgraphFree G BirdGraphᶜ)
    (hB : IsCompleteOrXSparseBlockadeIn G S ℓ w x B)
    (hx : 6 * x ≤ 1 / 2)
    (v : V) (hv_ext : ∀ i : Fin ℓ, v ∉ B i) :
    IsInducedSubgraphFree
      ((blockadePatternGraph G B).induce (openAttachmentIndices G B v : Set (Fin ℓ)))
      witnessHBird := by
  rintro ⟨emb, hemb⟩
  let emb' : Fin 5 ↪ Fin ℓ := emb.trans (Function.Embedding.subtype _)
  have hemb_mem : ∀ r : Fin 5, emb' r ∈ openAttachmentIndices G B v := fun r => (emb r).2
  have hemb_adj : witnessHBird = (blockadePatternGraph G B).comap emb' := by
    ext r s
    have h := congr_arg (fun H => H.Adj r s) hemb
    simpa [emb', comap_adj] using h
  exact patternGraph_openAttachment_witnessHBird_free hG hB hx v hv_ext emb' hemb_mem hemb_adj

/--
**Proposition 6(1a) — Open-Interval Thresholded Wonderfulness of `BirdGraph` (`bird_isThresholdedWonderful`, `main.tex` line 986)**:
Given `HasErdosHajnalProp witnessHBird` ($H_{\mathrm{Bird}} \in \mathcal{EH}$), `BirdGraph` satisfies
`IsThresholdedWonderful BirdGraph` (Definition 2(4) of `main.tex`).
-/
theorem bird_isThresholdedWonderful (hEH : HasErdosHajnalProp witnessHBird) :
    IsThresholdedWonderful BirdGraph := by
  obtain ⟨c_H, hc_H, h_eh⟩ := hEH
  let a : ℕ := max 7 ⌈5 / c_H + 1⌉₊
  have ha7 : 7 ≤ a := le_max_left 7 _
  have ha_cH : 5 / c_H + 1 ≤ (a : ℝ) := by
    calc 5 / c_H + 1
      _ ≤ (⌈5 / c_H + 1⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (a : ℝ) := by exact_mod_cast le_max_right 7 ⌈5 / c_H + 1⌉₊
  refine ⟨a, 1 / 4, ha7, by norm_num, le_rfl, ?_⟩
  intro V _ _ G y δ_cross ℓ w B hy_pos hy_le hG hℓ_ge hδ_pos hδ_le hw_ge hB hB_eq_anti
  have hy_half : y ≤ 1 / 2 := by linarith
  have ha7_real : (7 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha7
  obtain ⟨hya_six, hya_le, h_rpow_ge⟩ :=
    wonderful_exponent_bounds hc_H ha7_real ha_cH hy_pos hy_half hℓ_ge
  have hℓ_pos : 0 < ℓ := by
    have : (0 : ℝ) < (ℓ : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hy_pos (-(a : ℝ))) hℓ_ge
    exact Nat.cast_pos.mp this
  have hδ_ya : δ_cross ≤ y ^ (a : ℝ) := by
    have h1 := hδ_le.trans (min_le_left _ _)
    rwa [Real.rpow_natCast]
  have hB_ya : IsCompleteOrXSparseBlockadeIn G Finset.univ ℓ (w : ℝ) (y ^ (a : ℝ)) B := by
    refine ⟨hB.1, fun i j hij => ?_⟩
    rcases hB.2 i j hij with hcomp | ⟨hsp1, hsp2⟩
    · exact Or.inl hcomp
    · refine Or.inr ⟨fun v hv => ?_, fun u hu => ?_⟩
      · exact (hsp1 v hv).trans (mul_le_mul_of_nonneg_right hδ_ya (Nat.cast_nonneg _))
      · exact (hsp2 u hu).trans (mul_le_mul_of_nonneg_right hδ_ya (Nat.cast_nonneg _))
  by_cases hAllSmall : ∀ v ∈ blockadeExternalVerts Finset.univ B,
      ((openAttachmentIndices G B v).card : ℝ) < y * (ℓ : ℝ)
  · right
    have hS_ne : (Finset.univ : Finset V).Nonempty := by
      obtain ⟨u, hu⟩ := hB.1.nonempty_blocks ⟨0, hℓ_pos⟩
      exact ⟨u, Finset.mem_univ u⟩
    obtain ⟨i_star, hi_star⟩ :=
      exists_block_few_openAttachmentExternalVerts G Finset.univ B hℓ_pos hy_pos hS_ne hAllSmall
    refine ⟨i_star, ?_⟩
    have h_set_eq : (Finset.univ \ Finset.biUnion Finset.univ B).filter (fun v =>
        0 < (neighborFinsetIn G v (B i_star)).card ∧
        ((neighborFinsetIn G v (B i_star)).card : ℝ) < (1 / 2) * (w : ℝ)) =
        openAttachmentExternalVerts G Finset.univ B i_star := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_biUnion,
        true_and, not_exists, mem_openAttachmentExternalVerts, mem_blockadeExternalVerts,
        mem_openAttachmentIndices, (hB_eq_anti i_star).1]
    rw [h_set_eq]
    have h_card_univ : ((Finset.univ : Finset V).card : ℝ) = (Fintype.card V : ℝ) := by simp
    rw [h_card_univ] at hi_star
    exact le_of_lt hi_star
  · left
    push_neg at hAllSmall
    rcases hAllSmall with ⟨v, hv_ext_mem, hv_large⟩
    have hv_ext : ∀ i : Fin ℓ, v ∉ B i := (mem_blockadeExternalVerts Finset.univ B v).mp hv_ext_mem |>.2
    have hFree := isInducedSubgraphFree_patternGraph_induce_openAttachment_witnessHBird
      hG hB_ya hya_six v hv_ext
    let I := openAttachmentIndices G B v
    let P_pat := blockadePatternGraph G B
    let J : SimpleGraph ↥(I : Set (Fin ℓ)) := P_pat.induce (I : Set (Fin ℓ))
    have hcard_J : Fintype.card ↥(I : Set (Fin ℓ)) = I.card := Fintype.card_coe I
    have hkappa_J : (I.card : ℝ) ^ c_H ≤ (kappa J : ℝ) := by
      rw [← hcard_J]
      exact h_eh ↥(I : Set (Fin ℓ)) J hFree
    have h_rpow_mono : (y * (ℓ : ℝ)) ^ c_H ≤ (I.card : ℝ) ^ c_H :=
      Real.rpow_le_rpow (by positivity) hv_large (le_of_lt hc_H)
    have hkappa_ge : 2 / (y ^ 4) ≤ (kappa J : ℝ) := h_rpow_ge.trans (h_rpow_mono.trans hkappa_J)
    have hya_nonneg : 0 ≤ y ^ (a : ℝ) := Real.rpow_nonneg (le_of_lt hy_pos) _
    have hy4_pos : 0 < y ^ 4 := by positivity
    rcases (kappa_cast_ge_iff J (2 / (y ^ 4))).mp hkappa_ge with hclique | hindep
    · obtain ⟨s, hs⟩ := J.exists_isNClique_cliqueNum
      let emb : ↥(I : Set (Fin ℓ)) ↪ Fin ℓ := Function.Embedding.subtype _
      let R := s.map emb
      have hR_card : (R.card : ℝ) = (J.cliqueNum : ℝ) := by
        rw [Finset.card_map, hs.card_eq]
      have hR_ge : 2 / (y ^ 4) ≤ (R.card : ℝ) := hR_card ▸ hclique
      have hR_pos : 0 < (R.card : ℝ) := lt_of_lt_of_le (div_pos zero_lt_two hy4_pos) hR_ge
      have hR_ne : R.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hR_pos)
      have h1R : 1 / (R.card : ℝ) ≤ y ^ 4 := by
        have h2 : 2 ≤ (R.card : ℝ) * (y ^ 4) := (div_le_iff₀ hy4_pos).mp hR_ge
        rw [div_le_iff₀ hR_pos]
        linarith
      have hClique : ∀ i ∈ R, ∀ j ∈ R, i ≠ j → P_pat.Adj i j := by
        intro i hi j hj hij
        rcases Finset.mem_map.mp hi with ⟨x₁, hx₁, rfl⟩
        rcases Finset.mem_map.mp hj with ⟨x₂, hx₂, rfl⟩
        exact hs.isClique hx₁ hx₂ (ne_of_apply_ne emb hij)
      refine ⟨blockUnion B R, Or.inr ?_, ?_⟩
      · exact isEpsSparseOn_compl_blockUnion_of_pattern_clique hB.1.pairwise_disjoint R hR_ne
          w (fun i _ => (hB_eq_anti i).1) hClique h1R
      · exact_mod_cast width_le_card_blockUnion B hB.1.pairwise_disjoint R hR_ne w
          (fun i _ => (hB_eq_anti i).1)
    · obtain ⟨s, hs⟩ := J.exists_isNIndepSet_indepNum
      let emb : ↥(I : Set (Fin ℓ)) ↪ Fin ℓ := Function.Embedding.subtype _
      let R := s.map emb
      have hR_card : (R.card : ℝ) = (J.indepNum : ℝ) := by
        rw [Finset.card_map, hs.card_eq]
      have hR_ge : 2 / (y ^ 4) ≤ (R.card : ℝ) := hR_card ▸ hindep
      have hR_pos : 0 < (R.card : ℝ) := lt_of_lt_of_le (div_pos zero_lt_two hy4_pos) hR_ge
      have hR_ne : R.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hR_pos)
      have h1R : 1 / (R.card : ℝ) + y ^ (a : ℝ) ≤ y ^ 4 := by
        have h2 : 2 ≤ (R.card : ℝ) * (y ^ 4) := (div_le_iff₀ hy4_pos).mp hR_ge
        have h1R_half : 1 / (R.card : ℝ) ≤ (y ^ 4) / 2 := by
          rw [div_le_div_iff₀ hR_pos zero_lt_two]
          linarith
        linarith
      have hIndep : ∀ i ∈ R, ∀ j ∈ R, i ≠ j → ¬P_pat.Adj i j := by
        intro i hi j hj hij
        rcases Finset.mem_map.mp hi with ⟨x₁, hx₁, rfl⟩
        rcases Finset.mem_map.mp hj with ⟨x₂, hx₂, rfl⟩
        exact hs.isIndepSet hx₁ hx₂ (ne_of_apply_ne emb hij)
      refine ⟨blockUnion B R, Or.inl ?_, ?_⟩
      · exact isEpsSparseOn_blockUnion_of_pattern_indep hB_ya hya_nonneg R hR_ne
          w (fun i _ => (hB_eq_anti i).1) hIndep h1R
      · exact_mod_cast width_le_card_blockUnion B hB.1.pairwise_disjoint R hR_ne w
          (fun i _ => (hB_eq_anti i).1)

/-!
### Section 3: Proposition 6(1a), Part 2 — 64-State `EGraph` Purity, Quotient Descent, and Comb Dichotomy for `BirdGraph`
(`main.tex` lines 988–1001)

This section establishes the Stage-1 Comb Dichotomy (`bird_comb_dichotomy`) for `BirdGraph`:
1. Observing $\overline{\mathrm{Bird}} \cong \Phi(P_3 \sqcup P_1, w_0)$ (`main.tex` line 986), any
   apex-cutter triple $(x, y, u)$ over $S_0 \subseteq B_i$ in a `BirdGraphᶜ`-free graph $G$ enforces
   **Rule (i)** (`bird_comb_rule1`) and **Rule (ii)** (`bird_comb_rule2`) on $G[S_0]$.
2. By a finite 64-state boolean case analysis (`eGraph_64_state_purity_bool`), Rules (i) and (ii)
   force $u$ to be pure to every induced copy of `EGraph` inside $S_0$ (`bird_egraph_pure`, `main.tex` lines 993–999).
3. Iteratively merging overlapping or mixed anticonnected blocks preserves apex-cutter purity via
   triple shifting $(x, y, u) \mapsto (y, u, u')$ (`isApexCutterPureBlock_union_of_mixed`), yielding
   the mixed-equivalence quotient partition $\mathcal{L}^q = (A_1, \dots, A_t)$ of $X_i$ whose pattern
   graph is `{EGraph, BirdGraphᶜ}`-free (`bird_quotient_descent`, `main.tex` line 1001).
4. Combining $\{E\text{-graph}, \overline{\mathrm{Bird}}\} \in \mathcal{EH}$ on $Y_i = B_i \setminus X_i$
   with cross-block pure blockades or Cauchy-series extraction on $\mathcal{L}^q$ proves `bird_comb_dichotomy`.
-/

/--
An apex-cutter triple $(x, y, u)$ over $S_0 \subseteq V$ in $G$ (`main.tex` line 988):
$x, y, u \notin S_0$, $x \neq y$, $\neg G.\text{Adj } x y$, both $x$ and $y$ are complete in $G$ to $S_0$,
$G.\text{Adj } x u$, and $\neg G.\text{Adj } y u$ (realizing the 2-vertex apex extension $\Phi(G[\{u\} \cup W], u)$
with $v_{\mathrm{univ}} = x$, $v_{\mathrm{alm}} = y$, and $w_0 = u$).
-/
structure IsApexCutterTriple {V : Type*} (G : SimpleGraph V) (S₀ : Finset V) (x y u : V) : Prop where
  x_not_mem : x ∉ S₀
  y_not_mem : y ∉ S₀
  u_not_mem : u ∉ S₀
  x_ne_y : x ≠ y
  not_adj_xy : ¬G.Adj x y
  x_complete : ∀ z ∈ S₀, G.Adj x z
  y_complete : ∀ z ∈ S₀, G.Adj y z
  adj_xu : G.Adj x u
  not_adj_yu : ¬G.Adj y u

/-- Restriction of an apex-cutter triple $(x, y, u)$ over $S_0$ to a subset $D \subseteq S_0$. -/
theorem IsApexCutterTriple.mono {V : Type*} {G : SimpleGraph V} {D S₀ : Finset V} {x y u : V}
    (hD : D ⊆ S₀) (h : IsApexCutterTriple G S₀ x y u) : IsApexCutterTriple G D x y u where
  x_not_mem hx := h.x_not_mem (hD hx)
  y_not_mem hy := h.y_not_mem (hD hy)
  u_not_mem hu := h.u_not_mem (hD hu)
  x_ne_y := h.x_ne_y
  not_adj_xy := h.not_adj_xy
  x_complete z hz := h.x_complete z (hD hz)
  y_complete z hz := h.y_complete z (hD hz)
  adj_xu := h.adj_xu
  not_adj_yu := h.not_adj_yu

/-- In any comb $(a, B)$ with external apex $v$, for any distinct block indices $r \neq i$ and any
vertex $u \in B_r$, the triple $(v, a_i, u)$ is an apex-cutter triple over any subset $D \subseteq B_i$. -/
theorem isApexCutterTriple_of_comb {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {S : Finset V} {ℓ : ℕ} {w : ℝ}
    {a : Fin ℓ → V} {B : Fin ℓ → Finset V} {v : V}
    (hcomb : IsCombIn G S ℓ w a B) (hapex : IsCombExternalApex G S ℓ a B v)
    {i r : Fin ℓ} (hri : r ≠ i) {D : Finset V} (hD : D ⊆ B i) {u : V} (hu : u ∈ B r) :
    IsApexCutterTriple G D v (a i) u where
  x_not_mem hv := hapex.not_in_blocks i (hD hv)
  y_not_mem ha := hcomb.apex_disjoint_blocks i i (hD ha)
  u_not_mem huD := Finset.disjoint_left.mp (hcomb.is_blockade.pairwise_disjoint r i hri) hu (hD huD)
  x_ne_y := hapex.not_apex i
  not_adj_xy := hapex.anticomplete_to_apices i
  x_complete z hz := hapex.complete_to_blocks i z (hD hz)
  y_complete z hz := hcomb.apex_complete_own i z (hD hz)
  adj_xu := hapex.complete_to_blocks r u hu
  not_adj_yu := hcomb.apex_anticomplete_other i r hri.symm u hu

/--
**Rule (i) (`bird_comb_rule1`, Proposition 6(1a), `main.tex` line 990)**:
In a `BirdGraphᶜ`-free graph $G$ with an apex-cutter triple $(x, y, u)$ over $S_0$,
$G[S_0]$ contains no induced $P_2 \sqcup P_1 = \{a b\} \sqcup \{c\}$ with
$G.\text{Adj } u a$, $\neg G.\text{Adj } u b$, and $\neg G.\text{Adj } u c$
(otherwise `![u, c, b, y, x, a]` embeds `BirdGraphᶜ` into $G$).
-/
theorem bird_comb_rule1 {V : Type*} {G : SimpleGraph V} {S₀ : Finset V} {x y u : V}
    (hG : IsInducedSubgraphFree G BirdGraphᶜ)
    (htriple : IsApexCutterTriple G S₀ x y u)
    {a b c : V} (ha : a ∈ S₀) (hb : b ∈ S₀) (hc : c ∈ S₀)
    (hac_ne : a ≠ c) (hbc_ne : b ≠ c)
    (hab : G.Adj a b) (hac : ¬G.Adj a c) (hbc : ¬G.Adj b c)
    (hua : G.Adj u a) (hub : ¬G.Adj u b) (huc : ¬G.Adj u c) :
    False := by
  let f : Fin 6 → V := ![u, c, b, y, x, a]
  have hab_ne : a ≠ b := G.ne_of_adj hab
  have hu_ne_a : u ≠ a := fun h => htriple.u_not_mem (h ▸ ha)
  have hu_ne_b : u ≠ b := fun h => htriple.u_not_mem (h ▸ hb)
  have hu_ne_c : u ≠ c := fun h => htriple.u_not_mem (h ▸ hc)
  have hu_ne_x : u ≠ x := (G.ne_of_adj htriple.adj_xu).symm
  have hu_ne_y : u ≠ y := fun h => htriple.not_adj_xy (h ▸ htriple.adj_xu)
  have hx_ne_a : x ≠ a := fun h => htriple.x_not_mem (h ▸ ha)
  have hx_ne_b : x ≠ b := fun h => htriple.x_not_mem (h ▸ hb)
  have hx_ne_c : x ≠ c := fun h => htriple.x_not_mem (h ▸ hc)
  have hy_ne_a : y ≠ a := fun h => htriple.y_not_mem (h ▸ ha)
  have hy_ne_b : y ≠ b := fun h => htriple.y_not_mem (h ▸ hb)
  have hy_ne_c : y ≠ c := fun h => htriple.y_not_mem (h ▸ hc)
  have hxa : G.Adj x a := htriple.x_complete a ha
  have hxb : G.Adj x b := htriple.x_complete b hb
  have hxc : G.Adj x c := htriple.x_complete c hc
  have hya : G.Adj y a := htriple.y_complete a ha
  have hyb : G.Adj y b := htriple.y_complete b hb
  have hyc : G.Adj y c := htriple.y_complete c hc
  have hxu : G.Adj x u := htriple.adj_xu
  have hnxy : ¬G.Adj x y := htriple.not_adj_xy
  have hnyx : ¬G.Adj y x := fun h => hnxy (G.symm h)
  have hnyu : ¬G.Adj y u := htriple.not_adj_yu
  have hnuy : ¬G.Adj u y := fun h => hnyu (G.symm h)
  have hca : ¬G.Adj c a := fun h => hac (G.symm h)
  have hcb : ¬G.Adj c b := fun h => hbc (G.symm h)
  have hbu : ¬G.Adj b u := fun h => hub (G.symm h)
  have hcu : ¬G.Adj c u := fun h => huc (G.symm h)
  have hf_inj : Function.Injective f := by
    intro p q hpq
    fin_cases p <;> fin_cases q <;> dsimp [f] at hpq ⊢ <;>
      first | rfl
            | exact False.elim (hu_ne_c hpq) | exact False.elim (hu_ne_c hpq.symm)
            | exact False.elim (hu_ne_b hpq) | exact False.elim (hu_ne_b hpq.symm)
            | exact False.elim (hu_ne_y hpq) | exact False.elim (hu_ne_y hpq.symm)
            | exact False.elim (hu_ne_x hpq) | exact False.elim (hu_ne_x hpq.symm)
            | exact False.elim (hu_ne_a hpq) | exact False.elim (hu_ne_a hpq.symm)
            | exact False.elim (hbc_ne hpq) | exact False.elim (hbc_ne hpq.symm)
            | exact False.elim (hy_ne_c hpq) | exact False.elim (hy_ne_c hpq.symm)
            | exact False.elim (hx_ne_c hpq) | exact False.elim (hx_ne_c hpq.symm)
            | exact False.elim (hac_ne hpq) | exact False.elim (hac_ne hpq.symm)
            | exact False.elim (hy_ne_b hpq) | exact False.elim (hy_ne_b hpq.symm)
            | exact False.elim (hx_ne_b hpq) | exact False.elim (hx_ne_b hpq.symm)
            | exact False.elim (hab_ne hpq) | exact False.elim (hab_ne hpq.symm)
            | exact False.elim (htriple.x_ne_y hpq) | exact False.elim (htriple.x_ne_y hpq.symm)
            | exact False.elim (hy_ne_a hpq) | exact False.elim (hy_ne_a hpq.symm)
            | exact False.elim (hx_ne_a hpq) | exact False.elim (hx_ne_a hpq.symm)
  refine hG ⟨⟨f, hf_inj⟩, ?_⟩
  ext p q
  simp only [BirdGraph, compl_adj, comap_adj, Function.Embedding.coeFn_mk]
  fin_cases p <;> fin_cases q <;>
    simp [f, hab, hab.symm, hac, hca, hbc, hcb,
      hua, hua.symm, hub, hbu, huc, hcu,
      hxa, hxa.symm, hxb, hxb.symm, hxc, hxc.symm, hya, hya.symm, hyb, hyb.symm, hyc, hyc.symm,
      hxu, hxu.symm, hnxy, hnyx, hnyu, hnuy]

/--
**Rule (ii) (`bird_comb_rule2`, Proposition 6(1a) of `main.tex`)**:
In a `BirdGraphᶜ`-free graph $G$ with an apex-cutter triple $(x, y, u)$ over $S_0$,
$G[S_0]$ contains no induced $P_3 \sqcup P_1 = (a - b - c) \sqcup \{d\}$ with
$\neg G.\text{Adj } u a$ and $G.\text{Adj } u b, G.\text{Adj } u c, G.\text{Adj } u d$.
-/
theorem bird_comb_rule2 {V : Type*} {G : SimpleGraph V} {S₀ : Finset V} {x y u : V}
    (hG : IsInducedSubgraphFree G BirdGraphᶜ)
    (htriple : IsApexCutterTriple G S₀ x y u)
    {a b c d : V} (ha : a ∈ S₀) (hb : b ∈ S₀) (hc : c ∈ S₀) (hd : d ∈ S₀)
    (hac_ne : a ≠ c) (had_ne : a ≠ d) (hbd_ne : b ≠ d) (hcd_ne : c ≠ d)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hac : ¬G.Adj a c)
    (had : ¬G.Adj a d) (hbd : ¬G.Adj b d) (hcd : ¬G.Adj c d)
    (hua : ¬G.Adj u a) (hub : G.Adj u b) (huc : G.Adj u c) (hud : G.Adj u d) :
    False := by
  let f : Fin 6 → V := ![a, d, c, u, y, b]
  have hab_ne : a ≠ b := G.ne_of_adj hab
  have hbc_ne : b ≠ c := G.ne_of_adj hbc
  have hu_ne_a : u ≠ a := fun h => htriple.u_not_mem (h ▸ ha)
  have hu_ne_b : u ≠ b := fun h => htriple.u_not_mem (h ▸ hb)
  have hu_ne_c : u ≠ c := fun h => htriple.u_not_mem (h ▸ hc)
  have hu_ne_d : u ≠ d := fun h => htriple.u_not_mem (h ▸ hd)
  have hu_ne_y : u ≠ y := fun h => htriple.not_adj_xy (h ▸ htriple.adj_xu)
  have hy_ne_a : y ≠ a := fun h => htriple.y_not_mem (h ▸ ha)
  have hy_ne_b : y ≠ b := fun h => htriple.y_not_mem (h ▸ hb)
  have hy_ne_c : y ≠ c := fun h => htriple.y_not_mem (h ▸ hc)
  have hy_ne_d : y ≠ d := fun h => htriple.y_not_mem (h ▸ hd)
  have hya : G.Adj y a := htriple.y_complete a ha
  have hyb : G.Adj y b := htriple.y_complete b hb
  have hyc : G.Adj y c := htriple.y_complete c hc
  have hyd : G.Adj y d := htriple.y_complete d hd
  have hnyu : ¬G.Adj y u := htriple.not_adj_yu
  have hnuy : ¬G.Adj u y := fun h => hnyu (G.symm h)
  have hca : ¬G.Adj c a := fun h => hac (G.symm h)
  have hda : ¬G.Adj d a := fun h => had (G.symm h)
  have hdb : ¬G.Adj d b := fun h => hbd (G.symm h)
  have hdc : ¬G.Adj d c := fun h => hcd (G.symm h)
  have hau : ¬G.Adj a u := fun h => hua (G.symm h)
  have hf_inj : Function.Injective f := by
    intro p q hpq
    fin_cases p <;> fin_cases q <;> dsimp [f] at hpq ⊢ <;>
      first | rfl
            | exact False.elim (had_ne hpq) | exact False.elim (had_ne hpq.symm)
            | exact False.elim (hac_ne hpq) | exact False.elim (hac_ne hpq.symm)
            | exact False.elim (hu_ne_a hpq) | exact False.elim (hu_ne_a hpq.symm)
            | exact False.elim (hy_ne_a hpq) | exact False.elim (hy_ne_a hpq.symm)
            | exact False.elim (hab_ne hpq) | exact False.elim (hab_ne hpq.symm)
            | exact False.elim (hcd_ne hpq) | exact False.elim (hcd_ne hpq.symm)
            | exact False.elim (hu_ne_d hpq) | exact False.elim (hu_ne_d hpq.symm)
            | exact False.elim (hy_ne_d hpq) | exact False.elim (hy_ne_d hpq.symm)
            | exact False.elim (hbd_ne hpq) | exact False.elim (hbd_ne hpq.symm)
            | exact False.elim (hu_ne_c hpq) | exact False.elim (hu_ne_c hpq.symm)
            | exact False.elim (hy_ne_c hpq) | exact False.elim (hy_ne_c hpq.symm)
            | exact False.elim (hbc_ne hpq) | exact False.elim (hbc_ne hpq.symm)
            | exact False.elim (hu_ne_y hpq) | exact False.elim (hu_ne_y hpq.symm)
            | exact False.elim (hu_ne_b hpq) | exact False.elim (hu_ne_b hpq.symm)
            | exact False.elim (hy_ne_b hpq) | exact False.elim (hy_ne_b hpq.symm)
  refine hG ⟨⟨f, hf_inj⟩, ?_⟩
  ext p q
  simp only [BirdGraph, compl_adj, comap_adj, Function.Embedding.coeFn_mk]
  fin_cases p <;> fin_cases q <;>
    simp [f, hab, hab.symm, hbc, hbc.symm, hac, hca,
      had, hda, hbd, hdb, hcd, hdc,
      hua, hau, hub, hub.symm, huc, huc.symm, hud, hud.symm,
      hya, hya.symm, hyb, hyb.symm, hyc, hyc.symm, hyd, hyd.symm, hnyu, hnuy]

/-- Quantifier-free boolean Rule (i) and Rule (ii) check on `EGraph` (`0 - 1 - 2 - 3 - 4` and `2 - 5`). -/
def eGraphRulesBool (b0 b1 b2 b3 b4 b5 : Bool) : Bool :=
  let r1 (bp bq br : Bool) : Bool := !(bp && !bq && !br)
  let r2 (bp bq br bs : Bool) : Bool := !(!bp && bq && br && bs)
  r1 b5 b2 b0 && r1 b2 b5 b0 && r1 b5 b2 b4 && r1 b2 b5 b4 &&
  r1 b0 b1 b3 && r1 b1 b0 b3 && r1 b0 b1 b4 && r1 b1 b0 b4 && r1 b0 b1 b5 && r1 b1 b0 b5 &&
  r1 b3 b4 b0 && r1 b4 b3 b0 && r1 b3 b4 b1 && r1 b4 b3 b1 && r1 b3 b4 b5 && r1 b4 b3 b5 &&
  r1 b1 b2 b4 && r1 b2 b1 b4 && r1 b3 b2 b0 && r1 b2 b3 b0 &&
  r2 b5 b2 b3 b0 && r2 b2 b3 b4 b0 && r2 b1 b2 b5 b4 && r2 b0 b1 b2 b4 &&
  r2 b2 b1 b0 b4 && r2 b3 b2 b5 b0 && r2 b4 b3 b2 b0 && r2 b5 b2 b1 b4

/--
**64-State Boolean Purity Lemma on `EGraph` (`eGraph_64_state_purity_bool`, lines 993–999 of `main.tex`)**:
Any boolean assignment on `Fin 6` satisfying Rules (i) and (ii) on `EGraph` is either all `true` or all `false`.
-/
theorem eGraph_64_state_purity_bool (b0 b1 b2 b3 b4 b5 : Bool) :
    eGraphRulesBool b0 b1 b2 b3 b4 b5 = true →
    (b0 = true ∧ b1 = true ∧ b2 = true ∧ b3 = true ∧ b4 = true ∧ b5 = true) ∨
    (b0 = false ∧ b1 = false ∧ b2 = false ∧ b3 = false ∧ b4 = false ∧ b5 = false) := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> decide

/--
**64-State `EGraph` Purity Lemma (`bird_egraph_pure`, lines 993–999 of `main.tex`)**:
In any `BirdGraphᶜ`-free graph $G$, for any apex-cutter triple $(x, y, u)$ over $S_0$ and any
induced copy $g : \text{Fin } 6 \hookrightarrow V$ of `EGraph` in $S_0$, $u$ is pure to $g(\text{Fin } 6)$ in $G$.
-/
theorem bird_egraph_pure {V : Type*} [DecidableEq V] {G : SimpleGraph V} {S₀ : Finset V} {x y u : V}
    (hG : IsInducedSubgraphFree G BirdGraphᶜ)
    (htriple : IsApexCutterTriple G S₀ x y u)
    (g : Fin 6 ↪ V) (hg_sub : ∀ p : Fin 6, g p ∈ S₀) (hg_adj : EGraph = G.comap g) :
    IsVertexPureTo G u (Finset.univ.image g) := by
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  let b : Fin 6 → Bool := fun p => decide (G.Adj u (g p))
  have h_adj_iff : ∀ p q : Fin 6, EGraph.Adj p q ↔ G.Adj (g p) (g q) := by
    intro p q
    exact (congr_arg (fun H => H.Adj p q) hg_adj).to_iff
  have hr1 : ∀ p q r : Fin 6,
      (EGraph.Adj p q ∧ ¬EGraph.Adj p r ∧ ¬EGraph.Adj q r ∧ p ≠ r ∧ q ≠ r) →
      (!(b p && !b q && !b r)) = true := by
    intro p q r ⟨hpq, hpr, hqr, hpr_ne, hqr_ne⟩
    cases hbp : b p <;> cases hbq : b q <;> cases hbr : b r <;> try rfl
    exfalso
    exact bird_comb_rule1 hG htriple (hg_sub p) (hg_sub q) (hg_sub r)
      (g.injective.ne hpr_ne) (g.injective.ne hqr_ne)
      ((h_adj_iff p q).mp hpq)
      (fun h => hpr ((h_adj_iff p r).mpr h))
      (fun h => hqr ((h_adj_iff q r).mpr h))
      (of_decide_eq_true hbp) (of_decide_eq_false hbq) (of_decide_eq_false hbr)
  have hr2 : ∀ p q r s : Fin 6,
      (EGraph.Adj p q ∧ EGraph.Adj q r ∧ ¬EGraph.Adj p r ∧ p ≠ r ∧
       ¬EGraph.Adj p s ∧ ¬EGraph.Adj q s ∧ ¬EGraph.Adj r s ∧ p ≠ s ∧ q ≠ s ∧ r ≠ s) →
      (!(!b p && b q && b r && b s)) = true := by
    intro p q r s ⟨hpq, hqr, hpr, hpr_ne, hps, hqs, hrs, hps_ne, hqs_ne, hrs_ne⟩
    cases hbp : b p <;> cases hbq : b q <;> cases hbr : b r <;> cases hbs : b s <;> try rfl
    exfalso
    exact bird_comb_rule2 hG htriple (hg_sub p) (hg_sub q) (hg_sub r) (hg_sub s)
      (g.injective.ne hpr_ne) (g.injective.ne hps_ne) (g.injective.ne hqs_ne) (g.injective.ne hrs_ne)
      ((h_adj_iff p q).mp hpq) ((h_adj_iff q r).mp hqr)
      (fun h => hpr ((h_adj_iff p r).mpr h))
      (fun h => hps ((h_adj_iff p s).mpr h))
      (fun h => hqs ((h_adj_iff q s).mpr h))
      (fun h => hrs ((h_adj_iff r s).mpr h))
      (of_decide_eq_false hbp) (of_decide_eq_true hbq) (of_decide_eq_true hbr) (of_decide_eq_true hbs)
  have h_all : eGraphRulesBool (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) = true := by
    unfold eGraphRulesBool
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨
      hr1 5 2 0 (by decide), hr1 2 5 0 (by decide)⟩, hr1 5 2 4 (by decide)⟩, hr1 2 5 4 (by decide)⟩,
      hr1 0 1 3 (by decide)⟩, hr1 1 0 3 (by decide)⟩, hr1 0 1 4 (by decide)⟩, hr1 1 0 4 (by decide)⟩,
      hr1 0 1 5 (by decide)⟩, hr1 1 0 5 (by decide)⟩, hr1 3 4 0 (by decide)⟩, hr1 4 3 0 (by decide)⟩,
      hr1 3 4 1 (by decide)⟩, hr1 4 3 1 (by decide)⟩, hr1 3 4 5 (by decide)⟩, hr1 4 3 5 (by decide)⟩,
      hr1 1 2 4 (by decide)⟩, hr1 2 1 4 (by decide)⟩, hr1 3 2 0 (by decide)⟩, hr1 2 3 0 (by decide)⟩,
      hr2 5 2 3 0 (by decide)⟩, hr2 2 3 4 0 (by decide)⟩, hr2 1 2 5 4 (by decide)⟩, hr2 0 1 2 4 (by decide)⟩,
      hr2 2 1 0 4 (by decide)⟩, hr2 3 2 5 0 (by decide)⟩, hr2 4 3 2 0 (by decide)⟩, hr2 5 2 1 4 (by decide)⟩
  rcases eGraph_64_state_purity_bool (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) h_all with
    ⟨h0, h1, h2, h3, h4, h5⟩ | ⟨h0, h1, h2, h3, h4, h5⟩
  · left
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨p, _, rfl⟩
    fin_cases p
    · exact of_decide_eq_true h0
    · exact of_decide_eq_true h1
    · exact of_decide_eq_true h2
    · exact of_decide_eq_true h3
    · exact of_decide_eq_true h4
    · exact of_decide_eq_true h5
  · right
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨p, _, rfl⟩
    fin_cases p
    · exact of_decide_eq_false h0
    · exact of_decide_eq_false h1
    · exact of_decide_eq_false h2
    · exact of_decide_eq_false h3
    · exact of_decide_eq_false h4
    · exact of_decide_eq_false h5

/-- A subset $D \subseteq V$ is an apex-cutter pure block in $G$ (`IsApexCutterPureBlock G D`)
if every apex-cutter triple $(x, y, u)$ over $D$ has $u$ pure to $D$ in $G$. -/
def IsApexCutterPureBlock {V : Type*} (G : SimpleGraph V) (D : Finset V) : Prop :=
  ∀ x y u : V, IsApexCutterTriple G D x y u → IsVertexPureTo G u D

/-- `EGraphᶜ` is connected. -/
theorem eGraphCompl_connected : EGraphᶜ.Connected := by
  refine (connected_iff_exists_forall_reachable EGraphᶜ).mpr ⟨0, fun u => ?_⟩
  fin_cases u
  · exact Reachable.refl 0
  · exact (show EGraphᶜ.Adj 0 4 by decide).reachable.trans (show EGraphᶜ.Adj 4 1 by decide).reachable
  · exact (show EGraphᶜ.Adj 0 2 by decide).reachable
  · exact (show EGraphᶜ.Adj 0 3 by decide).reachable
  · exact (show EGraphᶜ.Adj 0 4 by decide).reachable
  · exact (show EGraphᶜ.Adj 0 5 by decide).reachable

/-- Every induced copy of `EGraph` in $G$ is anticonnected (`IsAnticonnected G (Finset.univ.image g)`). -/
theorem isAnticonnected_eGraph_image {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (g : Fin 6 ↪ V) (hg_adj : EGraph = G.comap g) :
    IsAnticonnected G (Finset.univ.image g) := by
  let D := Finset.univ.image g
  let φ : EGraphᶜ ≃g Gᶜ.induce (D : Set V) :=
    { toFun := fun p => ⟨g p, Finset.mem_image_of_mem g (Finset.mem_univ p)⟩
      invFun := fun z => Classical.choose (Finset.mem_image.mp (Finset.mem_coe.mp z.2))
      left_inv := fun p =>
        g.injective (Classical.choose_spec (Finset.mem_image.mp (Finset.mem_image_of_mem g (Finset.mem_univ p)))).2
      right_inv := fun z => by
        ext
        exact (Classical.choose_spec (Finset.mem_image.mp (Finset.mem_coe.mp z.2))).2
      map_rel_iff' := by
        intro p q
        simp only [Equiv.coe_fn_mk, induce_adj, compl_adj, ne_eq, Subtype.ext_iff, g.injective.eq_iff]
        exact and_congr_right (fun _ => not_congr (congr_arg (fun H => H.Adj p q) hg_adj).to_iff.symm) }
  exact φ.connected_iff.mp eGraphCompl_connected

/-- If $D_1, D_2$ are anticonnected in $G$ and share a vertex or a $Gᶜ$-edge, then $D_1 \cup D_2$ is anticonnected in $G$. -/
theorem isAnticonnected_union_of_compl_edge_or_inter {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {D₁ D₂ : Finset V}
    (hD₁ : IsAnticonnected G D₁) (hD₂ : IsAnticonnected G D₂)
    (h_link : (D₁ ∩ D₂).Nonempty ∨ ∃ d₁ ∈ D₁, ∃ d₂ ∈ D₂, Gᶜ.Adj d₁ d₂) :
    IsAnticonnected G (D₁ ∪ D₂) := by
  obtain ⟨z₀, hz₀⟩ := hD₁.nonempty
  refine (connected_iff_exists_forall_reachable (Gᶜ.induce ((D₁ ∪ D₂ : Finset V) : Set V))).mpr
    ⟨⟨z₀, Finset.mem_union_left D₂ hz₀⟩, fun ⟨w, hw⟩ => ?_⟩
  let emb₁ : Gᶜ.induce (D₁ : Set V) →g Gᶜ.induce ((D₁ ∪ D₂ : Finset V) : Set V) :=
    { toFun := fun u => ⟨u.1, Finset.mem_union_left D₂ u.2⟩
      map_rel' := fun h => h }
  let emb₂ : Gᶜ.induce (D₂ : Set V) →g Gᶜ.induce ((D₁ ∪ D₂ : Finset V) : Set V) :=
    { toFun := fun u => ⟨u.1, Finset.mem_union_right D₁ u.2⟩
      map_rel' := fun h => h }
  have h_reach₁ : ∀ u : (D₁ : Set V),
      (Gᶜ.induce ((D₁ ∪ D₂ : Finset V) : Set V)).Reachable ⟨z₀, Finset.mem_union_left D₂ hz₀⟩ (emb₁ u) :=
    fun u => (hD₁.preconnected ⟨z₀, hz₀⟩ u).map emb₁
  rcases Finset.mem_union.mp hw with hw₁ | hw₂
  · exact h_reach₁ ⟨w, hw₁⟩
  · rcases h_link with ⟨x₀, hx₀⟩ | ⟨d₁, hd₁, d₂, hd₂, hcadj⟩
    · obtain ⟨hx₀₁, hx₀₂⟩ := Finset.mem_inter.mp hx₀
      have hr₁ := h_reach₁ ⟨x₀, hx₀₁⟩
      have hr₂ := (hD₂.preconnected ⟨x₀, hx₀₂⟩ ⟨w, hw₂⟩).map emb₂
      exact hr₁.trans hr₂
    · have hr₁ := h_reach₁ ⟨d₁, hd₁⟩
      have h_step : (Gᶜ.induce ((D₁ ∪ D₂ : Finset V) : Set V)).Adj
          ⟨d₁, Finset.mem_union_left D₂ hd₁⟩ ⟨d₂, Finset.mem_union_right D₁ hd₂⟩ := hcadj
      have hr₂ := (hD₂.preconnected ⟨d₂, hd₂⟩ ⟨w, hw₂⟩).map emb₂
      exact hr₁.trans (h_step.reachable.trans hr₂)

/-- Merging overlapping apex-cutter pure blocks preserves `IsApexCutterPureBlock`. -/
theorem isApexCutterPureBlock_union_of_inter_nonempty {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {D₁ D₂ : Finset V}
    (h₁ : IsApexCutterPureBlock G D₁) (h₂ : IsApexCutterPureBlock G D₂)
    (h_inter : (D₁ ∩ D₂).Nonempty) :
    IsApexCutterPureBlock G (D₁ ∪ D₂) := by
  intro x y u htriple
  obtain ⟨z₀, hz₀⟩ := h_inter
  obtain ⟨hz₀₁, hz₀₂⟩ := Finset.mem_inter.mp hz₀
  have hp₁ := h₁ x y u (htriple.mono Finset.subset_union_left)
  have hp₂ := h₂ x y u (htriple.mono Finset.subset_union_right)
  rcases hp₁ with hc₁ | ha₁ <;> rcases hp₂ with hc₂ | ha₂
  · left; intro z hz; rcases Finset.mem_union.mp hz with h | h; exact hc₁ z h; exact hc₂ z h
  · exact False.elim (ha₂ z₀ hz₀₂ (hc₁ z₀ hz₀₁))
  · exact False.elim (ha₁ z₀ hz₀₁ (hc₂ z₀ hz₀₂))
  · right; intro z hz; rcases Finset.mem_union.mp hz with h | h; exact ha₁ z h; exact ha₂ z h

/--
**Mixed-Equivalence Quotient Descent Step (`isApexCutterPureBlock_union_of_mixed`, line 1001 of `main.tex`)**:
In a `BirdGraphᶜ`-free graph $G$, if $D_1, D_2$ are disjoint nonempty anticonnected blocks satisfying
`IsApexCutterPureBlock`, and $(D_1, D_2)$ is mixed (`¬IsPurePair G D₁ D₂`), then $D_1 \cup D_2$ is
anticonnected and satisfies `IsApexCutterPureBlock G (D₁ ∪ D₂)`.
-/
theorem isApexCutterPureBlock_union_of_mixed {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {D₁ D₂ : Finset V}
    (hG : IsInducedSubgraphFree G BirdGraphᶜ)
    (hdisj : Disjoint D₁ D₂)
    (hD₁_aconn : IsAnticonnected G D₁) (hD₂_aconn : IsAnticonnected G D₂)
    (h₁ : IsApexCutterPureBlock G D₁) (h₂ : IsApexCutterPureBlock G D₂)
    (hmix : ¬IsPurePair G D₁ D₂) :
    IsAnticonnected G (D₁ ∪ D₂) ∧ IsApexCutterPureBlock G (D₁ ∪ D₂) := by
  have h_not_comp : ¬IsCompletePair G D₁ D₂ := fun h => hmix (Or.inl h)
  unfold IsCompletePair at h_not_comp
  push_neg at h_not_comp
  obtain ⟨d₁₀, hd₁₀, d₂₀, hd₂₀, hnadj₀⟩ := h_not_comp
  have hne₀ : d₁₀ ≠ d₂₀ := fun h => Finset.disjoint_left.mp hdisj hd₁₀ (h ▸ hd₂₀)
  have h_aconn_union : IsAnticonnected G (D₁ ∪ D₂) :=
    isAnticonnected_union_of_compl_edge_or_inter hD₁_aconn hD₂_aconn
      (Or.inr ⟨d₁₀, hd₁₀, d₂₀, hd₂₀, ⟨hne₀, hnadj₀⟩⟩)
  refine ⟨h_aconn_union, ?_⟩
  -- Core asymmetric contradiction lemma: u cannot be complete to A and anticomplete to B
  have h_no_split : ∀ (A B : Finset V),
      Disjoint A B → A ∪ B = D₁ ∪ D₂ →
      IsAnticonnected G B → IsApexCutterPureBlock G A → ¬IsPurePair G A B →
      ∀ x y u : V, IsApexCutterTriple G (D₁ ∪ D₂) x y u →
      (∀ a ∈ A, G.Adj u a) → (∀ b ∈ B, ¬G.Adj u b) → False := by
    intro A B hAB_disj hAB_eq hB_aconn hA_pure hAB_mix x y u htriple huA huB
    have hAB_sub : A ⊆ D₁ ∪ D₂ := hAB_eq ▸ Finset.subset_union_left
    have hBA_sub : B ⊆ D₁ ∪ D₂ := hAB_eq ▸ Finset.subset_union_right
    by_cases h_ex_mix : ∃ a₀ ∈ A, IsVertexMixedOn G a₀ B
    · obtain ⟨a₀, ha₀A, ha₀_mix⟩ := h_ex_mix
      obtain ⟨b₂, hb₂B, b₁, hb₁B, hb₁₂_ne, hb₁₂_nadj, ha₀b₂_nadj, ha₀b₁_adj⟩ :=
        ha₀_mix.exists_anticonnected_edge hB_aconn
      have ha₀b₂_ne : a₀ ≠ b₂ := fun h => Finset.disjoint_left.mp hAB_disj ha₀A (h ▸ hb₂B)
      exact bird_comb_rule1 hG htriple (hAB_sub ha₀A) (hBA_sub hb₁B) (hBA_sub hb₂B)
        ha₀b₂_ne hb₁₂_ne.symm ha₀b₁_adj ha₀b₂_nadj (fun h => hb₁₂_nadj (G.symm h))
        (huA a₀ ha₀A) (huB b₁ hb₁B) (huB b₂ hb₂B)
    · push_neg at h_ex_mix
      have h_all_pure : ∀ a ∈ A, IsVertexPureTo G a B := by
        intro a ha
        by_contra hnp
        exact h_ex_mix a ha ((not_isVertexPureTo_iff_isVertexMixedOn G a B).mp hnp)
      have h_not_c : ¬IsCompletePair G A B := fun h => hAB_mix (Or.inl h)
      have h_not_a : ¬IsAnticompletePair G A B := fun h => hAB_mix (Or.inr h)
      unfold IsCompletePair at h_not_c
      unfold IsAnticompletePair at h_not_a
      push_neg at h_not_c h_not_a
      obtain ⟨a_anti, ha_anti, b_w₁, hb_w₁, h_nadj₁⟩ := h_not_c
      obtain ⟨a_comp, ha_comp, b_w₂, hb_w₂, h_adj₂⟩ := h_not_a
      have ha_anti_all : ∀ b ∈ B, ¬G.Adj a_anti b := by
        rcases h_all_pure a_anti ha_anti with hc | ha
        · exact False.elim (h_nadj₁ (hc b_w₁ hb_w₁))
        · exact ha
      have ha_comp_all : ∀ b ∈ B, G.Adj a_comp b := by
        rcases h_all_pure a_comp ha_comp with hc | ha
        · exact hc
        · exact False.elim (ha b_w₂ hb_w₂ h_adj₂)
      obtain ⟨u', hu'B⟩ := hB_aconn.nonempty
      have hy_ne_u : y ≠ u := fun h => huB u' hu'B (h ▸ htriple.y_complete u' (hBA_sub hu'B))
      have htriple' : IsApexCutterTriple G A y u u' :=
        { x_not_mem := fun hyA => htriple.y_not_mem (hAB_sub hyA)
          y_not_mem := fun huA' => htriple.u_not_mem (hAB_sub huA')
          u_not_mem := fun hu'A => Finset.disjoint_left.mp hAB_disj hu'A hu'B
          x_ne_y := hy_ne_u
          not_adj_xy := htriple.not_adj_yu
          x_complete := fun z hz => htriple.y_complete z (hAB_sub hz)
          y_complete := huA
          adj_xu := htriple.y_complete u' (hBA_sub hu'B)
          not_adj_yu := huB u' hu'B }
      rcases hA_pure y u u' htriple' with hc' | ha'
      · exact ha_anti_all u' hu'B (G.symm (hc' a_anti ha_anti))
      · exact ha' a_comp ha_comp (G.symm (ha_comp_all u' hu'B))
  intro x y u htriple
  have hp₁ := h₁ x y u (htriple.mono Finset.subset_union_left)
  have hp₂ := h₂ x y u (htriple.mono Finset.subset_union_right)
  rcases hp₁ with hc₁ | ha₁ <;> rcases hp₂ with hc₂ | ha₂
  · left; intro z hz; rcases Finset.mem_union.mp hz with h | h; exact hc₁ z h; exact hc₂ z h
  · exact False.elim (h_no_split D₁ D₂ hdisj rfl hD₂_aconn h₁ hmix x y u htriple hc₁ ha₂)
  · have hmix_symm : ¬IsPurePair G D₂ D₁ := fun h => hmix (isPurePair_symm h)
    exact False.elim (h_no_split D₂ D₁ hdisj.symm (Finset.union_comm D₂ D₁) hD₁_aconn h₂ hmix_symm x y u htriple hc₂ ha₁)
  · right; intro z hz; rcases Finset.mem_union.mp hz with h | h; exact ha₁ z h; exact ha₂ z h

/-- Union $X_i \subseteq B_i$ of all induced copies of `EGraph` inside $G[B_i]$. -/
noncomputable def eGraphUnionIn {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (B_i : Finset V) : Finset V :=
  by classical exact
    (Finset.univ.filter (fun g : Fin 6 ↪ V =>
      (∀ p : Fin 6, g p ∈ B_i) ∧ EGraph = G.comap g)).biUnion (fun g => Finset.univ.image g)

/-- The complement $Y_i = B_i \setminus X_i$ is induced-`EGraph`-free. -/
theorem isInducedSubgraphFree_eGraph_sdiff_eGraphUnionIn {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (B_i : Finset V) :
    IsInducedSubgraphFree (G.induce ((B_i \ eGraphUnionIn G B_i : Finset V) : Set V)) EGraph := by
  rintro ⟨g_ind, hg_ind⟩
  let g : Fin 6 ↪ V := g_ind.trans (Function.Embedding.subtype _)
  have hg_mem_Y : ∀ p : Fin 6, g p ∈ B_i \ eGraphUnionIn G B_i := fun p => (g_ind p).2
  have hg_B : ∀ p : Fin 6, g p ∈ B_i := fun p => (Finset.mem_sdiff.mp (hg_mem_Y p)).1
  have hg_adj : EGraph = G.comap g := by
    ext p q
    exact (congr_arg (fun H => H.Adj p q) hg_ind).to_iff
  have hg_0_in_X : g 0 ∈ eGraphUnionIn G B_i := by
    classical
    unfold eGraphUnionIn
    rw [Finset.mem_biUnion]
    refine ⟨g, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg_B, hg_adj⟩,
      Finset.mem_image_of_mem g (Finset.mem_univ 0)⟩
  exact (Finset.mem_sdiff.mp (hg_mem_Y 0)).2 hg_0_in_X

/-- Iterative merging of overlapping or mixed blocks into a pairwise-pure anticonnected blockade. -/
theorem merge_blocks_to_pure_partition_aux {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : IsInducedSubgraphFree G BirdGraphᶜ) (X : Finset V) :
    ∀ (n : ℕ) (L : Finset (Finset V)),
      L.card ≤ n →
      L.biUnion id = X →
      (∀ D ∈ L, D.Nonempty ∧ IsAnticonnected G D ∧ IsApexCutterPureBlock G D) →
      ∃ L_q : Finset (Finset V),
        L_q.biUnion id = X ∧
        (∀ D ∈ L_q, D.Nonempty ∧ IsAnticonnected G D ∧ IsApexCutterPureBlock G D) ∧
        (∀ D₁ ∈ L_q, ∀ D₂ ∈ L_q, D₁ ≠ D₂ → Disjoint D₁ D₂ ∧ IsPurePair G D₁ D₂) ∧
        (∀ D ∈ L, ∃ A ∈ L_q, D ⊆ A) := by
  classical
  intro n
  induction n with
  | zero =>
    intro L hcard h_biUnion h_props
    have hL_emp : L = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    refine ⟨L, h_biUnion, h_props, ?_, fun D hD => ⟨D, hD, Finset.Subset.rfl⟩⟩
    intro D₁ hD₁
    rw [hL_emp] at hD₁
    exact False.elim (Finset.notMem_empty D₁ hD₁)
  | succ m ih =>
    intro L hcard h_biUnion h_props
    by_cases h_done : ∀ D₁ ∈ L, ∀ D₂ ∈ L, D₁ ≠ D₂ → Disjoint D₁ D₂ ∧ IsPurePair G D₁ D₂
    · exact ⟨L, h_biUnion, h_props, h_done, fun D hD => ⟨D, hD, Finset.Subset.rfl⟩⟩
    · push_neg at h_done
      obtain ⟨D₁, hD₁L, D₂, hD₂L, hD₁₂_ne, h_not_both⟩ := h_done
      let L' := insert (D₁ ∪ D₂) ((L.erase D₁).erase D₂)
      have hD₂_er₁ : D₂ ∈ L.erase D₁ := Finset.mem_erase.mpr ⟨hD₁₂_ne.symm, hD₂L⟩
      have h_card_er : ((L.erase D₁).erase D₂).card + 2 = L.card := by
        rw [Finset.card_erase_of_mem hD₂_er₁, Finset.card_erase_of_mem hD₁L]
        have : 2 ≤ L.card := Finset.one_lt_card.mpr ⟨D₁, hD₁L, D₂, hD₂L, hD₁₂_ne⟩
        omega
      have hL'_card : L'.card ≤ m := by
        dsimp only [L']
        have h1 := Finset.card_insert_le (D₁ ∪ D₂) ((L.erase D₁).erase D₂)
        omega
      have hL'_biUnion : L'.biUnion id = X := by
        rw [← h_biUnion]
        ext z
        simp only [L', Finset.mem_biUnion, id_eq, Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro ⟨A, rfl | ⟨_, _, hAL⟩, hzA⟩
          · rcases Finset.mem_union.mp hzA with hz₁ | hz₂
            · exact ⟨D₁, hD₁L, hz₁⟩
            · exact ⟨D₂, hD₂L, hz₂⟩
          · exact ⟨A, hAL, hzA⟩
        · rintro ⟨A, hAL, hzA⟩
          by_cases hAD₁ : A = D₁
          · exact ⟨D₁ ∪ D₂, Or.inl rfl, Finset.mem_union_left D₂ (hAD₁ ▸ hzA)⟩
          · by_cases hAD₂ : A = D₂
            · exact ⟨D₁ ∪ D₂, Or.inl rfl, Finset.mem_union_right D₁ (hAD₂ ▸ hzA)⟩
            · exact ⟨A, Or.inr ⟨hAD₂, hAD₁, hAL⟩, hzA⟩
      have h_union_prop : (D₁ ∪ D₂).Nonempty ∧ IsAnticonnected G (D₁ ∪ D₂) ∧ IsApexCutterPureBlock G (D₁ ∪ D₂) := by
        obtain ⟨hD₁_ne, hD₁_ac, hD₁_p⟩ := h_props D₁ hD₁L
        obtain ⟨hD₂_ne, hD₂_ac, hD₂_p⟩ := h_props D₂ hD₂L
        have h_ne : (D₁ ∪ D₂).Nonempty := hD₁_ne.mono Finset.subset_union_left
        by_cases hdisj : Disjoint D₁ D₂
        · have hmix : ¬IsPurePair G D₁ D₂ := h_not_both hdisj
          obtain ⟨hac, hp⟩ := isApexCutterPureBlock_union_of_mixed hG hdisj hD₁_ac hD₂_ac hD₁_p hD₂_p hmix
          exact ⟨h_ne, hac, hp⟩
        · rw [Finset.not_disjoint_iff_nonempty_inter] at hdisj
          exact ⟨h_ne, isAnticonnected_union_of_compl_edge_or_inter hD₁_ac hD₂_ac (Or.inl hdisj),
            isApexCutterPureBlock_union_of_inter_nonempty hD₁_p hD₂_p hdisj⟩
      have hL'_props : ∀ D ∈ L', D.Nonempty ∧ IsAnticonnected G D ∧ IsApexCutterPureBlock G D := by
        intro D hD
        rcases Finset.mem_insert.mp hD with rfl | hD_er
        · exact h_union_prop
        · exact h_props D (Finset.erase_subset D₁ L (Finset.erase_subset D₂ _ hD_er))
      obtain ⟨L_q, hLq_bi, hLq_pr, hLq_pure, hLq_cov⟩ := ih L' hL'_card hL'_biUnion hL'_props
      refine ⟨L_q, hLq_bi, hLq_pr, hLq_pure, fun D hD => ?_⟩
      by_cases hDD₁ : D = D₁
      · obtain ⟨A, hA, hsub⟩ := hLq_cov (D₁ ∪ D₂) (Finset.mem_insert_self _ _)
        exact ⟨A, hA, hDD₁ ▸ Finset.subset_union_left.trans hsub⟩
      · by_cases hDD₂ : D = D₂
        · obtain ⟨A, hA, hsub⟩ := hLq_cov (D₁ ∪ D₂) (Finset.mem_insert_self _ _)
          exact ⟨A, hA, hDD₂ ▸ Finset.subset_union_right.trans hsub⟩
        · exact hLq_cov D (Finset.mem_insert_of_mem
            (Finset.mem_erase.mpr ⟨hDD₂, Finset.mem_erase.mpr ⟨hDD₁, hD⟩⟩))

/--
**Proposition 6(1a) — Mixed-Equivalence Quotient Descent $\mathcal{L}^q \to \mathcal{L}^1$ (`bird_quotient_descent`, line 1001 of `main.tex`)**:
In any `BirdGraphᶜ`-free graph $G$ and any subset $B_i \subseteq V$, $X_i := \text{eGraphUnionIn } G B_i$
partitions into a sorted pairwise-pure anticonnected blockade $\mathcal{L}^q = (A_1, \dots, A_t)$
($|A_1| \ge \dots \ge |A_t|$) such that every block satisfies `IsApexCutterPureBlock G (A j)`
and the pattern graph `purePatternGraph G A` on $\text{Fin } t$ is `{EGraph, BirdGraphᶜ}`-free.
-/
theorem bird_quotient_descent {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : IsInducedSubgraphFree G BirdGraphᶜ) (B_i : Finset V) :
    let X_i := eGraphUnionIn G B_i
    ∃ (t : ℕ) (A : Fin t → Finset V),
      Finset.univ.biUnion A = X_i ∧
      (∀ j : Fin t, A j ⊆ X_i ∧ (A j).Nonempty ∧ IsAnticonnected G (A j) ∧ IsApexCutterPureBlock G (A j)) ∧
      (∀ j₁ j₂ : Fin t, j₁ ≠ j₂ → Disjoint (A j₁) (A j₂) ∧ IsPurePair G (A j₁) (A j₂)) ∧
      (∀ j₁ j₂ : Fin t, j₁ ≤ j₂ → (A j₂).card ≤ (A j₁).card) ∧
      IsInducedSubgraphFree (purePatternGraph G A) EGraph ∧
      IsInducedSubgraphFree (purePatternGraph G A) BirdGraphᶜ := by
  classical
  intro X_i
  let copies : Finset (Fin 6 ↪ V) :=
    Finset.univ.filter (fun g : Fin 6 ↪ V => (∀ p : Fin 6, g p ∈ B_i) ∧ EGraph = G.comap g)
  let L₁ : Finset (Finset V) := copies.image (fun g : Fin 6 ↪ V => Finset.univ.image ⇑g)
  have hL₁_biUnion : L₁.biUnion id = X_i := by
    ext z
    simp only [L₁, X_i, eGraphUnionIn, copies, Finset.mem_biUnion, id_eq]
    constructor
    · rintro ⟨D, hD, hz⟩
      rcases Finset.mem_image.mp hD with ⟨g, hg, rfl⟩
      exact ⟨g, hg, hz⟩
    · rintro ⟨g, hg, hz⟩
      exact ⟨Finset.univ.image ⇑g, Finset.mem_image.mpr ⟨g, hg, rfl⟩, hz⟩
  have hL₁_props : ∀ D ∈ L₁, D.Nonempty ∧ IsAnticonnected G D ∧ IsApexCutterPureBlock G D := by
    intro D hD
    rcases Finset.mem_image.mp hD with ⟨g, hg_mem, rfl⟩
    obtain ⟨_, hg_B, hg_adj⟩ := Finset.mem_filter.mp hg_mem
    refine ⟨⟨g 0, Finset.mem_image_of_mem g (Finset.mem_univ 0)⟩,
      isAnticonnected_eGraph_image g hg_adj, ?_⟩
    intro x y u htriple
    exact bird_egraph_pure hG htriple g
      (fun p => Finset.mem_image_of_mem g (Finset.mem_univ p)) hg_adj
  obtain ⟨L_q, hLq_bi, hLq_pr, hLq_pure, hLq_cov⟩ :=
    merge_blocks_to_pure_partition_aux hG X_i L₁.card L₁ le_rfl hL₁_biUnion hL₁_props
  obtain ⟨t, A, _, hA_inj, hA_img, hA_mem, hA_surj, hA_mono⟩ := exists_sorted_equiv_of_finset L_q
  have hA_biUnion : Finset.univ.biUnion A = X_i := by
    rw [← hLq_bi]
    ext z
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, id_eq]
    exact ⟨fun ⟨j, hz⟩ => ⟨A j, hA_mem j, hz⟩,
      fun ⟨D, hD, hz⟩ => let ⟨j, hj⟩ := hA_surj D hD; ⟨j, hj ▸ hz⟩⟩
  have hX_sub_B : X_i ⊆ B_i := by
    intro z hz
    unfold X_i eGraphUnionIn at hz
    rcases Finset.mem_biUnion.mp hz with ⟨g, hg_mem, hz_img⟩
    rcases Finset.mem_image.mp hz_img with ⟨p, _, rfl⟩
    exact (Finset.mem_filter.mp hg_mem).2.1 p
  have hA_props : ∀ j : Fin t, A j ⊆ X_i ∧ (A j).Nonempty ∧ IsAnticonnected G (A j) ∧ IsApexCutterPureBlock G (A j) := by
    intro j
    have hsub : A j ⊆ X_i := by
      rw [← hA_biUnion]
      intro z hz
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hz⟩
    exact ⟨hsub, hLq_pr (A j) (hA_mem j)⟩
  have hA_pair : ∀ j₁ j₂ : Fin t, j₁ ≠ j₂ → Disjoint (A j₁) (A j₂) ∧ IsPurePair G (A j₁) (A j₂) :=
    fun j₁ j₂ hj => hLq_pure (A j₁) (hA_mem j₁) (A j₂) (hA_mem j₂) (fun h => hj (hA_inj h))
  -- Pattern graph embedding into G via block representatives
  let rep : Fin t → V := fun j => Classical.choose (hA_props j).2.1
  have hrep_mem : ∀ j : Fin t, rep j ∈ A j := fun j => Classical.choose_spec (hA_props j).2.1
  have hrep_inj : Function.Injective rep := by
    intro j₁ j₂ h
    by_contra hne
    exact Finset.disjoint_left.mp (hA_pair j₁ j₂ hne).1 (hrep_mem j₁) (h ▸ hrep_mem j₂)
  let repEmb : Fin t ↪ V := ⟨rep, hrep_inj⟩
  have h_pat_eq : purePatternGraph G A = G.comap repEmb := by
    ext j₁ j₂
    simp only [purePatternGraph, comap_adj, repEmb, Function.Embedding.coeFn_mk]
    by_cases hj : j₁ = j₂
    · subst hj; simp
    · simp only [hj, ne_eq, not_false_eq_true, true_and]
      rcases (hA_pair j₁ j₂ hj).2 with hcomp | hanti
      · exact iff_of_true hcomp (hcomp (rep j₁) (hrep_mem j₁) (rep j₂) (hrep_mem j₂))
      · exact iff_of_false
          (fun hc => hanti (rep j₁) (hrep_mem j₁) (rep j₂) (hrep_mem j₂)
            (hc (rep j₁) (hrep_mem j₁) (rep j₂) (hrep_mem j₂)))
          (hanti (rep j₁) (hrep_mem j₁) (rep j₂) (hrep_mem j₂))
  have h_free_bird : IsInducedSubgraphFree (purePatternGraph G A) BirdGraphᶜ := by
    rintro ⟨f, hf⟩
    refine hG ⟨f.trans repEmb, ?_⟩
    ext p q
    exact ((congr_arg (fun H => H.Adj p q) hf).trans
      (congr_arg (fun H => H.Adj (f p) (f q)) h_pat_eq)).to_iff
  have h_free_egraph : IsInducedSubgraphFree (purePatternGraph G A) EGraph := by
    rintro ⟨f, hf⟩
    let g : Fin 6 ↪ V := f.trans repEmb
    have hg_B : ∀ p : Fin 6, g p ∈ B_i := fun p =>
      hX_sub_B ((hA_props (f p)).1 (hrep_mem (f p)))
    have hg_adj : EGraph = G.comap g := by
      ext p q
      exact ((congr_arg (fun H => H.Adj p q) hf).trans
        (congr_arg (fun H => H.Adj (f p) (f q)) h_pat_eq)).to_iff
    have h_in_L₁ : Finset.univ.image ⇑g ∈ L₁ := by
      unfold L₁ copies
      exact Finset.mem_image.mpr ⟨g, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg_B, hg_adj⟩, rfl⟩
    obtain ⟨A₀, hA₀_mem, h_sub_A₀⟩ := hLq_cov (Finset.univ.image ⇑g) h_in_L₁
    obtain ⟨j₀, rfl⟩ := hA_surj A₀ hA₀_mem
    have h0_mem : g 0 ∈ A j₀ := h_sub_A₀ (Finset.mem_image_of_mem g (Finset.mem_univ 0))
    have h1_mem : g 1 ∈ A j₀ := h_sub_A₀ (Finset.mem_image_of_mem g (Finset.mem_univ 1))
    have hf0 : f 0 = j₀ := by
      by_contra hne
      exact Finset.disjoint_left.mp (hA_pair (f 0) j₀ hne).1 (hrep_mem (f 0)) h0_mem
    have hf1 : f 1 = j₀ := by
      by_contra hne
      exact Finset.disjoint_left.mp (hA_pair (f 1) j₀ hne).1 (hrep_mem (f 1)) h1_mem
    have h01 : (0 : Fin 6) = 1 := f.injective (hf0.trans hf1.symm)
    exact absurd h01 (by decide)
  exact ⟨t, A, hA_biUnion, hA_props, hA_pair, hA_mono, h_free_egraph, h_free_bird⟩

/-- Cross-block purity between apex-cutter pure blocks in distinct comb teeth:
if $D_1 \subseteq B_i$ and $D_2 \subseteq B_r$ ($i \neq r$) are nonempty and satisfy `IsApexCutterPureBlock`,
then $(D_1, D_2)$ is a pure pair in $G$. -/
theorem isPurePair_of_apexCutterPureBlock_in_comb {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {S : Finset V} {ℓ : ℕ} {w : ℝ}
    {a : Fin ℓ → V} {B : Fin ℓ → Finset V} {v : V}
    (hcomb : IsCombIn G S ℓ w a B) (hapex : IsCombExternalApex G S ℓ a B v)
    {i r : Fin ℓ} (hir : i ≠ r)
    {D₁ D₂ : Finset V} (hD₁B : D₁ ⊆ B i) (hD₂B : D₂ ⊆ B r)
    (hD₁_ne : D₁.Nonempty) (hD₂_ne : D₂.Nonempty)
    (h₁ : IsApexCutterPureBlock G D₁) (h₂ : IsApexCutterPureBlock G D₂) :
    IsPurePair G D₁ D₂ := by
  obtain ⟨z₀, hz₀⟩ := hD₁_ne
  obtain ⟨u₀, hu₀⟩ := hD₂_ne
  have hz₀_pure : IsVertexPureTo G z₀ D₂ :=
    h₂ v (a r) z₀ (isApexCutterTriple_of_comb hcomb hapex hir hD₂B (hD₁B hz₀))
  rcases hz₀_pure with hz₀_comp | hz₀_anti
  · left
    intro z hz u hu
    have hu_pure : IsVertexPureTo G u D₁ :=
      h₁ v (a i) u (isApexCutterTriple_of_comb hcomb hapex hir.symm hD₁B (hD₂B hu))
    rcases hu_pure with hu_comp | hu_anti
    · exact G.symm (hu_comp z hz)
    · exact False.elim (hu_anti z₀ hz₀ (G.symm (hz₀_comp u hu)))
  · right
    intro z hz u hu hadj
    have hu_pure : IsVertexPureTo G u D₁ :=
      h₁ v (a i) u (isApexCutterTriple_of_comb hcomb hapex hir.symm hD₁B (hD₂B hu))
    rcases hu_pure with hu_comp | hu_anti
    · exact hz₀_anti u hu (G.symm (hu_comp z₀ hz₀))
    · exact hu_anti z hz (G.symm hadj)

/--
**Rule (i) Non-Neighbor Anticonnected Component Modularity (`bird_comb_nonneighbor_anticonnectedComponent_isProperModuleIn`)**:
In a `BirdGraphᶜ`-free graph $F$ with an $(\ell, w)$-comb $(a, B)$ and external apex $v$,
for any $i \neq r$, any $M \subseteq B_i$, and any $u \in B_r$ not anticomplete to $M$ in $F$,
every anticonnected component $C$ of $F[M \setminus N_F(u)]$ is a proper module of $F[M]$.
-/
theorem bird_comb_nonneighbor_anticonnectedComponent_isProperModuleIn
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : SimpleGraph V} {S : Finset V} {ℓ : ℕ} {w : ℝ}
    {a : Fin ℓ → V} {B : Fin ℓ → Finset V} {v : V}
    (hF : IsInducedSubgraphFree F BirdGraphᶜ)
    (hcomb : IsCombIn F S ℓ w a B) (hapex : IsCombExternalApex F S ℓ a B v)
    {i r : Fin ℓ} (hri : r ≠ i) {M : Finset V} (hMB : M ⊆ B i)
    {u : V} (hu : u ∈ B r) (hnotanti : ∃ w₀ ∈ M, F.Adj u w₀)
    {C : Finset V} (hC : IsAnticonnectedComponentOf F (M \ neighborFinsetIn F u M) C) :
    IsProperModuleIn F M C := by
  have hCZ : C ⊆ M \ neighborFinsetIn F u M := hC.1
  have hCM : C ⊆ M := hCZ.trans Finset.sdiff_subset
  refine ⟨hC.nonempty, ?_, hCM, ?_⟩
  · rw [Finset.ssubset_iff_of_subset hCM]
    rcases hnotanti with ⟨w₀, hw₀M, huw₀⟩
    refine ⟨w₀, hw₀M, fun hw₀C => ?_⟩
    have hw₀Z := hCZ hw₀C
    rw [Finset.mem_sdiff, mem_neighborFinsetIn_iff] at hw₀Z
    exact hw₀Z.2 ⟨hw₀M, huw₀⟩
  · intro z hzM hzC
    by_cases huz : F.Adj u z
    · by_contra hnotpure
      rw [not_isVertexPureTo_iff_isVertexMixedOn] at hnotpure
      obtain ⟨s, hsC, q, hqC, hsq_ne, hsq_nadj, hzs_nadj, hzq_adj⟩ :=
        hnotpure.exists_anticonnected_edge hC.2.1
      have hsZ := hCZ hsC
      have hqZ := hCZ hqC
      rw [Finset.mem_sdiff, mem_neighborFinsetIn_iff, not_and] at hsZ hqZ
      have hus : ¬F.Adj u s := hsZ.2 hsZ.1
      have huq : ¬F.Adj u q := hqZ.2 hqZ.1
      have hzs_ne : z ≠ s := fun h => hus (h ▸ huz)
      have htriple := isApexCutterTriple_of_comb hcomb hapex hri hMB hu
      exact bird_comb_rule1 hF htriple hzM (hCM hqC) (hCM hsC)
        hzs_ne hsq_ne.symm hzq_adj hzs_nadj (fun h => hsq_nadj (F.symm h))
        huz huq hus
    · have hzZ : z ∈ M \ neighborFinsetIn F u M := by
        rw [Finset.mem_sdiff, mem_neighborFinsetIn_iff]
        exact ⟨hzM, fun h => huz h.2⟩
      left
      intro x hxC
      exact F.symm (hC.2.2 x hxC z hzZ hzC)

/--
**Proposition 6(1a) — Stage-1 Comb Dichotomy for `BirdGraph` (`bird_comb_dichotomy`, line 1001 of `main.tex`)**:
Given `HasPairErdosHajnalProp EGraph BirdGraphᶜ`, there exists an Erdős–Hajnal exponent $c_0 \in (0, 1]$
such that for every `BirdGraphᶜ`-free graph $F$, every $(\ell, w)$-comb $((a_i, B_i) : i \in [\ell])$
in $F$ inside $S \subseteq V$ with $\ell \ge 4$ and external apex $v \in S$, either:
- **(CD1)**: $(w / 2)^{c_0} \le \kappa(F)$; or
- **(CD2)**: $F[S]$ contains a pairwise-pure $(k, \min(\frac{w}{2\ell}, \frac{w}{8 k^2}))$-blockade
  for some integer $k \ge \lceil \frac{\ell}{2} \rceil$ (with $k = \ell$ or $(k : \mathbb{R})^{c_0} \le \kappa(F)$).
-/
theorem bird_comb_dichotomy (hEH : HasPairErdosHajnalProp EGraph BirdGraphᶜ) :
    ∃ c₀ > (0 : ℝ), c₀ ≤ 1 ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (F : SimpleGraph V) (S : Finset V)
        (ℓ : ℕ) (w : ℝ) (a : Fin ℓ → V) (B : Fin ℓ → Finset V) (v : V),
        IsInducedSubgraphFree F BirdGraphᶜ →
        IsCombIn F S ℓ w a B →
        IsCombExternalApex F S ℓ a B v →
        4 ≤ ℓ →
        0 ≤ w →
        ((w / 2) ^ c₀ ≤ (kappa F : ℝ)) ∨
        (∃ (k : ℕ) (U : Fin k → Finset V),
          ℓ ≤ 2 * k ∧
          (k = ℓ ∨ (k : ℝ) ^ c₀ ≤ (kappa F : ℝ)) ∧
          IsPureBlockadeIn F S k (min (w / (2 * (ℓ : ℝ))) (w / (8 * (k : ℝ) ^ 2))) U) := by
  obtain ⟨c_pair, hc_pair, h_pair⟩ := hEH
  let c₀ : ℝ := min c_pair 1
  have hc₀_pos : 0 < c₀ := lt_min hc_pair zero_lt_one
  have hc₀_le_one : c₀ ≤ 1 := min_le_right _ _
  have hc₀_le_cpair : c₀ ≤ c_pair := min_le_left _ _
  refine ⟨c₀, hc₀_pos, hc₀_le_one, ?_⟩
  intro V _ _ F S ℓ w a B v hF hcomb hapex hℓ4 hw_nonneg
  classical
  haveI : Nonempty V := ⟨v⟩
  have hkappa_ge_one : (1 : ℝ) ≤ (kappa F : ℝ) := by exact_mod_cast kappa_pos_of_nonempty F
  by_cases hw_small : w < 2
  · left
    have h1 : (w / 2) ^ c₀ ≤ 1 := Real.rpow_le_one (by linarith) (by linarith) (le_of_lt hc₀_pos)
    linarith
  · push_neg at hw_small
    let X (i : Fin ℓ) : Finset V := eGraphUnionIn F (B i)
    let Y (i : Fin ℓ) : Finset V := B i \ X i
    by_cases hY_large : ∃ i : Fin ℓ, w / 2 ≤ ((Y i).card : ℝ)
    · left
      obtain ⟨i, hiY⟩ := hY_large
      have hY_free_E : IsInducedSubgraphFree (F.induce ((Y i : Finset V) : Set V)) EGraph :=
        isInducedSubgraphFree_eGraph_sdiff_eGraphUnionIn F (B i)
      have hY_free_B : IsInducedSubgraphFree (F.induce ((Y i : Finset V) : Set V)) BirdGraphᶜ := by
        rintro ⟨f, hf⟩
        refine hF ⟨f.trans (Function.Embedding.subtype _), ?_⟩
        ext p q
        exact (congr_arg (fun H => H.Adj p q) hf).to_iff
      have h_eh_Y := h_pair ↥(Y i) (F.induce (Y i : Set V)) hY_free_E hY_free_B
      rw [Fintype.card_coe] at h_eh_Y
      have hY_ge_one : (1 : ℝ) ≤ ((Y i).card : ℝ) := by linarith
      have h_c0_le : ((Y i).card : ℝ) ^ c₀ ≤ ((Y i).card : ℝ) ^ c_pair :=
        Real.rpow_le_rpow_of_exponent_le hY_ge_one hc₀_le_cpair
      have h_mono : (w / 2) ^ c₀ ≤ ((Y i).card : ℝ) ^ c₀ :=
        Real.rpow_le_rpow (by linarith) hiY (le_of_lt hc₀_pos)
      have h_kappa_ind : (kappa (F.induce (Y i : Set V)) : ℝ) ≤ (kappa F : ℝ) := by
        exact_mod_cast induce_kappa_le F (Y i)
      linarith
    · push_neg at hY_large
      have hX_large : ∀ i : Fin ℓ, w / 2 < ((X i).card : ℝ) := by
        intro i
        have hX_sub : X i ⊆ B i := by
          intro z hz
          rcases Finset.mem_biUnion.mp hz with ⟨g, hg, hz_img⟩
          rcases Finset.mem_image.mp hz_img with ⟨p, _, rfl⟩
          exact (Finset.mem_filter.mp hg).2.1 p
        have h_sum : ((Y i).card : ℝ) + ((X i).card : ℝ) = ((B i).card : ℝ) := by
          exact_mod_cast Finset.card_sdiff_add_card_eq_card hX_sub
        have hB_ge : w ≤ ((B i).card : ℝ) := hcomb.is_blockade.width_ge i
        have hYi := hY_large i
        linarith
      have h_desc_all : ∀ i : Fin ℓ, ∃ (t : ℕ) (A : Fin t → Finset V),
          Finset.univ.biUnion A = X i ∧
          (∀ j : Fin t, A j ⊆ X i ∧ (A j).Nonempty ∧ IsAnticonnected F (A j) ∧ IsApexCutterPureBlock F (A j)) ∧
          (∀ j₁ j₂ : Fin t, j₁ ≠ j₂ → Disjoint (A j₁) (A j₂) ∧ IsPurePair F (A j₁) (A j₂)) ∧
          (∀ j₁ j₂ : Fin t, j₁ ≤ j₂ → (A j₂).card ≤ (A j₁).card) ∧
          IsInducedSubgraphFree (purePatternGraph F A) EGraph ∧
          IsInducedSubgraphFree (purePatternGraph F A) BirdGraphᶜ :=
        fun i => bird_quotient_descent hF (B i)
      choose t_i A_i hA_bi hA_pr hA_pair hA_mono hJ_E hJ_B using h_desc_all
      have ht_pos : ∀ i : Fin ℓ, 0 < t_i i := by
        intro i
        by_contra h0
        have ht0 : t_i i = 0 := Nat.eq_zero_of_le_zero (Nat.not_lt.mp h0)
        have hX_emp : X i = ∅ := by
          rw [← hA_bi i, Finset.eq_empty_iff_forall_notMem]
          intro z hz
          rcases Finset.mem_biUnion.mp hz with ⟨j, _, _⟩
          exact Fin.elim0 (ht0 ▸ j)
        have hX_gt := hX_large i
        rw [hX_emp, Finset.card_empty, Nat.cast_zero] at hX_gt
        linarith
      have hX_sub_B : ∀ i : Fin ℓ, X i ⊆ B i := by
        intro i z hz
        rcases Finset.mem_biUnion.mp hz with ⟨g, hg, hz_img⟩
        rcases Finset.mem_image.mp hz_img with ⟨p, _, rfl⟩
        exact (Finset.mem_filter.mp hg).2.1 p
      by_cases h_cross : ∀ i : Fin ℓ, w / (2 * (ℓ : ℝ)) ≤ ((A_i i ⟨0, ht_pos i⟩).card : ℝ)
      · right
        let U : Fin ℓ → Finset V := fun i => A_i i ⟨0, ht_pos i⟩
        refine ⟨ℓ, U, by omega, Or.inl rfl, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
        · intro i
          exact ((hA_pr i ⟨0, ht_pos i⟩).1.trans (hX_sub_B i)).trans (hcomb.is_blockade.subset_ambient i)
        · intro i
          exact (hA_pr i ⟨0, ht_pos i⟩).2.1
        · intro i r hir
          exact Finset.disjoint_of_subset_left
            ((hA_pr i ⟨0, ht_pos i⟩).1.trans (hX_sub_B i))
            (Finset.disjoint_of_subset_right
              ((hA_pr r ⟨0, ht_pos r⟩).1.trans (hX_sub_B r))
              (hcomb.is_blockade.pairwise_disjoint i r hir))
        · intro i
          exact (min_le_left _ _).trans (h_cross i)
        · intro i r hir
          exact isPurePair_of_apexCutterPureBlock_in_comb hcomb hapex hir
            ((hA_pr i ⟨0, ht_pos i⟩).1.trans (hX_sub_B i))
            ((hA_pr r ⟨0, ht_pos r⟩).1.trans (hX_sub_B r))
            (hA_pr i ⟨0, ht_pos i⟩).2.1 (hA_pr r ⟨0, ht_pos r⟩).2.1
            (hA_pr i ⟨0, ht_pos i⟩).2.2.2 (hA_pr r ⟨0, ht_pos r⟩).2.2.2
      · right
        push_neg at h_cross
        obtain ⟨i, hi_small⟩ := h_cross
        let q := t_i i
        let A := A_i i
        have hA_sum : ∑ j : Fin q, ((A j).card : ℝ) = ((X i).card : ℝ) := by
          have h_nat : ∑ j : Fin q, (A j).card = (X i).card := by
            rw [← hA_bi i, Finset.card_biUnion (fun j₁ _ j₂ _ hj => (hA_pair i j₁ j₂ hj).1)]
          exact_mod_cast h_nat
        let p₀ : ℕ := ℓ / 2
        have hp₀_ge_2 : 2 ≤ p₀ := by omega
        have hp₀_le_half : (p₀ : ℝ) ≤ (ℓ : ℝ) / 2 := by
          have h_mul : 2 * p₀ ≤ ℓ := Nat.mul_div_le ℓ 2
          have h_r : (2 : ℝ) * (p₀ : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast h_mul
          linarith
        let f : ℕ → ℝ := fun k =>
          if h : 1 ≤ k ∧ k ≤ q then ((A ⟨k - 1, by omega⟩).card : ℝ) else 0
        have hf_sum : w / 2 < ∑ k ∈ Finset.Icc 1 q, f k := by
          rw [← sum_fin_eq_sum_Icc q (fun j => ((A j).card : ℝ)), hA_sum]
          exact hX_large i
        have hf_le : ∀ k, f k ≤ w / (2 * (ℓ : ℝ)) := by
          intro k
          unfold f
          split_ifs with h
          · have hj_le : (⟨0, ht_pos i⟩ : Fin q) ≤ ⟨k - 1, by omega⟩ := by
              simp [Fin.le_def]
            have h_m : ((A ⟨k - 1, by omega⟩).card : ℝ) ≤ ((A ⟨0, ht_pos i⟩).card : ℝ) :=
              Nat.cast_le.mpr (hA_mono i _ _ hj_le)
            exact le_trans h_m (le_of_lt hi_small)
          · positivity
        have hp₀_sum : ∑ k ∈ Finset.Icc 1 p₀, f k ≤ w / 4 := by
          have hℓ_pos : (0 : ℝ) < (ℓ : ℝ) := by positivity
          calc ∑ k ∈ Finset.Icc 1 p₀, f k
              ≤ ∑ _k ∈ Finset.Icc 1 p₀, (w / (2 * (ℓ : ℝ))) := Finset.sum_le_sum (fun k _ => hf_le k)
            _ = (p₀ : ℝ) * (w / (2 * (ℓ : ℝ))) := by
                rw [Finset.sum_const, Nat.card_Icc, show p₀ + 1 - 1 = p₀ by omega, nsmul_eq_mul]
            _ ≤ ((ℓ : ℝ) / 2) * (w / (2 * (ℓ : ℝ))) :=
                mul_le_mul_of_nonneg_right hp₀_le_half (by positivity)
            _ = w / 4 := by field_simp; ring
        have hp₀_q : p₀ ≤ q := by
          by_contra hlt
          push_neg at hlt
          have hsub : Finset.Icc 1 q ⊆ Finset.Icc 1 p₀ := Finset.Icc_subset_Icc le_rfl (by omega)
          have h1 : ∑ k ∈ Finset.Icc 1 q, f k ≤ ∑ k ∈ Finset.Icc 1 p₀, f k :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by unfold f; split_ifs <;> positivity)
          linarith
        have h_tail_sum : w / 4 ≤ ∑ k ∈ Finset.Icc (p₀ + 1) q, f k := by
          have h_sp := sum_Icc_split p₀ q hp₀_q f
          linarith
        obtain ⟨m, hm_mem, hm_ge⟩ :=
          cauchy_series_extraction p₀ q f (w / 4) (by linarith) h_tail_sum
        obtain ⟨hm_low, hm_high⟩ := Finset.mem_Icc.mp hm_mem
        have hm_1 : 1 ≤ m ∧ m ≤ q := ⟨by omega, hm_high⟩
        unfold f at hm_ge
        rw [dif_pos hm_1] at hm_ge
        have hm_width : w / (8 * (m : ℝ) ^ 2) ≤ ((A ⟨m - 1, by omega⟩).card : ℝ) := by
          have h_eq : (w / 4) / (2 * (m : ℝ) ^ 2) = w / (8 * (m : ℝ) ^ 2) := by ring
          rwa [h_eq] at hm_ge
        -- Bound m ^ c₀ ≤ q ^ c₀ ≤ kappa F via the pattern graph J_i
        have h_eh_J := h_pair (Fin q) (purePatternGraph F A) (hJ_E i) (hJ_B i)
        rw [Fintype.card_fin] at h_eh_J
        let rep : Fin q → V := fun j => Classical.choose (hA_pr i j).2.1
        have hrep_mem : ∀ j : Fin q, rep j ∈ A j := fun j => Classical.choose_spec (hA_pr i j).2.1
        have hrep_inj : Function.Injective rep := by
          intro j₁ j₂ h
          by_contra hne
          exact Finset.disjoint_left.mp (hA_pair i j₁ j₂ hne).1 (hrep_mem j₁) (h ▸ hrep_mem j₂)
        let repEmb : Fin q ↪ V := ⟨rep, hrep_inj⟩
        have h_pat_eq : purePatternGraph F A = F.comap repEmb := by
          ext j₁ j₂
          simp only [purePatternGraph, comap_adj, repEmb, Function.Embedding.coeFn_mk]
          by_cases hj : j₁ = j₂
          · subst hj; simp
          · simp only [hj, ne_eq, not_false_eq_true, true_and]
            rcases (hA_pair i j₁ j₂ hj).2 with hcomp | hanti
            · exact iff_of_true hcomp (hcomp (rep j₁) (hrep_mem j₁) (rep j₂) (hrep_mem j₂))
            · exact iff_of_false
                (fun hc => hanti (rep j₁) (hrep_mem j₁) (rep j₂) (hrep_mem j₂)
                  (hc (rep j₁) (hrep_mem j₁) (rep j₂) (hrep_mem j₂)))
                (hanti (rep j₁) (hrep_mem j₁) (rep j₂) (hrep_mem j₂))
        have h_kappa_J : (kappa (purePatternGraph F A) : ℝ) ≤ (kappa F : ℝ) := by
          rw [h_pat_eq]
          exact_mod_cast kappa_comap_le F repEmb
        have hq_ge_1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
        have h_c0_q : (q : ℝ) ^ c₀ ≤ (q : ℝ) ^ c_pair :=
          Real.rpow_le_rpow_of_exponent_le hq_ge_1 hc₀_le_cpair
        have hm_le_q : (m : ℝ) ≤ (q : ℝ) := by exact_mod_cast hm_high
        have hm_c0 : (m : ℝ) ^ c₀ ≤ (kappa F : ℝ) := by
          have h1 : (m : ℝ) ^ c₀ ≤ (q : ℝ) ^ c₀ :=
            Real.rpow_le_rpow (by positivity) hm_le_q (le_of_lt hc₀_pos)
          linarith
        let U : Fin m → Finset V := fun j => A ⟨j.1, by omega⟩
        refine ⟨m, U, by omega, Or.inr hm_c0, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
        · intro j
          exact ((hA_pr i ⟨j.1, by omega⟩).1.trans (hX_sub_B i)).trans (hcomb.is_blockade.subset_ambient i)
        · intro j
          exact (hA_pr i ⟨j.1, by omega⟩).2.1
        · intro j₁ j₂ hj
          have hj' : (⟨j₁.1, by omega⟩ : Fin q) ≠ ⟨j₂.1, by omega⟩ := by
            intro h; apply hj; ext; exact Fin.mk.inj_iff.mp h
          exact (hA_pair i _ _ hj').1
        · intro j
          have hj_le : (⟨j.1, by omega⟩ : Fin q) ≤ ⟨m - 1, by omega⟩ := by
            simp only [Fin.mk_le_mk]; omega
          have h_m : ((A ⟨m - 1, by omega⟩).card : ℝ) ≤ ((U j).card : ℝ) :=
            Nat.cast_le.mpr (hA_mono i _ _ hj_le)
          exact (min_le_right _ _).trans (hm_width.trans h_m)
        · intro j₁ j₂ hj
          have hj' : (⟨j₁.1, by omega⟩ : Fin q) ≠ ⟨j₂.1, by omega⟩ := by
            intro h; apply hj; ext; exact Fin.mk.inj_iff.mp h
          exact (hA_pair i _ _ hj').2

/-!
### Section 4a: Proposition 6(2b) — Stable Sets $\overline{K_s}$ and $(s, d)$-Brooms $B(s, d)$ in Substitution Closures
(`main.tex` lines 980, 1012)

For all $s \ge 1$ and $d \ge 0$, the $(s + d + 1)$-vertex broom $B(s, d) := P_{d+2}[v_1 \leftarrow \overline{K_s}]$
(`BroomGraph s d`) is obtained from $P_{d+2}$ by substituting the $s$-vertex stable set $\overline{K_s} \in \mathcal{H}(\mathcal{B}_1^*)$
(`bot_inHClosure_one`) for the degree-$1$ endpoint `0` ($v_1$) of $P_{d+2}$. Consequently,
$B(s, d) \in \mathcal{H}(\mathcal{B}_{d+2}^*)$, and whenever $P_{d+2} \in \mathcal{EH}$, iterated twin
substitution (`erdos_hajnal_twin_substitution`) yields $B(s, d), \overline{B(s, d)} \in \mathcal{EH}$.
-/

/-- Equivalence between `{v : Fin 2 // v ≠ 1} ⊕ Fin s` and `Fin (s + 1)`. -/
def substFin2OneEquiv (s : ℕ) : ({v : Fin 2 // v ≠ 1} ⊕ Fin s) ≃ Fin (s + 1) where
  toFun
    | Sum.inl _ => 0
    | Sum.inr j => j.succ
  invFun i :=
    if h0 : i = 0 then Sum.inl ⟨0, by decide⟩
    else Sum.inr (i.pred h0)
  left_inv x := by
    rcases x with ⟨u, hu⟩ | j
    · fin_cases u
      · rfl
      · exact False.elim (hu rfl)
    · simp
  right_inv i := by
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩ <;> simp

/-- Explicit graph isomorphism $\overline{K_2}[1 \leftarrow \overline{K_s}] \simeq_g \overline{K_{s+1}}$
(`substGraph (⊥ : SimpleGraph (Fin 2)) 1 (⊥ : SimpleGraph (Fin s)) ≃g (⊥ : SimpleGraph (Fin (s + 1)))`). -/
def substBotFin2IsoBot (s : ℕ) :
    substGraph (⊥ : SimpleGraph (Fin 2)) 1 (⊥ : SimpleGraph (Fin s)) ≃g
      (⊥ : SimpleGraph (Fin (s + 1))) where
  toEquiv := substFin2OneEquiv s
  map_rel_iff' := by
    intro a b
    cases a <;> cases b <;> simp [substGraph]

/-- Explicit graph isomorphism $K_2[1 \leftarrow K_s] \simeq_g K_{s+1}$
(`substGraph (⊤ : SimpleGraph (Fin 2)) 1 (⊤ : SimpleGraph (Fin s)) ≃g (⊤ : SimpleGraph (Fin (s + 1)))`). -/
def substTopFin2IsoTop (s : ℕ) :
    substGraph (⊤ : SimpleGraph (Fin 2)) 1 (⊤ : SimpleGraph (Fin s)) ≃g
      (⊤ : SimpleGraph (Fin (s + 1))) where
  toEquiv := substFin2OneEquiv s
  map_rel_iff' := by
    intro a b
    rcases a with ⟨u, hu⟩ | x <;> rcases b with ⟨w, hw⟩ | y
    · fin_cases u <;> fin_cases w <;>
        first | exact False.elim (hu rfl) | exact False.elim (hw rfl) | simp [substGraph, substFin2OneEquiv]
    · fin_cases u <;>
        first | exact False.elim (hu rfl) | simp [substGraph, substFin2OneEquiv, (Fin.succ_ne_zero y).symm]
    · fin_cases w <;>
        first | exact False.elim (hw rfl) | simp [substGraph, substFin2OneEquiv, Fin.succ_ne_zero x]
    · simp [substGraph, substFin2OneEquiv]

/--
**Proposition 6(2b) — Every Empty Graph $\overline{K_s}$ Belongs to $\mathcal{H}(\mathcal{B}_1^*)$ (`bot_inHClosure_one`, `main.tex` line 1012)**:
For every integer $s \ge 1$, `(⊥ : SimpleGraph (Fin s))` belongs to `InHClosure 1`, proved by induction
on $s$ using `substGraph` with $\overline{K_2}$ (`⊥ : SimpleGraph (Fin 2)`) and $K_2$ (`⊤ : SimpleGraph (Fin 2)`).
-/
theorem bot_inHClosure_one : ∀ s : ℕ, 1 ≤ s → InHClosure 1 (⊥ : SimpleGraph (Fin s)) := by
  intro s hs
  induction s with
  | zero => omega
  | succ m ih =>
    rcases eq_or_lt_of_le (Nat.zero_le m) with rfl | hm_pos
    · exact ⟨inJClosure_of_card_eq_one 1 _ (by simp), inJClosure_of_card_eq_one 1 _ (by simp)⟩
    · obtain ⟨ih_bot, ih_compl⟩ := ih hm_pos
      have hk2_bot : InJClosure 1 (⊥ : SimpleGraph (Fin 2)) :=
        InJClosure.base _ (Or.inr (Or.inr (Or.inl ⟨SimpleGraph.Iso.refl⟩)))
      have hk2_top : InJClosure 1 (⊤ : SimpleGraph (Fin 2)) :=
        InJClosure.base _ (Or.inr (Or.inl ⟨SimpleGraph.Iso.refl⟩))
      have h_bot_next : InJClosure 1 (⊥ : SimpleGraph (Fin (m + 1))) :=
        InJClosure.iso _ _ (InJClosure.subst _ 1 _ hk2_bot ih_bot) ⟨substBotFin2IsoBot m⟩
      have h_compl_eq_m : (⊥ : SimpleGraph (Fin m))ᶜ = (⊤ : SimpleGraph (Fin m)) := compl_bot
      have h_compl_eq_succ : (⊥ : SimpleGraph (Fin (m + 1)))ᶜ = (⊤ : SimpleGraph (Fin (m + 1))) := compl_bot
      have ih_top : InJClosure 1 (⊤ : SimpleGraph (Fin m)) := h_compl_eq_m ▸ ih_compl
      have h_top_next : InJClosure 1 (⊤ : SimpleGraph (Fin (m + 1))) :=
        InJClosure.iso _ _ (InJClosure.subst _ 1 _ hk2_top ih_top) ⟨substTopFin2IsoTop m⟩
      exact ⟨h_bot_next, h_compl_eq_succ.symm ▸ h_top_next⟩

/-- Isomorphism invariance of `HasErdosHajnalProp`. -/
theorem HasErdosHajnalProp.of_iso {W₁ W₂ : Type*} {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂}
    (e : H₁ ≃g H₂) (h₁ : HasErdosHajnalProp H₁) : HasErdosHajnalProp H₂ := by
  obtain ⟨c, hc, h_bound⟩ := h₁
  refine ⟨c, hc, fun V _ _ G hG => ?_⟩
  refine h_bound V G ?_
  rintro ⟨f, hf⟩
  refine hG ⟨e.symm.toEquiv.toEmbedding.trans f, ?_⟩
  ext x y
  have h1 := (e.symm.map_rel_iff (a := x) (b := y)).symm
  have h2 := (congr_arg (fun H => H.Adj (e.symm x) (e.symm y)) hf).to_iff
  exact h1.trans h2

/-- Equivalence between `{v : Fin (d + 2) // v ≠ 0} ⊕ Fin s` and `Fin (d + 1 + s)`. -/
def broomVertEquiv (s d : ℕ) : ({v : Fin (d + 2) // v ≠ 0} ⊕ Fin s) ≃ Fin (d + 1 + s) where
  toFun
    | Sum.inl ⟨v, hv⟩ =>
        ⟨v.1 - 1, by
          have : 1 ≤ v.1 := Nat.one_le_iff_ne_zero.mpr (Fin.val_ne_of_ne hv)
          omega⟩
    | Sum.inr j => ⟨d + 1 + j.1, by omega⟩
  invFun i :=
    if h : i.1 < d + 1 then
      Sum.inl ⟨⟨i.1 + 1, by omega⟩, by intro hc; exact absurd (congr_arg Fin.val hc) (by simp)⟩
    else
      Sum.inr ⟨i.1 - (d + 1), by omega⟩
  left_inv x := by
    rcases x with ⟨v, hv⟩ | j
    · have hv1 : 1 ≤ v.1 := Nat.one_le_iff_ne_zero.mpr (Fin.val_ne_of_ne hv)
      have hlt : v.1 - 1 < d + 1 := by omega
      dsimp only
      rw [dif_pos hlt]
      congr 1; ext; dsimp; omega
    · have hnot : ¬(d + 1 + j.1 < d + 1) := by omega
      dsimp only
      rw [dif_neg hnot]
      congr 1; ext; dsimp; omega
  right_inv i := by
    dsimp only
    split_ifs with h
    · ext; dsimp
    · ext; dsimp; omega

/-- Canonical `Fin (d + 1 + s)` representation of `BroomGraph s d`. -/
def broomFinGraph (s d : ℕ) : SimpleGraph (Fin (d + 1 + s)) :=
  (BroomGraph s d).comap (broomVertEquiv s d).symm.toEmbedding

/-- Graph isomorphism `BroomGraph s d ≃g broomFinGraph s d`. -/
def broomIsoFin (s d : ℕ) : BroomGraph s d ≃g broomFinGraph s d where
  toEquiv := broomVertEquiv s d
  map_rel_iff' := by
    intro a b
    simp [broomFinGraph]

/-- Graph isomorphism $P_{d+2} \simeq_g B(1, d)$ (`pathGraph (d + 2) ≃g broomFinGraph 1 d`). -/
def pathGraphIsoBroomFinOne (d : ℕ) : pathGraph (d + 2) ≃g broomFinGraph 1 d where
  toFun v :=
    if hv : v = 0 then ⟨d + 1, by omega⟩
    else ⟨v.1 - 1, by have : 1 ≤ v.1 := Nat.one_le_iff_ne_zero.mpr (Fin.val_ne_of_ne hv); omega⟩
  invFun i :=
    if hi : i.1 < d + 1 then ⟨i.1 + 1, by omega⟩
    else 0
  left_inv v := by
    by_cases hv : v = 0
    · subst hv; simp
    · have hv1 : 1 ≤ v.1 := Nat.one_le_iff_ne_zero.mpr (Fin.val_ne_of_ne hv)
      have hlt : v.1 - 1 < d + 1 := by omega
      dsimp only
      rw [dif_neg hv, dif_pos hlt]
      ext; dsimp; omega
  right_inv i := by
    dsimp only
    by_cases hi : i.1 < d + 1
    · rw [dif_pos hi]
      have hne : (⟨i.1 + 1, by omega⟩ : Fin (d + 2)) ≠ 0 := by
        intro hc; exact absurd (congr_arg Fin.val hc) (by simp)
      rw [dif_neg hne]
      ext; dsimp
    · rw [dif_neg hi, dif_pos rfl]
      ext; dsimp; omega
  map_rel_iff' := by
    intro u v
    simp only [Equiv.coe_fn_mk, broomFinGraph, comap_adj, Equiv.coe_toEmbedding]
    by_cases hu : u = 0 <;> by_cases hv : v = 0
    · subst hu; subst hv; simp
    · subst hu
      have hv1 : 1 ≤ v.1 := Nat.one_le_iff_ne_zero.mpr (Fin.val_ne_of_ne hv)
      have hlt : v.1 - 1 < d + 1 := by omega
      have h_not : ¬(d + 1 < d + 1) := by omega
      simp only [dif_pos, dif_neg hv, broomVertEquiv, Equiv.coe_fn_symm_mk, dif_neg h_not, dif_pos hlt]
      dsimp [BroomGraph, substGraph]
      rw [pathGraph_adj, pathGraph_adj]
      simp only [Fin.val_zero]
      dsimp; omega
    · subst hv
      have hu1 : 1 ≤ u.1 := Nat.one_le_iff_ne_zero.mpr (Fin.val_ne_of_ne hu)
      have hlt : u.1 - 1 < d + 1 := by omega
      have h_not : ¬(d + 1 < d + 1) := by omega
      simp only [dif_pos, dif_neg hu, broomVertEquiv, Equiv.coe_fn_symm_mk, dif_neg h_not, dif_pos hlt]
      dsimp [BroomGraph, substGraph]
      rw [pathGraph_adj, pathGraph_adj]
      simp only [Fin.val_zero]
      dsimp; omega
    · have hu1 : 1 ≤ u.1 := Nat.one_le_iff_ne_zero.mpr (Fin.val_ne_of_ne hu)
      have hv1 : 1 ≤ v.1 := Nat.one_le_iff_ne_zero.mpr (Fin.val_ne_of_ne hv)
      have hlt_u : u.1 - 1 < d + 1 := by omega
      have hlt_v : v.1 - 1 < d + 1 := by omega
      simp only [dif_neg hu, dif_neg hv, broomVertEquiv, Equiv.coe_fn_symm_mk, dif_pos hlt_u, dif_pos hlt_v]
      dsimp [BroomGraph, substGraph]
      rw [pathGraph_adj, pathGraph_adj]
      dsimp; omega

/-- `broomFinGraph (s + 1) d` is a non-adjacent twin extension (`IsTwinExtension`) of `broomFinGraph s d` ($s \ge 1$). -/
theorem isTwinExtension_broomFinGraph (s d : ℕ) (hs : 1 ≤ s) :
    IsTwinExtension (broomFinGraph s d) (broomFinGraph (s + 1) d)
      ⟨d + 1, by omega⟩ (Fin.last (d + 1 + s)) Fin.castSuccEmb where
  h_miss w := Fin.ne_of_lt (Fin.castSucc_lt_last w)
  h_comap := by
    ext u v
    simp only [comap_adj, Fin.coe_castSuccEmb, broomFinGraph, Equiv.coe_toEmbedding,
      broomVertEquiv, Equiv.coe_fn_symm_mk, Fin.val_castSucc]
    by_cases hu : u.1 < d + 1 <;> by_cases hv : v.1 < d + 1 <;>
      simp [hu, hv, BroomGraph, substGraph]
  h_twin w hw := by
    simp only [Fin.coe_castSuccEmb, broomFinGraph, comap_adj, Equiv.coe_toEmbedding,
      broomVertEquiv, Equiv.coe_fn_symm_mk, Fin.val_castSucc, Fin.val_last]
    have h_not_last : ¬(d + 1 + s < d + 1) := by omega
    have h_not_v0 : ¬(d + 1 < d + 1) := by omega
    by_cases hw_lt : w.1 < d + 1
    · simp [hw_lt, h_not_last, h_not_v0, BroomGraph, substGraph]
    · simp [hw_lt, h_not_last, h_not_v0, BroomGraph, substGraph]

/--
**Proposition 6(2b) — $(s, d)$-Brooms `BroomGraph s d` in $\mathcal{H}(\mathcal{B}_{d+2}^*)$ and $\mathcal{EH}$ (`broom_in_subst_closure`, `main.tex` lines 980, 1012)**:
For all integers $s \ge 1$ and $d \ge 0$, `BroomGraph s d` belongs to `InJClosure (d + 2)` and `InHClosure (d + 2)`;
moreover, whenever `HasErdosHajnalProp (pathGraph (d + 2))` holds, both `BroomGraph s d` and `(BroomGraph s d)ᶜ`
satisfy `HasErdosHajnalProp` via iterated twin substitution (`erdos_hajnal_twin_substitution`).
-/
theorem broom_in_subst_closure (s d : ℕ) (hs : 1 ≤ s) :
    InJClosure (d + 2) (BroomGraph s d) ∧
    InHClosure (d + 2) (BroomGraph s d) ∧
    (HasErdosHajnalProp (pathGraph (d + 2)) →
      HasErdosHajnalProp (BroomGraph s d) ∧ HasErdosHajnalProp (BroomGraph s d)ᶜ) := by
  have hp : InJClosure (d + 2) (pathGraph (d + 2)) :=
    InJClosure.base _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨d + 2, by omega, le_rfl, Or.inl ⟨SimpleGraph.Iso.refl⟩⟩)))))
  have hpc : InJClosure (d + 2) ((pathGraph (d + 2))ᶜ) :=
    InJClosure.base _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨d + 2, by omega, le_rfl, Or.inr ⟨SimpleGraph.Iso.refl⟩⟩)))))
  have hbot : InHClosure (d + 2) (⊥ : SimpleGraph (Fin s)) :=
    (bot_inHClosure_one s hs).mono (by omega)
  have hJ : InJClosure (d + 2) (BroomGraph s d) :=
    InJClosure.subst (pathGraph (d + 2)) 0 (⊥ : SimpleGraph (Fin s)) hp hbot.1
  have hJc : InJClosure (d + 2) (BroomGraph s d)ᶜ := by
    rw [BroomGraph, substGraph_compl]
    exact InJClosure.subst ((pathGraph (d + 2))ᶜ) 0 ((⊥ : SimpleGraph (Fin s))ᶜ) hpc hbot.2
  refine ⟨hJ, ⟨hJ, hJc⟩, fun hEH_path => ?_⟩
  have h_fin_eh : ∀ m : ℕ, 1 ≤ m → HasErdosHajnalProp (broomFinGraph m d) := by
    intro m hm
    induction m with
    | zero => omega
    | succ k ih =>
      rcases eq_or_lt_of_le (Nat.zero_le k) with rfl | hk_pos
      · exact HasErdosHajnalProp.of_iso (pathGraphIsoBroomFinOne d) hEH_path
      · exact erdos_hajnal_twin_substitution (show 1 ≤ d + 1 + k by omega)
          (isTwinExtension_broomFinGraph k d hk_pos) (ih hk_pos)
  have h_broom : HasErdosHajnalProp (BroomGraph s d) :=
    HasErdosHajnalProp.of_iso (broomIsoFin s d).symm (h_fin_eh s hs)
  exact ⟨h_broom, h_broom.compl⟩

/-!
### Section 4b: Proposition 6(2a) — Depth-$m$ Defective Neighborhood Module Lemma & Comb Dichotomy for `{P_t, Hook_4(Q)}`
(`main.tex` lines 979, 1005–1010)

For $t = 6 + m \ge 6$ ($m \ge 0$) and $Q \in \mathcal{EH}$ with exponent $c_Q \in (0, 1]$, in any
$\overline{\{P_t, \operatorname{Hook}_4(Q)\}}$-free graph $F$ containing an $(\ell, w)$-comb with external
apex $v$, if $\kappa(F) < w_0^{c_Q / (m + 1)}$, then every anticonnected component $C_s$ of $F[N_F(u) \cap M]$
of size $|C_s| \ge 2^{m+1} w_0 > 2 \tau_m$ is a proper module of $F[M]$ (`hook4_defective_neighborhood_module`).
Otherwise, a mixed cutter $z \in M \setminus N_F(u)$ inductively promotes $(y_0 - \dots - y_{q+2}) \cong P_{q+3}$
in $\overline{F}$ across $q = 0, \dots, m$ against $\tau_{m-q} = (2\kappa(F))^{m-q}\kappa(F)^{1/c_Q}$ to produce
an induced $P_{6+m}$ in $\overline{F}$. Feeding this defective modularity into $\Phi_8$ Gallai tree refinement
establishes `hook4_comb_dichotomy`.
-/

/-- Threshold sequence $\tau_r := (2 \kappa(F))^r \kappa(F)^{1 / c_Q}$ from Proposition 6(2a) (`main.tex` line 1005). -/
noncomputable def hook4Tau {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (c_Q : ℝ) (r : ℕ) : ℝ :=
  (2 * (kappa F : ℝ)) ^ r * (kappa F : ℝ) ^ (1 / c_Q)

/-- Recurrence $\tau_{r+1} = 2 \kappa(F) \tau_r$ for `hook4Tau`. -/
theorem hook4Tau_succ {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (c_Q : ℝ) (r : ℕ) :
    hook4Tau F c_Q (r + 1) = 2 * (kappa F : ℝ) * hook4Tau F c_Q r := by
  unfold hook4Tau
  rw [pow_succ']
  ring

/-- Monotonicity $\tau_0 \le \tau_r$ whenever $\kappa(F) \ge 1$. -/
theorem hook4Tau_zero_le {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) {c_Q : ℝ} (r : ℕ) (hkappa : 1 ≤ kappa F) :
    hook4Tau F c_Q 0 ≤ hook4Tau F c_Q r := by
  unfold hook4Tau
  rw [pow_zero, one_mul]
  have hk1 : (1 : ℝ) ≤ 2 * (kappa F : ℝ) := by
    have : (1 : ℝ) ≤ (kappa F : ℝ) := by exact_mod_cast hkappa
    linarith
  have hpow : (1 : ℝ) ≤ (2 * (kappa F : ℝ)) ^ r := one_le_pow₀ hk1
  have hpos : (0 : ℝ) ≤ (kappa F : ℝ) ^ (1 / c_Q) := by positivity
  calc (kappa F : ℝ) ^ (1 / c_Q)
      = 1 * (kappa F : ℝ) ^ (1 / c_Q) := (one_mul _).symm
    _ ≤ (2 * (kappa F : ℝ)) ^ r * (kappa F : ℝ) ^ (1 / c_Q) :=
        mul_le_mul_of_nonneg_right hpow hpos

/-- Algebraic inequality $2 \tau_m < |C_s|$ when $\kappa(F) < w_0^{c_Q / (m + 1)}$ and $|C_s| \ge 2^{m+1} w_0$ (`main.tex` line 1005). -/
theorem two_mul_hook4Tau_lt_of_kappa_lt {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) {c_Q w₀ C_card : ℝ} {m : ℕ}
    (hc_pos : 0 < c_Q) (hc_le : c_Q ≤ 1) (hw₀ : 1 ≤ w₀) (hkappa_pos : 1 ≤ kappa F)
    (hkappa : (kappa F : ℝ) < w₀ ^ (c_Q / ((m : ℝ) + 1)))
    (hC_card : (2 : ℝ) ^ (m + 1) * w₀ ≤ C_card) :
    2 * hook4Tau F c_Q m < C_card := by
  have hm1_pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have h_exp_pos : 0 < ((m : ℝ) + 1) / c_Q := div_pos hm1_pos hc_pos
  have hk_ge_1 : (1 : ℝ) ≤ (kappa F : ℝ) := by exact_mod_cast hkappa_pos
  have h1 : (kappa F : ℝ) ^ (((m : ℝ) + 1) / c_Q) <
      (w₀ ^ (c_Q / ((m : ℝ) + 1))) ^ (((m : ℝ) + 1) / c_Q) :=
    Real.rpow_lt_rpow (by positivity) hkappa h_exp_pos
  have h_rhs : (w₀ ^ (c_Q / ((m : ℝ) + 1))) ^ (((m : ℝ) + 1) / c_Q) = w₀ := by
    rw [← Real.rpow_mul (by linarith)]
    have h_mul : (c_Q / ((m : ℝ) + 1)) * (((m : ℝ) + 1) / c_Q) = 1 := by
      field_simp [ne_of_gt hc_pos, ne_of_gt hm1_pos]
    rw [h_mul, Real.rpow_one]
  rw [h_rhs] at h1
  have h_exp_le : (m : ℝ) + 1 / c_Q ≤ ((m : ℝ) + 1) / c_Q := by
    rw [add_div]
    have h_m : (m : ℝ) ≤ (m : ℝ) / c_Q := by
      rw [le_div_iff₀ hc_pos]
      have : (m : ℝ) * c_Q ≤ (m : ℝ) * 1 := mul_le_mul_of_nonneg_left hc_le (Nat.cast_nonneg m)
      linarith
    linarith
  have h2 : (kappa F : ℝ) ^ ((m : ℝ) + 1 / c_Q) ≤ (kappa F : ℝ) ^ (((m : ℝ) + 1) / c_Q) :=
    Real.rpow_le_rpow_of_exponent_le hk_ge_1 h_exp_le
  have h3 : (kappa F : ℝ) ^ m * (kappa F : ℝ) ^ (1 / c_Q) =
      (kappa F : ℝ) ^ ((m : ℝ) + 1 / c_Q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by positivity)]
  have h4 : 2 * hook4Tau F c_Q m =
      (2 : ℝ) ^ (m + 1) * ((kappa F : ℝ) ^ m * (kappa F : ℝ) ^ (1 / c_Q)) := by
    unfold hook4Tau
    rw [pow_succ', mul_pow]
    ring
  have h_lt_w₀ : (kappa F : ℝ) ^ m * (kappa F : ℝ) ^ (1 / c_Q) < w₀ := by linarith
  have h5 : (2 : ℝ) ^ (m + 1) * ((kappa F : ℝ) ^ m * (kappa F : ℝ) ^ (1 / c_Q)) <
      (2 : ℝ) ^ (m + 1) * w₀ :=
    mul_lt_mul_of_pos_left h_lt_w₀ (by positivity)
  linarith

/-- If $F$ is `(Hook4Graph Q S_Q)ᶜ`-free ($S_Q = \text{Set.univ}$), $(y_0 - y_1 - y_2 - y_3)$ is an
induced $P_4$ in $Fᶜ$ with $\{y_0, y_1, y_2\}$ complete in $F$ to $W$ and $y_3 \notin W$ anticomplete
in $F$ to $W$, then $Fᶜ[W]$ is induced-$Q$-free. -/
theorem isInducedSubgraphFree_Q_of_hook4Compl_free
    {V W_Q : Type*} [DecidableEq V]
    {F : SimpleGraph V} {Q : SimpleGraph W_Q} {S_Q : Set W_Q}
    (hF_hook : IsInducedSubgraphFree F (Hook4Graph Q S_Q)ᶜ)
    (hS_Q : ∀ x : W_Q, x ∈ S_Q)
    {W : Finset V} {y₀ y₁ y₂ y₃ : V}
    (hc01 : Fᶜ.Adj y₀ y₁) (hc12 : Fᶜ.Adj y₁ y₂) (hc23 : Fᶜ.Adj y₂ y₃)
    (ha02 : F.Adj y₀ y₂) (ha03 : F.Adj y₀ y₃) (ha13 : F.Adj y₁ y₃)
    (hy0W : ∀ w ∈ W, F.Adj y₀ w) (hy1W : ∀ w ∈ W, F.Adj y₁ w) (hy2W : ∀ w ∈ W, F.Adj y₂ w)
    (hy3_not_W : y₃ ∉ W) (hy3W : ∀ w ∈ W, ¬F.Adj y₃ w) :
    IsInducedSubgraphFree (Fᶜ.induce (W : Set V)) Q := by
  rintro ⟨g, hg⟩
  let u : Fin 4 → V := ![y₃, y₂, y₁, y₀]
  have hy0_not_W : y₀ ∉ W := fun h => F.loopless y₀ (hy0W y₀ h)
  have hy1_not_W : y₁ ∉ W := fun h => F.loopless y₁ (hy1W y₁ h)
  have hy2_not_W : y₂ ∉ W := fun h => F.loopless y₂ (hy2W y₂ h)
  have hu_not_W : ∀ i : Fin 4, u i ∉ W := by
    intro i; fin_cases i <;> assumption
  have hu_inj : Function.Injective u := by
    have hne01 := hc01.1
    have hne12 := hc12.1
    have hne23 := hc23.1
    have hne02 := F.ne_of_adj ha02
    have hne03 := F.ne_of_adj ha03
    have hne13 := F.ne_of_adj ha13
    intro i j hij
    fin_cases i <;> fin_cases j <;> dsimp [u] at hij ⊢ <;>
      first | rfl
            | exact False.elim (hne23 hij.symm) | exact False.elim (hne23 hij)
            | exact False.elim (hne13 hij.symm) | exact False.elim (hne13 hij)
            | exact False.elim (hne03 hij.symm) | exact False.elim (hne03 hij)
            | exact False.elim (hne12 hij.symm) | exact False.elim (hne12 hij)
            | exact False.elim (hne02 hij.symm) | exact False.elim (hne02 hij)
            | exact False.elim (hne01 hij.symm) | exact False.elim (hne01 hij)
  let f_fun : W_Q ⊕ Fin 4 → V := fun z =>
    match z with
    | Sum.inl x => (g x).1
    | Sum.inr i => u i
  have hf_inj : Function.Injective f_fun := by
    intro z₁ z₂ hz
    cases z₁ with
    | inl x₁ =>
      cases z₂ with
      | inl x₂ =>
        dsimp [f_fun] at hz
        exact congr_arg Sum.inl (g.injective (Subtype.ext hz))
      | inr i₂ =>
        dsimp [f_fun] at hz
        exact False.elim (hu_not_W i₂ (hz ▸ (g x₁).2))
    | inr i₁ =>
      cases z₂ with
      | inl x₂ =>
        dsimp [f_fun] at hz
        exact False.elim (hu_not_W i₁ (hz.symm ▸ (g x₂).2))
      | inr i₂ =>
        dsimp [f_fun] at hz
        exact congr_arg Sum.inr (hu_inj hz)
  refine hF_hook ⟨⟨f_fun, hf_inj⟩, ?_⟩
  ext z₁ z₂
  simp only [compl_adj, comap_adj, Function.Embedding.coeFn_mk]
  cases z₁ with
  | inl x₁ =>
    cases z₂ with
    | inl x₂ =>
      have h_q := (congr_arg (fun H => H.Adj x₁ x₂) hg).to_iff
      simp only [comap_adj, induce_adj, compl_adj, ne_eq, Subtype.ext_iff] at h_q
      simp only [Hook4Graph, f_fun, ne_eq, Sum.inl.injEq]
      by_cases hx : x₁ = x₂
      · subst hx; simp
      · have hne_g : (g x₁).1 ≠ (g x₂).1 := fun h => hx (g.injective (Subtype.ext h))
        simp only [hx, not_false_eq_true, true_and]
        exact ⟨fun hnQ => Classical.byContradiction (fun hnF => hnQ (h_q.mpr ⟨hne_g, hnF⟩)),
          fun hF hQ => (h_q.mp hQ).2 hF⟩
    | inr i₂ =>
      simp only [Hook4Graph, f_fun, reduceCtorEq, not_false_eq_true, true_and, hS_Q x₁, and_true]
      fin_cases i₂
      · exact iff_of_false (by simp) (fun h => hy3W (g x₁).1 (g x₁).2 (F.symm h))
      · exact iff_of_true (by simp) (F.symm (hy2W (g x₁).1 (g x₁).2))
      · exact iff_of_true (by simp) (F.symm (hy1W (g x₁).1 (g x₁).2))
      · exact iff_of_true (by simp) (F.symm (hy0W (g x₁).1 (g x₁).2))
  | inr i₁ =>
    cases z₂ with
    | inl x₂ =>
      simp only [Hook4Graph, f_fun, reduceCtorEq, not_false_eq_true, true_and, hS_Q x₂, and_true]
      fin_cases i₁
      · exact iff_of_false (by simp) (hy3W (g x₂).1 (g x₂).2)
      · exact iff_of_true (by simp) (hy2W (g x₂).1 (g x₂).2)
      · exact iff_of_true (by simp) (hy1W (g x₂).1 (g x₂).2)
      · exact iff_of_true (by simp) (hy0W (g x₂).1 (g x₂).2)
    | inr i₂ =>
      have hn01 : ¬F.Adj y₀ y₁ := hc01.2
      have hn10 : ¬F.Adj y₁ y₀ := fun h => hc01.2 (F.symm h)
      have hn12 : ¬F.Adj y₁ y₂ := hc12.2
      have hn21 : ¬F.Adj y₂ y₁ := fun h => hc12.2 (F.symm h)
      have hn23 : ¬F.Adj y₂ y₃ := hc23.2
      have hn32 : ¬F.Adj y₃ y₂ := fun h => hc23.2 (F.symm h)
      simp only [Hook4Graph, f_fun, ne_eq, Sum.inr.injEq, pathGraph_adj]
      fin_cases i₁ <;> fin_cases i₂ <;>
        simp [u, hn01, hn10, hn12, hn21, hn23, hn32, ha02, ha02.symm, ha03, ha03.symm, ha13, ha13.symm]

/--
**Proposition 6(2a) — Depth-$m$ Multi-Stem Defective Neighborhood Module Lemma (`hook4_defective_neighborhood_module`, lines 979, 1005–1010 of `main.tex`)**:
Let $Q$ satisfy `HasErdosHajnalProp` with exponent $c_Q \in (0, 1]$ and $S_Q = \text{Set.univ}$.
For any $m \ge 0$ ($t = 6 + m \ge 6$), in any `{(pathGraph (6 + m))ᶜ, (Hook4Graph Q S_Q)ᶜ}`-free
graph $F$ containing an $(\ell, w)$-comb $(a, B)$ with external apex $v$, for any $i \neq j$,
any $M \subseteq B_i$, and any $u \in B_j$ not complete to $M$ in $F$, if $\kappa(F) < w_0^{c_Q / (m + 1)}$
($w_0 \ge 1$), then every anticonnected component $C_s$ of $F[N_F(u) \cap M]$ with
$|C_s| \ge 2^{m+1} w_0$ is a proper module of $F[M]$.
-/
theorem hook4_defective_neighborhood_module
    {V W_Q : Type} [Fintype V] [DecidableEq V] [Fintype W_Q] [DecidableEq W_Q]
    {F : SimpleGraph V} {Q : SimpleGraph W_Q} {S_Q : Set W_Q}
    {c_Q w₀ w : ℝ} {m ℓ : ℕ} {S_amb : Finset V}
    {a : Fin ℓ → V} {B : Fin ℓ → Finset V} {v : V}
    (hc_pos : 0 < c_Q) (hc_le : c_Q ≤ 1)
    (hEH_Q : ∀ (U : Type) [Fintype U] [DecidableEq U] (H : SimpleGraph U),
      IsInducedSubgraphFree H Q → (Fintype.card U : ℝ) ^ c_Q ≤ (kappa H : ℝ))
    (hS_Q : ∀ x : W_Q, x ∈ S_Q)
    (hF_path : IsInducedSubgraphFree F (pathGraph (6 + m))ᶜ)
    (hF_hook : IsInducedSubgraphFree F (Hook4Graph Q S_Q)ᶜ)
    (hcomb : IsCombIn F S_amb ℓ w a B)
    (hapex : IsCombExternalApex F S_amb ℓ a B v)
    {i j : Fin ℓ} (hij : i ≠ j)
    {M : Finset V} (hMB : M ⊆ B i)
    {u : V} (hu : u ∈ B j) (hnotcomp : ∃ w_non ∈ M, ¬F.Adj u w_non)
    (hw₀ : 1 ≤ w₀)
    (hkappa : (kappa F : ℝ) < w₀ ^ (c_Q / ((m : ℝ) + 1)))
    {C_s : Finset V} (hCs : IsAnticonnectedComponentOf F (neighborFinsetIn F u M) C_s)
    (hCs_card : (2 : ℝ) ^ (m + 1) * w₀ ≤ (C_s.card : ℝ)) :
    IsProperModuleIn F M C_s := by
  classical
  have hCs_Z : C_s ⊆ neighborFinsetIn F u M := hCs.1
  have hZM : neighborFinsetIn F u M ⊆ M := neighborFinsetIn_subset F u M
  have hCs_M : C_s ⊆ M := hCs_Z.trans hZM
  have hCs_B : C_s ⊆ B i := hCs_M.trans hMB
  have huCs : ∀ x ∈ C_s, F.Adj u x := fun x hx =>
    ((mem_neighborFinsetIn_iff F u M x).mp (hCs_Z hx)).2
  haveI : Nonempty V := by
    obtain ⟨x₀, _⟩ := hCs.nonempty
    exact ⟨x₀⟩
  have hkappa_pos : 1 ≤ kappa F := kappa_pos_of_nonempty F
  refine ⟨hCs.nonempty, ?_, hCs_M, ?_⟩
  · rw [Finset.ssubset_iff_of_subset hCs_M]
    rcases hnotcomp with ⟨w_non, hw_nonM, huw_non⟩
    exact ⟨w_non, hw_nonM, fun h_in => huw_non (huCs w_non h_in)⟩
  · intro z hzM hzCs
    by_cases huz : F.Adj u z
    · have hzZ : z ∈ neighborFinsetIn F u M := (mem_neighborFinsetIn_iff F u M z).mpr ⟨hzM, huz⟩
      left
      intro x hxCs
      exact F.symm (hCs.2.2 x hxCs z hzZ hzCs)
    · by_contra hnotpure
      rw [not_isVertexPureTo_iff_isVertexMixedOn] at hnotpure
      have h_tau_m : 2 * hook4Tau F c_Q m < (C_s.card : ℝ) :=
        two_mul_hook4Tau_lt_of_kappa_lt F hc_pos hc_le hw₀ hkappa_pos hkappa hCs_card
      -- Inductive construction of the (q+4)-stem y and anticonnected residual D^(q)
      have h_ind : ∀ q : ℕ, q ≤ m →
          ∃ (y : Fin (q + 4) → V) (D : Finset V),
            D ⊆ C_s ∧
            (∀ p₁ p₂ : Fin (q + 4), p₁.1 + 1 = p₂.1 → Fᶜ.Adj (y p₁) (y p₂)) ∧
            (∀ p₁ p₂ : Fin (q + 4), p₁.1 + 1 < p₂.1 → F.Adj (y p₁) (y p₂)) ∧
            IsAnticonnected F D ∧
            2 * hook4Tau F c_Q (m - q) < (D.card : ℝ) ∧
            (∀ p : Fin (q + 4), p.1 < q + 3 → y p ∉ D ∧ ∀ x ∈ D, F.Adj (y p) x) ∧
            y ⟨q + 3, by omega⟩ ∉ D ∧
            IsVertexMixedOn F (y ⟨q + 3, by omega⟩) D := by
        intro q
        induction q with
        | zero =>
          intro _
          let y₀ : Fin 4 → V := ![v, a i, u, z]
          have hne01 : v ≠ a i := hapex.not_apex i
          have hn01 : ¬F.Adj v (a i) := hapex.anticomplete_to_apices i
          have hne12 : a i ≠ u := fun h => hcomb.apex_disjoint_blocks i j (h ▸ hu)
          have hn12 : ¬F.Adj (a i) u := hcomb.apex_anticomplete_other i j hij u hu
          have hne23 : u ≠ z := fun h =>
            Finset.disjoint_left.mp (hcomb.is_blockade.pairwise_disjoint j i hij.symm) hu (h ▸ hMB hzM)
          have ha02 : F.Adj v u := hapex.complete_to_blocks j u hu
          have ha03 : F.Adj v z := hapex.complete_to_blocks i z (hMB hzM)
          have ha13 : F.Adj (a i) z := hcomb.apex_complete_own i z (hMB hzM)
          refine ⟨y₀, C_s, Finset.Subset.rfl, ?_, ?_, hCs.2.1, ?_, ?_, hzCs, hnotpure⟩
          · intro p₁ p₂ hp
            fin_cases p₁ <;> fin_cases p₂ <;> dsimp at hp <;> try omega
            · exact ⟨hne01, hn01⟩
            · exact ⟨hne12, hn12⟩
            · exact ⟨hne23, huz⟩
          · intro p₁ p₂ hp
            fin_cases p₁ <;> fin_cases p₂ <;> dsimp at hp <;> try omega
            · exact ha02
            · exact ha03
            · exact ha13
          · simpa using h_tau_m
          · intro p hp
            fin_cases p <;> dsimp at hp <;> try omega
            · exact ⟨fun h => hapex.not_in_blocks i (hCs_B h),
                fun x hx => hapex.complete_to_blocks i x (hCs_B hx)⟩
            · exact ⟨fun h => hcomb.apex_disjoint_blocks i i (hCs_B h),
                fun x hx => hcomb.apex_complete_own i x (hCs_B hx)⟩
            · exact ⟨fun h => Finset.disjoint_left.mp
                (hcomb.is_blockade.pairwise_disjoint j i hij.symm) hu (hCs_B h), huCs⟩
        | succ q ih =>
          intro hq_le
          obtain ⟨y, D, hD_sub, hy_consec, hy_nonconsec, hD_ac, hD_card, hy_init, hy_last_not, hy_last_mix⟩ :=
            ih (by omega)
          let y_last := y ⟨q + 3, by omega⟩
          let W := neighborFinsetIn Fᶜ y_last D
          let Z := neighborFinsetIn F y_last D
          have hW_sub : W ⊆ D := neighborFinsetIn_subset Fᶜ y_last D
          have hZ_sub : Z ⊆ D := neighborFinsetIn_subset F y_last D
          have hWZ_disj : Disjoint W Z := by
            rw [Finset.disjoint_left]
            intro x hxW hxZ
            have h1 := ((mem_neighborFinsetIn_iff Fᶜ y_last D x).mp hxW).2
            have h2 := ((mem_neighborFinsetIn_iff F y_last D x).mp hxZ).2
            exact h1.2 h2
          have hWZ_union : W ∪ Z = D := by
            ext x
            simp only [Finset.mem_union, W, Z, mem_neighborFinsetIn_iff, compl_adj]
            constructor
            · rintro (⟨hxD, _⟩ | ⟨hxD, _⟩) <;> exact hxD
            · intro hxD
              by_cases hadj : F.Adj y_last x
              · exact Or.inr ⟨hxD, hadj⟩
              · have hne : y_last ≠ x := fun h => by subst h; exact hy_last_not hxD
                exact Or.inl ⟨hxD, hne, hadj⟩
          have hWZ_cards : (W.card : ℝ) + (Z.card : ℝ) = (D.card : ℝ) := by
            exact_mod_cast (Finset.card_union_of_disjoint hWZ_disj).symm.trans (congr_arg Finset.card hWZ_union)
          obtain ⟨⟨w_pos, hw_posD, hw_pos_adj⟩, ⟨w_neg, hw_negD, hw_neg_nadj⟩⟩ := hy_last_mix
          have hW_ne : W.Nonempty := ⟨w_neg, (mem_neighborFinsetIn_iff Fᶜ y_last D w_neg).mpr
            ⟨hw_negD, fun h => by subst h; exact hy_last_not hw_negD, hw_neg_nadj⟩⟩
          -- Bound |W| ≤ tau 0 via Hook4(Q)-freeness
          have hW_free : IsInducedSubgraphFree (Fᶜ.induce (W : Set V)) Q := by
            refine isInducedSubgraphFree_Q_of_hook4Compl_free hF_hook hS_Q
              (hy_consec ⟨q, by omega⟩ ⟨q + 1, by omega⟩ rfl)
              (hy_consec ⟨q + 1, by omega⟩ ⟨q + 2, by omega⟩ rfl)
              (hy_consec ⟨q + 2, by omega⟩ ⟨q + 3, by omega⟩ rfl)
              (hy_nonconsec ⟨q, by omega⟩ ⟨q + 2, by omega⟩ (by dsimp; omega))
              (hy_nonconsec ⟨q, by omega⟩ ⟨q + 3, by omega⟩ (by dsimp; omega))
              (hy_nonconsec ⟨q + 1, by omega⟩ ⟨q + 3, by omega⟩ (by dsimp; omega))
              (fun w hw => (hy_init ⟨q, by omega⟩ (by dsimp; omega)).2 w (hW_sub hw))
              (fun w hw => (hy_init ⟨q + 1, by omega⟩ (by dsimp; omega)).2 w (hW_sub hw))
              (fun w hw => (hy_init ⟨q + 2, by omega⟩ (by dsimp; omega)).2 w (hW_sub hw))
              (fun h => hy_last_not (hW_sub h))
              (fun w hw => ((mem_neighborFinsetIn_iff Fᶜ y_last D w).mp hw).2.2)
          have h_eh_W := hEH_Q ↥W (Fᶜ.induce (W : Set V)) hW_free
          rw [Fintype.card_coe] at h_eh_W
          have h_kappa_W : (kappa (Fᶜ.induce (W : Set V)) : ℝ) ≤ (kappa F : ℝ) := by
            have h1 : Fᶜ.induce (W : Set V) = (F.induce (W : Set V))ᶜ := by
              ext x y; simp only [induce_adj, compl_adj, ne_eq, Subtype.ext_iff]
            rw [h1, kappa_compl]
            exact_mod_cast induce_kappa_le F W
          have hW_cQ : (W.card : ℝ) ^ c_Q ≤ (kappa F : ℝ) := h_eh_W.trans h_kappa_W
          have hW_le_tau0 : (W.card : ℝ) ≤ hook4Tau F c_Q 0 := by
            unfold hook4Tau
            rw [pow_zero, one_mul]
            have h1 := Real.rpow_le_rpow (by positivity) hW_cQ (show (0 : ℝ) ≤ 1 / c_Q by positivity)
            rwa [← Real.rpow_mul (Nat.cast_nonneg _), mul_one_div_cancel (ne_of_gt hc_pos), Real.rpow_one] at h1
          have hW_le_tau_mq : (W.card : ℝ) ≤ hook4Tau F c_Q (m - q) :=
            hW_le_tau0.trans (hook4Tau_zero_le F (m - q) hkappa_pos)
          have h_mq_eq : m - q = (m - (q + 1)) + 1 := by omega
          have hZ_gt : 2 * (kappa F : ℝ) * hook4Tau F c_Q (m - (q + 1)) < (Z.card : ℝ) := by
            have h_succ : hook4Tau F c_Q (m - q) = 2 * (kappa F : ℝ) * hook4Tau F c_Q (m - (q + 1)) := by
              rw [h_mq_eq, hook4Tau_succ]
            linarith
          -- Partition Z into anticonnected components E_1, ..., E_p
          obtain ⟨p, E, hE_fam⟩ := exists_anticonnectedComponentFamily F Z
          have hp_le_kappa : (p : ℝ) ≤ (kappa F : ℝ) := by
            have hp_cliq : p ≤ F.cliqueNum :=
              (hE_fam.isCompleteBlockadeIn (Subset.refl Z)).length_le_cliqueNum
            have h_cliq_k : F.cliqueNum ≤ kappa F := cliqueNum_le_kappa F
            exact_mod_cast hp_cliq.trans h_cliq_k
          have hE_sum : ∑ a_idx : Fin p, ((E a_idx).card : ℝ) = (Z.card : ℝ) := by
            exact_mod_cast hE_fam.sum_card_eq
          have h_ex_E : ∃ a_star : Fin p, 2 * hook4Tau F c_Q (m - (q + 1)) < ((E a_star).card : ℝ) := by
            by_contra! hall_le
            have h_sum_le : ∑ a_idx : Fin p, ((E a_idx).card : ℝ) ≤
                (p : ℝ) * (2 * hook4Tau F c_Q (m - (q + 1))) := by
              calc ∑ a_idx : Fin p, ((E a_idx).card : ℝ)
                  ≤ ∑ _a_idx : Fin p, (2 * hook4Tau F c_Q (m - (q + 1))) :=
                    Finset.sum_le_sum (fun a_idx _ => hall_le a_idx)
                _ = (p : ℝ) * (2 * hook4Tau F c_Q (m - (q + 1))) := by
                    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            have h_tau_nonneg : 0 ≤ 2 * hook4Tau F c_Q (m - (q + 1)) := by
              unfold hook4Tau; positivity
            have h_pk : (p : ℝ) * (2 * hook4Tau F c_Q (m - (q + 1))) ≤
                (kappa F : ℝ) * (2 * hook4Tau F c_Q (m - (q + 1))) :=
              mul_le_mul_of_nonneg_right hp_le_kappa h_tau_nonneg
            linarith
          obtain ⟨a_star, ha_star⟩ := h_ex_E
          let D' := E a_star
          have hD'_Z : D' ⊆ Z := (hE_fam.is_component a_star).1
          have hD'_D : D' ⊆ D := hD'_Z.trans hZ_sub
          have hD'_ac : IsAnticonnected F D' := (hE_fam.is_component a_star).2.1
          -- Extract y_{q+4} ∈ W with an Fᶜ-edge into D' ⊆ D \ W = Z
          have hD_sdiff_W : D \ W = Z := by
            rw [← hWZ_union, Finset.union_sdiff_cancel_left hWZ_disj]
          have hD'_comp_sdiff : IsAnticonnectedComponentOf F (D \ W) D' := by
            rw [hD_sdiff_W]
            exact hE_fam.is_component a_star
          obtain ⟨y_next, hy_nextW, w_in_D', hw_in_D', h_ynext_w_compl⟩ :=
            anticonnected_component_sdiff_exists_compl_adj hD_ac hW_sub hW_ne hD'_comp_sdiff
          have hy_next_not_D' : y_next ∉ D' := fun h =>
            Finset.disjoint_left.mp hWZ_disj hy_nextW (hD'_Z h)
          -- Show y_next is mixed on D' via Hook4(Q)-freeness on shifted suffix
          have hy_next_mix : IsVertexMixedOn F y_next D' := by
            refine ⟨?_, ⟨w_in_D', hw_in_D', h_ynext_w_compl.2⟩⟩
            by_contra! h_no_adj
            have hc_last_next : Fᶜ.Adj y_last y_next :=
              ((mem_neighborFinsetIn_iff Fᶜ y_last D y_next).mp hy_nextW).2
            have ha_q1_next : F.Adj (y ⟨q + 1, by omega⟩) y_next :=
              (hy_init ⟨q + 1, by omega⟩ (by dsimp; omega)).2 y_next (hW_sub hy_nextW)
            have ha_q2_next : F.Adj (y ⟨q + 2, by omega⟩) y_next :=
              (hy_init ⟨q + 2, by omega⟩ (by dsimp; omega)).2 y_next (hW_sub hy_nextW)
            have hD'_free : IsInducedSubgraphFree (Fᶜ.induce (D' : Set V)) Q := by
              refine isInducedSubgraphFree_Q_of_hook4Compl_free hF_hook hS_Q
                (hy_consec ⟨q + 1, by omega⟩ ⟨q + 2, by omega⟩ rfl)
                (hy_consec ⟨q + 2, by omega⟩ ⟨q + 3, by omega⟩ rfl)
                hc_last_next
                (hy_nonconsec ⟨q + 1, by omega⟩ ⟨q + 3, by omega⟩ (by dsimp; omega))
                ha_q1_next
                ha_q2_next
                (fun w hw => (hy_init ⟨q + 1, by omega⟩ (by dsimp; omega)).2 w (hD'_D hw))
                (fun w hw => (hy_init ⟨q + 2, by omega⟩ (by dsimp; omega)).2 w (hD'_D hw))
                (fun w hw => ((mem_neighborFinsetIn_iff F y_last D w).mp (hD'_Z hw)).2)
                hy_next_not_D'
                h_no_adj
            have h_eh_D' := hEH_Q ↥D' (Fᶜ.induce (D' : Set V)) hD'_free
            rw [Fintype.card_coe] at h_eh_D'
            have h_kappa_D' : (kappa (Fᶜ.induce (D' : Set V)) : ℝ) ≤ (kappa F : ℝ) := by
              have h1 : Fᶜ.induce (D' : Set V) = (F.induce (D' : Set V))ᶜ := by
                ext x y; simp only [induce_adj, compl_adj, ne_eq, Subtype.ext_iff]
              rw [h1, kappa_compl]
              exact_mod_cast induce_kappa_le F D'
            have hD'_cQ : (D'.card : ℝ) ^ c_Q ≤ (kappa F : ℝ) := h_eh_D'.trans h_kappa_D'
            have hD'_le_tau0 : (D'.card : ℝ) ≤ hook4Tau F c_Q 0 := by
              unfold hook4Tau
              rw [pow_zero, one_mul]
              have h1 := Real.rpow_le_rpow (by positivity) hD'_cQ (show (0 : ℝ) ≤ 1 / c_Q by positivity)
              rwa [← Real.rpow_mul (Nat.cast_nonneg _), mul_one_div_cancel (ne_of_gt hc_pos), Real.rpow_one] at h1
            have hD'_le_tau : (D'.card : ℝ) ≤ hook4Tau F c_Q (m - (q + 1)) :=
              hD'_le_tau0.trans (hook4Tau_zero_le F (m - (q + 1)) hkappa_pos)
            have h_tau_nonneg : 0 ≤ hook4Tau F c_Q (m - (q + 1)) := by
              unfold hook4Tau; positivity
            linarith
          let y' : Fin (q + 1 + 4) → V := fun p =>
            if hp : p.1 < q + 4 then y ⟨p.1, hp⟩ else y_next
          refine ⟨y', D', hD'_D.trans hD_sub, ?_, ?_, hD'_ac, ha_star, ?_, ?_, ?_⟩
          · intro p₁ p₂ hp
            dsimp only [y']
            by_cases hp₂ : p₂.1 < q + 4
            · have hp₁ : p₁.1 < q + 4 := by omega
              rw [dif_pos hp₁, dif_pos hp₂]
              exact hy_consec ⟨p₁.1, hp₁⟩ ⟨p₂.1, hp₂⟩ hp
            · have hp₂_eq : p₂.1 = q + 4 := by omega
              have hp₁ : p₁.1 < q + 4 := by omega
              have hp₁_eq : (⟨p₁.1, hp₁⟩ : Fin (q + 4)) = ⟨q + 3, by omega⟩ := by ext; dsimp; omega
              rw [dif_pos hp₁, dif_neg hp₂, hp₁_eq]
              exact ((mem_neighborFinsetIn_iff Fᶜ y_last D y_next).mp hy_nextW).2
          · intro p₁ p₂ hp
            dsimp only [y']
            by_cases hp₂ : p₂.1 < q + 4
            · have hp₁ : p₁.1 < q + 4 := by omega
              rw [dif_pos hp₁, dif_pos hp₂]
              exact hy_nonconsec ⟨p₁.1, hp₁⟩ ⟨p₂.1, hp₂⟩ hp
            · have hp₁ : p₁.1 < q + 4 := by omega
              have hp₁_lt : p₁.1 < q + 3 := by omega
              rw [dif_pos hp₁, dif_neg hp₂]
              exact (hy_init ⟨p₁.1, hp₁⟩ hp₁_lt).2 y_next (hW_sub hy_nextW)
          · intro p hp
            dsimp only [y']
            have hp_lt4 : p.1 < q + 4 := by omega
            rw [dif_pos hp_lt4]
            by_cases hp_lt3 : p.1 < q + 3
            · obtain ⟨hn_in, h_adj_all⟩ := hy_init ⟨p.1, hp_lt4⟩ hp_lt3
              exact ⟨fun h => hn_in (hD'_D h), fun x hx => h_adj_all x (hD'_D hx)⟩
            · have hp_eq : (⟨p.1, hp_lt4⟩ : Fin (q + 4)) = ⟨q + 3, by omega⟩ := by ext; dsimp; omega
              rw [hp_eq]
              exact ⟨fun h => hy_last_not (hD'_D h),
                fun x hx => ((mem_neighborFinsetIn_iff F y_last D x).mp (hD'_Z hx)).2⟩
          · dsimp only [y']
            have h_not : ¬(q + 1 + 3 < q + 4) := by omega
            rw [dif_neg h_not]
            exact hy_next_not_D'
          · dsimp only [y']
            have h_not : ¬(q + 1 + 3 < q + 4) := by omega
            rw [dif_neg h_not]
            exact hy_next_mix
      -- Apply at q = m and attach the final anticonnected edge (x₁, x₂) in D^(m)
      obtain ⟨y, D_m, _, hy_consec, hy_nonconsec, hDm_ac, _, hy_init, hy_last_not, hy_last_mix⟩ :=
        h_ind m le_rfl
      obtain ⟨x₁, hx₁D, x₂, hx₂D, hx₁₂_ne, hx₁₂_nadj, h_ylast_x₁, h_ylast_x₂⟩ :=
        hy_last_mix.exists_anticonnected_edge hDm_ac
      let f_path : Fin (6 + m) → V := fun p =>
        if hp : p.1 < m + 4 then y ⟨p.1, hp⟩
        else if p.1 = m + 4 then x₁
        else x₂
      refine hF_path (exists_pathGraph_compl_embedding F f_path ?_ ?_)
      · intro p₁ p₂ hp
        dsimp only [f_path]
        by_cases hp₂ : p₂.1 < m + 4
        · have hp₁ : p₁.1 < m + 4 := by omega
          rw [dif_pos hp₁, dif_pos hp₂]
          exact hy_consec ⟨p₁.1, hp₁⟩ ⟨p₂.1, hp₂⟩ hp
        · by_cases hp₂_eq : p₂.1 = m + 4
          · have hp₁ : p₁.1 < m + 4 := by omega
            have hp₁_eq : (⟨p₁.1, hp₁⟩ : Fin (m + 4)) = ⟨m + 3, by omega⟩ := by ext; dsimp; omega
            rw [dif_pos hp₁, dif_neg hp₂, if_pos hp₂_eq, hp₁_eq]
            exact ⟨fun h => hy_last_not (h ▸ hx₁D), h_ylast_x₁⟩
          · have hp₂_5 : p₂.1 = m + 5 := by omega
            have hp₁_not : ¬(p₁.1 < m + 4) := by omega
            have hp₁_4 : p₁.1 = m + 4 := by omega
            rw [dif_neg hp₁_not, if_pos hp₁_4, dif_neg hp₂, if_neg hp₂_eq]
            exact ⟨hx₁₂_ne, hx₁₂_nadj⟩
      · intro p₁ p₂ hp
        dsimp only [f_path]
        by_cases hp₂ : p₂.1 < m + 4
        · have hp₁ : p₁.1 < m + 4 := by omega
          rw [dif_pos hp₁, dif_pos hp₂]
          exact hy_nonconsec ⟨p₁.1, hp₁⟩ ⟨p₂.1, hp₂⟩ hp
        · by_cases hp₂_eq : p₂.1 = m + 4
          · have hp₁ : p₁.1 < m + 4 := by omega
            have hp₁_lt : p₁.1 < m + 3 := by omega
            rw [dif_pos hp₁, dif_neg hp₂, if_pos hp₂_eq]
            exact (hy_init ⟨p₁.1, hp₁⟩ hp₁_lt).2 x₁ hx₁D
          · have hp₂_5 : p₂.1 = m + 5 := by omega
            have hp₁ : p₁.1 < m + 4 := by omega
            rw [dif_pos hp₁, dif_neg hp₂, if_neg hp₂_eq]
            by_cases hp₁_lt : p₁.1 < m + 3
            · exact (hy_init ⟨p₁.1, hp₁⟩ hp₁_lt).2 x₂ hx₂D
            · have hp₁_eq : (⟨p₁.1, hp₁⟩ : Fin (m + 4)) = ⟨m + 3, by omega⟩ := by ext; dsimp; omega
              rw [hp₁_eq]
              exact h_ylast_x₂

/-- Local splitting dichotomy for `{P_{6+m}, Hook_4(Q)}` using `hook4_defective_neighborhood_module`. -/
theorem hook4_local_splitting_dichotomy
    {V W_Q : Type} [Fintype V] [DecidableEq V] [Fintype W_Q] [DecidableEq W_Q]
    {F : SimpleGraph V} {Q : SimpleGraph W_Q} {S_Q : Set W_Q}
    {c_Q w₀ w θ : ℝ} {m ℓ K₀ : ℕ} {S_amb : Finset V}
    {a : Fin ℓ → V} {B : Fin ℓ → Finset V} {v : V} {i : Fin ℓ}
    (hc_pos : 0 < c_Q) (hc_le : c_Q ≤ 1)
    (hEH_Q : ∀ (U : Type) [Fintype U] [DecidableEq U] (H : SimpleGraph U),
      IsInducedSubgraphFree H Q → (Fintype.card U : ℝ) ^ c_Q ≤ (kappa H : ℝ))
    (hS_Q : ∀ x : W_Q, x ∈ S_Q)
    (hF_path : IsInducedSubgraphFree F (pathGraph (6 + m))ᶜ)
    (hF_hook : IsInducedSubgraphFree F (Hook4Graph Q S_Q)ᶜ)
    (hcomb : IsCombIn F S_amb ℓ w a B)
    (hapex : IsCombExternalApex F S_amb ℓ a B v)
    (hw₀ : 1 ≤ w₀)
    (hkappa : (kappa F : ℝ) < w₀ ^ (c_Q / ((m : ℝ) + 1)))
    (hθ_pos : 0 < θ) (hK₀_ge : 4 ≤ K₀) (hK₀_gt : θ⁻¹ < (K₀ : ℝ) + 1)
    {W : Finset V} (hWB : W ⊆ B i) (hW_card : 64 ≤ W.card)
    (hw₀_bound : (2 : ℝ) ^ (m + 1) * w₀ ≤ θ * ((W.card : ℝ) / 4)) :
    (∃ M_star ⊆ W, (W.card : ℝ) / 4 ≤ (M_star.card : ℝ) ∧
      IsSmallAttachmentCore F B i θ M_star) ∨
    (∃ (k : ℕ) (U : Fin k → Finset V),
      2 ≤ k ∧ k ≤ K₀ ∧
      IsPureBlockadeIn F W k ((W.card : ℝ) / (64 * (k : ℝ) ^ 2)) U ∧
      (W.card : ℝ) ^ (1 / 8 : ℝ) ≤ ∑ j : Fin k, ((U j).card : ℝ) ^ (1 / 8 : ℝ)) := by
  classical
  have h_chain := greedy_module_chain_aux F hW_card W.card W ∅ ∅ le_rfl Finset.Subset.rfl
    (by simp) (by simp) (by simp) (by simp) (by simp)
  rcases h_chain with ⟨U, hU⟩ | ⟨M_s, hMs_W, hMs_gt, hmMax_lt⟩
  · right
    exact ⟨2, U, le_rfl, by omega, hU, potential_conservation_of_width le_rfl hU.1.width_ge⟩
  · have hW_r : (64 : ℝ) ≤ (W.card : ℝ) := Nat.ofNat_le_cast.mpr hW_card
    have hMs_ne : M_s.Nonempty := by
      rw [← Finset.card_pos, ← @Nat.cast_pos ℝ]
      linarith
    have hMs_B : M_s ⊆ B i := hMs_W.trans hWB
    by_cases hmMax_θ : (mMax F M_s : ℝ) ≤ θ * (M_s.card : ℝ)
    · left
      refine ⟨M_s, hMs_W, by linarith, hMs_B, hMs_ne, ?_⟩
      intro r hri u huB hu_not_comp
      have hnotcomp_ex : ∃ w_non ∈ M_s, ¬F.Adj u w_non := by
        by_contra! hall
        exact hu_not_comp hall
      obtain ⟨C_fam, hC_prop, hC_pair, hC_union⟩ :=
        exists_anticonnected_components_finset_aux F (neighborFinsetIn F u M_s).card
          (neighborFinsetIn F u M_s) le_rfl
      obtain ⟨q, C, _, hC_inj, _, hC_mem, hC_surj, hC_mono⟩ := exists_sorted_equiv_of_finset C_fam
      have hC_disj_comp : ∀ s t : Fin q, s ≠ t → Disjoint (C s) (C t) ∧ IsCompletePair F (C s) (C t) :=
        fun s t hst => hC_pair (C s) (hC_mem s) (C t) (hC_mem t) (fun h => hst (hC_inj h))
      have hC_biUnion : Finset.univ.biUnion C = neighborFinsetIn F u M_s := by
        rw [← hC_union]
        ext x
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, id_eq]
        exact ⟨fun ⟨s, hx⟩ => ⟨C s, hC_mem s, hx⟩,
          fun ⟨A, hA, hx⟩ => let ⟨s, hs⟩ := hC_surj A hA; ⟨s, hs ▸ hx⟩⟩
      have hC_sum : ∑ s : Fin q, (C s).card = (neighborFinsetIn F u M_s).card := by
        rw [← hC_biUnion, Finset.card_biUnion (fun s _ t _ hst => (hC_disj_comp s t hst).1)]
      refine ⟨q, C, fun s => hC_prop (C s) (hC_mem s), hC_disj_comp, hC_biUnion, hC_sum, hC_mono, fun s => ?_⟩
      by_cases hCs_small : ((C s).card : ℝ) < (2 : ℝ) ^ (m + 1) * w₀
      · have hMs_ge_W4 : (W.card : ℝ) / 4 ≤ (M_s.card : ℝ) := by linarith
        have h1 : θ * ((W.card : ℝ) / 4) ≤ θ * (M_s.card : ℝ) :=
          mul_le_mul_of_nonneg_left hMs_ge_W4 (le_of_lt hθ_pos)
        linarith
      · push_neg at hCs_small
        have hCs_comp : IsAnticonnectedComponentOf F (neighborFinsetIn F u M_s) (C s) := by
          obtain ⟨hsub, _, hac⟩ := hC_prop (C s) (hC_mem s)
          refine ⟨hsub, hac, fun x hx y hyZ hyC => ?_⟩
          rw [← hC_biUnion, Finset.mem_biUnion] at hyZ
          obtain ⟨t, _, hyt⟩ := hyZ
          have hst : s ≠ t := fun h => hyC (h ▸ hyt)
          exact (hC_disj_comp s t hst).2 x hx y hyt
        have hCs_mod := hook4_defective_neighborhood_module hc_pos hc_le hEH_Q hS_Q hF_path hF_hook
          hcomb hapex hri.symm hMs_B huB hnotcomp_ex hw₀ hkappa hCs_comp hCs_small
        have hle := card_le_mMax_of_isProperModuleIn hCs_mod
        exact le_trans (Nat.cast_le.mpr hle) hmMax_θ
    · push_neg at hmMax_θ
      have hMs_card2 : 2 ≤ M_s.card := by
        exact_mod_cast (by linarith : (2 : ℝ) ≤ (M_s.card : ℝ))
      have hmMax_2 : 2 * mMax F M_s < M_s.card := by
        exact_mod_cast (by linarith : (2 : ℝ) * (mMax F M_s : ℝ) < (M_s.card : ℝ))
      obtain ⟨hconn, haconn⟩ := connected_and_anticonnected_of_two_mul_mMax_lt hMs_card2 hmMax_2
      obtain ⟨t, P, hP_max, hP_pure, hP_biUnion, hP_sum, hP_mono, hP_sup⟩ :=
        gallai_prime_partition hMs_card2 hconn haconn
      have hP_lt_64 : ∀ j : Fin t, ((P j).card : ℝ) < (W.card : ℝ) / 64 := by
        intro j
        have hle : (P j).card ≤ mMax F M_s := card_le_mMax_of_isProperModuleIn (hP_max j).1
        have hle_r : ((P j).card : ℝ) ≤ (mMax F M_s : ℝ) := Nat.cast_le.mpr hle
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
            simp only [Fin.mk_le_mk]; omega
          have h_mono := Nat.cast_le (α := ℝ).mpr (hP_mono ⟨j.1, by omega⟩ ⟨k - 1, by omega⟩ hj_le)
          exact le_trans hk_width h_mono
        have hU_pure : IsPureBlockadeIn F W k ((W.card : ℝ) / (64 * (k : ℝ) ^ 2)) U := by
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
            rw [hj0]; norm_num; linarith
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
          simp only [I_head, I_tail, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
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
              simp only [Finset.mem_Icc]; omega
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
          push_cast; rfl
        have h_total_sum : ∑ j ∈ I_head, ((P j).card : ℝ) + ∑ j ∈ I_tail, ((P j).card : ℝ) =
            (M_s.card : ℝ) := by
          rw [← Finset.sum_union hI_disj, hI_union]
          exact_mod_cast hP_sum
        have hM_star_gt : (W.card : ℝ) / 4 < (M_star.card : ℝ) := by linarith
        have hM_star_ne : M_star.Nonempty := by
          rw [← Finset.card_pos, ← @Nat.cast_pos ℝ]; linarith
        have h_tail_le_θ : ∀ j : Fin t, K₀ ≤ j.1 → ((P j).card : ℝ) ≤ θ * (M_star.card : ℝ) := by
          intro j hjK₀
          have hk_min : 2 ≤ K₀ ∧ K₀ ≤ min t K₀ := by
            obtain ⟨x, hx⟩ := hM_star_ne
            obtain ⟨j', hj', _⟩ := Finset.mem_biUnion.mp hx
            have hj'' := (Finset.mem_filter.mp hj').2
            exact ⟨by omega, by omega⟩
          have h_K₀ := h_split K₀ hk_min
          have hj_ge : (⟨K₀ - 1, by omega⟩ : Fin t) ≤ j := by rw [Fin.le_def]; dsimp; omega
          have h_mono : ((P j).card : ℝ) ≤ ((P ⟨K₀ - 1, by omega⟩).card : ℝ) :=
            Nat.cast_le.mpr (hP_mono _ _ hj_ge)
          have hK₀_r : (4 : ℝ) ≤ (K₀ : ℝ) := Nat.ofNat_le_cast.mpr hK₀_ge
          have h_inv_le : (K₀ : ℝ) + 1 ≤ 16 * (K₀ : ℝ) ^ 2 := by nlinarith
          have hθ_inv_lt : θ⁻¹ < 16 * (K₀ : ℝ) ^ 2 := lt_of_lt_of_le hK₀_gt h_inv_le
          have h_16K₀_le_θ : 1 / (16 * (K₀ : ℝ) ^ 2) ≤ θ := by
            rw [div_le_iff₀ (by positivity)]
            have h1 : θ * θ⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hθ_pos)
            nlinarith [mul_lt_mul_of_pos_left hθ_inv_lt hθ_pos]
          have h1 : ((P j).card : ℝ) < (W.card : ℝ) / (64 * (K₀ : ℝ) ^ 2) := lt_of_le_of_lt h_mono h_K₀
          have h2 : (W.card : ℝ) / (64 * (K₀ : ℝ) ^ 2) ≤ (4 * (M_star.card : ℝ)) / (64 * (K₀ : ℝ) ^ 2) :=
            div_le_div_of_nonneg_right (by linarith) (by positivity)
          have h3 : (4 * (M_star.card : ℝ)) / (64 * (K₀ : ℝ) ^ 2) =
              (1 / (16 * (K₀ : ℝ) ^ 2)) * (M_star.card : ℝ) := by ring
          have h4 : (1 / (16 * (K₀ : ℝ) ^ 2)) * (M_star.card : ℝ) ≤ θ * (M_star.card : ℝ) :=
            mul_le_mul_of_nonneg_right h_16K₀_le_θ (Nat.cast_nonneg _)
          linarith
        refine ⟨M_star, hM_star_sub_W, le_of_lt hM_star_gt, hM_star_sub_W.trans hWB, hM_star_ne, ?_⟩
        intro r hri u huB hu_not_comp
        have hnotcomp_Ms : ∃ w_non ∈ M_s, ¬F.Adj u w_non := by
          by_contra! hall
          exact hu_not_comp (fun z hz => hall z (hM_star_sub_Ms hz))
        obtain ⟨C_fam, hC_prop, hC_pair, hC_union⟩ :=
          exists_anticonnected_components_finset_aux F (neighborFinsetIn F u M_star).card
            (neighborFinsetIn F u M_star) le_rfl
        obtain ⟨q, C, _, hC_inj, _, hC_mem, hC_surj, hC_mono⟩ := exists_sorted_equiv_of_finset C_fam
        have hC_disj_comp : ∀ s t : Fin q, s ≠ t → Disjoint (C s) (C t) ∧ IsCompletePair F (C s) (C t) :=
          fun s t hst => hC_pair (C s) (hC_mem s) (C t) (hC_mem t) (fun h => hst (hC_inj h))
        have hC_biUnion : Finset.univ.biUnion C = neighborFinsetIn F u M_star := by
          rw [← hC_union]
          ext x
          simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, id_eq]
          exact ⟨fun ⟨s, hx⟩ => ⟨C s, hC_mem s, hx⟩,
            fun ⟨A, hA, hx⟩ => let ⟨s, hs⟩ := hC_surj A hA; ⟨s, hs ▸ hx⟩⟩
        have hC_sum : ∑ s : Fin q, (C s).card = (neighborFinsetIn F u M_star).card := by
          rw [← hC_biUnion, Finset.card_biUnion (fun s _ t _ hst => (hC_disj_comp s t hst).1)]
        obtain ⟨D_fam, hD_prop, hD_pair, hD_union⟩ :=
          exists_anticonnected_components_finset_aux F (neighborFinsetIn F u M_s).card
            (neighborFinsetIn F u M_s) le_rfl
        refine ⟨q, C, fun s => hC_prop (C s) (hC_mem s), hC_disj_comp, hC_biUnion, hC_sum, hC_mono, fun s => ?_⟩
        by_cases hCs_small : ((C s).card : ℝ) < (2 : ℝ) ^ (m + 1) * w₀
        · have h1 : θ * ((W.card : ℝ) / 4) ≤ θ * (M_star.card : ℝ) :=
            mul_le_mul_of_nonneg_left (le_of_lt hM_star_gt) (le_of_lt hθ_pos)
          linarith
        · push_neg at hCs_small
          obtain ⟨hCs_Zstar, hCs_ne, hCs_ac⟩ := hC_prop (C s) (hC_mem s)
          obtain ⟨x₀, hx₀Cs⟩ := hCs_ne
          have hZstar_Z : neighborFinsetIn F u M_star ⊆ neighborFinsetIn F u M_s :=
            Finset.filter_subset_filter _ hM_star_sub_Ms
          have hCs_Z : C s ⊆ neighborFinsetIn F u M_s := hCs_Zstar.trans hZstar_Z
          have hx₀Z : x₀ ∈ neighborFinsetIn F u M_s := hCs_Z hx₀Cs
          rw [← hD_union, Finset.mem_biUnion] at hx₀Z
          obtain ⟨D_r, hDr_mem, hx₀Dr⟩ := hx₀Z
          have hDr_comp_sdiff : IsCompletePair F D_r (neighborFinsetIn F u M_s \ D_r) := by
            intro y hy z hz
            obtain ⟨hzZ, hz_not⟩ := Finset.mem_sdiff.mp hz
            rw [← hD_union, Finset.mem_biUnion] at hzZ
            obtain ⟨D_r', hDr'_mem, hzDr'⟩ := hzZ
            have hne : D_r ≠ D_r' := fun h => hz_not (h ▸ hzDr')
            exact (hD_pair D_r hDr_mem D_r' hDr'_mem hne).2 y hy z hzDr'
          have hCs_sub_Dr : C s ⊆ D_r :=
            subset_of_isAnticonnected_of_isCompletePair_sdiff hCs_Z hCs_ac hDr_comp_sdiff hx₀Cs hx₀Dr
          have hDr_card : (2 : ℝ) ^ (m + 1) * w₀ ≤ (D_r.card : ℝ) :=
            hCs_small.trans (Nat.cast_le.mpr (Finset.card_le_card hCs_sub_Dr))
          have hDr_isComp : IsAnticonnectedComponentOf F (neighborFinsetIn F u M_s) D_r := by
            obtain ⟨hd_sub, _, hd_ac⟩ := hD_prop D_r hDr_mem
            exact ⟨hd_sub, hd_ac, fun x hx y hyZ hyDr =>
              hDr_comp_sdiff x hx y (Finset.mem_sdiff.mpr ⟨hyZ, hyDr⟩)⟩
          have hDr_mod := hook4_defective_neighborhood_module hc_pos hc_le hEH_Q hS_Q hF_path hF_hook
            hcomb hapex hri.symm hMs_B huB hnotcomp_Ms hw₀ hkappa hDr_isComp hDr_card
          obtain ⟨j, hj_sup⟩ := hP_sup D_r hDr_mod
          have hCs_sub_Pj : C s ⊆ P j := hCs_sub_Dr.trans hj_sup
          have hx₀_Mstar : x₀ ∈ M_star := (Finset.mem_filter.mp (hCs_Zstar hx₀Cs)).1
          obtain ⟨j', hj'_tail, hx₀Pj'⟩ := Finset.mem_biUnion.mp hx₀_Mstar
          have hjj' : j = j' := by
            by_contra hne
            exact Finset.disjoint_left.mp (hP_pure j j' hne).1 (hCs_sub_Pj hx₀Cs) hx₀Pj'
          have hj_K₀ : K₀ ≤ j.1 := hjj' ▸ (Finset.mem_filter.mp hj'_tail).2
          exact (Nat.cast_le.mpr (Finset.card_le_card hCs_sub_Pj)).trans (h_tail_le_θ j hj_K₀)

/-- Potential-preserving Gallai tree refinement loop for `{P_{6+m}, Hook_4(Q)}`. -/
lemma hook4_gallai_tree_refinement_aux
    {V W_Q : Type} [Fintype V] [DecidableEq V] [Fintype W_Q] [DecidableEq W_Q]
    {F : SimpleGraph V} {Q : SimpleGraph W_Q} {S_Q : Set W_Q}
    {c_Q w₀ w θ : ℝ} {m ℓ K₀ : ℕ} {S_amb : Finset V}
    {a : Fin ℓ → V} {B : Fin ℓ → Finset V} {v : V} {i : Fin ℓ}
    (hc_pos : 0 < c_Q) (hc_le : c_Q ≤ 1)
    (hEH_Q : ∀ (U : Type) [Fintype U] [DecidableEq U] (H : SimpleGraph U),
      IsInducedSubgraphFree H Q → (Fintype.card U : ℝ) ^ c_Q ≤ (kappa H : ℝ))
    (hS_Q : ∀ x : W_Q, x ∈ S_Q)
    (hF_path : IsInducedSubgraphFree F (pathGraph (6 + m))ᶜ)
    (hF_hook : IsInducedSubgraphFree F (Hook4Graph Q S_Q)ᶜ)
    (hcomb : IsCombIn F S_amb ℓ w a B)
    (hapex : IsCombExternalApex F S_amb ℓ a B v)
    (hw₀ : 1 ≤ w₀)
    (hkappa : (kappa F : ℝ) < w₀ ^ (c_Q / ((m : ℝ) + 1)))
    (hℓ : 4 ≤ ℓ) (hw_big : (2 : ℝ) ^ 18 * (ℓ : ℝ) ^ 8 < w)
    (hθ_pos : 0 < θ) (hK₀_ℓ : ℓ ^ 4 ≤ K₀) (hK₀_gt : θ⁻¹ < (K₀ : ℝ) + 1)
    (hw₀_bound : (2 : ℝ) ^ (m + 1) * w₀ ≤ θ * (w / (4 * (ℓ : ℝ) ^ 8))) :
    ∀ (n : ℕ) (L_set : Finset (Finset V)),
      (B i).card - L_set.card ≤ n →
      (∀ A ∈ L_set, A ⊆ B i ∧ A.Nonempty ∧ w / (4 * (K₀ : ℝ)) ^ 16 ≤ (A.card : ℝ)) →
      (∀ A ∈ L_set, ∀ B' ∈ L_set, A ≠ B' → Disjoint A B' ∧ IsPurePair F A B') →
      w ^ (1 / 8 : ℝ) ≤ ∑ A ∈ L_set, (A.card : ℝ) ^ (1 / 8 : ℝ) →
      ∃ L_term : Finset (Finset V),
        (∀ A ∈ L_term, A ⊆ B i ∧ A.Nonempty ∧ w / (4 * (K₀ : ℝ)) ^ 16 ≤ (A.card : ℝ)) ∧
        (∀ A ∈ L_term, ∀ B' ∈ L_term, A ≠ B' → Disjoint A B' ∧ IsPurePair F A B') ∧
        w ^ (1 / 8 : ℝ) ≤ ∑ A ∈ L_term, (A.card : ℝ) ^ (1 / 8 : ℝ) ∧
        (∀ A ∈ L_term,
          (∃ M_star ⊆ A, (A.card : ℝ) / 4 ≤ (M_star.card : ℝ) ∧
            IsSmallAttachmentCore F B i θ M_star) ∨
          (A.card : ℝ) < w / (ℓ : ℝ) ^ 8) := by
  classical
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
          IsSmallAttachmentCore F B i θ M_star) ∨
        (A.card : ℝ) < w / (ℓ : ℝ) ^ 8
    · exact ⟨L_set, h_sub, h_pair, h_pot, h_done⟩
    · push_neg at h_done
      obtain ⟨W, hW_mem, hW_no_core, hW_ge⟩ := h_done
      have hW_card : 64 ≤ W.card := by
        have hℓ_pos : (0 : ℝ) < (ℓ : ℝ) ^ 8 := by positivity
        have h1 : (2 : ℝ) ^ 18 < w / (ℓ : ℝ) ^ 8 := (lt_div_iff₀ hℓ_pos).mpr hw_big
        have h2 : (64 : ℝ) ≤ (W.card : ℝ) := by linarith
        exact_mod_cast h2
      have hW_w₀ : (2 : ℝ) ^ (m + 1) * w₀ ≤ θ * ((W.card : ℝ) / 4) := by
        refine hw₀_bound.trans (mul_le_mul_of_nonneg_left ?_ (le_of_lt hθ_pos))
        have h_eq : w / (4 * (ℓ : ℝ) ^ 8) = (w / (ℓ : ℝ) ^ 8) / 4 := by ring
        linarith
      rcases hook4_local_splitting_dichotomy hc_pos hc_le hEH_Q hS_Q hF_path hF_hook hcomb hapex
          hw₀ hkappa hθ_pos hK₀_ge hK₀_gt (h_sub W hW_mem).1 hW_card hW_w₀ with
        ⟨M_star, hMW, hM_card, hM_core⟩ | ⟨k, U, hk2, _hkK₀, hU_pure, _⟩
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
  | succ m_step ih =>
    intro L_set h_rem h_sub h_pair h_pot
    by_cases h_done : ∀ A ∈ L_set,
        (∃ M_star ⊆ A, (A.card : ℝ) / 4 ≤ (M_star.card : ℝ) ∧
          IsSmallAttachmentCore F B i θ M_star) ∨
        (A.card : ℝ) < w / (ℓ : ℝ) ^ 8
    · exact ⟨L_set, h_sub, h_pair, h_pot, h_done⟩
    · push_neg at h_done
      obtain ⟨W, hW_mem, hW_no_core, hW_ge⟩ := h_done
      have hW_card : 64 ≤ W.card := by
        have hℓ_pos : (0 : ℝ) < (ℓ : ℝ) ^ 8 := by positivity
        have h1 : (2 : ℝ) ^ 18 < w / (ℓ : ℝ) ^ 8 := (lt_div_iff₀ hℓ_pos).mpr hw_big
        have h2 : (64 : ℝ) ≤ (W.card : ℝ) := by linarith
        exact_mod_cast h2
      have hW_w₀ : (2 : ℝ) ^ (m + 1) * w₀ ≤ θ * ((W.card : ℝ) / 4) := by
        refine hw₀_bound.trans (mul_le_mul_of_nonneg_left ?_ (le_of_lt hθ_pos))
        have h_eq : w / (4 * (ℓ : ℝ) ^ 8) = (w / (ℓ : ℝ) ^ 8) / 4 := by ring
        linarith
      rcases hook4_local_splitting_dichotomy hc_pos hc_le hEH_Q hS_Q hF_path hF_hook hcomb hapex
          hw₀ hkappa hθ_pos hK₀_ge hK₀_gt (h_sub W hW_mem).1 hW_card hW_w₀ with
        ⟨M_star, hMW, hM_card, hM_core⟩ | ⟨k, U, hk2, hkK₀, hU_pure, hU_pot⟩
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
        have hL'_pair : ∀ A ∈ L_set', ∀ B' ∈ L_set', A ≠ B' → Disjoint A B' ∧ IsPurePair F A B' := by
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

/-- Gallai tree decomposition for `{P_{6+m}, Hook_4(Q)}` inside comb blocks. -/
theorem hook4_gallai_tree_decomposition
    {V W_Q : Type} [Fintype V] [DecidableEq V] [Fintype W_Q] [DecidableEq W_Q]
    {F : SimpleGraph V} {Q : SimpleGraph W_Q} {S_Q : Set W_Q}
    {c_Q w₀ w θ : ℝ} {m ℓ K₀ : ℕ} {S_amb : Finset V}
    {a : Fin ℓ → V} {B : Fin ℓ → Finset V} {v : V}
    (hc_pos : 0 < c_Q) (hc_le : c_Q ≤ 1)
    (hEH_Q : ∀ (U : Type) [Fintype U] [DecidableEq U] (H : SimpleGraph U),
      IsInducedSubgraphFree H Q → (Fintype.card U : ℝ) ^ c_Q ≤ (kappa H : ℝ))
    (hS_Q : ∀ x : W_Q, x ∈ S_Q)
    (hF_path : IsInducedSubgraphFree F (pathGraph (6 + m))ᶜ)
    (hF_hook : IsInducedSubgraphFree F (Hook4Graph Q S_Q)ᶜ)
    (hcomb : IsCombIn F S_amb ℓ w a B)
    (hapex : IsCombExternalApex F S_amb ℓ a B v)
    (hw₀ : 1 ≤ w₀)
    (hkappa : (kappa F : ℝ) < w₀ ^ (c_Q / ((m : ℝ) + 1)))
    (hℓ : 4 ≤ ℓ) (hw : 1 ≤ w)
    (i : Fin ℓ)
    (hθ_pos : 0 < θ) (hK₀_ℓ : ℓ ^ 4 ≤ K₀) (hK₀_gt : θ⁻¹ < (K₀ : ℝ) + 1)
    (hw₀_bound : (2 : ℝ) ^ (m + 1) * w₀ ≤ θ * (w / (4 * (ℓ : ℝ) ^ 8))) :
    (∃ M_star ⊆ B i, w / ((2 : ℝ) ^ 18 * (ℓ : ℝ) ^ 8) ≤ (M_star.card : ℝ) ∧
      IsSmallAttachmentCore F B i θ M_star) ∨
    (∃ (k : ℕ) (U : Fin k → Finset V),
      2 ≤ k ∧ k ≤ K₀ ∧ (ℓ : ℝ) ^ (1 / 2 : ℝ) / 2 ≤ (k : ℝ) ∧
      IsPureBlockadeIn F (B i) k (w / (4 * (k : ℝ)) ^ 16) U) := by
  classical
  by_cases hw_small : w ≤ (2 : ℝ) ^ 18 * (ℓ : ℝ) ^ 8
  · left
    obtain ⟨z₀, hz₀⟩ := hcomb.is_blockade.nonempty_blocks i
    refine ⟨{z₀}, Finset.singleton_subset_iff.mpr hz₀, ?_, isSmallAttachmentCore_singleton hz₀⟩
    rw [Finset.card_singleton, Nat.cast_one]
    exact (div_le_one (by positivity)).mpr hw_small
  · push_neg at hw_small
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
        A ≠ B' → Disjoint A B' ∧ IsPurePair F A B' := by
      intro A hA B' hB' hne
      rw [Finset.mem_singleton.mp hA, Finset.mem_singleton.mp hB'] at hne
      exact False.elim (hne rfl)
    have h_init_pot : w ^ (1 / 8 : ℝ) ≤
        ∑ A ∈ ({B i} : Finset (Finset V)), (A.card : ℝ) ^ (1 / 8 : ℝ) := by
      rw [Finset.sum_singleton]
      exact Real.rpow_le_rpow (by linarith) hBi_ge_w (by positivity)
    obtain ⟨L_term, hL_sub, hL_pair, hL_pot, hL_term⟩ :=
      hook4_gallai_tree_refinement_aux hc_pos hc_le hEH_Q hS_Q hF_path hF_hook hcomb hapex
        hw₀ hkappa hℓ hw_small hθ_pos hK₀_ℓ hK₀_gt hw₀_bound
        ((B i).card - 1) {B i} (by simp) h_init_sub h_init_pair h_init_pot
    by_cases h_out1 : ∃ A ∈ L_term,
        (∃ M_star ⊆ A, (A.card : ℝ) / 4 ≤ (M_star.card : ℝ) ∧
          IsSmallAttachmentCore F B i θ M_star) ∧
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
      have hp_le_quarter : (p : ℝ) ≤ (ℓ : ℝ) / 4 := by
        have hp_le : (p : ℝ) ≤ (ℓ : ℝ) ^ (1 / 2 : ℝ) / 2 := Nat.floor_le (by positivity)
        linarith
      let f : ℕ → ℝ := fun k =>
        if h : 1 ≤ k ∧ k ≤ q then ((L ⟨k - 1, by omega⟩).card : ℝ) ^ (1 / 8 : ℝ) else 0
      have hf_sum : w ^ (1 / 8 : ℝ) ≤ ∑ k ∈ Finset.Icc 1 q, f k := by
        rw [← sum_fin_eq_sum_Icc q (fun j => ((L j).card : ℝ) ^ (1 / 8 : ℝ))]
        exact hL_pot_fin
      have hf_le : ∀ k, f k ≤ w ^ (1 / 8 : ℝ) / (ℓ : ℝ) := by
        intro k; unfold f; split_ifs with h; exact hL_rpow_lt ⟨k - 1, by omega⟩; positivity
      have hp_sum : ∑ k ∈ Finset.Icc 1 p, f k ≤ (1 / 4 : ℝ) * w ^ (1 / 8 : ℝ) := by
        calc ∑ k ∈ Finset.Icc 1 p, f k
            ≤ ∑ _k ∈ Finset.Icc 1 p, (w ^ (1 / 8 : ℝ) / (ℓ : ℝ)) := Finset.sum_le_sum (fun k _ => hf_le k)
          _ = (p : ℝ) * (w ^ (1 / 8 : ℝ) / (ℓ : ℝ)) := by
              rw [Finset.sum_const, Nat.card_Icc, show p + 1 - 1 = p by omega, nsmul_eq_mul]
          _ ≤ ((ℓ : ℝ) / 4) * (w ^ (1 / 8 : ℝ) / (ℓ : ℝ)) :=
              mul_le_mul_of_nonneg_right hp_le_quarter (by positivity)
          _ = (1 / 4 : ℝ) * w ^ (1 / 8 : ℝ) := by field_simp
      have hpq : p ≤ q := by
        by_contra hlt; push_neg at hlt
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
      have hk₀_1 : 1 ≤ k₀ ∧ k₀ ≤ q := ⟨by omega, hk₀_high⟩
      unfold f at hk₀_ge
      rw [dif_pos hk₀_1] at hk₀_ge
      have hk₀_pos : (0 : ℝ) < k₀ := by exact_mod_cast hk₀_1.1
      have hk₀_sq_pos : 0 < (k₀ : ℝ) ^ 2 := by positivity
      have hk₀_width : w / (4 * (k₀ : ℝ)) ^ 16 ≤ ((L ⟨k₀ - 1, by omega⟩).card : ℝ) := by
        have h1 : w ^ (1 / 8 : ℝ) / (4 * (k₀ : ℝ)) ^ 2 ≤ ((L ⟨k₀ - 1, by omega⟩).card : ℝ) ^ (1 / 8 : ℝ) := by
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
      have hp_ge_one : 1 ≤ p := Nat.le_floor (by linarith [h_sqrt_ge])
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
            simp only [Fin.mk_le_mk]; omega
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

/--
**Proposition 6(2a) — Stage-1 Comb Dichotomy for `{P_{6+m}, Hook_4(Q)}` (`hook4_comb_dichotomy`, line 1010 of `main.tex`)**:
Let $Q$ satisfy `HasErdosHajnalProp` and $S_Q = \text{Set.univ}$. Then there exists $c_Q \in (0, 1]$
such that for every $m \ge 0$ ($t = 6 + m \ge 6$), every `{(pathGraph (6 + m))ᶜ, (Hook4Graph Q S_Q)ᶜ}`-free
graph $F$, and every $(\ell, w)$-comb $(a, B)$ inside $S \subseteq V$ with external apex $v$
($0 < x \le y \le 2^{-8}$, $y^{-1/4} \le \ell \le x^{-2}$, $|S| / \ell^{18} \le w$), at least one of the
following holds (with $w_0 := \max\bigl(1,\, \frac{x^3 \max(w, 1)}{2^{m+7} \ell^{11}}\bigr)$):
- **(CD1)**: $w_0^{c_Q / (m + 1)} \le \kappa(F)$;
- **(CD2 / Long Complete Blockade)**: $F[S]$ contains a complete $(k, \frac{|S|}{k^{120}})$-blockade
  for some integer $k > x^{-2}$; or
- **(CD2 / CD3 / Moderate Complete-or-$x$-Sparse Blockade)**: $F[S]$ contains a complete-or-$x$-sparse
  $(k, \frac{|S|}{k^{120}})$-blockade for some integer $k \in [2, x^{-10}]$ with $k \ge \frac{\ell^{1/2}}{2}$.
-/
theorem hook4_comb_dichotomy
    {W_Q : Type} [Fintype W_Q] [DecidableEq W_Q]
    (Q : SimpleGraph W_Q) (S_Q : Set W_Q)
    (hEH_Q : HasErdosHajnalProp Q) (hS_Q : ∀ x : W_Q, x ∈ S_Q) :
    ∃ c_Q > (0 : ℝ), c_Q ≤ 1 ∧
      ∀ (m : ℕ) (V : Type) [Fintype V] [DecidableEq V] (F : SimpleGraph V) (S : Finset V)
        (ℓ : ℕ) (w x y : ℝ) (a : Fin ℓ → V) (B : Fin ℓ → Finset V) (v : V),
        IsInducedSubgraphFree F (pathGraph (6 + m))ᶜ →
        IsInducedSubgraphFree F (Hook4Graph Q S_Q)ᶜ →
        IsCombIn F S ℓ w a B →
        IsCombExternalApex F S ℓ a B v →
        0 < x → x ≤ y → y ≤ (2 : ℝ) ^ (-8 : ℝ) →
        y ^ (-1 / 4 : ℝ) ≤ (ℓ : ℝ) → (ℓ : ℝ) ≤ x ^ (-2 : ℝ) →
        (S.card : ℝ) / (ℓ : ℝ) ^ 18 ≤ w →
        let w' := max w 1
        let w₀ := max 1 ((x ^ 3 / (16 * (ℓ : ℝ) ^ 3)) * (w' / (4 * (ℓ : ℝ) ^ 8)) / (2 : ℝ) ^ (m + 1))
        -- (CD1)
        (w₀ ^ (c_Q / ((m : ℝ) + 1)) ≤ (kappa F : ℝ)) ∨
        -- (CD2 / Long Complete Blockade)
        (∃ (k : ℕ) (D : Fin k → Finset V),
          x ^ (-2 : ℝ) < (k : ℝ) ∧
          IsCompleteBlockadeIn F S k ((S.card : ℝ) / (k : ℝ) ^ 120) D) ∨
        -- (CD2 / CD3 / Moderate Complete-or-x-Sparse Blockade)
        (∃ (k : ℕ) (D : Fin k → Finset V),
          2 ≤ k ∧ (k : ℝ) ≤ x ^ (-10 : ℝ) ∧ (ℓ : ℝ) ^ (1 / 2 : ℝ) / 2 ≤ (k : ℝ) ∧
          IsCompleteOrXSparseBlockadeIn F S k ((S.card : ℝ) / (k : ℝ) ^ 120) x D) := by
  obtain ⟨c_0, hc_0, h_eh_0⟩ := hEH_Q
  let c_Q : ℝ := min c_0 1
  have hc_pos : 0 < c_Q := lt_min hc_0 zero_lt_one
  have hc_le : c_Q ≤ 1 := min_le_right _ _
  have hc_le_0 : c_Q ≤ c_0 := min_le_left _ _
  have hEH_cQ : ∀ (U : Type) [Fintype U] [DecidableEq U] (H : SimpleGraph U),
      IsInducedSubgraphFree H Q → (Fintype.card U : ℝ) ^ c_Q ≤ (kappa H : ℝ) := by
    intro U _ _ H hH
    by_cases hU0 : Fintype.card U = 0
    · rw [hU0, Nat.cast_zero, Real.zero_rpow (ne_of_gt hc_pos)]
      exact Nat.cast_nonneg _
    · have hU1 : (1 : ℝ) ≤ (Fintype.card U : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hU0
      exact (Real.rpow_le_rpow_of_exponent_le hU1 hc_le_0).trans (h_eh_0 U H hH)
  refine ⟨c_Q, hc_pos, hc_le, ?_⟩
  intro m V _ _ F S ℓ w x y a B v hF_path hF_hook hcomb hapex hx_pos hxy hy_max hℓ_low hℓ_high hw_ge
  classical
  let w' : ℝ := max w 1
  let θ : ℝ := x ^ 3 / (16 * (ℓ : ℝ) ^ 3)
  let K₀ : ℕ := ⌊θ⁻¹⌋₊
  let w₀ : ℝ := max 1 (θ * (w' / (4 * (ℓ : ℝ) ^ 8)) / (2 : ℝ) ^ (m + 1))
  have hw₀_ge_1 : 1 ≤ w₀ := le_max_left 1 _
  by_cases h_cd1 : w₀ ^ (c_Q / ((m : ℝ) + 1)) ≤ (kappa F : ℝ)
  · exact Or.inl h_cd1
  · right
    push_neg at h_cd1
    obtain ⟨hℓ, hx_256, hθ_pos, hK₀_ℓ, hK₀_gt, hK₀_max, hℓ_max, hℓ_sqrt⟩ :=
      comb_parameter_bounds hx_pos hxy hy_max hℓ_low hℓ_high
    have hw'_1 : 1 ≤ w' := le_max_right w 1
    have hw'_ge : (S.card : ℝ) / (ℓ : ℝ) ^ 18 ≤ w' := le_trans hw_ge (le_max_left w 1)
    have hcomb' : IsCombIn F S ℓ w' a B := by
      refine ⟨⟨hcomb.is_blockade.subset_ambient, hcomb.is_blockade.nonempty_blocks,
        hcomb.is_blockade.pairwise_disjoint, fun i => ?_⟩,
        hcomb.apex_in_ambient, hcomb.apex_injective, hcomb.apex_disjoint_blocks,
        hcomb.apex_complete_own, hcomb.apex_anticomplete_other⟩
      exact max_le (hcomb.is_blockade.width_ge i)
        (Nat.one_le_cast.mpr (Finset.card_pos.mpr (hcomb.is_blockade.nonempty_blocks i)))
    -- Note that if 1 > θ * (w' / (4 * ℓ^8)) / 2^(m+1), then w₀ = 1 and kappa F ≥ 1 contradicts h_cd1!
    haveI : Nonempty V := ⟨v⟩
    have hkappa_pos : (1 : ℝ) ≤ (kappa F : ℝ) := by exact_mod_cast kappa_pos_of_nonempty F
    have hw₀_gt_1 : 1 < w₀ := by
      by_contra hle
      have hw₀_eq : w₀ = 1 := le_antisymm (not_lt.mp hle) hw₀_ge_1
      rw [hw₀_eq, Real.one_rpow] at h_cd1
      linarith
    have hw₀_eq_rhs : w₀ = θ * (w' / (4 * (ℓ : ℝ) ^ 8)) / (2 : ℝ) ^ (m + 1) := by
      rcases max_cases (1 : ℝ) (θ * (w' / (4 * (ℓ : ℝ) ^ 8)) / (2 : ℝ) ^ (m + 1)) with ⟨h1, _⟩ | ⟨h2, _⟩
      · unfold w₀ at hw₀_gt_1; linarith
      · exact h2
    have hw₀_bound : (2 : ℝ) ^ (m + 1) * w₀ ≤ θ * (w' / (4 * (ℓ : ℝ) ^ 8)) := by
      rw [hw₀_eq_rhs]
      have h_pow_ne : (2 : ℝ) ^ (m + 1) ≠ 0 := by positivity
      field_simp [h_pow_ne]; linarith
    by_cases h_case1 : ∃ i : Fin ℓ, ∃ (k : ℕ) (U : Fin k → Finset V),
        2 ≤ k ∧ k ≤ K₀ ∧ (ℓ : ℝ) ^ (1 / 2 : ℝ) / 2 ≤ (k : ℝ) ∧
        IsPureBlockadeIn F (B i) k (w' / (4 * (k : ℝ)) ^ 16) U
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
          IsSmallAttachmentCore F B i θ M_star := by
        intro i
        rcases hook4_gallai_tree_decomposition hc_pos hc_le hEH_cQ hS_Q hF_path hF_hook hcomb' hapex
            hw₀_ge_1 h_cd1 hℓ hw'_1 i hθ_pos hK₀_ℓ hK₀_gt hw₀_bound with
          h_out1 | h_out2
        · exact h_out1
        · exact False.elim (h_case1 ⟨i, h_out2⟩)
      obtain ⟨M_star, hM_all⟩ := Classical.axiomOfChoice h_all_out1
      have hM_sub : ∀ i, M_star i ⊆ B i := fun i => (hM_all i).1
      have hM_card : ∀ i, w' / ((2 : ℝ) ^ 18 * (ℓ : ℝ) ^ 8) ≤ ((M_star i).card : ℝ) :=
        fun i => (hM_all i).2.1
      have hM_core : ∀ i, IsSmallAttachmentCore F B i θ (M_star i) := fun i => (hM_all i).2.2
      by_cases h_62a : ∃ (i j : Fin ℓ), j ≠ i ∧ ∃ u ∈ M_star j,
          (¬∀ z ∈ M_star i, F.Adj u z) ∧
          x / (2 * (ℓ : ℝ)) * ((M_star i).card : ℝ) ≤ ((neighborFinsetIn F u (M_star i)).card : ℝ)
      · left
        obtain ⟨i, j, hji, u, hu_Mj, hu_not_comp, hu_deg⟩ := h_62a
        exact comb_dichotomy_subcase_6_2a hx_pos hx_256 hℓ hℓ_high hw'_ge
          hcomb.is_blockade.subset_ambient hM_sub hM_card hM_core hji hu_Mj hu_not_comp hu_deg
      · right
        have h_sparse_att : ∀ (i j : Fin ℓ), j ≠ i → ∀ u ∈ M_star j,
            (¬∀ z ∈ M_star i, F.Adj u z) →
            ((neighborFinsetIn F u (M_star i)).card : ℝ) <
              x / (2 * (ℓ : ℝ)) * ((M_star i).card : ℝ) := by
          intro i j hji u hu_Mj hu_not_comp
          by_contra h_ge
          push_neg at h_ge
          exact h_62a ⟨i, j, hji, u, hu_Mj, hu_not_comp, h_ge⟩
        exact comb_dichotomy_subcase_6_2b hx_pos hx_256 hℓ hℓ_max hℓ_sqrt hw'_ge
          hcomb.is_blockade.subset_ambient hcomb.is_blockade.pairwise_disjoint
          hM_sub (fun i => (hM_core i).2.1) hM_card h_sparse_att
/-!
### Section 5: Proposition 6(3) — Pairwise Non-Isomorphic Infinite Prime Non-Split Towers Above Every Path $P_t$
(`main.tex` lines 982, 1014–1016)

For every $t \ge 6$ and $k \ge 0$, `PrimeTowerGraph t k` ($H_{t+k}^{(t)}$ on `Fin (t + k)`) starts from
$H_t^{(t)} \cong P_t$ (`primeTowerZeroIsoPath`) with endpoint $u_t = t - 1$ and recursively attaches:
- for odd $k \ge 1$, a co-leaf $u_{t+k}$ of co-degree $1$ in $H_{t+k}^{(t)}$ adjacent in $\overline{H_{t+k}^{(t)}}$
  solely to $u_{t+k-1}$;
- for even $k \ge 2$, a degree-$1$ leaf $u_{t+k}$ in $H_{t+k}^{(t)}$ adjacent in $H_{t+k}^{(t)}$
  solely to $u_{t+k-1}$.

We establish:
1. **Pairwise non-isomorphism** (`primeTower_iso_iff_eq`): $|H_{t+k}^{(t)}| = t + k$ strictly increases with $k$.
2. **Non-splitness** (`primeTower_not_isSplitGraph`): $P_6 \hookrightarrow_g H_{t+k}^{(t)}$ for $t \ge 6$,
   and $\omega(P_6) + \alpha(P_6) = 2 + 3 = 5 < 6$.
3. **Primality** (`primeTower_isPrimeGraph`): $P_t$ ($t \ge 4$) is prime (`isPrimeGraph_pathGraph`),
   and one-vertex leaf/co-leaf primality preservation (`isPrimeGraph_of_add_leaf`, `isPrimeGraph_of_add_coleaf`)
   propagates primality to all $k \ge 0$.
4. **Closure membership** (`primeTower_inHClosure`): $H_{t+k}^{(t)} \in \mathcal{H}(\mathcal{B}_t^*)$
   via alternating leaf addition in one graph and $K_2$-substitution plus degree-$1$ leaf re-attachment in the complement.
5. **Non-membership in $\mathcal{J}(\{K_1, K_2, \overline{K_2}, C_5\})$** (`primeTowerCompl_not_inJClosureC5`,
   `primeTower_not_inHClosureC5`): every prime induced subgraph of order $\ge 6$ in $\mathcal{J}(\{K_1, K_2, \overline{K_2}, C_5\})$
   has a vertex of degree $\le 1$, whereas $\overline{P_t} \hookrightarrow_g \overline{H_{t+k}^{(t)}}$ is prime of order $t \ge 6$
   with minimum degree $t - 3 \ge 2$.
-/

/-- Computable `DecidableRel` instance for `PrimeTowerGraph t k`. -/
instance instDecidableRelPrimeTowerGraphAdj (t k : ℕ) :
    DecidableRel (PrimeTowerGraph t k).Adj := by
  intro u v
  unfold PrimeTowerGraph primeTowerAdjLt
  dsimp
  infer_instance

/-- Adjacency of `u < v` in `PrimeTowerGraph t k` is `primeTowerAdjLt t u.1 v.1`. -/
theorem primeTowerGraph_adj_of_lt {t k : ℕ} {u v : Fin (t + k)} (huv : u.1 < v.1) :
    (PrimeTowerGraph t k).Adj u v ↔ primeTowerAdjLt t u.1 v.1 := by
  unfold PrimeTowerGraph
  dsimp
  rw [if_pos huv]

/-- Base-case isomorphism $H_t^{(t)} \simeq_g P_t$ (`PrimeTowerGraph t 0 ≃g pathGraph t`). -/
def primeTowerZeroIsoPath (t : ℕ) : PrimeTowerGraph t 0 ≃g pathGraph t where
  toEquiv := finCongr (Nat.add_zero t)
  map_rel_iff' := by
    intro u v
    have hu := u.2
    have hv := v.2
    unfold PrimeTowerGraph primeTowerAdjLt
    dsimp
    simp only [finCongr_apply, Fin.val_cast, pathGraph_adj]
    by_cases huv : u.1 < v.1
    · rw [if_pos huv, if_pos (by omega : v.1 < t)]
      omega
    · by_cases hvu : v.1 < u.1
      · rw [if_neg huv, if_pos hvu, if_pos (by omega : u.1 < t)]
        omega
      · rw [if_neg huv, if_neg hvu]
        simp only [iff_false, false_iff]
        omega

/-- Induced subgraph embedding $P_m \hookrightarrow_g H_{t+k}^{(t)}$ (`pathGraph m ↪g PrimeTowerGraph t k`) whenever $m \le t$. -/
def pathGraphEmbPrimeTower {m t k : ℕ} (hmt : m ≤ t) :
    pathGraph m ↪g PrimeTowerGraph t k where
  toEmbedding := ⟨fun i => ⟨i.1, by omega⟩, fun i j h => by ext; exact Fin.mk.inj h⟩
  map_rel_iff' := by
    intro i j
    have hi := i.2
    have hj := j.2
    unfold PrimeTowerGraph primeTowerAdjLt
    dsimp
    simp only [pathGraph_adj]
    by_cases hij : i.1 < j.1
    · rw [if_pos hij, if_pos (by omega : j.1 < t)]
      omega
    · by_cases hji : j.1 < i.1
      · rw [if_neg hij, if_pos hji, if_pos (by omega : i.1 < t)]
        omega
      · rw [if_neg hij, if_neg hji]
        simp only [iff_false, false_iff]
        omega

/-- Deleting the top vertex $u_{t+k+1}$ (`⟨t + k, _⟩`) from `PrimeTowerGraph t (k + 1)` yields `PrimeTowerGraph t k`. -/
def primeTowerStepIso (t k : ℕ) :
    (PrimeTowerGraph t (k + 1)).comap
      (Subtype.val : {v : Fin (t + (k + 1)) // v ≠ ⟨t + k, by omega⟩} → Fin (t + (k + 1))) ≃g
      PrimeTowerGraph t k where
  toFun v := ⟨v.1.1, by
    have hv : v.1.1 ≠ t + k := fun h => v.2 (Fin.ext h)
    omega⟩
  invFun i := ⟨⟨i.1, by omega⟩, fun h => by
    have := Fin.mk.inj h
    omega⟩
  left_inv v := by ext; rfl
  right_inv i := by ext; rfl
  map_rel_iff' := by
    intro a b
    unfold PrimeTowerGraph
    rfl

/--
**Proposition 6(3) — Pairwise Non-Isomorphism of `PrimeTowerGraph t k` across $k$ (`primeTower_iso_iff_eq`, `main.tex` line 1016)**:
`PrimeTowerGraph t k₁` and `PrimeTowerGraph t k₂` are isomorphic if and only if $k_1 = k_2$.
-/
theorem primeTower_iso_iff_eq (t k₁ k₂ : ℕ) :
    Nonempty (PrimeTowerGraph t k₁ ≃g PrimeTowerGraph t k₂) ↔ k₁ = k₂ := by
  constructor
  · rintro ⟨iso⟩
    have hcard := Fintype.card_congr iso.toEquiv
    simp only [Fintype.card_fin] at hcard
    omega
  · rintro rfl
    exact ⟨SimpleGraph.Iso.refl⟩

/-- Splitness (`IsSplitGraph`) is preserved under induced graph embeddings (`↪g`). -/
theorem IsSplitGraph.of_embedding {W₁ W₂ : Type*} [Fintype W₁] [DecidableEq W₁]
    [Fintype W₂] [DecidableEq W₂] {G₁ : SimpleGraph W₁} {G₂ : SimpleGraph W₂}
    (f : G₁ ↪g G₂) (h₂ : IsSplitGraph G₂) : IsSplitGraph G₁ := by
  obtain ⟨C, I, hCI_union, hCI_disj, hC_cliq, hI_cliq⟩ := h₂
  classical
  let C₁ : Finset W₁ := Finset.univ.filter (fun x => f x ∈ C)
  let I₁ : Finset W₁ := Finset.univ.filter (fun x => f x ∈ I)
  refine ⟨C₁, I₁, ?_, ?_, ?_, ?_⟩
  · ext x
    simp only [C₁, I₁, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    have hfx : f x ∈ C ∪ I := hCI_union ▸ Finset.mem_univ (f x)
    exact Finset.mem_union.mp hfx
  · rw [Finset.disjoint_left]
    intro x hxC hxI
    exact Finset.disjoint_left.mp hCI_disj (Finset.mem_filter.mp hxC).2 (Finset.mem_filter.mp hxI).2
  · intro x hx y hy hxy
    have hfx : f x ∈ (C : Set W₂) := (Finset.mem_filter.mp hx).2
    have hfy : f y ∈ (C : Set W₂) := (Finset.mem_filter.mp hy).2
    exact f.map_rel_iff.mp (hC_cliq hfx hfy (f.injective.ne hxy))
  · intro x hx y hy hxy
    have hfx : f x ∈ (I : Set W₂) := (Finset.mem_filter.mp hx).2
    have hfy : f y ∈ (I : Set W₂) := (Finset.mem_filter.mp hy).2
    have h_compl := hI_cliq hfx hfy (f.injective.ne hxy)
    rw [compl_adj] at h_compl ⊢
    exact ⟨hxy, fun hadj => h_compl.2 (f.map_rel_iff.mpr hadj)⟩

/-- `pathGraph 6` ($P_6$) is not a split graph, since $\omega(P_6) \le 2$ and $\alpha(P_6) \le 3$ give $|C| + |I| \le 5 < 6$ (`main.tex` line 1016). -/
theorem not_isSplitGraph_pathGraph_six : ¬IsSplitGraph (pathGraph 6) := by
  rintro ⟨C, I, hCI_union, hCI_disj, hC_cliq, hI_cliq⟩
  have hCI_card : C.card + I.card = 6 := by
    have h1 := Finset.card_union_of_disjoint hCI_disj
    rw [hCI_union, Finset.card_univ, Fintype.card_fin] at h1
    omega
  have hC_le : C.card ≤ 2 := by
    by_contra! hC
    obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card.mp hC
    have h1 := pathGraph_adj.mp (hC_cliq hx hy hxy)
    have h2 := pathGraph_adj.mp (hC_cliq hy hz hyz)
    have h3 := pathGraph_adj.mp (hC_cliq hx hz hxz)
    omega
  have hI_le : I.card ≤ 3 := by
    let f : Fin 6 → Fin 3 := fun x => ⟨x.1 / 2, by omega⟩
    have hinj : Set.InjOn f I := by
      intro x hx y hy hfeq
      by_contra hxy
      have hdiv : x.1 / 2 = y.1 / 2 := Fin.mk.inj hfeq
      have hval_ne : x.1 ≠ y.1 := Fin.ext_iff.not.mp hxy
      have hadj : (pathGraph 6).Adj x y := pathGraph_adj.mpr (by omega)
      exact ((compl_adj (pathGraph 6) x y).mp (hI_cliq hx hy hxy)).2 hadj
    calc I.card = (I.image f).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.univ : Finset (Fin 3)).card := Finset.card_le_univ _
      _ = 3 := Fintype.card_fin 3
  omega

/--
**Proposition 6(3) — Non-Splitness of `PrimeTowerGraph t k` (`primeTower_not_isSplitGraph`, `main.tex` line 1016)**:
For every $t \ge 6$ and $k \ge 0$, `PrimeTowerGraph t k` ($H_{t+k}^{(t)}$) is not a split graph,
since it contains $P_6$ as an induced subgraph (`pathGraphEmbPrimeTower`).
-/
theorem primeTower_not_isSplitGraph (t k : ℕ) (ht : 6 ≤ t) :
    ¬IsSplitGraph (PrimeTowerGraph t k) :=
  fun h => not_isSplitGraph_pathGraph_six (h.of_embedding (pathGraphEmbPrimeTower ht))

/-- Primality is invariant under graph complementation (`isPrimeGraph_compl_iff`). -/
theorem isPrimeGraph_compl_iff {W : Type*} [Fintype W] [DecidableEq W] (G : SimpleGraph W) :
    IsPrimeGraph Gᶜ ↔ IsPrimeGraph G := by
  unfold IsPrimeGraph
  simp only [isProperModuleIn_compl_iff]

/-- Primality is invariant under graph isomorphism (`IsPrimeGraph.of_iso`). -/
theorem IsPrimeGraph.of_iso {W₁ W₂ : Type*} [Fintype W₁] [DecidableEq W₁]
    [Fintype W₂] [DecidableEq W₂] {G₁ : SimpleGraph W₁} {G₂ : SimpleGraph W₂}
    (iso : G₁ ≃g G₂) (h₁ : IsPrimeGraph G₁) : IsPrimeGraph G₂ := by
  refine ⟨by rw [← Fintype.card_congr iso.toEquiv]; exact h₁.1, fun M hM => ?_⟩
  let M₁ : Finset W₁ := M.map iso.symm.toEquiv.toEmbedding
  have hM₁_card : M₁.card = M.card := Finset.card_map _
  rw [← hM₁_card]
  apply h₁.2 M₁
  refine ⟨hM.1.map, ?_, Finset.subset_univ _, fun z _ hz_not => ?_⟩
  · rw [Finset.ssubset_univ_iff]
    intro h_eq
    have h_card : M.card = Fintype.card W₂ := by
      calc M.card = M₁.card := hM₁_card.symm
        _ = Fintype.card W₁ := by rw [h_eq, Finset.card_univ]
        _ = Fintype.card W₂ := Fintype.card_congr iso.toEquiv
    have h_ne_univ : M ≠ Finset.univ := Finset.ssubset_univ_iff.mp hM.2.1
    exact h_ne_univ (Finset.eq_univ_of_card M h_card)
  · have h_iso_z_not : iso z ∉ M := by
      intro h_in
      apply hz_not
      rw [Finset.mem_map]
      exact ⟨iso z, h_in, by simp⟩
    rcases hM.2.2.2 (iso z) (Finset.mem_univ _) h_iso_z_not with h_comp | h_anti
    · left
      intro u hu
      rcases Finset.mem_map.mp hu with ⟨u₂, hu₂, rfl⟩
      have hadj := h_comp u₂ hu₂
      have h_symm : iso (iso.symm.toEquiv.toEmbedding u₂) = u₂ := iso.apply_symm_apply u₂
      rw [← h_symm] at hadj
      exact iso.map_rel_iff.mp hadj
    · right
      intro u hu hadj
      rcases Finset.mem_map.mp hu with ⟨u₂, hu₂, rfl⟩
      have hadj₂ : G₂.Adj (iso z) u₂ := by
        have h1 := iso.map_rel_iff.mpr hadj
        have h_symm : iso (iso.symm.toEquiv.toEmbedding u₂) = u₂ := iso.apply_symm_apply u₂
        rwa [h_symm] at h1
      exact h_anti u₂ hu₂ hadj₂

/-- For every $t \ge 4$, the $t$-vertex path `pathGraph t` ($P_t$) is a prime graph (`IsPrimeGraph (pathGraph t)`, `main.tex` line 1016). -/
theorem isPrimeGraph_pathGraph {t : ℕ} (ht : 4 ≤ t) :
    IsPrimeGraph (pathGraph t) := by
  refine ⟨by rw [Fintype.card_fin]; exact ht, fun M hM => ?_⟩
  by_contra hM_ne1
  have hM_ge2 : 2 ≤ M.card := by
    have := hM.1.card_pos
    omega
  let a := M.min' hM.1
  let b := M.max' hM.1
  have ha_mem : a ∈ M := Finset.min'_mem M hM.1
  have hb_mem : b ∈ M := Finset.max'_mem M hM.1
  have hab_lt : a < b := by
    by_contra! hab
    have hsub : M ⊆ {a} := fun x hx =>
      Finset.mem_singleton.mpr (le_antisymm (le_trans (Finset.le_max' M x hx) hab) (Finset.min'_le M x hx))
    have hcard := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hcard
    omega
  have ha_zero : a.1 = 0 := by
    by_contra ha_nz
    let z : Fin t := ⟨a.1 - 1, by omega⟩
    have hz_not : z ∉ M := fun hz => by
      have := Finset.min'_le M z hz
      change a.1 ≤ a.1 - 1 at this
      omega
    have hza : (pathGraph t).Adj z a := pathGraph_adj.mpr (by dsimp [z]; omega)
    have hzb : ¬(pathGraph t).Adj z b := by
      rw [pathGraph_adj]; dsimp [z]; have : a.1 < b.1 := hab_lt; omega
    rcases hM.2.2.2 z (Finset.mem_univ z) hz_not with h_comp | h_anti
    · exact hzb (h_comp b hb_mem)
    · exact h_anti a ha_mem hza
  have hb_last : b.1 = t - 1 := by
    by_contra hb_nt
    let z : Fin t := ⟨b.1 + 1, by omega⟩
    have hz_not : z ∉ M := fun hz => by
      have := Finset.le_max' M z hz
      change b.1 + 1 ≤ b.1 at this
      omega
    have hbz : (pathGraph t).Adj z b := pathGraph_adj.mpr (by dsimp [z]; omega)
    have haz : ¬(pathGraph t).Adj z a := by
      rw [pathGraph_adj]; dsimp [z]; have : a.1 < b.1 := hab_lt; omega
    rcases hM.2.2.2 z (Finset.mem_univ z) hz_not with h_comp | h_anti
    · exact haz (h_comp a ha_mem)
    · exact h_anti b hb_mem hbz
  have h_sdiff_ne : (Finset.univ \ M).Nonempty := by
    obtain ⟨y, hy_univ, hy_not⟩ := Finset.exists_of_ssubset hM.2.1
    exact ⟨y, Finset.mem_sdiff.mpr ⟨hy_univ, hy_not⟩⟩
  let z := (Finset.univ \ M).min' h_sdiff_ne
  have hz_sdiff : z ∈ Finset.univ \ M := Finset.min'_mem _ h_sdiff_ne
  have hz_not : z ∉ M := (Finset.mem_sdiff.mp hz_sdiff).2
  have hz_pos : 0 < z.1 := by
    by_contra h0
    have hza_eq : z = a := Fin.ext (by omega)
    exact hz_not (hza_eq ▸ ha_mem)
  let z_prev : Fin t := ⟨z.1 - 1, by omega⟩
  have hz_prev_mem : z_prev ∈ M := by
    by_contra hzp_not
    have hzp_sdiff : z_prev ∈ Finset.univ \ M := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzp_not⟩
    have := Finset.min'_le _ z_prev hzp_sdiff
    change z.1 ≤ z.1 - 1 at this
    omega
  have h_adj_prev : (pathGraph t).Adj z z_prev :=
    pathGraph_adj.mpr (by dsimp [z_prev]; omega)
  rcases hM.2.2.2 z (Finset.mem_univ z) hz_not with h_comp | h_anti
  · have hza := pathGraph_adj.mp (h_comp a ha_mem)
    have hzb := pathGraph_adj.mp (h_comp b hb_mem)
    omega
  · exact h_anti z_prev hz_prev_mem h_adj_prev
/--
**One-Vertex Primality Preservation under Leaf Addition (`isPrimeGraph_of_add_leaf`, `main.tex` line 1014)**:
If $G_0 = G - u$ is prime, $u$ has unique neighbor $w_0 \neq u$ in $G$, $w_0$ has a neighbor in $G_0$,
and every $z \notin \{u, w_0\}$ has a neighbor in $G_0 - w_0$ (so no $z \in V(G_0) \setminus \{w_0\}$ satisfies $N_{G_0}(z) = \{w_0\}$),
then $G$ is prime.
-/
theorem isPrimeGraph_of_add_leaf {W : Type*} [Fintype W] [DecidableEq W]
    {G : SimpleGraph W} {u w₀ : W}
    (hG₀ : IsPrimeGraph (G.comap (Subtype.val : {v : W // v ≠ u} → W)))
    (hw₀_ne : w₀ ≠ u)
    (hu_adj : ∀ v : W, G.Adj u v ↔ v = w₀)
    (hw₀_deg : ∃ x : W, x ≠ u ∧ G.Adj w₀ x)
    (hz_deg : ∀ z : W, z ≠ u → z ≠ w₀ → ∃ x : W, x ≠ u ∧ x ≠ w₀ ∧ G.Adj z x) :
    IsPrimeGraph G := by
  have hcard₀ : 4 ≤ Fintype.card {v : W // v ≠ u} := hG₀.1
  refine ⟨le_trans hcard₀ (Fintype.card_subtype_le _), fun M hM => ?_⟩
  by_contra hM_ne1
  have hM_ge2 : 2 ≤ M.card := by
    have := hM.1.card_pos
    omega
  let W₀ := {v : W // v ≠ u}
  let G₀ := G.comap (Subtype.val : W₀ → W)
  let M₀ : Finset W₀ := Finset.univ.filter (fun v : W₀ => v.1 ∈ M)
  have hM₀_map : M₀.map ⟨Subtype.val, Subtype.val_injective⟩ = M.erase u := by
    ext x
    simp only [M₀, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk, Subtype.exists, Finset.mem_erase]
    exact ⟨fun ⟨a, ha, haM, hax⟩ => ⟨hax ▸ ha, hax ▸ haM⟩, fun ⟨hxu, hxM⟩ => ⟨x, hxu, hxM, rfl⟩⟩
  have hM₀_card : M₀.card = (M.erase u).card := by
    rw [← Finset.card_map ⟨Subtype.val, Subtype.val_injective⟩, hM₀_map]
  have hM₀_mod : IsModuleIn G₀ Finset.univ M₀ := by
    refine ⟨Finset.subset_univ _, fun z _ hz_not => ?_⟩
    have hz_not_M : z.1 ∉ M := fun h => hz_not (Finset.mem_filter.mpr ⟨Finset.mem_univ z, h⟩)
    rcases hM.2.2.2 z.1 (Finset.mem_univ _) hz_not_M with h_comp | h_anti
    · left
      intro v hv
      exact h_comp v.1 (Finset.mem_filter.mp hv).2
    · right
      intro v hv hadj
      exact h_anti v.1 (Finset.mem_filter.mp hv).2 hadj
  by_cases huM : u ∈ M
  · have hM₀_ge1 : 1 ≤ M₀.card := by
      rw [hM₀_card, Finset.card_erase_of_mem huM]
      omega
    have hM₀_ssub : M₀ ⊂ Finset.univ := by
      rw [Finset.ssubset_univ_iff]
      intro h_univ
      obtain ⟨y, _, hy_not⟩ := Finset.exists_of_ssubset hM.2.1
      have hy_ne_u : y ≠ u := fun h => hy_not (h ▸ huM)
      have hy_M₀ : (⟨y, hy_ne_u⟩ : W₀) ∈ M₀ := h_univ ▸ Finset.mem_univ _
      exact hy_not (Finset.mem_filter.mp hy_M₀).2
    have hM₀_prop : IsProperModuleIn G₀ Finset.univ M₀ :=
      ⟨Finset.card_pos.mp hM₀_ge1, hM₀_ssub, hM₀_mod⟩
    have hM₀_eq1 : M₀.card = 1 := hG₀.2 M₀ hM₀_prop
    obtain ⟨z₀, hz₀_eq⟩ := Finset.card_eq_one.mp hM₀_eq1
    let z := z₀.1
    have hz_u : z ≠ u := z₀.2
    have hz_M₀ : z₀ ∈ M₀ := hz₀_eq ▸ Finset.mem_singleton_self z₀
    have hz_M : z ∈ M := (Finset.mem_filter.mp hz_M₀).2
    have hx_equiv : ∀ x : W, x ≠ u → x ≠ z → (G.Adj x u ↔ G.Adj x z) := by
      intro x hxu hxz
      have hx_not_M : x ∉ M := by
        intro hxM
        have hxM₀ : (⟨x, hxu⟩ : W₀) ∈ M₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxM⟩
        rw [hz₀_eq, Finset.mem_singleton, Subtype.ext_iff] at hxM₀
        exact hxz hxM₀
      rcases hM.2.2.2 x (Finset.mem_univ _) hx_not_M with h_comp | h_anti
      · exact ⟨fun _ => h_comp z hz_M, fun _ => h_comp u huM⟩
      · exact ⟨fun h => False.elim (h_anti u huM h), fun h => False.elim (h_anti z hz_M h)⟩
    by_cases hzw₀ : z = w₀
    · obtain ⟨x, hxu, h_w₀_x⟩ := hw₀_deg
      have hxz : x ≠ z := fun h => G.loopless w₀ ((h.trans hzw₀) ▸ h_w₀_x)
      have h_xu : G.Adj x u := (hx_equiv x hxu hxz).mpr (hzw₀ ▸ G.symm h_w₀_x)
      have h_xw₀ : x = w₀ := (hu_adj x).mp (G.symm h_xu)
      exact hxz (h_xw₀.trans hzw₀.symm)
    · obtain ⟨x, hxu, hxw₀, h_z_x⟩ := hz_deg z hz_u hzw₀
      have hxz : x ≠ z := fun h => G.loopless z (h ▸ h_z_x)
      have h_xu : G.Adj x u := (hx_equiv x hxu hxz).mpr (G.symm h_z_x)
      exact hxw₀ ((hu_adj x).mp (G.symm h_xu))
  · have hM₀_ge2 : 2 ≤ M₀.card := by
      rw [hM₀_card, Finset.erase_eq_of_notMem huM]
      exact hM_ge2
    have hM₀_ssub : M₀ ⊂ Finset.univ := by
      rw [Finset.ssubset_univ_iff]
      intro h_univ
      have hw₀_M : w₀ ∈ M := by
        have hw₀_M₀ : (⟨w₀, hw₀_ne⟩ : W₀) ∈ M₀ := h_univ ▸ Finset.mem_univ _
        exact (Finset.mem_filter.mp hw₀_M₀).2
      have h_erase_card : (Finset.univ.erase (⟨w₀, hw₀_ne⟩ : W₀)).card = Fintype.card W₀ - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
      have h_erase_ne : (Finset.univ.erase (⟨w₀, hw₀_ne⟩ : W₀)).Nonempty := by
        rw [← Finset.card_pos, h_erase_card]
        have : 4 ≤ Fintype.card W₀ := hcard₀
        omega
      obtain ⟨y₀, hy₀⟩ := h_erase_ne
      have hy_ne_w₀ : y₀.1 ≠ w₀ := by
        have := (Finset.mem_erase.mp hy₀).1
        rwa [ne_eq, Subtype.ext_iff] at this
      have hy₀_M₀ : y₀ ∈ M₀ := h_univ ▸ Finset.mem_univ y₀
      have hy_M : y₀.1 ∈ M := (Finset.mem_filter.mp hy₀_M₀).2
      rcases hM.2.2.2 u (Finset.mem_univ _) huM with h_comp | h_anti
      · exact hy_ne_w₀ ((hu_adj y₀.1).mp (h_comp y₀.1 hy_M))
      · exact h_anti w₀ hw₀_M ((hu_adj w₀).mpr rfl)
    have hM₀_prop : IsProperModuleIn G₀ Finset.univ M₀ :=
      ⟨Finset.card_pos.mp (by omega), hM₀_ssub, hM₀_mod⟩
    have hM₀_eq1 : M₀.card = 1 := hG₀.2 M₀ hM₀_prop
    omega

/-- Dual version of `isPrimeGraph_of_add_leaf` for adding a co-leaf $u$ of co-degree $1$ in $G$ (`main.tex` line 1014). -/
theorem isPrimeGraph_of_add_coleaf {W : Type*} [Fintype W] [DecidableEq W]
    {G : SimpleGraph W} {u w₀ : W}
    (hG₀ : IsPrimeGraph (G.comap (Subtype.val : {v : W // v ≠ u} → W)))
    (hw₀_ne : w₀ ≠ u)
    (hu_adj : ∀ v : W, Gᶜ.Adj u v ↔ v = w₀)
    (hw₀_deg : ∃ x : W, x ≠ u ∧ Gᶜ.Adj w₀ x)
    (hz_deg : ∀ z : W, z ≠ u → z ≠ w₀ → ∃ x : W, x ≠ u ∧ x ≠ w₀ ∧ Gᶜ.Adj z x) :
    IsPrimeGraph G := by
  rw [← isPrimeGraph_compl_iff]
  have hG₀_compl : IsPrimeGraph (Gᶜ.comap (Subtype.val : {v : W // v ≠ u} → W)) := by
    have h_eq : Gᶜ.comap (Subtype.val : {v : W // v ≠ u} → W) =
        (G.comap (Subtype.val : {v : W // v ≠ u} → W))ᶜ := by
      ext a b
      simp only [comap_adj, compl_adj, ne_eq, Subtype.ext_iff]
    rw [h_eq, isPrimeGraph_compl_iff]
    exact hG₀
  exact isPrimeGraph_of_add_leaf hG₀_compl hw₀_ne hu_adj hw₀_deg hz_deg

/--
**Proposition 6(3) — Primality of `PrimeTowerGraph t k` (`primeTower_isPrimeGraph`, `main.tex` lines 1014–1016)**:
For every $t \ge 6$ and $k \ge 0$, `PrimeTowerGraph t k` ($H_{t+k}^{(t)}$) is a prime graph (`IsPrimeGraph`),
proved by induction on $k$ via `isPrimeGraph_of_add_leaf` (for even steps) and `isPrimeGraph_of_add_coleaf` (for odd steps).
-/
theorem primeTower_isPrimeGraph (t k : ℕ) (ht : 6 ≤ t) :
    IsPrimeGraph (PrimeTowerGraph t k) := by
  induction k with
  | zero =>
    exact (isPrimeGraph_pathGraph (by omega : 4 ≤ t)).of_iso (primeTowerZeroIsoPath t).symm
  | succ k ih =>
    let G := PrimeTowerGraph t (k + 1)
    let u : Fin (t + (k + 1)) := ⟨t + k, by omega⟩
    let w₀ : Fin (t + (k + 1)) := ⟨t + k - 1, by omega⟩
    have hG₀ : IsPrimeGraph (G.comap (Subtype.val : {v : Fin (t + (k + 1)) // v ≠ u} → Fin (t + (k + 1)))) :=
      ih.of_iso (primeTowerStepIso t k).symm
    have hw₀_ne : w₀ ≠ u := by
      simp only [ne_eq, Fin.ext_iff, w₀, u]
      omega
    by_cases hk_even : (k + 1) % 2 = 0
    · refine isPrimeGraph_of_add_leaf hG₀ hw₀_ne ?_ ?_ ?_
      · intro v
        have hv_bound := v.2
        by_cases hvu : v = u
        · subst hvu
          exact ⟨fun h => False.elim (G.loopless u h), fun h => False.elim (hw₀_ne h.symm)⟩
        · have hv_lt : v.1 < u.1 := by
            have := Fin.ext_iff.not.mp hvu
            dsimp [u] at this ⊢
            omega
          rw [G.adj_comm, primeTowerGraph_adj_of_lt hv_lt]
          unfold primeTowerAdjLt
          dsimp [u, w₀]
          rw [if_neg (by omega : ¬t + k < t),
            if_neg (by omega : ¬(t + k - t + 1) % 2 = 1)]
          rw [Fin.ext_iff]
          dsimp
          omega
      · refine ⟨⟨0, by omega⟩, by simp only [ne_eq, Fin.ext_iff, u]; omega, ?_⟩
        rw [G.adj_comm, primeTowerGraph_adj_of_lt (by dsimp [w₀]; omega)]
        unfold primeTowerAdjLt
        dsimp [w₀]
        rw [if_neg (by omega : ¬t + k - 1 < t),
          if_pos (by omega : (t + k - 1 - t + 1) % 2 = 1)]
        omega
      · intro z hzu hzw₀
        have hz_bound := z.2
        have hz_lt : z.1 < t + k - 1 := by
          have h1 := Fin.ext_iff.not.mp hzu
          have h2 := Fin.ext_iff.not.mp hzw₀
          dsimp [u, w₀] at h1 h2
          omega
        by_cases hz0 : z.1 = 0
        · refine ⟨⟨1, by omega⟩, by simp only [ne_eq, Fin.ext_iff, u]; omega,
            by simp only [ne_eq, Fin.ext_iff, w₀]; omega, ?_⟩
          rw [primeTowerGraph_adj_of_lt (by dsimp; omega)]
          unfold primeTowerAdjLt
          dsimp
          rw [if_pos (by omega : 1 < t)]
          omega
        · by_cases hzt : z.1 < t
          · refine ⟨⟨z.1 - 1, by omega⟩, by simp only [ne_eq, Fin.ext_iff, u]; omega,
              by simp only [ne_eq, Fin.ext_iff, w₀]; omega, ?_⟩
            rw [G.adj_comm, primeTowerGraph_adj_of_lt (by dsimp; omega)]
            unfold primeTowerAdjLt
            dsimp
            rw [if_pos hzt]
            omega
          · by_cases hz_par : (z.1 - t + 1) % 2 = 1
            · refine ⟨⟨0, by omega⟩, by simp only [ne_eq, Fin.ext_iff, u]; omega,
                by simp only [ne_eq, Fin.ext_iff, w₀]; omega, ?_⟩
              rw [G.adj_comm, primeTowerGraph_adj_of_lt (by dsimp; omega)]
              unfold primeTowerAdjLt
              dsimp
              rw [if_neg hzt, if_pos hz_par]
              omega
            · refine ⟨⟨z.1 - 1, by omega⟩, by simp only [ne_eq, Fin.ext_iff, u]; omega,
                by simp only [ne_eq, Fin.ext_iff, w₀]; omega, ?_⟩
              rw [G.adj_comm, primeTowerGraph_adj_of_lt (by dsimp; omega)]
              unfold primeTowerAdjLt
              dsimp
              rw [if_neg hzt, if_neg hz_par]
              omega
    · refine isPrimeGraph_of_add_coleaf hG₀ hw₀_ne ?_ ?_ ?_
      · intro v
        have hv_bound := v.2
        by_cases hvu : v = u
        · subst hvu
          exact ⟨fun h => False.elim (Gᶜ.loopless u h), fun h => False.elim (hw₀_ne h.symm)⟩
        · have hv_lt : v.1 < u.1 := by
            have := Fin.ext_iff.not.mp hvu
            dsimp [u] at this ⊢
            omega
          rw [compl_adj, G.adj_comm, primeTowerGraph_adj_of_lt hv_lt]
          unfold primeTowerAdjLt
          dsimp [u, w₀]
          rw [if_neg (by omega : ¬t + k < t),
            if_pos (by omega : (t + k - t + 1) % 2 = 1)]
          simp only [ne_eq, Fin.ext_iff, u, w₀]
          omega
      · refine ⟨⟨0, by omega⟩, by simp only [ne_eq, Fin.ext_iff, u]; omega, ?_⟩
        rw [compl_adj]
        refine ⟨by simp only [ne_eq, Fin.ext_iff, w₀]; omega, ?_⟩
        rw [G.adj_comm, primeTowerGraph_adj_of_lt (by dsimp [w₀]; omega)]
        unfold primeTowerAdjLt
        dsimp [w₀]
        by_cases hk0 : k = 0
        · rw [if_pos (by omega : t + k - 1 < t)]
          omega
        · rw [if_neg (by omega : ¬t + k - 1 < t),
            if_neg (by omega : ¬(t + k - 1 - t + 1) % 2 = 1)]
          omega
      · intro z hzu hzw₀
        have hz_bound := z.2
        have hz_lt : z.1 < t + k - 1 := by
          have h1 := Fin.ext_iff.not.mp hzu
          have h2 := Fin.ext_iff.not.mp hzw₀
          dsimp [u, w₀] at h1 h2
          omega
        by_cases hzt : z.1 < t
        · by_cases hz1 : z.1 ≤ 1
          · refine ⟨⟨3, by omega⟩, by simp only [ne_eq, Fin.ext_iff, u]; omega,
              by simp only [ne_eq, Fin.ext_iff, w₀]; omega, ?_⟩
            rw [compl_adj]
            refine ⟨by simp only [ne_eq, Fin.ext_iff]; omega, ?_⟩
            rw [primeTowerGraph_adj_of_lt (by dsimp; omega)]
            unfold primeTowerAdjLt
            dsimp
            rw [if_pos (by omega : 3 < t)]
            omega
          · refine ⟨⟨0, by omega⟩, by simp only [ne_eq, Fin.ext_iff, u]; omega,
              by simp only [ne_eq, Fin.ext_iff, w₀]; omega, ?_⟩
            rw [compl_adj]
            refine ⟨by simp only [ne_eq, Fin.ext_iff]; omega, ?_⟩
            rw [G.adj_comm, primeTowerGraph_adj_of_lt (by dsimp; omega)]
            unfold primeTowerAdjLt
            dsimp
            rw [if_pos hzt]
            omega
        · by_cases hz_par : (z.1 - t + 1) % 2 = 1
          · refine ⟨⟨z.1 - 1, by omega⟩, by simp only [ne_eq, Fin.ext_iff, u]; omega,
              by simp only [ne_eq, Fin.ext_iff, w₀]; omega, ?_⟩
            rw [compl_adj]
            refine ⟨by simp only [ne_eq, Fin.ext_iff]; omega, ?_⟩
            rw [G.adj_comm, primeTowerGraph_adj_of_lt (by dsimp; omega)]
            unfold primeTowerAdjLt
            dsimp
            rw [if_neg hzt, if_pos hz_par]
            omega
          · refine ⟨⟨0, by omega⟩, by simp only [ne_eq, Fin.ext_iff, u]; omega,
              by simp only [ne_eq, Fin.ext_iff, w₀]; omega, ?_⟩
            rw [compl_adj]
            refine ⟨by simp only [ne_eq, Fin.ext_iff]; omega, ?_⟩
            rw [G.adj_comm, primeTowerGraph_adj_of_lt (by dsimp; omega)]
            unfold primeTowerAdjLt
            dsimp
            rw [if_neg hzt, if_neg hz_par]
            omega
/-- Graph isomorphism induces an isomorphism of complements. -/
def complIso {W₁ W₂ : Type*} {G₁ : SimpleGraph W₁} {G₂ : SimpleGraph W₂}
    (e : G₁ ≃g G₂) : G₁ᶜ ≃g G₂ᶜ where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro a b
    change G₂ᶜ.Adj (e a) (e b) ↔ G₁ᶜ.Adj a b
    simp only [compl_adj, ne_eq, e.injective.eq_iff, e.map_rel_iff]

/-- `Gᶜ.comap Subtype.val` is isomorphic to `(G.comap Subtype.val)ᶜ`. -/
def complComapSubtypeIso {W : Type*} {G : SimpleGraph W} (u : W) :
    Gᶜ.comap (Subtype.val : {v : W // v ≠ u} → W) ≃g
      (G.comap (Subtype.val : {v : W // v ≠ u} → W))ᶜ where
  toEquiv := Equiv.refl _
  map_rel_iff' := by
    intro a b
    simp only [Equiv.refl_apply, comap_adj, compl_adj, ne_eq, Subtype.ext_iff]

/-- Equivalence `{v : Fin 2 // v ≠ 0} ⊕ Fin n ≃ {v : Fin (n + 2) // v ≠ ⟨n, _⟩}` deleting the second-to-last index `n`. -/
def equivDeleteSecondLast (n : ℕ) :
    {v : Fin 2 // v ≠ 0} ⊕ Fin n ≃ {v : Fin (n + 2) // v ≠ ⟨n, by omega⟩} where
  toFun s :=
    match s with
    | Sum.inl _ => ⟨⟨n + 1, by omega⟩, by simp only [ne_eq, Fin.ext_iff]; omega⟩
    | Sum.inr i => ⟨⟨i.1, by omega⟩, by have := i.2; simp only [ne_eq, Fin.ext_iff]; omega⟩
  invFun v :=
    if h : v.1.1 < n then Sum.inr ⟨v.1.1, h⟩
    else Sum.inl ⟨1, by decide⟩
  left_inv s := by
    rcases s with ⟨x, hx⟩ | i
    · dsimp
      rw [dif_neg (by omega)]
      congr 1
      ext
      fin_cases x
      · exact False.elim (hx rfl)
      · rfl
    · dsimp
      rw [if_pos i.2]
  right_inv v := by
    rcases v with ⟨⟨val, hlt⟩, hne⟩
    have hne' : val ≠ n := by simp only [ne_eq, Fin.ext_iff] at hne; exact hne
    dsimp
    by_cases h : val < n
    · rw [dif_pos h]
    · rw [dif_neg h]
      ext
      dsimp
      omega

/-- Explicit isomorphism $K_2[0 \leftarrow P_{t-1}] \simeq_g H_{t+1}^{(t)} - u_t$ (`main.tex` line 1016):
deleting vertex $u_t = \langle t - 1, \dots \rangle$ from `PrimeTowerGraph t 1` ($t \ge 2$) yields
`substGraph (⊤ : SimpleGraph (Fin 2)) 0 (pathGraph (t - 1))`. -/
def primeTowerOneDeleteIso (t : ℕ) (ht : 2 ≤ t) :
    substGraph (⊤ : SimpleGraph (Fin 2)) 0 (pathGraph (t - 1)) ≃g
      (PrimeTowerGraph t 1).comap
        (Subtype.val : {v : Fin (t + 1) // v ≠ ⟨t - 1, by omega⟩} → Fin (t + 1)) where
  toFun s :=
    match s with
    | Sum.inl _ => ⟨⟨t, by omega⟩, by simp only [ne_eq, Fin.ext_iff]; omega⟩
    | Sum.inr i => ⟨⟨i.1, by omega⟩, by have := i.2; simp only [ne_eq, Fin.ext_iff]; omega⟩
  invFun v :=
    if h : v.1.1 < t - 1 then Sum.inr ⟨v.1.1, h⟩
    else Sum.inl ⟨1, by decide⟩
  left_inv s := by
    rcases s with ⟨x, hx⟩ | i
    · dsimp
      rw [dif_neg (by omega)]
      congr 1
      ext
      fin_cases x
      · exact False.elim (hx rfl)
      · rfl
    · dsimp
      rw [if_pos i.2]
  right_inv v := by
    rcases v with ⟨⟨val, hlt⟩, hne⟩
    have hne' : val ≠ t - 1 := by simp only [ne_eq, Fin.ext_iff] at hne; exact hne
    dsimp
    by_cases h : val < t - 1
    · rw [dif_pos h]
    · rw [dif_neg h]
      ext
      dsimp
      omega
  map_rel_iff' := by
    intro a b
    rcases a with ⟨x, hx⟩ | i <;> rcases b with ⟨y, hy⟩ | j
    · simp only [comap_adj, substGraph, top_adj, ne_eq]
      dsimp
      constructor
      · intro h
        exact False.elim ((PrimeTowerGraph t 1).loopless _ h)
      · intro hxy
        exfalso
        fin_cases x
        · exact hx rfl
        · fin_cases y
          · exact hy rfl
          · exact hxy rfl
    · have hj := j.2
      simp only [comap_adj, substGraph, top_adj, ne_eq, hx, not_false_eq_true, iff_true]
      dsimp
      rw [(PrimeTowerGraph t 1).adj_comm, primeTowerGraph_adj_of_lt (by dsimp; omega)]
      unfold primeTowerAdjLt
      dsimp
      rw [if_neg (by omega : ¬t < t), if_pos (by omega : (t - t + 1) % 2 = 1)]
      omega
    · have hi := i.2
      simp only [comap_adj, substGraph, top_adj, ne_eq, hy.symm, not_false_eq_true, iff_true]
      dsimp
      rw [primeTowerGraph_adj_of_lt (by dsimp; omega)]
      unfold primeTowerAdjLt
      dsimp
      rw [if_neg (by omega : ¬t < t), if_pos (by omega : (t - t + 1) % 2 = 1)]
      omega
    · have hi := i.2
      have hj := j.2
      simp only [comap_adj, substGraph, pathGraph_adj]
      unfold PrimeTowerGraph primeTowerAdjLt
      dsimp
      by_cases hij : i.1 < j.1
      · rw [if_pos hij, if_pos (by omega : j.1 < t)]
        omega
      · by_cases hji : j.1 < i.1
        · rw [if_neg hij, if_pos hji, if_pos (by omega : i.1 < t)]
          omega
        · rw [if_neg hij, if_neg hji]
          simp only [false_iff]
          omega

/-- Explicit odd-step isomorphism $K_2[0 \leftarrow H_{t+m}^{(t)}] \simeq_g H_{t+m+2}^{(t)} - u_{t+m+1}$ (`main.tex` line 1016):
when `(m + 2) % 2 = 1`, deleting $u_{t+m+1} = \langle t + m, \dots \rangle$ from `PrimeTowerGraph t (m + 2)` yields
`substGraph (⊤ : SimpleGraph (Fin 2)) 0 (PrimeTowerGraph t m)`. -/
def primeTowerOddStepDeleteIso (t m : ℕ) (hm_odd : (m + 2) % 2 = 1) :
    substGraph (⊤ : SimpleGraph (Fin 2)) 0 (PrimeTowerGraph t m) ≃g
      (PrimeTowerGraph t (m + 2)).comap
        (Subtype.val : {v : Fin (t + (m + 2)) // v ≠ ⟨t + m, by omega⟩} → Fin (t + (m + 2))) where
  toFun s :=
    match s with
    | Sum.inl _ => ⟨⟨t + m + 1, by omega⟩, by simp only [ne_eq, Fin.ext_iff]; omega⟩
    | Sum.inr i => ⟨⟨i.1, by omega⟩, by have := i.2; simp only [ne_eq, Fin.ext_iff]; omega⟩
  invFun v :=
    if h : v.1.1 < t + m then Sum.inr ⟨v.1.1, h⟩
    else Sum.inl ⟨1, by decide⟩
  left_inv s := by
    rcases s with ⟨x, hx⟩ | i
    · dsimp
      rw [dif_neg (by omega)]
      congr 1
      ext
      fin_cases x
      · exact False.elim (hx rfl)
      · rfl
    · dsimp
      rw [if_pos i.2]
  right_inv v := by
    rcases v with ⟨⟨val, hlt⟩, hne⟩
    have hne' : val ≠ t + m := by simp only [ne_eq, Fin.ext_iff] at hne; exact hne
    dsimp
    by_cases h : val < t + m
    · rw [dif_pos h]
    · rw [dif_neg h]
      ext
      dsimp
      omega
  map_rel_iff' := by
    intro a b
    rcases a with ⟨x, hx⟩ | i <;> rcases b with ⟨y, hy⟩ | j
    · simp only [comap_adj, substGraph, top_adj, ne_eq]
      dsimp
      constructor
      · intro h
        exact False.elim ((PrimeTowerGraph t (m + 2)).loopless _ h)
      · intro hxy
        exfalso
        fin_cases x
        · exact hx rfl
        · fin_cases y
          · exact hy rfl
          · exact hxy rfl
    · have hj := j.2
      simp only [comap_adj, substGraph, top_adj, ne_eq, hx, not_false_eq_true, iff_true]
      dsimp
      rw [(PrimeTowerGraph t (m + 2)).adj_comm, primeTowerGraph_adj_of_lt (by dsimp; omega)]
      unfold primeTowerAdjLt
      dsimp
      rw [if_neg (by omega : ¬t + m + 1 < t), if_pos (by omega : (t + m + 1 - t + 1) % 2 = 1)]
      omega
    · have hi := i.2
      simp only [comap_adj, substGraph, top_adj, ne_eq, hy.symm, not_false_eq_true, iff_true]
      dsimp
      rw [primeTowerGraph_adj_of_lt (by dsimp; omega)]
      unfold primeTowerAdjLt
      dsimp
      rw [if_neg (by omega : ¬t + m + 1 < t), if_pos (by omega : (t + m + 1 - t + 1) % 2 = 1)]
      omega
    · simp only [comap_adj, substGraph]
      unfold PrimeTowerGraph
      rfl

/-- Explicit even-step complement isomorphism $K_2[0 \leftarrow \overline{H_{t+m}^{(t)}}] \simeq_g \overline{H_{t+m+2}^{(t)}} - u_{t+m+1}$ (`main.tex` line 1016):
when `(m + 2) % 2 = 0`, deleting $u_{t+m+1} = \langle t + m, \dots \rangle$ from `(PrimeTowerGraph t (m + 2))ᶜ` yields
`substGraph (⊤ : SimpleGraph (Fin 2)) 0 (PrimeTowerGraph t m)ᶜ`. -/
def primeTowerEvenStepDeleteComplIso (t m : ℕ) (hm_even : (m + 2) % 2 = 0) :
    substGraph (⊤ : SimpleGraph (Fin 2)) 0 (PrimeTowerGraph t m)ᶜ ≃g
      (PrimeTowerGraph t (m + 2))ᶜ.comap
        (Subtype.val : {v : Fin (t + (m + 2)) // v ≠ ⟨t + m, by omega⟩} → Fin (t + (m + 2))) where
  toFun s :=
    match s with
    | Sum.inl _ => ⟨⟨t + m + 1, by omega⟩, by simp only [ne_eq, Fin.ext_iff]; omega⟩
    | Sum.inr i => ⟨⟨i.1, by omega⟩, by have := i.2; simp only [ne_eq, Fin.ext_iff]; omega⟩
  invFun v :=
    if h : v.1.1 < t + m then Sum.inr ⟨v.1.1, h⟩
    else Sum.inl ⟨1, by decide⟩
  left_inv s := by
    rcases s with ⟨x, hx⟩ | i
    · dsimp
      rw [dif_neg (by omega)]
      congr 1
      ext
      fin_cases x
      · exact False.elim (hx rfl)
      · rfl
    · dsimp
      rw [if_pos i.2]
  right_inv v := by
    rcases v with ⟨⟨val, hlt⟩, hne⟩
    have hne' : val ≠ t + m := by simp only [ne_eq, Fin.ext_iff] at hne; exact hne
    dsimp
    by_cases h : val < t + m
    · rw [dif_pos h]
    · rw [dif_neg h]
      ext
      dsimp
      omega
  map_rel_iff' := by
    intro a b
    rcases a with ⟨x, hx⟩ | i <;> rcases b with ⟨y, hy⟩ | j
    · simp only [comap_adj, substGraph, top_adj, ne_eq]
      dsimp
      constructor
      · intro h
        exact False.elim ((PrimeTowerGraph t (m + 2))ᶜ.loopless _ h)
      · intro hxy
        exfalso
        fin_cases x
        · exact hx rfl
        · fin_cases y
          · exact hy rfl
          · exact hxy rfl
    · have hj := j.2
      simp only [comap_adj, substGraph, top_adj, ne_eq, hx, not_false_eq_true, iff_true]
      dsimp
      rw [compl_adj]
      refine ⟨by simp only [ne_eq, Fin.ext_iff]; omega, ?_⟩
      rw [(PrimeTowerGraph t (m + 2)).adj_comm, primeTowerGraph_adj_of_lt (by dsimp; omega)]
      unfold primeTowerAdjLt
      dsimp
      rw [if_neg (by omega : ¬t + m + 1 < t), if_neg (by omega : ¬(t + m + 1 - t + 1) % 2 = 1)]
      omega
    · have hi := i.2
      simp only [comap_adj, substGraph, top_adj, ne_eq, hy.symm, not_false_eq_true, iff_true]
      dsimp
      rw [compl_adj]
      refine ⟨by simp only [ne_eq, Fin.ext_iff]; omega, ?_⟩
      rw [primeTowerGraph_adj_of_lt (by dsimp; omega)]
      unfold primeTowerAdjLt
      dsimp
      rw [if_neg (by omega : ¬t + m + 1 < t), if_neg (by omega : ¬(t + m + 1 - t + 1) % 2 = 1)]
      omega
    · simp only [comap_adj, substGraph, compl_adj, ne_eq, Fin.ext_iff]
      unfold PrimeTowerGraph
      rfl

/--
**Proposition 6(3) — Membership of `PrimeTowerGraph t k` in $\mathcal{H}(\mathcal{B}_t^*)$ (`primeTower_inHClosure`, `main.tex` line 1016)**:
For every $t \ge 6$ and $k \ge 0$, both `PrimeTowerGraph t k` and `(PrimeTowerGraph t k)ᶜ` belong to `InJClosure t`,
so `InHClosure t (PrimeTowerGraph t k)` holds.
-/
theorem primeTower_inHClosure (t k : ℕ) (ht : 6 ≤ t) :
    InHClosure t (PrimeTowerGraph t k) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    have hk2 : InJClosure t (⊤ : SimpleGraph (Fin 2)) :=
      InJClosure.base _ (Or.inr (Or.inl ⟨SimpleGraph.Iso.refl⟩))
    rcases k with _ | k
    · constructor
      · have hp : InJClosure t (pathGraph t) :=
          InJClosure.base _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨t, by omega, le_refl t, Or.inl ⟨SimpleGraph.Iso.refl⟩⟩)))))
        exact InJClosure.iso _ _ hp ⟨(primeTowerZeroIsoPath t).symm⟩
      · have hpc : InJClosure t (pathGraph t)ᶜ :=
          InJClosure.base _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨t, by omega, le_refl t, Or.inr ⟨SimpleGraph.Iso.refl⟩⟩)))))
        exact InJClosure.iso _ _ hpc ⟨complIso (primeTowerZeroIsoPath t).symm⟩
    · have ih_k : InHClosure t (PrimeTowerGraph t k) := ih k (Nat.lt_succ_self k)
      rcases k with _ | m
      · -- Case k + 1 = 1
        let u : Fin (t + 1) := ⟨t, by omega⟩
        let w₀ : Fin (t + 1) := ⟨t - 1, by omega⟩
        constructor
        · -- PrimeTowerGraph t 1 ∈ InJClosure t via leaf w₀ = ⟨t - 1, _⟩
          have hw₀_deg : (neighborFinsetIn (PrimeTowerGraph t 1) w₀ Finset.univ).card ≤ 1 := by
            refine card_neighborFinsetIn_le_one_of_unique _ w₀ ⟨t - 2, by omega⟩ ?_
            intro v hadj
            have hv := v.2
            by_cases hvw : v.1 < w₀.1
            · rw [(PrimeTowerGraph t 1).adj_comm, primeTowerGraph_adj_of_lt hvw] at hadj
              unfold primeTowerAdjLt at hadj
              dsimp [w₀] at hvw hadj
              rw [if_pos (by omega : t - 1 < t)] at hadj
              ext; dsimp; omega
            · have hwv : w₀.1 < v.1 := by
                have hne : w₀ ≠ v := fun h => (PrimeTowerGraph t 1).loopless w₀ (h ▸ hadj)
                have := Fin.ext_iff.not.mp hne
                dsimp [w₀] at hvw this ⊢
                omega
              rw [primeTowerGraph_adj_of_lt hwv] at hadj
              unfold primeTowerAdjLt at hadj
              dsimp [w₀] at hwv hadj
              rw [if_neg (by omega : ¬v.1 < t), if_pos (by omega : (v.1 - t + 1) % 2 = 1)] at hadj
              omega
          have hp_prev : InJClosure t (pathGraph (t - 1)) :=
            InJClosure.base _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              ⟨t - 1, by omega, by omega, Or.inl ⟨SimpleGraph.Iso.refl⟩⟩)))))
          have h_subst : InJClosure t (substGraph (⊤ : SimpleGraph (Fin 2)) 0 (pathGraph (t - 1))) :=
            InJClosure.subst _ 0 _ hk2 hp_prev
          have h_del : InJClosure t ((PrimeTowerGraph t 1).comap
              (Subtype.val : {v : Fin (t + 1) // v ≠ w₀} → Fin (t + 1))) :=
            InJClosure.iso _ _ h_subst ⟨primeTowerOneDeleteIso t (by omega)⟩
          exact InJClosure.add_leaf _ w₀ hw₀_deg h_del
        · -- (PrimeTowerGraph t 1)ᶜ ∈ InJClosure t via leaf u = ⟨t, _⟩
          have hu_deg : (neighborFinsetIn (PrimeTowerGraph t 1)ᶜ u Finset.univ).card ≤ 1 := by
            refine card_neighborFinsetIn_le_one_of_unique _ u w₀ ?_
            intro v hadj
            have hv := v.2
            obtain ⟨huv_ne, hnadj⟩ := (compl_adj _ _ _).mp hadj
            have hv_lt : v.1 < u.1 := by
              have := Fin.ext_iff.not.mp huv_ne.symm
              dsimp [u] at this ⊢
              omega
            rw [(PrimeTowerGraph t 1).adj_comm, primeTowerGraph_adj_of_lt hv_lt] at hnadj
            unfold primeTowerAdjLt at hnadj
            dsimp [u] at hv_lt hnadj
            rw [if_neg (by omega : ¬t < t), if_pos (by omega : (t - t + 1) % 2 = 1)] at hnadj
            ext; dsimp [w₀]; omega
          have h_del : InJClosure t ((PrimeTowerGraph t 1)ᶜ.comap
              (Subtype.val : {v : Fin (t + 1) // v ≠ u} → Fin (t + 1))) :=
            InJClosure.iso _ _ ih_k.2
              ⟨(complIso (primeTowerStepIso t 0)).symm.trans (complComapSubtypeIso u).symm⟩
          exact InJClosure.add_leaf _ u hu_deg h_del
      · -- Case k + 1 = m + 2
        have ih_m : InHClosure t (PrimeTowerGraph t m) := ih m (by omega)
        let u : Fin (t + (m + 2)) := ⟨t + (m + 1), by omega⟩
        let w₀ : Fin (t + (m + 2)) := ⟨t + m, by omega⟩
        by_cases hm_even : (m + 2) % 2 = 0
        · constructor
          · -- PrimeTowerGraph t (m + 2) ∈ InJClosure t via leaf u
            have hu_deg : (neighborFinsetIn (PrimeTowerGraph t (m + 2)) u Finset.univ).card ≤ 1 := by
              refine card_neighborFinsetIn_le_one_of_unique _ u w₀ ?_
              intro v hadj
              have hv := v.2
              have huv_ne : u ≠ v := fun h => (PrimeTowerGraph t (m + 2)).loopless u (h ▸ hadj)
              have hv_lt : v.1 < u.1 := by
                have := Fin.ext_iff.not.mp huv_ne.symm
                dsimp [u] at this ⊢
                omega
              rw [(PrimeTowerGraph t (m + 2)).adj_comm, primeTowerGraph_adj_of_lt hv_lt] at hadj
              unfold primeTowerAdjLt at hadj
              dsimp [u] at hv_lt hadj
              rw [if_neg (by omega : ¬t + (m + 1) < t),
                if_neg (by omega : ¬(t + (m + 1) - t + 1) % 2 = 1)] at hadj
              ext; dsimp [w₀]; omega
            have h_del : InJClosure t ((PrimeTowerGraph t (m + 2)).comap
                (Subtype.val : {v : Fin (t + (m + 2)) // v ≠ u} → Fin (t + (m + 2)))) :=
              InJClosure.iso _ _ ih_k.1 ⟨(primeTowerStepIso t (m + 1)).symm⟩
            exact InJClosure.add_leaf _ u hu_deg h_del
          · -- (PrimeTowerGraph t (m + 2))ᶜ ∈ InJClosure t via leaf w₀ = ⟨t + m, _⟩
            have hw₀_deg : (neighborFinsetIn (PrimeTowerGraph t (m + 2))ᶜ w₀ Finset.univ).card ≤ 1 := by
              refine card_neighborFinsetIn_le_one_of_unique _ w₀ ⟨t + m - 1, by omega⟩ ?_
              intro v hadj
              have hv := v.2
              obtain ⟨hwv_ne, hnadj⟩ := (compl_adj _ _ _).mp hadj
              by_cases hvw : v.1 < w₀.1
              · rw [(PrimeTowerGraph t (m + 2)).adj_comm, primeTowerGraph_adj_of_lt hvw] at hnadj
                unfold primeTowerAdjLt at hnadj
                dsimp [w₀] at hvw hnadj
                rw [if_neg (by omega : ¬t + m < t),
                  if_pos (by omega : (t + m - t + 1) % 2 = 1)] at hnadj
                ext; dsimp; omega
              · have hwv : w₀.1 < v.1 := by
                  have := Fin.ext_iff.not.mp hwv_ne
                  dsimp [w₀] at hvw this ⊢
                  omega
                rw [primeTowerGraph_adj_of_lt hwv] at hnadj
                unfold primeTowerAdjLt at hnadj
                dsimp [w₀] at hwv hnadj
                rw [if_neg (by omega : ¬v.1 < t),
                  if_neg (by omega : ¬(v.1 - t + 1) % 2 = 1)] at hnadj
                omega
            have h_subst : InJClosure t (substGraph (⊤ : SimpleGraph (Fin 2)) 0 (PrimeTowerGraph t m)ᶜ) :=
              InJClosure.subst _ 0 _ hk2 ih_m.2
            have h_del : InJClosure t ((PrimeTowerGraph t (m + 2))ᶜ.comap
                (Subtype.val : {v : Fin (t + (m + 2)) // v ≠ w₀} → Fin (t + (m + 2)))) :=
              InJClosure.iso _ _ h_subst ⟨primeTowerEvenStepDeleteComplIso t m hm_even⟩
            exact InJClosure.add_leaf _ w₀ hw₀_deg h_del
        · have hm_odd : (m + 2) % 2 = 1 := by omega
          constructor
          · -- PrimeTowerGraph t (m + 2) ∈ InJClosure t via leaf w₀ = ⟨t + m, _⟩
            have hw₀_deg : (neighborFinsetIn (PrimeTowerGraph t (m + 2)) w₀ Finset.univ).card ≤ 1 := by
              refine card_neighborFinsetIn_le_one_of_unique _ w₀ ⟨t + m - 1, by omega⟩ ?_
              intro v hadj
              have hv := v.2
              have hwv_ne : w₀ ≠ v := fun h => (PrimeTowerGraph t (m + 2)).loopless w₀ (h ▸ hadj)
              by_cases hvw : v.1 < w₀.1
              · rw [(PrimeTowerGraph t (m + 2)).adj_comm, primeTowerGraph_adj_of_lt hvw] at hadj
                unfold primeTowerAdjLt at hadj
                dsimp [w₀] at hvw hadj
                rw [if_neg (by omega : ¬t + m < t),
                  if_neg (by omega : ¬(t + m - t + 1) % 2 = 1)] at hadj
                ext; dsimp; omega
              · have hwv : w₀.1 < v.1 := by
                  have := Fin.ext_iff.not.mp hwv_ne
                  dsimp [w₀] at hvw this ⊢
                  omega
                rw [primeTowerGraph_adj_of_lt hwv] at hadj
                unfold primeTowerAdjLt at hadj
                dsimp [w₀] at hwv hadj
                rw [if_neg (by omega : ¬v.1 < t),
                  if_pos (by omega : (v.1 - t + 1) % 2 = 1)] at hadj
                omega
            have h_subst : InJClosure t (substGraph (⊤ : SimpleGraph (Fin 2)) 0 (PrimeTowerGraph t m)) :=
              InJClosure.subst _ 0 _ hk2 ih_m.1
            have h_del : InJClosure t ((PrimeTowerGraph t (m + 2)).comap
                (Subtype.val : {v : Fin (t + (m + 2)) // v ≠ w₀} → Fin (t + (m + 2)))) :=
              InJClosure.iso _ _ h_subst ⟨primeTowerOddStepDeleteIso t m hm_odd⟩
            exact InJClosure.add_leaf _ w₀ hw₀_deg h_del
          · -- (PrimeTowerGraph t (m + 2))ᶜ ∈ InJClosure t via leaf u
            have hu_deg : (neighborFinsetIn (PrimeTowerGraph t (m + 2))ᶜ u Finset.univ).card ≤ 1 := by
              refine card_neighborFinsetIn_le_one_of_unique _ u w₀ ?_
              intro v hadj
              have hv := v.2
              obtain ⟨huv_ne, hnadj⟩ := (compl_adj _ _ _).mp hadj
              have hv_lt : v.1 < u.1 := by
                have := Fin.ext_iff.not.mp huv_ne.symm
                dsimp [u] at this ⊢
                omega
              rw [(PrimeTowerGraph t (m + 2)).adj_comm, primeTowerGraph_adj_of_lt hv_lt] at hnadj
              unfold primeTowerAdjLt at hnadj
              dsimp [u] at hv_lt hnadj
              rw [if_neg (by omega : ¬t + (m + 1) < t),
                if_pos (by omega : (t + (m + 1) - t + 1) % 2 = 1)] at hnadj
              ext; dsimp [w₀]; omega
            have h_del : InJClosure t ((PrimeTowerGraph t (m + 2))ᶜ.comap
                (Subtype.val : {v : Fin (t + (m + 2)) // v ≠ u} → Fin (t + (m + 2)))) :=
              InJClosure.iso _ _ ih_k.2
                ⟨(complIso (primeTowerStepIso t (m + 1))).symm.trans (complComapSubtypeIso u).symm⟩
            exact InJClosure.add_leaf _ u hu_deg h_del
/-- Graph embedding induces an embedding of complements. -/
def complEmbedding {W₁ W₂ : Type*} {G₁ : SimpleGraph W₁} {G₂ : SimpleGraph W₂}
    (f : G₁ ↪g G₂) : G₁ᶜ ↪g G₂ᶜ where
  toEmbedding := f.toEmbedding
  map_rel_iff' := by
    intro a b
    change G₂ᶜ.Adj (f a) (f b) ↔ G₁ᶜ.Adj a b
    simp only [compl_adj, ne_eq, f.injective.eq_iff, f.map_rel_iff]

/--
Structural invariant on $\mathcal{J}(\{K_1, K_2, \overline{K_2}, C_5\})$ (`InJClosureC5`, `main.tex` line 1016):
every prime induced subgraph $G \hookrightarrow_g H$ of order $|V(G)| \ge 6$ has a vertex of degree at most $1$.
-/
def HasNoLargeMinDegTwoPrimeInduced {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) : Prop :=
  ∀ {U : Type} [Fintype U] [DecidableEq U] (G : SimpleGraph U),
    Nonempty (G ↪g H) → 6 ≤ Fintype.card U → IsPrimeGraph G →
      ∃ u₀ : U, (neighborFinsetIn G u₀ Finset.univ).card ≤ 1

/-- Every graph $H \in \mathcal{J}(\{K_1, K_2, \overline{K_2}, C_5\})$ (`InJClosureC5`) satisfies `HasNoLargeMinDegTwoPrimeInduced`,
proved by induction on the closure construction (`k1`, `k2`, `k2_compl`, `c5` have $\le 5$ vertices, `add_leaf` restricts
degree $\le 1$, and `subst` collapses any prime induced subgraph into one of the two factors). -/
theorem inJClosureC5_hasNoLargeMinDegTwoPrimeInduced {W : Type} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} (hH : InJClosureC5 H) :
    HasNoLargeMinDegTwoPrimeInduced H := by
  induction hH with
  | k1 | k2 | k2_compl | c5 =>
    intro U _ _ G ⟨f⟩ hcard _
    have hle := Fintype.card_le_of_injective f f.injective
    simp only [Fintype.card_fin] at hle
    omega
  | iso H₁ H₂ _ h_iso ih =>
    obtain ⟨e⟩ := h_iso
    intro U _ _ G ⟨f⟩ hcard hprime
    let f₁ : G ↪g H₁ :=
      { toEmbedding := f.toEmbedding.trans e.symm.toEquiv.toEmbedding
        map_rel_iff' := by
          intro u₁ u₂
          simp only [Function.Embedding.trans_apply]
          change H₁.Adj (e.symm (f u₁)) (e.symm (f u₂)) ↔ G.Adj u₁ u₂
          rw [e.symm.map_rel_iff, f.map_rel_iff] }
    exact ih G ⟨f₁⟩ hcard hprime
  | add_leaf H v₀ hdeg _ ih =>
    intro U _ _ G ⟨f⟩ hcard hprime
    by_cases h_hit : ∃ u₀ : U, f u₀ = v₀
    · obtain ⟨u₀, hu₀⟩ := h_hit
      refine ⟨u₀, ?_⟩
      have h_sub : (neighborFinsetIn G u₀ Finset.univ).map f.toEmbedding ⊆
          neighborFinsetIn H v₀ Finset.univ := by
        intro w hw
        rcases Finset.mem_map.mp hw with ⟨u, hu, rfl⟩
        rw [mem_neighborFinsetIn_iff] at hu ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        have hadj : H.Adj (f u₀) (f u) := f.map_rel_iff.mpr hu.2
        rwa [hu₀] at hadj
      calc (neighborFinsetIn G u₀ Finset.univ).card
          = ((neighborFinsetIn G u₀ Finset.univ).map f.toEmbedding).card := (Finset.card_map _).symm
        _ ≤ (neighborFinsetIn H v₀ Finset.univ).card := Finset.card_le_card h_sub
        _ ≤ 1 := hdeg
    · push_neg at h_hit
      let f' : G ↪g H.comap (Subtype.val : {v : _ // v ≠ v₀} → _) :=
        { toEmbedding := ⟨fun u => ⟨f u, h_hit u⟩, fun u₁ u₂ h => f.injective (Subtype.ext_iff.mp h)⟩
          map_rel_iff' := by
            intro u₁ u₂
            exact f.map_rel_iff }
      exact ih G ⟨f'⟩ hcard hprime
  | subst H₁ v₀ H₂ _ _ ih₁ ih₂ =>
    intro U _ _ G ⟨f⟩ hcard hprime
    classical
    let M₂ : Finset U := Finset.univ.filter (fun u => ∃ y, f u = Sum.inr y)
    by_cases hM₂_univ : M₂ = Finset.univ
    · have h_inr : ∀ u : U, ∃ y, f u = Sum.inr y := by
        intro u
        have hu : u ∈ M₂ := hM₂_univ ▸ Finset.mem_univ u
        exact (Finset.mem_filter.mp hu).2
      let f₂ : G ↪g H₂ :=
        { toEmbedding := ⟨fun u => Classical.choose (h_inr u), by
            intro u₁ u₂ h
            dsimp at h
            have h₁ := Classical.choose_spec (h_inr u₁)
            have h₂ := Classical.choose_spec (h_inr u₂)
            exact f.injective (h₁.trans ((congr_arg Sum.inr h).trans h₂.symm))⟩
          map_rel_iff' := by
            intro u₁ u₂
            have h₁ := Classical.choose_spec (h_inr u₁)
            have h₂ := Classical.choose_spec (h_inr u₂)
            simp only [Function.Embedding.coeFn_mk]
            have h_adj : (substGraph H₁ v₀ H₂).Adj (f u₁) (f u₂) ↔
                H₂.Adj (Classical.choose (h_inr u₁)) (Classical.choose (h_inr u₂)) :=
              Eq.to_iff (congrArg₂ (substGraph H₁ v₀ H₂).Adj h₁ h₂)
            exact h_adj.symm.trans f.map_rel_iff }
      exact ih₂ G ⟨f₂⟩ hcard hprime
    · have hM₂_le_one : M₂.card ≤ 1 := by
        by_cases hM₂_ne : M₂.Nonempty
        · have hM₂_ssub : M₂ ⊂ Finset.univ := Finset.ssubset_univ_iff.mpr hM₂_univ
          have hM₂_mod : IsModuleIn G Finset.univ M₂ := by
            refine ⟨Finset.subset_univ _, fun z _ hz_not => ?_⟩
            rcases hfz : f z with x_z | y_z
            · by_cases hadj : H₁.Adj x_z.1 v₀
              · left
                intro u hu
                obtain ⟨y_u, hfu⟩ := (Finset.mem_filter.mp hu).2
                rw [← f.map_rel_iff, hfz, hfu]
                exact hadj
              · right
                intro u hu h_zu
                obtain ⟨y_u, hfu⟩ := (Finset.mem_filter.mp hu).2
                rw [← f.map_rel_iff, hfz, hfu] at h_zu
                exact hadj h_zu
            · exfalso
              exact hz_not (Finset.mem_filter.mpr ⟨Finset.mem_univ z, y_z, hfz⟩)
          exact le_of_eq (hprime.2 M₂ ⟨hM₂_ne, hM₂_ssub, hM₂_mod⟩)
        · rw [Finset.not_nonempty_iff_eq_empty.mp hM₂_ne, Finset.card_empty]
          omega
      let g : U → _ := fun u =>
        match f u with
        | Sum.inl x => x.1
        | Sum.inr _ => v₀
      have hg_inj : Function.Injective g := by
        intro u₁ u₂ hg_eq
        dsimp [g] at hg_eq
        rcases hfu₁ : f u₁ with x₁ | y₁ <;> rcases hfu₂ : f u₂ with x₂ | y₂
        · rw [hfu₁, hfu₂] at hg_eq
          dsimp at hg_eq
          exact f.injective (by rw [hfu₁, hfu₂, Subtype.ext hg_eq])
        · rw [hfu₁, hfu₂] at hg_eq
          dsimp at hg_eq
          exact False.elim (x₁.2 hg_eq)
        · rw [hfu₁, hfu₂] at hg_eq
          dsimp at hg_eq
          exact False.elim (x₂.2 hg_eq.symm)
        · have hu₁ : u₁ ∈ M₂ := Finset.mem_filter.mpr ⟨Finset.mem_univ u₁, y₁, hfu₁⟩
          have hu₂ : u₂ ∈ M₂ := Finset.mem_filter.mpr ⟨Finset.mem_univ u₂, y₂, hfu₂⟩
          exact Finset.card_le_one.mp hM₂_le_one u₁ hu₁ u₂ hu₂
      let f₁ : G ↪g H₁ :=
        { toEmbedding := ⟨g, hg_inj⟩
          map_rel_iff' := by
            intro u₁ u₂
            simp only [Function.Embedding.coeFn_mk]
            dsimp [g]
            rw [← f.map_rel_iff]
            rcases hfu₁ : f u₁ with x₁ | y₁ <;> rcases hfu₂ : f u₂ with x₂ | y₂
            · rfl
            · rfl
            · rfl
            · have hu₁ : u₁ ∈ M₂ := Finset.mem_filter.mpr ⟨Finset.mem_univ u₁, y₁, hfu₁⟩
              have hu₂ : u₂ ∈ M₂ := Finset.mem_filter.mpr ⟨Finset.mem_univ u₂, y₂, hfu₂⟩
              have hu_eq : u₁ = u₂ := Finset.card_le_one.mp hM₂_le_one u₁ hu₁ u₂ hu₂
              have hy_eq : y₁ = y₂ := Sum.inr.inj (hfu₁.symm.trans (hu_eq ▸ hfu₂))
              subst hy_eq
              exact ⟨fun h => False.elim (H₁.loopless v₀ h),
                fun h => False.elim (H₂.loopless y₁ h)⟩ }
      exact ih₁ G ⟨f₁⟩ hcard hprime

/-- For every $t \ge 6$, every vertex in `(pathGraph t)ᶜ` ($\overline{P_t}$) has degree at least $2$
(in fact $\delta(\overline{P_t}) = t - 3 \ge 3$, `main.tex` line 1016). -/
theorem pathGraphCompl_min_deg_ge_two {t : ℕ} (ht : 6 ≤ t) (v : Fin t) :
    2 ≤ (neighborFinsetIn (pathGraph t)ᶜ v Finset.univ).card := by
  have hv := v.2
  by_cases hv2 : v.1 ≤ 2
  · let a : Fin t := ⟨4, by omega⟩
    let b : Fin t := ⟨5, by omega⟩
    have hab : a ≠ b := by simp only [ne_eq, Fin.ext_iff, a, b]; omega
    have hsub : ({a, b} : Finset (Fin t)) ⊆ neighborFinsetIn (pathGraph t)ᶜ v Finset.univ := by
      intro x hx
      rw [mem_neighborFinsetIn_iff]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [compl_adj, pathGraph_adj]
      rcases Finset.mem_insert.mp hx with rfl | hxb
      · simp only [ne_eq, Fin.ext_iff, a]; omega
      · rw [Finset.mem_singleton.mp hxb]
        simp only [ne_eq, Fin.ext_iff, b]; omega
    calc 2 = ({a, b} : Finset (Fin t)).card := (Finset.card_pair hab).symm
      _ ≤ (neighborFinsetIn (pathGraph t)ᶜ v Finset.univ).card := Finset.card_le_card hsub
  · let a : Fin t := ⟨0, by omega⟩
    let b : Fin t := ⟨1, by omega⟩
    have hab : a ≠ b := by simp only [ne_eq, Fin.ext_iff, a, b]; omega
    have hsub : ({a, b} : Finset (Fin t)) ⊆ neighborFinsetIn (pathGraph t)ᶜ v Finset.univ := by
      intro x hx
      rw [mem_neighborFinsetIn_iff]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [compl_adj, pathGraph_adj]
      rcases Finset.mem_insert.mp hx with rfl | hxb
      · simp only [ne_eq, Fin.ext_iff, a]; omega
      · rw [Finset.mem_singleton.mp hxb]
        simp only [ne_eq, Fin.ext_iff, b]; omega
    calc 2 = ({a, b} : Finset (Fin t)).card := (Finset.card_pair hab).symm
      _ ≤ (neighborFinsetIn (pathGraph t)ᶜ v Finset.univ).card := Finset.card_le_card hsub

/--
**Proposition 6(3) — Non-Membership of `(PrimeTowerGraph t k)ᶜ` in $\mathcal{J}(\{K_1, K_2, \overline{K_2}, C_5\})$ (`primeTowerCompl_not_inJClosureC5`, `main.tex` line 1016)**:
For every $t \ge 6$ and $k \ge 0$, `(PrimeTowerGraph t k)ᶜ` does not belong to `InJClosureC5`,
since $\overline{P_t} \hookrightarrow_g \overline{H_{t+k}^{(t)}}$ is prime of order $t \ge 6$ with minimum degree $\ge 2$.
-/
theorem primeTowerCompl_not_inJClosureC5 (t k : ℕ) (ht : 6 ≤ t) :
    ¬InJClosureC5 (PrimeTowerGraph t k)ᶜ := by
  intro hH
  have h_inv : HasNoLargeMinDegTwoPrimeInduced (PrimeTowerGraph t k)ᶜ :=
    inJClosureC5_hasNoLargeMinDegTwoPrimeInduced hH
  have h_emb : Nonempty ((pathGraph t)ᶜ ↪g (PrimeTowerGraph t k)ᶜ) :=
    ⟨complEmbedding (pathGraphEmbPrimeTower (le_refl t))⟩
  have h_card : 6 ≤ Fintype.card (Fin t) := by
    rw [Fintype.card_fin]
    exact ht
  have h_prime : IsPrimeGraph (pathGraph t)ᶜ :=
    (isPrimeGraph_compl_iff _).mpr (isPrimeGraph_pathGraph (by omega))
  obtain ⟨u₀, hu₀⟩ := h_inv (pathGraph t)ᶜ h_emb h_card h_prime
  have h_ge2 := pathGraphCompl_min_deg_ge_two ht u₀
  omega

/--
**Proposition 6(3) — Non-Membership of `PrimeTowerGraph t k` in the Symmetric $C_5$-Closure (`primeTower_not_inHClosureC5`, `main.tex` line 1016)**:
For every $t \ge 6$ and $k \ge 0$, `PrimeTowerGraph t k` does not belong to
$\mathcal{H}(\{K_1, K_2, \overline{K_2}, C_5\}) := \mathcal{J}(\{K_1, K_2, \overline{K_2}, C_5\}) \cap \overline{\mathcal{J}(\{K_1, K_2, \overline{K_2}, C_5\})}$.
-/
theorem primeTower_not_inHClosureC5 (t k : ℕ) (ht : 6 ≤ t) :
    ¬(InJClosureC5 (PrimeTowerGraph t k) ∧ InJClosureC5 (PrimeTowerGraph t k)ᶜ) :=
  fun h => primeTowerCompl_not_inJClosureC5 t k ht h.2

/-! ### Axiom Verification -/

#print axioms forest_in_InJClosure
#print axioms eGraph_in_InJClosure_one
#print axioms birdGraph_in_InJClosure_one
#print axioms witnessHBird_inHClosure_one
#print axioms bird_isThresholdedWonderful
#print axioms bird_comb_dichotomy
#print axioms broom_in_subst_closure
#print axioms hook4_defective_neighborhood_module
#print axioms hook4_comb_dichotomy
#print axioms primeTower_iso_iff_eq
#print axioms primeTower_not_isSplitGraph
#print axioms primeTower_isPrimeGraph
#print axioms primeTower_inHClosure
#print axioms primeTowerCompl_not_inJClosureC5
#print axioms primeTower_not_inHClosureC5

end ErdosHajnalGen
