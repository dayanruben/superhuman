/-
Copyright 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosHajnal.AllPathsDefs
import ErdosHajnal.BasicLemmas
import ErdosHajnal.BirdBroomsForestsAndTowers
import ErdosHajnal.CombModules
import ErdosHajnal.Defs
import ErdosHajnal.GallaiAndCombDichotomy
import ErdosHajnal.GenDefs
import ErdosHajnal.P6Baseline
import ErdosHajnal.RecursiveGallaiAndStage1
import ErdosHajnal.SymmetricStage12Interface
import ErdosHajnal.ViralityAndClosures

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 800000

open Filter Finset SimpleGraph Real ErdosHajnalP6

namespace ErdosHajnalGen

instance instDecidableIsProperModuleInUniv {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (M : Finset W) :
    Decidable (IsProperModuleIn G Finset.univ M) := by
  unfold IsProperModuleIn IsModuleIn IsVertexPureTo
  infer_instance

/-- If $|W| \ge 6$ and every vertex of $H$ has degree $\le |W| - 3$, then every vertex of $Hᶜ$
has degree $\ge 2$. -/
theorem compl_minDeg_ge_two_of_maxDeg_le {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W)
    (hcard : 6 ≤ Fintype.card W)
    (hmax : ∀ u : W, (neighborFinsetIn H u Finset.univ).card ≤ Fintype.card W - 3) :
    ∀ u : W, 2 ≤ (neighborFinsetIn Hᶜ u Finset.univ).card := by
  classical
  intro u
  have hdisj : Disjoint (neighborFinsetIn H u Finset.univ) (neighborFinsetIn Hᶜ u Finset.univ) := by
    rw [Finset.disjoint_left]
    intro v hv₁ hv₂
    rw [ErdosHajnalP6.mem_neighborFinsetIn_iff] at hv₁ hv₂
    exact hv₂.2.2 hv₁.2
  have hunion : neighborFinsetIn H u Finset.univ ∪ neighborFinsetIn Hᶜ u Finset.univ =
      Finset.univ.erase u := by
    ext v
    simp only [Finset.mem_union, ErdosHajnalP6.mem_neighborFinsetIn_iff, Finset.mem_univ, true_and,
      compl_adj, Finset.mem_erase, ne_eq]
    by_cases huv : u = v
    · subst huv; simp
    · simp only [huv, not_false_eq_true, Ne.symm huv, true_and]; tauto
  have hsum : (neighborFinsetIn H u Finset.univ).card + (neighborFinsetIn Hᶜ u Finset.univ).card =
      Fintype.card W - 1 := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion,
      Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ]
  have hle := hmax u
  omega

/-- Vertex substitution `substGraph H₁ v₀ H₂` with $|W_1|, |W_2| \ge 2$ contains the non-trivial
proper module `Finset.univ.image Sum.inr` of cardinality $|W_2| \ge 2$, so it is never prime. -/
theorem not_isPrimeGraph_substGraph_esc {W₁ W₂ : Type*} [Fintype W₁] [DecidableEq W₁]
    [Fintype W₂] [DecidableEq W₂]
    (H₁ : SimpleGraph W₁) (v₀ : W₁) (H₂ : SimpleGraph W₂)
    (hW₁ : 2 ≤ Fintype.card W₁) (hW₂ : 2 ≤ Fintype.card W₂) :
    ¬IsPrimeGraph (substGraph H₁ v₀ H₂) := by
  classical
  intro hprime
  let M : Finset ({v : W₁ // v ≠ v₀} ⊕ W₂) := Finset.univ.image Sum.inr
  have hM_card : M.card = Fintype.card W₂ := by
    dsimp [M]
    rw [Finset.card_image_of_injective _ Sum.inr_injective, Finset.card_univ]
  have hM_ne : M.Nonempty := by
    rw [← Finset.card_pos, hM_card]; omega
  have hsub_ne : Nonempty {v : W₁ // v ≠ v₀} := by
    by_contra! hemp
    have h0 : Fintype.card {v : W₁ // v ≠ v₀} = 0 := Fintype.card_eq_zero
    have hc : Fintype.card {v : W₁ // v ≠ v₀} = Fintype.card W₁ - 1 := by
      rw [Fintype.card_subtype_compl, Fintype.card_ofSubsingleton]
    omega
  obtain ⟨u₀⟩ := hsub_ne
  have hM_ssub : M ⊂ Finset.univ := by
    rw [Finset.ssubset_univ_iff]
    intro huniv
    have hu : (Sum.inl u₀ : {v : W₁ // v ≠ v₀} ⊕ W₂) ∈ M := huniv ▸ Finset.mem_univ _
    rcases Finset.mem_image.mp hu with ⟨y, _, hy⟩
    cases hy
  have hM_mod : IsModuleIn (substGraph H₁ v₀ H₂) Finset.univ M := by
    refine ⟨Finset.subset_univ _, fun z _ hz_not => ?_⟩
    cases z with
    | inl x =>
      by_cases hadj : H₁.Adj x.1 v₀
      · left
        intro u hu; rcases Finset.mem_image.mp hu with ⟨y, _, rfl⟩; exact hadj
      · right
        intro u hu; rcases Finset.mem_image.mp hu with ⟨y, _, rfl⟩; exact hadj
    | inr y =>
      exact False.elim (hz_not (Finset.mem_image_of_mem Sum.inr (Finset.mem_univ y)))
  have h1 : M.card = 1 := hprime.2 M ⟨hM_ne, hM_ssub, hM_mod⟩
  omega

/-- Isomorphism transport of vertex degrees: `deg_{G₂}(e u) = deg_{G₁}(u)`. -/
lemma neighborFinsetIn_card_iso {W₁ W₂ : Type*} [Fintype W₁] [DecidableEq W₁]
    [Fintype W₂] [DecidableEq W₂] {G₁ : SimpleGraph W₁} {G₂ : SimpleGraph W₂}
    (e : G₁ ≃g G₂) (u : W₁) :
    (neighborFinsetIn G₂ (e u) Finset.univ).card =
      (neighborFinsetIn G₁ u Finset.univ).card := by
  classical
  refine Finset.card_bij (fun w _ => e.symm w) ?_ ?_ ?_
  · intro w hw
    rw [ErdosHajnalP6.mem_neighborFinsetIn_iff] at hw ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have h1 := (e.map_rel_iff (a := u) (b := e.symm w)).mp
    simp only [RelIso.apply_symm_apply] at h1
    exact h1 hw.2
  · intro w₁ _ w₂ _ h_eq; exact e.symm.injective h_eq
  · intro x hx
    rw [ErdosHajnalP6.mem_neighborFinsetIn_iff] at hx
    refine ⟨e x, ?_, e.symm_apply_apply x⟩
    rw [ErdosHajnalP6.mem_neighborFinsetIn_iff]
    exact ⟨Finset.mem_univ _, e.map_rel_iff.mpr hx.2⟩

/-- Isomorphism invariance of minimum degree $\ge 2$. -/
theorem minDeg_ge_two_of_iso {W₁ W₂ : Type*} [Fintype W₁] [DecidableEq W₁]
    [Fintype W₂] [DecidableEq W₂] {G₁ : SimpleGraph W₁} {G₂ : SimpleGraph W₂}
    (e : G₁ ≃g G₂) (h₂ : ∀ u : W₂, 2 ≤ (neighborFinsetIn G₂ u Finset.univ).card) :
    ∀ u : W₁, 2 ≤ (neighborFinsetIn G₁ u Finset.univ).card := by
  intro u
  rw [← neighborFinsetIn_card_iso e u]
  exact h₂ (e u)

/-- Every generator in `InBNew` has at least $1$ vertex. -/
lemma inBNew_card_pos_esc {W : Type} [Fintype W] [DecidableEq W]
    {B : SimpleGraph W} (hB : InBNew B) : 1 ≤ Fintype.card W := by
  rcases hB with h9 | hBull | ⟨d, _, _, hsp⟩ | ⟨d, _, _, hbd⟩
  · exact inBStar_card_pos h9
  · obtain ⟨eb⟩ := hBull; rw [Fintype.card_congr eb.toEquiv]; decide
  · rcases hsp with hsp1 | hsp2
    · obtain ⟨eb⟩ := hsp1; rw [Fintype.card_congr eb.toEquiv, Fintype.card_fin]; omega
    · obtain ⟨eb⟩ := hsp2; rw [Fintype.card_congr eb.toEquiv, Fintype.card_fin]; omega
  · rcases hbd with hbd1 | hbd2
    · obtain ⟨eb⟩ := hbd1; rw [Fintype.card_congr eb.toEquiv, Fintype.card_fin]; omega
    · obtain ⟨eb⟩ := hbd2; rw [Fintype.card_congr eb.toEquiv, Fintype.card_fin]; omega

/-- Every graph in `InJClosureBNew` has at least $1$ vertex. -/
theorem inJClosureBNew_card_pos_esc {W : Type} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} (hH : InJClosureBNew H) : 1 ≤ Fintype.card W := by
  induction hH with
  | base B hB => exact inBNew_card_pos_esc hB
  | iso _ _ _ he ihb => obtain ⟨eb⟩ := he; rwa [← Fintype.card_congr eb.toEquiv]
  | subst _ v _ _ _ _ ihb2 => rw [card_substGraph_vert v]; omega
  | add_leaf _ v _ _ _ => haveI : Nonempty _ := ⟨v⟩; exact Fintype.card_pos

/-- **General Escape Criterion for `InJClosure k` (`Proposition 7(1)`, `main.tex` line 1257)**:
If $H$ is prime, $|W| \ge 6$, every vertex of $H$ has degree $\le |W| - 3$, and $Hᶜ \notin \mathcal{B}_k^*$,
then $Hᶜ \notin \mathcal{J}(\mathcal{B}_k^*)$. -/
theorem escape_not_inJClosure {k : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W)
    (hprime : IsPrimeGraph H)
    (hcard : 6 ≤ Fintype.card W)
    (hmax : ∀ u : W, (neighborFinsetIn H u Finset.univ).card ≤ Fintype.card W - 3)
    (hnotB : ¬InBStar k Hᶜ) :
    ¬InJClosure k Hᶜ := by
  have hprime_c : IsPrimeGraph Hᶜ := (isPrimeGraph_compl_iff H).mpr hprime
  have hmin_c : ∀ u : W, 2 ≤ (neighborFinsetIn Hᶜ u Finset.univ).card :=
    compl_minDeg_ge_two_of_maxDeg_le H hcard hmax
  intro hJc
  rcases inJClosure_decomp hJc with
    hB | ⟨W_a, W_b, f_a, d_a, f_b, d_b, H_a, v₀, H_b, hca, hcb, _, _, ⟨e⟩⟩ | ⟨_, v₀, hdeg, _⟩
  · exact hnotB hB
  · exact not_isPrimeGraph_substGraph_esc H_a v₀ H_b hca hcb (hprime_c.of_iso e.symm)
  · have h2 := hmin_c v₀; omega

/-- **General Escape Criterion for `InJClosureBNew` (`Proposition 7(1)`, `main.tex` line 1257)**:
No prime graph $G$ of minimum degree $\ge 2$ outside `InBNew` belongs to `InJClosureBNew`. -/
theorem escape_not_inJClosureBNew {W : Type} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W)
    (hprime : IsPrimeGraph G)
    (hmin : ∀ u : W, 2 ≤ (neighborFinsetIn G u Finset.univ).card)
    (hnotB : ∀ {U : Type} [Fintype U] [DecidableEq U] (B : SimpleGraph U),
      InBNew B → ¬Nonempty (B ≃g G)) :
    ¬InJClosureBNew G := by
  suffices h_aux : ∀ {U : Type} [Fintype U] [DecidableEq U] (J : SimpleGraph U),
      InJClosureBNew J → ¬Nonempty (J ≃g G) by
    intro hJ
    exact h_aux G hJ ⟨SimpleGraph.Iso.refl⟩
  intro U _ _ J hJ
  induction hJ with
  | base B hB => exact hnotB B hB
  | iso H₁ H₂ _ he ih =>
      obtain ⟨e₁₂⟩ := he
      rintro ⟨e₂⟩
      exact ih ⟨e₁₂.trans e₂⟩
  | @subst W₁ W₂ _ _ _ _ H₁ v₀ H₂ hJ₁ hJ₂ ih₁ ih₂ =>
      rintro ⟨e⟩
      have hp₁ : 1 ≤ Fintype.card W₁ := inJClosureBNew_card_pos_esc hJ₁
      have hp₂ : 1 ≤ Fintype.card W₂ := inJClosureBNew_card_pos_esc hJ₂
      by_cases h1 : Fintype.card W₁ ≤ 1
      · have h1_eq : Fintype.card W₁ = 1 := by omega
        exact ih₂ ⟨(substGraphIsoOfCardOne H₁ v₀ H₂ h1_eq).symm.trans e⟩
      · by_cases h2 : Fintype.card W₂ ≤ 1
        · have h2_eq : Fintype.card W₂ = 1 := by omega
          exact ih₁ ⟨(substGraphIsoOfCardOneRight H₁ v₀ H₂ h2_eq).symm.trans e⟩
        · exact not_isPrimeGraph_substGraph_esc H₁ v₀ H₂ (by omega) (by omega) (hprime.of_iso e.symm)
  | add_leaf H₁ v₀ hdeg _ _ =>
      rintro ⟨e⟩
      have h2 := minDeg_ge_two_of_iso e hmin v₀
      omega

/-- Any graph containing two vertex-disjoint edges `(a₁, b₁)` and `(a₂, b₂)` with zero cross-edges
(induced $2K_2$) is not a split graph (`¬IsSplitGraph`). -/
theorem not_isSplitGraph_of_two_disjoint_edges {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) (a₁ b₁ a₂ b₂ : W)
    (he₁ : G.Adj a₁ b₁) (he₂ : G.Adj a₂ b₂)
    (hna₁a₂ : ¬G.Adj a₁ a₂) (hna₁b₂ : ¬G.Adj a₁ b₂)
    (hnb₁a₂ : ¬G.Adj b₁ a₂) (hnb₁b₂ : ¬G.Adj b₁ b₂) :
    ¬IsSplitGraph G := by
  rintro ⟨C, I, hCI_union, _, hC_cliq, hI_cliq⟩
  have hmem : ∀ x : W, x ∈ C ∨ x ∈ I := fun x =>
    Finset.mem_union.mp (hCI_union ▸ Finset.mem_univ x)
  have hc₁ : a₁ ∈ C ∨ b₁ ∈ C := by
    rcases hmem a₁ with h1 | h1
    · exact Or.inl h1
    · rcases hmem b₁ with h2 | h2
      · exact Or.inr h2
      · exfalso; exact ((compl_adj G a₁ b₁).mp (hI_cliq h1 h2 (G.ne_of_adj he₁))).2 he₁
  have hc₂ : a₂ ∈ C ∨ b₂ ∈ C := by
    rcases hmem a₂ with h1 | h1
    · exact Or.inl h1
    · rcases hmem b₂ with h2 | h2
      · exact Or.inr h2
      · exfalso; exact ((compl_adj G a₂ b₂).mp (hI_cliq h1 h2 (G.ne_of_adj he₂))).2 he₂
  rcases hc₁ with ha₁C | hb₁C <;> rcases hc₂ with ha₂C | hb₂C
  · exact hna₁a₂ (hC_cliq ha₁C ha₂C (fun h => hnb₁a₂ (G.symm (h ▸ he₁))))
  · exact hna₁b₂ (hC_cliq ha₁C hb₂C (fun h => hnb₁b₂ (G.symm (h ▸ he₁))))
  · exact hnb₁a₂ (hC_cliq hb₁C ha₂C (fun h => hna₁a₂ (h ▸ he₁)))
  · exact hnb₁b₂ (hC_cliq hb₁C hb₂C (fun h => hna₁b₂ (h ▸ he₁)))

/-!
## Section 2: `BullGraph`, `SpiderGraph d` ($d \ge 2$), and `BirdDGraph d` ($d \ge 2$)
(`Proposition 7(1)` of `main.tex`, lines 1258–1262 & 1298)
-/

/-- Adjacency characterization for `SpiderGraph d` on ordered indices `u.1 < v.1`. -/
lemma spiderGraph_adj_of_lt {d : ℕ} {u v : Fin (d + 4)} (huv : u.1 < v.1) :
    (SpiderGraph d).Adj u v ↔
      (u.1 = 0 ∧ (v.1 = 1 ∨ v.1 = 2 ∨ v.1 = 4)) ∨
      (u.1 = 2 ∧ v.1 = 3) ∨
      (4 ≤ u.1 ∧ v.1 = u.1 + 1) := by
  change (if u.1 < v.1 then spiderAdjLt u.1 v.1 = true
          else if v.1 < u.1 then spiderAdjLt v.1 u.1 = true
          else False) ↔ _
  rw [if_pos huv]
  unfold spiderAdjLt
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  tauto

/-- Adjacency characterization for `BirdDGraph d` on ordered indices `u.1 < v.1`. -/
lemma birdDGraph_adj_of_lt {d : ℕ} {u v : Fin (d + 4)} (huv : u.1 < v.1) :
    (BirdDGraph d).Adj u v ↔
      (u.1 = 0 ∧ v.1 = 1) ∨
      (u.1 = 1 ∧ (v.1 = 2 ∨ v.1 = 3)) ∨
      (u.1 = 2 ∧ (v.1 = 3 ∨ v.1 = 4)) ∨
      (4 ≤ u.1 ∧ v.1 = u.1 + 1) := by
  change (if u.1 < v.1 then birdDAdjLt u.1 v.1 = true
          else if v.1 < u.1 then birdDAdjLt v.1 u.1 = true
          else False) ↔ _
  rw [if_pos huv]
  unfold birdDAdjLt
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  tauto

/-- `BullGraph = BirdDGraph 1` is prime (`IsPrimeGraph BullGraph`). -/
theorem bullGraph_isPrime : IsPrimeGraph BullGraph := by
  refine ⟨by decide, ?_⟩
  decide

/-- Explicit self-complementarity isomorphism $\mathrm{Bull} \simeq_g \overline{\mathrm{Bull}}$
mapping `(0, 1, 2, 3, 4) ↦ (1, 4, 0, 3, 2)`. -/
def bullGraphSelfComplIso_esc : BullGraph ≃g BullGraphᶜ where
  toFun := ![1, 4, 0, 3, 2]
  invFun := ![2, 0, 4, 3, 1]
  left_inv u := by fin_cases u <;> rfl
  right_inv v := by fin_cases v <;> rfl
  map_rel_iff' := by
    intro u v
    fin_cases u <;> fin_cases v <;> decide

theorem bullGraph_self_compl : Nonempty (BullGraph ≃g BullGraphᶜ) :=
  ⟨bullGraphSelfComplIso_esc⟩

/-- `BullGraph = BirdDGraph 1` is a split graph (`V = {1, 2, 3} ⊔ {0, 4}`). -/
theorem bullGraph_isSplit : IsSplitGraph BullGraph := by
  refine ⟨{1, 2, 3}, {0, 4}, by decide, by decide, ?_, ?_⟩
  · intro x hx y hy hxy
    fin_cases x <;> fin_cases y <;> revert hx hy hxy <;> decide
  · intro x hx y hy hxy
    fin_cases x <;> fin_cases y <;> revert hx hy hxy <;> decide

/-- `BullGraph` belongs to $\mathcal{H}(\mathcal{B}_1^*)$ (`InHClosure 1 BullGraph`). -/
theorem bullGraph_inHClosure_one : InHClosure 1 BullGraph := by
  have hk2 : InJClosure 1 (⊤ : SimpleGraph (Fin 2)) :=
    InJClosure.base _ (Or.inr (Or.inl ⟨SimpleGraph.Iso.refl⟩))
  have hk3_subst : InJClosure 1 (substGraph (⊤ : SimpleGraph (Fin 2)) 1 (⊤ : SimpleGraph (Fin 2))) :=
    InJClosure.subst _ 1 _ hk2 hk2
  have hk3 : InJClosure 1 (⊤ : SimpleGraph (Fin 3)) :=
    InJClosure.iso _ _ hk3_subst ⟨substK2K2IsoK3⟩
  let B4 : SimpleGraph (Fin 4) := BullGraph.comap Fin.castSuccEmb
  let e_sub0 : B4.comap (Subtype.val : {v : Fin 4 // v ≠ 0} → Fin 4) ≃g (⊤ : SimpleGraph (Fin 3)) :=
    { toFun := fun v => ⟨v.1.1 - 1, by
        have hne : v.1.1 ≠ 0 := fun h => v.2 (Fin.ext h)
        have hlt := v.1.2
        omega⟩
      invFun := fun i => ⟨⟨i.1 + 1, by omega⟩, fun h => by
        have h1 : i.1 + 1 = 0 := congrArg Fin.val h
        exact Nat.succ_ne_zero i.1 h1⟩
      left_inv := fun v => by
        ext; dsimp
        have hne : v.1.1 ≠ 0 := fun h => v.2 (Fin.ext h)
        omega
      right_inv := fun i => by ext; simp
      map_rel_iff' := by
        intro a b
        rcases a with ⟨u, hu⟩
        rcases b with ⟨v, hv⟩
        fin_cases u <;> fin_cases v <;> decide +revert }
  have hB4 : InJClosure 1 B4 := by
    refine InJClosure.add_leaf B4 0
      (card_neighborFinsetIn_le_one_of_unique B4 0 1 (by intro u; fin_cases u <;> decide)) ?_
    exact InJClosure.iso _ _ hk3 ⟨e_sub0.symm⟩
  have hBull : InJClosure 1 BullGraph := by
    refine InJClosure.add_leaf BullGraph (Fin.last 4)
      (card_neighborFinsetIn_le_one_of_unique BullGraph (Fin.last 4) 2
        (by intro u; fin_cases u <;> decide)) ?_
    exact InJClosure.iso B4 _ hB4 ⟨(comapSubtypeNeLastIso 4 BullGraph).symm⟩
  exact ⟨hBull, InJClosure.iso _ _ hBull ⟨bullGraphSelfComplIso_esc⟩⟩

/-- Transport of `HasErdosHajnalProp` across graph isomorphism. -/
lemma hasErdosHajnalProp_of_iso' {W₁ W₂ : Type*} {G₁ : SimpleGraph W₁} {G₂ : SimpleGraph W₂}
    (e : G₁ ≃g G₂) (h₁ : HasErdosHajnalProp G₁) : HasErdosHajnalProp G₂ := by
  obtain ⟨c, hc, hprop⟩ := h₁
  refine ⟨c, hc, fun V _ _ G hG => hprop V G ?_⟩
  rintro ⟨g, hg⟩
  refine hG ⟨e.symm.toEquiv.toEmbedding.trans g, ?_⟩
  ext u v
  exact e.symm.map_rel_iff.symm.trans (congr_arg (fun H => H.Adj (e.symm u) (e.symm v)) hg).to_iff

/-- Explicit isomorphism `substGraph (pathGraph 3) 2 (⊤ : SimpleGraph (Fin 2)) ≃g BullGraph.comap Fin.castSuccEmb`. -/
def substP3K2IsoBullMinus4 :
    substGraph (pathGraph 3) 2 (⊤ : SimpleGraph (Fin 2)) ≃g
      BullGraph.comap (Fin.castSuccEmb : Fin 4 ↪ Fin 5) where
  toFun
    | Sum.inl ⟨0, _⟩ => 0
    | Sum.inl ⟨1, _⟩ => 1
    | Sum.inl ⟨2, h⟩ => False.elim (h rfl)
    | Sum.inr 0 => 2
    | Sum.inr 1 => 3
  invFun
    | 0 => Sum.inl ⟨0, by decide⟩
    | 1 => Sum.inl ⟨1, by decide⟩
    | 2 => Sum.inr 0
    | 3 => Sum.inr 1
  left_inv x := by
    rcases x with ⟨u, hu⟩ | r
    · fin_cases u
      · rfl
      · rfl
      · exact False.elim (hu rfl)
    · fin_cases r <;> rfl
  right_inv y := by fin_cases y <;> rfl
  map_rel_iff' := by
    intro a b
    rcases a with ⟨u, hu⟩ | r <;> rcases b with ⟨v, hv⟩ | s
    · fin_cases u <;> fin_cases v <;> decide +revert
    · fin_cases u <;> fin_cases s <;> decide +revert
    · fin_cases r <;> fin_cases v <;> decide +revert
    · fin_cases r <;> fin_cases s <;> decide

/-- Explicit isomorphism `(BullGraphᶜ - 2) ≃g BullGraph.comap Fin.castSuccEmb`. -/
def bullComplMinus2IsoBullMinus4 :
    BullGraphᶜ.comap (Subtype.val : {v : Fin 5 // v ≠ 2} → Fin 5) ≃g
      BullGraph.comap (Fin.castSuccEmb : Fin 4 ↪ Fin 5) where
  toFun v :=
    let w := bullGraphSelfComplIso_esc.symm v.1
    ⟨w.1, by
      have hw_ne : w ≠ 4 := fun h => v.2 (by
        have h1 : bullGraphSelfComplIso_esc w = v.1 := bullGraphSelfComplIso_esc.apply_symm_apply v.1
        rw [← h1, h]; rfl)
      have hw_lt := w.2
      have : w.1 ≠ 4 := fun h => hw_ne (Fin.ext h)
      omega⟩
  invFun i := ⟨bullGraphSelfComplIso_esc i.castSucc, by fin_cases i <;> decide⟩
  left_inv v := by
    rcases v with ⟨u, hu⟩
    fin_cases u <;> first | exact False.elim (hu rfl) | rfl
  right_inv i := by fin_cases i <;> rfl
  map_rel_iff' := by
    intro a b
    rcases a with ⟨u, hu⟩
    rcases b with ⟨v, hv⟩
    fin_cases u <;> fin_cases v <;> decide +revert

/-- Unconditional Erdős–Hajnal property for `BullGraph = BirdDGraph 1`. -/
theorem hasErdosHajnalProp_bullGraph : HasErdosHajnalProp BullGraph := by
  let B4 : SimpleGraph (Fin 4) := BullGraph.comap Fin.castSuccEmb
  have hp3_eh : HasErdosHajnalProp (pathGraph 3) := by
    obtain ⟨c, hc, hprop⟩ := ErdosHajnalP6.hasErdosHajnalProp_P6
    refine ⟨c, hc, fun V _ _ G hG => hprop V G ?_⟩
    rintro ⟨g, hg⟩
    refine hG ⟨(Fin.castLEEmb (by decide : 3 ≤ 6)).trans g, ?_⟩
    ext u v
    have h1 := congr_arg (fun H => H.Adj (Fin.castLE (by decide : 3 ≤ 6) u) (Fin.castLE (by decide : 3 ≤ 6) v)) hg
    simpa [pathGraph_adj] using h1
  have hB4_eh : HasErdosHajnalProp B4 :=
    hasErdosHajnalProp_of_iso' substP3K2IsoBullMinus4
      (hasErdosHajnalProp_substGraph (pathGraph 3) 2 (⊤ : SimpleGraph (Fin 2)) hp3_eh hasErdosHajnalProp_top_fin2)
  have hv_B4 : IsViral B4 := isViral_of_hasErdosHajnalProp hB4_eh
  have hv_B4c : IsViral B4ᶜ := isViral_of_hasErdosHajnalProp hB4_eh.compl
  have hv1 : IsPairViral (BullGraph.comap (Subtype.val : {v : Fin 5 // v ≠ 4} → Fin 5)) BullGraph :=
    isPairViral_of_isViral_left BullGraph
      ((isPairViral_self_iff _).mp (IsPairViral.congr (comapSubtypeNeLastIso 4 BullGraph).symm
        (comapSubtypeNeLastIso 4 BullGraph).symm ((isPairViral_self_iff B4).mpr hv_B4)))
  have hv2 : IsPairViral BullGraph (BullGraphᶜ.comap (Subtype.val : {v : Fin 5 // v ≠ 2} → Fin 5))ᶜ :=
    isPairViral_of_isViral_right BullGraph
      ((isPairViral_self_iff _).mp (IsPairViral.congr (complIso bullComplMinus2IsoBullMinus4).symm
        (complIso bullComplMinus2IsoBullMinus4).symm ((isPairViral_self_iff B4ᶜ).mpr hv_B4c)))
  have hpv : IsPairViral BullGraph (BullGraphᶜ)ᶜ :=
    isPairViral_simultaneous_leaf_coleaf BullGraph 4 BullGraphᶜ 2 (by decide) (by decide)
      (card_neighborFinsetIn_le_one_of_unique BullGraph 4 2 (by intro u; fin_cases u <;> decide))
      (card_neighborFinsetIn_le_one_of_unique BullGraphᶜ 2 0 (by intro u; fin_cases u <;> decide))
      (by simpa [compl_compl] using hv1) hv2
  rw [compl_compl] at hpv
  exact ((eh_iff_polyRodl_iff_isViral BullGraph).1.mpr
    ((eh_iff_polyRodl_iff_isViral BullGraph).2.mpr ((isPairViral_self_iff BullGraph).mp hpv)))

/-- `SpiderGraph d₁` and `SpiderGraph d₂` are isomorphic iff `d₁ = d₂`. -/
theorem spiderGraph_iso_iff (d₁ d₂ : ℕ) :
    Nonempty (SpiderGraph d₁ ≃g SpiderGraph d₂) ↔ d₁ = d₂ := by
  constructor
  · rintro ⟨iso⟩
    have h := Fintype.card_congr iso.toEquiv
    simp only [Fintype.card_fin] at h
    omega
  · rintro rfl
    exact ⟨SimpleGraph.Iso.refl⟩


/-- Explicit isomorphism `BirdDGraph 2 ≃g BirdGraph` (`(0, 1, 2, 3, 4, 5) ↦ (5, 1, 0, 2, 3, 4)`). -/
def birdDGraph2IsoBirdGraph_esc : BirdDGraph 2 ≃g BirdGraph where
  toFun := ![5, 1, 0, 2, 3, 4]
  invFun := ![2, 1, 3, 4, 5, 0]
  left_inv u := by fin_cases u <;> rfl
  right_inv v := by fin_cases v <;> rfl
  map_rel_iff' := by
    intro u v
    fin_cases u <;> fin_cases v <;> decide

theorem birdDGraph_2_iso_birdGraph : Nonempty (BirdDGraph 2 ≃g BirdGraph) :=
  ⟨birdDGraph2IsoBirdGraph_esc⟩



/-!
## Section 3: Universal Terminal Connected & Anticonnected Non-Neighborhood Modularity
(`Proposition 7(2a)–(2b)` of `main.tex`, lines 1263–1266 & 1300–1307)
-/

/-- Computable, typeclass-free reversed $(s + 1 + r + 1)$-vertex stem-and-cutter sequence
`(z_r, ..., z_0, a_hat, v_hat (s-1), ..., v_hat 0)` from $z_r$ back to $\hat{v}_1^{(i,j)}$. -/
def revStemAux {V : Type*} {s r : ℕ}
    (v_hat : Fin s → V) (a_hat : V) (z : Fin (r + 1) → V) (q : Fin ((s + 1 + r) + 1)) : V :=
  if hqr : q.1 ≤ r then
    z ⟨r - q.1, by omega⟩
  else if hq1 : q.1 = r + 1 then
    a_hat
  else
    v_hat ⟨s + 1 + r - q.1, Nat.sub_lt_left_of_lt_add (Nat.le_of_lt_succ q.isLt) (by omega)⟩

/-- Key structural properties of `revStemAux`. -/
lemma revStemAux_props {V : Type*} [Fintype V] [DecidableEq V]
    {F : SimpleGraph V} {S : Finset V} {ℓ s r : ℕ}
    {B : Fin ℓ → Finset V} {i j : Fin ℓ}
    {v_hat : Fin s → V} {a_hat : V}
    (hunif : IsUnifiedHandleStemPair F S s (B i) (B j) v_hat a_hat)
    (z : Fin (r + 1) → V) (M : Fin (r + 1) → Finset V)
    (hz0 : z 0 ∈ B j) (hM0 : M 0 ⊆ B i)
    (hM_step : ∀ d : Fin r, M d.succ ⊆ neighborFinsetIn F (z d.castSucc) (M d.castSucc))
    (hz_step : ∀ d : Fin r, z d.succ ∈ M d.castSucc ∧ ¬F.Adj (z d.castSucc) (z d.succ)) :
    revStemAux v_hat a_hat z 0 = z (Fin.last r) ∧
    (∀ p q : Fin ((s + 1 + r) + 1), p.1 + 1 = q.1 →
      revStemAux v_hat a_hat z p ≠ revStemAux v_hat a_hat z q ∧
      ¬F.Adj (revStemAux v_hat a_hat z p) (revStemAux v_hat a_hat z q)) ∧
    (∀ p q : Fin ((s + 1 + r) + 1), p.1 + 1 < q.1 →
      F.Adj (revStemAux v_hat a_hat z p) (revStemAux v_hat a_hat z q)) ∧
    (∀ q : Fin ((s + 1 + r) + 1), 1 ≤ q.1 → ∀ x ∈ M (Fin.last r),
      F.Adj (revStemAux v_hat a_hat z q) x) ∧
    (∀ q : Fin ((s + 1 + r) + 1), ∀ x ∈ M (Fin.last r),
      revStemAux v_hat a_hat z q ≠ x) := by
  classical
  have hs_pos : 1 ≤ s := hunif.stem_pos
  have hM_sub : ∀ d : Fin r, M d.succ ⊆ M d.castSucc :=
    fun d => (hM_step d).trans (neighborFinsetIn_subset F _ _)
  have hM_anti : Antitone M := module_chain_antitone hM_sub
  have hM_sub_Bi : ∀ d : Fin (r + 1), M d ⊆ B i :=
    fun d => (hM_anti (Fin.zero_le d)).trans hM0
  have hP_z : ∀ q : Fin ((s + 1 + r) + 1), ∀ h : q.1 ≤ r, revStemAux v_hat a_hat z q = z ⟨r - q.1, by omega⟩ := by
    intro q h; unfold revStemAux; rw [dif_pos h]
  have hP_a : ∀ q : Fin ((s + 1 + r) + 1), q.1 = r + 1 → revStemAux v_hat a_hat z q = a_hat := by
    intro q h; unfold revStemAux; rw [dif_neg (by omega), dif_pos h]
  have hP_v : ∀ (q : Fin ((s + 1 + r) + 1)) (h : r + 2 ≤ q.1), revStemAux v_hat a_hat z q = v_hat ⟨s + 1 + r - q.1, Nat.sub_lt_left_of_lt_add (Nat.le_of_lt_succ q.isLt) (by omega)⟩ := by
    intro q h; unfold revStemAux; rw [dif_neg (by omega), dif_neg (by omega)]
  have hP0 : revStemAux v_hat a_hat z 0 = z (Fin.last r) := by
    rw [hP_z 0 (by simp)]; congr 1
  have h_comp_Mr : ∀ q : Fin ((s + 1 + r) + 1), 1 ≤ q.1 → ∀ x ∈ M (Fin.last r), F.Adj (revStemAux v_hat a_hat z q) x := by
    intro q hq1 x hx
    by_cases hqr : q.1 ≤ r
    · rw [hP_z q hqr]
      let c : Fin r := ⟨r - q.1, by omega⟩
      have h_eq : (⟨r - q.1, by omega⟩ : Fin (r + 1)) = c.castSucc := by ext; dsimp [c]
      rw [h_eq]
      have hx_in : x ∈ M c.succ := hM_anti (Fin.le_last c.succ) hx
      exact ((ErdosHajnalP6.mem_neighborFinsetIn_iff F _ _ _).mp (hM_step c hx_in)).2
    · by_cases hqa : q.1 = r + 1
      · rw [hP_a q hqa]
        exact hunif.handle_complete_Bi x (hM_sub_Bi (Fin.last r) hx)
      · rw [hP_v q (by omega)]
        exact hunif.stem_complete_Bi _ x (hM_sub_Bi (Fin.last r) hx)
  refine ⟨hP0, ?_, ?_, h_comp_Mr, ?_⟩
  · intro p q hpq
    by_cases hqr : q.1 ≤ r
    · rw [hP_z p (by omega), hP_z q hqr]
      let c : Fin r := ⟨r - q.1, by omega⟩
      have hp_c : (⟨r - p.1, by omega⟩ : Fin (r + 1)) = c.succ := by ext; dsimp [c]; omega
      have hq_c : (⟨r - q.1, by omega⟩ : Fin (r + 1)) = c.castSucc := by ext; dsimp [c]
      rw [hp_c, hq_c]
      refine ⟨?_, fun h => (hz_step c).2 (F.symm h)⟩
      by_cases hc0 : c.1 = 0
      · have hcc : c.castSucc = 0 := by ext; exact hc0
        rw [hcc]
        exact fun h => Finset.disjoint_right.mp hunif.blocks_disjoint hz0 (h.symm ▸ hM_sub_Bi _ (hz_step c).1)
      · let c_prev : Fin r := ⟨c.1 - 1, by omega⟩
        have hc_eq : c_prev.succ = c.castSucc := by ext; dsimp [c_prev]; omega
        have hn : ¬F.Adj (z c_prev.castSucc) (z c.castSucc) := by rw [← hc_eq]; exact (hz_step c_prev).2
        have hin : z c.succ ∈ M c_prev.succ := by rw [hc_eq]; exact (hz_step c).1
        have hadj := ((ErdosHajnalP6.mem_neighborFinsetIn_iff F _ _ _).mp (hM_step c_prev hin)).2
        exact fun h => hn (h ▸ hadj)
    · by_cases hqa : q.1 = r + 1
      · rw [hP_z p (by omega), hP_a q hqa]
        have hp0 : (⟨r - p.1, by omega⟩ : Fin (r + 1)) = 0 := by ext; dsimp; omega
        rw [hp0]
        exact ⟨fun h => hunif.handle_not_in_Bj (h ▸ hz0),
          fun h => hunif.handle_anticomplete_Bj (z 0) hz0 (F.symm h)⟩
      · by_cases hpa : p.1 = r + 1
        · rw [hP_a p hpa, hP_v q (by omega)]
          have hq_lt := q.2
          have hs_eq : (⟨s + 1 + r - q.1, by omega⟩ : Fin s).1 + 1 = s := by
            dsimp; omega
          exact ⟨fun h => hunif.stem_not_handle _ h.symm,
            fun h => hunif.stem_last_nonadj_handle _ hs_eq (F.symm h)⟩
        · rw [hP_v p (by omega), hP_v q (by omega)]
          have hq_lt := q.2
          have h_path : (pathGraph s).Adj ⟨s + 1 + r - q.1, by omega⟩ ⟨s + 1 + r - p.1, by omega⟩ := by
            rw [pathGraph_adj]; dsimp; left; omega
          have hadjc := (hunif.stem_induced_path_compl _ _).mpr h_path
          exact ⟨hadjc.1.symm, fun h => hadjc.2 (F.symm h)⟩
  · intro p q hpq
    by_cases hqr : q.1 ≤ r
    · rw [hP_z p (by omega), hP_z q hqr]
      let c : Fin r := ⟨r - q.1, by omega⟩
      have hq_c : (⟨r - q.1, by omega⟩ : Fin (r + 1)) = c.castSucc := by ext; dsimp [c]
      rw [hq_c]
      have hp_in : z ⟨r - p.1, by omega⟩ ∈ M c.succ := by
        let c' : Fin r := ⟨r - p.1 - 1, by omega⟩
        have h1 : (⟨r - p.1, by omega⟩ : Fin (r + 1)) = c'.succ := by ext; dsimp [c']; omega
        rw [h1]
        have hle : c.succ ≤ c'.castSucc := by simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; dsimp [c, c']; omega
        exact hM_anti hle (hz_step c').1
      exact F.symm (((ErdosHajnalP6.mem_neighborFinsetIn_iff F _ _ _).mp (hM_step c hp_in)).2)
    · by_cases hqa : q.1 = r + 1
      · rw [hP_z p (by omega), hP_a q hqa]
        let c' : Fin r := ⟨r - p.1 - 1, by omega⟩
        have h1 : (⟨r - p.1, by omega⟩ : Fin (r + 1)) = c'.succ := by ext; dsimp [c']; omega
        rw [h1]
        exact F.symm (hunif.handle_complete_Bi _ (hM_sub_Bi _ (hz_step c').1))
      · rw [hP_v q (by omega)]
        by_cases hpr : p.1 ≤ r
        · rw [hP_z p hpr]
          by_cases hpr_eq : p.1 = r
          · have hp0 : (⟨r - p.1, by omega⟩ : Fin (r + 1)) = 0 := by ext; dsimp; omega
            rw [hp0]
            exact F.symm (hunif.stem_complete_Bj _ _ hz0)
          · let c' : Fin r := ⟨r - p.1 - 1, by omega⟩
            have h1 : (⟨r - p.1, by omega⟩ : Fin (r + 1)) = c'.succ := by ext; dsimp [c']; omega
            rw [h1]
            exact F.symm (hunif.stem_complete_Bi _ _ (hM_sub_Bi _ (hz_step c').1))
        · by_cases hpa : p.1 = r + 1
          · rw [hP_a p hpa]
            have hq_lt := q.2
            exact F.symm (hunif.stem_init_adj_handle ⟨s + 1 + r - q.1, by omega⟩ (by
              dsimp; omega))
          · rw [hP_v p (by omega)]
            have hq_lt := q.2
            have hne_idx : (⟨s + 1 + r - q.1, by omega⟩ : Fin s) ≠ ⟨s + 1 + r - p.1, by omega⟩ :=
              fun h => by have := Fin.mk.inj h; omega
            have hnpath : ¬(pathGraph s).Adj ⟨s + 1 + r - q.1, by omega⟩ ⟨s + 1 + r - p.1, by omega⟩ := by
              rw [pathGraph_adj]; dsimp; omega
            have hncompl := mt (hunif.stem_induced_path_compl _ _).mp hnpath
            have hvne := hunif.stem_injective.ne hne_idx
            exact F.symm (Decidable.byContradiction (fun hn => hncompl ⟨hvne, hn⟩))
  · intro q x hx h_eq
    by_cases hq0 : q.1 = 0
    · have hqe : q = 0 := Fin.ext hq0
      rw [hqe, hP0] at h_eq
      rcases Nat.eq_zero_or_pos r with rfl | hr_pos
      · exact Finset.disjoint_right.mp hunif.blocks_disjoint hz0 (h_eq ▸ hM0 hx)
      · let c_last : Fin r := ⟨r - 1, by omega⟩
        have hc_eq : c_last.succ = Fin.last r := by ext; dsimp [c_last]; omega
        have hn : ¬F.Adj (z c_last.castSucc) (z (Fin.last r)) := by rw [← hc_eq]; exact (hz_step c_last).2
        have hx_in : x ∈ M c_last.succ := by rw [hc_eq]; exact hx
        exact hn (h_eq ▸ ((ErdosHajnalP6.mem_neighborFinsetIn_iff F _ _ _).mp (hM_step c_last hx_in)).2)
    · exact F.loopless x (h_eq ▸ h_comp_Mr q (by omega) x hx)

/-- **Proposition 7(2a) (`spider_terminal_nonneighborhood_modularity`, `main.tex` line 1265)**:
In any `(SpiderGraph (s + 1 + r))ᶜ`-free graph $F$ containing an $(\ell, w)$-comb or co-comb with
per-handle $s$-stems, if $N_F(z_r) \cap M_r \neq \emptyset$, then every connected component $K$ of
$F[M_r \setminus N_F(z_r)]$ (`IsAnticonnectedComponentOf Fᶜ`) is a proper module of $F[M_r]$. -/
theorem spider_terminal_nonneighborhood_modularity {V : Type*} [Fintype V] [DecidableEq V]
    {F : SimpleGraph V} {S : Finset V} {ℓ s r : ℕ} {w : ℝ}
    {a : Fin ℓ → V} {B : Fin ℓ → Finset V} {stems : Fin ℓ → Fin s → V}
    (hfree : IsInducedSubgraphFree F (SpiderGraph (s + 1 + r))ᶜ)
    (hcomb : IsCombOrCoCombIn F S ℓ w a B)
    (hstems : HasPerHandleApexStems F S ℓ s a B stems)
    {i j : Fin ℓ} (hij : i ≠ j)
    (z : Fin (r + 1) → V) (M : Fin (r + 1) → Finset V)
    (hz0 : z 0 ∈ B j) (hM0 : M 0 ⊆ B i)
    (hM_step : ∀ d : Fin r, M d.succ ⊆ neighborFinsetIn F (z d.castSucc) (M d.castSucc))
    (hz_step : ∀ d : Fin r, z d.succ ∈ M d.castSucc ∧ ¬F.Adj (z d.castSucc) (z d.succ))
    (hz_not_anti : ∃ x ∈ M (Fin.last r), F.Adj (z (Fin.last r)) x)
    {K : Finset V}
    (hK : IsAnticonnectedComponentOf Fᶜ (M (Fin.last r) \ neighborFinsetIn F (z (Fin.last r)) (M (Fin.last r))) K) :
    IsProperModuleIn F (M (Fin.last r)) K := by
  classical
  obtain ⟨hunif, _, _⟩ := isUnifiedHandleStemPair_of_combOrCoComb hcomb hstems hij
  obtain ⟨hP0, hP_consec, hP_nonconsec, hP_comp_Mr, hP_not_Mr⟩ :=
    revStemAux_props hunif z M hz0 hM0 hM_step hz_step
  let P := revStemAux (unifiedStem F S w a B stems i j) (unifiedHandle F S w a B i j) z
  let Z_non := M (Fin.last r) \ neighborFinsetIn F (z (Fin.last r)) (M (Fin.last r))
  have hK_sub_Z : K ⊆ Z_non := hK.1
  have hK_sub_Mr : K ⊆ M (Fin.last r) := hK_sub_Z.trans Finset.sdiff_subset
  have hzr_nonadj_K : ∀ u ∈ K, ¬F.Adj (z (Fin.last r)) u := fun u hu => by
    obtain ⟨huM, hn⟩ := Finset.mem_sdiff.mp (hK_sub_Z hu)
    exact fun hadj => hn ((ErdosHajnalP6.mem_neighborFinsetIn_iff F _ _ u).mpr ⟨huM, hadj⟩)
  refine ⟨hK.nonempty, ?_, hK_sub_Mr, ?_⟩
  · rw [Finset.ssubset_iff_of_subset hK_sub_Mr]
    obtain ⟨x₀, hx₀M, hx₀_adj⟩ := hz_not_anti
    exact ⟨x₀, hx₀M, fun hx₀K => hzr_nonadj_K x₀ hx₀K hx₀_adj⟩
  · intro x₂ hx₂M hx₂_notK
    by_cases hzr_x₂ : ¬F.Adj (z (Fin.last r)) x₂
    · have hx₂Z : x₂ ∈ Z_non := Finset.mem_sdiff.mpr ⟨hx₂M,
        fun h => hzr_x₂ ((ErdosHajnalP6.mem_neighborFinsetIn_iff F _ _ x₂).mp h).2⟩
      right
      intro u huK hadj
      exact (hK.2.2 u huK x₂ hx₂Z hx₂_notK).2 (F.symm hadj)
    · push_neg at hzr_x₂
      by_contra hnot_pure
      rw [not_isVertexPureTo_iff_isVertexMixedOn] at hnot_pure
      have hmixed_c : IsVertexMixedOn Fᶜ x₂ K := by
        obtain ⟨u, huK, hu_adj⟩ := hnot_pure.1
        obtain ⟨v, hvK, hv_nadj⟩ := hnot_pure.2
        exact ⟨⟨v, hvK, fun h => hx₂_notK (h ▸ hvK), hv_nadj⟩,
          ⟨u, huK, fun h => h.2 hu_adj⟩⟩
      obtain ⟨w₂, hw₂K, w₁, hw₁K, hw₂_ne_w₁, hw₂w₁_nadj_c, hx₂w₂_nadj, hx₂w₁_adj_c⟩ :=
        hmixed_c.exists_anticonnected_edge hK.2.1
      have hw₁w₂_adj : F.Adj w₂ w₁ := Decidable.byContradiction (fun hn => hw₂w₁_nadj_c ⟨hw₂_ne_w₁, hn⟩)
      have hx₂w₁_adj : F.Adj x₂ w₂ := Decidable.byContradiction (fun hn =>
        hx₂w₂_nadj ⟨fun h => hx₂_notK (h ▸ hw₂K), hn⟩)
      have hx₂w₂_nadj' : ¬F.Adj x₂ w₁ := hx₂w₁_adj_c.2
      let f : Fin ((s + 1 + r) + 4) → V := fun p =>
        if p.1 = 0 then P 0
        else if p.1 = 1 then w₂
        else if p.1 = 2 then w₁
        else if p.1 = 3 then x₂
        else P ⟨p.1 - 3, by omega⟩
      have hf0 : ∀ p : Fin ((s + 1 + r) + 4), p.1 = 0 → f p = P 0 := fun p h => by dsimp [f]; rw [if_pos h]
      have hf1 : ∀ p : Fin ((s + 1 + r) + 4), p.1 = 1 → f p = w₂ := fun p h => by dsimp [f]; rw [if_neg (by omega), if_pos h]
      have hf2 : ∀ p : Fin ((s + 1 + r) + 4), p.1 = 2 → f p = w₁ := fun p h => by dsimp [f]; rw [if_neg (by omega), if_neg (by omega), if_pos h]
      have hf3 : ∀ p : Fin ((s + 1 + r) + 4), p.1 = 3 → f p = x₂ := fun p h => by dsimp [f]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h]
      have hf4 : ∀ p : Fin ((s + 1 + r) + 4), 4 ≤ p.1 → f p = P ⟨p.1 - 3, by omega⟩ := fun p h => by
        dsimp [f]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      have hw₂M : w₂ ∈ M (Fin.last r) := hK_sub_Mr hw₂K
      have hw₁M : w₁ ∈ M (Fin.last r) := hK_sub_Mr hw₁K
      have hx₂_ne_w₂ : x₂ ≠ w₂ := fun h => hx₂_notK (h ▸ hw₂K)
      have hx₂_ne_w₁ : x₂ ≠ w₁ := fun h => hx₂_notK (h ▸ hw₁K)
      have hf_lt : ∀ p q : Fin ((s + 1 + r) + 4), p.1 < q.1 →
          (f p ≠ f q ∧ ((SpiderGraph (s + 1 + r)).Adj p q ↔ Fᶜ.Adj (f p) (f q))) := by
        intro p q hpq
        rw [spiderGraph_adj_of_lt hpq, compl_adj]
        by_cases hq3 : q.1 ≤ 3
        · by_cases hp0 : p.1 = 0
          · rw [hf0 p hp0, show P 0 = z (Fin.last r) from hP0]
            by_cases hq1 : q.1 = 1
            · rw [hf1 q hq1]
              have hne : z (Fin.last r) ≠ w₂ := by rw [← hP0]; exact hP_not_Mr 0 w₂ hw₂M
              have hn : ¬F.Adj (z (Fin.last r)) w₂ := hzr_nonadj_K w₂ hw₂K
              have hlhs : (p.1 = 0 ∧ (q.1 = 1 ∨ q.1 = 2 ∨ q.1 = 4)) ∨ (p.1 = 2 ∧ q.1 = 3) ∨ (4 ≤ p.1 ∧ q.1 = p.1 + 1) :=
                Or.inl ⟨hp0, Or.inl hq1⟩
              exact ⟨hne, iff_of_true hlhs ⟨hne, hn⟩⟩
            · by_cases hq2 : q.1 = 2
              · rw [hf2 q hq2]
                have hne : z (Fin.last r) ≠ w₁ := by rw [← hP0]; exact hP_not_Mr 0 w₁ hw₁M
                have hn : ¬F.Adj (z (Fin.last r)) w₁ := hzr_nonadj_K w₁ hw₁K
                have hlhs : (p.1 = 0 ∧ (q.1 = 1 ∨ q.1 = 2 ∨ q.1 = 4)) ∨ (p.1 = 2 ∧ q.1 = 3) ∨ (4 ≤ p.1 ∧ q.1 = p.1 + 1) :=
                  Or.inl ⟨hp0, Or.inr (Or.inl hq2)⟩
                exact ⟨hne, iff_of_true hlhs ⟨hne, hn⟩⟩
              · have hq3' : q.1 = 3 := by omega
                rw [hf3 q hq3']
                have hne : z (Fin.last r) ≠ x₂ := by rw [← hP0]; exact hP_not_Mr 0 x₂ hx₂M
                have hlhs : ¬((p.1 = 0 ∧ (q.1 = 1 ∨ q.1 = 2 ∨ q.1 = 4)) ∨ (p.1 = 2 ∧ q.1 = 3) ∨ (4 ≤ p.1 ∧ q.1 = p.1 + 1)) := by omega
                exact ⟨hne, iff_of_false hlhs (fun h => h.2 hzr_x₂)⟩
          · by_cases hp1 : p.1 = 1
            · rw [hf1 p hp1]
              by_cases hq2 : q.1 = 2
              · rw [hf2 q hq2]
                have hlhs : ¬((p.1 = 0 ∧ (q.1 = 1 ∨ q.1 = 2 ∨ q.1 = 4)) ∨ (p.1 = 2 ∧ q.1 = 3) ∨ (4 ≤ p.1 ∧ q.1 = p.1 + 1)) := by omega
                exact ⟨hw₂_ne_w₁, iff_of_false hlhs (fun h => h.2 hw₁w₂_adj)⟩
              · have hq3' : q.1 = 3 := by omega
                rw [hf3 q hq3']
                have hlhs : ¬((p.1 = 0 ∧ (q.1 = 1 ∨ q.1 = 2 ∨ q.1 = 4)) ∨ (p.1 = 2 ∧ q.1 = 3) ∨ (4 ≤ p.1 ∧ q.1 = p.1 + 1)) := by omega
                exact ⟨hx₂_ne_w₂.symm, iff_of_false hlhs (fun h => h.2 (F.symm hx₂w₁_adj))⟩
            · have hp2 : p.1 = 2 := by omega
              have hq3' : q.1 = 3 := by omega
              rw [hf2 p hp2, hf3 q hq3']
              have hlhs : (p.1 = 0 ∧ (q.1 = 1 ∨ q.1 = 2 ∨ q.1 = 4)) ∨ (p.1 = 2 ∧ q.1 = 3) ∨ (4 ≤ p.1 ∧ q.1 = p.1 + 1) :=
                Or.inr (Or.inl ⟨hp2, hq3'⟩)
              exact ⟨hx₂_ne_w₁.symm, iff_of_true hlhs ⟨hx₂_ne_w₁.symm, fun h => hx₂w₂_nadj' (F.symm h)⟩⟩
        · have hq4 : 4 ≤ q.1 := by omega
          rw [hf4 q hq4]
          by_cases hp0 : p.1 = 0
          · rw [hf0 p hp0]
            by_cases hq_eq4 : q.1 = 4
            · obtain ⟨hne_c, hnadj_c⟩ := hP_consec 0 ⟨q.1 - 3, by omega⟩ (by dsimp; omega)
              have hlhs : (p.1 = 0 ∧ (q.1 = 1 ∨ q.1 = 2 ∨ q.1 = 4)) ∨ (p.1 = 2 ∧ q.1 = 3) ∨ (4 ≤ p.1 ∧ q.1 = p.1 + 1) :=
                Or.inl ⟨hp0, Or.inr (Or.inr hq_eq4)⟩
              exact ⟨hne_c, iff_of_true hlhs ⟨hne_c, hnadj_c⟩⟩
            · have hnc := hP_nonconsec 0 ⟨q.1 - 3, by omega⟩ (by dsimp; omega)
              have hne_c := F.ne_of_adj hnc
              have hlhs : ¬((p.1 = 0 ∧ (q.1 = 1 ∨ q.1 = 2 ∨ q.1 = 4)) ∨ (p.1 = 2 ∧ q.1 = 3) ∨ (4 ≤ p.1 ∧ q.1 = p.1 + 1)) := by omega
              exact ⟨hne_c, iff_of_false hlhs (fun h => h.2 hnc)⟩
          · by_cases hp3 : p.1 ≤ 3
            · have hfp_Mr : f p ∈ M (Fin.last r) := by
                by_cases hp1 : p.1 = 1
                · rw [hf1 p hp1]; exact hw₂M
                · by_cases hp2 : p.1 = 2
                  · rw [hf2 p hp2]; exact hw₁M
                  · rw [hf3 p (by omega)]; exact hx₂M
              have hadjF : F.Adj (f p) (P ⟨q.1 - 3, by omega⟩) :=
                F.symm (hP_comp_Mr ⟨q.1 - 3, by omega⟩ (by dsimp; omega) (f p) hfp_Mr)
              have hneF := F.ne_of_adj hadjF
              have hlhs : ¬((p.1 = 0 ∧ (q.1 = 1 ∨ q.1 = 2 ∨ q.1 = 4)) ∨ (p.1 = 2 ∧ q.1 = 3) ∨ (4 ≤ p.1 ∧ q.1 = p.1 + 1)) := by omega
              exact ⟨hneF, iff_of_false hlhs (fun h => h.2 hadjF)⟩
            · have hp4 : 4 ≤ p.1 := by omega
              rw [hf4 p hp4]
              by_cases hsucc : q.1 = p.1 + 1
              · obtain ⟨hne_c, hnadj_c⟩ := hP_consec ⟨p.1 - 3, by omega⟩ ⟨q.1 - 3, by omega⟩ (by dsimp; omega)
                have hlhs : (p.1 = 0 ∧ (q.1 = 1 ∨ q.1 = 2 ∨ q.1 = 4)) ∨ (p.1 = 2 ∧ q.1 = 3) ∨ (4 ≤ p.1 ∧ q.1 = p.1 + 1) :=
                  Or.inr (Or.inr ⟨hp4, hsucc⟩)
                exact ⟨hne_c, iff_of_true hlhs ⟨hne_c, hnadj_c⟩⟩
              · have hnc := hP_nonconsec ⟨p.1 - 3, by omega⟩ ⟨q.1 - 3, by omega⟩ (by dsimp; omega)
                have hne_c := F.ne_of_adj hnc
                have hlhs : ¬((p.1 = 0 ∧ (q.1 = 1 ∨ q.1 = 2 ∨ q.1 = 4)) ∨ (p.1 = 2 ∧ q.1 = 3) ∨ (4 ≤ p.1 ∧ q.1 = p.1 + 1)) := by omega
                exact ⟨hne_c, iff_of_false hlhs (fun h => h.2 hnc)⟩
      have hf_inj : Function.Injective f := by
        intro p q h_eq
        rcases lt_trichotomy p.1 q.1 with hlt | heq | hgt
        · exact False.elim ((hf_lt p q hlt).1 h_eq)
        · exact Fin.ext heq
        · exact False.elim ((hf_lt q p hgt).1 h_eq.symm)
      apply hfree
      refine ⟨⟨f, hf_inj⟩, ?_⟩
      ext p q
      simp only [comap_adj, Function.Embedding.coeFn_mk]
      rcases lt_trichotomy p.1 q.1 with hlt | heq | hgt
      · obtain ⟨hne_pq, hiff_pq⟩ := hf_lt p q hlt
        have hp_ne_q : p ≠ q := Fin.ext_iff.not.mpr (by omega)
        simp only [compl_adj] at hiff_pq ⊢
        tauto
      · have hpq : p = q := Fin.ext heq; subst hpq; simp
      · obtain ⟨hne_qp, hiff_qp⟩ := hf_lt q p hgt
        have hq_ne_p : q ≠ p := Fin.ext_iff.not.mpr (by omega)
        rw [(SpiderGraph (s + 1 + r))ᶜ.adj_comm, F.adj_comm]
        simp only [compl_adj] at hiff_qp ⊢
        tauto

/-- **Proposition 7(2b) (`bird_terminal_nonneighborhood_modularity`, `main.tex` line 1266)**:
In any `(BirdDGraph (s + 1 + r))ᶜ`-free graph $F$ containing an $(\ell, w)$-comb or co-comb with
per-handle $s$-stems, if $N_F(z_r) \cap M_r \neq \emptyset$, then every anticonnected component $L$
of $F[M_r \setminus N_F(z_r)]$ is a proper module of $F[M_r]$. -/
theorem bird_terminal_nonneighborhood_modularity {V : Type*} [Fintype V] [DecidableEq V]
    {F : SimpleGraph V} {S : Finset V} {ℓ s r : ℕ} {w : ℝ}
    {a : Fin ℓ → V} {B : Fin ℓ → Finset V} {stems : Fin ℓ → Fin s → V}
    (hfree : IsInducedSubgraphFree F (BirdDGraph (s + 1 + r))ᶜ)
    (hcomb : IsCombOrCoCombIn F S ℓ w a B)
    (hstems : HasPerHandleApexStems F S ℓ s a B stems)
    {i j : Fin ℓ} (hij : i ≠ j)
    (z : Fin (r + 1) → V) (M : Fin (r + 1) → Finset V)
    (hz0 : z 0 ∈ B j) (hM0 : M 0 ⊆ B i)
    (hM_step : ∀ d : Fin r, M d.succ ⊆ neighborFinsetIn F (z d.castSucc) (M d.castSucc))
    (hz_step : ∀ d : Fin r, z d.succ ∈ M d.castSucc ∧ ¬F.Adj (z d.castSucc) (z d.succ))
    (hz_not_anti : ∃ x ∈ M (Fin.last r), F.Adj (z (Fin.last r)) x)
    {L : Finset V}
    (hL : IsAnticonnectedComponentOf F (M (Fin.last r) \ neighborFinsetIn F (z (Fin.last r)) (M (Fin.last r))) L) :
    IsProperModuleIn F (M (Fin.last r)) L := by
  classical
  obtain ⟨hunif, _, _⟩ := isUnifiedHandleStemPair_of_combOrCoComb hcomb hstems hij
  obtain ⟨hP0, hP_consec, hP_nonconsec, hP_comp_Mr, hP_not_Mr⟩ :=
    revStemAux_props hunif z M hz0 hM0 hM_step hz_step
  let P := revStemAux (unifiedStem F S w a B stems i j) (unifiedHandle F S w a B i j) z
  let Z_non := M (Fin.last r) \ neighborFinsetIn F (z (Fin.last r)) (M (Fin.last r))
  have hL_sub_Z : L ⊆ Z_non := hL.1
  have hL_sub_Mr : L ⊆ M (Fin.last r) := hL_sub_Z.trans Finset.sdiff_subset
  have hzr_nonadj_L : ∀ u ∈ L, ¬F.Adj (z (Fin.last r)) u := fun u hu => by
    obtain ⟨huM, hn⟩ := Finset.mem_sdiff.mp (hL_sub_Z hu)
    exact fun hadj => hn ((ErdosHajnalP6.mem_neighborFinsetIn_iff F _ _ u).mpr ⟨huM, hadj⟩)
  refine ⟨hL.nonempty, ?_, hL_sub_Mr, ?_⟩
  · rw [Finset.ssubset_iff_of_subset hL_sub_Mr]
    obtain ⟨x₀, hx₀M, hx₀_adj⟩ := hz_not_anti
    exact ⟨x₀, hx₀M, fun hx₀L => hzr_nonadj_L x₀ hx₀L hx₀_adj⟩
  · intro x₀ hx₀M hx₀_notL
    by_cases hzr_x₀ : ¬F.Adj (z (Fin.last r)) x₀
    · have hx₀Z : x₀ ∈ Z_non := Finset.mem_sdiff.mpr ⟨hx₀M,
        fun h => hzr_x₀ ((ErdosHajnalP6.mem_neighborFinsetIn_iff F _ _ x₀).mp h).2⟩
      left
      intro u huL
      exact (hL.2.2 u huL x₀ hx₀Z hx₀_notL).symm
    · push_neg at hzr_x₀
      by_contra hnot_pure
      rw [not_isVertexPureTo_iff_isVertexMixedOn] at hnot_pure
      obtain ⟨w₁, hw₁L, w₂, hw₂L, hw₁_ne_w₂, hw₁w₂_nadj, hx₀w₁_nadj, hx₀w₂_adj⟩ :=
        hnot_pure.exists_anticonnected_edge hL.2.1
      let f : Fin ((s + 1 + r) + 4) → V := fun p =>
        if p.1 = 0 then x₀
        else if p.1 = 1 then w₁
        else if p.1 = 2 then P 0
        else if p.1 = 3 then w₂
        else P ⟨p.1 - 3, by omega⟩
      have hf0 : ∀ p : Fin ((s + 1 + r) + 4), p.1 = 0 → f p = x₀ := fun p h => by dsimp [f]; rw [if_pos h]
      have hf1 : ∀ p : Fin ((s + 1 + r) + 4), p.1 = 1 → f p = w₁ := fun p h => by dsimp [f]; rw [if_neg (by omega), if_pos h]
      have hf2 : ∀ p : Fin ((s + 1 + r) + 4), p.1 = 2 → f p = P 0 := fun p h => by dsimp [f]; rw [if_neg (by omega), if_neg (by omega), if_pos h]
      have hf3 : ∀ p : Fin ((s + 1 + r) + 4), p.1 = 3 → f p = w₂ := fun p h => by dsimp [f]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h]
      have hf4 : ∀ p : Fin ((s + 1 + r) + 4), 4 ≤ p.1 → f p = P ⟨p.1 - 3, by omega⟩ := fun p h => by
        dsimp [f]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      have hw₁M : w₁ ∈ M (Fin.last r) := hL_sub_Mr hw₁L
      have hw₂M : w₂ ∈ M (Fin.last r) := hL_sub_Mr hw₂L
      have hx₀_ne_w₁ : x₀ ≠ w₁ := fun h => hx₀_notL (h ▸ hw₁L)
      have hx₀_ne_w₂ : x₀ ≠ w₂ := fun h => hx₀_notL (h ▸ hw₂L)
      have hf_lt : ∀ p q : Fin ((s + 1 + r) + 4), p.1 < q.1 →
          (f p ≠ f q ∧ ((BirdDGraph (s + 1 + r)).Adj p q ↔ Fᶜ.Adj (f p) (f q))) := by
        intro p q hpq
        rw [birdDGraph_adj_of_lt hpq, compl_adj]
        by_cases hq3 : q.1 ≤ 3
        · by_cases hp0 : p.1 = 0
          · rw [hf0 p hp0]
            by_cases hq1 : q.1 = 1
            · rw [hf1 q hq1]
              have hlhs : (p.1 = 0 ∧ q.1 = 1) ∨ (p.1 = 1 ∧ (q.1 = 2 ∨ q.1 = 3)) ∨
                  (p.1 = 2 ∧ (q.1 = 3 ∨ q.1 = 4)) ∨ (4 ≤ p.1 ∧ q.1 = p.1 + 1) :=
                Or.inl ⟨hp0, hq1⟩
              exact ⟨hx₀_ne_w₁, iff_of_true hlhs ⟨hx₀_ne_w₁, hx₀w₁_nadj⟩⟩
            · by_cases hq2 : q.1 = 2
              · rw [hf2 q hq2, show P 0 = z (Fin.last r) from hP0]
                have hne : x₀ ≠ z (Fin.last r) := fun h => hP_not_Mr 0 x₀ hx₀M (by rw [hP0, h])
                have hlhs : ¬((p.1 = 0 ∧ q.1 = 1) ∨ (p.1 = 1 ∧ (q.1 = 2 ∨ q.1 = 3)) ∨
                    (p.1 = 2 ∧ (q.1 = 3 ∨ q.1 = 4)) ∨ (4 ≤ p.1 ∧ q.1 = p.1 + 1)) := by omega
                exact ⟨hne, iff_of_false hlhs (fun h => h.2 (F.symm hzr_x₀))⟩
              · have hq3' : q.1 = 3 := by omega
                rw [hf3 q hq3']
                have hlhs : ¬((p.1 = 0 ∧ q.1 = 1) ∨ (p.1 = 1 ∧ (q.1 = 2 ∨ q.1 = 3)) ∨
                    (p.1 = 2 ∧ (q.1 = 3 ∨ q.1 = 4)) ∨ (4 ≤ p.1 ∧ q.1 = p.1 + 1)) := by omega
                exact ⟨hx₀_ne_w₂, iff_of_false hlhs (fun h => h.2 hx₀w₂_adj)⟩
          · by_cases hp1 : p.1 = 1
            · rw [hf1 p hp1]
              by_cases hq2 : q.1 = 2
              · rw [hf2 q hq2, show P 0 = z (Fin.last r) from hP0]
                have hne : w₁ ≠ z (Fin.last r) := fun h => hP_not_Mr 0 w₁ hw₁M (by rw [hP0, h])
                have hlhs : (p.1 = 0 ∧ q.1 = 1) ∨ (p.1 = 1 ∧ (q.1 = 2 ∨ q.1 = 3)) ∨
                    (p.1 = 2 ∧ (q.1 = 3 ∨ q.1 = 4)) ∨ (4 ≤ p.1 ∧ q.1 = p.1 + 1) :=
                  Or.inr (Or.inl ⟨hp1, Or.inl hq2⟩)
                exact ⟨hne, iff_of_true hlhs ⟨hne, fun h => hzr_nonadj_L w₁ hw₁L (F.symm h)⟩⟩
              · have hq3' : q.1 = 3 := by omega
                rw [hf3 q hq3']
                have hlhs : (p.1 = 0 ∧ q.1 = 1) ∨ (p.1 = 1 ∧ (q.1 = 2 ∨ q.1 = 3)) ∨
                    (p.1 = 2 ∧ (q.1 = 3 ∨ q.1 = 4)) ∨ (4 ≤ p.1 ∧ q.1 = p.1 + 1) :=
                  Or.inr (Or.inl ⟨hp1, Or.inr hq3'⟩)
                exact ⟨hw₁_ne_w₂, iff_of_true hlhs ⟨hw₁_ne_w₂, hw₁w₂_nadj⟩⟩
            · have hp2 : p.1 = 2 := by omega
              have hq3' : q.1 = 3 := by omega
              rw [hf2 p hp2, hf3 q hq3', show P 0 = z (Fin.last r) from hP0]
              have hne : z (Fin.last r) ≠ w₂ := by rw [← hP0]; exact hP_not_Mr 0 w₂ hw₂M
              have hlhs : (p.1 = 0 ∧ q.1 = 1) ∨ (p.1 = 1 ∧ (q.1 = 2 ∨ q.1 = 3)) ∨
                  (p.1 = 2 ∧ (q.1 = 3 ∨ q.1 = 4)) ∨ (4 ≤ p.1 ∧ q.1 = p.1 + 1) :=
                Or.inr (Or.inr (Or.inl ⟨hp2, Or.inl hq3'⟩))
              exact ⟨hne, iff_of_true hlhs ⟨hne, hzr_nonadj_L w₂ hw₂L⟩⟩
        · have hq4 : 4 ≤ q.1 := by omega
          rw [hf4 q hq4]
          by_cases hp2 : p.1 = 2
          · rw [hf2 p hp2]
            by_cases hq_eq4 : q.1 = 4
            · obtain ⟨hne_c, hnadj_c⟩ := hP_consec 0 ⟨q.1 - 3, by omega⟩ (by dsimp; omega)
              have hlhs : (p.1 = 0 ∧ q.1 = 1) ∨ (p.1 = 1 ∧ (q.1 = 2 ∨ q.1 = 3)) ∨
                  (p.1 = 2 ∧ (q.1 = 3 ∨ q.1 = 4)) ∨ (4 ≤ p.1 ∧ q.1 = p.1 + 1) :=
                Or.inr (Or.inr (Or.inl ⟨hp2, Or.inr hq_eq4⟩))
              exact ⟨hne_c, iff_of_true hlhs ⟨hne_c, hnadj_c⟩⟩
            · have hnc := hP_nonconsec 0 ⟨q.1 - 3, by omega⟩ (by dsimp; omega)
              have hne_c := F.ne_of_adj hnc
              have hlhs : ¬((p.1 = 0 ∧ q.1 = 1) ∨ (p.1 = 1 ∧ (q.1 = 2 ∨ q.1 = 3)) ∨
                  (p.1 = 2 ∧ (q.1 = 3 ∨ q.1 = 4)) ∨ (4 ≤ p.1 ∧ q.1 = p.1 + 1)) := by omega
              exact ⟨hne_c, iff_of_false hlhs (fun h => h.2 hnc)⟩
          · by_cases hp3 : p.1 ≤ 3
            · have hfp_Mr : f p ∈ M (Fin.last r) := by
                by_cases hp0 : p.1 = 0
                · rw [hf0 p hp0]; exact hx₀M
                · by_cases hp1 : p.1 = 1
                  · rw [hf1 p hp1]; exact hw₁M
                  · rw [hf3 p (by omega)]; exact hw₂M
              have hadjF : F.Adj (f p) (P ⟨q.1 - 3, by omega⟩) :=
                F.symm (hP_comp_Mr ⟨q.1 - 3, by omega⟩ (by dsimp; omega) (f p) hfp_Mr)
              have hneF := F.ne_of_adj hadjF
              have hlhs : ¬((p.1 = 0 ∧ q.1 = 1) ∨ (p.1 = 1 ∧ (q.1 = 2 ∨ q.1 = 3)) ∨
                  (p.1 = 2 ∧ (q.1 = 3 ∨ q.1 = 4)) ∨ (4 ≤ p.1 ∧ q.1 = p.1 + 1)) := by omega
              exact ⟨hneF, iff_of_false hlhs (fun h => h.2 hadjF)⟩
            · have hp4 : 4 ≤ p.1 := by omega
              rw [hf4 p hp4]
              by_cases hsucc : q.1 = p.1 + 1
              · obtain ⟨hne_c, hnadj_c⟩ := hP_consec ⟨p.1 - 3, by omega⟩ ⟨q.1 - 3, by omega⟩ (by dsimp; omega)
                have hlhs : (p.1 = 0 ∧ q.1 = 1) ∨ (p.1 = 1 ∧ (q.1 = 2 ∨ q.1 = 3)) ∨
                    (p.1 = 2 ∧ (q.1 = 3 ∨ q.1 = 4)) ∨ (4 ≤ p.1 ∧ q.1 = p.1 + 1) :=
                  Or.inr (Or.inr (Or.inr ⟨hp4, hsucc⟩))
                exact ⟨hne_c, iff_of_true hlhs ⟨hne_c, hnadj_c⟩⟩
              · have hnc := hP_nonconsec ⟨p.1 - 3, by omega⟩ ⟨q.1 - 3, by omega⟩ (by dsimp; omega)
                have hne_c := F.ne_of_adj hnc
                have hlhs : ¬((p.1 = 0 ∧ q.1 = 1) ∨ (p.1 = 1 ∧ (q.1 = 2 ∨ q.1 = 3)) ∨
                    (p.1 = 2 ∧ (q.1 = 3 ∨ q.1 = 4)) ∨ (4 ≤ p.1 ∧ q.1 = p.1 + 1)) := by omega
                exact ⟨hne_c, iff_of_false hlhs (fun h => h.2 hnc)⟩
      have hf_inj : Function.Injective f := by
        intro p q h_eq
        rcases lt_trichotomy p.1 q.1 with hlt | heq | hgt
        · exact False.elim ((hf_lt p q hlt).1 h_eq)
        · exact Fin.ext heq
        · exact False.elim ((hf_lt q p hgt).1 h_eq.symm)
      apply hfree
      refine ⟨⟨f, hf_inj⟩, ?_⟩
      ext p q
      simp only [comap_adj, Function.Embedding.coeFn_mk]
      rcases lt_trichotomy p.1 q.1 with hlt | heq | hgt
      · obtain ⟨hne_pq, hiff_pq⟩ := hf_lt p q hlt
        have hp_ne_q : p ≠ q := Fin.ext_iff.not.mpr (by omega)
        simp only [compl_adj] at hiff_pq ⊢
        tauto
      · have hpq : p = q := Fin.ext heq; subst hpq; simp
      · obtain ⟨hne_qp, hiff_qp⟩ := hf_lt q p hgt
        have hq_ne_p : q ≠ p := Fin.ext_iff.not.mpr (by omega)
        rw [(BirdDGraph (s + 1 + r))ᶜ.adj_comm, F.adj_comm]
        simp only [compl_adj] at hiff_qp ⊢
        tauto


end ErdosHajnalGen
