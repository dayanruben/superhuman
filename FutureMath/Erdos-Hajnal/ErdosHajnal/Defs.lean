/-
Copyright 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Preliminaries and Definitions for Erdős–Hajnal Generalization

This file formalizes the core foundational graph concepts:
- Order, Cliques, Stable Sets, Complements, and $\kappa(G) = \max(\omega(G), \alpha(G))$
- Induced subgraph freeness (`IsInducedSubgraphFree`) and `Erdos61.IsErdosHajnalLowerBound`
- Sparsity, Density, Pure/Complete/Anticomplete pairs, and $\varepsilon$-restricted graphs
- Blockades, Pattern Graphs, and $(\ell, w)$-Combs with external apex vertices
- Anticonnectedness, Anticonnected Components, and Graph Modules (`m_max`)
-/

open Filter Finset SimpleGraph Real

namespace Erdos61

/--
For a graph $H$, consider all graphs $G$ that do not contain $H$ as an induced subgraph.
We would like to find a lower bound $f(n)$ such that every such $G$ on $n$ vertices
has a clique or independent set of size $\ge f(n)$ for sufficiently large $n$.
(Exact definition from `FormalConjectures/ErdosProblems/61.lean`.)
-/
def IsErdosHajnalLowerBound {α : Type*} [Fintype α] [DecidableEq α]
    (H : SimpleGraph α) (f : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ G : SimpleGraph (Fin n),
    (¬∃ g : α ↪ Fin n, H = G.comap g) → G.indepNum ≥ f n ∨ G.cliqueNum ≥ f n

end Erdos61

namespace ErdosHajnalP6

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
`kappa G` is $\kappa(G) := \max(\omega(G), \alpha(G))$, the maximum of the clique number
and independence (stability) number of $G$. (Section 2.1 of `FMBV4-016_readable.tex`.)
-/
noncomputable def kappa (G : SimpleGraph V) : ℕ :=
  max G.cliqueNum G.indepNum

/--
A graph $G$ is induced-$H$-free (`IsInducedSubgraphFree G H`) if there is no injective map
$g : W \hookrightarrow V$ such that $H = G.\text{comap } g$.
This matches the exact predicate `(¬∃ g : α ↪ Fin n, H = G.comap g)` in
`FormalConjectures/ErdosProblems/61.lean` (`Erdos61.IsErdosHajnalLowerBound`).
-/
def IsInducedSubgraphFree {W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ¬∃ g : W ↪ V, H = G.comap g

/--
A finite graph `H` satisfies the Erdős–Hajnal property (`HasErdosHajnalProp H`) if there exists
an exponent `c > 0` such that every induced-`H`-free finite graph `G` on `V` satisfies
`|V| ^ c ≤ kappa G`.
-/
def HasErdosHajnalProp {α : Type*} (H : SimpleGraph α) : Prop :=
  ∃ c > (0 : ℝ), ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    IsInducedSubgraphFree G H → (Fintype.card V : ℝ) ^ c ≤ (kappa G : ℝ)

/-- The 6-vertex path $P_6$ (`SimpleGraph.pathGraph 6`). -/
abbrev P6 : SimpleGraph (Fin 6) := pathGraph 6

/-- The 5-vertex path $P_5$ (`SimpleGraph.pathGraph 5`). -/
abbrev P5 : SimpleGraph (Fin 5) := pathGraph 5

/-- The complement of $P_6$, $\overline{P_6}$. -/
abbrev P6Compl : SimpleGraph (Fin 6) := (pathGraph 6)ᶜ

/-- The complement of $P_5$, $\overline{P_5}$. -/
abbrev P5Compl : SimpleGraph (Fin 5) := (pathGraph 5)ᶜ

/-! ### Sparsity, Density, and Restricted Subgraphs (Section 2.1 of `FMBV4-016_readable.tex`) -/

/--
Open neighborhood of $v$ inside a vertex subset $S \subseteq V(G)$:
$N_G(v) \cap S$.
-/
noncomputable def neighborFinsetIn (G : SimpleGraph V) (v : V) (S : Finset V) : Finset V :=
  by classical exact S.filter (fun u => G.Adj v u)

/--
A graph $G$ on a vertex subset $S \subseteq V$ is $\varepsilon$-sparse (`IsEpsSparseOn G S ε`)
if every vertex $v \in S$ satisfies $|N_G(v) \cap S| \le \varepsilon |S|$.
-/
def IsEpsSparseOn (G : SimpleGraph V) (S : Finset V) (ε : ℝ) : Prop :=
  ∀ v ∈ S, ((neighborFinsetIn G v S).card : ℝ) ≤ ε * (S.card : ℝ)

/--
A graph $G$ is $\varepsilon$-sparse (`IsEpsSparse G ε`) if `IsEpsSparseOn G univ ε`.
-/
def IsEpsSparse (G : SimpleGraph V) (ε : ℝ) : Prop :=
  IsEpsSparseOn G Finset.univ ε

/--
A vertex subset $S \subseteq V$ induces an $\varepsilon$-restricted subgraph in $G$
(`IsEpsRestrictedOn G S ε`) if either $G[S]$ is $\varepsilon$-sparse or $\overline{G}[S]$
is $\varepsilon$-sparse.
-/
def IsEpsRestrictedOn (G : SimpleGraph V) (S : Finset V) (ε : ℝ) : Prop :=
  IsEpsSparseOn G S ε ∨ IsEpsSparseOn Gᶜ S ε

/--
A graph $G$ is $\varepsilon$-restricted (`IsEpsRestricted G ε`) if either $G$ is $\varepsilon$-sparse
or $\overline{G}$ is $\varepsilon$-sparse.
-/
def IsEpsRestricted (G : SimpleGraph V) (ε : ℝ) : Prop :=
  IsEpsSparse G ε ∨ IsEpsSparse Gᶜ ε

/--
Disjoint vertex subsets $A, B \subseteq V$ are complete in $G$ (`IsCompletePair G A B`)
if every $u \in A$ and $v \in B$ are adjacent in $G$.
-/
def IsCompletePair (G : SimpleGraph V) (A B : Finset V) : Prop :=
  ∀ u ∈ A, ∀ v ∈ B, G.Adj u v

/--
Disjoint vertex subsets $A, B \subseteq V$ are anticomplete in $G$ (`IsAnticompletePair G A B`)
if no $u \in A$ and $v \in B$ are adjacent in $G$.
-/
def IsAnticompletePair (G : SimpleGraph V) (A B : Finset V) : Prop :=
  ∀ u ∈ A, ∀ v ∈ B, ¬G.Adj u v

/--
Disjoint vertex subsets $A, B \subseteq V$ are pure in $G$ (`IsPurePair G A B`)
if $(A, B)$ is either complete or anticomplete in $G$.
-/
def IsPurePair (G : SimpleGraph V) (A B : Finset V) : Prop :=
  IsCompletePair G A B ∨ IsAnticompletePair G A B

/--
A vertex $v \notin B$ is pure to $B$ in $G$ if $v$ is either adjacent to all of $B$ or to none of $B$.
-/
def IsVertexPureTo (G : SimpleGraph V) (v : V) (B : Finset V) : Prop :=
  (∀ u ∈ B, G.Adj v u) ∨ (∀ u ∈ B, ¬G.Adj v u)

/--
A vertex $v \notin B$ is mixed on $B$ in $G$ if it has both a neighbor and a non-neighbor in $B$.
-/
def IsVertexMixedOn (G : SimpleGraph V) (v : V) (B : Finset V) : Prop :=
  (∃ u ∈ B, G.Adj v u) ∧ (∃ u ∈ B, ¬G.Adj v u)

/--
$B$ is $x$-sparse to $A$ in $G$ (`IsXSparseTo G B A x`) if every $v \in B$ satisfies
$|N_G(v) \cap A| \le x |A|$.
-/
def IsXSparseTo (G : SimpleGraph V) (B A : Finset V) (x : ℝ) : Prop :=
  ∀ v ∈ B, ((neighborFinsetIn G v A).card : ℝ) ≤ x * (A.card : ℝ)

/--
The pair $(A, B)$ is $x$-sparse in both directions in $G$ (`IsXSparsePair G A B x`).
-/
def IsXSparsePair (G : SimpleGraph V) (A B : Finset V) (x : ℝ) : Prop :=
  IsXSparseTo G B A x ∧ IsXSparseTo G A B x

/--
The pair $(A, B)$ is complete-or-$x$-sparse in $G$ (`IsCompleteOrXSparsePair G A B x`).
-/
def IsCompleteOrXSparsePair (G : SimpleGraph V) (A B : Finset V) (x : ℝ) : Prop :=
  IsCompletePair G A B ∨ IsXSparsePair G A B x

/--
Number of edges between disjoint subsets $A, B \subseteq V$ in $G$:
$|E_G(A, B)| = \sum_{u \in A} |N_G(u) \cap B|$.
-/
noncomputable def crossEdgeCount (G : SimpleGraph V) (A B : Finset V) : ℕ :=
  ∑ u ∈ A, (neighborFinsetIn G u B).card

/--
The pair $(A, B)$ is weakly $\varepsilon$-sparse in $G$ (`IsWeaklySparsePair G A B ε`)
if $|E_G(A, B)| \le \varepsilon |A| |B|$.
-/
def IsWeaklySparsePair (G : SimpleGraph V) (A B : Finset V) (ε : ℝ) : Prop :=
  (crossEdgeCount G A B : ℝ) ≤ ε * (A.card : ℝ) * (B.card : ℝ)

/-! ### Blockades, Pattern Graphs, and Combs (Section 2.1 of `FMBV4-016_readable.tex`) -/

/--
A $(k, w)$-blockade in $G$ inside a vertex set $S \subseteq V$ is a family $B : \text{Fin } k \to \text{Finset } V$
of pairwise disjoint subsets of $S$, each of cardinality at least $w$ (and nonempty).
-/
structure IsBlockadeIn (G : SimpleGraph V) (S : Finset V) (k : ℕ) (w : ℝ)
    (B : Fin k → Finset V) : Prop where
  subset_ambient : ∀ i : Fin k, B i ⊆ S
  nonempty_blocks : ∀ i : Fin k, (B i).Nonempty
  pairwise_disjoint : ∀ i j : Fin k, i ≠ j → Disjoint (B i) (B j)
  width_ge : ∀ i : Fin k, w ≤ ((B i).card : ℝ)

/-- A blockade is complete if all distinct pairs $(B_i, B_j)$ are complete in $G$. -/
def IsCompleteBlockadeIn (G : SimpleGraph V) (S : Finset V) (k : ℕ) (w : ℝ)
    (B : Fin k → Finset V) : Prop :=
  IsBlockadeIn G S k w B ∧ ∀ i j : Fin k, i ≠ j → IsCompletePair G (B i) (B j)

/-- A blockade is anticomplete if all distinct pairs $(B_i, B_j)$ are anticomplete in $G$. -/
def IsAnticompleteBlockadeIn (G : SimpleGraph V) (S : Finset V) (k : ℕ) (w : ℝ)
    (B : Fin k → Finset V) : Prop :=
  IsBlockadeIn G S k w B ∧ ∀ i j : Fin k, i ≠ j → IsAnticompletePair G (B i) (B j)

/-- A blockade is pure if all distinct pairs $(B_i, B_j)$ are pure in $G$. -/
def IsPureBlockadeIn (G : SimpleGraph V) (S : Finset V) (k : ℕ) (w : ℝ)
    (B : Fin k → Finset V) : Prop :=
  IsBlockadeIn G S k w B ∧ ∀ i j : Fin k, i ≠ j → IsPurePair G (B i) (B j)

/-- A blockade is complete-or-$x$-sparse if all distinct pairs $(B_i, B_j)$ are complete-or-$x$-sparse in $G$. -/
def IsCompleteOrXSparseBlockadeIn (G : SimpleGraph V) (S : Finset V) (k : ℕ) (w x : ℝ)
    (B : Fin k → Finset V) : Prop :=
  IsBlockadeIn G S k w B ∧ ∀ i j : Fin k, i ≠ j → IsCompleteOrXSparsePair G (B i) (B j) x

/--
An $(\ell, w)$-comb in $G$ inside $S \subseteq V$ consists of a blockade $B : \text{Fin } \ell \to \text{Finset } V$
and pairwise distinct apex vertices $a : \text{Fin } \ell \to V$ in $S \setminus \bigcup_j B_j$
such that $a_i$ is complete to $B_i$ and anticomplete to $B_j$ ($i \neq j$).
-/
structure IsCombIn (G : SimpleGraph V) (S : Finset V) (ℓ : ℕ) (w : ℝ)
    (a : Fin ℓ → V) (B : Fin ℓ → Finset V) : Prop where
  is_blockade : IsBlockadeIn G S ℓ w B
  apex_in_ambient : ∀ i : Fin ℓ, a i ∈ S
  apex_injective : Function.Injective a
  apex_disjoint_blocks : ∀ i j : Fin ℓ, a i ∉ B j
  apex_complete_own : ∀ i : Fin ℓ, ∀ u ∈ B i, G.Adj (a i) u
  apex_anticomplete_other : ∀ i j : Fin ℓ, i ≠ j → ∀ u ∈ B j, ¬G.Adj (a i) u

/--
An external apex vertex $v \in S$ for a comb $(a, B)$ in $G$:
$v$ is outside $\{a_1, \dots, a_\ell\} \cup \bigcup_i B_i$, complete to $\bigcup_i B_i$ in $G$,
and anticomplete to $\{a_1, \dots, a_\ell\}$ in $G$.
-/
structure IsCombExternalApex (G : SimpleGraph V) (S : Finset V) (ℓ : ℕ)
    (a : Fin ℓ → V) (B : Fin ℓ → Finset V) (v : V) : Prop where
  mem_ambient : v ∈ S
  not_apex : ∀ i : Fin ℓ, v ≠ a i
  not_in_blocks : ∀ i : Fin ℓ, v ∉ B i
  complete_to_blocks : ∀ i : Fin ℓ, ∀ u ∈ B i, G.Adj v u
  anticomplete_to_apices : ∀ i : Fin ℓ, ¬G.Adj v (a i)

/-! ### Anticonnectedness and Modules (Section 2.1 of `FMBV4-016_readable.tex`) -/

/--
A subset $M \subseteq V$ is anticonnected in $G$ (`IsAnticonnected G M`) if the complement
induced subgraph $Gᶜ.\text{induce } M$ is connected.
-/
def IsAnticonnected (G : SimpleGraph V) (M : Finset V) : Prop :=
  (Gᶜ.induce (M : Set V)).Connected

/--
A subset $M \subseteq S$ is a module of $G[S]$ (`IsModuleIn G S M`) if $M \subseteq S$ and
every vertex $z \in S \setminus M$ is pure (complete or anticomplete) to $M$ in $G$.
-/
def IsModuleIn (G : SimpleGraph V) (S M : Finset V) : Prop :=
  M ⊆ S ∧ ∀ z ∈ S, z ∉ M → IsVertexPureTo G z M

/--
A subset $M \subseteq S$ is a proper module of $G[S]$ (`IsProperModuleIn G S M`) if
$\emptyset \subsetneq M \subsetneq S$ and $M$ is a module of $G[S]$.
-/
def IsProperModuleIn (G : SimpleGraph V) (S M : Finset V) : Prop :=
  M.Nonempty ∧ M ⊂ S ∧ IsModuleIn G S M

end ErdosHajnalP6
