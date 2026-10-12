# LEAP: Supercharging LLMs for Formal Mathematics with Agentic Frameworks

This directory contains the Lean 4 proof results presented in the LEAP paper:
**"LEAP: Supercharging LLMs for Formal Mathematics with Agentic Frameworks"**
([pdf](LEAP.pdf)).

LEAP (**L**LM-in-**L**ean **E**nvironment **A**gentic **P**rover) is an agentic
framework that decomposes complex mathematical problems into smaller subgoals
(using an AND-OR DAG blueprint) and iteratively refines formal proofs using Lean
compiler feedback and LLM-based reviews.

## Latest Results

Since the paper, LEAP has been extended into a more general multi-agent
reasoning workflow (Teamwork-LEAP). Teamwork-LEAP keeps a single shared proof
state as an AND-OR directed acyclic graph:

*   An **OR node** is the main theorem or a sub-theorem.
*   An **AND node** is one way of decomposing its parent OR node into
    sub-theorems.

The agent first reasons informally and makes a plan, using Mathlib and web
search. It then writes a formal proof and checks it with Lean. Whenever a node
needs to be split further, the agent checks that the split is necessary and
sound before applying it. This repeats at every level, and if a decomposition
fails, the agent proposes another one.

With this workflow, LEAP has produced the following machine-checked Lean 4
results on research-level mathematics. The Lean sources for these results are
not part of this directory.

| Problem | Size | Summary |
| --- | --- | --- |
| **Hilbert's tenth problem over rings of integers** | ~750K LoC | Hilbert asked in 1900 for an algorithm that decides whether any Diophantine equation has a solution. Matiyasevich showed in 1970 that no such algorithm exists over ℤ. The same question over the rings of integers of general number fields stayed open for more than 50 years until it was resolved recently. LEAP formalized that resolution. |
| **Well-posedness of KdV in H<sup>-1</sup>** | ~80K LoC | A formal proof of the 2019 *Annals of Mathematics* theorem of Killip and Vişan. The Korteweg–de Vries (KdV) equation is a classical model of water waves. The theorem shows that it still makes reliable predictions when the initial wave is extremely rough, reaching the roughest level the equation can handle. This settled a question that had been open for decades. |
| **Ağırseven–Ollis conjecture** | ~30K LoC | A conjecture on linear realizations of multisets. A linear realization is a Hamiltonian path on the vertices {0, 1, …, v−1} of the complete graph whose edge lengths are exactly the elements of the multiset. The conjecture is a stepping stone toward the Buratti–Horak–Rosa conjecture in combinatorial design theory. |

### Erdős problems

LEAP gave the first formal proof of an improved upper bound for the open Erdős
Problem #1063, and an independent formal proof of Erdős Problem #289. It also
produced independent proofs or formal verifications of dozens more Erdős
problems, including the nine that Google DeepMind solved earlier this year.
The additional problems are listed below.

In the table, \* marks a variant of the main problem and † marks a formal
verification of a known proof.

| Problem | Summary |
| --- | --- |
| [#1063](https://www.erdosproblems.com/1063) | Estimate n<sub>k</sub> with an upper bound better than Cambie's n<sub>k</sub> ≤ k · lcm(1, …, k − 1). |
| [#289](https://www.erdosproblems.com/289) | Is it true that, for all sufficiently large k, there are distinct finite intervals I<sub>1</sub>, …, I<sub>k</sub> ⊂ ℕ, no two overlapping or adjacent, each with \|I<sub>i</sub>\| ≥ 2, such that 1 = ∑<sub>i</sub> ∑<sub>n ∈ I<sub>i</sub></sub> 1/n? |
| [#357](https://www.erdosproblems.com/357)\* (Hegyvári) | A variant on the largest set of integers whose sums of consecutive terms are all distinct. |
| [#394](https://www.erdosproblems.com/394)\*† (Hall's conjecture) | A variant on a conjecture of Erdős and Hall. |
| [#416](https://www.erdosproblems.com/416)\*† (part i, ~49K LoC) | Let V(x) be the number of n ≤ x for which φ(m) = n has a solution. Does V(2x)/V(x) → 2? |
| [#789](https://www.erdosproblems.com/789)\*† ((n log n)<sup>1/3</sup> variant) | Let h(n) be the largest number such that every A ⊆ ℤ with \|A\| = n contains some B ⊆ A with \|B\| ≥ h(n) where a<sub>1</sub> + ⋯ + a<sub>r</sub> = b<sub>1</sub> + ⋯ + b<sub>s</sub> with a<sub>i</sub>, b<sub>i</sub> ∈ B forces r = s. Is h(n) = Θ((n log n)<sup>1/3</sup>)? |
| [#1095](https://www.erdosproblems.com/1095)\* (upper conjecture) | A variant on the conjectured upper bound. |
| [#1101](https://www.erdosproblems.com/1101)\*† (part ii) | There is a good sequence with sub-exponential growth. |

### Other problems

LEAP has also fully and automatically proved several hard problems posed by a
mathematician collaborator. For example:

*   Minimizing the length of a string that encloses three non-overlapping unit
    squares.
*   Showing that a system with delayed self-correction never overshoots below
    zero, even though the correction is strong and the outside push is fading.

## Structure of Proof Results

The formal proofs are organized in the `solutions/` directory:

*   **[Putnam 2025](solutions/Putnam-2025)**: Full formal solutions in Lean 4
    for all 12 problems from the 2025 William Lowell Putnam Mathematical
    Competition, where LEAP achieved a 100% solve rate.
    *   For the original math statements, please refer to
        [AxiomMath/putnam2025](https://github.com/AxiomMath/putnam2025).
*   **[Lean-IMO-Bench](solutions/LEAN-IMO-Bench)**: A benchmark of IMO-style
    problems formalized in Lean. The formal solutions are split into:
    *   **[Basic](solutions/LEAN-IMO-Bench/Basic)**: Pre-IMO to IMO-Medium
        difficulty.
    *   **[Advanced](solutions/LEAN-IMO-Bench/Advanced)**: Up to IMO-Hard
        difficulty.
    *   For the original IMO-Bench problem statements, please refer to
        [lean_proof_bench.csv][imo-csv-link].
*   **[Open Problems](solutions/Open-Problems)**: Formal proofs for complex
    combinatorial challenges and open problems:
    *   `knuth-color2_solution.lean`: A verified proof for a key subproblem
        (planar projection routing dynamics) in Knuth's Hamiltonian
        decomposition of even-order Cayley graphs.
    *   `erdos_457_solution.lean`: A verified proof for Erdős Problem 457
        concerning the density of triangle-free graphs.
    *   Statements:
        [original_statements](solutions/Open-Problems/original_statements)

## Citing this work

```
@misc{kung2026leapsuperchargingllmsformal,
  title         = {LEAP: Supercharging LLMs for Formal Mathematics with Agentic Frameworks},
  author        = {Po-Nien Kung and Linfeng Song and Dawsen Hwang and Jinsung Yoon and Chun-Liang Li and Simone Severini and Mirek Olšák and Edward Lockhart and Quoc V Le and Burak Gokturk and Thang Luong and Tomas Pfister and Nanyun Peng},
  year          = {2026},
  eprint        = {2606.03303},
  archivePrefix = {arXiv},
  primaryClass  = {cs.AI},
  url           = {https://arxiv.org/abs/2606.03303}
}
```

## License and disclaimer

Copyright 2026 Google LLC

All software is licensed under the Apache License, Version 2.0 (Apache 2.0);
you may not use this file except in compliance with the Apache 2.0 license.
You may obtain a copy of the Apache 2.0 license at:
https://www.apache.org/licenses/LICENSE-2.0

All other materials are licensed under the Creative Commons Attribution 4.0
International License (CC-BY). You may obtain a copy of the CC-BY license at:
https://creativecommons.org/licenses/by/4.0/legalcode

Unless required by applicable law or agreed to in writing, all software and
materials distributed here under the Apache 2.0 or CC-BY licenses are
distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
either express or implied. See the licenses for the specific language governing
permissions and limitations under those licenses.

This is not an official Google product.

[imo-csv-link]: https://github.com/google-deepmind/superhuman/blob/main/imobench/lean_proof_bench.csv
