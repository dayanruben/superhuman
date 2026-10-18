# Erdős-Hajnal for paths and beyond

[This paper](Erdos_Hajnal.pdf) proves the Erdős–Hajnal conjecture
unconditionally for all finite paths and co-paths, as well as for a number of
families of other graphs.

This paper was entirely obtained by Cogentic (arXiv preprint
[arXiv:2609.40324](https://arxiv.org/abs/2609.40324)), an agentic framework for
mathematical discovery, using Gemini 4 Argon as the base model. There was no
human interaction other than the initial prompt for Cogentic to generate a full
proof.
The Cogentic harness was built by Yang Cai, Vineet Gupta, Yanchen Jiang,
Christopher Liaw, Aranyak Mehta, Grigoris Velegkas, and Di Wang (Google Research
and Google DeepMind).

Junehyuk Jung (Brown University & Google DeepMind) and Joonkyung Lee (KIAS)
proposed we attempt to solve the problem, and helped
with inspecting and revising the natural language manuscript and the Lean
code. Eric Wieser (Google DeepMind) also provided valuable feedback on the
Lean project setup.

We would like to explicitly acknowledge that Tung H. Nguyen was the first to
resolve the $P_k$ case, preceding any other group of humans or AI systems to our
knowledge. Following discussions with Nguyen on how to present our respective
$P_k$ results, he kindly proposed that both parties announce their findings
independently while mutually acknowledging each other's work.

These discussions were initiated after we obtained a solution for the $P_6$
case, which was verified by Joonkyung Lee. We initially contacted Nguyen to
explore a potential collaboration on more general cases; he then informed us
that he had recently solved the general $P_k$ case and was in the process of
drafting his manuscript. In parallel, we continued exploring several variants,
including longer paths. During these attempts, one of our agent's runs
successfully resolved $P_k$. However, we emphasize that this result was obtained
strictly subsequent to our initial communication with Nguyen.

In the interest of full transparency, we are uploading the raw Cogentic
outputs—including both the natural-language manuscript and the corresponding
Lean code—on GitHub first. Following this, we will post a human-readable
expository article on arXiv describing the core ideas and structure of the
AI-generated proof to meet the standards of the mathematics community.

Finally, we disclose that we are also aware of the two related AI-generated
claims on GitHub:

-   [An anonymous GitHub repository][p6-repo] claiming the Erdős–Hajnal property
    of $P_6$, and
-   [A GitHub repository by Yuwen Zhou][pk-repo] claiming the Erdős–Hajnal
    property of $P_k$.

Note that as mentioned in their GitHub repositories, these are yet to be
verified by experts.

[p6-repo]: https://github.com/machine-qed/erdos-hajnal-six-vertex-path
[pk-repo]: https://github.com/OctopusTide/erdos-hajnal-all-paths

## License and disclaimer

Copyright 2026 Google LLC

All software is licensed under the Apache License, Version 2.0 (Apache 2.0); you
may not use this file except in compliance with the Apache 2.0 license. You may
obtain a copy of the Apache 2.0 license at:
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
