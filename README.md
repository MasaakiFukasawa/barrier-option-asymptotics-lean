# Short-term barrier option price expansion — Lean formalization

Lean 4 sources accompanying Masaaki Fukasawa's manuscript *Short-term barrier option price expansion*.

## Build

Install [elan](https://github.com/leanprover/elan), then run from this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean is pinned to 4.34.0; mathlib and its dependencies are pinned in the Lake manifest. The first build also compiles the required stochastic-analysis dependencies and may take substantial time and memory.

The 284 manuscript proof modules are in `Barrier/`. The supporting stochastic-analysis library is fetched by Lake from [stochastic-analysis-lean](https://github.com/MasaakiFukasawa/stochastic-analysis-lean), pinned to commit `0cb33378176178d269f53a4dada439f8ecd3bf5e`. Its 881 required modules match the sources used for the prior proof validation byte for byte. Supporting sources are not copied into this repository. `source-manifest.json` records hashes of the manuscript proof sources.

## Scope

The formalization includes the main up-and-out put theorem (in sequential asymptotic form), both corollary price formulas, the appendix conditional-maximum proposition, the deterministic-volatility time change, and SABR and rough Bergomi applications. The regular LSV application uses explicit sufficient regularity and moment bounds; it does not construct arbitrary SDE solutions or derive those bounds from local smoothness alone.

Start with `ManuscriptMainTheorem.lean`, `ManuscriptMainCorollary.lean`, `ManuscriptMainCorollaryDifference.lean`, `ManuscriptConditionalMaximum.lean`, `ManuscriptSABRApplication.lean`, `ManuscriptRoughExplicitApplication.lean`, and `ManuscriptLSVApplication.lean` in `Barrier/`. All hypotheses are explicit in the Lean statements and their model-data structures.

The UOC/DOP conjecture, externally cited ATM asymptotics, and the Monte Carlo implementation and coverage claims are outside this verification. The CEV application is not covered where required positivity fails. Kernel checking establishes the Lean statements; it does not by itself certify that every manuscript sentence has been faithfully translated.

## Axiom audit

`Audit.lean` imports all manuscript modules and audits every theorem in the `BarrierManuscript` namespace, including private declarations. It rejects dependencies on axioms other than Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. The prior local audit reported 1,402 theorem declarations. The supporting library is checked transitively for axioms used by these theorems.

## Authorship and AI use

The Lean formalization was carried out by OpenAI's ChatGPT in collaboration with Masaaki Fukasawa. Mathematical assumptions and the scope of verification should be assessed from the formal statements and proofs.

This repository contains proof sources and build metadata; it does not include the manuscript's private numerical code or experiment data.
