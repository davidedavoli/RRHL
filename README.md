# Xhl — a Rényi program logic for differential privacy, in Lean 4

This is the machine-checked artifact accompanying the paper *A program logic for
Rényi differential privacy*. It contains the formalization of the probabilistic 
language and its semantics, the judgment and its proof rules, the soundness 
theorem, the privacy conversion, and the case studies of the paper's examples 
section. It contains only the results the paper states and the declarations their
proofs use; `LEDGER.md` pairs each result with its place in the paper.


## Building it

Lean 4 is pinned by `lean-toolchain` (`leanprover/lean4:v4.33.1`) and Mathlib by
`lakefile.lean` (tag `v4.33.1`). With [`elan`](https://github.com/leanprover/elan)
installed, the toolchain is fetched automatically.

```bash
lake exe cache get     # download prebuilt Mathlib .olean files -- do this first
lake build Xhl         # build the development
```

## Checking the claims

Compilation succeeding *is* the proof check: Lean's kernel has accepted every theorem.

The file `Xhl/AxiomsCheck.lean` runs `#print axioms` on every headline theorem. It is 
part of the `Xhl` target, so the build above already elaborated it and printed the 
reports; each one must read exactly

```
'...' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These three are the axioms of Lean's standard library — propositional
extensionality, choice, and soundness of quotients. Nothing in this development
adds to them. 

## Layout


| Directory | Content |
|---|---|
| `Xhl/Measures/` | general measure theory, mentioning neither programs nor divergences: the supremum of a monotone family of measures evaluated setwise, the almost-everywhere `range` predicate, `bind`/`map` and finite-product identities, and the error function with the Gaussian half-line closed form |
| `Xhl/Language/` | the probabilistic `while` language: syntax, the typed memory interface `MemType` and its concrete instance `plainMemType`, the semantics `osemA` — a sub-Markov kernel into the Giry monad on states carrying a transcript of typed released values. Expressions are bundled measurable functions and samplers bundled sub-Markov kernels, so every program is well formed by construction |
| `Xhl/Divergence/` | the measure-level theory the budgets are stated in, mentioning no program: the Hellinger integral `hellingerIntegral`, its weighted form `weightedHellingerIntegral`, chain and map bounds, the mixture algebra, the Gaussian closed forms and the subsampled-Gaussian Rényi leaf at real order, and the mechanism-level definitions of differential privacy and their conversions |
| `Xhl/Duality/` | the measure-level duality between the two-witness Rényi lifting and the test lifting: weak duality in general, and strong duality on Polish spaces for closed relations in which almost every point has a partner, by an almost-everywhere measurable choice of partners (capacitability and the Kuratowski–Ryll-Nardzewski theorem, `Selection/`), discretization (`Discrete/`), a tightness limit and disintegration; used only by `Xhl/Logic/Rrhl/Duality.lean` |
| `Xhl/Logic/` | the logic: the judgment `RRhl`, its structural and sampling rules, the derivability relation `TDeriv` with its soundness theorem `TDeriv.sound`, the readout `rrhl_tr_hellingerIntegral_le`, and the derived rule forms the case studies instantiate |
| `Xhl/Examples/Support/` | the *program*-level material more than one case study needs and none owns: the Gaussian mechanism kernel, samplers, clipping, releases, the shared DP vocabulary (the one add/remove adjacency `AdjAt`/`AdjAtSym` every case study is proved at), and the `⟪…⟫` surface syntax for writing programs the way the paper prints them |
| `Xhl/Examples/DPSGD/` | DP-SGD, carried out on the `release`-carrying programs of the paper's figure, each analysis bounding the law of its program's own transcript: `Transcript/` (the transcript derivation and the `(ε,δ)` corollary), `LastIterate/` (the last-iterate derivation, its burn-round and spend-round derivations), `Shared/` (the programs, memory, support lemmas and divergence leaves, with the `CEquiv` program-equivalence derivations in `Shared/Equiv/`) |
| `Xhl/Examples/Filter/` | noisy gradient descent with per-record Rényi filters |
| `Xhl/Examples/DPFTRLMatrix/` | DP-FTRL with a matrix mechanism: the generic factorization program, the tree-aggregation combinatorics, the state-dependent budget at the sensitivity `sens_j = sup_D ‖C·D‖²_F` (`Potential.lean`), and the multi-participation derivation |
| `Xhl/Examples/DPFTRLBanded/` | amplified banded DP-FTRL: the program with a Bernoulli coin per eligible record, the subsampled-Gaussian block budgets, and the syntactic window-presampling derivation |
| `Xhl/AxiomsCheck.lean` | the axiom evidence described above |

