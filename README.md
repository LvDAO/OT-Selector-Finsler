# OT-Selector-Finsler

Deterministic empirical optimal transport selection on Finsler manifolds:
a [mathematical manuscript](main.tex) and a verified Lean 4 formalization.

## Mathematical scope

The theorem concerns connected, complete, smooth, reversible, strongly convex
Finsler manifolds of dimension $d\ge6$, equipped with a smooth positive volume
measure. The two marginal probabilities have arbitrary nonnegative Lipschitz
densities with disjoint compact supports. The cost is the original Finsler length
distance, $c(x,y)=d_F(x,y)$.

There is one intrinsic deterministic population-optimal plan, chosen before
quantifying over every independent iid sampling implementation, to which the
**entire empirical optimal set** converges in outer probability. This includes
fractional couplings, repeated observations and finite-sample ties, and holds in
every weak neighborhood and for every metric inducing weak convergence.
Uniqueness concerns the selected limit; the population transport problem may
have several minimizers.

No prescribed mass balance, density lower bound, curvature sign, geometric
separator or additional topological restriction is assumed. The result includes
Euclidean spaces and admissible Finsler tori. See the [precise scope](research/SCOPE.md)
and [theorem statement and proof outline](research/GENERAL-DISTANCE.md).

## Read the proofs

The general theorem is exported by `OTSelector.Transport`. Start with
[`exists_original_general_finsler_empirical_selector_on_carriers`](OTSelector/Transport/EmpiricalSelector/Carriers.lean)
and the [proof guide](research/PROOF_GUIDE.md). The other public interfaces are:

| Interface | Source |
| --- | --- |
| Ambient-space existence, with the population plan fixed before arbitrary iid models | [Existence.lean](OTSelector/Transport/EmpiricalSelector/Existence.lean) |
| Population readout and uniqueness of the selected plan | [WithReadout.lean](OTSelector/Transport/EmpiricalSelector/WithReadout.lean) |
| A fixed iid sampling implementation | [FixedSampling.lean](OTSelector/Transport/EmpiricalSelector/FixedSampling.lean) |
| Transfer to the original compact carriers | [CarrierLift.lean](OTSelector/Transport/EmpiricalSelector/CarrierLift.lean) |

These statements use the manuscript's original smooth assumptions and length
distance. Pressure, derivative, screening and local comparison inputs are
constructed within the proof. The [formalization status](research/STATUS.md)
explains their precise interpretation.

Reusable mathematics is organized by `Analysis`, `MeasureTheory`, `Probability`,
`Finite`, `PointProcess`, `Geometry/Finsler`, `Transport`, `Topology` and
`LinearAlgebra`. Domain pressure and local-to-global constructions remain in
`Reconstruction`. The complete entry point is [OTSelector.lean](OTSelector.lean);
the Lean library namespace remains `OTSelector`. The earlier uniform Euclidean
model is retained in [OTSelector/Main.lean](OTSelector/Main.lean).

Long technical constructions use topic-local `Proofs/` directories. Public
statements and their final proofs stay together, with reusable steps exposed as
lemmas. [Machine-readable proof skeletons](research/proof-skeletons.json) record
`conditions`, typed `objects` and `proof_detail`. The
[mathematical-methods catalog](research/MATHEMATICAL_METHODS.md) covers 1,207
foundational modules, 6,351 declarations and 334 precise reference locations;
it distinguishes classical results, derived combinations, generalizations and
implementation adapters. The public proof sources and structural/reference catalogs
are complete for this release. Historical source-preimage archives are retained
locally and identified as `development-archive://` references; they are not clone
or build dependencies.

## Build and verify

Install [Lean through elan](https://github.com/leanprover/elan), then clone the
public repository; GitHub authentication is not needed:

```sh
git clone https://github.com/LvDAO/OT-Selector-Finsler.git
cd OT-Selector-Finsler
lake exe cache get
lake build
lake env lean Verify.lean
```

[lean-toolchain](lean-toolchain) pins Lean `v4.34.0-rc1`.
[lakefile.toml](lakefile.toml) and [lake-manifest.json](lake-manifest.json) pin the
dependencies. Supporting sources and their attribution are included under
[vendor/](vendor/). Only `propext`, `Classical.choice` and `Quot.sound` are allowed;
no `sorry` or additional axiom is permitted.

The published proof sources retain the verified checkpoint
`37985b30f207ef45384440de999a8b59a4fdeb7f62f316286e64bb570c1bec1a`.
At that checkpoint, `lake build` passed 8,794 jobs and `Verify.lean` audited
46,971 declarations with exactly the three permitted axioms. The proof and
configuration bytes are preserved in this release; publication changes concern
documentation and packaging. [VERIFICATION.json](research/VERIFICATION.json)
records the check results and source binding, and
[verified-sources.json](research/verified-sources.json) records the source manifest.

## Manuscript

With TeX Live and `latexmk` installed:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error main.tex
```

The [Build PDF workflow](https://github.com/LvDAO/OT-Selector-Finsler/actions/workflows/build-pdf.yml)
also builds the manuscript. Its successful runs publish the
**OT-Selector-Finsler-paper** artifact. Generated PDF and intermediate output are
excluded from source history.

## Optional local proof retrieval

[Proof Atlas](tools/proof_atlas/README.md) provides declaration and proof-state
retrieval, dependency graphs, local embeddings and Lean-checked pattern transfer.
It is optional for building or checking the mathematics. Install its Python
dependencies as described in its guide, then build a local index:

```sh
python3 -m tools.proof_atlas build --embedding none
python3 -m tools.proof_atlas search 'bounded measurable integrable' --view conditions
```

Indexes, vectors, model weights and execution logs belong outside this repository.
The tools support changed-module extraction and an embedding queue that reuses
cached model inputs. No machine-specific index or running-job state is published.

Contributor instructions are in [AGENTS.md](AGENTS.md). Third-party licenses,
notices and attribution are retained with their sources under `vendor/`.
