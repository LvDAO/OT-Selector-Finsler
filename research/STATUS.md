# Formalization status

The general Finsler empirical selector theorem is proved in Lean under the
manuscript's original smooth assumptions. The public terminal declaration is
[`exists_original_general_finsler_empirical_selector_on_carriers`](../OTSelector/Transport/EmpiricalSelector/Carriers.lean).
It chooses a population-optimal plan on `A × B` before quantifying over every
independent iid sampling implementation. The entire empirical optimal set,
including fractional couplings, converges to that same plan in outer probability.

## Scope of the public theorem

The theorem corresponds to `thm:general-finsler-selector` in
[main.tex](../main.tex); see [SCOPE.md](SCOPE.md) for the mathematical scope.

| Requirement | Lean interface and conclusion |
| --- | --- |
| Connected, complete, smooth, reversible, strongly convex Finsler manifold; dimension at least six | `ContinuousFinslerNorm`, `IsSmoothStronglyConvex`, completeness of `F.metricSpace`, `6 ≤ finrank ℝ E`, and `IsManifold … ∞`. |
| Original length distance | `F.metricSpace.edist = F.lengthEDist`, the infimum of path integrals of the original tangent norm; the manifold topology is retained. |
| Smooth positive volume and arbitrary nonnegative Lipschitz densities | The original reference volume and chart densities are explicit; no density lower bound is added. |
| Disjoint compact supports | Compact carriers `A`, `B`, `Disjoint A B`, and almost-everywhere support of the two populations; no boundary regularity or finite-component hypothesis. |
| Arbitrary independent iid samples | Arbitrary row probability spaces and arrays, iid within each color and independence between the two arrays; no independence across sample sizes is required. |
| Entire empirical optimal set | Every feasible optimal coupling, including fractional optima, repeated observations and finite-sample ties. |
| One deterministic population-optimal limit | The population-plan existence quantifier precedes all sampling-space, law and array quantifiers. |
| Weak convergence | Every weak neighborhood and every metric inducing the weak topology on `A × B`, using outer probability without a measurable optimal-solution selector. |

Uniqueness concerns the selected limit. The population transport problem may have
several minimizers. The final statement adds no density lower bound, geometric
separator, nonfocusing assumption, global order, product structure, curvature
sign or topological restriction.

## Public entry points

- [Carriers.lean](../OTSelector/Transport/EmpiricalSelector/Carriers.lean): the original compact-carrier theorem.
- [Existence.lean](../OTSelector/Transport/EmpiricalSelector/Existence.lean): `exists_original_general_finsler_empirical_selector`, the ambient-space theorem with the same quantifier order.
- [WithReadout.lean](../OTSelector/Transport/EmpiricalSelector/WithReadout.lean): `existsUnique_original_general_finsler_selector_with_readout`, population pressure readout and uniqueness of the selected limit.
- [FixedSampling.lean](../OTSelector/Transport/EmpiricalSelector/FixedSampling.lean): `existsUnique_original_general_finsler_selector_for_iid_samples`, for a fixed sampling implementation.
- [CarrierLift.lean](../OTSelector/Transport/EmpiricalSelector/CarrierLift.lean): the unique population carrier lift and transfer of the entire empirical optimal face.

These modules are exported by `OTSelector.Transport` and `OTSelector`; their
existing declaration namespaces are preserved. The earlier `main_selector` in
[OTSelector/Main.lean](../OTSelector/Main.lean) concerns the uniform Euclidean model.

## Proof closure

[The chosen population inputs](../OTSelector/Reconstruction/OriginalIIDFinalValueFieldChosenClosed.lean)
are constructed from the original geometry and population data. Actual screening,
stage and port counts, reserve costs and retained-core costs feed the
[native focal reverse-pressure argument](../OTSelector/Reconstruction/OriginalReversePressureNativeFocal.lean).
The iid integrability, lower probability bound and upper expectation bound give
the same population pressure. [PopulationPressure.lean](../OTSelector/Transport/EmpiricalSelector/PopulationPressure.lean)
and its derivative readout then select the same population plan for every iid
sampling implementation.

The terminal theorem requires no externally supplied `FinalInputs`, pressure
field, reverse comparison, derivative, potential or atlas. Smooth manifold
regularity suffices; analyticity is not an assumption. The actual lemma calls and
reusable proof methods are shown in [PROOF_GUIDE.md](PROOF_GUIDE.md).

## Verification of the published proof sources

[VERIFICATION.json](VERIFICATION.json) records the successful checkpoint:

- Source digest: `37985b30f207ef45384440de999a8b59a4fdeb7f62f316286e64bb570c1bec1a`.
- `lake build`: exit code 0, 8,794 jobs.
- `lake env lean Verify.lean`: exit code 0, 46,971 audited declarations.
- Transitive axioms: exactly `propext`, `Classical.choice` and `Quot.sound`.

The proof and configuration bytes are preserved in this release and listed in
[verified-sources.json](verified-sources.json). Documentation and packaging were
prepared for public distribution; machine-specific indexes and research logs are
excluded. Lean compilation and the axiom audit can be reproduced with the commands
in the [README](../README.md).

Reusable mathematics is organized by subject. The
[reference catalog](MATHEMATICAL_METHODS.md) covers 1,207 foundational modules,
6,351 declarations and 334 precise reference locations. Local retrieval tools are
optional and build their own external data store; no existing DAG or embedding-job
state is required to use this proof library.
