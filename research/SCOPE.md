# Mathematical scope

The general theorem and Lean formalization are complete. See [STATUS.md](STATUS.md),
[GENERAL-DISTANCE.md](GENERAL-DISTANCE.md) and the [proof guide](PROOF_GUIDE.md).

## Exact theorem scope

The ambient space is a connected complete smooth reversible strongly convex
Finsler manifold of dimension d>=6, with smooth positive volume. The two
probability densities are arbitrary nonnegative Lipschitz functions with compact
disjoint supports. The colors are sampled independently, iid within each color;
n denotes sample size. The objective is the same metric's true length distance.

The entire empirical optimal set, including fractional couplings, converges in
probability to one intrinsic deterministic population optimum. No density lower
bound, regular support boundary, prescribed projection balance, global order,
product structure, smooth global foliation, common-latent representation, NF or
IC is assumed. All permitted Euclidean populations, curved complete Riemannian
manifolds and smooth reversible strongly convex Finsler tori are covered.

No further homology, homotopy, curvature-sign, global normal-neighborhood or
cut-locus condition is required within this background. This is not a claim
about nonreversible, incomplete or nonsmooth length structures. Necessity of the
ambient assumptions, dimensions four and five, touching or singular populations,
entropy-selector identification and Monge form remain separate questions.

## Completed proof and review

The common quotient measure and legal conditional couplings are derived from
continuous optimality. Finite color classes and zero-flux cuts give balanced
strict blocks without predetermined mass balance. Genuine Finsler Jacobi data
supply endpoint pole and determinant bounds. Original-input phase envelopes give
full-path L2 traffic for interleaved populations; endpoint first variations center
every deterministic prefix and slab current.

Nonnegative cut occupations and one independent reserve pool give stagewise
legal capacity-preserving repair. Generic cube orientation supplies the boundary
flux rate needed to pay the whole-cube exceptional event. The leading reserve
cost constant is independent of reserve intensity and the chosen minimizer;
only already-vanished subvolume errors depend on them. This proves I_w=I_2
without placing weighted minima in the ordinary second-moment class.

The exact legal maximum-cardinality finite pressure, global weighted lower and
second-moment upper bounds, integrated C1 and countable readout reconstruction
then yield the complete theorem. Pointwise constants and orientations are not
integrated or required to vary measurably over roots.

## Base cases and geometric interpretation

The separated-box case is included with arbitrary Lipschitz densities
and no prescribed balance. The convex-separator theorem remains a proved
intermediate result, but its extra separator is unnecessary for the final theorem.
The ordered d>=4 tube and explicit negative-curvature results retain their exact
scopes.

Curvature and cost are one geometric datum. Transfer under diffeomorphisms requires
the distance identity and pushforward marginals; transporting a flat metric isometrically preserves zero intrinsic
curvature.

## Formal verification and organization

[VERIFICATION.json](VERIFICATION.json) records a successful full `lake build`
(8,794 jobs) and `Verify.lean` (46,971 declarations), with only `propext`,
`Classical.choice` and `Quot.sound`, for source checkpoint
`37985b30f207ef45384440de999a8b59a4fdeb7f62f316286e64bb570c1bec1a`.
The proof and configuration bytes are retained in this public release; the
[verified source manifest](verified-sources.json) binds the individual files.

Reusable lemmas record conditions, typed objects, proof details and precise book
or paper sections. The [proof guide](PROOF_GUIDE.md) explains the mathematical
areas and topic-local `Proofs/` directories. The
[mathematical-methods catalog](MATHEMATICAL_METHODS.md) distinguishes classical
results from local combinations, generalizations and implementation adapters.
