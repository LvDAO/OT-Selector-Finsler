import OTSelector.Finite.MaxCardValueRelativeStability
import OTSelector.Limit.FinslerExpectationUpperBound
import OTSelector.Reconstruction.FinslerFiniteTilePressure

/-!
# Per-tile frozen-block comparison for the physical Finsler pressure

This module proves the *deterministic* half of the per-cell comparison `hblock`
of `Limit/FinslerExpectationUpperBound.lean`: for one fixed tile `c`, fixed
sample arrays `X Y : Fin (n+1) → M` and fixed labels
`blockS blockT : Fin (n+1) → ι`, the physical maximum-cardinality block value

`finslerTileBlock F μ ν K … blockS blockT X Y φ k f t c`

(the least cost of a maximum-cardinality matching inside the tile for the tilted
matrix `k * (dist - φ y + φ x) + t * f`) is compared with the frozen/model block

`frozenModelTileBlock blockS blockT frozenCost modelProbe t c`

(the same functional for the frozen kinetic matrix and the model probe).

Two pointwise inputs are used, only on the edges of the tile:

* a **relative geometric (freezing) bound**
  `|physical kinetic - frozenCost| ≤ 2 ε * frozenCost`, which is exactly the
  shape produced by
  `OriginalPopulationCoefficientCore.TaylorRootCover.physical_relative` (see
  `abs_finslerTileKinetic_sub_frozenPhysical_le` below for the adapter from the
  actual Taylor remainder to this hypothesis, with
  `frozenCost = k * frozenPhysicalCost`);
* a **uniform probe bound** `|physical probe - modelProbe| ≤ B`.

The honest deterministic conclusion is

`physical ≤ (1 + 2 ε) * frozen + min (#S_c) (#T_c) * (|t| * B + 2 ε * |t| * Gb)`,

together with the two-sided form

`|physical - frozen| ≤ 2 ε * (frozen + min (#S_c) (#T_c) * |t| * Gb)
    + min (#S_c) (#T_c) * |t| * B`,

where `Gb` bounds the model probe on the tile.  Both constants are sharp for
the maxCardValue lemmas used: the `(1 + 2 ε)` factor and the additive
`2 ε * |t| * Gb` correction are genuinely present (they already appear in
`PartialMatching.abs_maxCardValue_perturbed_sub_le_of_relative_kinetic`), and
`min (#S_c) (#T_c)` is the cardinality of a maximum-cardinality matching inside
the tile, i.e. the number of matched edges that can feel the probe error.

## What is *not* claimed, and the exact gap to `hblock`

The literal `hblock` interface of `finslerExpectationUpperBound_of_block_model`
demands, for every `n` and `c`,

`∫ ξ, finslerNormalizedTileBlock … ξ ∂P n ≤ modelBlockSum … / (n+1)`

with no multiplicative slack.  The comparison proved here does not give that:
it only gives the same statement with the factor `(1 + 2 ε)` and with an
additive term `min (#S_c) (#T_c) * (|t| * B + 2 ε * |t| * Gb)` before
normalization.  Consequently this module does **not** discharge `hblock`.  It
reduces it to the honest `(1 + δ_n)` form

`∫ block ≤ (1 + δ_n) * modelBlockSum / (n+1) + c_n`,

with `δ_n = 2 ε_n` and `c_n` the normalized probe/freezing correction.  The
assembly of `Limit/FinslerExpectationUpperBound.lean` would have to be weakened
accordingly: it suffices to replace `hblock` by

`∫ block ≤ (1 + δ_n) * modelBlockSum / (n+1) + c_n`

with `δ_n → 0` and `Σ_c c_n → 0`.  Indeed, `modelBlockSum / (n+1)` converges to
`w_c * p_c t` and is bounded, so `(1 + δ_n) * Σ_c modelBlockSum / (n+1) ≤
Σ_c w_c p_c t + ε` eventually, and the same `limsup_n ∫ V_n ≤ Σ_c w_c p_c t + ε`
conclusion follows.  The additive corrections

`c_n = (1/(n+1)) * ∫ min (#S_c) (#T_c) * (|t| * B_n + 2 ε_n * |t| * Gb)`

still have to be driven to zero, which needs `2 ε_n → 0` (the Taylor radius at
scale `(n+1)^(2/q)`) and an estimate of the form
`E[min (#S_c) (#T_c)] * B_n / n → 0` (the binomial count control together with
the clipped-probe modulus).  Both are random-count/probe inputs and belong to
the other lanes; this file is fixed-label and takes no expectation.

This file is fixed-label only: no measurability, no conditional law and no
expectation is taken here.

No `sorry`, `admit`, partial definition or added axiom occurs; the only
permitted axioms are `propext`, `Classical.choice` and `Quot.sound`.
-/

open Set Function Manifold MeasureTheory OTSelector.Geometry OTSelector.Probability
open scoped Topology ContDiff BigOperators ENNReal BoundedContinuousFunction

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace OTSelector

namespace PartialMatching

variable {a b : ℕ}

/-! ## Entrywise stability and probe-error absorption

`maxCardValue` is Lipschitz for the uniform entrywise distance, with the exact
constant `min a b`: a maximum-cardinality matching has `min a b` edges and each
edge can feel at most `B`.  This is the helper that absorbs the probe error
`|Q - G| ≤ B` into the cardinality term `min (#S_c) (#T_c) * |t| * B`. -/

/-- One-sided entrywise stability of the maximum-cardinality value. -/
theorem maxCardValue_sub_le_of_abs_sub_le {c d : Fin a → Fin b → ℝ} {B : ℝ}
    (h : ∀ i j, |c i j - d i j| ≤ B) :
    maxCardValue c - maxCardValue d ≤ (min a b : ℝ) * B := by
  classical
  obtain ⟨σ, hσ, hσd⟩ := exists_cost_eq_maxCardValue d
  have hc : maxCardValue c ≤ σ.cost c := maxCardValue_le_of_card c hσ
  have hdiff : |σ.cost c - σ.cost d| ≤ (σ.card : ℝ) * B := by
    unfold cost
    rw [← Finset.sum_sub_distrib]
    calc |∑ e ∈ σ.edges, (c e.1 e.2 - d e.1 e.2)|
        ≤ ∑ e ∈ σ.edges, |c e.1 e.2 - d e.1 e.2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _e ∈ σ.edges, B := Finset.sum_le_sum fun e _ => h e.1 e.2
      _ = B * (σ.edges.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ = (σ.card : ℝ) * B := by rw [card, mul_comm]
  have hle : σ.cost c ≤ σ.cost d + (σ.card : ℝ) * B := by
    have := (abs_le.mp hdiff).2
    linarith
  rw [hσd, hσ, Nat.cast_min] at hle
  linarith

/-- **Probe-error absorption.**  If two matrices differ entrywise by at most
`B`, the least maximum-cardinality costs differ by at most `min a b * B`.  The
number of matched edges is `min a b`, which is the cardinality factor appearing
in the per-tile comparison. -/
theorem abs_maxCardValue_sub_le_of_abs_sub_le {c d : Fin a → Fin b → ℝ} {B : ℝ}
    (h : ∀ i j, |c i j - d i j| ≤ B) :
    |maxCardValue c - maxCardValue d| ≤ (min a b : ℝ) * B := by
  rw [abs_sub_le_iff]
  constructor
  · exact maxCardValue_sub_le_of_abs_sub_le h
  · exact maxCardValue_sub_le_of_abs_sub_le fun i j => by
      rw [abs_sub_comm]; exact h i j

/-- **Affine scaling and translation of the value.**  If `c ≤ α * d + B` holds
entrywise with `α ≥ 0`, then
`maxCardValue c ≤ α * maxCardValue d + min a b * B`.  This is the combination of
monotonicity, homogeneity (`maxCardValue_const_mul`) and the constant shift
(`maxCardValue_add_const`) used to pass from a pointwise comparison to the tile
comparison. -/
theorem maxCardValue_le_of_le_const_mul_add_const {c d : Fin a → Fin b → ℝ} {α B : ℝ}
    (hα : 0 ≤ α) (h : ∀ i j, c i j ≤ α * d i j + B) :
    maxCardValue c ≤ α * maxCardValue d + (min a b : ℝ) * B := by
  calc maxCardValue c ≤ maxCardValue (fun i j => α * d i j + B) := maxCardValue_mono h
    _ = maxCardValue (fun i j => α * d i j) + (min a b : ℝ) * B :=
        maxCardValue_add_const _ B
    _ = α * maxCardValue d + (min a b : ℝ) * B := by rw [maxCardValue_const_mul d hα]

section Block

variable {N : ℕ} {β : Type*} [Fintype β] [DecidableEq β]
  (blockS : Fin N → β) (blockT : Fin N → β) (c : β)

/-- The tilted matrix of a tile block splits into the tilted kinetic block and
the tilted probe block.  This is the block form of `perturbedEdgeCost`
(`blockCost_add_smul` read through the definition of `perturbedEdgeCost`). -/
theorem blockCost_perturbedEdgeCost (P Q : Fin N → Fin N → ℝ) (t : ℝ) :
    blockCost blockS blockT (perturbedEdgeCost P Q t) c =
      fun i j => blockCost blockS blockT P c i j + t * blockCost blockS blockT Q c i j :=
  blockCost_add_smul blockS blockT P Q t c

variable {F P G Q : Fin N → Fin N → ℝ} {t B δ Gb : ℝ}

/-- **Two-sided frozen-block comparison.**  On one tile, suppose the physical
kinetic matrix `P` is relatively `δ`-close to the frozen kinetic matrix `F`
(with `F ≥ 0` and `δ ≤ 1`), the physical probe `Q` is uniformly `B`-close to
the model probe `G`, and `G` is bounded by `Gb`.  Then the physical and frozen
maximum-cardinality block values differ by at most

`δ * (frozen + min (#S_c) (#T_c) * |t| * Gb) + min (#S_c) (#T_c) * |t| * B`.

The kinetic part is `abs_maxCardValue_perturbed_sub_le_of_relative_kinetic`; the
probe part is the entrywise absorption lemma above. -/
theorem abs_maxCardValue_blockCost_perturbed_sub_le_of_relative
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hGb0 : 0 ≤ Gb)
    (hF0 : ∀ i j, blockS i = c → blockT j = c → 0 ≤ F i j)
    (hrel : ∀ i j, blockS i = c → blockT j = c → |P i j - F i j| ≤ δ * F i j)
    (hprobe : ∀ i j, blockS i = c → blockT j = c → |Q i j - G i j| ≤ B)
    (hG : ∀ i j, blockS i = c → blockT j = c → |G i j| ≤ Gb) :
    |maxCardValue (blockCost blockS blockT (perturbedEdgeCost P Q t) c) -
      maxCardValue (blockCost blockS blockT (perturbedEdgeCost F G t) c)| ≤
      δ * (maxCardValue (blockCost blockS blockT (perturbedEdgeCost F G t) c) +
        (min (blockSizeS blockS c) (blockSizeT blockT c) : ℝ) * |t| * Gb) +
      (min (blockSizeS blockS c) (blockSizeT blockT c) : ℝ) * (|t| * B) := by
  classical
  have hS : ∀ i, blockS (blockEmbeddingS blockS c i) = c := fun i =>
    mem_blockFinset.mp (blockEmbeddingS_mem blockS c i)
  have hT : ∀ j, blockT (blockEmbeddingT blockT c j) = c := fun j =>
    mem_blockFinset.mp (blockEmbeddingT_mem blockT c j)
  have hF' : ∀ i j, 0 ≤ blockCost blockS blockT F c i j := fun i j => hF0 _ _ (hS i) (hT j)
  have hG' : ∀ i j, |blockCost blockS blockT G c i j| ≤ Gb := fun i j =>
    hG _ _ (hS i) (hT j)
  have hrel' : ∀ i j,
      |blockCost blockS blockT P c i j - blockCost blockS blockT F c i j| ≤
        δ * blockCost blockS blockT F c i j := fun i j => hrel _ _ (hS i) (hT j)
  have hkin := abs_maxCardValue_perturbed_sub_le_of_relative_kinetic
    (m := blockSizeS blockS c) (n := blockSizeT blockT c)
    (c := blockCost blockS blockT F c) (c' := blockCost blockS blockT P c)
    (g := blockCost blockS blockT G c) (t := t)
    hδ0 hδ1 hGb0 hF' hG' hrel'
  have hprobe' : |maxCardValue (fun i j =>
        blockCost blockS blockT P c i j + t * blockCost blockS blockT Q c i j) -
      maxCardValue (fun i j =>
        blockCost blockS blockT P c i j + t * blockCost blockS blockT G c i j)| ≤
      (min (blockSizeS blockS c) (blockSizeT blockT c) : ℝ) * (|t| * B) := by
    apply abs_maxCardValue_sub_le_of_abs_sub_le
    intro i j
    have hp : |blockCost blockS blockT Q c i j - blockCost blockS blockT G c i j| ≤ B :=
      hprobe _ _ (hS i) (hT j)
    calc |(blockCost blockS blockT P c i j + t * blockCost blockS blockT Q c i j) -
          (blockCost blockS blockT P c i j + t * blockCost blockS blockT G c i j)|
        = |t * (blockCost blockS blockT Q c i j - blockCost blockS blockT G c i j)| := by
          ring_nf
      _ = |t| * |blockCost blockS blockT Q c i j - blockCost blockS blockT G c i j| := by
          rw [abs_mul]
      _ ≤ |t| * B := mul_le_mul_of_nonneg_left hp (abs_nonneg t)
  rw [blockCost_perturbedEdgeCost blockS blockT c P Q t,
    blockCost_perturbedEdgeCost blockS blockT c F G t]
  have h1 := (abs_le.mp hprobe').2
  have h2 := (abs_le.mp hkin).2
  have hsplit :
      maxCardValue (fun i j => blockCost blockS blockT P c i j +
          t * blockCost blockS blockT Q c i j) -
        maxCardValue (fun i j => blockCost blockS blockT F c i j +
          t * blockCost blockS blockT G c i j) =
      (maxCardValue (fun i j => blockCost blockS blockT P c i j +
          t * blockCost blockS blockT Q c i j) -
        maxCardValue (fun i j => blockCost blockS blockT P c i j +
          t * blockCost blockS blockT G c i j)) +
      (maxCardValue (fun i j => blockCost blockS blockT P c i j +
          t * blockCost blockS blockT G c i j) -
        maxCardValue (fun i j => blockCost blockS blockT F c i j +
          t * blockCost blockS blockT G c i j)) := by ring
  rw [hsplit]
  calc |(maxCardValue (fun i j => blockCost blockS blockT P c i j +
            t * blockCost blockS blockT Q c i j) -
          maxCardValue (fun i j => blockCost blockS blockT P c i j +
            t * blockCost blockS blockT G c i j)) +
        (maxCardValue (fun i j => blockCost blockS blockT P c i j +
            t * blockCost blockS blockT G c i j) -
          maxCardValue (fun i j => blockCost blockS blockT F c i j +
            t * blockCost blockS blockT G c i j))|
      ≤ |maxCardValue (fun i j => blockCost blockS blockT P c i j +
            t * blockCost blockS blockT Q c i j) -
          maxCardValue (fun i j => blockCost blockS blockT P c i j +
            t * blockCost blockS blockT G c i j)| +
        |maxCardValue (fun i j => blockCost blockS blockT P c i j +
            t * blockCost blockS blockT G c i j) -
          maxCardValue (fun i j => blockCost blockS blockT F c i j +
            t * blockCost blockS blockT G c i j)| := abs_add_le ..
    _ ≤ δ * (maxCardValue (fun i j => blockCost blockS blockT F c i j +
            t * blockCost blockS blockT G c i j) +
          (min (blockSizeS blockS c) (blockSizeT blockT c) : ℝ) * |t| * Gb) +
        (min (blockSizeS blockS c) (blockSizeT blockT c) : ℝ) * (|t| * B) := by
        linarith

/-- **One-sided frozen-block comparison.**  If the physical kinetic matrix is
relatively `δ`-close to the frozen kinetic matrix (with `F ≥ 0`), the physical
probe is uniformly `B`-close to the model probe, and the model probe is bounded
by `Gb`, then the physical tile block is at most

`(1 + δ) * frozen + min (#S_c) (#T_c) * (|t| * B + δ * |t| * Gb)`.

Besides the multiplicative factor `1 + δ = 1 + 2 ε`, the additive
`min * δ * |t| * Gb` term is the action of the relative kinetic error on the
tilted model probe; it cannot be dropped (take a constant frozen kinetic matrix
and a model probe equal to its negative bound).  No upper bound on `δ` and no
sign condition on `Gb` is needed for this one-sided form. -/
theorem maxCardValue_blockCost_perturbed_le_of_relative
    (hδ0 : 0 ≤ δ)
    (hF0 : ∀ i j, blockS i = c → blockT j = c → 0 ≤ F i j)
    (hrel : ∀ i j, blockS i = c → blockT j = c → |P i j - F i j| ≤ δ * F i j)
    (hprobe : ∀ i j, blockS i = c → blockT j = c → |Q i j - G i j| ≤ B)
    (hG : ∀ i j, blockS i = c → blockT j = c → |G i j| ≤ Gb) :
    maxCardValue (blockCost blockS blockT (perturbedEdgeCost P Q t) c) ≤
      (1 + δ) * maxCardValue (blockCost blockS blockT (perturbedEdgeCost F G t) c) +
        (min (blockSizeS blockS c) (blockSizeT blockT c) : ℝ) *
          (|t| * B + δ * (|t| * Gb)) := by
  classical
  have hS : ∀ i, blockS (blockEmbeddingS blockS c i) = c := fun i =>
    mem_blockFinset.mp (blockEmbeddingS_mem blockS c i)
  have hT : ∀ j, blockT (blockEmbeddingT blockT c j) = c := fun j =>
    mem_blockFinset.mp (blockEmbeddingT_mem blockT c j)
  have hF' : ∀ i j, 0 ≤ blockCost blockS blockT F c i j := fun i j => hF0 _ _ (hS i) (hT j)
  have hG' : ∀ i j, |blockCost blockS blockT G c i j| ≤ Gb := fun i j =>
    hG _ _ (hS i) (hT j)
  have hrel' : ∀ i j,
      |blockCost blockS blockT P c i j - blockCost blockS blockT F c i j| ≤
        δ * blockCost blockS blockT F c i j := fun i j => hrel _ _ (hS i) (hT j)
  have hprobe' : ∀ i j,
      |blockCost blockS blockT Q c i j - blockCost blockS blockT G c i j| ≤ B := fun i j =>
    hprobe _ _ (hS i) (hT j)
  rw [blockCost_perturbedEdgeCost blockS blockT c P Q t,
    blockCost_perturbedEdgeCost blockS blockT c F G t]
  apply maxCardValue_le_of_le_const_mul_add_const (α := 1 + δ)
    (B := |t| * B + δ * (|t| * Gb))
  · linarith
  · intro i j
    have h1 : blockCost blockS blockT P c i j - blockCost blockS blockT F c i j ≤
        δ * blockCost blockS blockT F c i j := (abs_le.mp (hrel' i j)).2
    have h2 : t * (blockCost blockS blockT Q c i j - blockCost blockS blockT G c i j) ≤
        |t| * B := by
      calc t * (blockCost blockS blockT Q c i j - blockCost blockS blockT G c i j)
          ≤ |t * (blockCost blockS blockT Q c i j - blockCost blockS blockT G c i j)| :=
            le_abs_self _
        _ = |t| * |blockCost blockS blockT Q c i j - blockCost blockS blockT G c i j| :=
            abs_mul _ _
        _ ≤ |t| * B := mul_le_mul_of_nonneg_left (hprobe' i j) (abs_nonneg t)
    have h3 : -(|t| * Gb) ≤ t * blockCost blockS blockT G c i j := by
      have h4 : |t * blockCost blockS blockT G c i j| ≤ |t| * Gb := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hG' i j) (abs_nonneg t)
      linarith [neg_abs_le (t * blockCost blockS blockT G c i j)]
    have h5 := mul_le_mul_of_nonneg_left h3 hδ0
    nlinarith [h1, h2, h5, hF' i j]

end Block

end PartialMatching

/-! ## The frozen/model tile block

The frozen comparison is against the maximum-cardinality value of the frozen
kinetic matrix plus the model probe, restricted to one label tile.  This is the
deterministic finite object which the marked-cube model lane identifies with
`markedFixedValue`; it is defined for arbitrary fixed labels, with no
measurability or law assumption. -/

/-- The frozen/model block of one tile: the least cost of a maximum-cardinality
matching inside the tile for the tilted matrix `frozenCost + t * modelProbe`. -/
noncomputable def frozenModelTileBlock {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (blockS blockT : Fin (n + 1) → ι)
    (frozenCost modelProbe : Fin (n + 1) → Fin (n + 1) → ℝ) (t : ℝ) (c : ι) : ℝ :=
  PartialMatching.maxCardValue
    (blockCost blockS blockT (perturbedEdgeCost frozenCost modelProbe t) c)

namespace Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]

/-! ## The physical kinetic and probe matrices of a tile

`finslerTileBlock` is the `maxCardValue` of the tilted matrix
`k * (dist - φ y + φ x) + t * f`, with the distance taken in the genuine
Finsler length metric `F.metricSpace`.  The two next definitions name the two
pieces of that matrix, so that the frozen comparison can be stated and used
entrywise. -/

/-- The physical kinetic matrix `k * (dist - φ y + φ x)` of a tile, in the
genuine Finsler length metric. -/
noncomputable def finslerTileKinetic (F : ContinuousFinslerNorm E M)
    {n : ℕ} (X Y : Fin (n + 1) → M) (φ : M → ℝ) (k : ℝ) :
    Fin (n + 1) → Fin (n + 1) → ℝ :=
  letI : MetricSpace M := F.metricSpace
  fun i j => k * distanceSlackEdgeCost X Y φ i j

/-- The physical probe matrix `f` of the supported pressure, evaluated through
the measurable support projections of the two marginals. -/
noncomputable def finslerTileProbe (μ ν : ProbabilityMeasure M) (K : Set M)
    (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    {n : ℕ} (X Y : Fin (n + 1) → M) (f : (K × K) →ᵇ ℝ) :
    Fin (n + 1) → Fin (n + 1) → ℝ :=
  fun i j => f (supportProjection μ K hK hμ (X i), supportProjection ν K hK hν (Y j))

/-- **Unfolding of the physical tile block.**  `finslerTileBlock` is exactly the
maximum-cardinality value of the block of the tilted matrix built from
`finslerTileKinetic` and `finslerTileProbe`. -/
theorem finslerTileBlock_eq_maxCardValue_blockCost
    (F : ContinuousFinslerNorm E M)
    {n : ℕ} (μ ν : ProbabilityMeasure M) (K : Set M) (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (blockS blockT : Fin (n + 1) → ι) (X Y : Fin (n + 1) → M)
    (φ : M → ℝ) (k : ℝ) (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : ι) :
    finslerTileBlock F μ ν K hK hμ hν blockS blockT X Y φ k f t c =
      PartialMatching.maxCardValue
        (blockCost blockS blockT
          (perturbedEdgeCost (finslerTileKinetic F X Y φ k)
            (finslerTileProbe μ ν K hK hμ hν X Y f) t) c) :=
  rfl

/-- **Per-tile frozen-block comparison (one-sided).**

For fixed labels and a fixed tile `c`, assume only on the edges of the tile:

* the relative freezing bound
  `|finslerTileKinetic … - frozenCost| ≤ 2 ε * frozenCost`;
* `frozenCost ≥ 0` (it is a frozen quadratic kinetic cost);
* the probe bound `|physical probe - modelProbe| ≤ B`;
* the model probe bound `|modelProbe| ≤ Gb`.

Then the physical tile block is at most `(1 + 2 ε)` times the frozen/model tile
block plus `min (#S_c) (#T_c) * (|t| * B + 2 ε * |t| * Gb)`. -/
theorem finslerTileBlock_le_frozenModelTileBlock
    (F : ContinuousFinslerNorm E M)
    {n : ℕ} (μ ν : ProbabilityMeasure M) (K : Set M) (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (blockS blockT : Fin (n + 1) → ι) (X Y : Fin (n + 1) → M)
    (φ : M → ℝ) (k : ℝ) (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : ι)
    (frozenCost modelProbe : Fin (n + 1) → Fin (n + 1) → ℝ)
    {ε B Gb : ℝ} (hε0 : 0 ≤ ε)
    (hF0 : ∀ i j, blockS i = c → blockT j = c → 0 ≤ frozenCost i j)
    (hrel : ∀ i j, blockS i = c → blockT j = c →
      |finslerTileKinetic F X Y φ k i j - frozenCost i j| ≤ (2 * ε) * frozenCost i j)
    (hprobe : ∀ i j, blockS i = c → blockT j = c →
      |finslerTileProbe μ ν K hK hμ hν X Y f i j - modelProbe i j| ≤ B)
    (hG : ∀ i j, blockS i = c → blockT j = c → |modelProbe i j| ≤ Gb) :
    finslerTileBlock F μ ν K hK hμ hν blockS blockT X Y φ k f t c ≤
      (1 + 2 * ε) * frozenModelTileBlock blockS blockT frozenCost modelProbe t c +
        (min (blockSizeS blockS c) (blockSizeT blockT c) : ℝ) *
          (|t| * B + 2 * ε * (|t| * Gb)) := by
  have h := PartialMatching.maxCardValue_blockCost_perturbed_le_of_relative
    (blockS := blockS) (blockT := blockT) (c := c)
    (F := frozenCost) (P := finslerTileKinetic F X Y φ k)
    (G := modelProbe) (Q := finslerTileProbe μ ν K hK hμ hν X Y f)
    (t := t) (B := B) (δ := 2 * ε) (Gb := Gb)
    (by linarith) hF0 hrel hprobe hG
  rwa [finslerTileBlock_eq_maxCardValue_blockCost]

/-- **Per-tile frozen-block comparison (two-sided).**

Under the hypotheses of the one-sided comparison together with `2 ε ≤ 1` and
`Gb ≥ 0`, the physical and frozen/model tile blocks differ by at most

`2 ε * (frozen + min (#S_c) (#T_c) * |t| * Gb) + min (#S_c) (#T_c) * |t| * B`.

Equivalently, the physical value lies in
`[(1 - 2 ε) * frozen - 2 ε * min * |t| * Gb - min * |t| * B,
  (1 + 2 ε) * frozen + 2 ε * min * |t| * Gb + min * |t| * B]`. -/
theorem abs_finslerTileBlock_sub_frozenModelTileBlock_le
    (F : ContinuousFinslerNorm E M)
    {n : ℕ} (μ ν : ProbabilityMeasure M) (K : Set M) (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (blockS blockT : Fin (n + 1) → ι) (X Y : Fin (n + 1) → M)
    (φ : M → ℝ) (k : ℝ) (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : ι)
    (frozenCost modelProbe : Fin (n + 1) → Fin (n + 1) → ℝ)
    {ε B Gb : ℝ} (hε0 : 0 ≤ ε) (hε1 : 2 * ε ≤ 1) (hGb0 : 0 ≤ Gb)
    (hF0 : ∀ i j, blockS i = c → blockT j = c → 0 ≤ frozenCost i j)
    (hrel : ∀ i j, blockS i = c → blockT j = c →
      |finslerTileKinetic F X Y φ k i j - frozenCost i j| ≤ (2 * ε) * frozenCost i j)
    (hprobe : ∀ i j, blockS i = c → blockT j = c →
      |finslerTileProbe μ ν K hK hμ hν X Y f i j - modelProbe i j| ≤ B)
    (hG : ∀ i j, blockS i = c → blockT j = c → |modelProbe i j| ≤ Gb) :
    |finslerTileBlock F μ ν K hK hμ hν blockS blockT X Y φ k f t c -
        frozenModelTileBlock blockS blockT frozenCost modelProbe t c| ≤
      (2 * ε) * (frozenModelTileBlock blockS blockT frozenCost modelProbe t c +
          (min (blockSizeS blockS c) (blockSizeT blockT c) : ℝ) * |t| * Gb) +
        (min (blockSizeS blockS c) (blockSizeT blockT c) : ℝ) * (|t| * B) := by
  have h := PartialMatching.abs_maxCardValue_blockCost_perturbed_sub_le_of_relative
    (blockS := blockS) (blockT := blockT) (c := c)
    (F := frozenCost) (P := finslerTileKinetic F X Y φ k)
    (G := modelProbe) (Q := finslerTileProbe μ ν K hK hμ hν X Y f)
    (t := t) (B := B) (δ := 2 * ε) (Gb := Gb)
    (by linarith) hε1 hGb0 hF0 hrel hprobe hG
  rwa [finslerTileBlock_eq_maxCardValue_blockCost]

end Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

namespace Reconstruction

/-! ## From the physical Taylor remainder to the frozen kinetic matrix

The geometry lane produces the relative freezing bound
`TaylorRootCover.physical_relative`, whose statement is
`|(lengthEDist x y).toReal - u y + u x - frozenPhysicalCost| ≤ 2 ε * frozenPhysicalCost`.
The next three lemmas connect it to the hypotheses of the tile comparison above,
with `frozenCost = k * frozenPhysicalCost` and `φ = u`. -/

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

/-- The frozen physical cost of a core is nonnegative on its retained centers:
it is a quadratic form of a positive definite coefficient matrix. -/
theorem frozenPhysicalCost_nonneg
    {C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ} {ε : ℝ}
    (D : C.TaylorRootCover ε) {z₀ : Z} (hz₀ : z₀ ∈ D.centers) {x y : M}
    (hp : (u x, u y) ∈ C.window.region) :
    0 ≤ C.frozenPhysicalCost z₀ x y := by
  have hpos : (C.matrix z₀ (u x, u y)).PosDef :=
    C.coefficient_posDef z₀ (D.subset hz₀) (u x, u y) hp
  unfold OriginalPopulationCoefficientCore.frozenPhysicalCost
  dsimp only
  rcases eq_or_ne ((Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFun
      (populationSeedRootLabelValue (P C.seedIndex).seed a (a y) -
        populationSeedRootLabelValue (P C.seedIndex).seed a (a x))) 0 with hv | hv
  · rw [hv, matrixQuadratic_zero]
  · exact (matrixQuadratic_pos hpos hv).le

variable [T2Space M] [PreconnectedSpace M] [BorelSpace M]
  [MeasurableSpace.CountablySeparated Z]
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instPhysRelativeMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

/-- **The Taylor relative bound in tile form.**  The relative freezing estimate
`TaylorRootCover.physical_relative`, scaled by the nonnegative kinetic
coefficient `k`, is exactly the frozen-comparison hypothesis of the tile block
for `frozenCost = k * frozenPhysicalCost`. -/
theorem abs_finslerTileKinetic_sub_frozenPhysical_le
    {C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ} {ε : ℝ}
    (D : C.TaylorRootCover ε) (hε : 0 ≤ ε)
    {n : ℕ} (X Y : Fin (n + 1) → M) (k : ℝ) (hk : 0 ≤ k)
    (z₀ : Fin (n + 1) → Fin (n + 1) → Z) (i j : Fin (n + 1))
    (hcenter : z₀ i j ∈ D.centers)
    (hx : a (X i) ∈ C.roots ∩ D.neighborhood (z₀ i j))
    (hy : a (Y j) ∈ C.roots ∩ D.neighborhood (z₀ i j))
    (hp : (u (X i), u (Y j)) ∈ C.window.region)
    (hxread : X i = (P C.seedIndex).seed.curve
      (populationSeedRootLabelValue (P C.seedIndex).seed a (a (X i)))
      (u (X i) - (P C.seedIndex).seed.level))
    (hyread : Y j = (P C.seedIndex).seed.curve
      (populationSeedRootLabelValue (P C.seedIndex).seed a (a (Y j)))
      (u (Y j) - (P C.seedIndex).seed.level)) :
    |Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex.finslerTileKinetic
        F X Y u k i j -
        k * C.frozenPhysicalCost (z₀ i j) (X i) (Y j)| ≤
      (2 * ε) * (k * C.frozenPhysicalCost (z₀ i j) (X i) (Y j)) := by
  letI : MetricSpace M := F.metricSpace
  have hb := D.physical_relative hF hcomplete hu ha hinj hε hcenter hx hy hp hxread hyread
  dsimp only [Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex.finslerTileKinetic]
  dsimp only [distanceSlackEdgeCost]
  rw [F.metricSpace_dist, ← mul_sub, abs_mul, abs_of_nonneg hk]
  calc k * |((F.lengthEDist (X i) (Y j)).toReal - u (Y j) + u (X i)) -
        C.frozenPhysicalCost (z₀ i j) (X i) (Y j)|
      ≤ k * ((2 * ε) * C.frozenPhysicalCost (z₀ i j) (X i) (Y j)) :=
        mul_le_mul_of_nonneg_left hb hk
    _ = (2 * ε) * (k * C.frozenPhysicalCost (z₀ i j) (X i) (Y j)) := by ring

/-- **Tile comparison from the physical Taylor remainder.**

This is the frozen-block comparison in the form produced by the geometry lane:
the freezing hypothesis is discharged from one `TaylorRootCover` and its
`physical_relative` estimate on each edge of the tile, and the frozen kinetic
matrix is the actual frozen physical cost `k * frozenPhysicalCost` at the
retained reference root of the edge.  The geometric side conditions (reference
center, source and target roots in its neighborhood, coordinate window and the
exact seed readout of both endpoints) are assumed only on the edges of the
tile, exactly as in `expected_finite_finsler_pressure`. -/
theorem finslerTileBlock_le_frozenPhysicalTileBlock
    {C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ} {ε : ℝ}
    (D : C.TaylorRootCover ε) (hε : 0 ≤ ε)
    {n : ℕ} (μ ν : ProbabilityMeasure M) (K : Set M) (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (blockS blockT : Fin (n + 1) → ι) (X Y : Fin (n + 1) → M)
    (k : ℝ) (hk : 0 ≤ k) (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : ι)
    (modelProbe : Fin (n + 1) → Fin (n + 1) → ℝ)
    (z₀ : Fin (n + 1) → Fin (n + 1) → Z)
    (hgeom : ∀ i j, blockS i = c → blockT j = c →
      z₀ i j ∈ D.centers ∧
      a (X i) ∈ C.roots ∩ D.neighborhood (z₀ i j) ∧
      a (Y j) ∈ C.roots ∩ D.neighborhood (z₀ i j) ∧
      (u (X i), u (Y j)) ∈ C.window.region ∧
      X i = (P C.seedIndex).seed.curve
        (populationSeedRootLabelValue (P C.seedIndex).seed a (a (X i)))
        (u (X i) - (P C.seedIndex).seed.level) ∧
      Y j = (P C.seedIndex).seed.curve
        (populationSeedRootLabelValue (P C.seedIndex).seed a (a (Y j)))
        (u (Y j) - (P C.seedIndex).seed.level))
    {B Gb : ℝ}
    (hprobe : ∀ i j, blockS i = c → blockT j = c →
      |Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex.finslerTileProbe
          μ ν K hK hμ hν X Y f i j - modelProbe i j| ≤ B)
    (hG : ∀ i j, blockS i = c → blockT j = c → |modelProbe i j| ≤ Gb) :
    Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex.finslerTileBlock
        F μ ν K hK hμ hν blockS blockT X Y u k f t c ≤
      (1 + 2 * ε) * frozenModelTileBlock blockS blockT
          (fun i j => k * C.frozenPhysicalCost (z₀ i j) (X i) (Y j)) modelProbe t c +
        (min (blockSizeS blockS c) (blockSizeT blockT c) : ℝ) *
          (|t| * B + 2 * ε * (|t| * Gb)) := by
  apply Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex.finslerTileBlock_le_frozenModelTileBlock
    F μ ν K hK hμ hν blockS blockT X Y u k f t c
    (fun i j => k * C.frozenPhysicalCost (z₀ i j) (X i) (Y j)) modelProbe hε
  · intro i j h1 h2
    obtain ⟨hcenter, -, -, hp, -, -⟩ := hgeom i j h1 h2
    exact mul_nonneg hk (frozenPhysicalCost_nonneg D hcenter hp)
  · intro i j h1 h2
    obtain ⟨hcenter, hx, hy, hp, hxread, hyread⟩ := hgeom i j h1 h2
    exact abs_finslerTileKinetic_sub_frozenPhysical_le hF hcomplete hu ha hinj D hε X Y k hk
      z₀ i j hcenter hx hy hp hxread hyread
  · exact hprobe
  · exact hG

end Reconstruction

end OTSelector
