import OTSelector.Limit.FinslerFrozenBlockBridge
import OTSelector.Limit.FinslerTileBlockMeasurability
import OTSelector.Limit.TileCountBinomialLaw

/-!
# The frozen-comparison upper bound on the canonical two-colour sample space

`OTSelector.Limit.FinslerFrozenBlockBridge` proves the expectation upper bound
and the `hupper` clause of the general Finsler selector under an arbitrary
sample space `Ω n`, probability laws `P n`, coordinate maps `X n i`, `Y n j`
and the explicit joint-law hypothesis

`(P n).map (fun ξ => (fun i => X n i ξ, fun j => Y n j ξ)) = twoColourLaw μ ν (n+1)`,

together with the count integrability `hintCount`, the binomial count bound
`hcount` and the per-block integrability of the physical and frozen blocks
`hintBlock`, `hintModel`.

This module instantiates that interface on the *canonical* two-colour sample
space

`canonicalOmega M n = (Fin (n+1) → M) × (Fin (n+1) → M)`

with the product law

`canonicalLaw μ ν n = twoColourLaw (μ : Measure M) (ν : Measure M) (n+1)`,
whose source and target coordinates are the canonical projections
`canonicalX n i` and `canonicalY n j`.  On this space

* the coordinate measurabilities and marginal laws `hX`, `hY`, `hXlaw`,
  `hYlaw` are proved from the evaluation maps of the product law;
* the joint law `hlaw` holds definitionally, because the tuple of coordinate
  maps is the identity;
* the tile labels `cellS ∘ canonicalX`, `cellT ∘ canonicalY` have the product
  of the two iid label laws as joint law, which gives `hcount` from
  `integral_abs_tileCount_sub_le_of_jointLaw`;
* `hintCount` follows from measurability of the labels alone
  (`integrable_abs_tileCount_sub`);
* `hintBlock` is `integrable_finslerNormalizedTileBlock_of_laws` with the
  marginal laws just proved;
* `hintModel` follows from the measurability of the random-label block value
  (`measurable_blockValue_random`) and the bounds `hCbnd`, `hGbnd` on
  the marked kernels (`integrable_blockValue_random`).

The resulting theorem `finsler_hupper_of_frozen_comparison_canonical` keeps
exactly the geometric/analytic hypotheses of
`finslerExpectationUpperBound_of_frozen_comparison'` (per-edge comparison,
atlas facts, kernel bounds, the frozen model bound `hmodel_bound`, and the
vanishing additive error `hδ`), with the sample space fixed to the canonical
one and all of `hX hY hXlaw hYlaw hlaw hintCount hcount hintBlock hintModel`
discharged internally.

No `sorry`, `admit` or added axiom occurs.
-/

open MeasureTheory ProbabilityTheory Filter Manifold OTSelector.Probability
open scoped BigOperators ENNReal NNReal Topology ContDiff BoundedContinuousFunction
  unitInterval

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace OTSelector.Probability

/-! ## The canonical two-colour sample space -/

/-- The canonical two-colour sample space at sample size `n + 1`: a source word
and a target word, each consisting of `n + 1` points of `M`. -/
abbrev canonicalOmega (M : Type*) (n : ℕ) : Type _ :=
  (Fin (n + 1) → M) × (Fin (n + 1) → M)

/-- The source coordinates of the canonical two-colour sample. -/
def canonicalX {M : Type*} (n : ℕ) (i : Fin (n + 1)) (p : canonicalOmega M n) : M :=
  p.1 i

/-- The target coordinates of the canonical two-colour sample. -/
def canonicalY {M : Type*} (n : ℕ) (j : Fin (n + 1)) (p : canonicalOmega M n) : M :=
  p.2 j

/-- The canonical two-colour sample law: `n + 1` iid source points with law
`μ` and `n + 1` iid target points with law `ν`. -/
noncomputable def canonicalLaw {M : Type*} [MeasurableSpace M]
    (μ ν : ProbabilityMeasure M) (n : ℕ) : Measure (canonicalOmega M n) :=
  twoColourLaw (μ : Measure M) (ν : Measure M) (n + 1)

instance canonicalLaw_isProbabilityMeasure {M : Type*} [MeasurableSpace M]
    (μ ν : ProbabilityMeasure M) (n : ℕ) : IsProbabilityMeasure (canonicalLaw μ ν n) := by
  unfold canonicalLaw
  infer_instance

/-- The source coordinate maps of the canonical sample are measurable. -/
theorem measurable_canonicalX {M : Type*} [MeasurableSpace M] (n : ℕ) (i : Fin (n + 1)) :
    Measurable (canonicalX (M := M) n i) := by
  unfold canonicalX
  exact (measurable_pi_apply i).comp measurable_fst

/-- The target coordinate maps of the canonical sample are measurable. -/
theorem measurable_canonicalY {M : Type*} [MeasurableSpace M] (n : ℕ) (j : Fin (n + 1)) :
    Measurable (canonicalY (M := M) n j) := by
  unfold canonicalY
  exact (measurable_pi_apply j).comp measurable_snd

/-- **The source marginal law on the canonical space.**  The `i`-th source
coordinate of `canonicalLaw μ ν n` has law `μ`. -/
theorem canonicalLaw_map_canonicalX {M : Type*} [MeasurableSpace M]
    (μ ν : ProbabilityMeasure M) (n : ℕ) (i : Fin (n + 1)) :
    (canonicalLaw μ ν n).map (canonicalX (M := M) n i) = (μ : Measure M) := by
  classical
  unfold canonicalLaw canonicalX twoColourLaw
  rw [show (fun p : (Fin (n + 1) → M) × (Fin (n + 1) → M) => p.1 i)
      = (fun x : Fin (n + 1) → M => x i) ∘ Prod.fst from rfl]
  rw [← Measure.map_map (measurable_pi_apply i) measurable_fst]
  rw [Measure.map_fst_prod]
  have hνuniv : (Measure.pi (fun _ : Fin (n + 1) => (ν : Measure M))) Set.univ = 1 :=
    measure_univ
  rw [hνuniv, one_smul]
  rw [Measure.pi_map_eval]
  simp

/-- **The target marginal law on the canonical space.**  The `j`-th target
coordinate of `canonicalLaw μ ν n` has law `ν`. -/
theorem canonicalLaw_map_canonicalY {M : Type*} [MeasurableSpace M]
    (μ ν : ProbabilityMeasure M) (n : ℕ) (j : Fin (n + 1)) :
    (canonicalLaw μ ν n).map (canonicalY (M := M) n j) = (ν : Measure M) := by
  classical
  unfold canonicalLaw canonicalY twoColourLaw
  rw [show (fun p : (Fin (n + 1) → M) × (Fin (n + 1) → M) => p.2 j)
      = (fun y : Fin (n + 1) → M => y j) ∘ Prod.snd from rfl]
  rw [← Measure.map_map (measurable_pi_apply j) measurable_snd]
  rw [Measure.map_snd_prod]
  have hμuniv : (Measure.pi (fun _ : Fin (n + 1) => (μ : Measure M))) Set.univ = 1 :=
    measure_univ
  rw [hμuniv, one_smul]
  rw [Measure.pi_map_eval]
  simp

/-- **The joint sample law on the canonical space is the identity law.**  The
tuple of all source and target coordinates is the identity map of the canonical
sample space, so its pushforward is the sample law itself. -/
theorem canonicalLaw_map_sample {M : Type*} [MeasurableSpace M]
    (μ ν : ProbabilityMeasure M) (n : ℕ) :
    (canonicalLaw μ ν n).map
      (fun ξ : canonicalOmega M n =>
        (fun i => canonicalX (M := M) n i ξ, fun j => canonicalY (M := M) n j ξ)) =
      twoColourLaw (μ : Measure M) (ν : Measure M) (n + 1) := by
  unfold canonicalLaw canonicalX canonicalY
  rw [show (fun ξ : (Fin (n + 1) → M) × (Fin (n + 1) → M) =>
        (fun i => ξ.1 i, fun j => ξ.2 j)) = id from rfl]
  exact Measure.map_id

/-! ## The joint law of the two label words -/

/-- **The joint law of the two tile-label words on the canonical space.**

Under `canonicalLaw μ ν n`, the source label word `fun i => cellS (canonicalX n i ·)`
is iid with common law `μ.map cellS`, the target label word is iid with common
law `ν.map cellT`, and the two words are independent: their joint law is the
product of the two iid label laws. -/
theorem canonicalLaw_map_labels {M : Type*} [MeasurableSpace M]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (μ ν : ProbabilityMeasure M) (cellS cellT : M → ι)
    (hcellS : Measurable cellS) (hcellT : Measurable cellT) (n : ℕ) :
    (canonicalLaw μ ν n).map
      (fun ξ : canonicalOmega M n =>
        (fun i => cellS (canonicalX (M := M) n i ξ),
          fun j => cellT (canonicalY (M := M) n j ξ))) =
      (iidLabelMeasure (n + 1) (Measure.map cellS (μ : Measure M))).prod
        (iidLabelMeasure (n + 1) (Measure.map cellT (ν : Measure M))) := by
  classical
  haveI : IsProbabilityMeasure (Measure.map cellS (μ : Measure M)) :=
    Measure.isProbabilityMeasure_map hcellS.aemeasurable
  haveI : IsProbabilityMeasure (Measure.map cellT (ν : Measure M)) :=
    Measure.isProbabilityMeasure_map hcellT.aemeasurable
  have hA : Measurable (fun x : Fin (n + 1) → M => fun i => cellS (x i)) :=
    measurable_pi_lambda _ fun i => hcellS.comp (measurable_pi_apply i)
  have hB : Measurable (fun y : Fin (n + 1) → M => fun j => cellT (y j)) :=
    measurable_pi_lambda _ fun j => hcellT.comp (measurable_pi_apply j)
  unfold canonicalLaw canonicalX canonicalY twoColourLaw
  rw [show (fun ξ : (Fin (n + 1) → M) × (Fin (n + 1) → M) =>
        (fun i => cellS (ξ.1 i), fun j => cellT (ξ.2 j)))
      = Prod.map (fun x : Fin (n + 1) → M => fun i => cellS (x i))
          (fun y : Fin (n + 1) → M => fun j => cellT (y j)) from rfl]
  rw [← Measure.map_prod_map
    (Measure.pi (fun _ : Fin (n + 1) => (μ : Measure M)))
    (Measure.pi (fun _ : Fin (n + 1) => (ν : Measure M))) hA hB]
  have hAeq : Measure.map (fun x : Fin (n + 1) → M => fun i => cellS (x i))
      (Measure.pi (fun _ : Fin (n + 1) => (μ : Measure M))) =
      iidLabelMeasure (n + 1) (Measure.map cellS (μ : Measure M)) := by
    rw [Measure.pi_map_pi (f := fun _ : Fin (n + 1) => cellS)
      (fun _ => hcellS.aemeasurable)]
    rfl
  have hBeq : Measure.map (fun y : Fin (n + 1) → M => fun j => cellT (y j))
      (Measure.pi (fun _ : Fin (n + 1) => (ν : Measure M))) =
      iidLabelMeasure (n + 1) (Measure.map cellT (ν : Measure M)) := by
    rw [Measure.pi_map_pi (f := fun _ : Fin (n + 1) => cellT)
      (fun _ => hcellT.aemeasurable)]
    rfl
  rw [hAeq, hBeq]

end OTSelector.Probability

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

open OTSelector.Probability

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

/-! ## Discharged count and integrability inputs -/

/-- **`hintCount` on the canonical space.**  The absolute tile-count
discrepancy of the canonical label words is integrable from measurability of
the label maps alone. -/
theorem integrable_abs_canonicalTileCount {ι : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ ν : ProbabilityMeasure M) (cellS cellT : M → ι)
    (hcellS : Measurable cellS) (hcellT : Measurable cellT) (n : ℕ) (c : ι) :
    Integrable (fun ξ =>
      |tileSourceCount (fun i ω' => cellS (canonicalX (M := M) n i ω')) c ξ -
        tileTargetCount (fun j ω' => cellT (canonicalY (M := M) n j ω')) c ξ|)
      (canonicalLaw μ ν n) :=
  integrable_abs_tileCount_sub
    (fun i ξ => cellS (canonicalX (M := M) n i ξ))
    (fun j ξ => cellT (canonicalY (M := M) n j ξ)) c (canonicalLaw μ ν n)
    (fun i => hcellS.comp (measurable_canonicalX n i))
    (fun j => hcellT.comp (measurable_canonicalY n j))

/-- **`hcount` on the canonical space.**  If the tile `c` has mass `w c` under
both marginals, the mean absolute tile-count discrepancy of the canonical label
words is at most `sqrt (2 (n+1) w)`. -/
theorem integral_abs_canonicalTileCount_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ ν : ProbabilityMeasure M) (cellS cellT : M → ι)
    (hcellS : Measurable cellS) (hcellT : Measurable cellT)
    (w : ι → unitInterval) (c : ι)
    (hmassS : (μ : Measure M) (cellS ⁻¹' {c}) = ENNReal.ofReal (w c : ℝ))
    (hmassT : (ν : Measure M) (cellT ⁻¹' {c}) = ENNReal.ofReal (w c : ℝ)) (n : ℕ) :
    ∫ ξ, |tileSourceCount (fun i ω' => cellS (canonicalX (M := M) n i ω')) c ξ -
        tileTargetCount (fun j ω' => cellT (canonicalY (M := M) n j ω')) c ξ|
      ∂(canonicalLaw μ ν n) ≤
      Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) * (w c : ℝ)) := by
  classical
  haveI : IsProbabilityMeasure (Measure.map cellS (μ : Measure M)) :=
    Measure.isProbabilityMeasure_map hcellS.aemeasurable
  haveI : IsProbabilityMeasure (Measure.map cellT (ν : Measure M)) :=
    Measure.isProbabilityMeasure_map hcellT.aemeasurable
  have hjoint := canonicalLaw_map_labels μ ν cellS cellT hcellS hcellT n
  have hmapS : (Measure.map cellS (μ : Measure M)) {c} = ENNReal.ofReal (w c : ℝ) := by
    rw [Measure.map_apply hcellS (measurableSet_singleton c), hmassS]
  have hmapT : (Measure.map cellT (ν : Measure M)) {c} = ENNReal.ofReal (w c : ℝ) := by
    rw [Measure.map_apply hcellT (measurableSet_singleton c), hmassT]
  have hw : ((Measure.map cellS (μ : Measure M)) {c}).toReal =
      ((Measure.map cellT (ν : Measure M)) {c}).toReal := by
    rw [hmapS, hmapT]
  have h := integral_abs_tileCount_sub_le_of_jointLaw (n := n)
    (blockS := fun i ξ => cellS (canonicalX (M := M) n i ξ))
    (blockT := fun j ξ => cellT (canonicalY (M := M) n j ξ))
    c (canonicalLaw μ ν n)
    (Measure.map cellS (μ : Measure M)) (Measure.map cellT (ν : Measure M))
    (fun i => hcellS.comp (measurable_canonicalX n i))
    (fun j => hcellT.comp (measurable_canonicalY n j)) hjoint hw
  simpa only [hmapS, ENNReal.toReal_ofReal (w c).2.1] using h

/-- **`hintBlock` on the canonical space.**  The normalized physical Finsler
tile block is integrable under the canonical law, by
`integrable_finslerNormalizedTileBlock_of_laws`, whose a.e. membership in the
compact carrier is derived from the marginal laws proved above. -/
theorem integrable_finslerNormalizedTileBlock_canonical
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (cellS cellT : M → ι) (hcellS : Measurable cellS) (hcellT : Measurable cellT)
    (φ : M → ℝ)
    (hφ : let _instCanonicalBlockMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    (hφmeas : Measurable φ)
    (q : ℕ) (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : ι) :
    Integrable (fun ξ =>
      finslerNormalizedTileBlock (n := n) (ι := ι) F μ ν K hK.measurableSet hμ hν
        (fun i ω' => cellS (canonicalX (M := M) n i ω'))
        (fun j ω' => cellT (canonicalY (M := M) n j ω'))
        (canonicalX (M := M) n) (canonicalY (M := M) n) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t c ξ) (canonicalLaw μ ν n) :=
  integrable_finslerNormalizedTileBlock_of_laws (F := F) hcomplete
    (P := canonicalLaw μ ν n) (n := n) μ ν K hK hμ hν
    (fun i ξ => cellS (canonicalX (M := M) n i ξ))
    (fun j ξ => cellT (canonicalY (M := M) n j ξ))
    (canonicalX (M := M) n) (canonicalY (M := M) n) φ hφ hφmeas
    (fun i => hcellS.comp (measurable_canonicalX n i))
    (fun j => hcellT.comp (measurable_canonicalY n j))
    (measurable_canonicalX n) (measurable_canonicalY n)
    (canonicalLaw_map_canonicalX μ ν n) (canonicalLaw_map_canonicalY μ ν n)
    (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ)))
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) f t c

/-- **`hintModel` on the canonical space.**  The normalized frozen model tile
block is integrable under the canonical law.  The block value is measurable by
`measurable_blockValue_random` (the marked kernels are jointly measurable in
the two points, and the canonical coordinates are measurable), and its
absolute value is bounded by `Cbnd n + |t| * Gbnd`, using the bounds
`hCbnd` and `hGbnd` at the fixed sample size. The kinetic constant may grow
with the sample size. -/
theorem integrable_frozenModelTileBlock_canonical
    {q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    {A C : Type*} [MeasurableSpace A] [MeasurableSpace C]
    {kin : ι → A → C → (Fin q → ℝ) → ℝ} {g : ι → A → C → ℝ}
    (hkin : ∀ c, Measurable (Function.uncurry (fun p : A × C => kin c p.1 p.2)))
    (hg : ∀ c, Measurable (Function.uncurry (g c)))
    (μ ν : ProbabilityMeasure M) (t : ℝ)
    (cellS cellT : M → ι) (hcellS : Measurable cellS) (hcellT : Measurable cellT)
    (coordS : M → Fin q → ℝ) (hcoordS : Measurable coordS)
    (labelS : M → A) (hlabelS : Measurable labelS)
    (coordT : M → Fin q → ℝ) (hcoordT : Measurable coordT)
    (labelT : M → C) (hlabelT : Measurable labelT)
    (w : ι → unitInterval) {Cbnd : ℕ → ℝ} {Gbnd : ℝ}
    (hCbnd0 : ∀ n, 0 ≤ Cbnd n) (hGbnd0 : 0 ≤ Gbnd)
    (hCbnd : ∀ (n : ℕ) (c : ι) (x y : M),
      |markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c)
        (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) x y| ≤ Cbnd n)
    (hGbnd : ∀ (c : ι) (x y : M),
      |markedProbeKernel (g c) (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT)
        x y| ≤ Gbnd)
    (n : ℕ) (c : ι) :
    Integrable (fun ξ =>
      OTSelector.frozenModelTileBlock
        (fun i => cellS (canonicalX (M := M) n i ξ))
        (fun j => cellT (canonicalY (M := M) n j ξ))
        (fun i j => markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c)
          (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT)
          (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ))
        (fun i j => markedProbeKernel (g c) (atlasMarkMap coordS labelS)
          (atlasMarkMap coordT labelT)
          (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ))
        t c / ((n + 1 : ℕ) : ℝ)) (canonicalLaw μ ν n) := by
  classical
  -- Joint measurability of the marked kernels in the two points.
  have hkinJoint : Measurable fun p : M × M =>
      markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c)
        (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) p.1 p.2 :=
    measurable_markedKineticKernel (hkin c)
      (atlasMarkMap coordS labelS) (measurable_atlasMarkMap coordS labelS hcoordS hlabelS)
      (atlasMarkMap coordT labelT) (measurable_atlasMarkMap coordT labelT hcoordT hlabelT)
  have hgJoint : Measurable fun p : M × M =>
      markedProbeKernel (g c) (atlasMarkMap coordS labelS)
        (atlasMarkMap coordT labelT) p.1 p.2 :=
    measurable_markedProbeKernel (hg c)
      (atlasMarkMap coordS labelS) (measurable_atlasMarkMap coordS labelS hcoordS hlabelS)
      (atlasMarkMap coordT labelT) (measurable_atlasMarkMap coordT labelT hcoordT hlabelT)
  -- Measurability of the two frozen matrices at each pair of sample points.
  have hcostMeas : ∀ i j, Measurable fun ξ : canonicalOmega M n =>
      markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c)
        (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT)
        (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ) := by
    intro i j
    exact hkinJoint.comp
      ((measurable_canonicalX n i).prodMk (measurable_canonicalY n j))
  have hprobeMeas : ∀ i j, Measurable fun ξ : canonicalOmega M n =>
      markedProbeKernel (g c) (atlasMarkMap coordS labelS)
        (atlasMarkMap coordT labelT)
        (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ) := by
    intro i j
    exact hgJoint.comp
      ((measurable_canonicalX n i).prodMk (measurable_canonicalY n j))
  -- Measurability of the tilted frozen edge costs.
  have hcMeas : ∀ i j, Measurable fun ξ : canonicalOmega M n =>
      perturbedEdgeCost
        (fun i j => markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c)
          (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT)
          (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ))
        (fun i j => markedProbeKernel (g c) (atlasMarkMap coordS labelS)
          (atlasMarkMap coordT labelT)
          (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ)) t i j := by
    intro i j
    unfold perturbedEdgeCost
    exact (hcostMeas i j).add ((hprobeMeas i j).const_mul t)
  -- Measurability of the random-label frozen block.
  have hblockMeas : Measurable fun ξ : canonicalOmega M n =>
      OTSelector.frozenModelTileBlock
        (fun i => cellS (canonicalX (M := M) n i ξ))
        (fun j => cellT (canonicalY (M := M) n j ξ))
        (fun i j => markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c)
          (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT)
          (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ))
        (fun i j => markedProbeKernel (g c) (atlasMarkMap coordS labelS)
          (atlasMarkMap coordT labelT)
          (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ))
        t c := by
    have h := measurable_blockValue_random
      (blockS := fun i ξ => cellS (canonicalX (M := M) n i ξ))
      (blockT := fun j ξ => cellT (canonicalY (M := M) n j ξ))
      (c := fun ξ i j => perturbedEdgeCost
        (fun i j => markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c)
          (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT)
          (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ))
        (fun i j => markedProbeKernel (g c) (atlasMarkMap coordS labelS)
          (atlasMarkMap coordT labelT)
          (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ)) t i j)
      (t := c)
      (fun i => hcellS.comp (measurable_canonicalX n i))
      (fun j => hcellT.comp (measurable_canonicalY n j)) hcMeas
    simpa only [OTSelector.frozenModelTileBlock] using h
  -- The tilted edge bound only needs the constant at the fixed sample size.
  have hB : ∀ ξ : canonicalOmega M n, ∀ i j,
      |perturbedEdgeCost
        (fun i j => markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c)
          (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT)
          (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ))
        (fun i j => markedProbeKernel (g c) (atlasMarkMap coordS labelS)
          (atlasMarkMap coordT labelT)
          (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ)) t i j| ≤
      Cbnd n + |t| * Gbnd := by
    intro ξ i j
    have h1 : |markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c)
        (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT)
        (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ)| ≤ Cbnd n :=
      hCbnd n c _ _
    have h2 : |markedProbeKernel (g c) (atlasMarkMap coordS labelS)
        (atlasMarkMap coordT labelT)
        (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ)| ≤ Gbnd :=
      hGbnd c _ _
    unfold perturbedEdgeCost
    calc |markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c)
          (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT)
          (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ) +
          t * markedProbeKernel (g c) (atlasMarkMap coordS labelS)
            (atlasMarkMap coordT labelT)
            (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ)|
        ≤ |markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c)
            (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT)
            (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ)| +
          |t * markedProbeKernel (g c) (atlasMarkMap coordS labelS)
            (atlasMarkMap coordT labelT)
            (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ)| := abs_add_le _ _
      _ = |markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c)
            (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT)
            (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ)| +
          |t| * |markedProbeKernel (g c) (atlasMarkMap coordS labelS)
            (atlasMarkMap coordT labelT)
            (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ)| := by
          rw [abs_mul]
      _ ≤ Cbnd n + |t| * Gbnd :=
          add_le_add h1 (mul_le_mul_of_nonneg_left h2 (abs_nonneg t))
  have hB0 : 0 ≤ Cbnd n + |t| * Gbnd :=
    add_nonneg (hCbnd0 n) (mul_nonneg (abs_nonneg t) hGbnd0)
  have hraw : Integrable (fun ξ : canonicalOmega M n =>
      OTSelector.frozenModelTileBlock
        (fun i => cellS (canonicalX (M := M) n i ξ))
        (fun j => cellT (canonicalY (M := M) n j ξ))
        (fun i j => markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c)
          (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT)
          (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ))
        (fun i j => markedProbeKernel (g c) (atlasMarkMap coordS labelS)
          (atlasMarkMap coordT labelT)
          (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ))
        t c) (canonicalLaw μ ν n) :=
    integrable_blockValue_random (P := canonicalLaw μ ν n)
      (blockS := fun i ξ => cellS (canonicalX (M := M) n i ξ))
      (blockT := fun j ξ => cellT (canonicalY (M := M) n j ξ))
      (c := fun ξ i j => perturbedEdgeCost
        (fun i j => markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c)
          (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT)
          (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ))
        (fun i j => markedProbeKernel (g c) (atlasMarkMap coordS labelS)
          (atlasMarkMap coordT labelT)
          (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ)) t i j)
      (t := c) hblockMeas hB0 hB
  exact hraw.div_const _

/-! ## The upper bound on the canonical space -/

/-- **The `hupper` clause of the Finsler selector on the canonical two-colour
sample space.**

This is `finslerExpectationUpperBound_of_frozen_comparison'` with the arbitrary
sample space replaced by `canonicalOmega M n = (Fin (n+1) → M) × (Fin (n+1) → M)`,
the law replaced by `canonicalLaw μ ν n = twoColourLaw μ ν (n+1)`, and the
coordinate maps by the canonical projections `canonicalX`, `canonicalY`.  The
hypotheses `hX`, `hY`, `hXlaw`, `hYlaw`, `hlaw`, `hintCount`, `hcount`,
`hintBlock` and `hintModel` are proved internally, so the remaining inputs are
exactly the geometric per-edge comparison, the atlas facts, the kernel bounds,
the frozen model bound `hmodel_bound`, and the vanishing additive error `hδ`.

The conclusion is the `hupper` bound at the weighted sum of the local marked
pressure limits. The raw frozen-kernel bound may depend on the sample size: it
justifies fixed-size integrability and the atlas law identity, and is not used
as a uniform asymptotic bound. -/
theorem finsler_hupper_of_frozen_comparison_canonical
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (μ ν : ProbabilityMeasure M)
    (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (φ : M → ℝ)
    (hφ : let _instUpperPotentialMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (q : ℕ) (hq : 4 < q) {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (w : ι → unitInterval) (hwsum : ∑ c, (w c : ℝ) = 1) (hwpos : ∀ c, 0 < (w c : ℝ))
    {A C : Type*} [MeasurableSpace A] [MeasurableSpace C]
    {kin : ι → A → C → (Fin q → ℝ) → ℝ} {g : ι → A → C → ℝ}
    {Cb G : ℝ} (hCb0 : 0 ≤ Cb) (hG0 : 0 ≤ G)
    (hkin : ∀ c, Measurable (Function.uncurry (fun p : A × C => kin c p.1 p.2)))
    (hkin_bound : ∀ c a b v, |kin c a b v| ≤ Cb * ∑ l, v l ^ 2)
    (hg : ∀ c, Measurable (Function.uncurry (g c)))
    (hgb : ∀ c a b, |g c a b| ≤ G)
    (α : ι → Measure A) (β : ι → Measure C)
    [∀ c, IsProbabilityMeasure (α c)] [∀ c, IsProbabilityMeasure (β c)]
    (p : ι → ℝ → ℝ)
    (hp : ∀ (c : ι) (t : ℝ), Tendsto
      (fun R => markedScalePressure q A C (α c) (β c) (kin c) (g c) R t)
      atTop (𝓝 (p c t)))
    (cellS : M → ι) (hcellS : Measurable cellS)
    (cellT : M → ι) (hcellT : Measurable cellT)
    (hmassS : ∀ c, (μ : Measure M) (cellS ⁻¹' {c}) = ENNReal.ofReal (w c : ℝ))
    (hmassT : ∀ c, (ν : Measure M) (cellT ⁻¹' {c}) = ENNReal.ofReal (w c : ℝ))
    (coordS : M → Fin q → ℝ) (hcoordS : Measurable coordS)
    (labelS : M → A) (hlabelS : Measurable labelS)
    (coordT : M → Fin q → ℝ) (hcoordT : Measurable coordT)
    (labelT : M → C) (hlabelT : Measurable labelT)
    (hcubeS : ∀ c, (((μ : Measure M) (cellS ⁻¹' {c}))⁻¹ •
      (μ : Measure M).restrict (cellS ⁻¹' {c})).map coordS = cubeMeasure (Fin q) 1)
    (hmarkLawS : ∀ c, (((μ : Measure M) (cellS ⁻¹' {c}))⁻¹ •
      (μ : Measure M).restrict (cellS ⁻¹' {c})).map labelS = α c)
    (hindepS : ∀ c, IndepFun coordS labelS
      (((μ : Measure M) (cellS ⁻¹' {c}))⁻¹ •
        (μ : Measure M).restrict (cellS ⁻¹' {c})))
    (hcubeT : ∀ c, (((ν : Measure M) (cellT ⁻¹' {c}))⁻¹ •
      (ν : Measure M).restrict (cellT ⁻¹' {c})).map coordT = cubeMeasure (Fin q) 1)
    (hmarkLawT : ∀ c, (((ν : Measure M) (cellT ⁻¹' {c}))⁻¹ •
      (ν : Measure M).restrict (cellT ⁻¹' {c})).map labelT = β c)
    (hindepT : ∀ c, IndepFun coordT labelT
      (((ν : Measure M) (cellT ⁻¹' {c}))⁻¹ •
        (ν : Measure M).restrict (cellT ⁻¹' {c})))
    {Cbnd : ℕ → ℝ} {Gbnd : ℝ} (hCbnd0 : ∀ n, 0 ≤ Cbnd n) (hGbnd0 : 0 ≤ Gbnd)
    (hCbnd : ∀ (n : ℕ) (c : ι) (x y : M),
      |markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c)
        (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) x y| ≤ Cbnd n)
    (hGbnd : ∀ (c : ι) (x y : M),
      |markedProbeKernel (g c) (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT)
        x y| ≤ Gbnd)
    (ε B Gb Bnd : ℕ → ℝ)
    (hε0 : ∀ n, 0 ≤ ε n) (hB0 : ∀ n, 0 ≤ B n) (hGb0 : ∀ n, 0 ≤ Gb n)
    (hBnd0 : ∀ n, 0 ≤ Bnd n)
    (hF0 : ∀ n c ξ i j,
      cellS (canonicalX (M := M) n i ξ) = c →
      cellT (canonicalY (M := M) n j ξ) = c →
      0 ≤ markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c)
        (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT)
        (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ))
    (hrel : ∀ᶠ n in atTop, ∀ c ξ i j,
      cellS (canonicalX (M := M) n i ξ) = c →
      cellT (canonicalY (M := M) n j ξ) = c →
      |finslerTileKinetic F (fun i => canonicalX (M := M) n i ξ)
          (fun j => canonicalY (M := M) n j ξ) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) i j -
          markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c)
            (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT)
            (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ)| ≤
        2 * ε n * markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c)
            (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT)
            (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ))
    (hprobe : ∀ n c ξ i j,
      cellS (canonicalX (M := M) n i ξ) = c →
      cellT (canonicalY (M := M) n j ξ) = c →
      |finslerTileProbe μ ν K hK.measurableSet hμ hν
          (fun i => canonicalX (M := M) n i ξ)
          (fun j => canonicalY (M := M) n j ξ) f i j -
          markedProbeKernel (g c) (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT)
            (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ)| ≤ B n)
    (hG : ∀ n c ξ i j,
      cellS (canonicalX (M := M) n i ξ) = c →
      cellT (canonicalY (M := M) n j ξ) = c →
      |markedProbeKernel (g c) (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT)
        (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ)| ≤ Gb n)
    (hmodel_bound : ∀ n c, (∫ ξ : canonicalOmega M n,
      frozenModelTileBlock
        (fun i => cellS (canonicalX (M := M) n i ξ))
        (fun j => cellT (canonicalY (M := M) n j ξ))
        (fun i j => markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c)
          (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT)
          (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ))
        (fun i j => markedProbeKernel (g c) (atlasMarkMap coordS labelS)
          (atlasMarkMap coordT labelT)
          (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ))
        t c / ((n + 1 : ℕ) : ℝ) ∂(canonicalLaw μ ν n)) ≤ Bnd n)
    (hδ : Tendsto (fun n =>
      2 * ε n * Bnd n + (|t| * B n + 2 * ε n * (|t| * Gb n))) atTop (𝓝 0)) :
    ∀ ε' : ℝ, 0 < ε' → ∀ᶠ n in atTop,
      (∫ ξ : canonicalOmega M n,
        finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
          (fun i => canonicalX (M := M) n i ξ)
          (fun j => canonicalY (M := M) n j ξ) φ
            (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t ∂(canonicalLaw μ ν n)) ≤
        (∑ c, (w c : ℝ) * p c t) + ε' := by
  classical
  letI : MetricSpace M := F.metricSpace
  have hφL : LipschitzWith 1 φ := hφ
  have hφmeas : Measurable φ := hφL.continuous.measurable
  have hX : ∀ n i, Measurable (canonicalX (M := M) n i) :=
    fun n i => measurable_canonicalX n i
  have hY : ∀ n j, Measurable (canonicalY (M := M) n j) :=
    fun n j => measurable_canonicalY n j
  -- The marginal and joint sample laws.
  have hXlaw : ∀ n i, (canonicalLaw μ ν n).map (canonicalX (M := M) n i) = (μ : Measure M) :=
    fun n i => canonicalLaw_map_canonicalX μ ν n i
  have hYlaw : ∀ n i, (canonicalLaw μ ν n).map (canonicalY (M := M) n i) = (ν : Measure M) :=
    fun n i => canonicalLaw_map_canonicalY μ ν n i
  have hlaw : ∀ n, (canonicalLaw μ ν n).map
      (fun ξ : canonicalOmega M n =>
        (fun i => canonicalX (M := M) n i ξ, fun j => canonicalY (M := M) n j ξ)) =
      twoColourLaw (μ : Measure M) (ν : Measure M) (n + 1) :=
    fun n => canonicalLaw_map_sample μ ν n
  -- The count integrability and the binomial count bound.
  have hintCount : ∀ n c, Integrable (fun ξ =>
      |tileSourceCount (fun i ω' => cellS (canonicalX (M := M) n i ω')) c ξ -
        tileTargetCount (fun j ω' => cellT (canonicalY (M := M) n j ω')) c ξ|)
      (canonicalLaw μ ν n) :=
    fun n c => integrable_abs_canonicalTileCount μ ν cellS cellT hcellS hcellT n c
  have hcount : ∀ n c, ∫ ξ,
      |tileSourceCount (fun i ω' => cellS (canonicalX (M := M) n i ω')) c ξ -
        tileTargetCount (fun j ω' => cellT (canonicalY (M := M) n j ω')) c ξ|
      ∂(canonicalLaw μ ν n) ≤
      Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) * (w c : ℝ)) :=
    fun n c => integral_abs_canonicalTileCount_le μ ν cellS cellT hcellS hcellT
      w c (hmassS c) (hmassT c) n
  -- The physical block and the frozen model block are integrable.
  have hintBlock : ∀ n c, Integrable (fun ξ =>
      finslerNormalizedTileBlock (n := n) (ι := ι) F μ ν K hK.measurableSet hμ hν
        (fun i ω' => cellS (canonicalX (M := M) n i ω'))
        (fun j ω' => cellT (canonicalY (M := M) n j ω'))
        (canonicalX (M := M) n) (canonicalY (M := M) n) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t c ξ) (canonicalLaw μ ν n) :=
    fun n c => integrable_finslerNormalizedTileBlock_canonical (F := F) hcomplete
      μ ν K hK hμ hν cellS cellT hcellS hcellT φ hφ hφmeas q f t n c
  have hintModel : ∀ n c, Integrable (fun ξ =>
      frozenModelTileBlock
        (fun i => cellS (canonicalX (M := M) n i ξ))
        (fun j => cellT (canonicalY (M := M) n j ξ))
        (fun i j => markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c)
          (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT)
          (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ))
        (fun i j => markedProbeKernel (g c) (atlasMarkMap coordS labelS)
          (atlasMarkMap coordT labelT)
          (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ))
        t c / ((n + 1 : ℕ) : ℝ)) (canonicalLaw μ ν n) :=
    fun n c => integrable_frozenModelTileBlock_canonical (q := q) hkin hg μ ν t
      cellS cellT hcellS hcellT coordS hcoordS labelS hlabelS coordT hcoordT labelT hlabelT
      w hCbnd0 hGbnd0 hCbnd hGbnd n c
  exact finslerExpectationUpperBound_of_frozen_comparison' (F := F) hcomplete μ ν K hK hμ hν
    (fun n => canonicalLaw μ ν n)
    (fun n i ξ => canonicalX (M := M) n i ξ)
    (fun n j ξ => canonicalY (M := M) n j ξ)
    (fun n i => measurable_canonicalX n i)
    (fun n j => measurable_canonicalY n j)
    (fun n i => canonicalLaw_map_canonicalX μ ν n i)
    (fun n j => canonicalLaw_map_canonicalY μ ν n j)
    (fun n => canonicalLaw_map_sample μ ν n)
    φ hφ f t q hq w hwsum hwpos hCb0 hG0 hkin hkin_bound hg hgb α β p hp
    cellS hcellS cellT hcellT hmassS hmassT
    coordS hcoordS labelS hlabelS coordT hcoordT labelT hlabelT
    hcubeS hmarkLawS hindepS hcubeT hmarkLawT hindepT
    hCbnd0 hGbnd0 hCbnd hGbnd
    ε B Gb Bnd hε0 hB0 hGb0 hBnd0 hF0 hrel hprobe hG hintBlock hintModel
    hmodel_bound hintCount hcount hδ

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
