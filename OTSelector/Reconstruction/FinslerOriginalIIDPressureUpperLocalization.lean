import OTSelector.Limit.FinslerCanonicalTileData
import OTSelector.Limit.PhysicalSelectorWrapper

/-!
# Actual iid upper pressure localization for the intrinsic Finsler length cost

`OTSelector/Limit/FinslerCanonicalTileData.lean` proves the `hupper` clause of the
general Finsler selector on the *canonical* two-colour sample space
`canonicalOmega M n = (Fin (n+1) → M) × (Fin (n+1) → M)` with the product law
`canonicalLaw μ ν n`, and discharges there all sample-level concentration and
integrability inputs (marginal laws, joint law, tile-count discrepancy,
integrability of the physical and frozen tile blocks).

The paper's sampling model, however, is an *arbitrary* probability space `Ω n`
with arbitrary iid coordinate maps `X n i`, `Y n j` whose marginals are the two
population probabilities and where the source and target families are
independent.  The present module closes that gap:

* `map_prod_iid_eq_canonicalLaw` shows that the joint law of the two iid
  families under the paper's sampling hypotheses is exactly the canonical
  two-colour law (this uses only `iIndepFun`, the marginal laws and the
  independence of the two families);
* `integral_finslerSupportedPressure_eq_canonicalLaw` transfers the expectation
  of the actual supported empirical Finsler pressure from the arbitrary sample
  space to the canonical one (the integrand is measurable because it is a
  continuous function of finitely many measurable coordinates);
* `finsler_hupper_of_iid_frozen_comparison` and its paper-scale form
  `finsler_hupper_of_iid_frozen_comparison_paperScale` are the resulting
  **actual iid limsup upper bound**: for every `ε' > 0` and eventually all `n`,
  the expected supported empirical pressure at the paper scale `(n+1)^(2/q)`
  is at most the explicit weighted sum `∑ c, w c * p c t` of the local marked
  pressure limits, plus `ε'`.

The concentration inputs (tile-count discrepancy, block integrability) are all
supplied by the canonical module; the remaining hypotheses are population-level
data only: the exact cell masses, the Haar/cube coordinate laws, the mark laws
and their independence, uniform kernel bounds, the relative freezing and probe
approximations, the frozen model bound and the vanishing additive error.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold
open scoped Topology ContDiff ENNReal NNReal BigOperators BoundedContinuousFunction
  unitInterval

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

open OTSelector.Probability

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

/-! ## The joint law of the paper's iid sampling model -/

/-- **The joint law of two independent iid families is the canonical law.**

If `X` and `Y` are independent iid families with common marginals `μ` and `ν`
and the two families are independent, then the law of the pair of sample words
is exactly the canonical two-colour law of `n + 1` source and `n + 1` target
points.  This is the joint-law hypothesis of the frozen-comparison lane, proved
from the paper's sampling assumptions. -/
theorem map_prod_iid_eq_canonicalLaw
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (μ ν : ProbabilityMeasure M)
    (X Y : Fin (n + 1) → Ω → M)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j))
    (hXi : iIndepFun X P) (hYi : iIndepFun Y P)
    (hXlaw : ∀ i, P.map (X i) = (μ : Measure M))
    (hYlaw : ∀ j, P.map (Y j) = (ν : Measure M))
    (hXY : IndepFun (fun ξ i => X i ξ) (fun ξ j => Y j ξ) P) :
    P.map (fun ξ => (fun i => X i ξ, fun j => Y j ξ)) = canonicalLaw μ ν n := by
  classical
  have hS : P.map (fun ξ => fun i => X i ξ) =
      Measure.pi (fun _ : Fin (n + 1) => (μ : Measure M)) := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map (fun i => (hX i).aemeasurable)).mp hXi]
    simp only [hXlaw]
  have hT : P.map (fun ξ => fun j => Y j ξ) =
      Measure.pi (fun _ : Fin (n + 1) => (ν : Measure M)) := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map (fun j => (hY j).aemeasurable)).mp hYi]
    simp only [hYlaw]
  have hST : P.map (fun ξ => (fun i => X i ξ, fun j => Y j ξ)) =
      (P.map (fun ξ => fun i => X i ξ)).prod (P.map (fun ξ => fun j => Y j ξ)) :=
    hXY.map_prod_eq_prod_map_map
      (aemeasurable_pi_iff.mpr fun i => (hX i).aemeasurable)
      (aemeasurable_pi_iff.mpr fun j => (hY j).aemeasurable)
  rw [hST, hS, hT]
  simp only [canonicalLaw, twoColourLaw]

/-! ## Transfer of the expected pressure to the canonical sample space -/

/-- **Expectation transfer to the canonical two-colour sample space.**

The actual supported empirical Finsler pressure depends on the sample only
through the two words of points.  Since the joint law of those words is the
canonical two-colour law, the expectation of the pressure under the paper's
sampling model equals the expectation of the pressure on the canonical sample
space.  In particular every upper bound proved on the canonical space is an
upper bound for the actual iid arrays. -/
theorem integral_finslerSupportedPressure_eq_canonicalLaw
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (X Y : Fin (n + 1) → Ω → M)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j))
    (hXi : iIndepFun X P) (hYi : iIndepFun Y P)
    (hXlaw : ∀ i, P.map (X i) = (μ : Measure M))
    (hYlaw : ∀ j, P.map (Y j) = (ν : Measure M))
    (hXY : IndepFun (fun ξ i => X i ξ) (fun ξ j => Y j ξ) P)
    (φ : M → ℝ)
    (hφ : let _instTransferPotentialMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    (k : ℝ) (f : (K × K) →ᵇ ℝ) (t : ℝ) :
    (∫ ξ, finslerSupportedPressure F μ ν K hK hμ hν (fun i => X i ξ) (fun j => Y j ξ)
        φ k f t ∂P) =
      ∫ ρ : canonicalOmega M n, finslerSupportedPressure F μ ν K hK hμ hν
        (fun i => canonicalX (M := M) n i ρ) (fun j => canonicalY (M := M) n j ρ)
        φ k f t ∂(canonicalLaw μ ν n) := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : SecondCountableTopology M :=
    @secondCountable_of_proper M F.metricSpace.toPseudoMetricSpace
      (F.properSpace_of_complete hcomplete)
  have hφL : LipschitzWith 1 φ := hφ
  have hφc : Continuous φ := hφL.continuous
  have hVmeas : Measurable (fun ρ : canonicalOmega M n =>
      finslerSupportedPressure F μ ν K hK hμ hν
        (fun i => canonicalX (M := M) n i ρ) (fun j => canonicalY (M := M) n j ρ)
        φ k f t) := by
    have h := OTSelector.Pressure.measurable_supportedDistancePressure
      (M := M) (Ω := canonicalOmega M n) (n := n + 1) μ ν K hK hμ hν
      (fun i ρ => canonicalX (M := M) n i ρ) (fun j ρ => canonicalY (M := M) n j ρ)
      (fun i => measurable_canonicalX n i) (fun j => measurable_canonicalY n j)
      φ hφc k f t
    simpa only [finslerSupportedPressure] using h
  have hΦ : AEMeasurable (fun ξ => (fun i => X i ξ, fun j => Y j ξ)) P :=
    ((measurable_pi_lambda (fun ξ i => X i ξ) fun i => hX i).prodMk
      (measurable_pi_lambda (fun ξ j => Y j ξ) fun j => hY j)).aemeasurable
  have hmap := map_prod_iid_eq_canonicalLaw P μ ν X Y hX hY hXi hYi hXlaw hYlaw hXY
  have hVc : AEStronglyMeasurable
      (fun ρ : canonicalOmega M n => finslerSupportedPressure F μ ν K hK hμ hν
        (fun i => canonicalX (M := M) n i ρ) (fun j => canonicalY (M := M) n j ρ)
        φ k f t) (Measure.map (fun ξ => (fun i => X i ξ, fun j => Y j ξ)) P) :=
    hmap.symm ▸ hVmeas.aestronglyMeasurable
  have htr := integral_map (μ := P)
    (φ := fun ξ => (fun i => X i ξ, fun j => Y j ξ))
    (f := fun ρ : canonicalOmega M n => finslerSupportedPressure F μ ν K hK hμ hν
      (fun i => canonicalX (M := M) n i ρ) (fun j => canonicalY (M := M) n j ρ)
      φ k f t) hΦ hVc
  rw [hmap] at htr
  simpa only [canonicalX, canonicalY] using htr.symm

/-! ## The actual iid upper pressure localization -/

/-- **The actual iid limsup upper pressure bound at exponent `2 / q`.**

This is the paper's `hupper` input for the intrinsic Finsler length cost on the
*actual* iid sampling model: an arbitrary sample space `Ω n` with probability laws
`P n`, arbitrary iid source and target arrays `X n`, `Y n` with the two population
marginals `μ`, `ν` and with the two families independent.  All sample-level
concentration and integrability inputs are discharged by
`finsler_hupper_of_frozen_comparison_canonical` through the transfer lemmas above;
the conclusion is the expected supported empirical pressure at scale
`(n + 1) ^ (2 / q)` being eventually at most the explicit weighted sum
`∑ c, w c * p c t` of the local marked pressure limits, plus `ε'`.

The remaining hypotheses are population data only: exact cell masses, the
Haar/cube coordinate laws of each cell, the mark laws and their independence,
the uniform kernel bounds, the relative freezing bound `hrel`, the probe
approximation `hprobe`, the frozen model bound `hmodel_bound` and the vanishing
additive bias `hδ`. -/
theorem finsler_hupper_of_iid_frozen_comparison
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (μ ν : ProbabilityMeasure M)
    (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n j, Measurable (Y n j))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n j, (P n).map (Y n j) = (ν : Measure M))
    (hXY : ∀ n, IndepFun (fun ξ i => X n i ξ) (fun ξ j => Y n j ξ) (P n))
    (φ : M → ℝ)
    (hφ : let _instIIDPotentialMetric : MetricSpace M := F.metricSpace
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
    {Cbnd Gbnd : ℝ} (hCbnd0 : 0 ≤ Cbnd) (hGbnd0 : 0 ≤ Gbnd)
    (hCbnd : ∀ (n : ℕ) (c : ι) (x y : M),
      |markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c)
        (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) x y| ≤ Cbnd)
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
    (hrel : ∀ n c ξ i j,
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
      (∫ ξ, finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
        (fun i => X n i ξ) (fun j => Y n j ξ) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t ∂P n) ≤
        (∑ c, (w c : ℝ) * p c t) + ε' := by
  intro ε' hε'
  have hcan := finsler_hupper_of_frozen_comparison_canonical (F := F)
    hcomplete μ ν K hK hμ hν φ hφ f t q hq
    w hwsum hwpos hCb0 hG0 hkin hkin_bound hg hgb α β p hp cellS hcellS cellT hcellT
    hmassS hmassT coordS hcoordS labelS hlabelS coordT hcoordT labelT hlabelT
    hcubeS hmarkLawS hindepS hcubeT hmarkLawT hindepT
    (fun _ => hCbnd0) hGbnd0 hCbnd hGbnd
    ε B Gb Bnd hε0 hB0 hGb0 hBnd0 hF0 (Filter.Eventually.of_forall hrel)
    hprobe hG hmodel_bound hδ
  filter_upwards [hcan ε' hε'] with n hn
  rw [integral_finslerSupportedPressure_eq_canonicalLaw (F := F) hcomplete μ ν K
    hK.measurableSet hμ hν (P n) (X n) (Y n) (hX n) (hY n) (hXi n) (hYi n)
    (hXlaw n) (hYlaw n) (hXY n) φ hφ _ f t]
  exact hn


/-- **The actual iid limsup upper pressure bound at the paper scale.** -/
theorem finsler_hupper_of_iid_frozen_comparison_paperScale
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (μ ν : ProbabilityMeasure M)
    (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n j, Measurable (Y n j))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n j, (P n).map (Y n j) = (ν : Measure M))
    (hXY : ∀ n, IndepFun (fun ξ i => X n i ξ) (fun ξ j => Y n j ξ) (P n))
    (φ : M → ℝ)
    (hφ : let _instIIDPotentialMetric : MetricSpace M := F.metricSpace
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
    {Cbnd Gbnd : ℝ} (hCbnd0 : 0 ≤ Cbnd) (hGbnd0 : 0 ≤ Gbnd)
    (hCbnd : ∀ (n : ℕ) (c : ι) (x y : M),
      |markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c)
        (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) x y| ≤ Cbnd)
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
    (hrel : ∀ n c ξ i j,
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
      2 * ε n * Bnd n + (|t| * B n + 2 * ε n * (|t| * Gb n))) atTop (𝓝 0))
    (hqdim : (q : ℝ) = (Module.finrank ℝ E : ℝ) - 1) :
    ∀ ε' : ℝ, 0 < ε' → ∀ᶠ n in atTop,
      (∫ ξ, finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
        (fun i => X n i ξ) (fun j => Y n j ξ) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t ∂P n) ≤
        (∑ c, (w c : ℝ) * p c t) + ε' := by
  intro ε' hε'
  simpa only [hqdim] using
    finsler_hupper_of_iid_frozen_comparison (F := F) hcomplete μ ν K hK hμ hν P X Y
      hX hY hXi hYi hXlaw hYlaw hXY φ hφ f t q hq w hwsum hwpos hCb0 hG0
      hkin hkin_bound hg hgb α β p hp cellS hcellS cellT hcellT hmassS hmassT
      coordS hcoordS labelS hlabelS coordT hcoordT labelT hlabelT
      hcubeS hmarkLawS hindepS hcubeT hmarkLawT hindepT hCbnd0 hGbnd0 hCbnd hGbnd
      ε B Gb Bnd hε0 hB0 hGb0 hBnd0 hF0 hrel hprobe hG hmodel_bound hδ ε' hε'

/-! ## The paper's original population data -/

/-- **Actual iid global upper pressure localization for the intrinsic Finsler
length cost, stated on the paper's original population data.**

The population probabilities are the physical source and target probabilities
`ωM.withDensity (ofReal ∘ ρ₀)` and `ωM.withDensity (ofReal ∘ ρ₁)`, carried by
the compact supports `A` and `B` (which are disjoint in the paper; only the
individual membership hypotheses are needed here).  The empirical data are
arbitrary iid arrays with those marginals, independent across the two colours.
The dimension is at least six and `q = d - 1`.

The conclusion is the actual limsup upper pressure bound at the paper scale
`(n+1)^(2/(d-1))`, with the explicit population constant `∑ c, w c * p c t`
built from the local marked pressure limits, plus `ε'`. -/
theorem finsler_originalIID_pressure_upper_localization
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (ωM : Measure M) (ρ₀ ρ₁ : M → ℝ)
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)))]
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμA : ∀ᵐ x ∂(physicalSourceProbability ωM ρ₀ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(physicalTargetProbability ωM ρ₁ : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n j, Measurable (Y n j))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ n i, (P n).map (X n i) = ((physicalSourceProbability ωM ρ₀ : Measure M)))
    (hYlaw : ∀ n j, (P n).map (Y n j) = ((physicalTargetProbability ωM ρ₁ : Measure M)))
    (hXY : ∀ n, IndepFun (fun ξ i => X n i ξ) (fun ξ j => Y n j ξ) (P n))
    (φ : M → ℝ)
    (hφ : let _instIIDPotentialMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ)
    (q : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (w : ι → unitInterval) (hwsum : ∑ c, (w c : ℝ) = 1) (hwpos : ∀ c, 0 < (w c : ℝ))
    {Am Cm : Type*} [MeasurableSpace Am] [MeasurableSpace Cm]
    {kin : ι → Am → Cm → (Fin q → ℝ) → ℝ} {g : ι → Am → Cm → ℝ}
    {Cb G : ℝ} (hCb0 : 0 ≤ Cb) (hG0 : 0 ≤ G)
    (hkin : ∀ c, Measurable (Function.uncurry (fun p : Am × Cm => kin c p.1 p.2)))
    (hkin_bound : ∀ c a b v, |kin c a b v| ≤ Cb * ∑ l, v l ^ 2)
    (hg : ∀ c, Measurable (Function.uncurry (g c)))
    (hgb : ∀ c a b, |g c a b| ≤ G)
    (α : ι → Measure Am) (β : ι → Measure Cm)
    [∀ c, IsProbabilityMeasure (α c)] [∀ c, IsProbabilityMeasure (β c)]
    (p : ι → ℝ → ℝ)
    (hp : ∀ (c : ι) (t : ℝ), Tendsto
      (fun R => markedScalePressure q Am Cm (α c) (β c) (kin c) (g c) R t)
      atTop (𝓝 (p c t)))
    (cellS : M → ι) (hcellS : Measurable cellS)
    (cellT : M → ι) (hcellT : Measurable cellT)
    (hmassS : ∀ c, ((physicalSourceProbability ωM ρ₀ : Measure M)) (cellS ⁻¹' {c}) = ENNReal.ofReal (w c : ℝ))
    (hmassT : ∀ c, ((physicalTargetProbability ωM ρ₁ : Measure M)) (cellT ⁻¹' {c}) = ENNReal.ofReal (w c : ℝ))
    (coordS : M → Fin q → ℝ) (hcoordS : Measurable coordS)
    (labelS : M → Am) (hlabelS : Measurable labelS)
    (coordT : M → Fin q → ℝ) (hcoordT : Measurable coordT)
    (labelT : M → Cm) (hlabelT : Measurable labelT)
    (hcubeS : ∀ c, ((((physicalSourceProbability ωM ρ₀ : Measure M)) (cellS ⁻¹' {c}))⁻¹ •
      ((physicalSourceProbability ωM ρ₀ : Measure M)).restrict (cellS ⁻¹' {c})).map coordS = cubeMeasure (Fin q) 1)
    (hmarkLawS : ∀ c, ((((physicalSourceProbability ωM ρ₀ : Measure M)) (cellS ⁻¹' {c}))⁻¹ •
      ((physicalSourceProbability ωM ρ₀ : Measure M)).restrict (cellS ⁻¹' {c})).map labelS = α c)
    (hindepS : ∀ c, IndepFun coordS labelS
      ((((physicalSourceProbability ωM ρ₀ : Measure M)) (cellS ⁻¹' {c}))⁻¹ •
        ((physicalSourceProbability ωM ρ₀ : Measure M)).restrict (cellS ⁻¹' {c})))
    (hcubeT : ∀ c, ((((physicalTargetProbability ωM ρ₁ : Measure M)) (cellT ⁻¹' {c}))⁻¹ •
      ((physicalTargetProbability ωM ρ₁ : Measure M)).restrict (cellT ⁻¹' {c})).map coordT = cubeMeasure (Fin q) 1)
    (hmarkLawT : ∀ c, ((((physicalTargetProbability ωM ρ₁ : Measure M)) (cellT ⁻¹' {c}))⁻¹ •
      ((physicalTargetProbability ωM ρ₁ : Measure M)).restrict (cellT ⁻¹' {c})).map labelT = β c)
    (hindepT : ∀ c, IndepFun coordT labelT
      ((((physicalTargetProbability ωM ρ₁ : Measure M)) (cellT ⁻¹' {c}))⁻¹ •
        ((physicalTargetProbability ωM ρ₁ : Measure M)).restrict (cellT ⁻¹' {c})))
    {Cbnd Gbnd : ℝ} (hCbnd0 : 0 ≤ Cbnd) (hGbnd0 : 0 ≤ Gbnd)
    (hCbnd : ∀ (n : ℕ) (c : ι) (x y : M),
      |markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c)
        (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) x y| ≤ Cbnd)
    (hGbnd : ∀ (c : ι) (x y : M),
      |markedProbeKernel (g c) (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT)
        x y| ≤ Gbnd)
    (ε Berr Gb Bnd : ℕ → ℝ)
    (hε0 : ∀ n, 0 ≤ ε n) (hB0 : ∀ n, 0 ≤ Berr n) (hGb0 : ∀ n, 0 ≤ Gb n)
    (hBnd0 : ∀ n, 0 ≤ Bnd n)
    (hF0 : ∀ n c ξ i j,
      cellS (canonicalX (M := M) n i ξ) = c →
      cellT (canonicalY (M := M) n j ξ) = c →
      0 ≤ markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c)
        (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT)
        (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ))
    (hrel : ∀ n c ξ i j,
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
      |finslerTileProbe (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁) (A ∪ B) (hA.union hB).measurableSet (hμA.mono fun x hx => Or.inl hx) (hνB.mono fun y hy => Or.inr hy)
          (fun i => canonicalX (M := M) n i ξ)
          (fun j => canonicalY (M := M) n j ξ) f i j -
          markedProbeKernel (g c) (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT)
            (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ)| ≤ Berr n)
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
        t c / ((n + 1 : ℕ) : ℝ) ∂(canonicalLaw (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁) n)) ≤ Bnd n)
    (hδ : Tendsto (fun n =>
      2 * ε n * Bnd n + (|t| * Berr n + 2 * ε n * (|t| * Gb n))) atTop (𝓝 0))
    (hqdim : (q : ℝ) = (Module.finrank ℝ E : ℝ) - 1) :
    ∀ ε' : ℝ, 0 < ε' → ∀ᶠ n in atTop,
      (∫ ξ, finslerSupportedPressure F (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁) (A ∪ B) (hA.union hB).measurableSet (hμA.mono fun x hx => Or.inl hx) (hνB.mono fun y hy => Or.inr hy)
        (fun i => X n i ξ) (fun j => Y n j ξ) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t ∂P n) ≤
        (∑ c, (w c : ℝ) * p c t) + ε' := by
  have hq : 4 < q := by
    have hd : (6 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by exact_mod_cast hdim
    have hqR : (4 : ℝ) < (q : ℝ) := by rw [hqdim]; linarith
    exact_mod_cast hqR
  exact finsler_hupper_of_iid_frozen_comparison_paperScale (F := F) hcomplete
    (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁) (A ∪ B) (hA.union hB)
    (hμA.mono fun x hx => Or.inl hx) (hνB.mono fun y hy => Or.inr hy)
    P X Y hX hY hXi hYi hXlaw hYlaw hXY φ hφ f t q hq w hwsum hwpos hCb0 hG0
    hkin hkin_bound hg hgb α β p hp cellS hcellS cellT hcellT hmassS hmassT
    coordS hcoordS labelS hlabelS coordT hcoordT labelT hlabelT
    hcubeS hmarkLawS hindepS hcubeT hmarkLawT hindepT hCbnd0 hGbnd0 hCbnd hGbnd
    ε Berr Gb Bnd hε0 hB0 hGb0 hBnd0 hF0 hrel hprobe hG hmodel_bound hδ hqdim

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
