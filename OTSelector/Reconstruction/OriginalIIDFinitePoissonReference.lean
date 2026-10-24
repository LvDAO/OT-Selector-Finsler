import OTSelector.Reconstruction.MarkedStationaryValueLegalPoissonLaplaceFormula
import OTSelector.PointProcess.MatchingScenePerfect
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputFiniteSimplicity
import OTSelector.PointProcess.PairLaplaceDetermination

/-! Finite uncolored Poisson reference laws on the actual locally finite
measure carrier, at arbitrary nonnegative physical intensity. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal BigOperators CompactlySupported BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

section Block
variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X]

/-- The finite original tuple is encoded without changing its multiplicities. -/
def originalFinitePoissonBlockLocal (base : X) (b : BlockData X) : LocalFiniteMeasure X :=
  LocalConfiguration.toLocalFiniteMeasure (LocalConfiguration.ofTuple base b.2)

/-- The block encoding is exactly the finite original sum of Dirac measures. -/
@[simp]
theorem coe_originalFinitePoissonBlockLocal (base : X) (b : BlockData X) :
    (originalFinitePoissonBlockLocal base b : Measure X) = legalInputBlockMeasure b :=
  LocalConfiguration.countingMeasure_ofTuple b.2

/-- The tuple encoding is measurable on the same vague locally finite carrier. -/
theorem measurable_originalFinitePoissonBlockLocal (base : X) :
    Measurable (originalFinitePoissonBlockLocal base : BlockData X → LocalFiniteMeasure X) := by
  apply measurable_localFiniteMeasure_of_measurable_measure
  simpa only [coe_originalFinitePoissonBlockLocal] using
    (measurable_legalInputBlockMeasure (X := X))

/-- Compact tests of the encoded tuple are their actual finite label sums. -/
@[simp]
theorem testIntegral_originalFinitePoissonBlockLocal (base : X) (b : BlockData X)
    (F : C_c(X, ℝ)) :
    LocalFiniteMeasure.testIntegral (originalFinitePoissonBlockLocal base b) F =
      legalInputBlockTest F b := by
  rw [originalFinitePoissonBlockLocal, LocalConfiguration.testIntegral_toLocalFiniteMeasure,
    LocalConfiguration.testIntegral_ofTuple]
  rfl
end Block

/-- The normalized actual Haar spatial point law in a nonempty cube is a
probability, in every spatial dimension. -/
theorem isProbabilityMeasure_originalFinitePoissonWindowPointLaw
    (q : ℕ) {S : ℝ} (hS : 0 < S) :
    IsProbabilityMeasure (normalizedFiniteLaw
      ((volume : Measure (Fin q → ℝ)).restrict (haarRootCube (Fin q) S))) := by
  have hfin : volume (haarRootCube (Fin q) S) ≠ ⊤ := isCompact_Icc.measure_ne_top
  have hpos : volume (haarRootCube (Fin q) S) ≠ 0 := by
    rw [volume_haarRootCube (Fin q) hS.le, Fintype.card_fin]
    exact (ENNReal.ofReal_pos.mpr (pow_pos (by positivity : 0 < 2 * S) q)).ne'
  have originalFinitePoissonWindowFinite : IsFiniteMeasure
      ((volume : Measure (Fin q → ℝ)).restrict (haarRootCube (Fin q) S)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hfin.lt_top⟩
  apply normalizedFiniteLaw_probability
  simpa only [Measure.real, Measure.restrict_apply_univ] using ENNReal.toReal_pos hpos hfin

/-- One finite uncolored Poisson reference keeps the original Haar-window
point law and the rate theta times its actual volume, including theta zero. -/
def originalFinitePoissonInputLaw (q : ℕ) {S : ℝ} (hS : 0 < S) (θ : ℝ)
    (α : Measure ℝ) [IsProbabilityMeasure α] :
    Measure (LocalFiniteMeasure ((Fin q → ℝ) × ℝ)) := by
  have originalFinitePoissonReferencePointProbability :=
    isProbabilityMeasure_originalFinitePoissonWindowPointLaw q hS
  exact (blockDataLaw
    ((normalizedFiniteLaw
      ((volume : Measure (Fin q → ℝ)).restrict (haarRootCube (Fin q) S))).prod α)
    (fun n ↦ poissonMeasure
      (θ.toNNReal * (volume (haarRootCube (Fin q) S)).toNNReal) {n})).map
    (originalFinitePoissonBlockLocal (0 : (Fin q → ℝ) × ℝ))

/-- The actual finite Poisson reference is a probability, even at zero rate. -/
theorem isProbabilityMeasure_originalFinitePoissonInputLaw
    (q : ℕ) {S : ℝ} (hS : 0 < S) (θ : ℝ)
    (α : Measure ℝ) [IsProbabilityMeasure α] :
    IsProbabilityMeasure (originalFinitePoissonInputLaw q hS θ α) := by
  have originalFinitePoissonWindowPointProbability :=
    isProbabilityMeasure_originalFinitePoissonWindowPointLaw q hS
  have originalFinitePoissonBlockProbability :=
    isProbabilityMeasure_originalPoissonBlockDataLaw
      ((normalizedFiniteLaw
        ((volume : Measure (Fin q → ℝ)).restrict (haarRootCube (Fin q) S))).prod α)
      (θ.toNNReal * (volume (haarRootCube (Fin q) S)).toNNReal)
  unfold originalFinitePoissonInputLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_originalFinitePoissonBlockLocal (0 : (Fin q → ℝ) × ℝ)).aemeasurable

/-- Positive-dimensional spatial Haar law makes every actual Poisson tuple
injective. Its unchanged finite measure is therefore simple almost surely. -/
theorem ae_simple_originalFinitePoissonInputLaw
    (q : ℕ) (hq : 0 < q) {S : ℝ} (hS : 0 < S) (θ : ℝ)
    (α : Measure ℝ) [IsProbabilityMeasure α] :
    ∀ᵐ μ ∂originalFinitePoissonInputLaw q hS θ α,
      IsLegalSimpleCountingMeasure (0 : (Fin q → ℝ) × ℝ) μ := by
  let originalFinitePoissonDimension : NeZero q := ⟨hq.ne'⟩
  let μ := (volume : Measure (Fin q → ℝ)).restrict (haarRootCube (Fin q) S)
  let ν := normalizedFiniteLaw μ
  have originalFinitePoissonPointProbability : IsProbabilityMeasure ν :=
    isProbabilityMeasure_originalFinitePoissonWindowPointLaw q hS
  have originalFinitePoissonSpatialAtomless : NullSingletonClass μ := by
    dsimp only [μ]
    infer_instance
  have originalFinitePoissonNormalizedAtomless : NullSingletonClass ν := by
    constructor
    intro x
    change (((μ.real univ)⁻¹.toNNReal : ℝ≥0) • μ) {x} = 0
    rw [Measure.smul_apply, measure_singleton, smul_zero]
  unfold originalFinitePoissonInputLaw
  apply (ae_map_iff
    (measurable_originalFinitePoissonBlockLocal (0 : (Fin q → ℝ) × ℝ)).aemeasurable
    (measurableSet_isLegalSimpleCountingMeasure (0 : (Fin q → ℝ) × ℝ))).mpr
  filter_upwards [ae_injective_legalBlockDataLaw (ν.prod α)
    (fun n ↦ poissonMeasure (θ.toNNReal *
      (volume (haarRootCube (Fin q) S)).toNNReal) {n})] with b hb
  have hs := isLegalSimpleCountingMeasure_of_injective_tuple
    (0 : (Fin q → ℝ) × ℝ) b.2 hb
  convert hs using 1
  apply Subtype.ext
  exact coe_originalFinitePoissonBlockLocal _ _

/-- The finite reference has exactly the physical compact Laplace exponent
at arbitrary nonnegative intensity, including zero, for tests inside its cube. -/
theorem integral_originalFinitePoissonInputLaw_laplace_eq
    (q : ℕ) {S : ℝ} (hS : 0 < S) (θ : ℝ) (hθ : 0 ≤ θ)
    (α : Measure ℝ) [IsProbabilityMeasure α]
    (F : LegalNonnegativeInputTest ((Fin q → ℝ) × ℝ))
    (hzero : ∀ x, x.1 ∉ haarRootCube (Fin q) S → F.1 x = 0) :
    (∫ μ, legalInputMeasureLaplace F μ ∂originalFinitePoissonInputLaw q hS θ α) =
      Real.exp (-(θ * ∫ x, (1 - Real.exp (-F.1 x))
        ∂(volume : Measure (Fin q → ℝ)).prod α)) := by
  let U := haarRootCube (Fin q) S
  let ν := normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict U)
  have originalFinitePoissonLaplacePointProbability : IsProbabilityMeasure ν :=
    isProbabilityMeasure_originalFinitePoissonWindowPointLaw q hS
  have hfin : volume U ≠ ⊤ := isCompact_Icc.measure_ne_top
  have hpos : volume U ≠ 0 := by
    dsimp only [U]
    rw [volume_haarRootCube (Fin q) hS.le, Fintype.card_fin]
    exact (ENNReal.ofReal_pos.mpr (pow_pos (by positivity : 0 < 2 * S) q)).ne'
  have hFm : Measurable (fun x ↦ F.1 x) := F.1.continuous.measurable
  have hscale : (((volume U).toNNReal : ℝ≥0) : ℝ) *
      ((∫ x, Real.exp (-F.1 x) ∂ν.prod α) - 1) =
        ∫ x, (Real.exp (-F.1 x) - 1)
          ∂((volume : Measure (Fin q → ℝ)).restrict U).prod α := by
    have hI : Integrable (fun x ↦ Real.exp (-F.1 x)) (ν.prod α) := by
      apply (integrable_const (1 : ℝ)).mono' hFm.neg.exp.aestronglyMeasurable
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
      exact neg_nonpos.mpr (F.2 x)
    rw [← physicalIntensity_smul_normalized_window q hfin hpos α, integral_smul_measure,
      integral_sub hI (integrable_const (1 : ℝ)), integral_const]
    simp only [probReal_univ, smul_eq_mul, mul_one]
    rfl
  have hglobal : (∫ x, (Real.exp (-F.1 x) - 1)
      ∂((volume : Measure (Fin q → ℝ)).restrict U).prod α) =
      ∫ x, (Real.exp (-F.1 x) - 1) ∂(volume : Measure (Fin q → ℝ)).prod α := by
    rw [Measure.restrict_prod_eq_prod_univ]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hxU : x.1 ∉ U := fun hmem ↦ hx ⟨hmem, mem_univ _⟩
    simp only [hzero x hxU, neg_zero, Real.exp_zero, sub_self]
  have hneg : (∫ x, (Real.exp (-F.1 x) - 1)
      ∂(volume : Measure (Fin q → ℝ)).prod α) =
      -(∫ x, (1 - Real.exp (-F.1 x)) ∂(volume : Measure (Fin q → ℝ)).prod α) := by
    rw [← integral_neg]
    congr 1
    funext x
    ring
  unfold originalFinitePoissonInputLaw
  rw [integral_map
    (measurable_originalFinitePoissonBlockLocal (0 : (Fin q → ℝ) × ℝ)).aemeasurable
    (legalInputMeasureLaplace F).continuous.measurable.aestronglyMeasurable]
  change (∫ b, Real.exp (-LocalFiniteMeasure.testIntegral
    (originalFinitePoissonBlockLocal (0 : (Fin q → ℝ) × ℝ) b) F.1)
    ∂blockDataLaw (ν.prod α)
      (fun n ↦ poissonMeasure (θ.toNNReal * (volume U).toNNReal) {n})) = _
  simp_rw [testIntegral_originalFinitePoissonBlockLocal]
  rw [integral_exp_neg_legalInputBlockTest_eq (ν.prod α)
    (θ.toNNReal * (volume U).toNNReal) hFm F.2]
  apply congrArg Real.exp
  rw [NNReal.coe_mul, Real.coe_toNNReal θ hθ, mul_assoc, hscale, hglobal, hneg]
  ring

end OTSelector.Reconstruction



