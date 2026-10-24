import OTSelector.Reconstruction.FinslerConcreteUpperClassPressure
import OTSelector.Reconstruction.MarkedStationaryValueLegalAffineBinomialFilling

/-!
The actual original finite class coefficient model has the sharp microscopic
shape comparison. Its literal pair-class law, original physical cost scale and
actual density-weighted count intensity are kept distinct throughout.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Matrix Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal Matrix.Norms.Operator BigOperators BoundedContinuousFunction Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

/-- Literal full-cube finite-class mean at original binomial counts. The count
parameter N,p and the kinetic intensity remain distinct. -/
def finiteClassBinomialMean {q : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (mask : A → B → Prop) (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β]
    (N : ℕ) (p : unitInterval) (intensity : ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ) (tilt : ℝ) : ℝ :=
  ∫ cloud, finiteClassLegalTilted q mask intensity kin probe tilt cloud
    ∂twoMarkedCountLaw q α β (ProbabilityTheory.binomial N p)

/-- Keep the original spatial shape in the unchanged full-box binomial
experiment and evaluate its true physical affine cost at sample size N. -/
def affineClassBinomialShapeExpectation {q : ℕ} {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (source : A → ℝ) (target : B → ℝ) (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β]
    (N : ℕ) (p : unitInterval) (side : ℝ≥0) (origin : Fin q → ℝ) (S : Set (Fin q → ℝ))
    (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ) (tilt : ℝ) : ℝ :=
  ∫ d : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B),
      unclampedBlockLegalTilted q source target N kin probe tilt
        (mapBlockData (affineMarkedPoint origin side) d.1)
        (mapBlockData (affineMarkedPoint origin side) d.2)
    ∂(binomialShapeBlockLaw q α N p S).prod (binomialShapeBlockLaw q β N p S)

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

/-- Actual coefficient data supply the arbitrary-shape binomial fill/delete
comparison. The original count law is retained at every finite sample size. -/
theorem OriginalPopulationCoefficientCore.exists_clockClass_affine_binomial_shape_comparison
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width)
    (z₀ : Z) (hz₀ : z₀ ∈ C.roots) (f : M × M →ᵇ ℝ)
    (P₀ : Fin Q.count → Fin Q.count → ℝ)
    (hP₀ : ∀ j k, 0 ≤ P₀ j k) (hmass : 0 < ∑ j, ∑ k, P₀ j k)
    (hq : 0 < Module.finrank ℝ (P C.seedIndex).seed.covector.ker) :
    let π := clockClassJointProbability P₀ hP₀ hmass
    let α := π.map measurable_fst.aemeasurable
    let β := π.map measurable_snd.aemeasurable
    let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
    ∃ (source target : Fin Q.count → ℝ) (rankBins : FiniteScalarBins
      (Icc (-((Q.count : ℝ) + 1)) 1) (1 / 2 : ℝ)) (K : ℝ),
      (∀ j k, C.clockClassAllowed Q j k ↔ source j < target k) ∧ 0 ≤ K ∧
      ∀ (N : ℕ) (p : unitInterval) (density side : ℝ≥0), 0 < density →
      ∀ (origin : Fin q → ℝ) (S : Set (Fin q → ℝ)), MeasurableSet S → ∀ tilt : ℝ,
      let intensity := (N : ℝ) * density * side ^ q
      let value := fun d : BlockData ((Fin q → ℝ) × Fin Q.count) × BlockData ((Fin q → ℝ) × Fin Q.count) ↦
        unclampedBlockLegalTilted q source target N (C.clockClassKinetic Q z₀)
          (C.clockClassProbe Q z₀ hz₀ f) tilt
          (mapBlockData (affineMarkedPoint origin side) d.1)
          (mapBlockData (affineMarkedPoint origin side) d.2)
      Integrable value ((binomialShapeBlockLaw q (α : Measure _) N p S).prod
        (binomialShapeBlockLaw q (β : Measure _) N p S)) ∧
      |affineClassBinomialShapeExpectation source target (α : Measure _) (β : Measure _)
          N p side origin S (C.clockClassKinetic Q z₀) (C.clockClassProbe Q z₀ hz₀ f) tilt -
        finiteClassBinomialMean (C.clockClassAllowed Q) (α : Measure _) (β : Measure _) N p intensity
          (C.densityClockClassKinetic Q z₀ density) (C.clockClassProbe Q z₀ hz₀ f) tilt| ≤
        (2 * ((N : ℝ) * (p : ℝ)) * ((cubeMeasure (Fin q) 1) Sᶜ).toReal) *
          (2 * ((rankBins.count : ℝ) + 1) *
            (intensity ^ (2 / (q : ℝ)) *
              (((density : ℝ) ^ (-(2 / (q : ℝ))) * K) * q) + |tilt| * ‖f‖)) := by
  classical
  let π := clockClassJointProbability P₀ hP₀ hmass
  let α := π.map measurable_fst.aemeasurable
  let β := π.map measurable_snd.aemeasurable
  let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
  obtain ⟨source, target, hcode, hsep, hsource, htarget⟩ := C.exists_clockClass_strict_clocks Q
  obtain ⟨rankBins⟩ := exists_finiteScalarBins (show IsCompact (Icc (-((Q.count : ℝ) + 1)) 1) from
    isCompact_Icc) (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨K, hK, hbound⟩ := C.exists_clockClassKinetic_bound Q z₀ hz₀
  refine ⟨source, target, rankBins, K, hcode, hK, ?_⟩
  intro N p density side hdensity origin S hS tilt
  have hk := C.measurable_clockClassKinetic Q z₀
  have hp := C.measurable_clockClassProbe Q z₀ hz₀ f
  have hhom : ∀ j k (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      C.clockClassKinetic Q z₀ j k (fun l ↦ c * v l) =
        c ^ 2 * C.clockClassKinetic Q z₀ j k v :=
    fun j k c _ v ↦ C.clockClassKinetic_homogeneous Q z₀ j k c v
  have result := rankBins.integrable_density_affine_binomialShapeLaw_compare
    (kin := C.clockClassKinetic Q z₀) (g := C.clockClassProbe Q z₀ hz₀ f)
    (by norm_num : (0 : ℝ) < 1 / 2) q hq (measurable_of_countable source) (measurable_of_countable target)
    (α : Measure _) (β : Measure _) N p (N : ℝ≥0) density side hdensity origin hS
    (Filter.Eventually.of_forall hsource)
    (Filter.Eventually.of_forall (fun ab ↦ hsep ab.1 ab.2)) hK (norm_nonneg f)
    hk hbound hhom hp (C.clockClassProbe_abs_le Q z₀ hz₀ f) tilt
  have hkinScaled : C.densityClockClassKinetic Q z₀ (density : ℝ) =
      (fun j k v ↦ (density : ℝ) ^ (-(2 / (q : ℝ))) * C.clockClassKinetic Q z₀ j k v) := by
    funext j k v
    simp only [OriginalPopulationCoefficientCore.densityClockClassKinetic, neg_div, q]
  have hfull : finiteClassBinomialMean (C.clockClassAllowed Q) (α : Measure _) (β : Measure _) N p
      ((N : ℝ) * density * side ^ q) (C.densityClockClassKinetic Q z₀ density)
      (C.clockClassProbe Q z₀ hz₀ f) tilt =
      ∫ cloud, legalMarkedTilted q source target ((N : ℝ) * density * side ^ q)
        (fun j k v ↦ (density : ℝ) ^ (-(2 / (q : ℝ))) * C.clockClassKinetic Q z₀ j k v)
        (C.clockClassProbe Q z₀ hz₀ f) tilt cloud
        ∂twoMarkedCountLaw q (α : Measure _) (β : Measure _) (ProbabilityTheory.binomial N p) := by
    unfold finiteClassBinomialMean
    rw [hkinScaled]
    exact integral_congr_ae (Filter.Eventually.of_forall
      (finiteClassLegalTilted_eq_clock q (C.clockClassAllowed Q) source target hcode _ _ _ _))
  dsimp only
  rw [hfull]
  simpa only [affineClassBinomialShapeExpectation, NNReal.coe_natCast] using result

/-- At fixed microscopic count scale, changing original binomial shape
families have vanishing normalized filling error uniformly on compact tilt
intervals. The literal class mask, P0 marginals and physical kernel remain fixed. -/
theorem OriginalPopulationCoefficientCore.exists_clockClass_binomial_filling_limit
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width)
    (z₀ : Z) (hz₀ : z₀ ∈ C.roots) (f : M × M →ᵇ ℝ)
    (P₀ : Fin Q.count → Fin Q.count → ℝ)
    (hP₀ : ∀ j k, 0 ≤ P₀ j k) (hmass : 0 < ∑ j, ∑ k, P₀ j k)
    (hq : 0 < Module.finrank ℝ (P C.seedIndex).seed.covector.ker) :
    let π := clockClassJointProbability P₀ hP₀ hmass
    let α := π.map measurable_fst.aemeasurable
    let β := π.map measurable_snd.aemeasurable
    let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
    ∃ source target : Fin Q.count → ℝ,
      (∀ j k, C.clockClassAllowed Q j k ↔ source j < target k) ∧
      ∀ (density countBound : ℝ≥0), 0 < density → ∀ T : ℝ, 0 ≤ T →
      ∀ (J : Type*) (cells : ℕ → Finset J) (p : ℕ → unitInterval) (side : ℕ → ℝ≥0),
      (∀ N, (p N : ℝ) ≤ (density : ℝ) * (side N : ℝ) ^ q) →
      (∀ N : ℕ, (N : ℝ≥0) * density * side N ^ q ≤ countBound) →
      ∀ (origin : ℕ → J → Fin q → ℝ) (S : ℕ → J → Set (Fin q → ℝ)),
      (∀ N j, j ∈ cells N → MeasurableSet (S N j)) →
      Tendsto (fun N ↦ (side N : ℝ) ^ q *
        ∑ j ∈ cells N, ((cubeMeasure (Fin q) 1) (S N j)ᶜ).toReal) atTop (𝓝 0) →
      TendstoUniformlyOn
        (fun N tilt ↦
          (∑ j ∈ cells N, affineClassBinomialShapeExpectation source target
            (α : Measure _) (β : Measure _) N (p N) (side N) (origin N j) (S N j)
            (C.clockClassKinetic Q z₀) (C.clockClassProbe Q z₀ hz₀ f) tilt) / N -
          ((cells N).card : ℝ) * finiteClassBinomialMean (C.clockClassAllowed Q)
            (α : Measure _) (β : Measure _) N (p N)
            ((N : ℝ) * density * (side N : ℝ) ^ q)
            (C.densityClockClassKinetic Q z₀ density) (C.clockClassProbe Q z₀ hz₀ f) tilt / N)
        (fun _ ↦ 0) atTop (Icc (-T) T) := by
  classical
  let π := clockClassJointProbability P₀ hP₀ hmass
  let α := π.map measurable_fst.aemeasurable
  let β := π.map measurable_snd.aemeasurable
  let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
  obtain ⟨source, target, bins, K, hcode, hK, hcompare⟩ :=
    C.exists_clockClass_affine_binomial_shape_comparison Q z₀ hz₀ f P₀ hP₀ hmass hq
  refine ⟨source, target, hcode, ?_⟩
  intro density countBound hdensity T hT J cells p side hp hcount origin S hS hfill
  let error := fun N tilt ↦
    (∑ j ∈ cells N, affineClassBinomialShapeExpectation source target
      (α : Measure _) (β : Measure _) N (p N) (side N) (origin N j) (S N j)
      (C.clockClassKinetic Q z₀) (C.clockClassProbe Q z₀ hz₀ f) tilt) / N -
    ((cells N).card : ℝ) * finiteClassBinomialMean (C.clockClassAllowed Q)
      (α : Measure _) (β : Measure _) N (p N) ((N : ℝ) * density * (side N : ℝ) ^ q)
      (C.densityClockClassKinetic Q z₀ density) (C.clockClassProbe Q z₀ hz₀ f) tilt / N
  let filling := fun N ↦ (side N : ℝ) ^ q *
    ∑ j ∈ cells N, ((cubeMeasure (Fin q) 1) (S N j)ᶜ).toReal
  let amplitude := bins.affineShapeFillingConstant q density countBound K ‖f‖ T
  have hbound : ∀ᶠ N in atTop, ∀ tilt ∈ Icc (-T) T,
      |error N tilt| ≤ amplitude * filling N := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    intro tilt htilt
    let intensity := (N : ℝ) * density * (side N : ℝ) ^ q
    let edge := 2 * ((bins.count : ℝ) + 1) *
      (intensity ^ (2 / (q : ℝ)) *
        (((density : ℝ) ^ (-(2 / (q : ℝ))) * K) * q) + |tilt| * ‖f‖)
    let model := finiteClassBinomialMean (C.clockClassAllowed Q) (α : Measure _) (β : Measure _)
      N (p N) intensity (C.densityClockClassKinetic Q z₀ density) (C.clockClassProbe Q z₀ hz₀ f) tilt
    have hedge : 0 ≤ edge := by dsimp [edge, intensity]; positivity
    let hole : J → ℝ := fun j ↦ ((cubeMeasure (Fin q) 1) (S N j)ᶜ).toReal
    let value : J → ℝ := fun j ↦ affineClassBinomialShapeExpectation source target
      (α : Measure _) (β : Measure _) N (p N) (side N) (origin N j) (S N j)
      (C.clockClassKinetic Q z₀) (C.clockClassProbe Q z₀ hz₀ f) tilt
    have hcell : ∀ j ∈ cells N,
        |value j - model| ≤ (2 * ((N : ℝ) * (p N : ℝ)) * hole j) * edge := by
      intro j hj
      exact (hcompare N (p N) density (side N) hdensity (origin N j) (S N j) (hS N j hj) tilt).2
    have hraw : |(∑ j ∈ cells N, value j) / N - (∑ _j ∈ cells N, model) / N| ≤
        (2 * (density : ℝ) * edge) * ((side N : ℝ) ^ q * ∑ j ∈ cells N, hole j) :=
      normalized_binomial_shape_sum_sub_le (J := J) (cells N) hN
        (p := (p N : ℝ)) (density := (density : ℝ)) (volume := (side N : ℝ) ^ q)
        (edge := edge) (hp N) hedge hole value (fun _ ↦ model)
        (fun _ _ ↦ ENNReal.toReal_nonneg) hcell
    have hconst : (∑ _j ∈ cells N, model) = ((cells N).card : ℝ) * model := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [hconst] at hraw
    change |error N tilt| ≤ (2 * (density : ℝ) * edge) * filling N at hraw
    have hi : 0 ≤ intensity := by dsimp [intensity]; positivity
    have hcountReal : intensity ≤ countBound := by exact_mod_cast hcount N
    have hcoeff : 2 * (density : ℝ) * edge ≤ amplitude :=
      bins.affine_shape_error_coefficient_le q density countBound hK (norm_nonneg f) hi
        hcountReal (abs_le.mpr htilt)
    have hfillNonneg : 0 ≤ filling N :=
      mul_nonneg (pow_nonneg (side N).coe_nonneg _)
        (Finset.sum_nonneg fun j _ ↦ ENNReal.toReal_nonneg)
    exact hraw.trans (mul_le_mul_of_nonneg_right hcoeff hfillNonneg)

  have result := tendstoUniformlyOn_binomial_shape_error_of_filling
    (error := error) (filling := filling) (K := amplitude) hfill hbound
  exact result

end OTSelector.Reconstruction
