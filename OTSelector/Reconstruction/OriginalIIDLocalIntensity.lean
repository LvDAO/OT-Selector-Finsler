import OTSelector.Reconstruction.FinslerCoefficientCoreFrozenLaw
import OTSelector.Reconstruction.FinslerOriginalCoordinateHaarPressure
import Mathlib.MeasureTheory.VectorMeasure.Integral
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.MeasureTheory.Covering.DensityTheorem

/-!
# Original iid local-intensity freezing estimates

Actual original cell laws identify their two clock-coordinate integrals. Bounded
Laplace tests are controlled by raw total variation; vanishing local oscillations
and bounded normalized window volume imply vanishing scaled freezing errors.
The exact full-reference Haar scaling retains the original coordinate intensity,
including its Haar basis factor. Density-point masks and the shrinking-cell
oscillation bounds must still be composed to obtain the original local limit.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ENNReal NNReal ContDiff BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Every bounded measurable real test is controlled by the full signed total
variation of two finite raw laws. No normalization of either law is used. -/
theorem original_abs_integral_sub_le_totalVariation
    {X : Type*} [MeasurableSpace X] (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : X → ℝ} (hf : Measurable f) (hb : ∀ x, |f x| ≤ 1) :
    |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤
      (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation.real univ := by
  have hμ : μ.toSignedMeasure.Integrable f := by
    change Integrable f μ.toSignedMeasure.variation
    rw [Measure.variation_toSignedMeasure]
    exact Integrable.of_bound hf.aestronglyMeasurable 1 (ae_of_all _ hb)
  have hν : ν.toSignedMeasure.Integrable f := by
    change Integrable f ν.toSignedMeasure.variation
    rw [Measure.variation_toSignedMeasure]
    exact Integrable.of_bound hf.aestronglyMeasurable 1 (ae_of_all _ hb)
  have : IsFiniteMeasure (μ.toSignedMeasure - ν.toSignedMeasure).variation := by
    rw [← SignedMeasure.totalVariation_eq_variation]
    infer_instance
  have h := VectorMeasure.norm_integral_le_of_norm_le_const
    (μ := μ.toSignedMeasure - ν.toSignedMeasure)
    (B := (ContinuousLinearMap.lsmul ℝ ℝ).flip)
    (f := f) (C := 1) (ae_of_all _ hb)
  rw [VectorMeasure.integral_sub_vectorMeasure hμ hν] at h
  simpa only [VectorMeasure.integral_toSignedMeasure, Real.norm_eq_abs,
    one_mul, ContinuousLinearMap.opNorm_flip, ContinuousLinearMap.opNorm_lsmul,
    SignedMeasure.totalVariation_eq_variation] using h

/-- A nonnegative Laplace test has defect between zero and one. -/
theorem original_laplace_defect_abs_le_one {X : Type*} {F : X → ℝ}
    (hF : ∀ x, 0 ≤ F x) (x : X) : |1 - Real.exp (-F x)| ≤ 1 := by
  have hpos : 0 < Real.exp (-F x) := Real.exp_pos _
  have hle : Real.exp (-F x) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hF x))
  rw [abs_of_nonneg (sub_nonneg.mpr hle)]
  linarith

/-- The moving compact Laplace test may depend on the microscopic scale. Its
uniform bound is one, independent of that scale or its support. -/
theorem original_abs_laplace_defect_sub_le_totalVariation
    {X : Type*} [MeasurableSpace X] (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {F : X → ℝ} (hF : Measurable F) (hF0 : ∀ x, 0 ≤ F x) :
    |(∫ x, 1 - Real.exp (-F x) ∂μ) - ∫ x, 1 - Real.exp (-F x) ∂ν| ≤
      (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation.real univ :=
  original_abs_integral_sub_le_totalVariation μ ν
    (measurable_const.sub hF.neg.exp) (original_laplace_defect_abs_le_one hF0)

/-- Quantitative freezing errors vanish after the ORIGINAL sample-size
normalization when the microscopic Haar window has uniformly bounded normalized
volume. The tests may vary arbitrarily with the scale, so this applies directly
to `1-exp(-F(s_n*(coord-z),clock))`. -/
theorem original_scaled_laplace_freezing_error_tendsto_zero
    {X : Type*} [MeasurableSpace X]
    (μ ν : ℕ → Measure X) [∀ n, IsFiniteMeasure (μ n)] [∀ n, IsFiniteMeasure (ν n)]
    (F : ℕ → X → ℝ) (hF : ∀ n, Measurable (F n)) (hF0 : ∀ n x, 0 ≤ F n x)
    {N mass ε : ℕ → ℝ} {C B : ℝ}
    (hN : ∀ n, 0 ≤ N n) (hC : 0 ≤ C)
    (hε : Tendsto ε atTop (𝓝 0))
    (hvolume : ∀ n, N n * mass n ≤ B)
    (hvariation : ∀ n,
      ((μ n).toSignedMeasure - (ν n).toSignedMeasure).totalVariation.real univ ≤
        C * |ε n| * mass n) :
    Tendsto (fun n ↦ N n *
      ((∫ x, 1 - Real.exp (-F n x) ∂μ n) - ∫ x, 1 - Real.exp (-F n x) ∂ν n))
      atTop (𝓝 0) := by
  apply squeeze_zero_norm (a := fun n ↦ C * B * |ε n|)
  · intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hN n)]
    calc
      _ ≤ N n * ((μ n).toSignedMeasure - (ν n).toSignedMeasure).totalVariation.real univ :=
        mul_le_mul_of_nonneg_left
          (original_abs_laplace_defect_sub_le_totalVariation (μ n) (ν n) (hF n) (hF0 n)) (hN n)
      _ ≤ N n * (C * |ε n| * mass n) :=
        mul_le_mul_of_nonneg_left (hvariation n) (hN n)
      _ = (C * |ε n|) * (N n * mass n) := by ring
      _ ≤ (C * |ε n|) * B :=
        mul_le_mul_of_nonneg_left (hvolume n) (mul_nonneg hC (abs_nonneg _))
      _ = _ := by ring
  · simpa using tendsto_const_nhds.mul hε.abs

/-- The same sample normalization cancels the actual native-Haar Jacobian in
the FULL frozen spatial-clock product. The population density and the Haar
basis factor remain multiplied together, and the original clock is unchanged. -/
theorem original_scale_pow_smul_map_frozen_haar_product
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {q : ℕ}
    (κ : Measure V) [κ.IsAddHaarMeasure] (e : V ≃L[ℝ] (Fin q → ℝ))
    {c : ℝ≥0∞} (hmap : κ.map e = c • (volume : Measure (Fin q → ℝ)))
    {scale : ℝ} (hscale : 0 < scale) (root : Fin q → ℝ)
    (α : Measure ℝ) [SFinite α] (ρ : ℝ≥0∞) :
    ENNReal.ofReal (scale ^ q) •
      (ρ • κ.prod α).map (fun p : V × ℝ ↦ (scale • e p.1 - root, p.2)) =
      ((ρ * c) • (volume : Measure (Fin q → ℝ))).prod α := by
  rw [Measure.map_smul,
    map_haar_product_scaled_seed_coordinate_sub κ e hmap hscale root α,
    Measure.prod_smul_left, smul_smul, smul_smul,
    ENNReal.ofReal_pow hscale.le]
  have hp0 : (ENNReal.ofReal scale) ^ q ≠ 0 :=
    pow_ne_zero _ (ENNReal.ofReal_pos.mpr hscale).ne'
  have hpfin : (ENNReal.ofReal scale) ^ q ≠ ⊤ := by finiteness
  rw [show (ENNReal.ofReal scale) ^ q * ρ * (c / (ENNReal.ofReal scale) ^ q) =
      ρ * c by
    rw [mul_comm ((ENNReal.ofReal scale) ^ q) ρ, mul_assoc,
      ENNReal.mul_div_cancel hp0 hpfin],
    Measure.prod_smul_left]

/-- Exact frozen Laplace defect at the genuine microscopic normalization.
This remains valid for any measurable nonnegative compact test; support and
nonnegativity are only needed later for finiteness and the moving-test bound. -/
theorem original_scale_pow_mul_frozen_haar_laplace_defect
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {q : ℕ}
    (κ : Measure V) [κ.IsAddHaarMeasure] (e : V ≃L[ℝ] (Fin q → ℝ))
    {c : ℝ≥0∞} (hmap : κ.map e = c • (volume : Measure (Fin q → ℝ)))
    {scale : ℝ} (hscale : 0 < scale) (root : Fin q → ℝ)
    (α : Measure ℝ) [SFinite α] (ρ : ℝ≥0∞)
    (H : (Fin q → ℝ) × ℝ → ℝ) (hH : Measurable H) :
    scale ^ q * (∫ p : V × ℝ, 1 - Real.exp (-H (scale • e p.1 - root, p.2))
        ∂(ρ • κ.prod α)) =
      (ρ * c).toReal * ∫ p, 1 - Real.exp (-H p)
        ∂((volume : Measure (Fin q → ℝ)).prod α) := by
  have hm := original_scale_pow_smul_map_frozen_haar_product
    κ e hmap hscale root α ρ
  have he := congrArg (fun μ ↦ ∫ p, 1 - Real.exp (-H p) ∂μ) hm
  have hobs : Measurable (fun p : V × ℝ ↦ (scale • e p.1 - root, p.2)) := by fun_prop
  rw [integral_smul_measure, integral_map (f := fun p ↦ 1 - Real.exp (-H p))
    hobs.aemeasurable (measurable_const.sub hH.neg.exp).aestronglyMeasurable,
    Measure.prod_smul_left] at he
  simpa only [integral_smul_measure, smul_eq_mul,
    ENNReal.toReal_ofReal (pow_nonneg hscale.le q)] using he

section ActualCore

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

/-- Both ORIGINAL iid colors, restricted by the same ROOT cell, have exactly
the corresponding raw Haar-clock Laplace defect. No target-partner mask or
conditional matching plan is inserted into either iid population law. -/
theorem PopulationLocalPressureCore.original_cell_laplace_defect_identities
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.haar.continuous.coefficient i).roots)
    (H : (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker × ℝ → ℝ)
    (hH : Measurable H) :
    let C := D.haar.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let R := populationSeedRootLabelValue S a
    let intensity := ((κ C.seedIndex).restrict (R '' L)).withDensity
      (populationSeedPieceHaarDensity P a κ lambda C.seedIndex)
    (∫ x, 1 - Real.exp (-H (R (a x), u x)) ∂η₀.restrict (a ⁻¹' L)) =
      ∫ x, 1 - Real.exp (-H x) ∂(intensity ⊗ₘ
        populationSeedCoordinateClockKernel S a ha (condDistrib u a η₀)) ∧
    (∫ x, 1 - Real.exp (-H (R (a x), u x)) ∂η₁.restrict (a ⁻¹' L)) =
      ∫ x, 1 - Real.exp (-H x) ∂(intensity ⊗ₘ
        populationSeedCoordinateClockKernel S a ha (condDistrib u a η₁)) := by
  dsimp only
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instBorel : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let S := (P C.seedIndex).seed
  let R := populationSeedRootLabelValue S a
  have hcoord : Measurable (fun x ↦ (R (a x), u x)) :=
    ((measurable_populationSeedRootLabelValue S hF hcomplete hu ha hinj).comp ha).prodMk
      hu.continuous.measurable
  have htest : Measurable (fun p ↦ 1 - Real.exp (-H p)) := measurable_const.sub hH.neg.exp
  obtain ⟨hsource, htarget⟩ := D.haar.cell_joint_laws hF hcomplete hu ha hinj i hL hsub
  constructor
  · rw [← hsource]
    exact (integral_map hcoord.aemeasurable htest.aestronglyMeasurable).symm
  · rw [← htarget]
    exact (integral_map hcoord.aemeasurable htest.aestronglyMeasurable).symm

omit [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)] in
/-- In the actual original finite seed basis the frozen microscopic intensity
is exactly `originalSeedCoordinateIntensity`, including the genuine Haar basis
factor. This is the full-space frozen reference used after density-point masks
have been removed, not a constant-density assertion about the population. -/
theorem original_seed_scale_pow_mul_frozen_laplace_defect
    [∀ j, (κ j).IsAddHaarMeasure]
    (j : ℕ) (z : ℚ → M) {scale : ℝ} (hscale : 0 < scale)
    (α : Measure ℝ) [SFinite α]
    (H : (Fin (Module.finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ → ℝ)
    (hH : Measurable H) :
    let S := (P j).seed
    let e := (Module.finBasis ℝ S.covector.ker).equivFunL
    let center := e (populationSeedRootLabelValue S a z)
    scale ^ Module.finrank ℝ S.covector.ker *
      (∫ p : S.covector.ker × ℝ,
        1 - Real.exp (-H (scale • e p.1 - scale • center, p.2))
        ∂(ENNReal.ofReal (populationAtlasTheta P a κ lambda j z) • (κ j).prod α)) =
      originalSeedCoordinateIntensity P a κ lambda j z *
        ∫ p, 1 - Real.exp (-H p) ∂((volume : Measure
          (Fin (Module.finrank ℝ S.covector.ker) → ℝ)).prod α) := by
  dsimp only
  have hθ := populationAtlasTheta_nonneg P a κ lambda j z
  have he := original_scale_pow_mul_frozen_haar_laplace_defect (κ j)
    (Module.finBasis ℝ (P j).seed.covector.ker).equivFunL
    (map_originalSeedHaar_eq_coordinate_volume (P j).seed (κ j)) hscale
    (scale • (Module.finBasis ℝ (P j).seed.covector.ker).equivFunL
      (populationSeedRootLabelValue (P j).seed a z)) α
    (ENNReal.ofReal (populationAtlasTheta P a κ lambda j z)) H hH
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hθ, ENNReal.coe_toReal,
    originalSeedCoordinateIntensity, mul_comm (populationAtlasTheta P a κ lambda j z)] using he

/-- The actual original two-color raw cell laws have the required quantitative
Laplace-defect freezing bound. Only original density/conditional-law oscillations
are hypotheses; no Poisson or iid convergence is assumed. -/
theorem PopulationLocalPressureCore.original_cell_laplace_defect_freezing_le
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.haar.continuous.coefficient i).roots)
    {z₀ : ℚ → M} (hz₀ : z₀ ∈ (D.haar.continuous.coefficient i).roots)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hclose : ∀ z ∈ L, |D.rootIntensity i z - D.rootIntensity i z₀| ≤
      ε * D.rootIntensity i z₀)
    (hmark : ∀ z ∈ L, ∀ color : Fin 2,
      ((populationTwoColorClockKernel u a η₀ η₁ color z).toSignedMeasure -
        (populationTwoColorClockKernel u a η₀ η₁ color z₀).toSignedMeasure).totalVariation
          univ ≤ ENNReal.ofReal ε)
    (H : (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker × ℝ → ℝ)
    (hH : Measurable H) (hH0 : ∀ x, 0 ≤ H x) :
    let C := D.haar.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let R := populationSeedRootLabelValue S a
    let spatial := (κ C.seedIndex).restrict (R '' L)
    let density := populationSeedPieceHaarDensity P a κ lambda C.seedIndex
    ∀ color : Fin 2,
      |(∫ x, 1 - Real.exp (-H x) ∂(spatial.withDensity density ⊗ₘ
          populationSeedCoordinateClockKernel S a ha
            (populationTwoColorClockKernel u a η₀ η₁ color))) -
        (∫ x, 1 - Real.exp (-H x) ∂((D.rootIntensity i z₀).toNNReal •
          spatial.prod (populationTwoColorClockKernel u a η₀ η₁ color z₀)))| ≤
        (2 * ε * D.rootIntensity i z₀) * (κ C.seedIndex).real (R '' L) := by
  dsimp only
  let C := D.haar.continuous.coefficient i
  let S := (P C.seedIndex).seed
  let R := populationSeedRootLabelValue S a
  let spatial := (κ C.seedIndex).restrict (R '' L)
  let density := populationSeedPieceHaarDensity P a κ lambda C.seedIndex
  have _instSpatial := D.cell_haar_finite hF hcomplete hu ha hinj i hL hsub
  have _instIntensity := D.cell_intensity_finite hF hcomplete hu ha hinj i hL hsub
  have hρ : 0 ≤ D.rootIntensity i z₀ := ENNReal.toReal_nonneg
  intro color
  let actual := spatial.withDensity density ⊗ₘ populationSeedCoordinateClockKernel S a ha
    (populationTwoColorClockKernel u a η₀ η₁ color)
  let frozen := (D.rootIntensity i z₀).toNNReal •
    spatial.prod (populationTwoColorClockKernel u a η₀ η₁ color z₀)
  have htv := D.frozen_cell_totalVariation_le hF hcomplete hu ha hinj i hL hsub hz₀
    hε hclose hmark color
  have hb := original_abs_laplace_defect_sub_le_totalVariation actual frozen hH hH0
  apply hb.trans
  have hfinite : (κ C.seedIndex) (R '' L) ≠ ⊤ := by
    simpa only [spatial, Measure.restrict_apply_univ] using measure_ne_top spatial univ
  have hnon : 0 ≤ 2 * ε * D.rootIntensity i z₀ := by positivity
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite) htv
  simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_ofReal hnon] using hreal

end ActualCore

end OTSelector.Reconstruction

