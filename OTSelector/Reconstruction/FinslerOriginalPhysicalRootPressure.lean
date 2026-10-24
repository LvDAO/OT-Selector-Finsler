import OTSelector.MeasureTheory.Integral.DisjointPieceGluing
import OTSelector.Reconstruction.FinslerOriginalCoordinateHaarPressure

/-! The actual physical general Finsler pressure on the original root law.
Both the native-Haar population weight and actual coordinate Jacobian are exact. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The canonical physical pressure on the unchanged original population root.
Its native-Haar unit pressure contains the exact positive coordinate Jacobian,
so its actual standard-coordinate intensity is Theta=cHaar*theta. Elsewhere zero. -/
def originalPhysicalFinslerRootPressure (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) [∀ j, (κ j).IsAddHaarMeasure]
    (lambda : Measure Z)
    (η₀ η₁ : Measure M) [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    (b : Z × ℝ → M) (f : M × M →ᵇ ℝ) (t : ℝ) : Z → ℝ :=
  disjointRootPressure (populationSeedRootPiece P a κ lambda)
    (fun j ↦ populationAtlasIntegrand P a κ lambda
      (originalSeedHaarPressure (P j).seed a (κ j) η₀ η₁ b f) j
      ((finrank ℝ E - 1 : ℕ) : ℝ) t)

variable {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} [∀ j, (κ j).IsAddHaarMeasure]
  {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {b : Z × ℝ → M} (f : M × M →ᵇ ℝ)

/-- Each original selected seed piece reads exactly its own canonical pressure
from the single original root function, with the correct population weight. -/
theorem originalPhysicalFinslerRootPressure_eq_on_piece (j : ℕ) (t : ℝ) {z : Z}
    (hz : z ∈ populationSeedRootPiece P a κ lambda j) :
    originalPhysicalFinslerRootPressure P a κ lambda η₀ η₁ b f t z =
      populationAtlasIntegrand P a κ lambda
        (originalSeedHaarPressure (P j).seed a (κ j) η₀ η₁ b f) j
        ((finrank ℝ E - 1 : ℕ) : ℝ) t z :=
  disjointRootPressure_eq_on_piece _ (pairwiseDisjoint_populationSeedRootPiece P a κ lambda) _ j hz

/-- At each selected original root, the final physical pressure has the
exact same Theta=cHaar*theta coordinate intensity as the original iid cube factory. -/
theorem originalPhysicalFinslerRootPressure_eq_coordinate_on_piece
    (j : ℕ) (t : ℝ) {z : Z} (hz : z ∈ populationSeedRootPiece P a κ lambda j) :
    originalPhysicalFinslerRootPressure P a κ lambda η₀ η₁ b f t z =
      originalSeedCoordinateIntensity P a κ lambda j z ^
        (-2 / (((finrank ℝ E - 1 : ℕ) : ℝ))) *
        originalSeedRootPressure (P j).seed a η₀ η₁ b f z
          (t * originalSeedCoordinateIntensity P a κ lambda j z ^
            (2 / (((finrank ℝ E - 1 : ℕ) : ℝ)))) := by
  have hdimj : (finrank ℝ (P j).seed.covector.ker : ℝ) =
      ((finrank ℝ E - 1 : ℕ) : ℝ) := by
    have h := (P j).seed.normalization.toLinearEquiv.finrank_eq
    simp only [Module.finrank_prod,Module.finrank_self] at h
    exact_mod_cast (show finrank ℝ (P j).seed.covector.ker = finrank ℝ E - 1 by omega)
  rw [originalPhysicalFinslerRootPressure_eq_on_piece f j t hz]
  simpa only [hdimj] using populationAtlasIntegrand_originalSeedHaarPressure_eq_coordinate
    P a κ lambda η₀ η₁ b f j t z

variable (hlaw : PopulationSeedPieceMomentLaw P a κ lambda η₀ η₁)
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
  (hdim : 6 ≤ finrank ℝ E)
  {gap diameter : ℝ} (hgap : 0 < gap)
  (hsep : PopulationConditionalSeparationLaw u a lambda η₀ η₁ gap diameter)
  (γ : Kernel Z (ℝ × ℝ)) [IsMarkovKernel γ]
  (hγ : ∀ᵐ z ∂lambda, Vlasov.IsCoupling (γ z)
    (condDistrib u a η₀ z) (condDistrib u a η₁ z) ∧ ∀ᵐ p ∂γ z, p.1 ≤ p.2)
  (hb : Measurable b)

include hlaw hF hcomplete hu ha hinj hdim hgap hsep γ hγ hb

/-- The canonical single actual root pressure is AE strongly measurable at
every physical tilt, and its zero-tilt value is nonnegative almost everywhere.
Every pressure/normalization/measurability assertion comes from original data. -/
theorem originalPhysicalFinslerRootPressure_measurable_nonneg (t : ℝ) :
    AEStronglyMeasurable (originalPhysicalFinslerRootPressure P a κ lambda η₀ η₁ b f t) lambda ∧
      ∀ᵐ z ∂lambda, 0 ≤ originalPhysicalFinslerRootPressure P a κ lambda η₀ η₁ b f 0 z := by
  have hdimj (j : ℕ) : (finrank ℝ (P j).seed.covector.ker : ℝ) =
      ((finrank ℝ E - 1 : ℕ) : ℝ) := by
    have h := (P j).seed.normalization.toLinearEquiv.finrank_eq
    simp only [Module.finrank_prod,Module.finrank_self] at h
    exact_mod_cast (show finrank ℝ (P j).seed.covector.ker = finrank ℝ E - 1 by omega)
  have hdata (j : ℕ) (s : ℝ) :
      AEStronglyMeasurable (populationAtlasIntegrand P a κ lambda
        (originalSeedHaarPressure (P j).seed a (κ j) η₀ η₁ b f) j
        ((finrank ℝ E - 1 : ℕ) : ℝ) s)
        (lambda.restrict (populationSeedRootPiece P a κ lambda j)) ∧
      ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece P a κ lambda j),
        LipschitzWith ‖f‖₊ (fun v ↦ populationAtlasIntegrand P a κ lambda
          (originalSeedHaarPressure (P j).seed a (κ j) η₀ η₁ b f) j
          ((finrank ℝ E - 1 : ℕ) : ℝ) v z) ∧
        -(|s| * ‖f‖) ≤ populationAtlasIntegrand P a κ lambda
          (originalSeedHaarPressure (P j).seed a (κ j) η₀ η₁ b f) j
          ((finrank ℝ E - 1 : ℕ) : ℝ) s z := by
    simpa only [hdimj] using actual_originalHaarPressure_normalized_measurable_lower
      hlaw hF hcomplete hu ha hinj hdim hgap hsep γ hγ hb f j s
  refine ⟨aestronglyMeasurable_disjointRootPressure lambda _
    (fun j ↦ measurableSet_populationSeedRootPiece P a κ lambda hF hcomplete hu ha hinj j)
    (pairwiseDisjoint_populationSeedRootPiece P a κ lambda) _ (fun j ↦ (hdata j t).1),?_⟩
  apply ae_nonneg_disjointRootPressure
  · exact pairwiseDisjoint_populationSeedRootPiece P a κ lambda
  · intro j
    filter_upwards [(hdata j 0).2] with z hz
    simpa only [abs_zero,zero_mul,neg_zero] using hz.2

/-- The common physical probe Lipschitz constant holds on one original
conull root set for every pair of real tilt parameters simultaneously. -/
theorem ae_lipschitz_originalPhysicalFinslerRootPressure :
    ∀ᵐ z ∂lambda,
      LipschitzWith ‖f‖₊ (fun t ↦ originalPhysicalFinslerRootPressure P a κ lambda η₀ η₁ b f t z) := by
  have hlipPiece (j : ℕ) : ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece P a κ lambda j),
      LipschitzWith ‖f‖₊ (fun t ↦ populationAtlasIntegrand P a κ lambda
        (originalSeedHaarPressure (P j).seed a (κ j) η₀ η₁ b f) j
        ((finrank ℝ E - 1 : ℕ) : ℝ) t z) := by
    have hdimj : (finrank ℝ (P j).seed.covector.ker : ℝ) =
        ((finrank ℝ E - 1 : ℕ) : ℝ) := by
      have h := (P j).seed.normalization.toLinearEquiv.finrank_eq
      simp only [Module.finrank_prod,Module.finrank_self] at h
      exact_mod_cast (show finrank ℝ (P j).seed.covector.ker = finrank ℝ E - 1 by omega)
    have h := (actual_originalHaarPressure_normalized_measurable_lower
      hlaw hF hcomplete hu ha hinj hdim hgap hsep γ hγ hb f j 0).2.mono (fun _ hz ↦ hz.1)
    simpa only [hdimj] using h
  filter_upwards [ae_all_iff.mpr (fun j ↦ ae_imp_of_ae_restrict (hlipPiece j))] with z hz
  by_cases hactive : ∃ j, z ∈ populationSeedRootPiece P a κ lambda j
  · obtain ⟨j,hj⟩ := hactive
    apply LipschitzWith.of_dist_le_mul
    intro t s
    rw [originalPhysicalFinslerRootPressure_eq_on_piece f j t hj,
      originalPhysicalFinslerRootPressure_eq_on_piece f j s hj]
    exact (hz j hj).dist_le_mul t s
  · have hzero t : originalPhysicalFinslerRootPressure P a κ lambda η₀ η₁ b f t z = 0 :=
      disjointRootPressure_eq_zero_of_notMem _ _
        (by simpa only [mem_iUnion,not_exists] using hactive)
    apply LipschitzWith.of_dist_le_mul
    intro t s
    rw [hzero t,hzero s,dist_self]
    exact mul_nonneg (NNReal.coe_nonneg _) dist_nonneg

omit hlaw hdim hgap hsep γ hγ hb in
/-- The integrable single actual original root pressure has exactly the paper's
countable original population atlas integral; uncovered roots contribute zero. -/
theorem integral_originalPhysicalFinslerRootPressure_eq_atlas (t : ℝ)
    (hi : Integrable (originalPhysicalFinslerRootPressure P a κ lambda η₀ η₁ b f t) lambda) :
    (∫ z, originalPhysicalFinslerRootPressure P a κ lambda η₀ η₁ b f t z ∂lambda) =
      populationAtlasPressure P a κ lambda
        (fun j ↦ originalSeedHaarPressure (P j).seed a (κ j) η₀ η₁ b f)
        ((finrank ℝ E - 1 : ℕ) : ℝ) t :=
  integral_disjointRootPressure_eq_tsum lambda _
    (fun j ↦ measurableSet_populationSeedRootPiece P a κ lambda hF hcomplete hu ha hinj j)
    (pairwiseDisjoint_populationSeedRootPiece P a κ lambda) _ hi

/-- True zero-tilt integrability alone supplies every signed original root
pressure and its actual integral budget. The nonnegative base and common
physical probe bound are produced from original geometry internally. -/
theorem integrable_originalPhysicalFinslerRootPressure_of_zero
    [IsFiniteMeasure lambda]
    (hp0 : Integrable (originalPhysicalFinslerRootPressure P a κ lambda η₀ η₁ b f 0) lambda)
    (t : ℝ) :
    Integrable (originalPhysicalFinslerRootPressure P a κ lambda η₀ η₁ b f t) lambda ∧
    |populationAtlasPressure P a κ lambda
      (fun j ↦ originalSeedHaarPressure (P j).seed a (κ j) η₀ η₁ b f)
      ((finrank ℝ E - 1 : ℕ) : ℝ) t| ≤
      (∫ z, originalPhysicalFinslerRootPressure P a κ lambda η₀ η₁ b f 0 z ∂lambda) +
        |t| * ‖f‖ * lambda.real univ := by
  have hread := originalPhysicalFinslerRootPressure_measurable_nonneg f
    hlaw hF hcomplete hu ha hinj hdim hgap hsep γ hγ hb t
  have hLip := ae_lipschitz_originalPhysicalFinslerRootPressure f
    hlaw hF hcomplete hu ha hinj hdim hgap hsep γ hγ hb
  let p := fun s ↦ originalPhysicalFinslerRootPressure P a κ lambda η₀ η₁ b f s
  have hpoint : ∀ᵐ z ∂lambda, |p t z| ≤ p 0 z + |t| * ‖f‖ := by
    filter_upwards [hread.2,hLip] with z hz0 hzLip
    have h := hzLip.dist_le_mul t 0
    simp only [Real.dist_eq,sub_zero] at h
    change |p t z - p 0 z| ≤ ‖f‖ * |t| at h
    have htri := abs_add_le (p t z - p 0 z) (p 0 z)
    rw [sub_add_cancel,abs_of_nonneg hz0] at htri
    nlinarith only [h,htri]
  have hmajor : Integrable (fun z ↦ p 0 z + |t| * ‖f‖) lambda :=
    hp0.add (integrable_const _)
  have hi : Integrable (p t) lambda := hmajor.mono' hread.1
    (hpoint.mono (fun _ h ↦ by simpa only [Real.norm_eq_abs] using h))
  refine ⟨hi,?_⟩
  rw [← integral_originalPhysicalFinslerRootPressure_eq_atlas f hF hcomplete hu ha hinj t hi]
  have hbound := (abs_integral_le_integral_abs : |∫ z, p t z ∂lambda| ≤ ∫ z, |p t z| ∂lambda).trans
    (integral_mono_ae hi.abs hmajor hpoint)
  have hpbase : Integrable (p 0) lambda := hp0
  have hconst : Integrable (fun _z : Z ↦ |t| * ‖f‖) lambda := integrable_const _
  rw [integral_add hpbase hconst,integral_const] at hbound
  simpa only [p,smul_eq_mul,mul_comm,mul_left_comm,mul_assoc] using hbound

end OTSelector.Reconstruction
