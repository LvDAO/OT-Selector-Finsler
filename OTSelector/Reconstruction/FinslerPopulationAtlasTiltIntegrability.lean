import OTSelector.Reconstruction.OriginalNormalizedPressureLipschitz

/-! Full-atlas integrability at every physical tilt is reduced to the true
zero-tilt pressure. The exact population normalization keeps one probe norm. -/
open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
  (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)

/-- The original physical probe Lipschitz constant is unchanged by the actual
population density normalization, including zero density. -/
theorem populationAtlasIntegrand_lipschitz
    (I : Z → ℝ → ℝ) (j : ℕ) {q : ℝ} (hq : 0 < q) {G : ℝ≥0}
    {z : Z} (hI : LipschitzWith G (I z)) :
    LipschitzWith G (fun t ↦ populationAtlasIntegrand P a κ lambda I j q t z) :=
  lipschitz_normalized_pressure (populationAtlasTheta_nonneg P a κ lambda j z) hq hI

/-- Genuine original zero-tilt integrability supplies every signed tilted
pressure on the same root set. The only measurability premise concerns that
actual tilted pressure; no upper or lower density bound is needed. -/
theorem integrableOn_populationAtlasIntegrand_of_zero
    [IsFiniteMeasure lambda] (I : Z → ℝ → ℝ) (j : ℕ) {q t : ℝ} (hq : 0 < q)
    {K : Set Z} {G : ℝ≥0}
    (hI : ∀ᵐ z ∂lambda.restrict K, LipschitzWith G (I z))
    (hzero : IntegrableOn (populationAtlasIntegrand P a κ lambda I j q 0) K lambda)
    (hread : AEStronglyMeasurable
      (populationAtlasIntegrand P a κ lambda I j q t) (lambda.restrict K)) :
    IntegrableOn (populationAtlasIntegrand P a κ lambda I j q t) K lambda ∧
      (∫ z in K, |populationAtlasIntegrand P a κ lambda I j q t z| ∂lambda) ≤
        (∫ z in K, |populationAtlasIntegrand P a κ lambda I j q 0 z| ∂lambda) +
          |t| * (G : ℝ) * lambda.real K := by
  let f := fun t z ↦ populationAtlasIntegrand P a κ lambda I j q t z
  have hpoint : ∀ᵐ z ∂lambda.restrict K, |f t z| ≤ |f 0 z| + |t| * (G : ℝ) := by
    filter_upwards [hI] with z hz
    have h := (populationAtlasIntegrand_lipschitz P a κ lambda I j hq hz).dist_le_mul t 0
    simp only [Real.dist_eq,sub_zero] at h
    have htri := abs_add_le (f t z-f 0 z) (f 0 z)
    dsimp only [f] at htri ⊢
    rw [sub_add_cancel] at htri
    linarith only [h,htri]
  have hboundI : Integrable (fun z ↦ |f 0 z| + |t| * (G : ℝ)) (lambda.restrict K) :=
    hzero.abs.add (integrable_const _)
  have hi : Integrable (f t) (lambda.restrict K) :=
    hboundI.mono' hread (hpoint.mono (fun _ h ↦ by simpa only [Real.norm_eq_abs] using h))
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ z in K, |f 0 z| + |t| * (G : ℝ) ∂lambda :=
      integral_mono_ae hi.abs hboundI hpoint
    _ = _ := by
      rw [integral_add hzero.abs (integrable_const _),integral_const]
      simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul]
      ring

/-- The actual normalized pressure difference has an integrated bound using
only original root mass. -/
theorem abs_integral_populationAtlasIntegrand_sub_le
    [IsFiniteMeasure lambda] (I : Z → ℝ → ℝ) (j : ℕ) {q t s : ℝ} (hq : 0 < q)
    {K : Set Z} {G : ℝ≥0}
    (hI : ∀ᵐ z ∂lambda.restrict K, LipschitzWith G (I z))
    (ht : IntegrableOn (populationAtlasIntegrand P a κ lambda I j q t) K lambda)
    (hs : IntegrableOn (populationAtlasIntegrand P a κ lambda I j q s) K lambda) :
    |(∫ z in K, populationAtlasIntegrand P a κ lambda I j q t z ∂lambda) -
      (∫ z in K, populationAtlasIntegrand P a κ lambda I j q s z ∂lambda)| ≤
        |t-s| * (G : ℝ) * lambda.real K := by
  rw [← integral_sub ht hs]
  have hbound : ∀ᵐ z ∂lambda.restrict K,
      ‖populationAtlasIntegrand P a κ lambda I j q t z -
        populationAtlasIntegrand P a κ lambda I j q s z‖ ≤ |t-s| * (G : ℝ) := by
    filter_upwards [hI] with z hz
    have h := (populationAtlasIntegrand_lipschitz P a κ lambda I j hq hz).dist_le_mul t s
    simpa only [Real.dist_eq,Real.norm_eq_abs,mul_comm] using h
  have h := norm_integral_le_of_norm_le_const hbound
  simpa only [Real.norm_eq_abs,Measure.real,Measure.restrict_apply_univ] using h

end OTSelector.Reconstruction
