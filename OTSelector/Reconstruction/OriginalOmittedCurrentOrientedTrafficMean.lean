import OTSelector.Reconstruction.OriginalOmittedCurrentOrientedTrafficCanonicalEnergy

/-! Real measurable same-frame omitted energy and its actual subextensive expectation. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- A finite nested nonnegative spatial mean supplies an integrable actual real spatial
integral, and its real expectation is precisely the same nested nonnegative mean. -/
theorem integral_spatial_integral_eq_nested_lintegral_of_finite
    {P X : Type*} [MeasurableSpace P] [MeasurableSpace X]
    (σ : Measure P) (ρ : Measure X) [SFinite ρ]
    {f : P × X → ℝ} (hf : Measurable f) (hf0 : ∀ p x, 0 ≤ f (p,x))
    (hfinite : (∫⁻ p, ∫⁻ x, ENNReal.ofReal (f (p,x)) ∂ρ ∂σ) ≠ (∞ : ℝ≥0∞)) :
    Integrable (fun p ↦ ∫ x, f (p,x) ∂ρ) σ ∧
    (∫ p, ∫ x, f (p,x) ∂ρ ∂σ) =
      (∫⁻ p, ∫⁻ x, ENNReal.ofReal (f (p,x)) ∂ρ ∂σ).toReal := by
  have hs : ∀ᵐ p ∂σ, (∫⁻ x, ENNReal.ofReal (f (p,x)) ∂ρ) ≠ (∞ : ℝ≥0∞) :=
    (ae_lt_top (hf.ennreal_ofReal.lintegral_prod_right' (ν := ρ)) hfinite).mono fun _ h ↦ h.ne
  have he : (fun p ↦ ENNReal.ofReal (∫ x, f (p,x) ∂ρ)) =ᵐ[σ]
      fun p ↦ ∫⁻ x, ENNReal.ofReal (f (p,x)) ∂ρ := by
    filter_upwards [hs] with p hp
    have hi := (lintegral_ofReal_ne_top_iff_integrable
      (hf.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (Eventually.of_forall (hf0 p))).mp hp
    exact ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (hf0 p))
  have hE := (hf.stronglyMeasurable.integral_prod_right' (ν := ρ)).measurable
  have hnonneg : 0 ≤ᵐ[σ] (fun p ↦ ∫ x, f (p,x) ∂ρ) :=
    Eventually.of_forall (fun p ↦ integral_nonneg (hf0 p))
  have hmean := lintegral_congr_ae he
  refine ⟨(lintegral_ofReal_ne_top_iff_integrable hE.aestronglyMeasurable hnonneg).mp
    (by rw [hmean]; exact hfinite), ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnonneg hE.aestronglyMeasurable, hmean]

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The actual real Euclidean energy of full-minus-same-frame-retained original current. -/
def originalCanonicalOrientedOmittedCurrentLtwoEnergy (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) (R ell : ℝ) (A : Set ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) : ℝ :=
  ∫ z in originalCenteredPhysicalCubeRegion b (2 * R),
    ‖(EuclideanSpace.equiv (Fin (finrank ℝ S.covector.ker)) ℝ).symm
      (originalOrientedOmittedSeedPathClockSetCurrent S w b R ell
        (fun x ↦ originalEuclideanMollifier _ (x-z)) A scene)‖^2

/-- The real original same-frame omitted energy is a measurable random variable. -/
theorem measurable_originalCanonicalOrientedOmittedCurrentLtwoEnergy
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) (R ell : ℝ) (A : Set ℝ) :
    Measurable (originalCanonicalOrientedOmittedCurrentLtwoEnergy S w b R ell A) := by
  have hm := measurable_originalOrientedOmittedCurrent_joint_spatial S hF hw b R ell
    (contDiff_originalEuclideanMollifier _).continuous.measurable A
  have hv := ((EuclideanSpace.equiv (Fin (finrank ℝ S.covector.ker)) ℝ).symm.continuous.measurable.comp hm).norm.pow_const 2
  exact hv.stronglyMeasurable.integral_prod_right'.measurable

/-- Finite actual same-frame energy gives integrable real energy with the exact real mean. -/
theorem integral_originalCanonicalOrientedOmittedCurrentLtwoEnergy_eq_of_finite
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) (R ell : ℝ) (A : Set ℝ)
    (P : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))
    (hfinite : (∫⁻ scene, ∫⁻ z in originalCenteredPhysicalCubeRegion b (2 * R),
      ENNReal.ofReal (‖(EuclideanSpace.equiv (Fin (finrank ℝ S.covector.ker)) ℝ).symm
        (originalOrientedOmittedSeedPathClockSetCurrent S w b R ell
          (fun x ↦ originalEuclideanMollifier _ (x-z)) A scene)‖^2) ∂volume ∂P) ≠ (∞ : ℝ≥0∞)) :
    Integrable (originalCanonicalOrientedOmittedCurrentLtwoEnergy S w b R ell A) P ∧
    (∫ scene, originalCanonicalOrientedOmittedCurrentLtwoEnergy S w b R ell A scene ∂P) =
      (∫⁻ scene, ∫⁻ z in originalCenteredPhysicalCubeRegion b (2 * R),
        ENNReal.ofReal (‖(EuclideanSpace.equiv (Fin (finrank ℝ S.covector.ker)) ℝ).symm
          (originalOrientedOmittedSeedPathClockSetCurrent S w b R ell
            (fun x ↦ originalEuclideanMollifier _ (x-z)) A scene)‖^2) ∂volume ∂P).toReal := by
  apply integral_spatial_integral_eq_nested_lintegral_of_finite P
    (volume.restrict (originalCenteredPhysicalCubeRegion b (2 * R)))
    (f := fun p ↦ ‖(EuclideanSpace.equiv (Fin (finrank ℝ S.covector.ker)) ℝ).symm
      (originalOrientedOmittedSeedPathClockSetCurrent S w b R ell
        (fun x ↦ originalEuclideanMollifier _ (x-p.2)) A p.1)‖^2)
    ?_ (fun _ _ ↦ sq_nonneg _) hfinite
  exact ((EuclideanSpace.equiv (Fin (finrank ℝ S.covector.ker)) ℝ).symm.continuous.measurable.comp
    (measurable_originalOrientedOmittedCurrent_joint_spatial S hF hw b R ell
      (contDiff_originalEuclideanMollifier _).continuous.measurable A)).norm.pow_const 2

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
local notation "qdim" => finrank ℝ S.covector.ker

/-- Actual original minimization produces integrable real Euclidean omitted energy at
every scale and a vanishing mean per the same chosen physical cube volume. -/
theorem original_minimizer_canonical_oriented_omittedCurrentLtwoEnergy_mean_density_zero
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels) (hq : 2≤qdim)
    (b : OrthonormalBasis (Fin qdim) ℝ (EuclideanSpace ℝ (Fin qdim)))
    {densityμ densityν : M→ℝ} {v : M→E→ℝ} (cμ cν : ℝ≥0∞)
    (hρμ : Continuous densityμ) (hρμ0 : ∀x,0≤densityμ x)
    (hρν : Continuous densityν) (hρν0 : ∀x,0≤densityν x)
    (hv : ∀old,ContinuousOn (v old) (extChartAt 𝓘(ℝ,E) old).target)
    (hv0 : ∀old,∀y∈(extChartAt 𝓘(ℝ,E) old).target,0≤v old y)
    (hdensityμ : PopulationSeedClockDensity S w
      (μ.map (fun x : ℝ↦x-S.level)) densityμ v cμ.toReal)
    (hdensityν : PopulationSeedClockDensity S w
      (ν.map (fun x : ℝ↦x-S.level)) densityν v cν.toReal)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter) (hgap : 0<gap)
    {g : ℝ→ℝ→ℝ} {gBound : ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀x y,|g x y|≤gBound) (τ : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching qdim μ ν (D.originalFocalKinetic gap) g)
    (hmin : ∀P : LegalWeightedStationaryPoissonMatching qdim μ ν (D.originalFocalKinetic gap) g,
      Q.value τ≤P.value τ)
    {ell : ℝ → ℝ} (hell : ∀ᶠ R in atTop, 0 ≤ ell R)
    (hlarge : Tendsto ell atTop atTop)
    (hsmall : Tendsto (fun R ↦ ell R / R) atTop (𝓝 0)) (A : ℝ → Set ℝ) :
    (∀ R, Measurable (originalCanonicalOrientedOmittedCurrentLtwoEnergy S w b R (ell R) (A R)) ∧
      Integrable (originalCanonicalOrientedOmittedCurrentLtwoEnergy S w b R (ell R) (A R))
        (Q.law : Measure (LegalMarkedOptimalInputScene qdim))) ∧
    Tendsto (fun R : ℝ ↦
      (∫ scene, originalCanonicalOrientedOmittedCurrentLtwoEnergy S w b R (ell R) (A R) scene
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene qdim))) /
          volume.real (originalCenteredPhysicalCubeRegion b (2 * R))) atTop (𝓝 0) := by
  obtain ⟨hfinite, hlim⟩ := D.original_minimizer_canonical_oriented_omittedCurrent_euclidean_sq_density_zero
    hF hw hq b cμ cν hρμ hρμ0 hρν hρν0 hv hv0 hdensityμ hdensityν hbounds hgap
    hg hgb τ Q hmin hell hlarge hsmall A
  have heq (R : ℝ) := integral_originalCanonicalOrientedOmittedCurrentLtwoEnergy_eq_of_finite
    S hF hw b R (ell R) (A R) (Q.law : Measure (LegalMarkedOptimalInputScene qdim)) (hfinite R)
  refine ⟨fun R ↦ ⟨measurable_originalCanonicalOrientedOmittedCurrentLtwoEnergy S hF hw b R (ell R) (A R),
    (heq R).1⟩, ?_⟩
  convert hlim using 1
  funext R
  rw [(heq R).2]
  rfl

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
