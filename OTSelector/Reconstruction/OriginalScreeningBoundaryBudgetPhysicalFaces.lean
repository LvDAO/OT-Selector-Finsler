import OTSelector.Reconstruction.OriginalCubeTraceCompactnessPhysicalGradientBound

/-! Dimension-uniform actual physical face coefficients, retaining the same selected frame. -/
open Set Function Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology BigOperators InnerProductSpace Distributions
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability
local instance originalScreeningPhysicalFacesColorMetric : MetricSpace (Fin 2) :=
  TopologicalSpace.metrizableSpaceMetric (Fin 2)

/-- The actual full-current common physical face coefficient on a side-L cube.
Dimension zero has no faces; positive dimensions use the proved same-scene trace quantity. -/
def originalScreeningPhysicalFaceBudget {q : ℕ} {μ ν : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q μ ν kin g)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (j : LegalMarkedOptimalInputScene q → Fin q → ℝ)
    (hj : ∀ k, MemLp (fun scene ↦ j scene k) 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)))
    (L : ℝ) (scene : LegalMarkedOptimalInputScene q) : ℝ := by
  cases q with
  | zero => exact 0
  | succ r =>
    exact Q.scenePhysicalCubeTraceDualBound b
      (fun i ↦ originalLinearCurrentReadoutLtwo (Q.law : Measure _) j hj
        (originalEuclideanNormalReadout (b i))) L scene

/-- The actual true-normal signed physical boundary pairing in every dimension. -/
def originalScreeningPhysicalCurrentBoundaryPairing {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (J : (Fin q → ℝ) → Fin q → ℝ) (L : ℝ) (φ : (Fin q → ℝ) → ℝ) : ℝ := by
  cases q with
  | zero => exact 0
  | succ r => exact originalPhysicalCubeVectorBoundaryPairing b J L φ

/-- The actual selected-frame coefficient is a measurable original-scene random variable. -/
theorem measurable_originalScreeningPhysicalFaceBudget {q : ℕ} {μ ν : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q μ ν kin g)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (j : LegalMarkedOptimalInputScene q → Fin q → ℝ)
    (hj : ∀ k, MemLp (fun scene ↦ j scene k) 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)))
    (L : ℝ) : Measurable (originalScreeningPhysicalFaceBudget Q b j hj L) := by
  cases q with
  | zero => exact measurable_const
  | succ r => exact Q.measurable_scenePhysicalCubeTraceDualBound b _ L

/-- Actual stationarity supplies integrability of the same selected-frame coefficient. -/
theorem integrable_originalScreeningPhysicalFaceBudget {q : ℕ} {μ ν : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q μ ν kin g)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (j : LegalMarkedOptimalInputScene q → Fin q → ℝ)
    (hj : ∀ k, MemLp (fun scene ↦ j scene k) 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)))
    (L : ℝ) : Integrable (originalScreeningPhysicalFaceBudget Q b j hj L) (Q.law : Measure _) := by
  cases q with
  | zero => exact integrable_zero _ _ _
  | succ r => exact Q.integrable_scenePhysicalCubeTraceDualBound b _ L

/-- The same true face coefficient is nonnegative at every nonnegative physical scale. -/
theorem originalScreeningPhysicalFaceBudget_nonneg {q : ℕ} {μ ν : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q μ ν kin g)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (j : LegalMarkedOptimalInputScene q → Fin q → ℝ)
    (hj : ∀ k, MemLp (fun scene ↦ j scene k) 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)))
    {L : ℝ} (hL : 0 ≤ L) (scene : LegalMarkedOptimalInputScene q) :
    0 ≤ originalScreeningPhysicalFaceBudget Q b j hj L scene := by
  cases q with
  | zero => exact le_rfl
  | succ r => exact Q.scenePhysicalCubeTraceDualBound_nonneg b _ hL scene

/-- Zero true normal face projections imply vanishing mean coefficient per true cube volume.
The implication uses proved weighted mean ergodic limits and compact trace approximation. -/
theorem tendsto_originalScreeningPhysicalFaceBudget_mean_div_pow_zero {q : ℕ} {μ ν : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q μ ν kin g)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (j : LegalMarkedOptimalInputScene q → Fin q → ℝ)
    (hj : ∀ k, MemLp (fun scene ↦ j scene k) 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)))
    (hproj : ∀ i, (translationFixedSubspace Q.sceneEuclideanKoopman (ℝ ∙ b i)ᗮ).starProjection
      (originalLinearCurrentReadoutLtwo (Q.law : Measure _) j hj
        (originalEuclideanNormalReadout (b i))) = 0) :
    Tendsto (fun L : ℝ ↦ (∫ scene, originalScreeningPhysicalFaceBudget Q b j hj L scene
      ∂(Q.law : Measure _)) / L^q) atTop (𝓝 0) := by
  cases q with
  | zero => simp [originalScreeningPhysicalFaceBudget]
  | succ r => exact Q.tendsto_integral_scenePhysicalCubeTraceDualBound_div_volume_zero b _ hproj

/-- One actual scene event controls every physical mean-zero smooth test by the same
selected-frame coefficient and the exact original physical gradient norm. -/
theorem ae_all_originalScreeningPhysicalCurrentBoundaryPairing_sq_le {q : ℕ} {μ ν : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q μ ν kin g)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (j : LegalMarkedOptimalInputScene q → Fin q → ℝ)
    (hj : ∀ k, MemLp (fun scene ↦ j scene k) 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)))
    (hm : Measurable j) {L : ℝ} (hL : 0 < L) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      ∀ (K : Compacts (Fin q → ℝ)) (φ : 𝓓_{K}(Fin q → ℝ, ℝ)),
      (∫ z in originalCenteredPhysicalCubeRegion b L, φ z) = 0 →
      (originalScreeningPhysicalCurrentBoundaryPairing b
        (fun z ↦ j (legalMarkedInputSceneReroot q z scene)) L φ)^2 ≤
        originalScreeningPhysicalFaceBudget Q b j hj L scene *
          ‖smoothPhysicalGradientLtwo K (volume.restrict (originalCenteredPhysicalCubeRegion b L)) φ‖^2 := by
  cases q with
  | zero =>
    apply Eventually.of_forall
    intro scene K φ _
    simp [originalScreeningPhysicalCurrentBoundaryPairing, originalScreeningPhysicalFaceBudget]
  | succ r =>
    filter_upwards [Q.ae_all_smooth_originalCurrent_physicalCube_pairing_sq_le b j hj hm hL] with scene hs
    intro K φ hmean
    have h := hs φ (φ.contDiff.of_le (by norm_num)) hmean
    rw [originalCenteredPhysicalCubeGradientEnergy_eq_smoothPhysicalGradientLtwo_norm_sq] at h
    exact h

end OTSelector.Reconstruction
