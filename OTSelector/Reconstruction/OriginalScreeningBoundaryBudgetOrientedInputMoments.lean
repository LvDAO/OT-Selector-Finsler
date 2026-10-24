import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetOrientedInputMass
import OTSelector.Reconstruction.OriginalPoissonHilbertInputMomentsActual

/-! Genuine scalar moments of the same original-input physical reflected masses. -/
open Set Function Filter MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- The actual same-frame full-input reflected mass has a finite second moment, zero
mean and the genuine surface-order second-moment bound, from the original Poisson law. -/
theorem LegalWeightedStationaryPoissonMatching.originalScreening_orientedInputMass_moments
    {q : ℕ} {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q μ ν kin g)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {R : ℝ} (hR : 1 ≤ R) {C : Set ℝ} (hC : MeasurableSet C) (c : Fin 2) :
    let I := originalScreeningOrientedReflectedInputMass b R C c
    let γ := if c = 0 then μ else ν
    MemLp I 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)) ∧
    (∫ scene, I scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) = 0 ∧
    (∫ scene, (I scene)^2 ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) ≤
      γ.real C * ((4*(q:ℝ)*4^(q-1))*R^(q-1)) := by
  let η := originalEuclideanMollifier q
  let γ := if c = 0 then μ else ν
  let F := originalScreeningOrientedInputClassBoundaryWeight b R C
  let F₀ := originalInputClassBoundaryWeight η R C
  let J := fun scene : LegalMarkedOptimalInputScene q ↦ ∫ p, F p ∂legalInputColorMeasure q scene.2 c
  have : IsProbabilityMeasure γ := by
    by_cases hc : c = 0 <;> simp only [γ, hc, ↓reduceIte] <;> infer_instance
  have hmη : Measurable η := (contDiff_originalEuclideanMollifier q).continuous.measurable
  have hηI : Integrable η := integrable_originalEuclideanMollifier q
  have hone : ∫ x, η x = 1 := integral_originalEuclideanMollifier_eq_one q
  have hsup (x : Fin q → ℝ) (hx : 1 < ‖x‖) : η x = 0 :=
    raw_unit_range_of_euclidean_unit_range (originalEuclideanMollifier_unit_range q) x hx.le
  have hF : Measurable F := (measurable_originalInputClassBoundaryWeight hmη R hC).comp
    (originalOrientedInputCoordinates b).measurable
  have hB : ∀ p, ‖F p‖ ≤ 1 := fun p ↦ by
    exact abs_originalInputClassBoundaryWeight_le_one hηI (originalEuclideanMollifier_nonneg q)
      hone R C (originalOrientedInputCoordinates b p)
  have hsupport (p : LegalMarkedPhysicalPoint q)
      (hp : p.1 ∉ orthonormalPhysicalCubeMap b '' haarRootCube (Fin q) (R+1)) : F p = 0 := by
    have hx : (orthonormalPhysicalCubeMap b).symm p.1 ∉ haarRootCube (Fin q) (R+1) := by
      intro hx
      exact hp ⟨_, hx, (orthonormalPhysicalCubeMap b).apply_symm_apply p.1⟩
    change originalInputBoundaryWeight η R ((orthonormalPhysicalCubeMap b).symm p.1) *
      C.indicator (fun _ ↦ (1:ℝ)) p.2 = 0
    rw [originalInputBoundaryWeight_eq_zero_off_shell hone hsup hR _ (fun hs ↦ hx hs.1), zero_mul]
  have hmean₀ : (∫ p, F₀ p ∂(volume : Measure (Fin q → ℝ)).prod γ) = 0 := by
    change (∫ p, originalInputBoundaryWeight η R p.1 * C.indicator (fun _ ↦ (1:ℝ)) p.2
      ∂(volume : Measure (Fin q → ℝ)).prod γ) = 0
    rw [integral_prod_mul, integral_originalInputBoundaryWeight_eq_zero hηI hone R, zero_mul]
  have hmean : (∫ p, F p ∂(volume : Measure (Fin q → ℝ)).prod γ) = 0 := by
    rw [show (∫ p, F p ∂(volume : Measure (Fin q → ℝ)).prod γ) =
        ∫ p, F₀ p ∂(volume : Measure (Fin q → ℝ)).prod γ from
      (measurePreserving_originalOrientedInputCoordinates b γ).integral_comp' F₀]
    exact hmean₀
  have hsquare : (∫ p, ‖F p‖^2 ∂(volume : Measure (Fin q → ℝ)).prod γ) =
      γ.real C * ∫ x, (originalInputBoundaryWeight η R x)^2 := by
    rw [show (∫ p, ‖F p‖^2 ∂(volume : Measure (Fin q → ℝ)).prod γ) =
        ∫ p, ‖F₀ p‖^2 ∂(volume : Measure (Fin q → ℝ)).prod γ from
      (measurePreserving_originalOrientedInputCoordinates b γ).integral_comp' (fun p ↦ ‖F₀ p‖^2)]
    have he (p : LegalMarkedPhysicalPoint q) : ‖F₀ p‖^2 =
        (originalInputBoundaryWeight η R p.1)^2 * C.indicator (fun _ ↦ (1:ℝ)) p.2 := by
      by_cases hp : p.2 ∈ C <;> simp [F₀, originalInputClassBoundaryWeight, hp, Real.norm_eq_abs]
    simp_rw [he]
    rw [integral_prod_mul (fun x ↦ (originalInputBoundaryWeight η R x)^2)
      (C.indicator (fun _ ↦ (1:ℝ))), integral_indicator hC, integral_const, smul_eq_mul, mul_one]
    simp only [Measure.real, Measure.restrict_apply_univ]
    ring
  have h := Q.centered_fullInput_hilbert_moments (stdOrthonormalBasis ℝ ℝ).toHilbertBasis
    (isCompact_Icc.image (orthonormalPhysicalCubeMap b).continuous) hF hsupport zero_le_one hB c
  dsimp only at h
  dsimp only [γ] at hmean hsquare
  have hLp : MemLp J 2 (Q.law : Measure _) := by simpa only [hmean, sub_zero, J] using h.2.1
  have hJmean : (∫ scene, J scene ∂(Q.law : Measure _)) = 0 := h.2.2.1.trans hmean
  have hJsecond : (∫ scene, (J scene)^2 ∂(Q.law : Measure _)) =
      γ.real C * ∫ x, (originalInputBoundaryWeight η R x)^2 := by
    simpa only [hmean, sub_zero, Real.norm_eq_abs, sq_abs, J] using h.2.2.2.trans hsquare
  have he := Q.ae_originalScreening_orientedInputMass_eq_boundaryWeight b hR hC c
  dsimp only at he ⊢
  refine ⟨hLp.ae_eq he.symm, (integral_congr_ae he).trans hJmean, ?_⟩
  calc
    _ = ∫ scene, (J scene)^2 ∂(Q.law : Measure _) :=
      integral_congr_ae (he.mono (fun _ hx ↦ congrArg (fun x : ℝ ↦ x^2) hx))
    _ = _ := hJsecond
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((integral_sq_originalInputBoundaryWeight_le_shell hmη hηI
        (originalEuclideanMollifier_nonneg q) hone hsup hR).trans
        (by simpa only [Fintype.card_fin] using
          (volume_real_originalInputBoundaryShell_le (ι := Fin q) hR))) measureReal_nonneg

end OTSelector.Reconstruction
