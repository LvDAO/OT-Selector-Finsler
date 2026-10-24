import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingRandomCount
import OTSelector.Reconstruction.MarkedStationaryValueHaarRootBoundary

/-! The actual random original reserve transports have a volume-normalized
rho^(1-2/q) budget, with the physical cube scale cancelled exactly. -/
open Set Function MeasureTheory
open OTSelector.Probability
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Literal cube scale cancellation in the actual population transport budget. -/
theorem originalCubePopulation_squareRate_normalization {q : ℕ} (hq : 0 < q)
    {L ρ : ℝ} (hL : 0 < L) (hρ : 0 ≤ ρ) (C : ℝ) :
    L^2*C*(ρ*L^q)^(1-2/(q : ℝ))/L^q = C*ρ^(1-2/(q : ℝ)) := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hpower : L^2*(L^q)^(1-2/(q : ℝ)) = L^q := by
    rw [← Real.rpow_natCast_mul hL.le, ← Real.rpow_natCast L 2,
      ← Real.rpow_add hL]
    conv_rhs => rw [← Real.rpow_natCast L q]
    congr 1
    push_cast
    field_simp
    ring
  rw [Real.mul_rpow hρ (pow_nonneg hL.le q)]
  calc
    _ = C*ρ^(1-2/(q : ℝ))*(L^2*(L^q)^(1-2/(q : ℝ)))/L^q := by ring
    _ = _ := by rw [hpower]; exact mul_div_cancel_right₀ _ (pow_ne_zero _ hL.ne')

variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}

/-- In the actual same-scene experiment the reserve mean count is rho times
its true cube volume. The resulting original source population transport has
per-volume expected energy at most q*Cq*rho^(1-2/q), at every positive cube size. -/
theorem LegalWeightedStationaryPoissonMatching.original_sourceReserveClass_normalizedPopulationCoupling
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    {R ρ : ℝ} (hR : 0 < R) (hρ : 0 ≤ ρ)
    {C D : Set ℝ} (hC : MeasurableSet C) (hD : MeasurableSet D) (hq : 4 < q) :
    let V := volume.real (haarRootCube (Fin q) R)
    let rate := Real.toNNReal (ρ*V)
    let Γ := originalReserveExcessClassPopulationCouplingRandom R 0 1 C D
      ((EuclideanSpace.equiv (Fin q) ℝ).symm (fun _ ↦ -R)) (2*R) ∘
        originalSourceReserveExperimentSplice
    Measurable Γ ∧ Measurable (fun p ↦ ∫ v, ‖v.1-v.2‖^2 ∂Γ p) ∧
      Integrable (fun p ↦ ∫ v, ‖v.1-v.2‖^2 ∂Γ p) (originalMainReserveExperimentLaw Q rate) ∧
      (∫ p, ∫ v, ‖v.1-v.2‖^2 ∂Γ p ∂originalMainReserveExperimentLaw Q rate)/V ≤
        (q : ℝ)*dyadicMatchingConstant q*ρ^(1-2/(q : ℝ)) := by
  let V := volume.real (haarRootCube (Fin q) R)
  have hV : V = (2*R)^q := by simp only [V, volume_real_haarRootCube _ hR.le, Fintype.card_fin]
  have hVpos : 0 < V := by rw [hV]; positivity
  let rate := Real.toNNReal (ρ*V)
  have hr : (rate : ℝ) = ρ*V := Real.coe_toNNReal _ (mul_nonneg hρ hVpos.le)
  have h := Q.original_sourceReserveClass_randomPopulationCoupling rate R hC hD hq
    ((EuclideanSpace.equiv (Fin q) ℝ).symm (fun _ ↦ -R)) (2*R)
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  calc
    _ ≤ (((q : ℝ)*(2*R)^2)*dyadicMatchingConstant q*(rate : ℝ)^(1-2/(q : ℝ)))/V :=
      div_le_div_of_nonneg_right h.2.2.2 hVpos.le
    _ = _ := by
      rw [hr, hV]
      convert originalCubePopulation_squareRate_normalization (by omega : 0 < q)
        (by positivity : 0 < 2*R) hρ ((q : ℝ)*dyadicMatchingConstant q) using 1
      ring

/-- The actual target reserve uses the same full original experiment and the
same true volume normalization; zero reserve intensity is included. -/
theorem LegalWeightedStationaryPoissonMatching.original_targetReserveClass_normalizedPopulationCoupling
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    {R ρ : ℝ} (hR : 0 < R) (hρ : 0 ≤ ρ)
    {C D : Set ℝ} (hC : MeasurableSet C) (hD : MeasurableSet D) (hq : 4 < q) :
    let V := volume.real (haarRootCube (Fin q) R)
    let rate := Real.toNNReal (ρ*V)
    let Γ := originalReserveExcessClassPopulationCouplingRandom R 1 0 C D
      ((EuclideanSpace.equiv (Fin q) ℝ).symm (fun _ ↦ -R)) (2*R) ∘
        originalTargetReserveExperimentSplice
    Measurable Γ ∧ Measurable (fun p ↦ ∫ v, ‖v.1-v.2‖^2 ∂Γ p) ∧
      Integrable (fun p ↦ ∫ v, ‖v.1-v.2‖^2 ∂Γ p) (originalMainReserveExperimentLaw Q rate) ∧
      (∫ p, ∫ v, ‖v.1-v.2‖^2 ∂Γ p ∂originalMainReserveExperimentLaw Q rate)/V ≤
        (q : ℝ)*dyadicMatchingConstant q*ρ^(1-2/(q : ℝ)) := by
  let V := volume.real (haarRootCube (Fin q) R)
  have hV : V = (2*R)^q := by simp only [V, volume_real_haarRootCube _ hR.le, Fintype.card_fin]
  have hVpos : 0 < V := by rw [hV]; positivity
  let rate := Real.toNNReal (ρ*V)
  have hr : (rate : ℝ) = ρ*V := Real.coe_toNNReal _ (mul_nonneg hρ hVpos.le)
  have h := Q.original_targetReserveClass_randomPopulationCoupling rate R hC hD hq
    ((EuclideanSpace.equiv (Fin q) ℝ).symm (fun _ ↦ -R)) (2*R)
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  calc
    _ ≤ (((q : ℝ)*(2*R)^2)*dyadicMatchingConstant q*(rate : ℝ)^(1-2/(q : ℝ)))/V :=
      div_le_div_of_nonneg_right h.2.2.2 hVpos.le
    _ = _ := by
      rw [hr, hV]
      convert originalCubePopulation_squareRate_normalization (by omega : 0 < q)
        (by positivity : 0 < 2*R) hρ ((q : ℝ)*dyadicMatchingConstant q) using 1
      ring
end OTSelector.Reconstruction
