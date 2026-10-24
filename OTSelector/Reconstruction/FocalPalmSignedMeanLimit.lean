import OTSelector.Reconstruction.FocalPalmEnergyLowerSemicontinuity
import OTSelector.MeasureTheory.ShiftedSignedIntegral

/-! Actual weak Palm limits retain the signed original focal energy bound. -/
open Set Function MeasureTheory Filter Topology
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Converging actual signed means and weak original Palm laws produce
integrable original kinetic and probe readouts with value at most that limit.
No endpoint continuity or unweighted displacement moment is required. -/
theorem integrable_original_focal_signed_energy_le_of_weak_mean_limit
    (q : ℕ) {O W : Set (ℝ × ℝ)} (hO : IsOpen O) (hWO : W ⊆ O)
    (matrix : (ℝ × ℝ) → Matrix (Fin q) (Fin q) ℝ)
    (hmatrix : ContinuousOn matrix O) (hpos : ∀ w ∈ O, (matrix w).PosSemidef)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hkn : ∀ a b v, 0 ≤ kin a b v)
    (hactual : ∀ w ∈ W, ∀ v, kin w.1 w.2 v = matrixQuadratic (matrix w) v)
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgc : ContinuousOn (Function.uncurry g) O)
    {G : ℝ} (hgb : ∀ a b, |g a b| ≤ G) (t p : ℝ)
    (ηs : ℕ → ProbabilityMeasure (PhysicalPairPalmMark (Fin q)))
    (η : ProbabilityMeasure (PhysicalPairPalmMark (Fin q)))
    (hweak : Tendsto ηs atTop (𝓝 η))
    (hcarriers : ∀ n, ∀ᵐ m ∂(ηs n : Measure (PhysicalPairPalmMark (Fin q))), m.1 ∈ W)
    (hcarrier : ∀ᵐ m ∂(η : Measure (PhysicalPairPalmMark (Fin q))), m.1 ∈ W)
    (hIs : ∀ n, Integrable (fun m ↦ kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2)
      (ηs n : Measure (PhysicalPairPalmMark (Fin q))))
    (hmean : Tendsto (fun n ↦ ∫ m, kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2
      ∂(ηs n : Measure (PhysicalPairPalmMark (Fin q)))) atTop (𝓝 p)) :
    Integrable (fun m ↦ kin m.1.1 m.1.2 m.2)
        (η : Measure (PhysicalPairPalmMark (Fin q))) ∧
      Integrable (fun m ↦ g m.1.1 m.1.2)
        (η : Measure (PhysicalPairPalmMark (Fin q))) ∧
      (∫ m, kin m.1.1 m.1.2 m.2 ∂(η : Measure (PhysicalPairPalmMark (Fin q)))) +
        t * (∫ m, g m.1.1 m.1.2 ∂(η : Measure (PhysicalPairPalmMark (Fin q)))) ≤ p := by
  let shift (m : PhysicalPairPalmMark (Fin q)) :=
    kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2 + |t| * G
  have hn (m : PhysicalPairPalmMark (Fin q)) : 0 ≤ shift m := by
    have hb : |t * g m.1.1 m.1.2| ≤ |t| * G := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hgb m.1.1 m.1.2) (abs_nonneg t)
    dsimp only [shift]
    linarith [(abs_le.mp hb).1, hkn m.1.1 m.1.2 m.2]
  have hshiftI (n : ℕ) : Integrable shift
      (ηs n : Measure (PhysicalPairPalmMark (Fin q))) :=
    (hIs n).add (integrable_const _)
  have heq (n : ℕ) :
      (∫ m, shift m ∂(ηs n : Measure (PhysicalPairPalmMark (Fin q)))) =
        (∫ m, kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2
          ∂(ηs n : Measure (PhysicalPairPalmMark (Fin q)))) + |t| * G := by
    rw [show shift = fun m ↦
      (kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2) + |t| * G from rfl]
    rw [integral_add (hIs n) (integrable_const _), integral_const]
    simp
  have hshiftMean : Tendsto
      (fun n ↦ ∫ m, shift m ∂(ηs n : Measure (PhysicalPairPalmMark (Fin q))))
      atTop (𝓝 (p + |t| * G)) := by
    simp_rw [heq]
    exact hmean.add_const _
  have hlow : 0 ≤ p + |t| * G :=
    ge_of_tendsto hshiftMean (.of_forall fun n ↦ integral_nonneg hn)
  have hlintegral : Tendsto
      (fun n ↦ ∫⁻ m, ENNReal.ofReal (shift m)
        ∂(ηs n : Measure (PhysicalPairPalmMark (Fin q))))
      atTop (𝓝 (ENNReal.ofReal (p + |t| * G))) := by
    simp_rw [← ofReal_integral_eq_lintegral_ofReal (hshiftI _) (.of_forall hn)]
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hshiftMean
  have hbound := lintegral_original_focal_shifted_le_liminf_of_weak q hO hWO
    matrix hmatrix hpos hkn hactual hgc hgb t ηs η hweak hcarriers hcarrier
  rw [hlintegral.liminf_eq] at hbound
  exact integrable_signed_energy_of_shifted_lintegral_le
    (η : Measure (PhysicalPairPalmMark (Fin q)))
    (fun m ↦ kin m.1.1 m.1.2 m.2) (fun m ↦ g m.1.1 m.1.2)
    hk (fun m ↦ hkn m.1.1 m.1.2 m.2) (hg.comp measurable_fst)
    (fun m ↦ hgb m.1.1 m.1.2) t p hlow hbound

end OTSelector.Reconstruction
