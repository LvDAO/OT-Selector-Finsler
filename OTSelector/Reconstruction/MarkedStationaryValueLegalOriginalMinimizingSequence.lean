import OTSelector.Reconstruction.MarkedStationaryValueLegalFiniteMomentReserve
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Actual original weighted stationary infimum and minimizing sequence

The original finite-second-moment reserve proves nonemptiness of the genuine
weighted stationary class on the unchanged original Poisson inputs. Original
nonnegative kinetic energy and the bounded original probe bound its infimum
below. Actual near-infimum competitors then supply a minimizing sequence and
its uniform original kinetic bound internally.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option linter.unusedSectionVars false

/-- Original nonnegative kinetic and bounded probe give a common actual
signed value lower bound for every genuine original weighted matching. -/
theorem LegalWeightedStationaryPoissonMatching.value_lower_bound
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hkin : ∀ a b v, 0 ≤ kin a b v) {G : ℝ} (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) :
    -(|t| * G) ≤ Q.value t := by
  let η := legalMarkedJointPalm q Q.law
  have : IsProbabilityMeasure η := Q.palm_probability
  have hp : |∫ m, g m.1.1 m.1.2 ∂η| ≤ G := by
    have h := norm_integral_le_of_norm_le_const (μ := η) (f := fun m ↦ g m.1.1 m.1.2)
      (.of_forall (fun m ↦ by simpa only [Real.norm_eq_abs] using hgb m.1.1 m.1.2))
    simpa only [Real.norm_eq_abs, probReal_univ, one_mul, mul_one] using h
  have hprobe : |t * (∫ m, g m.1.1 m.1.2 ∂η)| ≤ |t| * G := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hp (abs_nonneg _)
  have hnonneg : 0 ≤ ∫ m, kin m.1.1 m.1.2 m.2 ∂η :=
    integral_nonneg (fun m ↦ hkin m.1.1 m.1.2 m.2)
  change -(|t| * G) ≤ (∫ m, kin m.1.1 m.1.2 m.2 ∂η) +
    t * (∫ m, g m.1.1 m.1.2 ∂η)
  linarith [(abs_le.mp hprobe).1]

/-- The bounded original probe bounds the actual kinetic mean by signed
value plus the same probe allowance, on the unchanged true probability Palm. -/
theorem LegalWeightedStationaryPoissonMatching.kinetic_mean_le_value_add_probe_bound
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    {G : ℝ} (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) :
    (∫ m, kin m.1.1 m.1.2 m.2 ∂legalMarkedJointPalm q Q.law) ≤ Q.value t + |t| * G := by
  let η := legalMarkedJointPalm q Q.law
  have : IsProbabilityMeasure η := Q.palm_probability
  have hp : |∫ m, g m.1.1 m.1.2 ∂η| ≤ G := by
    have h := norm_integral_le_of_norm_le_const (μ := η) (f := fun m ↦ g m.1.1 m.1.2)
      (.of_forall (fun m ↦ by simpa only [Real.norm_eq_abs] using hgb m.1.1 m.1.2))
    simpa only [Real.norm_eq_abs, probReal_univ, one_mul, mul_one] using h
  have hprobe : |t * (∫ m, g m.1.1 m.1.2 ∂η)| ≤ |t| * G := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hp (abs_nonneg _)
  change (∫ m, kin m.1.1 m.1.2 m.2 ∂η) ≤
    ((∫ m, kin m.1.1 m.1.2 m.2 ∂η) + t * (∫ m, g m.1.1 m.1.2 ∂η)) + |t| * G
  linarith [(abs_le.mp hprobe).1]

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The original weighted stationary variational value over genuine complete
original Poisson matchings, with the literal original focal cost and probe. -/
def originalWeightedStationaryInf (gap : ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  sInf (range (fun Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
    (D.originalFocalKinetic gap) g ↦ Q.value t))

/-- Original physical data produce a genuine minimizing sequence, its actual
infimum lower comparison, and the uniform kinetic mean needed by compactness.
Neither a pre-existing matching nor an energy-bound oracle is supplied. -/
theorem exists_original_weighted_minimizing_sequence
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 4 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (hπ : Vlasov.IsCoupling π μ ν) (horder : ∀ᵐ p ∂π, p.1 ≤ p.2)
    {G : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) :
    (∀ Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, D.originalWeightedStationaryInf gap g t ≤ Q.value t) ∧
    ∃ Q : ℕ → LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g,
      (∀ n, D.originalWeightedStationaryInf gap g t ≤ (Q n).value t ∧
        (Q n).value t ≤ D.originalWeightedStationaryInf gap g t + 1 / ((n : ℝ) + 1)) ∧
      Tendsto (fun n ↦ (Q n).value t) atTop (𝓝 (D.originalWeightedStationaryInf gap g t)) ∧
      ∀ n, (∫ m, D.originalFocalKinetic gap m.1.1 m.1.2 m.2
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) (Q n).law) ≤
        D.originalWeightedStationaryInf gap g t + 1 + |t| * G := by
  let V := range (fun Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
    (D.originalFocalKinetic gap) g ↦ Q.value t)
  obtain ⟨Q₀, _hsecond⟩ := D.exists_original_focal_finiteSecondMoment_stationaryMatching
    hF hw hq hgap hbounds π hπ horder hg hgb
  have hnonempty : V.Nonempty := ⟨Q₀.value t, Q₀, rfl⟩
  have hbounded : BddBelow V := by
    refine ⟨-(|t| * G), ?_⟩
    rintro _ ⟨R, rfl⟩
    exact R.value_lower_bound (D.originalFocalKinetic_nonneg hF hw hgap) hgb t
  have hinf (R : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) : D.originalWeightedStationaryInf gap g t ≤ R.value t :=
    csInf_le hbounded ⟨R, rfl⟩
  have hex (n : ℕ) : ∃ R : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g,
      R.value t < D.originalWeightedStationaryInf gap g t + 1 / ((n : ℝ) + 1) := by
    obtain ⟨v, ⟨R, rfl⟩, hv⟩ := exists_lt_of_csInf_lt hnonempty
      (show sInf V < D.originalWeightedStationaryInf gap g t + 1 / ((n : ℝ) + 1) from
        lt_add_of_pos_right _ (by positivity))
    exact ⟨R, hv⟩
  choose Q hQ using hex
  have hQbounds (n : ℕ) : D.originalWeightedStationaryInf gap g t ≤ (Q n).value t ∧
      (Q n).value t ≤ D.originalWeightedStationaryInf gap g t + 1 / ((n : ℝ) + 1) :=
    ⟨hinf _, (hQ n).le⟩
  refine ⟨hinf, Q, hQbounds, ?_, ?_⟩
  · have hupper : Tendsto (fun n : ℕ ↦ D.originalWeightedStationaryInf gap g t + 1 / ((n : ℝ) + 1))
        atTop (𝓝 (D.originalWeightedStationaryInf gap g t)) := by
      simpa only [add_zero] using (tendsto_const_nhds.add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun n ↦ (hQbounds n).1) (fun n ↦ (hQbounds n).2)
  · intro n
    have heps : 1 / ((n : ℝ) + 1) ≤ 1 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
      norm_num
    have hk := (Q n).kinetic_mean_le_value_add_probe_bound hgb t
    linarith [(hQbounds n).2]

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
