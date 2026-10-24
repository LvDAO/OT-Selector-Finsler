import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryClockShiftPalm
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryClockShiftMatching
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryClockShiftPoisson
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalFocalKinetic

/-!
# Actual original focal weighted matching after continuous clock shifts

The original globally nonnegative quadratic kernel obeys the parallelogram
bound. Every continuous clock shift is automatically bounded on the original
finite clock span. These two facts preserve original weighted integrability
and produce a complete genuine competitor on the actual pushed joint scene.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Matrix Module Manifold
open scoped ENNReal NNReal CompactlySupported Classical ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false
local instance markedStationaryValueLegalStationaryClockShiftEnergyInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalStationaryClockShiftEnergyPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- The actual mark shift has an inverse subtracting exactly the same
unchanged-clock displacement shift. -/
def legalPairMarkClockShiftHomeomorph (q : ℕ) (b : Fin 2 → C(ℝ, Fin q → ℝ)) :
    PhysicalPairPalmMark (Fin q) ≃ₜ PhysicalPairPalmMark (Fin q) where
  toFun := legalPairMarkClockShift q b
  invFun m := (m.1, m.2 - b 1 m.1.2 + b 0 m.1.1)
  left_inv m := by
    apply Prod.ext
    · rfl
    · change (m.2 + b 1 m.1.2 - b 0 m.1.1) - b 1 m.1.2 + b 0 m.1.1 = m.2
      abel
  right_inv m := by
    apply Prod.ext
    · rfl
    · change (m.2 - b 1 m.1.2 + b 0 m.1.1) + b 1 m.1.2 - b 0 m.1.1 = m.2
      abel
  continuous_toFun := continuous_fst.prodMk ((continuous_snd.add
    ((b 1).continuous.comp continuous_fst.snd)).sub ((b 0).continuous.comp continuous_fst.fst))
  continuous_invFun := continuous_fst.prodMk ((continuous_snd.sub
    ((b 1).continuous.comp continuous_fst.snd)).add ((b 0).continuous.comp continuous_fst.fst))

/-- Every original clock-only integrable probe stays integrable on the
actual transformed true Palm, without a new measurability or moment premise. -/
theorem LegalWeightedStationaryPoissonMatching.clockShift_probe_integrable
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    (b : Fin 2 → C(ℝ, Fin q → ℝ)) :
    Integrable (fun m ↦ g m.1.1 m.1.2)
      (legalMarkedJointPalm q (legalMarkedInputClockShiftLaw q b Q.law)) := by
  rw [legalMarkedJointPalm_clockShift_of_weighted_stationary Q b]
  change Integrable (fun m ↦ g m.1.1 m.1.2)
    ((legalMarkedJointPalm q Q.law).map (legalPairMarkClockShiftHomeomorph q b).toMeasurableEquiv)
  rw [(legalPairMarkClockShiftHomeomorph q b).toMeasurableEquiv.measurableEmbedding.integrable_map_iff]
  change Integrable (fun m ↦ g m.1.1 m.1.2) (legalMarkedJointPalm q Q.law)
  exact Q.probe_integrable

/-- The parallelogram identity controls shifted quadratic energy using only
the original weighted energy and the energy of the bounded clock shift. -/
theorem matrixQuadratic_add_le_twice_of_nonneg {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (hA : ∀ v, 0 ≤ matrixQuadratic A v) (v h : ι → ℝ) :
    matrixQuadratic A (v + h) ≤ 2 * matrixQuadratic A v + 2 * matrixQuadratic A h := by
  have hpar : matrixQuadratic A (v + h) + matrixQuadratic A (v - h) =
      2 * matrixQuadratic A v + 2 * matrixQuadratic A h := by
    simp only [matrixQuadratic, mulVec_add, mulVec_sub, add_dotProduct, sub_dotProduct,
      dotProduct_add, dotProduct_sub]
    ring
  linarith [hA (v - h)]

/-- Arbitrary continuous original clock shifts have an automatic finite
bound on any finite original clock interval; no global shift bound is required. -/
theorem exists_clockShift_difference_bound_on_interval (q : ℕ)
    (b : Fin 2 → C(ℝ, Fin q → ℝ)) (lo hi : ℝ) :
    ∃ B ≥ 0, ∀ a ∈ Icc lo hi, ∀ c ∈ Icc lo hi, ‖b 1 c - b 0 a‖ ≤ B := by
  obtain ⟨B₀, hB₀, hb₀⟩ := ((isCompact_Icc : IsCompact (Icc lo hi)).image
    (b 0).continuous).isBounded.exists_pos_norm_lt
  obtain ⟨B₁, hB₁, hb₁⟩ := ((isCompact_Icc : IsCompact (Icc lo hi)).image
    (b 1).continuous).isBounded.exists_pos_norm_lt
  refine ⟨B₁ + B₀, by positivity, fun a ha c hc ↦ ?_⟩
  exact (norm_sub_le _ _).trans (add_le_add
    (hb₁ _ ⟨c, hc, rfl⟩).le (hb₀ _ ⟨a, ha, rfl⟩).le)

variable {E N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N]
  {F : ContinuousFinslerNorm E N} {u : N → ℝ}

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- Original weighted energy remains integrable under every continuous
source/target clock shift. Actual compact clock support supplies the shift
bound, while original geometry supplies the coefficient bound internally. -/
theorem integrable_originalFocalKinetic_clockShift
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap) (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (b : Fin 2 → C(ℝ, Fin (finrank ℝ S.covector.ker) → ℝ)) :
    Integrable (fun m ↦ D.originalFocalKinetic gap m.1.1 m.1.2 m.2)
      (legalMarkedJointPalm (finrank ℝ S.covector.ker)
        (legalMarkedInputClockShiftLaw (finrank ℝ S.covector.ker) b Q.law)) := by
  let η := legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law
  have : IsProbabilityMeasure η := Q.palm_probability
  have hk : Measurable (fun m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦
      D.originalFocalKinetic gap m.1.1 m.1.2 m.2) := D.measurable_originalFocalKinetic hF hw gap
  rw [legalMarkedJointPalm_clockShift_of_weighted_stationary Q b]
  apply (integrable_map_measure hk.aestronglyMeasurable
    (measurable_legalPairMarkClockShift _ b).aemeasurable).mpr
  have hs : ∀ᵐ m ∂η, m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi := by
    have hmap : ∀ᵐ a ∂η.map (fun m ↦ m.1.1), a - (S.level : ℝ) ∈ Ioo D.lo D.hi := by
      simpa only [η, Q.source_clock] using D.support.source.ae_open
    exact ae_of_ae_map measurable_fst.fst.aemeasurable hmap
  have ht : ∀ᵐ m ∂η, m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi := by
    have hmap : ∀ᵐ a ∂η.map (fun m ↦ m.1.2), a - (S.level : ℝ) ∈ Ioo D.lo D.hi := by
      simpa only [η, Q.target_clock] using D.support.target.ae_open
    exact ae_of_ae_map measurable_fst.snd.aemeasurable hmap
  obtain ⟨C, hC, hquad⟩ := D.exists_originalFocalKinetic_quadratic_bound hF hw hgap hbounds
  obtain ⟨B, hB, hb⟩ := exists_clockShift_difference_bound_on_interval
    (finrank ℝ S.covector.ker) b (S.level + D.lo) (S.level + D.hi)
  let K : ℝ := 2 * C * (finrank ℝ S.covector.ker : ℝ) * B ^ 2
  apply ((Q.kinetic_integrable.const_mul 2).add (integrable_const K)).mono'
    (hk.comp (measurable_legalPairMarkClockShift _ b)).aestronglyMeasurable
  filter_upwards [hs, ht] with m hms hmt
  let d := b 1 m.1.2 - b 0 m.1.1
  have hms' : m.1.1 ∈ Icc (S.level + D.lo) (S.level + D.hi) := by constructor <;> linarith [hms.1, hms.2]
  have hmt' : m.1.2 ∈ Icc (S.level + D.lo) (S.level + D.hi) := by constructor <;> linarith [hmt.1, hmt.2]
  have hd : ‖d‖ ≤ B := hb _ hms' _ hmt'
  have hsum : ∑ i, d i ^ 2 ≤ (finrank ℝ S.covector.ker : ℝ) * B ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin (finrank ℝ S.covector.ker), B ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have hi : |d i| ≤ B := (norm_le_pi_norm d i).trans hd
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr hi
      _ = _ := by simp
  have hkd : D.originalFocalKinetic gap m.1.1 m.1.2 d ≤
      C * ((finrank ℝ S.covector.ker : ℝ) * B ^ 2) :=
    (le_abs_self _).trans ((hquad _ _ d).trans (mul_le_mul_of_nonneg_left hsum hC))
  have hshift : (legalPairMarkClockShift _ b m).2 = m.2 + d := by
    dsimp only [legalPairMarkClockShift, d]
    abel
  change ‖D.originalFocalKinetic gap m.1.1 m.1.2 (legalPairMarkClockShift _ b m).2‖ ≤
    2 * D.originalFocalKinetic gap m.1.1 m.1.2 m.2 + K
  rw [Real.norm_eq_abs, abs_of_nonneg (D.originalFocalKinetic_nonneg hF hw hgap _ _ _), hshift]
  have hdom := matrixQuadratic_add_le_twice_of_nonneg (D.originalFocalMatrix gap m.1)
    (fun v ↦ D.originalFocalKinetic_nonneg hF hw hgap m.1.1 m.1.2 v) m.2 d
  change D.originalFocalKinetic gap m.1.1 m.1.2 (m.2 + d) ≤
    2 * D.originalFocalKinetic gap m.1.1 m.1.2 m.2 + 2 * D.originalFocalKinetic gap m.1.1 m.1.2 d at hdom
  dsimp only [K]
  nlinarith only [hdom, hkd]

/-- Every continuous clock shift produces an actual genuine weighted
stationary Poisson matching for the same original clocks, kinetic kernel and
probe. Every required field is derived on its actual pushed joint scene. -/
def clockShiftWeightedStationaryMatching
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap) (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (b : Fin 2 → C(ℝ, Fin (finrank ℝ S.covector.ker) → ℝ)) :
    LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g := by
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  exact
    { law := legalMarkedInputClockShiftLaw _ b Q.law
      stationary := measurePreserving_legalMarkedInputClockShiftLaw_reroot _ b Q.law Q.stationary
      full_matching := Q.clockShift_full_matching b
      forward := Q.clockShift_forward b
      input_laplace := Q.clockShift_input_laplace b
      palm_probability := Q.clockShift_palm_probability b
      source_clock := Q.clockShift_source_clock b
      target_clock := Q.clockShift_target_clock b
      kinetic_integrable := D.integrable_originalFocalKinetic_clockShift hF hw hgap hbounds Q b
      probe_integrable := Q.clockShift_probe_integrable b }

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
