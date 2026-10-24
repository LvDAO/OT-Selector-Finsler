import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryClockShiftEnergy
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalFocalMomentum

/-!
# Exact energy polynomial of actual continuous clock-shift competitors

The complete genuine weighted matching is the actual shifted original scene.
Its kinetic value is an exact polynomial in the scalar shift amplitude.
The linear coefficient uses the literal original momentum, with coefficient
one because matrixQuadratic includes one half. All coefficients are integrable
by original geometry and the automatically bounded original clock support.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Matrix Module Manifold
open scoped ENNReal NNReal CompactlySupported Classical ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option linter.unusedSectionVars false

/-- The original target clock shift minus the original source clock shift,
read on the actual paired-clock full-displacement Palm mark. -/
def legalPairClockShiftDifference (q : ℕ) (b : Fin 2 → C(ℝ, Fin q → ℝ))
    (m : PhysicalPairPalmMark (Fin q)) : Fin q → ℝ := b 1 m.1.2 - b 0 m.1.1

theorem measurable_legalPairClockShiftDifference (q : ℕ) (b : Fin 2 → C(ℝ, Fin q → ℝ)) :
    Measurable (legalPairClockShiftDifference q b) :=
  ((b 1).continuous.measurable.comp measurable_fst.snd).sub
    ((b 0).continuous.measurable.comp measurable_fst.fst)

/-- Scaling the actual continuous clock shifts scales their full displacement
increment by the same scalar, including negative amplitudes. -/
theorem legalPairMarkClockShift_scaled_displacement (q : ℕ)
    (b : Fin 2 → C(ℝ, Fin q → ℝ)) (ε : ℝ) (m : PhysicalPairPalmMark (Fin q)) :
    (legalPairMarkClockShift q (fun c ↦ ε • b c) m).2 =
      m.2 + ε • legalPairClockShiftDifference q b m := by
  change m.2 + ε • b 1 m.1.2 - ε • b 0 m.1.1 =
    m.2 + ε • (b 1 m.1.2 - b 0 m.1.1)
  rw [smul_sub, add_sub_assoc]

/-- The exact half-quadratic expansion has original momentum dotted with
the shift as its linear coefficient. -/
theorem matrixQuadratic_add_smul_eq_of_isHermitian {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (v h : ι → ℝ) (ε : ℝ) :
    matrixQuadratic A (v + ε • h) = matrixQuadratic A v +
      ε * ((A *ᵥ v) ⬝ᵥ h) + ε ^ 2 * matrixQuadratic A h := by
  have ht : Aᵀ = A := by
    ext i j
    simpa only [transpose_apply, star_trivial] using hA.apply i j
  have hcross : v ⬝ᵥ (A *ᵥ h) = h ⬝ᵥ (A *ᵥ v) := by
    simpa only [ht] using dotProduct_transpose_mulVec A v h
  rw [dotProduct_comm (A *ᵥ v) h]
  simp only [matrixQuadratic, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add,
    dotProduct_smul, smul_dotProduct, smul_eq_mul, hcross]
  ring

/-- A bound in the actual coordinate norm controls the finite coordinate
square sum, including the zero-dimensional case. -/
theorem legalClockShift_sum_sq_le_card_mul_sq_of_norm_le {ι : Type*} [Fintype ι]
    (v : ι → ℝ) {B : ℝ} (hB : 0 ≤ B) (hv : ‖v‖ ≤ B) :
    ∑ i, v i ^ 2 ≤ (Fintype.card ι : ℝ) * B ^ 2 := by
  calc
    _ ≤ ∑ _i : ι, B ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have hi : |v i| ≤ B := (norm_le_pi_norm v i).trans hv
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr hi
    _ = _ := by simp

/-- The literal full-coordinate momentum pairing is bounded by its original
norm times the bounded shift; no displacement moment enters. -/
theorem legalClockShift_norm_dotProduct_le {ι : Type*} [Fintype ι]
    (p h : ι → ℝ) {B : ℝ} (hh : ‖h‖ ≤ B) :
    ‖p ⬝ᵥ h‖ ≤ ((Fintype.card ι : ℝ) * B) * ‖p‖ := by
  rw [Real.norm_eq_abs]
  calc
    _ ≤ ∑ i, |p i * h i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, ‖p‖ * B := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      apply mul_le_mul
      · simpa only [Real.norm_eq_abs] using norm_le_pi_norm p i
      · exact (norm_le_pi_norm h i).trans hh
      · exact abs_nonneg _
      · exact norm_nonneg _
    _ = _ := by simp; ring

variable {E N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N]
  {F : ContinuousFinslerNorm E N} {u : N → ℝ}

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- The same original marginal clocks automatically give a finite bound for
any continuous shift difference on the actual true probability Palm. -/
theorem exists_ae_clockShift_difference_bound
    {gap : ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (b : Fin 2 → C(ℝ, Fin (finrank ℝ S.covector.ker) → ℝ)) :
    ∃ B ≥ 0, ∀ᵐ m ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law,
      ‖legalPairClockShiftDifference _ b m‖ ≤ B := by
  let η := legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law
  have hs : ∀ᵐ m ∂η, m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi := by
    have hmap : ∀ᵐ a ∂η.map (fun m ↦ m.1.1), a - (S.level : ℝ) ∈ Ioo D.lo D.hi := by
      simpa only [η, Q.source_clock] using D.support.source.ae_open
    exact ae_of_ae_map measurable_fst.fst.aemeasurable hmap
  have ht : ∀ᵐ m ∂η, m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi := by
    have hmap : ∀ᵐ a ∂η.map (fun m ↦ m.1.2), a - (S.level : ℝ) ∈ Ioo D.lo D.hi := by
      simpa only [η, Q.target_clock] using D.support.target.ae_open
    exact ae_of_ae_map measurable_fst.snd.aemeasurable hmap
  obtain ⟨B, hB, hb⟩ := exists_clockShift_difference_bound_on_interval
    (finrank ℝ S.covector.ker) b (S.level + D.lo) (S.level + D.hi)
  refine ⟨B, hB, ?_⟩
  filter_upwards [hs, ht] with m hms hmt
  apply hb
  · constructor <;> linarith [hms.1, hms.2]
  · constructor <;> linarith [hmt.1, hmt.2]

/-- Both exact polynomial coefficients are integrable on the actual original
true Palm. Original momentum supplies the linear term; original coefficient
bounds and compact clock support supply the pure shift energy. -/
theorem integrable_clockShift_energy_coefficients
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap) (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (b : Fin 2 → C(ℝ, Fin (finrank ℝ S.covector.ker) → ℝ)) :
    Integrable (fun m ↦ originalSeedPairMomentum S w m ⬝ᵥ legalPairClockShiftDifference _ b m)
        (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ∧
      Integrable (fun m ↦ D.originalFocalKinetic gap m.1.1 m.1.2
        (legalPairClockShiftDifference _ b m))
        (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) := by
  let η := legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law
  have : IsProbabilityMeasure η := Q.palm_probability
  have hp := (D.integrable_original_pair_momentum_of_weighted_stationary hF hw hgap hbounds Q).1
  have hm : Measurable (fun m ↦ originalSeedPairMomentum S w m ⬝ᵥ legalPairClockShiftDifference _ b m) := by
    have hc : Continuous (fun p : (Fin (finrank ℝ S.covector.ker) → ℝ) ×
        (Fin (finrank ℝ S.covector.ker) → ℝ) ↦ p.1 ⬝ᵥ p.2) := by unfold dotProduct; fun_prop
    exact hc.measurable.comp ((measurable_originalSeedPairMomentum S hF hw).prodMk
      (measurable_legalPairClockShiftDifference _ b))
  obtain ⟨B, hB, hb⟩ := D.exists_ae_clockShift_difference_bound Q b
  obtain ⟨C, hC, hquad⟩ := D.exists_originalFocalKinetic_quadratic_bound hF hw hgap hbounds
  constructor
  · apply (hp.norm.const_mul ((finrank ℝ S.covector.ker : ℝ) * B)).mono' hm.aestronglyMeasurable
    filter_upwards [hb] with m hbm
    simpa only [Fintype.card_fin] using
      legalClockShift_norm_dotProduct_le (originalSeedPairMomentum S w m) _ hbm
  · have hk : Measurable (fun m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦
        D.originalFocalKinetic gap m.1.1 m.1.2 (legalPairClockShiftDifference _ b m)) :=
      (D.measurable_originalFocalKinetic hF hw gap).comp
        (measurable_fst.prodMk (measurable_legalPairClockShiftDifference _ b))
    apply (integrable_const (C * ((finrank ℝ S.covector.ker : ℝ) * B ^ 2))).mono' hk.aestronglyMeasurable
    filter_upwards [hb] with m hbm
    rw [Real.norm_eq_abs]
    exact (hquad _ _ _).trans (mul_le_mul_of_nonneg_left
      (by simpa only [Fintype.card_fin] using
        legalClockShift_sum_sq_le_card_mul_sq_of_norm_le _ hB hbm) hC)

/-- The exact original inverse-compliance quadratic expansion holds almost
everywhere on the actual true Palm and keeps the literal original momentum. -/
theorem ae_originalFocalKinetic_clockShift_scaled_expansion
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (b : Fin 2 → C(ℝ, Fin (finrank ℝ S.covector.ker) → ℝ)) (ε : ℝ) :
    ∀ᵐ m ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law,
      D.originalFocalKinetic gap m.1.1 m.1.2 (legalPairMarkClockShift _ (fun c ↦ ε • b c) m).2 =
        D.originalFocalKinetic gap m.1.1 m.1.2 m.2 +
          ε * (originalSeedPairMomentum S w m ⬝ᵥ legalPairClockShiftDifference _ b m) +
            ε ^ 2 * D.originalFocalKinetic gap m.1.1 m.1.2 (legalPairClockShiftDifference _ b m) := by
  let η := legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law
  have hs : ∀ᵐ m ∂η, m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m.1.1 ∈ μ.support := by
    have h : ∀ᵐ a ∂μ, a - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ a ∈ μ.support :=
      D.support.source.ae_open.and μ.support_mem_ae
    have hmap : ∀ᵐ a ∂η.map (fun m ↦ m.1.1),
        a - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ a ∈ μ.support := by
      simpa only [η, Q.source_clock] using h
    exact ae_of_ae_map measurable_fst.fst.aemeasurable hmap
  have ht : ∀ᵐ m ∂η, m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m.1.2 ∈ ν.support := by
    have h : ∀ᵐ a ∂ν, a - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ a ∈ ν.support :=
      D.support.target.ae_open.and ν.support_mem_ae
    have hmap : ∀ᵐ a ∂η.map (fun m ↦ m.1.2),
        a - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ a ∈ ν.support := by
      simpa only [η, Q.target_clock] using h
    exact ae_of_ae_map measurable_fst.snd.aemeasurable hmap
  filter_upwards [hs, ht, Q.ae_palm_forward] with m hms hmt hmf
  rw [legalPairMarkClockShift_scaled_displacement]
  have hkin := D.originalFocalKinetic_eq_of_original_support hbounds hms hmt hmf
  rw [hkin _, hkin _, hkin _]
  exact matrixQuadratic_add_smul_eq_of_isHermitian
    (D.pair_compliance_posDef hF hw hms.1 hmt.1 hmf).2.isHermitian _ _ ε

/-- The actual transformed kinetic expectation is the exact original kinetic
expectation plus its integrable original momentum and pure-shift coefficients. -/
theorem integral_originalFocalKinetic_clockShift_scaled_polynomial
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap) (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (b : Fin 2 → C(ℝ, Fin (finrank ℝ S.covector.ker) → ℝ)) (ε : ℝ) :
    (∫ m, D.originalFocalKinetic gap m.1.1 m.1.2 m.2
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker)
        (legalMarkedInputClockShiftLaw _ (fun c ↦ ε • b c) Q.law)) =
      (∫ m, D.originalFocalKinetic gap m.1.1 m.1.2 m.2
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) +
        ε * (∫ m, originalSeedPairMomentum S w m ⬝ᵥ legalPairClockShiftDifference _ b m
          ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) +
        ε ^ 2 * (∫ m, D.originalFocalKinetic gap m.1.1 m.1.2 (legalPairClockShiftDifference _ b m)
          ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) := by
  have hk : Measurable (fun m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦
      D.originalFocalKinetic gap m.1.1 m.1.2 m.2) := D.measurable_originalFocalKinetic hF hw gap
  obtain ⟨hlin, hquad⟩ := D.integrable_clockShift_energy_coefficients hF hw hgap hbounds Q b
  rw [legalMarkedJointPalm_clockShift_of_weighted_stationary Q (fun c ↦ ε • b c),
    integral_map (measurable_legalPairMarkClockShift _ (fun c ↦ ε • b c)).aemeasurable
      hk.aestronglyMeasurable]
  have hread := D.ae_originalFocalKinetic_clockShift_scaled_expansion hF hw hbounds Q b ε
  have heq := integral_congr_ae hread
  change (∫ m, D.originalFocalKinetic gap m.1.1 m.1.2
    (legalPairMarkClockShift _ (fun c ↦ ε • b c) m).2
    ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) = _
  rw [heq]
  have hsplit := integral_add (Q.kinetic_integrable.add (hlin.const_mul ε)) (hquad.const_mul (ε ^ 2))
  have hsplit₀ := integral_add Q.kinetic_integrable (hlin.const_mul ε)
  simp only [Pi.add_apply] at hsplit hsplit₀
  rw [hsplit, hsplit₀, integral_const_mul, integral_const_mul]

/-- The paired-clock probe expectation is exactly unchanged on the actual
shifted true Palm, even when only its original integrability is available. -/
theorem integral_probe_clockShift_of_weighted_stationary
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    (b : Fin 2 → C(ℝ, Fin q → ℝ)) :
    (∫ m, g m.1.1 m.1.2 ∂legalMarkedJointPalm q (legalMarkedInputClockShiftLaw q b Q.law)) =
      ∫ m, g m.1.1 m.1.2 ∂legalMarkedJointPalm q Q.law := by
  rw [legalMarkedJointPalm_clockShift_of_weighted_stationary Q b]
  change (∫ m, g m.1.1 m.1.2
    ∂(legalMarkedJointPalm q Q.law).map (legalPairMarkClockShiftHomeomorph q b).toMeasurableEquiv) = _
  rw [integral_map_equiv]
  rfl

/-- The complete actual genuine competitor has the exact energy polynomial
for every real amplitude and probe tilt. No minimizing or centering assertion
is assumed or concluded. -/
theorem value_clockShiftWeightedStationaryMatching_scaled_polynomial
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap) (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (b : Fin 2 → C(ℝ, Fin (finrank ℝ S.covector.ker) → ℝ)) (ε t : ℝ) :
    (D.clockShiftWeightedStationaryMatching hF hw hgap hbounds Q (fun c ↦ ε • b c)).value t =
      Q.value t +
        ε * (∫ m, originalSeedPairMomentum S w m ⬝ᵥ legalPairClockShiftDifference _ b m
          ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) +
        ε ^ 2 * (∫ m, D.originalFocalKinetic gap m.1.1 m.1.2 (legalPairClockShiftDifference _ b m)
          ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) := by
  have hlaw : (D.clockShiftWeightedStationaryMatching hF hw hgap hbounds Q
      (fun c ↦ ε • b c)).law = legalMarkedInputClockShiftLaw _ (fun c ↦ ε • b c) Q.law := rfl
  unfold LegalWeightedStationaryPoissonMatching.value
  rw [hlaw, D.integral_originalFocalKinetic_clockShift_scaled_polynomial hF hw hgap hbounds Q b ε,
    integral_probe_clockShift_of_weighted_stationary Q (fun c ↦ ε • b c)]
  ring

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
