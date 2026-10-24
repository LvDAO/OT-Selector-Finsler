import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalFocalPathMoment
import OTSelector.MeasureTheory.LocalFiniteMeasureProbability

/-!
# Uniform original first moments for the stationary direct method

The original inverse-compliance moment bound depends only on the two fixed
clock populations. Every genuine original weighted matching consequently has
a displacement first moment bounded by its actual kinetic mean plus the same
fixed geometric constant. Compact original clock supports extend the bound
to the whole true Palm mark, giving genuine tightness for bounded energy.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical
noncomputable section
namespace OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- Uniform actual first moments imply tightness in every proper normed
space. The measures need only be finite, and the index set is arbitrary. -/
theorem isTightMeasureSet_of_uniform_integral_norm_bound
    {X J : Type*} [NormedAddCommGroup X] [ProperSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : J → Measure X) [∀ j, IsFiniteMeasure (μ j)]
    (hI : ∀ j, Integrable (fun x : X ↦ ‖x‖) (μ j))
    (B : ℝ) (hB : ∀ j, (∫ x : X, ‖x‖ ∂μ j) ≤ B) :
    IsTightMeasureSet (range μ) := by
  apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
  intro ε hε
  obtain ⟨δ, hδ0, hδ, hδε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
  have hδpos : 0 < δ := ENNReal.ofReal_pos.mp hδ
  let R := (|B| + 1) / δ
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨Metric.closedBall (0 : X) R, isCompact_closedBall _ _, ?_⟩
  rintro _ ⟨j, rfl⟩
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (μ := μ j) (.of_forall (fun x : X ↦ norm_nonneg x)) (hI j) R
  have hsub : (Metric.closedBall (0 : X) R)ᶜ ⊆ {x : X | R ≤ ‖x‖} := by
    intro x hx
    have hxR : ¬‖x‖ ≤ R := by
      simpa only [mem_compl_iff, Metric.mem_closedBall, dist_zero_right] using hx
    exact (lt_of_not_ge hxR).le
  have hprob : (μ j).real (Metric.closedBall (0 : X) R)ᶜ ≤ δ := by
    have hmul : R * (μ j).real (Metric.closedBall (0 : X) R)ᶜ ≤ B :=
      (mul_le_mul_of_nonneg_left (measureReal_mono hsub) hR.le).trans (hmark.trans (hB j))
    have heq : R * δ = |B| + 1 := by dsimp [R]; field_simp
    nlinarith [le_abs_self B]
  exact (show (μ j) (Metric.closedBall (0 : X) R)ᶜ ≤ ENNReal.ofReal δ by
    simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
      ENNReal.ofReal_le_ofReal hprob).trans hδε.le

end OTSelector.Probability
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- One original marginal-compliance constant bounds the actual inverse
coefficient mean for every genuine original weighted matching. -/
theorem exists_uniform_inverse_coefficient_mean_bound
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) :
    ∃ C ≥ 0, ∀ {gap : ℝ} {g : ℝ → ℝ → ℝ}
      (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
        (D.originalFocalKinetic gap) g),
      Integrable (fun m ↦ ‖(originalSeedPairCoefficient S w m.1)⁻¹‖)
        (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ∧
      (∫ m, ‖(originalSeedPairCoefficient S w m.1)⁻¹‖
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≤ C := by
  let root := (D.lo + D.hi) / 2
  have hroot : root ∈ Ioo D.lo D.hi :=
    ⟨by dsimp [root]; linarith [D.support.lt], by dsimp [root]; linarith [D.support.lt]⟩
  let C := (∫ x, ‖∫ t in root..(x - S.level), originalSeedKernel S w t‖ ∂μ) +
    ∫ y, ‖∫ t in root..(y - S.level), originalSeedKernel S w t‖ ∂ν
  have hC : 0 ≤ C := add_nonneg (integral_nonneg (fun _ ↦ norm_nonneg _))
    (integral_nonneg (fun _ ↦ norm_nonneg _))
  refine ⟨C, hC, fun {gap} {g} Q ↦ ?_⟩
  let η := legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law
  let π : Measure (ℝ × ℝ) := η.map Prod.fst
  have hπ : Vlasov.IsCoupling π μ ν := by
    constructor
    · rw [show π.map Prod.fst = η.map (fun m ↦ m.1.1) from
        Measure.map_map measurable_fst measurable_fst]
      exact Q.source_clock
    · rw [show π.map Prod.snd = η.map (fun m ↦ m.1.2) from
        Measure.map_map measurable_snd measurable_fst]
      exact Q.target_clock
  have hforward : ∀ᵐ p ∂π, p.1 < p.2 :=
    (ae_map_iff measurable_fst.aemeasurable
      (measurableSet_lt measurable_fst measurable_snd)).mpr Q.ae_palm_forward
  have hmeas := (measurable_real_matrix_inverse.comp
    (measurable_originalSeedPairCoefficient S hF hw)).norm
  have hI := D.integrable_inverse_pair_coefficient hF hw hroot hπ hforward
  have hmean := (D.paired_inverse_coefficient_moments hF hw hroot hπ hforward
    (r := 1) zero_lt_one (by norm_num)).2
  have hIη : Integrable (fun m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦
      ‖(originalSeedPairCoefficient S w m.1)⁻¹‖) η :=
    (integrable_map_measure hmeas.aestronglyMeasurable measurable_fst.aemeasurable).mp hI.norm
  refine ⟨hIη, ?_⟩
  have heq := integral_map (μ := η) measurable_fst.aemeasurable hmeas.aestronglyMeasurable
  simp only [Function.comp_def] at heq
  change (∫ m, ‖(originalSeedPairCoefficient S w m.1)⁻¹‖ ∂η) ≤ C
  rw [← heq]
  simpa only [Real.rpow_one, sub_self, max_self, Real.rpow_zero, one_mul] using hmean

/-- The original geometric constant bounds actual mean displacement for all
original genuine competitors, with their kinetic expectation kept literal. -/
theorem exists_uniform_displacement_firstMoment_bound
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter) :
    ∃ C ≥ 0, ∀ {g : ℝ → ℝ → ℝ}
      (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
        (D.originalFocalKinetic gap) g),
      (∫ m, ‖m.2‖ ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≤
        (∫ m, D.originalFocalKinetic gap m.1.1 m.1.2 m.2
          ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) + C := by
  obtain ⟨C, hC, hCI⟩ := D.exists_uniform_inverse_coefficient_mean_bound hF hw
  refine ⟨C, hC, fun {g} Q ↦ ?_⟩
  let η := legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law
  have hdisp := (D.integrable_displacement_of_original_weighted_stationary hF hw hbounds Q).2
  obtain ⟨hI, hmean⟩ := hCI Q
  have ha : ∀ᵐ m ∂η, m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m.1.1 ∈ μ.support := by
    have h : ∀ᵐ a ∂η.map (fun m ↦ m.1.1),
        a - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ a ∈ μ.support := by
      rw [Q.source_clock]
      exact D.support.source.ae_open.and μ.support_mem_ae
    exact ae_of_ae_map measurable_fst.fst.aemeasurable h
  have hb : ∀ᵐ m ∂η, m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m.1.2 ∈ ν.support := by
    have h : ∀ᵐ a ∂η.map (fun m ↦ m.1.2),
        a - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ a ∈ ν.support := by
      rw [Q.target_clock]
      exact D.support.target.ae_open.and ν.support_mem_ae
    exact ae_of_ae_map measurable_fst.snd.aemeasurable h
  have hbound : ∀ᵐ m ∂η, ‖m.2‖ ≤ D.originalFocalKinetic gap m.1.1 m.1.2 m.2 +
      ‖(originalSeedPairCoefficient S w m.1)⁻¹‖ := by
    filter_upwards [ha, hb, Q.ae_palm_forward] with m ha hb hf
    rw [D.originalFocalKinetic_eq_of_original_support hbounds ha hb hf]
    exact norm_le_matrixQuadratic_add_inverse_norm
      (D.pair_compliance_posDef hF hw ha.1 hb.1 hf).2 m.2
  calc
    _ ≤ ∫ m, D.originalFocalKinetic gap m.1.1 m.1.2 m.2 +
        ‖(originalSeedPairCoefficient S w m.1)⁻¹‖ ∂η :=
      integral_mono_ae hdisp (Q.kinetic_integrable.add hI) hbound
    _ = (∫ m, D.originalFocalKinetic gap m.1.1 m.1.2 m.2 ∂η) +
        ∫ m, ‖(originalSeedPairCoefficient S w m.1)⁻¹‖ ∂η :=
      integral_add Q.kinetic_integrable hI
    _ ≤ _ := add_le_add le_rfl hmean

/-- Compact original clock supports extend the same mean estimate to the
entire true paired-clock/full-displacement Palm mark, uniformly over all
genuine original competitors and without a second displacement moment. -/
theorem exists_uniform_wholePalm_firstMoment_bound
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter) :
    ∃ C ≥ 0, ∀ {g : ℝ → ℝ → ℝ}
      (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
        (D.originalFocalKinetic gap) g),
      Integrable (fun m ↦ ‖m‖) (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ∧
      (∫ m, ‖m‖ ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≤
        (∫ m, D.originalFocalKinetic gap m.1.1 m.1.2 m.2
          ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) + C := by
  obtain ⟨C, hC, hdisp⟩ := D.exists_uniform_displacement_firstMoment_bound hF hw hbounds
  obtain ⟨T, hT, hclock⟩ := (hbounds.source_compact.union hbounds.target_compact).isBounded.exists_pos_norm_lt
  refine ⟨T + C, add_nonneg hT.le hC, fun {g} Q ↦ ?_⟩
  let η := legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law
  have : IsProbabilityMeasure η := Q.palm_probability
  have hs : ∀ᵐ m ∂η, m.1.1 ∈ μ.support := by
    have h : ∀ᵐ a ∂η.map (fun m ↦ m.1.1), a ∈ μ.support := by
      rw [Q.source_clock]
      exact μ.support_mem_ae
    exact ae_of_ae_map measurable_fst.fst.aemeasurable h
  have ht : ∀ᵐ m ∂η, m.1.2 ∈ ν.support := by
    have h : ∀ᵐ a ∂η.map (fun m ↦ m.1.2), a ∈ ν.support := by
      rw [Q.target_clock]
      exact ν.support_mem_ae
    exact ae_of_ae_map measurable_fst.snd.aemeasurable h
  have hpoint : ∀ᵐ m ∂η, ‖m‖ ≤ T + ‖m.2‖ := by
    filter_upwards [hs, ht] with m hs ht
    have hsT : ‖m.1.1‖ ≤ T := (hclock _ (Or.inl hs)).le
    have htT : ‖m.1.2‖ ≤ T := (hclock _ (Or.inr ht)).le
    rw [Prod.norm_def, Prod.norm_def]
    apply max_le
    · exact (max_le hsT htT).trans (le_add_of_nonneg_right (norm_nonneg _))
    · exact le_add_of_nonneg_left hT.le
  have hdispI := (D.integrable_displacement_of_original_weighted_stationary hF hw hbounds Q).2
  have hwholeI : Integrable (fun m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦ ‖m‖) η := by
    apply ((integrable_const T).add hdispI).mono' measurable_id.norm.aestronglyMeasurable
    filter_upwards [hpoint] with m hm
    simpa only [Real.norm_eq_abs, abs_norm, id_eq, Pi.add_apply] using hm
  refine ⟨hwholeI, ?_⟩
  calc
    _ ≤ ∫ m, T + ‖m.2‖ ∂η := integral_mono_ae hwholeI ((integrable_const T).add hdispI) hpoint
    _ = T + ∫ m, ‖m.2‖ ∂η := by
      rw [integral_add (integrable_const T) hdispI]
      simp only [integral_const, probReal_univ, one_smul]
      rfl
    _ ≤ T + ((∫ m, D.originalFocalKinetic gap m.1.1 m.1.2 m.2 ∂η) + C) :=
      add_le_add le_rfl (hdisp Q)
    _ = _ := by ring

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
