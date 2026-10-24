import OTSelector.Reconstruction.OriginalReserveWindowConsistency

/-! The actual compact cutoff supplies the containing Poisson window and its spatial cover. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
local instance originalReserveWindowCoveredInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance originalReserveWindowCoveredPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- The containing window is produced by the same compact cutoff; its
geometric cover is retained rather than discarded from the readout certificate. -/
theorem map_originalInputRestriction_eq_originalPoisson_with_spatial_cover
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q))
    (hLaplace : ∀ S : ℝ, 0 < S →
      ∀ (F : C_c(LegalColoredInputPoint q, ℝ)) (hF : ∀ x, 0 ≤ F x),
      (∀ (x : LegalMarkedPhysicalPoint q) (c : Fin 2),
        x.1 ∉ haarRootCube (Fin q) S → F (x, c) = 0) →
      (∫ s, legalMarkedInputSceneLaplace q F hF s
        ∂(Q : Measure (LegalMarkedOptimalInputScene q))) =
        ∫ b, legalInputBlockLaplace (fun x ↦ F (x, 0)) (fun x ↦ F (x, 1)) b
          ∂legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β)
    {U : Set (LegalColoredInputPoint q)} (hU : IsCompact U) :
    ∃ S > 0,
      (∀ p ∈ U, p.1.1 ∈ haarRootCube (Fin q) S) ∧
      (Q : Measure (LegalMarkedOptimalInputScene q)).map
        (fun s ↦ (s.2 : Measure (LegalColoredInputPoint q)).restrict U) =
      (legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β).map
        (fun b ↦ (legalInputTwoBlockMeasure q b).restrict U) := by
  obtain ⟨η, hηU, hη⟩ := LocalFiniteMeasure.exists_compact_cutoff hU
  obtain ⟨S, hS, hbound⟩ := (η.hasCompactSupport.image
    (continuous_fst.comp continuous_fst)).isBounded.exists_pos_norm_lt
  have hηzero (x : LegalMarkedPhysicalPoint q) (c : Fin 2)
      (hx : x.1 ∉ haarRootCube (Fin q) S) : η (x, c) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hsupp
    apply hx
    have hn : ‖x.1‖ < S := hbound _ ⟨(x, c), hsupp, rfl⟩
    have hi (i : Fin q) : |x.1 i| ≤ S := by
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm x.1 i).trans hn.le
    exact ⟨fun i ↦ (abs_le.mp (hi i)).1, fun i ↦ (abs_le.mp (hi i)).2⟩
  have hvol : volume (haarRootCube (Fin q) S) ≠ 0 := by
    rw [volume_haarRootCube (Fin q) hS.le, Fintype.card_fin]
    exact (ENNReal.ofReal_pos.mpr (pow_pos (by positivity : 0 < 2 * S) q)).ne'
  have : IsProbabilityMeasure (legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β) :=
    isProbabilityMeasure_legalInputPoissonWindowLaw q hS.le measurableSet_Icc (Subset.refl _) hvol α β
  let P := (Q : Measure (LegalMarkedOptimalInputScene q)).map Prod.snd
  let P' := (legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β).map
    (legalInputTwoBlockLocal q)
  have : IsProbabilityMeasure P := by
    exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have : IsProbabilityMeasure P' := by
    exact Measure.isProbabilityMeasure_map (measurable_legalInputTwoBlockLocal q).aemeasurable
  have hLap : ∀ F : LegalNonnegativeInputTest (LegalColoredInputPoint q),
      (∫ μ, legalInputMeasureLaplace
        ⟨LocalFiniteMeasure.weightedContinuousTest F.1 η.toContinuousMap,
          fun x ↦ mul_nonneg (F.2 x) (hη x).1⟩ μ ∂P) =
      ∫ μ, legalInputMeasureLaplace
        ⟨LocalFiniteMeasure.weightedContinuousTest F.1 η.toContinuousMap,
          fun x ↦ mul_nonneg (F.2 x) (hη x).1⟩ μ ∂P' := by
    intro F
    let T : C_c(LegalColoredInputPoint q, ℝ) :=
      LocalFiniteMeasure.weightedContinuousTest F.1 η.toContinuousMap
    have hT (x) : 0 ≤ T x := mul_nonneg (F.2 x) (hη x).1
    have hTzero (x : LegalMarkedPhysicalPoint q) (c : Fin 2)
        (hx : x.1 ∉ haarRootCube (Fin q) S) : T (x, c) = 0 := by
      change F.1 (x, c) * η (x, c) = 0
      rw [hηzero x c hx, mul_zero]
    have hread := hLaplace S hS T hT hTzero
    change (∫ μ, legalInputMeasureLaplace ⟨T, hT⟩ μ ∂P) =
      ∫ μ, legalInputMeasureLaplace ⟨T, hT⟩ μ ∂P'
    dsimp only [P, P']
    rw [integral_map measurable_snd.aemeasurable
      (legalInputMeasureLaplace ⟨T, hT⟩).continuous.aestronglyMeasurable,
      integral_map (measurable_legalInputTwoBlockLocal q).aemeasurable
        (legalInputMeasureLaplace ⟨T, hT⟩).continuous.aestronglyMeasurable]
    change (∫ s, legalMarkedInputSceneLaplace q T hT s ∂(Q : Measure (LegalMarkedOptimalInputScene q))) = _
    rw [hread]
    apply integral_congr_ae
    exact .of_forall fun b ↦ by
      change Real.exp (-(legalInputBlockTest (fun x ↦ T (x, 0)) b.1 +
        legalInputBlockTest (fun x ↦ T (x, 1)) b.2)) =
          Real.exp (-(∫ x, T x ∂legalInputTwoBlockMeasure q b))
      rw [integral_legalInputTwoBlockMeasure]

  have hlocal := map_legalInput_restrict_eq_of_cutoff_laplace P P' η.toContinuousMap
    (fun x ↦ (hη x).1) hU.measurableSet hηU hLap
  have hr : Measurable (fun μ : LocalFiniteMeasure (LegalColoredInputPoint q) ↦
      (μ : Measure (LegalColoredInputPoint q)).restrict U) := by
    apply Measure.measurable_of_measurable_coe
    intro V hV
    simpa only [Measure.restrict_apply hV, Function.comp_def] using
      (Measure.measurable_coe (hV.inter hU.measurableSet)).comp measurable_localFiniteMeasure_coe
  have hcover : ∀ p ∈ U, p.1.1 ∈ haarRootCube (Fin q) S := by
    intro p hp
    by_contra hn
    have hz := hηzero p.1 p.2 hn
    have ho : η p = 1 := hηU hp
    exact zero_ne_one (hz.symm.trans ho)
  refine ⟨S, hS, hcover, ?_⟩
  simpa only [P, P', Measure.map_map hr measurable_snd,
    Measure.map_map hr (measurable_legalInputTwoBlockLocal q),
    Function.comp_def, legalInputTwoBlockLocal] using hlocal

end OTSelector.Reconstruction
