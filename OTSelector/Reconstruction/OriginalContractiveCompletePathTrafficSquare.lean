import OTSelector.Reconstruction.OriginalCompletePathEdgeTraffic
import OTSelector.MeasureTheory.Integral.ContractiveContributorBound

/-! Literal same-scene traffic-square control from actual contractive contributors. -/
open Set Function Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- Actual tube contributors turn the same original finite-count bound into a
literal weighted complete-path traffic bound. The field and curve inputs here
are intermediate geometric objects; no traffic-square estimate is assumed. -/
theorem legalMarkedCompletePathTraffic_sq_le_of_contractive_contributors
    {q : ℕ} {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [MeasurableSpace U] [BorelSpace U] [SecondCountableTopology U]
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ) (hd : Measurable d)
    {η : (Fin q → ℝ) → ℝ≥0∞} {f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞}
    (hη : Measurable η) (hf : Measurable f)
    (p : PhysicalPairPalmMark (Fin q) → U) (hp : Measurable p)
    (s : LegalMarkedOptimalInputScene q) (A : Set (LegalMarkedPhysicalEdge q))
    (hA : MeasurableSet A)
    (hfiniteCount : (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) A < ∞)
    (hfinite : legalMarkedCompletePathTraffic q d η f s ≠ ∞)
    (hzero : ∀ᵐ e ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q)),
      e ∉ A → legalMarkedCompletePathEdgeTraffic q d η f e = 0)
    (P : U → U) {L : ℝ} (hL : 0 ≤ L)
    (hP : ∀ x y, ‖P x - P y‖ ≤ L * ‖x - y‖)
    (R : ℝ → U →L[ℝ] U)
    (hsmall : ∀ t ∈ Icc (0 : ℝ) 1, ‖R t‖ * L ≤ (1 / 2 : ℝ))
    (z : LegalMarkedPhysicalEdge q → U) {a b : ℝ}
    (hlarge : 2 * (L * a + b) ≤ ‖P 0‖)
    (hcontributors : ∀ e ∈ A, ∃ t ∈ Icc (0 : ℝ) 1,
      ‖z e + R t (p (physicalPairAnchor e).2)‖ ≤ a ∧
        ‖p (physicalPairAnchor e).2 - P (z e)‖ ≤ b)
    {m B K C : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hbound : ∀ᵐ e ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q)).restrict A,
      (legalMarkedCompletePathEdgeTraffic q d η f e).toReal ≤ B)
    (hcount : (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).real A ≤ K * m)
    (hm : m ≤ C * ‖P 0‖) :
    (legalMarkedCompletePathTraffic q d η f s).toReal ^ 2 ≤
      3 * B * K * C * (legalMarkedCompletePathTraffic q d η
        (fun z ↦ ENNReal.ofReal ‖p z.1‖ * f z) s).toReal := by
  have hfiniteWeight : legalMarkedCompletePathTraffic q d η
      (fun z ↦ ENNReal.ofReal ‖p z.1‖ * f z) s ≠ ∞ := by
    apply (legalMarkedCompletePathTraffic_markWeight_lt_top_of_contributor_bound
      (H := 3 * ‖P 0‖) d hd hη hf (fun m ↦ ‖p m‖) hp.norm s A hfinite hzero ?_).ne
    filter_upwards [] with e he
    obtain ⟨t, ht, hphysical, hrough⟩ := hcontributors e he
    exact (original_phaseAmplitude_comparable_to_actualMomentum hL hP
      (hsmall t ht) hphysical hrough hlarge).2
  have hu := (measurable_legalMarkedCompletePathEdgeTraffic d hd hη hf).ennreal_toReal
  have hpu := integrable_legalMarkedCompletePathEdgeTraffic_markWeight
    d hd hη hf (fun m ↦ ‖p m‖) hp.norm (fun _ ↦ norm_nonneg _) s hfiniteWeight
  have hsq := setIntegral_traffic_sq_le_actual_momentum hA hfiniteCount hL hP R hsmall z
    (fun e ↦ p (physicalPairAnchor e).2) hlarge hcontributors hB hK hC hcount hm
    hu.aestronglyMeasurable.restrict
    (Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg) hbound hpu.integrableOn
  have huA : (∫ e in A, (legalMarkedCompletePathEdgeTraffic q d η f e).toReal
      ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q))) =
      (legalMarkedCompletePathTraffic q d η f s).toReal := by
    rw [toReal_legalMarkedCompletePathTraffic_eq_integral_edges d hd hη hf s hfinite]
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [hzero] with e he hnot
    rw [he hnot, ENNReal.toReal_zero]
  have hpA : (∫ e in A, ‖p (physicalPairAnchor e).2‖ *
      (legalMarkedCompletePathEdgeTraffic q d η f e).toReal
        ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q))) =
      (legalMarkedCompletePathTraffic q d η
        (fun z ↦ ENNReal.ofReal ‖p z.1‖ * f z) s).toReal := by
    rw [toReal_legalMarkedCompletePathTraffic_markWeight d hd hη hf
      (fun m ↦ ‖p m‖) hp.norm (fun _ ↦ norm_nonneg _) s hfiniteWeight]
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [hzero] with e he hnot
    rw [he hnot, ENNReal.toReal_zero, mul_zero]
  rw [huA, hpA] at hsq
  exact hsq.2

end OTSelector.Reconstruction
