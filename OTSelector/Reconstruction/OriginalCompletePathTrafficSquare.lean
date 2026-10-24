import OTSelector.Reconstruction.OriginalCompletePathEdgeTraffic
import OTSelector.MeasureTheory.Integral.BoundedWeightedCount

/-! Literal scene traffic-square control from the original contributor count and edge weights. -/
open Set Function Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- A same-scene finite contributor count and its actual edgewise momentum comparison
control the square of literal complete-path traffic by momentum-weighted literal traffic.
The count, bounded occupation and pointwise weight are geometric intermediate inputs. -/
theorem legalMarkedCompletePathTraffic_sq_le_of_count_weight {q : ℕ}
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ) (hd : Measurable d)
    {η : (Fin q → ℝ) → ℝ≥0∞} {f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞}
    (hη : Measurable η) (hf : Measurable f)
    (p : PhysicalPairPalmMark (Fin q) → ℝ) (hp : Measurable p) (hp0 : ∀ m, 0 ≤ p m)
    (s : LegalMarkedOptimalInputScene q) (V : Set (LegalMarkedPhysicalEdge q))
    (hfiniteCount : (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) V < ∞)
    (hfinite : legalMarkedCompletePathTraffic q d η f s ≠ ∞)
    (hfiniteWeight : legalMarkedCompletePathTraffic q d η
      (fun z ↦ ENNReal.ofReal (p z.1) * f z) s ≠ ∞)
    (hzero : ∀ᵐ e ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q)),
      e ∉ V → legalMarkedCompletePathEdgeTraffic q d η f e = 0)
    {B K W C : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hbound : ∀ᵐ e ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q)).restrict V,
      (legalMarkedCompletePathEdgeTraffic q d η f e).toReal ≤ B)
    (hcount : (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).real V ≤ K * W)
    (hweight : ∀ᵐ e ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q)).restrict V,
      W ≤ C * p (physicalPairAnchor e).2) :
    (legalMarkedCompletePathTraffic q d η f s).toReal ^ 2 ≤
      B * K * C * (legalMarkedCompletePathTraffic q d η
        (fun z ↦ ENNReal.ofReal (p z.1) * f z) s).toReal := by
  have hu := (measurable_legalMarkedCompletePathEdgeTraffic d hd hη hf).ennreal_toReal
  have hpu := integrable_legalMarkedCompletePathEdgeTraffic_markWeight
    d hd hη hf p hp hp0 s hfiniteWeight
  have hsq := setIntegral_sq_le_of_count_and_pointwise_weight hfiniteCount
    hu.aestronglyMeasurable.restrict hB hK
    (Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg) hbound hcount hweight
    hpu.integrableOn
  have huV : (∫ e in V, (legalMarkedCompletePathEdgeTraffic q d η f e).toReal
      ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q))) =
      (legalMarkedCompletePathTraffic q d η f s).toReal := by
    rw [toReal_legalMarkedCompletePathTraffic_eq_integral_edges d hd hη hf s hfinite]
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [hzero] with e he hnot
    rw [he hnot, ENNReal.toReal_zero]
  have hpV : (∫ e in V, p (physicalPairAnchor e).2 *
      (legalMarkedCompletePathEdgeTraffic q d η f e).toReal
        ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q))) =
      (legalMarkedCompletePathTraffic q d η
        (fun z ↦ ENNReal.ofReal (p z.1) * f z) s).toReal := by
    rw [toReal_legalMarkedCompletePathTraffic_markWeight d hd hη hf p hp hp0 s hfiniteWeight]
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [hzero] with e he hnot
    rw [he hnot, ENNReal.toReal_zero, mul_zero]
  rw [huV, hpV] at hsq
  exact hsq.2

/-- The literal family of original edges with nonzero complete-path occupation. -/
def legalMarkedCompletePathContributors (q : ℕ)
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ)
    (η : (Fin q → ℝ) → ℝ≥0∞) (f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞) :
    Set (LegalMarkedPhysicalEdge q) :=
  {e | legalMarkedCompletePathEdgeTraffic q d η f e ≠ 0}

theorem measurableSet_legalMarkedCompletePathContributors {q : ℕ}
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ) (hd : Measurable d)
    {η : (Fin q → ℝ) → ℝ≥0∞} {f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞}
    (hη : Measurable η) (hf : Measurable f) :
    MeasurableSet (legalMarkedCompletePathContributors q d η f) :=
  (measurableSet_singleton (0 : ℝ≥0∞)).compl.preimage
    (measurable_legalMarkedCompletePathEdgeTraffic d hd hη hf)

/-- The literal positive-contribution family needs no supplied outside-zero premise. -/
theorem legalMarkedCompletePathTraffic_sq_le_of_contributor_count_weight {q : ℕ}
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ) (hd : Measurable d)
    {η : (Fin q → ℝ) → ℝ≥0∞} {f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞}
    (hη : Measurable η) (hf : Measurable f)
    (p : PhysicalPairPalmMark (Fin q) → ℝ) (hp : Measurable p) (hp0 : ∀ m, 0 ≤ p m)
    (s : LegalMarkedOptimalInputScene q)
    (hfiniteCount : (s.1.1 : Measure (LegalMarkedPhysicalEdge q))
      (legalMarkedCompletePathContributors q d η f) < ∞)
    (hfinite : legalMarkedCompletePathTraffic q d η f s ≠ ∞)
    (hfiniteWeight : legalMarkedCompletePathTraffic q d η
      (fun z ↦ ENNReal.ofReal (p z.1) * f z) s ≠ ∞)
    {B K W C : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hbound : ∀ᵐ e ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q)).restrict
      (legalMarkedCompletePathContributors q d η f),
      (legalMarkedCompletePathEdgeTraffic q d η f e).toReal ≤ B)
    (hcount : (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).real
      (legalMarkedCompletePathContributors q d η f) ≤ K * W)
    (hweight : ∀ᵐ e ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q)).restrict
      (legalMarkedCompletePathContributors q d η f),
      W ≤ C * p (physicalPairAnchor e).2) :
    (legalMarkedCompletePathTraffic q d η f s).toReal ^ 2 ≤
      B * K * C * (legalMarkedCompletePathTraffic q d η
        (fun z ↦ ENNReal.ofReal (p z.1) * f z) s).toReal := by
  apply legalMarkedCompletePathTraffic_sq_le_of_count_weight d hd hη hf p hp hp0 s
    (legalMarkedCompletePathContributors q d η f)
    hfiniteCount hfinite hfiniteWeight ?_ hB hK hbound hcount hweight
  filter_upwards [] with e he
  exact not_ne_iff.mp he

end OTSelector.Reconstruction
