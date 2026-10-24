import OTSelector.Reconstruction.OriginalCompletePathEdgeTraffic

/-! A literal original per-edge traffic upper bound gives the corresponding
actual first-plan count upper bound, with no replacement point process. -/
open Set Function MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction

theorem legalMarkedCompletePathTraffic_le_bound_mul_count {q : ℕ}
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ) (hd : Measurable d)
    {η : (Fin q → ℝ) → ℝ≥0∞} {f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞}
    (hη : Measurable η) (hf : Measurable f)
    (s : LegalMarkedOptimalInputScene q) (V : Set (LegalMarkedPhysicalEdge q))
    (hfiniteV : (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) V < (⊤ : ℝ≥0∞))
    (hfinite : legalMarkedCompletePathTraffic q d η f s ≠ (⊤ : ℝ≥0∞))
    (hzero : ∀ᵐ e ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q)),
      e ∉ V → legalMarkedCompletePathEdgeTraffic q d η f e = 0)
    {B : ℝ} (hbound : ∀ᵐ e ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q)).restrict V,
      (legalMarkedCompletePathEdgeTraffic q d η f e).toReal ≤ B) :
    (legalMarkedCompletePathTraffic q d η f s).toReal ≤
      B * (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).real V := by
  have hi := integrable_toReal_legalMarkedCompletePathEdgeTraffic d hd hη hf s hfinite
  have hconst : IntegrableOn (fun _ : LegalMarkedPhysicalEdge q ↦ B) V
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) := integrableOn_const hfiniteV.ne
  have heq : (legalMarkedCompletePathTraffic q d η f s).toReal =
      ∫ e in V, (legalMarkedCompletePathEdgeTraffic q d η f e).toReal
        ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q)) := by
    rw [toReal_legalMarkedCompletePathTraffic_eq_integral_edges d hd hη hf s hfinite]
    symm
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [hzero] with e he hnot
    rw [he hnot, ENNReal.toReal_zero]
  rw [heq]
  calc
    _ ≤ ∫ _ in V, B ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q)) :=
      integral_mono_ae hi.integrableOn hconst hbound
    _ = _ := by rw [setIntegral_const]; simp only [smul_eq_mul]; ring

end OTSelector.Reconstruction
