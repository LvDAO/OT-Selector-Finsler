import OTSelector.Reconstruction.OriginalCompletePathTrafficSquare

/-! A nonzero literal original-edge clock integral produces an actual physical contributor. -/
open Set Function Filter MeasureTheory Matrix
open scoped ENNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000

/-- A nonzero actual per-edge integral internally produces a clock at which
both original factors are nonzero. No measurability premise is needed. -/
theorem legalMarkedCompletePathEdgeTraffic_ne_zero_exists_clock {q : ℕ}
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ)
    (η : (Fin q → ℝ) → ℝ≥0∞) (f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞)
    (e : LegalMarkedPhysicalEdge q)
    (he : legalMarkedCompletePathEdgeTraffic q d η f e ≠ 0) :
    ∃ c : ℝ, η (e.1.1 + d ((physicalPairAnchor e).2, c)) ≠ 0 ∧
      f ((physicalPairAnchor e).2, c) ≠ 0 := by
  have hex : ∃ c : ℝ, η (e.1.1 + d ((physicalPairAnchor e).2, c)) *
      f ((physicalPairAnchor e).2, c) ≠ 0 := by
    by_contra hn
    apply he
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [] with c
    exact not_ne_iff.mp (not_exists.mp hn c)
  obtain ⟨c, hc⟩ := hex
  exact ⟨c, (mul_ne_zero_iff.mp hc).1, (mul_ne_zero_iff.mp hc).2⟩

/-- The literal positive-contribution family has exactly zero traffic outside it. -/
theorem legalMarkedCompletePathContributors_outside_zero {q : ℕ}
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ)
    (η : (Fin q → ℝ) → ℝ≥0∞) (f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞)
    (e : LegalMarkedPhysicalEdge q)
    (he : e ∉ legalMarkedCompletePathContributors q d η f) :
    legalMarkedCompletePathEdgeTraffic q d η f e = 0 :=
  not_ne_iff.mp he

/-- Every literal positive contributor has an actual original contributing clock. -/
theorem legalMarkedCompletePathContributors_exists_clock {q : ℕ}
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ)
    (η : (Fin q → ℝ) → ℝ≥0∞) (f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞)
    (e : LegalMarkedPhysicalEdge q)
    (he : e ∈ legalMarkedCompletePathContributors q d η f) :
    ∃ c : ℝ, η (e.1.1 + d ((physicalPairAnchor e).2, c)) ≠ 0 ∧
      f ((physicalPairAnchor e).2, c) ≠ 0 :=
  legalMarkedCompletePathEdgeTraffic_ne_zero_exists_clock d η f e he

/-- Actual marked-clock support and the physical kernel window turn positive
traffic into a unit-clock contributor. No division by the clock scale is used. -/
theorem legalMarkedCompletePathEdgeTraffic_ne_zero_exists_affineWindow_contributor {q : ℕ}
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ)
    (η : (Fin q → ℝ) → ℝ≥0∞) (f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞)
    (T : Matrix (Fin q) (Fin q) ℝ) (c₀ ell : ℝ) (e : LegalMarkedPhysicalEdge q)
    (he : legalMarkedCompletePathEdgeTraffic q d η f e ≠ 0)
    (hclock : ∀ m c, f (m, c) ≠ 0 → ∃ r ∈ Icc (0 : ℝ) 1, c = c₀ + ell * r)
    {a : ℝ} (hηwindow : ∀ x, η x ≠ 0 → ‖T *ᵥ x‖ ≤ a) :
    ∃ r ∈ Icc (0 : ℝ) 1,
      η (e.1.1 + d ((physicalPairAnchor e).2, c₀ + ell * r)) ≠ 0 ∧
      f ((physicalPairAnchor e).2, c₀ + ell * r) ≠ 0 ∧
      ‖T *ᵥ (e.1.1 + d ((physicalPairAnchor e).2, c₀ + ell * r))‖ ≤ a := by
  obtain ⟨c, hηc, hfc⟩ :=
    legalMarkedCompletePathEdgeTraffic_ne_zero_exists_clock d η f e he
  obtain ⟨r, hr, hc⟩ := hclock (physicalPairAnchor e).2 c hfc
  refine ⟨r, hr, ?_, ?_, ?_⟩
  · simpa only [← hc] using hηc
  · simpa only [← hc] using hfc
  · simpa only [← hc] using hηwindow _ hηc

end OTSelector.Reconstruction
