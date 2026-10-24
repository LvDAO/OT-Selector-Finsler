import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.MeasureTheory.IntegralGapBound
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerOriginalClockGap.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerOriginalClockGap`; the selected original proof blocks follow. -/
section

/-!
# Transport.Calibration.CompactClockGap

* **Conditions:** Disjoint compact source/target carriers and a 1-Lipschitz potential; the energy bound concerns finite plans carried there and explicitly integrable scaled slack.
* **Objects:** A positive support gap, a measurable insufficient-clock-separation event, its slack–mass bound and vanishing mass when the scale diverges under bounded energy.
* **Proof detail:** Minimize distance on the compact product, obtain slack ≥ gap/2 on the bad event, integrate this pointwise inequality, and divide by the positive diverging scale.

Mathematical sources:
- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).
- [Rick Durrett, Probability: Theory and Examples, 5th edition (11 January 2019)](https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=37): Section 1.6.1, Theorem 1.6.4 and equation (1.6.1), pp. 29–30.

Source relation (derived): A generic compact-separation and Markov-type estimate. It uses distance slack, without a transverse Hessian or focal-coefficient assumption.
-/

/-!
# Legal clock concentration from the original disjoint supports

A positive original support distance, rather than a local quadratic lower
bound, controls edges whose potential clocks are insufficiently separated.
The estimate applies to every finite plan carried by the two supports and
therefore to the whole original optimal face and to allocation couplings.
-/

open Set MeasureTheory Manifold Filter OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace OTSelector.Reconstruction

section Metric

variable {M : Type*} [MetricSpace M]

/-- Disjoint compact carriers supply a uniform positive distance threshold,
including when one of the carriers is empty. -/
theorem exists_original_support_gap {A B : Set M}
    (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B) :
    ∃ gap : ℝ, 0 < gap ∧ ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y := by
  obtain ⟨gap, hgap, hdist⟩ := Metric.exists_pos_forall_lt_edist hA hB.isClosed hAB
  refine ⟨gap, by exact_mod_cast hgap, ?_⟩
  intro x hx y hy
  have h : gap < nndist x y := by
    exact ENNReal.coe_lt_coe.mp (by simpa only [edist_nndist] using hdist x hx y hy)
  exact (show (gap : ℝ) < dist x y by exact_mod_cast h).le

/-- The original clock pairs that have not attained half the support gap. -/
def originalClockBadEvent (u : M → ℝ) (gap : ℝ) : Set (M × M) :=
  {p | u p.2 - u p.1 ≤ gap / 2}

variable [MeasurableSpace M] [BorelSpace M]

/-- The bad-clock event is measurable for the original Lipschitz potential. -/
theorem measurableSet_originalClockBadEvent {u : M → ℝ}
    (hu : LipschitzWith 1 u) (gap : ℝ) :
    MeasurableSet (originalClockBadEvent u gap) :=
  measurableSet_le ((hu.continuous.measurable.comp measurable_snd).sub
    (hu.continuous.measurable.comp measurable_fst)) measurable_const

omit [MeasurableSpace M] [BorelSpace M] in
/-- The genuine distance slack is nonnegative under the global calibration. -/
theorem originalDistanceSlack_nonneg {u : M → ℝ} (hu : LipschitzWith 1 u) (x y : M) :
    0 ≤ dist x y - u y + u x := by
  have h := hu.dist_le_mul y x
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
  rw [dist_comm y x] at h
  have hb := (le_abs_self (u y - u x)).trans h
  linarith

omit [MeasurableSpace M] [BorelSpace M] in
/-- An insufficient original clock gap costs at least half the actual support
distance. No displacement coercivity or curvature assumption is used. -/
theorem originalClockBadEvent_slack_gap {A B : Set M} {gap : ℝ}
    (hgap : ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    {u : M → ℝ} {x y : M} (hx : x ∈ A) (hy : y ∈ B)
    (hbad : (x, y) ∈ originalClockBadEvent u gap) :
    gap / 2 ≤ dist x y - u y + u x := by
  have hd := hgap x hx y hy
  change u y - u x ≤ gap / 2 at hbad
  linarith

/-- Every actual finite plan has a quantitative bad-clock mass bound from its
scaled slack energy. The plan need not be optimal or admit a density. -/
theorem originalClockBadEvent_mass_mul_le_energy
    (Γ : Measure (M × M)) [IsFiniteMeasure Γ]
    {A B : Set M} {gap scale : ℝ} (hscale : 0 ≤ scale)
    (hgap : ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hcarried : ∀ᵐ p ∂Γ, p.1 ∈ A ∧ p.2 ∈ B)
    {u : M → ℝ} (hu : LipschitzWith 1 u)
    (henergy : Integrable (fun p : M × M ↦ scale * (dist p.1 p.2 - u p.2 + u p.1)) Γ) :
    (scale * (gap / 2)) * Γ.real (originalClockBadEvent u gap) ≤
      ∫ p, scale * (dist p.1 p.2 - u p.2 + u p.1) ∂Γ := by
  apply Probability.measureReal_le_integral_of_gap Γ _ _
    (measurableSet_originalClockBadEvent hu gap) henergy
  · exact Filter.Eventually.of_forall fun p ↦
      mul_nonneg hscale (originalDistanceSlack_nonneg hu p.1 p.2)
  · filter_upwards [hcarried] with p hp hbad
    exact mul_le_mul_of_nonneg_left
      (originalClockBadEvent_slack_gap hgap hp.1 hp.2 hbad) hscale

/-- A uniform scaled-energy bound forces the bad-clock mass to vanish as the
scaling diverges. This also applies to averaged physical plans. -/
theorem tendsto_originalClockBadEvent_mass_zero
    (Γ : ℕ → Measure (M × M)) [∀ n, IsFiniteMeasure (Γ n)]
    {A B : Set M} {gap C : ℝ} (hgap : 0 < gap)
    (hdist : ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hcarried : ∀ n, ∀ᵐ p ∂Γ n, p.1 ∈ A ∧ p.2 ∈ B)
    {u : M → ℝ} (hu : LipschitzWith 1 u)
    (scale : ℕ → ℝ) (hscale : ∀ n, 0 < scale n)
    (hscaleTop : Tendsto scale atTop atTop)
    (hint : ∀ n, Integrable
      (fun p : M × M ↦ scale n * (dist p.1 p.2 - u p.2 + u p.1)) (Γ n))
    (hbound : ∀ n, (∫ p, scale n * (dist p.1 p.2 - u p.2 + u p.1) ∂Γ n) ≤ C) :
    Tendsto (fun n ↦ (Γ n).real (originalClockBadEvent u gap)) atTop (𝓝 0) := by
  have hupper (n : ℕ) :
      (Γ n).real (originalClockBadEvent u gap) ≤ (C / (gap / 2)) / scale n := by
    have h := (originalClockBadEvent_mass_mul_le_energy (Γ n) (hscale n).le
      hdist (hcarried n) hu (hint n)).trans (hbound n)
    apply (le_div_iff₀ (hscale n)).mpr
    apply (le_div_iff₀ (half_pos hgap)).mpr
    nlinarith only [h]
  exact squeeze_zero (fun _ ↦ measureReal_nonneg) hupper
    (hscaleTop.const_div_atTop (C / (gap / 2)))

end Metric

section Finsler

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] {F : ContinuousFinslerNorm E M}

/-- The original Finsler supports produce one positive threshold controlling
all finite physical plans, with the cost still the original length distance. -/
theorem exists_finsler_originalClockBadEvent_mass_bound
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B) :
    let _instOriginalClockMetric : MetricSpace M := F.metricSpace
    ∃ gap : ℝ, 0 < gap ∧ ∀ (u : M → ℝ), LipschitzWith 1 u →
      ∀ (Γ : Measure (M × M)) [IsFiniteMeasure Γ],
        (∀ᵐ p ∂Γ, p.1 ∈ A ∧ p.2 ∈ B) →
        ∀ scale : ℝ, 0 ≤ scale →
          Integrable (fun p : M × M ↦ scale *
            ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1)) Γ →
          (scale * (gap / 2)) * Γ.real (originalClockBadEvent u gap) ≤
            ∫ p, scale * ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1) ∂Γ := by
  let _instOriginalClockProofMetric : MetricSpace M := F.metricSpace
  obtain ⟨gap, hg, hdist⟩ := exists_original_support_gap hA hB hAB
  refine ⟨gap, hg, ?_⟩
  intro u hu Γ _ hcarried scale hscale hint
  simpa only [F.metricSpace_dist] using
    originalClockBadEvent_mass_mul_le_energy Γ hscale hdist hcarried hu
      (by simpa only [F.metricSpace_dist] using hint)

end Finsler
end OTSelector.Reconstruction

end
end
