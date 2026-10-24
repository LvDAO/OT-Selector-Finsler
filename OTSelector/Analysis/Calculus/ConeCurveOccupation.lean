import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Analysis.Calculus.ConeCurveOccupation

Conditions: A differentiable normed-space curve has velocity in a quarter-radius cone around a fixed nonzero vector on the relevant interval.

Objects: Chord lower bound, speed upper bound, and a bound on time spent by two endpoints in a ball.

Proof detail: Integrate or apply the mean-value norm bound to curve minus its reference line, then use the reverse triangle inequality and the ball diameter.

## Mathematical sources

- [Jiří Lebl, Basic Analysis II](https://www.jirka.org/ra/realanal2.pdf#page=46): Section 8.4.1, Lemma 8.4.1 and Proposition 8.4.2, pp. 46–47.
- [Jiří Lebl, Basic Analysis I](https://www.jirka.org/ra/realanal.pdf#page=200): Section 5.3.1, Theorem 5.3.1, pp. 200–201.

Source relation: Cone estimates derived from the vector mean-value inequality; the quarter-cone constants are proved locally.
-/

/-!
# Actual cone curves spend uniformly bounded time in a ball

Velocity in a fixed quarter cone gives a quantitative lower bound on every
chord. Thus all times at which the original path meets a physical ball have
bounded diameter and bounded Lebesgue measure. No change of spatial coordinates
is used.
-/

open Set MeasureTheory
open scoped Topology
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A quarter-cone velocity field gives an actual quantitative lower bound on every chord. -/
theorem coneCurve_chord_lower {X dX : ℝ → V} {v : V} {I : Set ℝ}
    (hI : Convex ℝ I) (hX : ∀ t ∈ I, HasDerivAt X (dX t) t)
    (hcone : ∀ t ∈ I, ‖dX t - v‖ ≤ ‖v‖ / 4)
    {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I) :
    (3 / 4 : ℝ) * ‖v‖ * |b - a| ≤ ‖X b - X a‖ := by
  have herr : ‖(X b - b • v) - (X a - a • v)‖ ≤ (‖v‖ / 4) * |b - a| := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply, id_eq] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun t ht ↦ ((hX t ht).sub ((hasDerivAt_id t).smul_const v)).hasDerivWithinAt)
        (fun t ht ↦ by simpa only [one_smul] using hcone t ht) hI ha hb
  have heq : (b - a) • v = (X b - X a) - ((X b - b • v) - (X a - a • v)) := by
    simp only [sub_smul]
    abel
  have hnorm := norm_sub_le (X b - X a) ((X b - b • v) - (X a - a • v))
  rw [← heq, norm_smul, Real.norm_eq_abs] at hnorm
  nlinarith

/-- Every actual velocity in that cone is at most five quarters of the reference speed. -/
theorem coneCurve_speed_upper {dX : ℝ → V} {v : V} {I : Set ℝ}
    (hcone : ∀ t ∈ I, ‖dX t - v‖ ≤ ‖v‖ / 4) {t : ℝ} (ht : t ∈ I) :
    ‖dX t‖ ≤ (5 / 4 : ℝ) * ‖v‖ := by
  have hh := norm_le_norm_sub_add (dX t) v
  have h := hcone t ht
  nlinarith

/-- Time spent in the unchanged physical radius-R ball is bounded by its cone chord. -/
theorem coneCurve_ball_time_le {X dX : ℝ → V} {v : V} {I : Set ℝ}
    (hI : Convex ℝ I) (hX : ∀ t ∈ I, HasDerivAt X (dX t) t)
    (hcone : ∀ t ∈ I, ‖dX t - v‖ ≤ ‖v‖ / 4) (hv : 0 < ‖v‖)
    {R : ℝ} (_hR : 0 ≤ R) :
    volume (I ∩ {t | ‖X t‖ ≤ R}) ≤ ENNReal.ofReal (2 * R / ((3 / 4 : ℝ) * ‖v‖)) := by
  apply (Real.volume_le_diam _).trans
  apply Metric.ediam_le_of_forall_dist_le
  intro a ha b hb
  rw [Real.dist_eq]
  apply (le_div_iff₀ (by positivity : 0 < (3 / 4 : ℝ) * ‖v‖)).mpr
  have hlower := coneCurve_chord_lower hI hX hcone hb.1 ha.1
  have hupper := (norm_sub_le (X a) (X b)).trans (add_le_add ha.2 hb.2)
  nlinarith

end OTSelector.Reconstruction
