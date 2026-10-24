import Mathlib.MeasureTheory.Function.JacobianOneDim
import OTSelector.MeasureTheory.Measure.ChangeOfDensity
import OTSelector.MeasureTheory.NormalizedLabelClockDensity

/-!
Conditions: A finite original joint label-clock law with its exact product-reference density, measurable section data and the stated a.e. equality to an interval-supported real density after each label-dependent clock shift.

Objects: The actual shifted conditional law as a restricted real density divided by its proved positive finite normalizer.

Proof detail: Use translation invariance of Lebesgue measure to shift the density, identify the actual conditional joint-density formula and convert its positive finite normalization to real division.

References: D. H. Fremlin: 452M–452N, pp. 25–26: product disintegration and the standard Borel target corollary; D. H. Fremlin: Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
Relation: A clock-shift/normalization consequence of an already established original joint density. It assumes the displayed section identity and does not serve as an oracle for a missing geometric Jacobi formula.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.ConditionalJacobiClockNormalization.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.ConditionalJacobiClockNormalization`; the selected original proof blocks follow. -/
section

/-!
# Original conditional clock normalization in the same family time

The potential clock and the family clock differ by their actual base value. The
original joint density determines the positive real normalizer after this shift.
An almost-everywhere geometric section identity therefore gives the exact real
density consumed by the Jacobi moment estimates, without a conditional-law oracle.
-/

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OTSelector.Reconstruction

open OTSelector.Geometry

/-- Subtracting the original potential at the chosen origin translates a density
without any Jacobian or normalization change. -/
theorem map_withDensity_sub_clock (d : ℝ → ℝ≥0∞) (u₀ : ℝ) :
    ((volume : Measure ℝ).withDensity d).map (fun x ↦ x - u₀) =
      volume.withDensity (fun t ↦ d (t + u₀)) := by
  have h := map_withDensity_measurableEquiv (MeasurableEquiv.subRight u₀) volume d
  have hvol : (volume : Measure ℝ).map (fun x ↦ x - u₀) = volume := by
    simpa only [sub_eq_add_neg] using (measurePreserving_add_right volume (-u₀)).map_eq
  change ((volume : Measure ℝ).withDensity d).map (fun x ↦ x - u₀) =
    ((volume : Measure ℝ).map (fun x ↦ x - u₀)).withDensity (fun t ↦ d (t + u₀)) at h
  rwa [hvol] at h

/-- The original scalar conditionals acquire their real Jacobi normalization from
the same original joint density and actual family-clock shift. -/
theorem ae_condDistrib_clockShift_eq_restrict_ofReal
    {M Z : Type*} [MeasurableSpace M] [MeasurableSpace Z]
    (eta : Measure M) [IsFiniteMeasure eta]
    {a : M → Z} {u : M → ℝ} (hu : Measurable u)
    (beta : Measure Z) [SigmaFinite beta]
    {G : Z × ℝ → ℝ≥0∞} (hG : Measurable G)
    (hjoint : eta.map (fun x ↦ (a x, u x)) =
      (beta.prod (volume : Measure ℝ)).withDensity G)
    (I : Z → Set ℝ) (hI : ∀ z, MeasurableSet (I z))
    (d : Z → ℝ → ℝ) (u₀ : Z → ℝ)
    (hsection : ∀ᵐ z ∂eta.map a,
      (fun t ↦ G (z, t + u₀ z)) =ᵐ[(volume : Measure ℝ)]
        (I z).indicator (fun t ↦ ENNReal.ofReal (d z t))) :
    ∀ᵐ z ∂eta.map a, 0 < (labelClockNormalizer G z).toReal ∧
      (condDistrib u a eta z).map (fun x ↦ x - u₀ z) =
        (volume.restrict (I z)).withDensity
          (fun t ↦ ENNReal.ofReal (d z t / (labelClockNormalizer G z).toReal)) := by
  filter_upwards [ae_condDistrib_eq_withDensity_normalized eta hu beta hG hjoint,
    ae_labelClockNormalizer_pos_lt_top eta hu beta hG hjoint, hsection]
      with z hcond htheta hsec
  refine ⟨ENNReal.toReal_pos_iff.mpr htheta, ?_⟩
  rw [hcond, map_withDensity_sub_clock]
  exact withDensity_div_eq_restrict_ofReal (hI z) htheta.1 htheta.2 hsec

end OTSelector.Reconstruction

end
