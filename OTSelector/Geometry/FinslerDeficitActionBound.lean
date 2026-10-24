import OTSelector.Geometry.FinslerStationaryPhaseAction

/-!
# Quantitative recovery of the original distance deficit

The stationary phase action differs from the original calibrated deficit only by
the two initial potential errors. Unit lengths and the same polynomial level cancel
the corrections for the model. The estimate retains the original distance cost.
-/

open Manifold
open scoped ContDiff

namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The original deficit comparison is bounded by the same phase-action comparison
and the two actual initial potential errors. No endpoint approximation is assumed. -/
theorem original_deficit_sub_model_norm_le_phaseAction
    (F : ContinuousFinslerNorm E M) (old : M) (Φ : (E × E) → ℝ → M)
    (G P : E → ℝ) (u : M → ℝ) (a b : ℝ) (z y : (E × E) × (E × E))
    (hz₁ : (F.chartLength old z.1 : ℝ) = 1)
    (hz₂ : (F.chartLength old z.2 : ℝ) = 1)
    (hy₁ : (F.chartLength old y.1 : ℝ) = 1)
    (hy₂ : (F.chartLength old y.2 : ℝ) = 1)
    (hclock₁ : u (Φ z.1 a) = G z.1.1 + a)
    (hclock₂ : u (Φ z.2 b) = G z.2.1 + b)
    (hlevel : P y.1.1 = P y.2.1) :
    ‖((F.lengthEDist (Φ z.1 a) (Φ z.2 b)).toReal - u (Φ z.2 b) + u (Φ z.1 a)) -
      ((F.lengthEDist (Φ y.1 a) (Φ y.2 b)).toReal - (b - a))‖ ≤
      ‖F.phaseLengthAction old Φ P a b z - F.phaseLengthAction old Φ P a b y‖ +
        ‖G z.1.1 - P z.1.1‖ + ‖G z.2.1 - P z.2.1‖ := by
  have hid :
      ((F.lengthEDist (Φ z.1 a) (Φ z.2 b)).toReal - u (Φ z.2 b) + u (Φ z.1 a)) -
        ((F.lengthEDist (Φ y.1 a) (Φ y.2 b)).toReal - (b - a)) =
      (F.phaseLengthAction old Φ P a b z - F.phaseLengthAction old Φ P a b y) +
        (G z.1.1 - P z.1.1) - (G z.2.1 - P z.2.1) := by
    simp only [phaseLengthAction, hz₁, hz₂, hy₁, hy₂, mul_one, hclock₁, hclock₂, hlevel]
    ring
  rw [hid]
  exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)

end OTSelector.Geometry.ContinuousFinslerNorm
