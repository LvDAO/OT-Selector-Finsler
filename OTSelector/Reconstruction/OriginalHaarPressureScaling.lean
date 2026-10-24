import OTSelector.Reconstruction.OriginalNormalizedPressureLipschitz

/-! Exact bridge between standard-coordinate unit Poisson pressure and native
Haar unit pressure. The actual Haar Jacobian is never silently set to one. -/
open MeasureTheory
open scoped NNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Unit intensity for native Haar c times standard volume is obtained from
the literal coordinate-unit pressure by its exact spatial intensity scaling. -/
def haarUnitPressure (q c : ℝ) (p : ℝ → ℝ) (v : ℝ) : ℝ :=
  c ^ (-2/q) * p (v * c ^ (2/q))

/-- Native-Haar pressure retains precisely the physical probe norm. -/
theorem lipschitz_haarUnitPressure {q c : ℝ} (hq : 0 < q) (hc : 0 ≤ c)
    {p : ℝ → ℝ} {G : ℝ≥0} (hp : LipschitzWith G p) :
    LipschitzWith G (haarUnitPressure q c p) :=
  lipschitz_normalized_pressure hc hq hp

/-- The exact population-normalized expression uses coordinate intensity
Theta=c*theta. Both zero theta and arbitrarily small densities are included. -/
theorem normalized_haarUnitPressure_eq_coordinate
    {q c theta : ℝ} (hc : 0 ≤ c) (htheta : 0 ≤ theta) (p : ℝ → ℝ) (t : ℝ) :
    theta ^ (-2/q) * haarUnitPressure q c p (t * theta ^ (2/q)) =
      (c*theta) ^ (-2/q) * p (t * (c*theta) ^ (2/q)) := by
  unfold haarUnitPressure
  rw [Real.mul_rpow hc htheta,Real.mul_rpow hc htheta]
  rw [show (t * theta ^ (2/q)) * c ^ (2/q) =
    t * (c ^ (2/q) * theta ^ (2/q)) by ring]
  ring

/-- The native-Haar and coordinate-volume integrands have the exact Jacobian:
c*theta^(1-2/q)*I_Haar(t theta^(2/q)) equals the coordinate integrand. -/
theorem haar_weighted_haarUnitPressure_eq_coordinate
    {q c theta : ℝ} (hc : 0 < c) (htheta : 0 ≤ theta) (p : ℝ → ℝ) (t : ℝ) :
    c * (theta ^ (1-2/q) * haarUnitPressure q c p (t * theta ^ (2/q))) =
      (c*theta) ^ (1-2/q) * p (t * (c*theta) ^ (2/q)) := by
  unfold haarUnitPressure
  rw [Real.mul_rpow hc.le htheta,Real.mul_rpow hc.le htheta]
  have hweight : c * c ^ (-2/q) = c ^ (1-2/q) := by
    calc
      _ = c^ (1 : ℝ) * c^(-2/q) := by rw [Real.rpow_one]
      _ = c ^ ((1 : ℝ) + (-2/q)) := (Real.rpow_add hc 1 (-2/q)).symm
      _ = _ := by congr 1; ring
  rw [show (t * theta ^ (2/q)) * c ^ (2/q) =
    t * (c ^ (2/q) * theta ^ (2/q)) by ring,← hweight]
  ring

end OTSelector.Reconstruction
