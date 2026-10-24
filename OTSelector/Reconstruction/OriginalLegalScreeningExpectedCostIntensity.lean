import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Actual working reserve errors retain the same constants after the full-input intensity dilation. -/
open scoped Topology
noncomputable section
namespace OTSelector.Reconstruction

/-- The physical intensity/quadratic prefactor exactly normalizes the genuine
working reserve energy and bounded-tilt errors. Constants remain unchanged. -/
theorem originalScreeningExpectedCost_intensity_normalization
    (q : ℕ) {rho : ℝ} (hrho : 0 ≤ rho) (C D G t : ℝ) (value : ℝ → ℝ) :
    let a := (1+rho)⁻¹
    let θ := rho/(1+rho)
    let r := 1-2/(q : ℝ)
    a^r*(value (t*a^(2/(q : ℝ)))+C*rho^r+D*|t*a^(2/(q : ℝ))| * G*rho) =
      a^r*value (t*a^(2/(q : ℝ)))+C*θ^r+D*|t| * G*θ := by
  let a := (1+rho)⁻¹
  let r := 1-2/(q : ℝ)
  have ha : 0 < a := inv_pos.mpr (by linarith)
  have hm : a*rho = rho/(1+rho) := by dsimp [a]; ring
  have henergy : a^r*rho^r = (rho/(1+rho))^r := by
    rw [← Real.mul_rpow ha.le hrho,hm]
  have hscale : a^r*a^(2/(q : ℝ)) = a := by
    rw [← Real.rpow_add ha,show r+2/(q : ℝ) = 1 by dsimp [r]; ring,Real.rpow_one]
  have htilt : a^r*|t*a^(2/(q : ℝ))| * rho = |t| * (rho/(1+rho)) := by
    rw [abs_mul,abs_of_pos (Real.rpow_pos_of_pos ha _)]
    calc
      _ = |t| * (a^r*a^(2/(q : ℝ)))*rho := by ring
      _ = _ := by rw [hscale]; rw [← hm]; ring
  change a^r*(value (t*a^(2/(q : ℝ)))+C*rho^r+D*|t*a^(2/(q : ℝ))| * G*rho) = _
  calc
    _ = a^r*value (t*a^(2/(q : ℝ)))+C*(a^r*rho^r)+D*G*(a^r*|t*a^(2/(q : ℝ))| * rho) := by ring
    _ = _ := by rw [henergy,htilt]; ring

end OTSelector.Reconstruction
