import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! The actual fixed finite-partition Hall repair vanishes after volume normalization. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace OTSelector.Reconstruction

/-- The genuine Poisson square-root Hall correction, including the physical
quadratic scale, is negligible in dimension greater than four. -/
theorem tendsto_originalOrientedShapePartition_repair_div_zero
    {q : ℕ} (hq : 4 < q) (bins cells : ℕ) (C G t : ℝ) :
    Tendsto (fun r : ℝ ↦
      Real.sqrt (2*r*((cells*(bins*bins+1) : ℕ) : ℝ)) *
        (2*((bins : ℝ)+1)*(r^(2/(q : ℝ))*(C*q)+|t| * G)) / r)
      atTop (𝓝 0) := by
  let N : ℝ := ((cells*(bins*bins+1) : ℕ) : ℝ)
  let K : ℝ := 2*((bins : ℝ)+1)*Real.sqrt (2*N)
  have hqR : (4 : ℝ) < q := by exact_mod_cast hq
  have hneg : 2/(q : ℝ)-(1/2:ℝ) < 0 := by
    have hdiv : 2/(q : ℝ) < (1/2:ℝ) := (div_lt_iff₀ (by linarith : (0:ℝ)<q)).mpr (by linarith)
    linarith
  have hpower : Tendsto (fun r : ℝ ↦ r^(2/(q : ℝ)-(1/2:ℝ))) atTop (𝓝 0) :=
    by simpa only [neg_neg] using
      (tendsto_rpow_neg_atTop (y := -(2/(q : ℝ)-(1/2:ℝ))) (neg_pos.mpr hneg))
  have hsqrt : Tendsto (fun r : ℝ ↦ 1/Real.sqrt r) atTop (𝓝 (0:ℝ)) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have hmodel := ((hpower.const_mul (C*q)).add (hsqrt.const_mul (|t| * G))).const_mul K
  simp only [mul_zero,zero_add] at hmodel
  apply hmodel.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hfactor : Real.sqrt (2*r*N) = Real.sqrt (2*N)*Real.sqrt r := by
    rw [show 2*r*N=(2*N)*r by ring,Real.sqrt_mul (by positivity)]
  have hs : Real.sqrt r ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
  change K*((C*q)*r^(2/(q : ℝ)-(1/2:ℝ))+(|t| * G)*(1/Real.sqrt r)) =
    Real.sqrt (2*r*N)*(2*((bins : ℝ)+1)*(r^(2/(q : ℝ))*(C*q)+|t| * G))/r
  rw [Real.rpow_sub hr,← Real.sqrt_eq_rpow,hfactor]
  dsimp only [K]
  field_simp [hr.ne',hs]
  rw [Real.sq_sqrt hr.le]
  ring

end OTSelector.Reconstruction
