import OTSelector.Reconstruction.OriginalFinslerPoleLoewnerComparison
import OTSelector.Reconstruction.SeparatedComplianceBound
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Exact pole integration gives focal compliance leg scales

Integrating the actual positive pole comparison on the two inward-distance intervals
`[t/2,t]` and `[t,2t]` gives both short compliance legs above a fixed multiple of the same
actual scale matrix `t I+t⁻¹G`. No simultaneous diagonalization or external leg bound enters.
-/

open Set Matrix MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The genuine reciprocal-square pole is continuous away from the focal endpoint. -/
theorem continuousOn_inverse_sq_positive_interval {a b : ℝ} (ha : 0<a) :
    ContinuousOn (fun s : ℝ ↦ (s^2)⁻¹) (Icc a b) :=
  (continuousOn_id.pow 2).inv₀ (fun _s hs ↦ pow_ne_zero 2 (ne_of_gt (ha.trans_le hs.1)))

/-- Exact integration of the actual scalar double pole along an ordered positive interval. -/
theorem intervalIntegral_inverse_sq_positive {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫s in a..b, (s^2)⁻¹)=a⁻¹-b⁻¹ := by
  have hint : IntervalIntegrable (fun s : ℝ ↦ (s^2)⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hab] using continuousOn_inverse_sq_positive_interval (b:=b) ha
  calc
    _ = -b⁻¹-(-a⁻¹) := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f:=fun s : ℝ ↦ -s⁻¹) (f':=fun s : ℝ ↦ (s^2)⁻¹) (a:=a) (b:=b)
      (fun s hs ↦ by
        have hs' : s∈Icc a b := by simpa only [uIcc_of_le hab] using hs
        simpa only [Pi.neg_apply,neg_neg] using! (hasDerivAt_inv (ne_of_gt (ha.trans_le hs'.1))).neg) hint
    _ = _ := by ring

/-- Exact fixed-matrix integral of the positive residue model. -/
theorem intervalIntegral_positivePole_model (G : Matrix ι ι ℝ) {a b : ℝ}
    (ha : 0<a) (hab : a≤b) :
    (∫s in a..b, ((s^2)⁻¹•G+1))=(a⁻¹-b⁻¹)•G+(b-a)•1 := by
  have hcont := (continuousOn_inverse_sq_positive_interval (b:=b) ha).smul
    (continuousOn_const (c:=G))
  have hint : IntervalIntegrable (fun s : ℝ ↦ (s^2)⁻¹•G) volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hab,Pi.smul_apply] using! hcont
  rw [intervalIntegral.integral_add hint intervalIntegrable_const,
    intervalIntegral.integral_smul_const,intervalIntegral_inverse_sq_positive ha hab,
    intervalIntegral.integral_const]

/-- Integrating the actual lower comparison gives its exact compliance lower model. -/
theorem intervalIntegral_positivePole_lower
    {W : ℝ→Matrix ι ι ℝ} {G : Matrix ι ι ℝ} {ε c a b : ℝ}
    (ha : 0<a) (hab : a≤b) (hb : b<ε) (hW : ContinuousOn W (Ioo 0 ε))
    (hlower : ∀s∈Ioo 0 ε, (W s-c•((s^2)⁻¹•G+1)).PosSemidef) :
    ((∫s in a..b,W s)-c•((a⁻¹-b⁻¹)•G+(b-a)•1)).PosSemidef := by
  have hsub : Icc a b ⊆ Ioo 0 ε := Icc_subset_Ioo ha hb
  have hWi : IntervalIntegrable W volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hab] using hW.mono hsub
  have hmodel : IntervalIntegrable (fun s : ℝ ↦ c•((s^2)⁻¹•G+1)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hab,Pi.smul_apply,Pi.add_apply] using!
      (((continuousOn_inverse_sq_positive_interval (b:=b) ha).smul continuousOn_const).add
        continuousOn_const).const_smul c
  have hp := posSemidef_intervalIntegral hab (fun s hs ↦ hlower s (hsub hs))
  rw [intervalIntegral.integral_sub hWi hmodel,intervalIntegral.integral_smul,
    intervalIntegral_positivePole_model G ha hab] at hp
  exact hp

/-- The two genuine short focal legs have the same actual matrix scale `tI+t⁻¹G` and
an internally derived positive lower constant. -/
theorem focal_positivePole_two_shortLeg_lower
    {W : ℝ→Matrix ι ι ℝ} {G : Matrix ι ι ℝ} {ε c t : ℝ}
    (hc : 0<c) (hG : G.PosSemidef) (ht : 0<t) (htε : 2*t<ε)
    (hW : ContinuousOn W (Ioo 0 ε))
    (hlower : ∀s∈Ioo 0 ε, (W s-c•((s^2)⁻¹•G+1)).PosSemidef) :
    ((∫s in (t/2)..t,W s)-(c/2)•(t•1+t⁻¹•G)).PosSemidef ∧
    ((∫s in t..(2*t),W s)-(c/2)•(t•1+t⁻¹•G)).PosSemidef := by
  have hleft := intervalIntegral_positivePole_lower (G:=G) (by positivity : 0<t/2)
    (by linarith : t/2≤t) (by linarith : t<ε) hW hlower
  have hright := intervalIntegral_positivePole_lower (G:=G) ht
    (by linarith : t≤2*t) htε hW hlower
  have hlinv : (t/2)⁻¹-t⁻¹=t⁻¹ := by field_simp; ring
  have hllen : t-t/2=t/2 := by ring
  have hrinv : t⁻¹-(2*t)⁻¹=t⁻¹/2 := by field_simp; ring
  have hrlen : 2*t-t=t := by ring
  rw [hlinv,hllen] at hleft
  rw [hrinv,hrlen] at hright
  constructor
  · have hp := hleft.add (hG.smul (show 0≤(c/2)*t⁻¹ by positivity))
    convert hp using 1
    module
  · have hp := hright.add (Matrix.PosSemidef.one.smul (show 0≤c*t/2 by positivity))
    convert hp using 1
    module

end OTSelector.Reconstruction
