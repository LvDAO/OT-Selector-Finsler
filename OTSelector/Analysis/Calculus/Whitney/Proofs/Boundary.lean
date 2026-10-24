import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.MetricSpace.HausdorffDistance
import OTSelector.Analysis.Calculus.Whitney.Basic

/-!
# Whitney compatibility and differentiability across the closed boundary

Main declarations: HasWhitneyLocalBlend; contDiff_whitney_of_local_blends.

This file contains the original declarations and their proofs. The source-unit
sections below preserve each unit's conditions, objects, proof details and
book or paper locations.
-/

/-! Source unit: `OTSelector.Analysis.Calculus.Whitney.Boundary`. Its original mathematical documentation follows. -/
section

/-!
## Lemma skeleton

* **Conditions:** Real normed spaces; continuous prescribed first jet and uniform first-order Whitney remainder on K; equality on K and actual local finite smooth affine blends off K. Derivative continuity/global C1 uses compact K and a nonnegative derivative-mass constant.
* **Objects:** Boundary value/derivative estimates, HasWhitneyLocalBlend, actual Fréchet derivative at every b in K and global C1 gluing.
* **Proof detail:** Compare the local blend to the affine jet at a nearby anchor and then a fixed boundary point. Scale-controlled support and partition derivative mass turn Whitney remainders into differentiability and continuity of the actual derivative.

## Mathematical sources

* Hassler Whitney, *Analytic Extensions of Differentiable Functions Defined in Closed Sets, Transactions of the AMS 36(1), 63–89 (1934)*, Section 3, pp. 64–65, equations (3.1)–(3.2); Section 6, p. 66, equations (6.1)–(6.3).
  https://www.ams.org/journals/tran/1934-036-01/S0002-9947-1934-1501735-3/S0002-9947-1934-1501735-3.pdf#page=2
* Hassler Whitney, *Analytic Extensions of Differentiable Functions Defined in Closed Sets, Transactions of the AMS 36(1), 63–89 (1934)*, Section 4, Theorem I, p. 65; Section 11, Lemma 2 and proof, pp. 69–71, equations (11.1)–(11.8).
  https://www.ams.org/journals/tran/1934-036-01/S0002-9947-1934-1501735-3/S0002-9947-1934-1501735-3.pdf#page=3

**Relationship to the sources:** This is the first-order normed-vector-valued boundary argument underlying Whitney’s Lemma 2. Local blend hypotheses are explicit at this stage; C1 constructs them later.
-/

/-!
# Boundary estimates for actual Whitney affine interpolation

The weighted affine formula is compared with the prescribed affine jet at a boundary
point. Nearest-point localization and the derivative mass of the actual partition give
quantitative value and derivative estimates, which supply the boundary C1 argument.
-/

open Set Filter Metric
open scoped Topology BigOperators

noncomputable section
namespace OTSelector.Geometry

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A normalized nonnegative affine blend differs from the reference jet by at most
five times the common first-jet error times the actual localization scale. -/
theorem norm_whitneyBlend_boundary_le (s : Finset ι) (φ : ι → E → ℝ)
    (f : E → F) (D : E → E →L[ℝ] F) (a : ι → E) {x b : E} {ε r : ℝ}
    (hε : 0 ≤ ε) (hpos : ∀ i ∈ s, 0 ≤ φ i x) (hone : ∑ i ∈ s, φ i x = 1)
    (hxb : ‖x - b‖ ≤ r) (hnear : ∀ i ∈ s, ‖x - a i‖ ≤ 2 * r)
    (hrem : ∀ i ∈ s, ‖f (a i) - f b - D b (a i - b)‖ ≤ ε * ‖a i - b‖)
    (hD : ∀ i ∈ s, ‖D (a i) - D b‖ ≤ ε) :
    ‖whitneyBlend s φ f D a x - whitneyAffineJet f D b x‖ ≤ 5 * ε * r := by
  apply norm_whitneyBlend_sub_le s φ f D a hpos hone
  intro i hi
  have hab : ‖a i - b‖ ≤ 3 * r := by
    calc
      _ ≤ ‖a i - x‖ + ‖x - b‖ := by
        simpa only [dist_eq_norm] using dist_triangle (a i) x b
      _ = ‖x - a i‖ + ‖x - b‖ := by rw [norm_sub_rev (a i) x]
      _ ≤ 2 * r + r := add_le_add (hnear i hi) hxb
      _ = 3 * r := by ring
  calc
    _ ≤ ε * ‖a i - b‖ + ε * ‖x - a i‖ :=
      norm_whitneyAffineJet_sub_le (hrem i hi) (hD i hi)
    _ ≤ ε * (3 * r) + ε * (2 * r) :=
      add_le_add (mul_le_mul_of_nonneg_left hab hε)
        (mul_le_mul_of_nonneg_left (hnear i hi) hε)
    _ = 5 * ε * r := by ring

/-- The true derivative of the finite affine formula approaches the reference derivative.
The partition derivative mass is explicit, and its inverse scale cancels the patch error. -/
theorem norm_fderiv_whitneyBlend_boundary_le (s : Finset ι) (φ : ι → E → ℝ)
    (f : E → F) (D : E → E →L[ℝ] F) (a : ι → E) {x b : E} {ε r A : ℝ}
    (hε : 0 ≤ ε) (hr : 0 < r)
    (hφ : ∀ i ∈ s, DifferentiableAt ℝ (φ i) x)
    (hpos : ∀ i ∈ s, 0 ≤ φ i x)
    (hone : (fun y ↦ ∑ i ∈ s, φ i y) =ᶠ[𝓝 x] fun _ ↦ (1 : ℝ))
    (hxb : ‖x - b‖ ≤ r) (hnear : ∀ i ∈ s, ‖x - a i‖ ≤ 2 * r)
    (hrem : ∀ i ∈ s, ‖f (a i) - f b - D b (a i - b)‖ ≤ ε * ‖a i - b‖)
    (hD : ∀ i ∈ s, ‖D (a i) - D b‖ ≤ ε)
    (hmass : ∑ i ∈ s, ‖fderiv ℝ (φ i) x‖ ≤ A / r) :
    ‖fderiv ℝ (whitneyBlend s φ f D a) x - D b‖ ≤ (1 + 5 * A) * ε := by
  have hpatch (i) (hi : i ∈ s) :
      ‖whitneyAffineJet f D (a i) x - whitneyAffineJet f D b x‖ ≤ 5 * ε * r := by
    have hab : ‖a i - b‖ ≤ 3 * r := by
      calc
        _ ≤ ‖a i - x‖ + ‖x - b‖ := by
          simpa only [dist_eq_norm] using dist_triangle (a i) x b
        _ = ‖x - a i‖ + ‖x - b‖ := by rw [norm_sub_rev (a i) x]
        _ ≤ 2 * r + r := add_le_add (hnear i hi) hxb
        _ = 3 * r := by ring
    exact (norm_whitneyAffineJet_sub_le (hrem i hi) (hD i hi)).trans (by
      nlinarith [mul_le_mul_of_nonneg_left hab hε,
        mul_le_mul_of_nonneg_left (hnear i hi) hε])
  calc
    _ ≤ ε + (5 * ε * r) * ∑ i ∈ s, ‖fderiv ℝ (φ i) x‖ :=
      norm_fderiv_whitneyBlend_sub_le s φ f D a hφ hpos hone hpatch hD
    _ ≤ ε + (5 * ε * r) * (A / r) := by
      gcongr
    _ = (1 + 5 * A) * ε := by field_simp

/-- Local finite affine representation and its quantitative partition data. These are
properties of the constructed interpolation on the open complement of the closed set. -/
def HasWhitneyLocalBlend (K : Set E) (φ : ι → E → ℝ) (f : E → F)
    (D : E → E →L[ℝ] F) (a : ι → E) (G : E → F) (A : ℝ) (x : E) : Prop :=
  ∃ s : Finset ι,
    G =ᶠ[𝓝 x] whitneyBlend s φ f D a ∧
    (∀ i ∈ s, ContDiffAt ℝ 1 (φ i) x) ∧ (∀ i ∈ s, 0 ≤ φ i x) ∧
    ((fun y ↦ ∑ i ∈ s, φ i y) =ᶠ[𝓝 x] fun _ ↦ (1 : ℝ)) ∧
    (∀ i ∈ s, a i ∈ K ∧ ‖x - a i‖ ≤ 2 * infDist x K) ∧
    (infDist x K < 1 → ∑ i ∈ s, ‖fderiv ℝ (φ i) x‖ ≤ A / infDist x K)

/-- The actual locally finite interpolation has the prescribed derivative at every
point of K. Its boundary differentiability is derived from the original Whitney condition. -/
theorem hasFDerivAt_whitney_local_blends {K : Set E}
    {φ : ι → E → ℝ} {f G : E → F} {D : E → E →L[ℝ] F} {a : ι → E} {A : ℝ}
    (hD : ContinuousOn D K)
    (hWhitney : ∀ ε > 0, ∃ δ > 0, ∀ u ∈ K, ∀ v ∈ K, dist u v < δ →
      ‖f u - f v - D v (u - v)‖ ≤ ε * ‖u - v‖)
    (hGK : EqOn G f K)
    (hlocal : ∀ x ∉ K, HasWhitneyLocalBlend K φ f D a G A x)
    {b : E} (hb : b ∈ K) : HasFDerivAt G (D b) b := by
  rw [hasFDerivAt_iff_isLittleO]
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  have he : 0 < ε / 5 := by positivity
  obtain ⟨δ₀, hδ₀, hW⟩ := hWhitney (ε / 5) he
  obtain ⟨δ₁, hδ₁, hDc⟩ := Metric.continuousWithinAt_iff.mp (hD b hb) (ε / 5) he
  let δ := min δ₀ δ₁ / 3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  filter_upwards [ball_mem_nhds b hδ] with x hx
  have hxb : ‖x - b‖ < δ := by simpa only [mem_ball, dist_eq_norm] using hx
  have hsmall₀ : 3 * ‖x - b‖ < δ₀ := by
    have h := min_le_left δ₀ δ₁
    dsimp [δ] at hxb
    linarith
  have hsmall₁ : 3 * ‖x - b‖ < δ₁ := by
    have h := min_le_right δ₀ δ₁
    dsimp [δ] at hxb
    linarith
  by_cases hxK : x ∈ K
  · rw [hGK hxK, hGK hb]
    have h := hW x hxK b hb (by rw [dist_eq_norm]; linarith [norm_nonneg (x - b)])
    exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  · obtain ⟨s, hgerm, hφ, hpos, hone, hanchor, _⟩ := hlocal x hxK
    have hδx : infDist x K ≤ ‖x - b‖ := by
      simpa only [dist_eq_norm] using infDist_le_dist_of_mem (x := x) hb
    have hnear (i) (hi : i ∈ s) : ‖x - a i‖ ≤ 2 * ‖x - b‖ :=
      (hanchor i hi).2.trans (by linarith)
    have hab (i) (hi : i ∈ s) : ‖a i - b‖ ≤ 3 * ‖x - b‖ := by
      have ht := dist_triangle (a i) x b
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, norm_sub_rev (a i) x] at ht
      linarith [hnear i hi]
    have hrem (i) (hi : i ∈ s) :
        ‖f (a i) - f b - D b (a i - b)‖ ≤ (ε / 5) * ‖a i - b‖ :=
      hW (a i) (hanchor i hi).1 b hb
        (by rw [dist_eq_norm]; exact (hab i hi).trans_lt hsmall₀)
    have hd (i) (hi : i ∈ s) : ‖D (a i) - D b‖ ≤ ε / 5 := by
      have h := hDc (hanchor i hi).1
        (show dist (a i) b < δ₁ by rw [dist_eq_norm]; exact (hab i hi).trans_lt hsmall₁)
      exact (by simpa only [dist_eq_norm] using h.le)
    have h := norm_whitneyBlend_boundary_le s φ f D a he.le hpos
      hone.self_of_nhds le_rfl hnear hrem hd
    rw [← hgerm.self_of_nhds] at h
    have heq : G x - G b - D b (x - b) = G x - whitneyAffineJet f D b x := by
      rw [hGK hb]
      simp only [whitneyAffineJet, sub_add_eq_sub_sub]
    rw [heq]
    convert h using 1
    ring

/-- The actual derivative of the interpolation is continuous at each boundary point.
The inverse-distance derivative mass cancels against the Whitney patch error around
an actual nearest point of K; no continuity of a chosen nearest-point map is assumed. -/
theorem continuousAt_fderiv_whitney_local_blends {K : Set E} (hK : IsCompact K)
    {φ : ι → E → ℝ} {f G : E → F} {D : E → E →L[ℝ] F} {a : ι → E} {A : ℝ}
    (hA : 0 ≤ A) (hD : ContinuousOn D K)
    (hWhitney : ∀ ε > 0, ∃ δ > 0, ∀ u ∈ K, ∀ v ∈ K, dist u v < δ →
      ‖f u - f v - D v (u - v)‖ ≤ ε * ‖u - v‖)
    (hGK : EqOn G f K)
    (hlocal : ∀ x ∉ K, HasWhitneyLocalBlend K φ f D a G A x)
    {b : E} (hb : b ∈ K) : ContinuousAt (fderiv ℝ G) b := by
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  let η := ε / (4 + 10 * A)
  have hden : 0 < 4 + 10 * A := by positivity
  have hη : 0 < η := div_pos hε hden
  have hηeq : (4 + 10 * A) * η = ε := by dsimp [η]; field_simp
  have hηsmall : (3 + 10 * A) * η < ε := by nlinarith
  have hηε : η < ε := by nlinarith
  obtain ⟨δ₀, hδ₀, hW⟩ := hWhitney (2 * η) (by positivity)
  obtain ⟨δ₁, hδ₁, hDc⟩ := Metric.continuousWithinAt_iff.mp (hD b hb) η hη
  let δ := min 1 (min δ₀ δ₁ / 4)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  have hxb : ‖x - b‖ < δ := by simpa only [dist_eq_norm] using hx
  have hsmall₀ : 3 * ‖x - b‖ < δ₀ := by
    have hh := min_le_right (1 : ℝ) (min δ₀ δ₁ / 4)
    have hh₀ := min_le_left δ₀ δ₁
    dsimp [δ] at hxb
    linarith [norm_nonneg (x - b)]
  have hsmall₁ : 3 * ‖x - b‖ < δ₁ := by
    have hh := min_le_right (1 : ℝ) (min δ₀ δ₁ / 4)
    have hh₁ := min_le_right δ₀ δ₁
    dsimp [δ] at hxb
    linarith [norm_nonneg (x - b)]
  rw [(hasFDerivAt_whitney_local_blends hD hWhitney hGK hlocal hb).fderiv]
  by_cases hxK : x ∈ K
  · rw [(hasFDerivAt_whitney_local_blends hD hWhitney hGK hlocal hxK).fderiv]
    exact (hDc hxK (by rw [dist_eq_norm]; linarith [norm_nonneg (x - b)])).trans hηε
  · obtain ⟨b', hb', hb'dist⟩ := hK.exists_infDist_eq_dist ⟨b, hb⟩ x
    have hδx : infDist x K ≤ ‖x - b‖ := by
      simpa only [dist_eq_norm] using infDist_le_dist_of_mem (x := x) hb
    have hr : 0 < infDist x K := (hK.isClosed.notMem_iff_infDist_pos ⟨b, hb⟩).mp hxK
    have hrsmall : infDist x K < 1 := by
      have hh := min_le_left (1 : ℝ) (min δ₀ δ₁ / 4)
      dsimp [δ] at hxb
      linarith
    have hxb' : ‖x - b'‖ = infDist x K := by
      simpa only [dist_eq_norm] using hb'dist.symm
    have hb'b : ‖b' - b‖ ≤ 2 * ‖x - b‖ := by
      have ht := dist_triangle b' x b
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, norm_sub_rev b' x, hxb'] at ht
      linarith
    have hDb' : dist (D b') (D b) < η :=
      hDc hb' (by rw [dist_eq_norm]; linarith [norm_nonneg (x - b)])
    obtain ⟨s, hgerm, hφ, hpos, hone, hanchor, hmass⟩ := hlocal x hxK
    have hab (i) (hi : i ∈ s) : ‖a i - b‖ ≤ 3 * ‖x - b‖ := by
      have ht := dist_triangle (a i) x b
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, norm_sub_rev (a i) x] at ht
      linarith [(hanchor i hi).2]
    have hab' (i) (hi : i ∈ s) : ‖a i - b'‖ ≤ 3 * infDist x K := by
      have ht := dist_triangle (a i) x b'
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, norm_sub_rev (a i) x, hxb'] at ht
      linarith [(hanchor i hi).2]
    have hrem (i) (hi : i ∈ s) :
        ‖f (a i) - f b' - D b' (a i - b')‖ ≤ (2 * η) * ‖a i - b'‖ :=
      hW (a i) (hanchor i hi).1 b' hb'
        (by rw [dist_eq_norm]; linarith [hab' i hi])
    have hd (i) (hi : i ∈ s) : ‖D (a i) - D b'‖ ≤ 2 * η := by
      have hDa : dist (D (a i)) (D b) < η :=
        hDc (hanchor i hi).1
          (by rw [dist_eq_norm]; exact (hab i hi).trans_lt hsmall₁)
      have ht := dist_triangle (D (a i)) (D b) (D b')
      rw [dist_comm (D b) (D b')] at ht
      rw [← dist_eq_norm]
      linarith
    have hbound := norm_fderiv_whitneyBlend_boundary_le s φ f D a (by positivity) hr
      (fun i hi ↦ (hφ i hi).differentiableAt one_ne_zero) hpos hone hxb'.le
      (fun i hi ↦ (hanchor i hi).2) hrem hd (hmass hrsmall)
    rw [← hgerm.fderiv_eq] at hbound
    have ht := dist_triangle (fderiv ℝ G x) (D b') (D b)
    rw [dist_eq_norm (fderiv ℝ G x) (D b')] at ht
    calc
      _ ≤ ‖fderiv ℝ G x - D b'‖ + dist (D b') (D b) := ht
      _ ≤ (1 + 5 * A) * (2 * η) + η := add_le_add hbound hDb'.le
      _ = (3 + 10 * A) * η := by ring
      _ < ε := hηsmall

/-- A local finite formula of C1 weights and affine jets is C1 at the point. -/
theorem contDiffAt_of_hasWhitneyLocalBlend {K : Set E}
    {φ : ι → E → ℝ} {f G : E → F} {D : E → E →L[ℝ] F} {a : ι → E}
    {A : ℝ} {x : E} (h : HasWhitneyLocalBlend K φ f D a G A x) :
    ContDiffAt ℝ 1 G x := by
  obtain ⟨s, hgerm, hφ, _⟩ := h
  have hblend : ContDiffAt ℝ 1 (whitneyBlend s φ f D a) x := by
    apply ContDiffAt.sum
    intro i hi
    apply (hφ i hi).smul
    exact contDiffAt_const.add ((D (a i)).contDiff.contDiffAt.comp x
      (contDiffAt_id.sub contDiffAt_const))
  exact hblend.congr_of_eventuallyEq hgerm

/-- Uniform first-order Whitney compatibility and the constructed local affine formulas
produce an actual C1 function on the entire space with the prescribed derivative on K. -/
theorem contDiff_whitney_of_local_blends {K : Set E} (hK : IsCompact K)
    {φ : ι → E → ℝ} {f G : E → F} {D : E → E →L[ℝ] F} {a : ι → E} {A : ℝ}
    (hA : 0 ≤ A) (hD : ContinuousOn D K)
    (hWhitney : ∀ ε > 0, ∃ δ > 0, ∀ u ∈ K, ∀ v ∈ K, dist u v < δ →
      ‖f u - f v - D v (u - v)‖ ≤ ε * ‖u - v‖)
    (hGK : EqOn G f K)
    (hlocal : ∀ x ∉ K, HasWhitneyLocalBlend K φ f D a G A x) :
    ContDiff ℝ 1 G ∧ ∀ b ∈ K, HasFDerivAt G (D b) b := by
  have hboundary {b : E} (hb : b ∈ K) : HasFDerivAt G (D b) b :=
    hasFDerivAt_whitney_local_blends hD hWhitney hGK hlocal hb
  refine ⟨contDiff_one_iff_fderiv.mpr ⟨?_, ?_⟩, fun b hb ↦ hboundary hb⟩
  · intro x
    by_cases hx : x ∈ K
    · exact (hboundary hx).differentiableAt
    · exact (contDiffAt_of_hasWhitneyLocalBlend (hlocal x hx)).differentiableAt one_ne_zero
  · apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x ∈ K
    · exact continuousAt_fderiv_whitney_local_blends hK hA hD hWhitney hGK hlocal hx
    · exact ((contDiffAt_of_hasWhitneyLocalBlend (hlocal x hx)).fderiv_right
        (m := 0) (by norm_num)).continuousAt

end OTSelector.Geometry

end
end
