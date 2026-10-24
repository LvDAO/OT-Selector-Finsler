import OTSelector.Finite.PressureRegularity
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Relative quadratic errors in actual finite pressure values

A relative cost error is controlled by the reference pressure and its bounded
probe. This comparison uses the actual two minima and therefore does not require
an extra displacement moment for the optimizer of the perturbed cost.
-/

open Set MeasureTheory
open scoped BigOperators

noncomputable section
namespace OTSelector.Reconstruction

/-- Relative objective errors transfer to the attained tilted minima over the same
feasible set. The reference tilted value controls the error with constant one. -/
theorem relative_tilted_minimum_abs_sub_le {X : Type*} {S : Set X}
    (c d g h : X → ℝ) {x y : X} (hx : x ∈ S) (hy : y ∈ S)
    {t ε G B : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hc : ∀ z ∈ S, |c z - d z| ≤ ε * d z)
    (hh : ∀ z ∈ S, |h z| ≤ G)
    (hgh : ∀ z ∈ S, |g z - h z| ≤ B)
    (hxmin : ∀ z ∈ S, c x + t * g x ≤ c z + t * g z)
    (hymin : ∀ z ∈ S, d y + t * h y ≤ d z + t * h z) :
    |(c x + t * g x) - (d y + t * h y)| ≤
      ε * (d y + t * h y + |t| * G) + |t| * B := by
  have hprobe (z : X) (hz : z ∈ S) : |t * h z| ≤ |t| * G := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hh z hz) (abs_nonneg _)
  have hprobeDiff (z : X) (hz : z ∈ S) : |t * g z - t * h z| ≤ |t| * B := by
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left (hgh z hz) (abs_nonneg _)
  have hcx := abs_le.mp (hc x hx)
  have hcy := abs_le.mp (hc y hy)
  have hpx := abs_le.mp (hprobe x hx)
  have hpy := abs_le.mp (hprobe y hy)
  have hdx := abs_le.mp (hprobeDiff x hx)
  have hdy := abs_le.mp (hprobeDiff y hy)
  have hup : c x + t * g x ≤ d y + t * h y +
      ε * (d y + t * h y + |t| * G) + |t| * B := by
    have hnonneg := mul_nonneg hε0 (show 0 ≤ t * h y + |t| * G by linarith only [hpy.1])
    linarith only [hxmin y hy, hcy.2, hdy.2, hnonneg]
  have hlo : (1 - ε) * (d y + t * h y) - ε * (|t| * G) - |t| * B ≤
      c x + t * g x := by
    have hmin := mul_le_mul_of_nonneg_left (hymin x hx) (sub_nonneg.mpr hε1)
    have hnonneg := mul_nonneg hε0 (show 0 ≤ t * h x + |t| * G by linarith only [hpx.1])
    nlinarith only [hmin, hcx.1, hdx.1, hnonneg]
  exact abs_sub_le_iff.mpr ⟨by linarith only [hup], by nlinarith only [hlo]⟩

/-- Relative edge errors sum with the reference cost of the same assignment. -/
theorem assignmentCost_abs_sub_le_relative {n : ℕ}
    (c d : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ)
    (h : ∀ i j, |c i j - d i j| ≤ ε * d i j) (σ : Assignment n) :
    |assignmentCost c σ - assignmentCost d σ| ≤ ε * assignmentCost d σ := by
  simp only [assignmentCost, ← Finset.sum_sub_distrib]
  calc
    |∑ i, (c i (σ i) - d i (σ i))| ≤ ∑ i, |c i (σ i) - d i (σ i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ε * d i (σ i) := Finset.sum_le_sum (fun i _ ↦ h i (σ i))
    _ = _ := (Finset.mul_sum ..).symm

/-- Uniform edge probe errors sum with the original number of assignment edges. -/
theorem assignmentCost_abs_sub_le_uniform {n : ℕ}
    (g h : Matrix (Fin n) (Fin n) ℝ) (B : ℝ)
    (hb : ∀ i j, |g i j - h i j| ≤ B) (σ : Assignment n) :
    |assignmentCost g σ - assignmentCost h σ| ≤ (n : ℝ) * B := by
  simp only [assignmentCost, ← Finset.sum_sub_distrib]
  calc
    |∑ i, (g i (σ i) - h i (σ i))| ≤ ∑ i, |g i (σ i) - h i (σ i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin n, B := Finset.sum_le_sum (fun i _ ↦ hb i (σ i))
    _ = _ := by simp

/-- The actual finite pressure inherits a relative quadratic cost comparison. -/
theorem perturbedAssignmentValue_abs_sub_le_relative {n : ℕ}
    (c g d h : Matrix (Fin n) (Fin n) ℝ) (t ε G B : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hc : ∀ i j, |c i j - d i j| ≤ ε * d i j)
    (hh : ∀ i j, |h i j| ≤ G) (hgh : ∀ i j, |g i j - h i j| ≤ B) :
    |perturbedAssignmentValue c g t - perturbedAssignmentValue d h t| ≤
      ε * (perturbedAssignmentValue d h t + (n : ℝ) * (|t| * G)) +
        (n : ℝ) * (|t| * B) := by
  obtain ⟨σ, hσ, heσ⟩ := perturbedAssignmentValue_attained c g t
  obtain ⟨τ, hτ, heτ⟩ := perturbedAssignmentValue_attained d h t
  have hb (κ : Assignment n) : |assignmentCost h κ| ≤ (n : ℝ) * G := by
    simpa [assignmentCost] using
      assignmentCost_abs_sub_le_uniform h 0 G (by simpa using hh) κ
  have hcompare := relative_tilted_minimum_abs_sub_le
    (S := univ) (assignmentCost c) (assignmentCost d) (assignmentCost g) (assignmentCost h)
    (x := σ) (y := τ) (mem_univ _) (mem_univ _) hε0 hε1
    (fun κ _ ↦ assignmentCost_abs_sub_le_relative c d ε hc κ) (fun κ _ ↦ hb κ)
    (fun κ _ ↦ assignmentCost_abs_sub_le_uniform g h B hgh κ)
    (fun κ _ ↦ by simpa only [assignmentCost_perturbedEdgeCost] using hσ κ)
    (fun κ _ ↦ by simpa only [assignmentCost_perturbedEdgeCost] using hτ κ)
  rw [heσ, heτ, assignmentCost_perturbedEdgeCost, assignmentCost_perturbedEdgeCost]
  convert hcompare using 1
  ring

/-- Empirical normalization preserves the relative-error constant exactly. -/
theorem perturbedAssignmentValue_div_abs_sub_le_relative {n : ℕ} (hn : 0 < n)
    (c g d h : Matrix (Fin n) (Fin n) ℝ) (t ε G B : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hc : ∀ i j, |c i j - d i j| ≤ ε * d i j)
    (hh : ∀ i j, |h i j| ≤ G) (hgh : ∀ i j, |g i j - h i j| ≤ B) :
    |perturbedAssignmentValue c g t / n - perturbedAssignmentValue d h t / n| ≤
      ε * (perturbedAssignmentValue d h t / n + |t| * G) + |t| * B := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [← sub_div, abs_div, abs_of_pos hn']
  apply (div_le_iff₀ hn').mpr
  convert perturbedAssignmentValue_abs_sub_le_relative c g d h t ε G B hε0 hε1 hc hh hgh using 1
  · rfl
  · field_simp [ne_of_gt hn']

/-- The reference zero-tilt energy bounds its tilted pressure on every finite sample. -/
theorem perturbedAssignmentValue_div_le_zero_tilt {n : ℕ} (hn : 0 < n)
    (d h : Matrix (Fin n) (Fin n) ℝ) (t G : ℝ)
    (hh : ∀ i j, |h i j| ≤ G) :
    perturbedAssignmentValue d h t / n ≤ perturbedAssignmentValue d h 0 / n + |t| * G := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hb := assignmentCost_abs_sub_le_uniform h 0 G (by simpa using hh)
    (optimalAssignment d)
  simp only [assignmentCost, Matrix.zero_apply, Finset.sum_const_zero, sub_zero] at hb
  have ht := mul_le_mul_of_nonneg_left hb (abs_nonneg t)
  have hval := perturbedAssignmentValue_div_le_of_optimal hn d h t
    (optimalAssignment d) (optimalAssignment_isOptimal d)
  have hprobe : t * (assignmentCost h (optimalAssignment d) / (n : ℝ)) ≤ |t| * G := by
    apply (le_abs_self _).trans
    rw [abs_mul, abs_div, abs_of_pos hn', ← mul_div_assoc]
    apply (div_le_iff₀ hn').mpr
    simpa only [mul_assoc, mul_left_comm, mul_comm, assignmentCost] using ht
  exact hval.trans (add_le_add le_rfl hprobe)

/-- A zero-tilt comparator controls the relative finite-pressure error, even when the
reference tilted value is negative. -/
theorem perturbedAssignmentValue_div_abs_sub_le_relative_zero_tilt {n : ℕ} (hn : 0 < n)
    (c g d h : Matrix (Fin n) (Fin n) ℝ) (t ε G B : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hc : ∀ i j, |c i j - d i j| ≤ ε * d i j)
    (hh : ∀ i j, |h i j| ≤ G) (hgh : ∀ i j, |g i j - h i j| ≤ B) :
    |perturbedAssignmentValue c g t / n - perturbedAssignmentValue d h t / n| ≤
      ε * (perturbedAssignmentValue d h 0 / n + 2 * |t| * G) + |t| * B := by
  apply (perturbedAssignmentValue_div_abs_sub_le_relative hn c g d h t ε G B
    hε0 hε1 hc hh hgh).trans
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ hε0
  have hv := perturbedAssignmentValue_div_le_zero_tilt hn d h t G hh
  linarith only [hv]

end OTSelector.Reconstruction
