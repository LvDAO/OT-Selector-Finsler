import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Fixed-seed cutoff error at prescribed accuracy

After the finite scene and its constants are fixed, choose one cutoff radius.
The remaining sample error vanishes along the original spatial scale.
-/

open Filter
open scoped Topology ENNReal

namespace OTSelector.Reconstruction

/-- One radius controls the finite-scene error at every sample size.  The
remaining energy error converges to zero along the given diverging scale. -/
theorem exists_fixed_seed_cutoff_error_accuracy
    (L V Energy loss : ℝ≥0∞) (hL : L ≠ ⊤) (hV : V ≠ ⊤) (hEnergy : Energy ≠ ⊤)
    (count : ℕ) (q c : ℝ) (hq : 0 < q) (hc : 0 < c)
    (scale : ℕ → ℝ) (_hscalePos : ∀ n, 0 < scale n)
    (hscale : Tendsto scale atTop atTop)
    (accuracy : ℝ) (haccuracy : 0 < accuracy)
    (hloss : L * (V * loss) ≤ ENNReal.ofReal (accuracy / 2)) :
    ∃ R : ℝ, 0 < R ∧ ∃ sample : ℕ → ℝ≥0∞,
      Tendsto sample atTop (𝓝 0) ∧ ∀ n,
        L * ((count : ℝ≥0∞) *
          ((V * (Energy / ENNReal.ofReal q)) / ENNReal.ofReal (R ^ 2)) +
          V * (loss + Energy / ENNReal.ofReal (scale n ^ 2 * c))) ≤
          ENNReal.ofReal accuracy + sample n := by
  let A := L * ((count : ℝ≥0∞) * (V * (Energy / ENNReal.ofReal q)))
  have hA : A ≠ ⊤ :=
    ENNReal.mul_ne_top hL (ENNReal.mul_ne_top (by simp)
      (ENNReal.mul_ne_top hV
        (ENNReal.div_ne_top hEnergy (ne_of_gt (ENNReal.ofReal_pos.mpr hq)))))
  have hradius : Tendsto (fun m : ℕ ↦ (m : ℝ) + 1) atTop atTop := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hradiusDen : Tendsto (fun m : ℕ ↦ ENNReal.ofReal (((m : ℝ) + 1) ^ 2))
      atTop (𝓝 ⊤) :=
    ENNReal.tendsto_ofReal_nhds_top.mpr ((tendsto_pow_atTop (by decide)).comp hradius)
  have hradiusError : Tendsto
      (fun m : ℕ ↦ A / ENNReal.ofReal (((m : ℝ) + 1) ^ 2)) atTop (𝓝 0) := by
    simpa only [ENNReal.div_top] using
      (ENNReal.Tendsto.div tendsto_const_nhds (Or.inr (by simp))
        hradiusDen (Or.inr hA))
  have hhalf : 0 < ENNReal.ofReal (accuracy / 2) :=
    ENNReal.ofReal_pos.mpr (by positivity)
  obtain ⟨m, hm⟩ :=
    ((ENNReal.tendsto_nhds_zero.mp hradiusError) _ hhalf).exists
  let sample : ℕ → ℝ≥0∞ :=
    fun n ↦ L * (V * (Energy / ENNReal.ofReal (scale n ^ 2 * c)))
  have hsampleDen : Tendsto (fun n ↦ ENNReal.ofReal (scale n ^ 2 * c))
      atTop (𝓝 ⊤) :=
    ENNReal.tendsto_ofReal_nhds_top.mpr
      (((tendsto_pow_atTop (by decide)).comp hscale).atTop_mul_const hc)
  have hsampleDiv : Tendsto (fun n ↦ Energy / ENNReal.ofReal (scale n ^ 2 * c))
      atTop (𝓝 0) := by
    simpa only [ENNReal.div_top] using
      (ENNReal.Tendsto.div tendsto_const_nhds (Or.inr (by simp))
        hsampleDen (Or.inr hEnergy))
  have hsample : Tendsto sample atTop (𝓝 0) := by
    simpa only [sample, mul_zero] using
      ENNReal.Tendsto.const_mul
        (ENNReal.Tendsto.const_mul hsampleDiv (Or.inr hV)) (Or.inr hL)
  refine ⟨(m : ℝ) + 1, by positivity, sample, hsample, fun n ↦ ?_⟩
  have htail : L * ((count : ℝ≥0∞) *
      ((V * (Energy / ENNReal.ofReal q)) /
        ENNReal.ofReal (((m : ℝ) + 1) ^ 2))) ≤ ENNReal.ofReal (accuracy / 2) := by
    simpa only [A, div_eq_mul_inv, mul_assoc] using hm
  calc
    _ = (L * ((count : ℝ≥0∞) *
          ((V * (Energy / ENNReal.ofReal q)) /
            ENNReal.ofReal (((m : ℝ) + 1) ^ 2))) + L * (V * loss)) + sample n := by
      simp only [sample, mul_add, add_assoc]
    _ ≤ (ENNReal.ofReal (accuracy / 2) + ENNReal.ofReal (accuracy / 2)) + sample n :=
      add_le_add (add_le_add htail hloss) le_rfl
    _ = ENNReal.ofReal accuracy + sample n := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 2
      ring

end OTSelector.Reconstruction
