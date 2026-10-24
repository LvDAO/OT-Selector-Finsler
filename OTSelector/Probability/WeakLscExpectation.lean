import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Weak Lsc Expectation

Conditions: General topological carrier probability laws with weak convergence or explicit open-set lower bounds; measurable nonnegative lower-semicontinuous real/ENNReal readout.

Objects: Lower-semicontinuity of the expected readout, including the possibility of infinite expectation.

Proof detail: Use open superlevel sets, layer cake and Fatou for real readouts. Approximate ENNReal readouts by continuous monotone finite truncations and take their supremum.

Relation to primary sources: A general-carrier Portmanteau/layer-cake consequence, with infinite values retained. It is not restricted to the real-carrier Portmanteau theorem.

References:
* D. H. Fremlin, Measure Theory, Volume 4, Sections 437J(d),(f),(g), 437K–437L, PDF p. 61 onward. https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61
* Rick Durrett, Probability: Theory and Examples, fifth edition, author version 11 January 2019, Section 1.7, Exercise 1.7.2, p. 41. https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=49
* Rick Durrett, Probability: Theory and Examples, fifth edition, author version 11 January 2019, Section 1.6.2, Theorems 1.6.5–1.6.7, p. 30. https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=38
-/
/-!
# Lower semicontinuous nonnegative expectations under actual weak convergence

Open-superlevel Portmanteau and layer cake prove the real nonnegative LSC
inequality. Continuous monotone real truncations then give the full ENNReal
expectation inequality, including infinite values, by monotone convergence.
-/

open Set Function Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 800000

variable {S : Type*} [MeasurableSpace S] [TopologicalSpace S] [OpensMeasurableSpace S]

/-- Layer cake needs open strict superlevels, so the nonnegative real
Portmanteau integral inequality applies to LSC observables. -/
theorem lintegral_ofReal_lsc_le_liminf_of_open_bounds
    (Q : Measure S) (P : ℕ → Measure S) (f : S → ℝ)
    (hf : LowerSemicontinuous f) (hf0 : ∀ s, 0 ≤ f s)
    (hopen : ∀ U : Set S, IsOpen U → Q U ≤ atTop.liminf (fun n ↦ P n U)) :
    (∫⁻ s, ENNReal.ofReal (f s) ∂Q) ≤
      atTop.liminf (fun n ↦ ∫⁻ s, ENNReal.ofReal (f s) ∂P n) := by
  simp_rw [lintegral_eq_lintegral_meas_lt _ (Eventually.of_forall hf0)
    hf.measurable.aemeasurable]
  calc
    (∫⁻ t in Ioi (0 : ℝ), Q {s | t < f s}) ≤
        ∫⁻ t in Ioi (0 : ℝ), atTop.liminf (fun n ↦ P n {s | t < f s}) :=
      lintegral_mono fun t ↦ hopen _ (hf.isOpen_preimage t)
    _ ≤ atTop.liminf (fun n ↦ ∫⁻ t in Ioi (0 : ℝ), P n {s | t < f s}) :=
      lintegral_liminf_le fun n ↦ Antitone.measurable
        (fun s t hst ↦ measure_mono (fun x hx ↦ lt_of_le_of_lt hst hx))

/-- The actual weak limit preserves the full lower-semicontinuous ENNReal
expectation inequality. No boundedness, finiteness or tail-readout premise occurs. -/
theorem lintegral_lsc_le_liminf_of_weak_tendsto [HasOuterApproxClosed S]
    (Q : ProbabilityMeasure S) (P : ℕ → ProbabilityMeasure S)
    (hweak : Tendsto P atTop (𝓝 Q)) (W : S → ℝ≥0∞) (hW : LowerSemicontinuous W) :
    (∫⁻ s, W s ∂(Q : Measure S)) ≤
      atTop.liminf (fun n ↦ ∫⁻ s, W s ∂(P n : Measure S)) := by
  let trunc : ℕ → S → ℝ≥0∞ := fun n s ↦ min (n : ℝ≥0∞) (W s)
  let realTrunc : ℕ → S → ℝ := fun n s ↦ ENNReal.truncateToReal (n : ℝ≥0∞) (W s)
  have hfinite (n : ℕ) (s : S) : min (n : ℝ≥0∞) (W s) ≠ ⊤ :=
    ne_top_of_le_ne_top (by finiteness) (min_le_left _ _)
  have hcast (n : ℕ) (s : S) : ENNReal.ofReal (realTrunc n s) = trunc n s :=
    ENNReal.ofReal_toReal (hfinite n s)
  have hrealLsc (n : ℕ) : LowerSemicontinuous (realTrunc n) :=
    (ENNReal.continuous_truncateToReal (by finiteness)).comp_lowerSemicontinuous hW
      (ENNReal.monotone_truncateToReal (by finiteness))
  have htruncMeas (n : ℕ) : Measurable (trunc n) := measurable_const.min hW.measurable
  have htruncMono : Monotone trunc := by
    intro m n hmn s
    exact min_le_min (by exact_mod_cast hmn) le_rfl
  have hsup (s : S) : (⨆ n : ℕ, trunc n s) = W s := by
    change (⨆ n : ℕ, (n : ℝ≥0∞) ⊓ W s) = W s
    rw [← iSup_inf_eq, ENNReal.iSup_natCast, top_inf_eq]
  have htruncBound (n : ℕ) : (∫⁻ s, trunc n s ∂(Q : Measure S)) ≤
      atTop.liminf (fun k ↦ ∫⁻ s, trunc n s ∂(P k : Measure S)) := by
    have h := lintegral_ofReal_lsc_le_liminf_of_open_bounds (Q : Measure S)
      (fun k ↦ (P k : Measure S)) (realTrunc n) (hrealLsc n)
      (fun _ ↦ ENNReal.truncateToReal_nonneg)
      (fun U hU ↦ ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak hU)
    simpa only [hcast] using h
  calc
    (∫⁻ s, W s ∂(Q : Measure S)) = ∫⁻ s, ⨆ n : ℕ, trunc n s ∂(Q : Measure S) :=
      lintegral_congr fun s ↦ (hsup s).symm
    _ = ⨆ n : ℕ, ∫⁻ s, trunc n s ∂(Q : Measure S) :=
      lintegral_iSup htruncMeas htruncMono
    _ ≤ atTop.liminf (fun k ↦ ∫⁻ s, W s ∂(P k : Measure S)) :=
      iSup_le fun n ↦ (htruncBound n).trans (liminf_le_liminf
        (Eventually.of_forall fun k ↦ lintegral_mono fun s ↦ min_le_right _ _))

end OTSelector.Reconstruction
