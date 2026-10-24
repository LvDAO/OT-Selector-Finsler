import OTSelector.Reconstruction.FinslerOriginalLegalMaximumReadout

/-!
# Candidate window restriction lower bound

This module supplies the LOWER finite inequality of the local-optimality squeeze
(FinslerOriginalLegalMaximumReadout).  The actual candidate matching restricted
to the observation window is a legal finite matching, so its empirical readout
value is a lower bound for the finite legal maximum legalMarkedTilted up to the
finite missing-cardinality defect of the legal repair lane.

The finite repair lane (MarkedStationaryValuePhysicalRepair) proves exactly this
form: the full assignment value is bounded by the legal maximum-cardinality
minimum plus the physical cost of the true missing cardinality, per sample and
in expectation:
  perturbedAssignmentValue <= legalMaximumValue allowed cost +
    (n - legalMaximumCard allowed) * B.

Accordingly the lower inequality of the squeeze carries its own defect
(missing cardinality times the edge bound), which is normalized by the window
volume and is the second input of the two-defect squeeze:

1. **normalized_tendsto_of_twoSidedReadout**: the squeeze when both the lower
   and the upper finite inequality hold up to their own defects, each vanishing
   after volume normalization.

2. **candidateWindowLowerBound_of_finiteRepair**: the finite repair lower bound
   produces the lower defect inequality consumed by the squeeze.

3. **markedPressureReadout_of_twoSidedLocalOptimality**: instantiation with the
   window mass and the Palm readout: the normalized marked pressure limit is the
   Palm integral of the local candidate-value readout, with the lower defect
   coming from the missing legal cardinality and the upper defect from the
   frozen core.

## Exact remaining sub-gap

The remaining identification is the instantiation of the finite repair lower
bound for the concrete marked legal graph (legalMarkedGraph): the assignment
value of the actual candidate matching restricted to the original window is
exactly the sum of the local readout over the windowed matched edges, and its
missing cardinality is n minus the legal maximum cardinality of the window graph.
The squeeze and the defect bookkeeping are proved here; the concrete finite
repair instantiation is the paper's window-restriction legality statement.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- **Two-defect local-optimality squeeze.**  If the finite value T n is
sandwiched between vol n * J - lowerDefect n and vol n * J + upperDefect n, and
both normalized defects vanish, then T n / vol n tends to J. -/
theorem normalized_tendsto_of_twoSidedReadout
    (T vol lowerDefect upperDefect : ℕ → ℝ) (J : ℝ)
    (hvol : ∀ n, 0 < vol n)
    (hlower : ∀ n, vol n * J - lowerDefect n ≤ T n)
    (hupper : ∀ n, T n ≤ vol n * J + upperDefect n)
    (hlow : Tendsto (fun n => lowerDefect n / vol n) atTop (𝓝 0))
    (hup : Tendsto (fun n => upperDefect n / vol n) atTop (𝓝 0)) :
    Tendsto (fun n => T n / vol n) atTop (𝓝 J) := by
  have hlow' : ∀ n, J - lowerDefect n / vol n ≤ T n / vol n := by
    intro n
    have h := hlower n
    rw [le_div_iff₀ (hvol n)]
    have hmul : (J - lowerDefect n / vol n) * vol n = vol n * J - lowerDefect n := by
      rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt (hvol n))]
      ring
    rw [hmul]
    nlinarith [h]
  have hnonneg : ∀ n, -(lowerDefect n / vol n) ≤ T n / vol n - J := by
    intro n
    linarith [hlow' n]
  have hup' : ∀ n, T n / vol n ≤ upperDefect n / vol n + J := by
    intro n
    have h := hupper n
    rw [div_le_iff₀ (hvol n)]
    have hmul : (upperDefect n / vol n + J) * vol n = upperDefect n + vol n * J := by
      rw [add_mul, div_mul_cancel₀ _ (ne_of_gt (hvol n))]
      ring
    rw [hmul]
    nlinarith [h]
  have hle : ∀ n, T n / vol n - J ≤ upperDefect n / vol n := by
    intro n
    linarith [hup' n]
  have hbound : ∀ n, |T n / vol n - J| ≤
      |lowerDefect n / vol n| + |upperDefect n / vol n| := by
    intro n
    rw [abs_le]
    constructor
    · have h1 := le_abs_self (lowerDefect n / vol n)
      have h2 := abs_nonneg (upperDefect n / vol n)
      linarith [hnonneg n]
    · have h1 := le_abs_self (upperDefect n / vol n)
      have h2 := abs_nonneg (lowerDefect n / vol n)
      linarith [hle n]
  have hlow_abs : Tendsto (fun n => |lowerDefect n / vol n|) atTop (𝓝 0) := by
    simpa using hlow.abs
  have hup_abs : Tendsto (fun n => |upperDefect n / vol n|) atTop (𝓝 0) := by
    simpa using hup.abs
  have hlim : Tendsto (fun n => |lowerDefect n / vol n| + |upperDefect n / vol n|)
      atTop (𝓝 0) := by
    simpa using hlow_abs.add hup_abs
  have hzero : Tendsto (fun n => T n / vol n - J) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hlim
    filter_upwards with n
    simpa only [Real.norm_eq_abs] using hbound n
  have hstep : Tendsto (fun n => (T n / vol n - J) + J) atTop (𝓝 (0 + J)) :=
    hzero.add (tendsto_const_nhds (x := J))
  have heq : (fun n => (T n / vol n - J) + J) = fun n => T n / vol n := by
    funext n
    ring
  rw [heq] at hstep
  simpa using hstep

/-- **Lower bound from the finite legal repair.**  The finite repair lower bound
(assignment value <= legal maximum + missing cardinality times the edge bound)
gives the lower defect inequality of the squeeze. -/
theorem candidateWindowLowerBound_of_finiteRepair
    (readout vol lowerDefect : ℕ → ℝ) {J B : ℝ}
    (volpos : ∀ n, 0 < vol n)
    (missing : ℕ → ℝ)
    (hrepair : ∀ n, readout n ≥ vol n * J - missing n * B)
    (hdefect : ∀ n, lowerDefect n = missing n * B) :
    ∀ n, vol n * J - lowerDefect n ≤ readout n := by
  intro n
  rw [hdefect n]
  linarith [hrepair n]

/-- **Marked pressure readout from two-sided local optimality.**  Instantiation
with the window mass and the Palm readout of the local candidate value: the
lower defect is the missing legal cardinality defect and the upper defect is the
frozen-core defect. -/
theorem markedPressureReadout_of_twoSidedLocalOptimality
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (Jfun : PhysicalPairPalmMark (Fin q) → ℝ)
    (U : ℕ → Set (Fin q → ℝ))
    (hVol : ∀ n, 0 < volume.real (U n))
    (readout lowerDefect upperDefect : ℕ → ℝ)
    (hlower : ∀ n, volume.real (U n) *
        (∫ m, Jfun m ∂legalMarkedJointPalm q M.law) - lowerDefect n ≤ readout n)
    (hupper : ∀ n, readout n ≤ volume.real (U n) *
        (∫ m, Jfun m ∂legalMarkedJointPalm q M.law) + upperDefect n)
    (hlow : Tendsto (fun n => lowerDefect n / volume.real (U n)) atTop (𝓝 0))
    (hup : Tendsto (fun n => upperDefect n / volume.real (U n)) atTop (𝓝 0)) :
    Tendsto (fun n => readout n / volume.real (U n)) atTop
      (𝓝 (∫ m, Jfun m ∂legalMarkedJointPalm q M.law)) :=
  normalized_tendsto_of_twoSidedReadout readout (fun n => volume.real (U n))
    lowerDefect upperDefect (∫ m, Jfun m ∂legalMarkedJointPalm q M.law)
    hVol hlower hupper hlow hup

end OTSelector.Reconstruction
