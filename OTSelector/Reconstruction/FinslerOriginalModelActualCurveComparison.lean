import OTSelector.Geometry.Finsler.Calibration.SeedReadoutCoordinates
import OTSelector.Reconstruction.FinslerOriginalMomentumEligibleNodes

/-!
# Model-versus-actual comparison at nonzero clock

This file closes gap (i) of FinslerOriginalNodePositionIdentification.lean.

The literal node position originalMomentumNodePosition is a value of the model
path originalSeedCompletePath, whose velocity is the intrinsic label Hessian
inverse times the constant original pair momentum.  The actual chart flow of the
calibrated curve is a different object.  This file proves the sharp comparison
available from the model side:

1. intervalIntegral_mulVec: the interval integral of matrix-vector products is
   the matrix integral applied to the vector.
2. eq_originalSeedCompletePath_of_hasDerivAt: **exact identity**.  Any chart
   curve whose chart coordinate velocity equals the model velocity at every
   intermediate clock and which starts at the same source mark is exactly the
   model path.  This is the uniqueness of solutions of the linear model ODE,
   proved through the fundamental theorem of calculus; it needs no geometric
   input.
3. norm_sub_originalSeedCompletePath_le_of_velocity_defect: **error bound**.
   If the actual chart velocity deviates from the model velocity by at most
   delta on the clock interval, the chart curve stays within delta times the
   clock length of the model path.
4. eq_originalMomentumNodePosition_of_hasDerivAt and
   norm_originalMomentumNodePosition_sub_le_of_velocity_defect: the same two
   statements for the literal node position of a legal marked physical edge,
   anchored at its source mark and source clock.

The remaining gap is purely geometric: supplying the hypothesis that the actual
chart flow of the calibrated curve has the model velocity, i.e. that the chart
coordinate velocity is the intrinsic label Hessian inverse times the constant
chart momentum.  The model freezes the Hessian at the seed label w instead of
evaluating it along the actual curve, so the identity is exact only under that
frozen-label hypothesis; the deviation is bounded by the two above lemmas.
-/
open Set Function Filter MeasureTheory Matrix Module Manifold Metric
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical Topology BigOperators

noncomputable section
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace OTSelector.Reconstruction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-! ## Interval integrals of the model kernel -/

/-- The matrix-vector product as a continuous linear map, evaluated. -/
@[simp] theorem completePathMatrixApply_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (A : Matrix ι ι ℝ) :
    completePathMatrixApply p A = A *ᵥ p := rfl

/-- **Matrix-vector interval integrals.**  The interval integral of the
matrix-vector products is the matrix interval integral applied to the fixed
vector. -/
theorem intervalIntegral_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ℝ → Matrix ι ι ℝ} {p : ι → ℝ} {a b : ℝ}
    (hA : IntervalIntegrable A volume a b) :
    (∫ s in a..b, A s *ᵥ p) = (∫ s in a..b, A s) *ᵥ p := by
  have h := ContinuousLinearMap.intervalIntegral_comp_comm
    (completePathMatrixApply p) hA
  simpa only [completePathMatrixApply_apply] using h

/-- The literal original kernel, integrated against the fixed original momentum,
is the kernel integral applied to the momentum. -/
theorem intervalIntegral_originalSeedKernel_mulVec
    (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (p : Fin (finrank ℝ S.covector.ker) → ℝ) {a b : ℝ}
    (hK : IntervalIntegrable (originalSeedKernel S w) volume a b) :
    (∫ s in a..b, originalSeedKernel S w s *ᵥ p) =
      (∫ s in a..b, originalSeedKernel S w s) *ᵥ p :=
  intervalIntegral_mulVec hK

/-! ## Exact model identity under the model velocity -/

/-- **Exact identity of a chart curve with the model path.**  Any chart curve
whose chart velocity at every intermediate clock is the model velocity -- the
intrinsic label Hessian inverse times the fixed original momentum -- and which
starts at the same source mark is exactly the model complete path.  This is the
uniqueness of the linear model ODE, proved by the fundamental theorem of
calculus. -/
theorem eq_originalSeedCompletePath_of_hasDerivAt
    (S : CalibratedLevelSeedPatch F u) {w : S.covector.ker}
    {p : Fin (finrank ℝ S.covector.ker) → ℝ}
    {γ : ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ)}
    {x : Fin (finrank ℝ S.covector.ker) → ℝ} {t₀ t : ℝ}
    (hderiv : ∀ s ∈ uIcc t₀ t,
      HasDerivAt γ (originalSeedKernel S w (s - (S.level : ℝ)) *ᵥ p) s)
    (hintv : IntervalIntegrable
      (fun s ↦ originalSeedKernel S w (s - (S.level : ℝ)) *ᵥ p) volume t₀ t)
    (hintK : IntervalIntegrable
      (fun s ↦ originalSeedKernel S w (s - (S.level : ℝ))) volume t₀ t)
    (hγ : γ t₀ = x) :
    γ t = x + (∫ r in (t₀ - (S.level : ℝ))..(t - (S.level : ℝ)),
      originalSeedKernel S w r) *ᵥ p := by
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hintv
  have hcomm : (∫ s in t₀..t,
      originalSeedKernel S w (s - (S.level : ℝ)) *ᵥ p) =
      (∫ s in t₀..t, originalSeedKernel S w (s - (S.level : ℝ))) *ᵥ p :=
    intervalIntegral_mulVec
      (A := fun s ↦ originalSeedKernel S w (s - (S.level : ℝ))) hintK
  have hshift : (∫ s in t₀..t, originalSeedKernel S w (s - (S.level : ℝ))) =
      ∫ r in t₀ - (S.level : ℝ)..t - (S.level : ℝ), originalSeedKernel S w r :=
    intervalIntegral.integral_comp_sub_right
      (f := fun r ↦ originalSeedKernel S w r) (S.level : ℝ)
  calc γ t = γ t₀ + ∫ s in t₀..t,
        originalSeedKernel S w (s - (S.level : ℝ)) *ᵥ p := by
        rw [hfund]; abel
    _ = x + ∫ s in t₀..t,
        originalSeedKernel S w (s - (S.level : ℝ)) *ᵥ p := by rw [hγ]
    _ = x + ((∫ s in t₀..t,
        originalSeedKernel S w (s - (S.level : ℝ))) *ᵥ p) := by rw [hcomm]
    _ = x + (∫ r in (t₀ - (S.level : ℝ))..(t - (S.level : ℝ)),
        originalSeedKernel S w r) *ᵥ p := by rw [hshift]

/-- **Variation-of-constants error bound.**  If the actual chart velocity
deviates from the model velocity by at most delta on the clock interval, the
actual chart curve stays within delta times the clock length from the model
path. -/
theorem norm_sub_originalSeedCompletePath_le_of_velocity_defect
    (S : CalibratedLevelSeedPatch F u) {w : S.covector.ker}
    {p : Fin (finrank ℝ S.covector.ker) → ℝ}
    {γ : ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ)}
    {v : ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ)}
    {x : Fin (finrank ℝ S.covector.ker) → ℝ} {t₀ t : ℝ} {δ : ℝ}
    (hderiv : ∀ s ∈ uIcc t₀ t, HasDerivAt γ (v s) s)
    (hintv : IntervalIntegrable v volume t₀ t)
    (hintK : IntervalIntegrable
      (fun s ↦ originalSeedKernel S w (s - (S.level : ℝ))) volume t₀ t)
    (hintmodel : IntervalIntegrable
      (fun s ↦ originalSeedKernel S w (s - (S.level : ℝ)) *ᵥ p) volume t₀ t)
    (hγ : γ t₀ = x)
    (hdefect : ∀ s ∈ uIoc t₀ t,
      ‖v s - originalSeedKernel S w (s - (S.level : ℝ)) *ᵥ p‖ ≤ δ) :
    ‖γ t - (x + (∫ r in (t₀ - (S.level : ℝ))..(t - (S.level : ℝ)),
      originalSeedKernel S w r) *ᵥ p)‖ ≤ δ * |t - t₀| := by
  have hcomm : (∫ s in t₀..t,
      originalSeedKernel S w (s - (S.level : ℝ)) *ᵥ p) =
      (∫ s in t₀..t, originalSeedKernel S w (s - (S.level : ℝ))) *ᵥ p :=
    intervalIntegral_mulVec
      (A := fun s ↦ originalSeedKernel S w (s - (S.level : ℝ))) hintK
  have hshift : (∫ s in t₀..t, originalSeedKernel S w (s - (S.level : ℝ))) =
      ∫ r in t₀ - (S.level : ℝ)..t - (S.level : ℝ), originalSeedKernel S w r :=
    intervalIntegral.integral_comp_sub_right
      (f := fun r ↦ originalSeedKernel S w r) (S.level : ℝ)
  have hshift_v : (∫ s in t₀..t,
      originalSeedKernel S w (s - (S.level : ℝ)) *ᵥ p) =
      (∫ r in t₀ - (S.level : ℝ)..t - (S.level : ℝ),
        originalSeedKernel S w r) *ᵥ p := by
    rw [hcomm, hshift]
  rw [← hshift_v]
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hintv
  have hγt : γ t = x + ∫ s in t₀..t, v s := by
    rw [hfund, hγ]; abel
  have hdiff : γ t - (x + ∫ s in t₀..t,
        originalSeedKernel S w (s - (S.level : ℝ)) *ᵥ p) =
      ∫ s in t₀..t,
        (v s - originalSeedKernel S w (s - (S.level : ℝ)) *ᵥ p) := by
    rw [hγt, intervalIntegral.integral_sub hintv hintmodel]
    abel
  rw [hdiff]
  exact intervalIntegral.norm_integral_le_of_norm_le_const hdefect

/-! ## The literal node position of a legal marked physical edge -/

/-- **Node position identification under the model velocity.**  If a chart
curve starts at the source mark of a legal marked physical edge at the source
clock and has the model velocity with the original inverse-compliance momentum,
then at every clock it is exactly the literal node position. -/
theorem eq_originalMomentumNodePosition_of_hasDerivAt
    (S : CalibratedLevelSeedPatch F u) {w : S.covector.ker}
    (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) {c : ℝ}
    {γ : ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ)}
    (hderiv : ∀ s ∈ uIcc (((physicalPairAnchor e).2).1.1) c,
      HasDerivAt γ (originalSeedKernel S w (s - (S.level : ℝ)) *ᵥ
        originalSeedPairMomentum S w (physicalPairAnchor e).2) s)
    (hintv : IntervalIntegrable (fun s ↦
      originalSeedKernel S w (s - (S.level : ℝ)) *ᵥ
        originalSeedPairMomentum S w (physicalPairAnchor e).2)
      volume (((physicalPairAnchor e).2).1.1) c)
    (hintK : IntervalIntegrable
      (fun s ↦ originalSeedKernel S w (s - (S.level : ℝ)))
      volume (((physicalPairAnchor e).2).1.1) c)
    (hγ : γ (((physicalPairAnchor e).2).1.1) = e.1.1) :
    γ c = originalMomentumNodePosition S w c e := by
  rw [originalMomentumNodePosition, originalSeedCompletePath]
  exact eq_originalSeedCompletePath_of_hasDerivAt S hderiv hintv hintK hγ

/-- **Node position error bound.**  If the actual chart velocity of the edge
path deviates from the model velocity by at most delta on the clock interval,
then its chart position at clock c is within delta times the clock length of the
literal node position. -/
theorem norm_originalMomentumNodePosition_sub_le_of_velocity_defect
    (S : CalibratedLevelSeedPatch F u) {w : S.covector.ker}
    (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) {c : ℝ}
    {γ : ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ)}
    {v : ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ)} {δ : ℝ}
    (hderiv : ∀ s ∈ uIcc (((physicalPairAnchor e).2).1.1) c,
      HasDerivAt γ (v s) s)
    (hintv : IntervalIntegrable v volume (((physicalPairAnchor e).2).1.1) c)
    (hintK : IntervalIntegrable
      (fun s ↦ originalSeedKernel S w (s - (S.level : ℝ)))
      volume (((physicalPairAnchor e).2).1.1) c)
    (hintmodel : IntervalIntegrable (fun s ↦
      originalSeedKernel S w (s - (S.level : ℝ)) *ᵥ
        originalSeedPairMomentum S w (physicalPairAnchor e).2)
      volume (((physicalPairAnchor e).2).1.1) c)
    (hγ : γ (((physicalPairAnchor e).2).1.1) = e.1.1)
    (hdefect : ∀ s ∈ uIoc (((physicalPairAnchor e).2).1.1) c,
      ‖v s - originalSeedKernel S w (s - (S.level : ℝ)) *ᵥ
        originalSeedPairMomentum S w (physicalPairAnchor e).2‖ ≤ δ) :
    ‖γ c - originalMomentumNodePosition S w c e‖ ≤
      δ * |c - (((physicalPairAnchor e).2).1.1)| := by
  rw [originalMomentumNodePosition, originalSeedCompletePath]
  exact norm_sub_originalSeedCompletePath_le_of_velocity_defect S
    hderiv hintv hintK hintmodel hγ hdefect

end OTSelector.Reconstruction
