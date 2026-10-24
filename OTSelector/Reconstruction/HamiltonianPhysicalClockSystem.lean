import OTSelector.Reconstruction.ClosedJacobiConditionalMoments
import OTSelector.Reconstruction.JacobiComplianceClock

/-!
# The unchanged closed Hamiltonian system in actual physical time

An actual positive nonlinear graph clock composes the original Jacobi pair and multiplies
all three actual Hamiltonian coefficients by its same speed. The resulting physical-time
system retains the Wronskian, positive velocity coefficient and complete phase rank.
-/

open Set Matrix
open scoped Topology Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- Positive actual clock changes preserve the full closed Hamiltonian-Jacobi system,
with its original pair and its actual three speed-scaled coefficients. -/
theorem ClosedHamiltonianJacobiSystem.physicalClock
    {J P A B C : ℝ → Matrix n n ℝ} {a b l h : ℝ}
    (H : ClosedHamiltonianJacobiSystem J P A B C a b)
    {s v : ℝ → ℝ} (hsv : ∀ t∈Icc l h, HasDerivAt s (v t) t)
    (hv : ContinuousOn v (Icc l h)) (hvpos : ∀ t∈Icc l h, 0<v t)
    (himage : MapsTo s (Icc l h) (Icc a b)) :
    ClosedHamiltonianJacobiSystem (J∘s) (P∘s)
      (fun t ↦ v t•A (s t)) (fun t ↦ v t•B (s t)) (fun t ↦ v t•C (s t)) l h := by
  have hs : ContinuousOn s (Icc l h) :=
    fun t ht ↦ (hsv t ht).continuousAt.continuousWithinAt
  have hsys := fun t (ht : t∈Icc l h) ↦ hamiltonian_system_graphClock
    (H.position_derivative (s t) (himage ht)) (H.momentum_derivative (s t) (himage ht)) (hsv t ht)
  exact {
    position_derivative := fun t ht ↦ (hsys t ht).1
    momentum_derivative := fun t ht ↦ (hsys t ht).2
    continuous_A := hv.smul (H.continuous_A.comp hs himage)
    continuous_B := hv.smul (H.continuous_B.comp hs himage)
    continuous_C := hv.smul (H.continuous_C.comp hs himage)
    symmetric_A := fun t ht ↦ by rw [Matrix.transpose_smul,H.symmetric_A (s t) (himage ht)]
    symmetric_C := fun t ht ↦ by rw [Matrix.transpose_smul,H.symmetric_C (s t) (himage ht)]
    positive_C := fun t ht ↦ (H.positive_C (s t) (himage ht)).smul (hvpos t ht)
    wronskian := fun t ht ↦ H.wronskian (s t) (himage ht)
    phase_rank := fun t ht ↦ H.phase_rank (s t) (himage ht) }

end OTSelector.Reconstruction
