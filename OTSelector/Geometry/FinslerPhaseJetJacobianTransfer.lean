import OTSelector.MeasureTheory.AreaFormula.ParameterizedJacobianTransfer
import OTSelector.Geometry.FinslerGraphPositionJacobi
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily

/-!
# The original physical Jacobian in the comparison's actual Jacobi frame

Matching joint phase jets imply matching joint position jets and physical Jacobians.
Only the smooth comparison needs a graph inverse. Its identical central position and
first derivative retain the original graph clock and longitudinal velocity, so its
actual Hamiltonian Jacobi matrix computes the original physical Jacobian.
-/

open Set Filter Matrix Module Manifold
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

set_option backward.isDefEq.respectTransparency false

variable {E W V ι M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Actual joint phase jets project to the same joint position derivative. -/
theorem chartPosition_same_firstJet_of_chartMomentum
    (F : ContinuousFinslerNorm E M) (old : M) {Γ₁ Γ₂ : W → ℝ → M}
    {q : W × ℝ} {D : (W × ℝ) →L[ℝ] E × (E →L[ℝ] ℝ)}
    (h₁ : HasFDerivAt (F.chartMomentumFamily old Γ₁) D q)
    (h₂ : HasFDerivAt (F.chartMomentumFamily old Γ₂) D q) :
    HasFDerivAt (fun p : W × ℝ ↦ extChartAt 𝓘(ℝ, E) old (Γ₁ p.1 p.2))
      (fderiv ℝ (fun p : W × ℝ ↦ extChartAt 𝓘(ℝ, E) old (Γ₂ p.1 p.2)) q) q ∧
    HasFDerivAt (fun p : W × ℝ ↦ extChartAt 𝓘(ℝ, E) old (Γ₂ p.1 p.2))
      (fderiv ℝ (fun p : W × ℝ ↦ extChartAt 𝓘(ℝ, E) old (Γ₂ p.1 p.2)) q) q := by
  have hp₁ := h₁.fst
  have hp₂ := h₂.fst
  rw [← hp₂.fderiv] at hp₁ hp₂
  exact ⟨hp₁, hp₂⟩

/-- Matching actual phase jets give equal original and comparison physical Jacobians. -/
theorem parameterizedJacobian_eq_of_chartMomentum_same_firstJet
    (F : ContinuousFinslerNorm E M) (old : M) {Γ₁ Γ₂ : W → ℝ → M}
    {w : W} {t : ℝ} {D : (W × ℝ) →L[ℝ] E × (E →L[ℝ] ℝ)}
    (h₁ : HasFDerivAt (F.chartMomentumFamily old Γ₁) D (w, t))
    (h₂ : HasFDerivAt (F.chartMomentumFamily old Γ₂) D (w, t))
    (ℓ : (ℝ × W) ≃L[ℝ] E) :
    parameterizedJacobian (fun p : ℝ × W ↦ extChartAt 𝓘(ℝ, E) old (Γ₁ p.2 p.1)) ℓ (t, w) =
      parameterizedJacobian (fun p : ℝ × W ↦ extChartAt 𝓘(ℝ, E) old (Γ₂ p.2 p.1)) ℓ (t, w) :=
  parameterizedJacobian_timeFirst_eq_of_hasFDerivAt h₁.fst h₂.fst ℓ

variable [FiniteDimensional ℝ W] [Fintype ι] [DecidableEq ι]

/-- The original map uses the comparison's true graph inverse and Hamiltonian position
matrix. Its own graph time and longitudinal derivative remain explicit in the formula. -/
theorem parameterizedJacobian_graphPhase_of_same_firstJet
    (F : ContinuousFinslerNorm E M) (old : M)
    (bW : Basis ι ℝ W) (bV : Basis ι ℝ V)
    (A : E ≃L[ℝ] (ℝ × V)) (ℓ : (ℝ × W) ≃L[ℝ] E)
    {γ Γ : W × ℝ → E} {w : W} {t : ℝ}
    (hvalue : γ (w, t) = Γ (w, t))
    (hγ : HasFDerivAt γ (fderiv ℝ Γ (w, t)) (w, t))
    (hΓ : DifferentiableAt ℝ Γ (w, t))
    {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap (A ∘ Γ))
    (hz : (w, t) ∈ e.source)
    (hv : (fderiv ℝ (A ∘ Γ) (w, t) (0, 1)).1 ≠ 0)
    (hP : DifferentiableAt ℝ
      (fun z ↦ F.adaptedGraphPhase old A (A ∘ Γ) e (z, (A (Γ (w, t))).1)) w) :
    let s := (A (γ (w, t))).1
    let c := (fderiv ℝ (A ∘ γ) (w, t) (0, 1)).1
    let J := vectorFamilyMatrix bV (fun j ↦
      (fderiv ℝ (fun z ↦ F.adaptedGraphPhase old A (A ∘ Γ) e (z, s)) w (bW j)).1)
    HasDerivAt (fun r ↦ (e.symm (w, r)).2) c⁻¹ s ∧
      parameterizedJacobian (fun p : ℝ × W ↦ γ (p.2, p.1)) ℓ (t, w) =
        |c| * |J.det| * |(LinearMap.toMatrix (timeLabelBasis bV) (timeLabelBasis bW)
          (ℓ.trans A).symm.toLinearEquiv.toLinearMap).det| := by
  have hderiv : fderiv ℝ (A ∘ γ) (w, t) = fderiv ℝ (A ∘ Γ) (w, t) :=
    (A.hasFDerivAt.comp (w, t) hγ).fderiv.trans
      (A.hasFDerivAt.comp (w, t) hΓ.hasFDerivAt).fderiv.symm
  have hJacobian := parameterizedJacobian_timeFirst_eq_of_hasFDerivAt hγ hΓ.hasFDerivAt ℓ
  dsimp only
  rw [hvalue, hderiv, hJacobian]
  exact F.parameterizedJacobian_adaptedGraphPhase_data old bW bV A ℓ he hz hΓ hv hP

end OTSelector.Geometry.ContinuousFinslerNorm
