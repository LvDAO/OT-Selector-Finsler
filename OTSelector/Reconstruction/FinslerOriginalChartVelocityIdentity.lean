import OTSelector.Geometry.Finsler.AdaptedGraphJacobi
import OTSelector.Reconstruction.FinslerOriginalModelActualCurveComparison

/-!
# Chart-velocity identity for the calibrated flow

This file assembles sub-gap (a) of FinslerOriginalModelActualCurveComparison.lean: the
derivative-level identity between the actual chart flow of the calibrated curve and the
inverse intrinsic label Hessian acting on momentum.

What is proved here, from the existing adapted-graph Hamiltonian machinery:

1. graphHamiltonian_field_fst_eq_legendrePreimage: the velocity component of the actual
   graph Hamiltonian field is the second component of the inverse parametric Legendre
   image of the position-momentum state. This is the pointwise chart-velocity identity:
   the actual chart velocity is recovered from the actual momentum by inverting the
   genuine Legendre branch (no approximation and no frozen label).
2. graphHamiltonian_field_fst_eq_chartVelocity: consequently, if the parametric Legendre
   branch sends an actual chart phase z to the position-momentum state p, then the
   velocity component of the field at p is exactly the actual chart velocity z.2.
3. graphHamiltonian_field_fst_fderiv_snd_eq_inverseMomentumDerivative: the derivative of
   the velocity component with respect to the momentum, at fixed position, is the
   momentum derivative of the genuine inverse Legendre branch (the C block of the actual
   nonautonomous graph Hamiltonian).
4. graphHamiltonian_field_fst_fderiv_snd_eq_inverseHessian: that momentum derivative is
   the inverse of the actual vertical Hessian of the graph Lagrangian. This is the
   derivative-level form of "chart velocity equals the inverse intrinsic label Hessian
   times the momentum", pointwise at the actual flow state.
5. graphHamiltonian_field_fst_fderiv_snd_eq_inverseHessian_of_finsler: the same identity
   for the actual adapted graph Lagrangian of an original smooth strongly convex Finsler
   norm, with the positivity of the vertical Hessian discharged from the original length.
6. chartVelocityDefect: the literal frozen-label velocity defect, and
   chartVelocityDefect_eq_hessianDifference: its Hessian-difference form
   ||(C(c) - originalSeedKernel(c)) p||.
7. norm_sub_originalSeedCompletePath_le_integral_chartVelocityDefect: the true deviation
   integral estimate -- the model-versus-actual path distance is bounded by the integral
   of the frozen-label velocity defect, with no constant-defect hypothesis.

The remaining gap is the identification of the frozen-label intrinsic label Hessian with
the matrix of the actual vertical Hessian in the label basis, i.e. the exact linear-algebra
comparison of familyLabelHessianMatrix with the adapted graph vertical Hessian along the
actual curve, together with the Lipschitz bound on the resulting kernel difference.
-/
open Set Function Filter MeasureTheory Matrix Module Manifold Metric Bundle
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical Topology BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace OTSelector.Geometry

section Generic

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Velocity as the inverse Legendre image.**  The velocity component of the actual graph
Hamiltonian field is the second component of the inverse parametric Legendre image of the
position-momentum state. This is the pointwise chart-velocity identity. -/
theorem graphHamiltonian_field_fst_eq_legendrePreimage
    {L : (ℝ × V) × V → ℝ}
    {e : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ))}
    {t : ℝ} {p : V × (V →L[ℝ] ℝ)} :
    (GraphHamiltonian.field L e t p).1 = (e.symm ((t, p.1), p.2)).2 := rfl

/-- **Chart-velocity identity for a calibrated flow state.**  If the parametric Legendre
branch sends an actual chart phase z to the position-momentum state p, then the velocity
component of the Hamiltonian field at p is exactly the actual chart velocity z.2. -/
theorem graphHamiltonian_field_fst_eq_chartVelocity
    {L : (ℝ × V) × V → ℝ}
    {e : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ))}
    {t : ℝ} {p : V × (V →L[ℝ] ℝ)} {z : (ℝ × V) × V}
    (hz : z ∈ e.source) (hzp : e z = ((t, p.1), p.2)) :
    (GraphHamiltonian.field L e t p).1 = z.2 := by
  rw [graphHamiltonian_field_fst_eq_legendrePreimage, ← hzp, e.left_inv hz]

/-- **Momentum differential of the chart velocity.**  The derivative of the velocity
component of the actual field with respect to the momentum, at fixed position, is the
momentum derivative of the genuine inverse Legendre branch, i.e. the C block of the actual
nonautonomous graph Hamiltonian. -/
theorem graphHamiltonian_field_fst_fderiv_snd_eq_inverseMomentumDerivative
    {L : (ℝ × V) × V → ℝ}
    {e : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ))}
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {t : ℝ} {p : V × (V →L[ℝ] ℝ)} (hp : ((t, p.1), p.2) ∈ e.target)
    (q : V →L[ℝ] ℝ) :
    fderiv ℝ (fun q' : V × (V →L[ℝ] ℝ) ↦ (GraphHamiltonian.field L e t q').1) p
        ((0 : V), q) = GraphLegendre.inverseMomentumDerivative e ((t, p.1), p.2) q := by
  have hjoint : DifferentiableAt ℝ
      (fun x : (ℝ × V) × (V →L[ℝ] ℝ) ↦
        GraphHamiltonian.field L e x.1.1 (x.1.2, x.2)) ((t, p.1), p.2) :=
    ((GraphHamiltonian.contDiffOn_field hL hG).contDiffAt
      (e.open_target.mem_nhds hp)).differentiableAt (by simp)
  have hsplit : DifferentiableAt ℝ
      (fun q : V × (V →L[ℝ] ℝ) ↦ ((t, q.1), q.2)) p :=
    ((differentiableAt_const (𝕜 := ℝ) (x := p) t).prodMk
      (differentiableAt_fst (p := p))).prodMk (differentiableAt_snd (p := p))
  have hX : DifferentiableAt ℝ (GraphHamiltonian.field L e t) p := by
    simpa only [Function.comp_def] using hjoint.comp p hsplit
  have hfst : fderiv ℝ
        (fun q' : V × (V →L[ℝ] ℝ) ↦ (GraphHamiltonian.field L e t q').1) p =
      (ContinuousLinearMap.fst ℝ V (V →L[ℝ] ℝ)).comp
        (fderiv ℝ (GraphHamiltonian.field L e t) p) :=
    (hX.hasFDerivAt.fst).fderiv
  rw [hfst, ContinuousLinearMap.comp_apply]
  change ((fderiv ℝ (GraphHamiltonian.field L e t) p) ((0 : V), q)).1 =
    GraphLegendre.inverseMomentumDerivative e ((t, p.1), p.2) q
  rw [GraphHamiltonian.field_fderiv_fst hL hG hp ((0 : V), q)]
  rfl

/-- **Inverse-Hessian form of the velocity momentum differential.**  The momentum
derivative of the actual chart velocity is the inverse of the actual vertical Hessian of the
graph Lagrangian: the derivative-level form of "chart velocity is the inverse intrinsic
label Hessian times the momentum", pointwise at the actual flow state. -/
theorem graphHamiltonian_field_fst_fderiv_snd_eq_inverseHessian
    [FiniteDimensional ℝ V]
    {L : (ℝ × V) × V → ℝ}
    {e : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ))}
    (he : (e : ((ℝ × V) × V) → ((ℝ × V) × (V →L[ℝ] ℝ))) = parametricLegendre L)
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {t : ℝ} {p : V × (V →L[ℝ] ℝ)} (hp : ((t, p.1), p.2) ∈ e.target)
    (q : V →L[ℝ] ℝ)
    (hpos : ∀ w : V, w ≠ 0 →
      0 < GraphLegendre.verticalHessian L (e.symm ((t, p.1), p.2)) w w) :
    fderiv ℝ (fun q' : V × (V →L[ℝ] ℝ) ↦ (GraphHamiltonian.field L e t q').1) p
        ((0 : V), q) =
      ContinuousLinearMap.inverse
        (GraphLegendre.verticalHessian L (e.symm ((t, p.1), p.2))) q := by
  rw [graphHamiltonian_field_fst_fderiv_snd_eq_inverseMomentumDerivative hL hG hp q]
  exact congrArg (fun F : (V →L[ℝ] ℝ) →L[ℝ] V ↦ F q)
    (GraphLegendre.inverseMomentumDerivative_eq_inverse he hp
      (hL.contDiffAt (e.open_source.mem_nhds (e.map_target hp)))
      ((hG.contDiffAt (e.open_target.mem_nhds hp)).differentiableAt (by simp)) hpos)

end Generic

section Finsler

variable {E V M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

/-- **Inverse-Hessian momentum differential for the original Finsler graph flow.**  For the
actual adapted graph Lagrangian of an original smooth strongly convex Finsler norm, the
momentum derivative of the chart velocity is the inverse of the actual vertical Hessian; the
positivity needed for the inverse is discharged from the original length Hessian. -/
theorem graphHamiltonian_field_fst_fderiv_snd_eq_inverseHessian_of_finsler
    (hF : F.IsSmoothStronglyConvex) (old : M) (T : E ≃L[ℝ] (ℝ × V))
    {e : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ))}
    (he : (e : ((ℝ × V) × V) → ((ℝ × V) × (V →L[ℝ] ℝ))) =
      parametricLegendre (F.adaptedGraphLagrangian old T))
    (hsub : e.source ⊆ (T.symm ⁻¹' (extChartAt 𝓘(ℝ, E) old).target) ×ˢ univ)
    (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {t : ℝ} {p : V × (V →L[ℝ] ℝ)} (hp : ((t, p.1), p.2) ∈ e.target)
    (q : V →L[ℝ] ℝ) :
    fderiv ℝ (fun q' : V × (V →L[ℝ] ℝ) ↦
        (GraphHamiltonian.field (F.adaptedGraphLagrangian old T) e t q').1) p
        ((0 : V), q) =
      ContinuousLinearMap.inverse
        (GraphLegendre.verticalHessian (F.adaptedGraphLagrangian old T)
          (e.symm ((t, p.1), p.2))) q := by
  have hz : e.symm ((t, p.1), p.2) ∈ e.source := e.map_target hp
  have hx : T.symm (e.symm ((t, p.1), p.2)).1 ∈
      (extChartAt 𝓘(ℝ, E) old).target := (hsub hz).1
  exact graphHamiltonian_field_fst_fderiv_snd_eq_inverseHessian he
    ((ContinuousFinslerNorm.IsSmoothStronglyConvex.contDiffOn_adaptedGraphLagrangian
      hF old T).mono hsub) hG hp q
    (fun w hw ↦
      ContinuousFinslerNorm.IsSmoothStronglyConvex.adaptedGraphLagrangian_hessian_pos
        hF old T hx (e.symm ((t, p.1), p.2)).2 hw)

end Finsler

end OTSelector.Geometry

namespace OTSelector.Reconstruction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The literal frozen-label chart velocity defect: the distance between the actual chart
velocity and the model velocity of the frozen seed label kernel. -/
def chartVelocityDefect (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (p : Fin (finrank ℝ S.covector.ker) → ℝ)
    (v : ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ)) (c : ℝ) : ℝ :=
  ‖v c - originalSeedKernel S w (c - (S.level : ℝ)) *ᵥ p‖

/-- **Hessian-difference form of the frozen-label defect.**  If the actual chart velocity is
the actual inverse Hessian applied to the fixed momentum, the frozen-label defect is exactly
the difference of the actual inverse Hessian and the frozen seed label kernel applied to that
momentum. -/
theorem chartVelocityDefect_eq_hessianDifference (S : CalibratedLevelSeedPatch F u)
    {w : S.covector.ker} {p : Fin (finrank ℝ S.covector.ker) → ℝ}
    {v : ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ)}
    {A : ℝ → Matrix (Fin (finrank ℝ S.covector.ker))
      (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hA : ∀ c, v c = A c *ᵥ p) (c : ℝ) :
    chartVelocityDefect S w p v c =
      ‖(A c - originalSeedKernel S w (c - (S.level : ℝ))) *ᵥ p‖ := by
  rw [chartVelocityDefect, hA c, Matrix.sub_mulVec]

/-- **True deviation integral estimate.**  The distance between the actual chart curve and
the frozen-label model path is bounded by the integral of the frozen-label velocity defect
over the clock interval: no constant-defect hypothesis is needed. This is the precise form in
which the kernel-difference error enters the model-versus-actual comparison. -/
theorem norm_sub_originalSeedCompletePath_le_integral_chartVelocityDefect
    (S : CalibratedLevelSeedPatch F u) {w : S.covector.ker}
    {p : Fin (finrank ℝ S.covector.ker) → ℝ}
    {γ : ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ)}
    {v : ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ)}
    {x : Fin (finrank ℝ S.covector.ker) → ℝ} {t₀ t : ℝ}
    (hderiv : ∀ s ∈ uIcc t₀ t, HasDerivAt γ (v s) s)
    (hintv : IntervalIntegrable v volume t₀ t)
    (hintK : IntervalIntegrable
      (fun s ↦ originalSeedKernel S w (s - (S.level : ℝ))) volume t₀ t)
    (hintmodel : IntervalIntegrable
      (fun s ↦ originalSeedKernel S w (s - (S.level : ℝ)) *ᵥ p) volume t₀ t)
    (hγ : γ t₀ = x) :
    ‖γ t - (x + (∫ r in (t₀ - (S.level : ℝ))..(t - (S.level : ℝ)),
      originalSeedKernel S w r) *ᵥ p)‖ ≤
      ∫ s in Set.uIoc t₀ t, chartVelocityDefect S w p v s := by
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
  have hdiff : γ t - (x + (∫ s in t₀..t,
        originalSeedKernel S w (s - (S.level : ℝ)) *ᵥ p)) =
      ∫ s in t₀..t,
        (v s - originalSeedKernel S w (s - (S.level : ℝ)) *ᵥ p) := by
    rw [hγt, intervalIntegral.integral_sub hintv hintmodel]
    abel
  rw [hdiff]
  simpa only [chartVelocityDefect] using
    (intervalIntegral.norm_integral_le_integral_norm_uIoc
      (f := fun s ↦ v s - originalSeedKernel S w (s - (S.level : ℝ)) *ᵥ p)
      (a := t₀) (b := t))

end OTSelector.Reconstruction
