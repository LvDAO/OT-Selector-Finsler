import OTSelector.Geometry.Finsler.AdaptedGraphJacobi
import OTSelector.Geometry.Finsler.IntrinsicLabelHessian
import OTSelector.Reconstruction.FinslerOriginalChartVelocityIdentity

/-!
# Vertical Hessian and label Hessian matrix assembly

This file completes sub-gap (a) of FinslerOriginalChartVelocityIdentity.lean: the matrix
representation identifying the actual adapted-graph vertical Hessian of the original length
with familyLabelHessianMatrix in the label basis.

The assembly has two layers.

1. familyLabelHessianMatrix_eq_chartLength_hessianMatrix: the intrinsic label Hessian
   matrix is the matrix of the chart-length fiber Hessian evaluated at the actual chart
   state, in the basis obtained by transporting the label basis through the genuine
   chart differential of the label family. This is the Hessian equality transported along
   the immersion (chartLength_hessian_mfderiv_extChartAt).
2. familyLabelHessianMatrix_eq_adaptedGraphVerticalHessian: for any clock splitting
   A : E = R x V of the chart tangent space whose first coordinate pairs the actual
   label-family time direction with 1 and whose kernel contains the actual label
   directions, the label Hessian matrix is exactly the vertical Hessian of the actual
   adapted graph Lagrangian of the original length, in the transported label basis
   (adaptedGraphLagrangian_hessian_eq).

The clock splitting itself is a linear-algebra datum (a clock functional with value one on
the time direction and vanishing on the label directions, plus a complement equivalence);
the file states the assembly conditionally on exactly that datum and instantiates it for
the calibrated seed patch.

The label-basis momentum form is then recorded: the model velocity originalSeedKernel * p
is the inverse family label Hessian applied to the momentum, the family label Hessian of
that velocity recovers the momentum, and the frozen-label defect is the difference of the
actual inverse Hessian and the frozen family label Hessian inverse applied to the momentum.
-/
open Set Function Filter MeasureTheory Matrix Module Manifold Metric Bundle
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical Topology BigOperators

noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E W M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

/-- The actual label-family differential in the intrinsic fiber model. -/
noncomputable def familyLabelVelocityDifferential (Γ : W × ℝ → M) (q : W × ℝ) :
    (W × ℝ) →L[ℝ] E :=
  (tangentFiberModelEquiv (Γ q)).symm.toContinuousLinearMap.comp
    (mfderiv 𝓘(ℝ, W × ℝ) 𝓘(ℝ, E) Γ q)

/-- The genuine chart differential of the actual label family. -/
noncomputable def familyChartVelocityDifferential (old : M) (Γ : W × ℝ → M) (q : W × ℝ) :
    E →L[ℝ] E :=
  (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) old) (Γ q)).comp
    (tangentFiberModelEquiv (Γ q)).toContinuousLinearMap

/-- Entrywise form of the intrinsic label Hessian matrix in terms of the actual label-family
differentials. -/
theorem familyLabelHessianMatrix_apply (bW : Basis ι ℝ W) {Γ : W × ℝ → M} (q : W × ℝ)
    (i j : ι) :
    familyLabelHessianMatrix F bW Γ q i j =
      fderiv ℝ (fderiv ℝ (fun v : E ↦
          (F.toFun ⟨Γ q, tangentFiberModelEquiv (Γ q) v⟩ : ℝ)))
        (familyLabelVelocityDifferential (E := E) Γ q ((0 : W), (1 : ℝ)))
        (familyLabelVelocityDifferential (E := E) Γ q (bW j, 0))
        (familyLabelVelocityDifferential (E := E) Γ q (bW i, 0)) := rfl

/-- **The label Hessian matrix in the transported chart basis.**  The intrinsic label
Hessian matrix is the chart-length fiber Hessian at the actual chart state, evaluated in
the transported label basis. This is the Hessian equality transported along the immersion. -/
theorem familyLabelHessianMatrix_eq_chartLength_hessianMatrix
    (hF : F.IsSmoothStronglyConvex) (bW : Basis ι ℝ W) {Γ : W × ℝ → M}
    {old : M} {q : W × ℝ} (hx : Γ q ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hD1 : familyLabelVelocityDifferential (E := E) Γ q ((0 : W), (1 : ℝ)) ≠ 0) :
    familyLabelHessianMatrix F bW Γ q =
      fun i j ↦ fderiv ℝ (fderiv ℝ (fun v : E ↦
          (F.chartLength old (extChartAt 𝓘(ℝ, E) old (Γ q), v) : ℝ)))
        (familyChartVelocityDifferential (E := E) old Γ q
          (familyLabelVelocityDifferential (E := E) Γ q ((0 : W), (1 : ℝ))))
        (familyChartVelocityDifferential (E := E) old Γ q
          (familyLabelVelocityDifferential (E := E) Γ q (bW j, 0)))
        (familyChartVelocityDifferential (E := E) old Γ q
          (familyLabelVelocityDifferential (E := E) Γ q (bW i, 0))) := by
  funext i j
  rw [familyLabelHessianMatrix_apply]
  exact (hF.chartLength_hessian_mfderiv_extChartAt (old := old) (x := Γ q) hx
    (v := familyLabelVelocityDifferential (E := E) Γ q ((0 : W), (1 : ℝ))) hD1
    (familyLabelVelocityDifferential (E := E) Γ q (bW j, 0))
    (familyLabelVelocityDifferential (E := E) Γ q (bW i, 0))).symm

/-- **The label Hessian matrix is the actual adapted-graph vertical Hessian in the label
basis.**  Let A : E = R x V be the clock splitting of the chart tangent space, with first
coordinate one on the actual label-family time direction and vanishing on the actual label
directions. Then familyLabelHessianMatrix is exactly the vertical Hessian of the actual
adapted graph Lagrangian of the original length, evaluated in the transported label basis. -/
theorem familyLabelHessianMatrix_eq_adaptedGraphVerticalHessian
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hF : F.IsSmoothStronglyConvex) (bW : Basis ι ℝ W) {Γ : W × ℝ → M}
    {old : M} {q : W × ℝ} (hx : Γ q ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hD1 : familyLabelVelocityDifferential (E := E) Γ q ((0 : W), (1 : ℝ)) ≠ 0)
    {A : E ≃L[ℝ] (ℝ × V)} {η : V} {bvec : ι → V}
    (hη : A (familyChartVelocityDifferential (E := E) old Γ q
      (familyLabelVelocityDifferential (E := E) Γ q ((0 : W), (1 : ℝ)))) = (1, η))
    (hb : ∀ i, A (familyChartVelocityDifferential (E := E) old Γ q
      (familyLabelVelocityDifferential (E := E) Γ q (bW i, 0))) = (0, bvec i)) :
    familyLabelHessianMatrix F bW Γ q =
      fun i j ↦ fderiv ℝ (fderiv ℝ (fun θ : V ↦
        F.adaptedGraphLagrangian old A
          (A (extChartAt 𝓘(ℝ, E) old (Γ q)), θ))) η (bvec j) (bvec i) := by
  rw [familyLabelHessianMatrix_eq_chartLength_hessianMatrix hF bW hx hD1]
  funext i j
  have hη' : familyChartVelocityDifferential (E := E) old Γ q
      (familyLabelVelocityDifferential (E := E) Γ q ((0 : W), (1 : ℝ))) = A.symm (1, η) := by
    rw [← hη, A.symm_apply_apply]
  have hb' (i : ι) : familyChartVelocityDifferential (E := E) old Γ q
      (familyLabelVelocityDifferential (E := E) Γ q (bW i, 0)) = A.symm (0, bvec i) := by
    rw [← hb i, A.symm_apply_apply]
  have hx' : A.symm (A (extChartAt 𝓘(ℝ, E) old (Γ q))) ∈
      (extChartAt 𝓘(ℝ, E) old).target := by
    rw [A.symm_apply_apply]
    exact (extChartAt 𝓘(ℝ, E) old).map_source hx
  have hchart : (fun v : E ↦
      (F.chartLength old (A.symm (A (extChartAt 𝓘(ℝ, E) old (Γ q))), v) : ℝ)) =
      fun v : E ↦ (F.chartLength old (extChartAt 𝓘(ℝ, E) old (Γ q), v) : ℝ) := by
    rw [A.symm_apply_apply]
  trans fderiv ℝ (fderiv ℝ (fun v : E ↦
      (F.chartLength old (extChartAt 𝓘(ℝ, E) old (Γ q), v) : ℝ)))
      (A.symm (1, η)) (A.symm (0, bvec j)) (A.symm (0, bvec i))
  · rw [hη', hb' j, hb' i]
  · rw [← hchart]
    exact (hF.adaptedGraphLagrangian_hessian_eq (old := old) (A := A)
      (x := A (extChartAt 𝓘(ℝ, E) old (Γ q))) hx' η (bvec j) (bvec i)).symm

end OTSelector.Geometry.ContinuousFinslerNorm

namespace OTSelector.Reconstruction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- **Calibrated seed assembly.**  For the calibrated seed label family, the label Hessian
matrix of the patch is the vertical Hessian of the actual adapted graph Lagrangian of the
original length, in the transported label basis. -/
theorem calibratedSeed_familyLabelHessianMatrix_eq_adaptedGraphVerticalHessian
    (hF : F.IsSmoothStronglyConvex) {S : CalibratedLevelSeedPatch F u}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {old : M} {w : S.covector.ker} {t : ℝ}
    (hx : S.curve w t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hD1 : ContinuousFinslerNorm.familyLabelVelocityDifferential (E := E)
      (fun q : S.covector.ker × ℝ ↦ S.curve q.1 q.2) (w, t)
      ((0 : S.covector.ker), (1 : ℝ)) ≠ 0)
    {A : E ≃L[ℝ] (ℝ × V)} {η : V}
    {bvec : Fin (finrank ℝ S.covector.ker) → V}
    (hη : A (ContinuousFinslerNorm.familyChartVelocityDifferential (E := E) old
      (fun q : S.covector.ker × ℝ ↦ S.curve q.1 q.2) (w, t)
        (ContinuousFinslerNorm.familyLabelVelocityDifferential (E := E)
          (fun q : S.covector.ker × ℝ ↦ S.curve q.1 q.2) (w, t)
          ((0 : S.covector.ker), (1 : ℝ)))) = (1, η))
    (hb : ∀ i, A (ContinuousFinslerNorm.familyChartVelocityDifferential (E := E) old
      (fun q : S.covector.ker × ℝ ↦ S.curve q.1 q.2) (w, t)
        (ContinuousFinslerNorm.familyLabelVelocityDifferential (E := E)
          (fun q : S.covector.ker × ℝ ↦ S.curve q.1 q.2) (w, t)
          (Module.finBasis ℝ S.covector.ker i, 0))) = (0, bvec i)) :
    F.familyLabelHessianMatrix (Module.finBasis ℝ S.covector.ker)
        (fun q ↦ S.curve q.1 q.2) (w, t) =
      fun i j ↦ fderiv ℝ (fderiv ℝ (fun θ : V ↦
        F.adaptedGraphLagrangian old A
          (A (extChartAt 𝓘(ℝ, E) old (S.curve w t)), θ))) η (bvec j) (bvec i) :=
  ContinuousFinslerNorm.familyLabelHessianMatrix_eq_adaptedGraphVerticalHessian
    (E := E) hF (Module.finBasis ℝ S.covector.ker) hx hD1 hη hb

/-- The literal original kernel is the inverse of the family label Hessian matrix. -/
theorem originalSeedKernel_eq_familyLabelHessianMatrix_inv
    (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker) (t : ℝ) :
    originalSeedKernel S w t =
      (F.familyLabelHessianMatrix (Module.finBasis ℝ S.covector.ker)
        (fun q ↦ S.curve q.1 q.2) (w, t))⁻¹ := rfl

/-- **The label Hessian of the model velocity recovers the momentum.**  The model chart
velocity originalSeedKernel * p is the inverse family label Hessian applied to the momentum,
so the family label Hessian of that velocity is the momentum itself. -/
theorem familyLabelHessianMatrix_mulVec_originalSeedKernel
    (S : CalibratedLevelSeedPatch F u) {w : S.covector.ker} {t : ℝ}
    (hinv : IsUnit (F.familyLabelHessianMatrix (Module.finBasis ℝ S.covector.ker)
      (fun q ↦ S.curve q.1 q.2) (w, t)).det)
    (p : Fin (finrank ℝ S.covector.ker) → ℝ) :
    F.familyLabelHessianMatrix (Module.finBasis ℝ S.covector.ker)
        (fun q ↦ S.curve q.1 q.2) (w, t) *ᵥ (originalSeedKernel S w t *ᵥ p) = p := by
  have hmat : F.familyLabelHessianMatrix (Module.finBasis ℝ S.covector.ker)
      (fun q ↦ S.curve q.1 q.2) (w, t) *
      (F.familyLabelHessianMatrix (Module.finBasis ℝ S.covector.ker)
        (fun q ↦ S.curve q.1 q.2) (w, t))⁻¹ = 1 := Matrix.mul_nonsing_inv _ hinv
  rw [originalSeedKernel, Matrix.mulVec_mulVec, hmat, Matrix.one_mulVec]

/-- **Chart velocity in the label basis.**  If the actual family label Hessian applied to
the chart velocity is the momentum, then the chart velocity is the family label Hessian
inverse applied to the momentum: exactly the model velocity originalSeedKernel * p. -/
theorem chartVelocity_eq_familyLabelHessianMatrix_inv_mulVec
    (S : CalibratedLevelSeedPatch F u) {w : S.covector.ker} {t : ℝ}
    (hinv : IsUnit (F.familyLabelHessianMatrix (Module.finBasis ℝ S.covector.ker)
      (fun q ↦ S.curve q.1 q.2) (w, t)).det)
    {p : Fin (finrank ℝ S.covector.ker) → ℝ}
    {v : Fin (finrank ℝ S.covector.ker) → ℝ}
    (h : F.familyLabelHessianMatrix (Module.finBasis ℝ S.covector.ker)
      (fun q ↦ S.curve q.1 q.2) (w, t) *ᵥ v = p) :
    v = originalSeedKernel S w t *ᵥ p := by
  have hmat : (F.familyLabelHessianMatrix (Module.finBasis ℝ S.covector.ker)
      (fun q ↦ S.curve q.1 q.2) (w, t))⁻¹ *
      F.familyLabelHessianMatrix (Module.finBasis ℝ S.covector.ker)
        (fun q ↦ S.curve q.1 q.2) (w, t) = 1 := Matrix.nonsing_inv_mul _ hinv
  rw [← h, originalSeedKernel, Matrix.mulVec_mulVec, hmat, Matrix.one_mulVec]

/-- **The frozen-label defect in the label Hessian basis.**  The frozen-label chart
velocity defect is the difference between the actual inverse Hessian and the frozen
family label Hessian inverse, applied to the momentum. -/
theorem chartVelocityDefect_eq_familyLabelHessianMatrix
    (S : CalibratedLevelSeedPatch F u) {w : S.covector.ker}
    {p : Fin (finrank ℝ S.covector.ker) → ℝ}
    {v : ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ)}
    {A : ℝ → Matrix (Fin (finrank ℝ S.covector.ker))
      (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hA : ∀ c, v c = A c *ᵥ p) (c : ℝ) :
    chartVelocityDefect S w p v c =
      ‖(A c - (F.familyLabelHessianMatrix (Module.finBasis ℝ S.covector.ker)
        (fun q ↦ S.curve q.1 q.2) (w, c - (S.level : ℝ)))⁻¹) *ᵥ p‖ := by
  rw [chartVelocityDefect_eq_hessianDifference S hA c, originalSeedKernel]

end OTSelector.Reconstruction
