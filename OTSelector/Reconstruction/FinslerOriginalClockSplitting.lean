import OTSelector.Geometry.Finsler.AdaptedClock
import OTSelector.Geometry.FinslerIntrinsicKernelRegularity
import OTSelector.Reconstruction.FinslerOriginalLabelHessianMatrix

/-!
# Clock splitting construction and determinant positivity

This file closes the two residual data hypotheses of FinslerOriginalLabelHessianMatrix.lean.

1. The clock splitting A : E = R x V is constructed, not assumed. The actual original
   Finsler momentum of the label family supplies the clock covector; its kernel is the
   transverse vertical model. The construction is covectorClock of the actual chart energy
   momentum, so the actual chart velocity becomes the positive unit time direction
   (covectorClock_velocity). The label directions become transverse graph directions
   (second component) as soon as the momentum annihilates them, exactly the normality of
   the original momentum along label variations. The assembled label Hessian matrix is
   then the vertical Hessian of the actual adapted graph Lagrangian in the constructed
   label basis.

2. The family label Hessian matrix has nonzero determinant, in fact it is positive
   definite. The graph vertical Hessian is symmetric (chart length Hessian symmetry
   transported through the graph Hessian identity) and strictly positive on every nonzero
   graph direction, so its basis matrix is positive definite; positive definiteness gives
   unit determinant by Mathlib's Matrix.PosDef.isUnit and Matrix.isUnit_iff_isUnit_det.
-/
open Set Function Filter MeasureTheory Matrix Module Manifold Metric Bundle
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical Topology BigOperators

noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E W M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

/-- The actual clock covector: the original Finsler momentum of the label family at the
actual chart state, along the actual chart velocity. -/
noncomputable def chartClockCovector (F : ContinuousFinslerNorm E M) (old : M)
    (Γ : W × ℝ → M) (q : W × ℝ) : E →L[ℝ] ℝ :=
  fiberLegendre (F.chartEnergy old)
    (extChartAt 𝓘(ℝ, E) old (Γ q),
      familyChartVelocityDifferential (E := E) old Γ q
        (familyLabelVelocityDifferential (E := E) Γ q ((0 : W), (1 : ℝ))))

/-- The actual chart velocity of the label family at the actual chart state. -/
noncomputable def chartClockVelocity (F : ContinuousFinslerNorm E M) (old : M)
    (Γ : W × ℝ → M) (q : W × ℝ) : E :=
  familyChartVelocityDifferential (E := E) old Γ q
    (familyLabelVelocityDifferential (E := E) Γ q ((0 : W), (1 : ℝ)))

/-- The actual chart image of one label direction. -/
noncomputable def chartClockLabelVelocity (F : ContinuousFinslerNorm E M) (bW : Basis ι ℝ W)
    (old : M) (Γ : W × ℝ → M) (q : W × ℝ) (i : ι) : E :=
  familyChartVelocityDifferential (E := E) old Γ q
    (familyLabelVelocityDifferential (E := E) Γ q (bW i, 0))

/-- The constructed clock splitting: the actual Finsler momentum supplies the clock
coordinate and its kernel the transverse model. -/
noncomputable def chartClockSplitting (F : ContinuousFinslerNorm E M) (old : M)
    (Γ : W × ℝ → M) (q : W × ℝ)
    (hpv : chartClockCovector F old Γ q (chartClockVelocity F old Γ q) ≠ 0) :
    E ≃L[ℝ] (ℝ × (chartClockCovector F old Γ q).ker) :=
  covectorClock (chartClockCovector F old Γ q) (chartClockVelocity F old Γ q) hpv

/-- The actual momentum is positive on the actual chart velocity. -/
theorem chartClockCovector_velocity_pos (hF : F.IsSmoothStronglyConvex) {old : M}
    {Γ : W × ℝ → M} {q : W × ℝ} (hx : Γ q ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hvel : chartClockVelocity F old Γ q ≠ 0) :
    0 < chartClockCovector F old Γ q (chartClockVelocity F old Γ q) := by
  have hz : (extChartAt 𝓘(ℝ, E) old (Γ q), chartClockVelocity F old Γ q) ∈
      chartEnergyDomain old :=
    ⟨(extChartAt 𝓘(ℝ, E) old).map_source hx, hvel⟩
  show 0 < fiberLegendre (F.chartEnergy old)
    (extChartAt 𝓘(ℝ, E) old (Γ q), chartClockVelocity F old Γ q)
    (chartClockVelocity F old Γ q)
  rw [hF.chartEnergy_euler old hz]
  exact mul_pos (by norm_num) (F.chartEnergy_pos old hz)

/-- The actual chart velocity becomes the positive unit time direction. -/
theorem chartClockSplitting_velocity {old : M} {Γ : W × ℝ → M} {q : W × ℝ}
    (hpv : chartClockCovector F old Γ q (chartClockVelocity F old Γ q) ≠ 0) :
    chartClockSplitting F old Γ q hpv (chartClockVelocity F old Γ q) = (1, 0) := by
  rw [chartClockSplitting]
  exact covectorClock_velocity _ _ hpv

/-- The constructed clock coordinate is normalized evaluation by the actual momentum. -/
theorem chartClockSplitting_fst {old : M} {Γ : W × ℝ → M} {q : W × ℝ}
    (hpv : chartClockCovector F old Γ q (chartClockVelocity F old Γ q) ≠ 0) (u : E) :
    (chartClockSplitting F old Γ q hpv u).1 =
      chartClockCovector F old Γ q u /
        chartClockCovector F old Γ q (chartClockVelocity F old Γ q) := by
  rw [chartClockSplitting]
  exact covectorClock_fst _ _ hpv u

/-- Momentum normality along a label direction makes that label direction transverse in
the constructed splitting. -/
theorem chartClockSplitting_label (bW : Basis ι ℝ W) {old : M} {Γ : W × ℝ → M} {q : W × ℝ}
    (hpv : chartClockCovector F old Γ q (chartClockVelocity F old Γ q) ≠ 0)
    (hker : ∀ i, chartClockCovector F old Γ q (chartClockLabelVelocity F bW old Γ q i) = 0)
    (i : ι) :
    chartClockSplitting F old Γ q hpv (chartClockLabelVelocity F bW old Γ q i) =
      (0, (chartClockSplitting F old Γ q hpv (chartClockLabelVelocity F bW old Γ q i)).2) := by
  apply Prod.ext
  · rw [chartClockSplitting_fst, hker i, zero_div]
  · rfl

/-- **Assembled label Hessian matrix from the constructed clock splitting.**  With the
clock splitting built from the actual momentum, the intrinsic label Hessian matrix is the
vertical Hessian of the actual adapted graph Lagrangian of the original length, evaluated
at unit clock speed in the constructed label basis. Nothing about A is assumed: the momenta
and label directions are the actual ones. The only remaining input is the actual normality
of the momentum along label directions. -/
theorem familyLabelHessianMatrix_eq_adaptedGraphVerticalHessian_chartClock
    (hF : F.IsSmoothStronglyConvex) (bW : Basis ι ℝ W) {Γ : W × ℝ → M}
    {old : M} {q : W × ℝ} (hx : Γ q ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hD1 : familyLabelVelocityDifferential (E := E) Γ q ((0 : W), (1 : ℝ)) ≠ 0)
    (hvel : chartClockVelocity F old Γ q ≠ 0)
    (hker : ∀ i, chartClockCovector F old Γ q (chartClockLabelVelocity F bW old Γ q i) = 0) :
    familyLabelHessianMatrix F bW Γ q =
      fun i j ↦ fderiv ℝ (fderiv ℝ (fun θ : (chartClockCovector F old Γ q).ker ↦
        F.adaptedGraphLagrangian old
          (chartClockSplitting F old Γ q
            (ne_of_gt (chartClockCovector_velocity_pos hF hx hvel)))
          (chartClockSplitting F old Γ q
            (ne_of_gt (chartClockCovector_velocity_pos hF hx hvel))
            (extChartAt 𝓘(ℝ, E) old (Γ q)), θ))) 0
        ((chartClockSplitting F old Γ q
          (ne_of_gt (chartClockCovector_velocity_pos hF hx hvel))
          (chartClockLabelVelocity F bW old Γ q j)).2)
        ((chartClockSplitting F old Γ q
          (ne_of_gt (chartClockCovector_velocity_pos hF hx hvel))
          (chartClockLabelVelocity F bW old Γ q i)).2) := by
  exact familyLabelHessianMatrix_eq_adaptedGraphVerticalHessian (E := E) (F := F)
    (V := (chartClockCovector F old Γ q).ker)
    (A := chartClockSplitting F old Γ q
      (ne_of_gt (chartClockCovector_velocity_pos hF hx hvel)))
    (η := 0)
    (bvec := fun i ↦ (chartClockSplitting F old Γ q
      (ne_of_gt (chartClockCovector_velocity_pos hF hx hvel))
      (chartClockLabelVelocity F bW old Γ q i)).2)
    hF bW hx hD1
    (chartClockSplitting_velocity (ne_of_gt (chartClockCovector_velocity_pos hF hx hvel)))
    (fun i ↦ chartClockSplitting_label bW
      (ne_of_gt (chartClockCovector_velocity_pos hF hx hvel)) hker i)

/-- The actual graph vertical Hessian is symmetric. -/
theorem adaptedGraphLagrangian_hessian_symm (hF : F.IsSmoothStronglyConvex)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (old : M) (A : E ≃L[ℝ] (ℝ × V)) {x : ℝ × V}
    (hx : A.symm x ∈ (extChartAt 𝓘(ℝ, E) old).target) (η u w : V) :
    fderiv ℝ (fderiv ℝ (fun θ : V ↦ F.adaptedGraphLagrangian old A (x, θ))) η u w =
      fderiv ℝ (fderiv ℝ (fun θ : V ↦ F.adaptedGraphLagrangian old A (x, θ))) η w u := by
  have hz : (A.symm x, A.symm (1, η)) ∈ chartEnergyDomain old := by
    refine ⟨hx, ?_⟩
    intro he
    have h := congrArg A he
    simp at h
  rw [hF.adaptedGraphLagrangian_hessian_eq old A hx η u w,
    hF.adaptedGraphLagrangian_hessian_eq old A hx η w u]
  exact hF.chartLength_hessian_symm old hz (A.symm (0, u)) (A.symm (0, w))

/-- **Positive definiteness of the family label Hessian matrix.**  Once the actual label
directions are linearly independent in the vertical model, the label Hessian matrix is the
basis matrix of the actual positive definite graph vertical Hessian, hence positive
definite. -/
theorem familyLabelHessianMatrix_posDef [Fintype ι] [DecidableEq ι]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (hF : F.IsSmoothStronglyConvex) (bW : Basis ι ℝ W) {Γ : W × ℝ → M}
    {old : M} {q : W × ℝ} (hx : Γ q ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hD1 : familyLabelVelocityDifferential (E := E) Γ q ((0 : W), (1 : ℝ)) ≠ 0)
    {A : E ≃L[ℝ] (ℝ × V)} {η : V} {bvec : ι → V}
    (hη : A (familyChartVelocityDifferential (E := E) old Γ q
      (familyLabelVelocityDifferential (E := E) Γ q ((0 : W), (1 : ℝ)))) = (1, η))
    (hb : ∀ i, A (familyChartVelocityDifferential (E := E) old Γ q
      (familyLabelVelocityDifferential (E := E) Γ q (bW i, 0))) = (0, bvec i))
    (hli : LinearIndependent ℝ bvec) (hcard : Fintype.card ι = finrank ℝ V) :
    (familyLabelHessianMatrix F bW Γ q).PosDef := by
  classical
  let bV : Basis ι ℝ V := basisOfLinearIndependentOfCardEqFinrank' bvec hli hcard
  let x : ℝ × V := A (extChartAt 𝓘(ℝ, E) old (Γ q))
  let G : V →L[ℝ] (V →L[ℝ] ℝ) :=
    fderiv ℝ (fderiv ℝ (fun θ : V ↦ F.adaptedGraphLagrangian old A (x, θ))) η
  have hx' : A.symm x ∈ (extChartAt 𝓘(ℝ, E) old).target := by
    dsimp only [x]
    rw [A.symm_apply_apply]
    exact (extChartAt 𝓘(ℝ, E) old).map_source hx
  have hM : familyLabelHessianMatrix F bW Γ q = hamiltonianMatrixA bV G := by
    rw [familyLabelHessianMatrix_eq_adaptedGraphVerticalHessian (E := E) hF bW hx hD1 hη hb]
    ext i j
    simp only [hamiltonianMatrixA, bV, x, G, coe_basisOfLinearIndependentOfCardEqFinrank']
  rw [hM]
  exact hamiltonianMatrixA_posDef bV
    (fun u w ↦ adaptedGraphLagrangian_hessian_symm hF old A hx' η u w)
    (fun w hw ↦ hF.adaptedGraphLagrangian_hessian_pos old A hx' η hw)

/-- **Nonzero determinant of the family label Hessian matrix.**  Positive definiteness
gives an invertible matrix, hence unit determinant. -/
theorem familyLabelHessianMatrix_isUnit_det [Fintype ι] [DecidableEq ι]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (hF : F.IsSmoothStronglyConvex) (bW : Basis ι ℝ W) {Γ : W × ℝ → M}
    {old : M} {q : W × ℝ} (hx : Γ q ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hD1 : familyLabelVelocityDifferential (E := E) Γ q ((0 : W), (1 : ℝ)) ≠ 0)
    {A : E ≃L[ℝ] (ℝ × V)} {η : V} {bvec : ι → V}
    (hη : A (familyChartVelocityDifferential (E := E) old Γ q
      (familyLabelVelocityDifferential (E := E) Γ q ((0 : W), (1 : ℝ)))) = (1, η))
    (hb : ∀ i, A (familyChartVelocityDifferential (E := E) old Γ q
      (familyLabelVelocityDifferential (E := E) Γ q (bW i, 0))) = (0, bvec i))
    (hli : LinearIndependent ℝ bvec) (hcard : Fintype.card ι = finrank ℝ V) :
    IsUnit (familyLabelHessianMatrix F bW Γ q).det :=
  (Matrix.isUnit_iff_isUnit_det (A := familyLabelHessianMatrix F bW Γ q)).mp
    (familyLabelHessianMatrix_posDef hF bW hx hD1 hη hb hli hcard).isUnit

end OTSelector.Geometry.ContinuousFinslerNorm

namespace OTSelector.Reconstruction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- **Nonzero determinant for the calibrated seed label Hessian.**  The clock splitting is
the one constructed from the actual momentum (no assumed datum A): with the actual chart
velocity nonzero, actual momentum nonvanishing, momentum normality along the actual label
directions, and actual label directions linearly independent in the vertical model, the
calibrated seed label Hessian matrix has unit determinant. This discharges the determinant
hypothesis of the frozen-label momentum lemmas. -/
theorem calibratedSeed_familyLabelHessianMatrix_isUnit_det
    (hF : F.IsSmoothStronglyConvex) {S : CalibratedLevelSeedPatch F u}
    {old : M} {w : S.covector.ker} {t : ℝ}
    (hx : S.curve w t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hD1 : ContinuousFinslerNorm.familyLabelVelocityDifferential (E := E)
      (fun q : S.covector.ker × ℝ ↦ S.curve q.1 q.2) (w, t)
      ((0 : S.covector.ker), (1 : ℝ)) ≠ 0)
    (hvel : ContinuousFinslerNorm.chartClockVelocity (F := F) old
      (fun q : S.covector.ker × ℝ ↦ S.curve q.1 q.2) (w, t) ≠ 0)
    (hker : ∀ i, ContinuousFinslerNorm.chartClockCovector (F := F) old
      (fun q : S.covector.ker × ℝ ↦ S.curve q.1 q.2) (w, t)
      (ContinuousFinslerNorm.chartClockLabelVelocity (F := F)
        (bW := Module.finBasis ℝ S.covector.ker) old
        (fun q : S.covector.ker × ℝ ↦ S.curve q.1 q.2) (w, t) i) = 0)
    (hli : LinearIndependent ℝ (fun i ↦ (ContinuousFinslerNorm.chartClockSplitting (F := F)
      old (fun q : S.covector.ker × ℝ ↦ S.curve q.1 q.2) (w, t)
      (ne_of_gt (ContinuousFinslerNorm.chartClockCovector_velocity_pos hF hx hvel))
      (ContinuousFinslerNorm.chartClockLabelVelocity (F := F)
        (bW := Module.finBasis ℝ S.covector.ker) old
        (fun q : S.covector.ker × ℝ ↦ S.curve q.1 q.2) (w, t) i)).2)) :
    IsUnit (F.familyLabelHessianMatrix (Module.finBasis ℝ S.covector.ker)
      (fun q ↦ S.curve q.1 q.2) (w, t)).det := by
  have hpne : ContinuousFinslerNorm.chartClockCovector (F := F) old
      (fun q : S.covector.ker × ℝ ↦ S.curve q.1 q.2) (w, t) ≠ 0 := by
    intro h0
    exact (ne_of_gt (ContinuousFinslerNorm.chartClockCovector_velocity_pos hF hx hvel))
      (by rw [h0]; rfl)
  have hS : Module.finrank ℝ S.covector.ker + 1 = Module.finrank ℝ E := by
    have h := S.normalization.toLinearEquiv.finrank_eq
    rw [Module.finrank_prod] at h
    simpa only [Module.finrank_self, add_comm] using h
  have hpne' : (↑(ContinuousFinslerNorm.chartClockCovector (F := F) old
      (fun q : S.covector.ker × ℝ ↦ S.curve q.1 q.2) (w, t)) : E →ₗ[ℝ] ℝ) ≠ 0 := by
    intro h0
    apply hpne
    ext v
    have hh := congrArg (fun f : E →ₗ[ℝ] ℝ ↦ f v) h0
    simpa using hh
  have hp : Module.finrank ℝ (ContinuousFinslerNorm.chartClockCovector (F := F) old
      (fun q : S.covector.ker × ℝ ↦ S.curve q.1 q.2) (w, t)).ker + 1 =
      Module.finrank ℝ E :=
    Module.Dual.finrank_ker_add_one_of_ne_zero hpne'
  have hcard : Fintype.card (Fin (Module.finrank ℝ S.covector.ker)) =
      Module.finrank ℝ (ContinuousFinslerNorm.chartClockCovector (F := F) old
        (fun q : S.covector.ker × ℝ ↦ S.curve q.1 q.2) (w, t)).ker := by
    rw [Fintype.card_fin]
    omega
  exact ContinuousFinslerNorm.familyLabelHessianMatrix_isUnit_det (E := E) (F := F)
    (V := (ContinuousFinslerNorm.chartClockCovector (F := F) old
      (fun q : S.covector.ker × ℝ ↦ S.curve q.1 q.2) (w, t)).ker)
    (A := ContinuousFinslerNorm.chartClockSplitting (F := F) old
      (fun q : S.covector.ker × ℝ ↦ S.curve q.1 q.2) (w, t)
      (ne_of_gt (ContinuousFinslerNorm.chartClockCovector_velocity_pos hF hx hvel)))
    (η := 0)
    (bvec := fun i ↦ (ContinuousFinslerNorm.chartClockSplitting (F := F) old
      (fun q : S.covector.ker × ℝ ↦ S.curve q.1 q.2) (w, t)
      (ne_of_gt (ContinuousFinslerNorm.chartClockCovector_velocity_pos hF hx hvel))
      (ContinuousFinslerNorm.chartClockLabelVelocity (F := F)
        (bW := Module.finBasis ℝ S.covector.ker) old
        (fun q : S.covector.ker × ℝ ↦ S.curve q.1 q.2) (w, t) i)).2)
    hF (Module.finBasis ℝ S.covector.ker) hx hD1
    (ContinuousFinslerNorm.chartClockSplitting_velocity
      (ne_of_gt (ContinuousFinslerNorm.chartClockCovector_velocity_pos hF hx hvel)))
    (fun i ↦ ContinuousFinslerNorm.chartClockSplitting_label
      (bW := Module.finBasis ℝ S.covector.ker)
      (ne_of_gt (ContinuousFinslerNorm.chartClockCovector_velocity_pos hF hx hvel)) hker i)
    hli hcard

end OTSelector.Reconstruction
