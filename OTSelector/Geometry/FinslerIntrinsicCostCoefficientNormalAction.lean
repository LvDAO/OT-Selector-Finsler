import OTSelector.Geometry.FinslerIntrinsicCostCoefficientNormalData
import OTSelector.Geometry.FinslerIntrinsicCostCoefficient
import OTSelector.Geometry.FinslerParameterizedPhaseAction

/-!
# Stationary original phase action for a true normal potential family

The constructed polynomial has the actual central length covector. A genuine
calibrated tube therefore supplies joint action regularity and stationarity for
that family's retained complete flow, with no new distance-jet premise.
-/

open Set Manifold Bundle
open scoped Topology ContDiff

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm.NormalPotentialFamily

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M} {initial : M}
  {z₀ : E × (E →L[ℝ] ℝ)} {R : W →L[ℝ] E} {Q : W →L[ℝ] E →L[ℝ] ℝ} {value : ℝ}
  (N : F.NormalPotentialFamily initial z₀ R Q value)

omit [FiniteDimensional ℝ W] [T2Space M] [PreconnectedSpace M] in
/-- The retained central state is unit speed and its actual energy covector is
the original prescribed covector. -/
theorem central_state_data (hF : F.IsSmoothStronglyConvex) :
    F.chartEnergy initial (N.position 0, N.velocity 0) = 1 / 2 ∧
      (F.chartLength initial (N.position 0, N.velocity 0) : ℝ) = 1 ∧
      fiberLegendre (F.chartEnergy initial) (N.position 0, N.velocity 0) = z₀.2 := by
  have hi : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (N.curve 0) ⟨0, (1 : ℝ)⟩ =
      (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
        (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm (N.position 0, N.velocity 0) := by
    rw [N.curve_eq]
    exact N.flow_initial _ (N.initial_legal 0 N.anchor_mem)
  have henergy : F.chartEnergy initial (N.position 0, N.velocity 0) = 1 / 2 :=
    (congrArg F.energy hi).symm.trans (N.energy_eq 0 N.anchor_mem 0)
  have hm := hF.chartMomentum_of_tangent_eq
    (N.complete 0 N.anchor_mem 0 (mem_univ _)) initial (N.initial_legal 0 N.anchor_mem) hi
  have hm' : parametricLegendre (F.chartEnergy initial) (N.position 0, N.velocity 0) = z₀ :=
    hm.symm.trans N.initial_phase
  refine ⟨henergy, ?_, congrArg Prod.snd hm'⟩
  rw [F.chartLength_eq_sqrt_energy, henergy]
  norm_num

/-- A true calibrated tube constructs joint C3 action and central stationarity for
the exact complete flow and polynomial retained by the actual label producer. -/
theorem phase_action_data_of_calibratedTube
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {u : M → ℝ} (hu : let _instNormalActionLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) {a b : ℝ} (D : F.CalibratedTube N.curve a b u) :
    let j : ScalarSecondJet E := (z₀.1, value, z₀.2, N.hessian)
    let z : E × E := (N.position 0, N.velocity 0)
    ContDiffAt ℝ 3 (F.parameterizedPhaseLengthAction initial N.flow)
      ((j, (a, b)), (z, z)) ∧
      HasFDerivAt (F.phaseLengthAction initial N.flow (scalarSecondJetPolynomial j) a b)
        (0 : ((E × E) × (E × E)) →L[ℝ] ℝ) (z, z) := by
  let j : ScalarSecondJet E := (z₀.1, value, z₀.2, N.hessian)
  let z : E × E := (N.position 0, N.velocity 0)
  have hs := N.central_state_data hF
  have hmatch : fderiv ℝ (scalarSecondJetPolynomial j) z.1 =
      fiberLegendre (fun q ↦ (F.chartLength initial q : ℝ)) z := by
    change fderiv ℝ (scalarSecondJetPolynomial j) (N.position 0) = _
    rw [N.position_center, (hasFDerivAt_scalarSecondJetPolynomial_center j).fderiv]
    exact hs.2.2.symm.trans (by
      simpa only [fiberLegendre, hs.2.1, one_smul] using
        hF.chartLegendre_eq_length_smul_fderiv initial (N.initial_legal 0 N.anchor_mem))
  have hΦ := (hF.contMDiffOn_tangentFamily_of_chartSeed_smooth initial
    (isOpen_chartEnergyDomain initial) N.flow_complete (ι := id) contDiffOn_id
    (fun _ hz ↦ hz) N.flow_initial).1
  have hsame : N.flow z = N.curve 0 := by rw [N.curve_eq]
  exact hF.parameterizedPhaseLengthAction_jet_of_calibrated_curve hcomplete initial
    N.flow_complete N.flow_initial hΦ (N.initial_legal 0 N.anchor_mem) hmatch
    D.smooth D.smooth_symm D.coe_eq D.energy_eq D.timeOrigin D.covector_le
    D.ordered (N.complete 0 N.anchor_mem) hsame D.stay D.minimizing
    hu D.saturation D.differentiable

end OTSelector.Geometry.ContinuousFinslerNorm.NormalPotentialFamily
