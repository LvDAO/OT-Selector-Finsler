import OTSelector.Geometry.FinslerIntrinsicCostCoefficientNormalAction
import OTSelector.Analysis.Calculus.UniformStationaryQuadraticModel

/-!
# Uniform intrinsic action coefficients for normal families

The same retained complete flow gives one quadratic remainder radius over compact
sets of calibrated time pairs, including for actual state germs sharing its first jet.
-/

open Set Filter Asymptotics
open scoped Topology ContDiff

noncomputable section
open Manifold Bundle Module
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm.NormalPotentialFamily

variable {E W M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype ι] [DecidableEq ι]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M} {initial : M}
  {z₀ : E × (E →L[ℝ] ℝ)} {R : W →L[ℝ] E} {Q : W →L[ℝ] E →L[ℝ] ℝ} {value : ℝ}
  (N : F.NormalPotentialFamily initial z₀ R Q value)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ W] [Fintype ι] [DecidableEq ι] [T2Space M]
    [PreconnectedSpace M] in
/-- Every retained normal state has its actual unit length. -/
theorem state_length_eq_one (z : W) (hz : z ∈ N.labels) :
    (F.chartLength initial (N.position z, N.velocity z) : ℝ) = 1 := by
  have hi := N.flow_initial _ (N.initial_legal z hz)
  have hh := congrArg F.energy hi
  have he := N.energy_eq z hz 0
  rw [N.curve_eq] at he
  have henergy : F.chartEnergy initial (N.position z, N.velocity z) = 1 / 2 :=
    hh.symm.trans he
  rw [F.chartLength_eq_sqrt_energy, henergy]
  norm_num

/-- The actual phase action on every germ sharing the normal state jet has one
intrinsic quadratic remainder radius on compactly many calibrated time pairs. -/
theorem uniform_phaseAction_intrinsic_quadratic
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {u : M → ℝ} (hu : let _instUniformNormalLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) (bW : Basis ι ℝ W)
    {T : Set (ℝ × ℝ)} (hT : IsCompact T)
    (hTube : ∀ t ∈ T, Nonempty (F.CalibratedTube N.curve t.1 t.2 u))
    {X : W → E × E} {A : W →L[ℝ] E × E}
    (hX : HasFDerivAt X A 0) (hX₀ : X 0 = (N.position 0, N.velocity 0))
    (hY : HasFDerivAt (fun z ↦ (N.position z, N.velocity z)) A 0) :
    ∀ ε : ℝ, 0 < ε → ∃ r > 0, ∀ t ∈ T, ∀ ξ : W × W, ‖ξ‖ < r →
      ‖F.phaseLengthAction initial N.flow
        (secondJetPolynomial z₀.1 value z₀.2 N.hessian) t.1 t.2 (X ξ.1, X ξ.2) -
          F.intrinsicLengthQuadratic bW N.curve 0 t.1 t.2 ξ‖ ≤ ε * ‖ξ‖ ^ 2 := by
  let P := secondJetPolynomial z₀.1 value z₀.2 N.hessian
  let j : ScalarSecondJet E := (z₀.1, value, z₀.2, N.hessian)
  let z := (N.position 0, N.velocity 0)
  let Y : W → E × E := fun w ↦ (N.position w, N.velocity w)
  let f : (ℝ × ℝ) × ((E × E) × (E × E)) → ℝ :=
    fun q ↦ F.phaseLengthAction initial N.flow P q.1.1 q.1.2 q.2
  have hf (t : ℝ × ℝ) (ht : t ∈ T) : ContDiffAt ℝ 3 f (t, (z, z)) := by
    obtain ⟨D⟩ := hTube t ht
    have h3 := (N.phase_action_data_of_calibratedTube hF hcomplete hu D).1
    have hm : ContDiffAt ℝ 3
        (fun q : (ℝ × ℝ) × ((E × E) × (E × E)) ↦ ((j, q.1), q.2)) (t, (z, z)) :=
      (contDiffAt_const.prodMk contDiffAt_fst).prodMk contDiffAt_snd
    exact h3.comp (t, (z, z)) hm
  have hs (t : ℝ × ℝ) (ht : t ∈ T) :
      HasFDerivAt (fun p ↦ f (t, p)) (0 : ((E × E) × (E × E)) →L[ℝ] ℝ) (z, z) := by
    obtain ⟨D⟩ := hTube t ht
    exact (N.phase_action_data_of_calibratedTube hF hcomplete hu D).2
  have heq (t : ℝ × ℝ) (ξ : W × W) (h₁ : ξ.1 ∈ N.labels) (h₂ : ξ.2 ∈ N.labels) :
      f (t, (Y ξ.1, Y ξ.2)) =
        (F.lengthEDist (N.curve ξ.1 t.1) (N.curve ξ.2 t.2)).toReal - (t.2 - t.1) := by
    dsimp only [f, Y, phaseLengthAction]
    rw [N.state_length_eq_one ξ.1 h₁, N.state_length_eq_one ξ.2 h₂]
    change (F.lengthEDist (N.flow _ _) (N.flow _ _)).toReal - P (N.position ξ.2) +
      P (N.position ξ.1) - t.2 * 1 + t.1 * 1 = _
    rw [show P (N.position ξ.2) = value from N.level ξ.2 h₂,
      show P (N.position ξ.1) = value from N.level ξ.1 h₁, N.curve_eq]
    ring
  have hmodel (t : ℝ × ℝ) (ht : t ∈ T) :
      (fun ξ : W × W ↦ f (t, (Y ξ.1, Y ξ.2)) -
        F.intrinsicLengthQuadratic bW N.curve 0 t.1 t.2 ξ) =o[𝓝 (0 : W × W)]
          fun ξ ↦ ‖ξ‖ ^ 2 := by
    obtain ⟨D⟩ := hTube t ht
    apply (D.distance_sub_intrinsicLengthQuadratic_isLittleO hF hcomplete hu
      (N.complete 0 N.anchor_mem) bW).congr' ?_ Filter.EventuallyEq.rfl
    have hh : ∀ᶠ ξ : W × W in 𝓝 0, ξ.1 ∈ N.labels ∧ ξ.2 ∈ N.labels :=
      (N.open_labels.prod N.open_labels).mem_nhds ⟨N.anchor_mem, N.anchor_mem⟩
    filter_upwards [hh] with ξ hξ
    rw [heq t ξ hξ.1 hξ.2]
  have hzero (t : ℝ × ℝ) (ht : t ∈ T) : f (t, (z, z)) = 0 := by
    have hz := (hmodel t ht).isBigO.eq_zero_imp.self_of_nhds (by simp)
    simpa [Y, z, intrinsicLengthQuadratic] using hz
  let DA : W × W →L[ℝ] (E × E) × (E × E) :=
    (A.comp (ContinuousLinearMap.fst ℝ W W)).prod
      (A.comp (ContinuousLinearMap.snd ℝ W W))
  have hXP : HasFDerivAt (fun ξ : W × W ↦ (X ξ.1, X ξ.2)) DA 0 :=
    (hX.comp 0 hasFDerivAt_fst).prodMk (hX.comp 0 hasFDerivAt_snd)
  have hYactual : HasFDerivAt Y A 0 := hY
  have hY1 : HasFDerivAt (fun ξ : W × W ↦ Y ξ.1)
      (A.comp (ContinuousLinearMap.fst ℝ W W)) 0 := by
    simpa only [Function.comp_def] using!
      hYactual.comp (0 : W × W) (hasFDerivAt_fst (𝕜 := ℝ) (p := (0 : W × W)))
  have hY2 : HasFDerivAt (fun ξ : W × W ↦ Y ξ.2)
      (A.comp (ContinuousLinearMap.snd ℝ W W)) 0 := by
    simpa only [Function.comp_def] using!
      hYactual.comp (0 : W × W) (hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : W × W)))
  have hYP : HasFDerivAt (fun ξ : W × W ↦ (Y ξ.1, Y ξ.2)) DA 0 :=
    hY1.prodMk hY2
  have hhom (t : ℝ × ℝ) (ht : t ∈ T) (a : ℝ) (ξ : W × W) :
      F.intrinsicLengthQuadratic bW N.curve 0 t.1 t.2 (a • ξ) =
        a ^ 2 * F.intrinsicLengthQuadratic bW N.curve 0 t.1 t.2 ξ := by
    obtain ⟨D⟩ := hTube t ht
    simp only [← D.quadratic_eq_intrinsicLengthQuadratic hF bW]
    exact D.quadratic_smul a ξ
  have hXP0 : (X (0 : W), X (0 : W)) = (z, z) := by rw [hX₀]
  have hh := uniform_stationary_composition_of_shared_jet_model hT hf hs hXP
    hXP0 hYP rfl hhom
    (fun t ht ↦ by simpa only [hzero t ht, sub_zero] using hmodel t ht)
  intro ε hε
  obtain ⟨r, hr, hb⟩ := hh ε hε
  refine ⟨r, hr, ?_⟩
  intro t ht ξ hξ
  simpa only [hzero t ht, sub_zero] using hb t ht ξ hξ

end OTSelector.Geometry.ContinuousFinslerNorm.NormalPotentialFamily
