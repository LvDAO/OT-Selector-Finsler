import OTSelector.Geometry.FinslerIntrinsicCostCoefficientSeedNormal
import OTSelector.Geometry.Finsler.InitialFamilyIdentity

/-!
# The actual original state germ in the retained normal family's flow

One actual Legendre branch represents the original seed and the smooth normal
seed in the very same complete flow. Their state derivatives agree, their central
states coincide, and every represented original curve is unchanged for all times.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm.CalibratedLevelSeedPatch

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] {F : ContinuousFinslerNorm E M} {u : M → ℝ}

omit [BorelSpace E] in
/-- The original state germ and true normal seed share their actual value and full
state derivative in the same retained complete flow. Original unit speed is recovered
on the actual seed labels, without imposing it on the whole extension neighborhood. -/
theorem exists_state_germ_normalPotentialFamily (S : CalibratedLevelSeedPatch F u)
    (D : C11LevelSeedPresentation F u S.covector S.level S.openLabels S.labels S.curve)
    (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.openLabels)
    {Q : S.covector.ker →L[ℝ] E →L[ℝ] ℝ}
    (hQ : HasFDerivAt (fun z ↦ fderiv ℝ D.potential (D.position z)) Q w)
    (N : F.NormalPotentialFamily D.initialChart
      (D.position w, fderiv ℝ D.potential (D.position w)) (fderiv ℝ D.position w) Q S.level) :
    ∃ (X : S.covector.ker → E × E) (A : S.covector.ker →L[ℝ] E × E),
      X 0 = (N.position 0, N.velocity 0) ∧ HasFDerivAt X A 0 ∧
      HasFDerivAt (fun z ↦ (N.position z, N.velocity z)) A 0 ∧
      ∀ᶠ z in 𝓝 (0 : S.covector.ker),
        X z ∈ chartEnergyDomain D.initialChart ∧
        (X z).1 = D.position (w + z) ∧ N.flow (X z) = S.curve (w + z) ∧
        (w + z ∈ S.labels → (F.chartLength D.initialChart (X z) : ℝ) = 1) := by
  let Z : S.covector.ker → E × E := fun z ↦ (N.position z, N.velocity z)
  let p := (D.position w, fderiv ℝ D.potential (D.position w))
  let q : S.covector.ker → E × (E →L[ℝ] ℝ) :=
    fun z ↦ (D.position (w + z), fderiv ℝ D.potential (D.position (w + z)))
  have hq0 : q 0 = p := by simp only [q, p, add_zero]
  have hposition := (D.position_contDiff.contDiffAt
    (S.openLabels_open.mem_nhds hw)).differentiableAt one_ne_zero
  have hphase : HasFDerivAt (fun z ↦ (D.position z, fderiv ℝ D.potential (D.position z)))
      ((fderiv ℝ D.position w).prod Q) w := hposition.hasFDerivAt.prodMk hQ
  have hphase' : HasFDerivAt (fun z ↦ (D.position z, fderiv ℝ D.potential (D.position z)))
      ((fderiv ℝ D.position w).prod Q) (w + 0) := by simpa only [add_zero] using hphase
  have hq : HasFDerivAt q ((fderiv ℝ D.position w).prod Q) 0 := by
    simpa only [ContinuousLinearMap.comp_id] using!
      hphase'.comp 0 ((hasFDerivAt_id (0 : S.covector.ker)).const_add w)
  have hZs : ContDiffOn ℝ ∞ Z N.labels := N.position_smooth.prodMk N.velocity_smooth
  have hZc : ContinuousAt Z 0 := (hZs.contDiffAt
    (N.open_labels.mem_nhds N.anchor_mem)).continuousAt
  have hm (z : S.covector.ker) (hz : z ∈ N.labels) :
      F.chartMomentumFamily D.initialChart N.curve (z, 0) =
        parametricLegendre (F.chartEnergy D.initialChart) (Z z) := by
    apply hF.chartMomentum_of_tangent_eq (N.complete z hz 0 (mem_univ _))
      D.initialChart (N.initial_legal z hz)
    rw [N.curve_eq]
    exact N.flow_initial _ (N.initial_legal z hz)
  have hm0 : parametricLegendre (F.chartEnergy D.initialChart) (Z 0) = p :=
    (hm 0 N.anchor_mem).symm.trans N.initial_phase
  obtain ⟨e, he, hZ0, htarget, hsub, _, hInv, _, _⟩ :=
    hF.exists_smooth_chartLegendre_local_inverse D.initialChart (N.initial_legal 0 N.anchor_mem)
  have hp : p ∈ e.target := hm0 ▸ htarget
  have he0 : e.symm p = Z 0 := by
    rw [← hm0, ← he]
    exact e.left_inv hZ0
  let X : S.covector.ker → E × E := fun z ↦ e.symm (q z)
  let A : S.covector.ker →L[ℝ] E × E :=
    (fderiv ℝ e.symm p).comp ((fderiv ℝ D.position w).prod Q)
  have hInvD : HasFDerivAt e.symm (fderiv ℝ e.symm p) p :=
    ((hInv.contDiffAt (e.open_target.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have hX : HasFDerivAt X A 0 := by
    have hInvD' : HasFDerivAt e.symm (fderiv ℝ e.symm p) (q 0) := by rwa [hq0]
    exact hInvD'.comp 0 hq
  have hZnear : ∀ᶠ z in 𝓝 (0 : S.covector.ker),
      e.symm (F.chartMomentumFamily D.initialChart N.curve (z, 0)) = Z z := by
    filter_upwards [N.open_labels.mem_nhds N.anchor_mem,
      hZc (e.open_source.mem_nhds hZ0)] with z hz hze
    rw [hm z hz, ← he]
    exact e.left_inv hze
  have hZ : HasFDerivAt Z A 0 := by
    have hInvN : HasFDerivAt e.symm (fderiv ℝ e.symm p)
        (F.chartMomentumFamily D.initialChart N.curve (0, 0)) := by
      rw [N.initial_phase]
      exact hInvD
    have heq : (fun z ↦ e.symm (F.chartMomentumFamily D.initialChart N.curve (z, 0)))
        =ᶠ[𝓝 0] Z := hZnear
    exact (HasFDerivAt.comp (f := fun z ↦ F.chartMomentumFamily D.initialChart N.curve (z, 0))
      (g := e.symm) 0 hInvN N.initial_jet).congr_of_eventuallyEq heq.symm
  refine ⟨X, A, ?_, hX, hZ, ?_⟩
  · change e.symm (q 0) = Z 0
    rw [hq0, he0]
  · have hqt : ∀ᶠ z in 𝓝 (0 : S.covector.ker), q z ∈ e.target :=
      hq.continuousAt (hq0 ▸ e.open_target.mem_nhds hp)
    have hdomain : ∀ᶠ z in 𝓝 (0 : S.covector.ker), w + z ∈ S.openLabels :=
      (continuousAt_const.add continuousAt_id)
        (show S.openLabels ∈ 𝓝 (w + 0) by simpa only [add_zero] using S.openLabels_open.mem_nhds hw)
    filter_upwards [hqt, hdomain] with z hzt hz
    have hlegal : X z ∈ chartEnergyDomain D.initialChart := hsub (e.map_target hzt)
    have hEL : F.IsEulerLagrangeOn (S.curve (w + z)) univ := by
      rw [D.curve_eq]
      exact D.ambient_complete _ (D.position_domain hz)
    have hcurve : N.flow (X z) = S.curve (w + z) :=
      hF.eq_complete_family_of_chartMomentum D.initialChart N.flow_complete N.flow_initial
        he hsub hEL (S.initial_mem_chart_source D hz) hzt (S.initial_phase_eq D hz)
    refine ⟨hlegal, (parametricLegendre_inverse_components he hzt).1, hcurve, ?_⟩
    intro hlabel
    have hE : F.chartEnergy D.initialChart (X z) = 1 / 2 := by
      have hi := N.flow_initial (X z) hlegal
      rw [hcurve] at hi
      have hh := congrArg F.energy hi
      rw [ContinuousFinslerNorm.energy, S.unit _ hlabel 0] at hh
      norm_num at hh
      exact hh.symm
    rw [F.chartLength_eq_sqrt_energy, hE]
    norm_num

end OTSelector.Geometry.ContinuousFinslerNorm.CalibratedLevelSeedPatch
