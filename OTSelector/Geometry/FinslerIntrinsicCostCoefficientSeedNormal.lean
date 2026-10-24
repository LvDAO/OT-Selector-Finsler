import OTSelector.Geometry.FinslerIntrinsicCostCoefficientNormalData
import OTSelector.Geometry.FinslerIntrinsicCostCoefficientLabelShift
import OTSelector.Geometry.FinslerSeedPatchEnergyTangency

/-!
# Genuine normal comparison families for the actual original seed

Almost every original label produces a smooth normal potential family in its own
translated labels. Complete-flow uniqueness transports the same phase jet, and the
literal original intrinsic matrix agrees with the normal family's matrix at every
time. Its potential error is quadratic-small along the original section.
-/

open Set Filter MeasureTheory Manifold Asymptotics Module
open scoped Topology ContDiff

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm.CalibratedLevelSeedPatch

variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M} {u : M → ℝ}

omit [BorelSpace E] in
/-- The actual original label translation has the same complete phase jet as any
normal family realizing its initial derivative. The comparison domain is shrunk
inside the original open labels in the proof. -/
theorem same_phase_firstJet_of_normalPotentialFamily (S : CalibratedLevelSeedPatch F u)
    (D : C11LevelSeedPresentation F u S.covector S.level S.openLabels S.labels S.curve)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {w : S.covector.ker} (hw : w ∈ S.openLabels)
    {Q : S.covector.ker →L[ℝ] E →L[ℝ] ℝ}
    (hQ : HasFDerivAt (fun z ↦ fderiv ℝ D.potential (D.position z)) Q w)
    (N : F.NormalPotentialFamily D.initialChart
      (D.position w, fderiv ℝ D.potential (D.position w)) (fderiv ℝ D.position w) Q S.level) :
    S.curve w = N.curve 0 ∧ ∀ (terminal : M) (t : ℝ),
      N.curve 0 t ∈ (extChartAt 𝓘(ℝ, E) terminal).source →
      HasFDerivAt (F.chartMomentumFamily terminal (fun z ↦ S.curve (w + z)))
        (fderiv ℝ (F.chartMomentumFamily terminal N.curve) (0, t)) (0, t) ∧
      HasFDerivAt (F.chartMomentumFamily terminal N.curve)
        (fderiv ℝ (F.chartMomentumFamily terminal N.curve) (0, t)) (0, t) := by
  let B := N.labels ∩ (fun z ↦ w + z) ⁻¹' S.openLabels
  have hB : IsOpen B := N.open_labels.inter
    (S.openLabels_open.preimage (continuous_const.add continuous_id))
  have h0 : (0 : S.covector.ker) ∈ B := ⟨N.anchor_mem, by simpa using hw⟩
  have hEL (z : S.covector.ker) (hz : z ∈ B) :
      F.IsEulerLagrangeOn (S.curve (w + z)) univ := by
    rw [D.curve_eq]
    exact D.ambient_complete (D.position (w + z)) (D.position_domain hz.2)
  have hsource (z : S.covector.ker) (hz : z ∈ B) :
      S.curve (w + z) 0 ∈ (extChartAt 𝓘(ℝ, E) D.initialChart).source :=
    S.initial_mem_chart_source D hz.2
  have hp := S.initial_phase_hasFDerivAt_of_covector D hw hQ
  have hp' : HasFDerivAt (fun z ↦ F.chartMomentumFamily D.initialChart S.curve (z, 0))
      ((fderiv ℝ D.position w).prod Q) (w + 0) := by simpa only [add_zero] using hp
  have hjet : HasFDerivAt
      (fun z ↦ F.chartMomentumFamily D.initialChart (fun z ↦ S.curve (w + z)) (z, 0))
      ((fderiv ℝ D.position w).prod Q) 0 := by
    simpa only [ContinuousLinearMap.comp_id, zero_add] using!
      hp'.comp 0 ((hasFDerivAt_id (0 : S.covector.ker)).const_add w)
  have hvalue : F.chartMomentumFamily D.initialChart (fun z ↦ S.curve (w + z)) (0, 0) =
      F.chartMomentumFamily D.initialChart N.curve (0, 0) := by
    change F.chartMomentumFamily D.initialChart S.curve (w + 0, 0) = _
    rw [add_zero, S.initial_phase_eq D hw, N.initial_phase]
  have hsame := hF.same_firstJet_of_complete_initial_phase hcomplete D.initialChart 0
    hB h0 hEL (fun z hz ↦ N.complete z hz.1) hsource
    (fun z hz ↦ N.initial_source z hz.1) hjet N.initial_jet hvalue
  simpa only [add_zero] using! hsame

/-- Almost every original label has a genuine all-label normal smooth family with
its exact original kernel and a quadratic-small potential error. Only the actual
pulled-back covector derivative is used, without an ambient second derivative. -/
theorem ae_exists_normalPotentialFamily (S : CalibratedLevelSeedPatch F u)
    (D : C11LevelSeedPresentation F u S.covector S.level S.openLabels S.labels S.curve)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure S.covector.ker) [m.IsAddHaarMeasure]
    (bW : Basis ι ℝ S.covector.ker) :
    ∀ᵐ w ∂m.restrict S.labels,
      let R := fderiv ℝ D.position w
      let Q := fderiv ℝ (fun z ↦ fderiv ℝ D.potential (D.position z)) w
      let p := (D.position w, fderiv ℝ D.potential (D.position w))
      w ∈ S.labels ∧ ∃ N : F.NormalPotentialFamily D.initialChart p R Q S.level,
        S.curve w = N.curve 0 ∧
        (∀ (terminal : M) (t : ℝ),
          N.curve 0 t ∈ (extChartAt 𝓘(ℝ, E) terminal).source →
          HasFDerivAt (F.chartMomentumFamily terminal (fun z ↦ S.curve (w + z)))
            (fderiv ℝ (F.chartMomentumFamily terminal N.curve) (0, t)) (0, t) ∧
          HasFDerivAt (F.chartMomentumFamily terminal N.curve)
            (fderiv ℝ (F.chartMomentumFamily terminal N.curve) (0, t)) (0, t)) ∧
        (fun z ↦ D.potential (D.position z) -
          secondJetPolynomial p.1 S.level p.2 N.hessian (D.position z)) =o[𝓝 w]
            (fun z ↦ ‖z - w‖ ^ 2) ∧
        ∀ t : ℝ,
          F.familyLabelHessianMatrix bW (fun q ↦ S.curve q.1 q.2) (w, t) =
            F.familyLabelHessianMatrix bW (fun q ↦ N.curve q.1 q.2) (0, t) := by
  filter_upwards [S.ae_initial_phase_regular_energy D hF m] with w hwdata
  obtain ⟨hw, _, hR, hnormal, hQ, _, hiso, e, he, hsource, hInv, hp, henergy, hzero⟩ := hwdata
  let R := fderiv ℝ D.position w
  let Q := fderiv ℝ (fun z ↦ fderiv ℝ D.potential (D.position z)) w
  let p := (D.position w, fderiv ℝ D.potential (D.position w))
  have hsym (ξ η : S.covector.ker) : Q ξ (R η) = Q η (R ξ) := by
    have hi := hiso ξ η
    change Q η (R ξ) - Q ξ (R η) = 0 at hi
    exact (sub_eq_zero.mp hi).symm
  have hnorm (ξ : S.covector.ker) : p.2 (R ξ) = 0 :=
    congrArg (fun L : S.covector.ker →L[ℝ] ℝ ↦ L ξ) hnormal
  obtain ⟨N⟩ := hF.nonempty_normalPotentialFamily hcomplete D.initialChart
    he hsource hInv hp henergy R Q hzero hR hsym hnorm S.level
  obtain ⟨hcurve, hjets⟩ := S.same_phase_firstJet_of_normalPotentialFamily D hF hcomplete
    (S.labels_subset hw) hQ N
  refine ⟨hw, N, hcurve, hjets, ?_, ?_⟩
  · let P := secondJetPolynomial p.1 S.level p.2 N.hessian
    have hPs : ContDiff ℝ ∞ P := contDiff_secondJetPolynomial _ _ _ _
    have hPD : HasFDerivAt P p.2 p.1 := by
      have hd := hasFDerivAt_secondJetPolynomial p.1 (S.level : ℝ) p.2
        N.hessian N.hessian_symm p.1
      rw [sub_self, N.hessian.map_zero, add_zero] at hd
      exact hd
    exact pullback_potential_error_isLittleO D.potential_contDiff.contDiffAt
      (hPs.contDiffAt.of_le (by simp))
      (D.position_contDiff.contDiffAt (S.openLabels_open.mem_nhds (S.labels_subset hw))) hQ
      (hasFDerivAt_fderiv_secondJetPolynomial _ _ _ _ N.hessian_symm _)
      N.hessian_comp ((secondJetPolynomial_self _ _ _ _).trans
        (D.level_eq w (S.labels_subset hw)).symm) hPD.fderiv
  · intro t
    exact S.familyLabelHessianMatrix_eq_centered_family hF bW hw hcurve N.open_labels
      N.anchor_mem (N.tangent_smooth.of_le (by simp)) (N.energy_eq 0 N.anchor_mem) t
        (fun old hx ↦ hjets old t hx)

end OTSelector.Geometry.ContinuousFinslerNorm.CalibratedLevelSeedPatch
