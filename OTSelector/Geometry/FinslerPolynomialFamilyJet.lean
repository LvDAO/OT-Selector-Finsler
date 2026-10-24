import OTSelector.Geometry.FinslerPolynomialTubeData
import OTSelector.Geometry.FinslerParameterizedSeedJet

/-!
# Actual initial first jets of the normalized polynomial family

The original calibrated core identifies the ordinary first jet of the prescribed
polynomial family. Its velocity and scale are the explicit covector normalization;
the inverse branch, section, and supplied complete flow are retained.
-/

open Set Filter Metric MeasureTheory MeasureTheory.Measure Manifold Bundle
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- The actual normalized polynomial flow has the original central momentum and
the phase derivative determined by the section derivative and original Hessian. -/
theorem polynomialPhaseFamily_initial_firstJet_of_calibrated_core
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    (m : Measure E) [IsAddHaarMeasure m]
    {C : Set E} (hCt : C ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hinterior : letI : MetricSpace M := F.metricSpace
      MapsTo (extChartAt 𝓘(ℝ, E) old).symm C
        (OTSelector.Geometry.calibratedInterior u))
    {G : E → ℝ} (hG : ContDiff ℝ 1 G)
    (hactual : ∀ y ∈ C,
      HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (fderiv ℝ G y) y)
    {x : E} (hxC : x ∈ C)
    (hdensity : Tendsto
      (fun r ↦ m (C ∩ closedBall x r) / m (closedBall x r))
      (𝓝[>] 0) (𝓝 1))
    (hsecond : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) x) x)
    {eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (heL : (eL : E × E → E × (E →L[ℝ] ℝ)) =
      parametricLegendre (F.chartEnergy old))
    (hsource : eL.source ⊆ chartEnergyDomain old)
    (hInv : ContDiffOn ℝ ∞ eL.symm eL.target)
    (hlegal : (x, fderiv ℝ G x) ∈ eL.target)
    (henergy : F.chartEnergy old (eL.symm (x, fderiv ℝ G x)) = 1 / 2)
    {O : Set (ScalarSecondJet E)} {B : Set W}
    (hO : IsOpen O) (hB : IsOpen B) (h0B : (0 : W) ∈ B)
    (hj : (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x) ∈ O)
    {σ : ScalarSecondJet E × W → E} (hσ : ContDiffOn ℝ 1 σ (O ×ˢ B))
    (hσ₀ : σ ((x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x), 0) = x)
    {Φ : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Φ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Φ z) ⟨0, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z) :
    let j : ScalarSecondJet E :=
      (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)
    let R := fderiv ℝ (fun w ↦ σ (j, w)) 0
    let Γ := F.polynomialPhaseFamily old Φ eL σ j
    F.chartMomentumFamily old Γ (0, 0) = (x, fderiv ℝ G x) ∧
      HasFDerivAt (fun w ↦ F.chartMomentumFamily old Γ (w, 0))
        (R.prod ((fderiv ℝ (fderiv ℝ G) x).comp R)) 0 := by
  let j : ScalarSecondJet E :=
    (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)
  let P : E → ℝ := scalarSecondJetPolynomial j
  let s : W → E := fun w ↦ σ (j, w)
  let q : W → E × (E →L[ℝ] ℝ) := fun w ↦ (s w, fderiv ℝ P (s w))
  let N : W → E × E := fun w ↦ F.covectorNormalization old eL (1 / 2) (q w)
  let v : W → E := fun w ↦ (N w).2
  let a : W → ℝ := fun w ↦ F.covectorNormalizationScale old eL (1 / 2) (q w)
  let Γ : W → ℝ → M := F.polynomialPhaseFamily old Φ eL σ j
  have hs0 : s 0 = x := hσ₀
  have hs : ContDiffAt ℝ 1 s 0 :=
    (hσ.contDiffAt ((hO.prod hB).mem_nhds ⟨hj, h0B⟩)).comp 0
      (contDiffAt_const.prodMk contDiffAt_id)
  have hP : ContDiff ℝ ∞ P :=
    contDiff_secondJetPolynomial x (G x) (fderiv ℝ G x) (fderiv ℝ (fderiv ℝ G) x)
  have hq : ContDiffAt ℝ 1 q 0 :=
    hs.prodMk (((hP.fderiv_right
      (show (1 : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) by simp)).contDiffAt).comp 0 hs)
  have hq0 : q 0 = (x, fderiv ℝ G x) := by
    change (s 0, fderiv ℝ P (s 0)) = _
    rw [hs0]
    exact Prod.ext rfl (hasFDerivAt_scalarSecondJetPolynomial_center j).fderiv
  have hqlegal : q 0 ∈ eL.target := by rw [hq0]; exact hlegal
  have hnear : ∀ᶠ w in 𝓝 (0 : W), q w ∈ eL.target :=
    hq.continuousAt (eL.open_target.mem_nhds hqlegal)
  have hc : (0 : ℝ) < 1 / 2 := by norm_num
  obtain ⟨hscale, hnormal, hspec⟩ := hF.covectorNormalization_spec old heL hsource hInv hc
  have ha : DifferentiableAt ℝ a 0 :=
    ((hscale.contDiffAt (eL.open_target.mem_nhds hqlegal)).differentiableAt (by simp)).comp
      0 (hq.differentiableAt one_ne_zero)
  have hv : ContinuousAt v 0 :=
    ((hnormal.contDiffAt (eL.open_target.mem_nhds hqlegal)).continuousAt.comp
      hq.continuousAt).snd
  have ha0 : a 0 = 1 := by
    change Real.sqrt ((1 / 2) / F.chartEnergy old (eL.symm (q 0))) = 1
    rw [hq0, henergy]
    norm_num
  have hN0 : N 0 = eL.symm (x, fderiv ℝ G x) := by
    change F.covectorNormalization old eL (1 / 2) (q 0) = _
    rw [hq0]
    exact (hspec _ hlegal).2.2.2.2 henergy
  have hzs : (s 0, v 0) ∈ eL.source := by
    change N 0 ∈ eL.source
    rw [hN0]
    exact eL.map_target hlegal
  have henergy0 : F.chartEnergy old (s 0, v 0) = 1 / 2 :=
    (hspec _ hqlegal).2.2.1
  have hdata : ∀ᶠ w in 𝓝 (0 : W),
      F.chartEnergy old (s w, v w) = F.chartEnergy old (s 0, v 0) ∧
      fiberLegendre (F.chartEnergy old) (s w, v w) = a w • fderiv ℝ P (s w) := by
    filter_upwards [hnear] with w hw
    exact ⟨(hspec _ hw).2.2.1.trans henergy0.symm, (hspec _ hw).2.2.2.1⟩
  obtain ⟨_, hcenter, hseed, _, _⟩ :=
    hF.normalized_polynomial_seed_firstJet_of_calibrated_core hcomplete old m hCt hu
      hinterior hG hactual hxC hdensity hsecond heL hsource hInv
      (hs.differentiableAt one_ne_zero) hs0 hv ha ha0 hzs hdata
  have hmomentum : (fun w ↦ F.chartMomentumFamily old Γ (w, 0)) =ᶠ[𝓝 (0 : W)]
      (fun w ↦ parametricLegendre (F.chartEnergy old) (s w, v w)) := by
    filter_upwards [hnear] with w hw
    have hz : N w ∈ chartEnergyDomain old := (hspec _ hw).2.1
    change eulerLagrangePhaseLift (F.chartEnergy old)
      (extChartAt 𝓘(ℝ, E) old ∘ Φ (N w)) 0 = _
    exact hF.chartMomentum_of_tangent_eq (hEL _ hz 0 (mem_univ _)) old hz (hinit _ hz)
  exact ⟨hmomentum.self_of_nhds.trans hcenter,
    hseed.congr_of_eventuallyEq hmomentum⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
