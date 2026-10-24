import OTSelector.Geometry.Finsler.C11EikonalSeed
import OTSelector.Geometry.Finsler.NormalizedSeedJet
import OTSelector.Analysis.Calculus.ParameterizedSecondJetLevel

/-!
# Original-core first jets of a selected normalized polynomial seed

The actual calibrated core gives the energy graph identity on a density-one set,
on the same supplied Legendre inverse branch. The explicit polynomial made from
its actual second jet has the identical energy-graph derivative. Consequently the
selected normalization has zero scale derivative and retains the original first jet.
The original potential covector graph is differentiated only within the original core.
-/

open Set Filter Metric MeasureTheory MeasureTheory.Measure Manifold
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

private theorem parameterizedSeedJet_density_one_inter_open
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]
    (m : Measure E) {C V : Set E} {x : E}
    (hx : Tendsto (fun r ↦ m (C ∩ closedBall x r) / m (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) (hV : IsOpen V) (hxV : x ∈ V) :
    Tendsto (fun r ↦ m ((C ∩ V) ∩ closedBall x r) / m (closedBall x r))
      (𝓝[>] 0) (𝓝 1) := by
  apply hx.congr'
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hxV)
  have hr : ∀ᶠ r : ℝ in 𝓝[>] 0, r < ε := nhdsWithin_le_nhds (gt_mem_nhds hε)
  filter_upwards [hr] with r hr
  have hclosed : closedBall x r ⊆ V := by
    intro y hy
    exact hball ((mem_closedBall.mp hy).trans_lt hr)
  have heq : (C ∩ V) ∩ closedBall x r = C ∩ closedBall x r := by
    ext y
    exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, hclosed h.2⟩, h.2⟩⟩
  rw [heq]

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- A genuine calibrated-core second jet identifies the first jet of the same selected
normalized polynomial seed and its original covector graph, on the supplied branch. -/
theorem normalized_polynomial_seed_firstJet_of_calibrated_core
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
    {σ v : W → E} {a : W → ℝ} {w₀ : W}
    (hσ : DifferentiableAt ℝ σ w₀) (hσ₀ : σ w₀ = x)
    (hv : ContinuousAt v w₀) (ha : DifferentiableAt ℝ a w₀)
    (ha₀ : a w₀ = 1) (hzs : (σ w₀, v w₀) ∈ eL.source)
    (hdata :
      let P := scalarSecondJetPolynomial
        (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)
      ∀ᶠ w in 𝓝 w₀,
        F.chartEnergy old (σ w, v w) = F.chartEnergy old (σ w₀, v w₀) ∧
        fiberLegendre (F.chartEnergy old) (σ w, v w) =
          a w • fderiv ℝ P (σ w)) :
    let R := fderiv ℝ σ w₀
    let H := fderiv ℝ (fderiv ℝ G) x
    let D : W →L[ℝ] E × (E →L[ℝ] ℝ) := R.prod (H.comp R)
    fderiv ℝ a w₀ = 0 ∧
      parametricLegendre (F.chartEnergy old) (σ w₀, v w₀) =
        (x, fderiv ℝ G x) ∧
      HasFDerivAt
        (fun w ↦ parametricLegendre (F.chartEnergy old) (σ w, v w)) D w₀ ∧
      HasFDerivAt (fun w ↦ (σ w, fderiv ℝ G (σ w))) D w₀ ∧
      HasFDerivWithinAt
        (fun w ↦ (σ w,
          fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (σ w)))
        D (σ ⁻¹' C) w₀ := by
  let _instParameterizedSeedJetMetric : MetricSpace M := F.metricSpace
  let H := fderiv ℝ (fderiv ℝ G) x
  let P : E → ℝ := scalarSecondJetPolynomial (x, G x, fderiv ℝ G x, H)
  have hfirst : ∀ᶠ y in 𝓝 x, HasFDerivAt G (fderiv ℝ G y) y :=
    Filter.Eventually.of_forall (fun y ↦ (hG.differentiable one_ne_zero y).hasFDerivAt)
  have hsym : ∀ v w : E, H v w = H w v :=
    second_derivative_symmetric_of_eventually hfirst hsecond
  have hP : ContDiff ℝ ∞ P :=
    contDiff_secondJetPolynomial x (G x) (fderiv ℝ G x) H
  have hDP : HasFDerivAt (fderiv ℝ P) H x :=
    hasFDerivAt_fderiv_secondJetPolynomial x (G x) (fderiv ℝ G x) H hsym x
  have hPx : fderiv ℝ P x = fderiv ℝ G x :=
    (hasFDerivAt_scalarSecondJetPolynomial_center (x, G x, fderiv ℝ G x, H)).fderiv
  change ∀ᶠ w in 𝓝 w₀,
    F.chartEnergy old (σ w, v w) = F.chartEnergy old (σ w₀, v w₀) ∧
    fiberLegendre (F.chartEnergy old) (σ w, v w) = a w • fderiv ℝ P (σ w) at hdata
  have hcentral : parametricLegendre (F.chartEnergy old) (σ w₀, v w₀) =
      (x, fderiv ℝ G x) := by
    apply Prod.ext hσ₀
    change fiberLegendre (F.chartEnergy old) (σ w₀, v w₀) = fderiv ℝ G x
    simpa only [ha₀, one_smul, hσ₀, hPx] using hdata.self_of_nhds.2
  have hp : (x, fderiv ℝ G x) ∈ eL.target := by
    rw [← hcentral, ← heL]
    exact eL.map_source hzs
  let V : Set E := (fun y ↦ (y, fderiv ℝ G y)) ⁻¹' eL.target
  have hV : IsOpen V := eL.open_target.preimage
    (continuous_id.prodMk (hG.continuous_fderiv one_ne_zero))
  have hxV : x ∈ V := hp
  have hd : ∀ y ∈ C, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u
      ((extChartAt 𝓘(ℝ, E) old).symm y) :=
    fun y hy ↦ hF.mdifferentiableAt_of_mem_calibratedInterior hcomplete hu (hinterior hy)
  have hunit := hF.chart_unit_legendre_on_of_calibrated_endpoints hcomplete old hCt hu hd
    (fun y hy ↦ (hinterior hy).2)
  have hmatch : EqOn (fderiv ℝ G)
      (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm)) C :=
    fun y hy ↦ (hactual y hy).fderiv.symm
  have henergy : ∀ y ∈ C ∩ V,
      localHamiltonian (F.chartEnergy old) eL (y, fderiv ℝ G y) = (1 / 2 : ℝ) := by
    intro y hy
    obtain ⟨vy, hvy, hvp, hve⟩ := hunit y hy.1
    have hyt : (y, fderiv ℝ G y) ∈ eL.target := hy.2
    have hinverse : eL.symm (y, fderiv ℝ G y) = (y, vy) := by
      apply hF.injOn_parametricLegendre_chartEnergy old (hsource (eL.map_target hyt)) hvy
      calc
        parametricLegendre (F.chartEnergy old) (eL.symm (y, fderiv ℝ G y)) =
            (y, fderiv ℝ G y) := by simpa only [heL] using eL.right_inv hyt
        _ = parametricLegendre (F.chartEnergy old) (y, vy) := by
          simp only [parametricLegendre, hvp, hmatch hy.1]
    rw [hF.localHamiltonian_chartEnergy_eq old heL hsource hyt, hinverse]
    exact hve
  have hdensityV := parameterizedSeedJet_density_one_inter_open m hdensity hV hxV
  have hzero := (hF.chartHamiltonian_energyGraph_hasFDerivAt_zero_of_density_one m old
    heL hsource hInv hdensityV (show x ∈ C ∩ V from ⟨hxC, hxV⟩)
    hsecond hp henergy).1
  let Hamiltonian := localHamiltonian (F.chartEnergy old) eL
  have hHd : DifferentiableAt ℝ Hamiltonian (x, fderiv ℝ G x) :=
    ((contDiffOn_localHamiltonian ((hF.contDiffOn_chartEnergy old).mono hsource)
      hInv).contDiffAt (eL.open_target.mem_nhds hp)).differentiableAt (by simp)
  have hroughChain : HasFDerivAt (fun y ↦ Hamiltonian (y, fderiv ℝ G y))
      ((fderiv ℝ Hamiltonian (x, fderiv ℝ G x)).comp
        ((ContinuousLinearMap.id ℝ E).prod H)) x := by
    simpa only [Function.comp_apply, id_eq] using!
      hHd.hasFDerivAt.comp x ((hasFDerivAt_id (𝕜 := ℝ) x).prodMk hsecond)
  have hlinearZero := hroughChain.unique hzero
  have hpolyHd : DifferentiableAt ℝ Hamiltonian (x, fderiv ℝ P x) := by
    simpa only [hPx] using hHd
  have hpolyChain := hpolyHd.hasFDerivAt.comp x
    ((hasFDerivAt_id (𝕜 := ℝ) x).prodMk hDP)
  rw [hPx, hlinearZero] at hpolyChain
  have hpolyZero : HasFDerivAt (fun y ↦ Hamiltonian (y, fderiv ℝ P y))
      (0 : E →L[ℝ] ℝ) (σ w₀) := by
    rw [hσ₀]
    exact hpolyChain
  have hjet : HasFDerivAt
      (fun w ↦ localHamiltonian (F.chartEnergy old) eL (σ w, fderiv ℝ P (σ w)))
      (0 : W →L[ℝ] ℝ) w₀ := by
    simpa only [ContinuousLinearMap.zero_comp, Function.comp_apply] using!
      hpolyZero.comp w₀ hσ.hasFDerivAt
  obtain ⟨hscale, hseed⟩ := hF.potentialConormalState_firstJet_of_constantEnergy old
    (hP.contDiffAt.of_le (by simp)) hσ hv ha ha₀ heL hsource hInv hzs hdata hjet
  have hHess : fderiv ℝ (fderiv ℝ P) (σ w₀) = H := by
    rw [hσ₀]
    exact hDP.fderiv
  rw [hHess] at hseed
  have hselected :
      (fun w ↦ parametricLegendre (F.chartEnergy old) (σ w, v w)) =ᶠ[𝓝 w₀]
        potentialConormalState P σ a := by
    filter_upwards [hdata] with w hw
    exact Prod.ext rfl hw.2
  have hsecondσ : HasFDerivAt (fderiv ℝ G) H (σ w₀) := by
    simpa only [hσ₀] using hsecond
  have hrough : HasFDerivAt (fun w ↦ (σ w, fderiv ℝ G (σ w)))
      ((fderiv ℝ σ w₀).prod (H.comp (fderiv ℝ σ w₀))) w₀ :=
    hσ.hasFDerivAt.prodMk (hsecondσ.comp w₀ hσ.hasFDerivAt)
  refine ⟨hscale, hcentral, hseed.congr_of_eventuallyEq hselected, hrough, ?_⟩
  apply hrough.hasFDerivWithinAt.congr'
  · intro w hw
    exact Prod.ext rfl (hactual (σ w) hw).fderiv
  · change σ w₀ ∈ C
    rwa [hσ₀]

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
