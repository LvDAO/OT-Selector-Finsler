import OTSelector.Geometry.FinslerCompleteAdaptedFocal
import OTSelector.Geometry.GraphFocalPositionRank
import OTSelector.Geometry.RegraphedFocalIsolation

/-!
# Local isolation of actual position degeneracies along a complete Finsler family

The original momentum chooses the local clock. The actual focal expansion and the
normal position-kernel identity transfer punctured graph-time injectivity to the
original time and original chart, without a position-rank hypothesis.
-/

open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E W V M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

private theorem eventually_chartPosition_normal_data (hF : F.IsSmoothStronglyConvex)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    {w₀ : W} (hw : w₀ ∈ B)
    (hnormal : ∀ (old : M) (t : ℝ), Γ w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source →
      ∀ ξ : W, (F.chartMomentumFamily old Γ (w₀, t)).2
        (fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) old (Γ w t)) w₀ ξ) = 0)
    (old : M) (A : E ≃L[ℝ] (ℝ × V)) (t₀ : ℝ)
    (hx : Γ w₀ t₀ ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hpos : 0 < (A (deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ w₀) t₀)).1) :
    let γ := fun q : W × ℝ ↦ extChartAt 𝓘(ℝ, E) old (Γ q.1 q.2)
    ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ γ (w₀, t) ∧
      (A (fderiv ℝ γ (w₀, t) (0, 1))).1 ≠ 0 ∧
      ∃ p : E →L[ℝ] ℝ, p (fderiv ℝ γ (w₀, t) (0, 1)) ≠ 0 ∧
        ∀ ξ : W, p (fderiv ℝ (fun w ↦ γ (w, t)) w₀ ξ) = 0 := by
  let γ := fun q : W × ℝ ↦ extChartAt 𝓘(ℝ, E) old (Γ q.1 q.2)
  obtain ⟨_, r, _, _, _, hr, _, hchart, hΨ, _, _⟩ :=
    hF.exists_chartMomentumFamily_box hB hEL hG hw old t₀ hx
  let U := ball w₀ r ×ˢ Ioo (t₀ - r) (t₀ + r)
  have hU : IsOpen U := isOpen_ball.prod isOpen_Ioo
  have hw₀ : w₀ ∈ ball w₀ r := mem_ball_self hr
  have ht₀ : t₀ ∈ Ioo (t₀ - r) (t₀ + r) := by constructor <;> linarith
  have hγ : ContDiffOn ℝ 2 γ U := hΨ.fst
  have hv (t : ℝ) (ht : t ∈ Ioo (t₀ - r) (t₀ + r)) :
      fderiv ℝ γ (w₀, t) (0, 1) = deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ w₀) t := by
    have hd := ((hγ.contDiffAt (hU.mem_nhds ⟨hw₀, ht⟩)).differentiableAt
      (by norm_num)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_const t w₀).prodMk (hasDerivAt_id t))
    exact hd.deriv.symm
  have hdc : ContinuousAt (fun t ↦ (A (fderiv ℝ γ (w₀, t) (0, 1))).1) t₀ := by
    have hγ₀ : ContDiffAt ℝ 2 γ (w₀, t₀) :=
      hγ.contDiffAt (hU.mem_nhds ⟨hw₀, ht₀⟩)
    have hd := (hγ₀.fderiv_right (m := 1) (by norm_num)).continuousAt
    exact ((A.continuousAt.comp (hd.clm_apply continuousAt_const)).fst).comp
      (continuousAt_const.prodMk continuousAt_id)
  have hpos' : 0 < (A (fderiv ℝ γ (w₀, t₀) (0, 1))).1 := by rwa [hv t₀ ht₀]
  have hev := hdc.eventually (isOpen_Ioi.mem_nhds hpos')
  filter_upwards [isOpen_Ioo.mem_nhds ht₀, hev] with t ht htpos
  have hx' := hchart (w₀, t) ⟨hw₀, ht⟩
  have hz := (hF.chartTangent_of_isEulerLagrangeAt (hEL w₀ hw t (mem_univ _)) old hx').2
  refine ⟨(hγ.contDiffAt (hU.mem_nhds ⟨hw₀, ht⟩)).differentiableAt (by norm_num),
    ne_of_gt htpos, (F.chartMomentumFamily old Γ (w₀, t)).2, ?_, ?_⟩
  · rw [hv t ht]
    change fiberLegendre (F.chartEnergy old)
      ((extChartAt 𝓘(ℝ, E) old ∘ Γ w₀) t,
        deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ w₀) t)
      (deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ w₀) t) ≠ 0
    rw [hF.chartLegendre_self_eq_chartLength_sq old hz]
    exact pow_ne_zero _ (NNReal.coe_pos.mpr (F.chartLength_pos old hz)).ne'
  · exact hnormal old t hx'

/-- For a codimension-one complete normal family, actual position parameter degeneracies
are locally isolated in original time and any legal original chart. Neither position
injectivity at the center nor an adapted clock or focal expansion is an input. -/
theorem eventually_injective_chartPosition_of_completeFamily [FiniteDimensional ℝ W]
    (hF : F.IsSmoothStronglyConvex)
    (hdim : Module.finrank ℝ W + 1 = Module.finrank ℝ E)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    {C₀ : ℝ} (henergy : ∀ w ∈ B, ∀ t : ℝ,
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t, (1 : ℝ)⟩) = C₀)
    {w₀ : W} (hw : w₀ ∈ B)
    (hrank : ∀ (old : M) (t : ℝ), Γ w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source →
      Function.Injective (fderiv ℝ (fun w ↦ F.chartMomentumFamily old Γ (w, t)) w₀))
    (hpair : ∀ (old : M) (t : ℝ), Γ w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source →
      ∀ ξ η : W, canonicalPhasePairing
        (fderiv ℝ (fun w ↦ F.chartMomentumFamily old Γ (w, t)) w₀ ξ)
        (fderiv ℝ (fun w ↦ F.chartMomentumFamily old Γ (w, t)) w₀ η) = 0)
    (hnormal : ∀ (old : M) (t : ℝ), Γ w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source →
      ∀ ξ : W, (F.chartMomentumFamily old Γ (w₀, t)).2
        (fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) old (Γ w t)) w₀ ξ) = 0)
    (old : M) (t₀ : ℝ)
    (hx : Γ w₀ t₀ ∈ (extChartAt 𝓘(ℝ, E) old).source) :
    ∀ᶠ t in 𝓝[≠] t₀, Function.Injective
      (fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) old (Γ w t)) w₀) := by
  let x := extChartAt 𝓘(ℝ, E) old ∘ Γ w₀
  let p := fiberLegendre (F.chartEnergy old) (x t₀, deriv x t₀)
  obtain ⟨hdimP, A, hAv, hJacobi⟩ :=
    hF.exists_completeFamily_adaptedGraphStructure hB hEL hG henergy hw
      hrank hpair hnormal old t₀ hx
  change Module.finrank ℝ p.ker + 1 = Module.finrank ℝ E at hdimP
  have hdim' : Module.finrank ℝ W = Module.finrank ℝ p.ker := by omega
  have hFocal := hF.hasAdaptedGraphFocalChart_of_finrank hdim' hJacobi
  obtain ⟨bW, e, g, D, he, hsource, _, _, _, _, _, hcenter, _, _, _, _, hfocal, _⟩ :=
    hFocal
  have hpositive : 0 < (A (deriv x t₀)).1 := by rw [hAv]; norm_num
  have hlocal := hF.eventually_chartPosition_normal_data hB hEL hG hw hnormal old A t₀ hx
    hpositive
  exact curveGraphPosition_eventually_injective_original_time A he hsource hlocal
    (hfocal.eventually_injective_position_fderiv hcenter)

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
