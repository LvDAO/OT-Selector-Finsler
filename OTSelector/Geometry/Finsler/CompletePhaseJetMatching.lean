import OTSelector.Analysis.Calculus.FlowJetMatching
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.EndpointMinimizerStability
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.FlowLocalC2
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.LegendreInjectivity
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.TangentReadout

/-!
# Geometry.Finsler.CompletePhaseJetMatching

* **Conditions:** Two supplied complete actual families have the same ordinary initial phase first jet and explicit legal initial chart membership.
* **Objects:** The same central trajectory and identical ordinary joint phase/position jets at every legal output time.
* **Proof detail:** Represent both germs through one genuine Legendre inverse and one complete flow; use initial uniqueness and the ordinary composite chain rule.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=61): Section 2.6, pp. 50–51, overlap uniqueness, equation (2.63), and Theorem 2.13 (unique maximal solution).
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): No within-set derivative uniqueness or density argument is used for this ordinary first-jet theorem.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerCompletePhaseJetMatching.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerCompletePhaseJetMatching`; the selected original proof blocks follow. -/
section

/-!
# Ordinary first-jet matching for actual complete Finsler families

Two supplied complete original Euler--Lagrange families with the same ordinary
initial phase jet have the same central trajectory and the same ordinary joint
phase jet at every legal output time. One genuine Legendre inverse and one complete
original tangent family represent both germs. Actual initial chart membership is
explicit; no density or uniqueness of within-set derivatives is used.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {F : ContinuousFinslerNorm E M}

/-- Equal actual initial phase values and ordinary first derivatives propagate to
ordinary joint phase derivatives of the two given complete families. Source legality
at the initial time is supplied by actual positions, independently of totalized phase
values. The common inverse branch and complete tangent flow are constructed internally. -/
theorem same_firstJet_of_complete_initial_phase (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (initial : M) (t₀ : ℝ)
    {B : Set W} (hB : IsOpen B) {w₀ : W} (hw₀ : w₀ ∈ B)
    {Γ₁ Γ₂ : W → ℝ → M}
    (hEL₁ : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ₁ w) univ)
    (hEL₂ : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ₂ w) univ)
    (hsource₁ : ∀ w ∈ B, Γ₁ w t₀ ∈ (extChartAt 𝓘(ℝ, E) initial).source)
    (hsource₂ : ∀ w ∈ B, Γ₂ w t₀ ∈ (extChartAt 𝓘(ℝ, E) initial).source)
    {D : W →L[ℝ] (E × (E →L[ℝ] ℝ))}
    (hjet₁ : HasFDerivAt (fun w ↦ F.chartMomentumFamily initial Γ₁ (w, t₀)) D w₀)
    (hjet₂ : HasFDerivAt (fun w ↦ F.chartMomentumFamily initial Γ₂ (w, t₀)) D w₀)
    (hvalue : F.chartMomentumFamily initial Γ₁ (w₀, t₀) =
      F.chartMomentumFamily initial Γ₂ (w₀, t₀)) :
    Γ₁ w₀ = Γ₂ w₀ ∧ ∀ (terminal : M) (r : ℝ),
      Γ₂ w₀ r ∈ (extChartAt 𝓘(ℝ, E) terminal).source →
      HasFDerivAt (F.chartMomentumFamily terminal Γ₁)
        (fderiv ℝ (F.chartMomentumFamily terminal Γ₂) (w₀, r)) (w₀, r) ∧
      HasFDerivAt (F.chartMomentumFamily terminal Γ₂)
        (fderiv ℝ (F.chartMomentumFamily terminal Γ₂) (w₀, r)) (w₀, r) := by
  let Q₁ : W → E × (E →L[ℝ] ℝ) :=
    fun w ↦ F.chartMomentumFamily initial Γ₁ (w, t₀)
  let Q₂ : W → E × (E →L[ℝ] ℝ) :=
    fun w ↦ F.chartMomentumFamily initial Γ₂ (w, t₀)
  let z₂ : E × E := ((extChartAt 𝓘(ℝ, E) initial ∘ Γ₂ w₀) t₀,
    deriv (extChartAt 𝓘(ℝ, E) initial ∘ Γ₂ w₀) t₀)
  have hz₂ : z₂ ∈ chartEnergyDomain initial :=
    (hF.chartTangent_of_isEulerLagrangeAt (hEL₂ w₀ hw₀ t₀ (mem_univ _))
      initial (hsource₂ w₀ hw₀)).2
  obtain ⟨e, he, _, hzt, hsub, _, hInv, _, _⟩ :=
    hF.exists_smooth_chartLegendre_local_inverse initial hz₂
  have hQ₂target : Q₂ w₀ ∈ e.target := hzt
  have hQ₁target : Q₁ w₀ ∈ e.target := by
    change F.chartMomentumFamily initial Γ₁ (w₀, t₀) ∈ e.target
    rw [hvalue]
    exact hQ₂target
  let S₁ : W → E × E := fun w ↦ e.symm (Q₁ w)
  let S₂ : W → E × E := fun w ↦ e.symm (Q₂ w)
  let A : W →L[ℝ] E × E := (fderiv ℝ e.symm (Q₂ w₀)).comp D
  have hE : HasFDerivAt e.symm (fderiv ℝ e.symm (Q₂ w₀)) (Q₂ w₀) :=
    ((hInv.contDiffAt (e.open_target.mem_nhds hQ₂target)).differentiableAt
      (by simp)).hasFDerivAt
  have hS₁ : HasFDerivAt S₁ A w₀ := by
    have hE₁ : HasFDerivAt e.symm (fderiv ℝ e.symm (Q₂ w₀)) (Q₁ w₀) := by
      change HasFDerivAt e.symm _ (F.chartMomentumFamily initial Γ₁ (w₀, t₀))
      rw [hvalue]
      exact hE
    exact hE₁.comp w₀ hjet₁
  have hS₂ : HasFDerivAt S₂ A w₀ := hE.comp w₀ hjet₂
  have hSvalue : S₁ w₀ = S₂ w₀ := congrArg e.symm hvalue
  obtain ⟨Φ, hΦEL, hΦinit, hΦ⟩ :=
    hF.exists_complete_tangentFamily_C2 hcomplete initial t₀
  have hrealize (Γ : W → ℝ → M)
      (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
      (hsource : ∀ w ∈ B, Γ w t₀ ∈ (extChartAt 𝓘(ℝ, E) initial).source)
      (hQ : DifferentiableAt ℝ (fun w ↦ F.chartMomentumFamily initial Γ (w, t₀)) w₀)
      (hQt : F.chartMomentumFamily initial Γ (w₀, t₀) ∈ e.target) :
      (fun w ↦ Φ (e.symm (F.chartMomentumFamily initial Γ (w, t₀))))
        =ᶠ[𝓝 w₀] Γ := by
    filter_upwards [hB.mem_nhds hw₀,
      hQ.continuousAt (e.open_target.mem_nhds hQt)] with w hw hwt
    let z : E × E := ((extChartAt 𝓘(ℝ, E) initial ∘ Γ w) t₀,
      deriv (extChartAt 𝓘(ℝ, E) initial ∘ Γ w) t₀)
    have hz : z ∈ chartEnergyDomain initial :=
      (hF.chartTangent_of_isEulerLagrangeAt (hEL w hw t₀ (mem_univ _))
        initial (hsource w hw)).2
    have hstate : e.symm (F.chartMomentumFamily initial Γ (w, t₀)) = z := by
      apply hF.injOn_parametricLegendre_chartEnergy initial (hsub (e.map_target hwt)) hz
      change parametricLegendre (F.chartEnergy initial)
        (e.symm (F.chartMomentumFamily initial Γ (w, t₀))) =
          F.chartMomentumFamily initial Γ (w, t₀)
      rw [← he]
      exact e.right_inv hwt
    rw [hstate]
    exact (hF.eq_complete_family_of_isEulerLagrangeOn initial hΦEL hΦinit
      (hEL w hw) (hsource w hw)).2
  have hcurve₁ : (fun w ↦ Φ (S₁ w)) =ᶠ[𝓝 w₀] Γ₁ :=
    hrealize Γ₁ hEL₁ hsource₁ hjet₁.differentiableAt hQ₁target
  have hcurve₂ : (fun w ↦ Φ (S₂ w)) =ᶠ[𝓝 w₀] Γ₂ :=
    hrealize Γ₂ hEL₂ hsource₂ hjet₂.differentiableAt hQ₂target
  have hcenter : Γ₁ w₀ = Γ₂ w₀ :=
    hcurve₁.self_of_nhds.symm.trans ((congrArg Φ hSvalue).trans hcurve₂.self_of_nhds)
  refine ⟨hcenter, fun terminal r hr ↦ ?_⟩
  have hlegal : Φ (S₂ w₀) r ∈ (extChartAt 𝓘(ℝ, E) terminal).source := by
    have hc₂ : Φ (S₂ w₀) = Γ₂ w₀ := hcurve₂.self_of_nhds
    rw [hc₂]
    exact hr
  have hread : HasFDerivAt (F.chartMomentumFamily terminal Φ)
      (fderiv ℝ (F.chartMomentumFamily terminal Φ) (S₂ w₀, r)) (S₂ w₀, r) :=
    ((hF.contDiffAt_chartMomentumFamily_of_tangentFamily
      (isOpen_chartEnergyDomain initial) hΦEL hΦ (hsub (e.map_target hQ₂target))
      terminal r hlegal).differentiableAt (by norm_num)).hasFDerivAt
  let J : W × ℝ →L[ℝ] (E × E) × ℝ :=
    (A.comp (ContinuousLinearMap.fst ℝ W ℝ)).prod (ContinuousLinearMap.snd ℝ W ℝ)
  have hfst : HasFDerivAt (Prod.fst : W × ℝ → W)
      (ContinuousLinearMap.fst ℝ W ℝ) (w₀, r) := hasFDerivAt_fst
  have hsnd : HasFDerivAt (Prod.snd : W × ℝ → ℝ)
      (ContinuousLinearMap.snd ℝ W ℝ) (w₀, r) := hasFDerivAt_snd
  have hseed₁ : HasFDerivAt (fun q : W × ℝ ↦ (S₁ q.1, q.2)) J (w₀, r) := by
    simpa only [Function.comp_apply, J] using
      (HasFDerivAt.comp (f := Prod.fst) (g := S₁) (w₀, r) hS₁ hfst).prodMk hsnd
  have hseed₂ : HasFDerivAt (fun q : W × ℝ ↦ (S₂ q.1, q.2)) J (w₀, r) := by
    simpa only [Function.comp_apply, J] using
      (HasFDerivAt.comp (f := Prod.fst) (g := S₂) (w₀, r) hS₂ hfst).prodMk hsnd
  have hread₁ : HasFDerivAt (F.chartMomentumFamily terminal Φ)
      (fderiv ℝ (F.chartMomentumFamily terminal Φ) (S₂ w₀, r)) (S₁ w₀, r) := by
    rw [hSvalue]
    exact hread
  have hcomp₁ := hread₁.comp (w₀, r) hseed₁
  have hcomp₂ := hread.comp (w₀, r) hseed₂
  have hphase_eq (Γ : W → ℝ → M) (S : W → E × E)
      (hc : (fun w ↦ Φ (S w)) =ᶠ[𝓝 w₀] Γ) :
      (fun q : W × ℝ ↦ F.chartMomentumFamily terminal Φ (S q.1, q.2))
        =ᶠ[𝓝 (w₀, r)] F.chartMomentumFamily terminal Γ := by
    filter_upwards [(continuousAt_fst : ContinuousAt (Prod.fst : W × ℝ → W) (w₀, r))
      hc] with q hq
    change Φ (S q.1) = Γ q.1 at hq
    simp only [ContinuousFinslerNorm.chartMomentumFamily, hq]
  have hΓ₁ := hcomp₁.congr_of_eventuallyEq (hphase_eq Γ₁ S₁ hcurve₁).symm
  have hΓ₂ := hcomp₂.congr_of_eventuallyEq (hphase_eq Γ₂ S₂ hcurve₂).symm
  rw [← hΓ₂.fderiv] at hΓ₁ hΓ₂
  exact ⟨hΓ₁, hΓ₂⟩


/-- The fixed-time actual position maps of the given families have the same ordinary
first derivative whenever their actual initial phase jets agree. Taking `.fderiv` of
the first conclusion gives the equality of their actual Fréchet derivatives. -/
theorem same_position_firstJet_of_complete_initial_phase (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (initial : M) (t₀ : ℝ)
    {B : Set W} (hB : IsOpen B) {w₀ : W} (hw₀ : w₀ ∈ B)
    {Γ₁ Γ₂ : W → ℝ → M}
    (hEL₁ : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ₁ w) univ)
    (hEL₂ : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ₂ w) univ)
    (hsource₁ : ∀ w ∈ B, Γ₁ w t₀ ∈ (extChartAt 𝓘(ℝ, E) initial).source)
    (hsource₂ : ∀ w ∈ B, Γ₂ w t₀ ∈ (extChartAt 𝓘(ℝ, E) initial).source)
    {D : W →L[ℝ] (E × (E →L[ℝ] ℝ))}
    (hjet₁ : HasFDerivAt (fun w ↦ F.chartMomentumFamily initial Γ₁ (w, t₀)) D w₀)
    (hjet₂ : HasFDerivAt (fun w ↦ F.chartMomentumFamily initial Γ₂ (w, t₀)) D w₀)
    (hvalue : F.chartMomentumFamily initial Γ₁ (w₀, t₀) =
      F.chartMomentumFamily initial Γ₂ (w₀, t₀)) :
    Γ₁ w₀ = Γ₂ w₀ ∧ ∀ (terminal : M) (r : ℝ),
      Γ₂ w₀ r ∈ (extChartAt 𝓘(ℝ, E) terminal).source →
      HasFDerivAt (fun w ↦ extChartAt 𝓘(ℝ, E) terminal (Γ₁ w r))
        (fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) terminal (Γ₂ w r)) w₀) w₀ ∧
      HasFDerivAt (fun w ↦ extChartAt 𝓘(ℝ, E) terminal (Γ₂ w r))
        (fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) terminal (Γ₂ w r)) w₀) w₀ := by
  obtain ⟨hcenter, hphase⟩ := hF.same_firstJet_of_complete_initial_phase hcomplete
    initial t₀ hB hw₀ hEL₁ hEL₂ hsource₁ hsource₂ hjet₁ hjet₂ hvalue
  refine ⟨hcenter, fun terminal r hr ↦ ?_⟩
  obtain ⟨h₁, h₂⟩ := hphase terminal r hr
  have hseed : HasFDerivAt (fun w : W ↦ (w, r))
      ((ContinuousLinearMap.id ℝ W).prod (0 : W →L[ℝ] ℝ)) w₀ :=
    (hasFDerivAt_id w₀).prodMk (hasFDerivAt_const (𝕜 := ℝ) r w₀)
  have hp₁ := (HasFDerivAt.comp (f := fun w : W ↦ (w, r))
    (g := F.chartMomentumFamily terminal Γ₁) w₀ h₁ hseed).fst
  have hp₂ := (HasFDerivAt.comp (f := fun w : W ↦ (w, r))
    (g := F.chartMomentumFamily terminal Γ₂) w₀ h₂ hseed).fst
  rw [← hp₂.fderiv] at hp₁ hp₂
  exact ⟨hp₁, hp₂⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
