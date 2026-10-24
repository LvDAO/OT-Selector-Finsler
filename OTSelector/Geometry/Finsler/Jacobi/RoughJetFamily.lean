import OTSelector.Analysis.Calculus.FlowJetMatching
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.EikonalJet
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.LengthMetric
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerRoughJetFamily.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerRoughJetFamily`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Jacobi.RoughJetFamily

* **Conditions:** A genuine Legendre branch, complete Finsler geometry and an actual rough second jet satisfying the eikonal value 1/2 on a density-one core.
* **Objects:** One smooth matching polynomial and normalized covector, then a single complete phase-indexed family through which both rough and smooth seeds have the same within-core first jet.
* **Proof detail:** Use density-one differentiation to normalize the matching polynomial without changing its first covector jet; feed both seeds into the same supplied-branch family and apply the composite chain rule.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap47.pdf#page=22): Theorem 472D, pp. 22–23 (Besicovitch Density Theorem).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [OT-Selector project authors, Project manuscript main.tex (local provenance)](/data/lyuwt/OT-Selector-smooth-length/main.tex): Proof of proposition prop:rough-ray-quadratic, equation eq:rough-eikonal-jet at line 1228 and following normalized conormal construction.

Source relation (derived): This proves same-family rough/smooth jet transfer with the exact core and clock corrections. It does not compare independently chosen complete families.
-/

/-!
# Propagating a rough Finsler eikonal jet by one complete original family

The original Legendre branch defines the Hamiltonian used to normalize the smooth
polynomial differential. Original completeness then constructs one family indexed
by actual position and covector. Its parameter domain contains the same central phase,
as follows from the original branch inverse identity. Both the rough seed and its
smooth normalized replacement enter this one family. No equality between independently
chosen Legendre branches or between two separately constructed families is used.
-/

open Set Filter Metric MeasureTheory MeasureTheory.Measure Manifold
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false

variable {V E M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M} (hF : F.IsSmoothStronglyConvex)
  (μ : Measure E) [IsAddHaarMeasure μ]

include hF

/-- An actual rough eikonal second jet produces a smooth representative and one complete
original family transporting both seed jets identically. Initial parameterizations and
clocks need only have matching derivatives within the allowed set. The propagated
position and original energy momentum agree to first order at every chart-legal time. -/
theorem exists_complete_family_matching_rough_secondJet
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (initial : M) (t₀ : ℝ)
    {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) =
      parametricLegendre (F.chartEnergy initial))
    (hsub : e.source ⊆ chartEnergyDomain initial)
    (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {s : Set E} {x : E}
    (hx : Tendsto (fun r ↦ μ (s ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) (hxs : x ∈ s)
    {f : E → ℝ} {f' : E → E →L[ℝ] ℝ} {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hfirst : ∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y)
    (hsecond : HasFDerivAt f' B x) (hp : (x, f' x) ∈ e.target)
    (heq : ∀ y ∈ s,
      localHamiltonian (F.chartEnergy initial) e (y, f' y) = (1 / 2 : ℝ)) :
    ∃ P : E → ℝ, ContDiff ℝ ∞ P ∧ P x = f x ∧
      HasFDerivAt P (f' x) x ∧ HasFDerivAt (fderiv ℝ P) B x ∧
      fderiv ℝ P x = fderiv ℝ f x ∧
      fderiv ℝ (fderiv ℝ P) x = fderiv ℝ (fderiv ℝ f) x ∧
      HasFDerivAt (fun y ↦ localHamiltonian (F.chartEnergy initial) e (y, fderiv ℝ P y))
        (0 : E →L[ℝ] ℝ) x ∧
      let n : E → E →L[ℝ] ℝ := fun y ↦
        (Real.sqrt (2 * localHamiltonian (F.chartEnergy initial) e (y, fderiv ℝ P y)))⁻¹ •
          fderiv ℝ P y
      n x = f' x ∧ HasFDerivAt n B x ∧ ContDiffAt ℝ ∞ n x ∧
      ∃ (U : Set (E × (E →L[ℝ] ℝ))) (Γ : (E × (E →L[ℝ] ℝ)) → ℝ → M),
        IsOpen U ∧ (x, f' x) ∈ U ∧
        (∀ q ∈ U, F.IsEulerLagrangeOn (Γ q) univ) ∧
        (∀ q ∈ U, F.chartMomentumFamily initial Γ (q, t₀) = q) ∧
        ∀ (σ : V → E) (offset₁ offset₂ : V → ℝ) (S : Set V) (w : V)
          (J : V →L[ℝ] E) (a : V →L[ℝ] ℝ),
          σ w = x → HasFDerivWithinAt σ J S w →
          HasFDerivWithinAt offset₁ a S w → HasFDerivWithinAt offset₂ a S w →
          offset₁ w = offset₂ w → ∀ (old : M) (r : ℝ),
          Γ (σ w, f' (σ w)) (r - offset₁ w) ∈ (extChartAt 𝓘(ℝ, E) old).source →
          ∃ L : V →L[ℝ] E × (E →L[ℝ] ℝ),
            F.chartMomentumFamily old Γ ((σ w, f' (σ w)), r - offset₁ w) =
              F.chartMomentumFamily old Γ ((σ w, n (σ w)), r - offset₂ w) ∧
            HasFDerivWithinAt
              (fun v ↦ F.chartMomentumFamily old Γ ((σ v, f' (σ v)), r - offset₁ v))
              L S w ∧
            HasFDerivWithinAt
              (fun v ↦ F.chartMomentumFamily old Γ ((σ v, n (σ v)), r - offset₂ v))
              L S w := by
  obtain ⟨P, hP, hval, hD, hD₂, hactual₁, hactual₂, hzero, hnval, hnD, hnSmooth⟩ :=
    hF.exists_smooth_chartHamiltonian_normalized_secondJet μ initial he hsub hG
      hx hxs hfirst hsecond hp heq
  let n : E → E →L[ℝ] ℝ := fun y ↦
    (Real.sqrt (2 * localHamiltonian (F.chartEnergy initial) e (y, fderiv ℝ P y)))⁻¹ •
      fderiv ℝ P y
  change n x = f' x at hnval
  change HasFDerivAt n B x at hnD
  have hz : e.symm (x, f' x) ∈ chartEnergyDomain initial := hsub (e.map_target hp)
  have hphase : parametricLegendre (F.chartEnergy initial) (e.symm (x, f' x)) =
      (x, f' x) := by
    rw [← he]
    exact e.right_inv hp
  obtain ⟨U, Γ, hU, hpU, hEL, hinit, hmatch⟩ :=
    hF.exists_complete_covectorFamily_matching_firstJets (V := V) hcomplete initial hz t₀
  rw [hphase] at hpU
  refine ⟨P, hP, hval, hD, hD₂, hactual₁, hactual₂, hzero, hnval, hnD, hnSmooth,
    U, Γ, hU, hpU, hEL, hinit, ?_⟩
  intro σ offset₁ offset₂ S w J a hσ₀ hσ hoff₁ hoff₂ hoff old r hlegal
  have hq : HasFDerivAt f' B (σ w) := by rw [hσ₀]; exact hsecond
  have hn : HasFDerivAt n B (σ w) := by rw [hσ₀]; exact hnD
  have hX := hσ.prodMk (hq.comp_hasFDerivWithinAt w hσ)
  have hY := hσ.prodMk (hn.comp_hasFDerivWithinAt w hσ)
  exact hmatch (fun v ↦ (σ v, f' (σ v))) (fun v ↦ (σ v, n (σ v)))
    offset₁ offset₂ S w (J.prod (B.comp J)) a hX hY hoff₁ hoff₂
    (by rw [hσ₀, hnval]) hoff (by simpa only [hσ₀] using hpU) old r hlegal

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
