import Mathlib.Analysis.ODE.ExistUnique
import OTSelector.Analysis.Calculus.EikonalDensityJet
import OTSelector.Analysis.Calculus.SmoothEikonalJet
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Hamiltonian.Basic

/-!
# Geometry.Finsler.EikonalJet

* **Conditions:** A genuine original Hamiltonian branch and an actual rough covector second jet satisfying value 1/2 on a density-one set.
* **Objects:** Zero first derivative of the actual Hamiltonian graph and a smooth polynomial/normalized covector with the same original rough first jet.
* **Proof detail:** Differentiate the actual branch Hamiltonian, use density-one constancy to force zero derivative and realize the symmetric jet by a smooth quadratic before normalization.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap47.pdf#page=22): Theorem 472D, pp. 22–23 (Besicovitch Density Theorem).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [OT-Selector project authors, Project manuscript main.tex (local provenance)](/data/lyuwt/OT-Selector-smooth-length/main.tex): Proof of proposition prop:rough-ray-quadratic, equation eq:rough-eikonal-jet at line 1228 and following normalized conormal construction.

Source relation (derived): Preserves the project rough-to-smooth eikonal construction and its actual branch, rather than attributing that auxiliary family verbatim to a book.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerEikonalJet.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerEikonalJet`; the selected original proof blocks follow. -/
section

/-!+# Smooth representatives of actual Finsler eikonal second jets

Use the original chart energy and the same genuine Legendre inverse throughout.
Its Hamiltonian differential follows from smooth strong convexity and the branch,
so the rough density-one energy identity needs no additional derivative oracle.
The smooth polynomial matches the actual rough second jet. Its energy graph has
zero derivative, and normalizing its differential preserves that first jet.
-/

open Set Filter Metric MeasureTheory MeasureTheory.Measure Manifold
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} (hF : F.IsSmoothStronglyConvex)

include hF

private theorem chartHamiltonian_hasFDerivAt (old : M)
    {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) =
      parametricLegendre (F.chartEnergy old))
    (hsub : e.source ⊆ chartEnergyDomain old)
    (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {p : E × (E →L[ℝ] ℝ)} (hp : p ∈ e.target) :
    HasFDerivAt (localHamiltonian (F.chartEnergy old) e)
      ((ContinuousLinearMap.snd ℝ E (E →L[ℝ] ℝ)).flip (e.symm p).2 -
        (baseEnergyDifferential (F.chartEnergy old) (e.symm p)).comp
          (ContinuousLinearMap.fst ℝ E (E →L[ℝ] ℝ))) p := by
  exact hasFDerivAt_localHamiltonian he hp
    ((((hF.contDiffOn_chartEnergy old).mono hsub).contDiffAt
      (e.open_source.mem_nhds (e.map_target hp))).differentiableAt (by simp))
    ((hG.contDiffAt (e.open_target.mem_nhds hp)).differentiableAt
      (by simp)).hasFDerivAt

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsAddHaarMeasure μ]

/-- The actual Finsler energy graph has zero differential at a genuine density-one
point. In every direction this gives the original identity `B(v)(velocity) = D_x E(v)`.
All Hamiltonian derivatives are derived from the original energy and its given branch. -/
theorem chartHamiltonian_energyGraph_hasFDerivAt_zero_of_density_one (old : M)
    {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) =
      parametricLegendre (F.chartEnergy old))
    (hsub : e.source ⊆ chartEnergyDomain old)
    (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {s : Set E} {x : E}
    (hx : Tendsto (fun r ↦ μ (s ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) (hxs : x ∈ s)
    {q : E → E →L[ℝ] ℝ} {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hq : HasFDerivAt q B x) (hp : (x, q x) ∈ e.target)
    (heq : ∀ y ∈ s, localHamiltonian (F.chartEnergy old) e (y, q y) = (1 / 2 : ℝ)) :
    HasFDerivAt (fun y ↦ localHamiltonian (F.chartEnergy old) e (y, q y))
        (0 : E →L[ℝ] ℝ) x ∧
      ∀ v : E, B v (e.symm (x, q x)).2 =
        baseEnergyDifferential (F.chartEnergy old) (e.symm (x, q x)) v := by
  have hK := hF.chartHamiltonian_hasFDerivAt old he hsub hG hp
  refine ⟨hasFDerivAt_energyGraph_zero_of_density_one μ hx hxs hK hq heq, ?_⟩
  intro v
  have hv := energyGraph_direction_eq_zero_of_density_one μ hx hxs hK hq heq v
  exact sub_eq_zero.mp hv

/-- The original Finsler Hamiltonian turns a rough actual second jet into a globally
smooth polynomial with the same value and derivatives. Its normalized differential
is smooth near the center and has the original covector first jet. The density-one
constraint is imposed only on the rough graph, never on the polynomial graph. -/
theorem exists_smooth_chartHamiltonian_normalized_secondJet (old : M)
    {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) =
      parametricLegendre (F.chartEnergy old))
    (hsub : e.source ⊆ chartEnergyDomain old)
    (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {s : Set E} {x : E}
    (hx : Tendsto (fun r ↦ μ (s ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) (hxs : x ∈ s)
    {f : E → ℝ} {f' : E → E →L[ℝ] ℝ} {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hfirst : ∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y)
    (hsecond : HasFDerivAt f' B x) (hp : (x, f' x) ∈ e.target)
    (heq : ∀ y ∈ s, localHamiltonian (F.chartEnergy old) e (y, f' y) = (1 / 2 : ℝ)) :
    ∃ P : E → ℝ, ContDiff ℝ ∞ P ∧ P x = f x ∧
      HasFDerivAt P (f' x) x ∧ HasFDerivAt (fderiv ℝ P) B x ∧
      fderiv ℝ P x = fderiv ℝ f x ∧
      fderiv ℝ (fderiv ℝ P) x = fderiv ℝ (fderiv ℝ f) x ∧
      HasFDerivAt (fun y ↦ localHamiltonian (F.chartEnergy old) e (y, fderiv ℝ P y))
        (0 : E →L[ℝ] ℝ) x ∧
      let n : E → E →L[ℝ] ℝ := fun y ↦
        (Real.sqrt (2 * localHamiltonian (F.chartEnergy old) e (y, fderiv ℝ P y)))⁻¹ •
          fderiv ℝ P y
      n x = f' x ∧ HasFDerivAt n B x ∧ ContDiffAt ℝ ∞ n x := by
  have hK := hF.chartHamiltonian_hasFDerivAt old he hsub hG hp
  obtain ⟨P, hP, hval, hD, hD₂, hactual₁, hactual₂, hzero, hnorm, hnD⟩ :=
    exists_smooth_normalized_secondJet_of_density_one μ hx hxs hfirst hsecond hK heq
  refine ⟨P, hP, hval, hD, hD₂, hactual₁, hactual₂, hzero, hnorm, hnD, ?_⟩
  have hDP : ContDiff ℝ ∞ (fderiv ℝ P) := hP.fderiv_right (by simp)
  have hKsmooth := contDiffOn_localHamiltonian
    ((hF.contDiffOn_chartEnergy old).mono hsub) hG
  have hpP : (x, fderiv ℝ P x) ∈ e.target := by rwa [hD.fderiv]
  have hgraph := (hKsmooth.contDiffAt (e.open_target.mem_nhds hpP)).comp x
    (contDiffAt_id.prodMk hDP.contDiffAt)
  have hc : 2 * localHamiltonian (F.chartEnergy old) e (x, fderiv ℝ P x) = 1 := by
    rw [hD.fderiv, heq x hxs]
    norm_num
  have hsqrt := ((contDiffAt_const (c := (2 : ℝ))).mul hgraph).sqrt
    (by change 2 * localHamiltonian (F.chartEnergy old) e (x, fderiv ℝ P x) ≠ 0
        rw [hc]
        exact one_ne_zero)
  have hroot : Real.sqrt
      (2 * localHamiltonian (F.chartEnergy old) e (x, fderiv ℝ P x)) = 1 := by
    rw [hc, Real.sqrt_one]
  exact (hsqrt.inv (by
    change Real.sqrt (2 * localHamiltonian (F.chartEnergy old) e (x, fderiv ℝ P x)) ≠ 0
    rw [hroot]
    exact one_ne_zero)).smul hDP.contDiffAt

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
