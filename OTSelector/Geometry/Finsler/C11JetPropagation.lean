import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.C11EikonalSeed
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Jacobi.RoughJetFamily
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Transport.Kantorovich.CalibratedReach

/-!
# Geometry.Finsler.C11JetPropagation

* **Conditions:** An actual original C1,1 contact core with rough extension covector and its actual second jet almost everywhere.
* **Objects:** Rough/smooth normalized first jets propagated within one complete covector-indexed family at every legal time and for every parameter space.
* **Proof detail:** Construct the actual normalized representative, use one complete original family and apply the same-map within-set chain rule.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [OT-Selector project authors, Project manuscript main.tex (local provenance)](/data/lyuwt/OT-Selector-smooth-length/main.tex): Proof of proposition prop:rough-ray-quadratic, equation eq:rough-eikonal-jet at line 1228 and following normalized conormal construction.

Source relation (derived): This does not identify a separately constructed potential-level family; the parameter space may be the point-dependent covector kernel.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerC11JetPropagation.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerC11JetPropagation`; the selected original proof blocks follow. -/
section

/-!
# Actual C1,1 contact jets propagated through one complete original family

At almost every original contact point, the rough extension covector and a smooth
normalized representative have matching jets at all chart-legal times. Each comparison
uses one complete covector-indexed family. No identification with a separately
constructed potential-level family is asserted. The parameter space is quantified
inside the almost-everywhere conclusion, allowing the covector kernel at that point.
-/

open Set Filter Metric MeasureTheory MeasureTheory.Measure Manifold
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
universe u v w
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E : Type u} {M : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

section Parameter
variable {V : Type w} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Actual original-potential first derivatives and within-core second derivatives,
together with a smooth normalized representative transported alongside the rough
extension by one complete covector-indexed family. The parameter space V is arbitrary;
the original potential is not assigned an ambient Hessian off the contact core. -/
def HasC11PropagatedJetAt (F : ContinuousFinslerNorm E M) (m : Measure E)
    (old : M) (t₀ : ℝ) (u : M → ℝ) (G : E → ℝ) (K : Set E) (x : E) : Prop :=
  x ∈ K ∧
  Tendsto (fun r ↦ m (K ∩ closedBall x r) / m (closedBall x r))
    (𝓝[>] 0) (𝓝 1) ∧
  HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (fderiv ℝ G x) x ∧
  HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) x) x ∧
  HasFDerivWithinAt (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm))
    (fderiv ℝ (fderiv ℝ G) x) K x ∧
  ∃ e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ)),
    (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre (F.chartEnergy old) ∧
    e.source ⊆ chartEnergyDomain old ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
    (x, fderiv ℝ G x) ∈ e.target ∧
    localHamiltonian (F.chartEnergy old) e (x, fderiv ℝ G x) = (1 / 2 : ℝ) ∧
    ∃ P : E → ℝ, ContDiff ℝ ∞ P ∧
      P x = u ((extChartAt 𝓘(ℝ, E) old).symm x) ∧
      HasFDerivAt P (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) x) x ∧
      HasFDerivAt (fderiv ℝ P) (fderiv ℝ (fderiv ℝ G) x) x ∧
      fderiv ℝ P x = fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) x ∧
      fderiv ℝ (fderiv ℝ P) x = fderiv ℝ (fderiv ℝ G) x ∧
      HasFDerivAt (fun y ↦ localHamiltonian (F.chartEnergy old) e (y, fderiv ℝ P y))
        (0 : E →L[ℝ] ℝ) x ∧
      let n : E → E →L[ℝ] ℝ := fun y ↦
        (Real.sqrt (2 * localHamiltonian (F.chartEnergy old) e (y, fderiv ℝ P y)))⁻¹ •
          fderiv ℝ P y
      n x = fderiv ℝ G x ∧ HasFDerivAt n (fderiv ℝ (fderiv ℝ G) x) x ∧
      ContDiffAt ℝ ∞ n x ∧
      ∃ (U : Set (E × (E →L[ℝ] ℝ))) (Γ : (E × (E →L[ℝ] ℝ)) → ℝ → M),
        IsOpen U ∧ (x, fderiv ℝ G x) ∈ U ∧
        (∀ q ∈ U, F.IsEulerLagrangeOn (Γ q) univ) ∧
        (∀ q ∈ U, F.chartMomentumFamily old Γ (q, t₀) = q) ∧
        ∀ (σ : V → E) (offset₁ offset₂ : V → ℝ) (S : Set V) (z : V)
          (J : V →L[ℝ] E) (a : V →L[ℝ] ℝ),
          σ z = x → HasFDerivWithinAt σ J S z →
          HasFDerivWithinAt offset₁ a S z → HasFDerivWithinAt offset₂ a S z →
          offset₁ z = offset₂ z → ∀ (chart : M) (r : ℝ),
          Γ (σ z, fderiv ℝ G (σ z)) (r - offset₁ z) ∈
            (extChartAt 𝓘(ℝ, E) chart).source →
          ∃ D : V →L[ℝ] E × (E →L[ℝ] ℝ),
            F.chartMomentumFamily chart Γ ((σ z, fderiv ℝ G (σ z)), r - offset₁ z) =
              F.chartMomentumFamily chart Γ ((σ z, n (σ z)), r - offset₂ z) ∧
            HasFDerivWithinAt
              (fun y ↦ F.chartMomentumFamily chart Γ
                ((σ y, fderiv ℝ G (σ y)), r - offset₁ y)) D S z ∧
            HasFDerivWithinAt
              (fun y ↦ F.chartMomentumFamily chart Γ ((σ y, n (σ y)), r - offset₂ y)) D S z

end Parameter

namespace IsSmoothStronglyConvex
variable [T2Space M] [PreconnectedSpace M]

/-- The same full-measure set of actual contact points supports every normed parameter
space, including the point-dependent covector kernel. For each parameter space one
complete original family propagates both the rough and normalized smooth seed jets.
No branch, Hessian, density-one set, family or flow-jet identity is an input. -/
theorem ae_complete_jetPropagation_of_calibrated_C11_core (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M) (t₀ : ℝ)
    {m ν : Measure E} [IsAddHaarMeasure m] (hν : ν ≪ m)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    {u : M → ℝ} (hu : let _instC11JetPropagationLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (hinterior : let _instC11JetPropagationInterior : MetricSpace M := F.metricSpace
      MapsTo (extChartAt 𝓘(ℝ, E) old).symm K (OTSelector.Geometry.calibratedInterior u))
    {G : E → ℝ} {L : ℝ≥0} (hG : ContDiff ℝ 1 G)
    (hLip : LipschitzWith L (fderiv ℝ G))
    (hval : EqOn G (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) K)
    (hactual : ∀ x ∈ K,
      HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (fderiv ℝ G x) x) :
    ∀ᵐ x ∂ν.restrict K, ∀ (V : Type w)
      (_instC11PropagationNorm : NormedAddCommGroup V)
      (_instC11PropagationSpace : NormedSpace ℝ V),
      F.HasC11PropagatedJetAt (V := V) m old t₀ u G K x := by
  filter_upwards [hF.ae_complete_eikonal_seed_data_of_calibrated_C11_core
    hcomplete old hν hK hKt hu hinterior hG hLip hactual] with x hx
  obtain ⟨hxK, hdensity, hsecond, hwithin, e, O, he, hsub, heG, _, hxO,
    htarget, hdensityO, henergy⟩ := hx
  intro V _instC11PropagationNorm _instC11PropagationSpace
  have hfirst : ∀ᶠ y in 𝓝 x, HasFDerivAt G (fderiv ℝ G y) y :=
    Eventually.of_forall fun y ↦ (hG.differentiable one_ne_zero y).hasFDerivAt
  have hp := htarget x hxO
  obtain ⟨P, hP, hPx, hP₁, hP₂, hactual₁, hactual₂, hzero, hfamily⟩ :=
    hF.exists_complete_family_matching_rough_secondJet (V := V) m hcomplete old t₀
      he hsub heG hdensityO ⟨hxK, hxO⟩ hfirst hsecond hp henergy
  have hmatch : fderiv ℝ G x =
      fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) x := (hactual x hxK).fderiv.symm
  exact ⟨hxK, hdensity, hactual x hxK, hsecond, hwithin, e, he, hsub, heG, hp,
    henergy x ⟨hxK, hxO⟩, P, hP, hPx.trans (hval hxK), hP₁.congr_fderiv hmatch,
    hP₂, hactual₁.trans hmatch, hactual₂, hzero, hfamily⟩

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm

end
end
