import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.CompleteTangentSmooth
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.FlowLocalC2
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Energy
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.TangentReadout
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerParameterizedFlow.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerParameterizedFlow`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.ParameterizedFlow

* **Conditions:** A complete smooth strongly convex Finsler metric and a supplied smooth chart seed contained in the actual slit domain.
* **Objects:** One all-slit complete smooth family, and its actual seed composite with smooth tangent/position, exact initial momentum and conserved energy.
* **Proof detail:** Upgrade the identity-seeded complete family to joint smoothness by local ODE dependence, then compose that same family with the supplied seed.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=61): Section 2.6, pp. 50–51, overlap uniqueness, equation (2.63), and Theorem 2.13 (unique maximal solution).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.

Source relation (derived): A derived specialization of the cited differential/ODE principles to the exact Finsler data; constructed branches, phase maps and parameter derivatives belong to the same family throughout.
-/

/-!
# One complete smooth family for actual chart seeds

One all-slit complete family is upgraded to joint smoothness using the identity seed.
Composing this same family with the supplied seed gives its actual smooth tangent and
position, initial Legendre momentum, and conserved original Finsler energy.
-/

open Set Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- One complete all-slit family remains jointly smooth after composition with the
supplied smooth chart seed, with its actual initial momentum and conserved energy. -/
theorem exists_complete_smooth_family_of_chartSeed
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (old : M) (t₀ : ℝ) {U : Set W} (hU : IsOpen U)
    {ι : W → E × E} (hι : ContDiffOn ℝ ∞ ι U)
    (hιDomain : MapsTo ι U (chartEnergyDomain old)) :
    ∃ Φ : (E × E) → ℝ → M,
      (∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Φ z) univ) ∧
      (∀ z ∈ chartEnergyDomain old,
        tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Φ z) ⟨t₀, (1 : ℝ)⟩ =
          (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
            (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z) ∧
      ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
        (fun z ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Φ z.1) ⟨z.2, (1 : ℝ)⟩)
        (chartEnergyDomain old ×ˢ univ) ∧
      let Γ : W → ℝ → M := fun w ↦ Φ (ι w)
      ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
        (fun z ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ z.1) ⟨z.2, (1 : ℝ)⟩)
        (U ×ˢ univ) ∧
      ContMDiffOn 𝓘(ℝ, W × ℝ) 𝓘(ℝ, E) ∞
        (fun z ↦ Γ z.1 z.2) (U ×ˢ univ) ∧
      ∀ w ∈ U,
        Γ w t₀ = (extChartAt 𝓘(ℝ, E) old).symm (ι w).1 ∧
        F.chartMomentumFamily old Γ (w, t₀) =
          parametricLegendre (F.chartEnergy old) (ι w) ∧
        ∀ t : ℝ,
          F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t, (1 : ℝ)⟩) =
            F.chartEnergy old (ι w) := by
  obtain ⟨Φ, hEL, hinit, _⟩ := hF.exists_complete_tangentFamily_C2 hcomplete old t₀
  have hΦSmooth := (hF.contMDiffOn_tangentFamily_of_chartSeed_smooth old
    (isOpen_chartEnergyDomain old) hEL (ι := id) contDiffOn_id
    (fun _ hz ↦ hz) hinit).1
  let Γ : W → ℝ → M := fun w ↦ Φ (ι w)
  have hΓ (w : W) (hw : w ∈ U) : F.IsEulerLagrangeOn (Γ w) univ :=
    hEL (ι w) (hιDomain hw)
  have hΓinit (w : W) (hw : w ∈ U) :
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t₀, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm (ι w) :=
    hinit (ι w) (hιDomain hw)
  have hS : ContDiffOn ℝ ∞ (fun z : W × ℝ ↦ (ι z.1, z.2)) (U ×ˢ univ) := by
    apply (hU.prod isOpen_univ).contDiffOn_iff.mpr
    intro z hz
    exact ((hι.contDiffAt (hU.mem_nhds hz.1)).comp z contDiffAt_fst).prodMk contDiffAt_snd
  have hΓSmooth := hΦSmooth.comp hS.contMDiffOn
    (fun z hz ↦ ⟨hιDomain hz.1, mem_univ _⟩)
  refine ⟨Φ, hEL, hinit, hΦSmooth, hΓSmooth, ?_, ?_⟩
  · intro z hz
    exact (Bundle.contMDiffWithinAt_totalSpace.mp (hΓSmooth z hz)).1
  · intro w hw
    have hb := congrArg (fun q : TangentBundle 𝓘(ℝ, E) M ↦ q.1) (hΓinit w hw)
    rw [tangentChart_symm_eq old (hιDomain hw).1 (ι w).2] at hb
    refine ⟨hb, ?_, ?_⟩
    · exact hF.chartMomentum_of_tangent_eq (hΓ w hw t₀ (mem_univ _)) old
        (hιDomain hw) (hΓinit w hw)
    · intro t
      calc
        F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t, (1 : ℝ)⟩) =
            F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t₀, (1 : ℝ)⟩) := by
          unfold ContinuousFinslerNorm.energy
          rw [hF.speed_eq_of_isEulerLagrangeOn (hΓ w hw) isPreconnected_univ
            (mem_univ t) (mem_univ t₀)]
        _ = F.chartEnergy old (ι w) := congrArg F.energy (hΓinit w hw)

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
