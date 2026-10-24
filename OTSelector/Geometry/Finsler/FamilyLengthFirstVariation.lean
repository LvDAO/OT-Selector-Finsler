import OTSelector.Analysis.Calculus.VariationDerivatives
import OTSelector.Analysis.CompactParameterIntegral
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Proofs.MaximalExtension
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.LengthFirstVariation
import OTSelector.Geometry.Finsler.Variation.Lagrangian
import OTSelector.Geometry.Manifold.TangentChartCurve
import OTSelector.Geometry.Manifold.TangentFamilyPosition

/-!
# Geometry.Finsler.FamilyLengthFirstVariation

* **Conditions:** A jointly regular actual intrinsic family whose central compact segment lies in a legal chart, satisfying original energy dynamics.
* **Objects:** The scalar path-length endpoint first-variation formula with true endpoint fields from the same family.
* **Proof detail:** Construct a common chart reconstruction strip by compactness, derive coordinate energy equations intrinsically and apply original length first variation.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249): Section 8.3, pp. 238–240, equations (8.33)–(8.47): first variation, Euler–Lagrange, Legendre transformation, Hamilton equations and energy conservation.
- [D. H. Fremlin, Measure Theory, Volume 2, Chapter 22](https://www1.essex.ac.uk/maths/people/fremlin/chap22.pdf#page=29): Section 225E, p. 29 (absolute continuity and indefinite integral); Section 225F, p. 30 (integration by parts).
- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).

Source relation (derived): No independent reconstructed family or coordinate equation is supplied; path length is not silently identified with global distance.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerFamilyLengthFirstVariation.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerFamilyLengthFirstVariation`; the selected original proof blocks follow. -/
section

/-!
# Length first variation of actual manifold families

The original jointly regular manifold family supplies its chart variation on the open
legal chart domain. Compactness gives a parameter strip on which chart reconstruction
is exactly the original family throughout the time segment. Intrinsic energy dynamics
supply the true coordinate energy equation, and hence the original-length endpoint formula.

No reconstructed family, coordinate equation, constant speed, or path-length identification
is an input. All lengths use the original Finsler norm. The formula concerns those paths;
it does not identify their lengths with global endpoint distance.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- An actual manifold parameter tangent is read by the ordinary derivative of its
actual chart coordinates, with no supplied tangent identification. -/
theorem tangentMap_eq_chartParameter_fderiv (old : M) {c : ℝ → M} {s₀ : ℝ}
    (hc : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 c s₀)
    (hsrc : c s₀ ∈ (extChartAt 𝓘(ℝ, E) old).source) :
    tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨s₀, (1 : ℝ)⟩ =
      (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
        (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm
        (extChartAt 𝓘(ℝ, E) old (c s₀),
          fderiv ℝ (extChartAt 𝓘(ℝ, E) old ∘ c) s₀ 1) := by
  have hchart : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 1
      (extChartAt 𝓘(ℝ, E) old) (c s₀) :=
    contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hsrc)
  have hx := ((hchart.comp s₀ hc).contDiffAt).differentiableAt one_ne_zero
  have heq : c =ᶠ[𝓝 s₀] (extChartAt 𝓘(ℝ, E) old).symm ∘
      (extChartAt 𝓘(ℝ, E) old ∘ c) := by
    filter_upwards [hc.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source old).mem_nhds hsrc)] with s hs
    exact ((extChartAt 𝓘(ℝ, E) old).left_inv hs).symm
  rw [tangentCurve_eq_of_eventuallyEq heq, fderiv_apply_one_eq_deriv]
  exact tangentMap_chart_symm_curve old ((extChartAt 𝓘(ℝ, E) old).map_source hsrc)
    hx.hasDerivAt

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable [FiniteDimensional ℝ E] {F : ContinuousFinslerNorm E M}

/-- Original path-length first variation from a jointly C2 position family and the
central intrinsic energy equation. The legal chart variation is constructed internally. -/
theorem hasDerivAt_family_pathELength_endpoint_from_position
    (hF : F.IsSmoothStronglyConvex) (old : M) {Γ : ℝ → ℝ → M}
    {B I : Set ℝ} (hB : IsOpen B) (hI : IsOpen I) (hconn : IsPreconnected I)
    (hΓ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) 2
      (fun q ↦ Γ q.1 q.2) (B ×ˢ I)) {s₀ a b : ℝ} (hs₀ : s₀ ∈ B)
    (hab : a ≤ b) (hsegment : Icc a b ⊆ I)
    (hEL : F.IsEulerLagrangeOn (Γ s₀) I)
    (hmap : MapsTo (Γ s₀) I (extChartAt 𝓘(ℝ, E) old).source) :
    letI : ∀ y : M, ENorm (TangentSpace 𝓘(ℝ, E) y) := F.enorm
    let σ : ℝ × ℝ → E := fun q ↦ extChartAt 𝓘(ℝ, E) old (Γ q.1 q.2)
    HasDerivAt (fun s ↦ (Manifold.pathELength 𝓘(ℝ, E) (Γ s) a b).toReal)
      (fiberLegendre (fun z ↦ (F.chartLength old z : ℝ)) (variationPhase σ (s₀, b))
          (fderiv ℝ (fun s ↦ σ (s, b)) s₀ 1) -
        fiberLegendre (fun z ↦ (F.chartLength old z : ℝ)) (variationPhase σ (s₀, a))
          (fderiv ℝ (fun s ↦ σ (s, a)) s₀ 1)) s₀ := by
  let : ∀ y : M, ENorm (TangentSpace 𝓘(ℝ, E) y) := F.enorm
  let σ : ℝ × ℝ → E := fun q ↦ extChartAt 𝓘(ℝ, E) old (Γ q.1 q.2)
  let D := (B ×ˢ I) ∩ (fun q : ℝ × ℝ ↦ Γ q.1 q.2) ⁻¹'
    (extChartAt 𝓘(ℝ, E) old).source
  have hD : IsOpen D := hΓ.continuousOn.isOpen_inter_preimage (hB.prod hI)
    (isOpen_extChartAt_source old)
  have hσ : ContDiffOn ℝ 2 σ D := by
    apply ContMDiffOn.contDiffOn
    exact contMDiffOn_extChartAt.comp (hΓ.mono inter_subset_left) (fun q hq ↦ by
      simpa only [extChartAt_source] using hq.2)
  have htrace (t : ℝ) (ht : t ∈ I) : (s₀, t) ∈ D := ⟨⟨hs₀, ht⟩, hmap ht⟩
  obtain ⟨_, hphase, hcoordEL⟩ := hF.chartEulerLagrange_of_isEulerLagrangeOn hEL old hmap
  have h := hF.hasDerivAt_pathELength_endpoint_of_chartEnergy old hD hσ hab hI hconn
    hsegment htrace hphase hcoordEL
  obtain ⟨r, hr, hstrip⟩ := exists_pos_compact_parameter_strip hD
    (fun t ht ↦ htrace t (hsegment ht))
  have hpaths : (fun s ↦ (Manifold.pathELength 𝓘(ℝ, E) (Γ s) a b).toReal) =ᶠ[𝓝 s₀]
      (fun s ↦ (Manifold.pathELength 𝓘(ℝ, E)
        ((extChartAt 𝓘(ℝ, E) old).symm ∘ (fun t ↦ σ (s, t))) a b).toReal) := by
    filter_upwards [Icc_mem_nhds (show s₀ - r < s₀ by linarith)
      (show s₀ < s₀ + r by linarith)] with s hs
    apply congrArg ENNReal.toReal
    apply Manifold.pathELength_congr
    intro t ht
    have hsrc : Γ s t ∈ (extChartAt 𝓘(ℝ, E) old).source :=
      (hstrip (show (s, t) ∈ Icc (s₀ - r) (s₀ + r) ×ˢ Icc a b from ⟨hs, ht⟩)).2
    exact ((extChartAt 𝓘(ℝ, E) old).left_inv hsrc).symm
  simpa only [variationField, fderiv_apply_one_eq_deriv] using
    h.congr_of_eventuallyEq hpaths

/-- Joint C2 regularity of the original total tangent family automatically supplies
all position regularity needed for the actual path-length endpoint formula. -/
theorem hasDerivAt_family_pathELength_endpoint
    (hF : F.IsSmoothStronglyConvex) (old : M) {Γ : ℝ → ℝ → M}
    {B I : Set ℝ} (hB : IsOpen B) (hI : IsOpen I) (hconn : IsPreconnected I)
    (hG : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ I))
    {s₀ a b : ℝ} (hs₀ : s₀ ∈ B) (hab : a ≤ b) (hsegment : Icc a b ⊆ I)
    (hEL : F.IsEulerLagrangeOn (Γ s₀) I)
    (hmap : MapsTo (Γ s₀) I (extChartAt 𝓘(ℝ, E) old).source) :
    letI : ∀ y : M, ENorm (TangentSpace 𝓘(ℝ, E) y) := F.enorm
    let σ : ℝ × ℝ → E := fun q ↦ extChartAt 𝓘(ℝ, E) old (Γ q.1 q.2)
    HasDerivAt (fun s ↦ (Manifold.pathELength 𝓘(ℝ, E) (Γ s) a b).toReal)
      (fiberLegendre (fun z ↦ (F.chartLength old z : ℝ)) (variationPhase σ (s₀, b))
          (fderiv ℝ (fun s ↦ σ (s, b)) s₀ 1) -
        fiberLegendre (fun z ↦ (F.chartLength old z : ℝ)) (variationPhase σ (s₀, a))
          (fderiv ℝ (fun s ↦ σ (s, a)) s₀ 1)) s₀ :=
  hF.hasDerivAt_family_pathELength_endpoint_from_position old hB hI hconn
    (contMDiffOn_positionFamily_of_tangentFamily hG) hs₀ hab hsegment hEL hmap

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
end
