import LeanPool.Vlasov.OT.Coupling
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.StrongLaw
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import OTSelector.Analysis.Calculus.FlowJetMatching
import OTSelector.Analysis.Calculus.MixedFlowJetMatching
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerParameterizedFlowJet.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerParameterizedFlowJet`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.ParameterizedFlowJet

* **Conditions:** A supplied all-slit smooth complete family, one supplied inverse branch and matched ordinary/within-set seed and clock first jets at the point.
* **Objects:** Equal actual chart-momentum values and equal mixed ordinary/within-set composite derivatives for those same data.
* **Proof detail:** Apply the chain rule to the actual smooth position–momentum evaluation map, retaining matched phase seeds and clock corrections on the original core.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=38): Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).

Source relation (derived): Foundation-only exact split: only the two generic supplied-family first-jet helpers are covered. The normalized-polynomial calibrated-core paper adapter is excluded.
-/

/-!
# Mixed first jets in the supplied complete smooth family

Matched phase seeds are passed through the same supplied inverse Legendre branch
and the same supplied all-slit family. The normal composite retains its ordinary
derivative; the original composite has that derivative within the original core.
The generic helpers take seed and clock first jets as inputs. The calibrated-core
consumer derives the seed jets from the selected normalized polynomial and uses
constant clocks. None of these results selects a second family or proves a uniform
distance remainder.
-/

open Set Filter Metric MeasureTheory MeasureTheory.Measure Manifold Bundle
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

/-- Mixed seed jets propagate through the retained inverse and the supplied smooth
all-slit flow to the actual ambient derivative of the normal position/momentum
readout. Only the central point needs to lie in the legal output chart. -/
theorem chartMomentum_supplied_family_same_firstJet_mixed
    (hF : F.IsSmoothStronglyConvex) (initial : M)
    {Φ : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain initial, F.IsEulerLagrangeOn (Φ z) univ)
    (hΦ : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Φ z.1) ⟨z.2, (1 : ℝ)⟩)
      (chartEnergyDomain initial ×ˢ univ))
    {eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (hsource : eL.source ⊆ chartEnergyDomain initial)
    (hInv : ContDiffOn ℝ ∞ eL.symm eL.target)
    {X Y : W → E × (E →L[ℝ] ℝ)} {f g : W → ℝ} {s : Set W} {w : W}
    {D : W →L[ℝ] E × (E →L[ℝ] ℝ)} {a : W →L[ℝ] ℝ}
    (hX : HasFDerivWithinAt X D s w) (hY : HasFDerivAt Y D w)
    (hf : HasFDerivWithinAt f a s w) (hg : HasFDerivAt g a w)
    (hseed : X w = Y w) (hclock : f w = g w) (hYt : Y w ∈ eL.target)
    (out : M) (r : ℝ)
    (hlegal : Φ (eL.symm (Y w)) (r - g w) ∈ (extChartAt 𝓘(ℝ, E) out).source) :
    let Ψ := fun (q : (E × (E →L[ℝ] ℝ)) × ℝ) ↦
      F.chartMomentumFamily out Φ (eL.symm q.1, q.2)
    Ψ (X w, r - f w) = Ψ (Y w, r - g w) ∧
      HasFDerivAt (fun y ↦ Ψ (Y y, r - g y))
        (fderiv ℝ (fun y ↦ Ψ (Y y, r - g y)) w) w ∧
      HasFDerivWithinAt (fun y ↦ Ψ (X y, r - f y))
        (fderiv ℝ (fun y ↦ Ψ (Y y, r - g y)) w) s w := by
  have hread := hF.contDiffAt_chartMomentumFamily_of_tangentFamily
    (isOpen_chartEnergyDomain initial) hEL
    (hΦ.of_le (by simp : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω)))
    (hsource (eL.map_target hYt)) out (r - g w) hlegal
  have hinv : DifferentiableAt ℝ eL.symm (Y w) :=
    (hInv.contDiffAt (eL.open_target.mem_nhds hYt)).differentiableAt (by simp)
  have hpair : DifferentiableAt ℝ
      (fun q : (E × (E →L[ℝ] ℝ)) × ℝ ↦ (eL.symm q.1, q.2)) (Y w, r - g w) :=
    (hinv.comp (Y w, r - g w) differentiableAt_fst).prodMk differentiableAt_snd
  exact flow_comp_sub_clock_same_firstJet_mixed r hX hY hf hg hseed hclock
    ((hread.differentiableAt (by norm_num)).comp (Y w, r - g w) hpair)

/-- When the normal phase seed is the Legendre image of the selected chart seed,
the normal derivative is literally that of the supplied family at that chart seed.
Local source membership is enough; no different complete family is constructed. -/
theorem chartSeed_supplied_family_same_firstJet_mixed
    (hF : F.IsSmoothStronglyConvex) (initial : M)
    {Φ : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain initial, F.IsEulerLagrangeOn (Φ z) univ)
    (hΦ : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Φ z.1) ⟨z.2, (1 : ℝ)⟩)
      (chartEnergyDomain initial ×ˢ univ))
    {eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (heL : (eL : E × E → E × (E →L[ℝ] ℝ)) =
      parametricLegendre (F.chartEnergy initial))
    (hsource : eL.source ⊆ chartEnergyDomain initial)
    (hInv : ContDiffOn ℝ ∞ eL.symm eL.target)
    {X : W → E × (E →L[ℝ] ℝ)} {ι : W → E × E}
    {f g : W → ℝ} {s : Set W} {w : W}
    {D : W →L[ℝ] E × (E →L[ℝ] ℝ)} {a : W →L[ℝ] ℝ}
    (hX : HasFDerivWithinAt X D s w)
    (hY : HasFDerivAt (fun y ↦ parametricLegendre (F.chartEnergy initial) (ι y)) D w)
    (hf : HasFDerivWithinAt f a s w) (hg : HasFDerivAt g a w)
    (hseed : X w = parametricLegendre (F.chartEnergy initial) (ι w))
    (hclock : f w = g w) (hι : ∀ᶠ y in 𝓝 w, ι y ∈ eL.source)
    (out : M) (r : ℝ)
    (hlegal : Φ (ι w) (r - g w) ∈ (extChartAt 𝓘(ℝ, E) out).source) :
    F.chartMomentumFamily out Φ (eL.symm (X w), r - f w) =
      F.chartMomentumFamily out Φ (ι w, r - g w) ∧
      HasFDerivAt (fun y ↦ F.chartMomentumFamily out Φ (ι y, r - g y))
        (fderiv ℝ (fun y ↦ F.chartMomentumFamily out Φ (ι y, r - g y)) w) w ∧
      HasFDerivWithinAt
        (fun y ↦ F.chartMomentumFamily out Φ (eL.symm (X y), r - f y))
        (fderiv ℝ (fun y ↦ F.chartMomentumFamily out Φ (ι y, r - g y)) w) s w := by
  have hinverse : ∀ᶠ y in 𝓝 w,
      eL.symm (parametricLegendre (F.chartEnergy initial) (ι y)) = ι y := by
    filter_upwards [hι] with y hy
    simpa only [heL] using eL.left_inv hy
  have ht : parametricLegendre (F.chartEnergy initial) (ι w) ∈ eL.target := by
    simpa only [heL] using eL.map_source hι.self_of_nhds
  have hlegal' : Φ (eL.symm (parametricLegendre (F.chartEnergy initial) (ι w)))
      (r - g w) ∈ (extChartAt 𝓘(ℝ, E) out).source := by
    rwa [hinverse.self_of_nhds]
  obtain ⟨heq, hn, hr⟩ := hF.chartMomentum_supplied_family_same_firstJet_mixed
    initial hEL hΦ hsource hInv hX hY hf hg hseed hclock ht out r hlegal'
  have hevent : (fun y ↦ F.chartMomentumFamily out Φ
      (eL.symm (parametricLegendre (F.chartEnergy initial) (ι y)), r - g y)) =ᶠ[𝓝 w]
      (fun y ↦ F.chartMomentumFamily out Φ (ι y, r - g y)) := by
    filter_upwards [hinverse] with y hy
    rw [hy]
  change F.chartMomentumFamily out Φ (eL.symm (X w), r - f w) =
    F.chartMomentumFamily out Φ
      (eL.symm (parametricLegendre (F.chartEnergy initial) (ι w)), r - g w) at heq
  rw [hinverse.self_of_nhds] at heq
  have hnormal := hn.congr_of_eventuallyEq hevent.symm
  rw [hevent.fderiv_eq] at hnormal hr
  exact ⟨heq, hnormal, hr⟩



end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
