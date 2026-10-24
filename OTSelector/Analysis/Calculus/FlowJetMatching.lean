import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.FlowLocalC2
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.TangentReadout
import OTSelector.Geometry.Manifold.TangentFamilyPosition
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerFlowJetMatching.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerFlowJetMatching`; the selected original proof blocks follow. -/
section

/-!
Conditions: Actual differentiable seeds and clocks, or the specified C2 complete Finsler flow and actual momentum readout.

Objects: Chain rules and propagation of matching first phase jets, and the resulting complete covector family.

Proof detail: Differentiate seed/clock compositions, substitute equal initial jets and read actual momentum from the same tangent flow.

Sources: Gerald Teschl, Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10 (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56); Jiří Lebl, Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity) (https://www.jirka.org/ra/realanal2.pdf#page=38); Matias Dahl, Section 1.2, Definition 1.8, Propositions 1.9–1.10, pp. 6–8; equations (3)–(8) (https://math.aalto.fi/~fdahl/finsler/finsler.pdf#page=6).
Relation: Flow-chain-rule adapter. Completeness and actual flow hypotheses are used only where present.
-/

/-!
# Matching first jets propagated by the same original Finsler flow

The complete original family is jointly C2 in its actual tangent. Reading its position
and energy momentum in any chart therefore transports equal seed first jets to equal
first jets at every legal time. Parameter-dependent clocks may differ away from the
center but need only agree to first order there. Within-set derivatives suffice.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {V W Z : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- A differentiable flow readout preserves matching seed and clock first jets on an
arbitrary allowed parameter set. The shared derivative is the actual chain-rule map. -/
theorem flow_comp_sub_clock_same_firstJet_within {Φ : W × ℝ → Z}
    {X Y : V → W} {f g : V → ℝ} {s : Set V} {x : V}
    {D : V →L[ℝ] W} {a : V →L[ℝ] ℝ} (r : ℝ)
    (hX : HasFDerivWithinAt X D s x) (hY : HasFDerivWithinAt Y D s x)
    (hf : HasFDerivWithinAt f a s x) (hg : HasFDerivWithinAt g a s x)
    (hseed : X x = Y x) (hclock : f x = g x)
    (hΦ : DifferentiableAt ℝ Φ (X x, r - f x)) :
    let L := (fderiv ℝ Φ (X x, r - f x)).comp (D.prod (-a))
    Φ (X x, r - f x) = Φ (Y x, r - g x) ∧
      HasFDerivWithinAt (fun y ↦ Φ (X y, r - f y)) L s x ∧
      HasFDerivWithinAt (fun y ↦ Φ (Y y, r - g y)) L s x := by
  refine ⟨by rw [hseed, hclock], ?_, ?_⟩
  · exact hΦ.hasFDerivAt.comp_hasFDerivWithinAt x (hX.prodMk (hf.const_sub r))
  · have hΦ' : HasFDerivAt Φ (fderiv ℝ Φ (X x, r - f x)) (Y x, r - g x) := by
      rw [← hseed, ← hclock]
      exact hΦ.hasFDerivAt
    exact hΦ'.comp_hasFDerivWithinAt x (hY.prodMk (hg.const_sub r))

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {F : ContinuousFinslerNorm E M}

/-- The actual position and energy momentum are jointly C2 at every chart-legal point
of the complete family. A legal neighborhood follows from original position continuity. -/
theorem contDiffAt_chartMomentumFamily_of_tangentFamily (hF : F.IsSmoothStronglyConvex)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    {w : W} (hw : w ∈ B) (old : M) (t : ℝ)
    (hx : Γ w t ∈ (extChartAt 𝓘(ℝ, E) old).source) :
    ContDiffAt ℝ 2 (F.chartMomentumFamily old Γ) (w, t) := by
  let D := (B ×ˢ univ) ∩ (fun q : W × ℝ ↦ Γ q.1 q.2) ⁻¹'
    (extChartAt 𝓘(ℝ, E) old).source
  have hc := (contMDiffOn_positionFamily_of_tangentFamily hG).continuousOn
  have hD : IsOpen D := hc.isOpen_inter_preimage (hB.prod isOpen_univ)
    (isOpen_extChartAt_source old)
  have hC2 := hF.contDiffOn_chartMomentumFamily old
    (fun q hq ↦ hEL q.1 hq.1.1 q.2 (mem_univ _))
    (hG.mono (show D ⊆ B ×ˢ univ from inter_subset_left)) (fun _ hq ↦ hq.2)
  exact hC2.contDiffAt (hD.mem_nhds ⟨⟨hw, mem_univ _⟩, hx⟩)

/-- The same actual Finsler family transports matching seed and shifted-clock jets to
one shared actual position-and-momentum derivative, including arbitrary allowed sets. -/
theorem chartMomentumFamily_same_firstJet_within (hF : F.IsSmoothStronglyConvex)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    {X Y : V → W} {f g : V → ℝ} {s : Set V} {x : V}
    {D : V →L[ℝ] W} {a : V →L[ℝ] ℝ}
    (hX : HasFDerivWithinAt X D s x) (hY : HasFDerivWithinAt Y D s x)
    (hf : HasFDerivWithinAt f a s x) (hg : HasFDerivWithinAt g a s x)
    (hseed : X x = Y x) (hclock : f x = g x) (hXB : X x ∈ B)
    (old : M) (r : ℝ) (hx : Γ (X x) (r - f x) ∈ (extChartAt 𝓘(ℝ, E) old).source) :
    let L := (fderiv ℝ (F.chartMomentumFamily old Γ) (X x, r - f x)).comp (D.prod (-a))
    F.chartMomentumFamily old Γ (X x, r - f x) =
      F.chartMomentumFamily old Γ (Y x, r - g x) ∧
      HasFDerivWithinAt (fun y ↦ F.chartMomentumFamily old Γ (X y, r - f y)) L s x ∧
      HasFDerivWithinAt (fun y ↦ F.chartMomentumFamily old Γ (Y y, r - g y)) L s x := by
  exact flow_comp_sub_clock_same_firstJet_within r hX hY hf hg hseed hclock
    ((hF.contDiffAt_chartMomentumFamily_of_tangentFamily hB hEL hG hXB old (r - f x) hx)
      |>.differentiableAt (by norm_num))

/-- Completeness and the same original Legendre inverse construct one family indexed
by genuine initial position and energy covector, with jointly C2 actual total tangent. -/
theorem exists_complete_covectorFamily_C2 [T2Space M] [PreconnectedSpace M]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (initial : M) {z₀ : E × E} (hz₀ : z₀ ∈ chartEnergyDomain initial) (t₀ : ℝ) :
    ∃ (U : Set (E × (E →L[ℝ] ℝ))) (Γ : (E × (E →L[ℝ] ℝ)) → ℝ → M),
      IsOpen U ∧ parametricLegendre (F.chartEnergy initial) z₀ ∈ U ∧
      (∀ q ∈ U, F.IsEulerLagrangeOn (Γ q) univ) ∧
      (∀ q ∈ U, F.chartMomentumFamily initial Γ (q, t₀) = q) ∧
      ContMDiffOn 𝓘(ℝ, (E × (E →L[ℝ] ℝ)) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
        (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩)
        (U ×ˢ univ) := by
  obtain ⟨e, he, hzs, hzt, hsub, hLeg, hInv, hbase, hInvDeriv⟩ :=
    hF.exists_smooth_chartLegendre_local_inverse initial hz₀
  obtain ⟨Φ, hEL, hinit, hG⟩ := hF.exists_complete_tangentFamily_C2 hcomplete initial t₀
  let Γ : (E × (E →L[ℝ] ℝ)) → ℝ → M := fun q ↦ Φ (e.symm q)
  have hlegal (q) (hq : q ∈ e.target) : e.symm q ∈ chartEnergyDomain initial :=
    hsub (e.map_target hq)
  refine ⟨e.target, Γ, e.open_target, hzt, fun q hq ↦ hEL _ (hlegal q hq), ?_, ?_⟩
  · intro q hq
    change eulerLagrangePhaseLift (F.chartEnergy initial)
      (extChartAt 𝓘(ℝ, E) initial ∘ Φ (e.symm q)) t₀ = q
    rw [hF.chartMomentum_of_tangent_eq
      (hEL (e.symm q) (hlegal q hq) t₀ (mem_univ _)) initial (hlegal q hq)
      (hinit (e.symm q) (hlegal q hq))]
    simpa only [he] using e.right_inv hq
  · have hj : ContDiffOn ℝ 2
        (fun q : (E × (E →L[ℝ] ℝ)) × ℝ ↦ (e.symm q.1, q.2)) (e.target ×ˢ univ) :=
      ((hInv.of_le (by simp)).comp contDiffOn_fst (fun q hq ↦ hq.1)).prodMk contDiffOn_snd
    exact hG.comp hj.contMDiffOn (fun q hq ↦ ⟨hlegal q.1 hq.1, mem_univ _⟩)

/-- One genuinely complete original family transports every pair of matching initial
position/covector jets and clock jets at all chart-legal times. No family regularity or
flow-jet identity is supplied: original completeness constructs the family and its C2
regularity. The two maps may be differentiable only within the allowed parameter set. -/
theorem exists_complete_covectorFamily_matching_firstJets [T2Space M] [PreconnectedSpace M]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (initial : M) {z₀ : E × E} (hz₀ : z₀ ∈ chartEnergyDomain initial) (t₀ : ℝ) :
    ∃ (U : Set (E × (E →L[ℝ] ℝ))) (Γ : (E × (E →L[ℝ] ℝ)) → ℝ → M),
      IsOpen U ∧ parametricLegendre (F.chartEnergy initial) z₀ ∈ U ∧
      (∀ q ∈ U, F.IsEulerLagrangeOn (Γ q) univ) ∧
      (∀ q ∈ U, F.chartMomentumFamily initial Γ (q, t₀) = q) ∧
      ∀ (X Y : V → E × (E →L[ℝ] ℝ)) (f g : V → ℝ) (s : Set V) (x : V)
        (D : V →L[ℝ] E × (E →L[ℝ] ℝ)) (a : V →L[ℝ] ℝ),
        HasFDerivWithinAt X D s x → HasFDerivWithinAt Y D s x →
        HasFDerivWithinAt f a s x → HasFDerivWithinAt g a s x →
        X x = Y x → f x = g x → X x ∈ U → ∀ (old : M) (r : ℝ),
        Γ (X x) (r - f x) ∈ (extChartAt 𝓘(ℝ, E) old).source →
        ∃ L : V →L[ℝ] E × (E →L[ℝ] ℝ),
          F.chartMomentumFamily old Γ (X x, r - f x) =
            F.chartMomentumFamily old Γ (Y x, r - g x) ∧
          HasFDerivWithinAt (fun y ↦ F.chartMomentumFamily old Γ (X y, r - f y)) L s x ∧
          HasFDerivWithinAt (fun y ↦ F.chartMomentumFamily old Γ (Y y, r - g y)) L s x := by
  obtain ⟨U, Γ, hU, hpU, hEL, hi, hG⟩ :=
    hF.exists_complete_covectorFamily_C2 hcomplete initial hz₀ t₀
  refine ⟨U, Γ, hU, hpU, hEL, hi, ?_⟩
  intro X Y f g s x D a hX hY hf hg hseed hclock hXU old r hx
  exact ⟨_, hF.chartMomentumFamily_same_firstJet_within hU hEL hG hX hY hf hg
    hseed hclock hXU old r hx⟩

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
end
