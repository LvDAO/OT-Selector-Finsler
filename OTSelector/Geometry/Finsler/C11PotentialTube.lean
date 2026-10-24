import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.C11LevelPositionRank
import OTSelector.Geometry.Finsler.C11LevelSmoothTube
import OTSelector.Geometry.Finsler.C11PotentialFamily
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Jacobi.Pairing
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Manifold.ManifoldFlowTimePotential
import OTSelector.Geometry.Symplectic.PotentialConormal

/-!
# Geometry.Finsler.C11PotentialTube

* **Conditions:** Actual C1,1 potential-family data, ordinary position comparison and central isometry for the same selected family.
* **Objects:** A selected smooth potential-level family admitting actual calibrated tubes on every compact interior time set.
* **Proof detail:** Retain the original representative/family and apply the smooth tube theorem to its actual regular position derivative.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=51): Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [J. C. Álvarez Paiva; A. C. Thompson, Volumes on Normed and Finsler Spaces, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/02AT.pdf#page=22): Section 4.2, Definition 4.11 and Proposition 4.12, p. 22.

Source relation (derived): Inverse tube time is a local calibration; equality with the original rough potential off the contact set is not asserted.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerC11PotentialTube.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerC11PotentialTube`; the selected original proof blocks follow. -/
section

/-!
# One selected smooth potential-level family with calibrated tubes

Retain the smooth representative and complete potential-level family selected by the
actual C1,1 contact data. Ordinary position comparison and the central calibrated
isometry give a smooth common tube around each compact interior time set for this
same family. The inverse time coordinate is a local calibration of the actual
Finsler length; no equality with the original potential off the contact set is claimed.
-/

open Set Filter MeasureTheory Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {F : ContinuousFinslerNorm E M}

/-- One smooth representative and one complete level family selected before choosing
the compact time set. Every such set inside the calibrated interval has a common
smooth tube of that family with a smooth inverse and actual inverse-time calibration. -/
def HasC11SmoothTubeFamilyAt (F : ContinuousFinslerNorm E M) (old : M)
    (u : M → ℝ) (G : E → ℝ) (A : E → ℝ → M) (δ : ℝ) (x : E) : Prop :=
  let p := fderiv ℝ G x
  HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) p x ∧
  Module.finrank ℝ p.ker + 1 = Module.finrank ℝ E ∧
  ∃ P : E → ℝ, ContDiff ℝ ∞ P ∧
    P x = u ((extChartAt 𝓘(ℝ, E) old).symm x) ∧
    HasFDerivAt P p x ∧ HasFDerivAt (fderiv ℝ P) (fderiv ℝ (fderiv ℝ G) x) x ∧
    ∃ (B : Set p.ker) (σ : p.ker → E) (Γ : p.ker → ℝ → M),
      IsOpen B ∧ (0 : p.ker) ∈ B ∧ ContDiffOn ℝ ∞ σ B ∧ σ 0 = x ∧
      (∀ w ∈ B, P (σ w) = P x) ∧ HasFDerivAt σ p.ker.subtypeL 0 ∧ InjOn σ B ∧
      MapsTo σ B (extChartAt 𝓘(ℝ, E) old).target ∧
      (∀ w ∈ B, Γ w 0 = (extChartAt 𝓘(ℝ, E) old).symm (σ w)) ∧
      (∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ) ∧
      ContMDiffOn 𝓘(ℝ, p.ker × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
        (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ) ∧
      (∀ w ∈ B, ∀ t : ℝ,
        F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t, (1 : ℝ)⟩) = (1 / 2 : ℝ)) ∧
      HasFDerivAt (fun w ↦ F.chartMomentumFamily old Γ (w, 0))
        (p.ker.subtypeL.prod ((fderiv ℝ (fderiv ℝ G) x).comp p.ker.subtypeL)) 0 ∧
      A x = Γ 0 ∧
      (∀ (chart : M) (t : ℝ), Γ 0 t ∈ (extChartAt 𝓘(ℝ, E) chart).source →
        Function.Injective (fderiv ℝ (fun w ↦ F.chartMomentumFamily chart Γ (w, t)) 0)) ∧
      (∀ w ∈ B, ∀ (chart : M) (t : ℝ),
        Γ w t ∈ (extChartAt 𝓘(ℝ, E) chart).source →
        ∀ ξ η : p.ker, canonicalPhasePairing
          (fderiv ℝ (fun b ↦ F.chartMomentumFamily chart Γ (b, t)) w ξ)
          (fderiv ℝ (fun b ↦ F.chartMomentumFamily chart Γ (b, t)) w η) = 0) ∧
      ∀ J : Set ℝ, IsCompact J → J ⊆ Ioo (-δ) δ →
        ∃ (T : Set ℝ) (V : Set p.ker)
            (e : OpenPartialHomeomorph (ℝ × p.ker) M),
          IsOpen T ∧ IsOpen V ∧ J ⊆ T ∧ (0 : p.ker) ∈ V ∧ T ×ˢ V ⊆ univ ×ˢ B ∧
          (e : ℝ × p.ker → M) = (fun q ↦ Γ q.2 q.1) ∧
          e.source = T ×ˢ V ∧
          e.target = (fun q : ℝ × p.ker ↦ Γ q.2 q.1) '' (T ×ˢ V) ∧
          ContMDiffOn 𝓘(ℝ, ℝ × p.ker) 𝓘(ℝ, E) ∞ e e.source ∧
          ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × p.ker) ∞ e.symm e.target ∧
          ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (manifoldFlowTimePotential e 1 0) e.target ∧
          (∀ y ∈ e.target, ∀ z : TangentSpace 𝓘(ℝ, E) y,
            @LE.le ℝ _ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential e 1 0) y z)
              (F.toFun ⟨y, z⟩ : ℝ)) ∧
          ∀ q ∈ e.source,
            manifoldFlowTimePotential e 1 0 (Γ q.2 q.1) = q.1 ∧
            HasDerivAt (fun t ↦ manifoldFlowTimePotential e 1 0 (Γ q.2 t)) 1 q.1 ∧
            mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential e 1 0) (Γ q.2 q.1) =
              fderiv ℝ (F.fiberEnergy (Γ q.2 q.1))
                (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.2) q.1 1)

namespace IsSmoothStronglyConvex

variable [T2Space M] [PreconnectedSpace M] [MeasurableSpace E]

/-- The already selected potential-level witnesses form smooth calibrated tubes of
one common family over every compact interior time set. Original completeness and
position rank have already been discharged in the supplied core conclusions. -/
theorem smoothTubeFamily_of_C11PotentialFamily (hF : F.IsSmoothStronglyConvex)
    {m : Measure E} {old : M} {u : M → ℝ} {G : E → ℝ} {K : Set E} {x : E}
    {A : E → ℝ → M} {δ : ℝ}
    (hx : F.HasC11PotentialFamilyAt m old 0 u G K x)
    (hcmp : F.HasC11LevelPositionComparisonAt old G A δ x)
    (hiso : let _instPotentialTubeCentralMetric : MetricSpace M := F.metricSpace
      Isometry (fun t : Icc (-δ) δ ↦ A x t)) :
    F.HasC11SmoothTubeFamilyAt old u G A δ x := by
  obtain ⟨_, _, hfirst, _, _, _, _, _, _, _, P, hP, hPval, hP₁, hP₂, _, _,
    hdim, B₀, B, σ, v, a, Γ, _, _, hB, h0, hBB₀, _, _, hσ, hσ0, hlevel, hσD,
    hσinj, _, hv, _, _, ha0, hstate, hEL, hinit, hm, _, henergy, hrank, hpair, _, hjet⟩ := hx
  have hDP : fderiv ℝ P x = fderiv ℝ G x := hP₁.fderiv.trans hfirst.fderiv
  have hσB : ContDiffOn ℝ ∞ σ B := hσ.mono hBB₀
  have hlevelB : ∀ w ∈ B, P (σ w) = P x := fun w hw ↦ hlevel w (hBB₀ hw)
  have hdomain : ∀ w ∈ B, (σ w, v w) ∈ chartEnergyDomain old :=
    fun w hw ↦ (hstate w hw).1
  have hPdiff : ∀ w ∈ B, DifferentiableAt ℝ P (σ w) :=
    fun w _ ↦ hP.differentiable (by simp) (σ w)
  have htube (J : Set ℝ) (hJ : IsCompact J) (hJsub : J ⊆ Ioo (-δ) δ) :=
    hF.exists_smooth_calibratedTube_of_levelPositionComparison old hcmp hdim hB h0
      hPdiff hσB hσ0 hlevelB hv ha0 hDP hdomain hEL hinit hm henergy hjet hiso hJ hJsub
  obtain ⟨hcenter, hΓ, _⟩ := htube ∅ isCompact_empty (empty_subset _)
  refine ⟨hfirst, hdim, P, hP, hPval, hP₁.congr_fderiv hfirst.fderiv, hP₂,
    B, σ, Γ, hB, h0, hσB, hσ0, hlevelB, hσD, hσinj.mono hBB₀,
    (fun w hw ↦ (hdomain w hw).1), ?_, hEL, hΓ, henergy, hjet, hcenter, hrank, hpair,
    fun J hJ hJsub ↦ (htube J hJ hJsub).2.2⟩
  intro w hw
  have hb := congrArg (fun q : TangentBundle 𝓘(ℝ, E) M ↦ q.1) (hinit w hw)
  rw [tangentChart_symm_eq old (hdomain w hw).1] at hb
  exact hb

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm

end
end
