import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.C11LevelPositionRank
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.CompleteTangentSmooth
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialCompleteGauss
import OTSelector.Geometry.Finsler.SmoothTubeCalibration
import OTSelector.Geometry.Manifold.ManifoldFlowTimePotential
import OTSelector.Geometry.Manifold.ManifoldPositionRank
import OTSelector.Geometry.Symplectic.PotentialConormal

/-!
# Geometry.Finsler.C11LevelSmoothTube

* **Conditions:** The same selected smooth potential-level family, its ordinary position comparison and central calibrated isometry.
* **Objects:** A common smooth actual tube/inverse and intrinsic calibration around every compact time set strictly inside the reach.
* **Proof detail:** Use level-normal initial data for Gauss identity, smooth initial seed for joint smoothness and actual position rank for the regular tube construction.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=51): Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [J. C. Álvarez Paiva; A. C. Thompson, Volumes on Normed and Finsler Spaces, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/02AT.pdf#page=22): Section 4.2, Definition 4.11 and Proposition 4.12, p. 22.

Source relation (derived): Derived from the cited geometric/analytic principles with the exact actual source hypotheses. The local construction and its original phase/covector data are retained, rather than asserted as a verbatim source statement.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerC11LevelSmoothTube.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerC11LevelSmoothTube`; the selected original proof blocks follow. -/
section

/-!
# Smooth calibrated tubes for the selected C1,1 potential-level family

The ordinary position comparison controls the same selected smooth potential-level
family. Its initial conormal data give Gauss normality, and its retained smooth
position and velocity seed gives joint smoothness. The central calibrated isometry
then supplies a common smooth tube and inverse-time calibration around every compact
time set strictly inside the calibrated interval.
-/

open Set Filter Manifold
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- The selected potential-level witnesses and their ordinary position comparison
construct a smooth calibrated tube of that exact family. The ambient central
isometry and comparison are intermediate conclusions of the original calibrated
core; no regularity or rank premise is imposed on the tube. -/
theorem exists_smooth_calibratedTube_of_levelPositionComparison
    (hF : F.IsSmoothStronglyConvex) (old : M)
    {G P : E → ℝ} {A : E → ℝ → M} {δ : ℝ} {x : E}
    (hcmp : F.HasC11LevelPositionComparisonAt old G A δ x)
    (hdim : Module.finrank ℝ (fderiv ℝ G x).ker + 1 = Module.finrank ℝ E)
    {B : Set (fderiv ℝ G x).ker} {σ v : (fderiv ℝ G x).ker → E}
    {a : (fderiv ℝ G x).ker → ℝ} {Γ : (fderiv ℝ G x).ker → ℝ → M}
    (hB : IsOpen B) (h0 : (0 : (fderiv ℝ G x).ker) ∈ B)
    (hP : ∀ w ∈ B, DifferentiableAt ℝ P (σ w))
    (hσ : ContDiffOn ℝ ∞ σ B) (hσ0 : σ 0 = x)
    (hlevel : ∀ w ∈ B, P (σ w) = P x)
    (hv : ContDiffOn ℝ ∞ v B) (ha0 : a 0 = 1)
    (hDP : fderiv ℝ P x = fderiv ℝ G x)
    (hdomain : ∀ w ∈ B, (σ w, v w) ∈ chartEnergyDomain old)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hinit : ∀ w ∈ B,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨0, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm (σ w, v w))
    (hm : ∀ w ∈ B, F.chartMomentumFamily old Γ (w, 0) =
      potentialConormalState P σ a w)
    (henergy : ∀ w ∈ B, ∀ t : ℝ,
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t, (1 : ℝ)⟩) = 1 / 2)
    (hjet : HasFDerivAt (fun w ↦ F.chartMomentumFamily old Γ (w, 0))
      ((fderiv ℝ G x).ker.subtypeL.prod
        ((fderiv ℝ (fderiv ℝ G) x).comp (fderiv ℝ G x).ker.subtypeL)) 0)
    (hiso : letI : MetricSpace M := F.metricSpace
      Isometry (fun t : Icc (-δ) δ ↦ A x t))
    {J : Set ℝ} (hJ : IsCompact J) (hJsub : J ⊆ Ioo (-δ) δ) :
    A x = Γ 0 ∧
    ContMDiffOn 𝓘(ℝ, (fderiv ℝ G x).ker × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩)
      (B ×ˢ univ) ∧
    ∃ (T : Set ℝ) (V : Set (fderiv ℝ G x).ker)
        (e : OpenPartialHomeomorph (ℝ × (fderiv ℝ G x).ker) M),
      IsOpen T ∧ IsOpen V ∧ J ⊆ T ∧ (0 : (fderiv ℝ G x).ker) ∈ V ∧
      T ×ˢ V ⊆ univ ×ˢ B ∧
      (e : ℝ × (fderiv ℝ G x).ker → M) = (fun q ↦ Γ q.2 q.1) ∧
      e.source = T ×ˢ V ∧
      e.target = (fun q : ℝ × (fderiv ℝ G x).ker ↦ Γ q.2 q.1) '' (T ×ˢ V) ∧
      ContMDiffOn 𝓘(ℝ, ℝ × (fderiv ℝ G x).ker) 𝓘(ℝ, E) ∞ e e.source ∧
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × (fderiv ℝ G x).ker) ∞ e.symm e.target ∧
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (manifoldFlowTimePotential e 1 0) e.target ∧
      (∀ y ∈ e.target, ∀ z : TangentSpace 𝓘(ℝ, E) y,
        @LE.le ℝ _ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential e 1 0) y z)
          (F.toFun ⟨y, z⟩ : ℝ)) ∧
      ∀ q ∈ e.source,
        manifoldFlowTimePotential e 1 0 (Γ q.2 q.1) = q.1 ∧
        HasDerivAt (fun t ↦ manifoldFlowTimePotential e 1 0 (Γ q.2 t)) 1 q.1 ∧
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential e 1 0) (Γ q.2 q.1) =
          fderiv ℝ (F.fiberEnergy (Γ q.2 q.1))
            (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.2) q.1 1) := by
  have hseed : ContDiffOn ℝ ∞ (fun w ↦ (σ w, v w)) B := hσ.prodMk hv
  have hΓ := (hF.contMDiffOn_tangentFamily_of_chartSeed_smooth old hB hEL
    hseed hdomain hinit).1
  have hΓ₂ := hΓ.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)
  have hsource (w : (fderiv ℝ G x).ker) (hw : w ∈ B) :
      Γ w 0 ∈ (extChartAt 𝓘(ℝ, E) old).source := by
    have hb : Γ w 0 = (extChartAt 𝓘(ℝ, E) old).symm (σ w) := by
      have h := congrArg (fun q : TangentBundle 𝓘(ℝ, E) M ↦ q.1) (hinit w hw)
      rw [tangentChart_symm_eq old (hdomain w hw).1] at h
      exact h
    rw [hb]
    exact (extChartAt 𝓘(ℝ, E) old).map_target (hdomain w hw).1
  have hvalue : F.chartMomentumFamily old Γ (0, 0) = (x, fderiv ℝ G x) := by
    simpa only [potentialConormalState, hσ0, ha0, one_smul, hDP] using hm 0 h0
  obtain ⟨hcenter, hrank⟩ := hcmp B Γ hB h0 hEL hsource hjet hvalue
  have hnormal (w : (fderiv ℝ G x).ker) (hw : w ∈ B) (t : ℝ) (terminal : M)
      (ht : Γ w t ∈ (extChartAt 𝓘(ℝ, E) terminal).source)
      (ξ : (fderiv ℝ G x).ker) :
      (F.chartMomentumFamily terminal Γ (w, t)).2
        (fderiv ℝ (fun z ↦ extChartAt 𝓘(ℝ, E) terminal (Γ z t)) w ξ) = 0 := by
    apply hF.chartMomentumFamily_gauss_zero_of_potential_initial hB hEL hΓ₂
      henergy old 0 hm hw (hsource w hw) (hP w hw)
      ((hσ.contDiffAt (hB.mem_nhds hw)).differentiableAt (by simp))
      (c := P x) _ terminal t ht ξ
    filter_upwards [hB.mem_nhds hw] with z hz
    exact hlevel z hz
  have hisoΓ : letI : MetricSpace M := F.metricSpace
      Isometry (fun t : Icc (-δ) δ ↦ Γ 0 t) := by
    rwa [← hcenter]
  have hregular (t : ℝ) (ht : t ∈ J) :
      HasInjectiveManifoldPosition (E := E) (fun w ↦ Γ w t) 0 := by
    intro terminal hlegal
    obtain ⟨_, _, c, hc, hbound, hinj⟩ :=
      hrank terminal t (abs_lt.mpr (hJsub ht)) hlegal
    exact hinj
  refine ⟨hcenter, ?_⟩
  simpa only [sub_zero] using
    hF.exists_smooth_manifoldTube_calibration_of_chartSeed hdim hB hEL old
      hseed hdomain hinit henergy hnormal h0 hisoΓ hJ
      (fun _ ht ↦ ⟨(hJsub ht).1.le, (hJsub ht).2.le⟩) hregular 0

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
