import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.CompleteTangentSmooth
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.ManifoldTubeCalibration
import OTSelector.Geometry.Finsler.RegularTube
import OTSelector.Geometry.Manifold.ManifoldFlowTimePotential
import OTSelector.Geometry.Manifold.ManifoldInjectiveTube
import OTSelector.Geometry.Manifold.ManifoldPositionRank

/-!
# Geometry.Finsler.SmoothTubeCalibration

* **Conditions:** The same smooth initial seed and a compact regular central portion of its complete original family, with unit energy and Gauss identities.
* **Objects:** A genuine smooth manifold tube and smooth inverse with its actual intrinsic calibration.
* **Proof detail:** Upgrade the same family by smooth ODE dependence, construct a smooth regular compact tube and identify inverse-time differential with the actual original momentum.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=51): Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57.
- [J. C. Álvarez Paiva; A. C. Thompson, Volumes on Normed and Finsler Spaces, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/02AT.pdf#page=22): Section 4.2, Definition 4.11 and Proposition 4.12, p. 22.

Source relation (derived): The tube may be newly constructed for that same family; it need not equal a formerly selected C2 inverse.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerSmoothTubeCalibration.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerSmoothTubeCalibration`; the selected original proof blocks follow. -/
section

/-!
# Smooth calibrated tubes of the same complete Finsler family

The original smooth initial seed gives joint smoothness of the same complete
Euler--Lagrange family. Its regular compact central portion then has a common
smooth manifold tube and smooth inverse, across arbitrary original charts.
Half energy and the actual Gauss identity make inverse time a smooth calibration
with the intrinsic original energy momentum as differential in every direction.
The regular compact set is a localization away from focal times, not a new final
geometric condition. The tube is newly constructed for the same family; it need
not coincide with a previously chosen C2 tube inverse.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- The same smooth complete family has a common smooth regular tube and a smooth
inverse-time calibration with its original intrinsic energy momentum. -/
theorem exists_smooth_manifoldTube_calibration (hF : F.IsSmoothStronglyConvex)
    (hdim : Module.finrank ℝ W + 1 = Module.finrank ℝ E)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    (henergy : ∀ w ∈ B, ∀ t : ℝ,
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t, (1 : ℝ)⟩) = 1 / 2)
    (hnormal : ∀ w ∈ B, ∀ (t : ℝ) (old : M),
      Γ w t ∈ (extChartAt 𝓘(ℝ, E) old).source → ∀ ξ : W,
        (F.chartMomentumFamily old Γ (w, t)).2
          (fderiv ℝ (fun v ↦ extChartAt 𝓘(ℝ, E) old (Γ v t)) w ξ) = 0)
    {w₀ : W} (hw : w₀ ∈ B) {a b : ℝ}
    (hiso : letI : MetricSpace M := F.metricSpace; Isometry (fun t : Icc a b ↦ Γ w₀ t))
    {K : Set ℝ} (hK : IsCompact K) (hKIcc : K ⊆ Icc a b)
    (hregular : ∀ t ∈ K, HasInjectiveManifoldPosition (E := E) (fun w ↦ Γ w t) w₀)
    (t₀ : ℝ) :
    ∃ (T : Set ℝ) (V : Set W) (e : OpenPartialHomeomorph (ℝ × W) M),
      IsOpen T ∧ IsOpen V ∧ K ⊆ T ∧ w₀ ∈ V ∧ T ×ˢ V ⊆ univ ×ˢ B ∧
      (e : ℝ × W → M) = (fun q ↦ Γ q.2 q.1) ∧ e.source = T ×ˢ V ∧
      e.target = (fun q : ℝ × W ↦ Γ q.2 q.1) '' (T ×ˢ V) ∧
      ContMDiffOn 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) ∞ e e.source ∧
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) ∞ e.symm e.target ∧
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (manifoldFlowTimePotential e 1 t₀) e.target ∧
      (∀ x ∈ e.target, ∀ v : TangentSpace 𝓘(ℝ, E) x,
        @LE.le ℝ _ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential e 1 t₀) x v)
          (F.toFun ⟨x, v⟩ : ℝ)) ∧
      ∀ q ∈ e.source,
        manifoldFlowTimePotential e 1 t₀ (Γ q.2 q.1) = q.1 - t₀ ∧
        HasDerivAt (fun t ↦ manifoldFlowTimePotential e 1 t₀ (Γ q.2 t)) 1 q.1 ∧
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential e 1 t₀) (Γ q.2 q.1) =
          fderiv ℝ (F.fiberEnergy (Γ q.2 q.1))
            (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.2) q.1 1) := by
  have hG₂ := hG.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)
  have hposition : ContMDiffOn 𝓘(ℝ, W × ℝ) 𝓘(ℝ, E) ∞
      (fun q ↦ Γ q.1 q.2) (B ×ˢ univ) :=
    fun q hq ↦ (Bundle.contMDiffWithinAt_totalSpace.mp (hG q hq)).1
  have hp : ContMDiffOn 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) ∞
      (fun q ↦ Γ q.2 q.1) (univ ×ˢ B) :=
    hposition.comp ((contDiff_snd.prodMk contDiff_fst).contMDiff.contMDiffOn)
      (fun _ hq ↦ ⟨hq.2, hq.1⟩)
  have hi : InjOn (Γ w₀) K := by
    have hi' : Function.Injective (fun t : Icc a b ↦ Γ w₀ t) := by
      let : MetricSpace M := F.metricSpace
      exact hiso.injective
    intro s hs t ht hst
    exact congrArg Subtype.val (hi' (a₁ := ⟨s, hKIcc hs⟩) (a₂ := ⟨t, hKIcc ht⟩) hst)
  have hcentral : K ×ˢ {w₀} ⊆ (univ : Set ℝ) ×ˢ B := by
    rintro ⟨t, w⟩ ⟨_, hw'⟩
    exact ⟨mem_univ _, mem_singleton_iff.mp hw' ▸ hw⟩
  have hinv (t : ℝ) (ht : t ∈ K) :
      (fderiv ℝ ((extChartAt 𝓘(ℝ, E) (Γ w₀ t)) ∘ fun q : ℝ × W ↦ Γ q.2 q.1)
        (t, w₀)).IsInvertible :=
    hF.isInvertible_fderiv_timeLabel_chartPosition hdim hB hEL hG₂ hw (Γ w₀ t) t
      (mem_extChartAt_source _) (hnormal w₀ hw t _ (mem_extChartAt_source _)) (hregular t ht)
  obtain ⟨T, V, e, hT, hV, hKT, hwV, hTV, he, hes, het, hf, hinverse⟩ :=
    exists_manifold_common_tube_inverse hK (isOpen_univ.prod hB) (by simp) hp
      hcentral hi hinv
  have hsource : e.source ⊆ univ ×ˢ B := by rwa [hes]
  have hunit (q : ℝ × W) (hq : q ∈ e.source) :
      (F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.2) ⟨q.1, (1 : ℝ)⟩) : ℝ) = 1 := by
    have he := henergy q.2 (hsource hq).2 q.1
    have hn := (F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.2)
      ⟨q.1, (1 : ℝ)⟩)).coe_nonneg
    unfold ContinuousFinslerNorm.energy at he
    nlinarith
  obtain ⟨_, hbound, htime⟩ := hF.manifoldTubeTime_calibration hB hEL hG₂ e he hsource
    (hinverse.of_le (by simp)) hunit
    (fun q hq ↦ hnormal q.2 (hsource hq).2 q.1) t₀
  exact ⟨T, V, e, hT, hV, hKT, hwV, hTV, he, hes, het, hf, hinverse,
    contMDiffOn_manifoldFlowTimePotential e hinverse 1 t₀, hbound, htime⟩

/-- The already constructed smooth chart seed builds a smooth calibrated tube of
its same complete family. For a potential-level seed use `ι w = (σ w, v w)`;
its existing seed regularity and exact initial tangent identity supply every input. -/
theorem exists_smooth_manifoldTube_calibration_of_chartSeed
    (hF : F.IsSmoothStronglyConvex)
    (hdim : Module.finrank ℝ W + 1 = Module.finrank ℝ E)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (initial : M) {ι : W → E × E} (hι : ContDiffOn ℝ ∞ ι B)
    (hιDomain : MapsTo ι B (chartEnergyDomain initial)) {s₀ : ℝ}
    (hinit : ∀ w ∈ B,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨s₀, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm (ι w))
    (henergy : ∀ w ∈ B, ∀ t : ℝ,
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t, (1 : ℝ)⟩) = 1 / 2)
    (hnormal : ∀ w ∈ B, ∀ (t : ℝ) (old : M),
      Γ w t ∈ (extChartAt 𝓘(ℝ, E) old).source → ∀ ξ : W,
        (F.chartMomentumFamily old Γ (w, t)).2
          (fderiv ℝ (fun v ↦ extChartAt 𝓘(ℝ, E) old (Γ v t)) w ξ) = 0)
    {w₀ : W} (hw : w₀ ∈ B) {a b : ℝ}
    (hiso : letI : MetricSpace M := F.metricSpace; Isometry (fun t : Icc a b ↦ Γ w₀ t))
    {K : Set ℝ} (hK : IsCompact K) (hKIcc : K ⊆ Icc a b)
    (hregular : ∀ t ∈ K, HasInjectiveManifoldPosition (E := E) (fun w ↦ Γ w t) w₀)
    (t₀ : ℝ) :
    ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ) ∧
    ∃ (T : Set ℝ) (V : Set W) (e : OpenPartialHomeomorph (ℝ × W) M),
      IsOpen T ∧ IsOpen V ∧ K ⊆ T ∧ w₀ ∈ V ∧ T ×ˢ V ⊆ univ ×ˢ B ∧
      (e : ℝ × W → M) = (fun q ↦ Γ q.2 q.1) ∧ e.source = T ×ˢ V ∧
      e.target = (fun q : ℝ × W ↦ Γ q.2 q.1) '' (T ×ˢ V) ∧
      ContMDiffOn 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) ∞ e e.source ∧
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) ∞ e.symm e.target ∧
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (manifoldFlowTimePotential e 1 t₀) e.target ∧
      (∀ x ∈ e.target, ∀ v : TangentSpace 𝓘(ℝ, E) x,
        @LE.le ℝ _ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential e 1 t₀) x v)
          (F.toFun ⟨x, v⟩ : ℝ)) ∧
      ∀ q ∈ e.source,
        manifoldFlowTimePotential e 1 t₀ (Γ q.2 q.1) = q.1 - t₀ ∧
        HasDerivAt (fun t ↦ manifoldFlowTimePotential e 1 t₀ (Γ q.2 t)) 1 q.1 ∧
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential e 1 t₀) (Γ q.2 q.1) =
          fderiv ℝ (F.fiberEnergy (Γ q.2 q.1))
            (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.2) q.1 1) := by
  have hG := (hF.contMDiffOn_tangentFamily_of_chartSeed_smooth initial hB hEL
    hι hιDomain hinit).1
  exact ⟨hG, hF.exists_smooth_manifoldTube_calibration hdim hB hEL hG henergy hnormal
    hw hiso hK hKIcc hregular t₀⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
