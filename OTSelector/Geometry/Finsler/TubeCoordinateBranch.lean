import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.CompleteTangentSmooth
import OTSelector.Geometry.Finsler.EndpointDistanceBranch
import OTSelector.Geometry.Finsler.EndpointInverse
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Uniqueness
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.TubeCoordinateDistance
import OTSelector.Geometry.Finsler.TubeCoordinateEndpoint
import OTSelector.Geometry.Manifold.ManifoldFlowTimePotential

/-!
# Geometry.Finsler.TubeCoordinateBranch

* **Conditions:** The same actual calibrated manifold tube and original minimizing central family.
* **Objects:** One genuine endpoint inverse branch precomposed with the two tube-to-old-chart changes, exact endpoints and original distance=length.
* **Proof detail:** Construct the inverse once, compose its seed map with actual endpoint coordinate changes and retain the same original complete curves and C2 tangent data.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=51): Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, p. 313: the length integral, induced distance and minimizing curves.

Source relation (derived): The stated result is a derived local construction from the cited principles. The exact original family, branch, coordinate maps and hypotheses remain those in the full source telescope.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerTubeCoordinateBranch.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerTubeCoordinateBranch`; the selected original proof blocks follow. -/
section

/-!
# The original minimizing endpoint branch in genuine tube coordinates

Construct the endpoint inverse once, then precompose its actual seed map with the
true changes from tube coordinates to the two endpoint charts. The resulting curves
belong to the same original complete family. Their true global distance equals their
original path length, with exact endpoints and jointly C2 actual tangent data.
No claim that the entire tube lies in one fixed manifold chart is used.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- A genuinely calibrated tube constructs the minimizing endpoint branch of the same
complete original family, including its actual seed map, full-time Euler--Lagrange
curves, C2 total tangent, exact endpoints and original extended-distance identity. -/
theorem exists_tubeCoordinate_endpointBranch_of_calibrated_manifoldTube
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (initial terminal : M)
    {Y : OpenPartialHomeomorph (ℝ × W) M} {Λ : W → ℝ → M}
    (hY : ContMDiffOn 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) ∞ Y.symm Y.target)
    (heq : (Y : ℝ × W → M) = fun q ↦ Λ q.2 q.1)
    (hhalf : ∀ q ∈ Y.source,
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Λ q.2) ⟨q.1, (1 : ℝ)⟩) = 1 / 2)
    (t₀ : ℝ)
    (hbound : ∀ x ∈ Y.target, ∀ v : TangentSpace 𝓘(ℝ, E) x,
      @LE.le ℝ _ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential Y 1 t₀) x v)
        (F.toFun ⟨x, v⟩ : ℝ))
    {a b : ℝ} (hab : a < b) {Γ : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain initial, F.IsEulerLagrangeOn (Γ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain initial,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ z) ⟨a, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    {z : E × E} (hz : z ∈ chartEnergyDomain initial) {w : W}
    (hΛ : F.IsEulerLagrangeOn (Λ w) univ)
    (hseed : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Λ w) ⟨a, (1 : ℝ)⟩ =
      (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
        (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    (hstay : ∀ t ∈ Icc a b, (t, w) ∈ Y.source)
    (hterminal : Λ w b ∈ (extChartAt 𝓘(ℝ, E) terminal).source)
    (hmin : letI _instTubeBranchMinENorm :
        ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
      F.lengthEDist (Γ z a) (Γ z b) = Manifold.pathELength 𝓘(ℝ, E) (Γ z) a b)
    {u : M → ℝ}
    (hu : letI _instTubeBranchLipMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (hsat : letI _instTubeBranchSatMetric : MetricSpace M := F.metricSpace
      u (Γ z b) - u (Γ z a) = dist (Γ z a) (Γ z b))
    (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (Γ z a)) :
    letI _instTubeBranchOutputENorm :
      ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
    ∃ (e : OpenPartialHomeomorph (E × E) (E × E))
      (Q : Set ((ℝ × W) × (ℝ × W))),
      (e : E × E → E × E) = chartEndpointMap terminal Γ b ∧
      IsOpen Q ∧ ((a, w), (b, w)) ∈ Q ∧ Q ⊆ Y.source ×ˢ Y.source ∧
      let η : ((ℝ × W) × (ℝ × W)) → E × E := fun q ↦
        e.symm (tubeEndpointChart initial terminal Y q)
      ContDiffOn ℝ 2 η Q ∧ MapsTo η Q (chartEnergyDomain initial) ∧
      η ((a, w), (b, w)) = z ∧
      (∀ q ∈ Q, F.IsEulerLagrangeOn (Γ (η q)) univ) ∧
      ContMDiffOn 𝓘(ℝ, ((ℝ × W) × (ℝ × W)) × ℝ)
        (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
        (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ (η q.1)) ⟨q.2, (1 : ℝ)⟩)
        (Q ×ˢ univ) ∧
      (∀ q ∈ Q, Γ (η q) a = Y q.1 ∧ Γ (η q) b = Y q.2 ∧
        F.lengthEDist (Y q.1) (Y q.2) =
          Manifold.pathELength 𝓘(ℝ, E) (Γ (η q)) a b) ∧
      Γ (η ((a, w), (b, w))) = Λ w := by
  let _instTubeBranchProofENorm : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  have hsame : Γ z = Λ w := by
    funext t
    exact hF.eqOn_of_isEulerLagrangeOn isOpen_univ isPreconnected_univ
      (hEL z hz) hΛ (mem_univ a) ((hinit z hz).trans hseed.symm) (mem_univ t)
  have hYval (t : ℝ) : Y (t, w) = Γ z t := (congrFun heq (t, w)).trans
    (congrFun hsame t).symm
  have hinv := hF.isInvertible_chartEndpointMap_of_calibrated_manifoldTube
    initial terminal hY hi heq hhalf t₀ hbound hab hEL hinit hz hΛ hseed hstay hterminal
  have hx : Γ z b ∈ (extChartAt 𝓘(ℝ, E) terminal).source := by
    simpa only [hsame] using hterminal
  have hG := (hF.contMDiffOn_tangentFamily_of_chartSeed_smooth initial
    (isOpen_chartEnergyDomain initial) hEL contDiffOn_id (fun _ hz ↦ hz) hinit).1
  have hG₂ := hG.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)
  obtain ⟨e, V, he, hze, hzV, hsub, heC2, hInv, hV, hVe, hcharts, hbranch, hdist⟩ :=
    hF.exists_calibrated_endpointDistanceBranch hcomplete initial terminal hab hEL hinit hG₂
      hz hmin hu hsat hdu hx hinv
  have hstart : Γ z a = (extChartAt 𝓘(ℝ, E) initial).symm z.1 := by
    have hb := congrArg (fun v : TangentBundle 𝓘(ℝ, E) M ↦ v.1) (hinit z hz)
    rw [tangentChart_symm_eq initial hz.1 z.2] at hb
    exact hb
  let A : Set (ℝ × W) := Y.source ∩ Y ⁻¹' (extChartAt 𝓘(ℝ, E) initial).source
  let B : Set (ℝ × W) := Y.source ∩ Y ⁻¹' (extChartAt 𝓘(ℝ, E) terminal).source
  have hA : IsOpen A := hY.continuousOn.isOpen_inter_preimage Y.open_source
    (isOpen_extChartAt_source initial)
  have hB : IsOpen B := hY.continuousOn.isOpen_inter_preimage Y.open_source
    (isOpen_extChartAt_source terminal)
  have hca : ContDiffOn ℝ ∞ (fun q ↦ extChartAt 𝓘(ℝ, E) initial (Y q)) A := by
    apply hA.contDiffOn_iff.mpr
    intro q hq
    exact ((contMDiffAt_extChartAt' (n := ∞)
      (by simpa only [mem_preimage, extChartAt_source] using hq.2)).comp q
      (hY.contMDiffAt (Y.open_source.mem_nhds hq.1))).contDiffAt
  have hcb : ContDiffOn ℝ ∞ (fun q ↦ extChartAt 𝓘(ℝ, E) terminal (Y q)) B := by
    apply hB.contDiffOn_iff.mpr
    intro q hq
    exact ((contMDiffAt_extChartAt' (n := ∞)
      (by simpa only [mem_preimage, extChartAt_source] using hq.2)).comp q
      (hY.contMDiffAt (Y.open_source.mem_nhds hq.1))).contDiffAt
  have hC : ContDiffOn ℝ ∞ (tubeEndpointChart initial terminal Y) (A ×ˢ B) :=
    (hca.comp contDiffOn_fst (fun q hq ↦ hq.1)).prodMk
      (hcb.comp contDiffOn_snd (fun q hq ↦ hq.2))
  have hqa : (a, w) ∈ A := by
    refine ⟨hstay a (left_mem_Icc.mpr hab.le), ?_⟩
    change Y (a, w) ∈ (extChartAt 𝓘(ℝ, E) initial).source
    rw [hYval a, hstart]
    exact (extChartAt 𝓘(ℝ, E) initial).map_target hz.1
  have hqb : (b, w) ∈ B :=
    ⟨hstay b (right_mem_Icc.mpr hab.le), by
      change Y (b, w) ∈ (extChartAt 𝓘(ℝ, E) terminal).source
      rwa [hYval b]⟩
  have hcenter : tubeEndpointChart initial terminal Y ((a, w), (b, w)) =
      chartEndpointMap terminal Γ b z := by
    apply Prod.ext
    · change extChartAt 𝓘(ℝ, E) initial (Y (a, w)) = z.1
      rw [hYval a, hstart, (extChartAt 𝓘(ℝ, E) initial).right_inv hz.1]
    · exact congrArg (extChartAt 𝓘(ℝ, E) terminal) (hYval b)
  let Q : Set ((ℝ × W) × (ℝ × W)) :=
    (A ×ˢ B) ∩ (tubeEndpointChart initial terminal Y) ⁻¹' V
  have hQ : IsOpen Q := hC.continuousOn.isOpen_inter_preimage (hA.prod hB) hV
  have hqQ : ((a, w), (b, w)) ∈ Q := ⟨⟨hqa, hqb⟩, by
    change tubeEndpointChart initial terminal Y ((a, w), (b, w)) ∈ V
    rwa [hcenter]⟩
  let η : ((ℝ × W) × (ℝ × W)) → E × E := fun q ↦
    e.symm (tubeEndpointChart initial terminal Y q)
  have hη : ContDiffOn ℝ 2 η Q :=
    hInv.comp ((hC.mono inter_subset_left).of_le (by simp)) (fun q hq ↦ hVe hq.2)
  have hmap : MapsTo η Q (chartEnergyDomain initial) :=
    fun q hq ↦ hsub (e.map_target (hVe hq.2))
  have hηz : η ((a, w), (b, w)) = z := by
    change e.symm (tubeEndpointChart initial terminal Y ((a, w), (b, w))) = z
    rw [hcenter, ← he]
    exact e.left_inv hze
  have hpre : ContDiffOn ℝ 2
      (fun q : ((ℝ × W) × (ℝ × W)) × ℝ ↦ (η q.1, q.2)) (Q ×ˢ univ) :=
    (hη.comp contDiffOn_fst (fun q hq ↦ hq.1)).prodMk contDiffOn_snd
  refine ⟨e, Q, he, hQ, hqQ, fun q hq ↦ ⟨hq.1.1.1, hq.1.2.1⟩,
    hη, hmap, hηz, fun q hq ↦ hEL _ (hmap hq),
    hG₂.comp hpre.contMDiffOn (fun q hq ↦ ⟨hmap hq.1, mem_univ _⟩), ?_, ?_⟩
  · intro q hq
    have hia := (extChartAt 𝓘(ℝ, E) initial).left_inv hq.1.1.2
    have hib := (extChartAt 𝓘(ℝ, E) terminal).left_inv hq.1.2.2
    have hbq := hbranch (tubeEndpointChart initial terminal Y q) hq.2
    exact ⟨by simpa only [tubeEndpointChart, hia] using hbq.1,
      by simpa only [tubeEndpointChart, hib] using hbq.2.1,
      by simpa only [tubeEndpointChart, hia, hib] using hbq.2.2.1⟩
  · change Γ (η ((a, w), (b, w))) = Λ w
    rw [hηz]
    exact hsame

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
