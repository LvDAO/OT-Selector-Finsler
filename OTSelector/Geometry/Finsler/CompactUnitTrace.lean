import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.EndpointMinimizerStability
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Energy.Compact
import OTSelector.Geometry.Finsler.FlowLocalC2
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.TangentReadout
import OTSelector.Geometry.Manifold.TangentFamilyPosition

/-!
# Geometry.Finsler.CompactUnitTrace

* **Conditions:** A compact legal chart core and all original unit initial states over it in complete Finsler geometry.
* **Objects:** One common short time interval and compact slit phase trace for every actual curve from that layer.
* **Proof detail:** Compactify the full unit-speed layer and apply continuity of the actual complete flow uniformly, keeping the chart trace inside the slit domain.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).

Source relation (derived): No continuity of a selected potential direction is assumed.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerCompactUnitTrace.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerCompactUnitTrace`; the selected original proof blocks follow. -/
section

/-!
# Uniform compact chart traces of the complete original unit flow

The entire unit-speed layer over a compact chart core is compact. The actual complete
flow then gives one common short open time interval and one compact slit phase set for
all complete Euler--Lagrange curves starting in this layer. No continuity of a selected
potential direction or prescribed family of minimizing curves is needed.
-/

open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- All actual complete curves with unit initial speed over a compact chart core share
one open time interval and one compact original slit phase set. The constants and set
are constructed from the full unit layer, independently of the chosen curve. -/
theorem exists_compact_unit_chartTrace (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {K : Set E} (hK : IsCompact K)
    (hKtarget : K ⊆ (extChartAt 𝓘(ℝ, E) old).target) {ε : ℝ} (hε : 0 < ε) :
    ∃ (τ : ℝ) (I : Set ℝ) (P : Set (E × E)),
      0 < τ ∧ τ ≤ ε ∧ IsOpen I ∧ Icc (-τ) 0 ⊆ I ∧
      IsCompact P ∧ P ⊆ chartEnergyDomain old ∧
      ∀ (c : ℝ → M), F.IsEulerLagrangeOn c univ →
        F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨0, (1 : ℝ)⟩) = 1 →
        c 0 ∈ (extChartAt 𝓘(ℝ, E) old).source → extChartAt 𝓘(ℝ, E) old (c 0) ∈ K →
        MapsTo c I (extChartAt 𝓘(ℝ, E) old).source ∧
        ContDiffOn ℝ ∞ (extChartAt 𝓘(ℝ, E) old ∘ c) I ∧
        ∀ t ∈ Icc (-τ) 0,
          ((extChartAt 𝓘(ℝ, E) old ∘ c) t,
            deriv (extChartAt 𝓘(ℝ, E) old ∘ c) t) ∈ P := by
  let S := {z : E × E | z.1 ∈ K ∧ (F.chartLength old z : ℝ) ∈ Icc 1 1}
  have hS : IsCompact S := F.isCompact_chartSpeed_range old hK hKtarget 1 1
  have hSD : S ⊆ chartEnergyDomain old :=
    F.chartSpeed_range_subset_domain old hKtarget (by norm_num : (0 : ℝ) < 1)
  obtain ⟨Γ, hEL, hinit, hG⟩ := hF.exists_complete_tangentFamily_C2 hcomplete old 0
  let pos : (E × E) × ℝ → M := fun q ↦ Γ q.1 q.2
  have hp : ContinuousOn pos (chartEnergyDomain old ×ˢ univ) :=
    (contMDiffOn_positionFamily_of_tangentFamily hG).continuousOn
  let O := (chartEnergyDomain old ×ˢ univ) ∩
    pos ⁻¹' (extChartAt 𝓘(ℝ, E) old).source
  have hO : IsOpen O := hp.isOpen_inter_preimage
    ((isOpen_chartEnergyDomain old).prod isOpen_univ) (isOpen_extChartAt_source old)
  have hcentral : S ×ˢ ({0} : Set ℝ) ⊆ O := by
    rintro ⟨z, t⟩ ⟨hz, ht⟩
    have ht0 : t = 0 := ht
    subst t
    refine ⟨⟨hSD hz, mem_univ _⟩, ?_⟩
    have hb := congrArg TotalSpace.proj (hinit z (hSD hz))
    rw [tangentChart_symm_eq old (hSD hz).1 z.2] at hb
    change Γ z 0 = (extChartAt 𝓘(ℝ, E) old).symm z.1 at hb
    change Γ z 0 ∈ (extChartAt 𝓘(ℝ, E) old).source
    rw [hb]
    exact (extChartAt 𝓘(ℝ, E) old).map_target (hSD hz).1
  obtain ⟨U, V, hU, hV, hSU, h0V, hUV⟩ :=
    generalized_tube_lemma hS isCompact_singleton hO hcentral
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds (h0V (mem_singleton 0)))
  let τ := min (r / 2) ε
  have hτ : 0 < τ := lt_min (half_pos hr) hε
  have hτr : τ < r := (min_le_left _ _).trans_lt (half_lt_self hr)
  have hseg : Icc (-τ) 0 ⊆ ball (0 : ℝ) r := by
    intro t ht
    rw [mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  let phase : (E × E) × ℝ → E × E := fun q ↦
    ((extChartAt 𝓘(ℝ, E) old ∘ Γ q.1) q.2,
      deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ q.1) q.2)
  have hphase : ContDiffOn ℝ 2 phase O :=
    hF.contDiffOn_chartPhase_of_tangentFamily_C2 old
      (fun q hq ↦ hEL q.1 hq.1.1 q.2 (mem_univ _))
      (hG.mono inter_subset_left) (fun q hq ↦ hq.2)
  have hstrip : S ×ˢ Icc (-τ) 0 ⊆ O :=
    fun q hq ↦ hUV ⟨hSU hq.1, hrV (hseg hq.2)⟩
  let P := phase '' (S ×ˢ Icc (-τ) 0)
  have hPc : IsCompact P := (hS.prod isCompact_Icc).image_of_continuousOn
    (hphase.continuousOn.mono hstrip)
  have hPD : P ⊆ chartEnergyDomain old := by
    rintro p ⟨q, hq, rfl⟩
    exact (hF.chartTangent_of_isEulerLagrangeAt
      (hEL q.1 (hSD hq.1) q.2 (mem_univ _)) old (hstrip hq).2).2
  refine ⟨τ, ball (0 : ℝ) r, P, hτ, min_le_right _ _, isOpen_ball, hseg, hPc, hPD, ?_⟩
  intro c hc hunit hsource hbase
  let z := (extChartAt 𝓘(ℝ, E) old (c 0), deriv (extChartAt 𝓘(ℝ, E) old ∘ c) 0)
  obtain ⟨hz, hrep⟩ :=
    hF.eq_complete_family_of_isEulerLagrangeOn old hEL hinit hc hsource
  change z ∈ chartEnergyDomain old at hz
  change Γ z = c at hrep
  have hunitz : F.chartLength old z = 1 := by
    change F.toFun ((extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
      (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z) = 1
    rw [← hinit z hz, hrep]
    exact hunit
  have hzS : z ∈ S := ⟨hbase, by rw [hunitz]; norm_num⟩
  have hmap : MapsTo c (ball (0 : ℝ) r) (extChartAt 𝓘(ℝ, E) old).source := by
    intro t ht
    have h := (hUV (show (z, t) ∈ U ×ˢ V from ⟨hSU hzS, hrV ht⟩)).2
    change Γ z t ∈ (extChartAt 𝓘(ℝ, E) old).source at h
    rwa [hrep] at h
  refine ⟨hmap, ?_, ?_⟩
  · exact (contMDiffOn_extChartAt.comp
      (hF.contMDiffOn_of_isEulerLagrangeOn (hc.mono (subset_univ _)))
      (by
        intro t ht
        change c t ∈ (chartAt E old).source
        simpa only [extChartAt_source] using hmap ht)).contDiffOn
  · intro t ht
    refine ⟨(z, t), ⟨hzS, ht⟩, ?_⟩
    dsimp only [phase]
    rw [hrep]

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
