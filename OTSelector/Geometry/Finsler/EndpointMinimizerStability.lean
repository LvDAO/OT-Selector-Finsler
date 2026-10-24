import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedConstantSpeed
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.EndpointInverse
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Energy.Compact
import OTSelector.Geometry.Finsler.Geodesic.ConstantSpeedDistance
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Energy
import OTSelector.Geometry.Finsler.Geodesic.Uniqueness
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.TangentReadout
import OTSelector.Geometry.Manifold.TangentFamilyPosition

/-!
# Geometry.Finsler.EndpointMinimizerStability

* **Conditions:** A fixed actual complete family, compact speed layers and a unique central minimizing curve, with the stated open inverse neighborhood.
* **Objects:** Neighborhood control of every actual nearby minimizing initial state, including confinement to the existing endpoint branch.
* **Proof detail:** Apply compact-fiber upper semicontinuity to the actual endpoint/speed map, use central uniqueness to exclude outside states and recover all minimizing curves by their initial tangent.

Mathematical sources:
- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=61): Section 2.6, pp. 50–51, overlap uniqueness, equation (2.63), and Theorem 2.13 (unique maximal solution).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.

Source relation (derived): This is a compactness-and-uniqueness stability derivation, without a preselected nearby minimizer.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerEndpointMinimizerStability.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerEndpointMinimizerStability`; the selected original proof blocks follow. -/
section

/-!
# Stability of actual minimizing initial states near a unique endpoint branch

Compact original speed layers confine the initial states of nearby minimizing segments.
On these compact sets, continuity of the actual endpoints and speed transfers uniqueness
of the central minimizing curve to neighborhood control of every minimizing initial state.
The complete intrinsic family is kept fixed throughout the argument.
-/

open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry

/-- A compact continuous map has uniformly small inverse fibers near an isolated fiber. -/
theorem exists_open_preimage_subset_of_compact_fiber
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {K U : Set X} {T : X → Y} {y : Y} (hK : IsCompact K)
    (hT : ContinuousOn T K) (hU : IsOpen U)
    (hfiber : ∀ x ∈ K, T x = y → x ∈ U) :
    ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ ∀ x ∈ K, T x ∈ V → x ∈ U := by
  let C := T '' (K \ U)
  have hC : IsClosed C := ((hK.diff hU).image_of_continuousOn (hT.mono sdiff_subset)).isClosed
  refine ⟨Cᶜ, hC.isOpen_compl, ?_, ?_⟩
  · rintro ⟨x, hx, hxy⟩
    exact hx.2 (hfiber x hx.1 hxy)
  · intro x hx hxV
    by_contra hxU
    exact hxV ⟨x, ⟨hx, hxU⟩, rfl⟩

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

omit [FiniteDimensional ℝ E] [T2Space M] [PreconnectedSpace M] in
private theorem initial_position_of_tangent (initial : M)
    {Γ : (E × E) → ℝ → M} {a : ℝ} {z : E × E}
    (hz : z ∈ chartEnergyDomain initial)
    (hi : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ z) ⟨a, (1 : ℝ)⟩ =
      (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
        (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z) :
    Γ z a = (extChartAt 𝓘(ℝ, E) initial).symm z.1 := by
  have hb := congrArg (fun v : TangentBundle 𝓘(ℝ, E) M ↦ v.1) hi
  rw [tangentChart_symm_eq initial hz.1 z.2] at hb
  exact hb

omit [FiniteDimensional ℝ E] [T2Space M] [PreconnectedSpace M] in
private theorem family_speed (hF : F.IsSmoothStronglyConvex) (initial : M)
    {Γ : (E × E) → ℝ → M} {a : ℝ} {z : E × E}
    (_hz : z ∈ chartEnergyDomain initial) (hEL : F.IsEulerLagrangeOn (Γ z) univ)
    (hi : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ z) ⟨a, (1 : ℝ)⟩ =
      (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
        (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z) (t : ℝ) :
    F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ z) ⟨t, (1 : ℝ)⟩) =
      F.chartLength initial z := by
  rw [hF.speed_eq_of_isEulerLagrangeOn hEL isPreconnected_univ (mem_univ t) (mem_univ a), hi]
  rfl

/-- For a fixed actual complete family, uniqueness of the central globally minimizing
curve forces all nearby minimizing endpoint states into every prescribed initial-state
neighborhood. Original compact speed bounds are derived from their minimizing lengths. -/
theorem exists_endpoint_nhds_minimizers_subset (hF : F.IsSmoothStronglyConvex)
    (initial : M) {Γ : (E × E) → ℝ → M} {a b : ℝ} (hab : a < b)
    (hEL : ∀ z ∈ chartEnergyDomain initial, F.IsEulerLagrangeOn (Γ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain initial,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ z) ⟨a, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    (hG : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩)
      (chartEnergyDomain initial ×ˢ univ))
    {z₀ : E × E} (hz₀ : z₀ ∈ chartEnergyDomain initial)
    (hmin₀ : letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
      F.lengthEDist (Γ z₀ a) (Γ z₀ b) = Manifold.pathELength 𝓘(ℝ, E) (Γ z₀) a b)
    (hunique : letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
      ∀ z ∈ chartEnergyDomain initial, Γ z a = Γ z₀ a → Γ z b = Γ z₀ b →
        F.lengthEDist (Γ z a) (Γ z b) = Manifold.pathELength 𝓘(ℝ, E) (Γ z) a b →
        Γ z = Γ z₀)
    {N : Set (E × E)} (hN : IsOpen N) (hzN : z₀ ∈ N) :
    letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
    ∃ V : Set (M × M), IsOpen V ∧ (Γ z₀ a, Γ z₀ b) ∈ V ∧
      ∀ z ∈ chartEnergyDomain initial, (Γ z a, Γ z b) ∈ V →
        F.lengthEDist (Γ z a) (Γ z b) = Manifold.pathELength 𝓘(ℝ, E) (Γ z) a b → z ∈ N := by
  let : MetricSpace M := F.metricSpace
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  let S : E × E → ℝ := fun z ↦ (F.chartLength initial z : ℝ)
  let H : E × E → M × M := fun z ↦ (Γ z a, Γ z b)
  let T : E × E → (M × M) × ℝ := fun z ↦ (H z, S z)
  let L := dist (Γ z₀ a) (Γ z₀ b)
  have hd (z : E × E) (hz : z ∈ chartEnergyDomain initial)
      (hm : F.lengthEDist (Γ z a) (Γ z b) = Manifold.pathELength 𝓘(ℝ, E) (Γ z) a b) :
      dist (Γ z a) (Γ z b) = S z * (b - a) :=
    F.dist_eq_mul_sub_of_constant_speed hab.le
      (fun t _ ↦ hF.family_speed initial hz (hEL z hz) (hinit z hz) t) hm
  have hL : L = S z₀ * (b - a) := hd z₀ hz₀ hmin₀
  have hLpos : 0 < L := by
    rw [hL]
    exact mul_pos (NNReal.coe_pos.mpr (F.chartLength_pos initial hz₀)) (sub_pos.mpr hab)
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_extChartAt_target initial).mem_nhds hz₀.1)
  let R := r / 2
  have hR : 0 < R := half_pos hr
  have hbase : closedBall z₀.1 R ⊆ (extChartAt 𝓘(ℝ, E) initial).target :=
    (closedBall_subset_ball (by dsimp [R]; linarith)).trans hrsub
  let lo := L / (2 * (b - a))
  let hi := (L + 1) / (b - a)
  have hlo : 0 < lo := div_pos hLpos (mul_pos (by norm_num) (sub_pos.mpr hab))
  let K : Set (E × E) := {z | z.1 ∈ closedBall z₀.1 R ∧ S z ∈ Icc lo hi}
  have hK : IsCompact K :=
    F.isCompact_chartSpeed_range initial (isCompact_closedBall _ _) hbase lo hi
  have hKD : K ⊆ chartEnergyDomain initial :=
    F.chartSpeed_range_subset_domain initial hbase hlo
  have hpos (t : ℝ) : ContinuousOn (fun z ↦ Γ z t) (chartEnergyDomain initial) := by
    exact ((contMDiffOn_positionFamily_of_tangentFamily hG).comp
      (contDiffOn_id.prodMk contDiffOn_const).contMDiffOn
      (fun z hz ↦ ⟨hz, mem_univ _⟩)).continuousOn
  have hTK : ContinuousOn T K :=
    ((hpos a).mono hKD |>.prodMk ((hpos b).mono hKD)).prodMk
      ((NNReal.continuous_coe.comp_continuousOn (F.continuousOn_chartLength initial)).mono
        (fun z hz ↦ ⟨(hKD hz).1, mem_univ _⟩))
  have hfiber (z : E × E) (hz : z ∈ K) (heq : T z = T z₀) : z ∈ N := by
    have hstart : Γ z a = Γ z₀ a := congrArg (fun q ↦ q.1.1) heq
    have hend : Γ z b = Γ z₀ b := congrArg (fun q ↦ q.1.2) heq
    have hs : F.chartLength initial z = F.chartLength initial z₀ :=
      NNReal.coe_injective (congrArg Prod.snd heq)
    have hm : F.lengthEDist (Γ z a) (Γ z b) = Manifold.pathELength 𝓘(ℝ, E) (Γ z) a b := by
      rw [hstart, hend, hmin₀,
        F.pathELength_eq_of_constant_speed
          (fun t _ ↦ hF.family_speed initial hz₀ (hEL z₀ hz₀) (hinit z₀ hz₀) t),
        F.pathELength_eq_of_constant_speed
          (fun t _ ↦ hF.family_speed initial (hKD hz) (hEL z (hKD hz)) (hinit z (hKD hz)) t), hs]
    have hc := hunique z (hKD hz) hstart hend hm
    have ht := (hinit z (hKD hz)).symm.trans
      ((congrArg (fun c ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨a, (1 : ℝ)⟩) hc).trans
        (hinit z₀ hz₀))
    have hzEq : z = z₀ := by
      apply (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
        (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm.injOn
      · change _ ∈ (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).target
        rw [tangentChart_target]
        exact ⟨(hKD hz).1, mem_univ _⟩
      · change _ ∈ (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).target
        rw [tangentChart_target]
        exact ⟨hz₀.1, mem_univ _⟩
      · exact ht
    exact hzEq ▸ hzN
  obtain ⟨V₀, hV₀, htV₀, hV₀sub⟩ :=
    exists_open_preimage_subset_of_compact_fiber hK hTK hN hfiber
  let J : M × M → (M × M) × ℝ := fun q ↦ (q, dist q.1 q.2 / (b - a))
  have hJ : Continuous J := continuous_id.prodMk
    ((continuous_fst.dist continuous_snd).div_const (b - a))
  have hj₀ : J (H z₀) = T z₀ := by
    apply Prod.ext
    · rfl
    change L / (b - a) = S z₀
    rw [hL, mul_div_cancel_right₀ _ (sub_ne_zero.mpr hab.ne')]
  have hstart₀ := initial_position_of_tangent initial hz₀ (hinit z₀ hz₀)
  have hsrc₀ : Γ z₀ a ∈ (extChartAt 𝓘(ℝ, E) initial).source := by
    rw [hstart₀]
    exact (extChartAt 𝓘(ℝ, E) initial).map_target hz₀.1
  have hcoord₀ : extChartAt 𝓘(ℝ, E) initial (Γ z₀ a) = z₀.1 := by
    rw [hstart₀, (extChartAt 𝓘(ℝ, E) initial).right_inv hz₀.1]
  have hnbase : ∀ᶠ q : M × M in 𝓝 (H z₀),
      extChartAt 𝓘(ℝ, E) initial q.1 ∈ ball z₀.1 R := by
    have hc : ContinuousAt (fun q : M × M ↦ extChartAt 𝓘(ℝ, E) initial q.1) (H z₀) :=
      ((continuousOn_extChartAt initial).continuousAt
        ((isOpen_extChartAt_source initial).mem_nhds hsrc₀)).comp (f := Prod.fst)
          continuousAt_fst
    apply hc.preimage_mem_nhds
    rw [hcoord₀]
    exact ball_mem_nhds _ hR
  have hndist : ∀ᶠ q : M × M in 𝓝 (H z₀), dist q.1 q.2 ∈ Ioo (L / 2) (L + 1) :=
    (continuous_fst.dist continuous_snd).continuousAt.preimage_mem_nhds
      (Ioo_mem_nhds (by dsimp [H]; change L / 2 < L; linarith)
        (by dsimp [H]; change L < L + 1; linarith))
  have hnJ : J ⁻¹' V₀ ∈ 𝓝 (H z₀) := hJ.continuousAt.preimage_mem_nhds
    (hV₀.mem_nhds (hj₀.symm ▸ htV₀))
  obtain ⟨V, hVsub, hV, hzV⟩ := _root_.mem_nhds_iff.mp (inter_mem hnJ (inter_mem hnbase hndist))
  refine ⟨V, hV, hzV, ?_⟩
  intro z hz hzV hm
  have hbounds := hVsub hzV
  have hdist := hd z hz hm
  have hs : S z = dist (Γ z a) (Γ z b) / (b - a) := by
    rw [hdist, mul_div_cancel_right₀ _ (sub_ne_zero.mpr hab.ne')]
  have hzK : z ∈ K := by
    refine ⟨?_, ?_, ?_⟩
    · have hcoord : extChartAt 𝓘(ℝ, E) initial (Γ z a) = z.1 := by
        rw [initial_position_of_tangent initial hz (hinit z hz),
          (extChartAt 𝓘(ℝ, E) initial).right_inv hz.1]
      exact ball_subset_closedBall (hcoord ▸ hbounds.2.1)
    · dsimp only [lo]
      rw [hs, div_mul_eq_div_div]
      exact div_le_div_of_nonneg_right hbounds.2.2.1.le (sub_nonneg.mpr hab.le)
    · dsimp only [hi]
      rw [hs]
      exact div_le_div_of_nonneg_right hbounds.2.2.2.le (sub_nonneg.mpr hab.le)
  apply hV₀sub z hzK
  have hj : J (H z) = T z := Prod.ext rfl hs.symm
  exact hj ▸ hbounds.1

omit [PreconnectedSpace M] in
/-- The complete family prescribed on every slit chart state represents every complete
intrinsic Euler--Lagrange curve whose actual initial position lies in that chart. -/
theorem eq_complete_family_of_isEulerLagrangeOn (hF : F.IsSmoothStronglyConvex)
    (initial : M) {Γ : (E × E) → ℝ → M} {a : ℝ}
    (hEL : ∀ z ∈ chartEnergyDomain initial, F.IsEulerLagrangeOn (Γ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain initial,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ z) ⟨a, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    {c : ℝ → M} (hc : F.IsEulerLagrangeOn c univ)
    (hsource : c a ∈ (extChartAt 𝓘(ℝ, E) initial).source) :
    let z := (extChartAt 𝓘(ℝ, E) initial (c a),
      deriv (extChartAt 𝓘(ℝ, E) initial ∘ c) a)
    z ∈ chartEnergyDomain initial ∧ Γ z = c := by
  let z := (extChartAt 𝓘(ℝ, E) initial (c a),
    deriv (extChartAt 𝓘(ℝ, E) initial ∘ c) a)
  have hread := hF.chartTangent_of_isEulerLagrangeAt (hc a (mem_univ _)) initial hsource
  have hsrc : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨a, (1 : ℝ)⟩ ∈
      (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
        (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).source := by
    simpa only [extChartAt_source, FiberBundle.chartedSpace_chartAt, mfld_simps] using hsource
  have hi : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ z) ⟨a, (1 : ℝ)⟩ =
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨a, (1 : ℝ)⟩ := by
    rw [hinit z hread.2]
    exact (congrArg (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
      (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm hread.1).symm.trans
        ((extChartAt _ _).left_inv hsrc)
  refine ⟨hread.2, funext (fun t ↦ ?_)⟩
  exact hF.eqOn_of_isEulerLagrangeOn isOpen_univ isPreconnected_univ
    (hEL z hread.2) hc (mem_univ a) hi (mem_univ t)

/-- A calibrated central minimizing segment with invertible actual endpoint differential
constructs a C2 endpoint branch containing every nearby globally minimizing initial state
of the same complete family. Calibration derives central uniqueness; compact original
speed layers derive stability, with no supplied inverse or distance-branch identity. -/
theorem exists_calibrated_endpointInverse_minimizers_subset (hF : F.IsSmoothStronglyConvex)
    (initial terminal : M) {Γ : (E × E) → ℝ → M} {a b : ℝ} (hab : a < b)
    (hEL : ∀ z ∈ chartEnergyDomain initial, F.IsEulerLagrangeOn (Γ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain initial,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ z) ⟨a, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    (hG : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩)
      (chartEnergyDomain initial ×ˢ univ))
    {z₀ : E × E} (hz₀ : z₀ ∈ chartEnergyDomain initial)
    (hmin₀ : letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
      F.lengthEDist (Γ z₀ a) (Γ z₀ b) = Manifold.pathELength 𝓘(ℝ, E) (Γ z₀) a b)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hsat : letI : MetricSpace M := F.metricSpace
      u (Γ z₀ b) - u (Γ z₀ a) = dist (Γ z₀ a) (Γ z₀ b))
    (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (Γ z₀ a))
    (hx : Γ z₀ b ∈ (extChartAt 𝓘(ℝ, E) terminal).source)
    (hinv : (fderiv ℝ (chartEndpointMap terminal Γ b) z₀).IsInvertible) :
    letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
    ∃ (e : OpenPartialHomeomorph (E × E) (E × E)) (V : Set (M × M)),
      (e : E × E → E × E) = chartEndpointMap terminal Γ b ∧
      z₀ ∈ e.source ∧ chartEndpointMap terminal Γ b z₀ ∈ e.target ∧
      e.source ⊆ chartEnergyDomain initial ∧
      (∀ z ∈ e.source, Γ z b ∈ (extChartAt 𝓘(ℝ, E) terminal).source) ∧
      ContDiffOn ℝ 2 e e.source ∧ ContDiffOn ℝ 2 e.symm e.target ∧
      IsOpen V ∧ (Γ z₀ a, Γ z₀ b) ∈ V ∧
      ∀ z ∈ chartEnergyDomain initial, (Γ z a, Γ z b) ∈ V →
        F.lengthEDist (Γ z a) (Γ z b) = Manifold.pathELength 𝓘(ℝ, E) (Γ z) a b →
        z ∈ e.source ∧ chartEndpointMap terminal Γ b z ∈ e.target ∧
          e.symm (chartEndpointMap terminal Γ b z) = z := by
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  obtain ⟨e, he, hze, hzt, hsub, _, hmap, hf, hi, _⟩ :=
    exists_chartEndpointInverse initial terminal (isOpen_chartEnergyDomain initial)
      Subset.rfl hG hz₀ b hx hinv
  have huniq (z : E × E) (hz : z ∈ chartEnergyDomain initial)
      (hstart : Γ z a = Γ z₀ a) (hend : Γ z b = Γ z₀ b)
      (hm : F.lengthEDist (Γ z a) (Γ z b) = Manifold.pathELength 𝓘(ℝ, E) (Γ z) a b) :
      Γ z = Γ z₀ :=
    (hF.eq_of_complete_calibrated_minimizers hu hab (hEL z₀ hz₀) (hEL z hz)
      hstart.symm hend.symm hmin₀ hm hsat hdu).symm
  obtain ⟨V, hV, hzV, hVN⟩ := hF.exists_endpoint_nhds_minimizers_subset initial hab
    hEL hinit hG hz₀ hmin₀ huniq e.open_source hze
  refine ⟨e, V, he, hze, hzt, hsub, hmap, hf, hi, hV, hzV, ?_⟩
  intro z hz hv hm
  have hs := hVN z hz hv hm
  refine ⟨hs, ?_, ?_⟩
  · rw [← he]
    exact e.map_source hs
  · rw [← he]
    exact e.left_inv hs

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
end
