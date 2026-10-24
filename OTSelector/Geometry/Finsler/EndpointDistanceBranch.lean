import OTSelector.Geometry.Finsler.AffineTime
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.ChartLipschitzCalibration
import OTSelector.Geometry.Finsler.EndpointInverse
import OTSelector.Geometry.Finsler.EndpointMinimizerStability
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.FlatBaseEndpoint
import OTSelector.Geometry.Finsler.Geodesic.ConstantSpeedDistance
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Energy
import OTSelector.Geometry.Finsler.LengthHessian
import OTSelector.Geometry.Finsler.LengthMetric

/-!
# Geometry.Finsler.EndpointDistanceBranch

* **Conditions:** A calibrated central segment, a genuine endpoint inverse and invertibility of the actual endpoint differential in complete Finsler geometry.
* **Objects:** An open branch on which original global distance equals the same-family path length/speed and is C2.
* **Proof detail:** Represent actual nearby fixed-time minimizers in the given complete family, confine all of them by stability and identify their states through the endpoint inverse.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=51): Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, p. 313: the length integral, induced distance and minimizing curves.
- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).

Source relation (derived): Distance-branch equality is proved from minimizer stability. C3 and second variation require later steps.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerEndpointDistanceBranch.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerEndpointDistanceBranch`; the selected original proof blocks follow. -/
section

/-!
# The original distance on an actual endpoint branch

Original fixed-time smooth minimizing segments are represented by the same complete
initial-state family. Stability places every such minimizing state in the constructed
endpoint inverse branch. Consequently the original global distance agrees with that
branch's actual path length and its constant-speed formula on an open endpoint domain.
This proves C2 regularity of the original coordinate distance on that domain.

Calibration of the central segment and invertibility of its actual endpoint derivative
remain explicit internal inputs. No distance-branch identity or nearby minimizer choice
is assumed, and neither a C3 estimate nor a second-variation formula is asserted here.
-/

open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- Near a calibrated nonconjugate minimizing segment, the original global distance
is the original length of the actual endpoint-inverse branch. The branch and its C2
coordinate distance are constructed from the same complete family and actual initial data. -/
theorem exists_calibrated_endpointDistanceBranch (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
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
    let Q : E × E → M × M := fun q ↦
      ((extChartAt 𝓘(ℝ, E) initial).symm q.1, (extChartAt 𝓘(ℝ, E) terminal).symm q.2)
    ∃ (e : OpenPartialHomeomorph (E × E) (E × E)) (W : Set (E × E)),
      (e : E × E → E × E) = chartEndpointMap terminal Γ b ∧
      z₀ ∈ e.source ∧ chartEndpointMap terminal Γ b z₀ ∈ W ∧
      e.source ⊆ chartEnergyDomain initial ∧
      ContDiffOn ℝ 2 e e.source ∧ ContDiffOn ℝ 2 e.symm e.target ∧
      IsOpen W ∧ W ⊆ e.target ∧
      W ⊆ (extChartAt 𝓘(ℝ, E) initial).target ×ˢ (extChartAt 𝓘(ℝ, E) terminal).target ∧
      (∀ q ∈ W, Γ (e.symm q) a = (Q q).1 ∧ Γ (e.symm q) b = (Q q).2 ∧
        F.lengthEDist (Q q).1 (Q q).2 =
          Manifold.pathELength 𝓘(ℝ, E) (Γ (e.symm q)) a b ∧
        (F.lengthEDist (Q q).1 (Q q).2).toReal =
          (F.chartLength initial (e.symm q) : ℝ) * (b - a)) ∧
      ContDiffOn ℝ 2 (fun q ↦ (F.lengthEDist (Q q).1 (Q q).2).toReal) W := by
  let : MetricSpace M := F.metricSpace
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  let Q : E × E → M × M := fun q ↦
    ((extChartAt 𝓘(ℝ, E) initial).symm q.1, (extChartAt 𝓘(ℝ, E) terminal).symm q.2)
  have hspeed (z : E × E) (hz : z ∈ chartEnergyDomain initial) (t : ℝ) :
      F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ z) ⟨t, (1 : ℝ)⟩) =
        F.chartLength initial z := by
    rw [hF.speed_eq_of_isEulerLagrangeOn (hEL z hz) isPreconnected_univ
      (mem_univ t) (mem_univ a), hinit z hz]
    rfl
  have hstart : Γ z₀ a = (extChartAt 𝓘(ℝ, E) initial).symm z₀.1 := by
    have hb := congrArg (fun v : TangentBundle 𝓘(ℝ, E) M ↦ v.1) (hinit z₀ hz₀)
    rw [tangentChart_symm_eq initial hz₀.1 z₀.2] at hb
    exact hb
  have hne : Γ z₀ a ≠ Γ z₀ b := by
    apply dist_pos.mp
    rw [F.dist_eq_mul_sub_of_constant_speed hab.le (fun t _ ↦ hspeed z₀ hz₀ t) hmin₀]
    exact mul_pos (NNReal.coe_pos.mpr (F.chartLength_pos initial hz₀)) (sub_pos.mpr hab)
  obtain ⟨e, V, he, hze, hzt, hsub, _, hf, hi, hV, hzV, hVN⟩ :=
    hF.exists_calibrated_endpointInverse_minimizers_subset initial terminal hab
      hEL hinit hG hz₀ hmin₀ hu hsat hdu hx hinv
  let B := (extChartAt 𝓘(ℝ, E) initial).target ×ˢ
    (extChartAt 𝓘(ℝ, E) terminal).target
  have hB : IsOpen B := (isOpen_extChartAt_target initial).prod
    (isOpen_extChartAt_target terminal)
  have hQ : ContinuousOn Q B :=
    ((continuousOn_extChartAt_symm initial).comp continuousOn_fst (fun _ hq ↦ hq.1)).prodMk
      ((continuousOn_extChartAt_symm terminal).comp continuousOn_snd (fun _ hq ↦ hq.2))
  let W := e.target ∩ (B ∩ Q ⁻¹' (V ∩ {p : M × M | p.1 ≠ p.2}))
  have hW : IsOpen W := e.open_target.inter
    (hQ.isOpen_inter_preimage hB (hV.inter (isOpen_ne_fun continuous_fst continuous_snd)))
  have hQB : Q (chartEndpointMap terminal Γ b z₀) = (Γ z₀ a, Γ z₀ b) := by
    apply Prod.ext
    · exact hstart.symm
    · exact (extChartAt 𝓘(ℝ, E) terminal).left_inv hx
  have hzW : chartEndpointMap terminal Γ b z₀ ∈ W := by
    refine ⟨hzt, ⟨hz₀.1, (extChartAt 𝓘(ℝ, E) terminal).map_source hx⟩, ?_⟩
    change Q (chartEndpointMap terminal Γ b z₀) ∈ V ∩ {p : M × M | p.1 ≠ p.2}
    rw [hQB]
    exact ⟨hzV, hne⟩
  have hbranch (q : E × E) (hq : q ∈ W) :
      Γ (e.symm q) a = (Q q).1 ∧ Γ (e.symm q) b = (Q q).2 ∧
      F.lengthEDist (Q q).1 (Q q).2 =
        Manifold.pathELength 𝓘(ℝ, E) (Γ (e.symm q)) a b := by
    obtain ⟨c, hca, hcb, hc, _, _, hmin⟩ :=
      hF.exists_smooth_lengthMetric_minimizer_fixedTime hcomplete hab hq.2.2.2
    have hsource : c a ∈ (extChartAt 𝓘(ℝ, E) initial).source := by
      rw [hca]
      exact (extChartAt 𝓘(ℝ, E) initial).map_target hq.2.1.1
    obtain ⟨hz, hrep⟩ := hF.eq_complete_family_of_isEulerLagrangeOn initial hEL hinit hc hsource
    let z := (extChartAt 𝓘(ℝ, E) initial (c a),
      deriv (extChartAt 𝓘(ℝ, E) initial ∘ c) a)
    have hp : chartEndpointMap terminal Γ b z = q := by
      apply Prod.ext
      · change extChartAt 𝓘(ℝ, E) initial (c a) = q.1
        rw [hca]
        exact (extChartAt 𝓘(ℝ, E) initial).right_inv hq.2.1.1
      · change extChartAt 𝓘(ℝ, E) terminal (Γ z b) = q.2
        rw [hrep, hcb]
        exact (extChartAt 𝓘(ℝ, E) terminal).right_inv hq.2.1.2
    have hminz : F.lengthEDist (Γ z a) (Γ z b) = Manifold.pathELength 𝓘(ℝ, E) (Γ z) a b := by
      rw [hrep]
      exact hmin a ⟨le_rfl, hab.le⟩ b ⟨hab.le, le_rfl⟩ hab.le
    have hv : (Γ z a, Γ z b) ∈ V := by
      rw [hrep, hca, hcb]
      exact hq.2.2.1
    have hin := (hVN z hz hv hminz).2.2
    rw [hp] at hin
    have hcurve : Γ (e.symm q) = c := hin ▸ hrep
    refine ⟨?_, ?_, ?_⟩
    · rw [hcurve]
      exact hca
    · rw [hcurve]
      exact hcb
    · rw [hcurve, ← hca, ← hcb]
      exact hmin a ⟨le_rfl, hab.le⟩ b ⟨hab.le, le_rfl⟩ hab.le
  have hformula (q : E × E) (hq : q ∈ W) :
      (F.lengthEDist (Q q).1 (Q q).2).toReal =
        (F.chartLength initial (e.symm q) : ℝ) * (b - a) := by
    rw [(hbranch q hq).2.2,
      F.pathELength_eq_of_constant_speed
        (fun t _ ↦ hspeed (e.symm q) (hsub (e.map_target hq.1)) t),
      ENNReal.toReal_mul, ENNReal.coe_toReal,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)]
  refine ⟨e, W, he, hze, hzW, hsub, hf, hi, hW, inter_subset_left,
    fun _ hq ↦ hq.2.1, fun q hq ↦ ⟨(hbranch q hq).1, (hbranch q hq).2.1,
      (hbranch q hq).2.2, hformula q hq⟩, ?_⟩
  have hsmooth : ContDiffOn ℝ 2
      (fun q ↦ (F.chartLength initial (e.symm q) : ℝ) * (b - a)) W :=
    (((hF.contDiffOn_chartLength initial).of_le (by simp)).comp (hi.mono inter_subset_left)
      (fun q hq ↦ hsub (e.map_target hq.1))).mul contDiffOn_const
  exact hsmooth.congr hformula

/-- An actual affine calibrated unit-velocity chart tube supplies endpoint
nonconjugacy and hence C2 regularity of the original coordinate distance. The covector
bound follows from the original global Lipschitz potential; neither it nor an invertible
endpoint derivative is an additional premise of this consumer. -/
theorem contDiffAt_endpointDistance_of_affine_calibrated_tube (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (old : M) {Γ : (E × E) → ℝ → M} {a b : ℝ} (hab : a < b)
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Γ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ z) ⟨a, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    (hG : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩)
      (chartEnergyDomain old ×ˢ univ))
    {z₀ : E × E} (hz₀ : z₀ ∈ chartEnergyDomain old)
    (hmin₀ : letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
      F.lengthEDist (Γ z₀ a) (Γ z₀ b) = Manifold.pathELength 𝓘(ℝ, E) (Γ z₀) a b)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hsat : letI : MetricSpace M := F.metricSpace
      u (Γ z₀ b) - u (Γ z₀ a) = dist (Γ z₀ a) (Γ z₀ b))
    (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (Γ z₀ a))
    (hx : ∀ t ∈ Icc a b, Γ z₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    {U : Set E} (hU : IsOpen U) (hsub : U ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    (p : E →L[ℝ] ℝ) {v₀ : E} (hp : p v₀ = 1)
    (hunit : ∀ x ∈ U, F.chartLength old (x, v₀) = 1) {C : ℝ}
    (heq : ∀ y ∈ U, u ((extChartAt 𝓘(ℝ, E) old).symm y) = p y + C)
    (hspace : ∀ t ∈ Icc a b, (extChartAt 𝓘(ℝ, E) old ∘ Γ z₀) t ∈ U)
    (hvelocity : ∀ t ∈ Icc a b, deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ z₀) t = v₀) :
    ContDiffAt ℝ 2 (fun q : E × E ↦
      (F.lengthEDist ((extChartAt 𝓘(ℝ, E) old).symm q.1)
        ((extChartAt 𝓘(ℝ, E) old).symm q.2)).toReal)
      (chartEndpointMap old Γ b z₀) := by
  have hinv := hF.isInvertible_chartEndpointMap_of_calibrated_tube old hab hEL hinit hG
    hz₀ hx hU hsub p hp hunit
    (fun x hx v ↦ hF.chart_covector_le_chartLength old hu hU hsub p heq hx v)
    hspace hvelocity
  obtain ⟨e, W, _, _, hzW, _, _, _, hW, _, _, _, hC2⟩ :=
    hF.exists_calibrated_endpointDistanceBranch hcomplete old old hab hEL hinit hG
      hz₀ hmin₀ hu hsat hdu (hx b ⟨hab.le, le_rfl⟩) hinv
  exact hC2.contDiffAt (hW.mem_nhds hzW)

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
