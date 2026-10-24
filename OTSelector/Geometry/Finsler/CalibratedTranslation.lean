import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.AffineTime
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedDistance
import OTSelector.Geometry.Finsler.CalibratedIntervalCovector
import OTSelector.Geometry.Finsler.CalibratedPartnerOrientation
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.Geodesic.ConstantSpeedDistance
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.ManifoldTubeCalibration
import OTSelector.Geometry.Finsler.TangentReadout
import OTSelector.Topology.MetricSpace.SaturatedCalibration

/-!
# Geometry.Finsler.CalibratedTranslation

* **Conditions:** The actual initial chart momentum equals the original potential differential and the core has two calibrated partners at a common positive reach.
* **Objects:** The same complete curve has unit speed, exact original potential clock, isometry and calibration on the whole closed trim.
* **Proof detail:** Identify its intrinsic covector and both partner minimizers by actual Legendre injectivity and complete-solution uniqueness.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=29): Sections 4–4.1, Definition 4.2 and Proposition 4.3, p. 29; Lemma 4.5, pp. 30–31; Definition 4.6 and Lemma 4.8, pp. 31–32.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=61): Section 2.6, pp. 50–51, overlap uniqueness, equation (2.63), and Theorem 2.13 (unique maximal solution).

Source relation (derived): Derived from the cited geometric/analytic principles with the exact actual source hypotheses. The local construction and its original phase/covector data are retained, rather than asserted as a verbatim source statement.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerCalibratedTranslation.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerCalibratedTranslation`; the selected original proof blocks follow. -/
section

/-!
# The original potential clock on actual calibrated translations

The original two-sided calibrated partners determine both halves of the same
complete energy Euler--Lagrange curve. An actual initial potential momentum
identifies that curve by Legendre injectivity and intrinsic uniqueness. Its
original speed is one and its potential grows exactly by elapsed time throughout
the closed trimmed interval.
-/

open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

omit [T2Space M] [PreconnectedSpace M] in
private theorem intrinsic_covector_of_actual_chartMomentum
    (hF : F.IsSmoothStronglyConvex) {c : ℝ → M} {t : ℝ}
    (hc : F.IsEulerLagrangeAt c t) (old : M)
    (hx : c t ∈ (extChartAt 𝓘(ℝ, E) old).source) {u : M → ℝ}
    (hd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c t))
    (hp : fiberLegendre (F.chartEnergy old)
      (extChartAt 𝓘(ℝ, E) old (c t), deriv (extChartAt 𝓘(ℝ, E) old ∘ c) t) =
        fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (extChartAt 𝓘(ℝ, E) old (c t))) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1 ≠ 0 ∧
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c t) =
        fderiv ℝ (F.fiberEnergy (c t)) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1) := by
  let instActualCovectorFiberNorm : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) (c t)) :=
    inferInstanceAs (NormedAddCommGroup E)
  let instActualCovectorFiberSpace : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) (c t)) :=
    inferInstanceAs (NormedSpace ℝ E)
  let e := extChartAt 𝓘(ℝ, E) old
  let v := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1
  let D := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e (c t)
  have hcDiff := (hF.contMDiffAt_of_isEulerLagrangeAt hc).mdifferentiableAt (by simp)
  have hchart : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) e (c t) :=
    mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hx)
  have hvel : deriv (e ∘ c) t = D v := by
    have h := mfderiv_comp_apply t hchart hcDiff (1 : ℝ)
    rw [mfderiv_eq_fderiv] at h
    exact (fderiv_apply_one_eq_deriv (𝕜 := ℝ)).symm.trans h
  have hz : (e (c t), D v) ∈ chartEnergyDomain old := by
    have h := (hF.chartTangent_of_isEulerLagrangeAt hc old hx).2
    change (e (c t), deriv (e ∘ c) t) ∈ chartEnergyDomain old at h
    rwa [hvel] at h
  have hv : v ≠ 0 := fun hv ↦ hz.2 (by rw [hv, _root_.map_zero])
  have hi : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e (c t)) := by
    simpa only [modelWithCornersSelf_coe, range_id, mdifferentiableWithinAt_univ] using
      mdifferentiableWithinAt_extChartAt_symm (e.map_source hx)
  have hdi : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (e.symm (e (c t))) := by
    rwa [e.left_inv hx]
  have hinv : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e (c t))).comp D =
      ContinuousLinearMap.id ℝ _ := by
    simpa only [modelWithCornersSelf_coe, range_id, mfderivWithin_univ] using
      mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hx
  have hchain : (fderiv ℝ (u ∘ e.symm) (e (c t))).comp D =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c t) := by
    rw [← mfderiv_eq_fderiv, mfderiv_comp (e (c t)) hdi hi,
      ContinuousLinearMap.comp_assoc, hinv, ContinuousLinearMap.comp_id, e.left_inv hx]
  have hm := hF.chartEnergy_fderiv_comp_mfderiv old hx v hz
  change (fiberLegendre (F.chartEnergy old) (e (c t), D v)).comp D = _ at hm
  have hmomentum : fiberLegendre (F.chartEnergy old) (e (c t), D v) =
      fderiv ℝ (u ∘ e.symm) (e (c t)) := by
    change fiberLegendre (F.chartEnergy old) (e (c t), deriv (e ∘ c) t) = _ at hp
    rwa [hvel] at hp
  rw [hmomentum] at hm
  exact ⟨hv, hchain.symm.trans hm⟩


private theorem exists_unit_isometric_minimizer_fixedTime (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {a b : ℝ} (hab : a < b) {x y : M}
    (hdist : let _instFixedUnitMetric : MetricSpace M := F.metricSpace
      dist x y = b - a) :
    let _instFixedUnitMetric : MetricSpace M := F.metricSpace
    ∃ c : ℝ → M, c a = x ∧ c b = y ∧ F.IsEulerLagrangeOn c univ ∧
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ c ∧
      (∀ t : ℝ, F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) = 1) ∧
      Isometry (fun t : Icc a b ↦ c t) := by
  let _instFixedUnitMetric : MetricSpace M := F.metricSpace
  let _instFixedUnitENorm : ∀ z : M, ENorm (TangentSpace 𝓘(ℝ, E) z) := F.enorm
  have hxy : x ≠ y := dist_pos.mp (by rw [hdist]; exact sub_pos.mpr hab)
  obtain ⟨c, hc0, hc1, hcEL, hcsm, hcspeed, hmin⟩ :=
    hF.exists_smooth_lengthMetric_minimizer_fixedTime hcomplete hab hxy
  have hunit (t : ℝ) :
      F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) = 1 := by
    apply NNReal.coe_injective
    simpa only [hdist, div_self (sub_pos.mpr hab).ne', NNReal.coe_one] using hcspeed t
  refine ⟨c, hc0, hc1, hcEL, hcsm, hunit, ?_⟩
  apply isometry_iff_dist_eq.mpr
  intro s t
  have hordered (r : ℝ) (hr : r ∈ Icc a b) (q : ℝ) (hq : q ∈ Icc a b)
      (hrq : r ≤ q) : dist (c r) (c q) = q - r := by
    have hh := F.dist_eq_mul_sub_of_constant_speed (s := 1) hrq
      (fun t _ ↦ hunit t) (hmin r hr q hq hrq)
    simpa only [NNReal.coe_one, one_mul] using hh
  change dist (c s) (c t) = dist (s : ℝ) (t : ℝ)
  rcases le_total (s : ℝ) (t : ℝ) with hst | hts
  · rw [hordered s s.property t t.property hst, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr hst)]
    ring
  · rw [dist_comm (c s), hordered t t.property s s.property hts,
      Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hts)]

private theorem translation_of_initial_fiberEnergy_covector
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {u : M → ℝ} (hu : let _instTranslationLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {c : ℝ → M} (hc : F.IsEulerLagrangeOn c univ)
    (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c 0))
    (hv : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c 0 1 ≠ 0)
    (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c 0) =
      fderiv ℝ (F.fiberEnergy (c 0)) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c 0 1))
    {δ : ℝ} (hδ : 0 < δ) {a b : M}
    (ha : let _instTranslationPre : MetricSpace M := F.metricSpace
      dist a (c 0) = δ ∧ u (c 0) - u a = δ)
    (hb : let _instTranslationPost : MetricSpace M := F.metricSpace
      dist (c 0) b = δ ∧ u b - u (c 0) = δ) :
    let _instTranslationResult : MetricSpace M := F.metricSpace
    (∀ t : ℝ, F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) = 1) ∧
      c (-δ) = a ∧ c δ = b ∧
      (∀ t ∈ Icc (-δ) δ, u (c t) = u (c 0) + t) ∧
      Isometry (fun t : Icc (-δ) δ ↦ c t) := by
  let _instTranslationResult : MetricSpace M := F.metricSpace
  obtain ⟨g, hga, hg0, hgEL, hgsm, hgs, hgi⟩ :=
    exists_unit_isometric_minimizer_fixedTime hF hcomplete
      (a := -δ) (b := 0) (by linarith) (x := a) (y := c 0)
      (by simpa only [zero_sub, neg_neg] using ha.1)
  obtain ⟨k, hk0, hkb, hkEL, hksm, hks, hki⟩ :=
    exists_unit_isometric_minimizer_fixedTime hF hcomplete
      (a := 0) (b := δ) hδ (x := c 0) (y := b)
      (by simpa only [sub_zero] using hb.1)
  have hgsat : u (g 0) - u (g (-δ)) = 0 - -δ := by
    rw [hg0, hga, zero_sub, neg_neg]
    exact ha.2
  have hksat : u (k δ) - u (k 0) = δ - 0 := by
    rw [hk0, hkb, sub_zero]
    exact hb.2
  have hn (d : ℝ → M)
      (hd : F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨0, (1 : ℝ)⟩) = 1) :
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d 0 1 ≠ 0 := by
    intro hz
    change F.toFun ⟨d 0, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d 0 1⟩ = 1 at hd
    rw [hz, F.map_zero] at hd
    exact zero_ne_one hd
  have hgp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (g 0) =
      fderiv ℝ (F.fiberEnergy (g 0)) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) g 0 1) :=
    hF.mfderiv_eq_fiberEnergy_of_calibrated_closedInterval hu (by linarith)
      hgi hgsat (right_mem_Icc.mpr (by linarith))
      (hgsm.mdifferentiable (by simp) 0) (hgs 0) (by rwa [hg0])
  have hkp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (k 0) =
      fderiv ℝ (F.fiberEnergy (k 0)) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) k 0 1) :=
    hF.mfderiv_eq_fiberEnergy_of_calibrated_closedInterval hu hδ
      hki hksat (left_mem_Icc.mpr hδ.le)
      (hksm.mdifferentiable (by simp) 0) (hks 0) (by rwa [hk0])
  have hcg : c = g := hF.eq_of_complete_initial_fiberEnergy_covector
    hc hgEL rfl hg0 hv (hn g (hgs 0)) hp hgp
  have hck : c = k := hF.eq_of_complete_initial_fiberEnergy_covector
    hc hkEL rfl hk0 hv (hn k (hks 0)) hp hkp
  have hclock : ∀ t ∈ Icc (-δ) δ, u (c t) = u (c 0) + t := by
    intro t ht
    rcases le_total t 0 with ht0 | h0t
    · have hh := eq_affine_of_lipschitz_saturated_isometry hu hgi hgsat t ⟨ht.1, ht0⟩
      rw [hga, ← hcg] at hh
      linarith [ha.2]
    · have hh := eq_affine_of_lipschitz_saturated_isometry hu hki hksat t ⟨h0t, ht.2⟩
      simpa only [← hck, sub_zero] using hh
  have hunit : ∀ t : ℝ,
      F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) = 1 := by
    simpa only [hck] using hks
  refine ⟨hunit, by rw [hcg]; exact hga, by rw [hck]; exact hkb, hclock, ?_⟩
  apply F.isometry_Icc_of_unitSpeed_calibration hu
    ((hck ▸ hksm).of_le (by simp)).contMDiffOn
    (fun t _ ↦ hunit t)
  intro t ht
  simpa only [add_comm] using hclock t ht

/-- Actual initial chart momentum equal to the original potential differential forces
unit speed and the exact potential clock throughout the original two-sided trimmed
calibrated interval. The whole segment preserves the original length distance. -/
theorem calibrated_translation_of_chartMomentum (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {u : M → ℝ} (hu : let _instChartTranslationLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {Γ : E → ℝ → M} {x : E} (hx : x ∈ (extChartAt 𝓘(ℝ, E) old).target)
    (hEL : F.IsEulerLagrangeOn (Γ x) univ)
    (hinit : Γ x 0 = (extChartAt 𝓘(ℝ, E) old).symm x)
    (hmomentum : F.chartMomentumFamily old Γ (x, 0) =
      (x, fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) x))
    (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u ((extChartAt 𝓘(ℝ, E) old).symm x))
    {δ : ℝ} (hδ : 0 < δ) {a b : M}
    (ha : let _instChartTranslationPre : MetricSpace M := F.metricSpace
      dist a ((extChartAt 𝓘(ℝ, E) old).symm x) = δ ∧
        u ((extChartAt 𝓘(ℝ, E) old).symm x) - u a = δ)
    (hb : let _instChartTranslationPost : MetricSpace M := F.metricSpace
      dist ((extChartAt 𝓘(ℝ, E) old).symm x) b = δ ∧
        u b - u ((extChartAt 𝓘(ℝ, E) old).symm x) = δ) :
    let _instChartTranslationResult : MetricSpace M := F.metricSpace
    (∀ t : ℝ, F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ x) ⟨t, (1 : ℝ)⟩) = 1) ∧
      Γ x (-δ) = a ∧ Γ x δ = b ∧
      (∀ t ∈ Icc (-δ) δ,
        u (Γ x t) = u ((extChartAt 𝓘(ℝ, E) old).symm x) + t) ∧
      Isometry (fun t : Icc (-δ) δ ↦ Γ x t) ∧
      ∀ t ∈ Icc (-δ) δ,
        |u (Γ x t) - u ((extChartAt 𝓘(ℝ, E) old).symm x)| =
          dist ((extChartAt 𝓘(ℝ, E) old).symm x) (Γ x t) := by
  let _instChartTranslationResult : MetricSpace M := F.metricSpace
  have hsource : Γ x 0 ∈ (extChartAt 𝓘(ℝ, E) old).source := by
    rw [hinit]
    exact (extChartAt 𝓘(ℝ, E) old).map_target hx
  have hbase : extChartAt 𝓘(ℝ, E) old (Γ x 0) = x := by
    rw [hinit]
    exact (extChartAt 𝓘(ℝ, E) old).right_inv hx
  have hp := congrArg Prod.snd hmomentum
  change fiberLegendre (F.chartEnergy old)
    (extChartAt 𝓘(ℝ, E) old (Γ x 0), deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ x) 0) =
      fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) x at hp
  have hdu0 : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (Γ x 0) := by rwa [hinit]
  obtain ⟨hv, hcov⟩ := intrinsic_covector_of_actual_chartMomentum hF (hEL 0 (mem_univ _)) old hsource hdu0 (by simpa only [hbase] using hp)
  obtain ⟨hunit, hendA, hendB, hclock, hiso⟩ :=
    translation_of_initial_fiberEnergy_covector hF hcomplete hu hEL hdu0 hv hcov hδ
      (by simpa only [hinit] using ha) (by simpa only [hinit] using hb)
  refine ⟨hunit, hendA, hendB, ?_, hiso, ?_⟩
  · simpa only [hinit] using hclock
  · intro t ht
    have hd := hiso.dist_eq ⟨0, by constructor <;> linarith⟩ ⟨t, ht⟩
    change dist (Γ x 0) (Γ x t) = dist (0 : ℝ) t at hd
    rw [hinit, Real.dist_eq, zero_sub, abs_neg] at hd
    rw [← hinit, hclock t ht, add_sub_cancel_left]
    simpa only [hinit] using hd.symm

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
