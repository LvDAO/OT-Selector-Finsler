import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedDistance
import OTSelector.Geometry.Finsler.DistanceGradientAlignment
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Topology.MetricSpace.SaturatedCalibration

/-!
# Geometry.Finsler.CalibratedPartnerCurve

* **Conditions:** A potential differentiable at a point with one nontrivial forward calibrated partner in complete Finsler geometry.
* **Objects:** One unique complete smooth unit curve reaching every forward calibrated partner at its original potential distance.
* **Proof detail:** Construct one original minimizing extension, identify all competing partner curves by the same initial potential covector and retain their individual segment isometries.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=29): Sections 4–4.1, Definition 4.2 and Proposition 4.3, p. 29; Lemma 4.5, pp. 30–31; Definition 4.6 and Lemma 4.8, pp. 31–32.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=61): Section 2.6, pp. 50–51, overlap uniqueness, equation (2.63), and Theorem 2.13 (unique maximal solution).

Source relation (derived): Derived from the cited geometric/analytic principles with the exact actual source hypotheses. The local construction and its original phase/covector data are retained, rather than asserted as a verbatim source statement.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerCalibratedPartnerCurve.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerCalibratedPartnerCurve`; the selected original proof blocks follow. -/
section

/-!
# One original complete curve through every calibrated forward partner

One nontrivial calibrated endpoint constructs a complete smooth unit Finsler
Euler--Lagrange curve from the original potential's differentiability point.
The same actual initial differential identifies the complete curve for every
other forward calibrated partner, even when the endpoint distances differ.
Every such segment is an original-distance isometry and has affine calibration.
The curve is constructed and unique; no curve decomposition is an assumption.
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

/-- One nontrivial forward calibrated partner determines a unique complete smooth
unit original geodesic containing every forward calibrated partner at its original
distance time, with actual metric isometry and calibration on each entire segment. -/
theorem existsUnique_complete_curve_of_forward_calibrated_partners
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {u : M → ℝ} (hu : let _instForwardPartnerLipMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {x y₀ : M} (hxy₀ : x ≠ y₀)
    (hsat₀ : let _instForwardPartnerSatMetric : MetricSpace M := F.metricSpace
      u y₀ - u x = dist x y₀)
    (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x) :
    let _instForwardPartnerOutputMetric : MetricSpace M := F.metricSpace
    ∃! g : ℝ → M, g 0 = x ∧ F.IsEulerLagrangeOn g univ ∧
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ g ∧
      (∀ t : ℝ, F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) g ⟨t, (1 : ℝ)⟩) = 1) ∧
      ∀ y : M, u y - u x = dist x y →
        g (dist x y) = y ∧ Isometry (fun t : Icc (0 : ℝ) (dist x y) ↦ g t) ∧
          ∀ t ∈ Icc (0 : ℝ) (dist x y), u (g t) = u x + t := by
  let _instForwardPartnerProofMetric : MetricSpace M := F.metricSpace
  let _instForwardPartnerProofENorm :
      ∀ z : M, ENorm (TangentSpace 𝓘(ℝ, E) z) := F.enorm
  obtain ⟨g, ⟨hg0, hgy₀, hgEL, hgsm, hgs, hgi, _⟩, _⟩ :=
    hF.existsUnique_complete_calibrated_minimizer hcomplete hu hxy₀ hsat₀ hdu
  have hdug : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (g 0) := by rwa [hg0]
  have hgsat : u (g (dist x y₀)) - u (g 0) = dist x y₀ - 0 := by
    simpa only [hgy₀, hg0, sub_zero] using hsat₀
  have hall : ∀ y : M, u y - u x = dist x y →
      g (dist x y) = y ∧ Isometry (fun t : Icc (0 : ℝ) (dist x y) ↦ g t) ∧
        ∀ t ∈ Icc (0 : ℝ) (dist x y), u (g t) = u x + t := by
    intro y hsat
    by_cases hxy : x = y
    · subst y
      refine ⟨by simpa only [dist_self] using hg0, ?_, ?_⟩
      · intro s t
        have hs : (s : ℝ) = 0 :=
          le_antisymm (by simpa only [dist_self] using s.2.2) s.2.1
        have ht : (t : ℝ) = 0 :=
          le_antisymm (by simpa only [dist_self] using t.2.2) t.2.1
        simp only [hs, ht, edist_self, Subtype.edist_eq]
      · intro t ht
        have ht0 : t = 0 :=
          le_antisymm (by simpa only [dist_self] using ht.2) ht.1
        simp only [ht0, hg0, add_zero]
    · obtain ⟨k, ⟨hk0, hky, hkEL, _, hks, hki, _⟩, _⟩ :=
        hF.existsUnique_complete_calibrated_minimizer hcomplete hu hxy hsat hdu
      have hksat : u (k (dist x y)) - u (k 0) = dist x y - 0 := by
        simpa only [hky, hk0, sub_zero] using hsat
      have hgk : g = k := hF.eq_of_complete_calibrated_initial_differential hu hu
        (dist_pos.mpr hxy₀) (dist_pos.mpr hxy) hgEL hkEL (hg0.trans hk0.symm)
        (hgs 0) (hks 0) hgi hki hgsat hksat hdug hdug rfl
      refine ⟨by rw [hgk]; exact hky, by rw [hgk]; exact hki, ?_⟩
      intro t ht
      have htcal := eq_affine_of_lipschitz_saturated_isometry hu hki hksat t ht
      simpa only [hgk, hk0, sub_zero] using htcal
  refine ⟨g, ⟨hg0, hgEL, hgsm, hgs, hall⟩, ?_⟩
  rintro k ⟨hk0, hkEL, _, hks, hkall⟩
  obtain ⟨hky₀, hki, _⟩ := hkall y₀ hsat₀
  have hduk : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (k 0) := by rwa [hk0]
  have hksat : u (k (dist x y₀)) - u (k 0) = dist x y₀ - 0 := by
    simpa only [hky₀, hk0, sub_zero] using hsat₀
  exact hF.eq_of_complete_calibrated_initial_differential hu hu
    (dist_pos.mpr hxy₀) (dist_pos.mpr hxy₀) hkEL hgEL (hk0.trans hg0.symm)
    (hks 0) (hgs 0) hki hgi hksat hgsat hduk hduk rfl

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
