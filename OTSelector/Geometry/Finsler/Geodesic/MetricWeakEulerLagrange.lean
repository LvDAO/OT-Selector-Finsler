import OTSelector.Analysis.Calculus.Variational.LipschitzFirstVariation
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Energy.ChartActionAE
import OTSelector.Geometry.Finsler.Geodesic.MetricMinimizerComparison
import OTSelector.Geometry.Finsler.Geodesic.MinimizerChartPhase
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.Variation.First
import OTSelector.Geometry.Finsler.Variation.Lipschitz
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerMetricWeakEL.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerMetricWeakEL`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Geodesic.MetricWeakEulerLagrange

* **Conditions:** A smooth strongly convex finite-dimensional Finsler norm and an original-distance isometric interval, at an interior time.
* **Objects:** A local weak Euler–Lagrange integral identity against every C1 additive perturbation vanishing at the local endpoints.
* **Proof detail:** Construct a compact slit phase and admissible Lipschitz competitors, differentiate the coordinate action under an integrable bound, and set its derivative to zero by actual energy minimality.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=107): Section 3B, Theorem 3.31, p. 92 (Dominated Convergence).
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): A weak first-variation proof leading to the classical smooth-geodesic characterization; the source geodesic criterion does not replace the AE and admissibility arguments.
-/

/-!
# Weak Euler--Lagrange identity for original-distance minimizing intervals

Every interior point of an original Finsler-distance isometric interval has genuine
coordinates in which the unintegrated first variation vanishes for every C1 additive
perturbation fixing the local time endpoints. Local coordinate regularity, compact
slit phase containment, and admissible original-metric Lipschitz competitors are all
constructed from the isometry. No classical Euler--Lagrange or smooth-center premise
is supplied.
-/

open Set Filter Metric Manifold MeasureTheory
open scoped Topology ContDiff NNReal

noncomputable section

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

set_option backward.isDefEq.respectTransparency false in
/-- An actual original-distance isometric interval satisfies the local weak
Euler--Lagrange identity against every C1 variation vanishing at the local endpoints. -/
theorem exists_chart_weak_eulerLagrange_of_isometric_interval (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (hiso : letI : MetricSpace M := F.metricSpace
      Isometry (fun t : Icc a b ↦ c t)) :
    let χ := extChartAt 𝓘(ℝ, E) (c t₀)
    let x := χ ∘ c
    ∃ δ > (0 : ℝ), Icc (t₀ - δ) (t₀ + δ) ⊆ Ioo a b ∧
      MapsTo c (Icc (t₀ - δ) (t₀ + δ)) χ.source ∧
      ∀ η : ℝ → E, ContDiff ℝ 1 η → η (t₀ - δ) = 0 → η (t₀ + δ) = 0 →
        (∫ t in (t₀ - δ)..(t₀ + δ),
          baseEnergyDifferential (F.chartEnergy (c t₀)) (x t, deriv x t) (η t) +
            fiberLegendre (F.chartEnergy (c t₀)) (x t, deriv x t) (deriv η t)) = 0 := by
  let : MetricSpace M := F.metricSpace
  let χ := extChartAt 𝓘(ℝ, E) (c t₀)
  let x : ℝ → E := χ ∘ c
  obtain ⟨δ, hδ, r, hr, Kx, Kinv, P, hsub, hsource, hxball, hxLip,
      htarget, hinv, hP, hPU, hphase⟩ :=
    hF.exists_compact_chartPhase_of_isometric_interval ht₀ hiso
  have hab : t₀ - δ ≤ t₀ + δ := by linarith
  have hisolocal : Isometry (fun t : Icc (t₀ - δ) (t₀ + δ) ↦ c t) := by
    intro u v
    exact hiso.edist_eq ⟨u, Ioo_subset_Icc_self (hsub u.property)⟩
      ⟨v, Ioo_subset_Icc_self (hsub v.property)⟩
  have hdiff : ∀ᵐ t ∂volume.restrict (Ioo (t₀ - δ) (t₀ + δ)),
      DifferentiableAt ℝ x t := by
    have hwithin := (hxLip.mono Ioo_subset_Icc_self).ae_differentiableWithinAt
      (μ := volume) measurableSet_Ioo
    filter_upwards [hwithin, ae_restrict_mem measurableSet_Ioo] with t ht htin
    exact ht.differentiableAt (isOpen_Ioo.mem_nhds htin)
  have hdiff' : ∀ᵐ t ∂volume.restrict (uIoc (t₀ - δ) (t₀ + δ)),
      DifferentiableAt ℝ x t := by
    rw [uIoc_of_le hab, ← restrict_Ioo_eq_restrict_Ioc]
    exact hdiff
  have hsource' : MapsTo c (uIcc (t₀ - δ) (t₀ + δ)) χ.source := by
    simpa only [uIcc_of_le hab] using hsource
  refine ⟨δ, hδ, hsub, hsource, ?_⟩
  intro η hη hηa hηb
  obtain ⟨Kη, hηLip⟩ := exists_lipschitzOnWith_Icc_of_contDiff hη (t₀ - δ) (t₀ + δ)
  obtain ⟨ε, hε, hvariation⟩ := F.exists_lipschitz_chart_add_variations (c t₀)
    hr htarget hinv hxball hxLip hηLip hηa hηb
  let action : ℝ → ℝ := fun s ↦ ∫ t in (t₀ - δ)..(t₀ + δ),
    F.chartEnergy (c t₀) (x t + s • η t, deriv x t + s • deriv η t)
  have hcentral : F.curveEnergyAction c (t₀ - δ) (t₀ + δ) = action 0 := by
    simpa only [action, zero_smul, add_zero, x, χ] using
      F.curveEnergyAction_eq_chart_of_ae (c t₀) hsource' hdiff'
  have hmin : IsLocalMin action 0 := by
    change ∀ᶠ s in 𝓝 (0 : ℝ), action 0 ≤ action s
    filter_upwards [ball_mem_nhds (0 : ℝ) hε] with s hs
    have hs' : |s| < ε := by simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs] using hs
    obtain ⟨hbase, hLip, ha, hb⟩ := hvariation s hs'
    have hbase' : ∀ᵐ t ∂volume.restrict (uIoc (t₀ - δ) (t₀ + δ)),
        x t + s • η t ∈ χ.target := by
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
      rw [uIoc_of_le hab] at ht
      exact hbase (Ioc_subset_Icc_self ht)
    have hηdiff : ∀ᵐ t ∂volume.restrict (uIoc (t₀ - δ) (t₀ + δ)),
        DifferentiableAt ℝ η t := Eventually.of_forall (fun t ↦ hη.differentiable_one t)
    have haction := F.curveEnergyAction_chart_add_eq_of_ae (c t₀) hbase' hdiff' hηdiff
    change F.curveEnergyAction (χ.symm ∘ (fun t ↦ x t + s • η t))
      (t₀ - δ) (t₀ + δ) = action s at haction
    rw [← hcentral, ← haction]
    apply hF.curveEnergyAction_le_of_isometric_interval hab hisolocal hLip
    · exact ha.trans (χ.left_inv (hsource (left_mem_Icc.mpr hab)))
    · exact hb.trans (χ.left_inv (hsource (right_mem_Icc.mpr hab)))
  have hderiv := hasDerivAt_intervalIntegral_lagrangian_add_of_compact_ae
    (isOpen_chartEnergyDomain (c t₀)) ((hF.contDiffOn_chartEnergy (c t₀)).of_le (by simp))
    hP hPU hab hxLip hphase hη
  exact hmin.hasDerivAt_eq_zero hderiv

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
