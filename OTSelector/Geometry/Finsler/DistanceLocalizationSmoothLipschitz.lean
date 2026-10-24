import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Coordinates.InverseChartLipschitz
import OTSelector.Geometry.Finsler.LengthMetric
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerDistanceLocalizationSmoothLipschitz.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerDistanceLocalizationSmoothLipschitz`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.DistanceLocalizationSmoothLipschitz

* **Conditions:** A C1 manifold map into the original continuous Finsler metric; a compact set lies in its open regularity domain for the uniform theorem.
* **Objects:** Local and compact-set original-metric Lipschitz bounds.
* **Proof detail:** Use a local chart, bound the C1 coordinate derivative and compose with inverse-chart length-metric comparison; combine finitely many neighborhoods on the compact set.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, p. 313: the length integral, induced distance and minimizing curves.
- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).

Source relation (derived): The compact bound is a derived local-to-global finite-cover estimate and allows chart crossings and folds.
-/

/-!
# Original-metric Lipschitz bounds for smooth parameter families

Every smooth manifold map is locally Lipschitz for the original Finsler metric.
Compact parameter sets give one common bound even when their physical images
cross charts or the parameter map has folds.
-/

open Set Filter Metric Manifold
open scoped Topology ContDiff NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E V M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M]

/-- A C1 manifold map has a genuine local Lipschitz bound in the original
Finsler distance, derived from its actual chart readout. -/
theorem exists_lipschitzOnWith_of_contMDiffAt (F : ContinuousFinslerNorm E M)
    {f : V → M} {x : V} (hf : ContMDiffAt 𝓘(ℝ, V) 𝓘(ℝ, E) 1 f x) :
    let _inst : MetricSpace M := F.metricSpace
    ∃ C : ℝ≥0, ∃ T ∈ 𝓝 x, LipschitzOnWith C f T := by
  let _inst : MetricSpace M := F.metricSpace
  let old := f x
  let χ := extChartAt 𝓘(ℝ, E) old
  have hsrc : f x ∈ χ.source := mem_extChartAt_source (f x)
  obtain ⟨r, Ci, hr, _, hCi⟩ := F.exists_lipschitzOnWith_extChartAt_symm old
  have hχ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 1 χ (f x) :=
    contMDiffAt_extChartAt' (by simpa only [χ, extChartAt_source] using hsrc)
  have hread : ContDiffAt ℝ 1 (χ ∘ f) x := (hχ.comp x hf).contDiffAt
  obtain ⟨Cr, S, hS, hCr⟩ := hread.exists_lipschitzOnWith
  let T := S ∩ (f ⁻¹' χ.source ∩ (χ ∘ f) ⁻¹' ball (χ old) r)
  have hT : T ∈ 𝓝 x := inter_mem hS (inter_mem
    (hf.continuousAt.preimage_mem_nhds ((isOpen_extChartAt_source old).mem_nhds hsrc))
    (hread.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hr)))
  have hcomp := hCi.comp (hCr.mono (show T ⊆ S from inter_subset_left))
    (show MapsTo (χ ∘ f) T (ball (χ old) r) from fun _ ht ↦ ht.2.2)
  refine ⟨Ci * Cr, T, hT, ?_⟩
  intro y hy w hw
  have hh := hcomp hy hw
  change edist (χ.symm (χ (f y))) (χ.symm (χ (f w))) ≤ _ at hh
  simpa only [χ.left_inv hy.2.1, χ.left_inv hw.2.1] using hh

/-- One actual-metric Lipschitz constant works on any compact parameter set
inside a smooth map's open domain; neither injectivity nor convexity is used. -/
theorem exists_lipschitzOnWith_on_compact_of_contMDiffOn (F : ContinuousFinslerNorm E M)
    {f : V → M} {K U : Set V} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) 1 f U) :
    let _inst : MetricSpace M := F.metricSpace
    ∃ C : ℝ≥0, LipschitzOnWith C f K := by
  let _inst : MetricSpace M := F.metricSpace
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK
  intro x hx
  obtain ⟨C, T, hT, hC⟩ := F.exists_lipschitzOnWith_of_contMDiffAt
    (hf.contMDiffAt (hU.mem_nhds (hKU hx)))
  exact ⟨C, T, nhdsWithin_le_nhds hT, hC⟩

end OTSelector.Geometry.ContinuousFinslerNorm

end
end
