import OTSelector.Analysis.CompactParameterIntegral
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Energy.Compact
import OTSelector.Geometry.Finsler.Variation.Lagrangian
import OTSelector.Geometry.Manifold.TangentChartCurve

/-!
# Geometry.Finsler.LengthAction

* **Conditions:** A C1 coordinate curve or variation lying in the actual chart target on the compact time segment, with ordered endpoints.
* **Objects:** Equality of original manifold path length with its real coordinate length integral and a uniform parameter-neighborhood action identity.
* **Proof detail:** Use the genuine chart tangent formula, continuity of speed including zero, and compactness to retain the target for nearby parameters.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, p. 313: the length integral, induced distance and minimizing curves.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).

Source relation (derived): This is a path-length identity; no slit, Euler–Lagrange, completeness or endpoint-distance equality is required.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerLengthAction.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerLengthAction`; the selected original proof blocks follow. -/
section

/-!
# Original Finsler path length and the coordinate length action

A C1 coordinate curve has continuous original Finsler speed, including at zero velocity.
Its actual manifold path length is therefore the nonnegative real coordinate length
integral. For a C1 variation, compactness of the central time segment supplies a common
parameter neighborhood on which this identity identifies the two actions.

No slit condition, Euler--Lagrange equation, finite-dimensionality, completeness, or
separate integrability hypothesis is used. This is an identity for the original path
length, without identifying that length with the distance between its endpoints.
-/

open Set Filter Bundle MeasureTheory
open scoped Manifold Topology ContDiff ENNReal NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The actual path length of a C1 curve reconstructed in a chart equals the coordinate
length integral. Continuity of the actual chart length supplies integrability. -/
theorem pathELength_chart_eq (F : ContinuousFinslerNorm E M) (x₀ : M)
    {x : ℝ → E} {I : Set ℝ} (hI : IsOpen I) (hx : ContDiffOn ℝ 1 x I)
    {a b : ℝ} (hab : a ≤ b) (htrace : Icc a b ⊆ I)
    (hbase : ∀ t ∈ Icc a b, x t ∈ (extChartAt 𝓘(ℝ, E) x₀).target) :
    letI : ∀ y : M, ENorm (TangentSpace 𝓘(ℝ, E) y) := F.enorm
    Manifold.pathELength 𝓘(ℝ, E) ((extChartAt 𝓘(ℝ, E) x₀).symm ∘ x) a b =
      ENNReal.ofReal (∫ t in a..b, (F.chartLength x₀ (x t, deriv x t) : ℝ)) := by
  let : ∀ y : M, ENorm (TangentSpace 𝓘(ℝ, E) y) := F.enorm
  have hc : ContinuousOn (fun t ↦ (F.chartLength x₀ (x t, deriv x t) : ℝ))
      (Icc a b) :=
    NNReal.continuous_coe.comp_continuousOn ((F.continuousOn_chartLength x₀).comp
      ((hx.continuousOn.prodMk (hx.continuousOn_deriv_of_isOpen hI le_rfl)).mono htrace)
      (fun t ht ↦ ⟨hbase t ht, mem_univ _⟩))
  have hi : IntervalIntegrable
      (fun t ↦ (F.chartLength x₀ (x t, deriv x t) : ℝ)) volume a b :=
    hc.intervalIntegrable_of_Icc hab
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
    intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo,
    ofReal_integral_eq_lintegral_ofReal (hi.1.mono_set Ioo_subset_Ioc_self)
      (Eventually.of_forall (fun _ ↦ NNReal.coe_nonneg _))]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have ht' : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
  have hd := (hx.contDiffAt (hI.mem_nhds (htrace ht'))).differentiableAt_one
  change (F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
    ((extChartAt 𝓘(ℝ, E) x₀).symm ∘ x) ⟨t, (1 : ℝ)⟩) : ℝ≥0∞) = _
  rw [tangentMap_chart_symm_curve x₀ (hbase t ht') hd.hasDerivAt]
  exact ENNReal.ofReal_coe_nnreal.symm

/-- A C1 chart variation identifies the real value of original path length with the
coordinate length action near the central parameter. A common admissible strip and
integrability are derived from the compact central trace. -/
theorem pathELength_chartVariation_eventuallyEq
    (F : ContinuousFinslerNorm E M) (x₀ : M)
    {σ : ℝ × ℝ → E} {D : Set (ℝ × ℝ)} (hD : IsOpen D)
    (hσ : ContDiffOn ℝ 1 σ D) {s₀ a b : ℝ} (hab : a ≤ b)
    (htrace : ∀ t ∈ Icc a b, (s₀, t) ∈ D)
    (hbase : ∀ t ∈ Icc a b, σ (s₀, t) ∈ (extChartAt 𝓘(ℝ, E) x₀).target) :
    letI : ∀ y : M, ENorm (TangentSpace 𝓘(ℝ, E) y) := F.enorm
    (fun s ↦ (Manifold.pathELength 𝓘(ℝ, E)
      ((extChartAt 𝓘(ℝ, E) x₀).symm ∘ (fun t ↦ σ (s, t))) a b).toReal) =ᶠ[𝓝 s₀]
      lagrangianAction (fun z ↦ (F.chartLength x₀ z : ℝ)) σ a b := by
  let : ∀ y : M, ENorm (TangentSpace 𝓘(ℝ, E) y) := F.enorm
  let O := D ∩ σ ⁻¹' (extChartAt 𝓘(ℝ, E) x₀).target
  have hO : IsOpen O := hσ.continuousOn.isOpen_inter_preimage hD
    (isOpen_extChartAt_target x₀)
  obtain ⟨r, hr, hstrip⟩ := exists_pos_compact_parameter_strip hO
    (fun t ht ↦ ⟨htrace t ht, hbase t ht⟩)
  have hS : Icc (s₀ - r) (s₀ + r) ∈ 𝓝 s₀ :=
    Icc_mem_nhds (by linarith) (by linarith)
  filter_upwards [hS] with s hs
  let I : Set ℝ := {t | (s, t) ∈ D}
  have hI : IsOpen I := hD.preimage (continuous_const.prodMk continuous_id)
  have hx : ContDiffOn ℝ 1 (fun t ↦ σ (s, t)) I :=
    hσ.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ ht ↦ ht)
  rw [F.pathELength_chart_eq x₀ hI hx hab
    (fun t ht ↦ (hstrip ⟨hs, ht⟩).1)
    (fun t ht ↦ (hstrip ⟨hs, ht⟩).2)]
  exact ENNReal.toReal_ofReal
    (intervalIntegral.integral_nonneg hab (fun _ _ ↦ NNReal.coe_nonneg _))

end OTSelector.Geometry.ContinuousFinslerNorm

end
end
