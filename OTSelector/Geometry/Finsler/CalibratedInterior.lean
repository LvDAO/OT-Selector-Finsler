import OTSelector.Analysis.Calculus.Whitney.MetricPotentialUpperDifferentiable
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedCovector
import OTSelector.Geometry.Finsler.CalibratedReach
import OTSelector.Geometry.Finsler.DistanceUpperSupport
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialGlobalFamily
import OTSelector.Geometry.Finsler.PotentialRegularMass
import OTSelector.Transport.Kantorovich.CalibratedReach

/-!
# Geometry.Finsler.CalibratedInterior

* **Conditions:** A point in the actual two-sided calibrated interior of a 1-Lipschitz potential in complete Finsler geometry.
* **Objects:** Genuine potential differentiability everywhere in that interior, actual unit Legendre state and regular compact trimmed covers.
* **Proof detail:** Construct smooth upper supports from both calibrated endpoints, squeeze their touching first jets and recover the actual potential differential.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=29): Sections 4–4.1, Definition 4.2 and Proposition 4.3, p. 29; Lemma 4.5, pp. 30–31; Definition 4.6 and Lemma 4.8, pp. 31–32.
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=33): Section 4.2, Theorem 4.11, p. 33, Lemmas 4.12–4.13, pp. 34–36, proof of Theorem 4.11, p. 36; Lemma 4.15, p. 37.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).

Source relation (derived): This is pointwise interior regularity, without a full-volume conclusion or assumed distance smoothness.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerCalibratedInterior.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerCalibratedInterior`; the selected original proof blocks follow. -/
section

/-!
# Actual regularity throughout the two-sided calibrated interior

Complete original smooth Finsler geometry constructs smooth upper supports to the
original distances from both calibrated endpoints. Their contact determines the actual
potential differential at every point of the two-sided calibrated interior. Thus the
entire interior lies in the intrinsic regular potential domain, and its compact trimmed
cover consists of actual regular points. No distance smoothness, nonconjugacy, or
assumed potential derivative is needed. No full-volume assertion is made here.
-/

open Set Filter Metric Manifold
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- An original one-Lipschitz potential is actually differentiable at every point
with nontrivial calibrated partners on both sides, including distance cut points. -/
theorem mdifferentiableAt_of_mem_calibratedInterior (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {u : M → ℝ} (hu : let _instInteriorDiffLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) {x : M}
    (hx : let _instInteriorDiffMem : MetricSpace M := F.metricSpace
      x ∈ OTSelector.Geometry.calibratedInterior u) :
    MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x := by
  let _instInteriorDiffMetric : MetricSpace M := F.metricSpace
  obtain ⟨⟨a, hax, ha⟩, ⟨b, hxb, hb⟩⟩ := hx
  obtain ⟨U, A, hU, hxU, _, hA, hAdom, hAtouch⟩ :=
    hF.exists_smooth_distance_upperSupport hcomplete hax
  obtain ⟨V, B, hV, hxV, _, hB, hBdom, hBtouch⟩ :=
    hF.exists_smooth_distance_upperSupport hcomplete hxb.symm
  have hinv : (extChartAt 𝓘(ℝ, E) x).symm (extChartAt 𝓘(ℝ, E) x x) = x :=
    (extChartAt 𝓘(ℝ, E) x).left_inv (mem_extChartAt_source x)
  have hda : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℝ, E) x x),
      dist a ((extChartAt 𝓘(ℝ, E) x).symm z) ≤ A z := by
    filter_upwards [hU.mem_nhds hxU] with z hz
    exact hAdom z hz
  have hdb : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℝ, E) x x),
      dist ((extChartAt 𝓘(ℝ, E) x).symm z) b ≤ B z := by
    filter_upwards [hV.mem_nhds hxV] with z hz
    simpa only [dist_comm] using hBdom z hz
  have hd := metric_potential_hasFDerivAt_of_local_upper_costs hu
    (extChartAt 𝓘(ℝ, E) x).symm A B
    (by simpa only [hinv] using ha) (by simpa only [hinv] using hb)
    hda hdb (by simpa only [hinv] using hAtouch)
    (by simpa only [hinv, dist_comm] using hBtouch)
    ((hA.contDiffAt (hU.mem_nhds hxU)).of_le (by simp))
    ((hB.contDiffAt (hV.mem_nhds hxV)).of_le (by simp))
  apply (mdifferentiableAt_iff_source_of_mem_source
    (mem_chart_source E x)).mpr
  simpa using hd.1.differentiableAt.mdifferentiableAt.mdifferentiableWithinAt
    (s := Set.range (𝓘(ℝ, E) : E → E))

/-- Every two-sided calibrated interior point belongs to the intrinsic regular domain;
its actual inverse-Legendre tangent is constructed by the original geometry. -/
theorem mem_potentialRegularDomain_of_mem_calibratedInterior
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {u : M → ℝ} (hu : let _instInteriorRegularLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) {x : M}
    (hx : let _instInteriorRegularMem : MetricSpace M := F.metricSpace
      x ∈ OTSelector.Geometry.calibratedInterior u) :
    x ∈ F.potentialRegularDomain u := by
  have hdu := hF.mdifferentiableAt_of_mem_calibratedInterior hcomplete hu hx
  obtain ⟨b, hxb, hb⟩ := hx.2
  exact hF.mem_potentialRegularDomain_of_calibrated_partner hcomplete hu hxb (.inl hb) hdu

/-- Every two-sided calibrated interior point has an actual unit tangent whose energy
Legendre covector equals the original potential differential. -/
theorem exists_unit_legendre_of_mem_calibratedInterior (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {u : M → ℝ} (hu : let _instInteriorUnitLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) {x : M}
    (hx : let _instInteriorUnitMem : MetricSpace M := F.metricSpace
      x ∈ OTSelector.Geometry.calibratedInterior u) :
    ∃ v : TangentSpace 𝓘(ℝ, E) x, F.toFun ⟨x, v⟩ = 1 ∧
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x = fderiv ℝ (F.fiberEnergy x) v ∧
      F.fiberEnergy x v = (1 / 2 : ℝ) := by
  have hdu := hF.mdifferentiableAt_of_mem_calibratedInterior hcomplete hu hx
  obtain ⟨b, hxb, hb⟩ := hx.2
  exact hF.exists_unit_legendre_of_calibrated_endpoints hcomplete hu hxb hb hdu

/-- The actual two-sided interior has a countable compact trimmed cover consisting
entirely of intrinsically regular points, with compact calibrated endpoint carriers. -/
theorem exists_compact_regular_trimmed_contact_cover (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {u : M → ℝ} (hu : let _instRegularTrimmedLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) :
    let _instRegularTrimmedMetric : MetricSpace M := F.metricSpace
    ∃ K A : ℕ × ℕ → Set M,
      (∀ i, IsCompact (K i) ∧ IsCompact (A i) ∧ K i ⊆ F.potentialRegularDomain u) ∧
      (⋃ i, K i) = OTSelector.Geometry.calibratedInterior u ∧
      ∀ i x, x ∈ K i → ∃ a ∈ A i, ∃ b ∈ A i,
        dist a x = 1 / (i.1 + 1 : ℝ) ∧ u x - u a = 1 / (i.1 + 1 : ℝ) ∧
        dist x b = 1 / (i.1 + 1 : ℝ) ∧ u b - u x = 1 / (i.1 + 1 : ℝ) := by
  let _instRegularTrimmedMetric : MetricSpace M := F.metricSpace
  obtain ⟨K, A, hcompact, hcover, hcontact⟩ := F.exists_compact_trimmed_contact_cover hcomplete hu
  refine ⟨K, A, ?_, hcover, hcontact⟩
  intro i
  refine ⟨(hcompact i).1, (hcompact i).2, ?_⟩
  intro x hx
  apply hF.mem_potentialRegularDomain_of_mem_calibratedInterior hcomplete hu
  change x ∈ OTSelector.Geometry.calibratedInterior u
  rw [← hcover]
  exact mem_iUnion.mpr ⟨i, hx⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
