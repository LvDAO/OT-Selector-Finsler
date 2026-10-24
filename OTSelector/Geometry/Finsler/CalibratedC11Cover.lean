import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedC11
import OTSelector.Geometry.Finsler.CalibratedInterior
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialGlobalFamily
import OTSelector.Geometry.Manifold.CompactChartRefinement
import OTSelector.Transport.Kantorovich.CalibratedReach

/-!
# Geometry.Finsler.CalibratedC11Cover

* **Conditions:** The complete calibrated interior and its countable compact trimmed contact cover.
* **Objects:** Countably many genuine chart cores with actual C1,1 extensions covering exactly the whole calibrated interior.
* **Proof detail:** Refine each compact trim by finitely many legal charts and finite C1,1 support pieces, then enumerate the resulting countable family.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=33): Section 4.2, Theorem 4.11, p. 33, Lemmas 4.12–4.13, pp. 34–36, proof of Theorem 4.11, p. 36; Lemma 4.15, p. 37.
- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).
- [D. H. Fremlin, Measure Theory, Volume 4, Appendix](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=24): Sections 4A2G(e), pp. 15–16; 4A2N(b), p. 22; 4A2Q(h) and proof, pp. 24–25.

Source relation (derived): Derived from the cited geometric/analytic principles with the exact actual source hypotheses. The local construction and its original phase/covector data are retained, rather than asserted as a verbatim source statement.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerCalibratedC11Cover.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerCalibratedC11Cover`; the selected original proof blocks follow. -/
section

/-!
# Countable actual C1,1 contact charts covering the full calibrated interior

The original two-sided calibrated interior has a countable compact trimmed cover.
Finite genuine chart refinement and finite original-distance upper-support refinement
then give countably many compact coordinate cores with true global C1,1 extensions.
The inverse chart images cover exactly the whole interior, including both inclusions.
-/

open Set Filter Manifold Metric
open scoped Topology ContDiff NNReal

noncomputable section
universe u v
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type u} {M : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- The entire actual two-sided calibrated interior admits a countable exact cover by
compact coordinate cores. On each core a constructed global compactly supported C1
function has globally Lipschitz derivative and matches the original potential and its
actual derivative. No prescribed contact jet, extension, chart cover or full-mass
assumption is supplied. The indexing type may be empty. -/
theorem exists_countable_calibrated_C11_cover (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {f : M → ℝ} (hf : let _instCountableC11Lip : MetricSpace M := F.metricSpace
      LipschitzWith 1 f) :
    let _instCountableC11Metric : MetricSpace M := F.metricSpace
    ∃ ι : Type (max u v), Countable ι ∧
      ∃ (old : ι → M) (K : ι → Set E) (G : ι → E → ℝ) (L : ι → ℝ≥0),
        (∀ i, IsCompact (K i) ∧ K i ⊆ (extChartAt 𝓘(ℝ, E) (old i)).target ∧
          ContDiff ℝ 1 (G i) ∧ HasCompactSupport (G i) ∧
          ContDiffOn ℝ ∞ (G i) (K i)ᶜ ∧ LipschitzWith (L i) (fderiv ℝ (G i)) ∧
          EqOn (G i) (f ∘ (extChartAt 𝓘(ℝ, E) (old i)).symm) (K i) ∧
          EqOn (fderiv ℝ (G i))
            (fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) (old i)).symm)) (K i) ∧
          ∀ x ∈ K i, HasFDerivAt (f ∘ (extChartAt 𝓘(ℝ, E) (old i)).symm)
            (fderiv ℝ (G i) x) x) ∧
        (⋃ i, (extChartAt 𝓘(ℝ, E) (old i)).symm '' K i) =
          OTSelector.Geometry.calibratedInterior f := by
  classical
  let _instCountableC11Metric : MetricSpace M := F.metricSpace
  obtain ⟨A, B, hcompact, hcover, hreach⟩ :=
    hF.exists_compact_regular_trimmed_contact_cover hcomplete hf
  have hchart (i : ℕ × ℕ) :=
    exists_finite_compact_chart_refinement (E := E) (A i) (hcompact i).1
  choose J C hC hCcover using hchart
  have hfinite (i : ℕ × ℕ) (j : {j // j ∈ J i}) :=
    hF.exists_finite_calibrated_C11_cover hcomplete j.val
      (hC i j.val j.property).1 (hC i j.val j.property).2.1
      (by positivity : (0 : ℝ) < 1 / (i.1 + 1 : ℝ)) hf
      (by
        intro x hx
        obtain ⟨a, _, b, _, ha, hfa, hb, hfb⟩ := hreach i
          ((extChartAt 𝓘(ℝ, E) j.val).symm x)
          ((hC i j.val j.property).2.2 ⟨x, hx, rfl⟩)
        exact ⟨a, b, ha, hfa, hb, hfb⟩)
  choose r hr T hTcover hT using hfinite
  have hext (i : ℕ × ℕ) (j : {j // j ∈ J i}) (k : {k // k ∈ T i j}) :=
    (hT i j k.val k.property).2
  choose G L hG using hext
  let ι := Σ i : ℕ × ℕ, Σ j : {j // j ∈ J i}, {k // k ∈ T i j}
  let old : ι → M := fun p ↦ p.2.1.val
  let K : ι → Set E := fun p ↦ C p.1 p.2.1.val ∩
    closedBall p.2.2.val (r p.1 p.2.1 / 8)
  refine ⟨ι, inferInstance, old, K, (fun p ↦ G p.1 p.2.1 p.2.2),
    (fun p ↦ L p.1 p.2.1 p.2.2), ?_, ?_⟩
  · intro p
    refine ⟨(hT p.1 p.2.1 p.2.2.val p.2.2.property).1, ?_,
      hG p.1 p.2.1 p.2.2⟩
    exact fun x hx ↦ (hC p.1 p.2.1.val p.2.1.property).2.1 hx.1
  · apply Subset.antisymm
    · intro x hx
      obtain ⟨p, z, hz, rfl⟩ := mem_iUnion.mp hx
      rw [← hcover]
      exact mem_iUnion.mpr ⟨p.1,
        (hC p.1 p.2.1.val p.2.1.property).2.2 ⟨z, hz.1, rfl⟩⟩
    · intro x hx
      rw [← hcover] at hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      rw [← hCcover i] at hi
      obtain ⟨j, hj, z, hz, hzx⟩ := mem_iUnion₂.mp hi
      let j' : {j // j ∈ J i} := ⟨j, hj⟩
      obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.mp (hTcover i j' hz)
      exact mem_iUnion.mpr ⟨⟨i, j', ⟨k, hk⟩⟩, z, ⟨hz, hzk⟩, hzx⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
