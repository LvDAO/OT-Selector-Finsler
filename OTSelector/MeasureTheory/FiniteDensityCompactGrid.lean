import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import OTSelector.MeasureTheory.CompactCarrierGridGeometry
import OTSelector.MeasureTheory.FiniteDensityCellReadout
import OTSelector.Transport.Neumann.CellLaw
import OTSelector.Transport.Neumann.EndpointCoupling
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalNeumannTimeDependentHamiltonJacobiOriginalDensityGrid.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalNeumannTimeDependentHamiltonJacobiOriginalDensityGrid`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.FiniteDensityCompactGrid

## Lemma skeleton

* **Conditions:** Integrable nonnegative original densities on one compact Euclidean carrier, positive source density mass and positive grid radius.
* **Objects:** One nonempty finite grid inside the original carrier with measurable common quantizer, geometric diameter bounds and exact pushforward cell-weight laws for both densities.
* **Proof detail:** Positive mass forces the carrier nonempty. Choose a finite compact ball cover, select measurable nearest eligible centers, use carrier diameter for pair geometry and integrate each literal density fiber to identify the two pushed-forward finite laws.

## Mathematical sources

- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).
- [D. H. Fremlin, Measure Theory, Volume 4, Appendix](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=32): Sections 4A3B(a)–(c), p. 32; 4A3C(a)–(f), pp. 32–33.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf#page=27): Sections 234I–234L, pp. 27–29; especially 234L(c); Section 235K, p. 40.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=99): Section 3A, Theorem 3.23, p. 84; Section 3B, Theorem 3.25, p. 88.

Source relation (composition): Shared finite-density quantization; node weights retain original cell masses and are not individually normalized.
-/

/-! Actual original density laws share one finite-index grid whose nodes stay
in the same Euclidean carrier, with exact cell marginals and quadratic geometry. -/
open Set MeasureTheory Metric
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 1400000
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- Positive original density mass excludes an empty carried Euclidean set. -/
theorem originalDensity_positive_mass_carrier_nonempty
    (μ : Measure (ι→ℝ)) (f : (ι→ℝ)→ℝ) {Ω : Set (EuclideanSpace ℝ ι)}
    (hsupp : ∀ᵐz∂μ,(EuclideanSpace.equiv ι ℝ).symm z∈Ω)
    (hmass : 0<∫z,f z∂μ) : Ω.Nonempty := by
  by_contra hempty
  have hfalse : ∀ᵐz∂μ,False := hsupp.mono fun z hz↦hempty ⟨_,hz⟩
  have hzero : μ=0 := ae_eq_bot.mp (Filter.eventually_false_iff_eq_bot.mp hfalse)
  simp only [hzero,integral_zero_measure,lt_self_iff_false] at hmass

/-- One genuine measurable grid of the original compact Euclidean carrier
serves both density laws, with all nodes retained and exact original cell laws. -/
theorem exists_originalDensity_compact_finiteIndex_quadratic_grid
    (μ : Measure (ι→ℝ)) (f g : (ι→ℝ)→ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ᵐz∂μ,0≤f z) (hg0 : ∀ᵐz∂μ,0≤g z)
    {Ω : Set (EuclideanSpace ℝ ι)} (hΩ : IsCompact Ω)
    (hsupp : ∀ᵐz∂μ,(EuclideanSpace.equiv ι ℝ).symm z∈Ω)
    (hmass : 0<∫z,f z∂μ) {h : ℝ} (hh : 0<h) :
    ∃s:Finset (EuclideanSpace ℝ ι),s.Nonempty ∧ (∀i:s,(i:EuclideanSpace ℝ ι)∈Ω) ∧
      ∃T:(ι→ℝ)→s,Measurable T ∧
        (∀ᵐz∂μ,(EuclideanSpace.equiv ι ℝ).symm z∈Ω ∧ (T z:EuclideanSpace ℝ ι)∈Ω) ∧
        (∀ᵐz∂μ,‖(T z:EuclideanSpace ℝ ι)-(EuclideanSpace.equiv ι ℝ).symm z‖≤h) ∧
        (∀z∈Ω,∀i:s,‖z-(i:EuclideanSpace ℝ ι)‖≤Metric.diam Ω) ∧
        (∀i j:s,‖(j:EuclideanSpace ℝ ι)-(i:EuclideanSpace ℝ ι)‖^2/2≤(Metric.diam Ω)^2/2) ∧
        (μ.withDensity (fun z↦ENNReal.ofReal (f z))).map T=
          finiteWeightedMeasure (originalDensityCellWeight μ f T) ∧
        (μ.withDensity (fun z↦ENNReal.ofReal (g z))).map T=
          finiteWeightedMeasure (originalDensityCellWeight μ g T) := by
  obtain ⟨s,hsne,hsΩ,Q,hQ,hnear⟩:=exists_compact_measurable_finiteIndex_grid hΩ
    (originalDensity_positive_mass_carrier_nonempty μ f hsupp hmass) hh
  let T:(ι→ℝ)→s:=fun z↦Q ((EuclideanSpace.equiv ι ℝ).symm z)
  have hT : Measurable T:=hQ.comp (EuclideanSpace.equiv ι ℝ).symm.continuous.measurable
  have hnode : ∀i:s,(i:EuclideanSpace ℝ ι)∈Ω:=fun i↦hsΩ i.property
  have hgeom:=compact_grid_quadratic_geometry hΩ (fun i:s↦(i:EuclideanSpace ℝ ι)) hnode
  refine ⟨s,hsne,hnode,T,hT,hsupp.mono (fun z hz↦⟨hz,hnode (T z)⟩),?_,hgeom.1,hgeom.2,?_,?_⟩
  · exact hsupp.mono fun z hz↦hnear _ hz
  · exact originalDensityCellWeight_map_withDensity μ f hf hf0 T hT
  · exact originalDensityCellWeight_map_withDensity μ g hg hg0 T hT

end OTSelector.Reconstruction

end
end
