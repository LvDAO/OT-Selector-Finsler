import OTSelector.MeasureTheory.HaarNullNormalDirections
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.StationaryFrequencyDirectionsNearFrame.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.StationaryFrequencyDirectionsNearFrame`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.HaarNullDirectionsNearFrame

## Lemma skeleton

* **Conditions:** Finite-dimensional inner-product space of dimension>2, a countable SFinite frequency family, an initial orthonormal frame and positive tolerance.
* **Objects:** An arbitrarily close orthonormal frame whose punctured normal lines are all frequency-null.
* **Proof detail:** First reflect the original frame in a fixed unit line, then reflect back with a nearby parameter. Their composition is the identity at the fixed parameter. Choose a nearby parameter from the dense conull good-reflection set, giving the required close frame.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=22): Theorem 263A, pp. 22–24: linear change of variables and absolute determinant.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19): Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25.
- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).

Source relation (composition): Near-frame refinement of the explicit reflection/Tonelli construction, not a spectral theorem.
-/

/-! Arbitrarily close original orthonormal frames avoiding countably many bad frequency lines. -/

open Set MeasureTheory Metric
open scoped Topology Pointwise
noncomputable section
namespace OTSelector.Probability
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]

/-- Every original orthonormal frame can be approximated by one avoiding all
nonzero masses in a countable family of genuine frequency measures. -/
theorem exists_orthonormalBasis_near_all_measure_normalLines_eq_zero
    {κ : Type*} [Countable κ]
    (μ : Measure F) [μ.IsAddHaarMeasure] (hdim : 2 < Module.finrank ℝ F)
    (ν : κ → Measure F) [∀ j, SFinite (ν j)]
    (b₀ : OrthonormalBasis (Fin (Module.finrank ℝ F)) ℝ F)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ b : OrthonormalBasis (Fin (Module.finrank ℝ F)) ℝ F,
      (∀ i, ‖b i-b₀ i‖ < δ) ∧ ∀ i j, ν j ((ℝ ∙ b i : Set F) \ {0}) = 0 := by
  let e (i : Fin (Module.finrank ℝ F)) : sphere (0 : F) 1 :=
    ⟨b₀ i, by simpa only [mem_sphere_zero_iff_norm] using b₀.norm_eq_one i⟩
  let v₀ := e ⟨0, by omega⟩
  let e' := fun i ↦ reflectedUnitDirection v₀ (e i)
  let U := {v : sphere (0 : F) 1 | ∀ i,
    ‖(reflectedUnitDirection v (e' i) : F)-b₀ i‖ < δ}
  have hU : IsOpen U := by
    simp only [U,Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_Iio.preimage (((continuous_subtype_val.comp
      (continuous_reflectedUnitDirection (e' i))).sub continuous_const).norm)
  have hv₀ : v₀ ∈ U := by
    intro i
    simpa only [e',reflectedUnitDirection,Submodule.reflection_reflection,e,
      Subtype.coe_mk,sub_self,norm_zero] using hδ
  have hdense := MeasureTheory.Measure.dense_of_ae
    (ae_toSphere_all_measure_reflected_normalLineAwayZero_eq_zero μ hdim e' ν)
  obtain ⟨v,hvU,hv⟩ := hdense.inter_open_nonempty U hU ⟨v₀,hv₀⟩
  let O := (ℝ ∙ (v₀ : F)).reflection.trans (ℝ ∙ (v : F)).reflection
  exact ⟨b₀.map O,hvU,hv⟩

end OTSelector.Probability

end
end
