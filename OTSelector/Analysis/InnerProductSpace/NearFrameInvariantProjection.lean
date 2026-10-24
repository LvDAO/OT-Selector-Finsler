import OTSelector.MeasureTheory.HaarNullDirectionsNearFrame
import OTSelector.Probability.StationaryHyperplaneInvariantProjection
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalMinimizerActualRawFluxNearFrameDirections.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalMinimizerActualRawFluxNearFrameDirections`; the selected original proof blocks follow. -/
section

/-!
Conditions: Dimension greater than two, a translation group of Hilbert isometries, countably many vectors orthogonal to global invariants and a prescribed frame/tolerance.

Objects: A genuine nearby orthonormal frame whose hyperplane-invariant projections of every vector vanish.

Proof detail: The nonzero invariant hyperplane family is countable by Hilbert orthogonality; choose a nearby frame avoiding all its normal lines and contradict a nonzero projection.

Sources: Terence Tao, Section 1.4, Exercises 1.4.12–1.4.13, pp. 52–53 (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=61); D. H. Fremlin, Proposition 262D, p. 11; Corollary 262N, p. 17; Proposition 264G, pp. 38–39; Theorem 264I, pp. 40–41 (https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=38); D. H. Fremlin, Sections 441A (invariant measure definition) and 441J (integration under an invariant action), pp. 2 and 6; Section 443A, pp. 19–20 (Haar measurability) (https://www1.essex.ac.uk/maths/people/fremlin/chap44.pdf#page=6).
Relation: Locally proved countable-exception/frame-avoidance combination. The paper’s boundary-current argument motivates its use; no spectral-measure or mixing premise is added.
-/

/-! Arbitrarily close genuine frames annihilate countably many centered invariant components. -/
open Set Function Filter Submodule
open scoped InnerProductSpace Topology BigOperators
noncomputable section
namespace OTSelector.Probability
variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The common good frame can lie arbitrarily close to any prescribed frame.
Only actual centered invariant projections and their countable bad family are
used; no spectral-measure or uniform coercivity assumption is required. -/
theorem exists_orthonormalBasis_near_hyperplane_invariant_projections_eq_zero
    {ι : Type*} [Countable ι] (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure]
    (hdim : 2 < Module.finrank ℝ E)
    (U : E → H ≃ₗᵢ[ℝ] H) (hadd : ∀ a b x, U a (U b x) = U (a+b) x)
    (x : ι → H)
    (hx : ∀ j y, y ∈ translationFixedSubspace U ⊤ → ⟪x j,y⟫_ℝ = 0)
    (b₀ : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E,
      (∀ i, ‖b i-b₀ i‖ < δ) ∧ ∀ i j,
      (translationFixedSubspace U (ℝ ∙ b i)ᗮ).starProjection (x j) = 0 := by
  classical
  let Bad : Set {A : Submodule ℝ E // IsCoatom A} :=
    {A | ∃ j, (translationFixedSubspace U A.1).starProjection (x j) ≠ 0}
  have hBad : Bad.Countable :=
    countable_nonzero_hyperplane_invariant_projections_family U hadd x hx
  let _ : Countable Bad := hBad.to_subtype
  choose n hn using fun A : Bad ↦ exists_unit_normal_of_isCoatom A.1.1 A.1.2
  obtain ⟨b,hnear,hb⟩ := exists_orthonormalBasis_near_all_measure_normalLines_eq_zero
    μ hdim (fun A : Bad ↦ MeasureTheory.Measure.dirac (n A : E)) b₀ hδ
  refine ⟨b,hnear,fun i j ↦ ?_⟩
  by_contra hbad
  let ni : Metric.sphere (0 : E) 1 :=
    ⟨b i, by simpa only [Metric.mem_sphere,dist_zero_right] using b.norm_eq_one i⟩
  let A : {A : Submodule ℝ E // IsCoatom A} :=
    ⟨(ℝ ∙ b i)ᗮ,isCoatom_orthogonal_span_unit ni⟩
  let a : Bad := ⟨A,⟨j,hbad⟩⟩
  have horth : (ℝ ∙ (n a : E))ᗮ = (ℝ ∙ b i)ᗮ := (hn a).symm
  have hspan : ℝ ∙ (n a : E) = ℝ ∙ b i := by
    simpa only [Submodule.orthogonal_orthogonal] using
      congrArg (fun W : Submodule ℝ E ↦ Wᗮ) horth
  have hmem : (n a : E) ∈ ((ℝ ∙ b i : Set E) \ {0}) := by
    refine ⟨?_,?_⟩
    · rw [← hspan]
      exact Submodule.mem_span_singleton_self _
    · have hnunit : ‖(n a : E)‖ = 1 := by
        simpa only [Metric.mem_sphere,dist_zero_right] using (n a).property
      intro hz
      have hz' : (n a : E) = 0 := Set.mem_singleton_iff.1 hz
      have hz'' : (0 : ℝ) = 1 := by simpa only [hz',norm_zero] using hnunit
      exact zero_ne_one hz''
  have hone := MeasureTheory.Measure.dirac_apply_of_mem hmem
  exact zero_ne_one ((hb i a).symm.trans hone)

end OTSelector.Probability

end
end
