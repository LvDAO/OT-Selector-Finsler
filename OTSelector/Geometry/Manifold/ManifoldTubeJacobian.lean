import OTSelector.Geometry.Manifold.TubeCoordinates
import OTSelector.MeasureTheory.SmoothPartialHomeomorphJacobian
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.ManifoldTubeJacobian.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.ManifoldTubeJacobian`; the selected original proof blocks follow. -/
section

/-!
Conditions: An actual C1 manifold tube and its inverse, a linear label normalization and the explicitly transported parameter measure.

Objects: Normalized absolute tube Jacobian, compact positive bounds and change of variables for nonnegative integrands.

Proof detail: Write the chart derivative determinant, use inverse derivatives for nonvanishing, compactness for bounds and the Jacobian change-of-variables theorem for transport.

Sources: D. H. Fremlin, Theorem 263D(i)–(v), pp. 26–28; Lemma 263C, p. 25; decomposition Lemma 262M, pp. 15–17 (https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=26); D. H. Fremlin, Theorem 263A, pp. 22–24: linear change of variables and absolute determinant (https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=22); Jiří Lebl, Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity) (https://www.jirka.org/ra/realanal2.pdf#page=38).
Relation: Chart and parameter-measure adapter; the formula allows vanishing densities and does not silently normalize Haar measure.
-/

/-!
# The actual volume factor of a manifold tube

The charted tube has a positive continuous Jacobian with compact bounds. Its
change-of-variables formula uses the model Haar measure transported by the chosen
linear normalization. Thus the normalization is retained explicitly, and the
formula applies to arbitrary nonnegative densities, including densities that vanish.
-/

open Set MeasureTheory Manifold
open scoped ContDiff ENNReal

noncomputable section
namespace OTSelector.Geometry

variable {E V M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M] [ChartedSpace E M]

/-- Actual coordinate volume factor in the original tube parameters. -/
def manifoldTubeJacobian (Y : OpenPartialHomeomorph V M) (ℓ : V ≃L[ℝ] E)
    (old : M) (q : V) : ℝ :=
  partialHomeomorphJacobian (manifoldTubeChart Y ℓ old) (ℓ q)

/-- The determinant keeps the chosen linear normalization explicitly. -/
theorem manifoldTubeJacobian_eq_det (Y : OpenPartialHomeomorph V M) (ℓ : V ≃L[ℝ] E)
    (old : M) (q : V) : manifoldTubeJacobian Y ℓ old q =
      |((fderiv ℝ ((chartAt E old) ∘ Y) q).comp ℓ.symm.toContinuousLinearMap).det| := by
  unfold manifoldTubeJacobian partialHomeomorphJacobian
  rw [fderiv_manifoldTubeChart]

variable [IsManifold 𝓘(ℝ, E) 1 M]

/-- The coordinate volume factor is continuous on its actual chart overlap. -/
theorem continuousOn_manifoldTubeJacobian (Y : OpenPartialHomeomorph V M)
    (ℓ : V ≃L[ℝ] E) (old : M)
    (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) 1 Y Y.source) :
    ContinuousOn (manifoldTubeJacobian Y ℓ old)
      (Y.source ∩ Y ⁻¹' (chartAt E old).source) := by
  apply (continuousOn_partialHomeomorphJacobian
    (contDiffOn_manifoldTubeChart Y ℓ old hY)).comp ℓ.continuous.continuousOn
  intro q hq
  exact (apply_mem_manifoldTubeChart_source_iff Y ℓ old q).2 hq

/-- Actual inverse regularity gives positive volume factor without an extra rank premise. -/
theorem manifoldTubeJacobian_pos (Y : OpenPartialHomeomorph V M) (ℓ : V ≃L[ℝ] E)
    (old : M) (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) 1 Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) 1 Y.symm Y.target)
    {q : V} (hq : q ∈ Y.source ∩ Y ⁻¹' (chartAt E old).source) :
    0 < manifoldTubeJacobian Y ℓ old q :=
  partialHomeomorphJacobian_pos (contDiffOn_manifoldTubeChart Y ℓ old hY)
    (contDiffOn_manifoldTubeChart_symm Y ℓ old hi)
    ((apply_mem_manifoldTubeChart_source_iff Y ℓ old q).2 hq)

/-- Compact legal parameter sets admit finite positive volume-factor bounds. -/
theorem exists_manifoldTubeJacobian_bounds (Y : OpenPartialHomeomorph V M)
    (ℓ : V ≃L[ℝ] E) (old : M)
    (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) 1 Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) 1 Y.symm Y.target)
    {K : Set V} (hK : IsCompact K)
    (hKD : K ⊆ Y.source ∩ Y ⁻¹' (chartAt E old).source) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ∀ q ∈ K, a ≤ manifoldTubeJacobian Y ℓ old q ∧ manifoldTubeJacobian Y ℓ old q ≤ b := by
  have hKC : ℓ '' K ⊆ (manifoldTubeChart Y ℓ old).source := by
    rintro _ ⟨q, hq, rfl⟩
    exact (apply_mem_manifoldTubeChart_source_iff Y ℓ old q).2 (hKD hq)
  obtain ⟨a, b, ha, hb, h⟩ := exists_partialHomeomorphJacobian_bounds
    (contDiffOn_manifoldTubeChart Y ℓ old hY)
    (contDiffOn_manifoldTubeChart_symm Y ℓ old hi) (hK.image ℓ.continuous) hKC
  exact ⟨a, b, ha, hb, fun q hq ↦ h (ℓ q) (mem_image_of_mem ℓ hq)⟩

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace V] [BorelSpace V]

/-- Reference measure in the original parameters, with normalization retained. -/
def tubeParameterMeasure (ℓ : V ≃L[ℝ] E) (m : Measure E) : Measure V := m.map ℓ.symm

/-- The chosen normalization carries its transported reference measure back exactly. -/
theorem measurePreserving_tubeNormalization (ℓ : V ≃L[ℝ] E) (m : Measure E) :
    MeasurePreserving ℓ (tubeParameterMeasure ℓ m) m := by
  refine ⟨ℓ.continuous.measurable, ?_⟩
  rw [tubeParameterMeasure, Measure.map_map ℓ.continuous.measurable ℓ.symm.continuous.measurable]
  have he : (ℓ : V → E) ∘ ℓ.symm = id := funext ℓ.apply_symm_apply
  rw [he]
  exact Measure.map_id

variable [FiniteDimensional ℝ E] (m : Measure E) [m.IsAddHaarMeasure]

/-- The actual charted image integral equals its Jacobian-weighted parameter integral.
The nonnegative integrand is arbitrary; no positive density assumption is imposed. -/
theorem lintegral_image_manifoldTubeJacobian (Y : OpenPartialHomeomorph V M)
    (ℓ : V ≃L[ℝ] E) (old : M)
    (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) 1 Y Y.source)
    {s : Set V} (hs : MeasurableSet s)
    (hsD : s ⊆ Y.source ∩ Y ⁻¹' (chartAt E old).source) (g : E → ℝ≥0∞) :
    (∫⁻ z in (chartAt E old) '' (Y '' s), g z ∂m) =
      ∫⁻ q in s, ENNReal.ofReal (manifoldTubeJacobian Y ℓ old q) *
        g ((chartAt E old) (Y q)) ∂(tubeParameterMeasure ℓ m) := by
  let C := manifoldTubeChart Y ℓ old
  have hC : ContDiffOn ℝ 1 C C.source := contDiffOn_manifoldTubeChart Y ℓ old hY
  have hsC : ℓ '' s ⊆ C.source := by
    rintro _ ⟨q, hq, rfl⟩
    exact (apply_mem_manifoldTubeChart_source_iff Y ℓ old q).2 (hsD hq)
  have hf : ∀ z ∈ ℓ '' s, HasFDerivWithinAt C (fderiv ℝ C z) (ℓ '' s) z := by
    intro z hz
    exact ((hC.contDiffAt (C.open_source.mem_nhds (hsC hz))).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt
  have he : C '' (ℓ '' s) = (chartAt E old) '' (Y '' s) := by
    simp only [C, image_image, manifoldTubeChart_coe, Function.comp_def, ℓ.symm_apply_apply]
  have hs' : MeasurableSet (ℓ '' s) :=
    ℓ.toHomeomorph.toMeasurableEquiv.measurableEmbedding.measurableSet_image.2 hs
  have hchange := lintegral_image_eq_lintegral_abs_det_fderiv_mul m hs' hf (C.injOn.mono hsC) g
  rw [he] at hchange
  rw [hchange, ← (measurePreserving_tubeNormalization ℓ m).setLIntegral_comp_emb
    ℓ.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun z ↦ ENNReal.ofReal |(fderiv ℝ C z).det| * g (C z)) s]
  simp only [C, manifoldTubeJacobian, partialHomeomorphJacobian,
    manifoldTubeChart_coe, Function.comp_def, ℓ.symm_apply_apply]

/-- In particular the actual charted volume is the integral of the parameter Jacobian. -/
theorem measure_image_manifoldTubeJacobian (Y : OpenPartialHomeomorph V M)
    (ℓ : V ≃L[ℝ] E) (old : M)
    (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) 1 Y Y.source)
    {s : Set V} (hs : MeasurableSet s)
    (hsD : s ⊆ Y.source ∩ Y ⁻¹' (chartAt E old).source) :
    m ((chartAt E old) '' (Y '' s)) =
      ∫⁻ q in s, ENNReal.ofReal (manifoldTubeJacobian Y ℓ old q)
        ∂(tubeParameterMeasure ℓ m) := by
  simpa using lintegral_image_manifoldTubeJacobian m Y ℓ old hY hs hsD (fun _ ↦ 1)

end OTSelector.Geometry

end
end
