import Mathlib.MeasureTheory.Function.Jacobian

/-!
## Lemma skeleton

* **Conditions:** A finite-dimensional real normed space with additive Haar measure, arbitrary source S and target-null N; f has a within derivative with nonzero determinant almost everywhere on S.
* **Objects:** The source part of the preimage of N is Haar-null.
* **Proof detail:** Discard the null derivative exception and partition the remaining differentiability points into countably many pieces on which linear approximation yields a lower Lipschitz image bound; a target-null image then forces each source piece null.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 2*, Theorem 263D(i)–(v), pp. 26–28; Lemma 263C, p. 25; decomposition Lemma 262M, pp. 15–17.
  https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=26
* D. H. Fremlin, *Measure Theory, Volume 2*, Proposition 262D, p. 11; Corollary 262N, p. 17; Proposition 264G, pp. 38–39; Theorem 264I, pp. 40–41.
  https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=38

**Relationship to the sources:** Derived nondegenerate-derivative null-preimage corollary of the countable linear-approximation pieces in the Jacobian proof. No global injectivity or measurable source/target set is added.
-/

/-!
# Null preimages under almost-everywhere nondegenerate derivatives

On an arbitrary source set, an almost-everywhere nondegenerate within derivative
suffices to pull back Haar-null sets to Haar-null sets. Countable linear-approximation
pieces supply the required image lower bounds without an injectivity assumption.
-/

open Set Filter MeasureTheory MeasureTheory.Measure
open scoped Topology NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Haar-null sets have null preimages on an arbitrary source set wherever the within
 derivative is almost everywhere nondegenerate. Neither set need be measurable. -/
theorem measure_inter_preimage_eq_zero_of_ae_hasFDerivWithinAt_det_ne_zero
    (m : Measure E) [m.IsAddHaarMeasure]
    {f : E → E} {D : E → E →L[ℝ] E} {S N : Set E}
    (hD : ∀ᵐ x ∂m.restrict S,
      HasFDerivWithinAt f (D x) S x ∧ (D x).det ≠ 0)
    (hN : m N = 0) : m (S ∩ f ⁻¹' N) = 0 := by
  classical
  let Good := fun x ↦ HasFDerivWithinAt f (D x) S x ∧ (D x).det ≠ 0
  let T := (S ∩ f ⁻¹' N) ∩ {x | Good x}
  have hbad : m ({x | ¬ Good x} ∩ S) = 0 :=
    measure_inter_eq_zero_of_restrict (ae_iff.mp hD)
  have hradius (A : E →L[ℝ] E) : ∃ ε : ℝ≥0, ε ≠ 0 ∧
      ∀ (B : Set E) (g : E → E), A.det ≠ 0 →
        ApproximatesLinearOn g A B ε → m (g '' B) = 0 → m B = 0 := by
    by_cases hA : A.det = 0
    · exact ⟨1, one_ne_zero, fun _ _ hn ↦ False.elim (hn hA)⟩
    · let θ : ℝ≥0 := Real.toNNReal |A.det| / 2
      have hdet : 0 < Real.toNNReal |A.det| := Real.toNNReal_pos.mpr (abs_pos.mpr hA)
      have hθ : 0 < θ := div_pos hdet (by norm_num)
      have hθdet : (θ : ℝ≥0∞) < ENNReal.ofReal |A.det| := by
        exact ENNReal.coe_lt_coe.mpr (half_lt_self hdet)
      obtain ⟨ε, hbound, hε⟩ :=
        ((mul_le_addHaar_image_of_lt_det m A hθdet).and self_mem_nhdsWithin).exists
      refine ⟨ε, ne_of_gt hε, fun B g _ happ hzero ↦ ?_⟩
      have hmul : (θ : ℝ≥0∞) * m B = 0 :=
        nonpos_iff_eq_zero.mp (hzero ▸ hbound B g happ)
      exact (mul_eq_zero.mp hmul).resolve_left (by exact_mod_cast hθ.ne')
  choose ε hε hnull using hradius
  have hT : m T = 0 := by
    rcases eq_empty_or_nonempty T with hTempty | hTnonempty
    · simp [hTempty]
    · have hdiff : ∀ x ∈ T, HasFDerivWithinAt f (D x) T x := by
        intro x hx
        exact hx.2.1.mono (fun _ hy ↦ hy.1.1)
      obtain ⟨B, A, _, hcover, happ, hactual⟩ :=
        exists_closed_cover_approximatesLinearOn_of_hasFDerivWithinAt f T D hdiff ε hε
      have hpieces (n : ℕ) : m (T ∩ B n) = 0 := by
        obtain ⟨y, hy, hAy⟩ := hactual hTnonempty n
        apply hnull (A n) (T ∩ B n) f (hAy ▸ hy.2.2) (happ n)
        apply measure_mono_null _ hN
        rintro _ ⟨x, hx, rfl⟩
        exact hx.1.1.2
      apply measure_mono_null (show T ⊆ ⋃ n, T ∩ B n from ?_)
        (measure_iUnion_null hpieces)
      intro x hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp (hcover hx)
      exact mem_iUnion.mpr ⟨n, hx, hn⟩
  apply measure_mono_null (show S ∩ f ⁻¹' N ⊆ T ∪ ({x | ¬ Good x} ∩ S) from ?_)
    (measure_union_null hT hbad)
  intro x hx
  by_cases hg : Good x
  · exact Or.inl ⟨hx, hg⟩
  · exact Or.inr ⟨hg, hx.1⟩

end OTSelector.Geometry
