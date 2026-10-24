import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt

/-!
## Lemma skeleton

* **Conditions:** Compact metric state space and finitely many continuous point-separating coordinates.
* **Objects:** Finite measures with identical mixed coordinate moments.
* **Proof detail:** Extend monomial equality to the polynomial algebra, approximate continuous probes, then use measure extensionality.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 2*, Section 281E, Stone–Weierstrass theorem for a point-separating unital algebra.
  https://www1.essex.ac.uk/maths/people/fremlin/chap28.pdf#page=4
* D. H. Fremlin, *Measure Theory, Volume 4*, Sections 436J–436K, Riesz representation on locally compact Hausdorff spaces.
  https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=47

**Relationship to the sources:** This is the compact mixed-moment corollary of Stone–Weierstrass and Riesz uniqueness; the exact coordinate API is local.
-/

/-!
# Compact finite-coordinate laws are determined by their mixed moments

Coordinate polynomials separate points of a compact state space. Equality of all
mixed moments gives equality on their algebra, and the existing finite-measure
extensionality theorem identifies the entire law. This is the law-identification
step after computing the actual cavity cell-mass moments.
-/

open MeasureTheory Set
open scoped BigOperators BoundedContinuousFunction

noncomputable section
namespace OTSelector.Probability

/-- Finite real coordinate monomials determine finite measures on a compact
metric space when the coordinates distinguish its points. -/
theorem measure_eq_of_compact_mixed_moments
    {X ι : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] [Fintype ι]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : ι → X → ℝ) (hf : ∀ i, Continuous (f i))
    (hinj : Function.Injective (fun x i ↦ f i x))
    (hmom : ∀ r : ι → ℕ,
      (∫ x, ∏ i, f i x ^ r i ∂μ) = ∫ x, ∏ i, f i x ^ r i ∂ν) : μ = ν := by
  classical
  let c : ι → X →ᵇ ℝ := fun i ↦ BoundedContinuousFunction.mkOfCompact ⟨f i, hf i⟩
  let φ : MvPolynomial ι ℝ →ₐ[ℝ] (X →ᵇ ℝ) := MvPolynomial.aeval c
  let A : StarSubalgebra ℝ (X →ᵇ ℝ) :=
    { φ.range with
      star_mem' := by
        intro g hg
        have heq : star g = g := by ext x; simp
        simpa only [heq] using hg }
  have hA : (A.map (BoundedContinuousFunction.toContinuousMapStarₐ ℝ)).SeparatesPoints := by
    intro x y hxy
    have hne : (fun i ↦ f i x) ≠ (fun i ↦ f i y) := fun h ↦ hxy (hinj h)
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    refine ⟨f i, ?_, hi⟩
    refine ⟨(BoundedContinuousFunction.toContinuousMapStarₐ ℝ) (c i), ?_, rfl⟩
    refine ⟨c i, ?_, rfl⟩
    change c i ∈ φ.range
    exact ⟨MvPolynomial.X i, MvPolynomial.aeval_X _ _⟩
  have hp (p : MvPolynomial ι ℝ) :
      (∫ x, φ p x ∂μ) = ∫ x, φ p x ∂ν := by
    induction p using MvPolynomial.induction_on' with
    | monomial d a =>
      have hmono (x : X) : φ (MvPolynomial.monomial d a) x = a * ∏ i, f i x ^ d i := by
        simp [φ, MvPolynomial.aeval_monomial,
          Finsupp.prod_fintype d (fun i k ↦ c i ^ k) (by simp), c]
      simp_rw [hmono]
      rw [integral_const_mul, integral_const_mul, hmom]
    | add p q hp hq =>
      simp only [map_add, BoundedContinuousFunction.add_apply]
      rw [integral_add ((φ p).integrable μ) ((φ q).integrable μ),
        integral_add ((φ p).integrable ν) ((φ q).integrable ν), hp, hq]
  apply ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable hA
  intro g hg
  obtain ⟨p, rfl⟩ := (show g ∈ φ.range from hg)
  exact hp p

/-- Finite-dimensional laws carried by the same compact set are determined by
their actual coordinate moments, without changing the ambient law's domain. -/
theorem measure_eq_of_mixed_moments_of_isCompact
    {ι : Type*} [Fintype ι] (μ ν : Measure (ι → ℝ))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {K : Set (ι → ℝ)} (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂μ, x ∈ K) (hν : ∀ᵐ x ∂ν, x ∈ K)
    (hmom : ∀ r : ι → ℕ,
      (∫ x, ∏ i, x i ^ r i ∂μ) = ∫ x, ∏ i, x i ^ r i ∂ν) : μ = ν := by
  let _instCompactSupport : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let μK := μ.comap ((↑) : K → (ι → ℝ))
  let νK := ν.comap ((↑) : K → (ι → ℝ))
  have hμmap : μK.map ((↑) : K → (ι → ℝ)) = μ := by
    rw [map_comap_subtype_coe hK.measurableSet, Measure.restrict_eq_self_of_ae_mem hμ]
  have hνmap : νK.map ((↑) : K → (ι → ℝ)) = ν := by
    rw [map_comap_subtype_coe hK.measurableSet, Measure.restrict_eq_self_of_ae_mem hν]
  have heq : μK = νK := by
    apply measure_eq_of_compact_mixed_moments μK νK (fun i x ↦ x.val i)
      (fun i ↦ (continuous_apply i).comp continuous_subtype_val)
      (fun _ _ h ↦ Subtype.ext h)
    intro r
    have hm : Measurable (fun x : ι → ℝ ↦ ∏ i, x i ^ r i) :=
      (continuous_finsetProd _ fun i _ ↦ (continuous_apply i).pow (r i)).measurable
    have hμint := integral_map (μ := μK) measurable_subtype_coe.aemeasurable
      hm.aestronglyMeasurable
    have hνint := integral_map (μ := νK) measurable_subtype_coe.aemeasurable
      hm.aestronglyMeasurable
    rw [hμmap] at hμint
    rw [hνmap] at hνint
    exact hμint.symm.trans ((hmom r).trans hνint)
  rw [← hμmap, ← hνmap, heq]

/-- For nonnegative compact coordinates, the original nonnegative mixed-moment
identities also determine the entire finite law. -/
theorem measure_eq_of_compact_nonnegative_mixed_moments
    {X ι : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] [Fintype ι]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : ι → X → ℝ) (hf : ∀ i, Continuous (f i))
    (hf0 : ∀ i x, 0 ≤ f i x)
    (hinj : Function.Injective (fun x i ↦ f i x))
    (hmom : ∀ r : ι → ℕ,
      (∫⁻ x, ∏ i, ENNReal.ofReal (f i x) ^ r i ∂μ) =
        ∫⁻ x, ∏ i, ENNReal.ofReal (f i x) ^ r i ∂ν) : μ = ν := by
  apply measure_eq_of_compact_mixed_moments μ ν f hf hinj
  intro r
  have hcont : Continuous (fun x ↦ ∏ i, f i x ^ r i) :=
    continuous_finsetProd _ fun i _ ↦ (hf i).pow (r i)
  have hnonneg (x : X) : 0 ≤ ∏ i, f i x ^ r i :=
    Finset.prod_nonneg fun i _ ↦ pow_nonneg (hf0 i x) _
  have hprod (x : X) : ENNReal.ofReal (∏ i, f i x ^ r i) =
      ∏ i, ENNReal.ofReal (f i x) ^ r i := by
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ pow_nonneg (hf0 i x) _)]
    exact Finset.prod_congr rfl (fun i _ ↦ ENNReal.ofReal_pow (hf0 i x) _)
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnonneg)
      hcont.measurable.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnonneg)
      hcont.measurable.aestronglyMeasurable]
  simp_rw [hprod]
  rw [hmom]

end OTSelector.Probability
