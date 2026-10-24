import Mathlib.MeasureTheory.Measure.Prod

/-!
## Lemma skeleton

* **Conditions:** SFinite positive full, retained and discarded measures with exact full=retained+discarded decompositions. The event lies in a specified product carrier; B and carrier sets need not be measurable in the Lean headers.
* **Objects:** An upper bound for full product mass by retained product mass plus the two discarded-mass errors, with self-product and retained-null specializations.
* **Proof detail:** Expand the product as retained0 x retained1 + retained0 x discarded1 + discarded0 x full1. Bound each discarded term by the product of carrier masses, then specialize and insert a mass cutoff.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 2*, Sections 251A–251I, pp. 2–6: rectangular covers, product outer measures and the product-measure rectangle formula.
  https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=2

**Relationship to the sources:** Positive product-measure telescoping corollary. The arbitrary-set outer-measure and SFinite formulation is a local extension of the textbook rectangle construction, not a normalization-dependent probability total-variation theorem.
-/

/-! Product witnesses change by at most the discarded mass in either factor.
The bound applies to arbitrary measurable transport plans with their original
retained/discarded decomposition; no independence of those plans is assumed. -/

open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Probability

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- A two-edge event inside a fixed rectangle has an error controlled by the
discarded mass of either original marginal plan. -/
theorem measure_prod_witness_le_of_add
    (full₀ retained₀ discarded₀ : Measure X)
    (full₁ retained₁ discarded₁ : Measure Y)
    [SFinite full₀] [SFinite retained₀] [SFinite discarded₀]
    [SFinite full₁] [SFinite retained₁] [SFinite discarded₁]
    (hsplit₀ : full₀ = retained₀ + discarded₀)
    (hsplit₁ : full₁ = retained₁ + discarded₁)
    {K₀ : Set X} {K₁ : Set Y} {B : Set (X × Y)} (hB : B ⊆ K₀ ×ˢ K₁) :
    full₀.prod full₁ B ≤ retained₀.prod retained₁ B +
      full₀ K₀ * discarded₁ K₁ + discarded₀ K₀ * full₁ K₁ := by
  have hprod : full₀.prod full₁ =
      retained₀.prod retained₁ + retained₀.prod discarded₁ + discarded₀.prod full₁ := by
    calc
      full₀.prod full₁ = (retained₀ + discarded₀).prod full₁ :=
        congrArg (fun μ : Measure X ↦ μ.prod full₁) hsplit₀
      _ = retained₀.prod full₁ + discarded₀.prod full₁ := Measure.add_prod _
      _ = retained₀.prod retained₁ + retained₀.prod discarded₁ +
          discarded₀.prod full₁ := by rw [hsplit₁, Measure.prod_add]
  have hret : retained₀ K₀ ≤ full₀ K₀ := by
    rw [hsplit₀, Measure.add_apply]
    exact le_add_right le_rfl
  calc
    full₀.prod full₁ B = retained₀.prod retained₁ B + retained₀.prod discarded₁ B +
        discarded₀.prod full₁ B := by rw [hprod, Measure.add_apply, Measure.add_apply]
    _ ≤ retained₀.prod retained₁ B + retained₀ K₀ * discarded₁ K₁ +
        discarded₀ K₀ * full₁ K₁ :=
      add_le_add (add_le_add le_rfl
        ((measure_mono hB).trans (Measure.prod_prod_le K₀ K₁)))
        ((measure_mono hB).trans (Measure.prod_prod_le K₀ K₁))
    _ ≤ retained₀.prod retained₁ B + full₀ K₀ * discarded₁ K₁ +
        discarded₀ K₀ * full₁ K₁ := by gcongr

/-- For two edges from the same full plan, only twice its local mass times
the original discarded local mass is lost. -/
theorem measure_prod_self_witness_le_of_add
    (full retained discarded : Measure X)
    [SFinite full] [SFinite retained] [SFinite discarded]
    (hsplit : full = retained + discarded)
    {K : Set X} {B : Set (X × X)} (hB : B ⊆ K ×ˢ K) :
    full.prod full B ≤ retained.prod retained B + 2 * full K * discarded K := by
  calc
    full.prod full B ≤ retained.prod retained B + full K * discarded K +
        discarded K * full K :=
      measure_prod_witness_le_of_add full retained discarded full retained discarded
        hsplit hsplit hB
    _ = retained.prod retained B + 2 * full K * discarded K := by ring

/-- A local mass cutoff makes the bound uniform over the full scene. The
retained plan needs only to exclude this particular improvement witness. -/
theorem measure_prod_self_witness_le_of_retained_null
    (full retained discarded : Measure X)
    [SFinite full] [SFinite retained] [SFinite discarded]
    (hsplit : full = retained + discarded)
    {K : Set X} {B : Set (X × X)} (hB : B ⊆ K ×ˢ K)
    (hretained : retained.prod retained B = 0)
    {L : ℝ≥0∞} (hfull : full K ≤ L) :
    full.prod full B ≤ 2 * L * discarded K := by
  calc
    full.prod full B ≤ retained.prod retained B + 2 * full K * discarded K :=
      measure_prod_self_witness_le_of_add full retained discarded hsplit hB
    _ = 2 * full K * discarded K := by rw [hretained, zero_add]
    _ ≤ 2 * L * discarded K := by gcongr

end OTSelector.Probability
