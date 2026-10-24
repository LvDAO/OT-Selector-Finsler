import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
## Lemma skeleton

* **Conditions:** A measurable carrier K for Giry measurability; compact K in a Hausdorff Borel space for weak compactness. The generic tightness result assumes zero complement mass for every law in the family.
* **Objects:** The set of probability laws carried by K is measurable and weakly compact; any measure family on a common compact carrier is tight.
* **Proof detail:** Use measurable evaluation at K-complement for the Giry event. Apply the compact-mass-constraint form of Prokhorov with zero escape; common-carrier tightness follows immediately from its definition.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 4*, Proposition 437P(a)–(b), pp. 66–67, and Theorem 437R(g)–(h), p. 68 and following proof.
  https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=66

**Relationship to the sources:** Common-compact-carrier case of tightness/Prokhorov. The Lean compactness theorem uses the inherited Borel probability topology directly and does not state an additional Radon hypothesis; the book’s measure regularity conventions are distinct.
-/

/-!
# Compact carriers of original probability plans

Probabilities carried by one fixed compact physical set form a compact weak
cohort. Its Giry measurability is proved directly, without a Borel shortcut.
-/
open Set Function Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
variable {X : Type*} [MeasurableSpace X]

/-- Probability plans giving no mass outside the original compact carrier. -/
def probabilityCompactCarrier (K : Set X) : Set (ProbabilityMeasure X) :=
  {π | (π : Measure X) Kᶜ = 0}

/-- This cohort is Giry-measurable directly from evaluation on the original
measurable carrier, without identifying weak Borel and Giry structures. -/
theorem measurableSet_probabilityCompactCarrier
    {K : Set X} (hK : MeasurableSet K) : MeasurableSet (probabilityCompactCarrier K) := by
  exact measurableSet_eq_fun
    ((Measure.measurable_coe hK.compl).comp measurable_subtype_coe) measurable_const

/-- A fixed compact physical carrier gives a compact weak set of probability
plans by Prokhorov, with zero escape at every exhaustion index. -/
theorem isCompact_probabilityCompactCarrier
    [TopologicalSpace X] [T2Space X] [BorelSpace X]
    {K : Set X} (hK : IsCompact K) : IsCompact (probabilityCompactCarrier K) := by
  have hc := isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le
    (u := fun _ ↦ (0 : NNReal)) (K := fun _ ↦ K) tendsto_const_nhds (fun _ ↦ hK)
    (Or.inr (fun _ _ _ ↦ subset_rfl))
  convert hc using 1
  ext π
  simp only [probabilityCompactCarrier, mem_ofPred_eq, le_zero_iff]
  exact ⟨fun h _ ↦ (π.null_iff_toMeasure_null Kᶜ).mpr h,
    fun h ↦ (π.null_iff_toMeasure_null Kᶜ).mp (h 0)⟩

/-- Any original law family carried almost surely by one fixed compact weak
cohort is uniformly tight. The cohort need not be postulated independently. -/
theorem isTightMeasureSet_of_common_compact_carrier
    {S I : Type*} [MeasurableSpace S] [TopologicalSpace S]
    (R : I → Measure S) (K : Set S) (hK : IsCompact K)
    (hcarried : ∀ i, R i Kᶜ = 0) :
    IsTightMeasureSet (range R) := by
  apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
  intro ε hε
  refine ⟨K, hK, ?_⟩
  rintro _ ⟨i, rfl⟩
  rw [hcarried i]
  exact bot_le

end OTSelector.Probability
