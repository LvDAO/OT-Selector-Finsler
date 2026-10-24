import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Dominated Random Measure Equality

Conditions: Dominated random measures and a countable covering family with finite expected dominating masses and equal local means; deterministic comparison uses finite dominating mass on each cover member.

Objects: Deterministic equality and one a.e. event on which the random measures coincide.

Proof detail: Each nonnegative local mass defect has zero mean, hence vanishes a.e. Intersect countably many such events and identify the dominated measures from their finite covering masses.

Relation to primary sources: A locally derived zero-defect/countable-cover result; neither global finite mass nor an unstated measurability hypothesis on each cover set is inserted.

References:
* Rick Durrett, Probability: Theory and Examples, fifth edition, author version 11 January 2019, Section 1.4, Exercise 1.4.1, p. 24. https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=32
-/
/-!
# Equality of dominated random measures from local mean masses

Only a countable measurable cover with finite reference masses is used.
The dominated measure need not be finite on the whole space. Equality of
expected cover masses gives one common event on which the full measures agree.
-/

open Set MeasureTheory Filter
open scoped ENNReal
noncomputable section
namespace OTSelector.Probability

variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]

/-- A dominated measure is identified by its masses on a countable cover of
finite reference mass; intersections of cover sets need no separate tests. -/
theorem measure_eq_of_le_of_countable_cover_mass_eq
    (μ ν : Measure X) (hμν : μ ≤ ν) (K : ℕ → Set X)
    (hcover : ⋃ k, K k = univ) (hfinite : ∀ k, ν (K k) ≠ ⊤)
    (hmass : ∀ k, μ (K k) = ν (K k)) : μ = ν := by
  apply Measure.ext_of_iUnion_eq_univ hcover
  intro k
  have hμfinite : μ (K k) < ⊤ := (hμν (K k)).trans_lt (lt_top_iff_ne_top.mpr (hfinite k))
  let _inst : IsFiniteMeasure (μ.restrict (K k)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hμfinite⟩
  apply Measure.eq_of_le_of_measure_univ_eq (Measure.restrict_mono_measure hμν (K k))
  simpa only [Measure.restrict_apply_univ] using hmass k

/-- Local expected masses identify two dominated random measures on one
common almost-everywhere event, without global finite total mass. -/
theorem ae_measure_eq_of_le_of_countable_cover_mean_eq
    (R : Measure Ω) (μ ν : Ω → Measure X) (K : ℕ → Set X)
    (hcover : ⋃ k, K k = univ)
    (hμν : ∀ᵐ ω ∂R, μ ω ≤ ν ω)
    (hν : ∀ k, AEMeasurable (fun ω ↦ ν ω (K k)) R)
    (hfinite : ∀ k, (∫⁻ ω, ν ω (K k) ∂R) ≠ ⊤)
    (hmean : ∀ k, (∫⁻ ω, ν ω (K k) ∂R) ≤ ∫⁻ ω, μ ω (K k) ∂R) :
    ∀ᵐ ω ∂R, μ ω = ν ω := by
  have hmass : ∀ᵐ ω ∂R, ∀ k, μ ω (K k) = ν ω (K k) := by
    apply ae_all_iff.mpr
    intro k
    have hle : (fun ω ↦ μ ω (K k)) ≤ᵐ[R] fun ω ↦ ν ω (K k) :=
      hμν.mono fun ω hω ↦ hω (K k)
    exact ae_eq_of_ae_le_of_lintegral_le hle
      (ne_top_of_le_ne_top (hfinite k) (lintegral_mono_ae hle)) (hν k) (hmean k)
  have hlocal : ∀ᵐ ω ∂R, ∀ k, ν ω (K k) ≠ ⊤ := by
    apply ae_all_iff.mpr
    intro k
    exact (ae_lt_top' (hν k) (hfinite k)).mono fun _ h ↦ h.ne
  filter_upwards [hμν, hmass, hlocal] with ω hle heq hfin
  exact measure_eq_of_le_of_countable_cover_mass_eq (μ ω) (ν ω) hle K hcover hfin heq

end OTSelector.Probability
