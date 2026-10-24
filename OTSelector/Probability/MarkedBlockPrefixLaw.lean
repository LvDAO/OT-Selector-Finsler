import OTSelector.Probability.MarkedCountExpectation

/-!
# The marked fixed block only depends on the iid prefixes

A Poissonized marked cloud is a Poisson count together with an infinite iid
sequence of marked cube points (`markedPoissonLaw`).  The fixed block value
`markedFixedBlockValue` reads only the first `m` source and `k` target entries of
the two sequences; the counts are irrelevant (`markedFixedBlockValue_eq_seq`).
Consequently the expectation under the Poisson cloud factors through the
projection onto the iid sequences:

`markedFixedBlockExpectation q r t kin g α β R m k`
is the integral of the block value against
`(markedSeqLaw q A α).prod (markedSeqLaw q B β)`.

In particular the expected block value is independent of the cloud intensity
`R`: intensity enters the binomial tile assembly only through the block sizes
`m` and `k`.  This is the law-theoretic half of the per-cell block comparison
`hblock` in `exists_physical_upper_bound_of_block_model`: a physical tile block
whose points are iid from the conditional laws `α`, `β` has exactly the marked
model block expectation at the same sizes.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

noncomputable section
namespace OTSelector.Probability

variable {q : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

omit [MeasurableSpace A] [MeasurableSpace B] in
/-- The fixed block value does not depend on the two Poisson counts. -/
theorem markedFixedBlockValue_eq_seq (q : ℕ) (r t : ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ)
    (m k : ℕ) (ω : TwoMarkedCloudSpace q A B) :
    markedFixedBlockValue q r t kin g m k ω =
      markedFixedBlockValue q r t kin g m k ((0, ω.1.2), (0, ω.2.2)) :=
  rfl

/-- The law of the two iid prefixes under the Poissonized cloud is the product
of the two iid sequence laws. -/
theorem map_seqProj_twoMarkedCloudLaw (q : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (R : ℝ≥0) :
    Measure.map (fun ω : TwoMarkedCloudSpace q A B => (ω.1.2, ω.2.2))
        (twoMarkedCloudLaw q A B α β R) =
      (markedSeqLaw q A α).prod (markedSeqLaw q B β) := by
  rw [twoMarkedCloudLaw, markedPoissonLaw, markedPoissonLaw]
  rw [show (fun ω : (ℕ × (ℕ → (Fin q → ℝ) × A)) × (ℕ × (ℕ → (Fin q → ℝ) × B)) =>
      (ω.1.2, ω.2.2)) = Prod.map Prod.snd Prod.snd from rfl]
  rw [← Measure.map_prod_map
    (μa := (poissonMeasure R).prod (markedSeqLaw q A α))
    (μc := (poissonMeasure R).prod (markedSeqLaw q B β))
    (f := Prod.snd) (g := Prod.snd) measurable_snd measurable_snd]
  simp

/-- **Prefix-law form of the marked block expectation.**  The expected block
value at fixed sizes is an integral over the two iid sequences; the Poisson
counts integrate out because they are independent of the blocks. -/
theorem markedFixedBlockExpectation_eq_seq (q : ℕ) (r t : ℝ)
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hg : Measurable (Function.uncurry g))
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (R : ℝ≥0) (m k : ℕ) :
    markedFixedBlockExpectation q r t kin g α β R m k =
      ∫ z : (ℕ → (Fin q → ℝ) × A) × (ℕ → (Fin q → ℝ) × B),
        markedFixedBlockValue q r t kin g m k ((0, z.1), (0, z.2))
        ∂((markedSeqLaw q A α).prod (markedSeqLaw q B β)) := by
  unfold markedFixedBlockExpectation
  rw [show (fun ω : TwoMarkedCloudSpace q A B =>
        markedFixedBlockValue q r t kin g m k ω)
      = (fun ω => markedFixedBlockValue q r t kin g m k ((0, ω.1.2), (0, ω.2.2))) from
        funext fun _ => rfl]
  have hproj : Measurable (fun ω : TwoMarkedCloudSpace q A B => (ω.1.2, ω.2.2)) :=
    (measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)
  have hseqMeas : Measurable (fun z :
      (ℕ → (Fin q → ℝ) × A) × (ℕ → (Fin q → ℝ) × B) =>
      markedFixedBlockValue q r t kin g m k ((0, z.1), (0, z.2))) := by
    have hemb : Measurable (fun z :
        (ℕ → (Fin q → ℝ) × A) × (ℕ → (Fin q → ℝ) × B) =>
        ((0, z.1), (0, z.2)) : _ → TwoMarkedCloudSpace q A B) :=
      (measurable_const.prodMk measurable_fst).prodMk
        (measurable_const.prodMk measurable_snd)
    exact (measurable_markedFixedBlockValue q r t hkin hg m k).comp hemb
  rw [← map_seqProj_twoMarkedCloudLaw (q := q) (A := A) (B := B) α β R]
  exact (integral_map_of_stronglyMeasurable hproj hseqMeas.stronglyMeasurable).symm

/-- **Independence of the cloud intensity.**  At fixed block sizes the marked
block expectation does not depend on the Poisson intensity. -/
theorem markedFixedBlockExpectation_indep_intensity (q : ℕ) (r t : ℝ)
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hg : Measurable (Function.uncurry g))
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (R R' : ℝ≥0) (m k : ℕ) :
    markedFixedBlockExpectation q r t kin g α β R m k =
      markedFixedBlockExpectation q r t kin g α β R' m k :=
  (markedFixedBlockExpectation_eq_seq q r t hkin hg α β R m k).trans
    (markedFixedBlockExpectation_eq_seq q r t hkin hg α β R' m k).symm

end OTSelector.Probability
