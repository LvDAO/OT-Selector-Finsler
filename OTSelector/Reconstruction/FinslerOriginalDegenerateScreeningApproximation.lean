import OTSelector.Reconstruction.FinslerOriginalLegalPressureValueEquality
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalClockCollars
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryTightCut
import OTSelector.Transport.Neumann.EndpointCoupling

/-!
# Screening approximation for the degenerate focal coefficient

The remaining value-identification input hvalue of the general Finsler selector
is the unconditional screening approximation for the literal original focal
kinetic cost: for every weighted stationary matching and every positive epsilon
there is a finite-second-moment matching whose signed value exceeds the weighted
value by at most epsilon.

This module proves the collar-coercivity and quantitative collar-control halves
of the paper's screening argument (main.tex, prop:general-finite-path-screening
and thm:general-focal-value-equality) for the actual degenerate focal
coefficient, and reduces the whole approximation to one named collar-density
statement:

1. **Palm collars and coercivity.**  The actual conditional Finsler coefficient
   has arbitrarily full compact interior collars on which it is uniformly
   positive definite (imported collar theorem of the original clock data).  A
   weighted stationary matching whose true Palm pair heights lie in such a
   collar is automatically a finite-second-moment matching
   (secondMomentSubclass_of_collar).  This is the literal interior-collar
   coercivity used by the paper; no global positivity of the focal coefficient
   is needed.

2. **Quantitative collar control.**  For every weighted stationary matching and
   every epsilon there is a collar such that (i) the Palm mass of pairs outside
   the collar is at most 2 epsilon (from the exact original clock marginals),
   (ii) the second moment restricted to the collar is integrable and bounded by
   the weighted energy divided by the coercivity constant
   (exists_collar_palmMass_secondMoment_control).  Hence the obstruction to a
   finite unweighted second moment is confined to a set of arbitrarily small
   Palm mass: exactly the paper's interior collars omitting endpoint
   probabilities tending to zero.

3. **Collar value density implies screening.**  If collar-supported weighted
   stationary matchings are value-dense below the weighted pressure, then the
   screening approximation holds and I_w = I_2
   (screening_of_collarValueDensity,
   originalWeightedStationaryInf_eq_secondMomentInf_of_collarValueDensity).
   This reduces the remaining gap to the paper's reserve construction: produce
   collar-supported near-minimizers.

4. **Budget and repair forms.**  The screening approximation with an explicit
   value budget bounds the pressure gap (quantitative value identification), and
   the budget is connected to the explicit constants of the residual-repair
   chain: the Neumann repair value rho^{-1} C^2 / 2 of
   legalResidualRepair_absSignedValue_le and the retained-plan added cost
   L times the common residual port mass of repairedRetainedPlan_measureCost_le.
   Vanishing repair budgets are equivalent to the screening approximation
   (screening_iff_vanishing_budget).

## Remaining gap

The one unproved analytic input is collar value density: for every epsilon, a
collar-supported weighted stationary matching with value at most I_w + epsilon.
The paper obtains it by the reserve construction (dilate the weighted minimizer
to intensity lambda, superpose an independent reserve of intensity rho, complete
to a maximum-cardinality matching preserving the retained edges; the added
squared-distance cost is C rho^{1-2/q} plus o, and the retained-edge loss is
charged against the bounded probe).  Items 1 and 2 above prove that this
construction indeed suffices, since every collar-supported matching is a
finite-second-moment matching; the reserve completion itself is not formalized
here.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal BigOperators Topology Matrix.Norms.Operator

noncomputable section

namespace OTSelector.Reconstruction

open Module Manifold OTSelector.Geometry ContinuousFinslerNorm
open scoped ContDiff

set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

/-! ## 1. Palm collars and coercivity -/

section CollarCoercivity

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The unit weight of the set of Palm points whose pair height lies in the
collar C. -/
def palmCollarWeight {q : ℕ} (C : Set (ℝ × ℝ)) (m : PhysicalPairPalmMark (Fin q)) : ℝ := by
  classical
  exact if m.1 ∈ C then 1 else 0

omit [FiniteDimensional ℝ E] [BorelSpace E] in
theorem measurable_palmCollarWeight {q : ℕ} {C : Set (ℝ × ℝ)}
    (hC : MeasurableSet C) :
    Measurable (palmCollarWeight (q := q) C) := by
  classical
  refine Measurable.ite ?_ measurable_const measurable_const
  exact hC.preimage measurable_fst

omit [FiniteDimensional ℝ E] [BorelSpace E] in
theorem palmCollarWeight_nonneg {q : ℕ} (C : Set (ℝ × ℝ)) (m : PhysicalPairPalmMark (Fin q)) :
    0 ≤ palmCollarWeight C m := by
  classical
  unfold palmCollarWeight
  split_ifs <;> norm_num

omit [FiniteDimensional ℝ E] [BorelSpace E] in
theorem palmCollarWeight_le_one {q : ℕ} (C : Set (ℝ × ℝ)) (m : PhysicalPairPalmMark (Fin q)) :
    palmCollarWeight C m ≤ 1 := by
  classical
  unfold palmCollarWeight
  split_ifs <;> norm_num

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The collar weight is one exactly on the collar. -/
theorem palmCollarWeight_eq_one {q : ℕ} {C : Set (ℝ × ℝ)} {m : PhysicalPairPalmMark (Fin q)}
    (hm : m.1 ∈ C) : palmCollarWeight C m = 1 := by
  classical
  unfold palmCollarWeight
  rw [ite_eq_left hm]

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The collar weight vanishes off the collar. -/
theorem palmCollarWeight_eq_zero {q : ℕ} {C : Set (ℝ × ℝ)} {m : PhysicalPairPalmMark (Fin q)}
    (hm : m.1 ∉ C) : palmCollarWeight C m = 0 := by
  classical
  unfold palmCollarWeight
  rw [ite_eq_right hm]

/-- A weighted stationary matching whose true Palm pair heights lie almost
everywhere in a collar on which the focal kinetic coefficient is bounded below
by a positive constant is a finite-second-moment matching.  This is the paper's
interior-collar coercivity at the matching level; it does not require any global
lower bound for the focal coefficient. -/
theorem secondMomentSubclass_of_collar
    (D : OriginalSeedConditionalMoments S w μ ν)
    {gap : ℝ} {g : ℝ → ℝ → ℝ}
    {C : Set (ℝ × ℝ)} {c : ℝ} (hc : 0 < c)
    (hLB : ∀ p ∈ C, p.1 < p.2 → ∀ v : Fin (finrank ℝ S.covector.ker) → ℝ,
      c * ‖v‖ ^ 2 ≤ D.originalFocalKinetic gap p.1 p.2 v)
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (hQ : ∀ᵐ m ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law, m.1 ∈ C) :
    Q.secondMomentSubclass := by
  change Integrable (fun m => ‖m.2‖ ^ 2)
    (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)
  have hdom : Integrable (fun m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) =>
      (1 / c) * D.originalFocalKinetic gap m.1.1 m.1.2 m.2)
      (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) :=
    Q.kinetic_integrable.const_mul (1 / c)
  have hmeas : AEStronglyMeasurable
      (fun m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) => ‖m.2‖ ^ 2)
      (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) :=
    ((measurable_norm.comp measurable_snd).pow_const 2).aestronglyMeasurable
  refine hdom.mono' hmeas ?_
  filter_upwards [hQ, Q.ae_palm_forward] with m hm hforward
  have hkin := hLB m.1 hm hforward m.2
  have hnonneg : 0 ≤ ‖m.2‖ ^ 2 := sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  rw [show (1 / c) * D.originalFocalKinetic gap m.1.1 m.1.2 m.2 =
    D.originalFocalKinetic gap m.1.1 m.1.2 m.2 / c from by ring]
  exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hkin)

end CollarCoercivity

/-! ## 2. Quantitative collar control -/

section CollarControl

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The literal original focal kinetic cost has compact interior product
collars with uniformly positive-definite cost and arbitrarily small
complementary clock mass. -/
theorem exists_focalKinetic_collar
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (A B : Set ℝ) (c : ℝ), IsCompact A ∧ IsCompact B ∧
      μ Aᶜ < ENNReal.ofReal ε ∧ ν Bᶜ < ENNReal.ofReal ε ∧ 0 < c ∧
      ∀ a ∈ A, ∀ b ∈ B, a < b →
        ∀ v : Fin (finrank ℝ S.covector.ker) → ℝ,
          c * ‖v‖ ^ 2 ≤ D.originalFocalKinetic gap a b v := by
  obtain ⟨A, B, hAc, hBc, hAsub, hBsub, hAmass, hBmass, c, hc, hLB⟩ :=
    D.exists_compact_pair_coefficient_collars hF hw hgap hbounds
      (ENNReal.ofReal_pos.mpr hε)
  refine ⟨A, B, c, hAc, hBc, hAmass, hBmass, hc, fun a ha b hb hab v => ?_⟩
  rw [D.originalFocalKinetic_eq_of_original_support hbounds
    ⟨(hAsub ha).1, (hAsub ha).2⟩ ⟨(hBsub hb).1, (hBsub hb).2⟩ hab v]
  exact hLB a ha b hb hab v

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The Palm mass of a source-clock tail is the original source tail mass. -/
theorem palm_source_compl {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    {g : ℝ → ℝ → ℝ} (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    {A : Set ℝ} (hA : MeasurableSet A) :
    legalMarkedJointPalm q Q.law {m | m.1.1 ∈ Aᶜ} = α Aᶜ := by
  have hpre : (fun m : PhysicalPairPalmMark (Fin q) => m.1.1) ⁻¹' Aᶜ =
      {m | m.1.1 ∈ Aᶜ} := rfl
  rw [← hpre, ← Measure.map_apply measurable_fst.fst hA.compl, Q.source_clock]

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The Palm mass of a target-clock tail is the original target tail mass. -/
theorem palm_target_compl {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    {g : ℝ → ℝ → ℝ} (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    {B : Set ℝ} (hB : MeasurableSet B) :
    legalMarkedJointPalm q Q.law {m | m.1.2 ∈ Bᶜ} = β Bᶜ := by
  have hpre : (fun m : PhysicalPairPalmMark (Fin q) => m.1.2) ⁻¹' Bᶜ =
      {m | m.1.2 ∈ Bᶜ} := rfl
  rw [← hpre, ← Measure.map_apply measurable_fst.snd hB.compl, Q.target_clock]

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The mass outside a product collar in the true Palm law is bounded by the
original clock tail masses.  Only the exact original clock marginals of the
stationary matching are used, not any selected sample. -/
theorem palm_mass_outside_collar_le
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    legalMarkedJointPalm q Q.law {m | m.1 ∉ A ×ˢ B} ≤ α Aᶜ + β Bᶜ := by
  have hcompl : {m : PhysicalPairPalmMark (Fin q) | m.1 ∉ A ×ˢ B} ⊆
      {m | m.1.1 ∈ Aᶜ} ∪ {m | m.1.2 ∈ Bᶜ} := by
    intro m hm
    exact not_and_or.mp hm
  calc legalMarkedJointPalm q Q.law {m | m.1 ∉ A ×ˢ B}
      ≤ legalMarkedJointPalm q Q.law ({m | m.1.1 ∈ Aᶜ} ∪ {m | m.1.2 ∈ Bᶜ}) :=
        measure_mono hcompl
    _ ≤ legalMarkedJointPalm q Q.law {m | m.1.1 ∈ Aᶜ} +
          legalMarkedJointPalm q Q.law {m | m.1.2 ∈ Bᶜ} := measure_union_le _ _
    _ = α Aᶜ + β Bᶜ := by rw [palm_source_compl Q hA, palm_target_compl Q hB]

/-- **Quantitative collar control of the displacement second moment.**  For every
weighted stationary matching and every positive epsilon there is a compact
interior product collar such that the Palm mass of pairs outside the collar is
at most 2 epsilon and the second moment restricted to the collar is integrable
and bounded by the weighted kinetic energy divided by the collar coercivity
constant.  Hence the failure of a finite unweighted second moment is confined to
a Palm-null-as-epsilon collar complement. -/
theorem exists_collar_palmMass_secondMoment_control
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (A B : Set ℝ) (c : ℝ), IsCompact A ∧ IsCompact B ∧
      legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law {m | m.1 ∉ A ×ˢ B} ≤
        ENNReal.ofReal (2 * ε) ∧
      0 < c ∧
      (∀ a ∈ A, ∀ b ∈ B, a < b →
        ∀ v : Fin (finrank ℝ S.covector.ker) → ℝ,
          c * ‖v‖ ^ 2 ≤ D.originalFocalKinetic gap a b v) ∧
      Integrable (fun m => ‖m.2‖ ^ 2 * palmCollarWeight (A ×ˢ B) m)
        (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ∧
      (∫ m, ‖m.2‖ ^ 2 * palmCollarWeight (A ×ˢ B) m
          ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≤
        (1 / c) * ∫ m, D.originalFocalKinetic gap m.1.1 m.1.2 m.2
          ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law := by
  obtain ⟨A, B, c, hAc, hBc, hAmass, hBmass, hc, hLB⟩ :=
    exists_focalKinetic_collar D hF hw hgap hbounds hε
  have hAm : MeasurableSet A := hAc.isClosed.measurableSet
  have hBm : MeasurableSet B := hBc.isClosed.measurableSet
  have hCm : MeasurableSet (A ×ˢ B) := hAm.prod hBm
  have hmass : legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law
      {m | m.1 ∉ A ×ˢ B} ≤ ENNReal.ofReal (2 * ε) := by
    refine (palm_mass_outside_collar_le Q hAm hBm).trans ?_
    refine (add_le_add hAmass.le hBmass.le).trans_eq ?_
    rw [← ENNReal.ofReal_add hε.le hε.le]
    congr 1
    ring
  have hkin_nonneg : ∀ a b (v : Fin (finrank ℝ S.covector.ker) → ℝ),
      0 ≤ D.originalFocalKinetic gap a b v :=
    fun a b v => D.originalFocalKinetic_nonneg hF hw hgap a b v
  have hw_meas : Measurable (palmCollarWeight (q := finrank ℝ S.covector.ker) (A ×ˢ B)) :=
    measurable_palmCollarWeight hCm
  have hprod_meas : AEStronglyMeasurable
      (fun m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) =>
        ‖m.2‖ ^ 2 * palmCollarWeight (A ×ˢ B) m)
      (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) :=
    (((measurable_norm.comp measurable_snd).pow_const 2).mul hw_meas).aestronglyMeasurable
  have hdom : Integrable (fun m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) =>
      (1 / c) * D.originalFocalKinetic gap m.1.1 m.1.2 m.2)
      (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) :=
    Q.kinetic_integrable.const_mul (1 / c)
  have hbound_le_ae : ∀ᵐ m ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law,
      ‖m.2‖ ^ 2 * palmCollarWeight (A ×ˢ B) m ≤
        (1 / c) * D.originalFocalKinetic gap m.1.1 m.1.2 m.2 := by
    filter_upwards [Q.ae_palm_forward] with m hforward
    have hkin := hkin_nonneg m.1.1 m.1.2 m.2
    by_cases hmem : m.1 ∈ A ×ˢ B
    · rw [palmCollarWeight_eq_one hmem, mul_one]
      have hpair : m.1.1 ∈ A ∧ m.1.2 ∈ B := hmem
      have hlow := hLB m.1.1 hpair.1 m.1.2 hpair.2 hforward m.2
      rw [show (1 / c) * D.originalFocalKinetic gap m.1.1 m.1.2 m.2 =
        D.originalFocalKinetic gap m.1.1 m.1.2 m.2 / c from by ring]
      exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hlow)
    · rw [palmCollarWeight_eq_zero hmem, mul_zero]
      exact mul_nonneg (by positivity) hkin
  have hbound_ae : ∀ᵐ m ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law,
      ‖‖m.2‖ ^ 2 * palmCollarWeight (A ×ˢ B) m‖ ≤
        (1 / c) * D.originalFocalKinetic gap m.1.1 m.1.2 m.2 :=
    hbound_le_ae.mono fun m hm => by
      rwa [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _)
        (palmCollarWeight_nonneg (A ×ˢ B) m))]
  have hint : Integrable (fun m => ‖m.2‖ ^ 2 * palmCollarWeight (A ×ˢ B) m)
      (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) :=
    hdom.mono' hprod_meas hbound_ae
  have hint_le : (∫ m, ‖m.2‖ ^ 2 * palmCollarWeight (A ×ˢ B) m
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≤
      ∫ m, (1 / c) * D.originalFocalKinetic gap m.1.1 m.1.2 m.2
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law :=
    integral_mono_ae hint hdom hbound_le_ae
  have hconst : (∫ m, (1 / c) * D.originalFocalKinetic gap m.1.1 m.1.2 m.2
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) =
      (1 / c) * ∫ m, D.originalFocalKinetic gap m.1.1 m.1.2 m.2
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law :=
    integral_const_mul _ _
  exact ⟨A, B, c, hAc, hBc, hmass, hc, hLB, hint, hint_le.trans_eq hconst⟩

end CollarControl

/-! ## 3. Collar value density implies screening -/

section CollarValueDensity

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- **Collar value density.**  For every positive epsilon there is a
collar-supported weighted stationary matching whose signed value is at most the
weighted pressure plus epsilon, on a collar where the actual focal coefficient
is uniformly positive definite.  This is the exact conclusion of the paper's
reserve construction at one tilt; it is the one remaining analytic input of the
degenerate screening approximation. -/
def CollarValueDensity (D : OriginalSeedConditionalMoments S w μ ν)
    (gap : ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (C : Set (ℝ × ℝ)) (c : ℝ),
    0 < c ∧
    (∀ p ∈ C, p.1 < p.2 → ∀ v : Fin (finrank ℝ S.covector.ker) → ℝ,
      c * ‖v‖ ^ 2 ≤ D.originalFocalKinetic gap p.1 p.2 v) ∧
    ∃ Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
        (D.originalFocalKinetic gap) g,
      (∀ᵐ m ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law, m.1 ∈ C) ∧
      Q.value t ≤ D.originalWeightedStationaryInf gap g t + ε

/-- **Collar value density gives the screening approximation.**  Every weighted
stationary matching is approached in value from above by a finite-second-moment
matching; the collar coercivity of part 1 converts the collar-supported
near-minimizer into a second-moment matching. -/
theorem screening_of_collarValueDensity
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap : ℝ} (hgap : 0 < gap) {g : ℝ → ℝ → ℝ} {G : ℝ}
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ)
    (hCVD : CollarValueDensity D gap g t) :
    ∀ Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
        (D.originalFocalKinetic gap) g,
      ∀ ε : ℝ, 0 < ε →
        ∃ Q' ∈ D.originalSecondMomentSubclass gap g, Q'.value t < Q.value t + ε := by
  intro Q ε hε
  obtain ⟨C, c, hc, hLB, Q', hsupp, hval⟩ := hCVD (ε / 2) (by linarith)
  have hsub : Q' ∈ D.originalSecondMomentSubclass gap g :=
    secondMomentSubclass_of_collar D hc hLB Q' hsupp
  have hIle : D.originalWeightedStationaryInf gap g t ≤ Q.value t :=
    csInf_le (D.originalWeightedStationaryInf_bddBelow hF hw hgap hgb t) ⟨Q, rfl⟩
  exact ⟨Q', hsub, by linarith⟩

/-- **Unconditional order under collar value density.**  The second-moment legal
pressure is at most the weighted legal pressure; together with the unconditional
class order this identifies the two values. -/
theorem originalSecondMomentStationaryInf_le_weightedInf_of_collarValueDensity
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap : ℝ} (hgap : 0 < gap) {g : ℝ → ℝ → ℝ} {G : ℝ}
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ)
    (hCVD : CollarValueDensity D gap g t) :
    D.originalSecondMomentStationaryInf gap g t ≤
      D.originalWeightedStationaryInf gap g t := by
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  obtain ⟨C, c, hc, hLB, Q', hsupp, hval⟩ := hCVD ε hε
  have hsub : Q' ∈ D.originalSecondMomentSubclass gap g :=
    secondMomentSubclass_of_collar D hc hLB Q' hsupp
  have hI2 : D.originalSecondMomentStationaryInf gap g t ≤ Q'.value t :=
    D.originalSecondMomentStationaryInf_le_value hF hw hgap hgb t hsub
  linarith

/-- **The degenerate value identification from collar value density.**  The
literal original focal kinetic cost satisfies I_w = I_2 as soon as collar value
density holds at the tilt.  This is the exact content of the paper's legal
screening step for the degenerate coefficient. -/
theorem originalWeightedStationaryInf_eq_secondMomentInf_of_collarValueDensity
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 4 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (pi : Measure (ℝ × ℝ)) [IsFiniteMeasure pi]
    (hpi : Vlasov.IsCoupling pi μ ν) (horder : ∀ᵐ p ∂pi, p.1 ≤ p.2)
    {G : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ)
    (hCVD : CollarValueDensity D gap g t) :
    D.originalWeightedStationaryInf gap g t =
      D.originalSecondMomentStationaryInf gap g t := by
  have hle := originalSecondMomentStationaryInf_le_weightedInf_of_collarValueDensity
    D hF hw hgap hgb t hCVD
  have hge := D.originalWeightedStationaryInf_le_secondMomentStationaryInf
    hF hw hq hgap hbounds pi hpi horder hg hgb t
  exact le_antisymm hge hle

/-- **Collar-supported values bound the second-moment pressure.**  Every
collar-supported weighted stationary matching is a finite-second-moment
matching, so the second-moment legal pressure is below its signed value.  This
is the unconditional coercivity direction of the paper's screening argument,
valid for the actual degenerate focal coefficient. -/
theorem originalSecondMomentStationaryInf_le_collarValue
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap : ℝ} (hgap : 0 < gap) {g : ℝ → ℝ → ℝ} {G : ℝ}
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ)
    {C : Set (ℝ × ℝ)} {c : ℝ} (hc : 0 < c)
    (hLB : ∀ p ∈ C, p.1 < p.2 → ∀ v : Fin (finrank ℝ S.covector.ker) → ℝ,
      c * ‖v‖ ^ 2 ≤ D.originalFocalKinetic gap p.1 p.2 v)
    {Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g}
    (hQ : ∀ᵐ m ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law, m.1 ∈ C) :
    D.originalSecondMomentStationaryInf gap g t ≤ Q.value t :=
  D.originalSecondMomentStationaryInf_le_value hF hw hgap hgb t
    (secondMomentSubclass_of_collar D hc hLB Q hQ)

end CollarValueDensity

/-! ## 4. Budgets and repair constants -/

section Budgets

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- Reserve replacement of every weighted stationary matching by a
finite-second-moment matching with explicit value budget B.  This is the
quantitative form of the screening approximation. -/
def ReserveReplacementWithin (D : OriginalSeedConditionalMoments S w μ ν)
    (gap : ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ) (B : ℝ) : Prop :=
  ∀ Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g,
    ∃ Q' ∈ D.originalSecondMomentSubclass gap g, Q'.value t ≤ Q.value t + B

/-- The explicit residual-repair value constant supplied by the Neumann repair
estimate legalResidualRepair_absSignedValue_le. -/
def repairValueBudget (rho C : ℝ) : ℝ := rho⁻¹ * C ^ 2 / 2

/-- The retained-plan added-cost constant of repairedRetainedPlan_measureCost_le:
the cost of the repaired residual ports is at most the ambient cost bound L
times the common residual port mass. -/
def retainedPortBudget (L mass : ℝ) : ℝ := L * mass

theorem repairValueBudget_nonneg {rho C : ℝ} (hrho : 0 < rho) :
    0 ≤ repairValueBudget rho C := by
  have : 0 < rho⁻¹ := inv_pos.mpr hrho
  unfold repairValueBudget
  positivity

theorem retainedPortBudget_nonneg {L mass : ℝ} (hL : 0 ≤ L) (hmass : 0 ≤ mass) :
    0 ≤ retainedPortBudget L mass := by
  unfold retainedPortBudget
  exact mul_nonneg hL hmass

/-- **Quantitative value identification with a repair budget.**  A reserve
replacement with explicit value budget B bounds the gap of the two legal
pressures by the same budget. -/
theorem originalSecondMomentStationaryInf_le_weighted_add_of_reserveBudget
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 4 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (pi : Measure (ℝ × ℝ)) [IsFiniteMeasure pi]
    (hpi : Vlasov.IsCoupling pi μ ν) (horder : ∀ᵐ p ∂pi, p.1 ≤ p.2)
    {G : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ)
    {B : ℝ} (hB : ReserveReplacementWithin D gap g t B) :
    D.originalSecondMomentStationaryInf gap g t ≤
      D.originalWeightedStationaryInf gap g t + B :=
  D.originalSecondMomentStationaryInf_le_weighted_add hF hw hq hgap hbounds pi hpi
    horder hg hgb t hB

/-- The gap bound with the explicit Neumann residual-repair constant
rho^{-1} C^2 / 2. -/
theorem originalSecondMomentStationaryInf_le_weighted_add_repairValueBudget
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 4 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (pi : Measure (ℝ × ℝ)) [IsFiniteMeasure pi]
    (hpi : Vlasov.IsCoupling pi μ ν) (horder : ∀ᵐ p ∂pi, p.1 ≤ p.2)
    {G : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ)
    {rho C : ℝ} (hrho : 0 < rho) (hC : 0 ≤ C)
    (hB : ReserveReplacementWithin D gap g t (repairValueBudget rho C)) :
    D.originalSecondMomentStationaryInf gap g t ≤
      D.originalWeightedStationaryInf gap g t + repairValueBudget rho C := by
  have hbudget_nonneg : 0 ≤ repairValueBudget rho C := repairValueBudget_nonneg hrho
  have hC_nonneg : 0 ≤ C := hC
  exact originalSecondMomentStationaryInf_le_weighted_add_of_reserveBudget D hF hw hq
    hgap hbounds pi hpi horder hg hgb t hB

/-- The gap bound with the retained-plan added-cost constant L times the common
residual port mass. -/
theorem originalSecondMomentStationaryInf_le_weighted_add_retainedPortBudget
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 4 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (pi : Measure (ℝ × ℝ)) [IsFiniteMeasure pi]
    (hpi : Vlasov.IsCoupling pi μ ν) (horder : ∀ᵐ p ∂pi, p.1 ≤ p.2)
    {G : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ)
    {L mass : ℝ}
    (hB : ReserveReplacementWithin D gap g t (retainedPortBudget L mass)) :
    D.originalSecondMomentStationaryInf gap g t ≤
      D.originalWeightedStationaryInf gap g t + retainedPortBudget L mass :=
  originalSecondMomentStationaryInf_le_weighted_add_of_reserveBudget D hF hw hq
    hgap hbounds pi hpi horder hg hgb t hB

/-- **Vanishing repair budgets are exactly the screening approximation.**  The
paper sends the reserve density to zero, producing arbitrarily small value
budgets; this equivalence records that form of the remaining input. -/
theorem screening_iff_vanishing_reserveBudget
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap : ℝ} (hgap : 0 < gap) {g : ℝ → ℝ → ℝ} {G : ℝ}
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ)
    (hne : (Set.range (fun Q : LegalWeightedStationaryPoissonMatching
      (finrank ℝ S.covector.ker) μ ν (D.originalFocalKinetic gap) g => Q.value t)).Nonempty) :
    (∀ ε : ℝ, 0 < ε →
        ∃ Q' ∈ D.originalSecondMomentSubclass gap g,
          Q'.value t < D.originalWeightedStationaryInf gap g t + ε)
      ↔ ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 < B ∧ B ≤ ε ∧
          ReserveReplacementWithin D gap g t B := by
  constructor
  · intro hs ε hε
    refine ⟨ε, hε, le_rfl, fun Q => ?_⟩
    obtain ⟨Q', hQ', hlt⟩ := hs ε hε
    have hIle : D.originalWeightedStationaryInf gap g t ≤ Q.value t :=
      csInf_le (D.originalWeightedStationaryInf_bddBelow hF hw hgap hgb t) ⟨Q, rfl⟩
    exact ⟨Q', hQ', by linarith⟩
  · intro hb ε hε
    obtain ⟨B, hB0, hBε, hB⟩ := hb (ε / 2) (by linarith)
    have hbdd : BddBelow (Set.range (fun Q : LegalWeightedStationaryPoissonMatching
        (finrank ℝ S.covector.ker) μ ν (D.originalFocalKinetic gap) g => Q.value t)) :=
      D.originalWeightedStationaryInf_bddBelow hF hw hgap hgb t
    obtain ⟨y, hy, hylt⟩ := exists_lt_of_csInf_lt hne
      (show sInf (Set.range (fun Q : LegalWeightedStationaryPoissonMatching
          (finrank ℝ S.covector.ker) μ ν (D.originalFocalKinetic gap) g => Q.value t)) <
        sInf (Set.range (fun Q : LegalWeightedStationaryPoissonMatching
          (finrank ℝ S.covector.ker) μ ν (D.originalFocalKinetic gap) g => Q.value t)) + B
        from lt_add_of_pos_right _ hB0)
    obtain ⟨Q₀, rfl⟩ := hy
    obtain ⟨Q', hQ', hQ'le⟩ := hB Q₀
    refine ⟨Q', hQ', ?_⟩
    have hIeq : D.originalWeightedStationaryInf gap g t =
        sInf (Set.range (fun Q : LegalWeightedStationaryPoissonMatching
          (finrank ℝ S.covector.ker) μ ν (D.originalFocalKinetic gap) g => Q.value t)) := rfl
    rw [hIeq]
    linarith

end Budgets

end OTSelector.Reconstruction

