import OTSelector.Probability.CavitySemidiscretePressureComparison
import OTSelector.Probability.CavitySemidiscreteTargetBlockPacking
import OTSelector.Probability.CavitySemidiscreteBlockReadout

/-!
# Fixed-cost unrooted integrated cycle witnesses

A finite target-block packing certificate bounds the smaller of two actual block masses
in terms of the optimality excess of a common environment. At opposite good tilts the
excess is at most `t * G`. Integrating these pointwise bounds against the environment
law yields a fixed-cost, unrooted witness estimate: the expected smaller block mass is
controlled by `t * G`, with no reference to the particular optimizer.

The main results are `integral_min_blockMass_le_of_opposite_tilt` for the raw minimum of
the two block masses, and `integral_semidiscreteCycleBlockWitness_le_of_opposite_tilt`
for the version capped at one, which is better behaved for downstream measurability.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators

noncomputable section
namespace OTSelector.Probability

variable {m : ℕ} {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]

/-- A feasible allocation assigns total block mass at most one to any source set and any
finite set of target labels. -/
theorem IsSemidiscreteAllocation.blockMass_le_one
    {μ : Measure S} [IsProbabilityMeasure μ] {p : Fin (m + 1) → ℝ}
    {a : S → Fin (m + 1) → ℝ} (ha : IsSemidiscreteAllocation μ p a)
    (A : Set S) (J : Finset (Fin (m + 1))) :
    semidiscreteBlockMass μ a A J ≤ 1 := by
  classical
  have hterm : ∀ j ∈ J, (∫ s in A, a s j ∂μ) ≤ ∫ s, a s j ∂μ :=
    fun j _ ↦ setIntegral_le_integral (ha.integrable j)
      (ha.nonneg.mono fun s h ↦ h j)
  have hnonneg : ∀ j, 0 ≤ ∫ s, a s j ∂μ :=
    fun j ↦ integral_nonneg_of_ae (ha.nonneg.mono fun s h ↦ h j)
  calc semidiscreteBlockMass μ a A J
      = ∑ j ∈ J, ∫ s in A, a s j ∂μ := rfl
    _ ≤ ∑ j ∈ J, ∫ s, a s j ∂μ := Finset.sum_le_sum hterm
    _ ≤ ∑ j, ∫ s, a s j ∂μ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J)
          (fun j _ _ ↦ hnonneg j)
    _ = 1 := by
        rw [← integral_finsetSum (μ := μ) Finset.univ
          (f := fun (j : Fin (m + 1)) (s : S) ↦ a s j)
          (fun j _ ↦ ha.integrable j)]
        rw [integral_congr_ae ha.sum_one, integral_const, measureReal_def,
          measure_univ]
        simp

/-- The half-average of two jointly measurable allocations is jointly measurable. -/
theorem measurable_halfAverage_coefficient
    (aplus aminus : Ω → S → Fin (m + 1) → ℝ)
    (hpm : ∀ j, Measurable (fun v : Ω × S ↦ aplus v.1 v.2 j))
    (hmm : ∀ j, Measurable (fun v : Ω × S ↦ aminus v.1 v.2 j)) :
    ∀ j, Measurable (fun x : Ω × S ↦ (aplus x.1 x.2 j + aminus x.1 x.2 j) / 2) :=
  fun j ↦ ((hpm j).add (hmm j)).div_const 2

/-- Membership of a fixed label in a fixed finite set is measurable in the parameter
space. -/
theorem measurableSet_mem_finset_param (J : Finset (Fin (m + 1)))
    (j : Fin (m + 1)) :
    MeasurableSet {z : Ω | j ∈ J} := by
  by_cases hj : j ∈ J
  · convert (MeasurableSet.univ : MeasurableSet (Set.univ : Set Ω)) using 1
    ext _z
    simp [hj]
  · convert (MeasurableSet.empty : MeasurableSet (∅ : Set Ω)) using 1
    ext _z
    simp [hj]

/-- The actual block mass of the half-average allocation is measurable in the
environment. -/
theorem measurable_halfAverage_semidiscreteBlockMass
    (μ : Measure S) [SFinite μ] (aplus aminus : Ω → S → Fin (m + 1) → ℝ)
    (hpm : ∀ j, Measurable (fun v : Ω × S ↦ aplus v.1 v.2 j))
    (hmm : ∀ j, Measurable (fun v : Ω × S ↦ aminus v.1 v.2 j))
    (A : Set S) (hA : MeasurableSet A) (J : Finset (Fin (m + 1))) :
    Measurable (fun ω ↦ semidiscreteBlockMass μ
      (fun s j ↦ (aplus ω s j + aminus ω s j) / 2) A J) := by
  classical
  have ha := measurable_halfAverage_coefficient aplus aminus hpm hmm
  have hA' : MeasurableSet {x : Ω × S | x.2 ∈ A} := hA.preimage measurable_snd
  have hJ' : ∀ j, MeasurableSet {z : Ω | j ∈ J} :=
    fun j ↦ measurableSet_mem_finset_param J j
  have h := measurable_parameterized_semidiscreteBlockMass (μ := μ) (m := m) (V := Ω)
    (a := fun x : Ω × S ↦ fun j ↦ (aplus x.1 x.2 j + aminus x.1 x.2 j) / 2)
    ha (fun _ ↦ A) hA' (fun _ ↦ J) hJ'
  simpa only using h

/-- The cycle block witness of the half-average allocation is measurable in the
environment. -/
theorem measurable_halfAverage_semidiscreteCycleBlockWitness
    (μ : Measure S) [SFinite μ] (aplus aminus : Ω → S → Fin (m + 1) → ℝ)
    (hpm : ∀ j, Measurable (fun v : Ω × S ↦ aplus v.1 v.2 j))
    (hmm : ∀ j, Measurable (fun v : Ω × S ↦ aminus v.1 v.2 j))
    (A0 A1 : Set S) (hA0 : MeasurableSet A0) (hA1 : MeasurableSet A1)
    (J L : Finset (Fin (m + 1))) :
    Measurable (fun ω ↦ semidiscreteCycleBlockWitness μ
      (fun s j ↦ (aplus ω s j + aminus ω s j) / 2) A0 A1 J L) := by
  classical
  have ha := measurable_halfAverage_coefficient aplus aminus hpm hmm
  have hA0' : MeasurableSet {x : Ω × S | x.2 ∈ A0} := hA0.preimage measurable_snd
  have hA1' : MeasurableSet {x : Ω × S | x.2 ∈ A1} := hA1.preimage measurable_snd
  have hJ' : ∀ j, MeasurableSet {z : Ω | j ∈ J} :=
    fun j ↦ measurableSet_mem_finset_param J j
  have hL' : ∀ j, MeasurableSet {z : Ω | j ∈ L} :=
    fun j ↦ measurableSet_mem_finset_param L j
  have h := measurable_parameterized_semidiscreteCycleBlockWitness (μ := μ) (m := m)
    (V := Ω) (a := fun x : Ω × S ↦ fun j ↦ (aplus x.1 x.2 j + aminus x.1 x.2 j) / 2)
    ha (fun _ ↦ A0) (fun _ ↦ A1) hA0' hA1' (fun _ ↦ J) (fun _ ↦ L) hJ' hL'
  simpa only using h

/-- The minimum of the two half-average block masses is integrable. -/
theorem integrable_halfAverage_semidiscreteBlockMass_min
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure S) [IsProbabilityMeasure μ] (p : Ω → Fin (m + 1) → ℝ)
    (aplus aminus : Ω → S → Fin (m + 1) → ℝ)
    (hpm : ∀ j, Measurable (fun v : Ω × S ↦ aplus v.1 v.2 j))
    (hmm : ∀ j, Measurable (fun v : Ω × S ↦ aminus v.1 v.2 j))
    (hfeas : ∀ᵐ ω ∂P,
      IsSemidiscreteAllocation μ (p ω) (fun s j ↦ (aplus ω s j + aminus ω s j) / 2))
    (A0 A1 : Set S) (hA0 : MeasurableSet A0) (hA1 : MeasurableSet A1)
    (J L : Finset (Fin (m + 1))) :
    Integrable (fun ω ↦ min
      (semidiscreteBlockMass μ (fun s j ↦ (aplus ω s j + aminus ω s j) / 2) A0 J)
      (semidiscreteBlockMass μ (fun s j ↦ (aplus ω s j + aminus ω s j) / 2) A1 L)) P := by
  classical
  have h0 := measurable_halfAverage_semidiscreteBlockMass μ aplus aminus hpm hmm A0 hA0 J
  have h1 := measurable_halfAverage_semidiscreteBlockMass μ aplus aminus hpm hmm A1 hA1 L
  have hmeas : Measurable (fun ω ↦ min
      (semidiscreteBlockMass μ (fun s j ↦ (aplus ω s j + aminus ω s j) / 2) A0 J)
      (semidiscreteBlockMass μ (fun s j ↦ (aplus ω s j + aminus ω s j) / 2) A1 L)) :=
    h0.min h1
  refine Integrable.of_bound hmeas.aestronglyMeasurable 1 ?_
  filter_upwards [hfeas] with ω hω
  have hb0 := hω.blockMass_nonneg A0 J
  have hb1 := hω.blockMass_nonneg A1 L
  have hle := hω.blockMass_le_one A0 J
  have hnonneg : 0 ≤ min
      (semidiscreteBlockMass μ (fun s j ↦ (aplus ω s j + aminus ω s j) / 2) A0 J)
      (semidiscreteBlockMass μ (fun s j ↦ (aplus ω s j + aminus ω s j) / 2) A1 L) :=
    le_min hb0 hb1
  have hleone : min
      (semidiscreteBlockMass μ (fun s j ↦ (aplus ω s j + aminus ω s j) / 2) A0 J)
      (semidiscreteBlockMass μ (fun s j ↦ (aplus ω s j + aminus ω s j) / 2) A1 L) ≤ 1 :=
    (min_le_left _ _).trans hle
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact hleone

/-- The bounded cycle witness of the half-average allocation is integrable. -/
theorem integrable_halfAverage_semidiscreteCycleBlockWitness
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure S) [IsProbabilityMeasure μ] (p : Ω → Fin (m + 1) → ℝ)
    (aplus aminus : Ω → S → Fin (m + 1) → ℝ)
    (hpm : ∀ j, Measurable (fun v : Ω × S ↦ aplus v.1 v.2 j))
    (hmm : ∀ j, Measurable (fun v : Ω × S ↦ aminus v.1 v.2 j))
    (hfeas : ∀ᵐ ω ∂P,
      IsSemidiscreteAllocation μ (p ω) (fun s j ↦ (aplus ω s j + aminus ω s j) / 2))
    (A0 A1 : Set S) (hA0 : MeasurableSet A0) (hA1 : MeasurableSet A1)
    (J L : Finset (Fin (m + 1))) :
    Integrable (fun ω ↦ semidiscreteCycleBlockWitness μ
      (fun s j ↦ (aplus ω s j + aminus ω s j) / 2) A0 A1 J L) P := by
  classical
  have hmeas := measurable_halfAverage_semidiscreteCycleBlockWitness μ aplus aminus
    hpm hmm A0 A1 hA0 hA1 J L
  refine Integrable.of_bound hmeas.aestronglyMeasurable 1 ?_
  filter_upwards [hfeas] with ω hω
  have hnonneg : 0 ≤ semidiscreteCycleBlockWitness μ
      (fun s j ↦ (aplus ω s j + aminus ω s j) / 2) A0 A1 J L :=
    hω.cycleBlockWitness_nonneg A0 A1 J L
  have hleone : semidiscreteCycleBlockWitness μ
      (fun s j ↦ (aplus ω s j + aminus ω s j) / 2) A0 A1 J L ≤ 1 :=
    semidiscreteCycleBlockWitness_le_one μ _ A0 A1 J L
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact hleone

/-- Fixed-cost unrooted integrated witness bound: at opposite good tilts, the expected
smaller of the two actual half-average block masses is at most `t * G`. -/
theorem integral_min_blockMass_le_of_opposite_tilt
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (p : Ω → Fin (m + 1) → ℝ)
    (c g : S → Fin (m + 1) → ℝ)
    (a0 aplus aminus : Ω → S → Fin (m + 1) → ℝ)
    (t G eps : ℝ) (ht : 0 ≤ t) (heps : 0 ≤ eps)
    (hp : Measurable p)
    (h0m : ∀ j, Measurable (fun v : Ω × S ↦ a0 v.1 v.2 j))
    (hpm : ∀ j, Measurable (fun v : Ω × S ↦ aplus v.1 v.2 j))
    (hmm : ∀ j, Measurable (fun v : Ω × S ↦ aminus v.1 v.2 j))
    (hopt : ∀ᵐ ω ∂P,
      IsOptimalSemidiscreteAllocation μ (p ω) c (a0 ω) ∧
      IsOptimalSemidiscreteAllocation μ (p ω) (fun s j ↦ c s j + t * g s j) (aplus ω) ∧
      IsOptimalSemidiscreteAllocation μ (p ω) (fun s j ↦ c s j - t * g s j) (aminus ω))
    (hc : ∀ j, Integrable (fun s ↦ c s j) μ)
    (hg : ∀ j, Integrable (fun s ↦ g s j) μ)
    (hbound : ∀ᵐ s ∂μ, ∀ j, |g s j| ≤ G)
    (A0 A1 : Set S) (hA0 : MeasurableSet A0) (hA1 : MeasurableSet A1)
    (hdisj : Disjoint A0 A1)
    (J L : Finset (Fin (m + 1)))
    (hgap : ∀ s ∈ A0, ∀ s' ∈ A1, ∀ j ∈ J, ∀ k ∈ L,
      eps ≤ c s j + c s' k - c s k - c s' j) :
    eps * (∫ ω, min
      (semidiscreteBlockMass μ (fun s j ↦ (aplus ω s j + aminus ω s j) / 2) A0 J)
      (semidiscreteBlockMass μ (fun s j ↦ (aplus ω s j + aminus ω s j) / 2) A1 L) ∂P)
      ≤ t * G := by
  classical
  let B : Ω → ℝ := fun ω ↦ min
    (semidiscreteBlockMass μ (fun s j ↦ (aplus ω s j + aminus ω s j) / 2) A0 J)
    (semidiscreteBlockMass μ (fun s j ↦ (aplus ω s j + aminus ω s j) / 2) A1 L)
  have hfeas : ∀ᵐ ω ∂P,
      IsSemidiscreteAllocation μ (p ω) (fun s j ↦ (aplus ω s j + aminus ω s j) / 2) :=
    hopt.mono fun ω hω ↦ hω.2.1.1.average hω.2.2.1
  have hBint : Integrable B P :=
    integrable_halfAverage_semidiscreteBlockMass_min P μ p aplus aminus hpm hmm
      hfeas A0 A1 hA0 hA1 J L
  have hpoint : ∀ᵐ ω ∂P, eps * B ω ≤ t * G := by
    filter_upwards [hopt] with ω hω
    obtain ⟨h0opt, hplusopt, hminusopt⟩ := hω
    have hminus' : IsOptimalSemidiscreteAllocation μ (p ω)
        (fun s j ↦ c s j + (-t) * g s j) (aminus ω) := by
      have hEq : (fun s j ↦ c s j + (-t) * g s j) =
          (fun s j ↦ c s j - t * g s j) := by
        funext s j
        ring
      rw [hEq]
      exact hminusopt
    have hsingle := semidiscrete_opposite_tilt_target_block_packing_le μ (p ω) c g
      (a0 ω) (aplus ω) (aminus ω) t G ht h0opt hplusopt hminus' hc hg hbound
      (fun _ : Unit ↦ J) (fun _ ↦ L) (fun _ ↦ A0) (fun _ ↦ A1)
      (fun _ ↦ hA0) (fun _ ↦ hA1) (fun _ ↦ hdisj)
      (fun i k (hik : i ≠ k) ↦ (hik (Subsingleton.elim i k)).elim)
      (fun _ ↦ eps) (fun _ ↦ hgap)
    simpa [B, Fintype.sum_unique] using hsingle
  calc eps * (∫ ω, B ω ∂P) = ∫ ω, eps * B ω ∂P :=
        (integral_const_mul eps B).symm
    _ ≤ ∫ ω, t * G ∂P :=
        integral_mono_ae (hBint.const_mul eps) (integrable_const (t * G)) hpoint
    _ = t * G := by
        rw [integral_const, measureReal_def, measure_univ]
        simp

/-- Fixed-cost unrooted integrated witness bound in capped form: the expected
`min 1` of the two actual half-average block masses is at most `t * G`. -/
theorem integral_semidiscreteCycleBlockWitness_le_of_opposite_tilt
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (p : Ω → Fin (m + 1) → ℝ)
    (c g : S → Fin (m + 1) → ℝ)
    (a0 aplus aminus : Ω → S → Fin (m + 1) → ℝ)
    (t G eps : ℝ) (ht : 0 ≤ t) (heps : 0 ≤ eps)
    (hp : Measurable p)
    (h0m : ∀ j, Measurable (fun v : Ω × S ↦ a0 v.1 v.2 j))
    (hpm : ∀ j, Measurable (fun v : Ω × S ↦ aplus v.1 v.2 j))
    (hmm : ∀ j, Measurable (fun v : Ω × S ↦ aminus v.1 v.2 j))
    (hopt : ∀ᵐ ω ∂P,
      IsOptimalSemidiscreteAllocation μ (p ω) c (a0 ω) ∧
      IsOptimalSemidiscreteAllocation μ (p ω) (fun s j ↦ c s j + t * g s j) (aplus ω) ∧
      IsOptimalSemidiscreteAllocation μ (p ω) (fun s j ↦ c s j - t * g s j) (aminus ω))
    (hc : ∀ j, Integrable (fun s ↦ c s j) μ)
    (hg : ∀ j, Integrable (fun s ↦ g s j) μ)
    (hbound : ∀ᵐ s ∂μ, ∀ j, |g s j| ≤ G)
    (A0 A1 : Set S) (hA0 : MeasurableSet A0) (hA1 : MeasurableSet A1)
    (hdisj : Disjoint A0 A1)
    (J L : Finset (Fin (m + 1)))
    (hgap : ∀ s ∈ A0, ∀ s' ∈ A1, ∀ j ∈ J, ∀ k ∈ L,
      eps ≤ c s j + c s' k - c s k - c s' j) :
    eps * (∫ ω, semidiscreteCycleBlockWitness μ
      (fun s j ↦ (aplus ω s j + aminus ω s j) / 2) A0 A1 J L ∂P) ≤ t * G := by
  classical
  let B : Ω → ℝ := fun ω ↦ min
    (semidiscreteBlockMass μ (fun s j ↦ (aplus ω s j + aminus ω s j) / 2) A0 J)
    (semidiscreteBlockMass μ (fun s j ↦ (aplus ω s j + aminus ω s j) / 2) A1 L)
  let C : Ω → ℝ := fun ω ↦ semidiscreteCycleBlockWitness μ
    (fun s j ↦ (aplus ω s j + aminus ω s j) / 2) A0 A1 J L
  have hfeas : ∀ᵐ ω ∂P,
      IsSemidiscreteAllocation μ (p ω) (fun s j ↦ (aplus ω s j + aminus ω s j) / 2) :=
    hopt.mono fun ω hω ↦ hω.2.1.1.average hω.2.2.1
  have hCint : Integrable C P :=
    integrable_halfAverage_semidiscreteCycleBlockWitness P μ p aplus aminus hpm hmm
      hfeas A0 A1 hA0 hA1 J L
  have hBint : Integrable B P :=
    integrable_halfAverage_semidiscreteBlockMass_min P μ p aplus aminus hpm hmm
      hfeas A0 A1 hA0 hA1 J L
  have hCB : C ≤ᵐ[P] B :=
    Eventually.of_forall fun ω ↦ by
      dsimp only [C, B, semidiscreteCycleBlockWitness]
      exact min_le_right _ _
  have hIntle : ∫ ω, C ω ∂P ≤ ∫ ω, B ω ∂P := integral_mono_ae hCint hBint hCB
  exact (mul_le_mul_of_nonneg_left hIntle heps).trans
    (integral_min_blockMass_le_of_opposite_tilt P μ p c g a0 aplus aminus t G eps
      ht heps hp h0m hpm hmm hopt hc hg hbound A0 A1 hA0 hA1 hdisj J L hgap)

end OTSelector.Probability
