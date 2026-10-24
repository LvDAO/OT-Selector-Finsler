import OTSelector.Probability.CavitySemidiscretePressureComparison
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedAverageScreenedPacking

/-!
# Original average packing with both physical endpoint masks

The actual original global allocations are restricted to a physical source-target
rectangle. The target mask becomes an additional condition on the original finite
column screens; the original random columns and the original optimizers persist.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
  OTSelector.Probability
open scoped Topology ContDiff ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {ι M : Type*} [Fintype ι] [MeasurableSpace M] {n : ℕ}

/-- Restricting both original physical endpoints gives exactly the masked original
column blocks, with no change to the global allocation or its column vector. -/
theorem physicalSceneRootedPlan_allocation_restrict_masked_prod
    {μ : Measure M} {p : Fin (n + 1) → ℝ} {a : M → Fin (n + 1) → ℝ}
    (ha : IsSemidiscreteAllocation μ p a) (Y : Fin (n + 1) → M)
    (H Kt : Set M) (hH : MeasurableSet H) (hKt : MeasurableSet Kt)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (z : ι → ℝ)
    (A B : Set ((ι → ℝ) × ℝ)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    physicalSceneRootedPlan ((physicalSceneAllocationPlan μ a Y).restrict (H ×ˢ Kt))
      coord u N z (A ×ˢ B) =
      ENNReal.ofReal N * ENNReal.ofReal (semidiscreteBlockMass μ a
        (H ∩ (fun x ↦ (coord x - z, u x)) ⁻¹' A)
        (Finset.univ.filter (fun j ↦ Y j ∈ Kt ∧ (coord (Y j) - z, u (Y j)) ∈ B))) := by
  let f := fun x ↦ (coord x - z, u x)
  have hf : Measurable f := (hcoord.sub measurable_const).prodMk hu
  have ho := measurable_physicalSceneRootedObservation coord hcoord u hu z
  have hY : Measurable (Prod.map (id : M → M) Y) :=
    measurable_id.prodMap (measurable_of_finite Y)
  unfold physicalSceneRootedPlan
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply ho (hA.prod hB),
    Measure.restrict_apply ((hA.prod hB).preimage ho)]
  unfold physicalSceneAllocationPlan
  rw [Measure.map_apply hY (((hA.prod hB).preimage ho).inter (hH.prod hKt))]
  have heq : (Prod.map (id : M → M) Y) ⁻¹'
      ((physicalSceneRootedObservation coord u z ⁻¹' (A ×ˢ B)) ∩ (H ×ˢ Kt)) =
      (H ∩ f ⁻¹' A) ×ˢ
        (↑(Finset.univ.filter (fun j ↦ Y j ∈ Kt ∧ f (Y j) ∈ B)) : Set (Fin (n + 1))) := by
    ext v
    simp only [mem_preimage, mem_inter_iff, mem_prod,
      physicalSceneRootedObservation, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and, f]
    tauto
  rw [heq, ha.allocationMeasure_prod _ (hH.inter (hA.preimage hf))]

/-- The original coefficient average commutes with any physical endpoint restriction. -/
theorem physicalSceneRootedPlan_allocation_restrict_masked_average
    (μ : Measure M) (p : Fin (n + 1) → ℝ) (ap am : M → Fin (n + 1) → ℝ)
    (hp : IsSemidiscreteAllocation μ p ap) (hm : IsSemidiscreteAllocation μ p am)
    (hpm : ∀ j, Measurable (fun x ↦ ap x j))
    (hmm : ∀ j, Measurable (fun x ↦ am x j))
    (Y : Fin (n + 1) → M) (H Kt : Set M)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord) (u : M → ℝ) (hu : Measurable u)
    (N : ℝ) (z : ι → ℝ) :
    physicalSceneRootedPlan
      ((physicalSceneAllocationPlan μ (fun x j ↦ (ap x j + am x j) / 2) Y).restrict (H ×ˢ Kt))
      coord u N z = (2 : ℝ≥0∞)⁻¹ •
        (physicalSceneRootedPlan ((physicalSceneAllocationPlan μ ap Y).restrict (H ×ˢ Kt))
          coord u N z +
         physicalSceneRootedPlan ((physicalSceneAllocationPlan μ am Y).restrict (H ×ˢ Kt))
          coord u N z) := by
  have hY : Measurable (Prod.map (id : M → M) Y) :=
    measurable_id.prodMap (measurable_of_finite Y)
  have hobs := measurable_physicalSceneRootedObservation coord hcoord u hu z
  unfold physicalSceneRootedPlan physicalSceneAllocationPlan
  rw [semidiscreteAllocationMeasure_average μ p ap am hp hm hpm hmm]
  simp only [Measure.map_smul, Measure.map_add _ _ hY, Measure.restrict_smul,
    Measure.restrict_add, Measure.map_add _ _ hobs, smul_add, smul_smul]
  rw [mul_comm (ENNReal.ofReal N) ((2 : ℝ≥0∞)⁻¹)]

/-- Both masked rooted rectangle masses give exactly the original normalized
allocation block witness with the additional physical target screen. -/
theorem physicalSceneRootedPlan_allocation_restrict_masked_cycle_witness
    {μ : Measure M} {p : Fin (n + 1) → ℝ} {a : M → Fin (n + 1) → ℝ}
    (ha : IsSemidiscreteAllocation μ p a) (Y : Fin (n + 1) → M)
    (H Kt : Set M) (hH : MeasurableSet H) (hKt : MeasurableSet Kt)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord) (u : M → ℝ) (hu : Measurable u)
    (N : ℝ) (hN : 0 ≤ N) (z : ι → ℝ)
    (A₀ A₁ B₀ B₁ : Set ((ι → ℝ) × ℝ))
    (hA₀ : MeasurableSet A₀) (hA₁ : MeasurableSet A₁)
    (hB₀ : MeasurableSet B₀) (hB₁ : MeasurableSet B₁) :
    min 1 (min
      (physicalSceneRootedPlan ((physicalSceneAllocationPlan μ a Y).restrict (H ×ˢ Kt))
        coord u N z (A₀ ×ˢ B₀))
      (physicalSceneRootedPlan ((physicalSceneAllocationPlan μ a Y).restrict (H ×ˢ Kt))
        coord u N z (A₁ ×ˢ B₁))) =
      ENNReal.ofReal (min 1 (N * min
        (semidiscreteBlockMass μ a (H ∩ (fun x ↦ (coord x - z, u x)) ⁻¹' A₀)
          (Finset.univ.filter (fun j ↦ Y j ∈ Kt ∧ (coord (Y j) - z, u (Y j)) ∈ B₀)))
        (semidiscreteBlockMass μ a (H ∩ (fun x ↦ (coord x - z, u x)) ⁻¹' A₁)
          (Finset.univ.filter (fun j ↦ Y j ∈ Kt ∧ (coord (Y j) - z, u (Y j)) ∈ B₁))))) := by
  rw [physicalSceneRootedPlan_allocation_restrict_masked_prod ha Y H Kt hH hKt
      coord hcoord u hu N z A₀ B₀ hA₀ hB₀,
    physicalSceneRootedPlan_allocation_restrict_masked_prod ha Y H Kt hH hKt
      coord hcoord u hu N z A₁ B₁ hA₁ hB₁]
  simp only [mul_min_of_nonneg _ _ hN, ENNReal.ofReal_min,
    ENNReal.ofReal_mul hN, ENNReal.ofReal_one]

/-- Original global optimality controls the exact average of the two plans
restricted to `(H ∩ Ks) ×ˢ Kt`. The original cost certificate is only required
on the retained physical endpoints and screened roots. The bound is independent of `N`. -/
theorem lintegral_original_cost_rooted_average_screened_masked_rectangle_witness_le
    (μ : Measure M) [IsProbabilityMeasure μ] (p : Fin (n + 1) → ℝ)
    (c g ap am : M → Fin (n + 1) → ℝ) (t G : ℝ) (ht : 0 ≤ t)
    (hbase : ∃ a₀, IsOptimalSemidiscreteAllocation μ p c a₀)
    (hp : IsOptimalSemidiscreteAllocation μ p (fun x j ↦ c x j + t * g x j) ap)
    (hm : IsOptimalSemidiscreteAllocation μ p (fun x j ↦ c x j + (-t) * g x j) am)
    (hc : ∀ j, Integrable (fun x ↦ c x j) μ)
    (hg : ∀ j, Integrable (fun x ↦ g x j) μ)
    (hbound : ∀ᵐ x ∂μ, ∀ j, |g x j| ≤ G)
    (hpm : ∀ j, Measurable (fun x ↦ ap x j))
    (hmm : ∀ j, Measurable (fun x ↦ am x j))
    (Y : Fin (n + 1) → M) (H Ks Kt : Set M) (hH : MeasurableSet H)
    (hKs : MeasurableSet Ks) (hKt : MeasurableSet Kt)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord) (u : M → ℝ) (hu : Measurable u)
    (A₀ A₁ B₀ B₁ : Set ((ι → ℝ) × ℝ))
    (hA₀ : MeasurableSet A₀) (hA₁ : MeasurableSet A₁)
    (hB₀ : MeasurableSet B₀) (hB₁ : MeasurableSet B₁) (hdisj : Disjoint A₀ A₁)
    (K : ℝ) (hK : 0 < K) (offset : ι → ℝ)
    (hbox : ∀ s ∈ A₀ ∪ A₁, s.1 - offset ∈ cavityGridPhaseCell ι K)
    (Eroot : Set (ι → ℝ)) (hEroot : MeasurableSet Eroot)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hgap : ∀ z ∈ Eroot, ∀ x ∈ (H ∩ Ks), ∀ x' ∈ (H ∩ Ks),
      (coord x - z, u x) ∈ A₀ → (coord x' - z, u x') ∈ A₁ →
      ∀ j, Y j ∈ Kt → (coord (Y j) - z, u (Y j)) ∈ B₀ →
      ∀ l, Y l ∈ Kt → (coord (Y l) - z, u (Y l)) ∈ B₁ →
        ε ≤ c x j + c x' l - c x l - c x' j)
    (D : Set (ι → ℝ)) (N : ℝ) (hN : 0 < N) :
    let avg := fun z : ι → ℝ ↦ (2 : ℝ≥0∞)⁻¹ •
      (physicalSceneRootedPlan ((physicalSceneAllocationPlan μ ap Y).restrict ((H ∩ Ks) ×ˢ Kt))
        coord u N z +
       physicalSceneRootedPlan ((physicalSceneAllocationPlan μ am Y).restrict ((H ∩ Ks) ×ˢ Kt))
        coord u N z)
    (∫⁻ z, Eroot.indicator (fun z ↦ ENNReal.ofReal ε *
      min 1 (min (avg z (A₀ ×ˢ B₀)) (avg z (A₁ ×ˢ B₁)))) z
      ∂cavityRootMeasure volume D N) ≤
      ENNReal.ofReal (t * G) * ENNReal.ofReal K ^ Fintype.card ι := by
  obtain ⟨a₀, h₀⟩ := hbase
  let obs := fun z (x : M) ↦ (coord x - z, u x)
  let AA := fun z ↦ if z ∈ Eroot then (H ∩ Ks) ∩ obs z ⁻¹' A₀ else ∅
  let AB := fun z ↦ if z ∈ Eroot then (H ∩ Ks) ∩ obs z ⁻¹' A₁ else ∅
  let J := fun z ↦ Finset.univ.filter (fun j ↦ Y j ∈ Kt ∧ obs z (Y j) ∈ B₀)
  let L := fun z ↦ Finset.univ.filter (fun j ↦ Y j ∈ Kt ∧ obs z (Y j) ∈ B₁)
  have hobs : Measurable (fun v : (ι → ℝ) × M ↦ obs v.1 v.2) :=
    ((hcoord.comp measurable_snd).sub measurable_fst).prodMk (hu.comp measurable_snd)
  have hAA : MeasurableSet {v : (ι → ℝ) × M | v.2 ∈ AA v.1} := by
    have heq : {v : (ι → ℝ) × M | v.2 ∈ AA v.1} =
        {v | v.1 ∈ Eroot} ∩ {v | v.2 ∈ (H ∩ Ks) ∩ obs v.1 ⁻¹' A₀} := by
      ext v
      by_cases hz : v.1 ∈ Eroot <;> simp [AA, hz]
    rw [heq]
    exact (hEroot.preimage measurable_fst).inter
      (((hH.inter hKs).preimage measurable_snd).inter (hA₀.preimage hobs))
  have hAB : MeasurableSet {v : (ι → ℝ) × M | v.2 ∈ AB v.1} := by
    have heq : {v : (ι → ℝ) × M | v.2 ∈ AB v.1} =
        {v | v.1 ∈ Eroot} ∩ {v | v.2 ∈ (H ∩ Ks) ∩ obs v.1 ⁻¹' A₁} := by
      ext v
      by_cases hz : v.1 ∈ Eroot <;> simp [AB, hz]
    rw [heq]
    exact (hEroot.preimage measurable_fst).inter
      (((hH.inter hKs).preimage measurable_snd).inter (hA₁.preimage hobs))
  have hJ (j : Fin (n + 1)) : MeasurableSet {z | j ∈ J z} := by
    simp only [J, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hj : Y j ∈ Kt
    · simp only [hj, true_and]
      exact hB₀.preimage (hobs.comp (measurable_id.prodMk measurable_const))
    · simp only [hj, false_and, ofPred_false, MeasurableSet.empty]
  have hL (j : Fin (n + 1)) : MeasurableSet {z | j ∈ L z} := by
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hj : Y j ∈ Kt
    · simp only [hj, true_and]
      exact hB₁.preimage (hobs.comp (measurable_id.prodMk measurable_const))
    · simp only [hj, false_and, ofPred_false, MeasurableSet.empty]
  have hcell : ∀ z, AA z ∪ AB z ⊆ (fun x ↦ coord x - offset) ⁻¹' cavityGridCube ι K z := by
    intro z x hx
    have hz : z ∈ Eroot := by
      by_contra hn
      simp [AA, AB, hn] at hx
    have hx' : x ∈ ((H ∩ Ks) ∩ obs z ⁻¹' A₀) ∪ ((H ∩ Ks) ∩ obs z ⁻¹' A₁) := by
      simpa only [AA, AB, ite_eq_left hz] using hx
    have hs : obs z x ∈ A₀ ∪ A₁ := hx'.elim (fun h ↦ Or.inl h.2) (fun h ↦ Or.inr h.2)
    have hb := hbox (obs z x) hs
    change (coord x - offset) - z ∈ cavityGridPhaseCell ι K
    simpa only [obs, sub_right_comm] using hb
  have hb := lintegral_cavityRoot_opposite_tilt_cycle_witness_le μ p c g a₀ ap am t G ht
    h₀ hp hm hc hg hbound hpm hmm (fun x ↦ coord x - offset) K hK AA AB hAA hAB
    (fun z ↦ by
      by_cases hz : z ∈ Eroot
      · simpa only [AA, AB, ite_eq_left hz] using
          (hdisj.preimage (obs z)).mono inter_subset_right inter_subset_right
      · simp [AA, AB, hz])
    hcell J L hJ hL ε hε (by
      intro z x hx x' hx' j hj l hl
      by_cases hz : z ∈ Eroot
      · have hxA : x ∈ (H ∩ Ks) ∩ obs z ⁻¹' A₀ := by simpa only [AA, ite_eq_left hz] using hx
        have hxB : x' ∈ (H ∩ Ks) ∩ obs z ⁻¹' A₁ := by simpa only [AB, ite_eq_left hz] using hx'
        exact hgap z hz x hxA.1 x' hxB.1 hxA.2 hxB.2 j (Finset.mem_filter.mp hj).2.1
          (Finset.mem_filter.mp hj).2.2 l (Finset.mem_filter.mp hl).2.1
          (Finset.mem_filter.mp hl).2.2
      · simp [AA, hz] at hx) D N hN
  convert hb using 1
  apply lintegral_congr
  intro z
  dsimp only
  by_cases hz : z ∈ Eroot
  · rw [indicator_of_mem hz]
    rw [← physicalSceneRootedPlan_allocation_restrict_masked_average μ p ap am hp.1 hm.1 hpm hmm
      Y (H ∩ Ks) Kt coord hcoord u hu N z,
    physicalSceneRootedPlan_allocation_restrict_masked_cycle_witness (hp.1.average hm.1)
      Y (H ∩ Ks) Kt (hH.inter hKs) hKt coord hcoord u hu N hN.le z A₀ A₁ B₀ B₁ hA₀ hA₁ hB₀ hB₁,
      ← ENNReal.ofReal_mul hε]
    simp only [AA, AB, obs, J, L, ite_eq_left hz]
  · simp [AA, AB, hz, semidiscreteBlockMass]


/-- Original cost atomlessness supplies the base optimizer internally on one
Dirichlet full-measure event. Every actual choice from both tilted optimal
faces then satisfies the original physical-cost rooted average bound. -/
theorem ae_dirichlet_original_cost_rooted_average_screened_masked_rectangle_witness_le
    [StandardBorelSpace M]
    (μ : Measure M) [IsProbabilityMeasure μ]
    (c g : M → Fin (n + 1) → ℝ) (t G : ℝ) (ht : 0 ≤ t)
    (hcm : ∀ j, Measurable (fun x ↦ c x j))
    (hc : ∀ j, Integrable (fun x ↦ c x j) μ)
    (hatom : ∀ j l, j ≠ l → NullSingletonClass (μ.map (fun x ↦ c x j - c x l)))
    (hg : ∀ j, Integrable (fun x ↦ g x j) μ)
    (hbound : ∀ᵐ x ∂μ, ∀ j, |g x j| ≤ G)
    (Y : Fin (n + 1) → M) (H Ks Kt : Set M) (hH : MeasurableSet H)
    (hKs : MeasurableSet Ks) (hKt : MeasurableSet Kt)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord) (u : M → ℝ) (hu : Measurable u)
    (A₀ A₁ B₀ B₁ : Set ((ι → ℝ) × ℝ))
    (hA₀ : MeasurableSet A₀) (hA₁ : MeasurableSet A₁)
    (hB₀ : MeasurableSet B₀) (hB₁ : MeasurableSet B₁) (hdisj : Disjoint A₀ A₁)
    (K : ℝ) (hK : 0 < K) (offset : ι → ℝ)
    (hbox : ∀ s ∈ A₀ ∪ A₁, s.1 - offset ∈ cavityGridPhaseCell ι K)
    (Eroot : Set (ι → ℝ)) (hEroot : MeasurableSet Eroot)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hgap : ∀ z ∈ Eroot, ∀ x ∈ (H ∩ Ks), ∀ x' ∈ (H ∩ Ks),
      (coord x - z, u x) ∈ A₀ → (coord x' - z, u x') ∈ A₁ →
      ∀ j, Y j ∈ Kt → (coord (Y j) - z, u (Y j)) ∈ B₀ →
      ∀ l, Y l ∈ Kt → (coord (Y l) - z, u (Y l)) ∈ B₁ →
        ε ≤ c x j + c x' l - c x l - c x' j)
    (D : Set (ι → ℝ)) (N : ℝ) (hN : 0 < N) :
    ∀ᵐ p ∂dirichletOne n, ∀ ap am : M → Fin (n + 1) → ℝ,
      IsOptimalSemidiscreteAllocation μ p (fun x j ↦ c x j + t * g x j) ap →
      IsOptimalSemidiscreteAllocation μ p (fun x j ↦ c x j + (-t) * g x j) am →
      (∀ j, Measurable (fun x ↦ ap x j)) →
      (∀ j, Measurable (fun x ↦ am x j)) →
      let avg := fun z : ι → ℝ ↦ (2 : ℝ≥0∞)⁻¹ •
        (physicalSceneRootedPlan ((physicalSceneAllocationPlan μ ap Y).restrict ((H ∩ Ks) ×ˢ Kt))
          coord u N z +
         physicalSceneRootedPlan ((physicalSceneAllocationPlan μ am Y).restrict ((H ∩ Ks) ×ˢ Kt))
          coord u N z)
      (∫⁻ z, Eroot.indicator (fun z ↦ ENNReal.ofReal ε *
        min 1 (min (avg z (A₀ ×ˢ B₀)) (avg z (A₁ ×ˢ B₁)))) z
        ∂cavityRootMeasure volume D N) ≤
        ENNReal.ofReal (t * G) * ENNReal.ofReal K ^ Fintype.card ι := by
  filter_upwards [ae_exists_optimalSemidiscreteAllocation μ (fun j x ↦ c x j) hcm hc hatom]
    with p hp₀
  intro ap am hp hm hpm hmm
  exact lintegral_original_cost_rooted_average_screened_masked_rectangle_witness_le
    μ p c g ap am t G ht hp₀ hp hm hc hg hbound hpm hmm
    Y H Ks Kt hH hKs hKt coord hcoord u hu A₀ A₁ B₀ B₁
    hA₀ hA₁ hB₀ hB₁ hdisj K hK offset hbox Eroot hEroot ε hε hgap D N hN

section Finsler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {pot : M → ℝ}

/-- Original Finsler chart absolute continuity and compact source support
supply every analytic and base-optimizer input to the actual rooted average
packing estimate. The cost remains the original scaled physical slack. -/
theorem ae_dirichlet_original_finsler_rooted_average_screened_masked_rectangle_witness_le
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 2 ≤ Module.finrank ℝ E) (m : Measure E) [m.IsAddHaarMeasure]
    (μ : Measure M) [IsProbabilityMeasure μ]
    (hμchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {A : Set M} (hA : IsCompact A) (hμA : ∀ᵐ x ∂μ, x ∈ A)
    (hpot : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 pot)
    (scale : ℝ) (hscale : scale ≠ 0)
    (probe : M → M → ℝ) (hprobe : Measurable (Function.uncurry probe))
    (G : ℝ≥0) (hbound : ∀ x y, |probe x y| ≤ G) (t : ℝ) (ht : 0 ≤ t)
    (Y : Fin (n + 1) → M) (hinjY : Injective Y) (H Ks Kt : Set M) (hH : MeasurableSet H)
    (hKs : MeasurableSet Ks) (hKt : MeasurableSet Kt)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (A₀ A₁ B₀ B₁ : Set ((ι → ℝ) × ℝ))
    (hA₀ : MeasurableSet A₀) (hA₁ : MeasurableSet A₁)
    (hB₀ : MeasurableSet B₀) (hB₁ : MeasurableSet B₁) (hdisj : Disjoint A₀ A₁)
    (K : ℝ) (hK : 0 < K) (offset : ι → ℝ)
    (hbox : ∀ s ∈ A₀ ∪ A₁, s.1 - offset ∈ cavityGridPhaseCell ι K)
    (Eroot : Set (ι → ℝ)) (hEroot : MeasurableSet Eroot)
    (ε : ℝ) (hε : 0 ≤ ε) (D : Set (ι → ℝ)) (N : ℝ) (hN : 0 < N) :
    let c := fun x j ↦ scale * ((F.lengthEDist x (Y j)).toReal - pot (Y j) + pot x)
    (∀ z ∈ Eroot, ∀ x ∈ (H ∩ Ks), ∀ x' ∈ (H ∩ Ks),
      (coord x - z, pot x) ∈ A₀ → (coord x' - z, pot x') ∈ A₁ →
      ∀ j, Y j ∈ Kt → (coord (Y j) - z, pot (Y j)) ∈ B₀ →
      ∀ l, Y l ∈ Kt → (coord (Y l) - z, pot (Y l)) ∈ B₁ →
        ε ≤ c x j + c x' l - c x l - c x' j) →
    ∀ᵐ p ∂dirichletOne n, ∀ ap am : M → Fin (n + 1) → ℝ,
      IsOptimalSemidiscreteAllocation μ p (fun x j ↦ c x j + t * probe x (Y j)) ap →
      IsOptimalSemidiscreteAllocation μ p (fun x j ↦ c x j + (-t) * probe x (Y j)) am →
      (∀ j, Measurable (fun x ↦ ap x j)) →
      (∀ j, Measurable (fun x ↦ am x j)) →
      let avg := fun z : ι → ℝ ↦ (2 : ℝ≥0∞)⁻¹ •
        (physicalSceneRootedPlan ((physicalSceneAllocationPlan μ ap Y).restrict ((H ∩ Ks) ×ˢ Kt))
          coord pot N z +
         physicalSceneRootedPlan ((physicalSceneAllocationPlan μ am Y).restrict ((H ∩ Ks) ×ˢ Kt))
          coord pot N z)
      (∫⁻ z, Eroot.indicator (fun z ↦ ENNReal.ofReal ε *
        min 1 (min (avg z (A₀ ×ˢ B₀)) (avg z (A₁ ×ˢ B₁)))) z
        ∂cavityRootMeasure volume D N) ≤
        ENNReal.ofReal (t * G) * ENNReal.ofReal K ^ Fintype.card ι := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instStandard : StandardBorelSpace M := inferInstance
  dsimp only
  intro hgap
  let c := fun x j ↦ scale * ((F.lengthEDist x (Y j)).toReal - pot (Y j) + pot x)
  let g := fun x j ↦ probe x (Y j)
  have hcm j : Measurable (fun x ↦ c x j) :=
    ((F.measurable_distance_slack hpot).comp
      (measurable_id.prodMk measurable_const)).const_mul scale
  have hc j : Integrable (fun x ↦ c x j) μ := by
    simpa only [zero_mul, add_zero] using
      integrable_original_physical_tilted_cost_section μ hA hμA hpot probe hprobe G hbound
        scale 0 (Y j)
  have hg j : Integrable (fun x ↦ g x j) μ :=
    Integrable.of_bound (hprobe.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (G : ℝ) (Eventually.of_forall fun x ↦ by
        simpa only [Real.norm_eq_abs] using hbound x (Y j))
  have hatom j l (hjl : j ≠ l) :
      NullSingletonClass (μ.map (fun x ↦ c x j - c x l)) := by
    have hat := hF.nullSingletonClass_map_scaled_distanceSlack_sub m μ hdim hμchart
      hcomplete pot hscale (hinjY.ne hjl)
    simpa only [c, F.metricSpace_dist] using hat
  exact ae_dirichlet_original_cost_rooted_average_screened_masked_rectangle_witness_le
    μ c g t G ht hcm hc hatom hg (Eventually.of_forall fun x j ↦ hbound x (Y j))
    Y H Ks Kt hH hKs hKt coord hcoord
    pot hpot.continuous.measurable A₀ A₁ B₀ B₁ hA₀ hA₁ hB₀ hB₁ hdisj K hK offset hbox
    Eroot hEroot ε hε hgap D N hN

end Finsler

end OTSelector.Reconstruction
