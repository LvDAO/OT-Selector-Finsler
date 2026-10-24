import OTSelector.Probability.CavitySemidiscretePressureComparison
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedLocalCycleOriginal
import OTSelector.Probability.CavitySemidiscreteRootedWitness
import OTSelector.Probability.CavitySemidiscretePlanAverage
import OTSelector.Transport.CyclicMonotonicity.CountableRectangleSupport

/-!
# Actual opposite-tilt average witnesses for the original physical cost

The original global optimizers are compared in their original cost. Their
average excess pays all disjoint moving physical source-block exchanges.
Root normalization cancels the actual mass scaling before any weak limit.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
  OTSelector.Probability
open scoped Topology ContDiff ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {ι M : Type*} [Fintype ι] [MeasurableSpace M] {n : ℕ}

/-- Averaging the original coefficients averages the actual restricted rooted
physical plans. The two restricted column vectors remain their actual ones. -/
theorem physicalSceneRootedPlan_allocation_restrict_average
    (μ : Measure M) (p : Fin (n + 1) → ℝ) (ap am : M → Fin (n + 1) → ℝ)
    (hp : IsSemidiscreteAllocation μ p ap) (hm : IsSemidiscreteAllocation μ p am)
    (hpm : ∀ j, Measurable (fun x ↦ ap x j))
    (hmm : ∀ j, Measurable (fun x ↦ am x j))
    (Y : Fin (n + 1) → M) (H : Set M)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord) (u : M → ℝ) (hu : Measurable u)
    (N : ℝ) (z : ι → ℝ) :
    physicalSceneRootedPlan
      ((physicalSceneAllocationPlan μ (fun x j ↦ (ap x j + am x j) / 2) Y).restrict (H ×ˢ univ))
      coord u N z = (2 : ℝ≥0∞)⁻¹ •
        (physicalSceneRootedPlan ((physicalSceneAllocationPlan μ ap Y).restrict (H ×ˢ univ))
          coord u N z +
         physicalSceneRootedPlan ((physicalSceneAllocationPlan μ am Y).restrict (H ×ˢ univ))
          coord u N z) := by
  have hY : Measurable (Prod.map (id : M → M) Y) :=
    measurable_id.prodMap (measurable_of_finite Y)
  have hobs := measurable_physicalSceneRootedObservation coord hcoord u hu z
  unfold physicalSceneRootedPlan physicalSceneAllocationPlan
  rw [semidiscreteAllocationMeasure_average μ p ap am hp hm hpm hmm]
  simp only [Measure.map_smul, Measure.map_add _ _ hY, Measure.restrict_smul,
    Measure.restrict_add, Measure.map_add _ _ hobs, smul_add, smul_smul]
  rw [mul_comm (ENNReal.ofReal N) ((2 : ℝ≥0∞)⁻¹)]

/-- The actual mass-scaled restricted rectangle witness is exactly its original
unscaled allocation block witness. -/
theorem physicalSceneRootedPlan_allocation_restrict_cycle_witness
    {μ : Measure M} {p : Fin (n + 1) → ℝ} {a : M → Fin (n + 1) → ℝ}
    (ha : IsSemidiscreteAllocation μ p a) (Y : Fin (n + 1) → M)
    (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord) (u : M → ℝ) (hu : Measurable u)
    (N : ℝ) (hN : 0 ≤ N) (z : ι → ℝ)
    (A₀ A₁ B₀ B₁ : Set ((ι → ℝ) × ℝ))
    (hA₀ : MeasurableSet A₀) (hA₁ : MeasurableSet A₁)
    (hB₀ : MeasurableSet B₀) (hB₁ : MeasurableSet B₁) :
    min 1 (min
      (physicalSceneRootedPlan ((physicalSceneAllocationPlan μ a Y).restrict (H ×ˢ univ))
        coord u N z (A₀ ×ˢ B₀))
      (physicalSceneRootedPlan ((physicalSceneAllocationPlan μ a Y).restrict (H ×ˢ univ))
        coord u N z (A₁ ×ˢ B₁))) =
      ENNReal.ofReal (min 1 (N * min
        (semidiscreteBlockMass μ a (H ∩ (fun x ↦ (coord x - z, u x)) ⁻¹' A₀)
          (Finset.univ.filter (fun j ↦ (coord (Y j) - z, u (Y j)) ∈ B₀)))
        (semidiscreteBlockMass μ a (H ∩ (fun x ↦ (coord x - z, u x)) ⁻¹' A₁)
          (Finset.univ.filter (fun j ↦ (coord (Y j) - z, u (Y j)) ∈ B₁))))) := by
  rw [physicalSceneRootedPlan_allocation_restrict_prod ha Y H hH coord hcoord u hu N z
      A₀ B₀ hA₀ hB₀,
    physicalSceneRootedPlan_allocation_restrict_prod ha Y H hH coord hcoord u hu N z
      A₁ B₁ hA₁ hB₁]
  simp only [mul_min_of_nonneg _ _ hN, ENNReal.ofReal_min,
    ENNReal.ofReal_mul hN, ENNReal.ofReal_one]

/-- Original physical cost certificates control the actual restricted rooted
average witness by the tilt excess, independently of sample mass `N`. -/
theorem lintegral_original_cost_rooted_average_rectangle_witness_le
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
    (Y : Fin (n + 1) → M) (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord) (u : M → ℝ) (hu : Measurable u)
    (A₀ A₁ B₀ B₁ : Set ((ι → ℝ) × ℝ))
    (hA₀ : MeasurableSet A₀) (hA₁ : MeasurableSet A₁)
    (hB₀ : MeasurableSet B₀) (hB₁ : MeasurableSet B₁) (hdisj : Disjoint A₀ A₁)
    (K : ℝ) (hK : 0 < K) (offset : ι → ℝ)
    (hbox : ∀ s ∈ A₀ ∪ A₁, s.1 - offset ∈ cavityGridPhaseCell ι K)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hgap : ∀ z : ι → ℝ, ∀ x ∈ H, ∀ x' ∈ H,
      (coord x - z, u x) ∈ A₀ → (coord x' - z, u x') ∈ A₁ →
      ∀ j, (coord (Y j) - z, u (Y j)) ∈ B₀ →
      ∀ l, (coord (Y l) - z, u (Y l)) ∈ B₁ →
        ε ≤ c x j + c x' l - c x l - c x' j)
    (D : Set (ι → ℝ)) (N : ℝ) (hN : 0 < N) :
    let avg := fun z : ι → ℝ ↦ (2 : ℝ≥0∞)⁻¹ •
      (physicalSceneRootedPlan ((physicalSceneAllocationPlan μ ap Y).restrict (H ×ˢ univ))
        coord u N z +
       physicalSceneRootedPlan ((physicalSceneAllocationPlan μ am Y).restrict (H ×ˢ univ))
        coord u N z)
    (∫⁻ z, ENNReal.ofReal ε * min 1 (min (avg z (A₀ ×ˢ B₀)) (avg z (A₁ ×ˢ B₁)))
      ∂cavityRootMeasure volume D N) ≤
      ENNReal.ofReal (t * G) * ENNReal.ofReal K ^ Fintype.card ι := by
  obtain ⟨a₀, h₀⟩ := hbase
  let obs := fun z (x : M) ↦ (coord x - z, u x)
  let AA := fun z ↦ H ∩ obs z ⁻¹' A₀
  let AB := fun z ↦ H ∩ obs z ⁻¹' A₁
  let J := fun z ↦ Finset.univ.filter (fun j ↦ obs z (Y j) ∈ B₀)
  let L := fun z ↦ Finset.univ.filter (fun j ↦ obs z (Y j) ∈ B₁)
  have hobs : Measurable (fun v : (ι → ℝ) × M ↦ obs v.1 v.2) :=
    ((hcoord.comp measurable_snd).sub measurable_fst).prodMk (hu.comp measurable_snd)
  have hAA : MeasurableSet {v : (ι → ℝ) × M | v.2 ∈ AA v.1} :=
    (hH.preimage measurable_snd).inter (hA₀.preimage hobs)
  have hAB : MeasurableSet {v : (ι → ℝ) × M | v.2 ∈ AB v.1} :=
    (hH.preimage measurable_snd).inter (hA₁.preimage hobs)
  have hJ (j : Fin (n + 1)) : MeasurableSet {z | j ∈ J z} := by
    simp only [J, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hB₀.preimage (hobs.comp (measurable_id.prodMk measurable_const))
  have hL (j : Fin (n + 1)) : MeasurableSet {z | j ∈ L z} := by
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hB₁.preimage (hobs.comp (measurable_id.prodMk measurable_const))
  have hcell : ∀ z, AA z ∪ AB z ⊆ (fun x ↦ coord x - offset) ⁻¹' cavityGridCube ι K z := by
    intro z x hx
    have hs : obs z x ∈ A₀ ∪ A₁ := hx.elim (fun h ↦ Or.inl h.2) (fun h ↦ Or.inr h.2)
    have hb := hbox (obs z x) hs
    change (coord x - offset) - z ∈ cavityGridPhaseCell ι K
    simpa only [obs, sub_right_comm] using hb
  have hb := lintegral_cavityRoot_opposite_tilt_cycle_witness_le μ p c g a₀ ap am t G ht
    h₀ hp hm hc hg hbound hpm hmm (fun x ↦ coord x - offset) K hK AA AB hAA hAB
    (fun z ↦ (hdisj.preimage (obs z)).mono inter_subset_right inter_subset_right)
    hcell J L hJ hL ε hε (by
      intro z x hx x' hx' j hj l hl
      exact hgap z x hx.1 x' hx'.1 hx.2 hx'.2 j (Finset.mem_filter.mp hj).2
        l (Finset.mem_filter.mp hl).2) D N hN
  convert hb using 1
  apply lintegral_congr
  intro z
  dsimp only
  rw [← physicalSceneRootedPlan_allocation_restrict_average μ p ap am hp.1 hm.1 hpm hmm
      Y H coord hcoord u hu N z,
    physicalSceneRootedPlan_allocation_restrict_cycle_witness (hp.1.average hm.1) Y H hH
      coord hcoord u hu N hN.le z A₀ A₁ B₀ B₁ hA₀ hA₁ hB₀ hB₁,
    ← ENNReal.ofReal_mul hε]

/-- Original cost atomlessness supplies the base optimizer internally on one
Dirichlet full-measure event. Every actual choice from both tilted optimal
faces then satisfies the original physical-cost rooted average bound. -/
theorem ae_dirichlet_original_cost_rooted_average_rectangle_witness_le
    [StandardBorelSpace M]
    (μ : Measure M) [IsProbabilityMeasure μ]
    (c g : M → Fin (n + 1) → ℝ) (t G : ℝ) (ht : 0 ≤ t)
    (hcm : ∀ j, Measurable (fun x ↦ c x j))
    (hc : ∀ j, Integrable (fun x ↦ c x j) μ)
    (hatom : ∀ j l, j ≠ l → NullSingletonClass (μ.map (fun x ↦ c x j - c x l)))
    (hg : ∀ j, Integrable (fun x ↦ g x j) μ)
    (hbound : ∀ᵐ x ∂μ, ∀ j, |g x j| ≤ G)
    (Y : Fin (n + 1) → M) (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord) (u : M → ℝ) (hu : Measurable u)
    (A₀ A₁ B₀ B₁ : Set ((ι → ℝ) × ℝ))
    (hA₀ : MeasurableSet A₀) (hA₁ : MeasurableSet A₁)
    (hB₀ : MeasurableSet B₀) (hB₁ : MeasurableSet B₁) (hdisj : Disjoint A₀ A₁)
    (K : ℝ) (hK : 0 < K) (offset : ι → ℝ)
    (hbox : ∀ s ∈ A₀ ∪ A₁, s.1 - offset ∈ cavityGridPhaseCell ι K)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hgap : ∀ z : ι → ℝ, ∀ x ∈ H, ∀ x' ∈ H,
      (coord x - z, u x) ∈ A₀ → (coord x' - z, u x') ∈ A₁ →
      ∀ j, (coord (Y j) - z, u (Y j)) ∈ B₀ →
      ∀ l, (coord (Y l) - z, u (Y l)) ∈ B₁ →
        ε ≤ c x j + c x' l - c x l - c x' j)
    (D : Set (ι → ℝ)) (N : ℝ) (hN : 0 < N) :
    ∀ᵐ p ∂dirichletOne n, ∀ ap am : M → Fin (n + 1) → ℝ,
      IsOptimalSemidiscreteAllocation μ p (fun x j ↦ c x j + t * g x j) ap →
      IsOptimalSemidiscreteAllocation μ p (fun x j ↦ c x j + (-t) * g x j) am →
      (∀ j, Measurable (fun x ↦ ap x j)) →
      (∀ j, Measurable (fun x ↦ am x j)) →
      let avg := fun z : ι → ℝ ↦ (2 : ℝ≥0∞)⁻¹ •
        (physicalSceneRootedPlan ((physicalSceneAllocationPlan μ ap Y).restrict (H ×ˢ univ))
          coord u N z +
         physicalSceneRootedPlan ((physicalSceneAllocationPlan μ am Y).restrict (H ×ˢ univ))
          coord u N z)
      (∫⁻ z, ENNReal.ofReal ε * min 1 (min (avg z (A₀ ×ˢ B₀)) (avg z (A₁ ×ˢ B₁)))
        ∂cavityRootMeasure volume D N) ≤
        ENNReal.ofReal (t * G) * ENNReal.ofReal K ^ Fintype.card ι := by
  filter_upwards [ae_exists_optimalSemidiscreteAllocation μ (fun j x ↦ c x j) hcm hc hatom]
    with p hp₀
  intro ap am hp hm hpm hmm
  exact lintegral_original_cost_rooted_average_rectangle_witness_le μ p c g ap am t G ht
    hp₀ hp hm hc hg hbound hpm hmm Y H hH coord hcoord u hu A₀ A₁ B₀ B₁
    hA₀ hA₁ hB₀ hB₁ hdisj K hK offset hbox ε hε hgap D N hN

section Finsler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {pot : M → ℝ}

/-- Original Finsler chart absolute continuity and compact source support
supply every analytic and base-optimizer input to the actual rooted average
packing estimate. The cost remains the original scaled physical slack. -/
theorem ae_dirichlet_original_finsler_rooted_average_rectangle_witness_le
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
    (Y : Fin (n + 1) → M) (hinjY : Injective Y) (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (A₀ A₁ B₀ B₁ : Set ((ι → ℝ) × ℝ))
    (hA₀ : MeasurableSet A₀) (hA₁ : MeasurableSet A₁)
    (hB₀ : MeasurableSet B₀) (hB₁ : MeasurableSet B₁) (hdisj : Disjoint A₀ A₁)
    (K : ℝ) (hK : 0 < K) (offset : ι → ℝ)
    (hbox : ∀ s ∈ A₀ ∪ A₁, s.1 - offset ∈ cavityGridPhaseCell ι K)
    (ε : ℝ) (hε : 0 ≤ ε) (D : Set (ι → ℝ)) (N : ℝ) (hN : 0 < N) :
    let c := fun x j ↦ scale * ((F.lengthEDist x (Y j)).toReal - pot (Y j) + pot x)
    (∀ z : ι → ℝ, ∀ x ∈ H, ∀ x' ∈ H,
      (coord x - z, pot x) ∈ A₀ → (coord x' - z, pot x') ∈ A₁ →
      ∀ j, (coord (Y j) - z, pot (Y j)) ∈ B₀ →
      ∀ l, (coord (Y l) - z, pot (Y l)) ∈ B₁ →
        ε ≤ c x j + c x' l - c x l - c x' j) →
    ∀ᵐ p ∂dirichletOne n, ∀ ap am : M → Fin (n + 1) → ℝ,
      IsOptimalSemidiscreteAllocation μ p (fun x j ↦ c x j + t * probe x (Y j)) ap →
      IsOptimalSemidiscreteAllocation μ p (fun x j ↦ c x j + (-t) * probe x (Y j)) am →
      (∀ j, Measurable (fun x ↦ ap x j)) →
      (∀ j, Measurable (fun x ↦ am x j)) →
      let avg := fun z : ι → ℝ ↦ (2 : ℝ≥0∞)⁻¹ •
        (physicalSceneRootedPlan ((physicalSceneAllocationPlan μ ap Y).restrict (H ×ˢ univ))
          coord pot N z +
         physicalSceneRootedPlan ((physicalSceneAllocationPlan μ am Y).restrict (H ×ˢ univ))
          coord pot N z)
      (∫⁻ z, ENNReal.ofReal ε * min 1 (min (avg z (A₀ ×ˢ B₀)) (avg z (A₁ ×ˢ B₁)))
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
  exact ae_dirichlet_original_cost_rooted_average_rectangle_witness_le μ c g t G ht hcm hc
    hatom hg (Eventually.of_forall fun x j ↦ hbound x (Y j)) Y H hH coord hcoord
    pot hpot.continuous.measurable A₀ A₁ B₀ B₁ hA₀ hA₁ hB₀ hB₁ hdisj K hK offset hbox
    ε hε hgap D N hN

end Finsler

section IteratedWeak
variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
  [OpensMeasurableSpace S] [HasOuterApproxClosed S]

/-- Bounds that are uniform in sample size and vanish with the outer tilt
exclude an actual lower semicontinuous witness after the two separate weak
limits. Eventual certificates in each index suffice. -/
theorem ae_eq_zero_of_iterated_weak_lsc_tilt_bounds
    (Pn : ℕ → ℕ → ProbabilityMeasure S) (Q : ℕ → ProbabilityMeasure S)
    (R : ProbabilityMeasure S)
    (φ : ℕ → ℕ → ℕ) (hφ : ∀ k, Tendsto (φ k) atTop atTop)
    (ψ : ℕ → ℕ) (hψ : Tendsto ψ atTop atTop)
    (hinner : ∀ k, Tendsto (fun N ↦ Pn k (φ k N)) atTop (𝓝 (Q k)))
    (houter : Tendsto (fun k ↦ Q (ψ k)) atTop (𝓝 R))
    (W : S → ℝ≥0∞) (hW : LowerSemicontinuous W)
    (B : ℕ → ℝ≥0∞) (hB : Tendsto B atTop (𝓝 0))
    (hbound : ∀ᶠ k in atTop, ∀ᶠ N in atTop,
      (∫⁻ s, W s ∂(Pn k N : Measure S)) ≤ B k) :
    ∀ᵐ s ∂(R : Measure S), W s = 0 := by
  have hopen (r : ℝ≥0∞) (hr : 0 < r) (hrt : r ≠ ⊤) :
      (R : Measure S) {s | r < W s} = 0 := by
    have hQ : ∀ᶠ k in atTop, (Q k : Measure S) {s | r < W s} ≤ B k / r := by
      filter_upwards [hbound] with k hk
      have hb : ∀ᶠ N in atTop,
          (Pn k (φ k N) : Measure S) {s | r < W s} ≤ B k / r := by
        filter_upwards [(hφ k).eventually hk] with N hN
        exact ((measure_mono (show {s | r < W s} ⊆ {s | r ≤ W s} from
          fun s hs ↦ le_of_lt (show r < W s from hs))).trans
          (meas_ge_le_lintegral_div hW.measurable.aemeasurable (ne_of_gt hr) hrt)).trans
          (ENNReal.div_le_div_right hN r)
      exact (ProbabilityMeasure.le_liminf_measure_open_of_tendsto (hinner k)
        (hW.isOpen_preimage r)).trans (liminf_le_of_frequently_le hb.frequently)
    have hdiv : Tendsto (fun k ↦ B (ψ k) / r) atTop (𝓝 (0 : ℝ≥0∞)) := by
      simpa only [Function.comp_apply, ENNReal.zero_div] using
        ENNReal.Tendsto.div_const (hB.comp hψ) (Or.inr (ne_of_gt hr))
    have hle := ProbabilityMeasure.le_liminf_measure_open_of_tendsto houter
      (hW.isOpen_preimage r)
    have hQsub : ∀ᶠ k in atTop,
        (Q (ψ k) : Measure S) {s | r < W s} ≤ B (ψ k) / r := hψ.eventually hQ
    have hcompare : atTop.liminf (fun k ↦ (Q (ψ k) : Measure S) {s | r < W s}) ≤
        atTop.liminf (fun k ↦ B (ψ k) / r) := liminf_le_liminf hQsub
    exact le_antisymm (hle.trans (hcompare.trans_eq hdiv.liminf_eq)) bot_le
  have hzero : ∀ᵐ s ∂(R : Measure S), W s ≤ 0 := by
    apply (ae_le_const_iff_forall_gt_measure_zero W 0).mpr
    intro b hb
    obtain ⟨q, _, hq0, hqb⟩ := ENNReal.lt_iff_exists_rat_btwn.mp hb
    have hs : {s | b ≤ W s} ⊆ {s | ((q : ℝ).toNNReal : ℝ≥0∞) < W s} :=
      fun _ h ↦ hqb.trans_le h
    exact measure_mono_null hs (hopen _ hq0 ENNReal.coe_ne_top)
  exact hzero.mono fun _ h ↦ le_antisymm h bot_le

end IteratedWeak

end OTSelector.Reconstruction
