import OTSelector.Limit.FinslerSemidiscretePressureData
import OTSelector.Reconstruction.FinslerPopulationDirichletEnergy
import OTSelector.Probability.CavitySemidiscretePressurePhysical

/-!
# A uniform upper bound for the physical Dirichlet semidiscrete mean

The drafted value energy bound is transferred from the allocation value
`semidiscreteValue` to the full coupling value `fullSemidiscreteValue` occurring
in the selector endpoint.  The result is a crude but unconditional upper bound
on the limsup of the physical mean, with the exact probe norm constant.  It is
not the sharp pressure limit; it is the first compiled bridge between the
energy drafts and `finslerSemidiscreteMean`.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold Metric Filter OTSelector.Geometry
open OTSelector.Reconstruction OTSelector.Probability
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

noncomputable section
universe u v

namespace OTSelector.Probability

/-- A pointwise lower bound on every edge cost bounds the semidiscrete value from below. -/
theorem semidiscreteValue_ge_of_pointwise
    {S : Type*} [MeasurableSpace S] {m : ℕ} (μ : Measure S) [IsProbabilityMeasure μ]
    (c : S → Fin (m + 1) → ℝ) (hc : ∀ j, Integrable (fun s ↦ c s j) μ)
    {p : Fin (m + 1) → ℝ} (hp : p ∈ stdSimplex ℝ (Fin (m + 1))) {B : ℝ}
    (hB : ∀ᵐ s ∂μ, ∀ j, -B ≤ c s j) :
    -B ≤ semidiscreteValue μ c p := by
  refine le_csInf ⟨_, ⟨fun _ ↦ p, isSemidiscreteAllocation_const μ p hp, rfl⟩⟩ ?_
  rintro _ ⟨a, ha, rfl⟩
  have hint : Integrable (fun s ↦ ∑ j, a s j * c s j) μ :=
    integrable_finsetSum _ (fun j _ ↦ ha.integrable_mul c hc j)
  have hpoint : ∀ᵐ s ∂μ, -B ≤ ∑ j, a s j * c s j := by
    filter_upwards [ha.nonneg, ha.sum_one, hB] with s hn hs hcB
    have h : ∑ j, a s j * (-B) ≤ ∑ j, a s j * c s j :=
      Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (hcB j) (hn j)
    rwa [← Finset.sum_mul, hs, one_mul] at h
  have hconst : (∫ _s, (-B) ∂μ) = -B := by
    rw [integral_const]
    simp [measureReal_def]
  have := integral_mono_ae (integrable_const (-B)) hint hpoint
  rw [hconst] at this
  simpa only [semidiscreteAllocationCost] using this

end OTSelector.Probability

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type u} {M : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

set_option backward.isDefEq.respectTransparency false

/-- Original Lipschitz physical populations give a potential and a uniform crude
upper bound for the limsup of the physical Dirichlet semidiscrete mean at every
probe and tilt. -/
theorem exists_finsler_physicalSemidiscreteMean_upper_bound
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (m : Measure E) [m.IsAddHaarMeasure] (volM : Measure M)
    (ρ₀ ρ₁ : M → ℝ) {K₀ K₁ : ℝ≥0}
    (hρ₀ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₀ ρ₀)
    (hρ₁ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₁ ρ₁)
    (hρ₀nonneg : ∀ x, 0 ≤ ρ₀ x) (hρ₁nonneg : ∀ x, 0 ≤ ρ₁ x)
    [IsProbabilityMeasure (volM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (volM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x)))]
    (v : M → E → ℝ)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hvnonneg : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hvolume : ∀ old : M, let χ := extChartAt 𝓘(ℝ, E) old
      (volM.restrict χ.source).map χ = (m.restrict χ.target).withDensity
        (fun y ↦ ENNReal.ofReal (v old y)))
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμA : ∀ᵐ x ∂volM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x)), x ∈ A)
    (hνB : ∀ᵐ y ∂volM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x)), y ∈ B) :
    let μP : ProbabilityMeasure M :=
      ⟨volM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x)), inferInstance⟩
    let νP : ProbabilityMeasure M :=
      ⟨volM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x)), inferInstance⟩
    let K := A ∪ B
    let _inst : MetricSpace M := F.metricSpace
    ∃ (pot : M → ℝ) (C : ℝ), LipschitzWith 1 pot ∧ 0 < C ∧
      ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
        Filter.limsup (fun n ↦ finslerSemidiscreteMean F μP νP K (hA.union hB)
          (hμA.mono fun _ hx ↦ Or.inl hx) (hνB.mono fun _ hy ↦ Or.inr hy)
          pot f t n) atTop ≤ C + |t| * (‖f‖₊ : ℝ) := by
  let μP : ProbabilityMeasure M :=
    ⟨volM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x)), inferInstance⟩
  let νP : ProbabilityMeasure M :=
    ⟨volM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x)), inferInstance⟩
  let μ : Measure M := μP
  let ν : Measure M := νP
  let K := A ∪ B
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instStandard : StandardBorelSpace M := inferInstance
  let _instMeasEq : MeasurableEq M := inferInstance
  have hμK : ∀ᵐ x ∂μ, x ∈ K := hμA.mono fun _ hx ↦ Or.inl hx
  have hνK : ∀ᵐ y ∂ν, y ∈ K := hνB.mono fun _ hy ↦ Or.inr hy
  have hK : IsCompact K := hA.union hB
  obtain ⟨pot, C, hu, hC, hbound, _⟩ :=
    exists_finsler_lipschitz_population_uniform_energy hF hcomplete hdim m volM
      ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB
  have hdim2 : 2 ≤ Module.finrank ℝ E := by omega
  have hdim1 : 1 ≤ Module.finrank ℝ E := by omega
  have hqeq : ((Module.finrank ℝ E - 1 : ℕ) : ℝ) =
      (Module.finrank ℝ E : ℝ) - 1 := by
    rw [Nat.cast_sub hdim1]
    norm_num
  have hρ₀L : LipschitzWith K₀ ρ₀ := hρ₀
  have hρ₁L : LipschitzWith K₁ ρ₁ := hρ₁
  have hμchart : ∀ old : M, ((μ : Measure M).restrict
      (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m :=
    chartwise_ac_withDensity_of_volume_density volM m hρ₀L.continuous.measurable hρ₀nonneg
      v hv hvolume
  have hνchart : ∀ old : M, ((ν : Measure M).restrict
      (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m :=
    chartwise_ac_withDensity_of_volume_density volM m hρ₁L.continuous.measurable hρ₁nonneg
      v hv hvolume
  let _instDiffuse : NullSingletonClass ν :=
    nullSingletonClass_of_chartwise_ac m ν hdim2 hνchart
  let cost : M → M → ℝ := fun x y ↦
    (F.lengthEDist x y).toReal - pot y + pot x
  have hcostm : Measurable (Function.uncurry cost) :=
    F.measurable_distance_slack hu
  have hcost : Integrable (Function.uncurry cost) (μ.prod ν) :=
    integrable_continuous_of_compact_carriers μ ν hA hB hμA hνB
      (F.continuous_distance_slack hu)
  have hhat : ∀ y z, y ≠ z →
      NullSingletonClass (μ.map (fun x ↦ cost x y - cost x z)) := by
    intro y z hyz
    have h := hF.nullSingletonClass_map_scaled_distanceSlack_sub m μ hdim2 hμchart
      hcomplete pot (one_ne_zero) hyz
    simpa only [cost, one_mul, F.metricSpace_dist] using h
  refine ⟨pot, C, hu, hC, ?_⟩
  intro f t
  -- The comparison probe on the compact carrier.
  let probe : M → M → ℝ := fun x y ↦
    f (supportProjection μP K hK.measurableSet hμK x,
      supportProjection νP K hK.measurableSet hνK y)
  have hprobeM : Measurable (Function.uncurry probe) := by
    have hmap : Measurable (fun p : M × M ↦
        (supportProjection μP K hK.measurableSet hμK p.1,
          supportProjection νP K hK.measurableSet hνK p.2)) :=
      ((measurable_supportProjection μP K hK.measurableSet hμK).comp measurable_fst).prodMk
        ((measurable_supportProjection νP K hK.measurableSet hνK).comp measurable_snd)
    exact f.continuous.measurable.comp hmap
  have hprobe : ∀ x y, |probe x y| ≤ (‖f‖₊ : ℝ) := by
    intro x y
    have h := BoundedContinuousFunction.nnnorm_coe_le_nnnorm f
      (supportProjection μP K hK.measurableSet hμK x,
        supportProjection νP K hK.measurableSet hνK y)
    have h' : ((‖f (supportProjection μP K hK.measurableSet hμK x,
        supportProjection νP K hK.measurableSet hνK y)‖₊ : ℝ) ≤ (‖f‖₊ : ℝ)) :=
      NNReal.coe_le_coe.mpr h
    simpa only [probe, coe_nnnorm, Real.norm_eq_abs] using h'
  let G : ℝ := (‖f‖₊ : ℝ)
  -- Every edge cost is bounded below by `-|t| G`.
  have hedge_lower (k : ℝ) (hk : 0 ≤ k) (x y : M) :
      -(|t| * G) ≤ k * cost x y + t * probe x y := by
    have hslack : 0 ≤ cost x y := by
      have hlip := hu.dist_le_mul x y
      simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hlip
      have h1 : pot y - pot x ≤ dist x y := by linarith [(abs_le.mp hlip).1]
      simp only [cost]
      rw [← F.metricSpace_dist]
      linarith
    have hprobe' : |t * probe x y| ≤ |t| * G := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hprobe x y) (abs_nonneg t)
    have h2 : -(|t| * G) ≤ t * probe x y := (abs_le.mp hprobe').1
    have h1 : 0 ≤ k * cost x y := mul_nonneg hk hslack
    linarith
  -- The semidiscrete value bound at every sample size.
  have hval (n : ℕ) :
      Integrable (fun z : (Fin (n + 1) → M) × (Fin (n + 1) → ℝ) ↦
        semidiscreteValue μ (fun s j ↦
          ((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) *
            cost s (z.1 j) + t * probe s (z.1 j)) z.2)
        ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) ∧
      (∫ z, semidiscreteValue μ (fun s j ↦
          ((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) *
            cost s (z.1 j) + t * probe s (z.1 j)) z.2
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤
        C + |t| * G := by
    simpa only [G, mul_assoc] using
      integral_bipartite_dirichlet_tilted_value_le
        (S := M) (T := M) (m := n) (q := Module.finrank ℝ E - 1)
        (μ := μ) (ν := ν) (cost := cost) (C := C)
        hbound hcostm hcost hhat hprobeM (‖f‖₊) hprobe t
  -- Convert the full coupling value to the allocation value a.e. in the target cloud.
  have hfull (n : ℕ) :
      finslerSemidiscreteMean F μP νP K hK hμK hνK pot f t n =
        ∫ y, ∫ p, semidiscreteValue μ (fun s j ↦
          ((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) *
            cost s (y j) + t * probe s (y j)) p
          ∂dirichletOne n ∂Measure.pi (fun _ : Fin (n + 1) ↦ ν) := by
    let ρ : Measure (Fin (n + 1) → M) := Measure.pi (fun _ : Fin (n + 1) ↦ ν)
    let kval : ℝ := ((n + 1 : ℕ) : ℝ) ^
      (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ))
    have hi : ∀ᵐ y ∂ρ, ∀ j, Integrable (fun x ↦ kval * cost x (y j)) μ := by
      apply ae_all_iff.mpr
      intro j
      have hj := (measurePreserving_eval (fun _ : Fin (n + 1) ↦ ν) j).quasiMeasurePreserving
      exact hj.tendsto_ae.eventually
        ((hcost.const_mul kval).prod_left_ae)
    have houter : (fun y : Fin (n + 1) → M ↦
        ∫ p, fullSemidiscreteValue μ y (fun x y ↦
          kval * (dist x y - pot y + pot x) + t * probe x y) p
          ∂dirichletOne n) =ᵐ[ρ]
        (fun y ↦ ∫ p, semidiscreteValue μ (fun s j ↦
          kval * cost s (y j) + t * probe s (y j)) p ∂dirichletOne n) := by
      filter_upwards [ae_injective_pi_of_nullSingletonClass (ι := Fin (n + 1)) ν, hi]
        with y hy hiy
      refine integral_congr_ae ?_
      have h := ae_fullSemidiscreteValue_eq_semidiscreteValue μ y hy
        (fun x y ↦ kval * cost x y) probe
        (by
          have h' : Measurable (fun p : M × M ↦ kval * cost p.1 p.2) :=
            hcostm.const_mul kval
          exact h') hiy
        hprobeM (‖f‖₊) hprobe t
      filter_upwards [h] with p hp
      simpa only [F.metricSpace_dist] using hp
    unfold finslerSemidiscreteMean
    dsimp only
    rw [← hqeq]
    exact integral_congr_ae houter
  have hmean_le (n : ℕ) :
      finslerSemidiscreteMean F μP νP K hK hμK hνK pot f t n ≤
        C + |t| * G := by
    rw [hfull n, ← integral_prod _ (hval n).1]
    exact (hval n).2
  -- A matching lower bound makes the sequence bounded below, so `limsup` is well behaved.
  have hprobe_int (y : M) : Integrable (fun s ↦ t * probe s y) μ := by
    refine (integrable_const (|t| * G)).mono'
      ((hprobeM.comp (measurable_id.prodMk measurable_const)).const_mul t).aestronglyMeasurable
      (Eventually.of_forall fun s ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hprobe s y) (abs_nonneg t)
  have hcost_int (n : ℕ) : ∀ᵐ y ∂Measure.pi (fun _ : Fin (n + 1) ↦ ν),
      ∀ j, Integrable (fun s ↦
        ((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) *
          cost s (y j) + t * probe s (y j)) μ := by
    apply ae_all_iff.mpr
    intro j
    have hj := (measurePreserving_eval (fun _ : Fin (n + 1) ↦ ν) j).quasiMeasurePreserving
    have hsingle : ∀ᵐ y ∂ν, Integrable (fun s ↦
        ((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) *
          cost s y + t * probe s y) μ := by
      filter_upwards [(hcost.const_mul (((n + 1 : ℕ) : ℝ) ^
        (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)))).prod_left_ae] with y hy
      exact hy.add (hprobe_int y)
    exact hj.tendsto_ae.eventually hsingle
  have hmean_ge (n : ℕ) :
      -(|t| * G) ≤ finslerSemidiscreteMean F μP νP K hK hμK hνK pot f t n := by
    let ρ : Measure (Fin (n + 1) → M) := Measure.pi (fun _ : Fin (n + 1) ↦ ν)
    let P : Measure ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) := ρ.prod (dirichletOne n)
    let kval : ℝ := ((n + 1 : ℕ) : ℝ) ^
      (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ))
    have hkval : 0 ≤ kval := Real.rpow_nonneg (by positivity) _
    have hsimplex : ∀ᵐ z ∂P, z.2 ∈ stdSimplex ℝ (Fin (n + 1)) :=
      measurePreserving_snd.quasiMeasurePreserving.ae (ae_mem_stdSimplex_dirichletOne n)
    have hint : ∀ᵐ z ∂P, ∀ j, Integrable (fun s ↦
        kval * cost s (z.1 j) + t * probe s (z.1 j)) μ := by
      have hy := hcost_int n
      exact (measurePreserving_fst (μ := ρ) (ν := dirichletOne n)).quasiMeasurePreserving.ae hy
    have hpoint : ∀ᵐ z ∂P, -(|t| * G) ≤ semidiscreteValue μ (fun s j ↦
        kval * cost s (z.1 j) + t * probe s (z.1 j)) z.2 := by
      filter_upwards [hsimplex, hint] with z hz hzint
      exact semidiscreteValue_ge_of_pointwise μ _ hzint hz
        (Filter.Eventually.of_forall fun s j ↦ hedge_lower kval hkval s (z.1 j))
    calc
      -(|t| * G) = ∫ _z, -(|t| * G) ∂P := by simp
      _ ≤ ∫ z, semidiscreteValue μ (fun s j ↦
            kval * cost s (z.1 j) + t * probe s (z.1 j)) z.2 ∂P :=
          integral_mono_ae (integrable_const _) (hval n).1 hpoint
      _ = finslerSemidiscreteMean F μP νP K hK hμK hνK pot f t n := by
          rw [hfull n, ← integral_prod _ (hval n).1]
  let u : ℕ → ℝ := fun n ↦
    finslerSemidiscreteMean F μP νP K hK hμK hνK pot f t n
  change limsup u atTop ≤ C + |t| * G
  have hbdd : atTop.IsBoundedUnder (fun x1 x2 : ℝ ↦ x2 ≤ x1) u :=
    isBoundedUnder_of ⟨-(|t| * G), fun n ↦ hmean_ge n⟩
  exact limsup_le_of_le hbdd.isCoboundedUnder_le
    (Filter.Eventually.of_forall fun n ↦ hmean_le n)

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
