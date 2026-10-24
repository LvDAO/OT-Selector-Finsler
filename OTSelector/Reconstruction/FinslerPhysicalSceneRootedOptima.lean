import OTSelector.Probability.CavitySemidiscreteJointOptima
import OTSelector.Probability.CavitySemidiscreteBipartiteJointOptima
import OTSelector.Reconstruction.FinslerPhysicalSceneReadoutPopulation

/-!
# Actual opposite global optimizer families at every tilt and sample size

One countable exceptional set covers all original sample sizes. Its complement
provides a common deterministic positive decreasing tilt sequence. At every
pair of tilt index and sample size, the actual original target times Dirichlet
experiment supports jointly measurable opposite global allocation optima.
The Finsler specialization derives cost atomlessness and integrability from
original chart absolute continuity and compact physical carriers.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Metric OTSelector.Geometry
  OTSelector.Probability
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

section Original
variable {S T : Type*} [MeasurableSpace S] [StandardBorelSpace S]
  [MeasurableSpace T] [StandardBorelSpace T]

/-- All original sample sizes share one deterministic sequence of good tilts
and jointly measurable opposite global optimizers in their actual iid-target
and Dirichlet environment. -/
theorem exists_original_jointlyMeasurable_opposite_global_allocations
    (μ : Measure S) [IsProbabilityMeasure μ]
    (ν : Measure T) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (c : ℕ → S → T → ℝ)
    (hc : ∀ n, Measurable (Function.uncurry (c n)))
    (hci : ∀ n, Integrable (Function.uncurry (c n)) (μ.prod ν))
    (hatom : ∀ n y z, y ≠ z → NullSingletonClass (μ.map (fun s ↦ c n s y - c n s z)))
    (g : S → T → ℝ) (hg : Measurable (Function.uncurry g))
    (G : ℝ≥0) (hbound : ∀ s y, |g s y| ≤ G) :
    ∃ t : ℕ → ℝ,
    ∃ Aplus Amin : ∀ (_k n : ℕ), (((Fin (n + 1) → T) × (Fin (n + 1) → ℝ)) × S) →
        Fin (n + 1) → ℝ,
      StrictAnti t ∧ (∀ n, 0 < t n) ∧ Tendsto t atTop (𝓝 0) ∧
      (∀ k n j, Measurable (fun z ↦ Aplus k n z j)) ∧
      (∀ k n j, Measurable (fun z ↦ Amin k n z j)) ∧
      ∀ k n, ∀ᵐ z ∂(Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n),
        IsOptimalSemidiscreteAllocation μ z.2
          (fun s j ↦ c n s (z.1 j) + t k * g s (z.1 j)) (fun s ↦ Aplus k n (z, s)) ∧
        IsOptimalSemidiscreteAllocation μ z.2
          (fun s j ↦ c n s (z.1 j) + (-t k) * g s (z.1 j)) (fun s ↦ Amin k n (z, s)) := by
  let V := fun n ↦ Fin (n + 1) → T
  let ρ : ∀ n, Measure (V n) := fun n ↦ Measure.pi (fun _ ↦ ν)
  let base := fun n (v : V n) (j : Fin (n + 1)) s ↦ c n s (v j)
  let probe := fun n (v : V n) (j : Fin (n + 1)) s ↦ g s (v j)
  have hcm (n : ℕ) (j : Fin (n + 1)) :
      Measurable (fun z : V n × S ↦ base n z.1 j z.2) :=
    (hc n).comp (measurable_snd.prodMk ((measurable_pi_apply j).comp measurable_fst))
  have hgm (n : ℕ) (j : Fin (n + 1)) :
      Measurable (fun z : V n × S ↦ probe n z.1 j z.2) :=
    hg.comp (measurable_snd.prodMk ((measurable_pi_apply j).comp measurable_fst))
  have hci' (n : ℕ) : ∀ᵐ v ∂ρ n, ∀ j, Integrable (base n v j) μ := by
    apply ae_all_iff.mpr
    intro j
    exact (measurePreserving_eval (fun _ : Fin (n + 1) ↦ ν) j).quasiMeasurePreserving.ae
      (hci n).prod_left_ae
  have hat (n : ℕ) : ∀ᵐ v ∂ρ n, ∀ j l, j ≠ l →
      NullSingletonClass (μ.map (fun s ↦ base n v j s - base n v l s)) := by
    filter_upwards [ae_injective_pi_of_nullSingletonClass (ι := Fin (n + 1)) ν] with v hv
    exact fun j l hjl ↦ hatom n (v j) (v l) (hv.ne hjl)
  let Bad : ℕ → Set ℝ := fun n ↦ {u | ¬∀ᵐ v ∂ρ n, ∀ j l, j ≠ l →
    NullSingletonClass (μ.map (fun s ↦
      (base n v j s + u * probe n v j s) - (base n v l s + u * probe n v l s)))}
  have hBad (n : ℕ) : (Bad n).Countable :=
    countable_bad_parameterized_cavity_tilts μ (ρ n)
      (fun j v s ↦ base n v j s) (fun j v s ↦ probe n v j s)
      (hcm n) (hgm n) (hat n)
  let AllBad := (⋃ n, Bad n) ∪ Neg.neg '' (⋃ n, Bad n)
  have hAllBad : AllBad.Countable :=
    (countable_iUnion hBad).union ((countable_iUnion hBad).image Neg.neg)
  obtain ⟨t, ht, hmem, hlim⟩ :=
    (hAllBad.dense_compl ℝ).exists_seq_strictAnti_tendsto (0 : ℝ)
  have hgoodplus (k n : ℕ) : t k ∉ Bad n := by
    intro hn
    exact (hmem k).2 (Or.inl (mem_iUnion.mpr ⟨n, hn⟩))
  have hgoodminus (k n : ℕ) : -t k ∉ Bad n := by
    intro hn
    exact (hmem k).2 (Or.inr ⟨-t k, mem_iUnion.mpr ⟨n, hn⟩, neg_neg _⟩)
  have halloc (n : ℕ) (u : ℝ) (hu : u ∉ Bad n) :
      ∃ A : ((V n × (Fin (n + 1) → ℝ)) × S) → Fin (n + 1) → ℝ,
        (∀ j, Measurable (fun z ↦ A z j)) ∧
        ∀ᵐ z ∂(ρ n).prod (dirichletOne n),
          IsOptimalSemidiscreteAllocation μ z.2
            (fun s j ↦ base n z.1 j s + u * probe n z.1 j s) (fun s ↦ A (z, s)) := by
    have hgi (v : V n) (j : Fin (n + 1)) : Integrable (probe n v j) μ :=
      (integrable_const (G : ℝ)).mono'
        ((hgm n j).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
        (Eventually.of_forall fun s ↦ by simpa only [Real.norm_eq_abs] using hbound s (v j))
    obtain ⟨A, hA, ho⟩ := exists_jointlyMeasurable_parameterized_dirichlet_optimalAllocation
      μ (ρ n) (fun v j s ↦ base n v j s + u * probe n v j s)
      (fun j ↦ (hcm n j).add ((hgm n j).const_mul u))
      ((hci' n).mono fun v hv j ↦ (hv j).add ((hgi v j).const_mul u)) (not_not.mp hu)
    exact ⟨A, hA, ho.mono fun _ h ↦ h.1⟩
  choose Aplus hplus hp using fun k n ↦ halloc n (t k) (hgoodplus k n)
  choose Amin hminus hm using fun k n ↦ halloc n (-t k) (hgoodminus k n)
  exact ⟨t, Aplus, Amin, ht, fun n ↦ (hmem n).1, hlim, hplus, hminus,
    fun k n ↦ (hp k n).and (hm k n)⟩

end Original

section Finsler
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

/-- Actual original Finsler chart densities supply the measurable opposite
optimizer families for the original scaled physical slack, simultaneously
across tilt indices and sample sizes on the genuine target times Dirichlet laws. -/
theorem exists_finsler_original_opposite_global_allocations
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 2 ≤ Module.finrank ℝ E)
    (m : Measure E) [m.IsAddHaarMeasure]
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M, (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ y ∂ν, y ∈ B)
    (pot : M → ℝ) (hpot : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 pot)
    (scale : ℕ → ℝ) (hscale : ∀ n, scale n ≠ 0)
    (g : M → M → ℝ) (hg : Measurable (Function.uncurry g))
    (G : ℝ≥0) (hbound : ∀ s y, |g s y| ≤ G) :
    ∃ t : ℕ → ℝ,
    ∃ Aplus Amin : ∀ (_k n : ℕ), (((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M) →
        Fin (n + 1) → ℝ,
      StrictAnti t ∧ (∀ n, 0 < t n) ∧ Tendsto t atTop (𝓝 0) ∧
      (∀ k n j, Measurable (fun z ↦ Aplus k n z j)) ∧
      (∀ k n j, Measurable (fun z ↦ Amin k n z j)) ∧
      ∀ k n, ∀ᵐ z ∂(Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n),
        IsOptimalSemidiscreteAllocation μ z.2
          (fun s j ↦ scale n * ((F.lengthEDist s (z.1 j)).toReal - pot (z.1 j) + pot s) +
            t k * g s (z.1 j)) (fun s ↦ Aplus k n (z, s)) ∧
        IsOptimalSemidiscreteAllocation μ z.2
          (fun s j ↦ scale n * ((F.lengthEDist s (z.1 j)).toReal - pot (z.1 j) + pot s) +
            (-t k) * g s (z.1 j)) (fun s ↦ Amin k n (z, s)) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instStandard : StandardBorelSpace M := inferInstance
  let _instDiffuse : NullSingletonClass ν :=
    nullSingletonClass_of_chartwise_ac m ν hdim hνchart
  let c := fun n x y ↦ scale n * ((F.lengthEDist x y).toReal - pot y + pot x)
  have hc (n : ℕ) : Measurable (Function.uncurry (c n)) :=
    (F.measurable_distance_slack hpot).const_mul (scale n)
  have hci (n : ℕ) : Integrable (Function.uncurry (c n)) (μ.prod ν) :=
    (integrable_continuous_of_compact_carriers μ ν hA hB hμA hνB
      (F.continuous_distance_slack hpot)).const_mul (scale n)
  have hatom (n : ℕ) (y z : M) (hyz : y ≠ z) :
      NullSingletonClass (μ.map (fun s ↦ c n s y - c n s z)) := by
    have hat := hF.nullSingletonClass_map_scaled_distanceSlack_sub m μ hdim hμchart
      hcomplete pot (hscale n) hyz
    simpa only [c, F.metricSpace_dist] using hat
  exact exists_original_jointlyMeasurable_opposite_global_allocations μ ν c hc hci
    hatom g hg G hbound

end Finsler
end OTSelector.Reconstruction
