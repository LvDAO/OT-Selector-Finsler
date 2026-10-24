import OTSelector.Limit.PhysicalSelectorFinal

open Set Function MeasureTheory ProbabilityTheory Manifold Metric Filter Topology
open OTSelector.Geometry OTSelector.Reconstruction OTSelector.Probability
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

noncomputable section

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type*} {M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

/-- The physical source probability `volM.withDensity (ofReal ∘ ρ₀)`, bundled. -/
noncomputable def physicalSourceProbability
    (volM : Measure M) (ρ₀ : M → ℝ)
    [IsProbabilityMeasure (volM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x)))] :
    ProbabilityMeasure M :=
  ⟨volM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x)), inferInstance⟩

/-- The physical target probability `volM.withDensity (ofReal ∘ ρ₁)`, bundled. -/
noncomputable def physicalTargetProbability
    (volM : Measure M) (ρ₁ : M → ℝ)
    [IsProbabilityMeasure (volM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x)))] :
    ProbabilityMeasure M :=
  ⟨volM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x)), inferInstance⟩

set_option backward.isDefEq.respectTransparency false

/-- Conditional physical selector endpoint on the two compact carriers.

Takes the physical density/volume data of `exists_finsler_physicalSemidiscreteMean_upper_bound`,
the original iid sampling model, a `1`-Lipschitz potential, and the single open producer: a
pressure triple whose semidiscrete means converge pointwise on one common tilt interval and
whose limit is differentiable at zero.  It returns an optimal plan on `A × B` and the
paper-literal metric-sup outer-probability conclusion for the entire carrier empirical face. -/
theorem exists_physical_selector_on_carriers
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
    (hμA : ∀ᵐ x ∂(physicalSourceProbability volM ρ₀ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(physicalTargetProbability volM ρ₁ : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ n i, (P n).map (X n i) = (physicalSourceProbability volM ρ₀ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (physicalTargetProbability volM ρ₁ : Measure M))
    (hXY : ∀ n, IndepFun (fun sample i ↦ X n i sample)
      (fun sample i ↦ Y n i sample) (P n))
    (φ : M → ℝ)
    (hφ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 φ)
    (hprod : ∃ (pressure : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → ℝ)
        (radius derivative : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ),
      (∀ f, 0 < radius f) ∧
      (∀ f, HasDerivAt (pressure f) (derivative f) 0) ∧
      (∀ f t, |t| < radius f →
        Tendsto (fun n ↦ finslerSemidiscreteMean F
          (physicalSourceProbability volM ρ₀) (physicalTargetProbability volM ρ₁)
          (A ∪ B) (hA.union hB)
          (hμA.mono fun _ hx ↦ Or.inl hx) (hνB.mono fun _ hy ↦ Or.inr hy) φ f t n)
          atTop (𝓝 (pressure f t)))) :
    let _inst : MetricSpace M := F.metricSpace
    let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
    let _instSecondCountable : SecondCountableTopology M :=
    @secondCountable_of_proper M F.metricSpace.toPseudoMetricSpace
      (F.properSpace_of_complete hcomplete)
    ∃ πAB : ProbabilityMeasure (A × B),
      IsOptimalCoupling (fun (x : A) (y : B) => edist (x : M) (y : M))
        (probabilityOnSubset (physicalSourceProbability volM ρ₀) A hA.measurableSet hμA)
        (probabilityOnSubset (physicalTargetProbability volM ρ₁) B hB.measurableSet hνB)
        (πAB : Measure (A × B)) ∧
      ∀ (d : ProbabilityMeasure (A × B) → ProbabilityMeasure (A × B) → ℝ),
        d πAB πAB = 0 →
        (∀ ε : ℝ, 0 < ε → IsOpen {γ : ProbabilityMeasure (A × B) | d γ πAB < ε}) →
        ∀ ε : ℝ, 0 < ε → Tendsto (fun n ↦ (P n).real
          {s | ∃ γ ∈ carrierEmpiricalFace
            (fun i ↦ supportedVersion (physicalSourceProbability volM ρ₀) A
              hA.measurableSet hμA (X n i) s)
            (fun i ↦ supportedVersion (physicalTargetProbability volM ρ₁) B
              hB.measurableSet hνB (Y n i) s),
            ε ≤ d γ πAB}) atTop (𝓝 0) := by
  let μP : ProbabilityMeasure M := physicalSourceProbability volM ρ₀
  let νP : ProbabilityMeasure M := physicalTargetProbability volM ρ₁
  let K : Set M := A ∪ B
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instSecondCountable : SecondCountableTopology M :=
    @secondCountable_of_proper M F.metricSpace.toPseudoMetricSpace
      (F.properSpace_of_complete hcomplete)
  let _instPolish : PolishSpace M := inferInstance
  let _instStandard : StandardBorelSpace M := inferInstance
  let _instMeasEq : MeasurableEq M := inferInstance
  have hK : IsCompact K := by
    dsimp only [K]
    exact hA.union hB
  have hμK : ∀ᵐ x ∂(μP : Measure M), x ∈ K := by
    dsimp only [μP, K, physicalSourceProbability]
    exact hμA.mono fun _ hx ↦ Or.inl hx
  have hνK : ∀ᵐ y ∂(νP : Measure M), y ∈ K := by
    dsimp only [νP, K, physicalTargetProbability]
    exact hνB.mono fun _ hy ↦ Or.inr hy
  have hρ₀L : LipschitzWith K₀ ρ₀ := hρ₀
  have hρ₁L : LipschitzWith K₁ ρ₁ := hρ₁
  have hμchart : ∀ old : M, (((μP : Measure M).restrict
      (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m) := by
    intro old
    exact OTSelector.Geometry.chartwise_ac_withDensity_of_volume_density volM m
      hρ₀L.continuous.measurable hρ₀nonneg v hv hvolume old
  have hνchart : ∀ old : M, (((νP : Measure M).restrict
      (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m) := by
    intro old
    exact OTSelector.Geometry.chartwise_ac_withDensity_of_volume_density volM m
      hρ₁L.continuous.measurable hρ₁nonneg v hv hvolume old
  obtain ⟨pressure, radius, derivative, hradius, hderiv, hconv, hsel⟩ :=
    existsUnique_selector_of_finsler_pressure_producer hF hcomplete m hdim μP νP
      hμchart hνchart K hK hμK hνK P X Y hX hY hXi hYi hXlaw hYlaw hXY φ hφ hprod
  obtain ⟨π, hπ, _huniq⟩ := hsel
  have hfaceM : ∀ U ∈ 𝓝 π, Tendsto (fun n ↦ (P n).real
      {s | ∃ γ ∈ Pressure.empiricalOptimalFace
        (fun i ↦ X n i s) (fun i ↦ Y n i s), γ ∉ U}) atTop (𝓝 0) := hπ.2.1
  let incl : A × B → M × M := Prod.map ((↑) : A → M) ((↑) : B → M)
  let Φ : ProbabilityMeasure (A × B) → ProbabilityMeasure (M × M) :=
    fun π ↦ π.map ((MeasurableEmbedding.subtype_coe hA.measurableSet).measurable.prodMap
      (MeasurableEmbedding.subtype_coe hB.measurableSet).measurable).aemeasurable
  have hΦemb : IsEmbedding Φ := by
    exact isEmbedding_probabilityMeasure_map_subtype_prod hA hB
  have hμmap : ((probabilityOnSubset μP A hA.measurableSet hμA : Measure A)).map
      ((↑) : A → M) = (μP : Measure M) := by
    simpa only [ProbabilityMeasure.toMeasure_map] using
      congrArg (fun ν : ProbabilityMeasure M => (ν : Measure M))
        (map_probabilityOnSubset μP A hA.measurableSet hμA)
  have hνmap : ((probabilityOnSubset νP B hB.measurableSet hνB : Measure B)).map
      ((↑) : B → M) = (νP : Measure M) := by
    simpa only [ProbabilityMeasure.toMeasure_map] using
      congrArg (fun ν : ProbabilityMeasure M => (ν : Measure M))
        (map_probabilityOnSubset νP B hB.measurableSet hνB)
  have hκ : Vlasov.IsCoupling (π : Measure (M × M))
      (((probabilityOnSubset μP A hA.measurableSet hμA : Measure A)).map ((↑) : A → M))
      (((probabilityOnSubset νP B hB.measurableSet hνB : Measure B)).map ((↑) : B → M)) := by
    rw [hμmap, hνmap]
    exact hπ.2.2.1
  obtain ⟨π₀, ⟨hπ₀couple, hπ₀map⟩, -⟩ :=
    existsUnique_subtype_coupling_lift (s := A) (t := B)
      (μ := ((probabilityOnSubset μP A hA.measurableSet hμA : Measure A)).map
        ((↑) : A → M))
      (ν := ((probabilityOnSubset νP B hB.measurableSet hνB : Measure B)).map
        ((↑) : B → M))
      hA.measurableSet hB.measurableSet
      (by simpa only [hμmap] using hμA) (by simpa only [hνmap] using hνB) hκ
  have hprobmap : IsProbabilityMeasure (π₀.map incl) := by
    rw [hπ₀map]
    infer_instance
  letI : IsProbabilityMeasure (π₀.map incl) := hprobmap
  letI : IsProbabilityMeasure π₀ := Measure.isProbabilityMeasure_of_map incl
  let πAB : ProbabilityMeasure (A × B) := ⟨π₀, inferInstance⟩
  have hπABcoe : (πAB : Measure (A × B)) = π₀ := rfl
  have hopt : IsOptimalCoupling (fun (x : A) (y : B) => edist (x : M) (y : M))
      (probabilityOnSubset μP A hA.measurableSet hμA)
      (probabilityOnSubset νP B hB.measurableSet hνB) (πAB : Measure (A × B)) := by
    have hmapopt : IsOptimalCoupling edist
        (((probabilityOnSubset μP A hA.measurableSet hμA : Measure A)).map ((↑) : A → M))
        (((probabilityOnSubset νP B hB.measurableSet hνB : Measure B)).map ((↑) : B → M))
        (((πAB : Measure (A × B))).map incl) := by
      rw [hμmap, hνmap]
      rw [show (πAB : Measure (A × B)) = π₀ from rfl]
      rw [show incl = Prod.map ((↑) : A → M) ((↑) : B → M) from rfl]
      rw [hπ₀map]
      exact hπ.2.2
    exact (isOptimalCoupling_map_embedding_iff
      (MeasurableEmbedding.subtype_coe hA.measurableSet)
      (MeasurableEmbedding.subtype_coe hB.measurableSet)
      (fun (x : A) (y : B) => edist (x : M) (y : M)) edist (fun _ _ => rfl)).mp hmapopt
  have hΦπ : Φ πAB = π := by
    apply ProbabilityMeasure.toMeasure_injective
    rw [ProbabilityMeasure.toMeasure_map]
    rw [show (πAB : Measure (A × B)) = π₀ from rfl]
    exact hπ₀map
  have hFG : ∀ n, ∀ᵐ s ∂(P n),
      Φ '' carrierEmpiricalFace
        (fun i ↦ supportedVersion μP A hA.measurableSet hμA (X n i) s)
        (fun i ↦ supportedVersion νP B hB.measurableSet hνB (Y n i) s) =
      Pressure.empiricalOptimalFace (fun i ↦ X n i s) (fun i ↦ Y n i s) := by
    intro n
    have hx : ∀ᵐ s ∂(P n), ∀ i, X n i s ∈ A := by
      apply ae_all_iff.mpr
      intro i
      exact ae_of_ae_map (hX n i).aemeasurable (by rw [hXlaw n i]; exact hμA)
    have hy : ∀ᵐ s ∂(P n), ∀ i, Y n i s ∈ B := by
      apply ae_all_iff.mpr
      intro i
      exact ae_of_ae_map (hY n i).aemeasurable (by rw [hYlaw n i]; exact hνB)
    filter_upwards [hx, hy] with s hxs hys
    have hxAeq : (fun i ↦ (supportedVersion μP A hA.measurableSet hμA (X n i) s : M)) =
        fun i ↦ X n i s := by
      funext i
      exact congrArg Subtype.val
        (supportProjection_coe μP A hA.measurableSet hμA ⟨X n i s, hxs i⟩)
    have hyBeq : (fun i ↦ (supportedVersion νP B hB.measurableSet hνB (Y n i) s : M)) =
        fun i ↦ Y n i s := by
      funext i
      exact congrArg Subtype.val
        (supportProjection_coe νP B hB.measurableSet hνB ⟨Y n i s, hys i⟩)
    have h := image_empiricalOptimalFace_subtype_prod hA.measurableSet hB.measurableSet
      (fun i ↦ supportedVersion μP A hA.measurableSet hμA (X n i) s)
      (fun i ↦ supportedVersion νP B hB.measurableSet hνB (Y n i) s)
    rw [hxAeq, hyBeq] at h
    exact h
  refine ⟨πAB, hopt, ?_⟩
  intro d hd0 hdopen ε hε
  refine OTSelector.tendsto_measureReal_exists_metric_le_of_forall_nhds P
    (fun n s ↦ carrierEmpiricalFace
      (fun i ↦ supportedVersion μP A hA.measurableSet hμA (X n i) s)
      (fun i ↦ supportedVersion νP B hB.measurableSet hνB (Y n i) s))
    πAB d hd0 hdopen ?_ ε hε
  exact OTSelector.tendsto_measureReal_exists_notMem_of_face_embedding P Φ hΦemb
    (x₀ := πAB) (y₀ := π) hΦπ
    (fun n s ↦ carrierEmpiricalFace
      (fun i ↦ supportedVersion μP A hA.measurableSet hμA (X n i) s)
      (fun i ↦ supportedVersion νP B hB.measurableSet hνB (Y n i) s))
    (fun n s ↦ Pressure.empiricalOptimalFace (fun i ↦ X n i s) (fun i ↦ Y n i s))
    hFG hfaceM

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
