import OTSelector.Probability.SupportedIID

/-!
# Compact-carrier selection for the original ambient iid samples

The carrier probes below are evaluated using measurable retractions, but their distance-slack
costs use the original ambient observations and ambient distance. On the full-probability event
where all observations belong to the carrier, these pressures are exactly those of the
carrier-valued versions. Both probability laws and all outer failure probabilities are preserved.

Consequently the existing iid pressure theorem applies on a compact carrier and returns a unique
ambient selector for the entire original optimal face. Neither compactness of the ambient space
nor a new sampling law is assumed. Central and lower tilted pressure convergence and
differentiability remain explicit analytic hypotheses; this module does not prove them from
Finsler geometry. No intrinsic path distance on the carrier is introduced.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace OTSelector.Pressure
open Probability Reconstruction

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

/-- The actual ambient distance-slack assignment value with a carrier probe; only probe values
outside the full-mass carrier require a measurable retraction. -/
noncomputable def supportedDistancePressure
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    {n : ℕ} (X Y : Fin n → M) (φ : M → ℝ) (k : ℝ)
    (f : (K × K) →ᵇ ℝ) (t : ℝ) : ℝ :=
  perturbedAssignmentValue (fun i j ↦ k * distanceSlackEdgeCost X Y φ i j)
    (fun i j ↦ f (supportProjection μ K hK hμ (X i),
      supportProjection ν K hK hν (Y j))) t / (n : ℝ)

omit [BorelSpace M] in
/-- The original pressure agrees almost everywhere with the exact subtype pressure. -/
theorem supportedDistancePressure_eq_ae
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    (X Y : Fin n → Ω → M)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hlawX : ∀ i, P.map (X i) = μ) (hlawY : ∀ i, P.map (Y i) = ν)
    (φ : M → ℝ) (k : ℝ) (f : (K × K) →ᵇ ℝ) (t : ℝ) :
    (fun ω ↦ supportedDistancePressure μ ν K hK hμ hν
      (fun i ↦ X i ω) (fun i ↦ Y i ω) φ k f t) =ᵐ[P]
    (fun ω ↦ empiricalDistancePressure
      (fun i ↦ supportedVersion μ K hK hμ (X i) ω)
      (fun i ↦ supportedVersion ν K hK hν (Y i) ω)
      (fun x : K ↦ φ x) k f t) := by
  have hx := ae_all_iff.mpr (fun i ↦ coe_supportedVersion_ae μ K hK hμ (hX i) (hlawX i))
  have hy := ae_all_iff.mpr (fun i ↦ coe_supportedVersion_ae ν K hK hν (hY i) (hlawY i))
  filter_upwards [hx, hy] with ω hxω hyω
  unfold supportedDistancePressure empiricalDistancePressure
  congr 2
  funext i j
  simp only [distanceSlackEdgeCost, Subtype.dist_eq, hxω, hyω]

/-- The full original ambient face converges under the same row filter whenever its supported
versions do. No measurable selection of an empirical optimum is used. -/
theorem tendsto_empiricalOptimalFace_of_supportedVersion
    [SecondCountableTopology M]
    {Ω : ℕ → Type*} [∀ r, MeasurableSpace (Ω r)]
    (P : ∀ r, Measure (Ω r)) [∀ r, IsProbabilityMeasure (P r)]
    (X Y : ∀ r, Fin (r + 1) → Ω r → M)
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (hX : ∀ r i, Measurable (X r i)) (hY : ∀ r i, Measurable (Y r i))
    (hlawX : ∀ r i, (P r).map (X r i) = μ) (hlawY : ∀ r i, (P r).map (Y r i) = ν)
    (π : ProbabilityMeasure (K × K))
    (hface : Tendsto (fun z : Σ r, Ω r ↦ empiricalOptimalFace
      (fun i ↦ supportedVersion μ K hK hμ (X z.1 i) z.2)
      (fun i ↦ supportedVersion ν K hK hν (Y z.1 i) z.2))
      (rowProbabilityFilter P) (𝓝 π).smallSets) :
    Tendsto (fun z : Σ r, Ω r ↦ empiricalOptimalFace
      (fun i ↦ X z.1 i z.2) (fun i ↦ Y z.1 i z.2))
      (rowProbabilityFilter P)
      (𝓝 (π.map (measurable_subtype_coe.prodMap measurable_subtype_coe).aemeasurable)).smallSets := by
  have heq : (fun z : Σ r, Ω r ↦
      (fun π : ProbabilityMeasure (K × K) ↦ π.map
        (measurable_subtype_coe.prodMap measurable_subtype_coe).aemeasurable) ''
      empiricalOptimalFace
        (fun i ↦ supportedVersion μ K hK hμ (X z.1 i) z.2)
        (fun i ↦ supportedVersion ν K hK hν (Y z.1 i) z.2)) =ᶠ[rowProbabilityFilter P]
      (fun z : Σ r, Ω r ↦ empiricalOptimalFace
        (fun i ↦ X z.1 i z.2) (fun i ↦ Y z.1 i z.2)) :=
    eventuallyEq_rowProbabilityFilter_of_ae P (fun r ↦
    image_empiricalOptimalFace_supportedVersion_ae μ ν K hK hμ hν (X r) (Y r)
      (hX r) (hY r) (hlawX r) (hlawY r))
  have hcont := ProbabilityMeasure.continuous_map
    ((continuous_subtype_val : Continuous ((↑) : K → M)).prodMap
      (continuous_subtype_val : Continuous ((↑) : K → M)))
  exact (hcont.continuousAt.image_smallSets.comp hface).congr' heq

/-- Actual ambient iid arrays with compactly supported laws have a unique ambient selector
provided the actual central and lower tilted pressures converge and the limiting pressures are
differentiable. Readouts use the canonical pullback to the carrier. The probability `P`, sample
arrays, all empirical optimizers, and normalization `(r + 1)^(2/q)` are the original ones. -/
theorem existsUnique_supported_empirical_selector_of_iid_pressure
    [SecondCountableTopology M]
    {Ω : ℕ → Type*} [∀ r, MeasurableSpace (Ω r)]
    (P : ∀ r, Measure (Ω r)) [∀ r, IsProbabilityMeasure (P r)]
    (X Y : ∀ r, Fin (r + 1) → Ω r → M) (μ ν : ProbabilityMeasure M)
    (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (hX : ∀ r i, Measurable (X r i)) (hY : ∀ r i, Measurable (Y r i))
    (hindepX : ∀ r, ProbabilityTheory.iIndepFun (X r) (P r))
    (hindepY : ∀ r, ProbabilityTheory.iIndepFun (Y r) (P r))
    (hlawX : ∀ r i, (P r).map (X r i) = (μ : Measure M))
    (hlawY : ∀ r i, (P r).map (Y r i) = (ν : Measure M))
    (φ : M → ℝ) (hφ : LipschitzWith 1 φ) (q : ℝ) (hq : 0 < q)
    (pressure : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (radius derivative : ((K × K) →ᵇ ℝ) → ℝ)
    (hradius : ∀ f, 0 < radius f)
    (hderiv : ∀ f, HasDerivAt (pressure f) (derivative f) 0)
    (hzero : ∀ f ε, 0 < ε → Tendsto
      (fun r ↦ (P r).real {ω | ε ≤ |supportedDistancePressure μ ν K hK.measurableSet hμ hν
        (fun i ↦ X r i ω) (fun i ↦ Y r i ω) φ (((r + 1 : ℕ) : ℝ) ^ (2 / q)) f 0 -
          pressure f 0|}) atTop (𝓝 0))
    (hlower : ∀ f t, |t| < radius f → ∀ ε, 0 < ε → Tendsto
      (fun r ↦ (P r).real {ω | ε ≤ max (pressure f t -
        supportedDistancePressure μ ν K hK.measurableSet hμ hν
          (fun i ↦ X r i ω) (fun i ↦ Y r i ω) φ (((r + 1 : ℕ) : ℝ) ^ (2 / q)) f t) 0})
      atTop (𝓝 0)) :
    ∃! π : ProbabilityMeasure (M × M),
      (∀ f : (K × K) →ᵇ ℝ, ∫ z, f z ∂((π : Measure (M × M)).comap
        (Prod.map ((↑) : K → M) ((↑) : K → M))) = derivative f) ∧
      (∀ U ∈ 𝓝 π, Tendsto (fun r ↦ (P r).real
        {ω | ∃ γ ∈ empiricalOptimalFace (fun i ↦ X r i ω) (fun i ↦ Y r i ω), γ ∉ U})
        atTop (𝓝 0)) ∧
      IsOptimalCoupling edist (μ : Measure M) (ν : Measure M) (π : Measure (M × M)) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let XK : ∀ r, Fin (r + 1) → Ω r → K :=
    fun r i ↦ supportedVersion μ K hK.measurableSet hμ (X r i)
  let YK : ∀ r, Fin (r + 1) → Ω r → K :=
    fun r i ↦ supportedVersion ν K hK.measurableSet hν (Y r i)
  have hXK : ∀ r i, Measurable (XK r i) :=
    fun r i ↦ measurable_supportedVersion μ K hK.measurableSet hμ (hX r i)
  have hYK : ∀ r i, Measurable (YK r i) :=
    fun r i ↦ measurable_supportedVersion ν K hK.measurableSet hν (hY r i)
  have hindepXK : ∀ r, ProbabilityTheory.iIndepFun (XK r) (P r) :=
    fun r ↦ iIndepFun_supportedVersion μ K hK.measurableSet hμ (hindepX r)
  have hindepYK : ∀ r, ProbabilityTheory.iIndepFun (YK r) (P r) :=
    fun r ↦ iIndepFun_supportedVersion ν K hK.measurableSet hν (hindepY r)
  have hlawXK : ∀ r i, (P r).map (XK r i) =
      (probabilityOnSubset μ K hK.measurableSet hμ : Measure K) :=
    fun r i ↦ map_supportedVersion μ K hK.measurableSet hμ (hX r i) (hlawX r i)
  have hlawYK : ∀ r i, (P r).map (YK r i) =
      (probabilityOnSubset ν K hK.measurableSet hν : Measure K) :=
    fun r i ↦ map_supportedVersion ν K hK.measurableSet hν (hY r i) (hlawY r i)
  have hφK : LipschitzWith 1 (fun x : K ↦ φ x) := by
    simpa only [mul_one, Function.comp_def] using hφ.comp isometry_subtype_coe.lipschitzWith
  have hpre (f : (K × K) →ᵇ ℝ) (t : ℝ) (E : Set ℝ) (r : ℕ) :
      (P r).real ((fun ω ↦ empiricalDistancePressure
        (fun i ↦ XK r i ω) (fun i ↦ YK r i ω) (fun x : K ↦ φ x)
        (((r + 1 : ℕ) : ℝ) ^ (2 / q)) f t) ⁻¹' E) =
      (P r).real ((fun ω ↦ supportedDistancePressure μ ν K hK.measurableSet hμ hν
        (fun i ↦ X r i ω) (fun i ↦ Y r i ω) φ
        (((r + 1 : ℕ) : ℝ) ^ (2 / q)) f t) ⁻¹' E) :=
    outer_probability_congr_ae
      (supportedDistancePressure_eq_ae μ ν K hK.measurableSet hμ hν (X r) (Y r)
        (hX r) (hY r) (hlawX r) (hlawY r) φ _ f t).symm E
  have hzeroK : ∀ f ε, 0 < ε → Tendsto
      (fun r ↦ (P r).real {ω | ε ≤ |empiricalDistancePressure
        (fun i ↦ XK r i ω) (fun i ↦ YK r i ω) (fun x : K ↦ φ x)
        (((r + 1 : ℕ) : ℝ) ^ (2 / q)) f 0 - pressure f 0|}) atTop (𝓝 0) := by
    intro f ε hε
    convert hzero f ε hε using 1
    funext r
    exact hpre f 0 {z | ε ≤ |z - pressure f 0|} r
  have hlowerK : ∀ f t, |t| < radius f → ∀ ε, 0 < ε → Tendsto
      (fun r ↦ (P r).real {ω | ε ≤ max (pressure f t - empiricalDistancePressure
        (fun i ↦ XK r i ω) (fun i ↦ YK r i ω) (fun x : K ↦ φ x)
        (((r + 1 : ℕ) : ℝ) ^ (2 / q)) f t) 0}) atTop (𝓝 0) := by
    intro f t ht ε hε
    convert hlower f t ht ε hε using 1
    funext r
    exact hpre f t {z | ε ≤ max (pressure f t - z) 0} r
  obtain ⟨π, hπ, _⟩ := existsUnique_empirical_optimal_selector_of_iid_pressure
    P XK YK (probabilityOnSubset μ K hK.measurableSet hμ)
    (probabilityOnSubset ν K hK.measurableSet hν) hXK hYK hindepXK hindepYK hlawXK hlawYK
    (fun x : K ↦ φ x) hφK q hq pressure radius derivative hradius hderiv hzeroK hlowerK
  have hface : Tendsto (fun z : Σ r, Ω r ↦ empiricalOptimalFace
      (fun i ↦ XK z.1 i z.2) (fun i ↦ YK z.1 i z.2))
      (rowProbabilityFilter P) (𝓝 π).smallSets := by
    rw [Filter.tendsto_smallSets_iff]
    simpa only [eventually_rowProbabilityFilter_iff, Set.subset_def, not_forall, exists_prop]
      using hπ.2.1
  have htransport := compact_support_selector_transport K hK μ ν hμ hν
    (fun z : Σ r, Ω r ↦ z.1 + 1)
    (fun z i ↦ XK z.1 i z.2) (fun z i ↦ YK z.1 i z.2) π hπ.2.2 hface
  have hfaceAmbient := tendsto_empiricalOptimalFace_of_supportedVersion P X Y μ ν K
    hK.measurableSet hμ hν hX hY hlawX hlawY π hface
  let incl := Prod.map ((↑) : K → M) ((↑) : K → M)
  have hemb : MeasurableEmbedding incl :=
    (MeasurableEmbedding.subtype_coe hK.measurableSet).prodMap
      (MeasurableEmbedding.subtype_coe hK.measurableSet)
  refine ⟨π.map hemb.measurable.aemeasurable, ⟨?_, ?_, htransport.1⟩, ?_⟩
  · intro f
    change (∫ z, f z ∂(((π : Measure (K × K)).map incl).comap incl)) = derivative f
    rw [hemb.comap_map]
    exact hπ.1 f
  · rw [Filter.tendsto_smallSets_iff] at hfaceAmbient
    simpa only [eventually_rowProbabilityFilter_iff, Set.subset_def, not_forall, exists_prop]
      using hfaceAmbient
  · intro κ hκ
    have hcoupling : Vlasov.IsCoupling (κ : Measure (M × M))
        (((μ : Measure M).comap ((↑) : K → M)).map ((↑) : K → M))
        (((ν : Measure M).comap ((↑) : K → M)).map ((↑) : K → M)) := by
      simpa only [map_comap_subtype_of_ae_mem hK.measurableSet hμ,
        map_comap_subtype_of_ae_mem hK.measurableSet hν] using hκ.2.2.1
    have hrecover : ((κ : Measure (M × M)).comap incl).map incl = κ :=
      map_comap_of_isCoupling (MeasurableEmbedding.subtype_coe hK.measurableSet)
        (MeasurableEmbedding.subtype_coe hK.measurableSet) hcoupling
    have : IsProbabilityMeasure (((κ : Measure (M × M)).comap incl).map incl) := by
      rw [hrecover]
      infer_instance
    have : IsProbabilityMeasure ((κ : Measure (M × M)).comap incl) :=
      Measure.isProbabilityMeasure_of_map incl
    have heq : (κ : Measure (M × M)).comap incl = (π : Measure (K × K)) := by
      apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
      intro f
      exact (hκ.1 f).trans (hπ.1 f).symm
    apply ProbabilityMeasure.toMeasure_injective
    change (κ : Measure (M × M)) = (π : Measure (K × K)).map incl
    rw [← heq, hrecover]

end OTSelector.Pressure
