import OTSelector.Transport.EmpiricalSelector.CompactSupport

/-!
# Supported versions on the original probability space

A measurable carrier of full marginal mass admits a measurable retraction. Composing the
original variables with this retraction gives carrier-valued versions on the same probability
space, equal to the original observations almost everywhere after inclusion. Their laws are
exactly the pullback probabilities, without normalization or resampling. Measurable composition
preserves independence. Finite simultaneous equality identifies the entire empirical optimal
face, including ties and repeated observations, and preserves outer failure probabilities.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace OTSelector.Probability

open Reconstruction

variable {M Ω : Type*} [MeasurableSpace M] [MeasurableSpace Ω]

/-- Full mass in a measurable set supplies the almost-everywhere support premise. -/
theorem ae_mem_of_probability_one (μ : ProbabilityMeasure M) (K : Set M)
    (hK : MeasurableSet K) (hμ : (μ : Measure M) K = 1) :
    ∀ᵐ x ∂(μ : Measure M), x ∈ K :=
  (mem_ae_iff_prob_eq_one hK).mpr hμ

/-- A measurable retraction onto a full-mass carrier; its off-carrier values are immaterial. -/
noncomputable def supportProjection (μ : ProbabilityMeasure M) (K : Set M)
    (hK : MeasurableSet K) (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) : M → K :=
  (hK.exists_measurable_proj hμ.exists).choose

/-- The selected retraction is measurable. -/
theorem measurable_supportProjection (μ : ProbabilityMeasure M) (K : Set M)
    (hK : MeasurableSet K) (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) :
    Measurable (supportProjection μ K hK hμ) :=
  (hK.exists_measurable_proj hμ.exists).choose_spec.1

/-- Every point already in the carrier is fixed exactly. -/
@[simp] theorem supportProjection_coe (μ : ProbabilityMeasure M) (K : Set M)
    (hK : MeasurableSet K) (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (x : K) :
    supportProjection μ K hK hμ x = x :=
  (hK.exists_measurable_proj hμ.exists).choose_spec.2 x

/-- Carrier-valued version of an ambient random variable on its original sample space. -/
noncomputable def supportedVersion (μ : ProbabilityMeasure M) (K : Set M)
    (hK : MeasurableSet K) (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (X : Ω → M) : Ω → K :=
  supportProjection μ K hK hμ ∘ X

/-- Measurability is preserved by the construction. -/
theorem measurable_supportedVersion (μ : ProbabilityMeasure M) (K : Set M)
    (hK : MeasurableSet K) (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K)
    {X : Ω → M} (hX : Measurable X) : Measurable (supportedVersion μ K hK hμ X) :=
  (measurable_supportProjection μ K hK hμ).comp hX

/-- Inclusion agrees almost everywhere with the given ambient variable, under the same law. -/
theorem coe_supportedVersion_ae (μ : ProbabilityMeasure M) (K : Set M)
    (hK : MeasurableSet K) (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K)
    {P : Measure Ω} {X : Ω → M} (hX : Measurable X) (hlaw : P.map X = μ) :
    (fun ω ↦ (supportedVersion μ K hK hμ X ω : M)) =ᵐ[P] X := by
  have hmem : ∀ᵐ x ∂P.map X, x ∈ K := by rwa [hlaw]
  filter_upwards [ae_of_ae_map hX.aemeasurable hmem] with ω hω
  exact congrArg Subtype.val (supportProjection_coe μ K hK hμ ⟨X ω, hω⟩)

/-- The version has the exact carrier law obtained by pullback, with no change to `P`. -/
theorem map_supportedVersion (μ : ProbabilityMeasure M) (K : Set M)
    (hK : MeasurableSet K) (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K)
    {P : Measure Ω} {X : Ω → M} (hX : Measurable X) (hlaw : P.map X = μ) :
    P.map (supportedVersion μ K hK hμ X) = probabilityOnSubset μ K hK hμ := by
  apply (MeasurableEmbedding.subtype_coe hK).map_injective
  rw [Measure.map_map measurable_subtype_coe (measurable_supportedVersion μ K hK hμ hX)]
  change P.map (fun ω ↦ (supportedVersion μ K hK hμ X ω : M)) =
    ((μ : Measure M).comap ((↑) : K → M)).map ((↑) : K → M)
  rw [map_comap_subtype_of_ae_mem hK hμ, ← hlaw]
  exact Measure.map_congr (coe_supportedVersion_ae μ K hK hμ hX hlaw)

/-- Any independent family remains independent after passing to supported versions. -/
theorem iIndepFun_supportedVersion (μ : ProbabilityMeasure M) (K : Set M)
    (hK : MeasurableSet K) (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K)
    {ι : Type*} {P : Measure Ω} {X : ι → Ω → M}
    (hX : ProbabilityTheory.iIndepFun X P) :
    ProbabilityTheory.iIndepFun (fun i ↦ supportedVersion μ K hK hμ (X i)) P :=
  hX.comp (fun _ ↦ supportProjection μ K hK hμ)
    (fun _ ↦ measurable_supportProjection μ K hK hμ)

/-- Independence of two colors is preserved, if it is part of the original model. -/
theorem indepFun_supportedVersion (μ ν : ProbabilityMeasure M) (K : Set M)
    (hK : MeasurableSet K) (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K)
    (hν : ∀ᵐ x ∂(ν : Measure M), x ∈ K)
    {P : Measure Ω} {X Y : Ω → M} (hXY : ProbabilityTheory.IndepFun X Y P) :
    ProbabilityTheory.IndepFun (supportedVersion μ K hK hμ X)
      (supportedVersion ν K hK hν Y) P :=
  hXY.comp (measurable_supportProjection μ K hK hμ)
    (measurable_supportProjection ν K hK hν)

/-- Independence of the two entire sample families is preserved as well. -/
theorem indepFun_supportedVersion_family (μ ν : ProbabilityMeasure M) (K : Set M)
    (hK : MeasurableSet K) (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K)
    (hν : ∀ᵐ x ∂(ν : Measure M), x ∈ K)
    {ι κ : Type*} {P : Measure Ω} {X : ι → Ω → M} {Y : κ → Ω → M}
    (hXY : ProbabilityTheory.IndepFun (fun ω i ↦ X i ω) (fun ω j ↦ Y j ω) P) :
    ProbabilityTheory.IndepFun
      (fun ω i ↦ supportedVersion μ K hK hμ (X i) ω)
      (fun ω j ↦ supportedVersion ν K hK hν (Y j) ω) P :=
  hXY.comp (measurable_pi_iff.mpr fun i ↦
    (measurable_supportProjection μ K hK hμ).comp (measurable_pi_apply i))
    (measurable_pi_iff.mpr fun j ↦
      (measurable_supportProjection ν K hK hν).comp (measurable_pi_apply j))

/-- Almost-everywhere equality preserves every outer event probability, without event measurability. -/
theorem outer_probability_congr_ae {A : Type*} {P : Measure Ω} {X Y : Ω → A}
    (h : X =ᵐ[P] Y) (E : Set A) : P.real (X ⁻¹' E) = P.real (Y ⁻¹' E) :=
  measureReal_congr (h.preimage E)

/-- Rowwise almost-everywhere equality is equality along the original row-probability filter. -/
theorem eventuallyEq_rowProbabilityFilter_of_ae {Ωr : ℕ → Type*}
    [∀ r, MeasurableSpace (Ωr r)] (P : ∀ r, Measure (Ωr r))
    [∀ r, IsFiniteMeasure (P r)] {A : Type*} {X Y : (Σ r, Ωr r) → A}
    (h : ∀ r, (fun ω ↦ X ⟨r, ω⟩) =ᵐ[P r] (fun ω ↦ Y ⟨r, ω⟩)) :
    X =ᶠ[rowProbabilityFilter P] Y := by
  apply (eventually_rowProbabilityFilter_iff P _).mpr
  have hz : (fun r ↦ (P r).real {ω | X ⟨r, ω⟩ ≠ Y ⟨r, ω⟩}) = fun _ ↦ 0 := by
    funext r
    rw [Measure.real, (ae_iff.mp (h r)), ENNReal.toReal_zero]
  rw [hz]
  exact tendsto_const_nhds

section Metric
variable [MetricSpace M]

/-- For each finite sample row, inclusion maps the full subtype optimal face onto the actual
ambient face almost everywhere. Samples need not be distinct or independent. -/
theorem image_empiricalOptimalFace_supportedVersion_ae
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ x ∂(ν : Measure M), x ∈ K)
    {P : Measure Ω} {n : ℕ} [NeZero n] (X Y : Fin n → Ω → M)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hlawX : ∀ i, P.map (X i) = μ) (hlawY : ∀ i, P.map (Y i) = ν) :
    (fun ω ↦ (fun π : ProbabilityMeasure (K × K) ↦
      π.map (measurable_subtype_coe.prodMap measurable_subtype_coe).aemeasurable) ''
        Pressure.empiricalOptimalFace
          (fun i ↦ supportedVersion μ K hK hμ (X i) ω)
          (fun i ↦ supportedVersion ν K hK hν (Y i) ω)) =ᵐ[P]
      (fun ω ↦ Pressure.empiricalOptimalFace (fun i ↦ X i ω) (fun i ↦ Y i ω)) := by
  have hx := ae_all_iff.mpr (fun i ↦ coe_supportedVersion_ae μ K hK hμ (hX i) (hlawX i))
  have hy := ae_all_iff.mpr (fun i ↦ coe_supportedVersion_ae ν K hK hν (hY i) (hlawY i))
  filter_upwards [hx, hy] with ω hxω hyω
  rw [image_empiricalOptimalFace_subtype hK, funext hxω, funext hyω]

/-- In particular, the outer failure probability of the full optimal face is unchanged. -/
theorem outer_empiricalOptimalFace_supportedVersion
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ x ∂(ν : Measure M), x ∈ K)
    {P : Measure Ω} {n : ℕ} [NeZero n] (X Y : Fin n → Ω → M)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hlawX : ∀ i, P.map (X i) = μ) (hlawY : ∀ i, P.map (Y i) = ν)
    (U : Set (ProbabilityMeasure (M × M))) :
    P.real {ω | ∃ γ ∈ (fun π : ProbabilityMeasure (K × K) ↦
      π.map (measurable_subtype_coe.prodMap measurable_subtype_coe).aemeasurable) ''
        Pressure.empiricalOptimalFace
          (fun i ↦ supportedVersion μ K hK hμ (X i) ω)
          (fun i ↦ supportedVersion ν K hK hν (Y i) ω), γ ∉ U} =
      P.real {ω | ∃ γ ∈ Pressure.empiricalOptimalFace
        (fun i ↦ X i ω) (fun i ↦ Y i ω), γ ∉ U} :=
  outer_probability_congr_ae
    (image_empiricalOptimalFace_supportedVersion_ae μ ν K hK hμ hν X Y hX hY hlawX hlawY)
    {A | ∃ γ ∈ A, γ ∉ U}

end Metric
end OTSelector.Probability
