import OTSelector.Limit.PhysicalSelectorFinal

/-!
# Population carrier lifts and transfer of the entire empirical face

An ambient population optimum has one optimal probability lift to its two compact
carriers. The lift is constructed without sampling data. For each later sampling
implementation, exact marginal laws transfer convergence of the entire ambient
optimal face to that same carrier lift, including every fractional optimum.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Topology
open OTSelector.Probability
open scoped Topology ENNReal

noncomputable section

namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [ProperSpace M]

/-- Push a probability plan on the two carriers to the original ambient product. -/
def originalGeneralSelectorCarrierPushforward {A B : Set M}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (πAB : ProbabilityMeasure (A × B)) : ProbabilityMeasure (M × M) :=
  πAB.map ((MeasurableEmbedding.subtype_coe hA).measurable.prodMap
    (MeasurableEmbedding.subtype_coe hB).measurable).aemeasurable

/-- A fixed ambient population optimum has exactly one optimal carrier lift.
The witness depends only on the population plan, marginals and compact carriers. -/
theorem existsUnique_originalGeneralSelectorCarrierLift
    (μ ν : ProbabilityMeasure M) {A B : Set M}
    (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    (π : ProbabilityMeasure (M × M))
    (hπ : IsOptimalCoupling edist (μ : Measure M) (ν : Measure M)
      (π : Measure (M × M))) :
    ∃! πAB : ProbabilityMeasure (A × B),
      IsOptimalCoupling (fun (x : A) (y : B) ↦ edist (x : M) (y : M))
        (probabilityOnSubset μ A hA.measurableSet hμA)
        (probabilityOnSubset ν B hB.measurableSet hνB) (πAB : Measure (A × B)) ∧
      originalGeneralSelectorCarrierPushforward hA.measurableSet hB.measurableSet πAB = π := by
  have hμmap : ((probabilityOnSubset μ A hA.measurableSet hμA : Measure A)).map
      ((↑) : A → M) = (μ : Measure M) := by
    simpa only [ProbabilityMeasure.toMeasure_map] using
      congrArg (fun η : ProbabilityMeasure M ↦ (η : Measure M))
        (map_probabilityOnSubset μ A hA.measurableSet hμA)
  have hνmap : ((probabilityOnSubset ν B hB.measurableSet hνB : Measure B)).map
      ((↑) : B → M) = (ν : Measure M) := by
    simpa only [ProbabilityMeasure.toMeasure_map] using
      congrArg (fun η : ProbabilityMeasure M ↦ (η : Measure M))
        (map_probabilityOnSubset ν B hB.measurableSet hνB)
  have hface := image_optimalProbabilityCouplings_embedding
    (MeasurableEmbedding.subtype_coe hA.measurableSet)
    (MeasurableEmbedding.subtype_coe hB.measurableSet)
    (fun (x : A) (y : B) ↦ edist (x : M) (y : M)) edist (fun _ _ ↦ rfl)
    (probabilityOnSubset μ A hA.measurableSet hμA)
    (probabilityOnSubset ν B hB.measurableSet hνB)
  rw [hμmap, hνmap] at hface
  have hmem : π ∈ (fun η : ProbabilityMeasure (A × B) ↦
      originalGeneralSelectorCarrierPushforward hA.measurableSet hB.measurableSet η) ''
      {η | IsOptimalCoupling (fun (x : A) (y : B) ↦ edist (x : M) (y : M))
        (probabilityOnSubset μ A hA.measurableSet hμA)
        (probabilityOnSubset ν B hB.measurableSet hνB) (η : Measure (A × B))} := by
    change π ∈ (fun η : ProbabilityMeasure (A × B) ↦ η.map
      ((MeasurableEmbedding.subtype_coe hA.measurableSet).measurable.prodMap
        (MeasurableEmbedding.subtype_coe hB.measurableSet).measurable).aemeasurable) '' _
    rw [hface]
    exact hπ
  obtain ⟨πAB, hopt, hmap⟩ := hmem
  refine ⟨πAB, ⟨hopt, hmap⟩, ?_⟩
  intro η hη
  apply (isEmbedding_probabilityMeasure_map_subtype_prod hA hB).injective
  exact hη.2.trans hmap.symm

/-- Every later sampling realization transfers whole-face convergence to the
same fixed carrier plan. Independence is unnecessary for this transfer. -/
theorem originalGeneralSelectorCarrierLift_wholeFace
    (μ ν : ProbabilityMeasure M) {A B : Set M}
    (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    (π : ProbabilityMeasure (M × M)) (πAB : ProbabilityMeasure (A × B))
    (hmap : originalGeneralSelectorCarrierPushforward hA.measurableSet
      hB.measurableSet πAB = π)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (ν : Measure M))
    (hface : ∀ U ∈ 𝓝 π, Tendsto (fun n ↦ (P n).real
      {s | ∃ γ ∈ Pressure.empiricalOptimalFace
        (fun i ↦ X n i s) (fun i ↦ Y n i s), γ ∉ U}) atTop (𝓝 0)) :
    ∀ U ∈ 𝓝 πAB, Tendsto (fun n ↦ (P n).real
      {s | ∃ γ ∈ carrierEmpiricalFace
        (fun i ↦ supportedVersion μ A hA.measurableSet hμA (X n i) s)
        (fun i ↦ supportedVersion ν B hB.measurableSet hνB (Y n i) s), γ ∉ U})
      atTop (𝓝 0) := by
  let Φ := originalGeneralSelectorCarrierPushforward hA.measurableSet hB.measurableSet
  have hFG : ∀ n, ∀ᵐ s ∂(P n),
      Φ '' carrierEmpiricalFace
        (fun i ↦ supportedVersion μ A hA.measurableSet hμA (X n i) s)
        (fun i ↦ supportedVersion ν B hB.measurableSet hνB (Y n i) s) =
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
    have hxAeq : (fun i ↦ (supportedVersion μ A hA.measurableSet hμA (X n i) s : M)) =
        fun i ↦ X n i s := by
      funext i
      exact congrArg Subtype.val
        (supportProjection_coe μ A hA.measurableSet hμA ⟨X n i s, hxs i⟩)
    have hyBeq : (fun i ↦ (supportedVersion ν B hB.measurableSet hνB (Y n i) s : M)) =
        fun i ↦ Y n i s := by
      funext i
      exact congrArg Subtype.val
        (supportProjection_coe ν B hB.measurableSet hνB ⟨Y n i s, hys i⟩)
    have h := image_empiricalOptimalFace_subtype_prod hA.measurableSet hB.measurableSet
      (fun i ↦ supportedVersion μ A hA.measurableSet hμA (X n i) s)
      (fun i ↦ supportedVersion ν B hB.measurableSet hνB (Y n i) s)
    rw [hxAeq, hyBeq] at h
    exact h
  exact OTSelector.tendsto_measureReal_exists_notMem_of_face_embedding P Φ
    (isEmbedding_probabilityMeasure_map_subtype_prod hA hB) hmap
    (fun n s ↦ carrierEmpiricalFace
      (fun i ↦ supportedVersion μ A hA.measurableSet hμA (X n i) s)
      (fun i ↦ supportedVersion ν B hB.measurableSet hνB (Y n i) s))
    (fun n s ↦ Pressure.empiricalOptimalFace (fun i ↦ X n i s) (fun i ↦ Y n i s))
    hFG hface

/-- The fixed population carrier lift satisfies the metric form for every
weakly open ball, simultaneously for all fractional empirical optima. -/
theorem originalGeneralSelectorCarrierLift_metric
    (μ ν : ProbabilityMeasure M) {A B : Set M}
    (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    (π : ProbabilityMeasure (M × M)) (πAB : ProbabilityMeasure (A × B))
    (hmap : originalGeneralSelectorCarrierPushforward hA.measurableSet
      hB.measurableSet πAB = π)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (ν : Measure M))
    (hface : ∀ U ∈ 𝓝 π, Tendsto (fun n ↦ (P n).real
      {s | ∃ γ ∈ Pressure.empiricalOptimalFace
        (fun i ↦ X n i s) (fun i ↦ Y n i s), γ ∉ U}) atTop (𝓝 0))
    (d : ProbabilityMeasure (A × B) → ProbabilityMeasure (A × B) → ℝ)
    (hd0 : d πAB πAB = 0)
    (hdopen : ∀ ε : ℝ, 0 < ε → IsOpen {γ : ProbabilityMeasure (A × B) | d γ πAB < ε}) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n ↦ (P n).real
      {s | ∃ γ ∈ carrierEmpiricalFace
        (fun i ↦ supportedVersion μ A hA.measurableSet hμA (X n i) s)
        (fun i ↦ supportedVersion ν B hB.measurableSet hνB (Y n i) s), ε ≤ d γ πAB})
      atTop (𝓝 0) := by
  exact OTSelector.tendsto_measureReal_exists_metric_le_of_forall_nhds P
    (fun n s ↦ carrierEmpiricalFace
      (fun i ↦ supportedVersion μ A hA.measurableSet hμA (X n i) s)
      (fun i ↦ supportedVersion ν B hB.measurableSet hνB (Y n i) s))
    πAB d hd0 hdopen
    (originalGeneralSelectorCarrierLift_wholeFace μ ν hA hB hμA hνB π πAB hmap
      P X Y hX hY hXlaw hYlaw hface)

end OTSelector.Reconstruction
