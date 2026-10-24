import OTSelector.Reconstruction.FinslerPhysicalSceneReadoutIterated

/-!
# Auxiliary actual retained-plan limits preserve the previously fixed full scene

An auxiliary joint observation may retain pieces of the SAME original plans.
Its tightness lifts both previously selected weak-limit stages while keeping
their exact full-scene projections. Each stage only refines its own subsequence;
there is no tilt/sample diagonal and no additional accuracy-limit law.
-/

open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace OTSelector.Probability
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction

variable {X Y : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [T2Space X] [PseudoMetrizableSpace X] [SeparableSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [PseudoMetrizableSpace Y]

/-- Exact projection and tightness extend the SAME given inner and outer weak
limits to an actual auxiliary observation of their original two-index laws. -/
theorem exists_iterated_weak_extension_of_exact_projection
    (P : ℕ → ℕ → ProbabilityMeasure X) (Pfull : ℕ → ℕ → ProbabilityMeasure Y)
    (f : X → Y) (hf : Continuous f)
    (hmap : ∀ ℓ n, (P ℓ n).map hf.measurable.aemeasurable = Pfull ℓ n)
    (htight : IsTightMeasureSet (range (fun q : ℕ × ℕ ↦ (P q.1 q.2 : Measure X))))
    (Qfull : ℕ → ProbabilityMeasure Y) (Rfull : ProbabilityMeasure Y)
    (φ : ℕ → ℕ → ℕ) (hφ : ∀ ℓ, StrictMono (φ ℓ))
    (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    (hinner : ∀ ℓ, Tendsto (fun n ↦ Pfull ℓ (φ ℓ n)) atTop (𝓝 (Qfull ℓ)))
    (houter : Tendsto (fun ℓ ↦ Qfull (ψ ℓ)) atTop (𝓝 Rfull)) :
    ∃ Q : ℕ → ProbabilityMeasure X, ∃ θ : ℕ → ℕ → ℕ,
      (∀ ℓ, StrictMono (θ ℓ) ∧ StrictMono (fun n ↦ φ ℓ (θ ℓ n)) ∧
        Tendsto (fun n ↦ P ℓ (φ ℓ (θ ℓ n))) atTop (𝓝 (Q ℓ)) ∧
        (Q ℓ).map hf.measurable.aemeasurable = Qfull ℓ) ∧
      ∃ R : ProbabilityMeasure X, ∃ η : ℕ → ℕ,
        StrictMono η ∧ StrictMono (fun ℓ ↦ ψ (η ℓ)) ∧
        Tendsto (fun ℓ ↦ Q (ψ (η ℓ))) atTop (𝓝 R) ∧
        R.map hf.measurable.aemeasurable = Rfull := by
  have hfixed (ℓ : ℕ) : ∃ Q : ProbabilityMeasure X, ∃ θ : ℕ → ℕ,
      StrictMono θ ∧ Tendsto (fun n ↦ P ℓ (φ ℓ (θ n))) atTop (𝓝 Q) := by
    apply exists_tendsto_subseq_probabilityMeasure_of_isTight
      (fun n ↦ P ℓ (φ ℓ n))
    apply htight.subset
    rintro _ ⟨n, rfl⟩
    exact ⟨(ℓ, φ ℓ n), rfl⟩
  choose Q θ hθ hQ using hfixed
  have hQmap (ℓ : ℕ) : (Q ℓ).map hf.measurable.aemeasurable = Qfull ℓ := by
    have hm := ((ProbabilityMeasure.continuous_map hf).tendsto (Q ℓ)).comp (hQ ℓ)
    have hy := (hinner ℓ).comp (hθ ℓ).tendsto_atTop
    simp only [Function.comp_def] at hm hy
    simp_rw [hmap] at hm
    exact tendsto_nhds_unique hm hy
  have htightψ : IsTightMeasureSet
      (range (fun q : ℕ × ℕ ↦ (P (ψ q.1) q.2 : Measure X))) := by
    apply htight.subset
    rintro _ ⟨q, rfl⟩
    exact ⟨(ψ q.1, q.2), rfl⟩
  obtain ⟨R, η, hη, hR⟩ := exists_tendsto_outer_subseq_of_uniform_inner_tightness
    (fun ℓ n ↦ P (ψ ℓ) n) htightψ (fun ℓ ↦ Q (ψ ℓ))
    (fun ℓ n ↦ φ (ψ ℓ) (θ (ψ ℓ) n)) (fun ℓ ↦ hQ (ψ ℓ))
  have hRmap : R.map hf.measurable.aemeasurable = Rfull := by
    have hm := ((ProbabilityMeasure.continuous_map hf).tendsto R).comp hR
    have hy := houter.comp hη.tendsto_atTop
    simp only [Function.comp_def] at hm hy
    simp_rw [hQmap] at hm
    exact tendsto_nhds_unique hm hy
  exact ⟨Q, θ, fun ℓ ↦ ⟨hθ ℓ, (hφ ℓ).comp (hθ ℓ), hQ ℓ, hQmap ℓ⟩,
    R, η, hη, hψ.comp hη, hR, hRmap⟩

end OTSelector.Reconstruction
