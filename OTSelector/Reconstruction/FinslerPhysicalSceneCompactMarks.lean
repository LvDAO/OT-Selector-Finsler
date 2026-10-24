import OTSelector.Reconstruction.FinslerPhysicalSceneMarks

/-!
# Compact mark carriers for the actual physical scene laws

The original real clock can be read as a point of its actual compact physical
carrier.  Forgetting this subtype returns the entire original scene law
exactly.  This supplies compact target mark types without replacing the original
conditional clock distribution.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Reconstruction

namespace PhysicalScene

variable {V : Type*} [MeasurableSpace V]

/-- Read a clock in its actual carrier, with a harmless completion off the carrier. -/
def compactClockRead (K : Set ℝ) (k₀ : K) : ℝ → K :=
  Function.extend ((↑) : K → ℝ) id (fun _ ↦ k₀)

/-- Forget the compact clock subtype. -/
def compactMarkForget (K : Set ℝ) : V × K → V × ℝ :=
  Prod.map id Subtype.val

/-- Read the same actual spatial point and its compact clock mark. -/
def compactMarkRead (K : Set ℝ) (k₀ : K) : V × ℝ → V × K :=
  Prod.map id (compactClockRead K k₀)

/-- The compact clock completion is measurable on every measurable carrier. -/
theorem measurable_compactClockRead {K : Set ℝ} (hK : MeasurableSet K) (k₀ : K) :
    Measurable (compactClockRead K k₀) :=
  (MeasurableEmbedding.subtype_coe hK).measurable_extend measurable_id measurable_const

/-- The clock observation agrees with the original clock everywhere in its carrier. -/
theorem compactClockRead_apply (K : Set ℝ) (k₀ t : K) :
    compactClockRead K k₀ (t : ℝ) = t :=
  Subtype.val_injective.extend_apply _ _ t

/-- The spatial point and compact clock observation are jointly measurable. -/
theorem measurable_compactMarkRead {K : Set ℝ} (hK : MeasurableSet K) (k₀ : K) :
    Measurable (compactMarkRead (V := V) K k₀) :=
  measurable_id.prodMap (measurable_compactClockRead hK k₀)

/-- Forgetting the compact clock is measurable. -/
theorem measurable_compactMarkForget (K : Set ℝ) :
    Measurable (compactMarkForget (V := V) K) :=
  measurable_id.prodMap measurable_subtype_coe

omit [MeasurableSpace V] in
/-- Forgetting the subtype after reading a compact mark returns the actual point. -/
theorem compactMarkForget_read {K : Set ℝ} (k₀ : K) {s : V × ℝ} (hs : s.2 ∈ K) :
    compactMarkForget K (compactMarkRead K k₀ s) = s := by
  have ht := compactClockRead_apply K k₀ (⟨s.2, hs⟩ : K)
  exact Prod.ext rfl (congrArg Subtype.val ht)

/-- Reading and forgetting a carried compact mark preserves the whole scene law. -/
theorem map_compactMarkRead_forget (μ : Measure (V × ℝ))
    {K : Set ℝ} (hK : MeasurableSet K) (k₀ : K)
    (hcarrier : ∀ᵐ s ∂μ, s.2 ∈ K) :
    (μ.map (compactMarkRead K k₀)).map (compactMarkForget K) = μ := by
  rw [Measure.map_map (measurable_compactMarkForget K)
    (measurable_compactMarkRead hK k₀)]
  have heq : compactMarkForget K ∘ compactMarkRead K k₀ =ᵐ[μ] id :=
    hcarrier.mono fun s hs ↦ compactMarkForget_read k₀ hs
  rw [Measure.map_congr heq, Measure.map_id]

/-- Compact mark observation preserves the original physical recovery law. -/
theorem map_compactMarkRead_physical {X : Type*} [MeasurableSpace X]
    (μ : Measure (V × ℝ)) {K : Set ℝ} (hK : MeasurableSet K) (k₀ : K)
    (hcarrier : ∀ᵐ s ∂μ, s.2 ∈ K)
    (physical : V × ℝ → X) (hp : Measurable physical) :
    (μ.map (compactMarkRead K k₀)).map (physical ∘ compactMarkForget K) =
      μ.map physical := by
  rw [← Measure.map_map hp (measurable_compactMarkForget K),
    map_compactMarkRead_forget μ hK k₀ hcarrier]

end PhysicalScene

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

namespace PopulationHaarPressureCore

/-- Positive original cell mass produces nonempty compact clock carriers for
both actual scene populations, ready to be used as compact mark types. -/
theorem nonempty_compact_scene_clock_carriers
    (D : PopulationHaarPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hb : Measurable b)
    (hinv : ∀ x ∈ F.potentialRegularDomain u, b (a x, u x) = x)
    (hη₀reg : ∀ᵐ x ∂η₀, x ∈ F.potentialRegularDomain u)
    (hη₁reg : ∀ᵐ x ∂η₁, x ∈ F.potentialRegularDomain u)
    (i : Fin D.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.continuous.coefficient i).roots) (hmass : 0 < lambda.real L)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hη₀A : ∀ᵐ x ∂η₀, x ∈ A) (hη₁B : ∀ᵐ x ∂η₁, x ∈ B) :
    IsCompact (u '' A) ∧ IsCompact (u '' B) ∧
      Nonempty (u '' A) ∧ Nonempty (u '' B) := by
  obtain ⟨hAc, hBc, hsrc, htrg⟩ := D.sceneLaw_compact_clock_carriers hF hcomplete hu ha
    hinj horder hb hinv hη₀reg hη₁reg i hL hsub hA hB hη₀A hη₁B
  obtain ⟨hμ, hν⟩ := D.sceneLaw_probability hF hcomplete hu ha hinj i hL hsub hmass
  let _instSourceProbability : IsProbabilityMeasure (D.sceneLaw η₀ i L) := hμ
  let _instTargetProbability : IsProbabilityMeasure (D.sceneLaw η₁ i L) := hν
  obtain ⟨s, hs⟩ := hsrc.exists
  obtain ⟨t, ht⟩ := htrg.exists
  exact ⟨hAc, hBc, ⟨⟨s.2, hs⟩⟩, ⟨⟨t.2, ht⟩⟩⟩

/-- Both actual scene laws have compact clock-mark types.  Forgetting the
compact mark returns the original law exactly, and physical recovery returns
the same normalized restrictions of the original populations. -/
theorem exists_compact_mark_scene_laws
    (D : PopulationHaarPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hb : Measurable b)
    (hinv : ∀ x ∈ F.potentialRegularDomain u, b (a x, u x) = x)
    (hη₀reg : ∀ᵐ x ∂η₀, x ∈ F.potentialRegularDomain u)
    (hη₁reg : ∀ᵐ x ∂η₁, x ∈ F.potentialRegularDomain u)
    (i : Fin D.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.continuous.coefficient i).roots) (hmass : 0 < lambda.real L)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hη₀A : ∀ᵐ x ∂η₀, x ∈ A) (hη₁B : ∀ᵐ x ∂η₁, x ∈ B) :
    let S := (P (D.continuous.coefficient i).seedIndex).seed
    let V := S.covector.ker
    ∃ α : Measure (V × (u '' A)), ∃ β : Measure (V × (u '' B)),
      IsProbabilityMeasure α ∧ IsProbabilityMeasure β ∧
      α.map (PhysicalScene.compactMarkForget (u '' A)) = D.sceneLaw η₀ i L ∧
      β.map (PhysicalScene.compactMarkForget (u '' B)) = D.sceneLaw η₁ i L ∧
      α.map (populationSeedPhysicalMap S ∘ PhysicalScene.compactMarkForget (u '' A)) =
        normalizedFiniteLaw (η₀.restrict (a ⁻¹' L)) ∧
      β.map (populationSeedPhysicalMap S ∘ PhysicalScene.compactMarkForget (u '' B)) =
        normalizedFiniteLaw (η₁.restrict (a ⁻¹' L)) := by
  obtain ⟨hAc, hBc, hAn, hBn⟩ := D.nonempty_compact_scene_clock_carriers
    hF hcomplete hu ha hinj horder hb hinv hη₀reg hη₁reg i hL hsub hmass hA hB hη₀A hη₁B
  obtain ⟨hμ, hν⟩ := D.sceneLaw_probability hF hcomplete hu ha hinj i hL hsub hmass
  let _instSourceProbability : IsProbabilityMeasure (D.sceneLaw η₀ i L) := hμ
  let _instTargetProbability : IsProbabilityMeasure (D.sceneLaw η₁ i L) := hν
  obtain ⟨_, _, hsrc, htrg⟩ := D.sceneLaw_compact_clock_carriers hF hcomplete hu ha hinj
    horder hb hinv hη₀reg hη₁reg i hL hsub hA hB hη₀A hη₁B
  obtain ⟨hps, hpt⟩ := D.sceneLaw_physical_recovery hF hcomplete hu ha hinj horder hb hinv
    hη₀reg hη₁reg i hL hsub
  let s₀ : u '' A := hAn.some
  let t₀ : u '' B := hBn.some
  let α := (D.sceneLaw η₀ i L).map (PhysicalScene.compactMarkRead (u '' A) s₀)
  let β := (D.sceneLaw η₁ i L).map (PhysicalScene.compactMarkRead (u '' B) t₀)
  have hα : IsProbabilityMeasure α :=
    Measure.isProbabilityMeasure_map (PhysicalScene.measurable_compactMarkRead
      hAc.measurableSet s₀).aemeasurable
  have hβ : IsProbabilityMeasure β :=
    Measure.isProbabilityMeasure_map (PhysicalScene.measurable_compactMarkRead
      hBc.measurableSet t₀).aemeasurable
  refine ⟨α, β, hα, hβ,
    PhysicalScene.map_compactMarkRead_forget _ hAc.measurableSet s₀ hsrc,
    PhysicalScene.map_compactMarkRead_forget _ hBc.measurableSet t₀ htrg, ?_, ?_⟩
  · rw [PhysicalScene.map_compactMarkRead_physical _ hAc.measurableSet s₀ hsrc
      _ (measurable_populationSeedPhysicalMap _), hps]
  · rw [PhysicalScene.map_compactMarkRead_physical _ hBc.measurableSet t₀ htrg
      _ (measurable_populationSeedPhysicalMap _), hpt]

end PopulationHaarPressureCore
end OTSelector.Reconstruction
