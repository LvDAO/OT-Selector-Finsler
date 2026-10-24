import OTSelector.Reconstruction.FinslerPhysicalSceneCoordinates

/-!
# Actual legal carriers and compact marks of physical scenes

The physical compact carriers give compact sets of actual potential clocks.
On full-measure measurable legal carriers the physical reconstruction is
injective, and both the original root cell and physical support are retained.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Reconstruction

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

variable (D : PopulationHaarPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)

/-- The original coordinate carrier, with the actual inverse identity recorded. -/
def sceneLegalCarrier (i : Fin D.continuous.count) (L : Set (ℚ → M)) (K : Set M) :
    Set ((P (D.continuous.coefficient i).seedIndex).seed.covector.ker × ℝ) :=
  D.sceneDomain i L K ∩ {s | D.sceneCoordinate i
    (populationSeedPhysicalMap (P (D.continuous.coefficient i).seedIndex).seed s) = s}

/-- Physical reconstruction is injective on the actual legal carrier. -/
theorem injOn_physical_sceneLegalCarrier (i : Fin D.continuous.count)
    (L : Set (ℚ → M)) (K : Set M) :
    InjOn (populationSeedPhysicalMap (P (D.continuous.coefficient i).seedIndex).seed)
      (D.sceneLegalCarrier i L K) := by
  intro s hs t ht he
  exact hs.2.symm.trans ((congrArg (D.sceneCoordinate i) he).trans ht.2)

variable (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instSceneMarkMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
  (horder : let _instSceneMarkOrder : MetricSpace M := F.metricSpace
    ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
      (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
  (hb : Measurable b)
  (hinv : ∀ x ∈ F.potentialRegularDomain u, b (a x, u x) = x)
  (hη₀reg : ∀ᵐ x ∂η₀, x ∈ F.potentialRegularDomain u)
  (hη₁reg : ∀ᵐ x ∂η₁, x ∈ F.potentialRegularDomain u)

include hF hcomplete hu ha hinj

/-- Actual legal carriers are measurable, including their inverse identity. -/
theorem measurableSet_sceneLegalCarrier
    (i : Fin D.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.continuous.coefficient i).roots)
    {K : Set M} (hK : MeasurableSet K) : MeasurableSet (D.sceneLegalCarrier i L K) := by
  exact (D.measurableSet_sceneDomain hF hcomplete hu ha hinj i hL hsub hK).inter
    (measurableSet_eq_fun
      ((D.measurable_sceneCoordinate hF hcomplete hu ha hinj i).comp
        (measurable_populationSeedPhysicalMap _)) measurable_id)

include horder hb hinv hη₀reg hη₁reg

/-- Both original scene laws give full mass to their actual legal carrier. -/
theorem sceneLaw_ae_legalCarrier
    (i : Fin D.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.continuous.coefficient i).roots)
    {A B : Set M} (hη₀A : ∀ᵐ x ∂η₀, x ∈ A) (hη₁B : ∀ᵐ x ∂η₁, x ∈ B) :
    (∀ᵐ s ∂D.sceneLaw η₀ i L, s ∈ D.sceneLegalCarrier i L A) ∧
      (∀ᵐ s ∂D.sceneLaw η₁ i L, s ∈ D.sceneLegalCarrier i L B) := by
  obtain ⟨hs, ht⟩ := D.sceneLaw_ae_domain hF hcomplete hu ha hinj horder hb hinv
    hη₀reg hη₁reg i hL hsub hη₀A hη₁B
  obtain ⟨hsi, hti⟩ := D.sceneCoordinate_physical_inverse_ae hF hcomplete hu ha hinj
    horder hb hinv hη₀reg hη₁reg i hL hsub
  exact ⟨hs.and hsi, ht.and hti⟩

/-- The two actual mark marginals are carried by compact images of the original
physical supports, using the same potential clock as the scene law. -/
theorem sceneLaw_compact_clock_carriers
    (i : Fin D.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.continuous.coefficient i).roots)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hη₀A : ∀ᵐ x ∂η₀, x ∈ A) (hη₁B : ∀ᵐ x ∂η₁, x ∈ B) :
    IsCompact (u '' A) ∧ IsCompact (u '' B) ∧
      (∀ᵐ s ∂D.sceneLaw η₀ i L, s.2 ∈ u '' A) ∧
        (∀ᵐ s ∂D.sceneLaw η₁ i L, s.2 ∈ u '' B) := by
  let _instSceneMarkMetric : MetricSpace M := F.metricSpace
  obtain ⟨hs, ht⟩ := D.sceneLaw_ae_legalCarrier hF hcomplete hu ha hinj horder hb hinv
    hη₀reg hη₁reg i hL hsub hη₀A hη₁B
  refine ⟨hA.image hu.continuous, hB.image hu.continuous, ?_, ?_⟩
  · filter_upwards [hs] with s hs
    exact ⟨_, hs.1.2, congrArg Prod.snd hs.2⟩
  · filter_upwards [ht] with s ht
    exact ⟨_, ht.1.2, congrArg Prod.snd ht.2⟩

end PopulationHaarPressureCore
end OTSelector.Reconstruction
