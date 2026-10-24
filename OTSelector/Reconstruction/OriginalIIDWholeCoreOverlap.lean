import OTSelector.Reconstruction.OriginalIIDWholeCoreSceneKernel

/-!
# The same original scene candidate on overlapping measured cores

The rational-frame owner depends on the core only through membership in it.
With the same frame laws Q, the two whole-core scene kernels therefore agree
on their intersection. Restricting either joint law to any measured subset of
that intersection gives exactly the same original, unnormalized measure.
-/

open Set Function Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 20000

variable {q : ℕ}

local instance iidWholeCoreOverlapPointStandardBorel :
    StandardBorelSpace ((Fin q → ℝ) × ℝ) := inferInstance
local instance iidWholeCoreOverlapConfigurationTopology :
    TopologicalSpace (LocalConfiguration (0 : (Fin q → ℝ) × ℝ)) :=
  LocalConfiguration.vagueTopology _
local instance iidWholeCoreOverlapConfigurationBorel :
    BorelSpace (LocalConfiguration (0 : (Fin q → ℝ) × ℝ)) :=
  LocalConfiguration.vagueBorelSpace

set_option quotPrecheck false
local notation "V" => (Fin q → ℝ)
local notation "X" => V × ℝ
local notation "Scene" => OriginalIIDMaskedMacroInputScene (Fin q)
local notation "Macro" => OriginalIIDMaskedMacroCarrier (0 : X)

/-- Restricting either core's owner to the other core gives the same cell.
The earlier-frame exclusion is the original fixed one in both expressions. -/
theorem originalMacroFrameOwner_inter_eq (K L : Set V) (j : ℕ) :
    originalMacroFrameOwner q K j ∩ L =
      originalMacroFrameOwner q L j ∩ K := by
  rw [originalMacroFrameOwner_eq, originalMacroFrameOwner_eq]
  ext c
  simp only [mem_inter_iff, Set.mem_sdiff]
  tauto

/-- With the same prescribed frame laws, whole-core scene kernels agree at
every point in the two original cores, including their boundaries. -/
theorem originalIIDWholeCoreSceneKernel_eq_on_inter
    (K L : Set V) (hK : MeasurableSet K) (hL : MeasurableSet L)
    (Q : ℕ → ProbabilityMeasure (Macro × Macro))
    {c : V} (hc : c ∈ K ∩ L) :
    originalIIDWholeCoreSceneKernel K hK Q c =
      originalIIDWholeCoreSceneKernel L hL Q c := by
  have howner : c ∈ ⋃ j, originalMacroFrameOwner q K j := by
    rw [iUnion_originalMacroFrameOwner]
    exact hc.1
  obtain ⟨j, hj⟩ := mem_iUnion.mp howner
  have hjL : c ∈ originalMacroFrameOwner q L j := by
    have hmem : c ∈ originalMacroFrameOwner q K j ∩ L := ⟨hj, hc.2⟩
    rw [originalMacroFrameOwner_inter_eq K L j] at hmem
    exact hmem.1
  rw [originalIIDWholeCoreSceneKernel_eq_on_owner K hK Q j hj,
    originalIIDWholeCoreSceneKernel_eq_on_owner L hL Q j hjL]

/-- Any measured subset of the overlap has the same scene joint measure
under either core presentation. Its original root mass is not rescaled. -/
theorem originalIIDWholeCoreSceneJoint_restrict_eq_of_subset_inter
    (K L : Set V) (hK : MeasurableSet K) (hL : MeasurableSet L)
    (Q : ℕ → ProbabilityMeasure (Macro × Macro))
    {A : Set V} (hA : MeasurableSet A) (hAK : A ⊆ K) (hAL : A ⊆ L) :
    (originalIIDWholeCoreSceneJoint K hK Q).restrict (A ×ˢ univ) =
      (originalIIDWholeCoreSceneJoint L hL Q).restrict (A ×ˢ univ) := by
  have hleft : (originalIIDWholeCoreSceneJoint K hK Q).restrict (A ×ˢ univ) =
      (volume : Measure V).restrict A ⊗ₘ originalIIDWholeCoreSceneKernel K hK Q := by
    rw [originalIIDWholeCoreSceneJoint, ← measure_restrict_compProd_left _ _ hA,
      Measure.restrict_restrict_of_subset hAK]
  have hright : (originalIIDWholeCoreSceneJoint L hL Q).restrict (A ×ˢ univ) =
      (volume : Measure V).restrict A ⊗ₘ originalIIDWholeCoreSceneKernel L hL Q := by
    rw [originalIIDWholeCoreSceneJoint, ← measure_restrict_compProd_left _ _ hA,
      Measure.restrict_restrict_of_subset hAL]
  rw [hleft, hright]
  apply Measure.compProd_congr
  filter_upwards [ae_restrict_mem hA] with c hc
  exact originalIIDWholeCoreSceneKernel_eq_on_inter K L hK hL Q ⟨hAK hc, hAL hc⟩

/-- The two actual whole-core joint laws coincide on the complete overlap. -/
theorem originalIIDWholeCoreSceneJoint_restrict_inter_eq
    (K L : Set V) (hK : MeasurableSet K) (hL : MeasurableSet L)
    (Q : ℕ → ProbabilityMeasure (Macro × Macro)) :
    (originalIIDWholeCoreSceneJoint K hK Q).restrict ((K ∩ L) ×ˢ univ) =
      (originalIIDWholeCoreSceneJoint L hL Q).restrict ((K ∩ L) ×ˢ univ) :=
  originalIIDWholeCoreSceneJoint_restrict_eq_of_subset_inter K L hK hL Q
    (hK.inter hL) inter_subset_left inter_subset_right

/-- An arbitrary whole conditional-scene property transfers across the same
candidate on any measured overlap subset; no measurability of the property
or boundary-null condition is required. -/
theorem ae_originalIIDWholeCoreSceneKernel_iff_of_subset_inter
    (K L : Set V) (hK : MeasurableSet K) (hL : MeasurableSet L)
    (Q : ℕ → ProbabilityMeasure (Macro × Macro))
    {A : Set V} (hA : MeasurableSet A) (hAK : A ⊆ K) (hAL : A ⊆ L)
    (P : V → Measure Scene → Prop) :
    (∀ᵐ c ∂(volume : Measure V).restrict A,
      P c (originalIIDWholeCoreSceneKernel K hK Q c)) ↔
    (∀ᵐ c ∂(volume : Measure V).restrict A,
      P c (originalIIDWholeCoreSceneKernel L hL Q c)) := by
  have heq : ∀ᵐ c ∂(volume : Measure V).restrict A,
      originalIIDWholeCoreSceneKernel K hK Q c =
        originalIIDWholeCoreSceneKernel L hL Q c := by
    filter_upwards [ae_restrict_mem hA] with c hc
    exact originalIIDWholeCoreSceneKernel_eq_on_inter K L hK hL Q ⟨hAK hc, hAL hc⟩
  constructor
  · intro hP
    filter_upwards [hP, heq] with c hc he
    rwa [← he]
  · intro hP
    filter_upwards [hP, heq] with c hc he
    rwa [he]

end OTSelector.Reconstruction
