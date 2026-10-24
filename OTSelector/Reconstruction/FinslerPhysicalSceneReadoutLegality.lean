import OTSelector.Reconstruction.FinslerPhysicalSceneRootedGlobal
import OTSelector.Reconstruction.FinslerPhysicalSceneLimitClock

/-!
# Forward legality of limits of the actual global allocation scene

Original measurable allocation coefficients and sampled physical targets
construct the source-restricted rooted laws.  Almost-sure original feasibility,
the original target marginal law and the original allocation energy discharge
the corresponding physical-plan hypotheses.  Compact disjoint original
supports then make both limiting plans forward in the actual potential clock.
-/

open Set Function Filter MeasureTheory ProbabilityTheory OTSelector.Probability
open scoped Topology ENNReal

noncomputable section
namespace OTSelector.Reconstruction

variable {ι M Ω : Type*} [Fintype ι] [MeasurableSpace M] [MeasurableSpace Ω] {n : ℕ}

local instance physicalSceneReadoutLegalityLocalInst : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

/-- The actual two-sign global allocation scene on its original environment,
source cell and spatial root; its realized local columns are retained. -/
def actualAllocationRootedSceneLaw
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure M) [IsFiniteMeasure μ]
    (aplus aminus : Ω → M → Fin (n + 1) → ℝ)
    (hplus : ∀ j, Measurable (fun z : Ω × M ↦ aplus z.1 z.2 j))
    (hminus : ∀ j, Measurable (fun z : Ω × M ↦ aminus z.1 z.2 j))
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j))
    (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u)
    (N : ℝ) (hN : 0 < N) (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal N) :
    ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)) :=
  physicalSceneRestrictedRootedLocalSceneLaw P
    (physicalSceneGlobalAllocationFamily μ aplus Y)
    (physicalSceneGlobalAllocationFamily μ aminus Y)
    (measurable_physicalSceneGlobalAllocationFamily μ aplus hplus Y hY)
    (measurable_physicalSceneGlobalAllocationFamily μ aminus hminus Y hY)
    H hH coord hcoord u hu N hN D hD

section Limit

variable [MetricSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- The two actual source-restricted global allocation scenes have forward
clock limits.  The target sampling law and global allocation energy remain
the original ones; no law is prescribed for the local column masses. -/
theorem ae_actualAllocationRootedScene_limit_forward
    {Ωn : ℕ → Type*} [∀ k, MeasurableSpace (Ωn k)]
    (m : ℕ → ℕ) (P : ∀ k, Measure (Ωn k)) [∀ k, IsProbabilityMeasure (P k)]
    (μ ν : Measure M) [IsFiniteMeasure μ]
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ y ∂ν, y ∈ B)
    (aplus aminus : ∀ k, Ωn k → M → Fin (m k + 1) → ℝ)
    (hplus : ∀ k j, Measurable (fun z : Ωn k × M ↦ aplus k z.1 z.2 j))
    (hminus : ∀ k j, Measurable (fun z : Ωn k × M ↦ aminus k z.1 z.2 j))
    (Y : ∀ k, Ωn k → Fin (m k + 1) → M)
    (hY : ∀ k j, Measurable (fun w ↦ Y k w j))
    (hYlaw : ∀ k j, (P k).map (fun w ↦ Y k w j) = ν)
    (p : ∀ k, Ωn k → Fin (m k + 1) → ℝ)
    (hfeasplus : ∀ k, ∀ᵐ w ∂P k, IsSemidiscreteAllocation μ (p k w) (aplus k w))
    (hfeasminus : ∀ k, ∀ᵐ w ∂P k, IsSemidiscreteAllocation μ (p k w) (aminus k w))
    (H : ℕ → Set M) (hH : ∀ k, MeasurableSet (H k))
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ k, Measurable (coord k))
    {u : M → ℝ} (hu : LipschitzWith 1 u)
    (scale : ℕ → ℝ) (hscale : ∀ k, 0 < scale k)
    (hscaleTop : Tendsto scale atTop atTop)
    (N : ℕ → ℝ) (hN : ∀ k, 0 < N k)
    (D : ℕ → Set (ι → ℝ)) (hD : ∀ k, volume (D k) = ENNReal.ofReal (N k))
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (henergyplus : ∀ k, (∫⁻ w, ∫⁻ e, ENNReal.ofReal
      (scale k * (dist e.1 (Y k w e.2) - u (Y k w e.2) + u e.1))
        ∂semidiscreteAllocationMeasure μ (aplus k w) ∂P k) ≤ C)
    (henergyminus : ∀ k, (∫⁻ w, ∫⁻ e, ENNReal.ofReal
      (scale k * (dist e.1 (Y k w e.2) - u (Y k w e.2) + u e.1))
        ∂semidiscreteAllocationMeasure μ (aminus k w) ∂P k) ≤ C)
    (Q : ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    (hweak : Tendsto (fun k ↦ actualAllocationRootedSceneLaw (P k) μ (aplus k) (aminus k)
      (hplus k) (hminus k) (Y k) (hY k) (H k) (hH k) (coord k) (hcoord k)
      u hu.continuous.measurable (N k) (hN k) (D k) (hD k)) atTop (𝓝 Q)) :
    ∀ᵐ scene ∂(Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))),
      (∀ᵐ e ∂(scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))), e.1.2 < e.2.2) ∧
      (∀ᵐ e ∂(scene.2 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))), e.1.2 < e.2.2) := by
  obtain ⟨gap, hgap, hdist⟩ := exists_original_support_gap hA hB hAB
  let Γplus := fun k ↦ physicalSceneGlobalAllocationFamily μ (aplus k) (Y k)
  let Γminus := fun k ↦ physicalSceneGlobalAllocationFamily μ (aminus k) (Y k)
  have hYB (k : ℕ) : ∀ᵐ w ∂P k, ∀ j, Y k w j ∈ B := by
    apply ae_all_iff.mpr
    intro j
    apply ae_of_ae_map (p := fun y ↦ y ∈ B) (hY k j).aemeasurable
    simpa only [hYlaw k j] using hνB
  have hcarriedplus (k : ℕ) : ∀ᵐ w ∂P k, ∀ᵐ e ∂Γplus k w,
      e.1 ∈ A ∧ e.2 ∈ B :=
    ae_physicalSceneGlobalAllocationFamily_carried (P k) μ (aplus k) (Y k) (p k)
      (hfeasplus k) hA.measurableSet hB.measurableSet hμA (hYB k)
  have hcarriedminus (k : ℕ) : ∀ᵐ w ∂P k, ∀ᵐ e ∂Γminus k w,
      e.1 ∈ A ∧ e.2 ∈ B :=
    ae_physicalSceneGlobalAllocationFamily_carried (P k) μ (aminus k) (Y k) (p k)
      (hfeasminus k) hA.measurableSet hB.measurableSet hμA (hYB k)
  let energy := fun k (e : M × M) ↦
    ENNReal.ofReal (scale k * (dist e.1 e.2 - u e.2 + u e.1))
  have hem (k : ℕ) : Measurable (energy k) :=
    ((((continuous_fst.dist continuous_snd).sub (hu.continuous.comp continuous_snd)).add
      (hu.continuous.comp continuous_fst)).const_mul (scale k)).measurable.ennreal_ofReal
  have hep (k : ℕ) : (∫⁻ w, ∫⁻ e, energy k e ∂Γplus k w ∂P k) ≤ C := by
    rw [lintegral_physicalSceneGlobalAllocationFamily_eq (P k) μ (aplus k) (Y k) (p k)
      (hfeasplus k) (fun _ ↦ energy k) (fun _ ↦ hem k)]
    exact henergyplus k
  have hem' (k : ℕ) : (∫⁻ w, ∫⁻ e, energy k e ∂Γminus k w ∂P k) ≤ C := by
    rw [lintegral_physicalSceneGlobalAllocationFamily_eq (P k) μ (aminus k) (Y k) (p k)
      (hfeasminus k) (fun _ ↦ energy k) (fun _ ↦ hem k)]
    exact henergyminus k
  have hlegal := ae_physicalSceneRootedLocalScene_limit_clock_legal P Γplus Γminus
    (fun k ↦ measurable_physicalSceneGlobalAllocationFamily μ (aplus k) (hplus k) (Y k) (hY k))
    (fun k ↦ measurable_physicalSceneGlobalAllocationFamily μ (aminus k) (hminus k) (Y k) (hY k))
    hgap hdist hcarriedplus hcarriedminus H hH coord hcoord hu scale hscale hscaleTop
    N hN D hD C hC hep hem' Q hweak
  filter_upwards [hlegal] with scene hs
  constructor
  · exact hs.1.mono fun e he ↦ by linarith [half_pos hgap]
  · exact hs.2.mono fun e he ↦ by linarith [half_pos hgap]

end Limit
end OTSelector.Reconstruction
