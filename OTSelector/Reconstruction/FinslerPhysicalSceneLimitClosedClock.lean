import OTSelector.Reconstruction.FinslerPhysicalSceneReadoutLegality

/-!
# Closed physical carriers and the original positive clock gap

Closed edge carriers survive weak convergence of actual diffuse plan laws.
The original source and target support-distance gap is retained explicitly by
the actual global-allocation limit theorem, allowing the same gap to survive a
further weak tilt-index limit.
-/

open TopologicalSpace Set Function Filter MeasureTheory ProbabilityTheory OTSelector.Probability
open scoped Topology ENNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

section ClosedCarrier
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
  [PseudoMetrizableSpace X] [SigmaCompactSpace X]

/-- A closed edge carrier is a closed constraint on actual diffuse vague plans. -/
theorem isClosed_localFiniteMeasure_carried {K : Set X} (hK : IsClosed K) :
    IsClosed {μ : LocalFiniteMeasure X | ∀ᵐ x ∂(μ : Measure X), x ∈ K} := by
  have heq : {μ : LocalFiniteMeasure X | ∀ᵐ x ∂(μ : Measure X), x ∈ K} =
      {μ : LocalFiniteMeasure X | (μ : Measure X) Kᶜ ≤ 0} := by
    ext μ
    change (∀ᵐ x ∂(μ : Measure X), x ∈ K) ↔ (μ : Measure X) Kᶜ ≤ 0
    rw [ae_iff]
    change (μ : Measure X) Kᶜ = 0 ↔ (μ : Measure X) Kᶜ ≤ 0
    exact ⟨fun h ↦ h.le, fun h ↦ le_antisymm h bot_le⟩
  rw [heq]
  exact (LocalFiniteMeasure.lowerSemicontinuous_measure_open hK.isOpen_compl).isClosed_preimage 0

/-- Weak limits of the same scene laws retain a fixed closed physical edge
carrier under any continuous observation of the actual plan. -/
theorem ae_localFiniteMeasure_carried_of_weak_tendsto
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
    (P : ProbabilityMeasure Ω) (Pn : ℕ → ProbabilityMeasure Ω)
    (hweak : Tendsto Pn atTop (𝓝 P))
    (f : Ω → LocalFiniteMeasure X) (hf : Continuous f)
    {K : Set X} (hK : IsClosed K)
    (hcarried : ∀ n, ∀ᵐ w ∂(Pn n : Measure Ω), ∀ᵐ x ∂(f w : Measure X), x ∈ K) :
    ∀ᵐ w ∂(P : Measure Ω), ∀ᵐ x ∂(f w : Measure X), x ∈ K := by
  let Good : Set Ω := {w | ∀ᵐ x ∂(f w : Measure X), x ∈ K}
  have hGood : IsClosed Good := isClosed_localFiniteMeasure_carried hK |>.preimage hf
  have hn : ∀ n, (Pn n : Measure Ω) Goodᶜ = 0 := fun n ↦ hcarried n
  have hb := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak hGood.isOpen_compl
  change (P : Measure Ω) Goodᶜ ≤ atTop.liminf (fun n ↦ (Pn n : Measure Ω) Goodᶜ) at hb
  simp only [hn, liminf_const] at hb
  exact le_antisymm hb bot_le

end ClosedCarrier


section ActualClockGap
variable {ι M : Type*} [Fintype ι] [MeasurableSpace M]
  [MetricSpace M] [BorelSpace M] [SecondCountableTopology M]

local instance physicalSceneClosedClockPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

/-- The same original allocation energy retains the explicit positive original
support gap, which is closed and therefore survives a further weak limit. -/
theorem ae_actualAllocationRootedScene_limit_clock_gap
    {Ωn : ℕ → Type*} [∀ k, MeasurableSpace (Ωn k)]
    (m : ℕ → ℕ) (P : ∀ k, Measure (Ωn k)) [∀ k, IsProbabilityMeasure (P k)]
    (μ ν : Measure M) [IsFiniteMeasure μ]
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    {gap : ℝ} (hgap : 0 < gap) (hdist : ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
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
      (∀ᵐ e ∂(scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))), gap / 2 ≤ e.2.2 - e.1.2) ∧
      (∀ᵐ e ∂(scene.2 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))), gap / 2 ≤ e.2.2 - e.1.2) := by
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
  exact hlegal

end ActualClockGap
end OTSelector.Reconstruction
