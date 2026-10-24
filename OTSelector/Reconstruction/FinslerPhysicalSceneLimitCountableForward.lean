import OTSelector.Reconstruction.FinslerPhysicalSceneRootedCountable

/-!
# Actual forward countable-target scene limits

Original feasible allocations construct a common weak subsequence retaining
both source-restricted plans and their same original integer target array.
The actual original global energy makes both resulting plans forward in the
physical clock. Their target carrier is the same countable occupied-site set
of the integer cloud kept in that weak law.
-/

open Set Function Filter MeasureTheory ProbabilityTheory OTSelector.Probability
open scoped Topology ENNReal

noncomputable section
namespace OTSelector.Reconstruction

open PointProcess PointProcess.LocalConfiguration

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {ι M : Type*} [Fintype ι] [MeasurableSpace M]
  [MetricSpace M] [BorelSpace M] [SecondCountableTopology M]
variable (base : (ι → ℝ) × ℝ)

local instance : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

set_option maxHeartbeats 800000 in
/-- The actual original allocation data produce one weak scene with a common
countable target carrier and forward physical clock for both limiting plans. -/
theorem exists_actualAllocationRootedCountableScene_forward_limit
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
    (D : ℕ → Set (ι → ℝ)) (hD : ∀ k, volume (D k) = ENNReal.ofReal ((m k : ℝ) + 1))
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (henergyplus : ∀ k, (∫⁻ w, ∫⁻ e, ENNReal.ofReal
      (scale k * (dist e.1 (Y k w e.2) - u (Y k w e.2) + u e.1))
        ∂semidiscreteAllocationMeasure μ (aplus k w) ∂P k) ≤ C)
    (henergyminus : ∀ k, (∫⁻ w, ∫⁻ e, ENNReal.ofReal
      (scale k * (dist e.1 (Y k w e.2) - u (Y k w e.2) + u e.1))
        ∂semidiscreteAllocationMeasure μ (aminus k w) ∂P k) ≤ C)
    : ∃ Q : ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k ↦ actualAllocationRootedCountableSceneLaw base (P (φ k)) μ
        (aplus (φ k)) (aminus (φ k)) (hplus (φ k)) (hminus (φ k))
        (Y (φ k)) (hY (φ k)) (H (φ k)) (hH (φ k)) (coord (φ k)) (hcoord (φ k))
        u hu.continuous.measurable (D (φ k)) (hD (φ k))) atTop (𝓝 Q) ∧
      ∀ᵐ s ∂(Q : Measure
        (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)),
        (support (LocalConfiguration.multiplicity s.2)).Countable ∧
        (∀ᵐ e ∂(s.1.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))),
          e.2 ∈ support (LocalConfiguration.multiplicity s.2) ∧ e.1.2 < e.2.2) ∧
        (∀ᵐ e ∂(s.1.2 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))),
          e.2 ∈ support (LocalConfiguration.multiplicity s.2) ∧ e.1.2 < e.2.2) := by
  obtain ⟨Q, φ, hφ, hweak, hsupported⟩ :=
    exists_tendsto_subseq_actualAllocationRootedCountableSceneLaw base m P μ
      aplus aminus hplus hminus Y hY p hfeasplus hfeasminus
      H hH coord hcoord u hu.continuous.measurable D hD
  let Qpair := Q.map (f := Prod.fst) measurable_fst.aemeasurable
  have hweakpair : Tendsto (fun k ↦ actualAllocationRootedSceneLaw (P (φ k)) μ
      (aplus (φ k)) (aminus (φ k)) (hplus (φ k)) (hminus (φ k))
      (Y (φ k)) (hY (φ k)) (H (φ k)) (hH (φ k)) (coord (φ k)) (hcoord (φ k))
      u hu.continuous.measurable ((m (φ k) : ℝ) + 1) (by positivity)
      (D (φ k)) (hD (φ k))) atTop (𝓝 Qpair) := by
    have hw := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun k ↦ actualAllocationRootedCountableSceneLaw base (P (φ k)) μ
        (aplus (φ k)) (aminus (φ k)) (hplus (φ k)) (hminus (φ k))
        (Y (φ k)) (hY (φ k)) (H (φ k)) (hH (φ k)) (coord (φ k)) (hcoord (φ k))
        u hu.continuous.measurable (D (φ k)) (hD (φ k))) Q hweak continuous_fst
    simpa only [map_actualAllocationRootedCountableSceneLaw_pair] using hw
  have hlegal := ae_actualAllocationRootedScene_limit_forward
    (fun k ↦ m (φ k)) (fun k ↦ P (φ k)) μ ν hA hB hAB hμA hνB
    (fun k ↦ aplus (φ k)) (fun k ↦ aminus (φ k))
    (fun k ↦ hplus (φ k)) (fun k ↦ hminus (φ k))
    (fun k ↦ Y (φ k)) (fun k ↦ hY (φ k)) (fun k ↦ hYlaw (φ k))
    (fun k ↦ p (φ k)) (fun k ↦ hfeasplus (φ k)) (fun k ↦ hfeasminus (φ k))
    (fun k ↦ H (φ k)) (fun k ↦ hH (φ k))
    (fun k ↦ coord (φ k)) (fun k ↦ hcoord (φ k)) hu
    (fun k ↦ scale (φ k)) (fun k ↦ hscale (φ k)) (hscaleTop.comp hφ.tendsto_atTop)
    (fun k ↦ (m (φ k) : ℝ) + 1) (fun _ ↦ by positivity)
    (fun k ↦ D (φ k)) (fun k ↦ hD (φ k)) C hC
    (fun k ↦ henergyplus (φ k)) (fun k ↦ henergyminus (φ k)) Qpair hweakpair
  have hlift : ∀ᵐ s ∂(Q : Measure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)),
      (∀ᵐ e ∂(s.1.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))), e.1.2 < e.2.2) ∧
      (∀ᵐ e ∂(s.1.2 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))), e.1.2 < e.2.2) :=
    ae_of_ae_map (μ := (Q : Measure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)))
      (f := Prod.fst)
      (p := fun s : CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) ↦
        (∀ᵐ e ∂(s.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))), e.1.2 < e.2.2) ∧
        (∀ᵐ e ∂(s.2 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))), e.1.2 < e.2.2))
      measurable_fst.aemeasurable hlegal
  refine ⟨Q, φ, hφ, hweak, ?_⟩
  filter_upwards [hsupported, hlift] with s hs hl
  exact ⟨countable_multiplicity_support s.2,
    ((supportedOverConfiguration_iff_ae_mem Prod.snd continuous_snd _ _).mp hs.1).and hl.1,
    ((supportedOverConfiguration_iff_ae_mem Prod.snd continuous_snd _ _).mp hs.2).and hl.2⟩

end OTSelector.Reconstruction
