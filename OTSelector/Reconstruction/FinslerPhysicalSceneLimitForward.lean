import OTSelector.Reconstruction.FinslerPhysicalSceneRootedSubsequence

/-!
# Forward actual allocation limits without a convergence premise

The original allocation data construct a common weak subsequence of the actual
source-restricted rooted laws. Original global energy and compact disjoint
physical supports then make both plans of this produced limit forward in the
same physical potential clock.
-/

open Set Function Filter MeasureTheory ProbabilityTheory OTSelector.Probability
open scoped Topology ENNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {ι M : Type*} [Fintype ι] [MeasurableSpace M]
  [MetricSpace M] [BorelSpace M] [SecondCountableTopology M]

local instance : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

/-- Original global allocation energy constructs an actual forward weak limit;
weak convergence is produced from the same allocations and original root. -/
theorem exists_actualAllocationRootedScene_forward_limit
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
    : ∃ Q : ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k ↦ actualAllocationRootedSceneLaw (P (φ k)) μ
        (aplus (φ k)) (aminus (φ k)) (hplus (φ k)) (hminus (φ k))
        (Y (φ k)) (hY (φ k)) (H (φ k)) (hH (φ k)) (coord (φ k)) (hcoord (φ k))
        u hu.continuous.measurable (N (φ k)) (hN (φ k)) (D (φ k)) (hD (φ k)))
        atTop (𝓝 Q) ∧
      ∀ᵐ scene ∂(Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))),
        (∀ᵐ e ∂(scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))), e.1.2 < e.2.2) ∧
        (∀ᵐ e ∂(scene.2 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))), e.1.2 < e.2.2) := by
  obtain ⟨Q, φ, hφ, hweak⟩ := exists_tendsto_subseq_actualAllocationRootedSceneLaw
    m P μ aplus aminus hplus hminus Y hY p hfeasplus hfeasminus H hH coord hcoord
    u hu.continuous.measurable N hN D hD
  refine ⟨Q, φ, hφ, hweak, ?_⟩
  exact ae_actualAllocationRootedScene_limit_forward
    (fun k ↦ m (φ k)) (fun k ↦ P (φ k)) μ ν hA hB hAB hμA hνB
    (fun k ↦ aplus (φ k)) (fun k ↦ aminus (φ k))
    (fun k ↦ hplus (φ k)) (fun k ↦ hminus (φ k))
    (fun k ↦ Y (φ k)) (fun k ↦ hY (φ k)) (fun k ↦ hYlaw (φ k))
    (fun k ↦ p (φ k)) (fun k ↦ hfeasplus (φ k)) (fun k ↦ hfeasminus (φ k))
    (fun k ↦ H (φ k)) (fun k ↦ hH (φ k))
    (fun k ↦ coord (φ k)) (fun k ↦ hcoord (φ k)) hu
    (fun k ↦ scale (φ k)) (fun k ↦ hscale (φ k)) (hscaleTop.comp hφ.tendsto_atTop)
    (fun k ↦ N (φ k)) (fun k ↦ hN (φ k))
    (fun k ↦ D (φ k)) (fun k ↦ hD (φ k)) C hC
    (fun k ↦ henergyplus (φ k)) (fun k ↦ henergyminus (φ k)) Q hweak

end OTSelector.Reconstruction
