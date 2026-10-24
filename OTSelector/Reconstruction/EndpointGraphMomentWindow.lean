import OTSelector.Reconstruction.EndpointGraphIntrinsicKernel
import OTSelector.Reconstruction.PhysicalJacobiWindowFromClockInverse

/-!+# Moment windows from the selected actual endpoint graph

The actual graph record supplies the closed Hamiltonian system, positive clock and
its inverse, and the exact representation of the intrinsic kernel. Only the original
physical density and interior position regularity remain as inputs to this assembly.
-/

open Set Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.EndpointGraphData

open OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {E W V M ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [Fintype ι] [DecidableEq ι]
  {F : ContinuousFinslerNorm E M} {A : E ≃L[ℝ] (ℝ × V)}
  {Γ : W → ℝ → M} {B : Set W} {w : W} {old : M} {t₀ : ℝ}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ W] [FiniteDimensional ℝ V] in
/-- The original-time speed of the selected actual positive graph clock is continuous. -/
theorem continuousOn_clockSpeed (G : EndpointGraphData F A Γ B w old t₀)
    {I : Set ℝ} (hI : ∀ t ∈ I, (w, t) ∈ G.U) :
    ContinuousOn (fun t ↦ (fderiv ℝ
      (fun q : W × ℝ ↦ A (extChartAt 𝓘(ℝ, E) old (Γ q.1 q.2))) (w, t) (0, 1)).1) I := by
  intro t ht
  have hD := ((G.position_C2.contDiffAt (G.open_U.mem_nhds (hI t ht))).fderiv_right
    (m := 1) (by norm_num)).continuousAt
  exact ((hD.clm_apply continuousAt_const).fst.comp
    (f := fun r : ℝ ↦ (w, r)) (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt

variable {initial : M} {tᵢ : ℝ} {z₀ : E × (E →L[ℝ] ℝ)}
  {R : W →L[ℝ] E} {Q : W →L[ℝ] E →L[ℝ] ℝ}

/-- The selected actual endpoint graph constructs a moment window for the original
intrinsic kernel and physical measure. Closed-system and clock data are all derived. -/
def physicalMomentWindow
    (C : F.SmoothPhaseJetComparison initial tᵢ w z₀ R Q)
    (G : EndpointGraphData F A C.curve C.labels w old t₀)
    (hF : F.IsSmoothStronglyConvex) (bW : Basis ι ℝ W) (bV : Basis ι ℝ V)
    {l h : ℝ} (hlh : l < h) (hI : ∀ t ∈ Icc l h, (w, t) ∈ G.U)
    {μ : Measure ℝ} {ρ weight : ℝ → ℝ} {κ Rρ : ℝ}
    (hρ : Measurable ρ) (hweight : ContinuousOn weight (Icc l h))
    (hρ0 : ∀ t ∈ Ioo l h, 0 ≤ ρ t) (hρR : ∀ t ∈ Ioo l h, ρ t ≤ Rρ)
    (hweight0 : ∀ t ∈ Ioo l h, 0 ≤ weight t) (hκ : 0 ≤ κ) :
    let γ := fun q : W × ℝ ↦ A (extChartAt 𝓘(ℝ, E) old (C.curve q.1 q.2))
    let s := fun t ↦ (γ (w, t)).1
    let v := fun t ↦ (fderiv ℝ γ (w, t) (0, 1)).1
    let Ψ := F.adaptedGraphPhase old A γ G.e
    let J := fun r ↦ vectorFamilyMatrix bV
      (fun j ↦ (fderiv ℝ (fun z ↦ Ψ (z, r)) w (bW j)).1)
    (∀ t ∈ Ioo l h, (J (s t)).det ≠ 0) →
    μ.restrict (Ioo l h) = (volume.restrict (Ioo l h)).withDensity (fun t ↦
      ENNReal.ofReal ((ρ t * weight t) * (|v t| * |(J (s t)).det| * κ))) →
    PhysicalJacobiMomentWindow
      (fun t ↦ (F.familyLabelHessianMatrix bW (fun q ↦ C.curve q.1 q.2) (w, t))⁻¹)
      μ l h := by
  let γ := fun q : W × ℝ ↦ A (extChartAt 𝓘(ℝ, E) old (C.curve q.1 q.2))
  let s := fun t ↦ (γ (w, t)).1
  let v := fun t ↦ (fderiv ℝ γ (w, t) (0, 1)).1
  let Ψ := F.adaptedGraphPhase old A γ G.e
  let J := fun r ↦ vectorFamilyMatrix bV
    (fun j ↦ (fderiv ℝ (fun z ↦ Ψ (z, r)) w (bW j)).1)
  dsimp only
  intro hdet hμ
  have hγ (t : ℝ) (ht : t ∈ Icc l h) : DifferentiableAt ℝ γ (w, t) :=
    (G.position_C2.contDiffAt (G.open_U.mem_nhds (hI t ht))).differentiableAt (by norm_num)
  have hsource (t : ℝ) (ht : t ∈ Icc l h) := G.source_U (hI t ht)
  obtain ⟨_, himage, hτ, hτimage, hτs⟩ := curveGraphClock_closedInverse_data G.raw.1
    hlh.le hsource hγ (fun t ht ↦ (G.regular _ (hI t (Ioo_subset_Icc_self ht))).1)
  have hdetGraph : ∀ r ∈ Ioo (s l) (s h), (J r).det ≠ 0 := by
    intro r hr
    rw [← himage] at hr
    obtain ⟨t, ht, rfl⟩ := hr
    exact hdet t ht
  exact physicalJacobiMomentWindow_of_clockInverse hlh
    (G.closedJacobiSystem hF bW bV (G.closedGraphInterval_subset_phase hlh.le hI))
    hdetGraph (fun t ht ↦ curveGraphClock_hasDerivAt (hγ t (Ioo_subset_Icc_self ht)))
    (curveGraphClock_injOn_leftInverse G.raw.1
      (fun t ht ↦ hsource t (Ioo_subset_Icc_self ht))).1 himage
    (G.continuousOn_clockSpeed (fun t ht ↦ hI t (Ioo_subset_Icc_self ht)))
    hτ hτimage (fun t ht ↦ hτs t (Ioo_subset_Icc_self ht))
    (fun t ht ↦ G.intrinsic_kernel_eq C hF bW bV
      (hI t (Ioo_subset_Icc_self ht)) (hdet t ht))
    hρ hweight hρ0 hρR hweight0 (show 0 < (1 : ℝ) by norm_num) hκ
    (by simpa only [div_one] using hμ)

end OTSelector.Geometry.ContinuousFinslerNorm.EndpointGraphData
