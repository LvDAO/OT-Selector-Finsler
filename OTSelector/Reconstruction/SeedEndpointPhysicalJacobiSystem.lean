import OTSelector.Reconstruction.SeedEndpointJacobiDensity
import OTSelector.Reconstruction.HamiltonianPhysicalClockSystem

/-! Keep the selected endpoint chart and its Jacobi matrix in original physical
time, instead of replacing them by unrelated endpoint witnesses. -/
open Set Matrix Module Manifold
open scoped Topology ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.SeedEndpointChart
open OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [Fintype ι] [DecidableEq ι]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {S : CalibratedLevelSeedPatch F u}
  {initial : M} {t₀ : ℝ} {w : S.covector.ker} {z₀ : E × (E →L[ℝ] ℝ)}
  {R : S.covector.ker →L[ℝ] E} {Q : S.covector.ker →L[ℝ] E →L[ℝ] ℝ}
  {C : F.SmoothPhaseJetComparison initial t₀ w z₀ R Q} {endpoint : ℝ}

omit [BorelSpace E] [DecidableEq ι] in
/-- The fixed selected endpoint chart produces its actual physical-time closed
system and continuous original clock speed, including the physical endpoints. -/
theorem physical_clock_system (G : SeedEndpointChart S C endpoint)
    (hF : F.IsSmoothStronglyConvex) (bW : Basis ι ℝ S.covector.ker)
    {l h : ℝ} (hlh : l < h) (hI : ∀ t ∈ Icc l h, (w, t) ∈ G.geometry.U) :
    ContinuousOn G.speed (Icc l h) ∧
      ∃ P A B C : ℝ → Matrix ι ι ℝ,
        ClosedHamiltonianJacobiSystem
          (fun t ↦ G.jacobiPositionMatrix bW (G.clock t)) P A B C l h := by
  have hγ (t : ℝ) (ht : t ∈ Icc l h) :
      DifferentiableAt ℝ G.graphReadout (w, t) :=
    (G.geometry.position_C2.contDiffAt
      (G.geometry.open_U.mem_nhds (hI t ht))).differentiableAt (by norm_num)
  have hclock : ∀ t ∈ Icc l h, HasDerivAt G.clock (G.speed t) t :=
    fun t ht ↦ curveGraphClock_hasDerivAt (hγ t ht)
  have hv : ContinuousOn G.speed (Icc l h) := G.geometry.continuousOn_clockSpeed hI
  have hvpos : ∀ t ∈ Icc l h, 0 < G.speed t :=
    fun t ht ↦ (G.geometry.regular (w, t) (hI t ht)).1
  have himage := (curveGraphClock_closedInverse_data G.geometry.raw.1 hlh.le
    (fun t ht ↦ G.geometry.source_U (hI t ht)) hγ
    (fun t ht ↦ hvpos t (Ioo_subset_Icc_self ht))).1
  change G.clock '' Icc l h = Icc (G.clock l) (G.clock h) at himage
  have hmaps : MapsTo G.clock (Icc l h) (Icc (G.clock l) (G.clock h)) := by
    intro t ht
    rw [← himage]
    exact mem_image_of_mem _ ht
  have Hgraph := G.geometry.closedJacobiSystem hF bW (G.spatialBasis bW)
    (G.geometry.closedGraphInterval_subset_phase hlh.le hI)
  have Hphys := Hgraph.physicalClock hclock hv hvpos hmaps
  exact ⟨hv, _, _, _, _, Hphys⟩

end OTSelector.Geometry.ContinuousFinslerNorm.SeedEndpointChart
