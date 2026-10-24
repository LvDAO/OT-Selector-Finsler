import OTSelector.Reconstruction.OriginalMinimizerOldRegularTrafficFullWindow
import OTSelector.Reconstruction.OriginalMinimizerOldRegularTrafficSummation
import OTSelector.MeasureTheory.Lp.FiniteWindowENNRealReadout

/-! Full original old-focal traffic sums on a single shrinking collar.
Real dyadic summation and the finite physical cover retain the exact original
nonnegative traffic and establish finiteness before its real readout. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Topology Matrix.Norms.Operator Classical BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M→ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
local notation "qdim" => finrank ℝ S.covector.ker

/-- The actual complete left old-focal ENNReal traffic is AE finite and
its exact real readout is L2 on every smaller collar of the original minimizer. -/
theorem exists_original_left_full_old_traffic_memLp_two_on_collar
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels) (hq : 2≤qdim)
    {density : M→ℝ} {v : M→E→ℝ} (c : ℝ≥0∞)
    (hρ : Continuous density) (hρ0 : ∀x,0≤density x)
    (hv : ∀old,ContinuousOn (v old) (extChartAt 𝓘(ℝ,E) old).target)
    (hv0 : ∀old,∀y∈(extChartAt 𝓘(ℝ,E) old).target,0≤v old y)
    (hdensity : PopulationSeedClockDensity S w
      (μ.map (fun x:ℝ↦x-S.level)) density v c.toReal)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter) (hgap : 0<gap)
    {poleη : ℝ} (hη : 0<poleη) (hηspan : poleη<D.hi-D.lo)
    {G : Matrix (Fin qdim) (Fin qdim) ℝ} (hG : G.PosSemidef)
    {Rem : ℝ→Matrix (Fin qdim) (Fin qdim) ℝ}
    (hRem : ContinuousOn Rem (Ioo (-poleη) poleη))
    (hpole : ∀a∈Ioo 0 poleη,originalSeedKernel S w (D.lo+a)=(a^2)⁻¹•G+Rem a)
    {g:ℝ→ℝ→ℝ} {gBound:ℝ} (hg:Measurable (Function.uncurry g))
    (hgb:∀x y,|g x y|≤gBound) (τ:ℝ)
    (Q:LegalWeightedStationaryPoissonMatching qdim μ ν (D.originalFocalKinetic gap) g)
    (hmin:∀P:LegalWeightedStationaryPoissonMatching qdim μ ν (D.originalFocalKinetic gap) g,
      Q.value τ≤P.value τ)
    {η:(Fin qdim→ℝ)→ℝ} (hηmeas:Measurable η) (hηI:Integrable η volume)
    (hη0:∀x,0≤η x) {physicalRadius basecap M₀:ℝ}
    (hphysicalRadius:0≤physicalRadius) (hbasecap:0<basecap)
    (hηR:∀x,physicalRadius<‖x‖→η x=0) (hM:0≤M₀) (hηM:∀x,η x≤M₀) :
    ∃ ε₀ : ℝ,0<ε₀∧ε₀≤1∧∀{ε:ℝ},0<ε→ε<ε₀→
      MemLp (fun scene↦(∑'n:ℕ,D.originalClockPieceAbsoluteTraffic η ε
          (.inl (.inr ((0:Fin 2),n))) scene).toReal) 2
        (Q.law:Measure (LegalMarkedOptimalInputScene qdim))∧
      ∀ᵐscene∂(Q.law:Measure (LegalMarkedOptimalInputScene qdim)),
        (∑'n:ℕ,D.originalClockPieceAbsoluteTraffic η ε (.inl (.inr ((0:Fin 2),n))) scene)≠(∞:ℝ≥0∞) := by
  obtain ⟨h,cap,ε₀,A,Btail,K₀,E₀,_hh,hcap,_hcapbase,hε₀,hε₀1,hA,hBtail,hK₀,hE₀,hlevel⟩:=
    D.exists_original_left_old_fullWindow_level_norm hF hw hq c hρ hρ0 hv hv0 hdensity
      hbounds hgap hη hηspan hG hRem hpole hg hgb τ Q hmin hηmeas hηI hη0
      hphysicalRadius hbasecap hηR hM hηM
  refine ⟨ε₀,hε₀,hε₀1,?_⟩
  intro ε hε hεsmall
  let P:Measure (LegalMarkedOptimalInputScene qdim):=Q.law
  let window:=fun (ell:Fin (birthPhysicalClockWindowCount cap)) (n:ℕ) (_:Unit)
      (scene:LegalMarkedOptimalInputScene qdim)↦D.originalOldWindowAbsoluteTraffic η ε cap 0 n ell scene
  let level:=fun (ell:Fin (birthPhysicalClockWindowCount cap)) (n:ℕ)
      (scene:LegalMarkedOptimalInputScene qdim)↦(window ell n () scene).toReal
  have hfinite:∀ell n idx,∀ᵐscene∂P,window ell n idx scene≠(∞:ℝ≥0∞):=by
    intro ell n _unit
    filter_upwards [D.ae_original_completePathAbsoluteTraffic_lt_top hF hw hbounds Q hηmeas hηI]
      with scene hs
    apply ne_top_of_le_ne_top hs.ne
    apply legalMarkedCompletePathTraffic_mono_weights
    intro z
    change ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖*
      D.originalSupportedOldPhysicalClockMask ε cap 0 n ell z≤_
    calc
      _≤ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖*1:=by
        gcongr
        exact D.originalSupportedOldPhysicalClockMask_le_one hε cap 0 n ell z
      _=_:=mul_one _
  have hseries:∀ell:Fin (birthPhysicalClockWindowCount cap),
      MemLp (fun scene↦∑'n,level ell n scene) 2 P∧
        Summable (fun n↦(eLpNorm (level ell n) 2 P).toReal)∧
        ∀ᵐscene∂P,Summable (fun n↦‖level ell n scene‖):=by
    intro ell
    apply memLp_original_old_single_tsum_of_level_norm_bounds P hK₀
      (show 0<(qdim:ℝ) by exact_mod_cast (show 0<qdim by omega)) hε
      (show 0≤E₀ by linarith) hA hBtail (level ell)
    · intro n
      exact (hlevel hε hεsmall n ell ell.isLt le_rfl).1
    · intro n K hK
      exact (hlevel hε hεsmall n ell ell.isLt hK).2
  have hread:=memLp_finite_window_ennreal_traffic_readout P (fun _n:ℕ↦({()}:Finset Unit))
    window hfinite
    (fun ell↦by simpa only [Finset.sum_singleton] using (hseries ell).1)
    (fun ell↦by simpa only [Finset.sum_singleton] using (hseries ell).2.2)
  have heq(scene:LegalMarkedOptimalInputScene qdim):
      (∑ell:Fin (birthPhysicalClockWindowCount cap),∑'n:ℕ,∑idx∈({()}:Finset Unit),
        window ell n idx scene)=
      ∑'n:ℕ,D.originalClockPieceAbsoluteTraffic η ε (.inl (.inr ((0:Fin 2),n))) scene:=by
    simp only [Finset.sum_singleton]
    calc
      _=(∑'ell:Fin (birthPhysicalClockWindowCount cap),∑'n:ℕ,window ell n () scene):=by rw [tsum_fintype]
      _=(∑'n:ℕ,∑'ell:Fin (birthPhysicalClockWindowCount cap),window ell n () scene):=ENNReal.tsum_comm
      _=_:=by
        apply tsum_congr
        intro n
        rw [tsum_fintype]
        exact D.sum_originalOldWindowAbsoluteTraffic hF hw hηmeas hε hcap 0 n scene
  exact ⟨by simpa only [heq] using hread.1,
    hread.2.mono (fun scene hs↦by simpa only [heq] using hs)⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
