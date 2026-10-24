import OTSelector.MeasureTheory.Lp.ENNRealSeriesReadout
import OTSelector.Reconstruction.OriginalMinimizerFullBirthTraffic
import OTSelector.Reconstruction.OriginalBirthTrafficDoubleSummation

/-! Literal full original birth sums consume the verified physical level
profile. The real countable readout is also identified with the complete
ENNReal traffic sum, including almost sure finiteness. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Topology Matrix.Norms.Operator Classical BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M→ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
local notation "q" => finrank ℝ S.covector.ker

/-- One actual geometric choice works on every smaller birth collar.
The full original double traffic sum retains its L2 and absolute-summability
conclusions while later left/right/old/regular collars are synchronized. -/
theorem exists_original_left_full_birth_dyadic_traffic_on_collar
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) (hq : 0 < q)
    {density : M → ℝ} {v : M → E → ℝ} (c : ℝ≥0∞)
    (hdensityCont : Continuous density) (hdensity0 : ∀ x, 0 ≤ density x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hv0 : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hdensity : PopulationSeedClockDensity S w
      (μ.map (fun x : ℝ ↦ x - S.level)) density v c.toReal)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter) (hgap : 0 < gap)
    {poleη : ℝ} (hη : 0 < poleη) (hηspan : poleη < D.hi - D.lo)
    {G : Matrix (Fin q) (Fin q) ℝ} (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin q) (Fin q) ℝ}
    (hRem : ContinuousOn Rem (Ioo (-poleη) poleη))
    (hpole : ∀ r ∈ Ioo 0 poleη, originalSeedKernel S w (D.lo + r) = (r ^ 2)⁻¹ • G + Rem r)
    {g : ℝ → ℝ → ℝ} {gBound : ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ x y, |g x y| ≤ gBound) (τ : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching q μ ν (D.originalFocalKinetic gap) g)
    (hmin : ∀ P : LegalWeightedStationaryPoissonMatching q μ ν (D.originalFocalKinetic gap) g,
      Q.value τ ≤ P.value τ)
    {η : (Fin q → ℝ) → ℝ} (hηmeas : Measurable η)
    (hη0 : ∀ x, 0 ≤ η x)
    {physicalRadius basecap M₀ : ℝ} (hphysicalRadius : 0 ≤ physicalRadius)
    (hbasecap : 0 < basecap) (hηR : ∀ x, physicalRadius < ‖x‖ → η x = 0)
    (hM : 0 ≤ M₀) (hηM : ∀ x, η x ≤ M₀) :
    ∃cap ε₀:ℝ,0<cap∧cap≤basecap∧0<ε₀∧∀{ε:ℝ},0<ε→ε<ε₀→∀ell:ℕ,ell<birthPhysicalClockWindowCount cap→
      let level:=fun (z:ℕ×ℕ) (scene:LegalMarkedOptimalInputScene q)↦
        ∑i∈Finset.range (dyadicBirthBandCount z.2),
          (legalMarkedCompletePathTraffic q (fun z↦originalSeedPathOffset S w z.2 z.1)
            (fun x↦ENNReal.ofReal (η x))
            (D.originalSupportedLeftBirthPhysicalClockWeight ε cap z.1 z.2 i ell) scene).toReal
      MemLp (fun scene↦∑'z:ℕ×ℕ,level z scene) 2
        (Q.law:Measure (LegalMarkedOptimalInputScene q))∧
      Summable (fun z:ℕ×ℕ↦(eLpNorm (level z) 2
        (Q.law:Measure (LegalMarkedOptimalInputScene q))).toReal)∧
      ∀ᵐscene∂(Q.law:Measure (LegalMarkedOptimalInputScene q)),
        Summable (fun z:ℕ×ℕ↦‖level z scene‖) := by
  obtain ⟨cap,ε₀,A,B,K₀,E₀,hcap,hcapbase,hε₀,hε₀1,hA,hB,hK₀,hE₀,hlevel⟩:=
    D.exists_original_left_full_birth_level_norm hF hw hq
      c hdensityCont hdensity0 hv hv0 hdensity hbounds hgap hη hηspan hG hRem hpole
      hg hgb τ Q hmin hηmeas hη0 hphysicalRadius hbasecap hηR hM hηM
  refine ⟨cap,ε₀,hcap,hcapbase,hε₀,?_⟩
  intro ε hε hεsmall ell hell
  dsimp only
  let level:=fun (z:ℕ×ℕ) (scene:LegalMarkedOptimalInputScene q)↦
    ∑i∈Finset.range (dyadicBirthBandCount z.2),
      (legalMarkedCompletePathTraffic q (fun z↦originalSeedPathOffset S w z.2 z.1)
        (fun x↦ENNReal.ofReal (η x))
        (D.originalSupportedLeftBirthPhysicalClockWeight ε cap z.1 z.2 i ell) scene).toReal
  have hLp:∀z,MemLp (level z) 2 (Q.law:Measure (LegalMarkedOptimalInputScene q)):=by
    intro z
    exact (hlevel hε hεsmall z.1 z.2 ell hell (K:=K₀) le_rfl).1
  apply memLp_original_full_birth_double_tsum_of_level_norm_bounds
    (Q.law:Measure (LegalMarkedOptimalInputScene q)) hK₀
    (show 0<(q:ℝ) by exact_mod_cast hq) hε hE₀ hA hB G.rank level hLp
  intro z K hK
  simpa only [mul_assoc] using (hlevel hε hεsmall z.1 z.2 ell hell hK).2



/-- The literal complete original LEFT birth traffic, with no canonical
amplitude or original count truncation, is L2 across every inward and elapsed
scale. The same Q and one coherent geometric choice produce all branches. -/
theorem exists_original_left_full_birth_dyadic_traffic_memLp_two
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) (hq : 0 < q)
    {density : M → ℝ} {v : M → E → ℝ} (c : ℝ≥0∞)
    (hdensityCont : Continuous density) (hdensity0 : ∀ x, 0 ≤ density x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hv0 : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hdensity : PopulationSeedClockDensity S w
      (μ.map (fun x : ℝ ↦ x - S.level)) density v c.toReal)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter) (hgap : 0 < gap)
    {poleη : ℝ} (hη : 0 < poleη) (hηspan : poleη < D.hi - D.lo)
    {G : Matrix (Fin q) (Fin q) ℝ} (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin q) (Fin q) ℝ}
    (hRem : ContinuousOn Rem (Ioo (-poleη) poleη))
    (hpole : ∀ r ∈ Ioo 0 poleη, originalSeedKernel S w (D.lo + r) = (r ^ 2)⁻¹ • G + Rem r)
    {g : ℝ → ℝ → ℝ} {gBound : ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ x y, |g x y| ≤ gBound) (τ : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching q μ ν (D.originalFocalKinetic gap) g)
    (hmin : ∀ P : LegalWeightedStationaryPoissonMatching q μ ν (D.originalFocalKinetic gap) g,
      Q.value τ ≤ P.value τ)
    {η : (Fin q → ℝ) → ℝ} (hηmeas : Measurable η)
    (hη0 : ∀ x, 0 ≤ η x)
    {physicalRadius basecap M₀ : ℝ} (hphysicalRadius : 0 ≤ physicalRadius)
    (hbasecap : 0 < basecap) (hηR : ∀ x, physicalRadius < ‖x‖ → η x = 0)
    (hM : 0 ≤ M₀) (hηM : ∀ x, η x ≤ M₀) :
    ∃cap ε:ℝ,0<cap∧cap≤basecap∧0<ε∧∀ell:ℕ,ell<birthPhysicalClockWindowCount cap→
      let level:=fun (z:ℕ×ℕ) (scene:LegalMarkedOptimalInputScene q)↦
        ∑i∈Finset.range (dyadicBirthBandCount z.2),
          (legalMarkedCompletePathTraffic q (fun z↦originalSeedPathOffset S w z.2 z.1)
            (fun x↦ENNReal.ofReal (η x))
            (D.originalSupportedLeftBirthPhysicalClockWeight ε cap z.1 z.2 i ell) scene).toReal
      MemLp (fun scene↦∑'z:ℕ×ℕ,level z scene) 2
        (Q.law:Measure (LegalMarkedOptimalInputScene q))∧
      Summable (fun z:ℕ×ℕ↦(eLpNorm (level z) 2
        (Q.law:Measure (LegalMarkedOptimalInputScene q))).toReal)∧
      ∀ᵐscene∂(Q.law:Measure (LegalMarkedOptimalInputScene q)),
        Summable (fun z:ℕ×ℕ↦‖level z scene‖) := by
  obtain ⟨cap,ε₀,hcap,hcapbase,hε₀,hall⟩:=
    D.exists_original_left_full_birth_dyadic_traffic_on_collar hF hw hq
      c hdensityCont hdensity0 hv hv0 hdensity hbounds hgap hη hηspan hG hRem hpole
      hg hgb τ Q hmin hηmeas hη0 hphysicalRadius hbasecap hηR hM hηM
  refine ⟨cap,ε₀/2,hcap,hcapbase,(by positivity),?_⟩
  exact hall (by positivity) (by linarith)

/-- Every original supported birth-window occupation is almost surely finite
from its true Palm first moment. This precedes real readout and rules out
hiding an infinite occupation behind ENNReal.toReal. -/
theorem ae_original_left_birthWindowTraffic_lt_top
    (hF:F.IsSmoothStronglyConvex) (hw:w∈S.labels)
    {gap diameter:ℝ} (hbounds:ConditionalClockSupportBounds μ ν gap diameter)
    {g:ℝ→ℝ→ℝ} (Q:LegalWeightedStationaryPoissonMatching q μ ν (D.originalFocalKinetic gap) g)
    {η:(Fin q→ℝ)→ℝ} (hηmeas:Measurable η)
    {R₀ M₀:ℝ} (_hM:0≤M₀) (hηM:∀x,η x≤M₀) (hηR:∀x,R₀<‖x‖→η x=0)
    (ε cap:ℝ) (n j i ell:ℕ) :
    ∀ᵐscene∂(Q.law:Measure (LegalMarkedOptimalInputScene q)),
      legalMarkedCompletePathTraffic q (fun z↦originalSeedPathOffset S w z.2 z.1)
        (fun x↦ENNReal.ofReal (η x))
        (D.originalSupportedLeftBirthPhysicalClockWeight ε cap n j i ell) scene<(∞:ℝ≥0∞):=by
  have hηENN:Measurable (fun x↦ENNReal.ofReal (η x)):=hηmeas.ennreal_ofReal
  have hspace:(∫⁻x,ENNReal.ofReal (η x)∂(volume:Measure (Fin q→ℝ)))≠(∞:ℝ≥0∞):=by
    have hsupport:Function.support (fun x↦ENNReal.ofReal (η x))⊆Metric.closedBall (0:Fin q→ℝ) R₀:=by
      intro x hx
      have hb:‖x‖≤R₀:=le_of_not_gt (fun hn↦hx (by change ENNReal.ofReal (η x)=0;rw [hηR x hn,ENNReal.ofReal_zero]))
      simpa only [Metric.mem_closedBall,dist_zero_right] using hb
    rw [←setLIntegral_eq_of_support_subset hsupport]
    apply ne_top_of_le_ne_top (b:=ENNReal.ofReal M₀*volume (Metric.closedBall (0:Fin q→ℝ) R₀))
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (isCompact_closedBall _ _).measure_ne_top
    · calc
        _≤∫⁻_x in Metric.closedBall (0:Fin q→ℝ) R₀,ENNReal.ofReal M₀:=
          lintegral_mono (fun x↦ENNReal.ofReal_le_ofReal (hηM x))
        _=_:=by simp
  let d:=fun z:PhysicalPairPalmMark (Fin q)×ℝ↦originalSeedPathOffset S w z.2 z.1
  have hd:Measurable d:=measurable_originalSeedPathOffset_joint S hF hw
  have hf:=D.measurable_originalSupportedLeftBirthPhysicalClockWeight hF hw ε cap n j i ell
  have htraffic:=measurable_legalMarkedCompletePathTraffic d hd hηENN hf
  apply ae_lt_top htraffic
  rw [Q.lintegral_completePathTraffic d hd hηENN hf]
  exact ENNReal.mul_ne_top hspace
    (D.original_left_supportedBirthWindow_palm_lt_top hF hw hbounds Q ε cap n j i ell).ne

/-- Every smaller collar retains the finite actual original ENNReal
birth occupation and its L2 real readout, with the same physical subdivision. -/
theorem exists_original_left_full_birth_ennreal_traffic_on_collar
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) (hq : 0 < q)
    {density : M → ℝ} {v : M → E → ℝ} (c : ℝ≥0∞)
    (hdensityCont : Continuous density) (hdensity0 : ∀ x, 0 ≤ density x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hv0 : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hdensity : PopulationSeedClockDensity S w
      (μ.map (fun x : ℝ ↦ x - S.level)) density v c.toReal)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter) (hgap : 0 < gap)
    {poleη : ℝ} (hη : 0 < poleη) (hηspan : poleη < D.hi - D.lo)
    {G : Matrix (Fin q) (Fin q) ℝ} (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin q) (Fin q) ℝ}
    (hRem : ContinuousOn Rem (Ioo (-poleη) poleη))
    (hpole : ∀ r ∈ Ioo 0 poleη, originalSeedKernel S w (D.lo + r) = (r ^ 2)⁻¹ • G + Rem r)
    {g : ℝ → ℝ → ℝ} {gBound : ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ x y, |g x y| ≤ gBound) (τ : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching q μ ν (D.originalFocalKinetic gap) g)
    (hmin : ∀ P : LegalWeightedStationaryPoissonMatching q μ ν (D.originalFocalKinetic gap) g,
      Q.value τ ≤ P.value τ)
    {η : (Fin q → ℝ) → ℝ} (hηmeas : Measurable η)
    (hη0 : ∀ x, 0 ≤ η x)
    {physicalRadius basecap M₀ : ℝ} (hphysicalRadius : 0 ≤ physicalRadius)
    (hbasecap : 0 < basecap) (hηR : ∀ x, physicalRadius < ‖x‖ → η x = 0)
    (hM : 0 ≤ M₀) (hηM : ∀ x, η x ≤ M₀) :
    ∃cap ε₀:ℝ,0<cap∧cap≤basecap∧0<ε₀∧∀{ε:ℝ},0<ε→ε<ε₀→∀ell:ℕ,ell<birthPhysicalClockWindowCount cap→
      let traffic:=fun (z:ℕ×ℕ) (scene:LegalMarkedOptimalInputScene q)↦
        ∑i∈Finset.range (dyadicBirthBandCount z.2),
          legalMarkedCompletePathTraffic q (fun z↦originalSeedPathOffset S w z.2 z.1)
            (fun x↦ENNReal.ofReal (η x))
            (D.originalSupportedLeftBirthPhysicalClockWeight ε cap z.1 z.2 i ell) scene
      MemLp (fun scene↦(∑'z:ℕ×ℕ,traffic z scene).toReal) 2
        (Q.law:Measure (LegalMarkedOptimalInputScene q))∧
      ∀ᵐscene∂(Q.law:Measure (LegalMarkedOptimalInputScene q)),
        (∑'z:ℕ×ℕ,traffic z scene)≠(∞:ℝ≥0∞) := by
  obtain ⟨cap,ε₀,hcap,hcapbase,hε₀,hsum⟩:=
    D.exists_original_left_full_birth_dyadic_traffic_on_collar hF hw hq
      c hdensityCont hdensity0 hv hv0 hdensity hbounds hgap hη hηspan hG hRem hpole
      hg hgb τ Q hmin hηmeas hη0 hphysicalRadius hbasecap hηR hM hηM
  refine ⟨cap,ε₀,hcap,hcapbase,hε₀,?_⟩
  intro ε hε hεsmall ell hell
  dsimp only
  let P:Measure (LegalMarkedOptimalInputScene q):=Q.law
  let window:=fun (z:ℕ×ℕ) (i:ℕ) (scene:LegalMarkedOptimalInputScene q)↦
    legalMarkedCompletePathTraffic q (fun z↦originalSeedPathOffset S w z.2 z.1)
      (fun x↦ENNReal.ofReal (η x))
      (D.originalSupportedLeftBirthPhysicalClockWeight ε cap z.1 z.2 i ell) scene
  let traffic:=fun (z:ℕ×ℕ) (scene:LegalMarkedOptimalInputScene q)↦
    ∑i∈Finset.range (dyadicBirthBandCount z.2),window z i scene
  let level:=fun (z:ℕ×ℕ) (scene:LegalMarkedOptimalInputScene q)↦
    ∑i∈Finset.range (dyadicBirthBandCount z.2),(window z i scene).toReal
  have hwindowFinite:∀z i,∀ᵐscene∂P,window z i scene≠(∞:ℝ≥0∞):=by
    intro z i
    exact (D.ae_original_left_birthWindowTraffic_lt_top hF hw hbounds Q hηmeas hM hηM hηR
      ε cap z.1 z.2 i ell).mono (fun _ hx↦hx.ne)
  have hfinite:∀z,∀ᵐscene∂P,traffic z scene≠(∞:ℝ≥0∞):=by
    intro z
    filter_upwards [ae_all_iff.mpr (hwindowFinite z)] with scene hscene
    exact ENNReal.sum_ne_top.mpr (fun i _↦hscene i)
  have hread:∀ᵐscene∂P,∀z,(traffic z scene).toReal=level z scene:=by
    filter_upwards [ae_all_iff.mpr (fun z↦ae_all_iff.mpr (hwindowFinite z))] with scene hscene
    intro z
    exact ENNReal.toReal_sum (fun i _↦hscene z i)
  have hs:=hsum hε hεsmall ell hell
  have hsreal:∀ᵐscene∂P,Summable (fun z↦(traffic z scene).toReal):=by
    filter_upwards [hs.2.2,hread] with scene hs hscene
    have hlevels:Summable (fun z↦level z scene):=Summable.of_norm_bounded hs (fun _↦le_rfl)
    exact hlevels.congr (fun z↦(hscene z).symm)
  have hsumRead:(fun scene↦∑'z,(traffic z scene).toReal)=ᵐ[P]
      (fun scene↦∑'z,level z scene):=by
    filter_upwards [hread] with scene hscene
    exact tsum_congr hscene
  have hreadLp:MemLp (fun scene↦∑'z,(traffic z scene).toReal) 2 P:=hs.1.ae_eq hsumRead.symm
  exact ⟨memLp_ennreal_tsum_toReal_of_summable P traffic hfinite hsreal hreadLp,
    (ae_ennreal_tsum_ne_top_and_toReal_eq_of_summable P traffic hfinite hsreal).mono
      (fun _ hx↦hx.1)⟩

/-- The actual nonnegative original LEFT birth occupation sum is finite
almost surely and its exact real readout is L2. Every ENNReal finite-band term
is proved finite before conversion; no infinite traffic is discarded. -/
theorem exists_original_left_full_birth_ennreal_traffic_memLp_two
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) (hq : 0 < q)
    {density : M → ℝ} {v : M → E → ℝ} (c : ℝ≥0∞)
    (hdensityCont : Continuous density) (hdensity0 : ∀ x, 0 ≤ density x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hv0 : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hdensity : PopulationSeedClockDensity S w
      (μ.map (fun x : ℝ ↦ x - S.level)) density v c.toReal)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter) (hgap : 0 < gap)
    {poleη : ℝ} (hη : 0 < poleη) (hηspan : poleη < D.hi - D.lo)
    {G : Matrix (Fin q) (Fin q) ℝ} (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin q) (Fin q) ℝ}
    (hRem : ContinuousOn Rem (Ioo (-poleη) poleη))
    (hpole : ∀ r ∈ Ioo 0 poleη, originalSeedKernel S w (D.lo + r) = (r ^ 2)⁻¹ • G + Rem r)
    {g : ℝ → ℝ → ℝ} {gBound : ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ x y, |g x y| ≤ gBound) (τ : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching q μ ν (D.originalFocalKinetic gap) g)
    (hmin : ∀ P : LegalWeightedStationaryPoissonMatching q μ ν (D.originalFocalKinetic gap) g,
      Q.value τ ≤ P.value τ)
    {η : (Fin q → ℝ) → ℝ} (hηmeas : Measurable η)
    (hη0 : ∀ x, 0 ≤ η x)
    {physicalRadius basecap M₀ : ℝ} (hphysicalRadius : 0 ≤ physicalRadius)
    (hbasecap : 0 < basecap) (hηR : ∀ x, physicalRadius < ‖x‖ → η x = 0)
    (hM : 0 ≤ M₀) (hηM : ∀ x, η x ≤ M₀) :
    ∃cap ε:ℝ,0<cap∧cap≤basecap∧0<ε∧∀ell:ℕ,ell<birthPhysicalClockWindowCount cap→
      let traffic:=fun (z:ℕ×ℕ) (scene:LegalMarkedOptimalInputScene q)↦
        ∑i∈Finset.range (dyadicBirthBandCount z.2),
          legalMarkedCompletePathTraffic q (fun z↦originalSeedPathOffset S w z.2 z.1)
            (fun x↦ENNReal.ofReal (η x))
            (D.originalSupportedLeftBirthPhysicalClockWeight ε cap z.1 z.2 i ell) scene
      MemLp (fun scene↦(∑'z:ℕ×ℕ,traffic z scene).toReal) 2
        (Q.law:Measure (LegalMarkedOptimalInputScene q))∧
      ∀ᵐscene∂(Q.law:Measure (LegalMarkedOptimalInputScene q)),
        (∑'z:ℕ×ℕ,traffic z scene)≠(∞:ℝ≥0∞) := by
  obtain ⟨cap,ε₀,hcap,hcapbase,hε₀,hall⟩:=
    D.exists_original_left_full_birth_ennreal_traffic_on_collar hF hw hq
      c hdensityCont hdensity0 hv hv0 hdensity hbounds hgap hη hηspan hG hRem hpole
      hg hgb τ Q hmin hηmeas hη0 hphysicalRadius hbasecap hηR hM hηM
  refine ⟨cap,ε₀/2,hcap,hcapbase,(by positivity),?_⟩
  exact hall (by positivity) (by linarith)


/-- The finite physical-clock cover is added to the complete original
left-birth double family. This single actual nonnegative traffic sum is finite
almost surely and has L2 readout on every sufficiently small common collar. -/
theorem exists_original_left_full_birth_totalTraffic_memLp_two_on_collar
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) (hq : 0 < q)
    {density : M → ℝ} {v : M → E → ℝ} (c : ℝ≥0∞)
    (hdensityCont : Continuous density) (hdensity0 : ∀ x, 0 ≤ density x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hv0 : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hdensity : PopulationSeedClockDensity S w
      (μ.map (fun x : ℝ ↦ x - S.level)) density v c.toReal)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter) (hgap : 0 < gap)
    {poleη : ℝ} (hη : 0 < poleη) (hηspan : poleη < D.hi - D.lo)
    {G : Matrix (Fin q) (Fin q) ℝ} (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin q) (Fin q) ℝ}
    (hRem : ContinuousOn Rem (Ioo (-poleη) poleη))
    (hpole : ∀ r ∈ Ioo 0 poleη, originalSeedKernel S w (D.lo + r) = (r ^ 2)⁻¹ • G + Rem r)
    {g : ℝ → ℝ → ℝ} {gBound : ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ x y, |g x y| ≤ gBound) (τ : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching q μ ν (D.originalFocalKinetic gap) g)
    (hmin : ∀ P : LegalWeightedStationaryPoissonMatching q μ ν (D.originalFocalKinetic gap) g,
      Q.value τ ≤ P.value τ)
    {η : (Fin q → ℝ) → ℝ} (hηmeas : Measurable η)
    (hη0 : ∀ x, 0 ≤ η x)
    {physicalRadius basecap M₀ : ℝ} (hphysicalRadius : 0 ≤ physicalRadius)
    (hbasecap : 0 < basecap) (hηR : ∀ x, physicalRadius < ‖x‖ → η x = 0)
    (hM : 0 ≤ M₀) (hηM : ∀ x, η x ≤ M₀) :
    ∃cap ε₀:ℝ,0<cap∧cap≤basecap∧0<ε₀∧∀{ε:ℝ},0<ε→ε<ε₀→
      let windowTotal:=fun (ell:Fin (birthPhysicalClockWindowCount cap))
          (scene:LegalMarkedOptimalInputScene q)↦
        ∑'z:ℕ×ℕ,∑i∈Finset.range (dyadicBirthBandCount z.2),
          legalMarkedCompletePathTraffic q (fun z↦originalSeedPathOffset S w z.2 z.1)
            (fun x↦ENNReal.ofReal (η x))
            (D.originalSupportedLeftBirthPhysicalClockWeight ε cap z.1 z.2 i ell) scene
      MemLp (fun scene↦(∑ell,windowTotal ell scene).toReal) 2
        (Q.law:Measure (LegalMarkedOptimalInputScene q))∧
      ∀ᵐscene∂(Q.law:Measure (LegalMarkedOptimalInputScene q)),
        (∑ell,windowTotal ell scene)≠(∞:ℝ≥0∞) := by
  obtain ⟨cap,ε₀,hcap,hcapbase,hε₀,hall⟩:=
    D.exists_original_left_full_birth_ennreal_traffic_on_collar hF hw hq
      c hdensityCont hdensity0 hv hv0 hdensity hbounds hgap hη hηspan hG hRem hpole
      hg hgb τ Q hmin hηmeas hη0 hphysicalRadius hbasecap hηR hM hηM
  refine ⟨cap,ε₀,hcap,hcapbase,hε₀,?_⟩
  intro ε hε hεsmall
  dsimp only
  let P:Measure (LegalMarkedOptimalInputScene q):=Q.law
  let windowTotal:=fun (ell:Fin (birthPhysicalClockWindowCount cap))
      (scene:LegalMarkedOptimalInputScene q)↦
    ∑'z:ℕ×ℕ,∑i∈Finset.range (dyadicBirthBandCount z.2),
      legalMarkedCompletePathTraffic q (fun z↦originalSeedPathOffset S w z.2 z.1)
        (fun x↦ENNReal.ofReal (η x))
        (D.originalSupportedLeftBirthPhysicalClockWeight ε cap z.1 z.2 i ell) scene
  have hfinite:∀ell:Fin (birthPhysicalClockWindowCount cap),∀ᵐscene∂P,
      windowTotal ell scene≠(∞:ℝ≥0∞):=fun ell↦(hall hε hεsmall ell ell.isLt).2
  have hLp:∀ell:Fin (birthPhysicalClockWindowCount cap),
      MemLp (fun scene↦(windowTotal ell scene).toReal) 2 P:=
    fun ell↦(hall hε hεsmall ell ell.isLt).1
  have hsumLp:MemLp (fun scene↦∑ell,(windowTotal ell scene).toReal) 2 P:=
    memLp_finsetSum Finset.univ (fun ell _↦hLp ell)
  have hae:∀ᵐscene∂P,(∑ell,windowTotal ell scene)≠(∞:ℝ≥0∞)∧
      (∑ell,windowTotal ell scene).toReal=∑ell,(windowTotal ell scene).toReal:=by
    filter_upwards [ae_all_iff.mpr hfinite] with scene hscene
    exact ⟨ENNReal.sum_ne_top.mpr (fun ell _↦hscene ell),
      ENNReal.toReal_sum (fun ell _↦hscene ell)⟩
  exact ⟨hsumLp.ae_eq (hae.mono (fun _ hx↦hx.2.symm)),hae.mono (fun _ hx↦hx.1)⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
