import OTSelector.Reconstruction.OriginalMinimizerFullTrafficAssembly
import OTSelector.MeasureTheory.Lp.FiniteGoodBadSum
import OTSelector.Reconstruction.OriginalBirthTrafficDoubleSummation

/-! Actual bounded birth traffic with its original count-bad remainder.
The geometry, phase and input-count events are selected together. -/
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

/-- Full actual bounded-birth levels retain the interpolated energy saving
and the same original count-tail remainder, for the same geometric choice. -/
theorem exists_original_left_bounded_birth_level_norm
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
    ∃ h cap E₀ : ℝ,0<h∧0<cap∧1≤E₀∧∀ H:ℝ,0≤H→
    ∃ ε₀ radius A Btail : ℝ,0<ε₀∧ε₀≤1∧0≤radius∧0<A∧0≤Btail∧
      ∀ {ε:ℝ},0<ε→ε<ε₀→∀ n j ell:ℕ,ell<birthPhysicalClockWindowCount cap→∀ {K:ℝ},0≤K→
      let t:=birthDyadicShellScale ε n
      let s:=birthDyadicElapsedScale ε n j
      let δ:=birthTrafficCoarseScale q t s
      let T:=positiveMatrixNormalizer (birthResidueScale G t s)
      let L:ℝ≥0:=⟨Real.sqrt ((q:ℝ)/h^2),Real.sqrt_nonneg _⟩
      let cut:=fun i↦D.originalLeftBirthPhysicalClockReference ε cap n j i ell-S.level
      let Small:=fun i↦{scene:LegalMarkedOptimalInputScene q |
        ‖D.normalizedMomentumPhaseField T (cut i) h L scene 0‖≤H*δ}
      let traffic:=fun i scene↦(Small i).indicator (fun scene:LegalMarkedOptimalInputScene q↦
        (legalMarkedCompletePathTraffic q (fun z↦originalSeedPathOffset S w z.2 z.1)
          (fun x↦ENNReal.ofReal (η x))
          (D.originalSupportedLeftBirthPhysicalClockWeight ε cap n j i ell) scene).toReal) scene
      MemLp (fun scene↦∑ i∈Finset.range (dyadicBirthBandCount j),traffic i scene)
        2 (Q.law:Measure (LegalMarkedOptimalInputScene q)) ∧
      eLpNorm (fun scene↦∑ i∈Finset.range (dyadicBirthBandCount j),traffic i scene)
        2 (Q.law:Measure (LegalMarkedOptimalInputScene q))≤
      ENNReal.ofReal ((A*Real.sqrt K*Real.sqrt E₀)*
        (t^(if G.rank=0 then (3/8:ℝ) else (G.rank:ℝ)/8)*
          (s/t)^(if G.rank=0 then (3/28:ℝ) else (G.rank:ℝ)/(4*(3*(G.rank:ℝ)+4)))) + (dyadicBirthBandCount j : ℝ)*(Btail*Real.exp (-K/4))) := by
  obtain ⟨h,cap,hh,hcap,_hcapbase,hsmall⟩ :=
    D.exists_original_left_bounded_birth_goodBad_smallMoments hF hw hq
      c hdensityCont hdensity0 hv hv0 hdensity hbounds hgap hη hηspan hG hRem hpole
      hg hgb τ Q hmin hηmeas hη0 hphysicalRadius hbasecap hηR hM hηM
  obtain ⟨E₀,hE₀,henergy⟩ := D.exists_original_left_narrowBirthBands_energy_budget
    hF hw hη hηspan hG hRem hpole hgap hbounds Q
  refine ⟨h,cap,E₀,hh,hcap,hE₀,?_⟩
  intro H hH
  obtain ⟨ε₀,radius,C₁,C₂,Btail,hε₀,hε₀1,hradius,hC₁,hC₂,hBtail,hsmall⟩ := hsmall H hH
  let p₁:=4*M₀*(physicalRadius+1)*
    (∫⁻ x,ENNReal.ofReal (η x) ∂(volume:Measure (Fin q→ℝ))).toReal*cap*C₁
  let p₂:=(M₀*cap)^2*C₂
  let C:=max p₁ p₂+1
  have hp₁ : p₁≤C := (le_max_left _ _).trans (by dsimp only [C]; linarith)
  have hp₂ : p₂≤C := (le_max_right _ _).trans (by dsimp only [C]; linarith)
  have hp₁0 : 0≤p₁ := by dsimp only [p₁]; positivity
  have hC : 0<C := by dsimp only [C]; linarith [le_max_left p₁ p₂]
  let A:=(2*(8:ℝ)^(3/4:ℝ)+2*Real.sqrt 8)*Real.sqrt C
  have hA : 0<A := by dsimp only [A]; positivity
  refine ⟨ε₀,radius,A,Btail,hε₀,hε₀1,hradius,hA,hBtail,?_⟩
  intro ε hε hεsmall n j ell hell K hK
  dsimp only
  let t:=birthDyadicShellScale ε n
  let s:=birthDyadicElapsedScale ε n j
  let δ:=birthTrafficCoarseScale q t s
  let T:=positiveMatrixNormalizer (birthResidueScale G t s)
  let L:ℝ≥0:=⟨Real.sqrt ((q:ℝ)/h^2),Real.sqrt_nonneg _⟩
  let W:=birthTrafficSpatialWindow G t s radius
  let J:=D.originalLeftBirthNarrowClockBand ε n j
  let cut:=fun i↦D.originalLeftBirthPhysicalClockReference ε cap n j i ell-S.level
  let Good:=fun i↦{scene:LegalMarkedOptimalInputScene q |
    ‖D.normalizedMomentumPhaseField T (cut i) h L scene 0‖≤H*δ∧
      (scene.2:Measure (LegalColoredInputPoint q)) ((W×ˢJ i)×ˢ{0})≤ENNReal.ofReal K}
  let traffic:=fun i↦(Good i).indicator (fun scene:LegalMarkedOptimalInputScene q↦
    (legalMarkedCompletePathTraffic q (fun z↦originalSeedPathOffset S w z.2 z.1)
      (fun x↦ENNReal.ofReal (η x))
      (D.originalSupportedLeftBirthPhysicalClockWeight ε cap n j i ell) scene).toReal)
  let B : ℕ → Set (PhysicalPairPalmMark (Fin q)) := fun i ↦ {m | m.1.1 ∈ J i}
  let e:=fun i↦(∫⁻ m in B i,ENNReal.ofReal (originalSeedLeftPoleEnergy S w D.lo G m)
    ∂legalMarkedJointPalm q Q.law).toReal
  let v:=fun i↦(∫⁻ m in B i,ENNReal.ofReal (‖originalSeedPairMomentum S w m‖^2)
    ∂legalMarkedJointPalm q Q.law).toReal
  let bands:=Finset.range (dyadicBirthBandCount j)
  let P:Measure (LegalMarkedOptimalInputScene q):=Q.law
  have ht : 0<t := birthDyadicShellScale_pos hε n
  have hs : 0<s := div_pos ht (by positivity)
  have ht1 : t≤1 := by
    have htε : 2*t≤ε := by
      rw [two_mul_birthDyadicShellScale]
      exact div_le_self hε.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
    linarith [hεsmall.le.trans hε₀1]
  have hNs : (bands.card:ℝ)*s=8*t := by
    dsimp only [bands,birthDyadicElapsedScale,s,t]
    simp only [Finset.card_range,dyadicBirthBandCount,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    field_simp
  have hb:=henergy hε n j (dyadicBirthBandCount j)
  dsimp only at hb
  have he : ∀ i,0≤e i := fun _↦ENNReal.toReal_nonneg
  have hv : ∀ i,0≤v i := fun _↦ENNReal.toReal_nonneg
  have hE : (∑ i∈bands,e i)≤E₀ := hb.2.1
  have hV : (∑ i∈bands,v i)≤E₀ := hb.2.2
  have hLp : ∀ i∈bands,MemLp (traffic i) 2 P := by
    intro i hi
    exact (hsmall hε hεsmall n j i ell (Finset.mem_range.mp hi) hell hK).1.1
  have hfirst : ∀ i∈bands,(∫ scene,(traffic i scene)^2 ∂P)≤
      (K*C)*s^(3/2:ℝ)*(t^(((G.rank:ℝ)-3)/2)*Real.sqrt (e i)+t^((G.rank:ℝ)/2)*Real.sqrt (v i)) := by
    intro i hi
    have hr:=(hsmall hε hεsmall n j i ell (Finset.mem_range.mp hi) hell hK).1.2.1
    have hr:=hr.trans (min_le_left _ _)
    calc
      _ ≤ (K*p₁)*s^(3/2:ℝ)*(t^(((G.rank:ℝ)-3)/2)*Real.sqrt (e i)+t^((G.rank:ℝ)/2)*Real.sqrt (v i)) := by
        convert hr using 1
        all_goals first | rfl | (dsimp only [p₁,t,s,e,v,B,J]; ring)
      _ ≤ _ := by gcongr
  have hsecond : ∀ i∈bands,(∫ scene,(traffic i scene)^2 ∂P)≤
      (K*C)*s^2*(t^(-((G.rank:ℝ)+4))*e i+t^(-((G.rank:ℝ)+3))*v i) := by
    intro i hi
    have hr:=(hsmall hε hεsmall n j i ell (Finset.mem_range.mp hi) hell hK).1.2.1
    have hr:=hr.trans (min_le_right _ _)
    calc
      _ ≤ (K*p₂)*s^2*(t^(-((G.rank:ℝ)+4))*e i+t^(-((G.rank:ℝ)+3))*v i) := by
        convert hr using 1
        all_goals first | rfl | (dsimp only [p₂,t,s,e,v,B,J]; ring)
      _ ≤ _ := by gcongr
  have hgood : MemLp (fun scene↦∑ i∈bands,traffic i scene) 2 P ∧
      eLpNorm (fun scene↦∑ i∈bands,traffic i scene) 2 P ≤
        ENNReal.ofReal ((A*Real.sqrt K*Real.sqrt E₀)*
          (t^(if G.rank=0 then (3/8:ℝ) else (G.rank:ℝ)/8)*
            (s/t)^(if G.rank=0 then (3/28:ℝ) else (G.rank:ℝ)/(4*(3*(G.rank:ℝ)+4))))) := by
    by_cases hrank : G.rank=0
    · have hezero : ∀ i,e i=0 := by
        intro i
        simp only [e,D.original_left_poleEnergy_eq_zero_of_rank_zero hrank,ENNReal.ofReal_zero,
          lintegral_zero,ENNReal.toReal_zero]
      have hf : ∀ i∈bands,(∫ scene,(traffic i scene)^2 ∂P)≤(K*C)*s^(3/2:ℝ)*Real.sqrt (v i) := by
        simpa only [hrank,Nat.cast_zero,hezero,Real.sqrt_zero,mul_zero,zero_add,
          zero_div,Real.rpow_zero,one_mul] using hfirst
      have hs' : ∀ i∈bands,(∫ scene,(traffic i scene)^2 ∂P)≤(K*C)*s^2*(t^(-3:ℝ)*v i) := by
        simpa only [hrank,Nat.cast_zero,hezero,mul_zero,zero_add] using hsecond
      have hout:=birthBand_rankZero_traffic_interpolated_level_norm P bands traffic hLp v hv
        ht ht1 hs (mul_nonneg hK hC.le) hE₀ hNs hV hf hs'
      refine ⟨hout.1,hout.2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
      simp only [hrank,ite_true,Real.sqrt_mul hK,t,s]
      dsimp only [A]
      nlinarith [mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ)≤8) (3/4:ℝ))
        (mul_nonneg (Real.sqrt_nonneg K) (Real.sqrt_nonneg C)))
        (mul_nonneg (Real.sqrt_nonneg E₀) (mul_nonneg (Real.rpow_nonneg ht.le (3/8:ℝ))
          (Real.rpow_nonneg (div_nonneg hs.le ht.le) (3/28:ℝ))))]
    · have hk : 0<(G.rank:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hrank
      have hout:=birthBand_small_traffic_interpolated_level_norm P bands traffic hLp e v he hv
        ht ht1 hs (mul_nonneg hK hC.le) hE₀ hk hNs hE hV hfirst hsecond
      refine ⟨hout.1,hout.2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
      simp only [hrank,ite_false,Real.sqrt_mul hK,t,s]
      dsimp only [A]
      exact le_of_eq (by ring)
  
  
  let Small:=fun i↦{scene:LegalMarkedOptimalInputScene q |
    ‖D.normalizedMomentumPhaseField T (cut i) h L scene 0‖≤H*δ}
  let Bad:=fun i↦{scene:LegalMarkedOptimalInputScene q |
    ENNReal.ofReal K < (scene.2:Measure (LegalColoredInputPoint q)) ((W×ˢJ i)×ˢ{0})}
  let raw:=fun i (scene:LegalMarkedOptimalInputScene q)↦
    (legalMarkedCompletePathTraffic q (fun z↦originalSeedPathOffset S w z.2 z.1)
      (fun x↦ENNReal.ofReal (η x))
      (D.originalSupportedLeftBirthPhysicalClockWeight ε cap n j i ell) scene).toReal
  have hGoodEq : ∀ i,Good i=((Small i)ᶜ∪Bad i)ᶜ := by
    intro i
    ext scene
    simp only [Good,Small,Bad,mem_ofPred_eq,mem_compl_iff,mem_union,not_or,not_not,not_lt]
  have hgood' : MemLp (fun scene↦∑ i∈bands,((Small i)ᶜ∪Bad i)ᶜ.indicator (raw i) scene) 2 P ∧
      eLpNorm (fun scene↦∑ i∈bands,((Small i)ᶜ∪Bad i)ᶜ.indicator (raw i) scene) 2 P ≤
        ENNReal.ofReal ((A*Real.sqrt K*Real.sqrt E₀)*
          (t^(if G.rank=0 then (3/8:ℝ) else (G.rank:ℝ)/8)*
            (s/t)^(if G.rank=0 then (3/28:ℝ) else (G.rank:ℝ)/(4*(3*(G.rank:ℝ)+4))))) := by
    simpa only [traffic,hGoodEq] using hgood
  have hbad : ∀ i∈bands,MemLp ((Bad i).indicator ((Small i).indicator (raw i))) 2 P := by
    intro i hi
    exact (hsmall hε hεsmall n j i ell (Finset.mem_range.mp hi) hell hK).2.1
  have hbadNorm : ∀ i∈bands,eLpNorm ((Bad i).indicator ((Small i).indicator (raw i))) 2 P ≤
      ENNReal.ofReal (Btail*Real.exp (-K/4)) := by
    intro i hi
    exact (hsmall hε hεsmall n j i ell (Finset.mem_range.mp hi) hell hK).2.2
  have hfull:=finite_sceneEvent_traffic_memLp_two_of_good_bad_norm_bounds P bands Small Bad raw
    hgood'.1 hbad (by positivity) (by positivity) hgood'.2 hbadNorm
  simpa only [bands,Finset.card_range] using hfull


/-- Every bounded canonical phase of the actual original left-birth traffic
is L2 over the entire double dyadic family. The original count-good and
count-bad pieces are assembled internally on the same Q and same h/cap. -/
theorem exists_original_left_bounded_birth_dyadic_traffic_memLp_two
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
    ∃ h cap : ℝ,0<h∧0<cap∧∀ H:ℝ,0≤H→
    ∃ ε : ℝ,0<ε∧
      ∀ ell:ℕ,ell<birthPhysicalClockWindowCount cap→
      let level := fun (z:ℕ×ℕ) (scene:LegalMarkedOptimalInputScene q) ↦
        let t:=birthDyadicShellScale ε z.1
        let s:=birthDyadicElapsedScale ε z.1 z.2
        let δ:=birthTrafficCoarseScale q t s
        let T:=positiveMatrixNormalizer (birthResidueScale G t s)
        let L:ℝ≥0:=⟨Real.sqrt ((q:ℝ)/h^2),Real.sqrt_nonneg _⟩
        ∑ i∈Finset.range (dyadicBirthBandCount z.2),
          {scene:LegalMarkedOptimalInputScene q |
            ‖D.normalizedMomentumPhaseField T
              (D.originalLeftBirthPhysicalClockReference ε cap z.1 z.2 i ell-S.level) h L scene 0‖≤H*δ}.indicator
            (fun scene:LegalMarkedOptimalInputScene q ↦
              (legalMarkedCompletePathTraffic q (fun z↦originalSeedPathOffset S w z.2 z.1)
                (fun x↦ENNReal.ofReal (η x))
                (D.originalSupportedLeftBirthPhysicalClockWeight ε cap z.1 z.2 i ell) scene).toReal) scene
      MemLp (fun scene↦∑' z:ℕ×ℕ,level z scene) 2
        (Q.law:Measure (LegalMarkedOptimalInputScene q)) ∧
      Summable (fun z:ℕ×ℕ ↦(eLpNorm (level z) 2
        (Q.law:Measure (LegalMarkedOptimalInputScene q))).toReal) ∧
      ∀ᵐ scene∂(Q.law:Measure (LegalMarkedOptimalInputScene q)),
        Summable (fun z:ℕ×ℕ ↦‖level z scene‖) := by
  obtain ⟨h,cap,E₀,hh,hcap,hE₀,hlevel⟩ :=
    D.exists_original_left_bounded_birth_level_norm hF hw hq
      c hdensityCont hdensity0 hv hv0 hdensity hbounds hgap hη hηspan hG hRem hpole
      hg hgb τ Q hmin hηmeas hη0 hphysicalRadius hbasecap hηR hM hηM
  refine ⟨h,cap,hh,hcap,?_⟩
  intro H hH
  obtain ⟨ε₀,radius,A,Btail,hε₀,_hε₀1,hradius,hA,hBtail,hlevel⟩ := hlevel H hH
  let ε:=ε₀/2
  have hε : 0<ε := by dsimp only [ε]; positivity
  have hεsmall : ε<ε₀ := by dsimp only [ε]; linarith
  refine ⟨ε,hε,?_⟩
  intro ell hell
  dsimp only
  apply memLp_original_birth_double_tsum_of_level_norm_bounds
    (Q.law : Measure (LegalMarkedOptimalInputScene q))
    (show 0 < (q : ℝ) by exact_mod_cast hq)
    hε hE₀ hA.le hBtail G.rank
  · intro z
    exact (hlevel hε hεsmall z.1 z.2 ell hell (le_refl (0 : ℝ))).1
  · intro z K hK
    exact (hlevel hε hεsmall z.1 z.2 ell hell hK).2



end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
