import OTSelector.Reconstruction.OriginalMinimizerFullTrafficAssembly
import OTSelector.Reconstruction.OriginalMinimizerRightBirthWindowBasic

/-! Actual original-target determinant carriers at the same focal residue.
The carrier and original-input intensity hold for every positive subdivision
fraction, so they can be combined with an already chosen canonical h/cap. -/
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

/-- The exact original target contributor is in one deterministic determinant
carrier for every smaller collar and every positive physical subdivision cap.
The same carrier has its actual original-input intensity with the true s/t
saving. No canonical phase parameter is selected or changed by this lemma. -/
theorem exists_original_right_birth_targetDetCarrier_all_caps
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels) (hq : 0<q)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter) (hgap : 0<gap)
    {density : M→ℝ} {v : M→E→ℝ} (c : ℝ≥0∞)
    (hdensityCont : Continuous density) (hdensity0 : ∀x,0≤density x)
    (hv : ∀old,ContinuousOn (v old) (extChartAt 𝓘(ℝ,E) old).target)
    (hv0 : ∀old,∀y∈(extChartAt 𝓘(ℝ,E) old).target,0≤v old y)
    (hdensity : PopulationSeedClockDensity S w
      (ν.map (fun x:ℝ↦x-S.level)) density v c.toReal)
    {poleη : ℝ} (hη : 0<poleη) (hηspan : poleη<D.hi-D.lo)
    {G : Matrix (Fin q) (Fin q) ℝ} (hG : G.PosSemidef)
    {Rem : ℝ→Matrix (Fin q) (Fin q) ℝ}
    (hRem : ContinuousOn Rem (Ioo (-poleη) poleη))
    (hpole : ∀r∈Ioo 0 poleη,originalSeedKernel S w (D.hi-r)=(r^2)⁻¹•G+Rem r) :
    ∃ ε₀ Ddet : ℝ,0<ε₀∧ε₀≤1∧0<Ddet∧∀Rcell:ℝ,∃Λ:ℝ,0<Λ∧
      ∀{ε cap:ℝ},0<ε→ε<ε₀→0<cap→∀n j i ell:ℕ,
      i<dyadicBirthBandCount j→ell<birthPhysicalClockWindowCount cap→
      let t:=birthDyadicShellScale ε n
      let s:=birthDyadicElapsedScale ε n j
      let δ:=birthTrafficCoarseScale q t s
      let T:=positiveMatrixNormalizer (birthResidueScale G t s)
      let cut:=D.originalRightBirthPhysicalClockReference ε cap n j i ell-S.level
      let Band:=D.originalRightBirthNarrowClockBand ε n j i
      let Carrier:=D.originalBirthTargetDetCarrier T cut Band Ddet
      IsUnit T.det∧cut∈Ioo D.lo D.hi∧
        (∀(e:LegalMarkedPhysicalEdge q) clock,
          D.originalSupportedRightBirthPhysicalClockWeight ε cap n j i ell
            ((physicalPairAnchor e).2,clock)≠0→e.2.2∈Carrier)∧
        ∀z₀ p₀,((volume:Measure (Fin q→ℝ)).prod ν)
          (D.commonScaleOriginalTargetPhaseCell T cut δ Carrier z₀ p₀ Rcell)≤
            ENNReal.ofReal (Λ*(s/t)) := by
  let ηsmall:=min poleη 1
  have hηsmall:0<ηsmall:=lt_min hη zero_lt_one
  have hηsmallη:ηsmall≤poleη:=min_le_left _ _
  have hRemSmall:ContinuousOn Rem (Ioo (-ηsmall) ηsmall):=
    hRem.mono (fun r hr↦⟨lt_of_le_of_lt (neg_le_neg hηsmallη) hr.1,
      hr.2.trans_le hηsmallη⟩)
  obtain ⟨geoε,hgeoε,_hgeoη,hgeospan,lower,upper,hlower,hupper,hcomp⟩:=
    D.exists_original_right_birth_comparison_sameResidue hF hw hηsmall
      (hηsmallη.trans_lt hηspan) hG hRemSmall
      (fun r hr↦hpole r ⟨hr.1,hr.2.trans_le hηsmallη⟩)
  obtain ⟨εc,Ddet,hεc,hεc1,hDdet,hdet,hcell⟩:=
    D.exists_original_right_samePole_shrinkable_commonScale_intensity hF hw hq hη hG
      (hRem.continuousAt (Ioo_mem_nhds (by linarith) hη)) hpole
      c hdensityCont hdensity0 hv hv0 hdensity (16*upper)
  let ε₀:=min (geoε/16) (min (gap/16) εc)
  have hε₀:0<ε₀:=lt_min (by positivity) (lt_min (by positivity) hεc)
  have hε₀c:ε₀≤εc:=(min_le_right _ _).trans (min_le_right _ _)
  have hε₀geo:ε₀≤geoε/16:=min_le_left _ _
  have hε₀gap:ε₀≤gap/16:=(min_le_right _ _).trans (min_le_left _ _)
  refine ⟨ε₀,Ddet,hε₀,hε₀c.trans hεc1,hDdet,?_⟩
  intro Rcell
  obtain ⟨Λ,hΛ,hcell⟩:=hcell Rcell
  refine ⟨Λ,hΛ,?_⟩
  intro ε cap hε hεsmall hcap n j i ell hi hell
  dsimp only
  let t:=birthDyadicShellScale ε n
  let s:=birthDyadicElapsedScale ε n j
  let T:=positiveMatrixNormalizer (birthResidueScale G t s)
  let ref:=D.originalRightBirthPhysicalClockReference ε cap n j i ell
  let cut:=ref-S.level
  have ht:0<t:=birthDyadicShellScale_pos hε n
  have hs:0<s:=(birthDyadicClockBand_base_bounds hε n j i hi).1
  have htε:2*t≤ε:=by
    rw [two_mul_birthDyadicShellScale]
    exact div_le_self hε.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
  have hscale:8*t<geoε:=by linarith [hεsmall.trans_le hε₀geo]
  have hgapε:8*ε≤gap:=by linarith [hεsmall.trans_le hε₀gap]
  have hwidth:0≤birthPhysicalClockWindowWidth cap s:=(birthPhysicalClockWindow_spec hcap hs).2.1.le
  have hcutbounds:=D.originalRightBirthPhysicalClockWindow_inward_bounds hε hcap
    n j i ell hi hell (show ref∈Icc (ref-birthPhysicalClockWindowWidth cap s) ref from
      ⟨by linarith,le_rfl⟩)
  have hcut:cut∈Ioo D.lo D.hi:=by
    constructor <;> dsimp only [cut] <;> linarith [hcutbounds.1,hcutbounds.2]
  have hT:IsUnit T.det:=(positiveMatrixNormalizer_spec (birthResidueScale_posDef (t:=t) hG hs)).1
  refine ⟨hT,hcut,?_,hcell hε (hεsmall.trans_le hε₀c) n j i hi cut hcut⟩
  intro e clock hf
  have hmask:=D.originalSupportedRightBirthPhysicalClockWeight_mask_ne_zero
    ε cap n j i ell _ hf
  have hupperLeg:=D.originalSupportedRightBirthPhysicalClockMask_shortLeg_upper_of_comparison
    hF hw hG hε hcap hbounds hgapε hgeospan hlower.le hupper.le hcomp
    n j i ell hscale hell e clock hmask
  exact ⟨D.originalSupportedRightBirthPhysicalClockWeight_target_mem_band ε cap n j i ell _ hf,
    hdet _ (D.normalizedTargetPhaseLeg_posSemidef hF hw T hcut e.2.2) hupperLeg⟩


/-- The actual inverse-coarse-scale Palm mean is finite and has the true
large-phase s² physical energy coefficients as a real inequality. All moment
finiteness is derived from the original weighted matching, without a supplied
second-moment or completed traffic bound. -/
theorem exists_original_right_birth_coarseWeightedPalm_real_rate
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    {poleη : ℝ} (hη : 0<poleη) (hηspan : poleη<D.hi-D.lo)
    {G : Matrix (Fin q) (Fin q) ℝ} (hG : G.PosSemidef)
    {Rem : ℝ→Matrix (Fin q) (Fin q) ℝ}
    (hRem : ContinuousOn Rem (Ioo (-poleη) poleη))
    (hpole : ∀r∈Ioo 0 poleη,originalSeedKernel S w (D.hi-r)=(r^2)⁻¹•G+Rem r) :
    ∃ ε₀ C : ℝ,0<ε₀∧0<C∧∀{ε cap:ℝ},0<ε→ε<ε₀→0<cap→
      ∀{gap diameter:ℝ},0<gap→ConditionalClockSupportBounds μ ν gap diameter→
      ∀{g:ℝ→ℝ→ℝ}
        (Q:LegalWeightedStationaryPoissonMatching q μ ν (D.originalFocalKinetic gap) g),
      ∀n j i ell:ℕ,i<dyadicBirthBandCount j→ell<birthPhysicalClockWindowCount cap→
      let t:=birthDyadicShellScale ε n
      let s:=birthDyadicElapsedScale ε n j
      let δ:=birthTrafficCoarseScale q t s
      let T:=positiveMatrixNormalizer (birthResidueScale G t s)
      let B:={m:PhysicalPairPalmMark (Fin q)|m.1.2∈D.originalRightBirthNarrowClockBand ε n j i}
      let weightedPalm:=∫⁻m,∫⁻clock:ℝ,
        ENNReal.ofReal ‖(Tᵀ)⁻¹*ᵥoriginalSeedPairMomentum S w m‖*
          D.originalSupportedRightBirthPhysicalClockWeight ε cap n j i ell (m,clock)
        ∂volume∂legalMarkedJointPalm q Q.law
      weightedPalm≠(∞:ℝ≥0∞)∧δ⁻¹*weightedPalm.toReal≤(cap*C)*
        (s^2*t^(-2+1/(q:ℝ))*(∫⁻m in B,
            ENNReal.ofReal (originalSeedRightPoleEnergy S w D.hi G m)
            ∂legalMarkedJointPalm q Q.law).toReal+
          s^2*t^(-1+1/(q:ℝ))*(∫⁻m in B,
            ENNReal.ofReal (‖originalSeedPairMomentum S w m‖^2)
            ∂legalMarkedJointPalm q Q.law).toReal) := by
  obtain ⟨ε₀,C,hε₀,_hε₀η,_hε₀1,hC,hrate⟩:=
    D.exists_original_right_supportedBirthWindow_coarseWeightedPalm_rate hF hw hη hG
      (hRem.continuousAt (Ioo_mem_nhds (by linarith) hη)) hpole
  refine ⟨ε₀,C,hε₀,hC,?_⟩
  intro ε cap hε hεsmall hcap gap diameter hgap hbounds g Q n j i ell hi hell
  dsimp only
  let t:=birthDyadicShellScale ε n
  let s:=birthDyadicElapsedScale ε n j
  let δ:=birthTrafficCoarseScale q t s
  let T:=positiveMatrixNormalizer (birthResidueScale G t s)
  let B:={m:PhysicalPairPalmMark (Fin q)|m.1.2∈D.originalRightBirthNarrowClockBand ε n j i}
  let e:=∫⁻m in B,ENNReal.ofReal (originalSeedRightPoleEnergy S w D.hi G m)
    ∂legalMarkedJointPalm q Q.law
  let v:=∫⁻m in B,ENNReal.ofReal (‖originalSeedPairMomentum S w m‖^2)
    ∂legalMarkedJointPalm q Q.law
  let weightedPalm:=∫⁻m,∫⁻clock:ℝ,
    ENNReal.ofReal ‖(Tᵀ)⁻¹*ᵥoriginalSeedPairMomentum S w m‖*
      D.originalSupportedRightBirthPhysicalClockWeight ε cap n j i ell (m,clock)
    ∂volume∂legalMarkedJointPalm q Q.law
  have ht:0<t:=birthDyadicShellScale_pos hε n
  have hs:0<s:=(birthDyadicClockBand_base_bounds hε n j i hi).1
  have hδ:0<δ:=birthTrafficCoarseScale_pos q ht hs
  obtain ⟨E₀,_hE₀,henergy⟩:=D.exists_original_right_narrowBirthBands_energy_budget
    hF hw hη hηspan hG hRem hpole hgap hbounds Q
  have he:e≠(∞:ℝ≥0∞):=((henergy hε n j 0).1 i).1
  have hv:v≠(∞:ℝ≥0∞):=((henergy hε n j 0).1 i).2
  have hfirst:ENNReal.ofReal (s^2*t^(-2+1/(q:ℝ)))*e≠(∞:ℝ≥0∞):=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top he
  have hsecond:ENNReal.ofReal (s^2*t^(-1+1/(q:ℝ)))*v≠(∞:ℝ≥0∞):=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hv
  have hsum:=ENNReal.add_ne_top.mpr ⟨hfirst,hsecond⟩
  have hfinite:=ENNReal.mul_ne_top (a:=ENNReal.ofReal (cap*C)) ENNReal.ofReal_ne_top hsum
  have hr:=hrate hε hεsmall hcap Q n j i ell hi hell
  change ENNReal.ofReal (δ⁻¹)*weightedPalm≤ENNReal.ofReal (cap*C)*
    (ENNReal.ofReal (s^2*t^(-2+1/(q:ℝ)))*e+
      ENNReal.ofReal (s^2*t^(-1+1/(q:ℝ)))*v) at hr
  have hweighted:weightedPalm≠(∞:ℝ≥0∞):=
    (ENNReal.lt_top_of_mul_ne_top_right (ne_top_of_le_ne_top hfinite hr)
      (ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr hδ))).ne
  refine ⟨hweighted,?_⟩
  have hreal:=ENNReal.toReal_mono hfinite hr
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (inv_nonneg.mpr hδ.le),
    ENNReal.toReal_mul,ENNReal.toReal_ofReal (mul_nonneg hcap.le hC.le),
    ENNReal.toReal_add hfirst hsecond,
    ENNReal.toReal_mul,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (show 0≤s^2*t^(-2+1/(q:ℝ)) by positivity),
    ENNReal.toReal_ofReal (show 0≤s^2*t^(-1+1/(q:ℝ)) by positivity)] at hreal
  exact hreal

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
