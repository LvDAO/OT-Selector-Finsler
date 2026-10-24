import OTSelector.Reconstruction.OriginalMinimizerOldRegularTrafficPalmBands
import OTSelector.Reconstruction.OriginalBirthBandFirstOccupationMoment
import OTSelector.Reconstruction.OriginalBirthBandWeightedOccupation
import OTSelector.Reconstruction.BirthSmallFirstMomentScale
import OTSelector.Reconstruction.BirthLargePhaseMomentScale
import OTSelector.Reconstruction.OriginalOldFocalLegs
import OTSelector.Analysis.ENNRealSquareRootReadout

/-! The literal old physical-window Palm means retain the same endpoint
residue, original cumulative target mass, and actual finite kinetic energies. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Topology Matrix.Norms.Operator Classical BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M→ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
local notation "qdim" => finrank ℝ S.covector.ker

/-- The actual full old-window unweighted and weighted Palm occupations have their positive
shell powers and internally proved finite original energy budgets. -/
theorem exists_original_right_oldWindow_Palm_real_rates
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    {density : M→ℝ} {v : M→E→ℝ} (c : ℝ≥0∞)
    (hρ : Continuous density) (hρ0 : ∀x,0≤density x)
    (hv : ∀old,ContinuousOn (v old) (extChartAt 𝓘(ℝ,E) old).target)
    (hv0 : ∀old,∀y∈(extChartAt 𝓘(ℝ,E) old).target,0≤v old y)
    (hdensity : PopulationSeedClockDensity S w
      (ν.map (fun x:ℝ↦x-S.level)) density v c.toReal)
    {poleη : ℝ} (hη : 0<poleη) (hηspan : poleη<D.hi-D.lo)
    {G : Matrix (Fin qdim) (Fin qdim) ℝ} (hG : G.PosSemidef)
    {Rem : ℝ→Matrix (Fin qdim) (Fin qdim) ℝ}
    (hRem : ContinuousOn Rem (Ioo (-poleη) poleη))
    (hpole : ∀a∈Ioo 0 poleη,originalSeedKernel S w (D.hi-a)=(a^2)⁻¹•G+Rem a)
    {gap diameter : ℝ} (hgap : 0<gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter) {g : ℝ→ℝ→ℝ}
    (Q : LegalWeightedStationaryPoissonMatching qdim μ ν (D.originalFocalKinetic gap) g) :
    ∃ ε₀ Cfirst Cweighted E₀ : ℝ,0<ε₀∧ε₀≤1∧0<Cfirst∧0<Cweighted∧1≤E₀∧
      ∀ {ε cap : ℝ},0<ε→ε<ε₀→0<cap→∀n ell:ℕ,
      ell<birthPhysicalClockWindowCount cap→
      let t:=birthDyadicShellScale ε n
      let B:={m:PhysicalPairPalmMark (Fin qdim)|D.hi-(m.1.2-S.level)∈Ioc 0 (2*t)}
      let e:=∫⁻m in B,ENNReal.ofReal (originalSeedRightPoleEnergy S w D.hi G m)
        ∂legalMarkedJointPalm qdim Q.law
      let v:=∫⁻m in B,ENNReal.ofReal (‖originalSeedPairMomentum S w m‖^2)
        ∂legalMarkedJointPalm qdim Q.law
      let palm:=∫⁻m,∫⁻clock:ℝ,D.originalSupportedOldPhysicalClockWeight ε cap 1 n ell (m,clock)
        ∂volume∂legalMarkedJointPalm qdim Q.law
      let T:=positiveMatrixNormalizer (focalResidueScale G t)
      let δ:=birthTrafficCoarseScale qdim t t
      let weighted:=∫⁻m,∫⁻clock:ℝ,
        ENNReal.ofReal ‖(Tᵀ)⁻¹*ᵥoriginalSeedPairMomentum S w m‖*
          D.originalSupportedOldPhysicalClockWeight ε cap 1 n ell (m,clock)
        ∂volume∂legalMarkedJointPalm qdim Q.law
      e≠(∞:ℝ≥0∞)∧v≠(∞:ℝ≥0∞)∧e.toReal≤E₀∧v.toReal≤E₀∧
        palm≠(∞:ℝ≥0∞)∧palm.toReal≤cap*Cfirst*
          (t^((G.rank:ℝ)/2)*Real.sqrt e.toReal+
            t^(((G.rank:ℝ)+3)/2)*Real.sqrt v.toReal)∧
        weighted≠(∞:ℝ≥0∞)∧δ⁻¹*weighted.toReal≤cap*Cweighted*
          (t^(1/(qdim:ℝ))*e.toReal+t^(1+1/(qdim:ℝ))*v.toReal) := by
  have hRem0:=hRem.continuousAt (Ioo_mem_nhds (by linarith) hη)
  obtain ⟨εfirst,Cfirst,hεfirst,_hεfirstη,hCfirst,hfirst⟩:=
    D.exists_original_right_focalBand_firstOccupationMoment_bound hF hw hη hG hRem0 hpole
  obtain ⟨εweighted,Cweighted,hεweighted,_hεweightedη,hCweighted,hweighted⟩:=
    D.exists_original_right_focalBand_weightedOccupation_bound hF hw hη hG hRem0 hpole
  obtain ⟨εmass,Kmass,hεmass,_hεmassspan,hKmass,hmass⟩:=
    D.exists_original_right_birth_mass_bound hF hw c hρ hρ0 hv hv0 hdensity hη hRem0 hpole
  obtain ⟨E₀,hE₀,hbudget⟩:=D.exists_original_right_sameResidue_clockBand_energy_budget
    hF hw hη hηspan hG hRem hpole hgap hbounds Q
  let Km:ℝ:=3^(G.rank+1)*Kmass
  have hKm:0<Km:=by dsimp [Km];positivity
  let ε₀:=min ((min εfirst εweighted)/4) (min (εmass/3) 1)
  have hε₀:0<ε₀:=lt_min (by positivity) (lt_min (by positivity) zero_lt_one)
  have hε₀f:ε₀≤εfirst/4:=(min_le_left _ _).trans
    (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  have hε₀w:ε₀≤εweighted/4:=(min_le_left _ _).trans
    (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
  have hε₀m:ε₀≤εmass/3:=(min_le_right _ _).trans (min_le_left _ _)
  have hε₀1:ε₀≤1:=(min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ε₀,Cfirst*Real.sqrt Km,Cweighted,E₀,hε₀,hε₀1,by positivity,hCweighted,hE₀,?_⟩
  intro ε cap hε hεsmall hcap n ell hell
  dsimp only
  let t:=birthDyadicShellScale ε n
  let B:={m:PhysicalPairPalmMark (Fin qdim)|D.hi-(m.1.2-S.level)∈Ioc 0 (2*t)}
  let ref:=D.originalOldPhysicalClockReference ε cap 1 n ell
  let width:=oldPhysicalClockWindowWidth cap t
  let I:=Icc (ref-width) ref
  let P:=legalMarkedJointPalm qdim Q.law
  let e:=∫⁻m in B,ENNReal.ofReal (originalSeedRightPoleEnergy S w D.hi G m)∂P
  let v:=∫⁻m in B,ENNReal.ofReal (‖originalSeedPairMomentum S w m‖^2)∂P
  let palm:=∫⁻m,∫⁻clock:ℝ,D.originalSupportedOldPhysicalClockWeight ε cap 1 n ell (m,clock)∂volume∂P
  have ht:0<t:=birthDyadicShellScale_pos hε n
  have htε:2*t≤ε:=by
    rw [two_mul_birthDyadicShellScale]
    exact div_le_self hε.le (one_le_pow₀ (by norm_num:(1:ℝ)≤2))
  have h4t:4*t<εfirst:=by linarith [hεsmall.trans_le hε₀f]
  have h4tw:4*t<εweighted:=by linarith [hεsmall.trans_le hε₀w]
  have ht1:t≤1:=by linarith [hεsmall.le.trans hε₀1]
  have h3t:3*t<εmass:=by linarith [hεsmall.trans_le hε₀m]
  have hB:MeasurableSet B:=measurableSet_Ioc.preimage
    (measurable_const.sub (measurable_fst.snd.sub_const _))
  have hgrid:B=(fun m:PhysicalPairPalmMark (Fin qdim)↦D.hi-(m.1.2-S.level))⁻¹' clockGridBand 0 (2*t) 0:=by
    ext m
    simp [B,clockGridBand]
  have hb:=hbudget 0 (show 0≤2*t by positivity) 1
  dsimp only at hb
  have he:e≠(∞:ℝ≥0∞):=by simpa only [←hgrid] using (hb.1 0).1
  have hv':v≠(∞:ℝ≥0∞):=by simpa only [←hgrid] using (hb.1 0).2
  have heE:e.toReal≤E₀:=by simpa only [Finset.sum_range_one,←hgrid] using hb.2.1
  have hvE:v.toReal≤E₀:=by simpa only [Finset.sum_range_one,←hgrid] using hb.2.2
  have hmass':P B≤ENNReal.ofReal (Km*t^G.rank*t):=by
    apply (Q.palm_targetClockBand_mass_le (S.level:ℝ) measurableSet_Ioo
      (J:=Ioo (D.hi-3*t) D.hi) (fun m hm↦by
        change D.hi-(m.1.2-S.level)∈Ioc 0 (2*t) at hm
        constructor <;> linarith [hm.1,hm.2])).trans
    apply (hmass (3*t) ⟨by positivity,h3t⟩).trans_eq
    congr 1
    dsimp [Km]
    rw [mul_pow,pow_succ t G.rank]
    ring
  have hwidth:volume I≤ENNReal.ofReal (cap*t):=by
    rw [show I=Icc (ref-width) ref from rfl,Real.volume_Icc]
    apply ENNReal.ofReal_le_ofReal
    have h:width≤cap*t:=(oldPhysicalClockWindow_spec hcap ht).2.2.1
    linarith
  have hclock:∀clock∈I,D.hi-(clock-S.level)∈Icc t (4*t):=by
    intro clock hc
    have h:=D.originalOldPhysicalClockWindow_right_inward hε hcap n ell hell hc
    exact ⟨h.1,by linarith [h.2]⟩
  have hzero:∀m clock,m∉B∨clock∉I→
      D.originalSupportedOldPhysicalClockMask ε cap 1 n ell (m,clock)=0:=by
    intro m clock hz
    by_contra hn
    have hs:=D.originalSupportedRightOldPhysicalClockMask_focal_band_support ε cap n ell m clock hn
    rcases hz with hz|hz
    · exact hz ⟨hs.1.1,hs.1.2.le⟩
    · exact hz hs.2
  have hraw:=hfirst Q ht h4t hB (fun m hm↦hm) measurableSet_Icc hclock
    (D.originalSupportedOldPhysicalClockMask ε cap 1 n ell)
    (D.originalSupportedOldPhysicalClockMask_le_one hε cap 1 n ell) hzero
  have hsmall:=smallBirth_firstMoment_le_of_band_window_bounds (k:=G.rank)
    ht ht hcap.le hCfirst.le hKm.le hwidth hmass' hraw
  have hout:=firstMoment_energy_toReal_bound he hv'
    (show 0≤cap*Cfirst*Real.sqrt Km by positivity)
    (show 0≤t^(3/2:ℝ)*t^(((G.rank:ℝ)-3)/2) by positivity)
    (show 0≤t^(3/2:ℝ)*t^((G.rank:ℝ)/2) by positivity) hsmall
  have hpowe:t^(3/2:ℝ)*t^(((G.rank:ℝ)-3)/2)=t^((G.rank:ℝ)/2):=by
    rw [←Real.rpow_add ht];congr 1;ring
  have hpowv:t^(3/2:ℝ)*t^((G.rank:ℝ)/2)=t^(((G.rank:ℝ)+3)/2):=by
    rw [←Real.rpow_add ht];congr 1;ring
  have hfirstReal:palm.toReal≤cap*(Cfirst*Real.sqrt Km)*
      (t^((G.rank:ℝ)/2)*Real.sqrt e.toReal+t^(((G.rank:ℝ)+3)/2)*Real.sqrt v.toReal):=by
    simpa only [hpowe,hpowv,mul_assoc,palm,P,originalSupportedOldPhysicalClockWeight] using hout.2
  let T:=positiveMatrixNormalizer (focalResidueScale G t)
  let δ:=birthTrafficCoarseScale qdim t t
  let weighted:=∫⁻m,∫⁻clock:ℝ,
    ENNReal.ofReal ‖(Tᵀ)⁻¹*ᵥoriginalSeedPairMomentum S w m‖*
      D.originalSupportedOldPhysicalClockWeight ε cap 1 n ell (m,clock)∂volume∂P
  have hwraw:=hweighted Q ht ht1 ht h4tw hB (fun m hm↦hm) measurableSet_Icc hclock
    (D.originalSupportedOldPhysicalClockMask ε cap 1 n ell)
    (D.originalSupportedOldPhysicalClockMask_le_one hε cap 1 n ell) hzero
  rw [birthResidueScale_same_time_eq_focal G ht] at hwraw
  have hscaled:=birthLargePhase_moment_le_of_window_bound (q := finrank ℝ S.covector.ker) ht ht hcap.le hCweighted.le hwidth hwraw
  have hpE:t^2*t^(-2+1/(qdim:ℝ))=t^(1/(qdim:ℝ)):=by
    rw [←Real.rpow_two,←Real.rpow_add ht];congr 1;ring
  have hpV:t^2*t^(-1+1/(qdim:ℝ))=t^(1+1/(qdim:ℝ)):=by
    rw [←Real.rpow_two,←Real.rpow_add ht];congr 1;ring
  rw [hpE,hpV] at hscaled
  change ENNReal.ofReal δ⁻¹*weighted≤ENNReal.ofReal (cap*Cweighted)*
    (ENNReal.ofReal (t^(1/(qdim:ℝ)))*e+ENNReal.ofReal (t^(1+1/(qdim:ℝ)))*v) at hscaled
  have hEf:=ENNReal.mul_ne_top (a:=ENNReal.ofReal (t^(1/(qdim:ℝ)))) ENNReal.ofReal_ne_top he
  have hVf:=ENNReal.mul_ne_top (a:=ENNReal.ofReal (t^(1+1/(qdim:ℝ)))) ENNReal.ofReal_ne_top hv'
  have hfin:=ENNReal.mul_ne_top (a:=ENNReal.ofReal (cap*Cweighted)) ENNReal.ofReal_ne_top
    (ENNReal.add_ne_top.mpr ⟨hEf,hVf⟩)
  have hδ:0<δ:=birthTrafficCoarseScale_pos qdim ht ht
  have hwfin:weighted≠(∞:ℝ≥0∞):=
    (ENNReal.lt_top_of_mul_ne_top_right (ne_top_of_le_ne_top hfin hscaled)
      (ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr hδ))).ne
  have hwreal:=ENNReal.toReal_mono hfin hscaled
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (inv_nonneg.mpr hδ.le),
    ENNReal.toReal_mul,ENNReal.toReal_ofReal (mul_nonneg hcap.le hCweighted.le),
    ENNReal.toReal_add hEf hVf,ENNReal.toReal_mul,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (show 0≤t^(1/(qdim:ℝ)) by positivity),
    ENNReal.toReal_ofReal (show 0≤t^(1+1/(qdim:ℝ)) by positivity)] at hwreal
  exact ⟨he,hv',heE,hvE,hout.1,hfirstReal,hwfin,hwreal⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
