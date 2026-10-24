import OTSelector.Reconstruction.OriginalMinimizerDyadicTrafficBudget
import OTSelector.Reconstruction.FinslerOriginalBirthSameResidue
import OTSelector.Reconstruction.OriginalOldFocalLegs
import OTSelector.Reconstruction.OriginalMinimizerRightOldTrafficDensity
import OTSelector.Reconstruction.OriginalMinimizerRightCommonScaleTraffic

/-! Uniform old-focal phase intensity from the actual original population law.
The same residue enters the normalized compliance, its determinant loss, the
original density rate, and the physical frame. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Topology Matrix.Norms.Operator Classical BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
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
local notation "q" => finrank ℝ S.covector.ker

/-- The Borel actual original target extension has the true rank singularity
throughout its old-focal clock interval, with no bounded-leg hypothesis. -/
theorem original_right_old_targetPhaseLeg_det_rank_bound
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    {G : Matrix (Fin q) (Fin q) ℝ} (hG : G.PosSemidef)
    {geoε C t r : ℝ} (hgeo : geoε<D.hi-D.lo) (hC : 0≤C)
    (hupper : ∀s∈Ioo 0 geoε,
      (C•((s^2)⁻¹•G+1)-originalSeedKernel S w (D.hi-s)).PosSemidef)
    (ht : 0<t) (hr : r∈Icc t (2*t)) (h2t : 2*t<geoε) :
    let T:=positiveMatrixNormalizer (focalResidueScale G t)
    ∀a∈Ioo 0 (2*t),
      (1+T*D.targetPhaseLeg (D.hi-r) (D.hi-a+S.level)*Tᵀ).det ≤
        (2*C+2)^q*(2*t/a)^G.rank := by
  let T:=positiveMatrixNormalizer (focalResidueScale G t)
  have hcut:D.hi-r∈Ioo D.lo D.hi:=⟨by linarith [hr.2],by linarith [hr.1]⟩
  have hW : ContinuousOn (fun s ↦ originalSeedKernel S w (D.hi-s)) (Ioo 0 geoε):=
    (D.original_kernel_regular hF hw).1.comp (continuousOn_const.sub continuousOn_id)
      (fun s hs ↦ ⟨by linarith [hs.2],by linarith [hs.1]⟩)
  dsimp only
  intro a ha
  by_cases har:a<r
  · have hamem:D.hi-a+S.level∈D.targetPhaseClocks (D.hi-r):=by
      change D.hi-a+S.level-S.level∈Ioo (D.hi-r) D.hi
      constructor <;> linarith [ha.1]
    have heq : D.targetPhaseLeg (D.hi-r) (D.hi-a+S.level)=
        ∫s in a..r,originalSeedKernel S w (D.hi-s):=by
      rw [targetPhaseLeg,indicator_of_mem hamem]
      simpa only [add_sub_cancel_right] using
        (intervalIntegral.integral_comp_sub_left
          (fun s ↦ originalSeedKernel S w s) D.hi (a:=a) (b:=r)).symm
    rw [heq]
    simpa only [Fintype.card_fin] using oldFocal_compliance_det_le_rank_power hG hC ht ha.1 har.le hr
      (hr.2.trans_lt h2t) hW
      (fun s hs ↦ ((D.original_kernel_regular hF hw).2 _
        ⟨by linarith [hs.2],by linarith [hs.1]⟩).posSemidef) hupper
  · have hamem:D.hi-a+S.level∉D.targetPhaseClocks (D.hi-r):=by
      intro hx
      change D.hi-a+S.level-S.level∈Ioo (D.hi-r) D.hi at hx
      linarith [hx.1]
    rw [targetPhaseLeg,indicator_of_notMem hamem]
    simp only [Matrix.mul_zero,zero_mul,add_zero,Matrix.det_one]
    have hbase:1≤(2*t/a)^G.rank:=one_le_pow₀ ((le_div_iff₀ ha.1).mpr (by linarith [ha.2]))
    have hc:1≤(2*C+2)^q:=one_le_pow₀ (by linarith)
    exact one_le_mul_of_one_le_of_one_le hc hbase

/-- The unchanged original target determinant integral has the uniform
`t^(rank(G)+1)` bound. The original density rate and the full compliance
singularity use the same fixed residue before they cancel. -/
theorem exists_original_right_old_targetPhaseLeg_integral_rank_bound
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    {density : M→ℝ} {v : M→E→ℝ} (c : ℝ≥0∞)
    (hρ : Continuous density) (hρ0 : ∀x,0≤density x)
    (hv : ∀old,ContinuousOn (v old) (extChartAt 𝓘(ℝ,E) old).target)
    (hv0 : ∀old,∀y∈(extChartAt 𝓘(ℝ,E) old).target,0≤v old y)
    (hdensity : PopulationSeedClockDensity S w
      (ν.map (fun x:ℝ↦x-S.level)) density v c.toReal)
    {poleη : ℝ} (hη : 0<poleη) (hηspan : poleη<D.hi-D.lo)
    {G : Matrix (Fin q) (Fin q) ℝ} (hG : G.PosSemidef)
    {Rem : ℝ→Matrix (Fin q) (Fin q) ℝ}
    (hRem : ContinuousOn Rem (Ioo (-poleη) poleη))
    (hpole : ∀a∈Ioo 0 poleη,originalSeedKernel S w (D.hi-a)=(a^2)⁻¹•G+Rem a) :
    ∃ ε₀ A : ℝ,0<ε₀∧ε₀≤1∧ε₀<D.hi-D.lo∧0<A∧
      ∀ {t r : ℝ}, 0 < t → 2*t < ε₀ → r ∈ Icc t (2*t) →
      let T:=positiveMatrixNormalizer (focalResidueScale G t)
      (∫⁻a,ENNReal.ofReal ((D.targetPhaseClocks (D.hi-r)).indicator
        (fun a↦(1+T*D.targetPhaseLeg (D.hi-r) a*Tᵀ).det) a)∂ν)≤
          ENNReal.ofReal (A*t^(G.rank+1)) := by
  obtain ⟨geoε,hgeoε,_hgeoη,hgeospan,lower,C,_hlower,hC,hcomp⟩:=
    D.exists_original_right_birth_comparison_sameResidue hF hw hη hηspan hG hRem hpole
  obtain ⟨L,l,εden,K,_hlo,hl,hεden,hεdenh,hK,hlaw,hden⟩:=
    D.exists_original_right_density_residue_rate hF hw c hρ hρ0 hv hv0 hdensity hη
      (hRem.continuousAt (Ioo_mem_nhds (by linarith) hη)) hpole
  let ε₀:=min geoε (min εden 1)
  have hε₀:0<ε₀:=lt_min hgeoε (lt_min hεden zero_lt_one)
  have hε₀geo:ε₀≤geoε:=min_le_left _ _
  have hε₀den:ε₀≤εden:=(min_le_right _ _).trans (min_le_left _ _)
  have hε₀1:ε₀≤1:=(min_le_right _ _).trans (min_le_right _ _)
  let Ddet:=(2*C+2)^q
  have hDdet:0<Ddet:=by dsimp [Ddet];positivity
  refine ⟨ε₀,K*Ddet*2^(G.rank+1),hε₀,hε₀1,hε₀geo.trans_lt hgeospan,by positivity,?_⟩
  intro t r ht htε hr
  dsimp only
  let cut:=D.hi-r
  let T:=positiveMatrixNormalizer (focalResidueScale G t)
  let dabs:=fun b:ℝ↦(1+T*D.targetPhaseLeg cut b*Tᵀ).det
  let drel:=fun b:ℝ↦dabs (b+S.level)
  have hcut:cut∈Ioo D.lo D.hi:=⟨by dsimp [cut];linarith [hr.2,htε.trans_le hε₀geo,hgeospan],
    by dsimp [cut];linarith [hr.1]⟩
  have hdabs:Measurable dabs:=
    continuous_id.matrix_det.measurable.comp
      (measurable_const.add (D.measurable_normalizedTargetPhaseLeg hF hw T hcut))
  have hdrel:Measurable drel:=hdabs.comp (measurable_id.add_const _)
  have hpos:∀b∈Ioo (D.hi-2*t) D.hi,0≤drel b:=by
    intro b _hb
    exact (Matrix.PosDef.one.add_posSemidef
      (D.normalizedTargetPhaseLeg_posSemidef hF hw T hcut (b+S.level))).det_pos.le
  have hdet:∀a∈Ioo 0 (2*t),drel (D.hi-a)≤Ddet*(2*t/a)^G.rank:=by
    intro a ha
    exact D.original_right_old_targetPhaseLeg_det_rank_bound hF hw hG hgeospan hC.le
      (fun s hs↦(hcomp s hs).2) ht hr (htε.trans_le hε₀geo) a ha
  have hbound:=lintegral_right_oldFocal_det_le_of_density_rank_bound hlaw ht
    (show l≤D.hi-2*t by linarith [htε.trans_le hε₀den]) hK.le hDdet.le
    hdrel hpos
    (fun a ha↦hden a ⟨ha.1,ha.2.trans (htε.trans_le hε₀den)⟩) hdet
  have hcompare :
      (∫⁻b,ENNReal.ofReal ((D.targetPhaseClocks cut).indicator dabs b)∂ν)≤
        ∫⁻b in Ioo (D.hi-2*t) D.hi,ENNReal.ofReal (drel b)
          ∂ν.map (fun x:ℝ↦x-S.level):=by
    rw [←lintegral_indicator measurableSet_Ioo,
      lintegral_map (μ:=ν) (g:=fun x:ℝ↦x-S.level)
        (hdrel.ennreal_ofReal.indicator measurableSet_Ioo)
        (measurable_id.sub_const _)]
    apply lintegral_mono
    intro b
    by_cases hb:b∈D.targetPhaseClocks cut
    · have hb':b-S.level∈Ioo (D.hi-2*t) D.hi:=
        ⟨by dsimp [cut] at hb;linarith [hb.1,hr.2],hb.2⟩
      simp only [indicator_of_mem hb,indicator_of_mem hb']
      simp [drel]
    · simp only [indicator_of_notMem hb,ENNReal.ofReal_zero]
      exact bot_le
  calc
    _ ≤ ENNReal.ofReal (K*Ddet*(2*t)^(G.rank+1)):=hcompare.trans hbound
    _ = _:=by rw [mul_pow];congr 1;ring

/-- Full original old-target phase cells have a scale-independent true input
intensity. The original population density and physical Haar determinant cancel
using their common actual residue; the target leg may be unbounded. -/
theorem exists_original_right_old_commonScale_phaseCell_uniform_intensity
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels) (hq : 0<q)
    {density : M→ℝ} {v : M→E→ℝ} (c : ℝ≥0∞)
    (hρ : Continuous density) (hρ0 : ∀x,0≤density x)
    (hv : ∀old,ContinuousOn (v old) (extChartAt 𝓘(ℝ,E) old).target)
    (hv0 : ∀old,∀y∈(extChartAt 𝓘(ℝ,E) old).target,0≤v old y)
    (hdensity : PopulationSeedClockDensity S w
      (ν.map (fun x:ℝ↦x-S.level)) density v c.toReal)
    {poleη : ℝ} (hη : 0<poleη) (hηspan : poleη<D.hi-D.lo)
    {G : Matrix (Fin q) (Fin q) ℝ} (hG : G.PosSemidef)
    {Rem : ℝ→Matrix (Fin q) (Fin q) ℝ}
    (hRem : ContinuousOn Rem (Ioo (-poleη) poleη))
    (hpole : ∀a∈Ioo 0 poleη,originalSeedKernel S w (D.hi-a)=(a^2)⁻¹•G+Rem a) :
    ∃ ε₀ : ℝ,0<ε₀∧ε₀≤1∧ε₀<D.hi-D.lo∧
      ∀ Rcell : ℝ, ∃ Λ : ℝ, 0 < Λ ∧ ∀ {t r : ℝ}, 0 < t → 2*t < ε₀ → r ∈ Icc t (2*t) →
      let T:=positiveMatrixNormalizer (focalResidueScale G t)
      let cut:=D.hi-r
      let δ:=birthTrafficCoarseScale q t t
      ∀z₀ p₀,((volume:Measure (Fin q→ℝ)).prod ν)
        (D.commonScaleOriginalTargetPhaseCell T cut δ
          (D.targetPhaseClocks cut) z₀ p₀ Rcell)≤ENNReal.ofReal Λ := by
  let _ : IsProbabilityMeasure ν:=D.support.target.probability
  obtain ⟨ε₀,A,hε₀,hε₀1,hε₀span,hA,hint⟩:=
    D.exists_original_right_old_targetPhaseLeg_integral_rank_bound hF hw c hρ hρ0
      hv hv0 hdensity hη hηspan hG hRem hpole
  obtain ⟨Cf,hCf,hframe⟩:=exists_birthTrafficSpatialFrame_det_bound hG
    (by simpa only [Fintype.card_fin] using hq)
  refine ⟨ε₀,hε₀,hε₀1,hε₀span,?_⟩
  intro Rcell
  let ball:=Metric.closedBall (0:Fin q→ℝ) (phaseSourceCellRadius (Fin q) Rcell)
  let V:ℝ:=(volume ball).toReal
  have hV:0≤V:=ENNReal.toReal_nonneg
  have hVfin:volume ball≠(∞:ℝ≥0∞):=(isCompact_closedBall _ _).measure_ne_top
  have hVeq:volume ball=ENNReal.ofReal V:=(ENNReal.ofReal_toReal hVfin).symm
  refine ⟨Cf*V*A+1,by positivity,?_⟩
  intro t r ht htε hr
  dsimp only
  intro z₀ p₀
  let T:=positiveMatrixNormalizer (focalResidueScale G t)
  let cut:=D.hi-r
  let δ:=birthTrafficCoarseScale q t t
  let L:=birthTrafficSpatialFrame G t t
  have ht1:t≤1:=by linarith [htε.le.trans hε₀1]
  have hcut:cut∈Ioo D.lo D.hi:=⟨by dsimp [cut];linarith [hr.2,htε.trans_le hε₀span.le],
    by dsimp [cut];linarith [hr.1]⟩
  have hL:L=δ•T⁻¹:=by
    dsimp [L,birthTrafficSpatialFrame,T,δ]
    rw [birthResidueScale_same_time_eq_focal G ht]
    simp only [Fintype.card_fin]
  have hcoeff:|L.det| *V*(A*t^(G.rank+1))≤Cf*V*A:=by
    calc
      _ ≤ (Cf*(t^(G.rank+1))⁻¹)*V*(A*t^(G.rank+1)):=by
        gcongr
        exact hframe t t ht ht1 ht
      _ = _:=by field_simp
  have hbound:=hint ht htε hr
  change (∫⁻a,ENNReal.ofReal ((D.targetPhaseClocks cut).indicator
    (fun a↦(1+T*D.targetPhaseLeg cut a*Tᵀ).det) a)∂ν)≤
      ENNReal.ofReal (A*t^(G.rank+1)) at hbound
  have hcell := prod_volume_markedPhaseSourceCell
    (birthTrafficSpatialFrame_isUnit_det hG ht ht)
    (D.measurable_normalizedTargetPhaseLeg hF hw T hcut)
    (D.normalizedTargetPhaseLeg_posSemidef hF hw T hcut)
    (D.measurable_commonScaleOriginalTargetPhaseCenter hF hw T hcut δ z₀ p₀)
    (D.measurableSet_targetPhaseClocks cut) ν Rcell
  change ((volume:Measure (Fin q→ℝ)).prod ν)
    (markedPhaseSourceCell L _ _ _ _) = _ at hcell
  change ((volume:Measure (Fin q→ℝ)).prod ν)
    (markedPhaseSourceCell (δ•T⁻¹) (fun a↦T*D.targetPhaseLeg cut a*Tᵀ)
      (D.commonScaleOriginalTargetPhaseCenter T cut δ z₀ p₀)
      (D.targetPhaseClocks cut) Rcell)≤_
  rw [←hL]
  rw [hcell]
  change (ENNReal.ofReal |L.det| *volume ball)*_≤_
  rw [hVeq]
  calc
    _ ≤ (ENNReal.ofReal |L.det| *ENNReal.ofReal V)*
        ENNReal.ofReal (A*t^(G.rank+1)):=by gcongr
    _ = ENNReal.ofReal (|L.det| *V*(A*t^(G.rank+1))):=by
      rw [←ENNReal.ofReal_mul (abs_nonneg _),
        ←ENNReal.ofReal_mul (mul_nonneg (abs_nonneg _) hV)]
    _ ≤ ENNReal.ofReal (Cf*V*A):=ENNReal.ofReal_le_ofReal hcoeff
    _ ≤ _:=ENNReal.ofReal_le_ofReal (by linarith)

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
