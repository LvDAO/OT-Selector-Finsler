import OTSelector.Probability.WeakLscExpectation
import OTSelector.Reconstruction.MarkedStationaryValuePalmConditionalReadout
import OTSelector.Reconstruction.MarkedStationaryValuePalmRootedEnergy
import OTSelector.LinearAlgebra.Matrix.CompactPositiveQuadratic
import Mathlib.Topology.TietzeExtension

/-! Root-dependent nonnegative full-displacement energy passes through the
same actual joint weak law and its conditional paired-edge Palm. -/
open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped Topology ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false

section LocalIntegration
variable {W X : Type*} [TopologicalSpace W] [PolishSpace W]
  [MeasurableSpace W] [BorelSpace W]
  [TopologicalSpace X] [MeasurableSpace X] [T2Space X] [LocallyCompactSpace X]
  [BorelSpace X] [PseudoMetrizableSpace X] [SigmaCompactSpace X] [SecondCountableTopology X]
local instance taggedPalmLocalMeasurePolish : PolishSpace (LocalFiniteMeasure X) :=
  LocalFiniteMeasure.instPolishSpace

/-- An open joint set has lower-semicontinuous section mass when both the
parameter and its actual locally finite measure vary. -/
theorem lowerSemicontinuous_open_section_localMeasure
    {O : Set (W × X)} (hO : IsOpen O) :
    LowerSemicontinuous (fun p : W × LocalFiniteMeasure X ↦
      (p.2 : Measure X) {x | (p.1,x) ∈ O}) := by
  intro p r hr
  have hsection : IsOpen {x : X | (p.1,x) ∈ O} :=
    hO.preimage (continuous_const.prodMk continuous_id)
  obtain ⟨K,hKO,hK,hrK⟩ := hsection.exists_lt_isCompact hr
  have hprod : ({p.1} : Set W) ×ˢ K ⊆ O := by
    rintro ⟨w,x⟩ ⟨hw,hx⟩
    have hw' : w = p.1 := mem_singleton_iff.mp hw
    subst w
    exact hKO hx
  obtain ⟨V,T,hV,hT,hpV,hKT,hVT⟩ :=
    generalized_tube_lemma isCompact_singleton hK hO hprod
  have hroot : ∀ᶠ q : W × LocalFiniteMeasure X in 𝓝 p, q.1 ∈ V :=
    continuous_fst.continuousAt.eventually (hV.mem_nhds (hpV (mem_singleton _)))
  have hrT : r < (p.2 : Measure X) T := hrK.trans_le (measure_mono hKT)
  have hmass : ∀ᶠ q : W × LocalFiniteMeasure X in 𝓝 p, r < (q.2 : Measure X) T :=
    ((LocalFiniteMeasure.lowerSemicontinuous_measure_open hT).comp
      continuous_snd) p r hrT
  filter_upwards [hroot,hmass] with q hqV hqT
  exact hqT.trans_le (measure_mono (fun x hx ↦ hVT ⟨hqV,hx⟩))

/-- Layer cake and Fatou extend the open-section mass theorem to every
nonnegative real lower-semicontinuous parameter-dependent integrand. -/
theorem lowerSemicontinuous_lintegral_localMeasure_ofReal
    (F : W × X → ℝ) (hF : LowerSemicontinuous F) (hF0 : ∀ p, 0 ≤ F p) :
    LowerSemicontinuous (fun p : W × LocalFiniteMeasure X ↦
      ∫⁻ x, ENNReal.ofReal (F (p.1,x)) ∂(p.2 : Measure X)) := by
  have hslice (p : W × LocalFiniteMeasure X) :
      LowerSemicontinuous (fun x : X ↦ F (p.1,x)) :=
    hF.comp (continuous_const.prodMk continuous_id)
  have hc (p : W × LocalFiniteMeasure X) :
      (∫⁻ x, ENNReal.ofReal (F (p.1,x)) ∂(p.2 : Measure X)) =
        ∫⁻ t in Ioi (0 : ℝ), (p.2 : Measure X) {x | t < F (p.1,x)} :=
    lintegral_eq_lintegral_meas_lt _ (ae_of_all _ (fun x ↦ hF0 (p.1,x)))
      (hslice p).measurable.aemeasurable
  apply lowerSemicontinuous_iff_le_liminf.mpr
  intro p
  rw [hc]
  calc
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), (𝓝 p).liminf (fun q : W × LocalFiniteMeasure X ↦
        (q.2 : Measure X) {x | t < F (q.1,x)}) := by
      apply lintegral_mono
      intro t
      exact (lowerSemicontinuous_open_section_localMeasure
        (hF.isOpen_preimage t)).le_liminf p
    _ ≤ (𝓝 p).liminf (fun q : W × LocalFiniteMeasure X ↦
        ∫⁻ t in Ioi (0 : ℝ), (q.2 : Measure X) {x | t < F (q.1,x)}) := by
      apply lintegral_liminf_le
      intro q
      exact Antitone.measurable (fun s t hst ↦
        measure_mono (fun x hx ↦ lt_of_le_of_lt hst hx))
    _ = _ := by simp_rw [← hc]

/-- The full ENNReal readout is lower semicontinuous, including infinite
energies; no boundedness or compact support is required. -/
theorem lowerSemicontinuous_lintegral_localMeasure
    (F : W × X → ℝ≥0∞) (hF : LowerSemicontinuous F) :
    LowerSemicontinuous (fun p : W × LocalFiniteMeasure X ↦
      ∫⁻ x, F (p.1,x) ∂(p.2 : Measure X)) := by
  let trunc : ℕ → W × X → ℝ≥0∞ := fun n p ↦ min (n : ℝ≥0∞) (F p)
  let realTrunc : ℕ → W × X → ℝ := fun n p ↦
    ENNReal.truncateToReal (n : ℝ≥0∞) (F p)
  have hfinite (n : ℕ) (p : W × X) : min (n : ℝ≥0∞) (F p) ≠ ∞ :=
    ne_top_of_le_ne_top (by finiteness) (min_le_left _ _)
  have hcast (n : ℕ) (p : W × X) : ENNReal.ofReal (realTrunc n p) = trunc n p :=
    ENNReal.ofReal_toReal (hfinite n p)
  have hreal (n : ℕ) : LowerSemicontinuous (realTrunc n) :=
    (ENNReal.continuous_truncateToReal (by finiteness)).comp_lowerSemicontinuous hF
      (ENNReal.monotone_truncateToReal (by finiteness))
  have htrunc (n : ℕ) : Measurable (trunc n) := measurable_const.min hF.measurable
  have hmono : Monotone trunc := fun m n hmn p ↦
    min_le_min (by exact_mod_cast hmn) le_rfl
  have hsup (p : W × X) : (⨆ n, trunc n p) = F p := by
    change (⨆ n : ℕ, (n : ℝ≥0∞) ⊓ F p) = F p
    rw [← iSup_inf_eq,ENNReal.iSup_natCast,top_inf_eq]
  have heq : (fun p : W × LocalFiniteMeasure X ↦ ∫⁻ x, F (p.1,x) ∂(p.2 : Measure X)) =
      fun p ↦ ⨆ n, ∫⁻ x, ENNReal.ofReal (realTrunc n (p.1,x)) ∂(p.2 : Measure X) := by
    funext p
    simp_rw [hcast]
    rw [← lintegral_iSup]
    · exact lintegral_congr (fun x ↦ (hsup (p.1,x)).symm)
    · intro n
      exact (htrunc n).comp (measurable_const.prodMk measurable_id)
    · intro m n hmn x
      exact hmono hmn (p.1,x)
  rw [heq]
  exact lowerSemicontinuous_iSup fun n ↦
    lowerSemicontinuous_lintegral_localMeasure_ofReal (realTrunc n) (hreal n)
      (fun _ ↦ ENNReal.truncateToReal_nonneg)
end LocalIntegration

section TaggedPalm
variable {W ι : Type*} [TopologicalSpace W] [PolishSpace W]
  [MeasurableSpace W] [BorelSpace W] [Fintype ι]
local instance taggedPalmPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace
local instance taggedPalmPlanNonempty : Nonempty
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := ⟨⟨0,inferInstance⟩⟩
set_option quotPrecheck false
local notation "PairScene" => CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)

/-- The actual full-target source-window energy, retaining its original tag,
both scalar clocks and complete physical displacement. -/
def taggedPhysicalSceneSourceWindowEnergy (U : Set (ι → ℝ))
    (F : W × PhysicalPairPalmMark ι → ℝ≥0∞) (p : W × PairScene) : ℝ≥0∞ :=
  ∫⁻ e in {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.1.1 ∈ U},
    F (p.1,(physicalPairAnchor e).2) ∂(p.2.1 : Measure _)

/-- Parameter-dependent nonnegative LSC energy is an LSC observable of the
actual tagged plan for every open source window. -/
theorem lowerSemicontinuous_taggedPhysicalSceneSourceWindowEnergy
    {U : Set (ι → ℝ)} (hU : IsOpen U)
    (F : W × PhysicalPairPalmMark ι → ℝ≥0∞) (hF : LowerSemicontinuous F) :
    LowerSemicontinuous (taggedPhysicalSceneSourceWindowEnergy U F) := by
  let O : Set (W × (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := {p | p.2.1.1 ∈ U}
  let H : W × (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) → ℝ≥0∞ :=
    fun p ↦ F (p.1,(physicalPairAnchor p.2).2)
  have hO : IsOpen O := hU.preimage continuous_snd.fst.fst
  have hH : LowerSemicontinuous H := hF.comp
    (continuous_fst.prodMk (continuous_physicalPairAnchor.snd.comp continuous_snd))
  have hind : LowerSemicontinuous (O.indicator H) := by
    intro p r hr
    by_cases hp : p ∈ O
    · have hr' : r < H p := by simpa only [indicator_of_mem hp] using hr
      filter_upwards [hO.mem_nhds hp,hH p r hr'] with q hq hqr
      simpa only [indicator_of_mem hq] using hqr
    · simp only [indicator_of_notMem hp] at hr
      exact (not_lt_of_ge bot_le hr).elim
  have hproj : Continuous (fun p : W × PairScene ↦ (p.1,p.2.1)) :=
    continuous_fst.prodMk continuous_snd.fst
  have hread := (lowerSemicontinuous_lintegral_localMeasure (O.indicator H) hind).comp hproj
  convert hread using 1
  funext p
  change (∫⁻ e in {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.1.1 ∈ U},
    F (p.1,(physicalPairAnchor e).2) ∂(p.2.1 : Measure _)) =
      ∫⁻ e, O.indicator H (p.1,e) ∂(p.2.1 : Measure _)
  have hUE : MeasurableSet {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.1.1 ∈ U} :=
    hU.measurableSet.preimage measurable_fst.fst
  rw [← lintegral_indicator hUE]
  apply lintegral_congr
  intro e
  by_cases he : e.1.1 ∈ U <;> simp [O,H,he]

/-- Full tagged open-source-window energy obeys weak lower semicontinuity,
without a moment bound or any assumed readout limit. -/
theorem lintegral_tagged_sourceWindow_le_liminf_of_weak
    (P : ℕ → ProbabilityMeasure (W × PairScene)) {Q : ProbabilityMeasure (W × PairScene)}
    (hweak : Tendsto P atTop (𝓝 Q))
    {U : Set (ι → ℝ)} (hU : IsOpen U)
    (F : W × PhysicalPairPalmMark ι → ℝ≥0∞) (hF : LowerSemicontinuous F) :
    (∫⁻ p, taggedPhysicalSceneSourceWindowEnergy U F p ∂(Q : Measure _)) ≤
      liminf (fun n ↦ ∫⁻ p, taggedPhysicalSceneSourceWindowEnergy U F p
        ∂(P n : Measure _)) atTop :=
  lintegral_lsc_le_liminf_of_weak_tendsto Q P hweak _
    (lowerSemicontinuous_taggedPhysicalSceneSourceWindowEnergy hU F hF)

/-- The same conditional paired-edge Palm retains every original root-dependent
LSC nonnegative energy. Any open neighborhood of the physical unit source cube
bounds it by the actual finite tagged source-window energies. -/
theorem lintegral_conditional_cubePalm_le_liminf_tagged_sourceWindow
    (P : ℕ → ProbabilityMeasure (W × PairScene)) {Q : ProbabilityMeasure (W × PairScene)}
    (hweak : Tendsto P atTop (𝓝 Q))
    {U : Set (ι → ℝ)} (hU : IsOpen U) (hsub : palmUnitCube ι ⊆ U)
    (F : W × PhysicalPairPalmMark ι → ℝ≥0∞) (hF : LowerSemicontinuous F) :
    (∫⁻ w, ∫⁻ m, F (w,m)
      ∂cubePalm ι (physicalScenePairCampbell ((Q : Measure (W × PairScene)).condKernel w))
      ∂(Q : Measure (W × PairScene)).fst) ≤
      liminf (fun n ↦ ∫⁻ p, taggedPhysicalSceneSourceWindowEnergy U F p
        ∂(P n : Measure _)) atTop := by
  rw [lintegral_conditional_cubePalm_physicalScenePairCampbell
    (Q : Measure (W × PairScene)) hF.measurable]
  apply le_trans _ (lintegral_tagged_sourceWindow_le_liminf_of_weak P hweak hU F hF)
  apply lintegral_mono
  intro p
  exact lintegral_mono_set (fun e he ↦ hsub he)

/-- Shrinking genuine open neighborhoods removes their source-volume factor
and preserves exactly the same original root-dependent energy budget. -/
theorem lintegral_conditional_cubePalm_le_of_tagged_energy_density_bound
    (P : ℕ → ProbabilityMeasure (W × PairScene)) {Q : ProbabilityMeasure (W × PairScene)}
    (hweak : Tendsto P atTop (𝓝 Q))
    (F : W × PhysicalPairPalmMark ι → ℝ≥0∞) (hF : LowerSemicontinuous F)
    (E : ℝ≥0∞)
    (hbound : ∀ (U : Set (ι → ℝ)), IsOpen U → ∀ n,
      (∫⁻ p, taggedPhysicalSceneSourceWindowEnergy U F p ∂(P n : Measure _)) ≤ volume U * E) :
    (∫⁻ w, ∫⁻ m, F (w,m)
      ∂cubePalm ι (physicalScenePairCampbell ((Q : Measure (W × PairScene)).condKernel w))
      ∂(Q : Measure (W × PairScene)).fst) ≤ E := by
  let eps (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  let center : ι → ℝ := fun _ ↦ 1 / 2
  let U (n : ℕ) := Metric.ball center (1 / 2 + eps n)
  have heps (n) : 0 < eps n := by dsimp [eps]; positivity
  have hrad (n) : 0 < 1 / 2 + eps n := by positivity
  have hsub (n) : palmUnitCube ι ⊆ U n := by
    intro x hx
    have hnorm : ‖x - center‖ ≤ (1 / 2 : ℝ) := by
      apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)).mpr
      intro i
      change |x i - 1 / 2| ≤ 1 / 2
      exact abs_le.mpr ⟨by linarith [hx.1 i],by linarith [hx.2 i]⟩
    change dist x center < 1 / 2 + eps n
    rw [dist_eq_norm]
    exact hnorm.trans_lt (lt_add_of_pos_right _ (heps n))
  have hb (n) : (∫⁻ w, ∫⁻ m, F (w,m)
      ∂cubePalm ι (physicalScenePairCampbell ((Q : Measure (W × PairScene)).condKernel w))
      ∂(Q : Measure (W × PairScene)).fst) ≤ volume (U n) * E := by
    apply (lintegral_conditional_cubePalm_le_liminf_tagged_sourceWindow P hweak
      Metric.isOpen_ball (hsub n) F hF).trans
    exact liminf_le_of_frequently_le' (.of_forall (hbound (U n) Metric.isOpen_ball))
  have hepst : Tendsto eps atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hreal : Tendsto (fun n ↦ (2 * (1 / 2 + eps n)) ^ Fintype.card ι) atTop (𝓝 (1 : ℝ)) := by
    have hc : Tendsto (fun _ : ℕ ↦ (1 / 2 : ℝ)) atTop (𝓝 (1 / 2 : ℝ)) := tendsto_const_nhds
    convert ((hc.add hepst).const_mul 2).pow (Fintype.card ι) using 1
    norm_num
  have hvol : Tendsto (fun n ↦ volume (U n)) atTop (𝓝 (1 : ℝ≥0∞)) := by
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
    simpa only [ENNReal.ofReal_one] using h.congr' (.of_forall (fun n ↦
      (Real.volume_pi_ball center (hrad n)).symm))
  have hlim := ENNReal.Tendsto.mul_const (b := E) hvol (Or.inl one_ne_zero)
  simpa only [one_mul] using ge_of_tendsto hlim (.of_forall hb)

/-- The actual tagged conditional Palm is bounded by the liminf of its own
original finite energy budgets, allowing a deterministic initial sample cutoff. -/
theorem lintegral_conditional_cubePalm_le_liminf_tagged_energy_density
    (P : ℕ → ProbabilityMeasure (W × PairScene)) {Q : ProbabilityMeasure (W × PairScene)}
    (hweak : Tendsto P atTop (𝓝 Q))
    (F : W × PhysicalPairPalmMark ι → ℝ≥0∞) (hF : LowerSemicontinuous F)
    (energy : ℕ → ℝ≥0∞)
    (hbound : ∀ᶠ n in atTop, ∀ (U : Set (ι → ℝ)), IsOpen U →
      (∫⁻ p, taggedPhysicalSceneSourceWindowEnergy U F p ∂(P n : Measure _)) ≤
        volume U * energy n) :
    (∫⁻ w, ∫⁻ m, F (w,m)
      ∂cubePalm ι (physicalScenePairCampbell ((Q : Measure (W × PairScene)).condKernel w))
      ∂(Q : Measure (W × PairScene)).fst) ≤ liminf energy atTop := by
  by_contra hnot
  obtain ⟨B,hB,hbelow⟩ := exists_between (lt_of_not_ge hnot)
  have hfreq : ∃ᶠ n in atTop, energy n < B := frequently_lt_of_liminf_lt (h := hB)
  obtain ⟨φ,hφ,hφB⟩ := extraction_of_frequently_atTop (hfreq.and_eventually hbound)
  have hupper := lintegral_conditional_cubePalm_le_of_tagged_energy_density_bound
    (fun n ↦ P (φ n)) (hweak.comp hφ.tendsto_atTop) F hF B (by
      intro U hU n
      exact ((hφB n).2 U hU).trans
        (mul_le_mul_of_nonneg_left (hφB n).1.le bot_le))
  exact hbelow.not_ge hupper
end TaggedPalm

section OriginalPhysical
variable {W ι M : Type*} [TopologicalSpace W] [PolishSpace W]
  [MeasurableSpace W] [BorelSpace W] [Fintype ι] [MeasurableSpace M]
local instance taggedPhysicalEnergyPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace
local instance taggedPhysicalEnergyPlanNonempty : Nonempty
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := ⟨⟨0,inferInstance⟩⟩
set_option quotPrecheck false
local notation "PairScene" => CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)

/-- Literal original finite plans and their unchanged root measure give the
root-dependent Palm liminf bound by their own physical window readouts. The
original N prefactor and complete displacement appear explicitly in the result. -/
theorem lintegral_conditional_cubePalm_le_liminf_original_tagged_sourceWindow
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (Penv : ∀ n, Measure (Ω n))
    (Γplus Γminus : ∀ n, Ω n → Measure (M × M))
    [∀ n ξ, IsFiniteMeasure (Γplus n ξ)] [∀ n ξ, IsFiniteMeasure (Γminus n ξ)]
    (hplus : ∀ n, Measurable (Γplus n)) (hminus : ∀ n, Measurable (Γminus n))
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    (u : M → ℝ) (hu : Measurable u) (N : ℕ → ℝ) (D : ℕ → Set (ι → ℝ))
    (tag : ℕ → (ι → ℝ) → W) (htag : ∀ n, Measurable (tag n))
    (P : ℕ → ProbabilityMeasure (W × PairScene)) {Q : ProbabilityMeasure (W × PairScene)}
    (hlaw : ∀ n, (P n : Measure (W × PairScene)) =
      ((Penv n).prod (cavityRootMeasure volume (D n) (N n))).map
        (fun p ↦ (tag n p.2,physicalSceneRootedLocalScene
          (Γplus n) (Γminus n) (coord n) u (N n) p)))
    (hweak : Tendsto P atTop (𝓝 Q))
    {U : Set (ι → ℝ)} (hU : IsOpen U) (hsub : palmUnitCube ι ⊆ U)
    (F : W × PhysicalPairPalmMark ι → ℝ≥0∞) (hF : LowerSemicontinuous F) :
    (∫⁻ w, ∫⁻ m, F (w,m)
      ∂cubePalm ι (physicalScenePairCampbell ((Q : Measure (W × PairScene)).condKernel w))
      ∂(Q : Measure (W × PairScene)).fst) ≤
      liminf (fun n ↦ ∫⁻ p, ENNReal.ofReal (N n) *
        cavityRootWindowReadout (Γplus n p.1) (fun e ↦ coord n e.1)
          (fun e ↦ F (tag n p.2,((u e.1,u e.2),coord n e.2 - coord n e.1))) U p.2
        ∂((Penv n).prod (cavityRootMeasure volume (D n) (N n)))) atTop := by
  have heq (n : ℕ) :
      (∫⁻ p, taggedPhysicalSceneSourceWindowEnergy U F p ∂(P n : Measure _)) =
        ∫⁻ p, ENNReal.ofReal (N n) *
          cavityRootWindowReadout (Γplus n p.1) (fun e ↦ coord n e.1)
            (fun e ↦ F (tag n p.2,((u e.1,u e.2),coord n e.2 - coord n e.1))) U p.2
          ∂((Penv n).prod (cavityRootMeasure volume (D n) (N n))) := by
    have hobs : Measurable (fun p : Ω n × (ι → ℝ) ↦
        (tag n p.2,physicalSceneRootedLocalScene
          (Γplus n) (Γminus n) (coord n) u (N n) p)) :=
      ((htag n).comp measurable_snd).prodMk
        (measurable_physicalSceneRootedLocalScene (Γplus n) (Γminus n)
          (hplus n) (hminus n) (coord n) (hcoord n) u hu (N n))
    rw [hlaw n,lintegral_map
      (lowerSemicontinuous_taggedPhysicalSceneSourceWindowEnergy hU F hF).measurable hobs]
    apply lintegral_congr
    intro p
    exact setLIntegral_physicalSceneRootedPlan_energy
      (Γplus n p.1) (coord n) (hcoord n) u hu (N n) p.2
      (hF.measurable.comp (measurable_const.prodMk measurable_id)) U hU.measurableSet
  simpa only [heq] using
    lintegral_conditional_cubePalm_le_liminf_tagged_sourceWindow P hweak hU hsub F hF
end OriginalPhysical

section MatrixConsumer
variable {W ι : Type*} [TopologicalSpace W] [PolishSpace W]
  [MeasurableSpace W] [BorelSpace W] [Fintype ι]

/-- A root-dependent matrix and bounded probe continuous only on their actual
closed root/clock carrier admit a nonnegative continuous shifted extension.
Every coefficient and the full transverse vector are retained on that carrier. -/
theorem exists_continuous_nonnegative_tagged_matrix_shifted_energy
    {K : Set (W × (ℝ × ℝ))} (hK : IsClosed K)
    (matrix : W × (ℝ × ℝ) → Matrix ι ι ℝ) (hmatrix : ContinuousOn matrix K)
    (hkn : ∀ p ∈ K, ∀ v, 0 ≤ matrixQuadratic (matrix p) v)
    (g : W × (ℝ × ℝ) → ℝ) (hg : ContinuousOn g K)
    {G : ℝ} (hgb : ∀ p ∈ K, |g p| ≤ G) (t : ℝ) :
    ∃ F : C(W × PhysicalPairPalmMark ι,ℝ), (∀ p, 0 ≤ F p) ∧
      ∀ p : W × PhysicalPairPalmMark ι, (p.1,p.2.1) ∈ K →
        F p = matrixQuadratic (matrix (p.1,p.2.1)) p.2.2 +
          t * g (p.1,p.2.1) + |t| * G := by
  let T : Set (W × PhysicalPairPalmMark ι) := {p | (p.1,p.2.1) ∈ K}
  let H : W × PhysicalPairPalmMark ι → ℝ := fun p ↦
    matrixQuadratic (matrix (p.1,p.2.1)) p.2.2 + t * g (p.1,p.2.1) + |t| * G
  have hT : IsClosed T := hK.preimage (continuous_fst.prodMk continuous_snd.fst)
  have hparam : Continuous (fun p : W × PhysicalPairPalmMark ι ↦ (p.1,p.2.1)) :=
    continuous_fst.prodMk continuous_snd.fst
  have hm : ContinuousOn (fun p : W × PhysicalPairPalmMark ι ↦ matrix (p.1,p.2.1)) T :=
    hmatrix.comp hparam.continuousOn (fun p hp ↦ hp)
  have hg' : ContinuousOn (fun p : W × PhysicalPairPalmMark ι ↦ g (p.1,p.2.1)) T :=
    hg.comp hparam.continuousOn (fun p hp ↦ hp)
  have hH : ContinuousOn H T :=
    ((continuous_matrixQuadratic.comp_continuousOn
      (hm.prodMk continuous_snd.snd.continuousOn)).add
        (continuousOn_const.mul hg')).add continuousOn_const
  let H' : C(T,ℝ) := ⟨fun p ↦ H p,continuousOn_iff_continuous_domRestrict.mp hH⟩
  obtain ⟨E,hE⟩ := H'.exists_restrict_eq hT
  let F : C(W × PhysicalPairPalmMark ι,ℝ) :=
    ⟨fun p ↦ max (E p) 0,E.continuous.max continuous_const⟩
  refine ⟨F,fun _ ↦ le_max_right _ _,fun p hp ↦ ?_⟩
  have hEp : E p = H p := congrArg (fun f : C(T,ℝ) ↦ f ⟨p,hp⟩) hE
  have habs : |t * g (p.1,p.2.1)| ≤ |t| * G := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hgb _ hp) (abs_nonneg t)
  have hnonneg : 0 ≤ H p := by
    dsimp [H]
    linarith [(abs_le.mp habs).1,hkn _ hp p.2.2]
  change max (E p) 0 = _
  rw [hEp,max_eq_left hnonneg]
end MatrixConsumer

end OTSelector.Reconstruction
