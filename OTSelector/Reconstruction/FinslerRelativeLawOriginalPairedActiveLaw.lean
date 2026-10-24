import OTSelector.Reconstruction.FinslerConcreteUpperClassPressure
import OTSelector.Reconstruction.FinslerRelativeLawOriginalMarkedCellPrefix
import LeanPool.QuasiBorelSpaces.MeasureTheory.Option

/-! Null-safe Bernoulli spatial laws for the same original finite class population. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- Restoring a finite law by its own literal mass remains exact for zero mass. -/
theorem mass_smul_normalizedFiniteLaw_eq {W : Type*} [MeasurableSpace W]
    (m : Measure W) [IsFiniteMeasure m] : m univ • normalizedFiniteLaw m = m := by
  by_cases hm : m = 0
  · simp [hm,normalizedFiniteLaw]
  have hmass : m univ ≠ 0 := Measure.measure_univ_ne_zero.mpr hm
  have hr : 0 < m.real univ := ENNReal.toReal_pos hmass (measure_ne_top _ _)
  rw [normalizedFiniteLaw,← Measure.coe_nnreal_smul,smul_smul]
  have hc : m univ * (↑((m.real univ)⁻¹.toNNReal) : ℝ≥0∞) = 1 := by
    apply (ENNReal.toReal_eq_toReal_iff'
      (ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.coe_ne_top) ENNReal.one_ne_top).mp
    rw [ENNReal.toReal_mul,ENNReal.coe_toReal,
      Real.coe_toNNReal _ (inv_nonneg.mpr hr.le)]
    exact mul_inv_cancel₀ hr.ne'
  rw [hc,one_smul]

/-- Inactive mass together with the exact unnormalized retained spatial mass.
The product of the original spatial mass and class mass is the activity rate. -/
def originalRetainedSpatialLaw {W : Type*} [MeasurableSpace W]
    (m : Measure W) (classMass : ℝ≥0∞) : Measure (Option W) :=
  (1 - m univ * classMass) • Measure.dirac none + classMass • m.map some

theorem originalRetainedSpatialLaw_probability {W : Type*} [MeasurableSpace W]
    (m : Measure W) [IsFiniteMeasure m] (classMass : ℝ≥0∞)
    (hp : m univ * classMass ≤ 1) : IsProbabilityMeasure (originalRetainedSpatialLaw m classMass) := by
  constructor
  simp only [originalRetainedSpatialLaw,Measure.add_apply,Measure.smul_apply,
    Measure.map_apply MeasureTheory.Option.measurable_some MeasurableSet.univ,
    preimage_univ,Measure.dirac_apply_of_mem (mem_univ _),smul_eq_mul,mul_one]
  simpa only [mul_comm classMass] using tsub_add_cancel_of_le hp

/-- The requested normalized Bernoulli description is equal to the same raw
law, also when the original spatial cell is null. -/
theorem originalRetainedSpatialLaw_eq_bernoulli {W : Type*} [MeasurableSpace W]
    (m : Measure W) [IsFiniteMeasure m] (classMass : ℝ≥0∞) :
    originalRetainedSpatialLaw m classMass =
      (1 - m univ * classMass) • Measure.dirac none +
        (m univ * classMass) • (normalizedFiniteLaw m).map some := by
  unfold originalRetainedSpatialLaw
  congr 1
  rw [← Measure.map_smul,← Measure.map_smul]
  congr 1
  rw [show m univ * classMass = classMass * m univ by exact mul_comm _ _,
    mul_smul,mass_smul_normalizedFiniteLaw_eq]

/-- Read only the source class of the shared latent class pair. -/
def pairedActiveSourceRead {W I J : Type*} (p : Option W × (I × J)) : Option (W × I) :=
  p.1.map fun w ↦ (w,p.2.1)

/-- Read only the target class of the same shared latent class pair. -/
def pairedActiveTargetRead {W I J : Type*} (p : Option W × (I × J)) : Option (W × J) :=
  p.1.map fun w ↦ (w,p.2.2)

theorem measurable_pairedActiveSourceRead {W I J : Type*}
    [MeasurableSpace W] [MeasurableSpace I] [MeasurableSpace J]
    [Countable I] [Countable J] [MeasurableSingletonClass I] [MeasurableSingletonClass J] :
    Measurable (pairedActiveSourceRead (W := W) (I := I) (J := J)) := by
  apply measurable_from_prod_countable_left
  intro ij
  have heq : (fun x : Option W ↦ pairedActiveSourceRead (x,ij)) =
      (fun x : Option W ↦ x.elim none (fun w ↦ some (w,ij.1))) := by
    funext x
    cases x <;> rfl
  rw [heq]
  exact MeasureTheory.Option.measurable_elim none
    (MeasureTheory.Option.measurable_some.comp
      (show Measurable (fun w : W ↦ (w,ij.1)) from measurable_id.prodMk measurable_const))

theorem measurable_pairedActiveTargetRead {W I J : Type*}
    [MeasurableSpace W] [MeasurableSpace I] [MeasurableSpace J]
    [Countable I] [Countable J] [MeasurableSingletonClass I] [MeasurableSingletonClass J] :
    Measurable (pairedActiveTargetRead (W := W) (I := I) (J := J)) := by
  apply measurable_from_prod_countable_left
  intro ij
  have heq : (fun x : Option W ↦ pairedActiveTargetRead (x,ij)) =
      (fun x : Option W ↦ x.elim none (fun w ↦ some (w,ij.2))) := by
    funext x
    cases x <;> rfl
  rw [heq]
  exact MeasureTheory.Option.measurable_elim none
    (MeasureTheory.Option.measurable_some.comp
      (show Measurable (fun w : W ↦ (w,ij.2)) from measurable_id.prodMk measurable_const))

/-- The source readout of the whole latent product keeps its exact retained
spatial/class submeasure; inactive points become the one absent observation. -/
theorem originalRetainedSpatialLaw_source_map {W I J : Type*}
    [MeasurableSpace W] [MeasurableSpace I] [MeasurableSpace J]
    [Countable I] [Countable J] [MeasurableSingletonClass I] [MeasurableSingletonClass J]
    (m : Measure W) [IsFiniteMeasure m] (classMass : ℝ≥0∞)
    (π : Measure (I × J)) [IsProbabilityMeasure π] :
    ((originalRetainedSpatialLaw m classMass).prod π).map pairedActiveSourceRead =
      (1 - m univ * classMass) • Measure.dirac none +
        classMass • (m.prod (π.map Prod.fst)).map some := by
  have hr := measurable_pairedActiveSourceRead (W := W) (I := I) (J := J)
  have hn : ((Measure.dirac (none : Option W)).prod π).map pairedActiveSourceRead =
      Measure.dirac none := by
    rw [Measure.dirac_prod,Measure.map_map hr measurable_prodMk_left]
    change π.map (fun _ ↦ (none : Option (W × I))) = _
    simp [Measure.map_const]
  have hs : ((m.map some).prod π).map pairedActiveSourceRead =
      (m.prod (π.map Prod.fst)).map some := by
    calc
      _ = ((m.prod π).map (Prod.map some id)).map pairedActiveSourceRead := by
        congr 1
        simpa only [Measure.map_id] using
          Measure.map_prod_map m π MeasureTheory.Option.measurable_some measurable_id
      _ = (m.prod π).map (fun p ↦ some (p.1,p.2.1)) := by
        rw [Measure.map_map hr (MeasureTheory.Option.measurable_some.prodMap measurable_id)]
        rfl
      _ = ((m.prod π).map (Prod.map id Prod.fst)).map some := by
        rw [Measure.map_map MeasureTheory.Option.measurable_some (measurable_id.prodMap measurable_fst)]
        rfl
      _ = (m.prod (π.map Prod.fst)).map some := by
        rw [← Measure.map_prod_map m π measurable_id measurable_fst,Measure.map_id]
  rw [originalRetainedSpatialLaw,Measure.add_prod,Measure.prod_smul_left,Measure.prod_smul_left,
    Measure.map_add _ _ hr,Measure.map_smul,Measure.map_smul,hn,hs]

/-- The target readout of the whole latent product keeps its exact retained
spatial/class submeasure; inactive points become the one absent observation. -/
theorem originalRetainedSpatialLaw_target_map {W I J : Type*}
    [MeasurableSpace W] [MeasurableSpace I] [MeasurableSpace J]
    [Countable I] [Countable J] [MeasurableSingletonClass I] [MeasurableSingletonClass J]
    (m : Measure W) [IsFiniteMeasure m] (classMass : ℝ≥0∞)
    (π : Measure (I × J)) [IsProbabilityMeasure π] :
    ((originalRetainedSpatialLaw m classMass).prod π).map pairedActiveTargetRead =
      (1 - m univ * classMass) • Measure.dirac none +
        classMass • (m.prod (π.map Prod.snd)).map some := by
  have hr := measurable_pairedActiveTargetRead (W := W) (I := I) (J := J)
  have hn : ((Measure.dirac (none : Option W)).prod π).map pairedActiveTargetRead =
      Measure.dirac none := by
    rw [Measure.dirac_prod,Measure.map_map hr measurable_prodMk_left]
    change π.map (fun _ ↦ (none : Option (W × J))) = _
    simp [Measure.map_const]
  have hs : ((m.map some).prod π).map pairedActiveTargetRead =
      (m.prod (π.map Prod.snd)).map some := by
    calc
      _ = ((m.prod π).map (Prod.map some id)).map pairedActiveTargetRead := by
        congr 1
        simpa only [Measure.map_id] using
          Measure.map_prod_map m π MeasureTheory.Option.measurable_some measurable_id
      _ = (m.prod π).map (fun p ↦ some (p.1,p.2.2)) := by
        rw [Measure.map_map hr (MeasureTheory.Option.measurable_some.prodMap measurable_id)]
        rfl
      _ = ((m.prod π).map (Prod.map id Prod.snd)).map some := by
        rw [Measure.map_map MeasureTheory.Option.measurable_some (measurable_id.prodMap measurable_snd)]
        rfl
      _ = (m.prod (π.map Prod.snd)).map some := by
        rw [← Measure.map_prod_map m π measurable_id measurable_snd,Measure.map_id]
  rw [originalRetainedSpatialLaw,Measure.add_prod,Measure.prod_smul_left,Measure.prod_smul_left,
    Measure.map_add _ _ hr,Measure.map_smul,Measure.map_smul,hn,hs]

/-- A whole probability sample read through a fixed activity event keeps the
literal unnormalized observed submeasure; all inactive points read `none`. -/
theorem map_gated_original_observation
    {X W : Type*} [MeasurableSpace X] [MeasurableSpace W]
    (P : Measure X) [IsProbabilityMeasure P] {E : Set X} (hE : MeasurableSet E)
    (f : X → W) (hf : Measurable f) :
    P.map (fun x ↦ if x ∈ E then some (f x) else none) =
      (1 - P E) • Measure.dirac none + ((P.restrict E).map f).map some := by
  classical
  let read := fun x ↦ if x ∈ E then some (f x) else none
  have hr : Measurable read := (MeasureTheory.Option.measurable_some.comp hf).ite hE measurable_const
  have hyes : (P.restrict E).map read = ((P.restrict E).map f).map some := by
    rw [Measure.map_map MeasureTheory.Option.measurable_some hf]
    apply Measure.map_congr
    filter_upwards [ae_restrict_mem hE] with x hx
    simp [read,hx]
  have hno : (P.restrict Eᶜ).map read = P Eᶜ • Measure.dirac none := by
    calc
      _ = (P.restrict Eᶜ).map (fun _ ↦ (none : Option W)) := by
        apply Measure.map_congr
        filter_upwards [ae_restrict_mem hE.compl] with x hx
        simp [read,show x ∉ E from hx]
      _ = _ := by rw [Measure.map_const,Measure.restrict_apply_univ]
  calc
    P.map read = (P.restrict E + P.restrict Eᶜ).map read := by
      rw [Measure.restrict_add_restrict_compl hE]
    _ = (P.restrict E).map read + (P.restrict Eᶜ).map read := Measure.map_add _ _ hr
    _ = _ := by
      rw [hyes,hno,measure_compl hE (measure_ne_top _ _),measure_univ,add_comm]

/-- The shared normalized class pair restores the literal original source
submeasure after activity; zero spatial mass requires no fallback law. -/
theorem originalRetainedSpatialLaw_clockClass_source_map {W I J : Type*}
    [MeasurableSpace W] [MeasurableSpace I] [MeasurableSpace J] [Fintype I] [Fintype J]
    [MeasurableSingletonClass I] [MeasurableSingletonClass J]
    (m : Measure W) [IsFiniteMeasure m] (P₀ : I → J → ℝ)
    (hP₀ : ∀ i j, 0 ≤ P₀ i j) (hmass : 0 < ∑ i, ∑ j, P₀ i j) :
    ((originalRetainedSpatialLaw m ((clockClassPairMeasure P₀) univ)).prod
      (clockClassJointProbability P₀ hP₀ hmass : Measure (I × J))).map pairedActiveSourceRead =
      (1 - m univ * (clockClassPairMeasure P₀) univ) • Measure.dirac none +
        (m.prod ((clockClassPairMeasure P₀).map Prod.fst)).map some := by
  let π : Measure (I × J) := clockClassJointProbability P₀ hP₀ hmass
  have hrestore : (clockClassPairMeasure P₀) univ • (π.map Prod.fst) =
      (clockClassPairMeasure P₀).map Prod.fst := by
    rw [← Measure.map_smul]
    exact congrArg (fun ρ ↦ ρ.map Prod.fst) (mass_smul_normalizedFiniteLaw_eq (clockClassPairMeasure P₀))
  rw [originalRetainedSpatialLaw_source_map]
  congr 1
  rw [← Measure.map_smul,← Measure.prod_smul_right,hrestore]

/-- The target observes the other marginal of precisely the same latent class
pair, with its literal original unnormalized retained spatial mass. -/
theorem originalRetainedSpatialLaw_clockClass_target_map {W I J : Type*}
    [MeasurableSpace W] [MeasurableSpace I] [MeasurableSpace J] [Fintype I] [Fintype J]
    [MeasurableSingletonClass I] [MeasurableSingletonClass J]
    (m : Measure W) [IsFiniteMeasure m] (P₀ : I → J → ℝ)
    (hP₀ : ∀ i j, 0 ≤ P₀ i j) (hmass : 0 < ∑ i, ∑ j, P₀ i j) :
    ((originalRetainedSpatialLaw m ((clockClassPairMeasure P₀) univ)).prod
      (clockClassJointProbability P₀ hP₀ hmass : Measure (I × J))).map pairedActiveTargetRead =
      (1 - m univ * (clockClassPairMeasure P₀) univ) • Measure.dirac none +
        (m.prod ((clockClassPairMeasure P₀).map Prod.snd)).map some := by
  let π : Measure (I × J) := clockClassJointProbability P₀ hP₀ hmass
  have hrestore : (clockClassPairMeasure P₀) univ • (π.map Prod.snd) =
      (clockClassPairMeasure P₀).map Prod.snd := by
    rw [← Measure.map_smul]
    exact congrArg (fun ρ ↦ ρ.map Prod.snd) (mass_smul_normalizedFiniteLaw_eq (clockClassPairMeasure P₀))
  rw [originalRetainedSpatialLaw_target_map]
  congr 1
  rw [← Measure.map_smul,← Measure.prod_smul_right,hrestore]

end OTSelector.Reconstruction
