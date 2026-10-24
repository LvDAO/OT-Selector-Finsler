import OTSelector.Reconstruction.OriginalMarkedPressureMarkChange
import OTSelector.Reconstruction.MarkedStationaryValueLegalDyadicComparison

/-! Fixed-box legal pressure continuity under actual original common-sampling
couplings. The full original independent Poisson clouds keep their positions,
counts and exact projected iid mark laws. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.style.haveILetI false

/-- The actual coupled-mark disagreement masses control the full finite-box
original legal pressure, with one fixed coarse repair constant. -/
theorem abs_legalMarkedPressure_projected_laws_sub_le
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableEq A] [MeasurableEq B]
    (q : ℕ) {range : Set ℝ} {gap : ℝ} (coarse : FiniteScalarBins range gap) (hgap : 0 < gap)
    (source : A → ℝ) (target : B → ℝ) (hs : Measurable source) (ht : Measurable target)
    (κS : Measure (A × A)) [IsProbabilityMeasure κS]
    (κT : Measure (B × B)) [IsProbabilityMeasure κT]
    (hsource : ∀ᵐ a ∂κS, source a.1 ∈ range ∧ source a.2 ∈ range)
    (hsep : ∀ᵐ p ∂κS.prod κT,
      gap ≤ |target p.2.1 - source p.1.1| ∧ gap ≤ |target p.2.2 - source p.1.2|)
    (r : ℝ≥0) {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    (kin : A → B → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (probe : A → B → ℝ) (hp : Measurable (Function.uncurry probe))
    (hpb : ∀ a b, |probe a b| ≤ G) (t : ℝ) :
    let α₀ := κS.map Prod.fst
    let α₁ := κS.map Prod.snd
    let β₀ := κT.map Prod.fst
    let β₁ := κT.map Prod.snd
    let _instα₀ : IsProbabilityMeasure α₀ := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
    let _instα₁ : IsProbabilityMeasure α₁ := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
    let _instβ₀ : IsProbabilityMeasure β₀ := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
    let _instβ₁ : IsProbabilityMeasure β₁ := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
    |legalMarkedPressure q source target α₀ β₀ r kin probe t -
      legalMarkedPressure q source target α₁ β₁ r kin probe t| ≤
      4 * ((coarse.count : ℝ) + 1) *
        ((r : ℝ) ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) * (r : ℝ) *
          ((κS {p | p.1 ≠ p.2}).toReal + (κT {p | p.1 ≠ p.2}).toReal) := by
  letI : IsProbabilityMeasure (κS.map Prod.fst) := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  letI : IsProbabilityMeasure (κS.map Prod.snd) := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  letI : IsProbabilityMeasure (κT.map Prod.fst) := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  letI : IsProbabilityMeasure (κT.map Prod.snd) := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  dsimp only
  rw [legalMarkedPressure_eq_pullback q κS κT (κS.map Prod.fst) (κT.map Prod.fst)
    measurable_fst measurable_fst rfl rfl hs ht r kin hk probe hp t,
    legalMarkedPressure_eq_pullback q κS κT (κS.map Prod.snd) (κT.map Prod.snd)
    measurable_snd measurable_snd rfl rfl hs ht r kin hk probe hp t]
  let kin₀ := fun (a : A × A) (b : B × B) ↦ kin a.1 b.1
  let kin₁ := fun (a : A × A) (b : B × B) ↦ kin a.2 b.2
  let probe₀ := fun (a : A × A) (b : B × B) ↦ probe a.1 b.1
  let probe₁ := fun (a : A × A) (b : B × B) ↦ probe a.2 b.2
  have hk₀ : Measurable (Function.uncurry (fun p : (A × A) × (B × B) ↦ kin₀ p.1 p.2)) := by
    change Measurable ((Function.uncurry (fun p : A × B ↦ kin p.1 p.2)) ∘
      (fun x : ((A × A) × (B × B)) × (Fin q → ℝ) ↦ ((x.1.1.1,x.1.2.1),x.2)))
    exact hk.comp (by fun_prop)
  have hk₁ : Measurable (Function.uncurry (fun p : (A × A) × (B × B) ↦ kin₁ p.1 p.2)) := by
    change Measurable ((Function.uncurry (fun p : A × B ↦ kin p.1 p.2)) ∘
      (fun x : ((A × A) × (B × B)) × (Fin q → ℝ) ↦ ((x.1.1.2,x.1.2.2),x.2)))
    exact hk.comp (by fun_prop)
  have hp₀ : Measurable (Function.uncurry probe₀) := by
    change Measurable ((Function.uncurry probe) ∘ (fun x : (A × A) × (B × B) ↦ (x.1.1,x.2.1)))
    exact hp.comp (by fun_prop)
  have hp₁ : Measurable (Function.uncurry probe₁) := by
    change Measurable ((Function.uncurry probe) ∘ (fun x : (A × A) × (B × B) ↦ (x.1.2,x.2.2)))
    exact hp.comp (by fun_prop)
  let V₀ := legalMarkedTilted q (source ∘ Prod.fst) (target ∘ Prod.fst) r kin₀ probe₀ t
  let V₁ := legalMarkedTilted q (source ∘ Prod.snd) (target ∘ Prod.snd) r kin₁ probe₁ t
  let P := twoMarkedCloudLaw q (A × A) (B × B) κS κT r
  have hi₀ : Integrable V₀ P := integrable_legalMarkedTilted q (hs.comp measurable_fst)
    (ht.comp measurable_fst) κS κT r hC hG hk₀ (fun a b v ↦ hkb a.1 b.1 v)
    hp₀ (fun a b ↦ hpb a.1 b.1) t
  have hi₁ : Integrable V₁ P := integrable_legalMarkedTilted q (hs.comp measurable_snd)
    (ht.comp measurable_snd) κS κT r hC hG hk₁ (fun a b v ↦ hkb a.2 b.2 v)
    hp₁ (fun a b ↦ hpb a.2 b.2) t
  have hiS : Integrable (fun sample ↦ (markedCloudMismatchCount q sample.1 : ℝ)) P :=
    (integrable_markedCloudMismatchCount q κS r).comp_fst (markedPoissonLaw q (B × B) κT r)
  have hiT : Integrable (fun sample ↦ (markedCloudMismatchCount q sample.2 : ℝ)) P :=
    (integrable_markedCloudMismatchCount q κT r).comp_snd (markedPoissonLaw q (A × A) κS r)
  have hmeanS : (∫ sample, (markedCloudMismatchCount q sample.1 : ℝ) ∂P) =
      (r : ℝ) * (κS {p | p.1 ≠ p.2}).toReal := by
    have h := integral_fun_fst (μ := markedPoissonLaw q (A × A) κS r)
      (ν := markedPoissonLaw q (B × B) κT r)
      (fun z ↦ (markedCloudMismatchCount q z : ℝ))
    change (∫ sample : TwoMarkedCloudSpace q (A × A) (B × B),
      (markedCloudMismatchCount q sample.1 : ℝ) ∂P) = _ at h
    simpa only [probReal_univ,one_smul,integral_markedCloudMismatchCount] using h
  have hmeanT : (∫ sample, (markedCloudMismatchCount q sample.2 : ℝ) ∂P) =
      (r : ℝ) * (κT {p | p.1 ≠ p.2}).toReal := by
    have h := integral_fun_snd (μ := markedPoissonLaw q (A × A) κS r)
      (ν := markedPoissonLaw q (B × B) κT r)
      (fun z ↦ (markedCloudMismatchCount q z : ℝ))
    change (∫ sample : TwoMarkedCloudSpace q (A × A) (B × B),
      (markedCloudMismatchCount q sample.2 : ℝ) ∂P) = _ at h
    simpa only [probReal_univ,one_smul,integral_markedCloudMismatchCount] using h
  let coefficient := 4 * ((coarse.count : ℝ) + 1) *
    ((r : ℝ) ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G)
  have hib : Integrable (fun sample ↦
      ((markedCloudMismatchCount q sample.1 : ℝ) + markedCloudMismatchCount q sample.2) * coefficient) P :=
    (hiS.add hiT).mul_const coefficient
  have hbound : ∀ᵐ sample ∂P, |V₀ sample - V₁ sample| ≤
      ((markedCloudMismatchCount q sample.1 : ℝ) + markedCloudMismatchCount q sample.2) * coefficient := by
    filter_upwards [ae_all_sourceMarks q κS κT r
      (fun a ↦ source a.1 ∈ range ∧ source a.2 ∈ range) hsource,
      ae_all_crossMarks q κS κT r (fun p ↦ gap ≤ |target p.2.1 - source p.1.1| ∧
        gap ≤ |target p.2.2 - source p.1.2|) hsep] with sample hS hsepCloud
    exact abs_legalMarkedTilted_coupled_marks_sub_le q coarse hgap source target r C G t
      r.coe_nonneg hC hG kin probe hkb hpb sample
      (fun i ↦ (hS i).1) (fun i ↦ (hS i).2)
      (fun i j ↦ (hsepCloud i j).1) (fun i j ↦ (hsepCloud i j).2)
  change |(∫ sample, V₀ sample ∂P) - ∫ sample, V₁ sample ∂P| ≤ _
  calc
    _ = |∫ sample, V₀ sample - V₁ sample ∂P| := by rw [integral_sub hi₀ hi₁]
    _ ≤ ∫ sample, |V₀ sample - V₁ sample| ∂P := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun sample ↦ V₀ sample - V₁ sample)
    _ ≤ ∫ sample, ((markedCloudMismatchCount q sample.1 : ℝ) + markedCloudMismatchCount q sample.2) *
        coefficient ∂P := integral_mono_ae (hi₀.sub hi₁).abs hib hbound
    _ = _ := by
      rw [integral_mul_const,integral_add hiS hiT,hmeanS,hmeanT]
      dsimp only [coefficient]
      ring

end OTSelector.Reconstruction
