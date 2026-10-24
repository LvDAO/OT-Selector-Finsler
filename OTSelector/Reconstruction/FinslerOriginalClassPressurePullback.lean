import OTSelector.Reconstruction.FinslerOriginalLegalPressureCoefficientStability
import OTSelector.Reconstruction.MarkedStationaryValueLegalPoissonMap

/-! Original continuous marks and their exact finite-class images describe the
same cloud pressure whenever the legal graph and costs depend only on those
classes. Positions, counts and original iid sampling remain unchanged. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

variable {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace C] [MeasurableSpace D]
  [Fintype C] [Fintype D] [DecidableEq D]
  [MeasurableSingletonClass C] [MeasurableSingletonClass D]

omit [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
  [Fintype C] [Fintype D] [DecidableEq D]
  [MeasurableSingletonClass C] [MeasurableSingletonClass D] in
/-- Class observation preserves the literal original finite legal graph. -/
theorem finiteClassLegalGraph_mapMarkedCloud (q m n : ℕ)
    (f : A → C) (g : B → D) (allowed : C → D → Prop)
    (ω : TwoMarkedCloudSpace q A B) :
    finiteClassLegalGraph q m n allowed (mapMarkedCloud f ω.1,mapMarkedCloud g ω.2) =
      finiteClassLegalGraph q m n (fun a b ↦ allowed (f a) (g b)) ω := rfl

omit [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
  [Fintype C] [Fintype D] [DecidableEq D]
  [MeasurableSingletonClass C] [MeasurableSingletonClass D] in
/-- The exact class graph and costs commute with the original mark readout. -/
theorem finiteClassLegalTilted_mapMarkedCloud (q : ℕ)
    (f : A → C) (g : B → D) (allowed : C → D → Prop) (r : ℝ)
    (kin : C → D → (Fin q → ℝ) → ℝ) (probe : C → D → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q A B) :
    finiteClassLegalTilted q allowed r kin probe t (mapMarkedCloud f ω.1,mapMarkedCloud g ω.2) =
      finiteClassLegalTilted q (fun a b ↦ allowed (f a) (g b)) r
        (fun a b ↦ kin (f a) (g b)) (fun a b ↦ probe (f a) (g b)) t ω := rfl

/-- The finite-class pressure equals its pullback to the actual original
continuous mark law, using the exact original full-cloud pushforward. The
finite nested mask is only encoded, with no change of original physical clocks. -/
theorem finiteClassLegalPressure_eq_pullback (q : ℕ)
    (allowed : C → D → Prop)
    (hnested : ∀ c c', (∀ d, allowed c d → allowed c' d) ∨
      (∀ d, allowed c' d → allowed c d))
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (γ : Measure C) [IsProbabilityMeasure γ] (δ : Measure D) [IsProbabilityMeasure δ]
    {f : A → C} {g : B → D} (hf : Measurable f) (hg : Measurable g)
    (hγ : α.map f = γ) (hδ : β.map g = δ)
    (r : ℝ≥0) (kin : C → D → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : C × D ↦ kin p.1 p.2)))
    (probe : C → D → ℝ) (t : ℝ) :
    finiteClassLegalPressure q allowed γ δ r kin probe t =
      finiteClassLegalPressure q (fun a b ↦ allowed (f a) (g b)) α β r
        (fun a b ↦ kin (f a) (g b)) (fun a b ↦ probe (f a) (g b)) t := by
  obtain ⟨source,target,hcode,_⟩ :=
    OTSelector.FiniteRelation.exists_strict_clocks_of_nested_relation allowed hnested
  rw [finiteClassLegalPressure_eq_clock q allowed source target hcode]
  rw [legalMarkedPressure_eq_pullback q α β γ δ hf hg hγ hδ
    (measurable_of_countable source) (measurable_of_countable target) r kin hk probe
    (measurable_of_countable (Function.uncurry probe)) t]
  exact (finiteClassLegalPressure_eq_clock q (fun a b ↦ allowed (f a) (g b))
    (source ∘ f) (target ∘ g) (fun a b ↦ hcode (f a) (g b)) α β r
    (fun a b ↦ kin (f a) (g b)) (fun a b ↦ probe (f a) (g b)) t).symm

/-- Spatial normalization does not change the exact original class pullback. -/
theorem finiteClassLegalScalePressure_eq_pullback (q : ℕ)
    (allowed : C → D → Prop)
    (hnested : ∀ c c', (∀ d, allowed c d → allowed c' d) ∨
      (∀ d, allowed c' d → allowed c d))
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (γ : Measure C) [IsProbabilityMeasure γ] (δ : Measure D) [IsProbabilityMeasure δ]
    {f : A → C} {g : B → D} (hf : Measurable f) (hg : Measurable g)
    (hγ : α.map f = γ) (hδ : β.map g = δ)
    (kin : C → D → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : C × D ↦ kin p.1 p.2)))
    (probe : C → D → ℝ) (R t : ℝ) :
    finiteClassLegalScalePressure q allowed γ δ kin probe R t =
      finiteClassLegalScalePressure q (fun a b ↦ allowed (f a) (g b)) α β
        (fun a b ↦ kin (f a) (g b)) (fun a b ↦ probe (f a) (g b)) R t := by
  by_cases hR : 0 < R
  · simp only [finiteClassLegalScalePressure,hR,↓reduceIte]
    rw [finiteClassLegalPressure_eq_pullback q allowed hnested α β γ δ hf hg hγ hδ _ kin hk probe t]
  · simp only [finiteClassLegalScalePressure,hR,↓reduceIte]

/-- Actual original continuous marks inherit the original finite-class
thermodynamic limit exactly, with no replacement by independent auxiliary marks. -/
theorem tendsto_finiteClassLegalScalePressure_pullback (q : ℕ)
    (allowed : C → D → Prop)
    (hnested : ∀ c c', (∀ d, allowed c d → allowed c' d) ∨
      (∀ d, allowed c' d → allowed c d))
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (γ : Measure C) [IsProbabilityMeasure γ] (δ : Measure D) [IsProbabilityMeasure δ]
    {f : A → C} {g : B → D} (hf : Measurable f) (hg : Measurable g)
    (hγ : α.map f = γ) (hδ : β.map g = δ)
    (kin : C → D → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : C × D ↦ kin p.1 p.2)))
    (probe : C → D → ℝ) {p t : ℝ}
    (hp : Tendsto (fun R ↦ finiteClassLegalScalePressure q allowed γ δ kin probe R t)
      atTop (𝓝 p)) :
    Tendsto (fun R ↦ finiteClassLegalScalePressure q (fun a b ↦ allowed (f a) (g b)) α β
      (fun a b ↦ kin (f a) (g b)) (fun a b ↦ probe (f a) (g b)) R t) atTop (𝓝 p) := by
  simpa only [finiteClassLegalScalePressure_eq_pullback q allowed hnested α β γ δ hf hg hγ hδ
    kin hk probe] using hp


/-- Original continuous mark spaces have a true legal pressure limit under a
finite observed nested mask, even when the kinetic coefficient and physical
probe retain their full original continuous mark dependence. The exact mask
clocks, compact range and repair inputs are produced internally. -/
theorem exists_finiteClassLegalScalePressure_pullback_limit_of_nested
    (q : ℕ) (hq : 4 < q) (allowed : C → D → Prop)
    (hnested : ∀ c c', (∀ d, allowed c d → allowed c' d) ∨
      (∀ d, allowed c' d → allowed c d))
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    {f : A → C} {g : B → D} (hf : Measurable f) (hg : Measurable g)
    (π : Measure (A × B)) [IsFiniteMeasure π] (hπ : Vlasov.IsCoupling π α β)
    (hlegal : ∀ᵐ p ∂π, allowed (f p.1) (g p.2))
    {K G : ℝ} (hK : 0 ≤ K) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkn : ∀ a b v, 0 ≤ kin a b v)
    (hkb : ∀ a b v, |kin a b v| ≤ K * ∑ l, v l ^ 2)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l ↦ c * v l) = c ^ 2 * kin a b v)
    {probe : A → B → ℝ} (hp : Measurable (Function.uncurry probe))
    (hpb : ∀ a b, |probe a b| ≤ G) :
    ∃ p : ℝ → ℝ,
      (∀ t, Tendsto (fun R ↦ finiteClassLegalScalePressure q
        (fun a b ↦ allowed (f a) (g b)) α β kin probe R t) atTop (𝓝 (p t))) ∧
      ConcaveOn ℝ univ p ∧ LipschitzWith ⟨G,hG⟩ p := by
  obtain ⟨source,target,hcode,hsep,hsource,htarget⟩ :=
    OTSelector.FiniteRelation.exists_strict_clocks_of_nested_relation allowed hnested
  let I : Set ℝ := Icc (-((Fintype.card D : ℝ) + 1)) 1
  obtain ⟨bins⟩ := exists_finiteScalarBins (show IsCompact I from isCompact_Icc)
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hI : ∀ᵐ p ∂π, source (f p.1) ∈ I ∧ target (g p.2) ∈ I :=
    .of_forall fun p ↦ ⟨hsource (f p.1),htarget (g p.2)⟩
  have hgap : ∀ᵐ p ∂π, (1 / 2 : ℝ) ≤ target (g p.2) - source (f p.1) := by
    filter_upwards [hlegal] with p hp
    simpa only [abs_of_pos (sub_pos.mpr ((hcode _ _).mp hp))] using hsep (f p.1) (g p.2)
  obtain ⟨p,hpt,hconc,hlip⟩ := exists_legalMarkedScalePressure_limit_of_scalarBins bins
    (by norm_num) (show MeasurableSet I from measurableSet_Icc)
    (source ∘ f) (target ∘ g) ((measurable_of_countable source).comp hf)
    ((measurable_of_countable target).comp hg) π α β hπ hI hgap
    (.of_forall fun p ↦ hsep (f p.1) (g p.2)) q hq hK hG hk hkn hkb hhom hp hpb
  refine ⟨p,?_,hconc,hlip⟩
  intro t
  have heq : (fun R ↦ finiteClassLegalScalePressure q (fun a b ↦ allowed (f a) (g b))
      α β kin probe R t) =
      fun R ↦ legalMarkedScalePressure q (source ∘ f) (target ∘ g) α β kin probe R t :=
    funext fun R ↦ finiteClassLegalScalePressure_eq_clock q (fun a b ↦ allowed (f a) (g b))
      (source ∘ f) (target ∘ g) (fun a b ↦ hcode (f a) (g b)) α β kin probe R t
  rw [heq]
  exact hpt t

/-- The same original continuous masked model is integrable at every finite
intensity. Ordinary quadratic and probe growth suffice; no new moment or
geometric assumption is introduced by observing the finite classes. -/
theorem integrable_finiteClassLegalTilted_pullback_mask
    (q : ℕ) (allowed : C → D → Prop)
    (hnested : ∀ c c', (∀ d, allowed c d → allowed c' d) ∨
      (∀ d, allowed c' d → allowed c d))
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    {f : A → C} {g : B → D} (hf : Measurable f) (hg : Measurable g)
    (r : ℝ≥0) {K G : ℝ} (hK : 0 ≤ K) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b, allowed (f a) (g b) → ∀ v, |kin a b v| ≤ K * ∑ l, v l ^ 2)
    (probe : A → B → ℝ) (hp : Measurable (Function.uncurry probe))
    (hpb : ∀ a b, allowed (f a) (g b) → |probe a b| ≤ G) (t : ℝ) :
    Integrable (finiteClassLegalTilted q (fun a b ↦ allowed (f a) (g b)) r kin probe t)
      (twoMarkedCloudLaw q A B α β r) := by
  obtain ⟨source,target,hcode,_⟩ :=
    OTSelector.FiniteRelation.exists_strict_clocks_of_nested_relation allowed hnested
  have heq : finiteClassLegalTilted q (fun a b ↦ allowed (f a) (g b)) r kin probe t =
      legalMarkedTilted q (source ∘ f) (target ∘ g) r kin probe t :=
    funext (finiteClassLegalTilted_eq_clock q (fun a b ↦ allowed (f a) (g b))
      (source ∘ f) (target ∘ g) (fun a b ↦ hcode (f a) (g b)) r kin probe t)
  rw [heq]
  exact integrable_legalMarkedTilted_of_forward q
    ((measurable_of_countable source).comp hf) ((measurable_of_countable target).comp hg)
    α β r hK hG hk (fun a b hab ↦ hkb a b ((hcode _ _).mpr hab))
    hp
    (fun a b hab ↦ hpb a b ((hcode _ _).mpr hab)) t

end OTSelector.Reconstruction
