import OTSelector.Reconstruction.OriginalIIDConditionalLegalCandidate
import OTSelector.Reconstruction.OriginalIIDWholeCoreConditionalMatching
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputLaplaceFactorization
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalCountingMeasureSum
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryDilationPoisson
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryReserveCore

/-!
# Immutable colors on the same actual two-input conditional law

Color zero records the whole original source input and color one the whole
original target input. The original plan pair, clocks and multiplicities stay
in the same joint scene, including when scalar clock supports overlap.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported BoundedContinuousFunction BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000

local instance originalColoredCandidateColorMetric : MetricSpace (Fin 2) :=
  TopologicalSpace.metrizableSpaceMetric (Fin 2)
local instance originalColoredCandidateInputPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure ((Fin q → ℝ) × ℝ)) := LocalFiniteMeasure.instPolishSpace
local instance originalColoredCandidateColoredPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance originalColoredCandidatePlanPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- The literal whole two-color input measure, with immutable finite tags. -/
def originalColoredInputs (q : ℕ)
    (p : LocalFiniteMeasure (LegalMarkedPhysicalPoint q) ×
      LocalFiniteMeasure (LegalMarkedPhysicalPoint q)) :
    LocalFiniteMeasure (LegalColoredInputPoint q) :=
  ⟨(p.1 : Measure (LegalMarkedPhysicalPoint q)).prod (Measure.dirac (0 : Fin 2)) +
    (p.2 : Measure (LegalMarkedPhysicalPoint q)).prod (Measure.dirac (1 : Fin 2)), ⟨by
      intro K hK
      rw [Measure.add_apply]
      exact ENNReal.add_lt_top.mpr ⟨hK.measure_lt_top,hK.measure_lt_top⟩⟩⟩

/-- A colored compact test is exactly its two original color slice tests. -/
theorem testIntegral_originalColoredInputs (q : ℕ)
    (p : LocalFiniteMeasure (LegalMarkedPhysicalPoint q) ×
      LocalFiniteMeasure (LegalMarkedPhysicalPoint q))
    (F : C_c(LegalColoredInputPoint q, ℝ)) :
    LocalFiniteMeasure.testIntegral (originalColoredInputs q p) F =
      LocalFiniteMeasure.testIntegral p.1 (legalColoredInputTestSlice q F 0) +
        LocalFiniteMeasure.testIntegral p.2 (legalColoredInputTestSlice q F 1) := by
  have hi (μ : LocalFiniteMeasure (LegalMarkedPhysicalPoint q)) (c : Fin 2) :
      (∫ x, F x ∂(μ : Measure (LegalMarkedPhysicalPoint q)).prod (Measure.dirac c)) =
        LocalFiniteMeasure.testIntegral μ (legalColoredInputTestSlice q F c) := by
    rw [Measure.prod_dirac]
    exact integral_map (f := fun x : LegalColoredInputPoint q ↦ F x)
      (show Measurable (fun x : LegalMarkedPhysicalPoint q ↦ (x,c)) from
        measurable_id.prodMk measurable_const).aemeasurable F.continuous.aestronglyMeasurable
  change (∫ x, F x ∂((p.1 : Measure (LegalMarkedPhysicalPoint q)).prod (Measure.dirac (0 : Fin 2)) +
    (p.2 : Measure (LegalMarkedPhysicalPoint q)).prod (Measure.dirac (1 : Fin 2)))) = _
  rw [integral_add_measure F.integrable F.integrable,hi,hi]

theorem continuous_originalColoredInputs (q : ℕ) : Continuous (originalColoredInputs q) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro F
  change Continuous (fun p ↦ LocalFiniteMeasure.testIntegral (originalColoredInputs q p) F)
  simp_rw [testIntegral_originalColoredInputs]
  exact ((LocalFiniteMeasure.continuous_testIntegral _).comp continuous_fst).add
    ((LocalFiniteMeasure.continuous_testIntegral _).comp continuous_snd)

/-- Recovering an immutable color returns precisely the original whole input. -/
theorem legalInputColorMeasure_originalColoredInputs (q : ℕ)
    (p : LocalFiniteMeasure (LegalMarkedPhysicalPoint q) ×
      LocalFiniteMeasure (LegalMarkedPhysicalPoint q)) (c : Fin 2) :
    legalInputColorMeasure q (originalColoredInputs q p) c =
      if c = 0 then (p.1 : Measure (LegalMarkedPhysicalPoint q)) else (p.2 : Measure (LegalMarkedPhysicalPoint q)) := by
  ext B hB
  let μ : Measure (LegalMarkedPhysicalPoint q) := p.1
  let ν : Measure (LegalMarkedPhysicalPoint q) := p.2
  let E : Set (LegalColoredInputPoint q) := Prod.fst ⁻¹' B ∩ {x | x.2 = c}
  have hE : MeasurableSet E :=
    (hB.preimage measurable_fst).inter (measurable_snd (measurableSet_singleton c))
  rw [legalInputColorMeasure,Measure.map_apply measurable_fst hB,
    Measure.restrict_apply (hB.preimage measurable_fst)]
  change (μ.prod (Measure.dirac (0 : Fin 2)) + ν.prod (Measure.dirac (1 : Fin 2))) E =
    (if c = 0 then μ else ν) B
  rw [Measure.add_apply,Measure.prod_dirac,Measure.prod_dirac,
    Measure.map_apply (μ := μ) (f := fun x ↦ (x,(0 : Fin 2)))
      (measurable_id.prodMk measurable_const) hE,
    Measure.map_apply (μ := ν) (f := fun x ↦ (x,(1 : Fin 2)))
      (measurable_id.prodMk measurable_const) hE]
  fin_cases c <;> simp [E,Set.preimage]

/-- Literal source and target tags commute with any point homeomorphism. -/
theorem originalColoredInputs_mapHomeomorph (q : ℕ)
    (e : LegalMarkedPhysicalPoint q ≃ₜ LegalMarkedPhysicalPoint q)
    (p : LocalFiniteMeasure (LegalMarkedPhysicalPoint q) ×
      LocalFiniteMeasure (LegalMarkedPhysicalPoint q)) :
    localFiniteMapHomeomorph (e.prodCongr (Homeomorph.refl (Fin 2))) (originalColoredInputs q p) =
      originalColoredInputs q (localFiniteMapHomeomorph e p.1,localFiniteMapHomeomorph e p.2) := by
  have he (μ : Measure (LegalMarkedPhysicalPoint q)) [SFinite μ] (c : Fin 2) :
      (μ.prod (Measure.dirac c)).map (e.prodCongr (Homeomorph.refl (Fin 2))) =
        (μ.map e).prod (Measure.dirac c) := by
    rw [Measure.prod_dirac,Measure.prod_dirac]
    have htag : Measurable (fun x : LegalMarkedPhysicalPoint q ↦ (x,c)) :=
      measurable_id.prodMk measurable_const
    calc
      _ = μ.map ((e.prodCongr (Homeomorph.refl (Fin 2))) ∘ (fun x ↦ (x,c))) :=
        Measure.map_map (e.prodCongr (Homeomorph.refl (Fin 2))).continuous.measurable htag
      _ = μ.map ((fun x ↦ (x,c)) ∘ e) := rfl
      _ = _ := (Measure.map_map htag e.continuous.measurable).symm
  apply Subtype.ext
  change (((p.1 : Measure (LegalMarkedPhysicalPoint q)).prod (Measure.dirac (0 : Fin 2)) +
    (p.2 : Measure (LegalMarkedPhysicalPoint q)).prod (Measure.dirac (1 : Fin 2))).map
      (e.prodCongr (Homeomorph.refl (Fin 2)))) = _
  rw [Measure.map_add _ _ (e.prodCongr (Homeomorph.refl (Fin 2))).continuous.measurable,he,he]
  rfl

/-- The same original pair of plans and both inputs in the existing legal carrier. -/
def originalColoredScene (q : ℕ) (s : OriginalIIDMaskedMacroInputScene (Fin q)) :
    LegalMarkedOptimalInputScene q := (s.1,originalColoredInputs q s.2)

theorem continuous_originalColoredScene (q : ℕ) : Continuous (originalColoredScene q) :=
  continuous_fst.prodMk ((continuous_originalColoredInputs q).comp continuous_snd)

/-- The conversion keeps both actual original plans and reroots every original input. -/
theorem originalColoredScene_reroot (q : ℕ) (v : Fin q → ℝ)
    (s : OriginalIIDMaskedMacroInputScene (Fin q)) :
    originalColoredScene q (originalIIDMaskedMacroInputSceneReroot v s) =
      legalMarkedInputSceneReroot q v (originalColoredScene q s) := by
  apply Prod.ext
  · rfl
  · exact (originalColoredInputs_mapHomeomorph q (physicalScenePointReroot v) s.2).symm

section IntegerTags
variable {X Y : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X]
  [MetricSpace Y] [ProperSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]

/-- Every finite multiset of actual points has its literal integer carrier. -/
theorem original_exists_configuration_multiset_dirac (base : Y) (m : Multiset Y) :
    ∃ c : LocalConfiguration base, LocalConfiguration.countingMeasure c =
      (m.map Measure.dirac).sum := by
  induction m using Multiset.induction_on with
  | empty =>
    refine ⟨LocalConfiguration.ofTuple base (fun i : Fin 0 ↦ Fin.elim0 i),?_⟩
    simp [LocalConfiguration.countingMeasure_ofTuple]
  | @cons y m ih =>
    obtain ⟨c,hc⟩ := ih
    obtain ⟨d,hd⟩ := isLegalCountingMeasure_add base
      (⟨Measure.dirac y,inferInstance⟩ : LocalFiniteMeasure Y)
      (LocalConfiguration.toLocalFiniteMeasure c)
      (isLegalCountingMeasure_dirac base y) ⟨c,rfl⟩
    refine ⟨d,?_⟩
    have he := congrArg Subtype.val hd
    change LocalConfiguration.countingMeasure d =
      Measure.dirac y + LocalConfiguration.countingMeasure c at he
    simpa only [hc,Multiset.map_cons,Multiset.sum_cons] using he

/-- A locally finite measurable push of an original integer measure stays
integer. Its actual finite shell pieces construct the target carrier. -/
theorem original_isLegalCountingMeasure_map
    (baseX : X) (baseY : Y) (μ : LocalFiniteMeasure X)
    (hμ : IsLegalCountingMeasure baseX μ) (f : X → Y) (hf : Measurable f)
    (hfin : IsFiniteMeasureOnCompacts ((μ : Measure X).map f)) :
    IsLegalCountingMeasure baseY ⟨(μ : Measure X).map f,hfin⟩ := by
  obtain ⟨c,rfl⟩ := hμ
  choose d hd using fun n ↦ original_exists_configuration_multiset_dirac
    baseY ((c n).map (fun x ↦ f x.val))
  let A := fun n ↦ LocalConfiguration.toLocalFiniteMeasure (d n)
  have hsum : Measure.sum (fun n ↦ (A n : Measure Y)) =
      (LocalConfiguration.countingMeasure c).map f := by
    rw [LocalConfiguration.countingMeasure,Measure.map_sum hf.aemeasurable]
    congr 1
    funext n
    change LocalConfiguration.countingMeasure (d n) =
      (LocalConfiguration.shellMeasure c n).map f
    rw [hd n]
    have hmap := map_multiset_sum (Measure.mapₗ f)
      ((c n).map (fun x ↦ Measure.dirac x.val))
    simp only [Measure.mapₗ_apply_of_measurable hf,Multiset.map_map,
      Function.comp_def,Measure.map_dirac' hf] at hmap
    simpa only [Multiset.map_map,Function.comp_def,LocalConfiguration.shellMeasure] using hmap.symm
  have hSumFinite : IsFiniteMeasureOnCompacts (Measure.sum (fun n ↦ (A n : Measure Y))) :=
    hsum.symm ▸ hfin
  have hcount := isLegalCountingMeasure_sum baseY A (fun n ↦ ⟨d n,rfl⟩)
  convert hcount using 1
  exact Subtype.ext hsum.symm
end IntegerTags

/-- Tagging both original simple inputs retains their exact integer atoms. -/
theorem isLegalSimpleCountingMeasure_originalColoredInputs (q : ℕ)
    (p : LocalFiniteMeasure (LegalMarkedPhysicalPoint q) ×
      LocalFiniteMeasure (LegalMarkedPhysicalPoint q))
    (hs : IsLegalSimpleCountingMeasure (0 : LegalMarkedPhysicalPoint q) p.1)
    (ht : IsLegalSimpleCountingMeasure (0 : LegalMarkedPhysicalPoint q) p.2) :
    IsLegalSimpleCountingMeasure (0 : LegalColoredInputPoint q) (originalColoredInputs q p) := by
  let tag (c : Fin 2) (μ : LocalFiniteMeasure (LegalMarkedPhysicalPoint q)) :
      LocalFiniteMeasure (LegalColoredInputPoint q) := ⟨(μ : Measure (LegalMarkedPhysicalPoint q)).prod (Measure.dirac c),inferInstance⟩
  have htag (c : Fin 2) (μ : LocalFiniteMeasure (LegalMarkedPhysicalPoint q))
      (hc : IsLegalCountingMeasure (0 : LegalMarkedPhysicalPoint q) μ) :
      IsLegalCountingMeasure (0 : LegalColoredInputPoint q) (tag c μ) := by
    have he : (μ : Measure (LegalMarkedPhysicalPoint q)).prod (Measure.dirac c) =
        (μ : Measure (LegalMarkedPhysicalPoint q)).map (fun x ↦ (x,c)) := Measure.prod_dirac (μ := (μ : Measure (LegalMarkedPhysicalPoint q))) c
    have hfin : IsFiniteMeasureOnCompacts ((μ : Measure (LegalMarkedPhysicalPoint q)).map (fun x ↦ (x,c))) :=
      he ▸ inferInstance
    have h := original_isLegalCountingMeasure_map (0 : LegalMarkedPhysicalPoint q)
      (0 : LegalColoredInputPoint q) μ hc (fun x ↦ (x,c))
      (measurable_id.prodMk measurable_const) hfin
    convert h using 1
    exact Subtype.ext he
  obtain ⟨hsc,hsu⟩ := (isLegalSimpleCountingMeasure_iff _ _).mp hs
  obtain ⟨htc,htu⟩ := (isLegalSimpleCountingMeasure_iff _ _).mp ht
  apply (isLegalSimpleCountingMeasure_iff _ _).mpr
  refine ⟨?_,?_⟩
  · exact isLegalCountingMeasure_add _ (tag 0 p.1) (tag 1 p.2)
      (htag 0 p.1 hsc) (htag 1 p.2 htc)
  · intro z
    rcases z with ⟨x,c⟩
    change ((p.1 : Measure (LegalMarkedPhysicalPoint q)).prod (Measure.dirac (0 : Fin 2)) +
      (p.2 : Measure (LegalMarkedPhysicalPoint q)).prod (Measure.dirac (1 : Fin 2))) {(x,c)} ≤ 1
    rw [Measure.add_apply,← singleton_prod_singleton,Measure.prod_prod,Measure.prod_prod]
    fin_cases c
    · simpa using hsu x
    · simpa using htu x

/-- The unchanged actual full matching is a full matching of its immutable colors. -/
theorem isFullOriginalInputMatching_originalColoredScene (q : ℕ)
    (s : OriginalIIDMaskedMacroInputScene (Fin q))
    (h : IsFullOriginalBipartiteMatching (0 : LegalMarkedPhysicalPoint q)
      (0 : LegalMarkedPhysicalPoint q) s.1.1 s.2.1 s.2.2) :
    IsFullOriginalInputMatching q (originalColoredScene q s) := by
  apply isFullOriginalInputMatching_of_counting_simple_marginals
  · exact h.integer_edges
  · exact isLegalSimpleCountingMeasure_originalColoredInputs q s.2 h.simple_source h.simple_target
  · constructor
    · change (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).fst =
        legalInputColorMeasure q (originalColoredInputs q s.2) 0
      rw [legalInputColorMeasure_originalColoredInputs]
      change (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).fst = (s.2.1 : Measure (LegalMarkedPhysicalPoint q))
      exact h.source_marginal
    · change (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).snd =
        legalInputColorMeasure q (originalColoredInputs q s.2) 1
      rw [legalInputColorMeasure_originalColoredInputs]
      change (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).snd = (s.2.2 : Measure (LegalMarkedPhysicalPoint q))
      exact h.target_marginal

/-- The immutable colors recover every original scene coordinate exactly. -/
theorem originalColoredScene_injective (q : ℕ) : Injective (originalColoredScene q) := by
  intro s t h
  have hp := congrArg (fun z : LegalMarkedOptimalInputScene q ↦ z.1) h
  change s.1 = t.1 at hp
  have hi := congrArg (fun z : LegalMarkedOptimalInputScene q ↦ z.2) h
  change originalColoredInputs q s.2 = originalColoredInputs q t.2 at hi
  have hsource := congrArg (fun μ ↦ legalInputColorMeasure q μ 0) hi
  have htarget := congrArg (fun μ ↦ legalInputColorMeasure q μ 1) hi
  rw [legalInputColorMeasure_originalColoredInputs,legalInputColorMeasure_originalColoredInputs] at hsource htarget
  change (s.2.1 : Measure (LegalMarkedPhysicalPoint q)) = (t.2.1 : Measure (LegalMarkedPhysicalPoint q)) at hsource
  change (s.2.2 : Measure (LegalMarkedPhysicalPoint q)) = (t.2.2 : Measure (LegalMarkedPhysicalPoint q)) at htarget
  exact Prod.ext hp (Prod.ext (Subtype.ext hsource) (Subtype.ext htarget))

/-- The literal conversion is a measurable embedding, so all actual AE scene
properties transfer without a new measurable-event hypothesis. -/
theorem measurableEmbedding_originalColoredScene (q : ℕ) :
    MeasurableEmbedding (originalColoredScene q) :=
  (continuous_originalColoredScene q).measurable.measurableEmbedding (originalColoredScene_injective q)

/-- Coloring is compatible with actual physical dilation of every input and plan. -/
theorem originalColoredScene_dilation (q : ℕ) (c : ℝ) (hc : c ≠ 0)
    (s : OriginalIIDMaskedMacroInputScene (Fin q)) :
    originalColoredScene q
      (originalPairSceneDilation q c hc s.1,
        (localFiniteMapHomeomorph (legalMarkedPointDilation q c hc) s.2.1,
          localFiniteMapHomeomorph (legalMarkedPointDilation q c hc) s.2.2)) =
      legalMarkedInputSceneDilation q c hc (originalColoredScene q s) := by
  apply Prod.ext
  · rfl
  · exact (originalColoredInputs_mapHomeomorph q (legalMarkedPointDilation q c hc) s.2).symm

/-- The colored Laplace readout is exactly the two original uncolored input slices. -/
theorem originalColoredScene_laplace (q : ℕ)
    (F : C_c(LegalColoredInputPoint q, ℝ)) (hF : ∀ x, 0 ≤ F x)
    (s : OriginalIIDMaskedMacroInputScene (Fin q)) :
    legalMarkedInputSceneLaplace q F hF (originalColoredScene q s) =
      legalInputMeasureLaplacePair
        ⟨legalColoredInputTestSlice q F 0,fun x ↦ hF (x,0)⟩
        ⟨legalColoredInputTestSlice q F 1,fun x ↦ hF (x,1)⟩ s.2 := by
  change Real.exp (-LocalFiniteMeasure.testIntegral (originalColoredInputs q s.2) F) =
    Real.exp (-LocalFiniteMeasure.testIntegral s.2.1 (legalColoredInputTestSlice q F 0)) *
      Real.exp (-LocalFiniteMeasure.testIntegral s.2.2 (legalColoredInputTestSlice q F 1))
  rw [testIntegral_originalColoredInputs,neg_add,Real.exp_add]

/-- The unchanged whole colored inputs have their genuine theta Poisson
compact Laplace functional, produced from the original two-input profile. -/
theorem integral_originalColoredScene_laplace (q : ℕ) (θ : ℝ)
    (α β : Measure ℝ)
    (Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q)))
    (hLaplace : ∀ H G : LegalNonnegativeInputTest (LegalMarkedPhysicalPoint q),
      (∫ z, legalInputMeasureLaplacePair H G z ∂Q.map Prod.snd) =
        Real.exp (-(θ * ((∫ x, 1 - Real.exp (-H.1 x) ∂volume.prod α) +
          ∫ y, 1 - Real.exp (-G.1 y) ∂volume.prod β))))
    (F : C_c(LegalColoredInputPoint q, ℝ)) (hF : ∀ x, 0 ≤ F x) :
    (∫ s, legalMarkedInputSceneLaplace q F hF s ∂Q.map (originalColoredScene q)) =
      Real.exp (θ * legalOriginalInputPoissonExponent q α β F) := by
  let H : LegalNonnegativeInputTest (LegalMarkedPhysicalPoint q) :=
    ⟨legalColoredInputTestSlice q F 0,fun x ↦ hF (x,0)⟩
  let G : LegalNonnegativeInputTest (LegalMarkedPhysicalPoint q) :=
    ⟨legalColoredInputTestSlice q F 1,fun x ↦ hF (x,1)⟩
  rw [integral_map (continuous_originalColoredScene q).measurable.aemeasurable
    (legalMarkedInputSceneLaplace q F hF).continuous.aestronglyMeasurable]
  have heq : (fun s ↦ legalMarkedInputSceneLaplace q F hF (originalColoredScene q s)) =
      fun s ↦ legalInputMeasureLaplacePair H G s.2 :=
    funext fun s ↦ originalColoredScene_laplace q F hF s
  rw [heq,← integral_map measurable_snd.aemeasurable
    (legalInputMeasureLaplacePair H G).continuous.aestronglyMeasurable,hLaplace]
  have hneg (γ : Measure ℝ) (c : Fin 2) :
      (∫ x, 1 - Real.exp (-F (x,c)) ∂(volume : Measure (Fin q → ℝ)).prod γ) =
        -(∫ x, Real.exp (-F (x,c)) - 1 ∂(volume : Measure (Fin q → ℝ)).prod γ) := by
    rw [← integral_neg]
    congr 1
    funext x
    ring
  change Real.exp (-(θ * ((∫ x, 1 - Real.exp (-F (x,0)) ∂volume.prod α) +
    ∫ y, 1 - Real.exp (-F (y,1)) ∂volume.prod β))) = _
  rw [hneg α 0,hneg β 1]
  unfold legalOriginalInputPoissonExponent
  congr 1
  ring

/-- The original actual profile produces a stationary complete forward
matching with literal immutable colors and the original theta input law. -/
theorem originalColoredScene_of_conditionalMatchingProfile
    (q : ℕ) (gap θ : ℝ) (hgap : 0 < gap) (α β : Measure ℝ)
    (input : Measure (LocalFiniteMeasure (LegalMarkedPhysicalPoint q) ×
      LocalFiniteMeasure (LegalMarkedPhysicalPoint q)))
    (Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q)))
    (h : OriginalIIDConditionalMatchingProfile gap θ α β input Q) :
    let P := Q.map (originalColoredScene q)
    IsProbabilityMeasure P ∧
      (∀ v, MeasurePreserving (legalMarkedInputSceneReroot q v) P P) ∧
      (∀ F : C_c(LegalColoredInputPoint q, ℝ), ∀ hF : ∀ x, 0 ≤ F x,
        (∫ s, legalMarkedInputSceneLaplace q F hF s ∂P) =
          Real.exp (θ * legalOriginalInputPoissonExponent q α β F)) ∧
      ∀ᵐ s ∂P, s.1.1 = s.1.2 ∧ IsFullOriginalInputMatching q s ∧
        ∀ e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support,
          gap / 2 ≤ e.2.2 - e.1.2 ∧ e.1.2 < e.2.2 := by
  intro P
  have hQ : IsProbabilityMeasure Q := h.1
  have hp : IsProbabilityMeasure P :=
    Measure.isProbabilityMeasure_map (continuous_originalColoredScene q).measurable.aemeasurable
  refine ⟨hp,?_,integral_originalColoredScene_laplace q θ α β Q h.2.2.2.1,?_⟩
  · intro v
    refine ⟨(continuous_legalMarkedInputSceneReroot q v).measurable,?_⟩
    rw [Measure.map_map (continuous_legalMarkedInputSceneReroot q v).measurable
      (continuous_originalColoredScene q).measurable]
    have heq : legalMarkedInputSceneReroot q v ∘ originalColoredScene q =
        originalColoredScene q ∘ originalIIDMaskedMacroInputSceneReroot v :=
      funext fun s ↦ (originalColoredScene_reroot q v s).symm
    rw [heq,← Measure.map_map (continuous_originalColoredScene q).measurable
      (continuous_originalIIDMaskedMacroInputSceneReroot v).measurable,(h.2.2.1 v).map_eq]
  · apply (measurableEmbedding_originalColoredScene q).ae_map_iff.mpr
    filter_upwards [h.2.2.2.2.2] with s hs
    refine ⟨hs.1,isFullOriginalInputMatching_originalColoredScene q s hs.2.1,?_⟩
    have hc : IsClosed {e : LegalMarkedPhysicalEdge q | gap / 2 ≤ e.2.2 - e.1.2} :=
      isClosed_le continuous_const (continuous_snd.snd.sub continuous_fst.snd)
    have hsupport := Measure.support_subset_of_isClosed hc hs.2.2.2.1
    intro e he
    have hg : gap / 2 ≤ e.2.2 - e.1.2 := hsupport he
    exact ⟨hg,by linarith⟩

/-- The entire original colored Poisson exponent has the exact physical
Haar Jacobian under the same point dilation. -/
theorem originalColoredPoissonExponent_dilation (q : ℕ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (F : C_c(LegalColoredInputPoint q, ℝ)) (c : ℝ) (hc : c ≠ 0) :
    legalOriginalInputPoissonExponent q α β
        (F.comp (legalColoredInputDilation q c hc).toCocompactMap) =
      |(c ^ q)⁻¹| * legalOriginalInputPoissonExponent q α β F := by
  have hI (γ : Measure ℝ) [IsProbabilityMeasure γ] (k : Fin 2) :
      (∫ x, Real.exp (-F (legalMarkedPointDilation q c hc x,k)) - 1
        ∂(volume : Measure (Fin q → ℝ)).prod γ) =
      |(c ^ q)⁻¹| * ∫ x, Real.exp (-F (x,k)) - 1
        ∂(volume : Measure (Fin q → ℝ)).prod γ := by
    have hm : Measurable (fun x : LegalMarkedPhysicalPoint q ↦ Real.exp (-F (x,k)) - 1) := by
      fun_prop
    calc
      _ = ∫ x, Real.exp (-F (x,k)) - 1
          ∂((volume : Measure (Fin q → ℝ)).prod γ).map (legalMarkedPointDilation q c hc) :=
        (integral_map (legalMarkedPointDilation q c hc).continuous.measurable.aemeasurable
          hm.aestronglyMeasurable).symm
      _ = _ := by
        rw [map_physicalIntensity_legalMarkedPointDilation q c hc γ,integral_smul_measure]
        simp only [ENNReal.toReal_ofReal (abs_nonneg _),smul_eq_mul]
  change ((∫ x, Real.exp (-F (legalMarkedPointDilation q c hc x,0)) - 1 ∂volume.prod α) +
    ∫ x, Real.exp (-F (legalMarkedPointDilation q c hc x,1)) - 1 ∂volume.prod β) = _
  rw [hI α 0,hI β 1]
  unfold legalOriginalInputPoissonExponent
  ring

/-- The genuine theta compact input law transforms by its exact Haar Jacobian. -/
theorem originalColoredScene_dilation_laplace (q : ℕ) (θ : ℝ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (Q : Measure (LegalMarkedOptimalInputScene q))
    (hLaplace : ∀ F : C_c(LegalColoredInputPoint q, ℝ), ∀ hF : ∀ x, 0 ≤ F x,
      (∫ s, legalMarkedInputSceneLaplace q F hF s ∂Q) =
        Real.exp (θ * legalOriginalInputPoissonExponent q α β F))
    (c : ℝ) (hc : c ≠ 0)
    (F : C_c(LegalColoredInputPoint q, ℝ)) (hF : ∀ x, 0 ≤ F x) :
    (∫ s, legalMarkedInputSceneLaplace q F hF s ∂Q.map (legalMarkedInputSceneDilation q c hc)) =
      Real.exp ((θ * |(c ^ q)⁻¹|) * legalOriginalInputPoissonExponent q α β F) := by
  let G := F.comp (legalColoredInputDilation q c hc).toCocompactMap
  have hG : ∀ x, 0 ≤ G x := fun x ↦ hF _
  have hread : (fun s ↦ legalMarkedInputSceneLaplace q F hF
      (legalMarkedInputSceneDilation q c hc s)) =
      fun s ↦ legalMarkedInputSceneLaplace q G hG s := by
    funext s
    change Real.exp (-LocalFiniteMeasure.testIntegral (legalMarkedInputSceneDilation q c hc s).2 F) = _
    rw [legalMarkedInputSceneDilation_testIntegral]
    rfl
  rw [integral_map (continuous_legalMarkedInputSceneDilation q c hc).measurable.aemeasurable
    (legalMarkedInputSceneLaplace q F hF).continuous.aestronglyMeasurable,hread,hLaplace]
  rw [originalColoredPoissonExponent_dilation]
  congr 1
  ring

/-- Unit density is obtained by the actual d^q=theta dilation, with its exact
original compact-window PPP readout rather than an input-law hypothesis. -/
theorem originalColoredScene_dilation_unit_input (q : ℕ) (θ : ℝ) (hθ : 0 < θ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (Q : Measure (LegalMarkedOptimalInputScene q))
    (hLaplace : ∀ F : C_c(LegalColoredInputPoint q, ℝ), ∀ hF : ∀ x, 0 ≤ F x,
      (∫ s, legalMarkedInputSceneLaplace q F hF s ∂Q) =
        Real.exp (θ * legalOriginalInputPoissonExponent q α β F))
    (d : ℝ) (hd : 0 < d) (hpow : d ^ q = θ) :
    ∀ S : ℝ, 0 < S → ∀ (F : C_c(LegalColoredInputPoint q, ℝ)) (hF : ∀ x, 0 ≤ F x),
      (∀ (x : LegalMarkedPhysicalPoint q) (c : Fin 2),
        x.1 ∉ haarRootCube (Fin q) S → F (x,c) = 0) →
      (∫ s, legalMarkedInputSceneLaplace q F hF s
        ∂Q.map (legalMarkedInputSceneDilation q d hd.ne')) =
        ∫ b, legalInputBlockLaplace (fun x ↦ F (x,0)) (fun x ↦ F (x,1)) b
          ∂legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β := by
  intro S hS F hF hz
  rw [originalColoredScene_dilation_laplace q θ α β Q hLaplace d hd.ne' F hF,
    hpow,abs_of_pos (inv_pos.mpr hθ),mul_inv_cancel₀ hθ.ne',one_mul]
  have hfin : volume (haarRootCube (Fin q) S) ≠ ∞ := isCompact_Icc.measure_ne_top
  have hpos : volume (haarRootCube (Fin q) S) ≠ 0 := by
    rw [volume_haarRootCube (Fin q) hS.le]
    exact (ENNReal.ofReal_pos.mpr (pow_pos (by positivity : 0 < 2 * S) _)).ne'
  symm
  exact integral_legalInputPoissonWindowLaw_laplace_eq_global_exp q hfin hpos α β
    (F.continuous.measurable.comp (measurable_id.prodMk measurable_const))
    (F.continuous.measurable.comp (measurable_id.prodMk measurable_const))
    (fun x ↦ hF (x,0)) (fun x ↦ hF (x,1)) (fun x hx ↦ hz x 0 hx) (fun x hx ↦ hz x 1 hx)

/-- The actual scene dilation is a measurable embedding on the same carrier. -/
theorem measurableEmbedding_originalColoredSceneDilation (q : ℕ) (c : ℝ) (hc : c ≠ 0) :
    MeasurableEmbedding (legalMarkedInputSceneDilation q c hc) :=
  (((legalLocalFiniteMeasureHomeomorph (legalMarkedEdgeDilation q c hc)).prodCongr
    (legalLocalFiniteMeasureHomeomorph (legalMarkedEdgeDilation q c hc))).prodCongr
      (legalLocalFiniteMeasureHomeomorph (legalColoredInputDilation q c hc))).measurableEmbedding

/-- The same full matching and its positive clock gap survive actual spatial dilation. -/
theorem originalColoredScene_dilation_matching (q : ℕ) (gap : ℝ)
    (Q : Measure (LegalMarkedOptimalInputScene q))
    (hmatch : ∀ᵐ s ∂Q, s.1.1 = s.1.2 ∧ IsFullOriginalInputMatching q s ∧
      ∀ e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support,
        gap / 2 ≤ e.2.2 - e.1.2 ∧ e.1.2 < e.2.2)
    (d : ℝ) (hd : d ≠ 0) :
    ∀ᵐ s ∂Q.map (legalMarkedInputSceneDilation q d hd),
      s.1.1 = s.1.2 ∧ IsFullOriginalInputMatching q s ∧
      ∀ e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support,
        gap / 2 ≤ e.2.2 - e.1.2 ∧ e.1.2 < e.2.2 := by
  apply (measurableEmbedding_originalColoredSceneDilation q d hd).ae_map_iff.mpr
  filter_upwards [hmatch] with s hs
  refine ⟨congrArg (localFiniteMapHomeomorph (legalMarkedEdgeDilation q d hd)) hs.1,
    hs.2.1.dilation d hd,?_⟩
  intro e he
  have hc := ((isLegalSimpleCountingMeasure_iff _ _).mp hs.2.1.simple_edges).1
  have heold := (mem_support_mapHomeomorph_iff_of_legalCounting
    (0 : LegalMarkedPhysicalEdge q) (legalMarkedEdgeDilation q d hd) s.1.1 hc e).mp he
  have hg := hs.2.2 ((legalMarkedEdgeDilation q d hd).symm e) heold
  change gap / 2 ≤ e.2.2 - e.1.2 ∧ e.1.2 < e.2.2 at hg
  exact hg

/-- The normalized candidate is a deterministic double pushforward of the
same actual root-conditional matching law. No inputs or plans are resampled. -/
def originalUnitColoredLaw (q : ℕ)
    (Q : ProbabilityMeasure (OriginalIIDMaskedMacroInputScene (Fin q)))
    (d : ℝ) (hd : d ≠ 0) : ProbabilityMeasure (LegalMarkedOptimalInputScene q) :=
  (Q.map (continuous_originalColoredScene q).measurable.aemeasurable).map
    (continuous_legalMarkedInputSceneDilation q d hd).measurable.aemeasurable

/-- The plan pair in the colored normalized law is exactly the dilation of
the same original pair law. -/
theorem originalUnitColoredLaw_pairLaw (q : ℕ)
    (Q : ProbabilityMeasure (OriginalIIDMaskedMacroInputScene (Fin q)))
    (d : ℝ) (hd : d ≠ 0) :
    (legalMarkedInputPairLaw q (originalUnitColoredLaw q Q d hd) :
      Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))) =
      ((Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q))).map Prod.fst).map
        (originalPairSceneDilation q d hd) := by
  change (((Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q))).map
    (originalColoredScene q)).map (legalMarkedInputSceneDilation q d hd)).map Prod.fst = _
  rw [Measure.map_map measurable_fst
    (continuous_legalMarkedInputSceneDilation q d hd).measurable,
    Measure.map_map (measurable_fst.comp
      (continuous_legalMarkedInputSceneDilation q d hd).measurable)
      (continuous_originalColoredScene q).measurable,
    Measure.map_map (continuous_originalPairSceneDilation q d hd).measurable measurable_fst]
  rfl

/-- The actual colored candidate's Palm is exactly the Jacobian times the
pushforward of its raw theta Palm; clocks stay fixed and full displacement scales. -/
theorem originalUnitColoredLaw_palm_dilation (q : ℕ)
    (Q : ProbabilityMeasure (OriginalIIDMaskedMacroInputScene (Fin q)))
    (hstat : ∀ v, MeasurePreserving (physicalSceneReroot v)
      ((Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q))).map Prod.fst)
      ((Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q))).map Prod.fst))
    (hunit : (∫⁻ scene, (scene.1 : Measure (LegalMarkedPhysicalEdge q))
      {e | e.1.1 ∈ palmUnitCube (Fin q)}
        ∂((Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q))).map Prod.fst)) < ∞)
    (d : ℝ) (hd : d ≠ 0) :
    legalMarkedJointPalm q (originalUnitColoredLaw q Q d hd) =
      ENNReal.ofReal |(d ^ q)⁻¹| •
        (cubePalm (Fin q) (physicalScenePairCampbell
          ((Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q))).map Prod.fst))).map
            (legalPairMarkDilation q d) := by
  unfold legalMarkedJointPalm
  rw [originalUnitColoredLaw_pairLaw]
  exact original_raw_palm_dilation q _ hstat hunit d hd

/-- The entire normalized colored input law is the pushforward of the same
original immutable two-input law, independent of the retained plan factors. -/
theorem originalUnitColoredLaw_inputLaw (q : ℕ)
    (Q : ProbabilityMeasure (OriginalIIDMaskedMacroInputScene (Fin q)))
    (d : ℝ) (hd : d ≠ 0) :
    (originalUnitColoredLaw q Q d hd : Measure (LegalMarkedOptimalInputScene q)).map Prod.snd =
      (((Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q))).map Prod.snd).map
        (originalColoredInputs q)).map
          (localFiniteMapHomeomorph (legalColoredInputDilation q d hd)) := by
  change (((Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q))).map
    (originalColoredScene q)).map (legalMarkedInputSceneDilation q d hd)).map Prod.snd = _
  rw [Measure.map_map measurable_snd
    (continuous_legalMarkedInputSceneDilation q d hd).measurable,
    Measure.map_map (measurable_snd.comp
      (continuous_legalMarkedInputSceneDilation q d hd).measurable)
      (continuous_originalColoredScene q).measurable,
    Measure.map_map (continuous_localFiniteMapHomeomorph _).measurable
      (continuous_originalColoredInputs q).measurable,
    Measure.map_map ((continuous_localFiniteMapHomeomorph _).measurable.comp
      (continuous_originalColoredInputs q).measurable) measurable_snd]
  rfl

/-- Raw theta Campbell normalization applies to the exact colored candidate's
own plan law and preserves both original clock marginals. -/
theorem originalUnitColoredLaw_palm (q : ℕ) (gap θ : ℝ) (hθ : 0 < θ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (input : Measure (LocalFiniteMeasure (LegalMarkedPhysicalPoint q) ×
      LocalFiniteMeasure (LegalMarkedPhysicalPoint q)))
    (Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q)))
    (h : OriginalIIDConditionalMatchingProfile gap θ α β input Q)
    (d : ℝ) (hd : 0 < d) (hpow : d ^ q = θ) :
    let law := originalUnitColoredLaw q ⟨Q,h.1⟩ d hd.ne'
    IsProbabilityMeasure (legalMarkedJointPalm q law) ∧
      (legalMarkedJointPalm q law).map (fun m ↦ m.1.1) = α ∧
      (legalMarkedJointPalm q law).map (fun m ↦ m.1.2) = β := by
  intro law
  have hQ : IsProbabilityMeasure Q := h.1
  have hfull : ∀ᵐ s ∂Q, IsFullOriginalBipartiteMatching
      (0 : LegalMarkedPhysicalPoint q) (0 : LegalMarkedPhysicalPoint q) s.1.1 s.2.1 s.2.2 :=
    h.2.2.2.2.2.mono fun s hs ↦ hs.2.1
  have hraw := original_raw_campbell_of_stationary_full_input_profile
    q θ hθ.le α β Q h.2.2.1 hfull h.2.2.2.1
  have hjac : |(d ^ q)⁻¹| = θ⁻¹ := by rw [hpow,abs_of_pos (inv_pos.mpr hθ)]
  have hp := original_unit_palm_of_raw_dilation q (Q.map Prod.fst) hraw.1
    θ hθ α β hraw.2.2.1 hraw.2.2.2.1 hraw.2.2.2.2 d hd.ne' hjac
  change IsProbabilityMeasure (cubePalm (Fin q) (physicalScenePairCampbell
    (legalMarkedInputPairLaw q law : Measure (CavityLocalScene
      (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))))) ∧ _
  simpa only [law,legalMarkedJointPalm,originalUnitColoredLaw_pairLaw,ProbabilityMeasure.coe_mk] using hp

/-- Every geometric and prescribed-input property of the unit-density candidate
is produced from the same actual conditional matching profile. -/
theorem originalUnitColoredLaw_properties (q : ℕ) (gap θ : ℝ)
    (hgap : 0 < gap) (hθ : 0 < θ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (input : Measure (LocalFiniteMeasure (LegalMarkedPhysicalPoint q) ×
      LocalFiniteMeasure (LegalMarkedPhysicalPoint q)))
    (Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q)))
    (h : OriginalIIDConditionalMatchingProfile gap θ α β input Q)
    (d : ℝ) (hd : 0 < d) (hpow : d ^ q = θ) :
    let law := originalUnitColoredLaw q ⟨Q,h.1⟩ d hd.ne'
    (∀ v, MeasurePreserving (legalMarkedInputSceneReroot q v)
      (law : Measure (LegalMarkedOptimalInputScene q)) law) ∧
      (∀ᵐ s ∂(law : Measure (LegalMarkedOptimalInputScene q)),
        s.1.1 = s.1.2 ∧ IsFullOriginalInputMatching q s ∧
        ∀ e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support,
          gap / 2 ≤ e.2.2 - e.1.2 ∧ e.1.2 < e.2.2) ∧
      (∀ S : ℝ, 0 < S → ∀ (F : C_c(LegalColoredInputPoint q, ℝ)) (hF : ∀ x, 0 ≤ F x),
        (∀ (x : LegalMarkedPhysicalPoint q) (c : Fin 2),
          x.1 ∉ haarRootCube (Fin q) S → F (x,c) = 0) →
        (∫ s, legalMarkedInputSceneLaplace q F hF s ∂(law : Measure _)) =
          ∫ b, legalInputBlockLaplace (fun x ↦ F (x,0)) (fun x ↦ F (x,1)) b
            ∂legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β) ∧
      IsProbabilityMeasure (legalMarkedJointPalm q law) ∧
      (legalMarkedJointPalm q law).map (fun m ↦ m.1.1) = α ∧
      (legalMarkedJointPalm q law).map (fun m ↦ m.1.2) = β := by
  intro law
  have hraw := originalColoredScene_of_conditionalMatchingProfile q gap θ hgap α β input Q h
  let raw : ProbabilityMeasure (LegalMarkedOptimalInputScene q) :=
    ⟨Q.map (originalColoredScene q),hraw.1⟩
  exact ⟨measurePreserving_dilated_legalMarkedInputSceneLaw q raw d hd.ne' hraw.2.1,
    originalColoredScene_dilation_matching q gap _ hraw.2.2.2 d hd.ne',
    originalColoredScene_dilation_unit_input q θ hθ α β _ hraw.2.2.1 d hd hpow,
    originalUnitColoredLaw_palm q gap θ hθ α β input Q h d hd hpow⟩

/-- The original actual unit-density candidate becomes a weighted stationary
Poisson matching once its genuine kinetic Palm integral is finite. The bounded
measurable probe is automatically integrable on the proved probability Palm. -/
def originalLegalWeightedCandidate (q : ℕ) (gap θ : ℝ)
    (hgap : 0 < gap) (hθ : 0 < θ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (input : Measure (LocalFiniteMeasure (LegalMarkedPhysicalPoint q) ×
      LocalFiniteMeasure (LegalMarkedPhysicalPoint q)))
    (Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q)))
    (h : OriginalIIDConditionalMatchingProfile gap θ α β input Q)
    (d : ℝ) (hd : 0 < d) (hpow : d ^ q = θ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ)
    (hkin : Integrable (fun m ↦ kin m.1.1 m.1.2 m.2)
      (legalMarkedJointPalm q (originalUnitColoredLaw q ⟨Q,h.1⟩ d hd.ne')))
    (hg : Measurable (Function.uncurry g))
    (G : ℝ) (hgb : ∀ a b, |g a b| ≤ G) :
    LegalWeightedStationaryPoissonMatching q α β kin g := by
  have hp := originalUnitColoredLaw_properties q gap θ hgap hθ α β input Q h d hd hpow
  have hPalm : IsProbabilityMeasure
      (legalMarkedJointPalm q (originalUnitColoredLaw q ⟨Q,h.1⟩ d hd.ne')) := hp.2.2.2.1
  have hprobe : Integrable (fun m ↦ g m.1.1 m.1.2)
      (legalMarkedJointPalm q (originalUnitColoredLaw q ⟨Q,h.1⟩ d hd.ne')) :=
    MemLp.integrable (q := ∞) le_top
      (memLp_top_of_bound (hg.comp measurable_fst).aestronglyMeasurable G
        (Filter.Eventually.of_forall fun m ↦ hgb m.1.1 m.1.2))
  exact {
    law := originalUnitColoredLaw q ⟨Q,h.1⟩ d hd.ne'
    stationary := hp.1
    full_matching := hp.2.1.mono fun s hs ↦ hs.2.1
    forward := hp.2.1.mono fun s hs e he ↦ (hs.2.2 e he).2
    input_laplace := hp.2.2.1
    palm_probability := hp.2.2.2.1
    source_clock := hp.2.2.2.2.1
    target_clock := hp.2.2.2.2.2
    kinetic_integrable := hkin
    probe_integrable := hprobe }

end OTSelector.Reconstruction
