import OTSelector.Geometry.FinslerQuadraticCostDifferenceRigidity
import OTSelector.Geometry.FinslerQuadraticCostDifferenceAmbient
import OTSelector.Reconstruction.OriginalSeedPairCoefficient

/-!
# Restricted rigidity for the original intrinsic pair coefficient

The original seed kernel produces the measurable positive matrices on strictly
ordered interior scalar pairs. Thus the actual frozen coefficient, with its
original source clock law, supplies all matrix and atomlessness inputs to the
countable-target legal rigidity theorem.
-/

open Set MeasureTheory Manifold Module
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Reconstruction

open OTSelector.Geometry ContinuousFinslerNorm

set_option backward.isDefEq.respectTransparency false

/-- Legal original clock pairs in one full conditional interior interval. -/
def originalQuadraticLegalDomain {ι J : Type*} (offset lo hi : ℝ)
    (Y : J → (ι → ℝ) × ℝ) : Set (((ι → ℝ) × ℝ) × J) :=
  {p | p.1.2 - offset ∈ Ioo lo hi ∧ (Y p.2).2 - offset ∈ Ioo lo hi ∧
    p.1.2 < (Y p.2).2}

/-- The actual legal edge domain is measurable for every countable target cloud. -/
theorem measurableSet_originalQuadraticLegalDomain {ι J : Type*}
    [Fintype ι] [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J]
    (offset lo hi : ℝ) (Y : J → (ι → ℝ) × ℝ) :
    MeasurableSet (originalQuadraticLegalDomain offset lo hi Y) := by
  have hY : Measurable (fun j ↦ (Y j).2) := measurable_of_countable _
  exact ((measurable_snd.comp measurable_fst).sub_const offset measurableSet_Ioo).inter
    (((hY.comp measurable_snd).sub_const offset measurableSet_Ioo).inter
      (measurableSet_lt (measurable_snd.comp measurable_fst) (hY.comp measurable_snd)))

/-- For two fixed targets the common legal source domain is open, including
the possibility that it is empty. -/
theorem isOpen_commonLegalSource_originalQuadraticLegalDomain {ι J : Type*}
    [Fintype ι] (offset lo hi : ℝ) (Y : J → (ι → ℝ) × ℝ) (i j : J) :
    IsOpen (commonLegalSource (originalQuadraticLegalDomain offset lo hi Y) i j) := by
  have h (k : J) : IsOpen
      {x : (ι → ℝ) × ℝ | x.2 - offset ∈ Ioo lo hi ∧
        (Y k).2 - offset ∈ Ioo lo hi ∧ x.2 < (Y k).2} :=
    ((continuous_snd.sub continuous_const).isOpen_preimage _ isOpen_Ioo).inter
      (isOpen_const.inter (isOpen_lt continuous_snd continuous_const))
  exact (h i).inter (h j)

/-- The original legal domain is open in both actual marked endpoints. -/
theorem isOpen_originalQuadratic_ambientDomain {ι : Type*} [Fintype ι]
    (offset lo hi : ℝ) :
    IsOpen (originalQuadraticLegalDomain (ι := ι) offset lo hi id) :=
  (((continuous_snd.comp continuous_fst).sub continuous_const).isOpen_preimage _
    isOpen_Ioo).inter
    ((((continuous_snd.comp continuous_snd).sub continuous_const).isOpen_preimage _
      isOpen_Ioo).inter
      (isOpen_lt (continuous_snd.comp continuous_fst) (continuous_snd.comp continuous_snd)))

variable {E M J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  [Countable J] [MeasurableSpace J] [MeasurableSingletonClass J]
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

namespace OriginalSeedConditionalMoments

/-- The literal original pair coefficient has atomless cost differences on its
common open legal source domain; coefficient regularity and positivity are derived. -/
theorem nullSingletonClass_map_quadratic_sub (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (m : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)) [m.IsAddHaarMeasure]
    [SFinite μ] {ρ : Measure ((Fin (finrank ℝ S.covector.ker) → ℝ) × ℝ)}
    (hρ : ρ ≪ m.prod μ)
    (Y : J → (Fin (finrank ℝ S.covector.ker) → ℝ) × ℝ)
    {i j : J} (hij : (Y i).1 ≠ (Y j).1) :
    NullSingletonClass ((ρ.restrict
      (commonLegalSource (originalQuadraticLegalDomain S.level D.lo D.hi Y) i j)).map
      (fun x ↦ Probability.cavitySpatialDifferenceCost
        (fun s t v ↦ matrixQuadratic (originalSeedPairCoefficient S w (s, t)) v) x (Y i) -
        Probability.cavitySpatialDifferenceCost
          (fun s t v ↦ matrixQuadratic (originalSeedPairCoefficient S w (s, t)) v) x (Y j))) := by
  apply nullSingletonClass_map_marked_matrixQuadratic_sub m μ hρ
    (fun s t ↦ originalSeedPairCoefficient S w (s, t))
    ((measurable_originalSeedPairCoefficient S hF hw).comp
      (measurable_id.prodMk measurable_const))
    ((measurable_originalSeedPairCoefficient S hF hw).comp
      (measurable_id.prodMk measurable_const)) hij
    (measurableSet_commonLegalSource
      (measurableSet_originalQuadraticLegalDomain S.level D.lo D.hi Y) i j)
  intro x hx
  exact ⟨(D.pair_compliance_posDef hF hw hx.1.1 hx.1.2.1 hx.1.2.2).2,
    (D.pair_compliance_posDef hF hw hx.2.1 hx.2.2.1 hx.2.2.2).2⟩

/-- Two actual plans with the same source law agree when their average is carried
by a legally monotone relation for the original intrinsic quadratic cost. -/
theorem countable_quadratic_plans_eq (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (m : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)) [m.IsAddHaarMeasure]
    [SFinite μ] {ρ : Measure ((Fin (finrank ℝ S.covector.ker) → ℝ) × ℝ)}
    (hρ : ρ ≪ m.prod μ)
    (Y : J → (Fin (finrank ℝ S.covector.ker) → ℝ) × ℝ)
    (hY : Function.Injective (fun j ↦ (Y j).1))
    (Γ : Set (((Fin (finrank ℝ S.covector.ker) → ℝ) × ℝ) × J))
    (hΓ : MeasurableSet Γ) (hsub : Γ ⊆ originalQuadraticLegalDomain S.level D.lo D.hi Y)
    (π₀ π₁ : Measure (((Fin (finrank ℝ S.covector.ker) → ℝ) × ℝ) × J))
    (hsource₀ : π₀.map Prod.fst = ρ) (hsource₁ : π₁.map Prod.fst = ρ)
    {r : ℝ≥0∞} (hr : r ≠ 0) (hcarried : ∀ᵐ z ∂r • (π₀ + π₁), z ∈ Γ)
    (hcycle : IsTwoCycleMonotoneOn
      (fun x j ↦ Probability.cavitySpatialDifferenceCost
        (fun s t v ↦ matrixQuadratic (originalSeedPairCoefficient S w (s, t)) v) x (Y j))
      (originalQuadraticLegalDomain S.level D.lo D.hi Y) Γ) : π₀ = π₁ := by
  apply countable_plans_eq_of_marked_matrixQuadratic_legal_twoCycle m μ hρ
    (fun s t ↦ originalSeedPairCoefficient S w (s, t)) Y
    (fun j ↦ (measurable_originalSeedPairCoefficient S hF hw).comp
      (measurable_id.prodMk measurable_const)) hY
    (originalQuadraticLegalDomain S.level D.lo D.hi Y) Γ
    (measurableSet_originalQuadraticLegalDomain S.level D.lo D.hi Y) hΓ hsub _
    π₀ π₁ hsource₀ hsource₁ hr hcarried hcycle
  intro x j hx
  exact (D.pair_compliance_posDef hF hw hx.1 hx.2.1 hx.2.2).2

omit [Countable J] [MeasurableSpace J] [MeasurableSingletonClass J] in
/-- Actual ambient plan equality on the occupied target cloud for the original
intrinsic coefficient. The target indexing and exact pullback recovery are internal. -/
theorem ambient_quadratic_plans_eq (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (m : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)) [m.IsAddHaarMeasure]
    [SFinite μ] {ρ : Measure ((Fin (finrank ℝ S.covector.ker) → ℝ) × ℝ)}
    (hρ : ρ ≪ m.prod μ)
    {T : Set ((Fin (finrank ℝ S.covector.ker) → ℝ) × ℝ)}
    (hT : T.Countable) (hinj : InjOn Prod.fst T)
    (θ : Measure ((Fin (finrank ℝ S.covector.ker) → ℝ) × ℝ))
    (hθ : ∀ᵐ y ∂θ, y ∈ T)
    (π₀ π₁ : Measure (((Fin (finrank ℝ S.covector.ker) → ℝ) × ℝ) ×
      ((Fin (finrank ℝ S.covector.ker) → ℝ) × ℝ)))
    (hsource₀ : π₀.map Prod.fst = ρ) (hsource₁ : π₁.map Prod.fst = ρ)
    (htarget₀ : π₀.map Prod.snd = θ) (htarget₁ : π₁.map Prod.snd = θ)
    (hlegal₀ : ∀ᵐ p ∂π₀, p ∈ originalQuadraticLegalDomain S.level D.lo D.hi id)
    (hlegal₁ : ∀ᵐ p ∂π₁, p ∈ originalQuadraticLegalDomain S.level D.lo D.hi id)
    (hcycle : IsTwoCycleMonotoneOn
      (Probability.cavitySpatialDifferenceCost
        (fun s t v ↦ matrixQuadratic (originalSeedPairCoefficient S w (s, t)) v))
      (originalQuadraticLegalDomain S.level D.lo D.hi id)
      ((((2 : ℝ≥0∞)⁻¹ • (π₀ + π₁)).support) ∩
        originalQuadraticLegalDomain S.level D.lo D.hi id)) : π₀ = π₁ := by
  apply ambient_quadratic_plans_eq_of_countable_spatial_cloud m μ hρ
    (fun s t ↦ originalSeedPairCoefficient S w (s, t))
    (fun _ ↦ (measurable_originalSeedPairCoefficient S hF hw).comp
      (measurable_id.prodMk measurable_const)) hT hinj θ hθ π₀ π₁
    hsource₀ hsource₁ htarget₀ htarget₁
    (originalQuadraticLegalDomain S.level D.lo D.hi id)
    (isOpen_originalQuadratic_ambientDomain S.level D.lo D.hi).measurableSet
    _ hlegal₀ hlegal₁ hcycle
  intro p hp
  exact (D.pair_compliance_posDef hF hw hp.1 hp.2.1 hp.2.2).2

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
