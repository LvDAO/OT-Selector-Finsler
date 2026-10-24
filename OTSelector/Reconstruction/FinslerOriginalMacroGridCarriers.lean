import OTSelector.Reconstruction.FinslerConcreteUpperOriginalMicrocellMacroIndices
import OTSelector.Reconstruction.FinslerRelativeLawOriginalPairedActiveCarrier
import OTSelector.Reconstruction.FinslerConcreteUpperClassActive

/-! The original Haar restriction supplies every microbox boundary and
carrier fact on the entire optional paired cloud, before optimization. -/
open Set Function MeasureTheory ProbabilityTheory Module BoxIntegral
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {q : ℕ}

/-- The null coordinate faces remain null under the actual unnormalized Haar
restriction and its nullable retained-cloud law, including zero retained mass. -/
theorem ae_original_retained_grid_nonfaces
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] (Fin q → ℝ))
    (n : ℕ) [NeZero n] (s : Set E) (classMass : ℝ≥0∞) :
    ∀ᵐ o ∂originalRetainedSpatialLaw (μ.restrict s) classMass,
      ∀ w, o = some w → ∀ l : Fin q, ∀ z : ℤ, (n : ℝ) * e w l ≠ (z : ℝ) := by
  have hmeas : MeasurableSet {w : E | ∀ l : Fin q, ∀ z : ℤ, (n : ℝ) * e w l ≠ (z : ℝ)} := by
    simp only [ofPred_forall]
    apply MeasurableSet.iInter
    intro l
    apply MeasurableSet.iInter
    intro z
    exact (measurableSet_eq_fun
      ((measurable_pi_apply l).comp e.continuous.measurable |>.const_mul (n : ℝ)) measurable_const).compl
  exact originalRetainedSpatialLaw_ae_some_mem (μ.restrict s) classMass hmeas
    (ae_restrict_of_ae (ae_original_grid_coordinates_nonintegral μ e n))

/-- Every original active leaf value is its physical microbox value on one
full-measure event for all costs and all leaves. This uses the whole original
iid arrays; no selected subcloud is assigned an iid law. -/
theorem ae_original_paired_macro_leaves_eq_microcells
    {I J : Type*} [MeasurableSpace I] [MeasurableSpace J]
    (μ : Measure E) [μ.IsAddHaarMeasure] (basis : Basis (Fin q) ℝ E)
    {R n depth : ℕ} (hR : 0 < R) (hn : 0 < n)
    (hdepth : 2 * R * n ≤ 2 ^ depth)
    {s : Set E} (hs : MeasurableSet s)
    (hunit : ∀ x ∈ s, labelCubeCoordinates basis R x ∈ unitCubeSet q)
    (classMass : ℝ≥0∞) (hprob : IsProbabilityMeasure (originalRetainedSpatialLaw (μ.restrict s) classMass))
    (π : Measure (I × J)) [IsProbabilityMeasure π] (mask : I → J → Prop)
    (cells : Finset (Fin q → ℤ))
    (hfit : cells ⊆ Finset.univ.image (originalMacroMicroIndex (q := q) R n))
    (N : ℕ) :
    let _inst : NeZero n := ⟨hn.ne'⟩
    (∀ x ∈ s, basis.equivFun x ∈ ⋃ ν ∈ cells, (unitPartition.box n ν : Set (Fin q → ℝ))) →
    let spatial := originalRetainedSpatialLaw (μ.restrict s) classMass
    let common := spatial.prod π
    let law := (Measure.pi (fun _ : Fin N ↦ common)).prod (Measure.pi (fun _ : Fin N ↦ common))
    let point := fun o : Option E ↦ o.elim 0 id
    let z := fun o ↦ labelCubeCoordinates basis R (point o)
    let graph := fun sample ↦ pairedClassActiveGraph (fun o : Option E ↦ o.map (fun _ ↦ ()))
      mask sample.1 sample.2
    ∀ᵐ sample ∂law, ∀ cost : Fin N → Fin N → ℝ,
      (∑ leaf : Fin q → Fin (2 ^ depth + 1), PartialMatching.legalMaximumValue
        (PartialMatching.spatialLegalBlock (graph sample)
          (fun j ↦ gridCellLabel q (2 * R * n) depth depth (by positivity) hdepth (z (sample.1 j).1))
          (fun k ↦ gridCellLabel q (2 * R * n) depth depth (by positivity) hdepth (z (sample.2 k).1)) leaf) cost) =
      ∑ ν ∈ cells, PartialMatching.legalMaximumValue ((graph sample).filter (fun edge ↦
        basis.equivFun (point (sample.1 edge.1).1) ∈ unitPartition.box n ν ∧
        basis.equivFun (point (sample.2 edge.2).1) ∈ unitPartition.box n ν)) cost := by
  classical
  letI : NeZero n := ⟨hn.ne'⟩
  dsimp only
  intro hcover
  let spatial := originalRetainedSpatialLaw (μ.restrict s) classMass
  letI : IsProbabilityMeasure spatial := hprob
  let common := spatial.prod π
  let law := (Measure.pi (fun _ : Fin N ↦ common)).prod (Measure.pi (fun _ : Fin N ↦ common))
  have hfaces := ae_original_retained_grid_nonfaces μ basis.equivFunL n s classMass
  have hmem := originalRetainedSpatialLaw_ae_some_mem (μ.restrict s) classMass hs (ae_restrict_mem hs)
  have hpoint : ∀ᵐ o ∂spatial, ∀ w, o = some w → w ∈ s ∧
      (∀ l : Fin q, ∀ z : ℤ, (n : ℝ) * basis.equivFun w l ≠ (z : ℝ)) := by
    filter_upwards [hfaces,hmem] with o hf hm
    exact fun w hw ↦ ⟨hm w hw,hf w hw⟩
  have hcommon : ∀ᵐ p ∂common, ∀ w, p.1 = some w → w ∈ s ∧
      (∀ l : Fin q, ∀ z : ℤ, (n : ℝ) * basis.equivFun w l ≠ (z : ℝ)) :=
    Measure.quasiMeasurePreserving_fst.ae hpoint
  have hsource : ∀ᵐ sample ∂law, ∀ j : Fin N, ∀ w, (sample.1 j).1 = some w → w ∈ s ∧
      (∀ l : Fin q, ∀ z : ℤ, (n : ℝ) * basis.equivFun w l ≠ (z : ℝ)) := by
    rw [ae_all_iff]
    intro j
    exact Measure.quasiMeasurePreserving_fst.ae
      ((Measure.quasiMeasurePreserving_eval (fun _ : Fin N ↦ common) j).ae hcommon)
  have htarget : ∀ᵐ sample ∂law, ∀ k : Fin N, ∀ w, (sample.2 k).1 = some w → w ∈ s ∧
      (∀ l : Fin q, ∀ z : ℤ, (n : ℝ) * basis.equivFun w l ≠ (z : ℝ)) := by
    rw [ae_all_iff]
    intro k
    exact Measure.quasiMeasurePreserving_snd.ae
      ((Measure.quasiMeasurePreserving_eval (fun _ : Fin N ↦ common) k).ae hcommon)
  filter_upwards [hsource,htarget] with sample hS hT
  intro cost
  have hproperties : ∀ edge ∈ pairedClassActiveGraph (fun o : Option E ↦ o.map (fun _ ↦ ()))
      mask sample.1 sample.2,
      (sample.1 edge.1).1.elim 0 id ∈ s ∧ (sample.2 edge.2).1.elim 0 id ∈ s ∧
      ∀ l : Fin q, ∀ z : ℤ,
        (n : ℝ) * basis.equivFun ((sample.1 edge.1).1.elim 0 id) l ≠ (z : ℝ) ∧
        (n : ℝ) * basis.equivFun ((sample.2 edge.2).1.elim 0 id) l ≠ (z : ℝ) := by
    intro edge he
    have ha := (mem_pairedClassActiveGraph _ _ _ _ edge).mp he
    cases hs' : (sample.1 edge.1).1 with
    | none => simp [hs'] at ha
    | some x =>
      cases ht' : (sample.2 edge.2).1 with
      | none => simp [ht'] at ha
      | some y =>
        have hx := hS edge.1 x hs'
        have hy := hT edge.2 y ht'
        simp only [Option.elim_some]
        exact ⟨hx.1,hy.1,fun l z ↦ ⟨hx.2 l z,hy.2 l z⟩⟩
  exact PartialMatching.sum_macro_grid_leaves_eq_original_microcells _ cost
    (fun j ↦ (sample.1 j).1.elim 0 id) (fun k ↦ (sample.2 k).1.elim 0 id) basis hR hn hdepth
    (fun edge he ↦ ⟨hunit _ (hproperties edge he).1,hunit _ (hproperties edge he).2.1⟩)
    (fun edge he ↦ (hproperties edge he).2.2) cells hfit
    (fun edge he ↦ hcover _ (hproperties edge he).1)

end OTSelector.Reconstruction
