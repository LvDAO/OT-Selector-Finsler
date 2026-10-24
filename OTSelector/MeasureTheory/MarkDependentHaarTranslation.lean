import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Prod

/-!
## Lemma skeleton

* **Conditions:** Lebesgue coordinates times an arbitrary SFinite mark law, and a measurable displacement depending on the full mark. Bochner conclusions use the stated scalar and mark integrability.
* **Objects:** Mark-dependent translation preserves the product law; translated tensor observables remain integrable and their integral factors.
* **Proof detail:** Translate the spatial Haar measure separately on each mark fiber, apply Tonelli/Fubini, and transport the integrable tensor product.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 4*, Sections 441A (invariant measure definition) and 441J (integration under an invariant action), pp. 2 and 6; Section 443A, pp. 19–20 (Haar measurability).
  https://www1.essex.ac.uk/maths/people/fremlin/chap44.pdf#page=6
* D. H. Fremlin, *Measure Theory, Volume 2*, Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25.
  https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19
* D. H. Fremlin, *Measure Theory, Volume 2*, Exercises 253Y(f)(i)–(vii), 253Y(g)–(h), pp. 46–47: Banach-valued L1, bounded bilinear maps and section integrals.
  https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=46

**Relationship to the sources:** Fiberwise Haar invariance. No independence between the mark and its displacement is assumed; the pair map keeps the original mark unchanged.
-/

/-!
# Moving a physical Campbell window along its own marked path

A measurable displacement depending on the complete original edge mark preserves spatial
Haar measure times its mark law.  No independence between that displacement and the mark is
assumed.  This is the localization identity needed for actual path-position current windows.
-/

open Set Function Filter MeasureTheory MeasureTheory.Measure

noncomputable section
namespace OTSelector.Reconstruction

/-- An arbitrary measurable displacement of each mark preserves the complete Haar/mark
product measure, retaining that same mark. -/
theorem measurePreserving_markDependentAnchorTranslation
    {q : ℕ} {Z : Type*} [MeasurableSpace Z] (η : Measure Z) [SFinite η]
    (d : Z → Fin q → ℝ) (hd : Measurable d) :
    MeasurePreserving (fun p : (Fin q → ℝ) × Z ↦ (p.1 + d p.2, p.2))
      ((volume : Measure (Fin q → ℝ)).prod η)
      ((volume : Measure (Fin q → ℝ)).prod η) := by
  have hs := (MeasurePreserving.id η).skew_product
    (g := fun z x ↦ x + d z)
    (measurable_snd.add (hd.comp measurable_fst))
    (Eventually.of_forall (fun z ↦
      (measurePreserving_add_right (volume : Measure (Fin q → ℝ)) (d z)).map_eq))
  exact (measurePreserving_swap (μ := η) (ν := (volume : Measure (Fin q → ℝ)))).comp
    (hs.comp (measurePreserving_swap (μ := (volume : Measure (Fin q → ℝ))) (ν := η)))

/-- A localized marked vector readout remains integrable after moving its physical anchor by
its own arbitrary measurable displacement. -/
theorem integrable_markDependentAnchorTranslation
    {q : ℕ} {Z V : Type*} [MeasurableSpace Z] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (η : Measure Z) [SFinite η] (d : Z → Fin q → ℝ) (hd : Measurable d)
    {h : (Fin q → ℝ) → ℝ} {f : Z → V}
    (hh : Integrable h (volume : Measure (Fin q → ℝ))) (hf : Integrable f η) :
    Integrable (fun p : (Fin q → ℝ) × Z ↦ h (p.1 + d p.2) • f p.2)
      ((volume : Measure (Fin q → ℝ)).prod η) :=
  (measurePreserving_markDependentAnchorTranslation η d hd).integrable_comp_of_integrable
    (hh.smul_prod hf)

/-- Moving the window along its own marked path leaves the exact spatial/Palm mean unchanged. -/
theorem integral_markDependentAnchorTranslation
    {q : ℕ} {Z V : Type*} [MeasurableSpace Z] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] (η : Measure Z) [SFinite η] (d : Z → Fin q → ℝ) (hd : Measurable d)
    {h : (Fin q → ℝ) → ℝ} {f : Z → V}
    (hh : Integrable h (volume : Measure (Fin q → ℝ))) (hf : Integrable f η) :
    (∫ p : (Fin q → ℝ) × Z, h (p.1 + d p.2) • f p.2
      ∂(volume : Measure (Fin q → ℝ)).prod η) =
      (∫ x, h x ∂(volume : Measure (Fin q → ℝ))) • ∫ z, f z ∂η := by
  have hmp := measurePreserving_markDependentAnchorTranslation η d hd
  have hbase := hh.smul_prod hf
  have hm : AEStronglyMeasurable (fun p : (Fin q → ℝ) × Z ↦ h p.1 • f p.2)
      (((volume : Measure (Fin q → ℝ)).prod η).map
        (fun p : (Fin q → ℝ) × Z ↦ (p.1 + d p.2, p.2))) := by
    rw [hmp.map_eq]
    exact hbase.aestronglyMeasurable
  have hi := integral_map hmp.measurable.aemeasurable hm
  rw [hmp.map_eq] at hi
  exact hi.symm.trans (integral_prod_smul h f)

end OTSelector.Reconstruction
