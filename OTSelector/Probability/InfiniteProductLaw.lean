import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure

/-!
## Lemma skeleton

* **Conditions:** Measurable coordinate functions and probability product factors.
* **Objects:** Independent infinite coordinates and their finite-dimensional laws.
* **Proof detail:** Push forward the product along projections and finite coordinate maps.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 2*, Sections 254G–254I and 254N–254O, infinite products, coordinate maps and subproducts.
  https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf

**Relationship to the sources:** Lean iIndepFun and infinitePi interfaces implement the book product-measure identities.
-/

/-!
# Shared laws of iid sequences and independent product factors

These coordinate laws are shared by block decomposition, tile discrepancy and
conditional iid arguments. They depend only on the product measure infrastructure.
-/

open MeasureTheory ProbabilityTheory

noncomputable section
namespace OTSelector.Probability

/-- Random variables defined on the second factor of a product of probability
spaces inherit their independence. -/
theorem iIndepFun_snd_prod {ι Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {ν₁ : Measure Ω₁} [IsProbabilityMeasure ν₁] {ν₂ : Measure Ω₂} [IsProbabilityMeasure ν₂]
    {β : ι → Type*} [∀ i, MeasurableSpace (β i)] {Y : ∀ i, Ω₂ → β i}
    (mY : ∀ i, Measurable (Y i)) (hY : iIndepFun Y ν₂) :
    iIndepFun (fun i (p : Ω₁ × Ω₂) => Y i p.2) (ν₁.prod ν₂) := by
  classical
  refine (iIndepFun_iff_map_fun_eq_infinitePi_map (P := ν₁.prod ν₂)
    (X := fun i (p : Ω₁ × Ω₂) => Y i p.2)
    (fun i => (mY i).comp measurable_snd)).mpr ?_
  have hmap1 : (ν₁.prod ν₂).map (fun p : Ω₁ × Ω₂ => fun i => Y i p.2) =
      ν₂.map (fun s => fun i => Y i s) := by
    rw [show (fun p : Ω₁ × Ω₂ => fun i => Y i p.2) =
        (fun s : Ω₂ => fun i => Y i s) ∘ Prod.snd from rfl,
      ← Measure.map_map (measurable_pi_lambda (fun (s : Ω₂) (i : ι) => Y i s) mY)
        measurable_snd]
    rw [Measure.map_snd_prod]
    simp [measure_univ]
  rw [hmap1]
  have hmap2 : ∀ i, (ν₁.prod ν₂).map (fun p => Y i p.2) = ν₂.map (Y i) := by
    intro i
    rw [show (fun p : Ω₁ × Ω₂ => Y i p.2) = Y i ∘ Prod.snd from rfl,
      ← Measure.map_map (mY i) measurable_snd]
    rw [Measure.map_snd_prod]
    simp [measure_univ]
  rw [show (fun i => (ν₁.prod ν₂).map (fun p => Y i p.2)) = (fun i => ν₂.map (Y i)) from
    funext hmap2]
  exact (iIndepFun_iff_map_fun_eq_infinitePi_map (fun i => mY i)).mp hY

/-- Coordinates of an infinite product of a probability measure are independent. -/
theorem iIndepFun_infinitePi_apply_comp {Pos β : Type*} [MeasurableSpace Pos]
    [MeasurableSpace β] (ν : Measure Pos) [IsProbabilityMeasure ν]
    (g : Pos → β) (hg : Measurable g) :
    iIndepFun (fun (i : ℕ) (s : ℕ → Pos) => g (s i))
      (Measure.infinitePi (fun _ : ℕ => ν)) := by
  have h := iIndepFun_infinitePi (P := fun _ : ℕ => ν)
    (X := fun _ (x : Pos) => x) (by fun_prop)
  exact h.comp (fun _ x => g x) (fun _ => hg)

/-- The first `n` coordinates of an infinite product have the finite product law. -/
theorem infinitePi_map_fin {Pos : Type*} [MeasurableSpace Pos] (ν : Measure Pos)
    [IsProbabilityMeasure ν] (n : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => ν)).map
        (fun y : ℕ → Pos => fun j : Fin n => y j) =
      Measure.pi (fun _ : Fin n => ν) := by
  have h := Measure.map_infinitePi_infinitePi_of_inj
    (Ω := fun _ : ℕ => Pos) (P := fun _ : ℕ => ν)
    (f := fun i : Fin n => (i : ℕ)) (fun i j hij => Fin.ext hij)
  rwa [Measure.infinitePi_eq_pi (μ := fun _ : Fin n => ν)] at h

end OTSelector.Probability
