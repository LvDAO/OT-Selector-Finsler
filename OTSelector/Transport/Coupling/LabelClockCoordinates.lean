import LeanPool.Vlasov.OT.Coupling
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.LabelClockCoupling.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.LabelClockCoupling`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.LabelClockCoupling

**Conditions:** An injective measurable label-clock map on a Borel regular subset of a standard Borel space; both measures are carried by one fixed label.

**Objects:** A genuine measurable inverse and mutually inverse pushforward/lift maps on all scalar-clock couplings.

**Proof detail:** Apply Lusin–Souslin to the injective map, extend its measurable inverse, and use almost-everywhere inverse identities and exact marginals to prove both composition identities and equivalence of clock order.

**Sources:** [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=30), Section 424B(b)–(d), 424C–424D, pp. 30–31; Section 424G, p. 31; [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf), Section 235G, integration along an inverse-measure-preserving map; [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf), Section 2.2, Definition 2.1 and equations (2.6)–(2.7), p. 12; Section 2.3, Remark 2.13, equations (2.14)–(2.15), p. 20.

Source relation (composition): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Recovering original couplings from measurable label and scalar clock coordinates

Lusin--Souslin gives a genuine measurable inverse to the injective label-clock map on a
Borel regular domain. On each fixed label, pushing both coordinates through the original
clock and lifting through this same inverse give mutually inverse maps on all couplings.
The correspondence preserves and reflects increasing clock order. No density or absolute
continuity of any conditional measure is assumed.
-/

open Set MeasureTheory Filter

noncomputable section
namespace OTSelector.Reconstruction

variable {M Z : Type*} [MeasurableSpace M] [MeasurableSpace Z]

/-- The original label and clock form a measurable embedding of their Borel injectivity
domain. The codomain needs only countable separation of measurable points. -/
theorem measurableEmbedding_labelClock [StandardBorelSpace M]
    [MeasurableSpace.CountablySeparated Z] {N : Set M} (hN : MeasurableSet N)
    {a : M → Z} {u : M → ℝ} (ha : Measurable a) (hu : Measurable u)
    (hinj : Function.Injective (fun x : N ↦ (a x.val, u x.val))) :
    MeasurableEmbedding (fun x : N ↦ (a x.val, u x.val)) := by
  let _instLabelClockDomainBorel : StandardBorelSpace N := hN.standardBorel
  obtain ⟨tZ, hsecond, hT4, hopen⟩ :=
    exists_opensMeasurableSpace_of_countablySeparated Z
  let _instLabelClockLabelTopology : TopologicalSpace Z := tZ
  let _instLabelClockLabelSecondCountable : SecondCountableTopology Z := hsecond
  let _instLabelClockLabelT4 : T4Space Z := hT4
  let _instLabelClockLabelOpens : OpensMeasurableSpace Z := hopen
  exact ((ha.comp measurable_subtype_coe).prodMk
    (hu.comp measurable_subtype_coe)).measurableEmbedding hinj

/-- A total measurable inverse recovers every original point on the domain and is an
actual two-sided inverse on its label-clock image. Only the ambient space need be nonempty. -/
theorem exists_measurable_labelClock_inverse [StandardBorelSpace M] [Nonempty M]
    [MeasurableSpace.CountablySeparated Z] {N : Set M} (hN : MeasurableSet N)
    {a : M → Z} {u : M → ℝ} (ha : Measurable a) (hu : Measurable u)
    (hinj : Function.Injective (fun x : N ↦ (a x.val, u x.val))) :
    ∃ b : Z × ℝ → M, Measurable b ∧ (∀ x ∈ N, b (a x, u x) = x) ∧
      ∀ p ∈ (fun x ↦ (a x, u x)) '' N, b p ∈ N ∧ (a (b p), u (b p)) = p := by
  have he := measurableEmbedding_labelClock hN ha hu hinj
  obtain ⟨b, hb, hbf⟩ := he.exists_measurable_extend
    (measurable_subtype_coe : Measurable ((↑) : N → M)) (fun _ ↦ inferInstance)
  have hi (x : M) (hx : x ∈ N) : b (a x, u x) = x := congrFun hbf ⟨x, hx⟩
  refine ⟨b, hb, hi, ?_⟩
  rintro p ⟨x, hx, rfl⟩
  rw [hi x hx]
  exact ⟨hx, rfl⟩

private theorem map_map_eq_of_ae_leftInverse
    {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    {f : S → T} {g : T → S} (hf : Measurable f) (hg : Measurable g)
    {μ : Measure S} (hi : ∀ᵐ x ∂μ, g (f x) = x) : (μ.map f).map g = μ := by
  rw [Measure.map_map hg hf]
  calc
    μ.map (g ∘ f) = μ.map id := Measure.map_congr hi
    _ = μ := Measure.map_id

private theorem map_map_prod_eq_of_coupling
    {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    {f : S → T} {g : T → S} (hf : Measurable f) (hg : Measurable g)
    {μ ν : Measure S} {π : Measure (S × S)} (hπ : Vlasov.IsCoupling π μ ν)
    (hμ : ∀ᵐ x ∂μ, g (f x) = x) (hν : ∀ᵐ x ∂ν, g (f x) = x) :
    (π.map (Prod.map f f)).map (Prod.map g g) = π := by
  have hleft : ∀ᵐ p ∂π, g (f p.1) = p.1 :=
    ae_of_ae_map measurable_fst.aemeasurable (by rwa [hπ.1])
  have hright : ∀ᵐ p ∂π, g (f p.2) = p.2 :=
    ae_of_ae_map measurable_snd.aemeasurable (by rwa [hπ.2])
  apply map_map_eq_of_ae_leftInverse (hf.prodMap hf) (hg.prodMap hg)
  filter_upwards [hleft, hright] with p hp hq
  exact Prod.ext hp hq

private def scalarCouplingEquivOfInverse {u : M → ℝ} (hu : Measurable u)
    {g : ℝ → M} (hg : Measurable g) (μ ν : Measure M)
    (hμ : ∀ᵐ x ∂μ, g (u x) = x) (hν : ∀ᵐ x ∂ν, g (u x) = x) :
    {π : Measure (M × M) // Vlasov.IsCoupling π μ ν} ≃
      {κ : Measure (ℝ × ℝ) // Vlasov.IsCoupling κ (μ.map u) (ν.map u)} := by
  have hμinv := map_map_eq_of_ae_leftInverse hu hg hμ
  have hνinv := map_map_eq_of_ae_leftInverse hu hg hν
  have hscalar (ρ : Measure M) (hρ : ∀ᵐ x ∂ρ, g (u x) = x) :
      ∀ᵐ t ∂ρ.map u, u (g t) = t := by
    apply (ae_map_iff hu.aemeasurable
      (measurableSet_eq_fun (hu.comp hg) measurable_id)).mpr
    exact hρ.mono fun _ hx ↦ congrArg u hx
  refine
    { toFun := fun π ↦ ⟨π.val.map (Prod.map u u), π.property.map u u hu hu⟩
      invFun := fun κ ↦ ⟨κ.val.map (Prod.map g g), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · simpa only [hμinv, hνinv] using κ.property.map g g hg hg
  · intro π
    apply Subtype.ext
    exact map_map_prod_eq_of_coupling hu hg π.property hμ hν
  · intro κ
    apply Subtype.ext
    exact map_map_prod_eq_of_coupling hg hu κ.property (hscalar μ hμ) (hscalar ν hν)

/-- The constructed measurable inverse transports every fixed-label coupling exactly
between original points and their scalar clocks, preserving and reflecting clock order.
The two measures may be arbitrary, including zero or infinite measures. -/
theorem exists_labelClock_couplingEquiv [StandardBorelSpace M] [Nonempty M]
    [MeasurableSpace.CountablySeparated Z] {N : Set M} (hN : MeasurableSet N)
    {a : M → Z} {u : M → ℝ} (ha : Measurable a) (hu : Measurable u)
    (hinj : Function.Injective (fun x : N ↦ (a x.val, u x.val))) :
    ∃ b : Z × ℝ → M, Measurable b ∧ (∀ x ∈ N, b (a x, u x) = x) ∧
      ∀ (z : Z) (μ ν : Measure M),
        (∀ᵐ x ∂μ, x ∈ N ∧ a x = z) → (∀ᵐ x ∂ν, x ∈ N ∧ a x = z) →
        ∃ e : {π : Measure (M × M) // Vlasov.IsCoupling π μ ν} ≃
            {κ : Measure (ℝ × ℝ) // Vlasov.IsCoupling κ (μ.map u) (ν.map u)},
          (∀ π, (e π).val = π.val.map (Prod.map u u)) ∧
          (∀ κ, (e.symm κ).val = κ.val.map
            (Prod.map (fun t ↦ b (z, t)) (fun t ↦ b (z, t)))) ∧
          ∀ π, (∀ᵐ p ∂π.val, u p.1 ≤ u p.2) ↔ ∀ᵐ p ∂(e π).val, p.1 ≤ p.2 := by
  obtain ⟨b, hb, hi, _⟩ := exists_measurable_labelClock_inverse hN ha hu hinj
  refine ⟨b, hb, hi, ?_⟩
  intro z μ ν hμ hν
  have hg : Measurable (fun t : ℝ ↦ b (z, t)) := hb.comp (measurable_const.prodMk measurable_id)
  have hμi : ∀ᵐ x ∂μ, b (z, u x) = x := hμ.mono fun x hx ↦ by
    rw [← hx.2]
    exact hi x hx.1
  have hνi : ∀ᵐ x ∂ν, b (z, u x) = x := hν.mono fun x hx ↦ by
    rw [← hx.2]
    exact hi x hx.1
  refine ⟨scalarCouplingEquivOfInverse hu hg μ ν hμi hνi, fun _ ↦ rfl, fun _ ↦ rfl, ?_⟩
  intro π
  exact (ae_map_iff (hu.prodMap hu).aemeasurable
    (measurableSet_le measurable_fst measurable_snd)).symm

end OTSelector.Reconstruction

end
end
