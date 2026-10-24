import OTSelector.Reconstruction.FinslerOriginalBlockwiseStabilization

/-!
# Hupper lane end-to-end assembly

This module assembles the `hupper` readout of the blockwise stabilization chain from
the two genuinely remaining analytic inputs, packaged as precise named hypotheses:

* (a) **matching moment / pressure budget.**  The optimal block matching has average
  matching cost bounded by the pressure scale; the normalized residual moment of
  that optimal matching is `momentRate L`, with `momentRate L -> 0`.  The heavy
  lifting of (a) is `TaylorRootCover.matching_moment_bound`
  (`FinslerOriginalPhysicalCostRemainder`): total squared matched displacement
  ≤ (dim / ((1 - 2 eps) m)) * total physical matching cost, together with the
  block-scale pressure budget that bounds that cost by the reference pressure scale.
* (b) **mark modulus of the marked point law coupling.**  There is a coupling of the
  block marked point law with the reference marked point law whose mark modulus at
  the pairing scale decays: `markRate L -> 0` after dividing the coupling integral
  by `L ^ q`.

Composing (a) and (b) gives the quantitative blockwise stabilization error
`err L = momentRate L + markRate L -> 0`, hence, by
`eventually_kernelMarkedScalePressure_le_of_error_bound`, the `hupper` readout:
for every `eps > 0` the reference scale pressure is eventually at most `p + eps`,
where `p` is the reference constant-kernel limit.  Nothing analytic is assumed
silently: the residual rates are explicit hypotheses and the composed error is
their sum.  The exact remaining sub-gap is the *production* of the two rates from
the coupling construction and the pressure budget (the hupper lane still has to
prove the normalized coupling integral of the marked-edge error is `o(1)`); this
module proves the composition, so that the hupper lane only needs to fill (a) and
(b).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- **Hupper lane end-to-end assembly.**  From the matching moment pressure budget
rate (a) and the mark modulus coupling rate (b), both tending to `0`, together with
the quantitative blockwise stabilization they produce, one gets an explicit
vanishing error function and the `hupper` upper readout at the reference
constant-kernel limit `p`. -/
theorem hupper_readout_of_matching_moment_and_mark_modulus
    (q m J : ℕ) [NeZero m] (hq : 4 < q) (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    (hJ2 : 2 ^ J ≤ 2 * m)
    (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt]
    {C G t : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_nonneg : ∀ a b v, 0 ≤ kin a b v)
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hkin_homog : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l => c * v l) = c ^ 2 * kin a b v)
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G)
    {p : ℝ} {momentRate markRate : ℝ → ℝ}
    (hmoment : Tendsto momentRate atTop (𝓝 0))
    (hmark : Tendsto markRate atTop (𝓝 0))
    (hstab : QuantitativeBlockwiseStabilization q m Ks Kt kin g t
      (fun L => momentRate L + markRate L))
    (href : Tendsto (fun L : ℝ =>
      kernelMarkedScalePressure q A B Ks Kt kin g L t) atTop (𝓝 p)) :
    ∃ err : ℝ → ℝ, Tendsto err atTop (𝓝 0) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ L : ℝ in atTop,
        kernelMarkedScalePressure q A B Ks Kt kin g L t ≤ p + ε := by
  have herr : Tendsto (fun L : ℝ => momentRate L + markRate L) atTop (𝓝 0) := by
    simpa using hmoment.add hmark
  refine ⟨fun L => momentRate L + markRate L, herr, ?_⟩
  exact eventually_kernelMarkedScalePressure_le_of_error_bound (q := q) (m := m)
    (J := J) hq hm hJ hJ2 Ks Kt (t := t) hC0 hG0 hkin hkin_nonneg hkin_bound
    hkin_homog hg hgb herr hstab href

/-- **The `hupper` readout, spelled out.**  Same composition, stated directly in
the `forall eps > 0, eventually` form required by the aggregate lane. -/
theorem eventually_kernelMarkedScalePressure_le_of_matching_moment_and_mark_modulus
    (q m J : ℕ) [NeZero m] (hq : 4 < q) (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    (hJ2 : 2 ^ J ≤ 2 * m)
    (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt]
    {C G t : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_nonneg : ∀ a b v, 0 ≤ kin a b v)
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hkin_homog : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l => c * v l) = c ^ 2 * kin a b v)
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G)
    {p : ℝ} {momentRate markRate : ℝ → ℝ}
    (hmoment : Tendsto momentRate atTop (𝓝 0))
    (hmark : Tendsto markRate atTop (𝓝 0))
    (hstab : QuantitativeBlockwiseStabilization q m Ks Kt kin g t
      (fun L => momentRate L + markRate L))
    (href : Tendsto (fun L : ℝ =>
      kernelMarkedScalePressure q A B Ks Kt kin g L t) atTop (𝓝 p)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ L : ℝ in atTop,
      kernelMarkedScalePressure q A B Ks Kt kin g L t ≤ p + ε := by
  have herr : Tendsto (fun L : ℝ => momentRate L + markRate L) atTop (𝓝 0) := by
    simpa using hmoment.add hmark
  exact eventually_kernelMarkedScalePressure_le_of_error_bound (q := q) (m := m)
    (J := J) hq hm hJ hJ2 Ks Kt (t := t) hC0 hG0 hkin hkin_nonneg hkin_bound
    hkin_homog hg hgb herr hstab href

end OTSelector.Reconstruction
