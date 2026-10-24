import Mathlib.MeasureTheory.Measure.Support
import OTSelector.Transport.CyclicMonotonicity.CountableLegalTargetRigidity
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.MeasureTwoCycleSupport.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.MeasureTwoCycleSupport`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.MeasureTwoCycleSupport

**Conditions:** The plan is s-finite, the legal domain is open, the cost is continuous there, and the legal two-cycle inequality holds for almost every plan pair.

**Objects:** The same legal inequality on the actual topological support.

**Proof detail:** Product support contains pairs of support points; a strict violation persists on an open neighborhood of positive product mass, contradicting the almost-everywhere inequality.

**Sources:** [D. H. Fremlin, Measure Theory, Volume 4, Appendix 4A](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=6), Section 4A2A–4A2B, pp. 6–10 (closures, Hausdorff spaces, continuity and products); [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61), Section 437J(d), (f), (g) and Sections 437K–437L, narrow topology and semicontinuous evaluation; [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf), Sections 254G–254I and 254N–254O, infinite products, coordinate maps and subproducts; [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf), Section 2.2, Definition 2.1 and equations (2.6)–(2.7), p. 12; Section 2.3, Remark 2.13, equations (2.14)–(2.15), p. 20; [D. H. Fremlin, Measure Theory, Volume 4, Chapter 41](https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=6), 411N(b)–(e), p. 6: support, uniqueness, existence, and the closure of the continuous image of a support.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-! The almost-everywhere legal two-cycle inequality holds on the actual
support when the original cost is continuous on its open legal domain. -/

open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace OTSelector.Reconstruction

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y]

/-- Neighborhoods of two original support points have a positive product
mass, so their pair belongs to the product measure's support. -/
theorem mem_measure_prod_support_of_mem_support
    (μ : Measure X) (ν : Measure Y) [SFinite ν]
    {x : X} {y : Y} (hx : x ∈ μ.support) (hy : y ∈ ν.support) :
    (x, y) ∈ (μ.prod ν).support := by
  apply (Measure.mem_support_iff_forall _).mpr
  intro U hU
  obtain ⟨A, hA, B, hB, hsub⟩ := mem_nhds_prod_iff.mp hU
  have hApos := (Measure.mem_support_iff_forall _).mp hx A hA
  have hBpos := (Measure.mem_support_iff_forall _).mp hy B hB
  calc
    0 < μ A * ν B := by positivity
    _ = (μ.prod ν) (A ×ˢ B) := (Measure.prod_prod A B).symm
    _ ≤ (μ.prod ν) U := measure_mono hsub

/-- Almost-everywhere legal no-improvement for the same full plan upgrades
to the support relation used by countable-target rigidity. Continuity is
required only at legal old and crossed edges. -/
theorem isTwoCycleMonotoneOn_support_of_ae
    (π : Measure (X × Y)) [SFinite π]
    (c : X → Y → ℝ) {D : Set (X × Y)} (hD : IsOpen D)
    (hc : ContinuousOn (Function.uncurry c) D)
    (hcycle : ∀ᵐ p ∂π.prod π,
      p.1 ∈ D → p.2 ∈ D → (p.1.1, p.2.2) ∈ D → (p.2.1, p.1.2) ∈ D →
      c p.1.1 p.1.2 + c p.2.1 p.2.2 ≤ c p.1.1 p.2.2 + c p.2.1 p.1.2) :
    IsTwoCycleMonotoneOn c D (π.support ∩ D) := by
  intro x i y j hxi hyj hxj hyi
  by_contra hbad
  let gain : ((X × Y) × (X × Y)) → ℝ := fun p ↦
    c p.1.1 p.1.2 + c p.2.1 p.2.2 - c p.1.1 p.2.2 - c p.2.1 p.1.2
  have hcross : Continuous (fun p : (X × Y) × (X × Y) ↦ (p.1.1, p.2.2)) :=
    continuous_fst.fst.prodMk continuous_snd.snd
  have hcross' : Continuous (fun p : (X × Y) × (X × Y) ↦ (p.2.1, p.1.2)) :=
    continuous_snd.fst.prodMk continuous_fst.snd
  have hgain : ContinuousAt gain ((x, i), (y, j)) :=
    (((hc.continuousAt (hD.mem_nhds hxi.2)).comp (x := ((x, i), (y, j)))
      continuous_fst.continuousAt).add
      ((hc.continuousAt (hD.mem_nhds hyj.2)).comp (x := ((x, i), (y, j)))
        continuous_snd.continuousAt)).sub
        ((hc.continuousAt (hD.mem_nhds hxj)).comp (x := ((x, i), (y, j)))
          hcross.continuousAt) |>.sub
          ((hc.continuousAt (hD.mem_nhds hyi)).comp (x := ((x, i), (y, j)))
            hcross'.continuousAt)
  have hgainpos : 0 < gain ((x, i), (y, j)) := by
    dsimp [gain]
    linarith
  let bad : Set ((X × Y) × (X × Y)) := {p |
    p.1 ∈ D ∧ p.2 ∈ D ∧ (p.1.1, p.2.2) ∈ D ∧ (p.2.1, p.1.2) ∈ D ∧ 0 < gain p}
  have hbadnhds : bad ∈ 𝓝 ((x, i), (y, j)) := by
    filter_upwards [continuous_fst.continuousAt.eventually (hD.mem_nhds hxi.2),
      continuous_snd.continuousAt.eventually (hD.mem_nhds hyj.2),
      hcross.continuousAt.eventually (hD.mem_nhds hxj),
      hcross'.continuousAt.eventually (hD.mem_nhds hyi),
      hgain.eventually (Ioi_mem_nhds hgainpos)] with p h₀ h₁ h₂ h₃ h₄
    exact ⟨h₀, h₁, h₂, h₃, h₄⟩
  have hbadzero : (π.prod π) bad = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hcycle] with p hp hmem
    have hle := hp hmem.1 hmem.2.1 hmem.2.2.1 hmem.2.2.2.1
    have hpos := hmem.2.2.2.2
    dsimp [gain] at hpos
    linarith
  have hsupp := mem_measure_prod_support_of_mem_support π π hxi.1 hyj.1
  have hpos := (Measure.mem_support_iff_forall _).mp hsupp bad hbadnhds
  rw [hbadzero] at hpos
  exact (lt_irrefl 0) hpos

end OTSelector.Reconstruction

end
end
