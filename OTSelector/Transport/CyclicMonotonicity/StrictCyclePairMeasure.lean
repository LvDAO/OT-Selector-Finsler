import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Probability.Kernel.Composition.Prod
import OTSelector.MeasureTheory.LocalFiniteMeasure
import OTSelector.MeasureTheory.LocalFiniteMeasureKernel
import OTSelector.Transport.CyclicMonotonicity.CountableLegalTargetRigidity
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerPhysicalSceneRootedCyclePairWitness.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerPhysicalSceneRootedCyclePairWitness`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.FinslerPhysicalSceneRootedCyclePairWitness

**Conditions:** The locally finite plan and parameter-dependent bad event are measurable; compact-square domination and legal support hypotheses are explicit in their respective statements.

**Objects:** Actual product-plan mass of strict-cycle pairs and its measurability/zero identities.

**Proof detail:** Integrate the event indicator against the measurable product kernel, dominate by a compact square when applicable, and use product almost-everywhere statements plus the legal two-cycle inequality to force zero mass.

**Sources:** [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18), Section 452A–452F (integration of families and disintegrations), 452M (product disintegration); [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=144), Section 5B, Theorem 5.28 (Tonelli), printed p. 129, PDF page 144; [D. H. Fremlin, Measure Theory, Volume 4, Chapter 41](https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=6), 411N(b)–(e), p. 6: support, uniqueness, existence, and the closure of the continuous image of a support.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-! Measurable strict-cycle masses of the same actual locally finite plans. -/
open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

section PairMass
variable {S X : Type*} [MeasurableSpace S]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X]
  [LocallyCompactSpace X] [PseudoMetrizableSpace X] [SigmaCompactSpace X]

/-- The actual plan's two-edge product mass of a parameter-dependent Borel
cycle event. No independent plan or target experiment is substituted. -/
def physicalSceneCyclePairMass (plan : S → LocalFiniteMeasure X)
    (bad : Set (S × (X × X))) (s : S) : ℝ≥0∞ :=
  (plan s : Measure X).prod (plan s) (Prod.mk s ⁻¹' bad)

/-- Actual locally finite measure kernels supply measurability of the complete
cycle-pair readout, even when the true macro coefficient is only measurable. -/
theorem measurable_physicalSceneCyclePairMass
    (plan : S → LocalFiniteMeasure X) (hplan : Measurable plan)
    {bad : Set (S × (X × X))} (hbad : MeasurableSet bad) :
    Measurable (physicalSceneCyclePairMass plan bad) := by
  let κ : Kernel S X := localFiniteMeasureKernel.comap plan hplan
  have hm := (κ ×ₖ κ).measurable_kernel_prodMk_left hbad
  change Measurable (fun s ↦ (plan s : Measure X).prod (plan s) (Prod.mk s ⁻¹' bad))
  simpa only [Kernel.prod_apply, κ, Kernel.comap_apply,
    localFiniteMeasureKernel_apply] using hm

/-- A countable compact exhaustion will control the complete pair witness
using only actual compact masses of the same plan. -/
theorem physicalSceneCyclePairMass_le_compact_square
    (plan : S → LocalFiniteMeasure X) (bad : Set (S × (X × X))) (s : S)
    (K : Set X) (hsub : Prod.mk s ⁻¹' bad ⊆ K ×ˢ K) :
    physicalSceneCyclePairMass plan bad s ≤ (plan s : Measure X) K * (plan s : Measure X) K :=
  (measure_mono hsub).trans_eq (Measure.prod_prod _ _)

/-- Almost-everywhere exclusion of strict cycles gives zero actual pair mass. -/
theorem physicalSceneCyclePairMass_eq_zero_of_ae_ae
    (plan : S → LocalFiniteMeasure X) {bad : Set (S × (X × X))}
    (hbad : MeasurableSet bad) (s : S)
    (hzero : ∀ᵐ x ∂(plan s : Measure X), ∀ᵐ y ∂(plan s : Measure X),
      (s, (x, y)) ∉ bad) : physicalSceneCyclePairMass plan bad s = 0 := by
  have hmeas : MeasurableSet (Prod.mk s ⁻¹' bad) :=
    hbad.preimage (measurable_const.prodMk measurable_id)
  exact measure_eq_zero_iff_ae_notMem.mpr
    ((Measure.ae_prod_iff_ae_ae hmeas.compl).mpr hzero)
end PairMass

section CycleEvent
variable {S Z : Type*} [MeasurableSpace S] [MeasurableSpace Z]
local notation "Edge" => Z × Z

/-- Two original and two crossed legal edges with a strict actual cost gain,
localized to one fixed edge window. The original macro tag enters through c. -/
def physicalSceneStrictCyclePairEvent (c : S → Z → Z → ℝ)
    (legal K : Set Edge) (margin : ℝ) : Set (S × (Edge × Edge)) :=
  {p | p.2.1 ∈ K ∧ p.2.2 ∈ K ∧ p.2.1 ∈ legal ∧ p.2.2 ∈ legal ∧
    (p.2.1.1, p.2.2.2) ∈ legal ∧ (p.2.2.1, p.2.1.2) ∈ legal ∧
    margin < c p.1 p.2.1.1 p.2.1.2 + c p.1 p.2.2.1 p.2.2.2 -
      c p.1 p.2.1.1 p.2.2.2 - c p.1 p.2.2.1 p.2.1.2}

/-- Joint measurability of the unchanged original cost is enough; no constant
matrix is assigned to a whole macroscopic source piece. -/
theorem measurableSet_physicalSceneStrictCyclePairEvent
    (c : S → Z → Z → ℝ)
    (hc : Measurable (fun p : S × Edge ↦ c p.1 p.2.1 p.2.2))
    {legal K : Set Edge} (hlegal : MeasurableSet legal) (hK : MeasurableSet K)
    (margin : ℝ) : MeasurableSet (physicalSceneStrictCyclePairEvent c legal K margin) := by
  have hc0 : Measurable (fun p : S × (Edge × Edge) ↦ c p.1 p.2.1.1 p.2.1.2) := hc.comp (measurable_fst.prodMk measurable_snd.fst)
  have hc1 : Measurable (fun p : S × (Edge × Edge) ↦ c p.1 p.2.2.1 p.2.2.2) := hc.comp (measurable_fst.prodMk measurable_snd.snd)
  have hcross : Measurable (fun p : S × (Edge × Edge) ↦ c p.1 p.2.1.1 p.2.2.2) := hc.comp (measurable_fst.prodMk
    (measurable_snd.fst.fst.prodMk measurable_snd.snd.snd))
  have hcross' : Measurable (fun p : S × (Edge × Edge) ↦ c p.1 p.2.2.1 p.2.1.2) := hc.comp (measurable_fst.prodMk
    (measurable_snd.snd.fst.prodMk measurable_snd.fst.snd))
  exact (hK.preimage measurable_snd.fst).inter
    ((hK.preimage measurable_snd.snd).inter
      ((hlegal.preimage measurable_snd.fst).inter
        ((hlegal.preimage measurable_snd.snd).inter
          ((hlegal.preimage (measurable_snd.fst.fst.prodMk measurable_snd.snd.snd)).inter
            ((hlegal.preimage (measurable_snd.snd.fst.prodMk measurable_snd.fst.snd)).inter
              (measurableSet_lt measurable_const (((hc0.add hc1).sub hcross).sub hcross')))))))
end CycleEvent

section RetainedZero
variable {S Z : Type*} [MeasurableSpace S]
  [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z] [T2Space Z]
  [LocallyCompactSpace Z] [PseudoMetrizableSpace Z] [SigmaCompactSpace Z]
local notation "Edge" => Z × Z

/-- The actual carried support no-cycle inequality kills the strict-improvement
product witness. Crossed legality is checked in its original domain. -/
theorem physicalSceneStrictCyclePairMass_zero_of_carried_twoCycle
    (plan : S → LocalFiniteMeasure Edge) (c : S → Z → Z → ℝ)
    (hc : Measurable (fun p : S × Edge ↦ c p.1 p.2.1 p.2.2))
    {legal K : Set Edge} (hlegal : MeasurableSet legal) (hK : MeasurableSet K)
    {margin : ℝ} (hmargin : 0 ≤ margin) (s : S) (D : Set Edge)
    (hcarried : ∀ᵐ e ∂(plan s : Measure Edge), e ∈ D)
    (hmono : IsTwoCycleMonotoneOn (c s) D ((plan s : Measure Edge).support ∩ D))
    (hlift : ∀ e e' : Edge, e ∈ D → e' ∈ D →
      (e.1, e'.2) ∈ legal → (e'.1, e.2) ∈ legal →
      (e.1, e'.2) ∈ D ∧ (e'.1, e.2) ∈ D) :
    physicalSceneCyclePairMass plan (physicalSceneStrictCyclePairEvent c legal K margin) s = 0 := by
  apply physicalSceneCyclePairMass_eq_zero_of_ae_ae plan
    (measurableSet_physicalSceneStrictCyclePairEvent c hc hlegal hK margin) s
  have hsupp : ∀ᵐ e ∂(plan s : Measure Edge), e ∈ (plan s : Measure Edge).support :=
    (plan s : Measure Edge).support_mem_ae
  have hs := hsupp.and hcarried
  filter_upwards [hs] with e he
  filter_upwards [hs] with e' he' hbad
  obtain ⟨_, _, _, _, hcross, hcross', hgain⟩ := hbad
  have hD := hlift e e' he.2 he'.2 hcross hcross'
  have hle := hmono e.1 e.2 e'.1 e'.2 he he' hD.1 hD.2
  linarith
end RetainedZero
end OTSelector.Reconstruction

end
end
