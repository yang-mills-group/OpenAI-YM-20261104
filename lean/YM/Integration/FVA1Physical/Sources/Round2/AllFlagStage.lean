import YM.Integration.FVA1Physical.Sources.Round2.EventReadout

/-! A joint physical forecast on any measurable sector, including an anchored
healthy sector on which arbitrarily many distant flags may remain. -/

namespace YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics

open Filter MeasureTheory Lattice RG Wilson RG.Supply Input Org Source Extra.Histories LocalLTE LocalLTE.Sail
open MergeProof MergeProof.Accent YM.Integration.FVA1Physical YM.Integration.FVA1Physical.Round2
open Next.Foundations
open scoped BigOperators

variable {G : Gauge} {X : Metals G} {D : Rolls X.p} {A : Alloy X D} {P : Bolt A}
variable {N n i : ℕ} {I : Type} [DecidableEq I] [Fintype I]
variable (B : Marker.Census I) (Y : Batch (Issue.trail P) N n I)
variable (π : ∀ j : ℕ, j ≤ N → Y.steering j)
variable (F : ∀ (j : I) (s : ℕ), ((Labels.frames G).level (Y.demand j)).Coeff →
  Coefficient ((Labels.frames G).level (Y.demand j)) ((Issue.trail P).S.side s n))
variable (hi : i < N) (O : Appendix B ((Issue.trail P).rep N n i))
variable (V : ∀ d, Music ((Labels.frames G).level d) (Issue.trail P) N n)

private theorem measurableMach {S : Type*} [MeasurableSpace S] (B : Marker.Census I)
    (f : I → S → ℂ) (h : ∀ j, Measurable (f j)) :
    Measurable fun v => Mach B (fun j => f j v) := by
  apply Finset.measurable_fun_sum
  intro j _
  have hsend : Continuous (Marker.Poly.send (B.fire j)) := by
    change Continuous (fun z : ℂ => (Marker.Poly.send (B.fire j) z).part)
    apply continuous_pi
    intro k
    simp only [Marker.Poly.part_send]
    split_ifs <;> fun_prop
  exact hsend.measurable.comp (h j)

def allFlagStage (p K : ℕ) : Prop :=
  let H := Issue.trail P
  let μ := prior G (H.S.side i n)
  let Z := Wilson.partition G (H.S.side N n) (H.β N n N)
  let δ := fun v => gasForecast B Y π F hi O V v - gust H N n N (Y.raw B) i hi.le v
  (∀ v, Marker.Poly.price (fun _ => 1) (δ v) ≤ (H.rep N n i).eval v * gasReadoutCost (i := i) Y p K) ∧
    ∀ (u : Config G (H.S.side i n) → B.Mode → ℂ), (∀ v j, ‖u v j‖ ≤ 1) →
      (∀ j, Measurable fun v => u v j) → ∀ e : Set (Config G (H.S.side i n)), MeasurableSet e →
      let f := fun v => modeTest (u v) (δ v)
      IntegrableOn f e μ ∧
        (∫ v in e, ‖f v‖ ∂μ) / Z ≤ gasReadoutCost (i := i) Y p K * (OPE.Therm.scene H N n i).real e

theorem allFlagStage_of_finePrint {p K : ℕ} (h : ∀ v, FinePrint V B Y π F hi O p K v)
    (hp : Appendix.Prepared B ((Issue.trail P).rep N n i) O (Y.origin i) (Y.requested V i)
      (fun j => (Y.named V (π i hi.le) j).forced) (gust (Issue.trail P) N n N (Y.raw B) i hi.le))
    (hnamed : ∀ j, (Y.named V (π i hi.le) j).Format (Y.origin i j) (hol G) ((Issue.trail P).rep N n i))
    (hfield : ∀ j, (pointF Y π F hi j).Format (Y.origin i j) (hol G) ((Issue.trail P).rep N n i)) :
    allFlagStage B Y π F hi O V p K := by
  let H := Issue.trail P
  let Q := H.rep N n i
  let μ := prior G (H.S.side i n)
  let actual := gust H N n N (Y.raw B) i hi.le
  let forecast := gasForecast B Y π F hi O V
  let Δ := fun v => forecast v - actual v
  have hprice := physicalRetainedPrice B Y π F hi O V h hp
  refine ⟨hprice, ?_⟩
  intro u hu htests e he
  have hf (j : I) : Measurable (spectralValue Y π F hi j) :=
    (measurable_const.add (masked_measurable _ _ _
      ((localSection G (Y.demand j)).continuous_places ..).measurable)).add
        (Measurable.tsum fun k => masked_measurable _ _ _ ((hfield j).smooth k).borel)
  have hr (j : I) : Measurable (Y.requested V i j) := by
    rw [Batch.labels_equal Y V (π i hi.le) j]
    exact (measurable_const.add (masked_measurable _ _ _
      ((localSection G (Y.demand j)).continuous_places ..).measurable)).add
        (Measurable.tsum fun k => masked_measurable _ _ _ ((hnamed j).smooth k).borel)
  have ha : AEStronglyMeasurable actual μ := (gust_live H N n N (Y.raw B)
    (physicalSeed_integrable H P.choice B Y) hi.le).aestronglyMeasurable
  have hfm : Measurable (Sail.forecast B O (spectralValue Y π F hi)) :=
    (measurableMach B _ hf).add (O.model.extra_meas hp.shelf)
  have hrm : Measurable (Sail.receipt B O (Y.requested V i)) :=
    (measurableMach B _ hr).add (O.truth.extra_meas hp.entire)
  have heq : forecast = fun v => actual v * Marker.Poly.pass
      (Sail.forecast B O (spectralValue Y π F hi) v - Sail.receipt B O (Y.requested V i) v) :=
    funext fun v => Sail.Round2.retainedForecast_eq B Q O (Y.origin i)
      (Y.requested V i) (spectralValue Y π F hi) _ _ hp v (h v).vote.1 (h v).vote.2
  have hpred : AEStronglyMeasurable forecast μ := by
    rw [heq]
    exact ha.mul (Marker.Poly.pass_cont.measurable.comp (hfm.sub hrm)).aestronglyMeasurable
  have hm : AEStronglyMeasurable (fun v => modeTest (u v) (Δ v)) μ :=
    Finset.aestronglyMeasurable_fun_sum _ fun j _ => (htests j).aestronglyMeasurable.mul
      ((Marker.Poly.part_cont j).comp_aestronglyMeasurable (hpred.sub ha))
  exact eventReadout P.choice hi.le e he _ hm fun v =>
    (norm_modeTest_le_price (u v) (Δ v) (hu v)).trans (hprice v)

end YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
