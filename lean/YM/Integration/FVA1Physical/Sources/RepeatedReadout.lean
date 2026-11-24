import YM.LocalLTE.Sail.Pinnacle
import YM.Integration.FVA1Physical.Sources.TestedFields

/-! Physical joint-marker readings at every stage of a prescribed finite window.
The same terminal fields, transfer history, vacuum and bare partition are used
at every stage. The estimate is for the sector with no flags. -/

namespace YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics

open Function Filter Set MeasureTheory Lattice RG RG.Shoot Wilson Precision RG.Supply
open Input Org Extra.Histories Source Next.Foundations LocalLTE LocalLTE.Sail
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time UVNext.CouplingReset Cub Circlet Graces Roost
open Mallow Push.AbsoluteSums LocalLTE.Vinca VoucherB LocalLTE.Fan Menu
open ConnectedActivityE6 MergeProof MergeProof.Accent YM.Integration.FVA1Physical
open scoped BigOperators

variable {G : Gauge} {X : Metals G} {D : Rolls X.p} {A : Alloy X D} {P : Bolt A}
variable {N n i : ℕ} {I : Type} [DecidableEq I] [Fintype I]
variable (B : Marker.Census I) (Y : Batch (Issue.trail P) N n I)
variable (π : ∀ j : ℕ, j ≤ N → Y.steering j)
variable (fields : ∀ (j : I) (s : ℕ), ((Labels.frames G).level (Y.demand j)).Coeff →
  Coefficient ((Labels.frames G).level (Y.demand j)) ((Issue.trail P).S.side s n))
variable (hi : i < N) (O : Appendix B ((Issue.trail P).rep N n i))

/-- The readout error uses the pushed terminal marker polynomial and the physical
forecast before normalization. Mode tests may vary independently with both
the mode and the coarse configuration. -/
def physicalTestedStage (p K : ℕ) : Prop :=
  let H := Issue.trail P
  let Q := H.rep N n i
  let Q' := H.rep N n (i+1)
  let density := (A.B.a.clock.op i n).push Q'.beta Q'.eval
  let raw := gust H N n N (Y.raw B) i hi.le
  let forecasted := fun v => Marker.Poly.pass (Sail.forecast B O (spectralValue Y π fields hi) v)
  let good := {v : Config G (H.S.side i n) | flags Q.p.threshold v = ∅}
  let cost := (Sail.margin K * 2) * Coat.gStep Q'.beta ^ ((p : ℝ) + 1)
  let haar := prior G (H.S.side i n)
  let partition₀ := Wilson.partition G (H.S.side N n) (H.β N n N)
  ∀ u : Config G (H.S.side i n) → B.Mode → ℂ, (∀ v j, ‖u v j‖ ≤ 1) →
    let residual := fun v => modeTest (u v) (raw v - density v • forecasted v)
    (∀ v ∈ good, ‖residual v‖ ≤ density v * cost) ∧
      ((∀ j, Measurable (fun v => u v j)) →
        IntegrableOn residual good haar ∧ (∫ v in good, ‖residual v‖ ∂haar) / partition₀ ≤ cost) ∧
      ‖(∫ v in good, residual v ∂haar) / (partition₀ : ℂ)‖ ≤ cost

/-- Convert the multivariate conditional estimate to the physical Haar reading.
The partition identity and the integrability of the vacuum follow from the
selected history. No analytic estimate for the tested integral is assumed. -/
theorem physicalTestedStage_of_finePrint
    (V : ∀ d, Extra.Histories.Music ((Labels.frames G).level d) (Issue.trail P) N n)
    {p K : ℕ} (h : ∀ v, FinePrint V B Y π fields hi O p K v)
    (hfield : ∀ j, (pointF Y π fields hi j).Format (Y.origin i j) (hol G)
      ((Issue.trail P).rep N n i))
    (hmodel : O.model.Active)
    (hraw : Integrable (gust (Issue.trail P) N n N (Y.raw B) i hi.le)
      (prior G ((Issue.trail P).S.side i n))) :
    physicalTestedStage B Y π fields hi O p K := by
  let H := Issue.trail P
  let Q := H.rep N n i
  let Q' := H.rep N n (i+1)
  let q := (A.B.a.clock.op i n).push Q'.beta Q'.eval
  let good := {v : Config G (H.S.side i n) | flags Q.p.threshold v = ∅}
  let ε := (Sail.margin K * 2) * Coat.gStep Q'.beta ^ ((p : ℝ) + 1)
  let raw := gust H N n N (Y.raw B) i hi.le
  let predicted := fun v => Marker.Poly.pass (Sail.forecast B O (spectralValue Y π fields hi) v)
  have hq : Q.eval = q := (P.choice.steps N n i hi).1
  have hmargin : 0 ≤ Sail.margin K := by
    unfold Sail.margin
    exact mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun _ _ =>
      mul_nonneg (norm_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _))
  have hε : 0 ≤ ε := mul_nonneg (mul_nonneg hmargin (by norm_num))
    (Real.rpow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _)
  have hiq : Integrable q (prior G (H.S.side i n)) := by
    rw [← hq]
    exact (Q.envelope (P.choice.represents N n i hi.le).good).integrable _
  have htotal : (∫ v, q v ∂prior G (H.S.side i n)) =
      Wilson.partition G (H.S.side N n) (H.β N n N) := by
    rw [← hq]
    exact H.partition_eq P.choice N n i hi.le
  intro u hu
  let residual := fun v => modeTest (u v) (raw v - q v • predicted v)
  have hp : ∀ v ∈ good, ‖residual v‖ ≤ q v * ε := fun v hv =>
    unnormalized_modeTest_bound (u v) (raw v) (predicted v) (h v).volume (hu v)
      ((h v).sightings hv).2
  have hc := restricted_partition_bound _ q residual (flags_measurable_eq _ _)
    (Wilson.partition_pos _) hε hiq (fun v => (h v).volume.le) htotal hp
  refine ⟨hp, ?_, hc.2⟩
  intro htests
  apply hc.1
  have hs (j : I) : Measurable (spectralValue Y π fields hi j) :=
    (measurable_const.add (masked_measurable _ _ _
      ((localSection G (Y.demand j)).continuous_places ..).measurable)).add
        (Measurable.tsum fun k => masked_measurable _ _ _ ((hfield j).smooth k).borel)
  have hmach : Measurable (fun v => Mach B (fun j => spectralValue Y π fields hi j v)) := by
    refine Finset.measurable_fun_sum _ fun j _ => ?_
    have hsend : Continuous (Marker.Poly.send (B.fire j)) := by
      change Continuous (fun z : ℂ => (Marker.Poly.send (B.fire j) z).part)
      apply continuous_pi
      intro m
      simp only [Marker.Poly.part_send]
      split_ifs <;> fun_prop
    exact hsend.measurable.comp (hs j)
  have hpred : Measurable predicted :=
    Marker.Poly.pass_cont.measurable.comp (hmach.add (O.model.extra_meas hmodel))
  have hdelta := hraw.aestronglyMeasurable.sub
    (hiq.aestronglyMeasurable.smul hpred.aestronglyMeasurable)
  apply AEStronglyMeasurable.restrict
  exact Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
    (htests j).aestronglyMeasurable.mul ((Marker.Poly.part_cont j).comp_aestronglyMeasurable hdelta)

end YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
