import YM.Integration.WilsonRootedInteriorPhysicalExponent
import YM.Integration.WilsonPhysicalHistoryRetainedActivity
import YM.Integration.LocalComparisonPreReset

/-! The signed first-interior discrepancy on the exact selected Spring and its original numbered rows. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedInteriorPhysicalExponent
open Function Filter Lattice Wilson RG Marker PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open IterationFour IterationFour.Vacuum LocalComparison GapsLocal.Renew
open RG.Supply Pressure Extra.Histories ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open OriginalMarkedRunAction
open scoped BigOperators Classical
variable {G : Gauge} (R : Run G) {N per j : ℕ} (hj : j<N) {d : ℕ}
local notation "X" => R.family.path.rep N per j
local notation "Q" => approximation R (p:=per) hj d
local notation "E" => remainder R (p:=per) hj d
local notation "g" => Pert.Asymptotics.regulatorRun R.family N per j
local notation "fare" => (Real.sqrt 2 * Pert.Asymptotics.regulatorRun R.family N per (j+1))^(d+1)

private theorem mask_add {n : Side} (θ : ℝ) (S : Support n) (f h : Config G n→ℝ) (U : Config G n) :
    masked θ S (f+h) U=masked θ S f U+masked θ S h U := by
  by_cases live:Healthy θ S U
  · rw [masked_eq θ S (f+h) U live,masked_eq θ S f U live,masked_eq θ S h U live]
    rfl
  · rw [masked_ne θ S (f+h) U live,masked_ne θ S f U live,masked_ne θ S h U live,add_zero]

/-- The exact local signed subtraction on the physically enrolled addresses, before summation. -/
theorem occurrence (A : Comparison R (p:=per) hj d) (i : ℕ) (U : Config G (R.family.side j per)) :
    (X).activities.regularOccurrence (X).p i U=(Q).activities.regularOccurrence (X).p i U+
      (E).regularOccurrence (X).p i U := by
  obtain ⟨_,kept,omitted,rows,_,_,_⟩:=retained_rows R hj A
  calc
    _ = masked (X).p.threshold ((X).activities.reg i).support ((Q).activities.E i+(E).E i) U :=
      congrArg (fun f=>masked (X).p.threshold ((X).activities.reg i).support f U) (congrFun rows i)
    _ = masked (X).p.threshold ((X).activities.reg i).support ((Q).activities.E i) U+
        masked (X).p.threshold ((X).activities.reg i).support ((E).E i) U :=
      mask_add (X).p.threshold ((X).activities.reg i).support ((Q).activities.E i) ((E).E i) U
    _ = _ := congrArg₂ (·+·)
      (congrArg (fun A : ℕ→RegularAddress (R.family.side j per) =>
        masked (X).p.threshold (A i).support ((Q).activities.E i) U) kept.symm)
      (congrArg (fun A : ℕ→RegularAddress (R.family.side j per) =>
        masked (X).p.threshold (A i).support ((E).E i) U) omitted.symm)

/-- The exact renewed part and the *paid* omitted row series form the entire physical
exponent discrepancy with any independently specified fresh layer list. -/
theorem spring (A : Comparison R (p:=per) hj d) : (E).EBound (X).p (fare) ∧
    ∀ U : Config G (R.family.side j per),
    Summable (fun i=>(Q).activities.regularOccurrence (X).p i U) ∧
    Summable (fun i=>(E).regularOccurrence (X).p i U) ∧
    ∀ L : List (Piece G (R.family.side j per)), discrepancy R (N:=N) L U=
      ((Q).activities.additive (X).p U - Render.renders (Render.prefactor (g)) (X).p U L) +
      (E).additive (X).p U := by
  have fee:=(retained_rows R hj A).2.2.2.2.2.2
  refine ⟨fee,?_⟩
  intro U
  have all : Summable (fun i=>(X).activities.regularOccurrence (X).p i U) := PreReset.series_of_EBound (R.makes.wilson.represents N per j hj.le).good.labels.boundE U
  have omitted:=PreReset.series_of_EBound fee U
  have kept : Summable (fun i=>(Q).activities.regularOccurrence (X).p i U) :=
    (all.sub omitted).congr (fun i=>by
      change (X).activities.regularOccurrence (X).p i U-(E).regularOccurrence (X).p i U=_
      rw [occurrence R hj A i U,add_sub_cancel_right])
  refine ⟨kept,omitted,?_⟩
  intro L
  unfold discrepancy Activities.additive
  rw [tsum_congr (fun i=>occurrence R hj A i U),kept.tsum_add omitted]
  ring

/-- A single cutoff-independent level threshold on this original paid R buys the
whole signed identity, including the complete true lower layer selection, for every period. -/
theorem calendar (hG : G.Simple) (marks : Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees : Mallow.RG12.Earned (checkout G) R.kit.shape R.alloy.delay) (d : ℕ) :
    ∀ᶠ j : ℕ in atTop, ∀ (N per : ℕ) (hj : j<N),
      let out := R.family.path.rep N per j
      let kept := approximation R (p:=per) hj d
      let omitted := remainder R (p:=per) hj d
      omitted.EBound out.p ((Real.sqrt 2 * Pert.Asymptotics.regulatorRun R.family N per (j+1))^(d+1)) ∧
      ∀ U, Summable (fun i=>kept.activities.regularOccurrence out.p i U) ∧ Summable (fun i=>omitted.regularOccurrence out.p i U) ∧
        ∀ L : List (Piece G (R.family.side j per)), discrepancy R (N:=N) L U=
          (kept.activities.additive out.p U-Render.renders (Render.prefactor (Pert.Asymptotics.regulatorRun R.family N per j)) out.p U L)+omitted.additive out.p U := by
  filter_upwards [OriginalMarkedRunAction.calendar R hG marks fees d] with j bought
  exact fun N per hj=>spring R hj (bought N per hj)

end YM.Integration.WilsonRootedInteriorPhysicalExponent
