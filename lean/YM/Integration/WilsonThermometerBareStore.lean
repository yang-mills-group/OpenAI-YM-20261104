import YM.Integration.WilsonThermometerBareHall
import YM.Integration.WilsonCenteredFiledAtoms

/-! Install each literal microscopic face of the thermometer on the selected
Wilson hierarchy itself. A failed union of the three original stencils is
charged to the original compulsory inventory by its native keeper. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerBareStore
open Finset Function Lattice Wilson RG Source Marker Push.Local Planned.GuardedAtom Extra.Histories
open FVA1 PhysicalNext.Repeat.Legato Next.Rank Next.Foundations QuadraticLocal
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonPositionThermometerGradedReading WilsonThermometerBareHall
open WilsonCenteredFiledAtoms
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) (A : Group R.family 6) (simple : G.Simple) {N per : ℕ}
local notation "J" => Stock.census (Fin 3)
local notation "C" => R.family
local notation "P" => R.family.path.rep N per N
local notation "S" => R.family.localSection 0
local notation "Y" => R.family.params
local notation "η" => R.family.path.levels.clock.forcedAllowance N
local notation "X₀" => Config G (R.family.side N per)
variable (o : Positions (Fin 3) (R.family.side N per)) (s : (J).Mode) (y : Site (R.family.side N per))
local notation "f" => WilsonThermometerCourseHot.bare R A o s
local notation "Z" => hall (R:=R) o s y
local notation "slipped" => WilsonThermometerBareHall.slip R A o s y

def fee (κ E μ : ℝ) (rad : ℕ) := cartage (P).p (Y) (S) μ η κ
  (reservedMass (P).p Z (max (tested R A (N:=N) (per:=per) s rad) E)) 0

include simple in
theorem offered (refs : ∀ j : Fin 3, (C).ref (grade j) ≤ N) (rad : ℕ)
    (near : ∀ j∈s.val, separation (o.origin j) y ≤ rad) {κ E μ : ℝ} (div : 0 < κ)
    (room : hitWidth (P).p*η ≤ 1) (read : Readable (Y) (S) (P).p (R.family.side N per) μ)
    (whole : ∀ U : X₀, ‖(f) U‖ ≤ E) :
    Store (P) (S) (Y) y κ (fee R A o s y κ E μ rad) (fun U=>((P).eval U : ℂ)*(f) U) := by
  let dx := tested R A (N:=N) (per:=per) s rad
  let e := max dx E
  let a := reservedMass (P).p Z e
  let K := OriginalForcedAddresses.actual_keeper R simple N N per le_rfl
  have law := (R.makes.wilson.represents N per N le_rfl).good
  have hz : y∈Z := mem_insert_self ..
  have heard := germ R A o s refs y rad near
  have cap : (P).p.supBounds y Z (f) e := ⟨heard.2.1.trans (le_max_left ..),
    fun U healthy l ll dirs=>(heard.2.2 U healthy l ll dirs).trans (le_max_left ..)⟩
  have ads : SumBudget (fun _:Unit=>reservedMass (P).p Z e) a :=
    ⟨fun _=>mul_nonneg (Real.exp_nonneg _) cap.1,Summable.of_finite,by simp [a]⟩
  have blank : ForceFormat (P).p (P).activities y 0 :=
    ⟨by simp,by simp,fun _ _ _=>rfl,fun _ _ _ _ _=>rfl,fun _=>measurable_const⟩
  have quiet : ForceCost (P).p (P).activities 0 (κ*0) := by
    rw [mul_zero];exact ⟨fun _=>0,Extra.Histories.budget0 _ _,by simp⟩
  obtain ⟨D,form,bill,paid,-⟩ := WilsonCenteredMountedCapture.original y (fun _:Unit=>Z)
    (WilsonCenteredLampCapture.docket Unit) K (WilsonCenteredLampCapture.docket (Unit×Finset ℕ))
    0 (fun _:Unit=>(f)) (fun _:Unit=>(slipped)) 0 (S) (Y) law read div (Real.exp_nonneg _) room
    (fun _=>hz) (fun _=>heard.1) (fun _:Unit=>e) ads (fun _=>cap)
    (fun _=>attaches R A o s refs y rad near)
    (fun _ U=>(slip_cap R A o s y whole U).trans (le_max_right ..)) blank quiet
    (fun _=>Summable.of_finite) (fun _=>Summable.of_finite)
  refine ⟨D,form,bill.bound le_rfl,fun U=>?_⟩
  rw [paid]
  simp [WilsonThermometerBareHall.slip,Pi.sub_apply]

end YM.Integration.WilsonThermometerBareStore
