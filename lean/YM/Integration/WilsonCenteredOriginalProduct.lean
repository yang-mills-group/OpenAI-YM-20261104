import YM.Integration.WilsonThermometerBareHall
import YM.Integration.WilsonCenteredFiledAtoms
import YM.Integration.WilsonCenteredCaptureClock
import YM.Integration.WilsonCapturedPrimarySection

/-! A finite product of arbitrary actual Wilson fields on their independently
placed top sites, housed on the true union of their section stencils. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredOriginalProduct
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Marker Push.Local
open Planned.GuardedAtom Extra.Histories PhysicalNext.Repeat.Legato Next.Rank Next.Foundations QuadraticLocal
open FVA1 Trace.Pilot MergeProof.East OriginalForcedAddresses WilsonCenteredFiledAtoms
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) {N per : ℕ}
  {I : Type} (grades : I → ℕ) (values : ∀j,R.family.label (grades j))
local notation "P" => R.family.path.rep N per N
local notation "X" => Config G (R.family.side N per)
variable (sites : I → Site (R.family.side N per)) (faces : Finset I)

def word : X → ℂ := fun U => ∏j∈faces,R.family.O N per (values j) (sites j) U

def hall (y : Site (R.family.side N per)) : Support (R.family.side N per) :=
  insert y (faces.biUnion (fun j => (R.family.localSection (grades j)).footprint (sites j)))

def individual (j : I) := ActualRunPhysicalPages.price R N (grades j)
  (Price.awake R.family (grades j) N N per (values j))

theorem germ (refs : ∀j,R.family.ref (grades j) ≤ N) (y : Site (R.family.side N per)) (rad : ℕ)
    (near : ∀j∈faces,separation (sites j) y ≤ rad) :
    (P).p.Regular (hall R grades sites faces y) (word R grades values sites faces) ∧
    (P).p.supBounds y (hall R grades sites faces y) (word R grades values sites faces)
      ((((faces.card+1:ℕ):ℝ)*(1+(rad:ℝ))^(P).p.power)^(P).p.order*∏j∈faces,individual R (N:=N) (per:=per) grades values j) :=by
  let f (j:I):= R.family.O N per (values j) (sites j)
  let foot (j:I):= (R.family.localSection (grades j)).footprint (sites j)
  have q (j:I) : (P).p.Regular (foot j) (f j) ∧ (P).p.supBounds (sites j) (foot j) (f j)
      (individual R (N:=N) (per:=per) grades values j) := by
    have paid := ActualRunPhysicalPages.priced R N per N (grades j) le_rfl (refs j)
      (Price.awake R.family (grades j) N N per (values j)) (sites j)
    rw [WilsonPositionThermometerStationBirth.kernel R N per (grades j) (refs j) (values j) (sites j)] at paid
    exact paid
  have contains (j : I) (hj : j∈faces) : foot j ⊆ hall R grades sites faces y := by
    intro x hx
    exact mem_insert_of_mem (mem_biUnion.mpr ⟨j,hj,hx⟩)
  have result:=price_product (B:=(P).p) (Y:=hall R grades sites faces y) faces f
    (individual R (N:=N) (per:=per) grades values) y sites rad near foot contains (fun j _=>(q j).1) (fun j _=>(q j).2)
  have applyprod : (∏ j∈faces,f j)=(word R (N:=N) (per:=per) grades values sites faces) := by funext U;exact prod_apply U _ _
  rw [applyprod] at result
  exact result


theorem represented (simple : G.Simple) (d : ℕ) (refs : ∀j,R.family.ref (grades j) ≤ N)
    (ready : R.t d ≤ N) (y : Site (R.family.side N per)) (rad : ℕ) (near : ∀j∈faces,separation (sites j) y ≤ rad)
    (bought : WilsonCenteredCaptureClock.first R simple ≤ N) :
    ∃ rent : ℝ, Store (P) (R.family.localSection d) (R.family.params) y (LocalComparison.forcedDivisor R.family N)
      rent (fun U => ((P).eval U:ℂ)*word R grades values sites faces U) :=by
  let f :=word R grades values sites faces
  let Z:=hall R grades sites faces y
  let κ:=LocalComparison.forcedDivisor R.family N
  let η:=R.family.path.levels.clock.forcedAllowance N
  have point := (R.makes.wilson.represents N per N le_rfl).vac
  have read := (WilsonCapturedPrimarySection.original R ready (P) point).1
  have original:=germ R grades values sites faces refs y rad near
  have regular : (P).p.Regular Z f :=original.1
  have bound := original.2
  have continuous : Continuous f :=continuous_finsetProd _ fun _ _=>R.family.continuousO N per _ _ _
  obtain ⟨price,hcap⟩ := isCompact_univ.exists_bound_of_continuousOn continuous.continuousOn
  have priceAll (U:X) : ‖f U‖≤price:=hcap U (Set.mem_univ _)
  let e:=max ((((faces.card+1:ℕ):ℝ)*(1+(rad:ℝ))^(P).p.power)^(P).p.order*∏j∈faces,individual R (N:=N) (per:=per) grades values j) price
  let μ:=(R.family.path.levels.params N).columns
  let K:=OriginalForcedAddresses.actual_keeper R simple N N per le_rfl
  have law:=(R.makes.wilson.represents N per N le_rfl).good
  have hz : y∈Z :=mem_insert_self ..
  have cap : (P).p.supBounds y Z f e:=⟨bound.1.trans (le_max_left ..),fun U healthy l ll dirs=>(bound.2 U healthy l ll dirs).trans (le_max_left ..)⟩
  let off:=f-masked (P).p.threshold Z f
  have slips : Attaches (P).p.threshold Z off :=by
    refine ⟨fun U W agree flags=>congrArg₂ (·-·) (regular.sites U W agree)
      (uses_mask _ regular.sites U W agree flags),
      fun t U=>congrArg₂ (·-·) (regular.symmetry t U) (invariant_mask regular.symmetry _ _ t U),
      regular.borel.sub (masked_measurable _ _ _ regular.borel),fun U healthy=>?_⟩
    exact sub_eq_zero.mpr (masked_eq _ _ _ _ healthy).symm
  have expense (U:X) : ‖off U‖≤e :=by
    by_cases good : Healthy (P).p.threshold Z U
    · rw [show off U=0 from sub_eq_zero.mpr (masked_eq _ _ _ _ good).symm,norm_zero];exact (norm_nonneg (f U)).trans ((priceAll U).trans (le_max_right ..))
    · simpa only [off,Pi.sub_apply,masked_ne _ _ _ _ good,sub_zero] using (priceAll U).trans (le_max_right _ _)
  have ads : SumBudget (fun _:Unit => reservedMass (P).p Z e) (reservedMass (P).p Z e) :=
    ⟨fun _=>mul_nonneg (Real.exp_nonneg _) cap.1,Summable.of_finite,by simp⟩
  have blank : ForceFormat (P).p (P).activities y 0 :=
    ⟨by simp,by simp,fun _ _ _=>rfl,fun _ _ _ _ _=>rfl,fun _=>measurable_const⟩
  have quiet : ForceCost (P).p (P).activities 0 (κ*0) :=by
    rw [mul_zero];exact ⟨fun _=>0,Extra.Histories.budget0 _ _,by simp⟩
  obtain ⟨hk,_,room⟩:=(eventually_atTop.mp (WilsonCenteredCaptureClock.original R simple)).choose_spec N bought
  obtain ⟨u,form,bill,earned,-⟩:=WilsonCenteredMountedCapture.original y (fun _:Unit=>Z)
    (WilsonCenteredLampCapture.docket Unit) K (WilsonCenteredLampCapture.docket (Unit×Finset ℕ))
    0 (fun _:Unit=>f) (fun _:Unit=>off) 0 (R.family.localSection d) R.family.params law read hk (Real.exp_nonneg _)
    (point ▸ room) (fun _=>hz) (fun _=>regular) (fun _:Unit=>e) ads (fun _=>cap)
    (fun _=>slips) (fun _=>expense) blank quiet (fun _=>Summable.of_finite) (fun _=>Summable.of_finite)
  refine ⟨_,u,form,bill.bound le_rfl,fun U=>?_⟩
  rw [earned]
  simp [off,f,Pi.sub_apply]

end YM.Integration.WilsonCenteredOriginalProduct
