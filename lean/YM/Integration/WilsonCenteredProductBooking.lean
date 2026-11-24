import YM.Integration.WilsonCenteredOriginalProduct
import YM.RG16.Unmasked.Report
import YM.Extra.SOURCE_HISTORIES.Pencil

/-! Book a finite signed panel of heterogeneous original Wilson products on its
literal microscopic sites. The engineering factor is restored on each summand
before the native cutoff credit is compared to its deposited numerator. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredProductBooking
open Function Finset Filter Lattice RG Wilson Labels Source FVA1 Extra.Histories Next.Foundations
open Trace.Physical Trace.Physical.GermGraph RG16 RG16.Literal PhysicalNext.Repeat.Legato
open WilsonCenteredFiledAtoms WilsonCenteredOriginalProduct
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) (simple : G.Simple) {N per : ℕ} {J : Type}
  {I : J → Type} (grades : ∀ j,I j → ℕ) (v : ∀j t,R.family.label (grades j t))
  (sites : ∀j,I j → Site (R.family.side N per)) (faces : ∀j,Finset (I j))
  (c : J → ℂ) (taken : Finset J)
local notation "target" U:max j:max => word R (grades j) (v j) (sites j) (faces j) U
local notation "P" => R.family.path.rep N per N

def source (U : Config G (R.family.side N per)) := ∑j∈taken,c j*target U j

theorem original (d : ℕ) (refs : ∀j∈taken,∀ t,R.family.ref (grades j t) ≤ N) (date : R.t d ≤ N)
    (funded : WilsonCenteredCaptureClock.first R simple ≤ N) :
    Booked R.family N per d (source R grades v sites faces c taken) N le_rfl :=by
  let S:=R.family.localSection d
  let H:=R.family.params
  let κ:=LocalComparison.forcedDivisor R.family N
  let a:ℂ:=(R.family.S.a N:ℂ)^d
  let Y:=source R grades v sites faces c taken
  have invoices := (eventually_atTop.mp (WilsonCenteredCaptureClock.original R simple)).choose_spec N funded
  have div : 0 < κ:=invoices.1
  have law := (R.makes.wilson.represents N per N le_rfl).good
  have stock (j) (used : j∈taken) :
      ∃ t, Store (P) S H 0 κ t (fun U=>a*c j*(((P).eval U:ℂ)*target U j)) :=by
    let rad:=(faces j).sup (fun i=>separation (sites j i) 0)
    obtain ⟨price,q,fmt,paid,receipt⟩:=WilsonCenteredOriginalProduct.represented R (grades j) (v j) (sites j)
      (faces j) simple d (refs j used) date 0 rad (fun i hi=>le_sup (f:=fun i=>separation (sites j i) 0) hi) funded
    exact ⟨‖a*c j‖*price,stretch (a*c j) q,stretch_format _ fmt,stretch_rem _ paid,fun U=>
      (stretch_density S (P) 0 _ q U).trans (congrArg ((a*c j)*·) (receipt U))⟩
  have counted (b : Finset J) (sub : b⊆taken) :
      ∃ t,Store (P) S H 0 κ t (fun U=>∑j∈b,a*c j*(((P).eval U:ℂ)*target U j)) :=by
    induction b using Finset.induction_on with
    | empty =>simpa only [sum_empty] using ⟨0,WilsonCenteredFiledAtoms.empty S H 0 div⟩
    | @insert j b fresh ih =>
      obtain ⟨u,first⟩:=stock j (sub (mem_insert_self j b))
      obtain ⟨w,rest⟩:=ih (subset_trans (subset_insert _ _) sub)
      obtain ⟨q,form,bill,posted⟩:=WilsonCenteredFiledAtoms.add law div first rest
      exact ⟨u+w,q,form,bill,fun U=>by
        change q.density 0 S (P) U = ∑ k∈insert j b,a*c k*(((P).eval U:ℂ)*target U k)
        rw [sum_insert fresh];exact posted U⟩
  obtain ⟨t,q,fmt,paid,quoted⟩:=counted taken (Subset.rfl)
  refine ⟨q,t,⟨fmt,paid⟩,?_⟩
  rw [credit_bare R.family N per d R.makes]
  funext U
  change a*(((P).eval U:ℂ)*(∑j∈taken,c j*target U j))=q.density 0 S (P) U
  rw [quoted,mul_sum,mul_sum]
  exact sum_congr rfl fun _ _=>by ring

end YM.Integration.WilsonCenteredProductBooking
