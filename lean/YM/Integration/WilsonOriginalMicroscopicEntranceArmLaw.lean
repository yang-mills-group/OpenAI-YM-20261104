import YM.Integration.WilsonOriginalMicroscopicEntranceArms
import YM.Integration.WilsonOriginalMicroscopicEntranceEarlier

/-! Signed entrance reading and its conditional absolute wage at any earlier
physical decoder, on the original held field and true positive quiet. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceArmLaw
open Finset MeasureTheory Lattice Wilson RG OPE.Therm Push Marker PhysicalNext.Repeat.Legato
open WilsonOriginalMicroscopicEntranceDeposits (funded mean reading)
open WilsonOriginalMicroscopicEntranceEarlier (face salary carry)
open WilsonReflectedFundedHearing (Arm cropped signed)
open WilsonOriginalMicroscopicEntranceArms (physical)
open WilsonThermometerSolitaryExchange (share)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){N p K f:ℕ}
local notation "C" => R.family
local notation "J" => Stock.census (Fin 3)

def hearing {d:Fin 3 → ℕ}(A:∀a,Arm R (d a) N p f K)(stop:f ≤ K)(live:K ≤ N)(s:(J).Mode)
    (U:Config G ((C).side f p)):ℂ:=
  let X:=fun a=>physical R (A a) (stop.trans live)
  let B:=fun a=>cropped R (A a) stop
  let x:=fun a=>mean (C) N (X a) f U
  let y:=fun a=>mean (C) N (B a) f U
  ((∑i∈Ico f N,reading (C) N X s.val f i U)-(∑i∈Ico f K,reading (C) N B s.val f i U))+
    ∑a,signed R (A a) U*share x y a s

theorem original (d:Fin 3 → ℕ)(A:∀a,Arm R (d a) N p f K)(stop:f ≤ K)(live:K ≤ N)
    (ready:∀a,(C).ref (d a) ≤ f)(s:(J).Mode){u:ℕ}(earlier:u ≤ f)(W:Config G ((C).side u p)):
    let X:=fun a=>physical R (A a) (stop.trans live)
    let B:=fun a=>cropped R (A a) stop
    let D:=hearing R A stop live s
    let gap:=actualTransport (C) (N:=N) (face X s) (earlier.trans (stop.trans live)) W-
      actualTransport (C) (N:=N) (face B s) (earlier.trans stop) W
    gap=actualTransport (C) (N:=N) D earlier W ∧
      ‖gap‖ ≤ actualTransport (C) (N:=N) (fun U=>‖D U‖) earlier W:=by
  intro X B D gap
  have one(a):funded (X a):=by
    have h:Envelope (X a):=Envelope.compactC (WilsonReflectedOriginalTwoDeposit.continuous R _)
    exact ⟨h.meas,h.cost⟩
  have two(a):funded (B a):=by
    have h:Envelope (B a):=WilsonReflectedPlacedArm.trial_paid R (N:=N) (d a) stop (A a).w (A a).b (A a).s (A a).o
    exact ⟨h.meas,h.cost⟩
  obtain ⟨ma,xcap,cx⟩:=salary X one s
  obtain ⟨mb,bcap,cb⟩:=salary B two s
  have edge(U):actualTransport (C) (N:=N) (face X s) (stop.trans live) U-
      actualTransport (C) (N:=N) (face B s) stop U=D U:=
    WilsonOriginalMicroscopicEntranceArms.original R d A stop live ready s U
  have equal:gap=actualTransport (C) (N:=N) D earlier W:=
    carry (C) R.makes live stop earlier _ _ ⟨ma,_,cx⟩ ⟨mb,_,cb⟩ D edge W
  have first:=actualTransport_weighted_integrable (C) R.makes (le_refl N) ma.aestronglyMeasurable cx (stop.trans live)
  have last:=actualTransport_weighted_integrable (C) R.makes live mb.aestronglyMeasurable cb stop
  have paid:Integrable (fun U=>((C).path.rep N p f).eval U • D U) (prior G _):=by
    apply (first.sub last).congr
    exact Filter.Eventually.of_forall fun U=>by
      change _-_ = ((C).path.rep N p f).eval U • D U
      rw [←edge U,smul_sub]
  exact ⟨equal,equal ▸ ActualWilsonAbsoluteTransport.dominated (C) R.makes (stop.trans live) paid earlier W⟩

end YM.Integration.WilsonOriginalMicroscopicEntranceArmLaw
end
