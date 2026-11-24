import YM.Integration.WilsonOriginalMicroscopicEntranceExchange
import YM.Integration.WilsonReflectedFundedHearing

/-! At the original embedded sites, replace each conditional singleton by
the signed income of its actual filed one-source difference. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceArms
open Finset MeasureTheory Lattice Wilson RG OPE.Therm Push Marker PhysicalNext.Repeat.Legato
open WilsonOriginalMicroscopicEntranceDeposits (funded mean reading)
open WilsonReflectedFundedHearing (Arm source cropped signed)
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){N p f K:ℕ}
local notation "C" => R.family
local notation "J" => Stock.census (Fin 3)

def physical {d:ℕ}(A:Arm R d N p f K)(h:f ≤ N):Config G ((C).side N p) → ℂ:=
  WilsonReflectedOriginalTwoDeposit.raw R (source R A h)

theorem original (d:Fin 3 → ℕ)(A:∀a,Arm R (d a) N p f K)(stop:f ≤ K)(live:K ≤ N)
    (ready:∀a,(C).ref (d a) ≤ f)(s:(J).Mode)(W:Config G ((C).side f p)):
    let X:=fun a=>physical R (A a) (stop.trans live)
    let B:=fun a=>cropped R (A a) stop
    let x:=fun a=>mean (C) N (X a) f W
    let y:=fun a=>mean (C) N (B a) f W
    actualTransport (C) (N:=N) (fun U=>∏a∈s.val,X a U) (stop.trans live) W-
      actualTransport (C) (N:=N) (fun U=>∏a∈s.val,B a U) stop W=
      ((∑i∈Ico f N,reading (C) N X s.val f i W)-(∑i∈Ico f K,reading (C) N B s.val f i W))+
        ∑a,signed R (A a) W*WilsonThermometerSolitaryExchange.share x y a s:=by
  intro X B x y
  have one(a):funded (X a):=by
    have proof:Envelope (X a):=Envelope.compactC (WilsonReflectedOriginalTwoDeposit.continuous R (source R (A a) (stop.trans live)))
    exact ⟨proof.meas,proof.cost⟩
  have two(a):funded (B a):=by
    have proof:Envelope (B a):=WilsonReflectedPlacedArm.trial_paid R (N:=N) (d a) stop (A a).w (A a).b (A a).s (A a).o
    exact ⟨proof.meas,proof.cost⟩
  have identity:=WilsonOriginalMicroscopicEntranceExchange.original (C) R.makes live stop X B one two s W
  have change(a):x a-y a=signed R (A a) W:=
    WilsonReflectedFundedHearing.swap R (A a) stop live (ready a) W
  exact identity.trans (congrArg (fun z=>_+z) (sum_congr rfl (fun a _=>congrArg (fun z=>z*_) (change a))))

end YM.Integration.WilsonOriginalMicroscopicEntranceArms
end
