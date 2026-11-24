import YM.Integration.WilsonReflectedRestartedPair

/-! The physical square and its finite marked restart are each signed before
taking either regulator. The same candidate in a given arm is used in both
hearings. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedSquare
open Function Finset MeasureTheory Lattice Wilson RG OPE.Therm Push PhysicalNext.Repeat.Legato
open WilsonReflectedOriginalTwoDeposit
open WilsonReflectedRestartedPair
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){N p K:ℕ}
local notation "C" => R.family
local notation "space" i:max => Config G ((C).side i p)

def rectangle (v:Bool→Bool→ℂ):ℂ:=(v true true-v false true)-(v true false-v false false)

theorem conditional {f:ℕ}(before:f≤K)(live:K≤N)(A B:Bool→space K→ℂ)
    (pA:∀t,Envelope (A t))(pB:∀t,Envelope (B t))(W:space f):
    actualTransport (C) (N:=N) (fun U=>(A true U-A false U)*(B true U-B false U)) before W =
      rectangle (fun t s=>actualTransport (C) (N:=N) (fun U=>A t U*B s U) before W):=by
  let face (t s:Bool)(U:space K):ℂ:=A t U*B s U
  have ok (t s:Bool):Envelope (face t s):=(pA t).mulC (pB s)
  have sub (u v:space K→ℂ)(hu:Envelope u)(hv:Envelope v):
      actualTransport (C) (N:=N) (fun U=>u U-v U) before W =
        actualTransport (C) (N:=N) u before W-actualTransport (C) (N:=N) v before W :=
    congrFun (ActualWilsonAbsoluteTransport.sub (C) R.makes live (ActualWilsonAbsoluteTransport.weighted (C) R.makes live hu)
      (ActualWilsonAbsoluteTransport.weighted (C) R.makes live hv) before) W
  have pair (U:space K):(A true U-A false U)*(B true U-B false U)=
      (face true true U-face false true U)-(face true false U-face false false U):=by unfold face;ring
  simp_rw [pair]
  exact (sub _ _ ((ok true true).subC (ok false true)) ((ok true false).subC (ok false false))).trans
    (congrArg₂ (·-·) (sub _ _ (ok true true) (ok false true)) (sub _ _ (ok true false) (ok false false)))

def account {a b:ℕ}(left:Column R N p a)(right:Column R N p b)
    (A B:space K→ℂ)(f:ℕ)(W:space f):ℂ:=
  (∑i∈Ico f N,landed R left right f i W)-(∑i∈Ico f K,returned R N A B f i W)+
    (held R left f W-mean R N A f W)*held R right f W+
    mean R N A f W*(held R right f W-mean R N B f W)

theorem original {a b:ℕ}(left:Bool → Column R N p a)(right:Bool → Column R N p b)
    (A B:Bool→space K→ℂ)(pA:∀t,Envelope (A t))(pB:∀t,Envelope (B t))
    (upper:K≤N){f:ℕ}(before:f≤K)(W:space f):
    actualTransport (C) (N:=N) (fun U=>(raw R (left true) U-raw R (left false) U)*
       (raw R (right true) U-raw R (right false) U)) (before.trans upper) W -
     actualTransport (C) (N:=N) (fun U=>(A true U-A false U)*(B true U-B false U)) before W =
     rectangle (fun t s=>account R (left t) (right s) (A t) (B s) f W):=by
  have occupied (t s:Bool):actualTransport (C) (N:=N) (fun U=>raw R (left t) U*raw R (right s) U)
      (before.trans upper) W-actualTransport (C) (N:=N) (fun U=>A t U*B s U) before W=
      account R (left t) (right s) (A t) (B s) f W:=by
    have one:=WilsonReflectedOriginalTwoDeposit.original R (left t) (right s) (before.trans upper) W
    have two:=WilsonReflectedRestartedPair.original R (A t) (B s) (pA t) (pB s) upper before W
    unfold account
    rw [←one,←two];unfold separate WilsonReflectedRestartedPair.product;ring
  rw [conditional R _ (le_refl N) (fun t=>raw R (left t)) (fun t=>raw R (right t))
      (fun t=>Envelope.compactC (continuous R _)) (fun t=>Envelope.compactC (continuous R _)),
    conditional R before upper A B pA pB]
  simp only [rectangle,←occupied]
  ring

end YM.Integration.WilsonReflectedSquare
end
