import YM.Integration.WilsonReflectedFiledArm
import YM.Integration.WilsonReflectedSquare
/-! Compare the original four physical readings on separately placed
arms with the doubly localized K trial.  Each swapped singleton uses
its original paid signed coefficient.  The prior mixed deposits remain
on their respective histories. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedFundedHearing
open Push Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address RG05Readout.Records WilsonOriginalNullCorridor MergeProof MergeProof.Accent
open WilsonPositionProgramOriginalBlockedTrial WilsonAddressedRestartedColumn WilsonReflectedOriginalTwoDeposit
open WilsonReflectedPlacedArm WilsonReflectedFullPanel WilsonOriginalMicroscopicGuardedPage
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){N p f K:ℕ}
local notation "C₀" => R.family
local notation "space" i:max => Config G ((C₀).side i p)
local notation "P₀" i:max => (C₀).path.rep N p i

structure Arm (d N p f K:ℕ) where
  Y : (C₀).label d
  w : (C₀).label d
  b : Bool
  s : Signed
  o : Site ((C₀).side f p)
  cash : ℝ
  z : store (C₀) d p f
  filed : WilsonAddressedRestartedFiled.Filed R d N p f 0
    (track R d N p K (numerator R d N p K 0 w) f-calValues (C:=C₀) d N p f (((C₀).factory d N p).terminal.symm Y)) cash z

theorem purchased (d j q:ℕ)(before:j≤K)(high:K≤N)(early:j≤f)(late:f≤K){η bank:ℝ}
    {M:(C₀).label d ≃ₗ[ℂ] (C₀).label d}{Y:(C₀).label d}
    (bought:receipt R d j K N p q before high η M Y bank)(b:Bool)(s:Signed)(o:Site ((C₀).side f p)):
    ∃A:Arm R d N p f K,A.Y=Y ∧ A.w=M.symm (full R d N p j Y) ∧ A.b=b ∧ A.s=s ∧ A.o=o ∧
    A.cash=hike (C₀) K f rate*((1+4*stock (C₀) K)*((C₀).labels.level d).coeffSize A.w):=by
  obtain ⟨z,hz⟩:=bought.2.2 f early late 0
  exact ⟨⟨Y,_,b,s,o,_,z,hz⟩,rfl,rfl,rfl,rfl,rfl,rfl⟩

variable {d:ℕ}
def source (A:Arm R d N p f K)(h:f≤N):Column R N p d:=
  WilsonReflectedPlacedArm.original R d h A.Y A.b A.s A.o
def cropped (A:Arm R d N p f K)(h:f≤K):space K→ℂ:=
  trial R (N:=N) d h A.w A.b A.s A.o
def signed (A:Arm R d N p f K)(W:space f):ℂ:=
  -WilsonReflectedFiledArm.evaluated R (N:=N) d A.z A.b A.s A.o W /
    (((C₀).S.a f:ℂ)^d*((P₀ f).eval W:ℂ))

theorem swap (A:Arm R d N p f K)(begin:f≤K)(live:K≤N)(ready:(C₀).ref d≤f)(W:space f):
    WilsonReflectedOriginalTwoDeposit.held R (source R A (begin.trans live)) f W-
      WilsonReflectedRestartedPair.mean R N (cropped R A begin) f W=signed R A W:=by
  obtain ⟨n,rfl⟩:=Nat.exists_eq_add_of_le begin
  have eq:=WilsonReflectedFiledArm.original R d n live ready A.Y A.w A.filed A.b A.s A.o W
  have av:((C₀).S.a f:ℂ)≠0:=by exact_mod_cast ((C₀).S.a_pos f).ne'
  have pv:((P₀ f).eval W:ℂ)≠0:=by exact_mod_cast (Multi.AxisShift.chosen_positive R.makes.wilson (begin.trans live) W).ne'
  unfold signed source cropped WilsonReflectedRestartedPair.mean
  rw [dif_pos begin]
  apply (eq_div_iff (mul_ne_zero (pow_ne_zero d av) pv)).2
  dsimp only at eq;rw [eq];ring

/-- The original UV deposits, finite trial deposits and the two corrected
singleton sources, in the order in which their peers are still present. -/
def payment {a b:ℕ}(X:Arm R a N p f K)(Y:Arm R b N p f K)(begin:f≤K)(live:K≤N)(W:space f):ℂ:=
  let x:=source R X (begin.trans live)
  let y:=source R Y (begin.trans live)
  let A:=cropped R X begin
  let B:=cropped R Y begin
  (∑i∈Ico f N,landed R x y f i W)-
  (∑i∈Ico f K,WilsonReflectedRestartedPair.returned R N A B f i W)+
  signed R X W*WilsonReflectedOriginalTwoDeposit.held R y f W+
  WilsonReflectedRestartedPair.mean R N A f W*signed R Y W

theorem original {a b:ℕ}(X:Bool→Arm R a N p f K)(Y:Bool→Arm R b N p f K)
    (begin:f≤K)(live:K≤N)(left:(C₀).ref a≤f)(right:(C₀).ref b≤f)(W:space f):
    actualTransport (C₀) (N:=N) (fun U=>
      (WilsonReflectedOriginalTwoDeposit.raw R (source R (X true) (begin.trans live)) U-
       WilsonReflectedOriginalTwoDeposit.raw R (source R (X false) (begin.trans live)) U)*
      (WilsonReflectedOriginalTwoDeposit.raw R (source R (Y true) (begin.trans live)) U-
       WilsonReflectedOriginalTwoDeposit.raw R (source R (Y false) (begin.trans live)) U)) (begin.trans live) W-
     actualTransport (C₀) (N:=N) (fun U=>(cropped R (X true) begin U-cropped R (X false) begin U)*
       (cropped R (Y true) begin U-cropped R (Y false) begin U)) begin W=
      WilsonReflectedSquare.rectangle (fun t s=>payment R (X t) (Y s) begin live W):=by
  rw [WilsonReflectedSquare.original R (fun t=>source R (X t) (begin.trans live)) (fun t=>source R (Y t) (begin.trans live))
    (fun t=>cropped R (X t) begin) (fun t=>cropped R (Y t) begin)
    (fun _=>trial_paid R ..) (fun _=>trial_paid R ..) live begin W]
  apply congrArg WilsonReflectedSquare.rectangle
  funext t s
  unfold WilsonReflectedSquare.account payment
  rw [swap R (X t) begin live left W,swap R (Y s) begin live right W]

end YM.Integration.WilsonReflectedFundedHearing
end
