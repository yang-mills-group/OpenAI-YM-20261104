import YM.Integration.WilsonPhysicalHistoryPictureRestore
import YM.RG05Readout.Records.Gust

/-! Transport the field-independent marker polynomial of the old regular
rows through the original Wilson integrals and their licensed marker maps. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAllDateHarvestClearTransfer
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker RG05Readout Address Native View Bid Pressure Copper
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Records
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical

variable {G:Gauge}{C:Family G}{V:ℕ→Type}[∀j,DecidableEq (V j)]{W:Type*}
variable {per n b m i N:ℕ}(A:Planner C per n V W)(H:∀j,Census (V j))(s:W→ℕ)

def moved (i:ℕ)(ni:n ≤ i)(hc:License (H i) (H (i+1)) (Prod.fst ∘ A.narrows i ni)) :
    Poly (H (i+1)) →ₐ[ℂ] Poly (H i):=
  feed (fun x=>budwgt C per i (s (A.labelY i ((A.narrows i ni) x).1))) hc

theorem step (ni:n ≤ i)(hc:License (H i) (H (i+1)) (Prod.fst ∘ A.narrows i ni)) (c:Poly (H (i+1)))
    {F:Config G (C.side (i+1) per)→Poly (H (i+1))}(live:Integrable F (prior G _)):
    downdraft (N:=N) A H s i ni hc (fun U=>c*F U)=fun U=>
      moved A H s i ni hc c*downdraft (N:=N) A H s i ni hc F U := by
  let Q:=C.path.levels.clock.op i per
  let β:=(C.path.rep N per (i+1)).beta
  have frozen:Q.push β (fun U=>c*F U)=fun U=>c*Q.push β F U:=
    amp_live (LinearMap.mulLeft ℂ c) Q live (C.path.levels.transition_mass i per β)
  funext U
  change moved A H s i ni hc (Q.push β (fun U=>c*F U) U)=
    moved A H s i ni hc c*moved A H s i ni hc (Q.push β F U)
  rw [frozen,map_mul]

variable {H}{A}{s}{nb:n ≤ b}{F:∀j,Config G (C.side j per)→Poly (H j)}
variable (run:Replay A s nb m F N)(c:Poly (H m))

def carried (i:ℕ)(bi:b ≤ i)(im:i ≤ m) : Poly (H i) :=
  Nat.decreasingInduction (motive:=fun j _=>b ≤ j→Poly (H j))
    (fun j jm go bj=>moved A H s j (nb.trans bj) (run.downhill j bj jm).choose (go (bj.trans j.le_succ)))
    (fun _=>c) im bi

theorem born (bm:b ≤ m) : carried run c m bm le_rfl=c :=
by
  unfold carried
  rw [Nat.decreasingInduction_self]

theorem previous (bi:b ≤ i)(im:i < m) :
    carried run c i bi im.le=moved A H s i (nb.trans bi) (run.downhill i bi im).choose
      (carried run c (i+1) (bi.trans i.le_succ) im) :=
by
  unfold carried
  rw [Nat.decreasingInduction_succ_left]

theorem across {X:∀j,Config G (C.side j per)→Poly (H j)} (whole:Replay A s nb m X N) (mN:m ≤ N)
    (live:Integrable (F m) (prior G _)) (source:∀U,X m U=c*F m U)
    (bi:b ≤ i)(im:i ≤ m)(U:Config G (C.side i per)) :
    X i U=carried run c i bi im*F i U := by
  induction im using Nat.decreasingInduction with
  | self => rw [born];exact source U
  | of_succ j jm ih =>
    have bj:b ≤ j+1:=bi.trans j.le_succ
    obtain ⟨license,full⟩:=whole.downhill j bi jm
    have core:=(run.downhill j bi jm).choose_spec
    have price:=Replay.live (A:=A) (s:=s) nb run live mN bj jm
    have measured:X (j+1)=fun U=>carried run c (j+1) bj jm*F (j+1) U:=funext (ih bj)
    rw [full,measured,step A H s (nb.trans bi) license _ price,previous run c bi jm]
    exact congrArg (fun z:Poly (H j)=>moved A H s j (nb.trans bi) license
      (carried run c (j+1) bj jm)*z) (congr_fun core U).symm

end YM.Integration.WilsonAllDateHarvestClearTransfer
