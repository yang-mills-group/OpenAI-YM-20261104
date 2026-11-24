import YM.Integration.WilsonOriginalPublicTrialPhaseUnit

/-! One exact centered parent return on the incumbent physical history at any site. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseZero
open Finset Function Filter MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Guard Push Local RelayDifference.Opening Next.Foundations
open MergeProof MergeProof.Accent PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign
open OPE.Therm Push.AbsoluteSums.Animals Extra.Multi WilsonPositionProgramBlockedTrialAddBack
open RG05Readout RG05Readout.Address Offsets WilsonOriginalPublicTrialPhaseUnit
open scoped Classical BigOperators ContDiff
variable {G:Gauge}(R:Run G){m N per:ℕ}
local notation "C" => R.family
local notation "A" => R.alloy.B.a
local notation "S" => (C).path
local notation "P" => (S).rep N per (m+1)
local notation "Q" => (S).rep N per m
local notation "O" => (S).levels.clock.op m per
local notation "F" => ((C).labels.level 0)
local notation "loc" => (C).localSection 0

set_option maxHeartbeats 850000 in
/-- The literal issued scalar is kept and the same original occupied source continues.
The next root and every subsequent actual decoder retain the once-divided hard account. -/
theorem original (hG:G.Simple)(purchase:RG05Preconstruction.ReadoutPurchase R.b)
    (stock:RG05Readout.Many.Storage (C) R.doors)(live:m<N)(grade:3≤(A).clock.J m)
    (o:Site ((C).side (m+1) per))(q:Coefficient (F) ((C).side (m+1) per))
    (hit:Push.Local.hitWidth (Q).p*Push.Local.kappa (S) m≤1)(fine:Push.Local.kappa (S) (m+1)≤1)
    (r:ℝ)(fmt:q.Format o (C).params (P))(rem:q.remBound o (P) (Push.Local.kappa (S) (m+1)) r):
    let α:=Doors.rate ((A).S.block m)
    let b:=(O).ratio.parent o
    ∃k:Coefficient (F) ((C).side m per),
      k.Format b (C).params (Q) ∧ k.remBound b (Q) (Push.Local.kappa (S) m) (α*r) ∧
      (F).coeffSize k.x≤α*r ∧ ‖k.x 0‖≤α*r ∧
      Ride (O) o b (R.doors N per m live) 1
        (invoice (centered q) o (loc) (P)) (invoice k b (loc) (Q)) ((2+α)*r) ∧
      ∀W, (O).push (P).beta ((centered q).density o (loc) (P)) W =
        ((Q).eval W:ℂ)*k.x 0+(centered k).density b (loc) (Q) W:=by
  intro α b
  obtain ⟨hq,hr⟩:=account q fmt rem
  obtain ⟨k,f,w,s,t⟩:=WilsonOriginalPublicTrialPhaseLocated.original R hG purchase stock live
    0 grade o (centered q) hit fine r hq hr
  have z:(F).coeffSize (centered q).x=0:=by simp [WilsonOriginalPublicTrialPhaseUnit.centered,Frame.coeffSize]
  simp only [z,mul_zero,zero_add,pow_zero] at w s t
  refine ⟨k,f,w,s,(Finset.single_le_sum (f:=fun i=>‖k.x i‖) (fun i _=>norm_nonneg _)
    (Finset.mem_univ 0)).trans s,t,?_⟩
  intro W
  have hx:=congrFun t.exactStep W
  change k.density b (loc) (Q) W=(1:ℂ)*_ at hx
  rw [one_mul] at hx
  exact hx.symm.trans (WilsonOriginalPublicTrialPhaseUnit.density k b (loc) (Q) W)

end YM.Integration.WilsonOriginalPublicTrialPhaseZero
