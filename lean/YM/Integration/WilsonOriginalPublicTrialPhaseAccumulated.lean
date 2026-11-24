import YM.Integration.WilsonOriginalPublicTrialPhaseScalar

/-! The scalar of the complete earlier fit is retained at every physical edge. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseAccumulated
open Finset Function MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Guard Push Local Next.Foundations
open MergeProof PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign
open OPE.Therm
open RG05Readout RG05Readout.Address
open WilsonOriginalPublicTrialPhaseScalar WilsonOriginalPublicTrialPhaseUnit
open scoped Classical BigOperators ContDiff
variable {G:Gauge}{F:Frame G 0}{n:Side}

def row (q:Coefficient F n)(o:Site n)(S:SectionData F)(A:Rep G n)(z:ℂ):Three G n :=
  deposit A (invoice (centered q) o S A) z

theorem keep (q:Coefficient F n)(o:Site n)(S:SectionData F)(A:Rep G n)(z:ℂ):
    row q o S A (z+q.x 0)=deposit A (invoice q o S A) z:=by
  apply Prod.ext
  · funext U
    change (centered q).density o S A U+(z+q.x 0)*(A.eval U:ℂ)=q.density o S A U+z*(A.eval U:ℂ)
    rw [WilsonOriginalPublicTrialPhaseUnit.density q o S A U]
    ring
  · apply Prod.ext
    · funext U
      change (centered q).exponentialEntry o S A U+(z+q.x 0)=q.exponentialEntry o S A U+z
      rw [WilsonOriginalPublicTrialPhaseUnit.unmasked q o S A U]
      ring
    · rfl

theorem start (q:Coefficient F n)(o:Site n)(S:SectionData F)(A:Rep G n):
    row q o S A (q.x 0)=invoice q o S A:=by
  have eq:=keep q o S A 0
  simpa only [zero_add,deposit,zero_smul,add_zero] using eq

variable (R:Run G){m N per:ℕ}
local notation "C" => R.family
local notation "H" => (C).path
local notation "P" => (H).rep N per (m+1)
local notation "Q" => (H).rep N per m
local notation "A" => R.alloy.B.a
local notation "O" => (H).levels.clock.op m per
local notation "F₀" => (C).labels.level 0
local notation "loc" => (C).localSection 0

set_option maxHeartbeats 650000 in
theorem original (hG:G.Simple)(purchase:RG05Preconstruction.ReadoutPurchase R.b)
    (stock:RG05Readout.Many.Storage (C) R.doors)(live:m<N)(grade:3≤(A).clock.J m)
    (o:Site ((C).side (m+1) per))(q:Coefficient (F₀) ((C).side (m+1) per))
    (hit:Push.Local.hitWidth (Q).p*Push.Local.kappa (H) m≤1)(fine:Push.Local.kappa (H) (m+1)≤1)
    (r:ℝ)(fmt:q.Format o (C).params (P))(rem:q.remBound o (P) (Push.Local.kappa (H) (m+1)) r):
    let α:=Doors.rate ((A).S.block m)
    let b:=(O).ratio.parent o
    ∃k:Coefficient (F₀) ((C).side m per),
      k.Format b (C).params (Q) ∧ k.remBound b (Q) (Push.Local.kappa (H) m) (α*r) ∧
      ‖k.x 0‖≤α*r ∧ ∀z:ℂ,Ride (O) o b (R.doors N per m live) 1
        (row q o (loc) (P) z) (row k b (loc) (Q) (z+k.x 0)) ((2+α)*r+‖z‖):=by
  intro α b
  obtain ⟨k,f,w,-,v,t,-⟩:=WilsonOriginalPublicTrialPhaseZero.original R hG purchase stock live
    grade o q hit fine r fmt rem
  refine ⟨k,f,w,v,fun z=>?_⟩
  rw [keep]
  exact WilsonOriginalPublicTrialPhaseScalar.original R live o b _ _ _ z t

end YM.Integration.WilsonOriginalPublicTrialPhaseAccumulated
end
