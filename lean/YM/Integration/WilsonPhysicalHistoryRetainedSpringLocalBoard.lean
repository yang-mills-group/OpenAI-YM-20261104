import YM.Integration.WilsonPhysicalHistoryRetainedSpringLocalRows

/-! Subtract the two complete independently numbered expenditures on their
actual local fibre. Both original sets of incidence tests remain visible. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalMarkedRunAction
open Finset Lattice Lattice.Corona RG Wilson Push.GridApprox.Attach RG01Estimate
open AnalyticBridge VerifiedReset Collection Quotes PhysicalNext PhysicalNext.Repeat
open scoped Classical BigOperators
variable {G:Gauge} {n:Side}

def metered (P:Rep G n) (M:Precise.Leads G n):Activities G n:=
  {P.activities with reg:=M.listing.reg,E:=M.trunk}

theorem numbered_change (P:Rep G n) {δ κ:ℝ} (good:P.activities.Valid P.p δ κ)
    (M:Precise.Leads G n)(cash:Meadow.Budget P.p M.listing.reg M.trunk M.bill)
    (F:Config G n→ℝ)(filed:∀U,HasSum (fun i=>masked P.p.threshold (M.listing.reg i).support (M.trunk i) U) (F U))
    (r:ℕ)(hr:1≤P.p.supportExponent*r)(S:Support n)(U V:Config G n)
    (outside:OriginalMarkedLocalDifference.Outside S U V):
    let X:=metered P M
    let seen (A:Activities G n)i:=if Disjoint (A.reg i).support (halo 8 S) then 0 else
      A.regularOccurrence P.p i U-A.regularOccurrence P.p i V
    HasSum (seen P.activities) (P.activities.additive P.p U-P.activities.additive P.p V) ∧
    HasSum (seen X) (F U-F V) ∧
    |(P.activities.additive P.p U-F U)-(P.activities.additive P.p V-F V)|≤
      2*((S.card:ℝ)*17^4*(hitConstant ((P.p.B+1)*r)*(δ+M.bill))):=by
  intro X seen
  obtain ⟨b,early,priced⟩:=cash
  have proper:X.EBound P.p M.bill:=⟨b,fun i=>(priced i).2,
    Quotes.segment M.listing.reg (fun i=>(priced i).2.1) early⟩
  obtain ⟨ours,owned⟩:=local_rows P.activities P.p good.regular.smooth good.boundE r hr S U V outside
  have theirs:=local_rows X P.p (fun i=>(priced i).1) proper r hr S U V outside
  have exact_read (W:Config G n):X.additive P.p W=F W:=(filed W).tsum_eq
  rw [exact_read U,exact_read V] at theirs
  refine ⟨ours,theirs.1,?_⟩
  calc |(P.activities.additive P.p U-F U)-(P.activities.additive P.p V-F V)|=
      |(P.activities.additive P.p U-P.activities.additive P.p V)-(F U-F V)|:=by ring_nf
       _≤|P.activities.additive P.p U-P.activities.additive P.p V|+|F U-F V|:=abs_sub _ _
       _≤_:=by have h:=add_le_add owned theirs.2;linear_combination h

end YM.Integration.OriginalMarkedRunAction
