import YM.Integration.WilsonReceivedChronologicalFixedReserve

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedPublicFirstRanks
open Finset Marker Multi
open WilsonOriginalFullRosterCouplingClock WilsonReceivedChronologicalPanelClock
open WilsonReceivedChronologicalFixedReserve WilsonOriginalFullRosterBookedHearing
open WilsonOriginalDatedFieldsAtBoard
open scoped BigOperators Classical

private theorem max_over {V:Type}[Fintype V](x y:V→ℕ)(leaves:∀v,x v≤y v):
    Finset.univ.sup x≤Finset.univ.sup y:=
  Finset.sup_le fun v hv=>(leaves v).trans (Finset.le_sup (f:=y) hv)

private theorem leaf {n:ℕ}(a b:Fin n→ℕ)(leaves:∀v,a v≤b v)(w:ℕ)(s:(Stock.census (Fin n)).Mode):
    WilsonOriginalCensusPostedWages.debit w a s≤WilsonOriginalCensusPostedWages.debit w b s:=by
  unfold WilsonOriginalCensusPostedWages.debit
  exact Nat.add_le_add_left (Finset.sum_le_sum fun v _=>leaves v) _

private theorem panel {n:ℕ}(d a b:Fin n→ℕ)(leaves:∀v,a v≤b v)(k:ℕ):
    fare d a≤fare d b ∧ roof d d a k≤roof d d b k:=by
  constructor
  · exact max_over _ _ (leaf a b leaves _)
  · unfold roof
    apply max_over
    intro s
    unfold WilsonOriginalCensusTariff.debit
    gcongr
    exact leaf a b leaves _ s

/-- The rank chosen for the continuing census also funds the canonical first edge. -/
theorem original {n:ℕ}(d:Fin n→ℕ)(P:ℕ):
    let S:=terms d (fun _=>0) P
    let a:Fin n→ℕ:=fun _=>4
    let w:=work n P (fare d a) ((∑v,d v)+1)
    w+1+(wallet (fare d a)).pole+1≤S.rent+1 ∧
    w+1+1≤S.precision ∧ w+2≤S.precision ∧
    2*(S.precision+1)≤S.target ∧ 2*(S.rent+1)+8≤S.order ∧ 3*roof d d a S.target≤S.order:=by
  intro S a w
  let b:=charges (fun _:Fin n=>0)
  have leaves:∀v,a v≤b v:=by intro v;change 4 ≤ 2*(0+4);decide
  obtain ⟨paid,seated⟩:=panel d a b leaves S.target
  have weight:w≤work n P (fare d b) ((∑v,d v)+1):=by
    dsimp [w,work,debt,Degree.pole]
    gcongr
  have poles:(wallet (fare d a)).pole≤(wallet (fare d b)).pole:=by
    dsimp [wallet,Degree.pole]
    gcongr
  exact ⟨(Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_right weight 1) poles) 1).trans S.cash,
    (Nat.add_le_add_right (Nat.add_le_add_right weight 1) 1).trans S.marked,
    (Nat.add_le_add_right weight 2).trans S.failed,S.enough,S.deep,
    (Nat.mul_le_mul_left 3 seated).trans S.ceiling⟩

end YM.Integration.WilsonAddressedPublicFirstRanks
end
