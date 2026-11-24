import YM.Integration.WilsonOriginalLinkedAngularPage
import YM.Integration.WilsonOriginalCoverNominalPair
import YM.Integration.WilsonOriginalCoverNominalCubic

/-! Read one finite joint table after keeping all of its grades, modes and relative positions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCompactDeckRead
open Finset Function Filter Lattice RG Marker Comparison.RG02 Comparison.RG02.Order
open Further.PhysicalPeriodLimitF933 Macrame FVA1Physical TwoReset
open WilsonOriginalConnectedPeriodPage WilsonOriginalPolarizedAngularPage WilsonOriginalLinkedAngularPage
open scoped BigOperators Classical
variable {G:Gauge} {n X:Side} {r:ℕ}
local notation "E" => Stationary.Link G X

def flat (F:E→ℂ) : E→ℂ := F - fun _=>F 0

theorem copies (h:n.val∣X.val)(o:Site X)(F:E→ℂ)(y:E):
    board h o (move G) F y = ∑v:Deck h,F (move G v.val y) := by
  unfold board
  rw [Finset.sum_apply]
  change (∑v:Fin (Pages n X),F (move G ((page h (splitter h o) v).val-o) y))=_
  simpa only [add_sub_cancel_right] using pages h o (fun z=>F (move G (z-o) y))

theorem read {W:Type*} (h:n.val∣X.val)(o z:Site X)(V Z:ℕ→E→W)
    (same:∀e≤r,∀y,V e y=Z e y)(take:(Fin (r+1)→W)→ℂ)(y:E):
    board h o (move G) (flat (fun a=>take fun e=>V e a)) y =
    board h z (move G) (flat (fun a=>take fun e=>Z e a)) y := by
  rw [copies,copies]
  apply sum_congr rfl
  intro v _
  have eq (a:E):(fun e:Fin (r+1)=>V e a)=(fun e:Fin (r+1)=>Z e a):=
    funext (fun e=>same e (Nat.le_of_lt_succ e.isLt) a)
  change take _ - take _ = take _ - take _
  rw [eq,eq]
end YM.Integration.WilsonOriginalCompactDeckRead
end
