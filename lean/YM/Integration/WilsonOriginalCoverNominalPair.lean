import YM.Integration.WilsonIndependentOrdinaryPairGrade

/-! The connected deposit of two distinct marks is the joint ordinary moment
minus the product of its two ordinary means through every purchased grade. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCoverNominalPair
open Finset Marker Extra.Trajectories Comparison.RG02 Comparison.RG02.Order
open Comparison.RG02.Cumulants WilsonIndependentOrdinaryPairGrade
open scoped Classical BigOperators
variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V} {r : ℕ}

theorem deposited (x : Grade R r) (unit : UnitLeading x) (sym : Symmetric x)
    (a b : V) (s : R.Mode) (distinct : a≠b) (ab : s.val={a,b}) (j : ℕ) (hj : j≤r) :
    (Order.observe R r (logMarked x) j).part s =
      (slot s (render (ratio x)) -
        slot (R.fire a) (render (ratio x)) * slot (R.fire b) (render (ratio x))).coeff j := by
  let P := render (ratio x)
  let B := logSeries (Fintype.card V+r) P
  have restore : stamp R r P=ratio x := rerender (sym_ratio unit sym)
  have filed : stamp R r B=logMarked x := by
    change stamp R r (logSeries (Fintype.card V+r) P)=logMarked x
    rw [stamp_log,restore,logMarked,log_to (ratio x) (ratio_quiet unit) (Fintype.card V+r)
      (room_for (Fintype.card V) (fun t => Finset.card_le_univ t.val))]
  calc
    _ = (Order.observe R r (stamp R r B) j).part s := by rw [filed]
    _ = (slot s B).coeff j := by
      rw [←series_poly R r B,observation R r _ hj,Polynomial.coeff_coe,coeff_slot]
    _ = _ := by
      change (slot s (logSeries (Fintype.card V+r) (render (ratio x)))).coeff j=_
      rw [pair x unit a b s distinct ab]

end YM.Integration.WilsonOriginalCoverNominalPair
