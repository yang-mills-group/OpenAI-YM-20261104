import YM.Integration.WilsonSeparatedOriginalJointLog
import YM.Integration.WilsonIndependentOrdinaryPairGrade

/-! The next complete connected word at the filed grade, including the three
proper pair–singleton products and the triple of separate means. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCoverNominalCubic
open Finset Marker Extra.Trajectories Comparison.RG02 Comparison.RG02.Order
open Comparison.RG02.Cumulants WilsonIndependentOrdinaryPairGrade
open scoped Classical BigOperators
open WilsonSeparatedOriginalJointLog
local notation "J" => WilsonSeparatedOriginalJointLog.three

def cubic {A : Type} [CommRing A] (m : Finset (Fin 3) → A) : A :=
  m univ - (m {0,1} * m {2} + m {0,2} * m {1} + m {1,2} * m {0}) +
    2 * (m {0} * m {1} * m {2})

theorem integrated {r : ℕ} (x : Grade J r) (unit : UnitLeading x) :
    let P := render (ratio x)
    slot (shape univ) (logSeries (Fintype.card (Fin 3)+r) P) =
      cubic (fun a => slot (shape a) P) := by
  intro P
  apply Polynomial.funext
  intro z
  rw [read_slot,formula_log]
  have quiet : (formula z P).part (J).quiet=1 :=
    (value_render z (ratio x)) ▸ leading_trunc_value (ratio_pure unit) z
  have room (t : (J).Mode) : t.val.card ≤ Fintype.card (Fin 3)+r :=
    (card_le_univ t.val).trans (Nat.le_add_right ..)
  rw [←log_to (formula z P) quiet _ room]
  simpa only [cubic, WilsonSeparatedOriginalMarkedCubic.cubic, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, read_slot] using
    three_fields (formula z P) quiet

theorem deposited {r : ℕ} (x : Grade J r) (unit : UnitLeading x) (sym : Symmetric x)
    (j : ℕ) (hj : j≤r) :
    (Order.observe J r (Order.logMarked x) j).part (shape univ) =
      (cubic (fun a => slot (shape a) (render (ratio x)))).coeff j := by
  let P := render (ratio x)
  let B := logSeries (Fintype.card (Fin 3)+r) P
  have restore : stamp J r P=ratio x := rerender (sym_ratio unit sym)
  have filed : stamp J r B=logMarked x := by
    change stamp J r (logSeries (Fintype.card (Fin 3)+r) P)=logMarked x
    rw [stamp_log,restore,logMarked,log_to (ratio x) (ratio_quiet unit) (Fintype.card (Fin 3)+r)
      (room_for (Fintype.card (Fin 3)) (fun t => Finset.card_le_univ t.val))]
  calc
    _ = (Order.observe J r (stamp J r B) j).part (shape univ) := by rw [filed]
    _ = (slot (shape univ) B).coeff j := by
      rw [←series_poly J r B,observation J r _ hj,Polynomial.coeff_coe,coeff_slot]
    _ = _ := by
      change (slot (shape univ) (logSeries (Fintype.card (Fin 3)+r) (render (ratio x)))).coeff j=_
      exact congrArg (fun v : Polynomial ℂ => v.coeff j) (integrated x unit)

end YM.Integration.WilsonOriginalCoverNominalCubic
