import YM.Integration.WilsonIndependentOrdinaryPairGrade

/-! Recover the ordinary pair with its coupling convolution truncated at
the actual finite order, before comparing held-field derivatives. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryOrdinaryConvolution
open Finset Marker Comparison.RG02 Comparison.RG02.Order
open WilsonIndependentOrdinaryPairGrade
open scoped Classical BigOperators
variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V} {r : ℕ}

theorem singleton (x : Grade R r) (unit : UnitLeading x) (sym : Order.Symmetric x) (a : V) :
    slot (R.fire a) (render (ratio x)) = slot (R.fire a) (render (logMarked x)) := by
  let P := render (ratio x)
  let B := logSeries (Fintype.card V+r) P
  have restore : stamp R r P=ratio x := rerender (sym_ratio unit sym)
  have filed : stamp R r B = logMarked x := by
    change stamp R r (logSeries (Fintype.card V+r) P) = logMarked x
    rw [stamp_log,restore,logMarked,log_to (ratio x) (ratio_quiet unit) (Fintype.card V+r)
      (room_for (Fintype.card V) (fun t => Finset.card_le_univ t.val))]
  apply Polynomial.funext
  intro z
  rw [read_slot, read_slot, ← value_render, ← value_render]
  rw [← filed, ← restore, stamped, stamped, single x unit a]

theorem ordinary (x : Grade R r) (unit : UnitLeading x) (sym : Order.Symmetric x) (z : ℂ)
    (a b c : V) (s : R.Mode) (diff : a≠b) (ab : s.val={a,b}) :
    let L := value z (logMarked x)
    let Z := value z (ratio x)
    let e := fun (v : V) (j : ℕ) => (observe R r (logMarked x) j).part (R.fire v)
    Z.part s-Z.part (R.fire c) = L.part s-L.part (R.fire c) +
      ∑ j∈range (r+1), z^j * ∑ u∈antidiagonal j, e a u.1 * e b u.2 := by
  intro L Z e
  let A := slot (R.fire a) (render (ratio x))
  let B := slot (R.fire b) (render (ratio x))
  have ha : A.eval z = L.part (R.fire a) := by
    rw [show A= _ from singleton x unit sym a, read_slot, ← value_render]
  have hb : B.eval z = L.part (R.fire b) := by
    rw [show B= _ from singleton x unit sym b, read_slot, ← value_render]
  have H := overflow x unit sym z a b c s diff ab
  change (L.part s-L.part (R.fire c)+L.part (R.fire a)*L.part (R.fire b)) -
    (Z.part s-Z.part (R.fire c)) = (A*B).eval z-partialValue r z (A*B) at H
  rw [Polynomial.eval_mul,ha,hb] at H
  have truncated : partialValue r z (A*B) = ∑ j∈range (r+1), z^j *
      ∑ u∈antidiagonal j, e a u.1 * e b u.2 := by
    change ∑ j∈range (r+1), z^j * (A*B).coeff j = ∑ j∈range (r+1), z^j *
      ∑ u∈antidiagonal j, e a u.1 * e b u.2
    simp only [A,B,singleton x unit sym,Polynomial.coeff_mul,coeff_slot,render_coeff,e]
  rw [← truncated]
  linear_combination -H

end YM.Integration.WilsonCapturedPrimaryOrdinaryConvolution
