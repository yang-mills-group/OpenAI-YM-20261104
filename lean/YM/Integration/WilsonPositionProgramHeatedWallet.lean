import YM.Integration.WilsonPositionProgramRecastDraw

/-! The shared true source radius on the thermal-and-mark alphabet. -/
noncomputable section
namespace YM.Integration.WilsonPositionProgramHeatedWallet
open Function Finset Multi Marker Comparison.RG02 Comparison.RG02.Order
open scoped BigOperators Classical
variable {V:Type}[DecidableEq V][Fintype V]{R:Census V}{r:ℕ}

def deployed (w:V→ℝ)(r:ℕ):V⊕Fin r→ℝ:=Sum.elim w (fun _=>1)

omit [Fintype V] [DecidableEq V] in
theorem positive (w:V→ℝ)(hw:∀i,0<w i)(i:V⊕Fin r):0<deployed w r i:=by
  rcases i with i|i
  · exact hw i
  · exact zero_lt_one

theorem billed (w:V→ℝ)(s:(Board R r).Mode):Poly.toll (deployed w r) s=Poly.toll w (Join.left s):=by
  have pair(a:R.Mode)(b:(indices r).Mode):Poly.toll (deployed w r) (Join.pair a b)=Poly.toll w a:=by
    change (∏v∈a.val.disjSum b.val,deployed w r v)=_
    rw [prod_disjSum]
    simp [deployed,Poly.toll]
  have known:=pair (Join.left s) (Join.right s)
  simpa only [Join.pair_reunite] using known

theorem zero (i:Hot (Board R 0)):(Join.left i.val).val.Nonempty:=by
  by_contra no
  have left:Join.left i.val=R.quiet:=Subtype.ext (not_nonempty_iff_eq_empty.mp no)
  have right:Join.right i.val=(indices 0).quiet:=Subtype.ext (eq_empty_of_forall_notMem (fun k=>Fin.elim0 k))
  have re:=Join.pair_reunite i.val
  rw [left,right,Join.pair_quiet] at re
  have active:=i.property
  rw [←re] at active
  exact not_nonempty_empty active

omit [Fintype V] in
theorem shrunk (w v:V→ℝ)(hw:∀i,0<w i)(hv:∀i,0<v i)(s:R.Mode):
    Poly.toll (fun i=>min (w i) (v i)) s ≤ Poly.toll w s ∧
    Poly.toll (fun i=>min (w i) (v i)) s ≤ Poly.toll v s:=by
  have pos(i:V):0≤min (w i) (v i):=(lt_min (hw i) (hv i)).le
  exact ⟨prod_le_prod (fun j _=>pos j) (fun j _=>min_le_left _ _),
    prod_le_prod (fun j _=>pos j) (fun j _=>min_le_right _ _)⟩

end YM.Integration.WilsonPositionProgramHeatedWallet
end
