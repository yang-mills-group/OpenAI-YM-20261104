import YM.Integration.WilsonIndependentSpoutPostedBank

/-! Recover all nonconstant symmetric angular rows from the true centered
polynomial at its physical held fields. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutCenteredRanks
open Function PowerSeries WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Power
open scoped BigOperators Classical
variable {I:Type}[Fintype I]

theorem original {P Q:Gen ℝ I}(a:FiniteGen P)(b:FiniteGen Q)(p:Pure P)(q:Pure Q)
    (reads:∀x:I→ℝ,MvPolynomial.eval x (totalR P)-MvPolynomial.eval (0:I→ℝ) (totalR P)=
      MvPolynomial.eval x (totalR Q)-MvPolynomial.eval (0:I→ℝ) (totalR Q)):
    ∀r,0<r→P r=Q r:=by
  let c:=MvPolynomial.eval (0:I→ℝ) (totalR Q)-MvPolynomial.eval (0:I→ℝ) (totalR P)
  let T:Ten ℝ I 0:=fun _=>c
  let H:=shine T
  have fin:FiniteGen H:=⟨1,fun i hi=>shine_dark (by omega)⟩
  have pure:Pure H:=shine_pure (fun _ _=>rfl)
  have print:totalR H=MvPolynomial.C c:=by
    rw [visible_shine T]
    exact shell T (fun i=>i.elim0)
  have done:P+H=Q:=by
    apply gen_inj (finite_add a fin) b (fun r=>(p r).add (pure r)) q
    rw [visible_add a fin,print];apply MvPolynomial.funext;intro x
    rw [map_add,MvPolynomial.eval_C];have h:=reads x;dsimp only [c];linarith
  intro r hr
  have row:=congrFun done r
  change P r+shine T r=Q r at row
  rw [shine_dark (by omega : 0≠r),add_zero] at row
  exact row

end YM.Integration.WilsonIndependentSpoutCenteredRanks
