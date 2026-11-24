import YM.Integration.WilsonIndependentConditionalFiniteClock

/-! Separate the substitution of the coupling from the simultaneous
rescaling of each field variable in the actual `Blue.redo`. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutThermalChange
open Matrix PowerSeries WilsonCoeffUV WilsonCoeffUV.Blue
open scoped Classical BigOperators
variable {U Y:Type}

def degree (A:Cost):Ink U→+*Ink U:=
  edit C (x:=soil A*X) (by simp)

def axes (A:Cost)(i:U):Ink U:=soil A⁻¹*path i

theorem exact_reset (A:Cost):
    (train (axes (U:=U) A)).comp (degree A)=redo A:=by
  have hX:((train (axes (U:=U) A)).comp (degree A)) X=soil A*X:=by
    rw [RingHom.comp_apply,degree,edit_X,map_mul,income,train_X]
  apply serial_ext (by rw [hX];simp) _ (hX.trans (redo_X A).symm)
  intro p
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [RingHom.comp_apply,degree,edit_C,show C (MvPolynomial.C a:POL U)=realS a from rfl,
      train_real,redo_base]
  | add p q a b => simp only [map_add,a,b]
  | mul_X p j a =>
    rw [map_mul,map_mul,map_mul,a,show C (MvPolynomial.X j:POL U)=path j from rfl,
      RingHom.comp_apply,show degree A (path j)=path j from edit_C ..,train_path,redo_path]
    rfl

theorem held_cash (A:Cost):(holdUp U) (soil (U:=Y) A)=soil A:=by
  ext1 n
  unfold holdUp soil holdUpPoly
  simp

private theorem retain [Fintype Y][Fintype U](H:Matrix U U ℝ){f g:Ink (U⊕Y)}{k:ℕ}
    (h:Equal k f g):Equal k (Wick Y H f) (Wick Y H g):=by
  intro i hi
  simp only [Wick,projectZero,PowerSeries.coeff_map,overlay_apply,h i hi]

theorem heat [Fintype Y][Fintype U](A:Cost)(H:Matrix U U ℝ)(p:Ink (U⊕Y)):
    Wick Y H (degree A p)=degree A (Wick Y H p):=by
  ext1 e
  have parts {Z:Type}(q:Ink Z)(n:ℕ):Equal n (degree A q)
      (∑j∈Finset.range n,C (coeff j q)*(soil A*X)^j):=by
    intro i hi
    exact edit_coeff _ _ q hi
  rw [retain H (parts p (e+1)) e e.lt_succ_self,parts (Wick Y H p) (e+1) e e.lt_succ_self,
    W_sum]
  apply congr_arg (coeff e)
  refine Finset.sum_congr rfl fun j _=>?_
  have term:holdUp U ((soil (U:=Y) A*X)^j)=(soil A*X)^j:=by
    rw [map_pow,map_mul,held_cash,holdUp,map_X]
  rw [←term,W_param,Wick,overlay_C,projectZero,map_C]
  simp only [Wick,projectZero,coeff_map,overlay_apply]

end YM.Integration.WilsonIndependentSpoutThermalChange
