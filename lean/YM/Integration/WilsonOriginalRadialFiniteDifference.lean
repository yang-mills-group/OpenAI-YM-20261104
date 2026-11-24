import YM.Integration.WilsonOriginalRadialSpringRemainder

/-! Signed finite differences on the very real nodes used by germ extraction. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalRadialFiniteDifference
open Function Finset Set MeasureTheory Labels Lattice Wilson RG Source Push.Local RG01.Kernel
open WilsonFirstReceivedRadialStencil WilsonCapturedPrimarySampledPanel
open scoped Classical BigOperators Topology ContDiff
private def poly (k:ℕ)(P:Polynomial ℂ)(t:ℝ):ℂ:=∑ j∈range (k+1),t^j • P.coeff j
private theorem value (k:ℕ)(P:Polynomial ℂ)(deg:P.natDegree≤k)(t:ℝ):
    poly k P t=P.eval (t:ℂ):=by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le deg)]
  unfold poly
  apply sum_congr rfl
  intro j _
  simp [Complex.real_smul,mul_comm]
private theorem smooth (k:ℕ)(P:Polynomial ℂ)(z:ℝ)(n:ℕ):ContDiffAt ℝ n (poly k P) z:=by
  unfold poly;fun_prop
private theorem zero (k:ℕ)(P:Polynomial ℂ)(z:ℝ):iteratedDeriv (k+1) (poly k P) z=0:=by
  have sp (j:ℕ):ContDiffAt ℝ (k+1:ℕ) (fun t:ℝ=>t^j) z:=by fun_prop
  unfold poly
  rw [iteratedDeriv_fun_sum (I:=range (k+1))
    (f:=fun j (t:ℝ)=>t^j • P.coeff j) (fun j _=>by fun_prop)]
  apply sum_eq_zero
  intro j hj
  rw [iteratedDeriv_smul_const (sp j),iteratedDeriv_pow,
    Nat.descFactorial_eq_zero_iff_lt.mpr (mem_range.mp hj)]
  simp
private theorem top (k:ℕ)(P:Polynomial ℂ):iteratedDeriv k (poly k P) 0=(k.factorial:ℝ) • P.coeff k:=by
  have sp (j:ℕ):ContDiffAt ℝ k (fun t:ℝ=>t^j) 0:=by fun_prop
  unfold poly
  rw [iteratedDeriv_fun_sum (I:=range (k+1))
    (f:=fun j (t:ℝ)=>t^j • P.coeff j) (fun j _=>by fun_prop)]
  simp only [iteratedDeriv_smul_const (sp _),iteratedDeriv_fun_pow_zero]
  rw [sum_eq_single_of_mem k (mem_range.mpr (Nat.lt_succ_self k))]
  · simp
  · intro i _ hi;simp [Ne.symm hi]

def divided (k:ℕ)(t:ℝ)(values:ℕ→ℂ):ℂ:=(k.factorial:ℝ) • (sample k t values).coeff k

theorem interpolate (f:ℝ→ℂ)(k:ℕ){t E M:ℝ}(step:0<t)(mp:0≤M)
    (s:∀z∈Icc 0 t,ContDiffAt ℝ (k+1:ℕ) f z)
    (derivative:∀z∈Icc 0 t,‖iteratedDeriv (k+1) f z‖≤M)
    (values:ℕ→ℂ)(paid:∀j≤k,‖f (t*node k j)-values j‖≤E):
    ‖iteratedDeriv k f 0-divided k t values‖≤WilsonCapturedPrimarySamples.price k*(E/t^k+M*t):=by
  let P:=sample k t values
  let A:=fun z=>f z-poly k P z
  have sf:=s 0 (left_mem_Icc.mpr step.le)
  have g:=WilsonCapturedPrimarySamples.sampled A k step mp
    (fun z hz=>(s z hz).sub (smooth k P z (k+1)))
    (fun z hz=>by
      unfold A
      rw [iteratedDeriv_fun_sub (s z hz) (smooth k P z (k+1)),zero,sub_zero]
      exact derivative z hz)
    (fun j hj=>by
      unfold A
      rw [value k P (degree k step.ne' values),at_node k step.ne' values hj]
      exact paid j hj)
  simpa only [A,iteratedDeriv_fun_sub (sf.of_le (Nat.cast_le.mpr (Nat.le_succ k))) (smooth k P 0 k),
    top,divided,P] using g

variable {G:Gauge}(H:History G){N p i:ℕ}
local notation "n" => H.S.side i p
local notation "Ω" => Config G (H.S.side (i+1) p)
local notation "tags" => (H.levels.clock.op i p).Choices
open WilsonCapturedPrimaryAngles
theorem original (selected:H.Selected)(live:i<N)(F:tags→Ω→ℂ){M:ℝ}
    (meas:Bounded (prior G _) F M)(gross:0≤M){d:ℕ}
    (A:Hol G)(B:BudgetPoint)(o:Site n)(r:ℕ)(a:Probe G d)(k:ℕ)(dk:k≤d)
    {t E:ℝ}(tp:0<t)(unit:t≤1)(short:t*wallet A a r≤1)(width:B.threshold*(1+(r:ℝ))^2≤1)
    (values:ℕ→ℂ)
    (paid:∀j≤k,‖WilsonOriginalRadialSpringRemainder.curve H (N:=N) A B o r a F (t*node k j)-values j‖≤E):
    let f:=WilsonOriginalRadialSpringRemainder.curve H (N:=N) A B o r a F
    let fee:=WilsonOriginalRadialSpringRemainder.bill H (N:=N) A B o r a (k+1) M
    ‖iteratedDeriv k f 0-divided k t values‖≤WilsonCapturedPrimarySamples.price k*(E/t^k+fee*t):=by
  intro f fee
  have wg:0≤wallet A a r:=zero_le_one.trans (wallet_one A a r)
  have actual z (hz:z∈Icc 0 t):ContDiffAt ℝ (k+1:ℕ) f z ∧ ‖iteratedDeriv (k+1) f z‖≤fee:=
    WilsonOriginalRadialSpringRemainder.derivative H selected live F meas gross A B o r a
      (by simpa only [abs_of_nonneg hz.1] using hz.2.trans unit)
      (by rw [abs_of_nonneg hz.1];exact (mul_le_mul_of_nonneg_right hz.2 wg).trans short) width (k+1) (Nat.succ_le_succ dk)
  have nonnegative:= (norm_nonneg _).trans (actual 0 (left_mem_Icc.mpr tp.le)).2
  exact interpolate f k tp nonnegative (fun z hz=>(actual z hz).1)
    (fun z hz=>(actual z hz).2) values paid

end YM.Integration.WilsonOriginalRadialFiniteDifference
