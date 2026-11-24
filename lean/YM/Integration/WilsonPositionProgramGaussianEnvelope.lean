import YM.Integration.WilsonPositionProgramFiledGaussianChange

/-! Finite Gaussian prices for signed Wilson cofactors at their actual affine mean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramGaussianEnvelope
open Function Finset MeasureTheory
open Next.SectorChange Next.SectorChange.Gaussian Next.Rank Comparison.RG02.Cumulants
open scoped BigOperators Classical
variable {I:Type}[Fintype I][DecidableEq I]

def conjugate (f:Normal.poly I):Normal.poly I:=MvPolynomial.map (starRingEnd ℂ) f

omit [Fintype I] [DecidableEq I] in
theorem conjugated (x:I→ℝ)(f:Normal.poly I):Cloud.paint x (conjugate f)=star (Cloud.paint x f):=by
  induction f using MvPolynomial.induction_on with
  | C a=>simp [conjugate,Cloud.paint]
  | add p q hp hq=>simp only [conjugate,map_add] at *;simp [hp,hq]
  | mul_X p i hp=>simp only [conjugate,map_mul] at *;simp [hp,Cloud.paint]

def stock (E H:Normal.poly I):Normal.poly I:=E*(1+H*conjugate H)

omit [Fintype I] [DecidableEq I] in
theorem stock_read (x:I→ℝ)(E H:Normal.poly I):
    (Cloud.paint x (stock E H)).re=(Cloud.paint x E).re*(1+‖Cloud.paint x H‖^2):=by
  rw [stock,map_mul,map_add,map_one,map_mul,conjugated,Complex.star_def,Complex.mul_conj,
    Complex.normSq_eq_norm_sq]
  simp only [Complex.mul_re,Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.one_re,Complex.one_im,zero_add,mul_zero,sub_zero]

theorem bound (Q:Matrix I I ℝ)(hQ:Q.IsSymm)(hq:Q.PosSemidef)(m:I→ℝ)
    (D H E:Normal.poly I)(e:ℝ)
    (submit:∀z,‖Cloud.paint (m+z) D‖≤e*(Cloud.paint (m+z) E).re):
    ‖Cloud.wick Q hQ (Cloud.shift m) (D*H)‖≤e*(Cloud.wick Q hQ (Cloud.shift m) (stock E H)).re:=by
  obtain ⟨hstock,evalstock⟩:=Cloud.paid Q hQ hq m (stock E H)
  have cash:(∫z,(Cloud.paint (m+z) (stock E H)).re ∂cloud Q)=
      (Cloud.wick Q hQ (Cloud.shift m) (stock E H)).re:=
    (integral_re hstock).trans (congrArg Complex.re evalstock)
  rw [←(Cloud.paid Q hQ hq m (D*H)).2,←cash,←integral_const_mul]
  refine norm_integral_le_of_norm_le (hstock.re.const_mul e) (ae_of_all _ fun z=>?_ )
  rw [map_mul,norm_mul,stock_read,←mul_assoc]
  have head:=submit z
  have hpos:=le_trans (norm_nonneg _) head
  apply mul_le_mul head _ (norm_nonneg _) hpos
  nlinarith [sq_nonneg (‖Cloud.paint (m+z) H‖-1/2)]

end YM.Integration.WilsonPositionProgramGaussianEnvelope
end
