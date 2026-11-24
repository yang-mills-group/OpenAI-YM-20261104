import YM.Integration.WilsonVacuumPreResetTorusRegradedAction
import YM.Integration.WilsonVacuumPreResetFiniteHeatCourse

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonIndependentVacuumDirection
open Finset Lattice RG WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos
open Next.Foundations
open scoped Classical BigOperators

private theorem panel {V:Type}[Fintype V](r:ℕ)(F:Ten ℝ V r)(x:V→ℝ):
    MvPolynomial.eval x (paint r F)=∑a:Fin r→V,F a*∏i,x (a i):=by
  change MvPolynomial.eval x (∑a:Fin r→V,F a • ∏i,MvPolynomial.X (a i))=_
  simp [MvPolynomial.smul_eq_C_mul]

theorem tensor {V:Type}[Fintype V](r:ℕ)(S T:Ten ℝ V r)(x:V→ℝ){η w:ℝ}
    (eta:0≤η)(size:∀a,|x a|≤w)(small:∀a,|S a-T a|≤η):
    |MvPolynomial.eval x (paint r S)-MvPolynomial.eval x (paint r T)| ≤
      ((Fintype.card V:ℝ)*w)^r*η:=by
  rw [panel,panel,←Finset.sum_sub_distrib]
  simp only [←sub_mul]
  calc
    _ ≤ ∑a:Fin r→V,|(S a-T a)*∏i,x (a i)|:=Finset.abs_sum_le_sum_abs .. 
    _ ≤ ∑_a:Fin r→V,η*w^r:=Finset.sum_le_sum fun a _=>by
      have products := Finset.prod_le_prod (s:=Finset.univ) (f:=fun i:Fin r=>|x (a i)|)
        (g:=fun _=>w) (fun _ _=>abs_nonneg _) (fun i _=>size (a i))
      rw [abs_mul,Finset.abs_prod]
      simpa only [Finset.prod_const,card_univ,Fintype.card_fin] using
        mul_le_mul (small a) products (Finset.prod_nonneg fun _ _=>abs_nonneg _) eta
    _ = _:=by simp only [Finset.sum_const,card_univ,nsmul_eq_mul,Fintype.card_fun,
        Fintype.card_fin,Nat.cast_pow,mul_pow]; ring

theorem difference {G:Gauge}{n:Side}(t:ℕ)(P Q:PChart G n)(p:shellK 2 P)(q:shellK 2 Q)
    {η w:ℝ}(eta:0≤η)(w1:1≤w)(x y:Woods G n → ℝ)
    (cx:∀u,|x u|≤w)(cy:∀u,|y u|≤w)
    (terms:∀r<t+2,∀v,|P t (r+1) v-Q t (r+1) v|≤η):
    let z:=(1+(Fintype.card (Woods G n):ℝ))*w
    let Δ:=fun P=>WilsonVacuumPreResetTorusGrade.evaluated P t x-WilsonVacuumPreResetTorusGrade.evaluated P t y
    |Δ P-Δ Q|≤2*((t+2:ℕ):ℝ)*z^(t+2)*η:=by
  intro z Δ
  dsimp only [Δ]
  rw [WilsonVacuumPreResetTorusGrade.positive P p,WilsonVacuumPreResetTorusGrade.positive Q q,
    ←Finset.sum_sub_distrib]
  have z1:1≤z:=one_le_mul_of_one_le_of_one_le (by linarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card (Woods G n))]) w1
  have large(r)(hr:r<t+2): ((Fintype.card (Woods G n):ℝ)*w)^(r+1) ≤ z^(t+2):=by
    apply (pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans w1)) _ _).trans
        (pow_le_pow_right₀ z1 (by omega))
    dsimp only [z]
    nlinarith only [w1]
  apply (Finset.abs_sum_le_sum_abs ..).trans
  calc
    _ ≤ ∑_r∈Finset.range (t+2),2*z^(t+2)*η:=Finset.sum_le_sum fun r hr=>by
      have bound(field:Woods G n → ℝ)(paid:∀u,|field u|≤w):=
        (tensor (r+1) (P t (r+1)) (Q t (r+1)) field eta paid
          (terms r (mem_range.mp hr))).trans (mul_le_mul_of_nonneg_right (large r (mem_range.mp hr)) eta)
      rw [sub_sub_sub_comm]
      exact (abs_sub ..).trans (by linarith only [bound x cx,bound y cy])
    _ = _:=by simp only [sum_const,card_range,nsmul_eq_mul]; ring

end YM.Integration.WilsonIndependentVacuumDirection
end
