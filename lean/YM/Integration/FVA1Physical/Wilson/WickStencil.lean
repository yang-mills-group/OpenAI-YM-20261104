import YM.MSbar.Cacao.Gloss

/-! Every finite polynomial stencilled Gaussian reading is one universal polynomial
in its selected mean and covariance entries. The ambient torus does not occur
in this polynomial. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Finset Matrix MeasureTheory MvPolynomial MSbar.Cacao Further.GaussianScalar
open scoped Classical
variable {ι σ : Type} [Fintype σ] [DecidableEq σ]
abbrev WickSlot (σ : Type) := σ ⊕ σ × σ

def parameters (x : σ→ℝ) (K:σ→σ→ℝ) : WickSlot σ→ℝ := Sum.elim x (fun ij=>K ij.1 ij.2)

def heatStencil : ℕ → Pot σ → Pot (WickSlot σ)
  | 0, P=> MvPolynomial.rename Sum.inl P
  | n+1, P=> ∑ i,∑ j, (MvPolynomial.C (1/2) * MvPolynomial.X (Sum.inr (i,j))) *
        heatStencil n (MvPolynomial.pderiv i (MvPolynomial.pderiv j P))

def wickStencil (P : Pot σ) : Pot (WickSlot σ) :=
  ∑ j∈Finset.range (P.totalDegree+1),(j.factorial:ℝ)⁻¹ • heatStencil j P

lemma eval_real_smul {α : Type} (x : α→ℝ) (a : ℝ) (p : Pot α) :
    MvPolynomial.eval x (a • p)=a*MvPolynomial.eval x p := by
  rw [←MvPolynomial.C_mul',_root_.map_mul,MvPolynomial.eval_C]

omit [DecidableEq σ] in
lemma heatStencil_eval (x:σ→ℝ) (K:σ→σ→ℝ) (n:ℕ) (P : Pot σ) :
    MvPolynomial.eval (parameters x K) (heatStencil n P) = MvPolynomial.eval x (((stove K)^n) P) := by
  induction n generalizing P with
  | zero=> simp [heatStencil,parameters,MvPolynomial.eval_rename,Function.comp_def]
  | succ n ih=>
    rw [heatStencil,pow_succ,Module.End.mul_apply,stokes]
    simp only [_root_.map_sum,_root_.map_mul,MvPolynomial.eval_X,MvPolynomial.eval_C,parameters,Sum.elim_inr,
      map_smul,eval_real_smul]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [show MvPolynomial.eval (Sum.elim x fun ij=>K ij.1 ij.2) (heatStencil n ((pderiv i) ((pderiv j) P)))=_
      from ih ((pderiv i) ((pderiv j) P))]
    ring

omit [DecidableEq σ] in
theorem wickStencil_eval (x:σ→ℝ) (K:σ→σ→ℝ) (P : Pot σ) :
    MvPolynomial.eval (parameters x K) (wickStencil P)=MvPolynomial.eval x (bowl K P) := by
  unfold wickStencil bowl pearl
  simp only [_root_.map_sum, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
    one_pow,mul_one,pour,eval_real_smul,heatStencil_eval]

theorem wickStencil_integral [Fintype ι] [DecidableEq ι] (v:Matrix σ ι ℝ) (x:View σ)
    {C:Matrix ι ι ℝ} (hp:C.PosDef) (P:Pot σ) :
    MvPolynomial.eval (parameters x (v*C*v.transpose)) (wickStencil P)=
    ∫ y:View ι, MvPolynomial.eval (x+v *ᵥ y) P ∂fieldLaw C :=
  (wickStencil_eval x _ P).trans (seen v x hp P)
end YM.Integration.FVA1Physical.Wilson
