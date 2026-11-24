import YM.Integration.WilsonVacuumPreResetTorusSeason

/-! On a finite torus, the complete numerical contraction of a translation
invariant signed tensor has an intensive bound at one physical root. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetTorusContraction
open Filter Function Lattice Wilson WilsonCoeffUV WilsonCoeffUV.Bank
open Matrix RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open scoped Classical BigOperators
variable {α:Type*}[Fintype α]{n:Side}{l:ℕ}

def charge (F:Ten ℝ (Co n α) (l+1))(u:Site n)(a:α):ℝ:=
  ∑y:dock (Site n) α l,‖F (Fin.cons (u,a) y)‖

theorem translated (F:Ten ℝ (Co n α) (l+1))(moves:stroll F)(u:Site n)(a:α):
    charge F u a=charge F 0 a:=by
  classical
  let E:dock (Site n) α l ≃ dock (Site n) α l:=Equiv.piCongrRight fun _=>jog u
  unfold charge
  rw [←E.sum_comp (fun y=>‖F (Fin.cons (u,a) y)‖)]
  apply Finset.sum_congr rfl
  intro y _
  have pins:Fin.cons (u,a) (E y)=jog u ∘ Fin.cons (0,a) y:=by
    funext b
    refine Fin.cases ?_ (fun _=>rfl) b
    simp [jog]
  rw [pins,moves u]

def joined (F:Ten ℝ (Co n α) (l+1))(H:(Fin (l+1)→ (Site n × α))→ℂ):ℂ:=
  ∑u:Site n,∑a:α,∑y:dock (Site n) α l,
    let row:=Fin.cons (u,a) y
    F row • H row

theorem absolute_bound (F:Ten ℝ (Co n α) (l+1))(moves:stroll F)
    (H:(Fin (l+1)→ (Site n × α))→ℂ){D:ℝ}(bounded:∀row,‖H row‖≤D):
    ‖joined F H‖≤(Fintype.card (Site n):ℝ)* (D * ∑a,charge F 0 a):=by
  have one (u:Site n)(a:α):‖∑y:dock (Site n) α l,
      F (Fin.cons (u,a) y) • H (Fin.cons (u,a) y)‖ ≤ D*charge F 0 a:=by
    rw [←translated F moves u a]
    apply (norm_sum_le _ _).trans
    unfold charge
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro y _
    rw [norm_smul,mul_comm D]
    exact mul_le_mul_of_nonneg_left (bounded _) (norm_nonneg _)
  unfold joined
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑_u:Site n,D*∑a,charge F 0 a:=by
      apply Finset.sum_le_sum
      intro u _
      exact (norm_sum_le _ _).trans (by rw [Finset.mul_sum];exact Finset.sum_le_sum fun a _=>one u a)
    _ = _:=by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

theorem painted (F:Ten ℝ (Co n α) (l+1))(z:Co n α → ℝ):
    ((MvPolynomial.eval z (Blue.paint (l+1) F):ℝ):ℂ)=
    joined F (fun row=>∏i,(z (row i):ℂ)):=by
  classical
  let E:(Co n α × dock (Site n) α l) ≃ (Fin (l+1) → (Site n × α)):=
    { toFun:=fun p=>Fin.cons p.1 p.2
      invFun:=fun x=>(x 0,Fin.tail x)
      left_inv:=fun p=>by cases p;rfl
      right_inv:=fun x=>by funext i;refine Fin.cases rfl (fun _=>rfl) i }
  let value (row:Fin (l+1) → (Site n × α)):ℂ:=(F row:ℂ)*∏i,(z (row i):ℂ)
  have full:((MvPolynomial.eval z (Blue.paint (l+1) F):ℝ):ℂ)=∑row,value row:=by
    change ((MvPolynomial.eval z (∑row,F row • ∏i,MvPolynomial.X (row i)):ℝ):ℂ)=_
    simp [value,MvPolynomial.smul_eq_C_mul]
  rw [full,←E.sum_comp value]
  simp [Fintype.sum_prod_type,joined,E,value,Complex.real_smul]

end YM.Integration.WilsonVacuumPreResetTorusContraction
