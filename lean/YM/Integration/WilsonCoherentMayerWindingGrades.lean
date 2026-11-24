import YM.Integration.WilsonCoherentMayerWindingDensity

/-! Evaluating the signed finite-minus-covered club series on its original graded input. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerWindingGrades
open Finset RG Marker Comparison.RG02 Push.AbsoluteSums
open scoped BigOperators Classical Topology
variable {V ι:Type} [DecidableEq V] [Fintype V] {ρ:Census V}

def panel (r:ℕ) (g:ℂ)(term:ℕ→Poly ρ) : Poly ρ :=
  ∑ j∈range (r+1),g^j • term j

omit [Fintype V] in
theorem reverse (w:V→ℝ)(a b:Poly ρ):
    Poly.price w (a-b)=Poly.price w (b-a):=by
  rw [←neg_sub b a,←neg_one_smul ℂ (b-a),Poly.adapted,norm_neg,norm_one,one_mul]

omit [Fintype V] in
private theorem collect (g:ℂ) (D:Finset ℕ) (miss:ℕ→ι→Poly ρ)(e:ℕ→Poly ρ)
    (paid:∀j∈D,HasSum (miss j) (e j)):
    HasSum (fun c=>∑j∈D,g^j • miss j c) (∑j∈D,g^j • e j):=by
  induction D using Finset.induction_on with
  | empty => simp
  | @insert j D fresh ih =>
    have h:HasSum (fun c=>g^j • miss j c) (g^j • e j):=
      (paid j (mem_insert_self ..)).const_smul (g^j)
    simpa only [sum_insert fresh] using h.add (ih (fun i hi=>paid i (mem_insert_of_mem hi)))

theorem evaluated (w:V→ℝ)(hw:∀i,0<w i)(r:ℕ)(g:ℂ)(ledger:Order.Grade ρ r)
    (lower:ℕ→Poly ρ)(miss:ℕ→ι→Poly ρ)(bill:ℕ→ℝ)
    (paid:∀j≤r,∃e:Poly ρ,Order.observe ρ r ledger j=lower j+e ∧
      Poly.price w e ≤bill j ∧ HasSum (miss j) e ∧
      RG.SumBudget (fun c=>Poly.price w (miss j c)) (bill j)):
    let point:=Order.value g ledger
    let filed:=panel r g lower
    let total:=∑j∈range (r+1),‖g‖^j*bill j
    HasSum (fun c=>panel r g (fun j=>miss j c)) (point-filed) ∧
      RG.SumBudget (fun c=>Poly.price w (panel r g (fun j=>miss j c))) total ∧
      Poly.price w (filed-point)≤total:=by
  intro point filed total
  let e:=fun j=>Order.observe ρ r ledger j-lower j
  have got(j:ℕ)(hj:j≤r):
      Poly.price w (e j)≤bill j ∧ HasSum (miss j) (e j) ∧
        RG.SumBudget (fun c=>Poly.price w (miss j c)) (bill j):=by
    obtain ⟨v,hv,p,h,b⟩:=paid j hj
    simpa only [e,hv,add_sub_cancel_left] using And.intro p (And.intro h b)
  have diff:point-filed=panel r g e:=by simp only [point,filed,Order.value,panel,e,smul_sub,sum_sub_distrib]
  refine ⟨diff ▸ collect g (range (r+1)) miss e (fun j hj=>(got j (by simpa using hj)).2.1),?_,?_⟩
  · apply budget_of_sum (fun c=>Poly.nonnegative hw _)
    intro L
    calc
      ∑c∈L,Poly.price w (panel r g (fun j=>miss j c)) ≤
          ∑c∈L,∑j∈range (r+1),‖g‖^j*Poly.price w (miss j c):=by
        refine sum_le_sum fun c _=>?_
        simpa only [panel,Poly.adapted,norm_pow] using
          (Poly.batch hw (range (r+1)) (fun j=>g^j • miss j c))
      _ = ∑j∈range (r+1),‖g‖^j*(∑c∈L,Poly.price w (miss j c)):=by
        rw [sum_comm]
        simp only [mul_sum]
      _ ≤ total:=sum_le_sum fun j hj=>mul_le_mul_of_nonneg_left
        (budget_sum (got j (by simpa using hj)).2.2 L) (pow_nonneg (norm_nonneg _) _)
  · rw [reverse w filed point,diff]
    refine (Poly.batch hw (range (r+1)) (fun j=>g^j • e j)).trans (sum_le_sum fun j hj=>?_)
    simpa only [Poly.adapted,norm_pow] using
      (mul_le_mul_of_nonneg_left (got j (by simpa using hj)).1 (pow_nonneg (norm_nonneg g) j))

theorem capped (g:ℂ) (small:‖g‖≤1/2) (r:ℕ) (c:ℝ)(pos:0≤c):
    (∑j∈range (r+1),‖g‖^j*c)≤2*c:=by
  have geom (n:ℕ):(∑j∈range n,‖g‖^j)≤2-2*‖g‖^n:=by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ,pow_succ]
      nlinarith only [ih,mul_nonneg (pow_nonneg (norm_nonneg g) n) (sub_nonneg.mpr small)]
  rw [←sum_mul]
  exact mul_le_mul_of_nonneg_right ((geom (r+1)).trans (sub_le_self _ (by positivity))) pos

end YM.Integration.WilsonCoherentMayerWindingGrades
