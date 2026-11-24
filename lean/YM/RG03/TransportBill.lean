import YM.RG03.Valuation

/-! Quantitative nonlinear replacements: the extra curvature degree pays another factor of the actual
threshold through every required derivative (inside a COMMON healthy mask only). Full mask correction
must be separate. `cubeClosure` also has valuation ≥2 in raw link jets; pairing with at least one further
positive-degree factor starts at degree ≥3 and so has unconditional affine-Hessian nullness as needed
for a vacuum regular label. No contraction of a general inherited remainder asserted. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG03
open Wilson RG Lattice Next.Scheduling.Wages Work.G07
open scoped ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n : Side} {P: BudgetPoint}
    {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A:Type*} [NormedRing A] [NormedAlgebra ℝ A] {a:ℕ}
    {o:Site n}{X:Support n}{x y z : Config G n→A}{u:ℝ}

def costTriple (P:BudgetPoint) (u:ℝ) := let m := (2:ℝ)^P.order; 4 * (1+m*u)^3

private lemma poly_cost :
    let m := (2:ℝ)^P.order
    0≤u → (3*(m*(u*P.threshold)*(u*P.threshold))+(m*(m*(u*P.threshold)*(u*P.threshold))*(u*P.threshold))) ≤ costTriple P u * P.threshold^2 := by
  intro m hu
  unfold costTriple
  change _ ≤ 4*(1+m*u)^3*P.threshold^2
  have hm : 1≤m := one_le_pow₀ (by norm_num)
  have hP := P.threshold_pos
  have he:(1+m*u)≥0 := by positivity
  calc _ = (3*(m*u*u) + m^2*u^3*P.threshold) * P.threshold^2 := by ring
       _ ≤ (3*(m*u*u) + m^2*u^3*1) * P.threshold^2 := by gcongr; exact P.threshold_le
       _ ≤ 4 * (1+m*u)^3*P.threshold^2 := by gcongr; nlinarith [mul_nonneg (show 0≤m^2*(m-1) from by nlinarith) (show 0≤u^3 from by positivity),mul_nonneg (show 0≤m*(m-1) from by nlinarith) (sq_nonneg u), show 0≤m^2*u^3 from by positivity ]

private lemma u_nonneg (h:Pays P o X x (u*P.threshold)) : 0≤u := by
  have := h.nonneg
  have := P.threshold_pos
  nlinarith

lemma higher_pay (h : Pays P o X x (u*P.threshold)) (h' : Pays P o X y (u*P.threshold))
    (h'' : Pays P o X z (u*P.threshold)) : Pays P o X (fun U=>higher (x U) (y U) (z U)) (costTriple P u * P.threshold^2) := by
  have hp := Pays.mul h h'
  have hq := Pays.add (Pays.add (Pays.add hp (Pays.mul h' h'')) (Pays.mul h h'')) (Pays.mul hp h'')
  apply Pays.more hq
  apply le_trans (le_of_eq (by ring)) (poly_cost (P:=P) (u_nonneg h))

lemma increment_pay (h : Pays P o X x (u*P.threshold)) (h' : Pays P o X y (u*P.threshold))
    (h'' : Pays P o X z (u*P.threshold)) : Pays P o X (fun U=>incrementMat (x U) (y U) (z U)) (costTriple P u * P.threshold^2) := by
  have hq := Pays.add (Pays.add (Pays.mul h'' h) (Pays.mul h h')) (Pays.mul (Pays.mul h'' h) h')
  apply Pays.more hq
  have ht := P.threshold_pos.le
  have hu := u_nonneg h
  apply le_trans (show _ ≤ 3*((2:ℝ)^P.order*(u*P.threshold)*(u*P.threshold))+
    (2:ℝ)^P.order*((2:ℝ)^P.order*(u*P.threshold)*(u*P.threshold))*(u*P.threshold) by linarith [(show 0 ≤ (2:ℝ)^P.order*(u*P.threshold)*(u*P.threshold) by positivity)]) (poly_cost (P:=P) (u_nonneg h))

-- no need analytic regularity of masks, nor replacing tested equality by linearization.
def supplied (P:BudgetPoint)(o:Site n)(X:Support n)(w:Circuit)(u:ℝ) (G : Gauge) : Prop :=
    w.supply o X ∧ defectCost G P w.path.length≤u

lemma supplied.pay {w:Circuit} (h:supplied P o X w u G) : Pays P o X (w.defect (G:=G) o) (u*P.threshold) :=
  Pays.more (defect_pay P o X w le_rfl h.1) (mul_le_mul_of_nonneg_right h.2 P.threshold_pos.le)

lemma increment_of_swap_pay (r s:Walk)(i j k l:Step) (h : supplied P o X ⟨r,i,j⟩ u G) (h' : supplied P o X ⟨r,j,i⟩ u G)
    (e : supplied P o X (afterSwap r s j i k l) u G) :
    Pays P o X (fun U:Config G n=> (afterSwap r s i j k l).defect o U - (afterSwap r s j i k l).defect o U) (costTriple P u * P.threshold^2) := by
  rw [show (fun U:Config G n=> (afterSwap r s i j k l).defect o U - _)=_
    from funext fun w=>sub_eq_iff_eq_add.mpr ((defect_align r s i j k l w o).trans (add_comm ..))]
  exact increment_pay e.pay h'.pay h.pay

lemma cube_pay (i j k : Step) (hij : supplied P o X (block1 i j) u G) (hjk : supplied P o X (block1 j k) u G)
  (hik : supplied P o X (block1 i k) u G)
  (hj : supplied P o X (block2 j i k) u G) (hi : supplied P o X (block2 i j k) u G)(hk : supplied P o X (block2 k i j) u G) :
  Pays P o X (cubeClosure (G:=G) o i j k) (2*G.colorScale⁻¹*costTriple P u*P.threshold^2) := by
  have he := (Pays.sub (higher_pay hi.pay hik.pay hk.pay) (higher_pay hij.pay hj.pay hjk.pay))
  simp_rw [show cubeClosure (G:=G) o i j k = fun x:Config G n=> _ from funext (bianchi o i j k)]
  refine ⟨he.smooth.postcomp _, ?_, fun a ha hD U hu => ?_⟩
  · unfold costTriple; dsimp only; have := G.colorScale_pos; have := u_nonneg (hi.pay); positivity
  refine (congrArg Norm.norm (congr_fun (left_linear he.smooth (projector G) ha) U)).trans_le ?_
  refine (norm_projector G _).trans ((mul_le_mul_of_nonneg_left (he.budget.2 U hu a ha hD) (inv_nonneg.mpr G.colorScale_pos.le)).trans_eq (by ring))

lemma higher_vanish (hx:Vanishes a x) (hy:Vanishes a y) (hz:Vanishes a z) : Vanishes (a+a) (fun U=>higher (x U) (y U) (z U)) := by
 unfold higher
 exact (((hx.mul hy).add (hy.mul hz)).add (hx.mul hz)).add (hx.mul hy |>.mul hz |>.shorten (by omega))

lemma increment_vanish (hx:Vanishes a x) (hy:Vanishes a y) (hz:Vanishes a z) : Vanishes (a+a) (fun U=>incrementMat (x U) (y U) (z U)) := by
  unfold incrementMat
  exact ((hz.mul hx).add (hx.mul hy)).add (((hz.mul hx).mul hy).shorten (by omega))

lemma swap_vanish (r s:Walk)(i j k l:Step) :
    Vanishes 2 (fun U:Config G n=> (afterSwap r s i j k l).defect o U - (afterSwap r s j i k l).defect o U) := by
  rw [show (fun U:Config G n=> (afterSwap r s i j k l).defect o U - _)=_
    from funext fun w=>sub_eq_iff_eq_add.mpr ((defect_align r s i j k l w o).trans (add_comm ..))]
  exact increment_vanish (a:=1) (defect_vanish ..) (defect_vanish ..) (defect_vanish ..)

lemma cube_vanish (i j k : Step) : Vanishes 2 (cubeClosure (G:=G) o i j k) := by
  simp_rw [show cubeClosure (G:=G) o i j k = fun x : Config G n=>_ from funext fun U=>bianchi o i j k U]
  exact (higher_vanish (a:=1) (defect_vanish ..) (defect_vanish ..) (defect_vanish ..) |>.sub
    (higher_vanish (a:=1) (defect_vanish ..) (defect_vanish ..) (defect_vanish ..))).clm _
end YM.RG03
