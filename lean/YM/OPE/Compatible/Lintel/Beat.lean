import YM.OPE.Compatible.Lintel.Mit
/-! # Real wave table to centered tabs -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Work.F05
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J X Y Z:Type}{G:Gauge}{n m c f:Side}{S:StepData c f}{p q:Clip}{R T:PathData G} {P:Patch}{K:KernelChoices}{V:ChartRatio G} {i j t r:ℕ} {s s' u α T₁ T₂ b b' d U ℓ:ℝ}
namespace Script
open Page Virgin
abbrev amp (z: Tab (Shade G) n) (i:Site n)(a:TypeFace 1)(x:G.ColorIndex):ℂ:= if (a,x)= (mus G z.2) then (cell i z.1)⁻¹ else 0
lemma amp_ne (z: Tab (Shade G) n) (i:Site n)(a:TypeFace 1)(x:G.ColorIndex):‖amp z i a x‖≤1:=by unfold amp; split ; simp only [norm_inv,cell, mode_real _ _ (real_frequency _), inv_one, le_rfl]; simp
lemma railAmp (z:Tab (Shade G) n): (spool G n) (∑ i:Site n, Precision.wave i (amp z i))=(n.val:ℝ)^4 • deltaH z :=by
    rw [map_sum]; funext w; rw [Finset.sum_apply]; let c:=w.2.2; let b:=coord w.2.1; change ∑ i: Site n,(cell i w.1 * amp z i b c).re= _; by_cases hv:w.2=z.2
    · have he(i:Site n): amp z i b c=(cell i z.1)⁻¹:= if_pos ((show (b,c)=mus G w.2 from rfl).trans (congr_arg _ hv)); simp_rw [he,← Complex.re_sum]; rw [show (∑ i,cell i w.1 * _) = if w.1=z.1 then (n.val:ℂ)^4 else 0 from ?_]; swap
      · rw [← Bloch.orthogonal]; apply Finset.sum_congr rfl; intro i _; rw [cell_duality i,cell_duality i]
      split
      next hw=> have hp:w=z:=Prod.ext hw hv; subst w; rw [show (n.val:ℂ)^4=(((n.val:ℝ)^4:ℝ):ℂ) by simp,Complex.ofReal_re]; simp [deltaH]
      next hw=> have h:w ≠ z:=fun e=>hw (congr_arg Prod.fst e); simp [deltaH,h]
    have he(i:Site n):amp z i b c=0:= if_neg fun he=>hv ((mus G).injective he); have h:w≠z:=fun e=> hv (Prod.mk.inj e).2; simp only [he,mul_zero,Complex.zero_re,sum_const_zero]; simp [deltaH,h]
lemma sups2 [Fintype I][Fintype J] [NormedAddCommGroup X] [NormedSpace ℝ X](T:Tensor.T X ℝ 2)(v:I→X)(w:J→X): T ![∑ i,v i,∑ j,w j]=∑ i,∑ j,T ![v i,w j]:=by
    let L:= T.curryLeft; rw [show T ![_,_]=L (∑ i,v i) ![∑ j,w j] from rfl,map_sum, _root_.sum_apply]; refine Finset.sum_congr rfl fun i _=> ?_; let R:= (L (v i)).curryLeft; rw [show L (v i) ![∑ j,w j]= R (∑ j,w j) ![] from rfl, map_sum,_root_.sum_apply];rfl
variable (S)(hp:Odd S.ratio.count.val) {g:Bid.Dir G c→AxisChart G (forest S.ratio hp)}
lemma wield (h:FiniteBound (forest S.ratio hp) R T p q α V g T₁ T₂ b)(t:S.Choices)(z w:Tab (Shade G) c) :
     let A:=iteratedFDeriv ℝ 2 (thermal (forest S.ratio hp) t p R g V) 0 - iteratedFDeriv ℝ 2 (draft α T q) 0
     let C:=(spool G c).symm
     ‖A ![C (deltaH z),C (deltaH w)]‖ ≤ (c.val:ℝ)^4 * T₁*b*Real.exp (-T₂*c.val):=by
       intro A C; let d:ℝ:=(c.val:ℝ)^4; have hd:0<d:= by unfold d; apply pow_pos (Nat.cast_pos.mpr c.pos)
       let V : ℝ := T₁*b*Real.exp (-T₂*c.val); let a := T₁; let t' (i:Tab (Shade G) c):= C (deltaH i); let f(i: Tab (Shade G) c)(j:Site c):= wave j (amp i j); have ht(i:Tab (Shade G) c): ∑ j,f i j=d • t' i:= (spool G c).injective (by rw [map_smul, show spool G c (t' i)=deltaH i from (spool G c).apply_symm_apply _];exact railAmp i)
       have he: A ![d • t' z,d • t' w]= (d*d)* A ![t' z, t' w]:=by
           have hv:= A.map_smul_univ (c:=![d,d]) (m:=![t' z,t' w]); rw [Fin.prod_univ_two] at hv; change A _ = _; rw [show ![d • t' z,d • t' w]=(fun i:Fin 2=> (![d,d] i) • ((![t' z,t' w]: Fin 2→Bid.Dir G c) i)) from funext fun i=>by fin_cases i<;>rfl];exact hv
       apply le_of_mul_le_mul_left _ (mul_pos hd hd);rw [← show ‖A ![d • t' z,d • t' w]‖= (d*d)* _ from by rw [he,norm_mul, Real.norm_of_nonneg (mul_pos hd hd).le],← ht,← ht, sups2]; refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun (_:Site c)=>∑ _ : Site c,d*V) (fun i _=> (norm_sum_le ..).trans (sum_le_sum (fun j _=> (h.wave_price t i j _ _ (amp_ne z i) (amp_ne w j)).trans_eq ?_)))).trans_eq ?_)
       · rw [site_card]; unfold V d; push_cast; ring
       rw [sum_const, sum_const]; simp only [nsmul_eq_mul,card_univ,site_card,Nat.cast_pow]; unfold V d; ring
end Script
end YM.OPE.Flume
