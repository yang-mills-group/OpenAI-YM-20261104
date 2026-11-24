import YM.RG01Estimate.GermEqual
/-! # equilibrium 
 Pointwise preassignments or sunny equations all suffice. New kernel Σ density equality
 path exact. Nonheuristic. Ph λ pad class. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Censor
open Function Filter Set Lattice Wilson RG AnalyticBridge VerifiedReset Collection Averaging
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{n:Side}{p:BudgetPoint}{X:Support n}{a K:Listing G n}{v W:Collection.Source G n}
    (g:G.Simple) {f:Pot G n} {u H d D' β τ τ' α:ℝ} {C:Clip}{S:PathData G}
    (H':Local a p v H u)(h':Local K p W D' d)
    (hx:∀ U:Config G n,flags p.threshold U=∅→earlyValue a S C p v β τ α U=earlyValue K S C p W β τ' α U)

open Along
include g H'
private lemma currency (x y:Site n) : Summable fun i:ℕ=> wires (v.logRead i) x y:=by
     obtain ⟨b,hb,hb'⟩:= Activities.E_total H'.unweighted
     refine Summable.of_norm_bounded (hb.mul_right (3/p.threshold^2)) (fun i=> stab g (a:=a.reg i) (H'.smooth i) (hb' i) x y)

-- aspirant probe in authorized halo-sun chart
include hx h'
lemma partial_eq (z : Directions G n)(ht: ∀ i,p.dirBound i z) : (∑' i, logHessian (v.logRead i) z z)=∑' i, logHessian (W.logRead i) z z :=by
     have hf (U:Config G n) (hh:flags p.threshold U=∅): τ*Fintype.card (Site n)-(a.read v).additive p U=τ'*Fintype.card (Site n)-(K.read W).additive p U:=by
        have hx:= hx U hh
        unfold earlyValue at hx
        have hs:= mul_right_cancel₀ (Real.exp_pos _).ne' hx
        unfold Rep.eval Rep.exponent at hs; dsimp only [frozen] at hs; rw [Activities.gas_one (a.read v) p hh,Activities.gas_one (K.read W) p hh,mul_one,mul_one] at hs
        linarith only [Real.exp_injective hs]
     have hz:= jurors g H' z ht
     have hw:= jurors g h' z ht
     have hb:(∑' i, logHessian (v.logRead i) z z)/2=(∑' i, logHessian (W.logRead i) z z)/2:= by
        refine tendsto_nhds_unique (hz.1.congr' ?_) hw.1
        filter_upwards [Eventually.filter_mono nhdsWithin_le_nhds (Pert.Kinetic.rays_free (G:=G) _ p.threshold_pos z)] with t ht
        congr 1; linarith only [hf _ ht,hf 1 (UVNext.CouplingReset.flags_one ..)]
     linarith only [hb]

lemma verdict (x y:Site n) : (∑' i,wires (v.logRead i) x y)= (∑' i,wires (W.logRead i) x y):=by
    let t := p.threshold
    let r := p.threshold*2⁻¹
    let u := fun z:Site n=> r • needle G z
    have hU z o:p.dirBound o (u z):= by
       intro i; have h:= sample (p:=p) g z o i; rw [Pi.smul_apply,norm_smul] at h; unfold u; rw [Pi.smul_apply,norm_smul]; apply le_trans _ h
       apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); unfold r; rw [norm_mul]; norm_num; linarith only [abs_nonneg p.threshold]
    have hv o : p.dirBound o (u x+u y):= by
       intro i; unfold u; rw [Pi.add_apply,Pi.smul_apply, Pi.smul_apply]; apply (norm_add_le ..).trans; rw [norm_smul,norm_smul]; unfold r; simp only [norm_mul,norm_inv]; have he:= sample (p:=p) g x o i; have h:= sample (p:=p) g y o i; rw [Pi.smul_apply,norm_smul, Real.norm_eq_abs] at he h; norm_num; linarith only [he,h]
    have h (f:Pot G n) (X:Support n) (h:p.Regular X f) :
        logHessian f (u x+u y) (u x+u y)=logHessian f (u x) (u x)+logHessian f (u y) (u y)+2*(r*r)* wires f x y:= by
        simp only [hessian_eq,map_add,add_apply]; simp_rw [← hessian_eq]
        rw [hessian_symm h (u y) (u x)]; simp only [u,hessian_eq,map_smul,smul_apply,smul_eq_mul,wires]; ring
    have ht := partial_eq g H' h' hx (u x + u y) hv
    have hT := jurors g H' (u x) (hU x)
    have hp := jurors g H' (u y) (hU y)
    have hr:0<r:= by unfold r; have he:=p.threshold_pos; positivity
    simp_rw [fun i=> h _ _ (H'.smooth i), fun i=> h _ _ (h'.smooth i)] at ht
    rw [(hT.2.add hp.2).tsum_add ((currency g H' x y).mul_left _), hT.2.tsum_add hp.2,
      ((jurors g h' (u x) (hU x)).2.add (jurors g h' (u y) (hU y)).2).tsum_add ((currency g h' x y).mul_left _), (jurors g h' (u x) (hU x)).2.tsum_add (jurors g h' (u y) (hU y)).2, tsum_mul_left,tsum_mul_left,
      partial_eq g H' h' hx _ (hU x), partial_eq g H' h' hx _ (hU y)] at ht
    exact mul_left_cancel₀ (by positivity) (add_left_cancel ht)

theorem kinetic (hn:20<n.val) : Real.exp ((p.supportExponent+3)*(coin p n hn:ℝ)) * (p.threshold^2*|delta (a.read v)-delta (K.read W)|) ≤
       huge n *(H+D'):=by
    have ha:= jury_pays g H' hn
    have hb:= jury_pays g h' hn
    have hT: 0 < (Fintype.card (Site n):ℝ) := Nat.cast_pos.mpr Fintype.card_pos
    have he:(∑' i:ℕ, judge (v.logRead i))= ∑' i:ℕ, judge (W.logRead i):=by
       let u (x y : Site n):= pitch x y^2
       have h₁ (x y:Site n):= (currency g H' x y).mul_left (u x y)
       have h₂ (x y:Site n):= (currency g h' x y).mul_left (u x y)
       simp_rw [judge,tsum_mul_left]; congr 1
       rw [Summable.tsum_finsetSum (fun x _=> summable_sum (fun y _ => h₁ x y)),Summable.tsum_finsetSum (fun x _=>summable_sum (fun y _=>h₂ x y))]
       apply Finset.sum_congr rfl; intro i _
       rw [Summable.tsum_finsetSum (fun y _=> h₁ i y),Summable.tsum_finsetSum (fun y _=> h₂ i y)]; simp_rw [tsum_mul_left]
       simp_rw [verdict g H' h' hx]
    rw [he] at ha
    let V:= ∑' i:ℕ, judge (W.logRead i)
    apply le_of_mul_le_mul_left (a:=(Fintype.card (Site n):ℝ)) _ hT
    let E:= Real.exp ((p.supportExponent+3)*(coin p n hn:ℝ)); have hE:0≤ E:= Real.exp_nonneg _
    let Y:ℝ:= Fintype.card (Site n); let z:= delta (K.read W)*Y-V; let y:= delta (a.read v)*Y-V;
    have hu: Y*|delta (a.read v)-delta (K.read W)|=‖y-z‖ := by
       rw [← abs_of_nonneg (a:=Y) hT.le,← abs_mul]
       unfold y z; rw [sub_sub_sub_cancel_right]; change _=|_|; congr 1; ring
    calc
      _ = E*(p.threshold^2*‖y-z‖):= by rw [← hu]; unfold Y E; ring
      _ ≤ _ := by linarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (norm_sub_le y z) (sq_nonneg p.threshold)) hE,show E * (p.threshold^2*‖y‖)≤ huge n * (↑(Fintype.card (Site n))*H) from ha,show E*(p.threshold^2*‖z‖) ≤ huge n*(↑(Fintype.card (Site n))*D') from hb]
end YM.RG01Estimate.Censor
