import YM.OPE.Compatible.Grove.Quill
/-! # Derivative rooted sup arc. Raw Mark.P.V cost without density truncation. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume.Script
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J W E X:Type*}{i j n r d m:ℕ}{G:Gauge}{s b U D:ℝ}
open Page
variable [NormedAddCommGroup E][NormedSpace ℝ E]
-- cashBill scales
lemma fee_SC (f:ℝ→E)(hp:ContDiff ℝ ⊤ f)(c:ℝ)(j:ℕ)(t:ℝ): iteratedDeriv j (fun i=>f (c*i)) t=c^j • iteratedDeriv j f (c*t):=by
        let A:= c • ContinuousLinearMap.id ℝ ℝ; change iteratedFDeriv ℝ j (f∘A) t (fun _=>1)= _; have hz:= (A.iteratedFDeriv_comp_right hp t (i:=j) le_top); rw [hz]; change iteratedFDeriv ℝ j f (c*t) (fun _=>c*1)=_; simp only [mul_one]; let p:= iteratedFDeriv ℝ j f (c*t); have he:= p.map_smul_univ (fun i=>c) (fun i=>1); simpa only [smul_eq_mul,mul_one,prod_const,Fintype.card_fin,card_univ] using! he
section
omit [NormedAddCommGroup E][NormedSpace ℝ E]
lemma Scallop (G:Gauge)(k:ℕ) (s D:ℝ)(hk: 0<s)(hv:0 ≤ D)(i:ℕ):∃ b:ℝ,0 ≤ b∧∀ (p:Chant G k)(c:ℝ)(_hc:0 < c)(_hh:moderateX p D)(V:fieldX (Shade G)), (∀ j∈cashX p,‖indexS j V‖≤c)→∀ t:ℝ, ‖iteratedDeriv i (fun t:ℝ=>verseX p (lotU (t • V))) t‖ ≤ c^i*(b*Real.exp (s*lawn p)):=by
         obtain ⟨b,hb,H⟩:=cashBill G k _ 1 _ hk zero_le_one hv i; refine ⟨b,hb,fun p c hP hm V hx x=>?_⟩; let f:=fun t:ℝ=> verseX p (lotU (t • c⁻¹ • V)); rw [show (fun t:ℝ=>verseX p (lotU (t • V)))=fun y=> f (c*y) from funext fun i=>by unfold f; rw [mul_comm,mul_smul, smul_inv_smul₀ hP.ne'],fee_SC f (cash_smooth p _) c _,norm_smul,Real.norm_of_nonneg (pow_nonneg hP.le _)]; apply mul_le_mul_of_nonneg_left _ (pow_nonneg hP.le _); apply H _ _ hm; intro j hj; rw [map_smul,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hP.le),← div_eq_inv_mul]; exact (div_le_one hP).mpr (hx _ hj)
end
variable {P:I→ Chant G n}{x:I→ℝ}{v:fieldX (Shade G)}{N:Side}
omit [NormedAddCommGroup E][NormedSpace ℝ E] in
lemma lyricQ (h:saturate P x s U)(hs:0<s)(hg:∀ i,moderateX (P i) D)(hy:0≤D)(k:ℕ)(hp:Quiet v 0)(t:ℝ): HasSum (fun i=> x i * iteratedDeriv k (fun t:ℝ=>verseX (P i) (lotU (t • v))) t) (iteratedDeriv k (fun t:ℝ=> rhythm P x (lotU (t • v))) t):=by
    let f(i:I)(t:ℝ):=x i * verseX (P i) (lotU (t • v)); have he(i):ContDiff ℝ ∞ (f i):=contDiff_const.mul (cash_smooth _ v |>.of_le le_top)
    obtain ⟨z,hz,H⟩:=staffQ v hp; choose c hc hh using fun j=>cashBill G n s z D hs hz hy j
    let A(j)(i):=c j*(‖x i‖*Real.exp (s * lawn (P i))); have hP(j):Summable (A j):=h.2.1.mul_left _
    let g(i:I)(t:ℝ):=verseX (P i) (lotU (t • v))
    have hx(j:ℕ)(i t):iteratedFDeriv ℝ j (f i) t=x i • iteratedFDeriv ℝ j (g i) t:=by change iteratedFDeriv ℝ j (x i • g i) t=_; exact iteratedFDeriv_const_smul_apply ((cash_smooth (P i) v).contDiffAt.of_le le_top)
    have hV(j:ℕ)(i:I)(t):‖iteratedFDeriv ℝ j (f i) t‖≤ A j i:=by
       rw [hx,norm_smul,norm_iteratedFDeriv_eq_norm_iteratedDeriv]; exact (mul_le_mul_of_nonneg_left (hh j _ _ (hg i) (fun a _=>H a) t) (norm_nonneg _)).trans_eq (by unfold A;ring)
    change HasSum _ (iteratedFDeriv ℝ k (fun t:ℝ=>∑' i,f i t) t (fun _=>1)); rw [iteratedFDeriv_tsum_apply he (fun k _=> hP k) (fun k i j _=> hV k i j) le_top]; have he:= ((hP k).of_norm_bounded (fun i=> hV k i t)).hasSum.mapL (ContinuousMultilinearMap.apply ℝ _ _ (fun _:Fin k=>(1:ℝ))); refine he.congr_fun (fun i=>?_); change _=iteratedFDeriv ℝ k (f i) t _; rw [hx];rfl
end YM.OPE.Flume.Script
