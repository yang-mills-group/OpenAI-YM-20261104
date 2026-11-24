import YM.RG17.Weave

/-!
 Support toll for exact `packMark`. Root/group address pays integral
 shaped Test INCLUDING translation of test center. Otherwise sup with
 Jacobian r^(-4(n+1)) loses all precision. Counts all fine tuples in
 torus max-distance, not Euclidean norm of unlifted sum. No dropping
 configurations near torus seam or ties. These are smooth *Test value*
 weights, not derivative estimates on transported/polymer coefficients.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Extraction Spec Set Function Filter MeasureTheory Lattice
open scoped Topology BigOperators Classical
variable {G:Gauge} {C:Family G}{S:Table C.book}{f:Extraction.Order}(F:Final C f S){n:ℕ}
    (T:Test 1)(K:Set (Points (n+1)))

lemma shapeBound (hp:IsCompact K) :∃ A:ℝ,0 ≤ A∧ ∀ r:ℝ,0<r → ∀ (ψ: Test (n+1)), tsupport ψ⊆ K → ∀ b,Demand 0 ψ b →
     ∀ x:Points (n+1), r^(4*n)*‖shape (cashier F T) r ψ x‖ ≤ A*b:=by
    let V:= {x:E4 | ∃ y∈K, -y 0=x}
    have hV:V=(fun y: Points (n+1)=> -y 0) '' K:= rfl
    have hK:IsCompact V:= hV.symm ▸ (hp.image (by fun_prop : Continuous fun y : Points (n+1)=> -y 0))
    obtain ⟨c,hc⟩:= demandAccessible 0 T; have h0:= hc.nonneg
    let A:= volume.real V
    have hu:0 ≤ A:=ENNReal.toReal_nonneg
    refine ⟨A*c,mul_nonneg hu h0,fun r hr ψ hψ b hb x=>?_⟩
    have hb':=hb.nonneg
    by_cases he:r≠0 ∧ packs (cashier F T) r ψ; swap
    · unfold shape; rw [dif_neg he]; change _* ‖(0:ℂ)‖ ≤ _; rw [norm_zero,mul_zero]; positivity
    rw [shaped _ he.1 he.2,absolute]; let X:= cashier F T
    let z:= (pad (n:=n+1) (k:=0)).symm x
    let a:= z.1.ofLp 0
    let p(y:E4) := r⁻¹ • (z.1-echo (n+1) (y+a))
    let q(y:E4) :ℂ:= X.test (openRoot (y,z.2))*ψ (r⁻¹ • (z.1-echo (n+1) y)); let w(y:E4):=q (y+a)
    have ht:= Measure.integral_comp_smul_of_nonneg volume w r (hR:=hr.le); rw [show Module.finrank ℝ E4=4 from by simp [E4,Axis],Complex.real_smul] at ht
    have hx:∀ v∈Vᶜ, w (r•v)=0:=by
         intro v hv; have hi:p (r•v) ∉ tsupport ψ:=by
              intro hy; apply hv
              refine ⟨_,hψ hy,?_⟩; have h' : z.1.ofLp 0 - (r • v + a)= -(r • v):= by change a- _=_; abel
              simp [p,echo_at,h',hr.ne']
         exact mul_eq_zero_of_right _ (image_eq_zero_of_notMem_tsupport hi)
    have h : ‖∫ y:E4,w (r•y)‖≤A*c*b:=by
         rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hx]
         refine le_trans (norm_setIntegral_le_of_norm_le_const (hK.measure_lt_top) (fun v _=> show ‖w (r•v)‖ ≤ c*b from ?_ )) (le_of_eq ?_)
         · have hv(x):‖ψ x‖≤b:=by simpa only [norm_iteratedFDeriv_zero] using hb.smooth 0 (by omega) x
           have hl(x):‖T x‖ ≤ c:=by simpa only [norm_iteratedFDeriv_zero] using hc.smooth 0 (by omega) x
           unfold w q; rw [norm_mul]; exact mul_le_mul (hl _) (hv _) (norm_nonneg _) h0
         unfold A; ring
    change r^(4*n)*‖_* ∫ u:E4, q u‖ ≤ _
    rw [ht,norm_mul] at h; change ‖_‖ * ‖∫ y:E4,q (y+a)‖ ≤ _ at h
    rw [integral_add_right_eq_self] at h; rw [norm_mul,norm_pow,norm_inv,Complex.norm_real,Real.norm_of_nonneg hr.le,← mul_assoc]; refine le_trans (le_of_eq ?_) h
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity),inv_pow,Nat.mul_add,pow_add,mul_inv]; field_simp; ring

lemma addressCosts (hp:IsCompact K)(hz:K ⊆ conf _):∃ A B:ℝ, 0≤A ∧ 0 ≤ B ∧
    ∀ᶠ r in home,∀ (ψ:Test (n+1)),tsupport ψ ⊆ K→ ∀ (i:ℕ)(c:ℝ),Demand i ψ c → ∀ (b N p:ℕ)(h:b ≤ N), C.S.a N ≤ r →
        C.S.a b ^4 * (spools C F T K b N p h r).card ≤ A ∧
           ∀ z,C.S.a N^(4*(n+1)) *(∑ u∈yarns C F T K b N p h z r, ‖shape (cashier F T) r ψ (Order.cells C N p u)‖) ≤ B*C.S.a b^4 * c:=by
   obtain ⟨A,B,t,u,v,hA,hB,_,_,_,he⟩:=countableBill C F T K hp hz; obtain ⟨d,hd,hY⟩:=shapeBound F T K hp
   refine ⟨A,B*d,hA,mul_nonneg hB hd,?_⟩
   filter_upwards [he,positiveLength] with r hr hR ψ hψ i c hc b N p h hk
   obtain ⟨hp,hz⟩:= hr b N p h hk
   refine ⟨hp,fun z=>?_⟩; let U:= yarns C F T K b N p h z r; let k:= C.S.a N; have ha:=C.S.a_pos N; have hh:= hc.nonneg
   have ht:(∑ y ∈ U, ‖shape (cashier F T) r ψ (Order.cells C N p y)‖) ≤ ∑ _y ∈ U,d*c/r^(4*n):= Finset.sum_le_sum fun y _=> (le_div_iff₀ (pow_pos hR _)).mpr ((mul_comm ..).trans_le (hY _ hR _ hψ _ (hc.fewer (Nat.zero_le _)) _))
   refine le_trans (mul_le_mul_of_nonneg_left ht (pow_nonneg ha.le _)) ?_; rw [Finset.sum_const,nsmul_eq_mul,← mul_assoc]
   refine le_trans (mul_le_mul_of_nonneg_right (hz z).1 (by positivity)) (le_of_eq ?_); field_simp
end YM.RG17
