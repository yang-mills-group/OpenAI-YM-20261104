import YM.Next.MAXWELL.Jets
import YM.FormalBulk08.Dawn.Lido

/-! `Studio` Taylor expenses without measure topology. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Dawn
open Filter Function Set Lattice Metric
open scoped BigOperators Topology ContDiff Classical
variable {D j n:ℕ}

lemma linear_price (T : E4→L[ℝ]ℝ)(C:ℝ)(h:0≤C)(he:∀ i, ‖T (basis i)‖ ≤ C) : ‖T‖ ≤ 4*C := by
   refine T.opNorm_le_bound (by positivity) fun v=>?_
   have hv : ∑ i : Axis, v i • basis i = v := by ext; simp
   conv_lhs=> rw [←hv,map_sum]
   refine (norm_sum_le ..).trans ((Finset.sum_le_sum (g:=fun _=>‖v‖*C) ?_).trans_eq ?_)
   · intro i _; rw [map_smul,norm_smul,Real.norm_eq_abs]; have h : |v i|≤‖v‖ := by simpa only [EuclideanSpace.basisFun_inner,OrthonormalBasis.norm_eq_one,one_mul] using abs_real_inner_le_norm (EuclideanSpace.basisFun Axis ℝ i) v
     exact mul_le_mul h (he i) (norm_nonneg _) (norm_nonneg _)
   simp [Axis];ring
lemma lifted (p : Studio D) (C:ℝ)(hc:0≤C)(b: Brush D)(hb:b.1.val <D)
    (h : ∀ k : Brush D,k.1.val=b.1.val+1 →∀ x,‖p.val k x‖≤ C)(hn:p.val b origin=0) (x:Pier):
    ‖p.val b x‖ ≤ 32*C := by
   obtain ⟨f,rfl⟩:=portrayed D p
   let F:= f.val;let K:=halo f b
   have hf:ContDiff ℝ D F:=f.property
   have hh: Differentiable ℝ K:= fun y=> (((ContinuousMultilinearMap.apply ℝ (fun _=>E4) ℝ (basis ∘ b.2)).differentiableAt).comp y (hf.contDiffAt.differentiableAt_iteratedFDeriv (Nat.cast_lt.mpr hb)))
   let U:=closedBall (0:E4) 8
   have he (y)(hy:y∈U): ‖fderiv ℝ K y‖≤4*C:= by
      apply linear_price _ C hc; intro i
      let W : Fin (b.1.val+1) → Axis:=Fin.cons i b.2
      have hv : Fin.cons (basis i) (basis ∘ b.2) =basis ∘ W:= by ext k; cases k using Fin.cases <;> simp [W]
      let c:Brush D := ⟨⟨b.1.val+1,by omega⟩, W⟩
      have ht := Analysis.cons_jet (show ContDiffAt ℝ (↑(b.1.val+1:ℕ)) F y from (tends f c.1).contDiffAt) (basis i) (basis ∘ b.2)
      rw [hv] at ht
      exact (congr_arg (‖·‖) ht.symm).le.trans (h c rfl ⟨y,hy⟩)
   have Hq := (convex_closedBall (0:E4) 8).norm_image_sub_le_of_norm_fderiv_le (fun x _=> hh x) he (x:=0) (origin.property) (y:=x.val) x.property
   rw [show K 0=0 from hn, sub_zero,sub_zero] at Hq;exact Hq.trans (by nlinarith [still x])
lemma fog (f : Studio D) (q : ℕ)(C : ℝ)(hp:q≤D)(hc:0≤C)(he:∀ k:Brush D,q≤k.1.val → ∀ v,‖f.val k v‖≤C)
     (h : ∀ k:Brush D,k.1.val<q→ f.val k origin=0): ‖f‖ ≤ 32^q*C := by
   induction q generalizing C with
   | zero=> simpa only [pow_zero,one_mul] using panel_le f hc fun k=> he k (Nat.zero_le _)
   | succ q ih=>
     have ht : ∀ k:Brush D,q≤k.1.val → ∀ v, ‖f.val k v‖≤32*C := fun k hk v=> by
        by_cases hx : k.1.val=q
        · exact lifted f C hc k (by omega) (fun j hj=>he j (by omega)) (h k (by omega)) v
        exact (he k (by omega) v).trans (by linarith)
     rw [pow_succ,mul_assoc]; exact ih _ (by omega) (by positivity) ht (fun k l=> h k (by omega))

lemma diag_free (A:Tensor.T E4 ℝ j) (hA:Tensor.Sym A) (h:j<n) (x:E4) : iteratedFDeriv ℝ n (Tensor.diagonal A) x=0:= by
    ext v; induction j generalizing n with
    | zero=> rw [show Tensor.diagonal A=fun _=>Tensor.diagonal A 0 from funext fun _=>congr_arg A (Subsingleton.elim ..),iteratedFDeriv_const_of_ne (Nat.ne_of_gt h)];rfl
    | succ j ih=>
      cases n with
      | zero=> omega
      | succ n=>
        rw [← Fin.cons_self_tail v, Analysis.cons_inner (Tensor.diag_smooth A _ |>.contDiffAt)]
        let B := A.curryLeft (v 0)
        have he: Analysis.D (v 0) (Tensor.diagonal A)= (((j+1:ℕ):ℝ)) • Tensor.diagonal B := (funext fun x=> by rw [Analysis.D,Tensor.differential_diagonal _ hA]; rw [Pi.smul_apply,Nat.cast_smul_eq_nsmul]; rfl)
        rw [he,iteratedFDeriv_const_smul_apply ((Tensor.diag_smooth B _).contDiffAt)]
        simp only [_root_.smul_apply,ih (A:=B) (hA:=Tensor.freeze_sym _ hA _) (h:= Nat.lt_of_succ_lt_succ h)]
        simp
end YM.FormalBulk08.Dawn
