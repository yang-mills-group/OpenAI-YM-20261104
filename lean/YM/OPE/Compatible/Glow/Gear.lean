import YM.OPE.Compatible.Glow.Hewn
/-! # Fixed rank opacity passage. fees via scalar Leg Chair no giant halo. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson
open scoped Topology BigOperators Classical
variable {I J W E X:Type*}{i j n r d m:ℕ}
namespace Script
open Page
-- bound one v-plane from unit pol on K⊆r dimension. Need multi-vector norm regardless dimension. Via compact sphere pull linear. 
private abbrev G(n:ℕ):=Fin n→ ℝ
def steel (n:ℕ):Submodule ℝ (Tensor.T (G n) ℝ n) where
   carrier:= setOf Tensor.Sym
   zero_mem':=fun _ _=>rfl
   add_mem':=fun {x y} (hx:Tensor.Sym x) (hy:Tensor.Sym y) a b=> by simp only [_root_.add_apply,hx a b,hy a b]
   smul_mem':=fun x y (hx:Tensor.Sym y) a b=>by simp only [_root_.smul_apply,hx a b]
-- Op T ℝ
private lemma polarized (n:ℕ) :∃ C:ℝ,0≤C∧∀ (A:Tensor.T (G n) ℝ n) (t:ℝ),Tensor.Sym A → 0≤t → (∀ v:G n, ‖v‖≤(1:ℝ)→‖Tensor.diagonal A v‖≤t)→‖A‖≤C*t:=by
    -- finite evaluations spanning or compact C. simpler representative quotient via linear span Hahn
    let Z:= steel n; let k:= Metric.closedBall (0:G n) 1; letI : CompactSpace k:= isCompact_iff_compactSpace.mp (ProperSpace.isCompact_closedBall 0 1)
    let Y(T: Z)(v:k):= Tensor.diagonal T.val v.val; let X: Z →ₗ[ℝ] ContinuousMap k ℝ := {
       toFun t:=⟨Y t, (Tensor.diag_smooth t.val ⊤).continuous.comp continuous_subtype_val⟩
       map_add' :=fun x y=> ContinuousMap.ext fun i=>rfl
       map_smul' :=fun a x=> ContinuousMap.ext fun i=>rfl
    }
    have H(t:Z)(h:X t=0): t=0:=by
       have hh(g:k):Y t g=0:= DFunLike.congr_fun h g
       apply Subtype.ext; apply Tensor.ext_diag t.val 0 t.property (fun _ _=>rfl); ext1 x
       let a:= (‖x‖+1)⁻¹; have hx: 0<a:=by unfold a;positivity
       apply smul_right_injective ℝ (pow_pos hx n).ne'
       change a^n • Tensor.diagonal _ _ = _; rw [← Tensor.homogeneous]; have ht:a • x∈k:=by
         rw [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_of_nonneg hx.le]; have he:0<‖x‖+1:=by positivity
         exact (mul_le_mul_of_nonneg_left (show ‖x‖≤ ‖x‖+1 by linarith) hx.le).trans_eq (inv_mul_cancel₀ he.ne')
       exact (hh ⟨_,ht⟩).trans (smul_zero _).symm
    let g:=LinearEquiv.ofInjective X (LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr H)); let h:X.range→L[ℝ] Z:=by
        letI:FiniteDimensional ℝ X.range:=Module.Finite.of_basis (Module.finBasis ℝ Z |>.map g)
        exact LinearMap.toContinuousLinearMap g.symm.toLinearMap
    have he(t:Z): h (g t)=t:=g.symm_apply_apply _
    obtain ⟨C,hC,Hc⟩:= ContinuousLinearMap.bound (𝕜:=ℝ) (𝕜₂:=ℝ) (E:=X.range) (F:=Z) (σ₁₂:=RingHom.id ℝ) h; refine ⟨C,hC.le,fun A y hA hy hY=>?_⟩; let t:Z:=⟨A,hA⟩; change ‖t‖≤_; rw [← he t]; apply (Hc _).trans; exact mul_le_mul_of_nonneg_left (ContinuousMap.norm_le _ hy|>.mpr fun i=> hY i.val (by obtain hx:= i.property; rw [Metric.mem_closedBall, dist_zero_right] at hx; exact hx)) hC.le
lemma limelight (n:ℕ) :∃ C K:ℝ,0≤ C ∧ 0≤ K∧∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E] (A:Tensor.T E ℝ n) (t:ℝ), Tensor.Sym A→0≤ t→(∀ v:E,‖v‖≤ K→‖Tensor.diagonal A v‖≤t)→∀ x:Fin n→E,(∀ i,‖x i‖≤1)→‖A x‖≤C*t:=by
    obtain ⟨C,hC,H⟩:= polarized n; refine ⟨C,n,hC,Nat.cast_nonneg _,fun E _ _ A t ha ht h x hp=>?_⟩; let f : G n →L[ℝ] E:=∑ i: Fin n, (ContinuousLinearMap.proj i).smulRight (x i); let U:= A.compContinuousLinearMap (fun _=> f)
    let e(i:Fin n): G n:= Pi.single i 1; have he(i): f (e i)=x i:=by unfold f e; rw [_root_.sum_apply,Finset.sum_eq_single i]; simp; exact (fun j _ hj=>by simp [hj]); simp
    have hf(v:G n)(hv:‖v‖≤1):‖f v‖≤(n:ℝ):=by
        unfold f; rw [_root_.sum_apply]; apply (norm_sum_le ..).trans; apply (sum_le_sum (fun i _=> show ‖(ContinuousLinearMap.proj i|>.smulRight (x i)) v‖≤1 by change ‖v i • x i‖ ≤ _; rw [norm_smul]; apply mul_le_one₀ ((norm_le_pi_norm v i).trans hv) (norm_nonneg _) (hp i))).trans_eq; simp
    have hu:= H U t (fun x s=>ha (fun i=> f (x i)) s) ht fun v hv=> h (f v) (hf v hv)
    rw [show A x=U e from congr_arg A (funext fun i=> (he i).symm)]; apply (ContinuousMultilinearMap.le_opNorm ..).trans; apply (mul_le_of_le_one_right (norm_nonneg _) _).trans hu; apply Finset.prod_le_one (fun _ _=>norm_nonneg _); intro i _; apply (pi_norm_le_iff_of_nonneg (zero_le_one)).mpr; intro j; by_cases H:j=i<;>simp [e,H]
end Script
end YM.OPE.Flume
