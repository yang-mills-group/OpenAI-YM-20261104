import YM.OPE.Coverage.Theory

/-! Uniform temporal gaps for normalized difference lists by an array-level
rotation (using continuum O(4), not an assertion on single cutoff kernels). -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Coverage
open Function Filter Set Topology Metric Ortho
open scoped InnerProductSpace BigOperators Matrix Classical
variable {I : Type*}[Finite I]
private lemma dense_probe (p:E4)(ht:p≠0): Dense {y:E4|inner ℝ p y≠0}:=fun u=>by
    by_cases he: inner ℝ p u=0; swap; exact subset_closure he
    let v(n:ℕ):=u+(n+1:ℝ)⁻¹ • p
    have h:Tendsto v atTop (𝓝 u):=by
       simpa [v,one_div,zero_smul,add_zero] using tendsto_const_nhds.add ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).smul_const p)

    have hg (n:ℕ): inner ℝ p (v n)=(n+1:ℝ)⁻¹ * ‖p‖^2:=by simp [v,he,inner_add_right,real_inner_smul_right, real_inner_self_eq_norm_sq]
    exact mem_closure_of_tendsto h (Eventually.of_forall (fun i=>show inner ℝ p (v i)≠0 from (hg i).symm ▸ mul_ne_zero (by positivity) (pow_ne_zero 2 (norm_ne_zero_iff.mpr ht))))
private lemma exists_probe (x:I→E4)(hx:∀i,‖x i‖=1):∃ y:E4,∃ δ:ℝ, 0<δ ∧ ∀ i, δ < |inner ℝ (x i) y|:=by
   have hoff:Dense (⋂ i:I, {y:E4 | inner ℝ (x i) y≠0}):= dense_iInter_of_isOpen (fun i=>isOpen_ne_fun (by fun_prop) (by fun_prop)) (fun i=>dense_probe _ (fun he=>one_ne_zero ((hx i).symm.trans (he ▸ norm_zero))))
   obtain ⟨y,hy⟩:=hoff.nonempty
   have he: ∀ᶠ t:ℝ in 𝓝[>] (0:ℝ),∀ i, t < |inner ℝ (x i) y|:=eventually_all.mpr fun i=> (gt_mem_nhds (abs_pos.mpr (mem_iInter.mp hy i))).filter_mono nhdsWithin_le_nhds
   exact Exists.intro y ((he.and (show ∀ᶠ t:ℝ in 𝓝[>] (0:ℝ),0<t from self_mem_nhdsWithin)).exists |> (fun h=> let ⟨t,h',hv⟩:=h; ⟨t,hv,h'⟩))

private abbrev e:E4:=basis timeAxis
private lemma row_exists (u:E4)(hu:‖u‖=1):∃ R':Ortho,∀ x:E4,move R' x timeAxis= inner ℝ u x:=by
  let a:= timeAxis
  have coord (x:E4): inner ℝ e x=x a:=by simp [e,a,PiLp.inner_apply,basis_eq,apply_ite]
  by_cases h:u=e
  · exact ⟨1,fun x=> by rw [h,move_one,coord]⟩
  let v:=e-u
  let c :=2*(‖v‖^2)⁻¹
  let B:M4:=.of fun i j=> (c*v i)*v j
  let M:= (1:M4)-B
  have h₀:v≠0:= sub_ne_zero.mpr (Ne.symm (show u ≠ e from h))
  have hc : c*‖v‖^2=2:=by dsimp only [c]; rw [mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ (norm_ne_zero_iff.mpr h₀)),mul_one]
  have hMstar : Bᵀ=B:=by ext i j; change _ * v i = _ * v j;ring
  have hprod(i j:Axis): c*(e-u) i* ((c*‖v‖^2)*(e-u) j) = (c*‖v‖^2) * ((c*v i)*v j):=by dsimp only [v];ring
  have hBB: B * B= (2:ℝ) • B:=by
     ext i j; simp only [Matrix.mul_apply,Matrix.smul_apply,smul_eq_mul, B,Matrix.of_apply]
     simp_rw [show ∀ k:Axis, c * v i * v k * (c * v k * v j)=c * v k^2*B i j from by unfold B; simp only [Matrix.of_apply]; intro; ring, ← Finset.sum_mul, ← Finset.mul_sum]
     rw [show ∑ k:Axis, v k^2 = ‖v‖^2 from by simpa only [Real.norm_eq_abs,sq_abs] using (EuclideanSpace.real_norm_sq_eq v).symm,hc]; rfl
  have hM: M∈Matrix.unitaryGroup Axis ℝ:=by
     dsimp only [M];rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_sub,Matrix.transpose_one,hMstar,sub_mul,mul_sub,mul_sub,one_mul,mul_one,hBB]; simp [two_smul]
  refine ⟨⟨M,hM⟩,fun x=>?_⟩; change move _ x a=inner ℝ u x
  have hvt: v a = 1-u a:=by dsimp only [v]; simp [e,a,basis_eq]
  have he: ‖e‖=1:= by
     simp [e]
  have hvNorm : c*v a=1:=by
     rw [hvt]
     unfold v at hc
     have hh : inner ℝ u e=u a:= (real_inner_comm ..).trans (coord u)
     rw [← real_inner_self_eq_norm_sq, inner_sub_left,inner_sub_right,inner_sub_right,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,he,hu,hh,coord] at hc
     nlinarith only [hc,hu]
  have hBx:= show (∑ k:Axis, B a k*x k)=inner ℝ v x by
    simp only [B,Matrix.of_apply,mul_assoc,← Finset.mul_sum, ← mul_assoc, hvNorm,one_mul]
    simp [EuclideanSpace.inner_eq_star_dotProduct,dotProduct, RCLike.inner_apply,mul_comm]
  change M4.move M x a=_; rw [M4.at_coord]; simp only [M,Matrix.sub_apply,sub_mul,Finset.sum_sub_distrib]
  change M4.move 1 x a-(∑ k, B a k*x k)=_; rw [M4.move_one,hBx,show v=e-u from rfl,inner_sub_left,coord]; ring

/-- One uniform loss for all difference configurations; the axis may be
chosen *after* the configuration and then kept under replication. -/
theorem directions (I : Type*) [Finite I] : ∃ δ : ℝ, 0<δ ∧ ∀ x:I→E4, ∃ R':Ortho, ∀ i, δ*‖x i‖ ≤ |move R' (x i) timeAxis|:=by
   let K:= I→ sphere (0:E4) 1
   haveI : CompactSpace K:= by dsimp only [K];infer_instance
   choose v δ hδ h using fun (x:K)=> exists_probe (I:=I) (fun i=>(x i).val) (fun i => show ‖(x i).val‖=1 by simpa only [mem_sphere_iff_norm,sub_zero] using! (x i).property)
   let O(k:K):Set K:= {x:K| ∀ i, δ k < |inner ℝ ((x i).val) (v k)|}
   obtain ⟨t,ht⟩ := finite_cover_nhds (U:=O) (fun k=>by
      change ∀ᶠ y:K in 𝓝 k, ∀ i, δ k < |inner ℝ ((y i).val) (v k)|
      exact eventually_all.mpr fun i=> ((show Continuous (fun k':K => |inner ℝ ((k' i).val : E4) (v k)|) by fun_prop).continuousAt.eventually (lt_mem_nhds (h k i))))
   classical
   let j(i:K) := ‖v i‖⁻¹ • (v i)
   have hj(i:K)(l:I): ‖j i‖=1:= by
       have hh: v i ≠ 0:= fun e=> not_lt_of_ge (by simp [e]) ((hδ i).trans (h i l))
       exact norm_smul_inv_norm hh
   cases isEmpty_or_nonempty I
   · exact ⟨1,one_pos,fun _=> ⟨1,(isEmptyElim)⟩⟩ -- possibly
   obtain ⟨i₀⟩:= ‹Nonempty I›
   have hw' := (Eventually.exists (((show ∀ᶠ d in 𝓝[>] (0:ℝ), 0<d from self_mem_nhdsWithin)).and
      (eventually_all_finset t |>.mpr fun k hk=> (gt_mem_nhds (div_pos (hδ k) (by
        have he: v k ≠ 0:=fun e=> not_lt_of_ge (by simp [e]) ((hδ k).trans (h k i₀))
        exact norm_pos_iff.mpr he
      ))).filter_mono nhdsWithin_le_nhds)))
   obtain ⟨d,hd,hw⟩:=hw'
   refine ⟨d,hd,fun u=>?_⟩
   let x:K:= fun i=> if he0:u i=0 then ⟨e,by simp [e]⟩ else ⟨‖u i‖⁻¹ • u i,by
          have h:(RCLike.ofReal ‖u i‖ :ℝ)=‖u i‖:=rfl
          simpa only [mem_sphere_iff_norm,sub_zero,h] using norm_smul_inv_norm (𝕜:=ℝ) he0⟩
   obtain ⟨k,hk,hx⟩:= mem_iUnion₂.mp (ht ▸ mem_univ x)
   change x ∈ O k at hx
   obtain ⟨Q,hQ⟩:= row_exists (j k) (hj k i₀)
   refine ⟨Q,fun i=>?_⟩; by_cases he:u i=0
   · rw [he,norm_zero,mul_zero];exact abs_nonneg _
   have hE: u i=‖u i‖ • (‖u i‖⁻¹ • (u i)):= (smul_inv_smul₀ (norm_ne_zero_iff.mpr he) _).symm
   have hx:= hx i
   change δ k < |inner ℝ ((x i).val) (v k)| at hx
   have hv : |move Q (u i) timeAxis|=(|inner ℝ ((x i).val) (v k)|/ ‖v k‖) * ‖u i‖:=by
       rw [hQ]; dsimp only [j]; rw [real_inner_smul_left];nth_rw 1 [hE]
       dsimp only [x];rw [dif_neg he,real_inner_smul_right,abs_mul,abs_mul,abs_inv, abs_of_nonneg (norm_nonneg (v _)), abs_of_nonneg (norm_nonneg (u i)),real_inner_comm];ring
   rw [hv]; exact mul_le_mul_of_nonneg_right ((hw k hk).le.trans (div_le_div_of_nonneg_right hx.le (norm_nonneg _))) (norm_nonneg _)
end YM.OPE.Coverage
