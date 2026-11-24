import YM.RG11Proof.Stress.Shine

/-! # Tensor/centering and grade candidate tests for Ward normalization -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.RG11.Stress
open scoped Topology ContDiff Classical BigOperators Matrix.Norms.Frobenius
open YM.RG11.Fields YM.RG11.Scale
open YM.RG11.Jets YM.RG11.Nodes PowerSeries
open Maxwell Labels Table Climb Work.A01 Next.UVStress UVNext.FreeStress Function Filter MeasureTheory Analysis Pert.Position
variable {G:Gauge}{F:Frames G}(B:Adapted F 4)

-- I first index direction, second translation/response component
abbrev Taps := Axis × Axis

-- real coefficients, physical E expansion

def disclose(x:Rect Taps B.toBasis.J ℝ): (freeTable F).Stress:=fun i j=> B.toBasis.put (x (i,j))

def candidate : Submodule ℝ (Rect Taps B.toBasis.J ℝ) where
 carrier:={x| disclose B x ∈ SymSpace (Free.spin_free F) ∧ ∀ (i:Taps) j, Fields.height B j ≠ 4 → x i j=0}
 zero_mem':= by
   refine ⟨?_,fun _ _ _=>rfl⟩
   rw [show disclose B 0=0 from funext fun i=>funext fun j=>B.toBasis.put_zero]
   exact Submodule.zero_mem _
 add_mem':=by
   rintro x y ⟨h,k⟩ ⟨w,t⟩; refine ⟨?_,fun i j he=>by simp [k i j he,t i j he]⟩
   have he : disclose B (x+y)= disclose B x+disclose B y:=by
     funext i j; simp only [disclose,Basis.put_sum,Matrix.add_apply,Pi.add_apply,Complex.ofReal_add,add_smul,Finset.sum_add_distrib]
   rw [he]; exact Submodule.add_mem _ h w
 smul_mem':=by
   rintro c x ⟨h,k⟩
   refine ⟨?_,fun i j he=>by simp [Matrix.smul_apply,k i j he]⟩
   have he : disclose B (c • x)= c • disclose B x:=by
     funext i j; simp only [disclose,Basis.put_sum,Matrix.smul_apply,Pi.smul_apply,smul_eq_mul,Complex.ofReal_mul,RCLike.real_smul_eq_coe_smul (K:=ℂ),Finset.smul_sum,smul_smul]
     rfl
   rw [he]; exact Submodule.smul_mem _ c h

private theorem mean_scale (j:B.toBasis.J)(h:Fields.height B j=4): expectation (freeTable F) 4 (B.b j) = 0:=by
   let v:Fin 1 → B.toBasis.J:=fun _=>j
   have he(u:ℝ): expectation (freeTable F) 4 (B.b j)=(Real.exp (4*u):ℂ)*expectation (freeTable F) 4 (B.b j):=by
      let p : Fin 0→(freeTable F).Tag:=blank _
      have hx : (0:Points 1)∈conf 1:=fun _ _ _=> Subsingleton.elim ..
      have hl:= free_rays B u hx v
      rw [smul_zero,Fin.sum_univ_one,show Fields.height B (v 0)=_ from h] at hl
      have hv : visible F 4 (r:=1) 0 (B.b ∘ v)=expectation (freeTable F) 4 (B.b j):=by
        change (freeTable F).useAt (freeTable F) (n:=1) 0 (fourWord F (B.b ∘ v)) = _; -- n binder?

        trans (freeTable F).useAt (freeTable F) (n:=1) 0 (Fin.cons ⟨4,B.b j⟩ p)
        · congr! 1; funext i; fin_cases i; rfl
        exact (front_eval ..).symm
      rw [hv] at hl
      simpa using hl
   have hz:= he 1
   have hi: (↑(Real.exp ((4:ℝ)*1)):ℂ)≠1:= mod_cast (Real.one_lt_exp_iff.mpr (show (0:ℝ)<4*1 by norm_num)).ne'
   apply (mul_eq_zero.mp (show (1-(↑(Real.exp ((4:ℝ)*1)):ℂ))*expectation (freeTable F) _ _=0 from by rw [sub_mul,one_mul, sub_eq_zero]; exact hz)).resolve_left (sub_ne_zero.mpr hi.symm)

 theorem admitted {x:Rect Taps B.toBasis.J ℝ}(h:x∈candidate B):disclose B x∈KernelSpace (Free.spin_free F):=by
   obtain ⟨h,w⟩:=h
   refine kernel_mem.mpr ⟨h,fun i j=>?_⟩
   unfold disclose; rw [Basis.put_sum,map_sum]
   apply Finset.sum_eq_zero; intro s _; rw [map_smul]
   by_cases ho:Fields.height B s = 4
   · rw [mean_scale B s ho,smul_zero]
   rw [w _ s ho,Complex.ofReal_zero,zero_smul]

-- horizontal under lawful operator frames through 4
 theorem reorient {x:Rect Taps B.toBasis.J ℝ}(h:x∈candidate B){z:Square B.toBasis.J ℝ}(hs:z∈B.toBasis.guard.vary)(hz:graded (Fields.height B) z):x*z∈candidate B:=by
   obtain ⟨h,w⟩:=h
   refine ⟨?_,fun i j he=> by
      rw [Matrix.mul_apply]; apply Finset.sum_eq_zero; intro b _; by_cases hb: Fields.height B b=4
      · rw [@hz b j (by rw [hb]; exact he.symm),mul_zero]
      rw [w i b hb,zero_mul]⟩
   let L:=B.toBasis.liftRows z
   let y:=disclose B x
   rw [show disclose B (x*z)=(fun i j=>L (y i j)) from ?eq]
   case eq=>
     funext i j; apply B.b.equivFun.injective; ext1 b
     rw [show disclose B _ _ _ = B.toBasis.put _ from rfl,
         show y _ _=B.toBasis.put _ from rfl,B.toBasis.coeff_put,B.toBasis.read_row]
     simp_rw [B.toBasis.coeff_put,Matrix.mul_apply,Complex.ofReal_sum, Complex.ofReal_mul]
   obtain ⟨h,hv,hK⟩:= sym_mem.mp h
   apply sym_mem.mpr
   refine ⟨fun i j=>congrArg L (h i j),fun i j=>?_, fun s i j=>?_⟩
   · -- simpler operates like below
     have ht := (B.toBasis.operates (⟨z,hs⟩)).property.2.2.1 (y i j)
     exact ht.trans (congrArg L (hv i j))
   have ht := Pert.Rigid.owner F (B.toBasis.operates (⟨z,hs⟩)) s (y i j)
   exact ht.trans (Eq.trans (congrArg L (hK s i j)) (by simp only [map_sum,map_smul]; rfl))

-- injective on all real columns of Taps
 theorem disclose_inj : Injective (disclose B):=fun _ _ h=>Matrix.ext fun i j=>by
    rcases i with ⟨a,b⟩; exact congrFun (B.toBasis.put_injective (congrFun (congrFun h a) b)) j

 theorem disclose_zero : disclose B 0=0:=funext fun _=> funext fun _=>B.toBasis.put_zero

end YM.RG11.Stress
