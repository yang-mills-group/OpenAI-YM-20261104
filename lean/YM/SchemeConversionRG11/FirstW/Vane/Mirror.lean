import YM.SchemeConversionRG11.FirstW.Vane.Tilt
/-! Covariances under signed-axis group; does not require the inversion-center placement convention itself to be rotation invariant. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW
open Function Filter Set Lattice Pert Align Topology Maxwell
open scoped BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {n : Side} {X : Type*} [AddCommGroup X] [One X]
lemma volturn (s : Signed) (x : Site n) : linGreen n (s.act x) = linGreen n x := by
  let f:= linGreen n; let g := f ∘ s.act
  have hl (w : Site n) (F : Site n→ℝ) : Orb.lap (F ∘ s.act) w = Orb.lap F (s.act w) := by
    unfold Orb.lap; conv_rhs=> rw [← Equiv.sum_comp s.perm (fun i:Axis=> _+_ - _)] -- metavars
    apply Finset.sum_congr rfl; intro i _; unfold Function.comp; simp only [s.act_add,s.act_sub]; rw [←Step.vec_pos i,← Step.vec_rotate]; cases he : s.flip i <;> simp [Step.vec,Step.rotate,posDir,he,add_comm,sub_eq_add_neg]
  have h : (g-f) x = (g-f) 0 := Orb.harmonic_const (g-f) (fun p=>by
    have he : s.act (R:=Per n) p = 0 ↔ p=0 := ⟨fun e=>by rw [←s.inv_act p,e, Signed.act_zero],fun e=> by rw [e, Signed.act_zero]⟩
    have hv (x) := Orb.lap_shift x (n:=n)
    have hp : Orb.lap (g-f) p = Orb.lap g p-Orb.lap f p := by unfold Orb.lap; rw [← Finset.sum_sub_distrib]; simp only [Pi.sub_apply]; apply Finset.sum_congr rfl; intro i _; abel
    have h0 : Orb.lap (g-f) p=0 := by rw [hp,show Orb.lap g p=_ from hl p f]; unfold f linGreen; rw [hv,hv]; simp only [he,sub_self]
    simpa only [Orb.lap,nsmul_eq_mul,Nat.cast_ofNat] using h0) x 0
  change _-_ = f (s.act (0:Site n))-f 0 at h; rw [Signed.act_zero,sub_self] at h
  exact sub_eq_zero.mp h
lemma spin_once (s t : Signed) (A : Wind G X) : Bare.wideLink G t (Bare.wideLink G s A)=Bare.wideLink G (s*t) A := by
  have he (r : ℝ) : pointU (Bare.wideLink G t (Bare.wideLink G s A)) r = pointU (Bare.wideLink G (s*t) A) r := by simp only [point_pull,pull_pull, affine,Signed.act_zero,add_zero]
  funext i
  apply G.colorMat_injective
  have hp : (fun r:ℝ=>G.mat (pointU (Bare.wideLink G t (Bare.wideLink G s A)) r i)) = _ := funext (fun r => congrArg (fun U:Links X G.El=>G.mat (U i)) (he r))
  exact HasDerivAt.unique (f:=fun r:ℝ=>G.mat (pointU (Bare.wideLink G t (Bare.wideLink G s A)) r i)) (Orb.line_diff _) ((hp.symm ▸ (show HasDerivAt (fun r:ℝ=>G.mat (pointU (Bare.wideLink G (s*t) A) r i)) _ 0 from Orb.line_diff _))) -- `f'`
@[simp] lemma wire_same (A : Wind G X) : Bare.wideLink G 1 A=A := by funext i; rw [Bare.wideLink_apply]; simp [Step.rotate,posDir,Step.used]
lemma tilt_row (s : Signed) (l) (u : G.Color) :
   (tbranch G n (pinch l u ∘ₗ Bare.wideLink G s)) = Bare.wideLink G s⁻¹ (tbranch G n (pinch l u)) := by
  have he : pinch l u ∘ₗ Bare.wideLink G s= Bare.parity s l • pinch (Bare.motionLink s l) u := by
    apply LinearMap.ext; intro A; simp only [LinearMap.comp_apply,Bare.wideLink_apply,pinch_eq,real_inner_smul_right,Bare.parity,LinearMap.smul_apply,smul_eq_mul,Bare.motionLink,affine,add_zero]
  -- pull equality through s⁻¹ after reading with s
  let L:=Bare.wideLink G (R:=Per n) s
  suffices H : L (tbranch G n (pinch l u ∘ₗ L)) = tbranch G n (pinch l u) by change tbranch G n (pinch l u ∘ₗ L) = _; rw [← H]; unfold L; rw [spin_once, mul_inv_cancel,wire_same]
  unfold L; rw [he, map_smul,branch_at,branch_at]
  funext e; rw [Bare.wideLink_apply]; rcases e with ⟨x,i⟩; rcases l with ⟨y,j⟩
  cases hv : s.flip i <;> cases ht : s.flip j <;> simp only [Pi.smul_apply, Bare.motionLink,Bare.parity, posDir,Step.rotate,Step.used,affine,add_zero,hv,ht] <;> simp [Orb.ghostLink] <;> split_ifs with hb
  all_goals first| rfl| subst i
  all_goals first| (rw [hv] at ht; contradiction) | (simp only [sub_sub_sub_cancel_right]; rw [← s.act_sub]; exact congrArg (fun t:ℝ=> t • u) (volturn (n:=n) s _))| (rw [← s.act_sub]; exact congrArg (fun t:ℝ=> t • u) (volturn (n:=n) s _))
end YM.RG11.FirstW
