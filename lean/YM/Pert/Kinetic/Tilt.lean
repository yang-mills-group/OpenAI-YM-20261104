import YM.Pert.Kinetic.Signed
noncomputable section
namespace YM.Pert.Kinetic
open Function Filter Set Lattice Wilson Exterior RG Precision
open Work.F03
open scoped Topology BigOperators Classical ContDiff
variable {n : Side} {G : Gauge} (c : G.Color) (i j : Axis) (s : Signed) (hn : 4≤n.val)
include hn
lemma turn_mode (x : Site n) (b : Bool) : mode j b (s.act x) =
    (if b && s.flip (s.perm.symm j) then (-1:ℝ) else 1) * mode (s.perm.symm j) b x := by
   conv_lhs => rw [←wrap_lift x, wrap_signed]
   rw [mode_wrap hn,mode_base b hn,←s.perm.apply_symm_apply j, Signed.act_at,_root_.Equiv.symm_apply_apply]
   cases he: s.flip (s.perm.symm j) <;> cases b <;> simp [trig,Real.cos_neg,Real.sin_neg]

omit hn in lemma send_idx (e : Edge (Site n)) : (sendEdge s (0:Site n) e).2=s.perm e.2 := by unfold sendEdge Step.used; split <;> rfl
lemma snd_mode (hij : i ≠ j) (b : Bool) (e : Edge (Site n)) (he : s.perm e.2=i) :
   mode j b (sendEdge s 0 e).1 = mode j b (affine s (0:Site n) e.1) := by
   have hx : j≠s.perm e.2 := fun hj=> hij (he.symm.trans hj.symm)
   unfold sendEdge Step.used; split <;> rename_i hk
   swap
   · exact rfl -- order?
   simp only
   rw [sub_eq_add_neg,add_comm, ←wrap_step (n:=n), ←map_neg, mode_add b hn, mode_base b hn]
   rw [Pi.neg_apply,step_apply, show ((posDir e.2).rotate s).dir=s.perm e.2 from rfl,if_neg (hx : j ≠ ((posDir e.2).rotate s).dir)]; simp
lemma waves_turn (hij : i ≠ j) : ∃ c' : Bool→G.Color, (∀ b, ‖c' b‖=‖c‖) ∧ ∀ b,
    AnalyticBridge.VerifiedReset.pullDir (G:=G) s (0:Site n) (wave c b i j) = wave (c' b) b (s.perm.symm i) (s.perm.symm j) := by
   let ζ := fun b:Bool => (s.perm.symm i); refine ⟨fun b=> (StressFlux.sign s (s.perm.symm i) * (if b && s.flip (s.perm.symm j) then (-1:ℝ) else 1)) • c, fun b=>by rw [norm_smul,Real.norm_eq_abs]; unfold StressFlux.sign; split_ifs <;> norm_num, ?_⟩
   intro b; ext1 e
   change StressFlux.sign s e.2 • (wave c b i j (sendEdge s 0 e)) = _
   unfold wave; rw [send_idx]
   by_cases h : s.perm e.2=i
   · have ht : e.2=s.perm.symm i := (s.perm.symm_apply_apply e.2).symm.trans (congrArg _ h)
     rw [if_pos h, if_pos ht, snd_mode i j s hn hij b e h, affine, add_zero,turn_mode j s hn, ht,smul_smul,smul_smul,mul_comm,mul_assoc]; congr 1; ring
   rw [if_neg h,if_neg (show e.2 ≠ s.perm.symm i from fun he=> h (by rw [he,s.perm.apply_symm_apply]))]; simp

lemma converts_dir (v : Directions G n) : lift1 (AnalyticBridge.VerifiedReset.pullDir (G:=G) s 0 v) = Bid.pulled (lift1 v) s := by
   ext1 e; rcases e with ⟨x,i⟩
   simp only [AnalyticBridge.VerifiedReset.pullDir,Bid.pulled,lift1,sendEdge,StressFlux.sign];
   have he (x : Edge (Site n)) : v (x.1,axisEquiv.symm (coord x.2)) = v x := by exact congrArg (fun j=>v (x.1,j)) (axisEquiv.left_inv x.2)
   rw [he]
   dsimp only [StressFlux.sign,Step.rotate, posDir]
   simp only [ContinuousLinearMap.pi_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.proj_apply]
   have hh (u:Bool) : (false ^^ u)=u := by cases u <;> decide
   have e1 := show ((posDir (axisEquiv.symm i)).rotate s).neg=s.flip (axisEquiv.symm i) from hh _ -- invalid notation
   simp only [e1,hh,ite_smul,neg_one_smul,one_smul]
end YM.Pert.Kinetic
