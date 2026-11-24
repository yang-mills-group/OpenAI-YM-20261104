import YM.Pert.Kinetic.Character
import YM.Pert.Kinetic.Wave
import YM.Work.F03.Flat
/-! The linear curvature of the two tested modes. -/
noncomputable section
namespace YM.Pert.Kinetic
open Function Filter Set Lattice Wilson RG AnalyticBridge.VerifiedReset Exterior
open Work.F03
open scoped Topology BigOperators Classical ContDiff
variable {n : Side} {G : Gauge} (c : G.Color) (hc : ‖c‖=1) (b : Bool) (hn : 4 ≤ n.val)

def lift1 (v : Directions G n) : fieldDir G n 1 := fun e=>v (e.1,axisEquiv.symm e.2)
@[simp] lemma back_wave (v : Directions G n) : collect G (lift1 v)=v :=
   funext fun i=> congrArg (fun j => v (i.1,j)) (axisEquiv.left_inv i.2)

def wedge (i j : Axis) (d : PlaqAxes) : ℝ := (if d.1.1=j ∧ d.1.2=i then 1 else 0) - (if d.1.2=j ∧ d.1.1=i then 1 else 0)
def bump (b : Bool) (j : Axis) (x : Site n) := trig b (Full.mesh n * (lift x j:ℝ)+Full.mesh n) - trig b (Full.mesh n * (lift x j:ℝ))
include hc hn
omit hc in lemma mode_heard (x : Site n) (j k : Axis) : mode j b (x+step k) = trig b (Full.mesh n*(lift x j:ℝ)+(if j=k then Full.mesh n else 0)) := by
    conv_lhs => rw [add_comm,← wrap_step n k]
    rw [mode_add b hn,step_apply]
    split_ifs <;> simp_all
set_option maxRecDepth 10000 in
lemma curl_wave (x : Face (Per n)) (i j : Axis) :
   faceCurl x (lift1 (wave c b i j)) = (wedge i j x.2 * bump b j x.1) • c := by
    rcases x with ⟨x,d⟩
    unfold faceCurl; rw [← Exterior.fundamental,Square.cochain_square,back_wave]
    unfold wave wedge bump
    dsimp only
    rw [mode_heard,mode_heard,mode_base b hn]
    all_goals try exact hn
    all_goals try exact hc
    rw [←sub_smul,←sub_smul,←sub_smul]; congr 1
    by_cases hi : d.val.1=i <;> by_cases hi' : d.val.2=i <;>
      by_cases hj : d.val.1=j <;> by_cases hj' : d.val.2=j
    all_goals try have hk := d.property
    all_goals try exact False.elim (hk.ne (hi.trans hi'.symm))
    all_goals try exact False.elim (hk.ne (hj.trans hj'.symm))
    all_goals try simp only [if_pos hi]
    all_goals try simp only [if_neg hi]
    all_goals try simp only [if_pos hi']
    all_goals try simp only [if_neg hi']
    all_goals try simp only [if_pos (Eq.symm hj)]
    all_goals try simp only [if_neg (Ne.symm hj)]
    all_goals try simp only [if_pos (Eq.symm hj')]
    all_goals try simp only [if_neg (Ne.symm hj')]
    all_goals try simp only [if_pos (And.intro hj hi')]
    all_goals try simp only [if_pos (And.intro hj' hi)]
    all_goals try simp only [if_neg (not_and_of_not_left _ hj'),if_neg (not_and_of_not_right _ hi')]
    all_goals try simp only [if_neg (not_and_of_not_left _ hj)]
    all_goals try simp only [if_neg (not_and_of_not_left _ hj')]
    all_goals try simp only [if_neg (not_and_of_not_right _ hi')]
    all_goals try simp only [if_neg (not_and_of_not_right _ hi)]
    all_goals simp only [add_zero,sub_self,sub_zero, zero_sub,neg_mul,one_mul,zero_mul]


omit hc hn in lemma wedge_norm (i j : Axis) (x : PlaqAxes) : |wedge i j x| ≤ 1 := by unfold wedge;split_ifs <;> norm_num
lemma curl_le (x : Face (Per n)) (i j : Axis) : ‖faceCurl x (lift1 (wave c b i j))‖ ≤ Full.mesh n := by
   rw [curl_wave c hc b hn, norm_smul,hc,mul_one,Real.norm_eq_abs,abs_mul]
   refine (mul_le_mul (wedge_norm ..) ?_ (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
   apply le_trans (trig_lip b ..); rw [add_sub_cancel_left,abs_of_pos Full.mesh_pos]

omit hc hn in lemma second_lip (a t u : ℝ) : |(trig b (a+t+u) - trig b (a+t)) - (trig b (a+u) - trig b a)| ≤ |t| * |u| := by
    let f k := trig b (a+k*t+u) - trig b (a+k*t)
    have he(k:ℝ) := ((hasDerivAt_id' k).mul_const t).const_add a
    let D k:= t*(deriv (trig b) (a+k*t+u) - deriv (trig b) (a+k*t))
    have h(k:ℝ): HasDerivAt f (D k) k := by
       apply (((deriv_trig_diff b _).hasDerivAt.comp k ((he k).add_const u)).sub ((deriv_trig_diff b _).hasDerivAt.comp k (he k))).congr_deriv ?_
       dsimp only [D]; ring
    have hx(k:ℝ): ‖D k‖ ≤ |t| * |u| := by
       simp only [D,norm_mul,Real.norm_eq_abs]
       refine mul_le_mul_of_nonneg_left (deriv_trig_lip b .. |>.trans ?_) (abs_nonneg _); rw [add_sub_cancel_left]
    simpa [f,Real.norm_eq_abs] using (norm_image_sub_le_of_norm_deriv_le_segment_01' (fun x _ => (h x).hasDerivWithinAt) (fun x _=> hx x))
omit hc in lemma bump_diff (a : Cover) (x : Site n) (j : Axis) : |bump b j (wrap n a+x) - bump b j x| ≤ |(a j:ℝ)| * (Full.mesh n)^2 := by
    have e (y:Site n) : bump b j y = mode j b (y+step j)-mode j b y := by simp only [mode_heard b hn,mode_base b hn, ↓reduceIte,bump]
    rw [e,e,← show wrap n (a+(step j:Cover))+x=(wrap n a+x)+step j by rw [map_add,wrap_step,add_right_comm], add_comm x (step j), ←wrap_step n j,mode_add b hn,mode_add b hn,mode_add b hn,mode_base b hn]
    simp only [Pi.add_apply, step_apply,↓reduceIte,Int.cast_add,Int.cast_one,mul_add,mul_one,←add_assoc]
    apply (second_lip b ..).trans; rw [abs_mul,abs_of_pos Full.mesh_pos, sq]; ring_nf; exact le_rfl
lemma curl_step (x : Site n) (s : Slot) (i j : Axis) :
    ‖faceCurl (slotFace s x) (lift1 (wave c b i j)) - faceCurl (x,s.plaq) (lift1 (wave c b i j))‖ ≤ (s.length:ℝ)*(Full.mesh n)^2 := by
    rw [slotFace,curl_wave c hc b hn,curl_wave c hc b hn, ←sub_smul,←mul_sub,norm_smul,hc,mul_one,Real.norm_eq_abs,abs_mul]
    refine (mul_le_mul (wedge_norm ..) (bump_diff b hn s.offset x j) (abs_nonneg _) zero_le_one).trans ?_
    rw [one_mul]; apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have he := Extra.Iteration.Derivs.stencil_length s s.offset (show s.offset ∈ s.stencil by unfold Slot.stencil; exact Finset.mem_union_right _ (List.mem_toFinset.mpr (by simp [square,visits])))
    exact_mod_cast (by
       have H := (Finset.single_le_sum (f:=fun i=>(s.offset i).natAbs) (fun i _=>Nat.zero_le _) (Finset.mem_univ j) |>.trans he)
       rwa [←Int.natCast_natAbs,Int.ofNat_le] : |s.offset j| ≤ (s.length : ℤ))
end YM.Pert.Kinetic
