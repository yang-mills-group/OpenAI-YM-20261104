import YM.Pert.Kinetic.Character
import Mathlib.Analysis.Calculus.MeanValue
noncomputable section
set_option autoImplicit false
namespace YM.Pert.Kinetic
open Function Filter Set Lattice Wilson RG AnalyticBridge.VerifiedReset
open scoped Topology BigOperators Classical ContDiff
variable {n : Side} {G : Gauge} (c : G.Color) (hc : ‖c‖=1) (b : Bool) {i j : Axis}

def beyond (hn : 4 ≤ n.val) : ℝ := Full.mesh n -- proof-independent width notation? unused.
def wave (i j : Axis) : Directions G n := fun e => (if e.2=i then mode j b e.1 else (0:ℝ)) • c
lemma mode_add (hn : 4 ≤ n.val) (d : Axis) (u : Cover) (x : Site n) : mode d b (wrap n u + x) =
    trig b (Full.mesh n * (lift x d : ℝ) + Full.mesh n * (u d:ℝ)) := by
   conv_lhs => rw [show wrap n u+x=wrap n (u+lift x) by rw [map_add,wrap_lift]]
   rw [mode_wrap hn]; congr 1; simp [mul_add,add_comm]
lemma mode_base (hn : 4 ≤ n.val) (j : Axis) (x : Site n) : mode j b x = trig b (Full.mesh n * (lift x j:ℝ)) := by rw [← zero_add x, ← map_zero (wrap n),mode_add b hn]; simp
lemma bound_trig (x : ℝ) : |trig b x| ≤ 1 := by cases b; exact Real.abs_cos_le_one x; exact Real.abs_sin_le_one x
lemma deriv_trig_bound (x : ℝ) : |deriv (trig b) x| ≤ 1 := by
   cases b
   · simpa only [trig,Bool.false_eq_true,↓reduceIte, Real.deriv_cos,abs_neg] using Real.abs_sin_le_one x
   simpa only [trig,Bool.false_eq_true,↓reduceIte, Real.deriv_sin] using Real.abs_cos_le_one x

include hc
lemma wave_bound (hn : 4 ≤ n.val) (e : Edge (Site n)) : ‖wave c b i j e‖ ≤ 1 := by
   rw [wave,norm_smul,hc]; split_ifs
   · rw [Real.norm_eq_abs,mode_base b hn]; simpa using bound_trig b _
   simp

-- Taylor at center for Hessian E annihilating affine fields.
def jet (i j : Axis) (o : Site n) : LinearJet G where
   at0 k := if k=i then trig b (Full.mesh n * (lift o j:ℝ)) • c else 0
   slope k l := if k=i ∧ l=j then (Full.mesh n * (deriv (trig b) (Full.mesh n*(lift o j:ℝ)))) • c else 0

def delta (j : Axis) (o e : Site n) := Full.mesh n * (lift (e-o) j : ℝ)
omit hc in
lemma wave_add' (hn : 4 ≤ n.val) (e : Edge (Site n)) (o : Site n) : wave c b i j e =
    if e.2=i then trig b (Full.mesh n*(lift o j:ℝ) + delta j o e.1) • c else 0 := by
   unfold wave
   split_ifs
   · congr 1; convert mode_add b hn j (lift (e.1-o)) o using 2; simp; rfl
   exact zero_smul ..
omit hc in
lemma at_wave (e : Edge (Site n)) (o : Site n) : (jet c b i j o).field o e =
    if e.2=i then (trig b (Full.mesh n*(lift o j:ℝ)) + delta j o e.1 * deriv (trig b) (Full.mesh n*(lift o j:ℝ))) • c else 0 := by
   unfold LinearJet.field jet; dsimp only
   split_ifs with hi
   · simp only [hi,true_and,ite_smul]; rw [Finset.sum_eq_single j] <;> simp_all [smul_smul,add_smul, delta,mul_assoc,coord, mul_left_comm]
   simp [hi]
omit hc in lemma delta_le (o x : Site n) : |delta j o x| ≤ Full.mesh n * (separation x o : ℝ) := by
   have ha:= small_coord o x j
   unfold delta; rw [abs_mul,abs_of_pos Full.mesh_pos]; exact mul_le_mul_of_nonneg_left ha Full.mesh_pos.le

omit hc in lemma taylor_bound (a k : ℝ) : |trig b (a+k) - (trig b a + k*deriv (trig b) a)| ≤ k^2 := by
   let f (u:ℝ) := trig b (a+u*k) - (trig b a + (u*k)*deriv (trig b) a)
   have h (u:ℝ) : HasDerivAt f (k*deriv (trig b) (a+u*k) - k*deriv (trig b) a) u := by
      change HasDerivAt (fun u => trig b (a+u*k) - (trig b a + (u*k)*deriv (trig b) a)) _ _
      refine HasDerivAt.congr_deriv (((deriv_trig_diff b _).hasDerivAt.comp (x:=u) (((hasDerivAt_id' u).mul_const k).const_add a)).sub
        ((((hasDerivAt_id' u).mul_const k).mul_const (deriv (trig b) a)).const_add (trig b a))) ?_
      simp [one_mul, mul_comm]
   have hu (u:ℝ) (hu : u∈Icc (0:ℝ) 1) := calc
      ‖k*deriv (trig b) (a+u*k) - k*deriv (trig b) a‖
            = |k| * |deriv (trig b) (a+u*k) - deriv (trig b) a| := by rw[Real.norm_eq_abs,←mul_sub,abs_mul]
      _ ≤ |k| *|(a+u*k)-a| := mul_le_mul_of_nonneg_left (deriv_trig_lip b ..) (abs_nonneg _)
      _ ≤ k^2 := by rw [add_sub_cancel_left,abs_mul,pow_two,abs_of_nonneg hu.1]; calc
                         _ ≤ |k| *(1*|k|) := by gcongr;exact hu.2
                         _ = _ := by simp [← sq, sq_abs] -- fix
   simpa [f,Real.norm_eq_abs] using (norm_image_sub_le_of_norm_deriv_le_segment_01' (f:=f) (fun u _ => (h u).hasDerivWithinAt) (fun u h => hu u (Ico_subset_Icc_self h)))

lemma residual_bound (hn : 4 ≤ n.val) (e : Edge (Site n)) (o : Site n) :
    ‖wave c b i j e - (jet c b i j o).field o e‖ ≤ (Full.mesh n)^2*(separation e.1 o : ℝ)^2 := by
   rw [at_wave,wave_add' _ _ hn]; split_ifs
   · rw [← sub_smul,norm_smul,hc,mul_one, Real.norm_eq_abs]
     apply le_trans (taylor_bound b ..)
     rw [← mul_pow,← sq_abs (delta j o e.1)];gcongr;exact delta_le o e.1 -- need nonneg
   simp [mul_nonneg (sq_nonneg _) (sq_nonneg _)]

lemma linear_bound (e : Edge (Site n)) (o : Site n) :
     ‖((jet c b i j o).field o - (fun e : Edge (Site n) => (jet c b i j o).at0 e.2)) e‖ ≤ Full.mesh n*(separation e.1 o : ℝ) := by
    change ‖(jet c b i j o).field o e - _‖ ≤ _
    rw [at_wave]; dsimp only [jet]
    split_ifs
    · rw [← sub_smul,add_sub_cancel_left,norm_smul,hc,mul_one, Real.norm_eq_abs,abs_mul]; exact (mul_le_mul_of_nonneg_left (deriv_trig_bound b _) (abs_nonneg _) |>.trans_eq (mul_one _)).trans (delta_le o e.1)
    simpa only [sub_zero,norm_zero] using mul_nonneg (Full.mesh_pos.le) (Nat.cast_nonneg ..)

end YM.Pert.Kinetic
