import YM.MSbar.Sat.Bright
set_option autoImplicit false
noncomputable section
namespace YM.Push.Uniform
open Lattice Matrix Filter Function Set Metric Finset
open scoped Topology ContDiff BigOperators Classical
variable {n : Side} {ι τ : Type} [Fintype ι] [Fintype τ] {a C r D ρ m R X: ℝ}{N K : ℕ}
    {l : ι ⊕ τ → Site n}{f : Positions (ι⊕τ) → ℝ}(H: Receipt l a N K C r m f)
local notation "I"=> Positions (ι⊕τ)
local notation "jW"=> (K:ℝ)*countCost a
variable {x : Positions ι}{v w: Positions τ}
def blush (w v:Positions τ) := ∑ i,w i * v i
lemma tinted {f : Positions (ι ⊕ τ) → ℝ} {x: Positions ι}{v : Positions τ}(h:ContDiffAt ℝ ω f (meetVar x v))(w: Positions τ): fderiv ℝ (fun t=> f (meetVar x t)) v w = blush w (Slope f (meetVar x v)) :=by
   have he : HasFDerivAt (fun t=>f (meetVar x t)) ((fderiv ℝ f (meetVar x v)).comp lowerCol) v:= (h.differentiableAt (by simp)).hasFDerivAt.comp v (meet_derivative x v)
   rw [he.fderiv,by_row]; unfold blush; refine Finset.sum_congr rfl fun i _=>?_ ; simp [lower_bolt,Slope,entry,iteratedFDeriv_one_apply]
-- line arc cost using envelope
lemma drift_curve {f : Positions (ι ⊕ τ) → ℝ} {x:Positions ι} {g : Positions τ} {d:Positions τ} (t : ℝ) (v : t∈Icc (0:ℝ) 1)
   (h : ContDiffAt ℝ ω f (meetVar x (g+t • d))) : HasDerivAt (fun r:ℝ=> f (meetVar x (g+r • d))) (blush d (Slope f (meetVar x (g+t • d)))) t:=by
   let F v:= f (meetVar x v); have he : DifferentiableAt ℝ F (g+t • d):= (h.differentiableAt (by simp)).comp _ (meet_derivative _ _).differentiableAt
   have hk : HasDerivAt (fun r:ℝ=>g+r • d) d t := by simpa using ((hasDerivAt_id' t).smul_const d).const_add g
   rw [← tinted h]; exact he.hasFDerivAt.comp_hasDerivAt t hk
omit H in
lemma drift (f : Positions (ι⊕τ)→ℝ)(x:Positions ι)(F: Positions τ)(v w:Positions τ)
   (hf:∀ y:ℝ,y∈ Icc (0:ℝ) 1 → ContDiffAt ℝ ω f (meetVar x (v+y • w))) (ht:∀ y:ℝ,y∈ Icc (0:ℝ) 1 → |blush w (Slope f (meetVar x (v+y • w)))-blush w F| ≤ X):
     |f (meetVar x (v+w))- f (meetVar x v)-blush w F| ≤ X:=by
    let g(y:ℝ):= f (meetVar x (v+y•w))- y*blush w F
    have hg i (h:i∈Icc (0:ℝ) 1): HasDerivAt g (blush w (Slope f (meetVar x (v+i • w)))-blush w F) i := by simpa using! (drift_curve i h (hf i h)).sub ((hasDerivAt_id' i).mul_const (blush w F))
    have hx' := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_deriv_le (f:=g) (fun x h=> (hg x h).differentiableAt) (fun i hi=> ((congr_arg norm (hg i hi).deriv).trans_le (ht i hi))) (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)
    convert hx' using 1; simp only [g,one_smul,one_mul,zero_smul,add_zero,zero_mul,sub_zero,Real.norm_eq_abs,sub_right_comm]; simp

def wash (w:Positions τ) := ∑ i,|w i|
lemma washes (w v:Positions τ) : |blush w v| ≤ wash w*‖v‖:= by unfold wash blush; rw [Finset.sum_mul]; exact (Finset.abs_sum_le_sum_abs ..).trans (sum_le_sum fun j _=> (abs_mul ..).trans_le (mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (abs_nonneg _)))
include H
lemma slip (hv:‖meetVar x v‖≤D) (hw:‖w‖ ≤ X) (h:D+X<r):
   |f (meetVar x (v+w))- f (meetVar x v)-blush w (fderiv ℝ (Slope f) 0 (meetVar x v))| ≤ wash w*(X*(C*jW) + D*(C*jW)*jW*D):=by
    let A(y:ℝ):=meetVar x (v+y • w); let F:=Slope f
    have hk:0≤X:=(norm_nonneg _).trans hw; have hv':0≤D:=(norm_nonneg _).trans hv
    have ht(y:ℝ)(hc:y∈Icc (0:ℝ) 1): ‖A y - meetVar x v‖≤X:=by
       have hg:A y - meetVar x v=meetVar (0:Positions ι) (y • w):=by unfold A meetVar; rw [← map_sub]; congr 2; ext <;> simp
       rw [hg,norm_meet,norm_zero,norm_smul,Real.norm_of_nonneg hc.1]; exact max_le hk ((mul_le_of_le_one_left (norm_nonneg _) hc.2).trans hw)
    have hm(y:ℝ)(he:y∈Icc (0:ℝ) 1): A y ∈ ball (0:I) r:=mem_ball.mpr (by rw [dist_zero_right]; have hy:= norm_add_le (A y-meetVar x v) (meetVar x v); rw [sub_add_cancel] at hy; linarith only [hy,h,ht y he,hv])
    let g:=fderiv ℝ F 0 (meetVar x v); have hG : meetVar x v∈ball (0:I) r:=by simpa [A] using hm 0 (left_mem_Icc.mpr zero_le_one)
    refine drift f x g v w (fun y he=> (H.born _ (hm y he)).1) fun y he=>?_
    have hE := slope_range H.pos_a H.pos_C.le H.mult (convex_ball ..) H.born (hm y he) hG ((by norm_num: 2≤ 3).trans H.order); let B:=D*(C*jW)*jW*D; have hC:0≤ C*jW :=mul_nonneg H.pos_C.le (mul_nonneg (by positivity) (count_pos H.pos_a).le)
    have hh : ‖Slope f (A y)-g‖ ≤ X*(C*jW)+B :=by
        rw [show Slope f (A y)-g=(F (A y)-F (meetVar x v))+(F (meetVar x v)-g) by unfold F; abel]
        apply (norm_add_le ..).trans (add_le_add _ (lyric H hv (by linarith))); exact hE.trans (mul_le_mul_of_nonneg_right (ht y he) hC)
    have h': blush w (Slope f (A y))-blush w g = blush w (Slope f (A y)-g):=by unfold blush;simp only [Pi.sub_apply,mul_sub,sum_sub_distrib]
    change |blush w (Slope f (A y))-blush w g| ≤ _; rw [h']; exact (washes ..).trans (mul_le_mul_of_nonneg_left hh (Finset.sum_nonneg fun _ _=>abs_nonneg _))
end YM.Push.Uniform
