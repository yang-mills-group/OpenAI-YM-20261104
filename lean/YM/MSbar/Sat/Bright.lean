import YM.Push.STATIONARY_UNIFORM.Paths
/-! # Effective real Gaussian linearization, anchored to regular pricing
Receipt, tracks ℓ^1 change separately from window sup price. -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Uniform
open Lattice Matrix Filter Function Set Metric Finset
open scoped Topology ContDiff BigOperators Classical
variable {n : Side} {ι τ : Type} [Fintype ι] [Fintype τ] {a C r D ρ m X: ℝ}{N K : ℕ}
    {l : ι ⊕ τ → Site n}{f : Positions (ι⊕τ) → ℝ}(H: Receipt l a N K C r m f)
local notation "I"=> Positions (ι⊕τ)
local notation "jW"=> (K:ℝ)*countCost a
include H
variable {x : Positions ι}{v w: Positions τ}
local notation "F"=> Slope f
lemma driving {u:I}(h:u∈ball 0 r) : ContDiffAt ℝ ω F u := contDiffAt_pi.mpr (fun i=> (tend_entry (H.born _ h).1 ![Sum.inr i]).1)
local notation "L"=> fderiv ℝ F (0:I)
lemma driven (w : Positions τ) : L (meetVar (0:Positions ι) w)= (block f 0)*ᵥ w := by
   have hz: meetVar (0:Positions ι) (0:Positions τ)=(0:I) := by change (partSpace ι τ).symm 0=_; rw [map_zero]
   have hd := (slope_block (hz.symm ▸ (H.born _ (mem_ball_self H.pos_r)).1 : ContDiffAt ℝ ω f (meetVar (0:Positions ι) (0:Positions τ)))).2 w
   have hD:= ((driving H (show meetVar (0:Positions ι) (0:Positions τ) ∈ball 0 r by rw [hz];exact mem_ball_self H.pos_r)).differentiableAt (by simp)).hasFDerivAt.comp 0 (meet_derivative (0:Positions ι) (0:Positions τ))
   rw [show (meetVar (0:Positions ι) w) = lowerCol w from rfl, ←hz]; rw [hD.fderiv] at hd; exact hd
lemma leash {p:I} (hp:p∈ball 0 r) {A:ℝ}(h:‖p‖≤A) (i:τ):
    let g z := F z i; ‖fderiv ℝ g p-fderiv ℝ g 0‖ ≤ A*(C*jW)*jW := by
    intro g; let y:= l (Sum.inr i); have hb(j):= (tend_entry (H.born _ hp).1 ![Sum.inr i]).2 j
    have h₀:= mem_ball_self (x:=(0:I)) H.pos_r; have hx(j):= (tend_entry (H.born (0:I) h₀).1 ![Sum.inr i]).2 j
    have hz(i'): ‖(fderiv ℝ g p-fderiv ℝ g 0) (bolt i')‖ ≤ A*(C*jW)*Decay a y (l i') :=by
        rw [ContinuousLinearMap.sub_apply,show fderiv ℝ g p _=_ from hb i', show fderiv ℝ g 0 _=_ from hx i']; apply (scatter_difference H.pos_a H.pos_C.le H.mult (convex_ball ..) H.born h₀ hp H.order ![i',Sum.inr i] 1).trans -- k<N'H.order
        have hv:= H.pos_C; have hh:= count_pos H.pos_a; simp only [spanSites,Fin.sum_univ_succ]; simp [Decay,y]; gcongr
    have hv:0≤(K:ℝ)*countCost a:=mul_nonneg (by positivity) (count_pos H.pos_a).le; have hi := H.pos_C.le; have ha:0 ≤ A:= (norm_nonneg _).trans h
    have ht:0≤ A*(C*jW) := by exact mul_nonneg ha (mul_nonneg hi hv)
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg ht hv); intro v
    rw [by_row]; refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun i':ι⊕τ=>‖v‖*(A*(C*jW)*Decay a y (l i'))) (fun j _=> ?_)).trans ?_)
    · rw [norm_smul]; exact mul_le_mul (norm_le_pi_norm v j) (hz _) (norm_nonneg _) (norm_nonneg _)
    rw [← mul_sum, ← mul_sum]; apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (H.mult.count l H.pos_a y) ht) (norm_nonneg _)).trans_eq (mul_comm ..); -- bravo
lemma lyric {p:I}(he : ‖p‖≤D)(hg:D<r) : ‖F p-L p‖ ≤ D*(C*jW)*jW*D:=by
    have hd := count_pos H.pos_a; have hc:= H.pos_C; have hv : 0 ≤ D:= (norm_nonneg _).trans he
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ D*(C*jW)*jW*D)).2; intro i; let s y:= F y i; let Q : Positions τ →L[ℝ] ℝ := ContinuousLinearMap.proj i; let g(x:I):= s x-fderiv ℝ s 0 x
    have hz : fderiv ℝ s 0 = Q.comp L:= by unfold s; exact ((Q.hasFDerivAt).comp (0:I) ((driving H (mem_ball_self H.pos_r)).differentiableAt (by simp)).hasFDerivAt).fderiv
    have hx y (hy:y∈ closedBall (0:I) D): HasFDerivAt g (fderiv ℝ s y-fderiv ℝ s 0) y := (((tend_entry (H.born y (closedBall_subset_ball hg hy)).1 ![Sum.inr i]).1.differentiableAt (by simp)).hasFDerivAt.sub (fderiv ℝ s 0).hasFDerivAt) -- type
    have hw := (convex_closedBall (0:I) D).norm_image_sub_le_of_norm_fderiv_le (f:=g) (fun y hy=> (hx y hy).differentiableAt) (fun y hy=> ((congr_arg norm (hx y hy).fderiv).trans_le (leash H (closedBall_subset_ball hg hy) (p:=y) (show ‖y‖≤D by simpa using hy) i))) (mem_closedBall_self hv) (mem_closedBall.mpr (show dist p 0≤D by rwa [dist_zero_right])) -- binder
    rw [show g 0=0 from ?_,sub_zero,sub_zero] at hw; unfold g at hw; rw [hz] at hw; exact hw.trans (mul_le_mul_of_nonneg_left he (by positivity))
    unfold g s; rw [H.alone,map_zero]; simp
end YM.Push.Uniform
