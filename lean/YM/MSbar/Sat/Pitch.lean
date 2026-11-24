import YM.MSbar.Sat.Quick
set_option autoImplicit false
noncomputable section
namespace YM.Push.Uniform
open Lattice Matrix Filter Function Set Metric Finset
open scoped Topology ContDiff BigOperators Classical
variable {n : Side} {ι τ : Type} [Fintype ι] [Fintype τ] [DecidableEq τ]{a C r D ρ m R X T: ℝ}{N K : ℕ}
    {l : ι ⊕ τ → Site n}{f : Positions (ι⊕τ) → ℝ}(H: Receipt l a N K C r m f)
local notation "I"=> Positions (ι⊕τ)
set_option quotPrecheck false
local notation "jW"=> (K:ℝ)*countCost a
variable {x : Positions ι}{v w: Positions τ}
local notation "q₀"=> block f (0:Positions (ι⊕τ))
def vest (f:Positions (ι⊕τ)→ℝ)(x:Positions ι): Positions τ:= - ((block f 0)⁻¹ *ᵥ ((fderiv ℝ (Slope f) 0) (meetVar x (0:Positions τ))))
local notation "l₀"=> (fderiv ℝ (Slope f) (0:I))
def plank (f:Positions (ι⊕τ)→ℝ)(i j:τ):ℝ:= ((block f 0)⁻¹) i j
include H
lemma backs (v:Positions τ) (x:Positions ι) : l₀ (meetVar x v)= q₀*ᵥ(v-vest f x) :=by
   rw [meet_columns,map_add,driven H]
   have hz: 0<(block f 0).det:= H.priced_inverse (0:I) (mem_closedBall_self H.reserveH_pos.le)|>.1
   unfold vest; rw [sub_neg_eq_add,mulVec_add,mulVec_mulVec,(block f 0).mul_nonsing_inv (isUnit_iff_ne_zero.mpr hz.ne'),one_mulVec, add_comm]; -- edit
lemma sights (x:Positions ι) (v:Positions τ) (i:τ): blush (plank f i) (l₀ (meetVar x v))= v i-vest f x i:=by
   rw [backs H]; change ((block f 0)⁻¹ *ᵥ (q₀ *ᵥ _)) i=_
   have hz: 0<(block f 0).det:= (H.priced_inverse (0:I) (mem_closedBall_self H.reserveH_pos.le)).1
   rw [mulVec_mulVec,(block f 0).nonsing_inv_mul (isUnit_iff_ne_zero.mpr hz.ne'), one_mulVec]; rfl
omit H in
lemma blush_split (w v g:Positions τ) : blush (w+v) g=blush w g+blush v g:=by unfold blush; simp [add_mul,Finset.sum_add_distrib]
omit H in
lemma blush_rate (u v:Positions τ)(b:ℝ) : blush (b • u) v=b*blush u v:=by unfold blush; simp [mul_assoc,Finset.mul_sum]
omit H in
lemma wash_add (w v: Positions τ): wash (w+v)≤ wash w + wash v:=by unfold wash; rw [← Finset.sum_add_distrib]; exact sum_le_sum fun i _=> abs_add_le ..
omit H in
lemma wash_nonneg (w:Positions τ): 0 ≤ wash w:= by unfold wash; positivity
omit H in
lemma wash_smul (w:Positions τ)(r:ℝ): wash (r • w) =|r| * wash w:=by unfold wash; simp [Finset.mul_sum,abs_mul]
omit H in
lemma sup_wash (w:Positions τ):‖w‖ ≤ wash w:= (pi_norm_le_iff_of_nonneg (wash_nonneg w)).2 fun i=> le_trans (le_of_eq (Real.norm_eq_abs _)) (Finset.single_le_sum (f:=fun i=> |w i|) (fun i _=> abs_nonneg _) (Finset.mem_univ _))
lemma sight_range (p:I)(h:‖p‖ ≤ D)(hx:D<r): ‖l₀ p‖ ≤ D*(C*jW)+D*(C*jW)*jW*D:=by
   have h₁:=lyric H h hx; have hh:= slope_range H.pos_a H.pos_C.le H.mult (convex_ball ..) H.born (show p∈ball 0 r from (by simpa using h.trans_lt hx)) (mem_ball_self H.pos_r) ((by norm_num:2≤3).trans H.order); simp_rw [H.alone,sub_zero] at hh
   have hv : _ ≤ D*(C*jW):= hh.trans (mul_le_mul_of_nonneg_right h (mul_nonneg H.pos_C.le (mul_nonneg (Nat.cast_nonneg _) (count_pos H.pos_a|>.le))))
   exact le_trans (show ‖l₀ p‖ ≤ ‖Slope f p‖ + ‖Slope f p-l₀ p‖ from by nth_rw 1 [← show Slope f p - (Slope f p - l₀ p)= l₀ p from sub_sub_cancel _ _]; exact norm_sub_le ..) (add_le_add hv h₁)
lemma steer (hv:‖meetVar x v‖≤D)(hw:wash w≤ X)(hx:D+X<r)(i:τ){b:ℝ} (hp:wash (w+b • plank f i) ≤ T) : |f (meetVar x (v+w))- f (meetVar x v)+b*(v i-vest f x i)| ≤ X*(X*(C*jW) + D*(C*jW)*jW*D)+T*(D*(C*jW)+D*(C*jW)*jW*D) :=by
   let z:=l₀ (meetVar x v); have ha : 0 ≤ X:=(wash_nonneg _).trans hw; have hc := H.pos_C; have hy:= count_pos H.pos_a; have hD := (norm_nonneg _).trans hv
   have h := (slip H hv (sup_wash _ |>.trans hw) hx).trans (mul_le_mul_of_nonneg_right hw (by positivity))
   have ht := (washes (w+b • plank f i) z).trans (mul_le_mul hp (sight_range H _ hv (by linarith only [hx,ha])) (norm_nonneg _) ((wash_nonneg _).trans hp))
   let Y:=f (meetVar x (v+w))- f (meetVar x v); rw [show Y+_= (Y-blush w z)+blush (w+b • plank f i) z from ?_]; · exact (abs_add_le ..).trans (add_le_add h ht)
   rw [blush_split,blush_rate]; unfold z; rw [sights H]; abel
end YM.Push.Uniform
