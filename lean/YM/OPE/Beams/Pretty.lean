import YM.OPE.Beams.Contour
/-! # Lights for surviving sign shift
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Reels
open Function Filter Finset MeasureTheory Lattice RG Wilson Metric Polar
open Trunk Rhythm
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge}{C:Family G} {F:Extraction.Order} {S:Table C.book}(U:Spec.Final C F S)
variable {I J L Z:Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]{f:Filter L}
    {T:L→ℝ}{M η P₀:ℝ}{v j k:I}
    {X:L→ I→ E4}{x:L→ (I→ E4)→ J→ E4}
    {H t n m:ℕ}{Q: Rhythm I}
    {R r:L→ℕ→ℝ}{α:ℕ→ℝ}{Y: L→ ℕ}
    (B:Border f T Q.limit R r α)
    (H':Q.Strike H n) (hm:0≤M)(hη:0<η)(hX:∀ᶠ i in f,draft Q (R i) (r i) M η H (X i))
local notation "X'"=> (I→E4)
local notation "ξ!"=> Border.orbit Q H T r X
local notation "μ"=> Q.localTime H
local notation "πc"=> action T H Q r
open Shuttle
abbrev remaining (Q:Rhythm I)(H:ℕ) := univ \ Q.focus H
include B H' hm hη hX
-- build primitive s' without using new Pole perturbations.
lemma slender_main : Slender f T (fun i u=>substituted (Q.focus H) (ξ! i u)) (fun i u=>beside (sole (0:ℝ)) (chunk (remaining Q H) (πc i u))) :=by
    let J:= remaining Q H; have hc:=H'.atMost; have hP: H ≤ Q.age Q.star:= H'.exists_.symm.le; have he:Slender f T (fun i u=>chunk J (ξ! i u)) (fun i u=>chunk J (πc i u)):= (slender_lane B hP hm hη hX).relabel (Subtype.val (p:=fun x:I=> x∈J)) Subtype.val_injective
    refine Slender.join Slender.empty he ?_; intro k a i y hb
    let d:= Q.gap Q.star i.val; let γ:=η/2; let M':=M+γ; have hv:i.val∉ Q.focus H:= (mem_sdiff.mp i.property).2; have hh: Q.star ≠ i.val:= fun h=> hv (h ▸ (Q.on_focus).2 (Q.yes ..)); have hy:d < H:= (Q.flip Q.star i.val).trans_lt ((H'.reserve _ hv).trans_lt H'.before); let t:= μ k; have he:t ≤ Q.limit:= (Q.timeBirth hP k).trans (Q.bounded _); have h_t:d ≤ Q.limit:= hy.le.trans hc
    have hγ:0<γ:=half_pos hη; have hx:=B.trajectory hP hX hη; let h:=γ/2/2; have hs:h+h=γ/2:=(by unfold h; ring); have h':0<h:=half_pos (half_pos hγ)
    have hφ := (B.rates d h_t).mul (RateIs.const B.life (mul_pos hb h')); have hU:∀ᶠ i in f,jacket (T i) < r i d*(y*h):= hφ.overtakes ((jacket_price B.life).pays B.life) B.life (by linarith only [B.pace d h_t|>.2]); have hA:Tendsto (fun i=>R i (d+1)/r i d) f (𝓝 0):=by simpa only [pow_zero,mul_one] using! B.leap d (hy.trans_le hc) 0
    have hm':0≤ M':= add_nonneg hm hγ.le
    filter_upwards [hU,hx,(B.rates d h_t).pos,(B.rates t he).pos,B.life.eventually_gt_atTop 0,(tendsto_inv_atTop_zero.comp B.life).eventually (ge_mem_nhds (mul_pos hb h')), (show ∀ᶠ i in f, d ≤ t → r i t ≤ r i d from eventually_all.mpr fun h:d ≤ t=> (B.in_order h he).mono fun i h=> h.1), (hA.const_mul M').eventually (ge_mem_nhds (show M'*0<γ/2 from (by unfold γ; simp only [mul_zero]; positivity))), B.in_order (show d+1≤H from hy) hc] with i' hu ht hp hp' h0 ht0 hp0 hM hO z hz
    change |0-πc i' k i.val|+_ ≤ y*‖0-ξ! i' z i.val‖; have hV: γ/2*r i' d ≤ ‖0-ξ! i' z i.val‖:=by
       have h:= (ht z hz).reserve _ _ hh; have hG:= (ht z hz).hostel; let x:= ξ! i' z; have hY': M'*R i' (d+1) ≤ γ/2*r i' d:= (div_le_iff₀ hp).mp (by rw [mul_div_assoc]; exact hM); rw [zero_sub,norm_neg]; linarith only [show M' * R i' H ≤ M'*R i' (d+1) from mul_le_mul_of_nonneg_left hO.2 hm',show γ*r i' d < ‖x Q.star-x i.val‖ from h,hY', show ‖x Q.star‖ ≤ M'*R i' H from hG, norm_sub_le (x Q.star) (x i.val)]
    have hp'' : |0-πc i' k i.val| ≤ r i' d/T i':=by
       unfold action; rcases lt_or_ge t d with hH0|hH0; · rw [Q.root_affords hP (show Q.pinned _ i.val d from ⟨hy.le,(Q.on_focus).2 (Or.inr le_rfl)⟩) hH0 _,sub_self,abs_zero]; exact (div_pos hp h0).le
       by_cases he: Q.tracked H k i.val; · rw [reaches,if_pos he,zero_sub,abs_neg,abs_of_nonneg (div_pos hp' h0).le]; exact div_le_div_of_nonneg_right (hp0 hH0) h0.le
       rw [reaches,if_neg he,sub_self,abs_zero]; exact (div_pos hp h0).le
    rw [div_eq_mul_inv] at hp''; apply (add_le_add (hp''.trans (mul_le_mul_of_nonneg_left ht0 hp.le)) hu.le).trans; apply le_trans (b:=y*(γ/2*r i' d)) ?_ (mul_le_mul_of_nonneg_left hV hb.le); change r i' d*(y*h)+_ ≤_; rw [← hs]; exact le_of_eq (by ring)
end YM.OPE.Log.Reels
