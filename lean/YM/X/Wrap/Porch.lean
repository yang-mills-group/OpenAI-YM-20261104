import YM.X.Nest.Shore
/-!
# Porch: exterior to a set of finitely many standard path marks. Bounds recover distance to seam by day height.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Crate.Porch
open Lattice Wilson Next.Rank CellsInt Beamer Interval PertExtension LatticePT Normal Filter Set Function Metric MeasureTheory Asymptotics
open Reed Fielding Haze Rays Braid Shelf Print
open scoped Topology BigOperators Classical ENNReal
variable {q:ℕ+}{n:Side} {k m d:ℕ} {R:ℝ} {I:Type*} {G:Gauge} (hq:1<q.val)
local notation "Fℕ"=>(atTop:Filter ℕ)
local notation "ε"=>epsilon q
variable (f g:Fielding.Walk) (S: Finset I) (x:I→ Fielding.Walk) (p:I→E4)(hp:∀ i∈ S, plot q (x i) (p i))(χ:Floor R)
local notation "F" i => side q i
-- masks sum net as 0/1 when near single mark
abbrev Quiet (w:ℕ+)(S:Finset I)(x:I→ Fielding.Walk)(χ:Floor R)(k:ℕ)(a:Site (side w k)):ℝ:= 1-∑ i∈ S, χ.s (spot (epsilon w k) (lift (a-wrap (side w k) (x i k))))
def Rest (χ:Floor R)(S:Finset I)(p:I→ E4)(w:E4):ℝ:= 1-∑ i∈ S, χ.s (w-p i)
abbrev Apart (S:Finset I)(p:I→ E4)(R:ℝ):= ∀ i∈S,∀ j∈ S,i ≠ j → R < ‖p i-p j‖
lemma mildQ (a:Site (F k)) : |Quiet q S x χ k a|≤1+ (S.card:ℝ):= by
    unfold Quiet; rw [abs_le]; constructor
    · have h: ∑ i∈S, χ.s (spot (ε k) (lift (a-wrap (F k) (x i k)))) ≤ ∑ _∈ S,(1:ℝ):= Finset.sum_le_sum (fun i hi=> χ.s.le_one); -- _ infer eps?
      rw [Finset.sum_const,nsmul_eq_mul,mul_one] at h; linarith
    have hu: 0 ≤ ∑ i∈S, χ.s (spot (ε k) (lift (a-wrap (F k) (x i k)))):= Finset.sum_nonneg (fun _ _=> χ.s.nonneg); linarith [Nat.cast_nonneg (α:=ℝ) S.card]
include hq
lemma quiet_path {z:E4}(hf:plot q f z) (hp:∀ i∈ S, plot q (x i) (p i)) : Tendsto (fun k=> Quiet q S x χ k (wrap _ (f k))) atTop (𝓝 (Rest χ S p z)) := by
    refine tendsto_const_nhds.sub (tendsto_finsetSum S fun i hi=> ?_); have he:= plot.sub hf (hp i hi); apply χ.s.continuous.continuousAt.tendsto.comp (he.congr' ?_); filter_upwards [plot_lift hq he] with k hk; simp_rw [← map_sub]; exact congr_arg (spot _) hk.symm -- `apply`
-- near region mask does not overlap other marks
variable {i:I}(H:Apart S p R)
include hp H
lemma narrow_port {i j:I}(hi:i∈S)(hj:j∈S)(he:i≠j): ∀ᶠ k in Fℕ,∀ a:Site (F k), ‖spot (ε k) (lift (a-wrap _ (x i k)))‖≤χ.s.rIn → χ.s (spot (ε k) (lift (a-wrap _ (x j k))))=0:= by
    let t:= fun k i=> wrap (F k) (x i k); let g:=x i-x j; let y:=p i-p j; have h:= plot.sub (hp i hi) (hp j hj); have hh:R< ‖p i-p j‖:= H i hi j hj he
    filter_upwards [h.norm.eventually (lt_mem_nhds hh),spot_lift hq R,plot_lift hq h] with k hk ht hh' a ha
    let u:=lift (a-t k i); let v:= lift (a-t k j); let w:=spot (ε k); by_contra hz; have hz:= (show w v∈ Function.support χ.s from hz); rw [χ.s.support_eq,mem_ball,dist_zero_right] at hz; change ‖w u‖ ≤ χ.s.rIn at ha
    have hR : ‖w (v-u)‖≤ R:= by rw [map_sub]; linarith [norm_sub_le (w v) (w u),χ.s.rIn_lt_rOut,χ.s.rOut_pos,χ.h]
    have hp':v-u=g k:= by rw [← ht _ hR, map_sub, show wrap (F k) v=a-t k j from wrap_lift _, show wrap (F k) u= a-t k i from wrap_lift _,show a-t k j - (a-t k i)= t k i - t k j by abel]; simp_rw [t,←map_sub]; exact hh' -- pass notation risk
    rw [hp'] at hR; exact not_le_of_gt hk hR
lemma quiet_basement (hi:i∈ S): ∀ᶠ k in Fℕ, ∀ a: Site (F k), ‖spot (ε k) (lift (a-wrap (F k) (x i k)))‖≤χ.s.rIn → Quiet q S x χ k a=0:= by
    have ht:= (eventually_all_finset (S.erase i)).mpr (fun j hj=> narrow_port hq S x p hp χ H hi (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj).symm); filter_upwards [ht] with k hk a ha; unfold Quiet;rw [Finset.sum_eq_single i,χ.s.one_of_mem_closedBall]; swap; · rw [mem_closedBall,dist_zero_right]; exact ha
    simp; intro j hj hn; exact hk _ (Finset.mem_erase.mpr ⟨hn,hj⟩) a ha; simp [hi] -- edit
lemma tends_zero_at {i:I}(hi:i∈S)(hc:plot q f (p i)): ∀ᶠ k in Fℕ, Quiet q S x χ k (wrap _ (f k))=0:= by
    have hg : plot q (f-x i) 0:= by simpa only [sub_self] using plot.sub hc (hp _ hi)
    filter_upwards [hg.norm.eventually (ge_mem_nhds (by rw [norm_zero]; exact χ.s.rIn_pos)), plot_lift hq hg, quiet_basement hq S x p hp χ H hi] with k hk hh hg; apply hg; simp_rw [← map_sub]; rw [show lift (wrap _ (_-_))= f k-x i k from hh]; exact hk
-- footprint diameter indexed by representative lift of root
abbrev Width (q:ℕ+)(k:ℕ)(z:Cover):=1+epsilon q k*street z
omit hq hp H in
lemma depth(w:ℕ+)(k:ℕ)(z:Cover): 1≤Width w k z:= by unfold Width; have hy:= epsilon_pos w k; apply le_add_of_nonneg_right; positivity
-- (w,∞)-decay costs. No path lift issue. use vertex `wrap z`.
lemma fare (hi:i∈S): ∃ C:ℝ,C>0∧ ∀ᶠ k in Fℕ,∀ z:Cover,lift (wrap (F k) z)=z→ Quiet q S x χ k (wrap _ z)≠0→ Width q k z≤ C* (ε k* Print.scale (F k) z (x i k)):= by
    let B:= fun k:ℕ=> x i k; let t:= (‖p i‖+1); let D:= (1+16*t)/(χ.s.rIn/4); refine ⟨4+D,?_ ,?_ ⟩; · have h:= χ.s.rIn_pos; unfold D t; positivity
    filter_upwards [quiet_basement hq S x p hp χ H hi,(hp i hi).norm.eventually (ge_mem_nhds (lt_add_one ‖p i‖))] with k hk hx z hz hh; let p:=wrap (F k) z; let a:=wrap (F k) (B k); let s:= p-a; let w:=ε k ; have hW : w>0:= epsilon_pos ..; let r:=Print.scale (F k) z (B k); have hr: r=1+pdist s:= mass_eq ..
    have hq' : χ.s.rIn < ‖spot w (lift s)‖:= not_le.mp (fun h=> hh (hk p h));
    have hB : w*(street (B k):ℝ) ≤4*t:= le_trans (street_cost _) (mul_le_mul_of_nonneg_left hx (by norm_num));
    have hY : w* r≥ χ.s.rIn/4:= by
       have hu: (street (lift s):ℝ)≤4*pdist s:= by exact_mod_cast round_lift s
       have hv:= spot_cost (q:=q) (k:=k) (lift s); change _≤w* ↑(_) at hv; nlinarith only [hq'.le.trans hv,mul_le_mul_of_nonneg_left hu hW.le, hr,hW]
    have hw: (street z:ℝ) ≤ 4*pdist p:= by exact_mod_cast (show street z ≤ 4*pdist p from hz ▸ round_lift p)
    have he: pdist p≤ pdist s+street (B k):= by
        rw [show p=s+a from (sub_add_cancel ..).symm] -- fails p inside s?
        exact le_trans (pdist_triangle ..) (Nat.add_le_add_left (wrap_rotate (n:=F k) (B k)) _)
    have he' : Width q k z ≤ 4*(w*r)+(1+16*t):= by
       rw [hr];unfold Width; have he' : (pdist p:ℝ) ≤ (pdist s:ℝ)+(street (B k):ℝ):= by exact_mod_cast he
       change 1+w*(street z:ℝ)≤ _; nlinarith only [mul_le_mul_of_nonneg_left hw hW.le,mul_le_mul_of_nonneg_left he' hW.le,hW,hB]
    have hh: D*(w*r)≥1+16*t:= by
       have he: χ.s.rIn/4>0:= div_pos χ.s.rIn_pos (by norm_num); have hy:0≤1+16*t:= by unfold t; positivity
       unfold D; rw [div_mul_eq_mul_div]; exact (le_div_iff₀ he).2 (mul_le_mul_of_nonneg_left hY hy)
    exact le_trans he' (show _≤ (4+D)*(w*r) by rw [add_mul];exact add_le_add_right hh _)
end YM.PositionX.Crate.Porch
