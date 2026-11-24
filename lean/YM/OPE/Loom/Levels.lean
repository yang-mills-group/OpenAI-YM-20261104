import YM.OPE.Prices.Circuit
import YM.OPE.Columns.Cone
import YM.OPE.Loom.Cost
import YM.OPE.Loom.Clocks
/-!
# Polynomial renormalization-interval prices and grade-zero squeezes
Keeping the actual `Levels`; in particular at *zero* relative s/T, margins
still say `u` here grows with the tail when requested, and all post-block
onsite allowances shown are polynomial. `Cheap` is not used for path
lengths actually in units of radius.
-/
set_option autoImplicit false
noncomputable section
open Filter Function Set
open scoped Topology BigOperators
namespace YM.OPE.Loom
open Lattice RG Wilson MergeProof Accent Ribbons Source Overlay
open Bid ManyCopies PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Bandage
variable {G:Gauge} {C:Family G} {I : Type*} {φ : Filter I} {T a c : I→ℝ} {m k : I→ℕ} {b v : ℝ}
variable (hT:Tendsto T φ atTop)
local notation "Y" => C.path.levels
local notation "X" => C.path.levels.clock.hatBeta
local notation "L" => C.S
set_option quotPrecheck false
variable {W r D} (H : TableTickets C W r D)
-- using positive price T arbitrary with bounded-scale comparability as needed.
include hT
lemma cheap_by_ratio (h:Tendsto (fun i=> a i/T i) φ (𝓝 v)) : Cheap φ T a:= by
   apply Cheap.of_bound 2; filter_upwards [h.norm.eventually (gt_mem_nhds (lt_add_one ‖v‖)),hT.eventually_ge_atTop (‖v‖+1),hT.eventually_gt_atTop 0] with i hi hh hz
   change ‖a i/T i‖ < ‖v‖+1 at hi; rw [norm_div] at hi; rw [pow_two]; exact ((div_lt_iff₀ (norm_pos_iff.mpr hz.ne')).mp hi |>.le).trans (mul_le_mul_of_nonneg_right (hh.trans (Real.le_norm_self _)) (norm_nonneg _))
-- Height consumers
lemma hat_price (h : Height C.S φ T m b) : Coins φ T (X ∘ m):= by
   apply Coins.by_le; swap; · exact Eventually.of_forall fun i=> ((Y).fits.delayed _|>.le).trans (Real.le_norm_self _)
   exact (Bill.const (Y).clock.bar hT).add (Cheap.mul (Bill.const G.slopeConstant hT) (cheap_by_ratio hT h.pace)) hT
omit hT
lemma exists_hat (C:Family G) (h:G.Simple) : Tendsto C.path.levels.clock.hatBeta atTop atTop:= tendsto_atTop_add_const_left _ _ (C.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos h))
lemma first_price : Height C.S atTop C.S.scale id 1:= ⟨tendsto_id,tendsto_const_nhds.congr' ((C.S.divergent.eventually_gt_atTop 0).mono fun _ hi=> (div_self hi.ne').symm)⟩
-- stride scales
lemma prec (h : Height C.S φ T m b) : Height C.S φ T (fun i=>m i-1) b:=by
   let M i:= m i - 1; have hM : Tendsto M φ atTop:=tendsto_atTop.mpr fun j=> by filter_upwards [h.grows.eventually_gt_atTop j] with i hi; unfold M; omega
   let D i:= C.S.scale (M i); let d i:= C.S.scale (m i); let S i:=D i+Real.log (C.S.block (M i)).val; have he:= hM.eventually (C.S.divergent.eventually_gt_atTop 0); have hf:= (C.S.divergent.comp h.grows).eventually_gt_atTop 0; have hg: S =ᶠ[φ] d:= by
      filter_upwards [h.grows.eventually_gt_atTop 0] with i hi; change _= C.S.scale (m i); rw [← (show M i+1=m i from Nat.sub_add_cancel hi),C.S.scale_succ]
   have ht : Tendsto (fun i=> d i/D i) φ (𝓝 1):= by
      refine (show Tendsto (fun i=> 1+Real.log (C.S.block (M i)).val/D i) φ (𝓝 1) from by simpa only [add_zero] using! (((Y).fits.mesh.comp hM).const_add 1)).congr' ?_
      filter_upwards [he,hg] with i hi hh; rw [← hh,show S i=D i+_ from rfl,add_div,div_self (ne_of_gt (show 0 < D i from hi))]
   have hx:=h.pace.div ht (show (1:ℝ)≠0 from one_ne_zero); rw [div_one] at hx; refine ⟨hM,hx.congr' ?_⟩
   filter_upwards [he,hf] with i hi hh; change d i/T i/(d i/D i)=D i/_; have hz:0 < d i:= hh; field_simp
include hT
lemma block_p (H : Stock.Tabs C.path.levels) (h : Height C.S φ T m b) : Coins φ T (fun i=> ((C.S.block (m i)).val:ℝ)) := by
   have hb:= cheap_by_ratio hT (h.step (Y).fits.mesh).pace
   apply Coins.by_le; swap; · exact Eventually.of_forall fun i=> (show (1:ℝ)≤ (C.S.block (m i)).val by exact_mod_cast (C.S.block (m i)).pos).trans (Real.le_norm_self _)
   refine hb.norm_le ?_; filter_upwards [h.grows.eventually (H.cheap 1 one_pos)] with i hi
   let k:=m i; let l:ℝ:= (C.S.block k).val; let B:ℝ:= (Y).clock.coverSize k; let f:= Vac.fiat G ((Y).params (k+1)) ((X) (k+1)); have hl:1 ≤ l:= by unfold l; exact_mod_cast (C.S.block k).pos
   have hk:1 ≤ B:= Nat.one_le_cast.mpr ((Y).budget k).B_pos
   have hL:B^2 ≥ 1:= one_le_pow₀ hk; have hw := stock_fiat C (k+1)
   change ‖l‖ ≤ ‖C.S.scale (k+1)‖; rw [Real.norm_of_nonneg (by positivity : 0 ≤ l)]
   apply le_trans _ (Real.le_norm_self _); rw [one_mul] at hi; refine le_trans ?_ hi
   change l ≤ (l*B^2)^4*f; have hx:l ≤ l*B^2:=le_mul_of_one_le_right (by positivity) hL
   exact (hx.trans (by nth_rw 1 [← pow_one (l*B^2)]; exact pow_le_pow_right₀ (hl.trans hx) (by decide))).trans (le_mul_of_one_le_right (by positivity) hw)
lemma shift_mesh (h : Height C.S φ T m b) (H : Stock.Tabs C.path.levels) : Bi φ T (fun i=>C.S.a (m i+1)) (fun i=>C.S.a (m i)):= by
   have hv := block_p hT H h; have hh:= Bi.mul (Bi.refl φ T (C.S.a ∘ m)) (Coins.inv hv); simpa only [Function.comp_def,mul_one,Schedule.a_step,div_eq_mul_inv] using! hh
lemma shift_back (h : Height C.S φ T m b) (H : Stock.Tabs C.path.levels): Bi φ T (fun i=>C.S.a (m i-1)) (fun i=>C.S.a (m i)):= by
   apply Bi.congr (shift_mesh (m:=fun i=>m i-1) hT (prec h) H).symm (Filter.EventuallyEq.refl _ _)
   filter_upwards [h.grows.eventually_gt_atTop 0] with i hi; rw [Nat.sub_add_cancel hi]
include H in
lemma columns_p (h : Height C.S φ T m b) : Coins φ T (fun i=>((Y).params (m i)).columns):= by
   apply Coins.by_le; swap; · exact Eventually.of_forall fun i=> (((Y).params _).columns_ge).trans (Real.le_norm_self _)
   apply (block_p (C:=C) hT H.tabs (prec h)).up.norm_le; filter_upwards [h.grows.eventually_gt_atTop 0] with i hi
   let k:=m i; rw [Real.norm_of_nonneg (zero_le_one.trans ((Y).params _).columns_ge)]; apply le_trans _ (Real.le_norm_self _); change ((Y).params k).columns ≤ ((C.S.block _).val:ℝ); nth_rw 1 [← Nat.sub_add_cancel (show 1 ≤ k from hi)]; exact Columns.column_small (i:=k-1) H.system.costs.back
lemma covers_p (h : Height C.S φ T m b) : Coins φ T (fun i=>(((Y).budget (m i)).B:ℝ)):= by
   apply Coins.by_le; swap; · exact Eventually.of_forall fun i=> (Nat.one_le_cast.mpr ((Y).budget (m i)).B_pos).trans (Real.le_norm_self _)
   have he:= Cheap.power (hat_price hT h).up hT 2; refine (Bill.add he (Bill.const (1:ℝ) hT) hT).norm_le ?_
   apply Eventually.of_forall; intro i; let k:=m i; let t:= (X) k; have ht:1<t:= (Y).fits.delayed _; have hp:0 < Real.log t:= Real.log_pos ht
   change ‖(↑(Nat.ceil ((Real.log t)^2)):ℝ)‖≤ ‖t^2 +1‖; rw [Real.norm_of_nonneg (by positivity)]; apply le_trans _ (Real.le_norm_self _); exact (Nat.ceil_lt_add_one (sq_nonneg _) |>.le).trans (by gcongr; exact Real.log_le_self (by linarith only [ht]))
end YM.OPE.Loom
