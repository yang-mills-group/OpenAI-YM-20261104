import YM.OPE.Columns.SectorCost
import YM.OPE.Log.Wallet

/-!
# Numerical obstruction to the pricing argument directly with ordinary tickets

Do NOT use this to infer that a logarithmic strengthening of CLOSED or a
construction of a MatrixTicket is *false*! These are costs of bounds, not
lower bounds on the OPE/walking matrices.

But it is a provable obstacle to just using the multi-step estimates on those
tickets in the supply of our C along with choosing calibration stages and new
delays (even arbitrarily many extra delays): the prices giving the subpower
estimate `Columns.limit_cap` and/or `Columns.whole_origin` actually
have prefix-product factors that NEVER satisfy the needed log prices for
using those estimates, *even on a subsequence*, for ANY such construction.
Need a different argument or genuinely sharpened estimates. `G.Simple` needed
only as indicated for expressing the power with reference to hatBeta.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log
open Function Set Filter RG Columns
open scoped Topology BigOperators Classical ContDiff

private lemma ratio_rule {S : Schedule} (h : S.Gentle) : Tendsto (fun k=> S.scale (k+1) / S.scale k) atTop (𝓝 1) := by
   unfold Schedule.Gentle at h; have H := h.const_add 1
   rw [add_zero] at H
   apply H.congr'; filter_upwards [S.divergent.eventually_gt_atTop 0] with k hk
   rw [S.scale_succ,add_div,div_self hk.ne']

private lemma compare {Z S : ℕ→ℝ} (hS : ∀ᶠ i:ℕ in atTop,0 < S i) (h : Tendsto (fun i=> S (i+1)/S i) atTop (𝓝 1)) (p : ℕ) (he : ∀ i:ℕ,0 < Z i ∧ 2*Z i ≤ Z (i+1)) : Tendsto (fun i=> Z i / S i ^ p) atTop atTop := by
   let q i := Z i / S i ^ p
   have hf(i) : 0 < S i → 0 < q i := fun h=> div_pos (he i).1 (pow_pos h p)
   have hv := (h.pow p).congr (fun i=> div_pow (S (i+1)) (S i) p)
   rw [one_pow] at hv
   obtain ⟨k,hk⟩:= eventually_atTop.mp (hS.and (hv.eventually (ge_mem_nhds (by norm_num : (1:ℝ)<3/2))))
   have hz : 0<q k:= hf _ (hk k le_rfl).1
   have hy(i) (hi:k ≤ i) : (4/3)*q i ≤ q (i+1):= by
      let x:= S i^p; let y:=S (i+1)^p; have hx:0<x:= pow_pos (hk i hi).1 _; have ht:0<y:=pow_pos (hk _ (hi.trans i.le_succ)).1 _
      have hc:y ≤ 3/2*x:= (div_le_iff₀ hx).1 (hk i hi).2
      change 4/3*(Z i/x)≤Z (i+1)/y
      rw [← mul_div_assoc, div_le_div_iff₀ hx ht]; nlinarith only [mul_le_mul_of_nonneg_left hc (he i).1.le,mul_le_mul_of_nonneg_right (he i).2 hx.le] -- first drop and
   have he' (i:ℕ)(hi:k ≤ i) : (4/3 :ℝ)^(i-k)*q k ≤ q i := by
      induction i, hi using Nat.le_induction with
      | base=> simp
      | succ i hi ih=> refine le_trans ?_ (hy i hi); rw [show i+1-k=i-k+1 by omega,pow_succ']; rw [mul_assoc]; gcongr
   have hL : Tendsto (fun i:ℕ=> i-k) atTop atTop:= by refine tendsto_atTop_atTop.mpr ?_; intro b; refine ⟨k+b,fun i hi=>?_⟩; omega
   apply tendsto_atTop_mono' (l:=atTop) ?_ (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)< 4/3) |>.comp hL |>.atTop_mul_const hz)
   filter_upwards [eventually_ge_atTop k] with i hi using he' i hi

variable {G : Gauge} {C : Family G} {W r D} (V : TableTickets C W r D)
local notation "S"=> C.path.levels.S

lemma gel_too_big (C : Family G) (p:ℕ) : Tendsto (fun i=> gel C.path.levels i / (C.path.levels.S.scale i)^p) atTop atTop := by
  apply compare (C.path.levels.S.divergent.eventually_gt_atTop 0) (ratio_rule C.path.levels.fits.mesh)
  intro i; have hx:= zero_lt_one.trans_le (gel_pos C.path.levels i); have hy : (2:ℝ)≤(1+(C.path.levels.params i).columns)*(C.path.levels.params (i+1)).columns := (show 2 ≤ 1+(C.path.levels.params i).columns by linarith [(C.path.levels.params i).columns_ge]).trans (le_mul_of_one_le_right (by linarith [(C.path.levels.params i).columns_ge]) (C.path.levels.params _).columns_ge)
  refine ⟨hx,?_⟩; rw [gel_step,mul_comm 2]; gcongr
include V
lemma juice_too_big (p:ℕ) : Tendsto (fun i=> juice C.path.levels i / (C.path.levels.S.scale i)^p) atTop atTop := by
   apply compare ((S).divergent.eventually_gt_atTop 0) (ratio_rule C.path.levels.fits.mesh)
   intro i; have he:= zero_lt_one.trans_le (juice_pos C.path.levels i); refine ⟨he,?_⟩
   rw [juice_step]; let j := C.path.levels.clock.J (i+1) + 1
   exact mul_le_mul_of_nonneg_right ((show 2 ≤ 64*(W.K j)^2 by nlinarith only [W.prices j]).trans (V.system.costs.cost (i+1))) he.le
-- no receipt that keeps these factors obtains MatrixTicket-level poly prices
omit V
lemma not_fee {f : Filter ℕ}[f.NeBot](h:f≤atTop)(hG:G.Simple)(d e : ℕ) : ¬Wallet f C.path.levels.clock.hatBeta
       (fun k=> C.S.a k^(d-(e+1)) * fare C k d e) := by
    intro hC; have hS := ((S).divergent).mono_left h; have hb : Tendsto C.path.levels.clock.hatBeta f atTop:= tendsto_atTop_add_const_left _ _ (hS.const_mul_atTop (Gauge.slopeConstant_pos hG))
    have ht : Wallet f (S).scale C.path.levels.clock.hatBeta:= (Wallet.const hS C.path.levels.clock.bar).add hS ((Wallet.const hS G.slopeConstant).mul (Wallet.id hS))
    obtain ⟨p,hp⟩:= hC.raise hb ht
    let n:= d-(e+1); let A:=C.S.a (C.ref d)^n; have hA:0<A:=pow_pos (C.S.a_pos _) _
    obtain ⟨k,he,hq,hl⟩:= (hS.eventually_gt_atTop 0 |>.and (((gel_too_big C p).mono_left h).eventually_gt_atTop A⁻¹ |>.and hp)).exists
    have hL: (S).scale k^p < gel C.path.levels k * A := by
       have hp:= (lt_div_iff₀ (pow_pos he p)).mp hq; rw [mul_comm (A⁻¹),← div_eq_mul_inv] at hp; exact (div_lt_iff₀ hA).1 hp
    apply hL.not_ge; apply le_trans _ ((Real.le_norm_self _).trans hl); dsimp only; rw [fare]; let z:= C.S.a k; have hz:0<z:=C.S.a_pos _
    calc
       _ ≤ (gel C.path.levels k * (1+(C.path.levels.params k).columns)) * A:= by gcongr; apply le_mul_of_one_le_right (zero_le_one.trans (gel_pos ..)); linarith [(C.path.levels.params k).columns_ge]
       _ = _ := by unfold A n; rw [div_pow]; field_simp [(C.S.a_pos k).ne']
end YM.OPE.Log
