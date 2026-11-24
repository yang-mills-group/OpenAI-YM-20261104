import YM.OPE.Strobe.Ball
import YM.OPE.Yarn.Expense
/-! # Accounts at GracesP month. Post-L C. ordering. Spending. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Strobe
open Yarn
open Function Filter Set MeasureTheory Finset Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Overlay
open MergeProof Accent Ribbons ManyCopies MergeProof.Float PhysicalNext.Repeat Lotus Legato Mallow Bandage Patrol Loom
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {I J:Type}[Fintype J][DecidableEq J]{G:Gauge}{n: Side} {C:Family G} {k z i j l m p N d:ℕ}
variable {W r D}{σ χ:ℕ→ℝ} (H:Tune C W r D σ χ)
set_option quotPrecheck false
local notation "P" => C.path
local notation "T" => C.path.levels
local notation "δ" => renal C.path.levels
local notation "η" => near C.path.levels
local notation "ζ" => fly C.path.levels
local notation "ψ" => waybill C.path.levels
local notation "R" => C.path.rep N p
local notation "V" => Site (C.side m p)
local notation "Z" => royal C m p
local notation "r*" => stepUp
open Yarn.SitePlan Next.Rank.Station
local notation "B" => ((fun i=>(C.path.levels.budget i).B))
local notation "X" => (C.path.levels.clock.hatBeta)
variable {φ : Filter I} {k n:I→ℕ}{v w s:I→ℝ}(L: GracesP C φ k n)
local notation "d*" => B
local notation "loc" => (fun i=>C.S.scale (k i))
local notation "a" => (C.path.levels.clock.hatBeta ∘ k)
local notation "sp" => (fun i=>chapter C (k i) (n i))
local notation "κ" => (fun i=>Real.sqrt (C.path.levels.clock.forcedAllowance i))
include H L
lemma control (h:Cheap φ (C.S.scale ∘ k) v): Cheap φ (C.path.levels.clock.hatBeta ∘ k) v:=by
    -- slope compare polynomial in X (tolerance.S).
    have hy : Cheap φ a (C.S.scale ∘ k):= by
       let b:=G.slopeConstant; let c:=C.path.levels.clock.bar; have hb: 0<b:= Gauge.slopeConstant_pos H.tune; have hc:0<c:=(T).clock.bar_pos; apply (Cheap.mul (Bill.const b⁻¹ ((exists_hat C H.tune).comp L.seeks)) (Cheap.id φ a)).norm_le (Eventually.of_forall fun i=>?_)
       change ‖C.S.scale (k i)‖ ≤ ‖b⁻¹*(a i)‖; have he : 0 ≤ C.S.scale (k i):= by have hQ:= scale_mono C.S|>.monotone (Nat.zero_le (k i)); rw [Schedule.scale, Schedule.a_zero,inv_one,Real.log_one] at hQ; exact hQ
       rw [Function.comp_apply,Real.norm_of_nonneg he,Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr hb.le) (zero_le_one.trans ((T).fits.delayed _).le))]; apply le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hc.le) (inv_nonneg.mpr hb.le) : b⁻¹*(b*(C.S.scale (k i))) ≤ _); field_simp
    exact h.enlarge hy
lemma stainBeat (h:Cheap φ (C.S.scale ∘ k) v) : ∀ᶠ i in φ, ‖v i‖*κ (k i) ≤ 1 ∧ ‖v i‖ * Real.exp (-2*(B (k i):ℝ)) ≤ 1:=by
    obtain ⟨t,ht⟩:= control H L h; have hx:= (exists_hat C H.tune).comp L.seeks; filter_upwards [ht,hx.eventually (Extra.Histories.Doors.stain_beats t),(Real.tendsto_log_atTop.comp hx).eventually_ge_atTop (t:ℝ)] with i hi hz hs; let x:= X (k i); have he:0<x:= zero_lt_one.trans ((T).fits.delayed _); have hw:=Real.log_pos ((T).fits.delayed (k i)); have hb : ‖v i‖≤ x^t:= by change ‖v i‖ ≤ ‖(1:ℝ)‖*‖x‖^t at hi; rwa [norm_one,one_mul,Real.norm_of_nonneg he.le] at hi
    have he: Real.exp (-2*(B (k i):ℝ)) ≤ (x^t)⁻¹:= by rw [← Real.exp_log he,← Real.exp_nat_mul,← Real.exp_neg]; apply Real.exp_monotone; let e:=Real.log x; have ht:e^2 ≤ (B (k i):ℝ):= Nat.le_ceil _; change (t:ℝ) ≤ e at hs; change 0<e at hw; nlinarith only [ht,mul_le_mul_of_nonneg_right hs hw.le,sq_nonneg e] -- x overwrite binder hb issue
    refine ⟨(mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg _)).trans ?_ ,?_⟩
    · rw [mul_comm]; exact hz
    apply le_trans (mul_le_mul hb he (Real.exp_nonneg _) (norm_nonneg _ |>.trans hb))
    rw [mul_inv_cancel₀]; exact pow_ne_zero _ (by exact (zero_lt_one.trans ((T).fits.delayed (k i))).ne')
lemma modulo (t:ℕ) (hv:Coins φ (C.S.scale ∘ k) v)(he:∀ᶠ i in φ,0<v i) : Coins φ (C.S.scale ∘ k) (fun i=>payment C (k i) t (v i) false) := Function.const _ (by
   let y i:= Real.exp 100+1+κ (k i); have he' : ∀ i,1 ≤ y i:= fun i=> le_trans (le_add_of_nonneg_left (Real.exp_nonneg _)) (le_add_of_nonneg_right (Real.sqrt_nonneg _)); let u:= C.S.scale ∘ k; let hT:= C.S.divergent.comp L.seeks
   have hh:Coins φ u y:=by
       apply Coins.by_le _ (Eventually.of_forall fun i=> (he' i).trans (Real.le_norm_self _)); have hP := Bill.add (F':=fun i=>κ (k i)) (F:=fun _ : I=> Real.exp 100+1) (Bill.const _ hT); apply hP _ hT; apply (Bill.const (1:ℝ) hT).norm_le
       filter_upwards [stainBeat H L (Bill.const (1:ℝ) hT)] with i ⟨hi,_⟩; simp only [norm_one,one_mul] at hi; rw [norm_one]; exact (Real.norm_of_nonneg (Real.sqrt_nonneg _)).trans_le hi
   exact Coins.mul (Coins.mul (Coins.mul (Bi.const 2 (by norm_num) hT) (columns_p hT H.cuts.toPackage.toTableTickets L.ages)) hv) hh) he
omit H L in
lemma payday (ice:Bool){s:ℝ} (t:ℕ) (A:Family G)(k:ℕ)(he:0<s) : 0<payment A k t s ice∧ payment A k t s ice ≤ payment A k 0 s false:=by
    have hδ:= A.path.levels.params k|>.columns_ge; unfold payment; have hv: Real.exp (-2*(t:ℝ)) ≤ 1:= (Real.exp_le_one_iff).mpr (by simp); simp only [↓reduceIte, Bool.false_eq_true]; split; · exact ⟨by positivity,mul_le_mul_of_nonneg_left (by linarith only [hv,Real.exp_pos 100]) (by positivity)⟩
    exact ⟨by positivity,le_rfl⟩
-- repeg cash needs `t` universal bound for that bill. Applies any number of marks all within same x.
lemma ruby (hv:Coins φ (C.S.scale ∘ k) v)(he:Cheap φ (C.S.scale ∘ k) w) (hw:∀ᶠ i in φ,0<v i) : ∀ᶠ t:ℕ in atTop, ∀ᶠ i in φ, w i ≤ renal C.path.levels (k i)*(near C.path.levels (k i)*v i)*Real.exp ((Loom.count C t (k i):ℝ)/24):= by
    let P' i:=δ (k i)*(η (k i)*v i); let Vp i:=a i; have hz:= C.S.divergent.comp L.seeks --
    obtain ⟨b,hb⟩:= control H L (Cheap.div he (show Coins φ loc P' from Coins.mul (renal_coins hz L.ages) (Coins.mul (near_coins hz L.ages) hv)))
    filter_upwards [eventually_ge_atTop (24*b)] with t ht; filter_upwards [hw,hb] with i hp hi; let x:=Vp i; have h:1<x:= (T).fits.delayed _; have hξ:0 < P' i:= mul_pos ((H.brine (k i)).water _ le_rfl|>.2) (mul_pos ((H.brine (k i)).water _ le_rfl|>.1) hp)
    let a':=(Loom.count C t (k i):ℝ)/24; have hl : b*Real.log x ≤ a':=by
       have hh:t* Real.log x ≤ (Loom.count C t (k i):ℝ):= le_trans (mul_le_mul_of_nonneg_left (Real.log_le_log (zero_lt_one.trans h) ?_) (Nat.cast_nonneg _)) (Nat.le_ceil _); swap
       · unfold Calendar.hatBeta; change (T|>.clock.bar)+G.slopeConstant*C.S.scale (k i)≤ (T|>.clock.bar)+G.slopeConstant*C.S.scale (k i+1); gcongr; exacts [(Gauge.slopeConstant_pos H.tune).le, (scale_mono C.S).monotone (k i|>.le_succ)] -- first unfolds rhs. 
       have hm : 24*(b:ℝ) ≤ t := by exact_mod_cast ht
       unfold a'; linarith only [hh,mul_le_mul_of_nonneg_right hm (Real.log_nonneg h.le)]
    have hc: x^b ≤ Real.exp a':=by rw [← Real.exp_log (zero_lt_one.trans h), ← Real.exp_nat_mul]; exact Real.exp_monotone hl
    change ‖w i/P' i‖ ≤ ‖(1:ℝ)‖*‖x‖^b at hi
    rw [norm_one,one_mul, Real.norm_of_nonneg (by positivity : 0≤x)] at hi; exact (div_le_iff₀ hξ).mp ((Real.le_norm_self _).trans (hi.trans hc)) |>.trans_eq (mul_comm ..)
end YM.OPE.Strobe

