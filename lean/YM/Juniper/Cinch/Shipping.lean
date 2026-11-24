import YM.Juniper.Cinch.Receipt
set_option autoImplicit false
noncomputable section
namespace YM.Juniper.Cinch
open Function Filter Metric Lattice Wilson RG PhysicalNext PhysicalNext.Repeat
open Push Push.AbsoluteSums AnalyticBridge VerifiedReset Collection Averaging
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G: Gauge}{c:Side}{X:Support c}{W:BudgetPoint}
open Quotes Finset Ovens Ovens.Pipes Progress.DirectedRecipe Payments Further.LogJets Pressure
open Residual Geo
set_option quotPrecheck false
variable {δ ε b v w τ σ t u H : ℝ}{clip:Clip}{κ : ℝ}{P Q: Stage}
-- +2 cost before reach L2: no extra markets if softBudget at least linear shares.
section wages
lemma reset_pos : 1 ≤ resetFee G W := by
   have he : 1 ≤ resetLoss G W:= by unfold resetLoss; linarith only [multiplier_nonneg G W]
   unfold resetFee; apply one_le_mul_of_one_le_of_one_le _ he; exact Real.one_le_exp (by have h:=W.exponent_pos; positivity)
lemma soft_le : 1 ≤ softReset G W 1:= by
   have he:1 ≤ resetLoss G W:= by unfold resetLoss; linarith only [multiplier_nonneg G W]
   have h := W.B_pos; have hp : 1 ≤ Footprint.spread 1 (4*W.B+2):= by unfold Footprint.spread Animals.ballCost; exact Nat.succ_le_of_lt (by positivity)
   unfold softReset Footprint.payment Footprint.degreeIncome
   have hx: 0 < 1-Real.exp (-1):= by exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
   refine one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le ?_ (by exact_mod_cast hp)) ?_) ((one_le_inv₀ hx).mpr (by linarith only [Real.exp_pos (-1)]))
   · rw [mul_one]; exact one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by have h:=W.exponent_pos; positivity)) he
   norm_num [Nat.factorial]; have hg:= Real.one_le_exp (zero_le_one); linarith
lemma airy : softReset G W b= b*softReset G W 1:= by unfold softReset Footprint.payment Footprint.degreeIncome; ring
lemma levels {φ :ℝ} (hg:0<σ)(hp:0 ≤ φ) (he:0≤b)(hu:b≤H) (Q: BudgetPoint) :
   regularNeed G Q clip σ φ ε b+(H-b) ≤ regularNeed G Q clip σ φ ε H ∧ softNeed G Q clip σ φ ε b+(H-b) ≤ softNeed G Q clip σ φ ε H∧ 0 ≤ softNeed G Q clip σ φ ε b:= by
    obtain ⟨h',hh,hx⟩:= budget_pos Q G clip hg hp; have ht:=turnFee_pos Q; have hr:=Q.threshold_pos; have hH:=pair_nonneg G Q; let s: ℝ→ℝ:= softReset G Q
    unfold regularNeed softNeed
    have he':1≤resetFee G Q:=Cinch.reset_pos; have hv : hitNeed Q G ε b ≤ hitNeed Q G ε H := by unfold hitNeed; gcongr
    have hK:0≤ hitNeed Q G ε b:= by unfold hitNeed; positivity
    have hS:1 ≤ s 1:= Cinch.soft_le; refine ⟨by linarith only [mul_le_mul_of_nonneg_right he' (sub_nonneg.mpr hu),mul_nonneg (mul_nonneg ht.le (sub_nonneg.mpr hu)) h',mul_nonneg (mul_nonneg ht.le (sub_nonneg.mpr hu)) hh],?_,?_⟩
    · rw [airy (b:=b),airy (b:=H)]; linarith only [mul_le_mul_of_nonneg_right hv hx, mul_le_mul_of_nonneg_left hS (sub_nonneg.mpr hu)]
    rw [airy]; exact add_nonneg (mul_nonneg he (zero_le_one.trans hS)) (mul_nonneg hK hx)
lemma disappears (n:ℕ) (h:Rates n δ H b κ)(hz:0≤v)(hh:v≤b) : Rates n δ H v κ:= by
    have hp: inflation H v κ≤ inflation H b κ:= by unfold inflation; linarith only [hh]
    have h' := (Real.exp_lt_one_iff.mpr (by norm_num : -(1:ℝ)<0)); refine ⟨h.heading,h.hard,hz,hh.trans h.soft_limit, (mul_le_mul_of_nonneg_left hp (by positivity)).trans h.capital,?_⟩
    apply le_trans _ h.returns; apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _); gcongr
end wages
lemma soft_budget (n:Side)(d:ℝ): 0≤ forecastW G n W d:= by
   unfold forecastW Pylon.droop Pylon.headBill; have he:= pair_nonneg G W; positivity
variable {Y Y': Listing G c} {f g : Collection.Source G c} (h : Collection.Local Y W f b v) (hB:Collection.Local Y' W g b ε)
   {α r Δ η φ Λ θ : ℝ}{R:PathData G} (hG:G.Simple)(hw: Geo.Width W clip σ)(hv:R.Bounds clip σ φ Λ)(hf:WilsonStartup.Decent clip W) (hk:20<c.val)
-- +1 arithmetic for ALL proposals with preproof Ready. Keep cost slack at least 1/2 used below in shipped. Exponential converter upcoming.
include h
omit h in
lemma lode (hv:0<σ)(hS:0≤φ)(hb:0≤ b)(hu : b≤ H)(hx : forecastW G c W t ≤ H-b)(hh: Fees G W clip σ φ α H v w δ) : regularNeed G W clip σ φ α b+forecastW G c W t ≤ w ∧ ∃ κ,Rates W.B δ v (softNeed G W clip σ φ α b+forecastW G c W t) κ:= by
   obtain ⟨m,κ,hm,h'⟩:= hh.hard; obtain ⟨ha,hf,hy⟩:= levels (clip:=clip) (ε:=α) (G:=G) hv hS hb hu W; exact ⟨(add_le_add le_rfl hx|>.trans ha).trans hh.regular,κ, Cinch.disappears W.B h' (add_nonneg hy (soft_budget c t)) ((add_le_add le_rfl hx|>.trans hf).trans hm)⟩
lemma enlarge {H}(he:b ≤ H): Collection.Local Y W f H v:=by
   obtain ⟨k,hk,hB⟩:=h.cheap; exact { h with cheap:=⟨k,hk, fun i=> budget_loosen (hB i) he⟩ }
include hw hf hv hk hG
local notation "Λ'"=> Averaging.delta (Y.read f)
local notation "Φ"=> forecastW G c W
lemma financed (T:Pylon W c) (hh: Fees G W clip σ φ α H v w δ) (H₀:ℝ) (hu:H₀≤H) (hz : b ≤ H₀)(he: W.threshold^2 * |Δ| ≤ H₀)(ht : forecastW G c W (delta (Y.read f)-Δ) ≤ H-H₀) : let p:= lacquer T f Y R clip α τ r Δ
    Ingredients (adobe (shelves Y R W) T) (flint T (Λ'-Δ) (fill Y R clip W f α Δ)) W w δ ∧ p.eval=earlyValue Y R clip W f r τ α∧ p.activities.Valid W w δ:= by
   intro p; have hm:= enlarge h (H:=H₀) hz; obtain ⟨hA,k,H⟩:= lode hv.width (budget_nonneg hv.three) hm.H_nonneg hu ht hh -- check
   exact ⟨Cinch.fueled T hm hG hw hv hf he hk hA H,Cinch.velvet T hm hG hw hv hf he hk hA H⟩
end YM.Juniper.Cinch
