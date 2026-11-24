import YM.RG01Estimate.LeasePipe
/-! # authorization conditioned on Cost slack -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Censor.Toft
open Function Filter Set Lattice Wilson RG Progress.DirectedRecipe AnalyticBridge VerifiedReset Collection Averaging Ovens Ovens.Pipes
   Payments Extra.Iteration Pilgrim Push.BetaTransport Push Push.AbsoluteSums
open Quotes Fresco
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{n:Side}{p:BudgetPoint}{X:Listing G n}{d:Collection.Source G n}
      {u δ H T α w w' k W σ C Λ :ℝ} {c : Clip} {R:PathData G}
lemma reset_gain {p:BudgetPoint} : 1 ≤ Quotes.resetFee G p:=by
   unfold Quotes.resetFee Residual.resetLoss; have he:=p.exponent_pos
   exact one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by positivity)) (by linarith only [Residual.multiplier_nonneg G p])
lemma soft_gain (p:BudgetPoint) (G : Gauge) : 1 ≤ Quotes.softReset G p 1:= by
    unfold Quotes.softReset Footprint.payment Footprint.degreeIncome Footprint.spread Animals.ballCost
    have he:=p.exponent_pos
    have hL:1 ≤ Residual.resetLoss G p:=by unfold Residual.resetLoss; linarith only [Residual.multiplier_nonneg G p]
    have hx : 1 ≤ Real.exp ((p.supportExponent+1)*81):=Real.one_le_exp (by positivity)
    have hp : 1 ≤ (1- Real.exp (-1:ℝ))⁻¹ := (one_le_inv₀ (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num)))).mpr (sub_le_self _ (Real.exp_nonneg _))
    refine one_le_mul_of_one_le_of_one_le ?_ hp
    refine one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by simpa using hx) hL) ?_) ?_
    · norm_cast; rw [one_mul]; exact one_le_pow₀ (by omega)
    simp only [inv_one,one_pow,one_mul]; exact one_le_mul_of_one_le_of_one_le (by norm_num [Nat.factorial]) (Real.one_le_exp zero_le_one)
lemma soft_cubes (p:BudgetPoint) (G:Gauge) (H:ℝ) : Quotes.softReset G p H=H*Quotes.softReset G p 1:=by unfold Quotes.softReset Footprint.payment Footprint.degreeIncome; ring

-- revenue offset linear. Use stock reserves ON full assembly.
lemma reprices (g:G.Simple) (he : Local X p d H w) (hx:R.Bounds c σ C Λ)(hC: WilsonStartup.Decent c p)(hs:Geo.Width p c σ) (α v:ℝ)(hv:p.threshold^2*|v| ≤ H):
    let t:=fill X R c p d α v; let r := shelves X R p; (r.pours t).EBound p (regularNeed G p c σ C α H) ∧
      ∃ s u:ℕ→ℝ,softCost p r s (softNeed G p c σ C α H)∧hardCost p r u w∧Payments.rooted t u s:=by
    intro t r
    obtain ⟨u,hu,hb⟩:=he.cheap
    obtain ⟨k,hk,hK⟩:=he.expensive
    obtain ⟨hE,hL⟩:= Local.quote_family hx hC hs α _ hu hb hv
    let Y:= numbering (LKey n)
    have hQ (i : ℕ) := Local.quote_soft (R:=R) (v:=d) (c:=c) g α v hu he.smooth (Y i)
    exact ⟨⟨_,fun i=> Local.quote_regular g hx hC α v hu he.smooth (numbering _ i),fun x => Cost.equiv (numbering _) (hE x)⟩,
         _,k,⟨fun i=> (norm_nonneg _).trans (hQ i 1),fun x=> Cost.equiv Y (hL x)⟩,⟨fun i=> (hk i).1, hK⟩,fun i V=> ⟨(hk i).2 V,hQ i V⟩⟩
lemma budgets (hc:0 ≤ C)(hp:0<σ)(hu:0 ≤ u)(ht:H+u≤ T) (α:ℝ) : regularNeed G p c σ C α H + u ≤ regularNeed G p c σ C α T ∧
    softNeed G p c σ C α H+u ≤ softNeed G p c σ C α T := by
    have hr:= p.threshold_pos
    have hQ:1 ≤ Quotes.resetFee G p:= reset_gain
    obtain ⟨hL,hH,hG⟩:= budget_pos p G c hp hc
    have hv:H ≤ T:=by linarith only [hu,ht]
    unfold regularNeed softNeed
    constructor
    · have he := mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_right hv hL) (mul_le_mul_of_nonneg_right (add_le_add_right hv (|α| * p.threshold^3)) hH)) (turnFee_pos p).le
      linarith only [mul_le_mul_of_nonneg_right hQ (sub_nonneg.mpr hv),ht,he]
    rw [soft_cubes p G H,soft_cubes p G T]
    have hh:hitNeed p G α H ≤ hitNeed p G α T:= by unfold hitNeed; gcongr; exact pair_nonneg ..
    linarith only [mul_le_mul_of_nonneg_right hh hG, mul_le_mul_of_nonneg_left (soft_gain p G) (sub_nonneg.mpr hv), ht]
end YM.RG01Estimate.Censor.Toft
