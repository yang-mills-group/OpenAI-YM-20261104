import YM.RG01Estimate.CensorCost
import YM.RG01Estimate.PipeArithmetic
/-!
 # Seal. PreVac Export X,a,e MUST one assignment pp. Rα true stack. D determined
 from second (same density) via witness, called at exact arrangement. Dpred chosen projection
 on model contributions at this stage (OR adjusted: version using arbitrary nearly ΔP with
 fee allowance). Projection model independent of measured e; hnm can charge.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Censor.Toft
open Function Filter Set Lattice Wilson RG Progress.DirectedRecipe AnalyticBridge VerifiedReset Collection Averaging Ovens Ovens.Pipes
   Payments Extra.Iteration Pilgrim Push.BetaTransport Push Push.AbsoluteSums
open Quotes Fresco
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{n:Side}{p:BudgetPoint}{X:Listing G n}{d a b:Collection.Source G n}
      {α β τ D Δ w σ C Λ H T k u v ε δ y γ :ℝ} {c : Clip} {R:PathData G}
      (g:G.Simple) (h:Local X p d (u+v) w)(he:Local X p a u w)(hr:Local X p b v w)(hh:b.logRead=d.logRead-a.logRead)
-- Δ taken = Project(d) +- spatial; `pred` = Project(a). Include calibration consumption.
include g h he hr hh
lemma shift_prices : let M:=delta (X.read a)
    let Y:=p.threshold^2 * |Δ-delta (X.read d)|
    p.threshold^2* |M| ≤ u ∧ p.threshold^2*|Δ-M| ≤ v+Y ∧ p.threshold^2*|Δ| ≤ u+(v+Y):=by
   intro M Y; let Gx:=delta (X.read b); let s:=Δ-delta (X.read d)
   have ht: Δ - M = Gx+s := by have := polarized_gain g h he hh; unfold Gx s M; linarith only [this]
   have hQ:= delta_bound g he.projects; have hv:= delta_bound g hr.projects
   have hx:p.threshold^2*|Δ-M| ≤ v+Y := by rw [ht]; unfold Y; apply le_trans (mul_le_mul_of_nonneg_left (abs_add_le ..) (sq_nonneg _)); rw [mul_add]; exact add_le_add hv le_rfl
   exact ⟨hQ,hx, (mul_le_mul_of_nonneg_left (show |Δ| ≤ |M| + |Δ-M| from by simpa using abs_add_le M (Δ-M)) (sq_nonneg _)).trans (by rw [mul_add]; exact add_le_add hQ hx)⟩

variable {hn:20<n.val}(Q:Pilgrim p n hn)(hx:R.Bounds c σ C Λ)(hC: WilsonStartup.Decent c p)(hs:Geo.Width p c σ)
    (hU: u+v + p.threshold^2 * |Δ-delta (X.read d)| + priceWrap G p (Δ-delta (X.read d)) hn ≤ H) -- need var
    (hF:Fees G p c σ C α H w δ γ)

def stamp (a b d : Collection.Source G n)(R:PathData G)(X:Listing G n)(c:Clip)(α Δ:ℝ) :=
   let M:= delta (X.read a); let Y:= fill X R c p d α Δ
   Fresco.pour Q (Δ-delta (X.read d)) (fill X R c p a α M) (fill X R c p b 0 (Δ-M)) Y

include Q hx hC hs hF hU
-- t.log sum of orig (noncanonical Δ) converges. E payment and support
lemma seals:
    let M:=delta (X.read a); let Y:=p.threshold^2 * |Δ-delta (X.read d)|
    let _Δ₀:=Δ-delta (X.read d)
    let q:= regularNeed G p c σ C 0 (v+Y)
    let T:= combine Q (shelves X R p)
    let W:=fill X R c p d α Δ
    let T':=stamp Q a b d R X c α Δ
    Ingredients T T' p δ γ ∧ (((shelves X R p).pours (fill X R c p a α M)).EBound p (regularNeed G p c σ C α u)) ∧
      (((shelves X R p).pours (fill X R c p b 0 (Δ-M))).EBound p q) ∧ (∃ (k₀ : ℕ → ℝ), softCost p (shelves X R p) k₀ (softNeed G p c σ C α (u+(v+Y))) ∧ ∀ i U, ‖W.logarithm i U‖ ≤ k₀ i) :=by
    intro M Y Δ₀ q T W T'
    obtain ⟨hf,h',hk⟩:= shift_prices (Δ:=Δ) g h he hr hh
    obtain ⟨ht,s,f,hs',hh',hp⟩:= reprices g he hx hC hs α M hf
    have h₁ : v ≤ v+Y:= le_add_of_nonneg_right (by unfold Y; positivity)
    have hg:= VacuumListing.relax p hr h₁ (le_refl _)
    obtain ⟨ht',u',k,hπ,hξ,hQ⟩:= reprices g hg hx hC hs 0 (Δ-M) h'
    obtain ⟨heY,s₀,u₀,hS,hκ,hW⟩:= reprices g (VacuumListing.relax p h (add_le_add_right h₁ u) (le_refl _)) hx hC hs α Δ hk
    obtain ⟨hV,hΨ⟩:= Toft.budgets (p:=p) (c:=c) (Cost.nonneg hx.three) hx.width (wrap_nn G p Δ₀ hn) (show u+(v+Y)+priceWrap G p Δ₀ hn ≤ H by rw [← add_assoc u]; exact hU) α
    obtain ⟨m,κ,hm,hJ⟩:= hF.hard
    refine ⟨?_,ht,ht',s₀,hS,fun _ _=>(hW ..).2⟩
    obtain ⟨f,hB,hQ'⟩:= Fresco.budgets (b:=fill X R c p d α Δ) (d:=fill X R c p a α M) (c:=fill X R c p b 0 (Δ-M)) (L:=shelves X R p) Q (Δ:=Δ₀) hS hκ hW
    let F:= Fresco.mixes Q (he.fittings g hx hC hn α M) (hr.fittings g hx hC hn 0 (Δ-M)) (h.fittings g hx hC hn α Δ) Δ₀
    refine Payments.tender F (Time.E_rises (logistics Q ht ht').1 ((le_trans (by unfold regularNeed Δ₀; rw [abs_zero]; apply le_of_eq; ring) hV).trans hF.regular)) hκ (⟨hB.1,fun i=>budget_loosen (hB.2 i) (hΨ.trans hm)⟩:softCost p T f m) hQ' hJ

-- exact polynomial equality on REAL group (including tag changes still to own compatibility).
lemma bless (U:Config G n):
    let Y:=combine Q (shelves X R p); let T':=stamp Q a b d R X c α Δ; let T:= trunk R c p Y T' (β+α+Δ) (vac d τ)
    T.eval U * Real.exp (∑' i,T'.logarithm i U) = earlyValue X R c p d β τ α U :=by
   intro Y T' T
   obtain ⟨ht,hL,hK,b',hf,hM⟩:= seals g h he hr hh Q hx hC hs hU hF
   let P:= fill X R c p d α Δ; let hA:= Payments.drop_reserve p _ hf.1 hf.2
   let L:= shelves X R p
   have hp : Summable b':= Activities.summable_charge L.sites hf.1 hA
   have he':Summable (fun i=> P.logarithm i U):= Summable.of_norm_bounded hp (fun i=> hM i U)
   have hw := assigned_gain Q (Δ-delta (X.read d)) U hL hK (regular_sub h he R c α Δ (delta (X.read a)) hh) he'
   let Tβ:= (frozen X R c p d β τ); let H' := trunk R c p L P (β+α+Δ) (vac d τ)
   have hT:T.exponent U + (∑' i,T'.logarithm i U) = Tβ.exponent U - α*receipt R c p U:= by
       rw [← residual (β:=β) (τ:=τ) g h U hn hx hC hs α Δ];
       change _ - _ - (Y.pours T').additive p U + _ = (_ - _ - (L.pours P).additive p U) + _ + _ -- fix
       have hw : ((L.pours P).additive p U) + (∑' i,T'.logarithm i U) = (((Y).pours T').additive p U)+(∑' i,P.logarithm i U)+(Δ-delta (X.read d))* (∑ o: Site n, heads p o U):= hw
       dsimp only [T,P,L,trunk] at *; linarith only [hw]
   rw [Rep.eval, mul_right_comm _ (T.activities.gas T.p U), ←Real.exp_add,hT]
   rw [earlyValue,Rep.eval,mul_right_comm _ (Tβ.activities.gas _ _)] -- notation
   rw [← Real.exp_add,neg_mul,sub_eq_add_neg]; rfl
end YM.RG01Estimate.Censor.Toft
