import YM.LocalLTE.Pond.Azure
/-! Budget handoff, oxidizing pre+post affines. No receptive assumptions on stencil prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Collection.Price
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf
open LocalLTE.FrameBox LocalLTE.FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable (G : Gauge) {n : Side} {j:ℕ} {C V: ℝ}
attribute [local instance] Gauge.frobInner
-- uniform over all low rows. weights only station 
open Residual Geo Animals
open Quotes
variable {G}
open Extra.Iteration Urns
variable {t σ C' Λ Δ α k κ a v w u:ℝ} {c:Clip} {L:Side} {p:BudgetPoint} {d N:ℕ}
variable {R:PathData G}(hR:R.Bounds c σ C' Λ) (hv : Width p c σ)(hG:G.Simple)(hn:20<n.val)(hg:32*p.B<n.val) (ht:p.B=Pressure.radiusB t) (hC:p.threshold=Pressure.temp t) (he:p.threshold ≤2*Pressure.fiery G t L)(hx:1 ≤ betaF G t L) (hb:3 ≤ p.B)(hk:Reliable G κ k) (hd:WilsonStartup.Decent c p)
-- Numerics.After.D.D F.bore universe all.Current.True accuracy.
variable (X:Listing G n) (g:Source G n) (P0:ℕ→Pot G n)(V:Tour X d)
include hR hG hd hn
lemma masters (i:EKey n)(α Δ:ℝ)(h:∀ i,p.Regular (X.reg i|>.support) (g.logRead i)) : Comic G (Price.tubeX R p X i) p (archive X R c g α Δ i):=by
    rcases i with i|⟨v,i⟩|⟨v,i⟩
    · exact ⟨rebate_regular _ (h i),rebate_one ..,fun hz x y=>rebate_vanish (X.reg i) hG (h i) hz hn x y⟩
    · exact Comic.move (x:=⟨0,Low.home R i p 0,Low.small_home ..⟩) hG hn (h:=show Comic G _ _ _ from ⟨Low.fresh_regular R c i (0:Site n) hd (factor*Δ),Low.fresh_one R c i (0:Site n) (factor*Δ),fun hx x y=> Low.fresh_vanish R c i (0:Site n) hG hd hx hn (factor*Δ) x y⟩) v _ (Price.lowLoc R p _) rfl -- edit
    · exact Comic.move (x:=⟨0,bloomH R p 0 i,Price.erect R p 0 i (High.small_home ..)⟩) hG hn (h:=show Comic G _ _ _ from ⟨reg_larger (High.fresh_regular R i (0:Site n) hR p (factor*α) (factor*Δ)) (Price.erect R p (0:Site n) i), High.fresh_one R i _ _ _,fun _ x y _ _=> High.fresh_vanish R i (0:Site n) hG hR p (factor*α) (factor*Δ) x y⟩) v _ (Price.ridgeLoc R p _) rfl -- edit
-- actual base cap.Story.Multipliers on x.Stages.∆ separate pricing masks.
include hv
lemma dock (α Δ:ℝ) (h: Meadow.Budget p X.reg g.logRead a) (hΔ:p.threshold^2* |Δ| ≤ a): Stocked p (Price.tubeX R p X) (archive X R c g α Δ) (Price.tH p * regularNeed G p c σ C' α a):= by
    obtain ⟨x,h,hp⟩:=h; let Y:=Collection.quoteE R p c α Δ x (n:=n)
    have h' (i:EKey n):=Collection.Local.quote_regular (X:=X) (v:=g) hG hR hd α Δ (fun i=>(hp i).2) (fun i=> (hp i).1) i
    have hx:= Local.quote_family (X:=X) (v:=g) hR hd hv α Δ (fun i=> (hp i).2) h hΔ
    have hs:0≤ Price.tH p:=Real.exp_nonneg _
    refine ⟨Y,fun i=>⟨(masters hR hG hn hd X g i α Δ (fun i=> (hp i).1)).1,?_⟩,fun i=> budget_mono (budget_scale hs (hx.1 i)) (fun i=> ?_) (fun i=>?_) ⟩
    · rw [Price.boostT X i|>.1]; exact VerifiedReset.sup_larger (h' i) ((Price.boostT ..).2)
    · split
      · exact mul_nonneg (Real.exp_nonneg _) (h' _|>.1)
      exact le_rfl
    rw [← (Price.boostT X i|>.1)] -- edit index
    split
    next hi=>
        rcases i with i|i|i
        · exact le_mul_of_one_le_left (mul_nonneg (Real.exp_nonneg _) (show 0 ≤ Y (Sum.inl i) from (h' _).1)) (Real.one_le_exp (mul_nonneg p.exponent_pos.le (Nat.cast_nonneg _)))
        · exact le_mul_of_one_le_left (mul_nonneg (Real.exp_nonneg _) (show 0 ≤ Y (Sum.inr (Sum.inl i)) from (h' _).1)) (Real.one_le_exp (mul_nonneg p.exponent_pos.le (Nat.cast_nonneg _)))
        exact Price.ridge_w (show _ from (h' (Sum.inr (Sum.inr i))).1) i
    simp

end YM.AnalyticBridge.VerifiedReset.Collection.Price
