import YM.LocalLTE.Pond.Tickets
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
open Quotes Urns
variable {G}
-- tape paths. High PAY.R.number. Low stays. Post Forecast uses δ props.
variable (R:PathData G)(c:Clip)(p:BudgetPoint)(j:ℕ) (κ:ℝ)
def swan (o:Site n)(Δ:ℝ)(i:Low): Config G n→ℝ:= if Low.length R i < p.B then shave (cane o) (p.B-1) κ (pie j+1) (Low.fresh R c i o Δ) else 0
def craneH (o:Site n)(α Δ:ℝ)(i:High): Config G n→ℝ:= if High.length R i < p.B then shave (cane o) p.B κ (pie j+1) (High.fresh R i o α Δ) else 0
-- high output with fault.Same enrollment. moves supports depending ONLY on committed path. true hangs.
def bloomH (o:Site n)(i:High):= if High.length R i < p.B then neighbors (2*p.B) o else High.home R i o
lemma erect (o:Site n)(i:High) : High.home R i o ⊆ bloomH R p o i:=by
    unfold bloomH; split
    next h=> exact (tightH p R o i h.le).trans (Corona.halo_mono (by omega) (Finset.Subset.refl _))
    exact Finset.Subset.refl _
variable {R c p κ j} {v D d E:ℝ}
-- short cost. desire α fixed after L; ≤exp l. Prune doesn't depend c except M qua arcs.
def Found (G:Gauge)(L:Side)(κ:ℝ)(j p i:ℕ)(t:ℝ) : Prop := ∀ (n:Side) (a:ℕ),a = Pressure.radiusB t → 32*a < n.val → ∀ (c:Clip) (R:PathData G) {σ C Λ}, R.Bounds c σ C Λ → ∀ (P:BudgetPoint),P.power=p→P.order=j→P.B=a→ P.threshold=Pressure.temp t→ P.threshold ≤2*Pressure.fiery G t L →3 ≤ P.B → WilsonStartup.Decent c P →∀ (Δ α:ℝ)(o:Site n),
    let V:= betaF G t L ^ Urns.dust i
    (∀ d:Low,d.length R < P.B → P.supBounds o (d.home R P o) (d.fresh R c o Δ - swan R c P i κ o Δ d) ((|Δ| * |d.mark R c|)*V)) ∧
    ∀ d: High, d.length R < P.B→P.supBounds o (bloomH R P o d) (d.fresh R o α Δ - craneH R P i κ o α Δ d) ((|α+Δ| * d.charge R) * V)
lemma funded (hR : Reliable G κ v) (L:Side)(j p i:ℕ): ∀ᶠ t in atTop, Found G L κ j p i t:=by
    let Q:=pie i+1; let k:=Q+j;
    obtain ⟨V,hV,H⟩:= highs G L k; obtain ⟨U,hU,H'⟩:= plainly G L k; obtain ⟨C,hC,hX⟩:= proxyV G k
    have hv:0+clr * Q<Urns.dust i:= by unfold Q clr Urns.dust chip pie; push_cast; linarith
    have hz: Rate G L 0 fun t=>(2*radiusB t:ℕ):=by push_cast; exact Rate.mul_left Rate.radius_price _
    filter_upwards [LocalLTE.FrameBox.Hall.prunes G L j p Q hz hR (by norm_num [clr]: -(7/16:ℝ)≤clr) (by norm_num [clr]) ((Rate.const C).add hU) hv,Hall.prunes G L j p Q hz hR (by norm_num [clr]: -(7/16:ℝ) ≤ clr) (by norm_num [clr]) hV hv, (Rate.power (G:=G) (L:=L) (a:=clr)).below (by norm_num [clr]) 1 zero_lt_one] with t hu hh hx n a hq hP c R σ C' Λ hRf P hp hj hB ht hy h ha Δ α o d
    have hy':= P.B_pos; constructor
    · intro d hd; let b:=Low.fresh R c d o Δ; rw [swan,if_pos hd, tightL P R o d hd.le]; refine hu P hp hj ht hy _ _ (by omega) (by omega) _ _ (by omega) (by omega) _ b (lousy P c R o h ha d Δ hd) _ (mul_nonneg (abs_nonneg _) (abs_nonneg _)) ?_
      intro x hx'; have hv:‖x‖≤1:= hx'.le.trans ((le_abs_self _).trans hx); have h:= ((hX n o R d x hv).separating (H' t n o R d (by omega) x hv)).smul (Δ*d.mark R c); rw [Real.norm_eq_abs,abs_mul] at h; exact h
    intro d hd; unfold bloomH craneH; rw [if_pos hd,if_pos hd]; let f:= d.fresh R o α Δ
    refine hh P hp hj ht hy _ P.B (by rw [hB,hq]) (by omega) _ _ (by omega) (by omega) _ f (reg_larger (d.fresh_regular R o hRf P _ _) (tightH P R o d hd.le)) _ (mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun i _=> abs_nonneg _)) ?_
    intro x hp; have hz:= (H t n o R d (by omega) x (hp.le.trans ((le_abs_self _).trans hx))).smul (-(α+Δ)); rw [Real.norm_eq_abs,abs_neg,← mul_assoc] at hz; exact hz
end YM.AnalyticBridge.VerifiedReset.Collection.Price
