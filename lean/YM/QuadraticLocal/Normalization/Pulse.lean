import YM.QuadraticLocal.Feast
import YM.AllOrder.Rosary.Uniform
import YM.QuadraticLocal.Normalization.Audit
/-!
# Charge the failure of the ordinary all-order pre-reset tilt

Use the usual `branch` with the right increment for the *formal* predicted β,
needed also on the cubic-and-higher part. Only on a globally good field
can one be sure that receipt + highH agrees with the full kinetic. This
module charges the leftover via the Soft layer (on actual flags), through
which already marked K have to pass. We can do that by issuing Weaving
jobs for the **zeroed log** at α=Γ, Δ=0: their E labels evaluate identically
to zero (on good masks!). Then carry over their Soft part independently of
all existing log entries, as usual with compression `shelves`. The Hessian
reading is likewise zero here. Doesn't delete any old log term, of any rank.
This is for `PreLease.Internal` and analogous deferred-calibration calculations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Rosary
open Function Filter Set Lattice Wilson RG Ovens
open AnalyticBridge VerifiedReset Collection Quotes Residual WilsonStartup UVNext.PricedKernels Averaging Geo Progress.DirectedRecipe Extra.Iteration Push.BetaTransport
open Till Burn
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {R : PathData G} {c : Clip} {p : BudgetPoint} {σ C Λ H w : ℝ}
    {X : Listing G n} {v : Collection.Source G n} {ι κ : Type}
namespace Guard
open Lapis Herb Weaving Morning
namespace Dusk
open Lattice RG Pressure Push.AbsoluteSums
open PhysicalNext Repeat
-- abbreviations use RAW stamp budget. Price never quoted principal via cancellation.
abbrev nothing (v:Collection.Source G n): Collection.Source G n := {v with logRead:=fun _=>0}
lemma mask_nothing (i:ℕ) (U:Config G n): (X.read (nothing v)).regularOccurrence p i U=0 := by
 change masked p.threshold (X.reg i).support (0:Config G n→ℝ) U = _; by_cases h:Healthy p.threshold (X.reg i).support U; · rw [masked_eq _ _ _ _ h]; rfl
 rw [masked_ne _ _ _ _ h]
lemma supports (h:Collection.Local X p v H w): Collection.Local X p (nothing v) 0 w:=by
 refine ⟨fun _=> ?_, ⟨h.family.sym,h.family.symtest,h.family.meas,h.family.meas_test,h.family.reads,h.family.reads_test,h.family.permit⟩,fun s b=> ?_, ⟨fun _=>0,fun i=> ?_,fun i=>?_⟩, h.expensive⟩
 · exact CouplingShape.reg_const _
 · obtain ⟨Y⟩:= h.transforms s b; exact ⟨⟨Y.ep,Y.kp,Y.reg_site,Y.reg_support,Y.forced_support,Y.forced_inventory,Y.forced_tests,fun i W=> rfl,Y.valuesK⟩⟩
 · exact Progress.DirectedRecipe.no_cost ..
 simp [SumBudget] -- inspect

variable (h:Collection.Local X p v H w) (hG:G.Simple)
include h hG
lemma readNothing : delta (X.read (nothing v))=0:= by
 have he:= Averaging.delta_bound hG ( supports h|>.projects ); have ht:0<p.threshold:= p.threshold_pos; have hx := abs_nonneg (delta (X.read (nothing v))); suffices ht:|delta (X.read (nothing v))|=0 from abs_eq_zero.mp ht; exact le_antisymm (le_of_mul_le_mul_left (by rw [mul_zero]; exact he) (sq_pos_of_pos ht)) hx
variable (hB:R.Bounds c σ C Λ)(hc:Decent c p)(hW: Width p c σ)(hn:20 < n.val)(α:ℝ)
local notation "A"=> shelves X R p
local notation "d"=> Weaving.dawnK R c p X (nothing v) α 0
local notation "P"=> Pipes.pours A d
include hB hn hW hc
lemma neutral_supply: Ensemble p A d 0 w (softNeed G p c σ C α 0):= by
 have h0:= supports h; have ht:= Weaving.ok hG h0 hB hc hn α 0; have hv:= Weaving.members hG h0 hB hc hW hn α 0 (by simp); simp only [regularNeed, mul_zero, zero_mul, abs_zero, add_zero] at hv; exact ⟨ht,hv⟩
lemma hollow : ∀ i:ℕ, ∀ U:Config G n, (A|>.pours d).regularOccurrence p i U=0:= by
 obtain ⟨k,hk,hK⟩:= (neutral_supply h hG hB hc hW hn α).2.1
 intro i U; let o:= ((P).reg i).site; have hx: k i ≤ 0:= (p.loMass _ _ (hk i|>.1)).trans (by simpa [o] using budget_single (hK o) i ); exact abs_eq_zero.mp (le_antisymm (( CouplingShape.mask_cost (hk i) U ).trans hx) (abs_nonneg _))
lemma ex_cost (β:ℝ)(t:ℝ)(U:Config G n): ∑' i,(d).logarithm i U= R.inChannels c p (β+α) U - R.inChannels c p β U - α * ( Collection.receipt R c p U + Rosary.Weaving.highH R p U ):=by
 have hv:= Weaving.symbolizes hG (supports h) hB hc hW hn α 0 U β t; have hh: (A|>.pours d).additive p U=0:=by unfold Activities.additive; simp_rw [hollow h hG hB hc hW hn]; exact tsum_zero
 have hu : (X.read (nothing v)).additive p U=0:=by unfold Activities.additive; simp_rw [mask_nothing]; exact tsum_zero
 have ha: (Collection.vac (nothing v) t)=t:= by simp [vac]
 change _* _ - _ - (A|>.pours d).additive p U+_=t*_ - _- (X.read (nothing v)).additive p U - _-_+_ at hv; rw [hu, hh, readNothing h hG, ha, add_zero] at hv; dsimp only [Progress.DirectedRecipe.trunk,frozen] at hv; linarith


end Dusk
end Guard
end YM.AllOrder.Rosary
