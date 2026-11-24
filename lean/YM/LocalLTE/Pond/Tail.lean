import YM.LocalLTE.Pond.Archive
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
open LocalLTE.FrameBox LocalLTE.FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux Extra.Iteration
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable (G : Gauge) {n : Side} {j:ℕ} {C V: ℝ}
attribute [local instance] Gauge.frobInner
-- uniform over all low rows. weights only station 
open Residual Geo Animals
open Quotes Urns
open Residual Geo
variable {G} {ι : Type*}
-- long path ch. width profit reuse half of Low_budget's remaining. LEGEND.Manifold.
section bill
variable (p:BudgetPoint) (L:ι→ℕ)(g:ι→ℝ) {σ M:ℝ} (h:SumBudget (fun i=>g i*Real.exp (σ/2*L i)) M) (hg:∀ i, 0≤g i) (hσ:0<σ)
include h hg hσ
lemma coach : SumBudget (fun i=> if p.B ≤ L i then g i * Real.exp ((σ/4)*L i) else 0) (Real.exp (-(σ/4)*p.B)*M):=by
   refine budget_mono (budget_scale (Real.exp_nonneg _) h) (fun i=> ?_) (fun i=> ?_)
   · split; exact mul_nonneg (hg _) (Real.exp_nonneg _); exact le_rfl
   split
   next ht=> rw [mul_left_comm (Real.exp _) (g _), ← Real.exp_add]; refine mul_le_mul_of_nonneg_left (Real.exp_monotone (?_)) (hg _); nlinarith only [mul_le_mul_of_nonneg_left (Nat.cast_le (α:=ℝ)|>.mpr ht) hσ.le]
   exact mul_nonneg (Real.exp_nonneg _) (mul_nonneg (hg _) (Real.exp_nonneg _))
lemma driver (D:ι→Support n) (N:ℕ) (hw:p.supportExponent/p.B≤σ/4) (hD:∀ i,p.B*coverNumber p.B (D i)≤p.B*N + L i): ∀ o : Site n, SumBudget (fun i: Seat n ×ι=> if i.1.2=o then p.mass (i.1.spread (D i.2)) (if p.B ≤ L i.2 then g i.2 else 0) else 0) (Quotes.anchoredFee p N*(Real.exp (-(σ/4)*p.B)*M)) :=by
    refine Quotes.channel_mass (σ:=σ/2) L D (fun i=> if p.B ≤ L i then g i else 0) (fun i=> by split_ifs; exact hg i; exact le_rfl) ?_ N (by linarith) hD
    have hz:= Price.coach p L g h hg hσ; simp_rw [ite_mul,zero_mul,show σ/2/2=σ/4 from by ring]; exact hz
end bill

section prices
variable {σ Λ : ℝ} {c:Clip} {R:PathData G} (h:R.Bounds c σ C Λ) (p:BudgetPoint)(X: Listing G n)(Δ α:ℝ) (hw: Width p c σ)
include hw h
local notation "k" => (High.term R)
def slope (p:BudgetPoint)(σ:ℝ):=Real.exp (-(σ/4)*p.B)
def lpTag (i:EKey n):ℕ := Sum.elim id (fun _=>0) i
abbrev Lret (R:PathData G)(c:Clip)(Δ:ℝ)(j:Faces n) := turnFee p * (|Δ| * p.threshold^2) * (|j.2.mark R c| * lowCost G p (j.2.length R))
abbrev Hret (R:PathData G)(α Δ:ℝ)(j:Spikes n) := turnFee p * (|α+Δ| * p.threshold^3) * j.2.price R p
lemma lambC : anchored p (n:=n) (lowEntry G R p) (fun i=>if p.B ≤ i.2.length R then Lret p R c Δ i else 0) (turnFee p * (|Δ| *p.threshold^2) * (Price.slope p σ*lowBase G c p σ C)) :=by
    have ht:= p.exponent_pos; have hs:=p.B_pos; have hn:=hw.2.2
    let w (i:Low):= |i.mark R c| * lowCost G p (i.length R); let g i:= if p.B ≤ Low.length R i then w i else 0
    have he: anchored p (lowEntry G R p) (fun (i:Faces n)=> g i.2) (slope p σ*lowBase G c p σ C):= by
       rw [show (slope p σ*lowBase G c p σ C)=anchoredFee p lowCount*(Real.exp (-(σ/4)*p.B)*(lowFee G p σ* lowerSize c C)) from (by unfold slope lowBase; ring)]
       exact Price.driver p (Low.length R) w (low_budget G p R h) (fun i=> mul_nonneg (abs_nonneg _) (low_nonneg ..)) h.width (fun i:Low=> i.home R p (0:Site n)) lowCount (le_trans (div_le_div_of_nonneg_right (by linarith : p.supportExponent≤p.supportExponent+1) (Nat.cast_nonneg _)) hn) (fun i=> low_geometry p R i _)
    have hv:=turnFee_pos p
    have hx:= Quotes.anchored_scale (by positivity : 0≤ turnFee p*(|Δ| * p.threshold^2)) he; unfold g at hx; simp only [mul_ite,mul_zero] at hx; exact hx
lemma hartC : anchored p (n:=n) (highEntry G R) (fun i=>if p.B ≤ i.2.length R then Hret p R α Δ i else 0) (turnFee p * (|α+Δ| * p.threshold^3) * (slope p σ*highBase G p σ C)):=by
    have ht:=p.threshold_pos; let g i:= if p.B ≤ High.length R i then High.price R i p else 0
    have he: anchored p (highEntry G R) (fun i:Spikes n=>g i.2) (Price.slope p σ*highBase G p σ C):= by
       rw [show (slope p σ*highBase G p σ C)=anchoredFee p highCount*(Real.exp (-(σ/4)*p.B)*(both G p σ*(C+C))) from by unfold slope highBase; ring]
       exact Price.driver p (High.length R) (fun i=>High.price R i p) (high_budget G p R h) (fun i=> High.price_nn ..) h.width (fun i:High=>i.home R (0:Site n)) highCount (le_trans (div_le_div_of_nonneg_right (by linarith : p.supportExponent≤p.supportExponent+1) (Nat.cast_nonneg _)) hw.2.2) (fun i=> high_geometry p R i _)
    have hv:=turnFee_pos p; have hx:= Quotes.anchored_scale (by positivity : 0≤ turnFee p*(|α+Δ| * p.threshold^3)) he; unfold g at hx; simp only [mul_ite,mul_zero] at hx; exact hx
lemma lBase : anchored p (n:=n) (lowEntry G R p) (fun i => |i.2.mark R c|) (anchoredFee p lowCount * lowerSize c C):= by
   have hp := h.width
   refine Quotes.channel_mass (σ:=σ) (Low.length R) (fun i:Low=>i.home R p (0:Site n)) (fun i:Low=>|i.mark R c|) (fun i=>abs_nonneg _) (budget_mono (lower_budget G R h) (fun i=>mul_nonneg (abs_nonneg _) (Real.exp_nonneg _)) ?_) _ ?_ (fun i=>low_geometry p R i _)
   · intro i; refine mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg (α:=ℝ) (Low.length R i)))) (abs_nonneg _); linarith
   refine le_trans (div_le_div_of_nonneg_right (by linarith : p.supportExponent ≤ p.supportExponent+1) (Nat.cast_nonneg (α:=ℝ) _)) (hw.2.2.trans ?_); linarith
lemma hBase : anchored p (n:=n) (highEntry G R) (fun i=> i.2.charge R) (anchoredFee p highCount * (C+C)):=by
   have hp := h.width
   have hh:SumBudget (fun i:High=>(High.term R i).budget σ) (C+C):= Cost.sum h.three h.four
   have hx (i:High): 0≤ i.charge R:= Finset.sum_nonneg fun i _=> abs_nonneg _
   refine Quotes.channel_mass (σ:=σ) (High.length R) (fun i:High=>i.home R (0:Site n)) (High.charge R) hx (budget_mono hh (fun i=>mul_nonneg (hx _) (Real.exp_nonneg _)) (fun i=> ?_)) _ ?_ (fun i=>high_geometry p R i _)
   · refine mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))) (hx i); linarith
   refine le_trans (div_le_div_of_nonneg_right (by linarith : p.supportExponent ≤ p.supportExponent+1) (Nat.cast_nonneg (α:=ℝ) _)) (hw.2.2.trans ?_); linarith
end prices
end YM.AnalyticBridge.VerifiedReset.Collection.Price
