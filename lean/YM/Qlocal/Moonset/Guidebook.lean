import YM.Qlocal.Moonset.ResetGap
import YM.AllOrder.Wheel.Slip
/-!
Analytic rental price for the through-reset coefficient discrepancy: retention in `Meter`
(real trajectory aperture), only with the hypothesis of actual inherited kinetic discrepancy,
never treating a winding error as contraction.
Does **not** divide by arbitrary powers without paying (`Meter` gates). Does not require
uniform convergence of any series in a small coupling window. Used with the `Income` of the
adjacent forecast step. Implements the real account for every filtered term in `ResetGap`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Moonset
open Function Filter Finset PhysicalNext PhysicalNext.Repeat Fare Lapis
open Lattice RG MeasureTheory Wilson Pressure Gauge Precision
open AllOrder AllOrder.Floe AllOrder.Floe.Pace
open PositionX.Jet AllOrder.Catch AllOrder.Catch.Clock AllOrder.Wheel
open scoped Topology Classical BigOperators ContDiff
variable {ι : Type} {T : Catch.Clock ι}
variable {b bp : ι→ℝ}{p N i k L r:ℕ}{q : ι→Pace.Coin}
open ConnectedActivityE6.Coat
-- hq parent beta *numeric*, not model
abbrev discrepancy (b bp:ι→ℝ)(q:ι → Coin)(k:ℕ):ι→ℝ:=fun i=> (bp i - now (q i) k (b i))/b i
local notation "V"=> T.Meter
local notation "X"=> fun i=> gStep (b i)
local notation "Y"=> fun i=> gStep (bp i)
local notation "A"=> fun i=> wag (q i) r (b i)
local notation "C"=> fun i=> bp i / b i
variable (hT:Hall T r b q) (he:p ≤ r) (hq:T.Meter (discrepancy b bp q r) (graded (p+1)))
    (hP: ∀ᶠ i in T.rail,0<bp i)
include hT he hq
-- t model β, β' relative. Read at coarse using true group fields.Math.Root. Coin ladder paid exactly.
lemma digitizing : TaylorCap T p (fun i=> gStep (b i)) (fun i=>bp i/b i-1) q := by
  refine (hT.logic.zoom he).alteration (hq.eq_mem ?_)
  filter_upwards [hT.tune.one] with i hi
  change (bp i-b i*(1+A i))/b i = bp i/b i-1 - A i
  field_simp; ring
lemma tag_account (i k:ℕ) : TaylorCap T p X (fun m=> (bp m / b m) ^ indexT i k) (fun m => Moonset.forward (q m) i k):= by
 let v: ℝ := indexT i k; let A' := fun x:ℝ => (1+x)^v; have hL:ContDiffAt ℝ ω A' 0 := Pace.nice v
 have h := TaylorCap.process A' hL (digitizing hT he hq) (tendsto_const_nhds.congr' (hT.mild.mono fun i hi=>hi.1.symm)) hT.tune.stepI (hT.tune.one.mono fun i hi=> Fare.gS _ hi|>.1)
 refine h.fit (Eventually.of_forall fun t=>?_ ) (fun j hj=> hT.mild.mono fun i hi=> ?_)
 · unfold A'; simp only [Function.comp_apply]; rw [add_comm,sub_add_cancel]
 let hh:= Act.swell (q i) hj; exact (hh.transit (hi.1.symm ▸ hL)).trans_at (Pace.coin_word v hh hi.1) le_rfl
omit hT he hq
lemma stamp_worth (e k:ℕ)(h δ:ℝ) (hh:0<h) (hq:0<δ) : worth (h*δ) e k= YM.Comparison.RG02.Adjacent.tags 0 e k δ * worth h e k:= by unfold Comparison.RG02.Adjacent.tags worth; rw [zpow_zero,one_mul,inv_pow,mul_pow,mul_pow]; field_simp
lemma action_worth {b bp:ℝ}(hb:0<b)(ht:0<bp)(e k:ℕ): worth (gStep bp) e k=(bp/b)^(indexT e k)* worth (gStep b) e k:= by
 let v:= bp/b; have he':0<v:= div_pos ht hb; have hc: 1+(v-1)=v:= by ring
 have h: b*(1+(v-1))=bp:= by rw [hc]; unfold v; field_simp
 rw [show gStep bp=gStep b*v^(-(1/2:ℝ)) from ?_, stamp_worth _ _ _ _ (Fare.gS _ hb|>.1) (Real.rpow_pos_of_pos he' _), Moonset.tags_rpow e k he']; rw [← h,Hall.bubble hb _ (hc.symm ▸ he'),Pace.rhythm,hc]
-- placement at each Momentum.Note. Cost expression in Meter
lemma gap_fact {e k p:ℕ}{q:Pace.Coin}{b bp:ℝ}(hb:0<b)(ht:0<bp)(hi:e ≤ p): gap p e k (gStep b) (gStep bp) q = ((bp/b)^(indexT e k)-delay (Moonset.forward q e k) (p-e) (gStep b))* worth (gStep b) e k:= by
 let f:=gStep b; unfold gap; rw [action_worth hb ht,sub_mul]; refine congr_arg ((bp/b)^(indexT e k)* worth (gStep b) e k-·) ?_
 unfold delay; rw [Finset.sum_mul]; refine Eq.symm (Finset.sum_bij (fun x _=>x+e) (fun v hv=>?_ ) (fun i hi j hj h=> ?_) (fun j hj=> ?_) fun i hh=> ?_)
 · rw [mem_Icc]; simp only [mem_range] at hv; omega
 · omega
 · rw [mem_Icc] at hj; exact ⟨j-e,by rw [mem_range]; omega, by omega⟩
 rw [Nat.add_sub_cancel]; unfold worth; rw [pow_add]; change _* _ * _ = _; ring

include hT he hq hP
lemma cost_g (k e:ℕ)(he':e ≤ p) : T.Meter (fun i=> gap p e k (gStep (b i)) (gStep (bp i)) (q i)) (graded (p+1)-graded k):= by
 have hs : T.Meter (fun i=> worth (X i) e k) (graded e - graded k):= by simp only [worth, div_eq_mul_inv, ← inv_pow]; exact ((hT.tune.stepI.pow _).mul (hT.tune.starts.pow _)).weak (by unfold graded; linarith)
 let h:= V; apply Meter.weak (Meter.eq_mem (((tag_account hT he hq e k).stamps (p-e) (Nat.sub_le ..)).mul hs) ((hT.tune.one.and hP).mono (fun i hi=> (gap_fact (q:=q i) hi.1 hi.2 he').symm))); unfold graded; rw [Nat.cast_add, Nat.cast_sub he']; push_cast; linarith
-- buying the output width and θ^rank. for all possible orders,k ≤ p+l
variable {P:ι→BudgetPoint} {t δ W:ι→ℝ} (a:ℝ)
open Quipu Quipu.Sonnet
lemma books_charge (G:Gauge) (ha:T.Meter W 0)(ht:T.Meter (fun i=>(P i).threshold) (-(1/2)))(hx:∀ j≤p+L,T.Meter (fun i=> Vase.humid G (P i).power (P i).order j N (P i).B 1 (δ i) a) 0) : 
    T.Meter (fun i=>rent_gap (G:=G) (P i) p N L (gStep (b i)) (gStep (bp i)) (W i) (δ i) a (q i)) (graded (p+1)):=by
   unfold rent_gap; apply Meter.sum; intro j hj; apply Meter.sum; intro k hk; exact Meter.weak (((cost_g hT he hq hP k j (Nat.le_of_lt_succ (mem_range.mp hj))).ab).mul (((ht.pow _).mul (hx k (Nat.le_of_lt_succ (mem_range.mp hk)))).mul ha)) (by unfold graded; linarith)
end YM.Qlocal.Moonset
