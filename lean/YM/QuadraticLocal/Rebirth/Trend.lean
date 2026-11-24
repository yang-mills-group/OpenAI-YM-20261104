import YM.QuadraticLocal.Rebirth.Balance
/-!
## Actual coupling difference can be assigned highest degree stamps on this real chart.

Requires transport value `W.Hall` and true `g'=g(1+D)^(-1/2)` with error priced
 against predictor, never uses that the coupling Germ of the Caliber
 extended to this numerical argument predict the OPERATOR exactly. Estimates
 uniform any number of offsets ≤ request, for all admitted epochs on
 the rail. Calendar purchase still needed & non-growing setup assumptions
 separately checked by `WheelP`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Rebirth
open Function Filter Finset Lattice RG Wilson Marker
open Comparison.RG02 Comparison.RG02.Adjacent
open Pressure ConnectedActivityE6 AllOrder AllOrder.Catch
open AllOrder.Wheel AllOrder.Floe Next.Scheduling
open PositionX.Jet AllOrder.Response PositionX.Gauss
open AllOrder.Laplace AllOrder.Laplace.SigmaP
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open Chart
namespace Trend
open PhysicalNext Repeat
variable {ι:Type} (Z:AllOrder.Catch.Clock ι)
variable {Q:ι→Pace.Coin}{u u':ι→ℝ}{L k:ℕ} (s:ℤ)
    (hq : ∀ i,Q i 0=0) (he: k ≤ L)
    (H: Wheel.Hall Z L u Q)
set_option quotPrecheck false
local notation "G"=> Coat.gStep
local notation "g"=> (fun i=> G (u i))
local notation "f"=> (fun i=> G (u' i))
local notation "F"=> ( fun i :ι=> u' i/u i-1 )
local notation "Φ"=> (fun i=> u' i-Wheel.now (Q i) L (u i))
variable (hpos:∀ᶠ i in Z.rail,0<u' i)
-- required one extra inverse cost of time.Demand larger vacuum order when needed.
variable (hp: Z.Meter (fun i=> u' i-Wheel.now (Q i) L (u i)) (graded (k+1) +1))
local notation "r" => ( Z.rail )
local notation "T"=> ( Z.Meter )
local notation "v"=> (graded (k+1))
include H hpos hq hp he
lemma draft : TaylorCap Z k (g) (fun i=>u' i/u i -1) Q:=by
    have ht:=(H.logic).zoom he; refine ⟨ht.steps, fun j hj=>?_⟩; let f₁ i:=Wheel.wag (Q i) L (u i); let α i:= delay (Q i) j (g i); have hm:T (fun i=> F i-f₁ i) (graded (j+1)):= by
       refine ( (hp.mul (H.tune.stepI.pow 2)).weak ?_ ).eq_mem ?_
       · unfold graded; push_cast; have hw: (j:ℝ) ≤ k:= (by exact_mod_cast hj); linarith
       filter_upwards [H.tune.one] with i hi
       let a:=u i; let d:=u' i; let e:=g i; let b:=f₁ i; have ha:0<a:=hi; change (d-a*(1+b))*e^2=d/a-1-b; have hn:e^2*a=1:= Fare.gS (u i) hi|>.2; field_simp; linear_combination (d-a*(1+b))*hn
    let hq:=hm.add (ht.stamps j hj); exact hq.eq_mem (Eventually.of_forall fun i=> sub_add_sub_cancel (F i) (f₁ i) (α i))
lemma records : TaylorCap Z k (g) (fun i=> (f i/g i)^s) (fun i=> Pace.ladder (grade s) (Q i)):= by
    let f'' (x:ℝ):=(1+x)^(grade s); let Ux := fun i=> f'' (F i); let hz:= eo_Act k (Pace.nice (grade s)); have hf:= draft Z hq he H hpos hp
    have hh : Tendsto (fun i=> Q i 0) (r) (𝓝 0):= tendsto_const_nhds.congr' (Eventually.of_forall fun i=> (hq i).symm)
    apply ( hf.process f'' (Pace.nice (grade s)) hh H.tune.stepI ( H.tune.one.mono fun i hi=> Fare.gS _ hi|>.1 ) ).fit
    · filter_upwards [H.tune.one,hpos] with i hi hx; let d:=F i; have hk: 1+d=u' i/u i:=(by unfold d; ring); have he : 0<1+d:=hk.symm ▸ div_pos hx hi; have hh: f i/g i=(1+d)^(-(1/2:ℝ)):= by
          apply (div_eq_iff (Fare.gS _ hi|>.1.ne')).mpr; let a:=u i; change G (u' i)=_; rw (occs:=.pos [1]) [show u' i=u i*(1+d) by rw [hk]; field_simp]; exact (Hall.bubble hi d he).trans (mul_comm ..)
      unfold Function.comp; change (1+d)^grade s= (f i/g i)^s; rw [hh]; unfold Chart.grade; rw [Real.rpow_mul_intCast he.le]
    intro n hn; apply Eventually.of_forall; intro i; let h0:=Act.swell (Q i) (le_refl k); exact ((h0.transit (by rw [hq]; exact Pace.nice (grade s))).trans_at (Pace.coin_word _ h0 (hq i)) hn)
local notation "α" i:max j:max=> (tariff (Q i) (hq i) L s j)
lemma stamps (m:ℕ)(hm:m≤k): Z.Meter (fun i=> tariff (Q i) (hq i) L s m) 0:= by
    induction m using Nat.strong_induction_on with
    | h m ih=>
       cases m with
       | zero=> simp_rw [tariff_zero]; exact Clock.Meter.const Z 1
       | succ m=> simp_rw [Chart.history _ _ L _ m (hm.trans he)]; apply Catch.Clock.Meter.neg; refine Catch.Clock.Meter.sum _ fun i hi=>?_ ; have hi:i < m+1:= mem_range.mp hi; exact (((ih _ hi (hi.le.trans hm)).mul ((Trend.records Z (s+i) hq he H hpos hp).steps (m+1-i) (by omega))).weak (by simp))
-- uniform total residual of the chart semaphore including time ratio.
theorem delivery (m:ℕ)(hm:m≤k): Z.Meter (fun i=> Balance.balance (Q i) (hq i) L s (g i) (f i) m) (graded (m+1)):=by
    simp_rw [Balance.remainder _ _ _ _ _ _ m (hm.trans he)]; apply Catch.Clock.Meter.neg; refine Catch.Clock.Meter.sum _ fun i hi=>?_ ; have hi:i≤ m:= mem_range_succ_iff.mp hi; refine ((( (stamps Z s hq he H hpos hp i (hi.trans hm)).mul ( H.tune.stepI.pow i )).mul ( (Trend.records Z (s+i) hq he H hpos hp).stamps (m-i) (by omega))).weak ?_); unfold graded; push_cast; rw [Nat.cast_sub hi]; linarith -- orientation
end Trend
end YM.QuadraticLocal.Rebirth
