import YM.QuadraticLocal.Rebirth.Base
import YM.Comparison.RG02.Adjacent.Equivalent
/-!
## Born (vacuum action and calibration)

Keep complete kinetic directions. The projection is pre-calibration (to the
 actual local Fk step via its own orientation data), then these receipts show
 it's the new packet portfolio at the same predicted units. **No** estimates
 deducted from the calibration; don't claim Caliber predicts exactly numerically.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Faith
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll Extra.Iteration
open AllOrder AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Haiku.Coat AllOrder.Fire PertExtension.Series Radial
open AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet AllOrder.Floe AllOrder.Floe.Pace
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G: Gauge}{n : Side}
open Comparison.RG02 Comparison.RG02.Adjacent
open QuadraticLocal.Rebirth
namespace Spirit
variable (Q:Pace.Coin)(h:Q 0=0)(L:ℕ)(R:PathData G)(p:Clip)
local notation "Φ"=> (Stationary.Link G n)
local notation "K₀"=> (caliber Q h)
set_option quotPrecheck false
local notation "η"=> ((caliber Q h).direct L)
local notation "A"=> ( Haiku.Coat.clerk (fun _=> Precision.loop R) 0 ) -- Coat ambig
local notation "Bf"=> (A)

lemma looping : Spirit.Compatible (η) L (A) (A) := by
 let f:= Haiku.Coat.clerk (fun n:Side=> Precision.loop R (n:=n)) 0; have he: Spirit.Compatible (η) L f (factor (just 1) f):= by
    refine work (s:=0) (fun i _ n x t hh=>?_) ⟨ (η).spin _, fun i _=> ?_ ⟩
    · let g:= loop R ∘ Stationary.input G n; have ht:t^i*((t⁻¹)^i*Radial.jet g i x)=Radial.jet g i x:=by rw [inv_pow,←mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ hh),one_mul]
      rw [zpow_zero,one_mul]; exact Eq.trans (congr_arg (_*·) (Tensor.homogeneous (Tensor.coeff g i 0) x t⁻¹)) ht
    rw [ show (fun t:ℝ=> (η).rating t^(0:ℤ)) = fun _=>1 by funext x; simp ]; exact ((Act.static (n:=i) (1:ℝ)).writes i le_rfl)
 rw [show factor (just 1) f=f from funext fun i=> funext fun n=>Crest.nostep f i n] at he; exact he
-- inherited extra packets; same multi.Actor.Engine.Mark.P
variable (V:Floe.Layout G)(F:Finset Age)
lemma documented (i:Age): Spirit.Compatible (η) L (Haiku.Coat.trade i.e (V i) ) (moiety Q i V):= by
 let r:= i.r; let e:=i.e; let q:ℤ:= ↑i.e-↑i.r;
 refine work (s:=q) (fun k hk n x t ht=>?_) ?_;
 · unfold trade; split; next he=>
      let g:=turnSeries (m:=n) (V i); let j:= k-e+r; have hb:(q+j:ℤ)=(k:ℤ):=by unfold q j e r; omega
      have hw: t^k=t^q*t^j:= by rw [←zpow_natCast t k,←zpow_natCast t j, ←zpow_add₀ ht,hb];
      rw [hw, show Radial.jet _ j (t⁻¹ • x)= _ from Tensor.homogeneous (Tensor.coeff g j 0) x t⁻¹]; change t^q*t^j * ( (t⁻¹)^j * Radial.jet g j x)=_; rw [inv_pow]; field_simp; rfl
   next=> simp only [Pi.zero_apply,mul_zero]
 unfold elapsed; rw [show ((i.r-i.e:ℝ)/2) = Chart.grade q from (by unfold q Chart.grade; push_cast; ring)]; exact Chart.forward Q h L q
-- no early forecast pose assumptions
lemma auth : Spirit.Compatible (η) L (Pace.grouping 0 V F p R) (Pace.grouping Q V F p R):= by
 rw [show (Pace.grouping 0 V F p R)=Costume.basic R p F V from rfl, Costume.accountant]
 let S:=Pace.base p R; let H:= factor Q S; have ht:S+H+(A)=shiftB Q p R:=by unfold H shiftB S; abel
 unfold grouping; exact ((ht) ▸ ( Spirit.basic Q h L R p ).add ( looping Q h L R )).add (Spirit.Compatible.sum F (fun i hi=> documented Q h L V i)) -- rewrite
open Comparison.RG02.Moving Comparison.RG02.Moving.Path Comparison.RG02.Moving.Shift
variable {K:UnitCost}{l k:ℕ} {F G':Pace.Scene G}(hp:Spirit.Compatible K l F G') (hk:k ≤ l)
noncomputable abbrev suction (P:Pace.Scene G): Adjacent.Display (Stationary.Link G n):= fun i x=> -Complex.ofReal (P i n x)
local notation "P"=> (Spirit.suction F (n:=n))
local notation "P'"=> (Spirit.suction G' (n:=n))
include hp hk
lemma evolves : Adjacent.born (Spirit.suction F (n:=n)) K 0 l k= Spirit.suction G' k := by
 funext x; have ht:= hp n x; let f := glance l F K x; let L:ℝ→L[ℝ]ℂ:= - Complex.ofRealCLM; unfold Adjacent.born;
 rw [show (fun t:ℝ=> _)= (L ∘ f) by
     funext x; unfold f glance delay suction; dsimp only [Adjacent.ages, Adjacent.cover,Function.comp_apply]; simp only [zpow_zero,Complex.ofReal_one,one_mul]; unfold L; simp only [_root_.neg_apply, Complex.ofRealCLM_apply,mul_neg, sum_neg_distrib,UnitCost.enter,smul_eq_mul,Complex.ofReal_sum,Complex.ofReal_mul, Complex.ofReal_pow]
    ] -- typo shadow f unfolding & unspecified lhs
 change Assembly.jet (⇑L ∘ f) k 1= _; rw [← Assembly.jet_apply_left L f k (ht.nice.of_le le_top) 1]; change L _ = L (G' k n x); apply congr_arg; exact Eq.trans (b:=someJ f k) (by rw [someJ,iteratedDeriv_eq_iteratedFDeriv]) (ht.writes _ hk)
end Spirit
end YM.QuadraticLocal.Faith
