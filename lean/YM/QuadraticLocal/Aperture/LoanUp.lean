import YM.QuadraticLocal.Sunrise.Fruit
/-!
# Perturb weights allowed to be increased on small Θ experiments

The actual bulk coefficients at each mark are unchanged. Important: multipliers in W.power
 are specified using **unmasked coupling powers**. After pose/tags, StepData geometry etc.
 natural because the affine germ is evaluated with the coupling direction at 1. Don't assert
 `markLetter` equal away from it! This enables substituting *one* high D internally for all
 joins (after Career compiled), then doing Peony forecasts with the budgeted weights and their
 ExpStroke.Rack supplies. Holds any marked inputs in Balcony.pure config of Θ before Work.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Sunrise
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open ConnectedActivityE6 Blaze
open AbsoluteSums Org
open Comparison.RG02 AllOrder AllOrder.Floe AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Fire PertExtension.Series Radial
open PertExtension AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method Laurent
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Comparison.RG02 Assembly Bulk Multi Marker
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G: Gauge} {c f n : Side} {k j τ N : ℕ} {S:StepData c f}
variable {ι:Type}[Fintype ι] {V:Type}[Fintype V][DecidableEq V](J:Census V)
variable {C Z D β Θ:ℝ}
namespace Loan
abbrev wide (L:Loan)(k:ℕ)(h:0<k)(he:L.toll ≤ k) : Loan:= ⟨L.e,L.r,k,h,L.crest.trans (by omega : _ ≤ _)⟩
variable (L:Loan)(k:ℕ)(h:0<k)(he:L.toll ≤k)
local notation "q"=> L.wide k h he
lemma agree (V:Atom G L.r)(F:Forest S.ratio)(x: Site f)(d:ℕ) : Loan.alloy (q) V x F (d+k)= Loan.alloy L V x F (d+L.toll):= by
 unfold alloy
 by_cases hp:L.e ≤ d; · rw [if_pos (Nat.add_le_add_right hp k),if_pos (Nat.add_le_add_right hp L.toll)]; congr 2; unfold wide; dsimp only; omega -- lean .eta he equality casts maybe
 rw [if_neg (show ¬(L.e+k≤d+k) from fun hi=> hp (by omega)),if_neg (by omega)] -- parser
end Loan
namespace Balcony
open Focus
variable (I:ι→ Loan) [DecidableEq ι] (u:∀i:ι,Atom G (I i).r)(α:ι→Site c→ Site f) (L:Layout G)(T:Finset Age) (σ:rule ι c)
variable (F:Forest S.ratio) {O:ChartRatio G}{R:PathData G}{p:Clip} (Y:Bulk.Kernel S p R O) (t:S.Choices)
local notation "P"=> rule ι c
local notation "χ"=> (Apex c G × Poll.Body (Precision.Key F G))
set_option quotPrecheck false
local notation "Fr"=> Focus.census ι
local notation "ϰ"=> QuadraticLocal.Fk.Dress.trim G F
local notation "Fx" i:max=> Focus.detailI (ι:=ι) i
variable (k)(h:0 < k)(he:∀ i,(I i).toll≤k)
local notation "Δ"=> fun i:ι=> (I i).wide k h (he i)
local notation "τ₀"=> Balcony.displayC I u α L T σ
local notation "Θ₀"=> Balcony.displayC (Δ) u α L T σ
-- mark output spectator sum for a hypothetical hot r (when q not single ∴ throughput from Mark symbols factors still works). Here canonical colors `pure basis` only and lots of moments. general enough.Source calls even in mixed sectors.Frame.
include h he
lemma chill (r:Hot Fr)(d:ℕ)(x:χ) : Assembly.markLetter (τ₀).power (markFn S F (τ₀)) r (ϰ (1,x)) d = Assembly.markLetter (Θ₀).power (markFn S F (Θ₀)) r (ϰ (1,x)) d:= by
 let q:= Launch.index Fr (Loan.toll ∘ I) r.val; let v:= Launch.index Fr (Loan.toll ∘ Δ) r.val; change Assembly.jet (markFn S F τ₀ r) (q+1+d) (ϰ (1,x)) = Assembly.jet _ (v+1+d) _
 rw [show q+1+d=d+q+1 from (by omega),show v+1+d=d+v+1 from (by omega)]; unfold displayC; rw [keepM Fr,keepM Fr]; apply Finset.sum_congr rfl; intro j hj; apply Finset.sum_congr rfl; intro b hb; apply congr_arg ((toneC σ (1:ι→ℂ) j b)); let u':ι→Loan:= Δ; have hx : r.val=(Fx j).val:= (Finset.mem_filter.mp hj).2;
 have ht : v=k:=by unfold v; rw [hx]; exact Focus.weight _ _; -- card eval
 have hp:q=(I j).toll:=by unfold q; rw [hx]; exact Focus.weight ..
 rw [ht,hp]; exact congr_fun (Loan.agree (I j) k h (he j) (u j) F (α j b) d|>.symm) x
lemma aperture (x:Bulk.Joint S (G:=G) F) (hx:x.1=1) : Assembly.curve (τ₀).power (markFn S F (τ₀)) x= Assembly.curve (Θ₀).power (markFn S F (Θ₀)) x:= by
 ext1 d; rw [Assembly.curve,Assembly.curve, PowerSeries.coeff_mk, PowerSeries.coeff_mk]; apply congr_arg (lit Fr); ext1 r; let z:= (ϰ).symm x; have ht: (ϰ) (1,z.2)=x:= by have hz:z.1=1:=hx; rw (occs:=.pos [1])[← hz]; exact (ϰ).apply_symm_apply x; -- alignment full
 rw [←ht]; exact chill k I u α L T σ F h he r d z.2
lemma runway (x:Bulk.Joint S (G:=G) F)(hx:x.1=1) : expansions (τ₀).power (markFn S F (τ₀)) (geometric Y F t (τ₀)) x = expansions (Θ₀).power (markFn S F (Θ₀)) (geometric Y F t (Θ₀)) x := by unfold expansions; rw [aperture k I u α L T σ F h he x hx]; rfl
open Order
lemma progress (x: Exterior.fieldDir G c 1) (r:ℕ):Bulk.Fk Y F t τ₀ x r=Bulk.Fk Y F t Θ₀ x r:=by
 unfold Bulk.Fk; apply (Order.sym_coeff (R:=Fr) _ _ (prescription_sym _ _ _ _ _ _ _ (Y.positive F t)) (prescription_sym _ _ _ _ _ _ _ (Y.positive F t))).2; intro j hj -- args
 ext1 U; rw [order_read _ _ _ _ _ _ _ (Y.positive ..) U hj,order_read _ _ _ _ _ _ _ (Y.positive ..) U hj]; apply integral_congr_ae; filter_upwards with z; unfold insideMoment; unfold rows; rw [show Assembly.translate (Bulk.stage Y F x) (hinge F) z=translated Y F x z from rfl,runway k I u α L T σ F Y t h he _ (show (translated Y F x z).1=1 from (by rw [footing]))]
end Balcony
end YM.QuadraticLocal.Sunrise
