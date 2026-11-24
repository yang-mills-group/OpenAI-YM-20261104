import YM.AllOrder.Till.Glace
import YM.AllOrder.Burn.Notes
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Burn
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration Floe Floe.Pace Floe.Aero Floe.StateE
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge}{ι:Type}[Nonempty ι]{a b C D Z Λ ε σ Ω α:ℝ}{k r m n N l:ℕ}{j:Side}
open Till Tilt Floe.Step Floe.Step.PlanV Plateau
-- L=1 for receipts on either.Housing z support paid. R.Space β recognition. factor 2*sqrt or 4..
abbrev trivialL:Side:=1
local notation "R"=> Rate G trivialL
abbrev Near (x:ℝ) (t:ℝ): Prop :=x/4 ≤ t ∧ t ≤ 4*x
local notation "U"=>Claim G trivialL Near
lemma hat_this (G:Gauge)(x:ℝ) : betaF G x (1:Side)=x:= by simp [betaF]
lemma budgets_x {f:ℝ→ℝ→ℝ} (h: Claim G trivialL Near a f) {u:ℝ}(hu:a<u):∀ᶠ x in atTop,∀ s, Near x s → |f x s|≤ x^u:= by filter_upwards [h.bill hu] with x ht; simp_rw [hat_this] at ht; exact ht
local notation "κ"=> (fun x:ℝ=>x^ (1/2:ℝ))
lemma tracks (G:Gauge) (a:ℝ): Rate G trivialL a (fun x=> x^a):= Rate.congr Rate.power (Eventually.of_forall fun x=> (congr_arg (· ^ a) (hat_this G x)).symm)
open ConnectedActivityE6.Coat
lemma inv_sqrt (x:ℝ)(h:0<x): gStep x=x^(-(1/2:ℝ)):= by unfold gStep; rw [Real.sqrt_eq_rpow,Real.rpow_neg h.le]
lemma keep_rate : U (-(1/2:ℝ)) (fun _ s=> gStep s):= by
 refine ⟨_,(tracks G (-(1/2:ℝ))).mul_left (4:ℝ),?_⟩; filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx i h; have he:0<x/4:=(by positivity); have hi:= he.trans_le h.1; rw [abs_of_pos (gS i hi).1,← inv_sqrt x hx]; unfold gStep; apply le_trans (inv_anti₀ (Real.sqrt_pos.mpr he) (Real.sqrt_le_sqrt h.1)); rw [Real.sqrt_div hx.le]; have hv:= Real.sqrt_pos.mpr hx; rw [show (4:ℝ)= 2^2 by norm_num,Real.sqrt_sq (by norm_num)]; field_simp; norm_num
lemma reverse_rate : U (1/2:ℝ) (fun _ s=>(gStep s)⁻¹) := by
 refine ⟨_,(tracks G (1/2:ℝ)).mul_left (4:ℝ),?_⟩; filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx i h; unfold gStep; rw [inv_inv, abs_of_nonneg (Real.sqrt_nonneg _), ← Real.sqrt_eq_rpow]; have hv:= Real.sqrt_pos.mpr hx; refine (Real.sqrt_le_sqrt h.2).trans ?_; rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤4), show (4:ℝ)= 2^2 by norm_num, Real.sqrt_sq (by norm_num)]; nlinarith only [hv]
lemma temp_rate : R (-(1/2:ℝ)) Pressure.temp := Rate.congr (Rate.flame (G:=G)) (Eventually.of_forall (fun x=>(show temp x= temp (betaF G x (1:Side)) from congr_arg temp ((hat_this G x).symm))))
lemma hats_rate : R 0 strengthP:= Rate.congr (ConnectedActivityE6.loopBill_rate G trivialL) (Eventually.of_forall fun x=> by unfold loopBill strengthP; change _=2*Push.PriceCompiler.mon (betaF G x _); rw [hat_this])
lemma first_rate (i:Age)(k:ℕ): R 0 (fun x=> authority k i (strengthP x)):= (((Rate.const 1).add (Claim.absolute (G:=G) (L:=trivialL) hats_rate)).pow _).weaken (by simp)
lemma rates_x(i:Age): U (((i.r:ℝ)-i.e)/2) (fun _ x=> rates (gStep x) i) := by unfold Tilt.rates ratioW; simp only [←inv_pow]; exact ((keep_rate.power i.e).mul (reverse_rate.power i.r)).weaken (by push_cast; linarith)
lemma stop (X:Finset Age)(P:Stage)(r k:ℕ) : U (-(3/2)) (fun x s=> priceAt G k P.order P.power r (radiusB x) (Pressure.temp x) (strengthP x) (gStep s) X):= by
 unfold priceAt; apply Claim.sprocket; intro i hi; let A:=(i.r:ℝ); let d:=(i.e:ℝ); let L := (1:Side); let c:= Claim.hires (A:=Near) (first_rate (G:=G) i k); have hR: R (-(A/2)) (fun x=>temp x ^ i.r):= (temp_rate.pow i.r).weaken (by unfold A; linarith); have hf:= (Claim.hires (A:=Near) (((hR.mul_left (Next.Scheduling.Wages.startup G i.r P.power P.order)).mul (((Rate.const 1).add (Rate.radius_price (G:=G) (L:=L))).pow (Next.Scheduling.Wages.grade i.r P.power P.order))).weaken (by simp : -(A/2)+0* (Next.Scheduling.Wages.grade i.r P.power P.order:ℝ)≤ -(A/2)))); refine ((rates_x i).square.mul ((c.mul hf).l_scale _)).weaken ?_; unfold A; have hp:3≤ (i.e:ℝ):= Nat.cast_le (α:=ℝ)|>.mpr i.senior; linarith
abbrev silver (x:ℝ) := x^(-(7/5):ℝ)
-- consumer Y. fuel capρ arithmetic A.Main
lemma silver_pos(x:ℝ)(hx:0<x):0<silver x:=Real.rpow_pos_of_pos hx _
lemma fueling (G:Gauge)(k:ℕ) : ∀ᶠ x:ℝ in atTop, PostFuel x k (silver x) ∧ young x k ≤ (Real.sqrt x)⁻¹ ^ (11/5:ℝ):= by
 let v:= credit k+3/8*extraN k; have hv:v< -(11/10:ℝ):= by unfold v credit alt; push_cast; linarith
 let f(x:ℝ):= silver x+x^(3/8*extraN k:ℝ)*young x k; have he: Rate G trivialL v f:= ((((tracks G (-(7/5):ℝ)).weaken (by unfold v credit alt; push_cast; linarith)).add (((tracks G (3/8*extraN k:ℝ)).mul (tracks G (credit k))).weaken (by unfold v; linarith))));
 filter_upwards [eventually_ge_atTop (1:ℝ),he _ hv] with x hx h; have ht:0<x:=zero_lt_one.trans_le hx; rw [hat_this] at h; have hQ : (Real.sqrt x)⁻¹ ^ (11/5:ℝ) =x^(-(11/10:ℝ)) := by rw [Real.sqrt_eq_rpow,← Real.rpow_neg ht.le,← Real.rpow_mul ht.le, show -(1/2:ℝ)*(11/5) = -(11/10) by norm_num]; -- PostFuel first hidden. need inside after

 rw [← hQ] at h; have hy:= (le_abs_self (f x)).trans h; constructor; · exact ⟨hy⟩
 apply le_trans _ hy; exact (le_mul_of_one_le_left (Real.rpow_nonneg ht.le _) (Real.one_le_rpow hx (by positivity : (0:ℝ)≤3/8*(extraN k:ℝ)))).trans (le_add_of_nonneg_left (silver_pos x ht|>.le))
end YM.AllOrder.Burn
