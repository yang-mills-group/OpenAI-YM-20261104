import YM.Qlocal.Moonset.Guidebook
import YM.Qlocal.Calendars.Diligent
/-!
# Paying real after-reset account on the SAME calendar (quadratic price paid externally)

cf. `Tested` bounds at a fixed stage, and `Wheel.Ride.Pair` cost convergence with true
Artifact, local accuracy ep. Not uniform in the stage number until incorporated in a purchased
clock. The estimates about Γ only use the actual Epoch of that Income printer.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Moonset
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid Planned.JetPort
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open AllOrder Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration Catch Catch.Clock Floe StateE Pace Plateau Wheel
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G: Gauge}{L n f : Side}{ι:Type*}{T:Clock ι} {K:KernelChoices}{P:Patch}{σ C b a D η κ:ℝ}{k l p j M:ℕ}
open ConnectedActivityE6.Coat Shellac Work.G05
open Aux Aux.Name Push.PriceCompiler Kinetic.Port
open Aero Sienna Further.PhysicalPeriodLimitF933
namespace PostDebt
section cost
variable (k : ℕ)
open RGComparison01
-- follows Currency convention (proof adapted from CoreIntegration/Guildhall/Currency)
private lemma afterL (a:ℝ): Rate G L a (fun x:ℝ=> x^a):= by
   by_cases hp:0≤a
   · apply (Rate.power (G:=G) (L:=L)).compare; filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx; exact Eq.trans_le (abs_of_pos (by positivity)) ((Real.rpow_le_rpow hx.le (le_add_of_nonneg_right (Work.E04.shift_nonneg G L)) hp).trans (le_abs_self _))
   have hs : Rate G L a (fun x=> (betaF G x L /2)^a) := by
       apply (Rate.power.mul_right (2^a)⁻¹).congr; filter_upwards [Delay.shift_pos G L] with x hx; rw [Real.div_rpow hx.le (by norm_num),div_eq_mul_inv]
   apply hs.compare; filter_upwards [eventually_ge_atTop (G.slopeConstant*Real.log L.val),eventually_gt_atTop (0:ℝ),Delay.shift_pos G L] with x hx hp' h
   exact Eq.trans_le (abs_of_pos (by positivity)) ((Real.rpow_le_rpow_of_nonpos (div_pos h (by norm_num)) (by unfold betaF; linarith only [hx]) (le_of_not_ge hp)).trans (le_abs_self _))
lemma thermometer {G:Gauge} {L:Side} (b:ℝ) (f:ℝ→ℝ)(ht:Rate G 1 b f) : Rate G L b f:= by
 intro e he; obtain ⟨v,hb,hv⟩:= exists_between he
 filter_upwards [ht _ hb, afterL v e (G:=G) (L:=L) hv] with x hh hs; rw [Burn.hat_this] at hh; exact hh.trans ((le_abs_self _).trans hs)
-- shifted clock amount.Thermother used in `Ω.parent` stages. Includes θ^2 mismatch scale proof.
lemma rate_old_temperature : Rate G L (-(1/2:ℝ)) Pressure.temp:= thermometer _ _ Burn.temp_rate
lemma cost_inv {G:Gauge}{L: Side} : Rate G L (1/2) (fun i=>(Pressure.temp i)⁻¹):= by
  refine (afterL (G:=G) (L:=L) (1/2)).compare ((eventually_gt_atTop (0:ℝ)).mono fun x hi=> ?_)
  rw [abs_of_pos (inv_pos.mpr (Work.E09.temp_pos hi)),← Real.sqrt_eq_rpow,abs_of_pos (Real.sqrt_pos.mpr hi)]
  unfold Pressure.temp
  have hv:0<Real.sqrt x:=Real.sqrt_pos.mpr hi
  exact le_trans (inv_anti₀ (inv_pos.mpr hv) (le_mul_of_one_le_right (inv_pos.mpr hv|>.le) (Real.one_le_exp (by positivity)))) (le_of_eq (inv_inv _))
open Calendars.Cove
-- caps = min(sqrt(log) exp growth, exp log(log(x))^3). already chosen.Rate.
lemma reserve_rate (G:Gauge)(L:Side) : Rate G L 0 (fun i=> caps (betaF G i L)):= by
 let f:= fun i=> caps (betaF G i L); intro v hv; let u(t:ℝ):= Real.sqrt (Real.log t); let b(t:ℝ):= betaF G t L; have he:Tendsto (u ∘ b) atTop atTop:= (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop).comp (Work.E09.betaF_growth ..)
 filter_upwards [he.eventually_ge_atTop (1/v),(Work.E09.betaF_growth G L).eventually_ge_atTop 1] with x hx h; let b':=b x; have hq:1≤b':=h; let z:=u b'; have ht:1 ≤ z*v:=(div_le_iff₀ hv).mp (show 1/v ≤ z from hx); change |caps b'|≤ b'^v; rw [abs_of_nonneg (show 0≤caps b' from le_min (Real.exp_nonneg _) (Real.exp_nonneg _)),Real.rpow_def_of_pos (zero_lt_one.trans_le hq)]; apply le_trans (b:=Scale.drawer b') (min_le_left ..); apply Real.exp_monotone; change z ≤ Real.log b' * v; nth_rw 1 [show Real.log b'= z^2 from (Real.sq_sqrt (Real.log_nonneg hq)).symm]
 nlinarith only [mul_le_mul_of_nonneg_left ht (show 0≤z from Real.sqrt_nonneg _)]
end cost

variable {r:Stage} {q:ℕ}
open Wheel Wheel.Ride Wheel.Ride.Pair Aero Step Step.PlanV Laurent Bloch Further.PhysicalPeriodLimitF933 Shingle Macrame PhysicalNext ThroughLaunch Pane
variable {X:Metals G} {D':RG.Supply.Rolls X.p}(S:Roots (G:=G) X.p.profile X.K X.p.kernel)(x y:ℕ) (hx:4≤x)
set_option quotPrecheck false
local notation "κs"=> Burn.horizon q
local notation "LΩ"=>D'.L x
local notation "I"=>Card D' S x y hx κs
local notation "Tp"=> X.p.profile y
local notation "u"=> 1+ ((Tp).supportExponent)
local notation "C'" => Pane.cloak D' x
variable (D') (F: Income D' S x y hx (Burn.horizon q))
local notation "Λ"=>fun i:I=>i.self.paid
local notation "Γ"=>F.issue
include F
open RGComparison01
-- symbolic coefficient bounds from Income, not the numerical ratio (which is changing with cutoff)
lemma cost_era (p:ℕ): ∃ r:ℕ, Pace.Cost (fun i:I=>i.self.paid) r (fun i=> F.issue i p):= by
 let f:=fun i:I=>i.self.paid; rcases p with _|p; · refine ⟨0,?_⟩; simp_rw [(F.sustenance.due _).1]; exact Pace.Cost.fixed _
 rcases p with _|p; · refine ⟨0,?_⟩; simp_rw [(F.sustenance.due _).2.1]; exact Pace.Cost.fixed _
 rcases p with _|p
 · refine ⟨0, |C'|, abs_nonneg _,fun i=> ⟨abs_nonneg _,?_⟩⟩; rw [pow_zero,mul_one]; change |F.issue i 2| ≤ _; rw [(F.sustenance.due _).2.2]; exact i.self.bounded.trans (le_abs_self _)
 by_cases h:p < κs; · exact ⟨_,F.sustenance.income p h⟩
 refine ⟨0,?_⟩; simp_rw [F.sustenance.dormant _ (p+1+1+1) (by omega)]; exact Pace.Cost.fixed _
-- `ops` for layout price > 0. Will require one-size note bound by quota itself, thus true kernel forecast widths are still within admitted-step economy. l broad (do not confuse with conditional Fk horizon)
lemma meter_stencil (p l:ℕ) : ∃ (m:ℕ), CreditF (fun i:I=>i.self.paid) m (fun i=> price_ops (Moonset.raise (F.issue i)) p (p+l) 1):= by
 choose f hf using cost_era D' S x y hx F; let i:=∑ j∈range (p+1), f j; have h(j:ℕ)(hj:j ≤ p): Pace.Cost (Λ) i (fun a=>F.issue a j):= (hf j).up (Finset.single_le_sum (fun i _=> Nat.zero_le _) (Finset.mem_range.mpr (by omega:j<p+1))); refine ⟨i*p,?_⟩; unfold price_ops; simp_rw [mul_one]; refine CreditF.sum _ fun j hj=> CreditF.sum _ fun e he=> CreditF.sum _ fun k _=>?_ ; have hL: j-e ≤ p:= by have := mem_range.mp hj; omega
 exact Pace.Cost.up (Moonset.raises_cost e k p h (j-e) hL) (Nat.mul_le_mul_left i hL)
open RGComparison01 Geo
lemma price_pool (p l:ℕ) : ∃ (Q:ℝ→ℝ), RGComparison01.Geo G (D'.L x) Q ∧ ∀ t:ℝ,∀ A:I, A.self.paid=strengthP (betaF G t (D'.L x)) → |price_ops (Moonset.raise (F.issue A)) p (p+l) 1| ≤ Q t:= by
 obtain ⟨m,f,hf,h⟩:= meter_stencil D' S x y hx F p l; let V:=(fun t:ℝ=> strengthP (betaF G t (LΩ))); refine ⟨fun t=>f*(1+|V t|)^m,?_ ,fun t i hi=>?_ ⟩
 · have hP: V=(fun t:ℝ=> 2* Delay.fineMonitor G (LΩ) t):=rfl
   simp only [hP]; exact (Geo.fixed f).times (((Geo.fixed 1).joins (((Geo.fixed 2).times Geo.by_delay).mean)).power m)
 obtain ⟨hc,h⟩:= h i; let hx:= V t; dsimp only at h; rw [hi] at h; exact (abs_of_nonneg hc).trans_le h
end PostDebt
end YM.Qlocal.Moonset
