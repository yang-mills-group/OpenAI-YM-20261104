import YM.OPE.Rate
import YM.OPE.Therm.Request
import YM.Pert.Asymptotics.RawAxis
import YM.MatchingLedger.Compass.Sail
import YM.MatchingLedger.Hessian.Allowance

/-! # turn-time accounting: on all cutoffs and same real beta run. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.MatchingLedger.Compass.Income
open Function Filter Set MeasureTheory Precision RG Tree Wilson Lattice Work Exterior Pressure
open Sail OPE OPE.Therm Next.Scheduling Review.Clock Home Kiosk Spring.Fares Pert.Asymptotics
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} (C: Family G) (h:C.Makes)(hG:G.Simple)
namespace Weather
abbrev ice (m:ℕ):= C.path.levels.clock.hatBeta m
abbrev ħ (m:ℕ):= C.path.levels.clock.hatCoupling m
abbrev ℓ (m:ℕ):= Real.log (ice C m)
lemma ice_strict (m:ℕ) : 1< ice C m:= C.path.levels.fits.delayed m
lemma ice_pos (m:ℕ): 0< ice C m:= zero_lt_one.trans (ice_strict C m)
lemma hat_heat (m:ℕ): 0< ħ C m := inv_pos.mpr (Real.sqrt_pos.mpr (ice_pos C m))
lemma hat_one (m:ℕ): ħ C m ≤ 1:= inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr (ice_strict C m).le)
lemma hat_sqr (m:ℕ): ħ C m^2=(ice C m)⁻¹:= by unfold ħ Calendar.hatCoupling; rw [inv_pow,Real.sq_sqrt (ice_pos C m).le]
lemma hat_energy (p : ℝ) (m:ℕ): (ħ C m)^p=(ice C m)^(-p/2) := by
  have hv : 0< ice C m:= ice_pos C m
  unfold ħ Calendar.hatCoupling; rw [Real.inv_rpow,Real.sqrt_eq_rpow,← Real.rpow_mul hv.le,← Real.rpow_neg hv.le]; ring_nf
  exact (Real.sqrt_pos.mpr hv).le
include hG
lemma age : Tendsto (ℓ C) atTop atTop:= Real.tendsto_log_atTop.comp (hat_deep C hG)
omit hG
abbrev Fare (p : ℝ) (w:ℕ→ℝ) := RateLE atTop (ℓ C) w p
include hG
lemma betaLedger (u:ℝ): RateIs atTop (ℓ C) (fun i=>(ice C i)^u) u := by
    apply (RateIs.exp u (age C hG)).congr
    filter_upwards with i; rw [Real.rpow_def_of_pos (ice_pos C i),mul_comm]
lemma fair (p:ℝ) : RateIs atTop (ℓ C) (fun i=> (ħ C i)^p) (-p/2):=by simp_rw [hat_energy]; exact betaLedger C hG _
lemma spends {u p:ℝ} {w:ℕ→ℝ}(he:Fare C u w)(hh:u< -p/2) : ∀ᶠ i:ℕ in atTop, |w i| ≤ (ħ C i)^p:= (fair C hG p).outweigh he hh (age C hG)
lemma takeBeta {u v:ℝ}{w:ℕ→ℝ}(h:Fare C u w)(he:u<v):∀ᶠ i:ℕ in atTop, |w i| ≤ ice C i ^ v := (betaLedger C hG v).outweigh h he (age C hG)
lemma chill {u:ℝ}{w:ℕ→ℝ}(h:Fare C u w)(he:u<0): Tendsto w atTop (𝓝 0) := h.tends he (age C hG)

omit hG
namespace Fare -- abbrev dot?
-- standard income lemmas. exact rates.
include hG
lemma fixed (p:ℝ): Fare C 0 (fun _=>p):= RateLE.const _ (age C hG)
lemma adds {p u w} (v:Fare C p u)(z:Fare C p w): Fare C p (u+w):= v.add z (age C hG)
omit hG in
lemma times {u v:ℕ→ℝ}(a:Fare C 0 u)(b:Fare C 0 v): Fare C 0 (u*v) := by simpa only [zero_add] using! RateLE.mul a b
lemma costs {u:ℕ→ℝ}(a:Fare C 0 u)(k:ℕ): Fare C 0 (fun i=>u i^k):= by simpa only [mul_zero] using a.pow k (age C hG)
end Fare
local notation "A" => C.path.levels
local notation "V" => C.path.levels.clock
include hG
lemma monitors : Fare C 0 ((V).monitor) := by
   intro r hr; filter_upwards [(hat_deep C hG).eventually (Vac.Numbers.cost 1 r hr)] with i hi
   change ((V).monitor i) ^ (1:ℝ) ≤ ice C i ^r at hi; rw [Real.rpow_one] at hi
   rw [Real.norm_of_nonneg (show 0≤ (V).monitor i from Real.exp_pos _|>.le), mul_comm,ℓ,←Real.rpow_def_of_pos]; exact hi; exact ice_pos C i
lemma laurels : Fare C 0 (ℓ C):= (monitors C hG).of_norm_le (by
     filter_upwards [(hat_deep C hG).eventually (curtain 1 1 1 zero_lt_one zero_lt_one)] with i hi
     rw [Real.norm_of_nonneg (Real.log_pos (ice_strict C i)).le]; simpa only [pow_one,one_mul] using! hi)
lemma doors : Fare C 0 (fun i=> ((V).coverSize i:ℝ)):= by
    apply ((Fare.costs C hG (laurels C hG) 2).add (Fare.fixed C hG 1) (age C hG)).of_norm_le
    filter_upwards with i; rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]; exact (Nat.ceil_lt_add_one (sq_nonneg _)).le
lemma doors_ahead : Fare C 0 (fun i=> ((V).coverSize (i+1):ℝ)):= by
     let f(X:ℝ):= Real.log 2+X
     have hz:Fare C 0 (fun i=>f (ℓ C i)):= (Fare.fixed C hG _).add (laurels C hG) (age C hG)
     have hh: Fare C 0 (fun i=> f (ℓ C i)^2 +1) := (Fare.costs C hG hz 2).add (Fare.fixed C hG _) (age C hG)
     apply hh.of_norm_le; filter_upwards [Spring.Fares.next C hG] with i hi; rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]; refine (Nat.ceil_lt_add_one (sq_nonneg _)).le.trans ?_; apply add_le_add_left; refine pow_le_pow_left₀ (Real.log_pos (ice_strict C (i+1))).le ?_ 2; rw [show f (ℓ C i)= Real.log (2*ice C i) from (Real.log_mul (by norm_num) (ice_pos C i).ne').symm]; exact Real.log_le_log (ice_pos C (i+1)) hi
lemma loops_cost : Fare C 0 (V).loopCap := by
   apply (RateLE.of_norm_le (f:=fun i=>2*((V).monitor i)) ?_ ?_)
   · exact Fare.times C (Fare.fixed C hG _) (monitors C hG)
   filter_upwards with i
   have hMon : 1 ≤ (V).monitor i:= Real.one_le_exp (sq_nonneg _)
   rw [Calendar.loopCap,Real.norm_of_nonneg (by positivity)]
   exact mul_le_mul_of_nonneg_left ((Real.rpow_le_rpow_of_exponent_le hMon (by refine ((A).fits.thetaRange i).2.trans ?_; exact inv_le_one_of_one_le₀ (by exact_mod_cast (show 1 ≤ (V).J i from (by linarith only [(V).adm i]))))).trans_eq (Real.rpow_one _)) zero_le_two
variable (P:Pins.Prepared (Home.invite G) C.path.levels)
include P
lemma path_cost : Fare C 0 (fun i=> ((A).params i).paths) ∧ Fare C 0 (fun i=> ((A).params i).width⁻¹):=by
   constructor <;> apply (doors C hG).of_norm_le <;> filter_upwards [eventually_gt_atTop 0] with i hi
   · rw [Real.norm_of_nonneg ((A).params i).paths_pos.le]; exact (le_max_left ..).trans (Spring.Fares.future_payment C P hi)
   rw [Real.norm_of_nonneg (inv_pos.mpr ((A).params i).width_pos).le]; exact (le_max_right ..).trans (Spring.Fares.future_payment C P hi)

lemma length_cost : Fare C 0 (fun m=> ((C.S.block m).val:ℝ)):= (doors_ahead C hG).of_norm_le (Eventually.of_forall fun m=> by
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    have hb := (show earned ((V).op m 0).patch (V).kernel G _ from P m 0 0 (Nat.zero_le _)).2.1
    apply Nat.cast_le.mpr; unfold macroR at hb; change _ + 4*(C.S.block m).val≤ (V).coverSize (m+1) at hb; omega)
omit hG P
include h
local notation "f" => C.path.β
lemma into_band {m N:ℕ} (hm:m≤N)(p:ℕ): ħ C m/2 ≤ regulatorRun C N p m ∧ regulatorRun C N p m ≤2* ħ C m:= Next.Scheduling.band_gap (ice C m) ((f) N p m) (ice_pos C m) (Next.Scheduling.trial_in (h.wilson.represents N p m hm).band)
lemma iceborn {m N:ℕ} (hm:m≤N)(p:ℕ): 0< (f) N p m:= (half_pos (ice_pos C m)).trans_le (h.wilson.represents N p m hm).band.1
lemma runs_pos {m N:ℕ} (hm:m≤N)(p:ℕ): 0< regulatorRun C N p m:= inv_pos.mpr (Real.sqrt_pos.mpr (iceborn C h hm p))
lemma epoch {m N:ℕ}(hm:m≤N)(p:ℕ): (f) N p m * regulatorRun C N p m ^2=1:= by
   have hx:=iceborn C h hm p; unfold regulatorRun; rw [inv_pow,Real.sq_sqrt hx.le,mul_inv_cancel₀ hx.ne']

end Weather
end YM.MatchingLedger.Compass.Income
