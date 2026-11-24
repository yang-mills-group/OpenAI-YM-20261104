import YM.QuadraticLocal.Kiosk
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Rent
/-!
Income arithmetic, compiled on post-block stage pairs. Allocate *polynomial geometry*, not a
smaller xhat⁻ᵃ, additional resource for the mark re-expression factors at final K merger.
Pay on ANY actual coupling in the physical band via master theta-limit. No exponential price
restored from the area estimates after choosing T for each test. Separately book simultaneous
Lanes `Academy` hard rate versus the first assembly `First.roll`; uses a dedicated condition on
the construction: µ/32 suffices, from `Rent.pockets` before `F`, not inferred from
`earns` (endpoints ν all wallets need to retain Pocket). Feeds schedule purchase.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Willow
open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Precision Next.Scheduling
open Next.Scheduling.Clock AnalyticBridge VerifiedReset ConnectedActivityE6 PhysicalNext Repeat
open Progress.DirectedRecipe Payments
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius Asymptotics
variable {G: Gauge}{F : Postage}
-- currency at K ONLY. reserve x≥t, but B exactly at cover x.
def area (B:ℕ):ℝ:= (((B+B+1:ℕ):ℝ))^4
def haloSlack (B:ℕ):ℝ:= 1/(16*area B)
lemma area_ge_one (B:ℕ): 1≤ area B:= one_le_pow₀ (show (1:ℝ)≤ (B+B+1:ℕ) from by exact_mod_cast (show 1≤B+B+1 by omega))
lemma spare_pos (B:ℕ):0< haloSlack B:= by have h:= zero_lt_one.trans_le (area_ge_one B); unfold haloSlack; positivity
-- rates uniform in unrestricted β on a band. use full exp half jump factor even at B=0
lemma allot (P:Pairing F): ∀ᶠ y:ℝ in atTop,∀ β:ℝ, Next.Scheduling.inBand y β→ ∀ B≤ Clock.cover y,
    Rates B (Real.exp (-Pairing.kGoal F y β)) (P.strong y β) (2*haloSlack B) (Pairing.kGoal F y β):= by
    let P' : Pairing F := { P with C:=4*P.C, C_nonneg:=mul_nonneg (by norm_num) P.C_nonneg }
    filter_upwards [P'.currency] with y hy β hb B hB; let a:= P.strong y β; let k:=Pairing.kGoal F y β; let u:=haloSlack B; let z:=Payments.inflation a (2*u) k
    have hr:= hy.2 β hb B hB; have hv:1≤ area B:= area_ge_one B; have ho : 0 < u:=spare_pos B; have hu : u*area B=1/16 :=by have h:0<area B:=zero_lt_one.trans_le hv; unfold u haloSlack; field_simp
    have he : 0 ≤ a:= mul_nonneg P.C_nonneg (Real.exp_nonneg _); have hx :0≤ z:= add_nonneg (mul_nonneg (Real.exp_nonneg _) he) (by positivity)
    have hZ: area B*z ≤ 1/2:= by
       have ha:= hr.capital; change area B*Payments.inflation _ _ k ≤ (1:ℝ) at ha
       rw [show P'.strong y β=4*a from mul_assoc ..] at ha -- orientation?
       have hp: area B*(4*(Real.exp k*a))≤ 1:= le_trans (mul_le_mul_of_nonneg_left (show 4*(Real.exp k*a)≤ Payments.inflation (4*a) (P'.mild y) k from ?_) (zero_le_one.trans hv)) ha
       swap
       · rw [mul_left_comm, Payments.inflation]; exact le_add_of_nonneg_right (mul_nonneg zero_le_two hr.soft)
       unfold z Payments.inflation; linarith
    have hy:z≤1/2:= (le_mul_of_one_le_left hx hv).trans hZ
    refine ⟨hr.heading,he,(mul_nonneg zero_le_two ho.le),?_,hZ.trans (by norm_num),?_⟩
    · have ht: u≤1/16:= by rw [←hu]; exact le_mul_of_one_le_right ho.le hv
      linarith
    change Real.exp (-k)*(Real.exp z-1)≤ Real.exp (-k)
    apply mul_le_of_le_one_right (Real.exp_nonneg _); have he:= (le_abs_self (Real.exp z -1)).trans (Real.abs_exp_sub_one_le (by rw [abs_of_nonneg hx]; linarith only [hy])); rw [abs_of_nonneg hx] at he; linarith

lemma grows (r:ℝ)(hr:0<r) : ∀ᶠ x:ℝ in atTop, x^(-r)≤ haloSlack (radiusB x):=by
    have hb := Work.E09.radiusB_small r hr 4
    filter_upwards [eventually_gt_atTop (0:ℝ),Clock.counting.eventually_ge_atTop 1,hb.def (by norm_num : (0:ℝ)<1/1296)] with x hx hB hp -- IsLittleO.def
    let B:=radiusB x; let H:ℝ:=B; have he :1≤H:= by unfold H; exact_mod_cast (show 1≤ B from hB)
    have hz:0 < x^r := Real.rpow_pos_of_pos hx _
    change ‖H^4‖ ≤ _*(‖x^r‖) at hp; rw [Real.norm_of_nonneg hz.le,Real.norm_of_nonneg (by positivity : 0 ≤ H^4)] at hp -- argument b?
    have ht:area B ≤81*H^4:= by
       refine (pow_le_pow_left₀ (by positivity) (show ((B+B+1:ℕ):ℝ) ≤ 3*H from ?_) 4).trans_eq (by ring)
       push_cast; linarith
    rw [Real.rpow_neg hx.le]; unfold haloSlack; rw [← one_div,div_le_div_iff₀ hz (mul_pos (by norm_num) (zero_lt_one.trans_le (area_ge_one B)))]; linarith -- B change

lemma census (F:Postage) (A:Time.Forecast F)(H:ℝ)(hH:0≤H):∀ᶠ x:ℝ in atTop,∀ β:ℝ,Next.Scheduling.inBand (x+H) β→
    Rates (radiusB x) (Real.exp (-Pairing.kGoal F (x+H) β)) (A.pair.strong (x+H) β) (x^(-(1/3:ℝ))+haloSlack (radiusB x)) (Pairing.kGoal F (x+H) β):=by
    filter_upwards [(tendsto_atTop_add_const_right _ H tendsto_id).eventually (allot A.pair),eventually_gt_atTop (1:ℝ), grows (1/3) (by norm_num)] with i hi hB hz β hb
    let B:= radiusB i; have hr : Rates B (Real.exp (-Pairing.kGoal F (i+H) β)) _ _ (Pairing.kGoal F (i+H) β):= hi β hb B (Nat.ceil_le_ceil (pow_le_pow_left₀ (Real.log_pos hB|>.le) (Real.log_le_log (zero_lt_one.trans hB) (le_add_of_nonneg_right hH)) _))
    exact Canopy.hedge hr hr.hard le_rfl (add_nonneg (Real.rpow_pos_of_pos (zero_lt_one.trans hB) _).le (spare_pos _).le) (by linarith) le_rfl

-- µ reserved at post-block already; s≥1 in Lanes bill. May choose s HIGH for ANY demand.
lemma allot_in (P:Teller G)(Q:ConnectedActivityE6.Target G P)(L:Side)(μ:ℝ) (F:Postage)(A:Time.Forecast F)(hA:A.hard≤μ/32):∀ᶠ x:ℝ in atTop,∀ β: ℝ, Next.Scheduling.inBand (betaF G x L) β→ ∀ s:ℕ,1≤ s → Real.exp ((-Q.mark L μ x)*(1/2:ℝ))*Coat.gStep β^s ≤ A.pair.strong (betaF G x L) β / 8:=by
   -- stronger than including arbitrary polynomial because compare only at paid radii here
   have h : Tendsto (fun x:ℝ=> Clock.gap (betaF G x L)) atTop (𝓝 0):= checks_gauge.comp (Work.E09.betaF_growth G L)
   filter_upwards [Push.AbsoluteSums.Delay.shift_pos G L,h.eventually (ge_mem_nhds (by norm_num : (0:ℝ)< 1/16))] with x hx ht β hb s hs
   let y:= betaF G x L; have h0 :0< A.hard:= F.pos.trans A.surplus; obtain ⟨hz,h'h⟩:= band_gap y β hx hb
   have hI:= Clock.gp hx; have hv : 0< gap β:= (half_pos hI).trans_le hz
   have ht' : gap β≤ 1/8:= h'h.trans (by change 2*Clock.gap (betaF G x L) ≤_; linarith) -- might `* 2`?
   let p:= Instrument.plain.P y; let t := Instrument.plain.t y/ gap β; have hp:0<p:=wp _ _; have hV:0≤t:= div_nonneg (mul_pos hI hp).le hv.le; have ht':gap β ≤1/8:= ht'; have hT:t≤2*p:= (div_le_iff₀ hv).mpr (by change gap y*p ≤ _; nlinarith only [hz,hp]); let u:=Q.mark L μ x; have hu: u=μ/4*p^2:=by
       have he:p= Push.AbsoluteSums.Delay.fineMonitor G L x:= Clock.watch_two y; rw [he]; unfold u; change μ/2*(1/2) * _= _; ring
   have hs': -u*(1/2) ≤ -A.hard*t^2:=by rw [hu]; nlinarith only [mul_le_mul_of_nonneg_left (sq_le_sq₀ hV (hV.trans hT)|>.2 hT) h0.le,mul_le_mul_of_nonneg_right hA (sq_nonneg (2*p))]
   have hm:Real.exp (-u*(1/2)) ≤ A.pair.strong y β:= (Real.exp_monotone hs').trans (le_mul_of_one_le_left (Real.exp_nonneg _) (le_max_left 1 A.coeff))
   have hy: gap β^s ≤ 1/8:= (pow_le_pow_of_le_one hv.le (ht'.trans (by norm_num)) hs).trans (by simp only [pow_one]; exact ht')
   calc _ ≤ A.pair.strong y β * (1/8):= mul_le_mul hm hy (pow_nonneg hv.le _) ((Real.exp_pos _).le.trans hm)
        _ = _ := by ring
end YM.QuadraticLocal.Willow
