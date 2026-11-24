import YM.QuadraticLocal.Startup.Gain
import YM.AllOrder.Quay.Tariff
import YM.QuadraticLocal.View
/-!
# Post-loop tax for startup, prepaid, including mark power and shape.

 transcript relative attempts use Ω = HOMES Level schedule. Rates via positive asymptotics at Warm
 and not by changing the path after b−m etc fixed. Need all these costs before shooting Beta weights.
 This pack depends only on neighboring stage profiles not on Audience, G-W facilities after.L.
 Occupancy q grade; wants LOW p bound on affine vac later.Neutral.R
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Spes
open Function Filter Finset Wilson Lattice RG Marker MeasureTheory Push Push.AbsoluteSums Push.PriceCompiler
open PhysicalNext PhysicalNext.Repeat Pressure Next.Scheduling Input ThroughLaunch Org Roost
open Progress.DirectedRecipe Payments AnalyticBridge VerifiedReset Collection Quotes
open ConnectedActivityE6 Coat WilsonStartup AllOrder AllOrder.Quay AllOrder.Burn AllOrder.Plateau
open scoped Topology Classical Matrix.Norms.Frobenius BigOperators ContDiff
variable {G:Gauge} {n:Side}
namespace Market
variable {x u v h : ℝ}{S: RG.Stage} {d o m k K q r :ℕ}{p : BudgetPoint}
-- o=M horizon demand >0, not necessarily ≥2 except PUBLIC. k index asks budget exponent tolerance τ
-- w huge. Kernel occupancy data and high aggregate budget normalized to 1.Frame.L.
def charge (k:ℕ):ℝ:= 1/(k+3:ℕ)
def basic (o k:ℕ):ℝ:= (o+1:ℕ)*(1/2:ℝ)- charge k
def radiant (o k:ℕ)(x:ℝ):ℝ:=x^basic o k
def pad (o r:ℕ):ℕ:= o+r+1
def fundL (o r:ℕ)(x:ℝ):ℝ:= x^pad o r
-- Entry. Wish high startup + Tentative move after recoarse.Radius.Temp cost field incidence derived separately.
def tuning (S:RG.Stage)(p:BudgetPoint)(x:ℝ):Prop:=p.threshold=Pressure.temp x∧p.B=radiusB x∧ Time.Same S p -- check
structure Tray (G:Gauge)(S:RG.Stage)(x:ℝ)(o k K d r u:ℕ):Prop where
   sized : 1< x
   radius : d ≤ radiusB x
   expect (l:ℕ)(j:ℤ)(m:ℕ) : l ≤ r → j.natAbs ≤ r → 1≤ m→m≤ K→ (↑(o+1:ℕ):ℤ) * m ≤ j+l → ∀ (p:BudgetPoint), tuning S p x→∀ (β:ℝ), Near x β →
      radiant o k x ^ m * (gStep β ^ j * Legal.baseCost p G l d d) * Real.exp S.supportExponent ≤ 1 ∧ (radiant o k x / fundL o r x)^m * (gStep β ^ j * (2* (2:ℝ)^l)) * Real.exp (S.supportExponent+1) ≤ Willow.haloSlack (radiusB x)
   enough : WilsonStartup.Timing.normK (Real.log x) ≤ (Blush.glyph x) * x^(-(u:ℝ))
lemma price (k:ℕ):0<charge k:=by unfold charge; positivity
lemma positive (o k:ℕ):0< basic o k:=by
    have hp: (charge k) < (1/2:ℝ):= div_lt_div_of_pos_left zero_lt_one (by norm_num) (show (↑(k+3:ℕ):ℝ)>2 by push_cast; linarith only [show 0 ≤ (k:ℝ) from Nat.cast_nonneg k]); unfold basic; push_cast; linarith only [show 0 ≤ (o:ℝ) from Nat.cast_nonneg o,hp]
-- fields from Lane anytime after picking.L
local notation "U"=> Claim G trivialL Near
private lemma claim_below {f:ℝ→ℝ→ℝ}(h:Claim G trivialL Near u f)(hu:u<0) {v:ℝ}(hv:0<v):∀ᶠ x in atTop, ∀ y, Near x y→ |f x y|≤ v:= by obtain ⟨p,h,hp⟩:=h; filter_upwards [h.below hu v hv,hp] with x h hp y hy; exact (hp y hy).trans ((le_abs_self _).trans h)
lemma exponent (j:ℤ): U (-(j:ℝ)/2) (fun _ s=> gStep s ^ j):= by
   cases j
   next j=> change U (-(↑(↑j:ℤ):ℝ)/2) (fun _ s=> gStep s ^ (j:ℤ)); simp_rw [zpow_natCast]; refine (Burn.keep_rate.power j).weaken ?_; push_cast; linarith
   next j=>
      have he : (((Int.negSucc j):ℤ):ℝ)=-↑(j+1:ℕ):=by simp
      rw [he]; simp_rw [zpow_negSucc,← inv_pow]; refine (Burn.reverse_rate.power (j+1)).weaken ?_; push_cast; linarith
private lemma fill (S:RG.Stage)(k d:ℕ): let p:ℝ→ℝ:= fun x=> ((1+(d:ℝ))^S.power)^S.order * (2* Wages.startup G k S.power S.order * Pressure.temp x^k*(1+d:ℝ)^ Wages.grade k S.power S.order); U (-(k:ℝ)/2) (fun x _=>p x):= by intro p; exact ((Claim.hires ((((Burn.temp_rate.pow k).mul_left (2* Wages.startup G k S.power S.order)).mul_right ((1+(d:ℝ))^ Wages.grade k S.power S.order)).mul_left _))).weaken (by nlinarith only [])
variable (G S k K o d r u) {u:ℕ}
lemma audited (l:ℕ)(j:ℤ)(m:ℕ)(_hl:l≤ r)(hs:j.natAbs≤ r)(hm:1≤ m)(hj : (↑(o+1:ℕ):ℤ) * m ≤ j+l): ∀ᶠ x:ℝ in atTop,∀ p,tuning S p x→∀ β, Near x β→
      radiant o k x ^ m * (gStep β ^ j * Legal.baseCost p G l d d) * Real.exp S.supportExponent ≤ 1 ∧ (radiant o k x / fundL o r x)^m * (gStep β ^ j * (2* (2:ℝ)^l)) * Real.exp (S.supportExponent+1) ≤ Willow.haloSlack (radiusB x) := by
   let a:=(basic o k); let H(x:ℝ):=radiant o k x; let f(x:ℝ):=((1+(d:ℝ))^S.power)^S.order * (2* Wages.startup G l S.power S.order*Pressure.temp x^l*(1+d:ℝ)^Wages.grade l S.power S.order)
   let m':= (pad o r:ℝ); let v':= a-m'; let w(x:ℝ):= x^v'; have ht(x:ℝ)(h:0<x): w x= radiant o k x / fundL o r x:=by unfold w v' m'; rw [Real.rpow_sub h,Real.rpow_natCast]; rfl
   have h1 : Claim G trivialL Near a (fun x _=> H x) := Claim.hires (Burn.tracks G a); have h2 : Claim G trivialL Near v' (fun x _=> w x) := Claim.hires (Burn.tracks G v')
   let ε:=Real.exp S.supportExponent; let α:=Real.exp (S.supportExponent+1); let s:= fun (x b:ℝ)=> H x^m*(gStep b ^ j * f x)*ε; have he:= ((h1.power m).mul ((exponent (G:=G) j).mul (fill (G:=G) S l d))).r_scale ε
   have hI:1≤ (m:ℝ):=Nat.one_le_cast.mpr hm; have hδ:0< (charge k)*(m:ℝ):=mul_pos (price k) (zero_lt_one.trans_le hI)
   have hv: a*m+(- (j:ℝ)/2+ -(l:ℝ)/2)<0:=by
       have hh:(↑(o+1:ℕ):ℝ) * (m:ℝ) ≤ (j:ℝ)+ (l:ℝ):= by exact_mod_cast hj
       unfold a basic; linarith
   have hW : - (r:ℝ) ≤ (j:ℝ) := by
      have hh:j ≥ -(r:ℤ):=le_trans (neg_le_neg (by exact_mod_cast hs : (Int.natAbs j:ℤ) ≤ (r:ℤ))) ?_; rotate_left; · omega
      exact_mod_cast hh
   have hk: v' < -(r:ℝ):=by unfold v' m' a basic pad; push_cast; linarith only [price k,Nat.cast_nonneg (α:=ℝ) o]
   let p(x b:ℝ):=w x^m*(gStep b ^ j * (2* (2:ℝ)^l))*α*16*Quay.countH x
   have hp := ((( (h2.power m).mul ((exponent (G:=G) j).r_scale (2* (2:ℝ)^l))).r_scale α).r_scale 16).mul (Claim.hires (G:=G) (L:=trivialL) (Quay.volumeN (G:=G)));
   have hp':v'*m + (- (j:ℝ)/2)+0<0:=by nlinarith only [hW,hk,Nat.cast_nonneg (α:=ℝ) r, mul_le_mul_of_nonpos_left hI (show v'≤0 from hk.le.trans (neg_nonpos.mpr (Nat.cast_nonneg _)))]
   filter_upwards [claim_below he hv zero_lt_one,claim_below hp hp' zero_lt_one,eventually_gt_atTop (0:ℝ)] with x hP hQ hX p' hx b hB'
   refine ⟨?_, ?_⟩
   · have hQ:= (le_abs_self (s x b)).trans (hP b hB'); unfold Legal.baseCost; rw [hx.1,hx.2.2.1,hx.2.2.2.1]; exact hQ
   have he0:= (le_abs_self (p x b)).trans (hQ b hB'); rw [← ht x hX]; unfold Willow.haloSlack; apply (le_div_iff₀ (by have h:= Willow.area_ge_one (radiusB x); linarith)).2; rw [← mul_assoc]; exact he0
-- Kernel start reserve needed only if b=N. otherwise Price post restoration by dividing further by glyph x. This estimate also holds off-Opportunity.Need before order q entry.
lemma keeps (u:ℕ): ∀ᶠ x:ℝ in atTop, Timing.normK (Real.log x) ≤ Blush.glyph x*x^(-(u:ℝ)):=by
   let ψ (x:ℝ):=Real.exp ((Real.log (Real.log x))^2/5); -- Explicit convention §Timing.
   have hv(x:ℝ): Blush.glyph x=Real.exp (-ψ x/2):=by unfold Blush.glyph ψ; rw [Real.sqrt_eq_rpow,← Real.exp_mul,← Real.exp_mul]; congr 1; simp only [div_eq_mul_inv,one_mul] -- check ring inner exp
   filter_upwards [Real.tendsto_log_atTop.eventually (Timing.hard_growth 2), Real.tendsto_log_atTop.eventually_ge_atTop (2*(u:ℝ)), eventually_gt_atTop (1:ℝ)] with x hx hy hp
   rw [hv,Real.rpow_def_of_pos (zero_lt_one.trans hp),← Real.exp_add]; apply Real.exp_monotone; change -ψ x≤ _; change Real.log x ^2 ≤ ψ x at hx; linarith only [mul_le_mul_of_nonneg_left hy (Real.log_pos hp).le,hx]
lemma offers (K u:ℕ) : ∀ᶠ x in atTop, Tray G S x o k K d r u:=by
    let Y:=Finset.Iic r; let Z:=Finset.Icc (-(r:ℤ)) (r:ℤ); let J:=Finset.Icc 1 K
    let P x l j m:= ∀ p, tuning S p x→∀ β, Near x β→ radiant o k x ^ (m:ℕ)*(gStep β^(j:ℤ)*Legal.baseCost p G l d d)*Real.exp S.supportExponent ≤1 ∧ (radiant o k x / fundL o r x)^m * (gStep β ^ j * (2* (2:ℝ)^l)) * Real.exp (S.supportExponent+1) ≤ Willow.haloSlack (radiusB x)
    apply Eventually.mp (((eventually_all_finset Y).2 (fun i hi=> (eventually_all_finset Z).2 (fun j hj=> (eventually_all_finset J).2 (fun t ht=> show ∀ᶠ x in atTop, (↑(o+1:ℕ):ℤ)*t ≤ j+i → P x i j t from ?_)))).and ((keeps u).and ((Next.Scheduling.Clock.counting.eventually_ge_atTop d).and (eventually_gt_atTop (1:ℝ))))) ?_ -- order mp
    · exact Eventually.of_forall (fun x h=> Tray.mk h.2.2.2 h.2.2.1 (fun l j m hl hj hm hx hp=> h.1 l (mem_Iic.mpr hl) j (mem_Icc.mpr (by omega)) m (mem_Icc.mpr ⟨hm,hx⟩) hp) h.2.1)
    by_cases hp:(↑(o+1:ℕ):ℤ)*t ≤ j+i; swap; · exact Eventually.of_forall (fun x h=> (hp h).elim)
    exact (audited G S d o k r i j t (mem_Iic.mp hi) (by have hm := (mem_Icc.mp hj); omega) (mem_Icc.mp ht).1 hp).mono fun _ h _=>h
end Market
end YM.QuadraticLocal.Spes
