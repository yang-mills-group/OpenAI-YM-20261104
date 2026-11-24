import YM.QuadraticLocal.Class.Spill
import YM.QuadraticLocal.Cycle.Cap
import YM.QuadraticLocal.Found.Mastery

/-! # delay-budget upgrade to install model marks on the actual unmasked vacuum

No volume dependence, also on the top scale. Sharp power cost only for installation of
force partners. The regular receipt here has reserve-polynomial cost. In this delay
note all estimates are for a current site (not a pair of neighbors); equivalently
ratio=`trivialL=1`, not identity StepData. No statement here that a trivial ratio step
is possible or being prescribed in the formal or actual density comparisons!
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Spill.Raffle
open Function Filter Finset Lattice RG Pressure Ac Marker Next.Scheduling
open Wilson RG.Supply PhysicalNext Repeat
open ConnectedActivityE6 Push Push.AbsoluteSums Coat RemainderComparison
open AnalyticBridge VerifiedReset QuadraticLocal.Earn QuadraticLocal.Mentor Animals
open AllOrder AllOrder.Burn MintClock
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Asymptotics

variable (G:Gauge) (S:Stage)
variable (σ:ℝ)(ε:ℝ) (hp:0<σ) (hr:0< ε)(he:ε≤1)
variable (j v k:ℕ)

set_option quotPrecheck false
local notation "L"=> (1:Side)
local notation "Λ"=> S.supportExponent+1
local notation "I"=> j+v+1

private lemma climate {t:ℝ} (ht:0<t) (β:ℝ)(hv:inBand t β) : Pressure.temp t ≤ gStep β * Page.temperature G 1 t:=by
 have hρ:0<Delay.fineMonitor G L t:= Delay.monitor_pos G L _
 have hx: gStep t/2 ≤ gStep β:= (band_gap t β ht hv).1
 rw [show Pressure.temp t=gStep t * Delay.fineMonitor G L t from (by unfold Delay.fineMonitor; rw [Burn.hat_this]; rfl
 )]
 unfold Page.temperature
 linarith only [mul_le_mul_of_nonneg_right hx hρ.le, mul_pos (by unfold gStep; exact inv_pos.mpr (Real.sqrt_pos.mpr ht) : 0<gStep t) hρ]

private lemma outside {t:ℝ} (ht:16 ≤ t) : 1+2/Pressure.temp t ≤ t:= by
 have h:0<t:= lt_of_lt_of_le (by norm_num) ht
 let f:=Real.sqrt t
 have hf: 0< f:= Real.sqrt_pos.mpr h
 have hztemp(t:ℝ):1≤Real.exp (t^2):= Real.one_le_exp (sq_nonneg _)
 have hu : f⁻¹ ≤ Pressure.temp t:= le_mul_of_one_le_right (inv_pos.mpr hf).le (hztemp _)
 calc
   _ ≤ 1+2*f:= by rw [div_eq_mul_inv]; exact add_le_add_right (mul_le_mul_of_nonneg_left ((inv_anti₀ (inv_pos.mpr hf) hu).trans_eq (inv_inv _)) zero_le_two) _
   _ ≤ t:= by
     have hx : f^2=t:=Real.sq_sqrt h.le
     nlinarith only [hf,hx,ht]

private def page (j v k:ℕ):MintClock.Page:= ⟨k,j,v,0,0,0,0,0,0, 0,0,0⟩

/-- β-independent polynomial quote for regular model at support exponent **plus one**. -/
def fundsOne (t:ℝ): ℝ:= MintClock.Page.tariff G L (page j v k) S t (S.supportExponent+1) (σ/4) (Pressure.radiusB t)
lemma regular (B:BudgetPoint)(t:ℝ)(hv:Time.Same S B)(he:B.B=Pressure.radiusB t) : Invoice.price B (Page.temperature G L t) I k (B.supportExponent+1) (σ/4) G = fundsOne G S σ j v k t:= by
 rw [hv.2.2]; exact MintClock.Page.front_quote G L (page j v k) S t hv _ he Λ _
lemma polynomial : RemainderComparison.Reserve G L (fundsOne G S σ j v k):=
 MintClock.Page.income G L (page j v k) S Reserve.field (S.supportExponent+1) (σ/4)
local notation "K"=> (fundsOne G S σ j v k)

def pad (n:ℕ):= n+2
structure Gains (t:ℝ) :Prop where
 limit : K t ≤ MintClock.Page.reward t ε
 allowance : ∀ (p:BudgetPoint), Spes.Market.tuning S p t → ∀ β, Next.Scheduling.inBand t β → Invoice.Supports p (Page.temperature G L t) (p.supportExponent+1) (Coat.gStep β) σ (σ/4) ∧ (Spill.allOver p)^I * K t ≤ t^(Raffle.pad (j+v+1))* (Willow.haloSlack p.B)

include hp hr he
lemma insurance : ∀ᶠ t:ℝ in atTop, Gains G S σ ε j v k t:=by
   have hc:0≤ Λ:= (show 0 ≤ S.supportExponent+1 from by linarith only [ S.price_pos ])
   filter_upwards [Page.tender G L hr K (polynomial ..), Page.tender G L zero_lt_one _ (Page.season G L), Access.wide (G:=G) («L»:=L) (Rate.const (0:ℝ)), Page.feesAround σ hp (S.supportExponent+1) hc Pressure.radiusB Work.E01.radiusB_tendsto, eventually_ge_atTop (16:ℝ) ] with t ht hf h ho ht₁
   rw [Burn.hat_this] at ht hf
   have hz:1≤t:= le_trans (by norm_num) ht₁
   have hp₁:0<t:= zero_lt_one.trans_le hz
   refine ⟨ht,fun p hv β hβ=>?_⟩
   have hu : 1≤ Page.temperature G L t:=one_le_mul_of_one_le_of_one_le (by norm_num) (show 1 ≤ Delay.fineMonitor G L t from Real.one_le_exp (sq_nonneg _))
   obtain ⟨hβ',hpβ⟩:= h.2 β ((Burn.hat_this G t).symm ▸ hβ)
   refine ⟨⟨hβ',hpβ.le.trans (h.1.2.1.le.trans h.1.2.2.1.le),hu,hv.1.trans_le (climate G hp₁ β hβ), hp.le,?_⟩,?_⟩
   · rw [hv.2.1,hv.2.2.2.2]; exact ho
   have hT₁ : K t ≤ t:= ht.trans (le_trans (min_le_right ..) ((Real.rpow_le_rpow_of_exponent_le hz he).trans_eq (Real.rpow_one _)))
   let s':= Willow.haloSlack (radiusB t)
   have ht': 0< s':= Willow.spare_pos _
   have hX: s'⁻¹ ≤ t:= hf.trans ((min_le_right ..).trans_eq (Real.rpow_one _))
   rw [hv.2.1]
   refine (div_le_iff₀ ht').1 ?_
   calc
     ((Spill.allOver p)^I * K t) / s' ≤ (t^I*t)/s':= by
       apply div_le_div_of_nonneg_right _ ht'.le
       apply (mul_le_mul_of_nonneg_left hT₁ (pow_nonneg (zero_le_one.trans (Spill.allOver_ge p)) _)).trans
       apply mul_le_mul_of_nonneg_right _ hp₁.le
       exact pow_le_pow_left₀ (zero_le_one.trans (Spill.allOver_ge p)) (le_trans ( le_of_eq (show Spill.allOver p=1+2/Pressure.temp t from (by unfold Spill.allOver; rw [hv.1]))) (outside ht₁)) _
     _ ≤ _:=by rw [div_eq_mul_inv,pad,pow_succ,pow_succ]; exact mul_le_mul_of_nonneg_left hX (by positivity)
-- A bill on the delay applicable whenever using Stage `y`. Independent of input Rep. Need any registration thresholds at THIS index W before choosing Ψ. Does not depend on internal comparison loans.
omit hp hr he
open AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open Input Org Wilson ThroughLaunch PriceCompiler
open Legato.VowsR
variable {X: Metals G} (R:Roots (G:=G) X.p.profile X.K X.p.kernel)
variable {D:Rolls X.p} {P:Protection D}(W:Delays P)
variable (φ:ℕ→ℕ)

-- future semesters choose the cost tolerance as a Function of stage and θ demand
local notation "Ω" k0:max i:max=> Poetry.Agenda.seed R φ k0 i

def Warm : Prop:= ∀ x y, StepStages x y → ∀ t,W.betaEntry x≤ t →
   ∀ i ≤ y, ∀ j ≤ y, ∀ v ≤ y, ∀ k ≤ y, Gains G (X.p.profile y) (Poetry.Agenda.seed R φ i y) (Mentor.Tolerance y) j v k t

lemma accrues : ∃ Y:Delays P, DelayLe W Y ∧ ∀ Z:Delays P, DelayLe Y Z → Warm G R Z φ:= by
 let P x y:= ∀ i ≤ y, ∀ j ≤ y, ∀ v ≤ y, ∀ k ≤ y,Gains G ( X.p.profile y ) ( Poetry.Agenda.seed R φ i y ) (Mentor.Tolerance y) j v k x; have hp0 y:∀ᶠ t in atTop,P t y:=by
   let Kx:=Finset.Iic y
   have he : 0< Mentor.Tolerance y:= by unfold Mentor.Tolerance; positivity
   have hp: Mentor.Tolerance y ≤ 1:= by unfold Mentor.Tolerance; exact (div_le_iff₀ (by positivity)).mpr (by rw [one_mul]; exact_mod_cast Nat.le_add_left 1 y)
   filter_upwards [(eventually_all_finset Kx).2 fun i _=> (eventually_all_finset Kx).2 fun j _=> (eventually_all_finset Kx).2 fun v _=> (eventually_all_finset Kx).2 fun k _=> (insurance G ( X.p.profile y ) ( Poetry.Agenda.seed R φ i y ) (Mentor.Tolerance y) ( Poetry.Agenda.stem .. ) he hp j v k)] with t ht
   exact fun i hi j hj v hv k hk=> ht i (mem_Iic.mpr hi) j (mem_Iic.mpr hj) v (mem_Iic.mpr hv) k (mem_Iic.mpr hk)
 obtain ⟨t',-,hx,hy⟩:= collect_upper W.betaEntry _ (fun x=> eventually_transitions x _ _ fun y _=>hp0 y)
 exact ⟨{W with betaEntry:=t'},⟨hx,le_rfl,le_rfl,le_rfl⟩,fun _ he j i h x hk=> hy _ _ ((he.beta j).trans hk) i h⟩

def scroll : LawScroll G φ where
    clause (Y') D PP C R₀ q Wp Z Q₀ S R Yr Kq T' V':= Warm G R V' φ
    permits := by
      intro S Tq R C E' h; refine ⟨(fun _=> (0:ℕ)),fun l hL D q Wp Z Q' S' he Pw T₀ Yr Book hP V'=>?_⟩; exact accrues (X:=ThroughLaunch.currency S Tq l) G R V' φ

end YM.QuadraticLocal.Spill.Raffle
