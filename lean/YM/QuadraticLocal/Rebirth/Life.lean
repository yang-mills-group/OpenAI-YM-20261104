import YM.AllOrder.Wheel.Wage
import YM.Comparison.RG02.Adjacent.Caliber
/-!
# Use ONE coupling chart, including all floating powers of Wilson insertions

Uses `Floe.Pace.Coin`. No assumption that the actual next beta is
 `Wheel.now`; must measure the difference on using this chart numerically.
Includes negative powers of the coupling (rendered powers of the
 actual model despite advanced fluctuation grading). Uses the **forward**
 chart of the Caliber, and here does not request any birth assumptions
 on a germ *chosen* near the actual beta.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Rebirth
open Function Filter Finset Lattice RG Wilson Marker
open Comparison.RG02 Comparison.RG02.Adjacent
open Pressure ConnectedActivityE6 AllOrder AllOrder.Catch
open AllOrder.Wheel AllOrder.Floe Next.Scheduling
open PositionX.Jet AllOrder.Response
open AllOrder.Laplace AllOrder.Laplace.SigmaP
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable (Q : Pace.Coin) (h : Q 0=0) (L : ℕ) (s:ℤ)

/-- The actual-construction coefficient convention is beta ratio, as a predictor with
 separate error. -/
def caliber : Adjacent.Caliber := ⟨ Q + just 1, by rw [Pi.add_apply, h]; simp [just]⟩
namespace Chart
local notation "K"=> caliber Q h
local notation "Y"=> PositionX.Jet.delay Q L
lemma at_zero : (K).measure 0=1:= (K).starts
lemma elsewhere {j:ℕ} (hj:0<j) : (K).measure j=Q j:= (by unfold caliber; simp [just,hj.ne'])
lemma sale (t:ℝ) : (caliber Q h).tariff L t=1+delay Q L t:= by
    unfold caliber Caliber.tariff delay just; simp only [Pi.add_apply,_root_.mul_add, mul_ite, mul_zero, sum_add_distrib, smul_eq_mul, sum_ite_eq', mem_range, mul_one, pow_zero, if_pos (Nat.zero_lt_succ L)]; exact add_comm ..
local notation "G" => Coat.gStep
set_option quotPrecheck false
local notation "F"=> (caliber Q h).direct L
local notation "T"=> (caliber Q h).back L
lemma predictor (β:ℝ): Wheel.now Q L β=β*((K).tariff L (G β)):= by rw [sale]
lemma glow {β:ℝ} (hp:0<β) : G (Wheel.now Q L β)= ((caliber Q h).direct L).enter (G β):= by rw [predictor _ h, Coat.gStep, Real.sqrt_mul hp.le, _root_.mul_inv_rev]; exact mul_comm ..

private lemma speed_formula (t:ℝ)(ha:0 < 1+ delay Q L t) : ((caliber Q h).direct L).rating t=(1+delay Q L t)^(-(1/2:ℝ)) := by
 change (Real.sqrt ((K).tariff L t))⁻¹=_; rw [sale,Real.rpow_neg ha.le,← Real.sqrt_eq_rpow]

def grade (i:ℤ) : ℝ := -(1/2:ℝ)*(i:ℝ)

lemma income (t:ℝ)(ha:0 < 1+ delay Q L t) : ((caliber Q h).direct L).rating t ^ s= (1+delay Q L t)^(Chart.grade s) := by
 rw [speed_formula Q h L t ha]; unfold grade; rw [Real.rpow_mul_intCast ha.le] -- sign

lemma forward : Act L (fun x=> ( (caliber Q h).direct L ).rating x ^ s) (Pace.ladder (Chart.grade s) Q):= by
 apply (Pace.coin_word (Chart.grade s) (Act.swell Q (n:=L) le_rfl) h).realizes; exact ((K).rates L).mono fun x hx=> (income Q h L s x ((Chart.sale Q h L x) ▸ hx)).symm

/-- Formal comparison uses coefficients of the germ of this VERY back curve. -/
def tariff := someJ (fun x:ℝ=> ( (caliber Q h).back L ).rating x^s)
lemma revered : Act L (fun x=> ( (caliber Q h).back L ).rating x^s) (tariff Q h L s):= eo_Act _ ( (T).spin _ )
lemma tariff_zero : tariff Q h L s 0=1:= by simp [tariff,UnitCost.origin]

lemma composition (n:ℕ) :
    Act n ((fun x:ℝ=> ((caliber Q h).direct L).rating x^s) * (delay (tariff Q h L s) n ∘ ((caliber Q h).direct L).enter)) (just 1):=by
    let α x:=(F).rating x; let β x:= (T).rating x; let Yx:= (F).enter; let k:=tariff Q h L s; let u(x:ℝ):= α x^s; let v(x:ℝ):= β x^s; change Act n (u * (delay k n ∘ Yx)) (just 1)
    have hu: Act n u (someJ u):= eo_Act _ ((F).spin s); have he: Act n v k:= eo_Act _ ((T).spin s); let hm:=eo_Act n ((F).here); have ht: light (someJ Yx):= Eq.trans (someJ_zero _) ((F).borne); have hf:= exact_prod hu ( hm.dial (Act.swell k le_rfl) ht); have hh:= exact_prod hu ( hm.dial he ht ); apply hf.repairs; apply fun i hi=> hh.trans_at (b:=just 1) ?hm hi; case hm=>
        refine (Act.static _).realizes ?_; filter_upwards [((K).forward_back L).stays, (F).bright] with x hx hv
        change 1= α x^s*β (Yx x)^s; have hx: β (Yx x)=(α x)⁻¹:= hx; rw [hx,← mul_zpow, mul_inv_cancel₀ (show α x ≠0 from hv.ne'), one_zpow]
end Chart
end YM.QuadraticLocal.Rebirth
