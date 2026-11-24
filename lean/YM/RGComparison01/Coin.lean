import YM.RGComparison01.LogSplit
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roost.Foundry
import YM.Push.CORRECTED_COLUMNS.Grows

/-!
# Spend calendar and height currency across increasing stages

All real scale prices here. Avoid a false implication from separate
(stagewise, with free thresholds) eventual estimates to price stability
in the *supplied schedule*. `Quantity Rates` entail an often useful
safeguard: pre-attachment strong price ≤ hard output price. We will use
that plus the seed penalty and its prefactor's polynomial lower bound.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters Shoot Precision SectorMeasure Oriented Reserves
open ConnectedActivityE6.Blaze Blaze.March Captain Silica
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration
open PhysicalNext PhysicalNext.Repeat Song
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

namespace Coin
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G}
    {T : Tube G S} {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ}
    {o : ConnectedActivityE6.Target.Order G W} {I R : RG.Rep G f} {μ s : ℝ}

lemma poly_min {η : ℝ} (hη : 0 < η) (k : ℕ) : 1 ≤ polyPrice η k := by
  have hv : (1+0)^k ≤ polyPrice η k * Real.exp (η*0) := polynomial_cost hη (show (0:ℝ)≤0 from le_rfl) _
  simpa using hv
local notation "Θ" => betaF G s L
lemma overture_floor (Q : YM.ConnectedActivityE6.Target G P) (hs : 1 ≤ Θ) (k : ℕ) :
    Θ ^ (-(1/2 : ℝ)) ≤ Q.overture L μ s k := by
  let m := Q.costs L μ 1 s 0
  have hv : 1 ≤ extract Q.ε k 0 0 := by simpa [extract] using poly_min Q.usable k
  have hs : Θ ^ (-(1/2 : ℝ)) ≤ m.rootHit :=
    (Real.rpow_le_rpow_of_exponent_le hs Q.start.le).trans
      (le_add_of_nonneg_left (Real.exp_nonneg _))
  have hp : 0 ≤ m.rootHit := (Real.rpow_nonneg (by have := ‹1 ≤ Θ›; linarith) _).trans hs
  apply hs.trans
  change m.rootHit ≤ extract Q.ε k _ _ * (m.rootHit * (1/2)^0 * (1-1/2)⁻¹)
  have he : Q.ε = m.reservePoly := rfl
  rw [Nat.cast_zero,mul_zero,pow_zero, mul_one]
  exact le_trans (le_mul_of_one_le_right hp (by norm_num : (1:ℝ) ≤ (1-1/2)⁻¹))
    (le_mul_of_one_le_left (mul_nonneg hp (by norm_num : (0:ℝ)≤(1-1/2)⁻¹)) hv)

lemma seed_floor (Q : YM.ConnectedActivityE6.Target G P) (hs : 1 ≤ Θ) (k : ℕ) :
    Real.exp (- Q.mark L μ s) * Θ ^ (-(1/2 : ℝ)) ≤ Cash.armK Q L μ s 0 k := by
  unfold Cash.armK Target.mergeScale
  have hp:= overture_floor (μ:=μ) Q hs k
  have hv:= (Q.overture_pos (L:=L) (μ:=μ) s k (zero_lt_one.trans_le hs)).le
  rw [pow_zero, inv_one,one_mul]; refine mul_le_mul_of_nonneg_left (hp.trans ?_) (Real.exp_nonneg _)
  norm_num
  linarith only [hv]

lemma turn_floor (p : BudgetPoint) {η s : ℝ} (hη : 0 < η) :
    turnFee p ≤ collars G η s p.order p.power := by
  have he : 4 ≤ shiftG s := by
    unfold shiftG; linarith [Nat.cast_nonneg (α:=ℝ) (radiusB s)]
  unfold turnFee collars Push.Local.turnCost
  refine le_trans ?_ (le_mul_of_one_le_right (pow_nonneg (by linarith only [he] : 0 ≤ shiftG s) _) (poly_min hη _))
  rw [pow_mul]; apply pow_le_pow_left₀ (by positivity)
  calc
    _ ≤ (2:ℝ)^p.power * 2^p.power := by
      have hp := p.power_ge
      exact mul_le_mul_of_nonneg_right (le_self_pow₀ (by norm_num) (show p.power ≠ 0 by omega))
        (by positivity)
    _ = 4^p.power := by rw [← mul_pow]; norm_num
    _ ≤ _ := by gcongr

lemma turn_price (Q : YM.ConnectedActivityE6.Target G P) (hs : 1 ≤ Θ) (p : BudgetPoint)
    {i B : ℝ} {k : ℕ} (hb : 0 ≤ B) (hi : 0 < i)
    (h : collars G i s p.order p.power * (salary Q L μ B s p.order k * (1-1/2)⁻¹) ≤ 1) :
    turnFee p ≤ Θ ^ (1/2 : ℝ) := by
  have hp : Θ ^ (-(1/2 : ℝ)) ≤ salary Q L μ B s p.order k :=
    (overture_floor Q hs k).trans (le_mul_of_one_le_left (Q.overture_pos _ _ (zero_lt_one.trans_le hs)).le
        (le_add_of_nonneg_right (mul_nonneg (by positivity) hb)))
  have hv : 0 < Θ ^ (1/2 : ℝ) := Real.rpow_pos_of_pos (zero_lt_one.trans_le hs) _
  have hF : turnFee p * Θ ^ (-(1/2 : ℝ)) ≤ 1 := (mul_le_mul (turn_floor p hi)
    (hp.trans (le_mul_of_one_le_right ((Real.rpow_pos_of_pos (zero_lt_one.trans_le hs) _).le.trans hp)
      (by norm_num : (1:ℝ) ≤ (1-1/2)⁻¹))) (Real.rpow_pos_of_pos (zero_lt_one.trans_le hs) _).le
    ((turnFee_pos p).le.trans (turn_floor p hi))).trans h
  rw [Real.rpow_neg (zero_le_one.trans hs)] at hF; simpa only [one_mul] using (mul_inv_le_iff₀ hv).1 hF

open Input Org Supply PriceCompiler Next.Scheduling Progress.DirectedRecipe Time

lemma hard_floor {B : ℕ} {w a b κ : ℝ} (h : Payments.Rates B w a b κ) : a ≤ w := by
  apply le_trans _ h.returns
  unfold Bid.quote
  have hv : Real.exp κ * a ≤ Real.exp (Payments.inflation a b κ)-1 :=
    (le_add_of_nonneg_right (mul_nonneg zero_le_two h.soft)).trans
      ((le_sub_iff_add_le).2 (Real.add_one_le_exp _))
  simpa only [Real.exp_neg, inv_mul_cancel_left₀ (Real.exp_pos _).ne'] using
    mul_le_mul_of_nonneg_left hv (Real.exp_pos (-κ)).le

section actual
variable {X : Metals G} {D : Rolls X.p} {A : Alloy X D} (F : Roost.Factor A)
    {m N : ℕ} {β : ℝ}
local notation "J₀" => A.B.a.clock.J m
local notation "J₁" => A.B.a.clock.J (m+1)
local notation "x₀" => A.B.a.clock.hatBeta m
local notation "Q₀" => F.target J₁ J₀
local notation "L₀" => D.L J₁

lemma hard_savings (hβ : β ∈ Shoot.band A.B.a (m+1)) (hm : m<N) :
    forecastK A.B.a m F.scout β ≤ Time.quoteHard A.B.a m F.book β ∧
    Time.quoteHard A.B.a m F.book β ≤ A.B.a.clock.forcedAllowance m ∧
    Time.quoteHard A.B.a m F.book β ≤ Return.forcing A.B m := by
  let p:= A.B.a.budget m
  have hb := F.machine.shops J₁ x₀ (A.B.valid.pays m) J₀ (step_paid A.B.a m)
  have hy : A.B.a.clock.hatBeta (m+1) = x₀+G.slopeConstant*Real.log (L₀).val :=
    PriceCompiler.beta_eq A.B.valid m
  obtain ⟨_,_,_,_,hE,_,ht⟩ := Deployment.clock_eqns A.B.a.clock m
  have he := params_eq A.B.valid m
  have hb' := (hb p (show Same _ _ from he ▸ (show Same (A.B.a.params m) p from ⟨rfl,rfl,rfl⟩)) rfl ht).2.2
  have hu : |A.B.kin.alpha N m| ≤ UVNext.CouplingReset.alphaBound D J₁ := UVNext.CouplingReset.within_alpha hm
  have hh := hb' (F.exchange J₁ J₀) _ (A.B.a.clock.theta J₁) β hu (hy ▸ trial_in hβ)
  obtain ⟨hx,hx'⟩ := hh.2.2.2 (F.machine.coverage _ _ (step_paid A.B.a m)|>.1)
  obtain ⟨u,κ,_,hR⟩ := hh.2.2.1.hard
  refine ⟨?_, ?_, ?_⟩
  · unfold forecastK Time.quoteHard; rw [hy]; exact hard_floor hR
  · unfold Time.quoteHard; rw [hy,hE]; exact hx'
  unfold Time.quoteHard Return.forcing
  rw [(Deployment.clock_eqns A.B.a.clock (m+1)).2.1,hy]; exact hx

lemma hardPrice_actual (hm : m < N) (hβ : β ∈ Shoot.band A.B.a (m+1)) :
    Cash.armK Q₀ L₀ (F.shape.μ J₁ J₀) x₀ 0 (F.expense J₁ J₀).degrees ≤
      (1/8 : ℝ) * Time.quoteHard A.B.a m F.book β := by
  have ht := F.pledging.conducts.income.earns J₁ J₀ (step_paid A.B.a m) x₀ (A.B.valid.pays m) β
  have he := PriceCompiler.beta_eq A.B.valid m
  apply le_trans (b:=(1/8:ℝ)* Time.forecastK A.B.a m F.scout β)
  · unfold Time.forecastK; rw [he]; apply ht; rw [← he]; exact trial_in hβ
  exact mul_le_mul_of_nonneg_left (hard_savings F hβ hm).1 (by norm_num)
end actual

section flat
variable (a : Levels G) (hG : G.Simple)
include hG
lemma neighboring_hats : ∀ᶠ i : ℕ in atTop, a.clock.hatBeta (i+1) ≤ 2*a.clock.hatBeta i := by
  filter_upwards [a.fits.mesh.eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1)),
    a.S.divergent.eventually_gt_atTop 0] with i hi he
  have hL : Real.log (a.S.block i).val / a.S.scale i ≤ 1 := hi
  have hz := (div_le_iff₀ he).1 hL
  unfold Calendar.hatBeta
  rw [Schedule.scale_succ]
  rw [one_mul] at hz
  linarith only [a.clock.bar_pos, mul_le_mul_of_nonneg_left hz (G.slopeConstant_pos hG).le]

lemma reserve_power (k : ℕ) (b δ : ℝ) (hb : 0 ≤ b) (hδ : 0 < δ) :
    ∀ᶠ i : ℕ in atTop, b * a.clock.forcedAllowance i * (a.clock.hatBeta (i+1))^k ≤ δ := by
  let L : Side:=1
  let φ x:= Real.exp (-(1:ℝ)*(Delay.fineMonitor G L x)^(1/5:ℝ))
  have hq : Rate G L (-((k:ℝ)+1)) φ:= Rate.monitor_cutoff zero_lt_one (by norm_num)
  have hr := ((hq.mul (Rate.hat (G:=G) (L:=L)|>.pow k)).mul_left (b * 2^k)).below (by ring_nf; norm_num) δ hδ
  filter_upwards [neighboring_hats a hG, (Push.Corrected.Grows.beta a hG).eventually hr] with i hx hy
  let u:= a.clock.hatBeta i; have hu : 0 ≤ u := zero_le_one.trans (a.fits.delayed i).le
  have hz : betaF G u L=u := by simp [betaF,L]
  have hw : a.clock.forcedAllowance i=φ u:= by unfold φ Delay.fineMonitor; rw [hz]; rw [neg_mul,one_mul]; rfl
  rw [hw]; change |_| ≤ _ at hy
  calc
    _ ≤ b*φ u*(2*u)^k := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (zero_le_one.trans (a.fits.delayed _).le) hx _) (mul_nonneg hb (Real.exp_nonneg _))
    _ ≤ δ := by
      have hr : b*2^k*(φ u* (betaF G u L)^k) ≤ δ := (le_abs_self _).trans hy
      rw [hz] at hr
      rw [mul_pow]; convert hr using 1; ring
end flat

/-- The coupling used on input to an E6 step. -/
def coupling (β : ℝ) := (Real.sqrt β)⁻¹
lemma coupling_pos {β : ℝ} (hp : 0 < β) : 0 < coupling β := inv_pos.mpr (Real.sqrt_pos.mpr hp)
lemma coupling_grade {β : ℝ} (hp : 0 < β) (k : ℕ) : (coupling β ^ k)^2 = (β^k)⁻¹ := by
  rw [pow_right_comm]
  unfold coupling; rw [inv_pow,Real.sq_sqrt hp.le,inv_pow]
lemma power_absorb {β : ℝ} (hb : 0 < β) (hs : 1 ≤ Θ) (he : β ≤ 2*Θ) (p : ℕ) :
    (Height.grow G L s^(2*p))⁻¹ ≤ 2^p * coupling β^p := by
  rw [pow_mul, ← inv_pow, ← mul_pow]
  apply pow_le_pow_left₀ (inv_nonneg.mpr (sq_nonneg _))
  have hy : 0 < Θ := zero_lt_one.trans_le hs
  have ht : Θ ^ (1/2:ℝ) ≤ Height.grow G L s ^ 2 := by
    unfold Height.grow
    convert! (Real.rpow_le_rpow_of_exponent_le hs (show (1/2:ℝ) ≤ (3/8)*2 by norm_num)) using 1
    rw [Real.rpow_mul hy.le,Real.rpow_two]
  rw [← Real.sqrt_eq_rpow] at ht
  have hw : 0 < Real.sqrt Θ := Real.sqrt_pos.mpr hy
  apply le_trans (inv_anti₀ hw ht)
  unfold coupling
  rw [← div_eq_mul_inv]; have hp' := Real.sqrt_pos.mpr hb
  apply (le_div_iff₀ hp').2
  rw [mul_comm, ← div_eq_mul_inv]; apply (div_le_iff₀ hw).2
  apply (sq_le_sq₀ hp'.le (by positivity : (0:ℝ)≤ 2*Real.sqrt Θ)).1
  rw [mul_pow, Real.sq_sqrt hb.le,Real.sq_sqrt hy.le]; linarith

section accounted
variable {X : Metals G} {D : Rolls X.p} {A : Alloy X D} (F : Roost.Factor A) (hG : G.Simple)
include hG

def wage (m : ℕ) : ℝ :=
  let j := A.B.a.clock.J (m+1)
  let i := A.B.a.clock.J m
  Cash.armK (F.target j i) (D.L j) (F.shape.μ j i) (A.B.a.clock.hatBeta m) 0 (F.expense j i).degrees

/-- Keep the seed markup even as the stage (and its Mark/tuning constants)
changes. No loss from summing over sites. -/
lemma seeds_paid (k : ℕ) : ∀ᶠ m in atTop,
    let j := A.B.a.clock.J (m+1)
    let i := A.B.a.clock.J m
    let x := A.B.a.clock.hatBeta m
    Height.grow G (D.L j) x ^ k ≤ Real.exp ((F.target j i).mark (D.L j) (F.shape.μ j i) x) := by
  filter_upwards [reserve_power A.B.a hG (k+1) (1/8) 1 (by norm_num) zero_lt_one] with m hm
  intro j i x
  let Θ' := A.B.a.clock.hatBeta (m+1)
  let Q':= F.target j i
  let v := Q'.mark (D.L j) (F.shape.μ j i) x
  have he : Θ' = betaF G x (D.L j) := PriceCompiler.beta_eq A.B.valid m
  have hZ : 1 ≤ betaF G x (D.L j) := he ▸ (A.B.a.fits.delayed (m+1)).le
  have hr : Θ' ∈ Shoot.band A.B.a (m+1) := by
    unfold Shoot.band
    change Θ' / 2 ≤ Θ' ∧ Θ' ≤ 2*Θ'
    have hz : 0 ≤ Θ' := he ▸ zero_le_one.trans hZ
    constructor <;> linarith
  have ht:= seed_floor (μ:=F.shape.μ j i) Q' hZ (F.expense j i).degrees
  have hK : wage F m ≤ 1/8 * A.B.a.clock.forcedAllowance m := le_trans (hardPrice_actual F (Nat.lt_succ_self m) hr)
    (mul_le_mul_of_nonneg_left (hard_savings F hr (Nat.lt_succ_self m)).2.1 (by norm_num))
  have hp : 1 ≤ Θ' := he ▸ hZ
  have hz : 0 < Θ':= zero_lt_one.trans_le hp
  have hv : (Real.exp v)⁻¹ * Θ'⁻¹ ≤ (1/8 : ℝ)* A.B.a.clock.forcedAllowance m := calc
    _ = Real.exp (-v)*Θ'⁻¹ := by rw [Real.exp_neg]
    _ ≤ Real.exp (-v)*Θ'^(-(1/2:ℝ)) := by
      rw [← Real.rpow_neg_one]; apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      apply Real.rpow_le_rpow_of_exponent_le hp; norm_num
    _ ≤ wage F m := by rw [he]; exact ht
    _ ≤ _ := hK
  have hw := (mul_le_mul_of_nonneg_right hv (pow_nonneg hz.le (k+1))).trans hm
  rw [pow_succ, ← mul_assoc, mul_right_comm _ (Θ' ^ k), mul_assoc (Real.exp v)⁻¹, inv_mul_cancel₀ hz.ne', mul_one] at hw
  have hx : Θ' ^ k ≤ Real.exp v := by simpa only [mul_one] using (inv_mul_le_iff₀ (Real.exp_pos _)).1 hw
  apply le_trans ?_ hx
  rw [he]; refine pow_le_pow_left₀ (Real.rpow_nonneg (zero_le_one.trans hZ) _) ?_ k
  exact (Real.rpow_le_rpow_of_exponent_le hZ (show (3/8:ℝ) ≤ 1 by norm_num)).trans_eq (Real.rpow_one _)

/-- Same-scale strong forced credit (also not spending a new list of post
costs). Keep the pricing *before* any marked extension.
Doesn't assert that the marked outputs have this price. -/
lemma forced_price (k : ℕ) : ∀ᶠ m in atTop,
    ∀ β ∈ Shoot.band A.B.a (m+1),
    wage F m ≤ Real.sqrt (A.B.a.clock.forcedAllowance m) * coupling β ^ k := by
  filter_upwards [reserve_power A.B.a hG k (2^k) 1 (by positivity) zero_lt_one] with m hm
  intro β hβ
  let y:= A.B.a.clock.hatBeta (m+1)
  let w:= A.B.a.clock.forcedAllowance m
  have he: y/2 ≤ β ∧ β ≤ 2*y := hβ
  have hb:= lt_of_lt_of_le (half_pos (zero_lt_one.trans (A.B.a.fits.delayed _))) he.1
  have h := hardPrice_actual F (Nat.lt_succ_self m) hβ
  apply h.trans
  apply le_trans (b:=w)
  · calc
      _ ≤ 1/8*w := mul_le_mul_of_nonneg_left (hard_savings F hβ (Nat.lt_succ_self m)).2.1 (by norm_num)
      _ ≤ w := mul_le_of_le_one_left (Real.exp_pos _).le (by norm_num)
  have hw : 0 ≤ w := (Real.exp_pos _).le
  have hz : Real.sqrt w ≤ coupling β ^ k := by
    rw [← sq_le_sq₀ (Real.sqrt_nonneg _) (pow_nonneg (coupling_pos hb).le _), coupling_grade hb,Real.sq_sqrt hw]
    rw [← one_div, le_div_iff₀ (pow_pos hb _)]
    calc
      _ ≤ w*(2*y)^k := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb.le he.2 _) hw
      _ ≤ 1 := by rw [mul_pow,← mul_assoc,mul_comm w (2^k)]; exact hm
  exact (Real.mul_self_sqrt hw).symm.le.trans (mul_le_mul_of_nonneg_left hz (Real.sqrt_nonneg w))
end accounted
end Coin
end YM.RGComparison01
