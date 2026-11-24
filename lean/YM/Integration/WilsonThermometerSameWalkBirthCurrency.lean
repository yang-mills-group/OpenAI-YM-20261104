import YM.Integration.WilsonOriginalDepositedHardRate
import YM.Integration.WilsonThermometerSameWalkTariff
import YM.Integration.WilsonThermometerSameWalkBirthShift
/-! Naked hard marker fees at the actual bare age. Its original divided
allowance clears every fixed power, uniformly in all marked sites and cutoffs. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerSameWalkBirthCurrency
open Filter Lattice Wilson RG Source Labels Extra.Histories
open PhysicalNext Repeat Legato Graces Roost Org ProjectorNext.Equivariance Trace.Physical
open WilsonMeasuredPrimaryWindow WilsonOriginalNullPrimaryFees
open Push.Local Trace.Physical.Germ Next.Foundations
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (d:ℕ)
local notation "L" => R.family.path.levels
local notation "F" => R.family.labels.level d
local notation "S" => R.family.localSection d
local notation "p₀" i:max => (L).budget i
local notation "H" i:max => (L).clock.hatBeta i
def upper := (Next.Foundations.full_value_bound (G:=G) d).choose
def fee {n:Side} (i:ℕ) (o:Site n) (v:R.family.label d):ℝ:=
  (QuadraticLocal.Willow.haloSlack (p₀ i).B)⁻¹*
    (1+fullCost (F) (p₀ i) (upper (G:=G) d)*(F).coeffSize ((F).core v)*
      Real.exp (((p₀ i).supportExponent+1)*coverNumber (p₀ i).B ((S).footprint o)))

theorem aperture (i:ℕ): (QuadraticLocal.Willow.haloSlack (p₀ i).B)⁻¹ ≤ 10000*(H i)^8:=by
  have above:1 ≤ H i:=((L).fits.delayed i).le
  have nn:0 ≤ H i:=zero_le_one.trans above
  have log0:0 ≤ Real.log (H i):=Real.log_nonneg above
  have log1:Real.log (H i) ≤ H i:=by linarith only [Real.log_le_sub_one_of_pos (zero_lt_one.trans_le above)]
  have ce:(Real.log (H i))^2 ≤ (H i)^2:=pow_le_pow_left₀ log0 log1 2
  have gate:((p₀ i).B:ℝ) ≤ 2*(H i)^2:=by
    have n:=Nat.ceil_lt_add_one (sq_nonneg (Real.log (H i)))
    change (⌈(Real.log (H i))^2⌉₊:ℝ) ≤ _
    linarith only [n,ce,one_le_pow₀ above (n:=2)]
  have side:((p₀ i).B:ℝ)+(p₀ i).B+1 ≤ 5*(H i)^2:=by linarith only [gate,one_le_pow₀ above (n:=2)]
  have u:=pow_le_pow_left₀ (by positivity : 0 ≤ ((p₀ i).B:ℝ)+(p₀ i).B+1) side 4
  unfold QuadraticLocal.Willow.haloSlack QuadraticLocal.Willow.area
  rw [one_div,inv_inv]
  push_cast
  linarith only [(mul_le_mul_of_nonneg_left u (by norm_num : 0 ≤ (16:ℝ)))]

theorem field (i:ℕ):
    fullCost (F) (p₀ i) (upper (G:=G) d) ≤ upper (G:=G) d*(H i)^(degree (F)):=by
  have above:1 ≤ H i:=((L).fits.delayed i).le
  have monitor:1 ≤ (L).clock.monitor i:=Real.one_le_exp (sq_nonneg _)
  have native:(p₀ i).threshold⁻¹ ≤ H i:=by
    change ((Real.sqrt (H i))⁻¹*(L).clock.monitor i)⁻¹ ≤ _
    rw [mul_inv,inv_inv]
    calc _ ≤ Real.sqrt (H i):=mul_le_of_le_one_right (Real.sqrt_nonneg _) (inv_le_one_of_one_le₀ monitor)
         _ ≤ H i:=(Real.sqrt_le_left (zero_le_one.trans above)).mpr (le_self_pow₀ above (by omega))
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr (p₀ i).threshold_pos.le) native _)
    (zero_le_one.trans (Next.Foundations.full_value_bound (G:=G) d).choose_spec.1)

theorem width (M:WilsonMeasuredRankedMenu.Menu R d) (i:ℕ) (hi:M.onset ≤ i)
    {n:Side} (o:Site n):
    Real.exp (((p₀ i).supportExponent+1)*coverNumber (p₀ i).B ((S).footprint o)) ≤ M.cost*H i:=by
  have pass: (coverNumber (p₀ i).B ((S).footprint o):ℝ) ≤ atomTiles (S):=by exact_mod_cast atomTiles_price (S) (p₀ i) o
  have gh:0 ≤ (p₀ i).supportExponent:=(p₀ i).exponent_pos.le
  have discount:Real.exp (((p₀ i).supportExponent+1)*coverNumber (p₀ i).B ((S).footprint o))
      ≤ Real.exp (((p₀ i).supportExponent+2)*atomTiles (S)):=by
    apply Real.exp_le_exp.mpr
    gcongr
    linarith
  have slot:=(WilsonOriginalNullPrimaryFees.slots R d M i hi o).1
  apply discount.trans
  apply le_trans _ slot
  apply le_mul_of_one_le_right (Real.exp_pos _).le
  exact atomPrice_ge_one _ _ (zero_le_one.trans (price_one_le G _))

theorem original (simple:G.Simple) (M:WilsonMeasuredRankedMenu.Menu R d) (q:ℕ)
    {ε:ℝ} (positive:0 < ε):
    ∀ᶠ i in atTop, ∀ {n:Side} (o:Site n)(v:R.family.label d),
      fee R d i o v*Real.sqrt ((L).clock.forcedAllowance i) ≤ ε*((H i)^q)⁻¹*(1+(F).coeffSize v):=by
  let U:=upper (G:=G) d
  let K:=10000*(1+U*M.cost)
  have U0:0 ≤ U:=zero_le_one.trans (Next.Foundations.full_value_bound (G:=G) d).choose_spec.1
  filter_upwards [eventually_ge_atTop M.onset,
    WilsonOriginalDepositedHardRate.restored simple (L) (8+degree (F)+1) q K ε positive] with i late small
  intro n o v
  have above:1 ≤ H i:=((L).fits.delayed i).le
  have h0:0 < H i:=zero_lt_one.trans_le above
  have norm0:0 ≤ (F).coeffSize v:=Finset.sum_nonneg fun _ _=>norm_nonneg _
  have core0:0 ≤ (F).coeffSize ((F).core v):=Finset.sum_nonneg fun _ _=>norm_nonneg _
  have cb:(F).coeffSize ((F).core v) ≤ (F).coeffSize v:=by
    unfold Frame.core Frame.coeffSize
    refine Finset.sum_le_sum fun t _=>?_
    by_cases ht:t=0 <;> simp [ht]
  have sigma:=width R d M i late o
  have Mc:0 ≤ M.cost:=(nonneg_of_mul_nonneg_left ((Real.exp_pos _).le.trans sigma) h0)
  have root:=aperture R i
  have paid:=field R d i
  let z:= (F).coeffSize v
  have base:1 ≤ (H i)^(degree (F))*H i:=one_le_mul_of_one_le_of_one_le (one_le_pow₀ above) above
  have clear:0 ≤ fullCost (F) (p₀ i) U:=mul_nonneg U0 (pow_nonneg (inv_nonneg.mpr (p₀ i).threshold_pos.le) _)
  have r0:0 ≤ Real.sqrt ((L).clock.forcedAllowance i):=Real.sqrt_nonneg _
  have bounded:fee R d i o v ≤ K*(H i)^(8+degree (F)+1)*(1+z):=by
    unfold fee
    calc
      _ ≤ (10000*(H i)^8)*(1+(U*(H i)^(degree (F)))*z*(M.cost*H i)):=by gcongr
      _ ≤ (10000*(H i)^8)*(((H i)^(degree (F))*H i)+U*(H i)^(degree (F))*z*(M.cost*H i)):=by gcongr
      _ ≤ K*(H i)^(8+degree (F)+1)*(1+z):=by
        unfold K
        rw [pow_add,pow_add,pow_one]
        nlinarith only [mul_nonneg (show 0 ≤ (10000:ℝ)*(H i)^8*((H i)^(degree (F))*H i) by positivity)
          (add_nonneg (mul_nonneg U0 Mc) norm0)]
  calc
    _ ≤ (K*Real.sqrt ((L).clock.forcedAllowance i)*(H i)^(8+degree (F)+1))*(1+z):=by
      exact (mul_le_mul_of_nonneg_right bounded r0).trans_eq (by ring)
    _ ≤ _:=mul_le_mul_of_nonneg_right small (by positivity)

end YM.Integration.WilsonThermometerSameWalkBirthCurrency
end
