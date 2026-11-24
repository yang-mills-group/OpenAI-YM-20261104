import YM.Integration.WilsonPhysicalStationDirectedRead
import YM.IterationFour.Running

/-! The original monitor of the two-colour column and the real finite
kinetic threshold at the same date differ by at most a factor two. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationDetectorCurrency
open Function Filter RG Labels Source Wilson Next.Rank Next.Rank.Price
open PhysicalNext.Repeat.Legato
open scoped BigOperators Classical Topology
variable {G:Gauge} (R:Run G)
local notation "C" => R.family
local notation "A" => R.family.path.levels

theorem original {k N:ℕ} (per:ℕ) (top:k ≤ N):
    let T:=(A).clock.monitor k
    let P:=(shrink (C) k N per)⁻¹
    0 < P ∧ P ≤ 2*T ∧ T ≤ 2*P:=by
  intro T P
  have hp:=shrink_pos (C) R.makes top per
  refine ⟨inv_pos.mpr hp,shrink_min (C) R.makes top per,?_⟩
  let g:=(Real.sqrt ((C).path.β N per k))⁻¹
  let b:=(A).clock.hatCoupling k
  have cap:g ≤ 2*b:=(IterationFour.Currency.hat_g R.makes N per k top).2
  have bp:0 < b:=inv_pos.mpr (Real.sqrt_pos.mpr (WardBin.hot (A) k))
  have tp:0 < T:=Real.exp_pos _
  have bound:shrink (C) k N per ≤ 2/T:=by
    change g/(b*T) ≤ 2/T
    rw [←div_div,div_le_div_iff_of_pos_right tp,div_le_iff₀ bp]
    exact cap
  change T ≤ 2*(shrink (C) k N per)⁻¹
  rw [←div_eq_mul_inv,le_div_iff₀ hp,mul_comm]
  exact (le_div_iff₀ tp).mp bound

theorem low {T P B E cost:ℝ} {q Q:ℕ} (grade:q ≤ Q)
    (ht:0 ≤ T)(hp:0 ≤ P)(hb:0 ≤ B)(he:0 ≤ E)(positive:0 ≤ cost)
    (left:P ≤ 2*T)(right:T ≤ 2*P)(paid:cost*T^Q ≤ B*T^q*E):
    cost*P^Q ≤ (B*4^Q)*P^q*E:=by
  have a:=pow_le_pow_left₀ hp left Q
  have b:=pow_le_pow_left₀ ht right q
  have c:=pow_le_pow_right₀ (by norm_num:1 ≤ (2:ℝ)) grade
  rw [mul_pow] at a b
  calc
    _ ≤ cost*(2^Q*T^Q):=mul_le_mul_of_nonneg_left a positive
    _=2^Q*(cost*T^Q):=by ring
    _ ≤ 2^Q*(B*T^q*E):=mul_le_mul_of_nonneg_left paid (by positivity)
    _ ≤ 2^Q*(B*(2^q*P^q)*E):= by gcongr
    _ ≤ 2^Q*(B*(2^Q*P^q)*E):= by gcongr
    _=_:=by rw [show (4:ℝ)=2*2 by norm_num,mul_pow];ring

theorem reserve {T P κ:ℝ} (large:4 ≤ T)(right:T ≤ 2*P)(fee:κ ≤ 1/2):
    1 ≤ P ∧ 0 ≤ T^(-κ) ∧ 1 ≤ P*T^(-κ):=by
  have ht:1 ≤ T:=by linarith only [large]
  have tp:0 < T:=zero_lt_one.trans_le ht
  have rp:0 ≤ T^(-κ):=(Real.rpow_pos_of_pos tp _).le
  refine ⟨by linarith only [right,large],rp,?_⟩
  have sq:2 ≤ T^((1:ℝ)/2):=by
    rw [←Real.sqrt_eq_rpow]
    exact (Real.le_sqrt (by norm_num) tp.le).mpr (by norm_num;exact large)
  have exp: (1:ℝ)/2 ≤ 1+-κ:=by linarith only [fee]
  have all:=sq.trans (Real.rpow_le_rpow_of_exponent_le ht exp)
  rw [Real.rpow_add tp,Real.rpow_one] at all
  have paid:=mul_le_mul_of_nonneg_right right rp
  linarith only [all,paid]

end YM.Integration.WilsonPhysicalStationDetectorCurrency
end
