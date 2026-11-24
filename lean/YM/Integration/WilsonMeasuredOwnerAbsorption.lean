import YM.Integration.WilsonMeasuredRankedPrimaryBudget
import YM.Integration.WilsonReportHarvestUpperAge
import YM.Integration.WilsonCenteredReporterClock
import YM.Integration.WilsonOlderSignedOneMarkCurrency

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMeasuredOwnerAbsorption
open Filter Lattice Wilson RG PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Push.Local Pert.Asymptotics RG16 ConnectedActivityE6
open scoped Classical Topology

def fee (d:ℕ) (C:ℝ) := (72:ℝ)*2^d*max C 1

private theorem fee_pos (d:ℕ) (C:ℝ) : 0<fee d C := by
  unfold fee
  exact mul_pos (mul_pos (by norm_num) (by positivity)) (zero_lt_one.trans_le (le_max_right _ _))

theorem cash (d q:ℕ) {g L H C:ℝ} (order:2*d+5 ≤ q) (gp:0<g) (cool:g≤1)
    (one:1≤L) (hn:0≤H) (haul:L*g^2≤2) (stock:H*g^2≤4) (small:fee d C*g≤1) :
    (2+4*H)*(2*L^d*(C*g^q)) ≤ L^(-(1/8:ℝ)) := by
  let D:=max C 1
  have pos:0<D:=zero_lt_one.trans_le (le_max_right _ _)
  have posL:0<L:=zero_lt_one.trans_le one
  have hq:g^q ≤ g^(2*d+5):=pow_le_pow_of_le_one gp.le cool order
  have low:(2+4*H)*g^2 ≤ 18:=by
    rw [add_mul,mul_assoc]
    linarith [pow_le_one₀ gp.le cool (n:=2)]
  have hpow:(L*g^2)^d ≤ 2^d:=pow_le_pow_left₀ (by positivity) haul d
  have invoiced:((2+4*H)*(2*L^d*(C*g^q)))*L ≤ 1:=by
    calc
      _ ≤ ((2+4*H)*(2*L^d*(D*g^(2*d+5))))*L:=by
        have hratio:C*g^q ≤ D*g^(2*d+5):=(mul_le_mul_of_nonneg_right (le_max_left C 1) (pow_nonneg gp.le q)).trans
            (mul_le_mul_of_nonneg_left hq pos.le)
        gcongr
      _ = 2*(L*g^2)*((2+4*H)*g^2)*(L*g^2)^d*D*g:=by
        rw [mul_pow,pow_add,pow_mul];ring
      _ ≤ 2*2*18*(2:ℝ)^d*D*g:=by gcongr
      _ = fee d C*g:=by dsimp only [fee,D];ring
      _ ≤ 1:=small
  calc
    _ ≤ 1/L:=(le_div_iff₀ posL).mpr invoiced
    _ = L^(-(1:ℝ)):=by rw [Real.rpow_neg posL.le,Real.rpow_one,one_div]
    _ ≤ L^(-(1/8:ℝ)):=Real.rpow_le_rpow_of_exponent_le one (by norm_num)

/-- Before either Wilson regulator, the measured upper coupling pays the genuine
angular stock, engineering block factor and inverse of the lower stable margin. -/
theorem original {G:Gauge} (R:Run G) (simple:G.Simple) (d q:ℕ) (C:ℝ) (order:2*d+5≤q)
    (slow:∀i,((R.family.S.block i).val:ℝ)≤Real.log (Lambda R.family.path.levels i))
    (ready:WilsonReportLampForecast.Ready R.family.path.levels) :
    ∀ᶠ i:ℕ in atTop, ∀N per, i<N →
      let g:=Coat.gStep (R.family.path.rep N per (i+1)).beta
      let L:ℝ:=(R.family.S.block i).val
      0<g ∧ g≤1 ∧ (2+4*(R.family.path.levels.params i).columns)*(2*L^d*(C*g^q))≤L^(-(1/8:ℝ)) := by
  obtain ⟨j0,hj⟩:=eventually_atTop.mp (IterationFour.Currency.g_small simple R.makes
    ((fee d C)⁻¹) (inv_pos.mpr (fee_pos d C)))
  filter_upwards [eventually_ge_atTop j0,WilsonCenteredReporterClock.original R simple slow ready,
    WilsonReportHarvestUpperAge.block R simple] with i seen clock large N per live
  let g:=Coat.gStep (R.family.path.rep N per (i+1)).beta
  have gp:= (WilsonMeasuredRankedPrimaryBudget.native R simple live per).1
  have feePaid:g≤(fee d C)⁻¹:=(hj (i+1) (seen.trans i.le_succ) N per live).le
  have cold:g≤1:=(one_le_inv₀ gp).mp (clock N per live).1
  have old:((R.family.S.block i).val:ℝ)*g^2 ≤ 2:=(mul_le_mul_of_nonneg_right large
    (sq_nonneg g)).trans (WilsonMeasuredRankedPrimaryBudget.native R simple live per).2
  have hv:= (clock N per live).2.2.2.1
  change (R.family.path.levels.params i).columns≤4*(g⁻¹)^2 at hv
  have width:(R.family.path.levels.params i).columns*g^2≤4:=by
    calc
      _ ≤ (4*(g⁻¹)^2)*g^2:=mul_le_mul_of_nonneg_right hv (sq_nonneg g)
      _ = _:=by field_simp [show g≠0 from gp.ne']
  have one: 1 ≤ ((R.family.S.block i).val:ℝ):=by exact_mod_cast (R.family.S.block i).pos
  have small:fee d C*g≤1:=by
    rw [inv_eq_one_div] at feePaid
    simpa only [mul_comm] using (le_div_iff₀ (fee_pos d C)).mp feePaid
  exact ⟨gp,cold,cash d q order gp cold one (zero_le_one.trans (R.family.path.levels.params i).columns_ge) old width small⟩

end YM.Integration.WilsonMeasuredOwnerAbsorption
