import YM.Integration.WilsonOriginalNullPrimaryFees
import YM.Integration.WilsonThermometerOffsetLedger

/-! Price of a measured primary at its deposited site on the original course. -/

set_option quotPrecheck false
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerSameWalkTariff
open Filter Labels Lattice Wilson RG Source Trace.Physical Trace.Physical.Germ
open PhysicalNext Repeat Legato Graces Roost Org Push.Local Extra.Histories Next.Foundations
open Function Filter Set Lattice RG Pressure Tree Wilson Finset MeasureTheory
open PhysicalNext Repeat Legato Graces
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus Blush Mallow
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open Extra.Histories Next.Foundations Labels Peak Mercury
open AllOrder AllOrder.Transit WheelP AllOrder.Floe
open scoped Classical Topology
variable {G:Gauge} (R:Run G) (d:ℕ)
local notation "F₀" => R.family.labels.level d
local notation "T₀" => R.family.localSection d
local notation "B₀" j:max => R.family.path.levels.budget j
local notation "w₀" j:max => price G (max (B₀ j).order (B₀ j).power)
local notation "staff₀" j:max => factor R.family.params T₀ (B₀ j).supportExponent (w₀ j)
local notation "l₀" j:max => GermGraph.factor R.family j
local notation "β₀" => R.family.path.levels.clock.hatBeta

def charge (M:WilsonMeasuredRankedMenu.Menu R d) (i:ℕ):ℝ :=
  (l₀ i)^d*(4*(M.cost*β₀ i)+1)*(M.cost*β₀ (i+1))

theorem paid (M:WilsonMeasuredRankedMenu.Menu R d) {i:ℕ} (enrolled:M.onset ≤ i) {n:Side}
    (o:Site n) (v:(F₀).Coeff):
    (l₀ i)^d*(4*staff₀ i+1)*(B₀ (i+1)).mass ((T₀).footprint o)
        (w₀ (i+1)*(F₀).coeffSize ((F₀).core v)) ≤ charge R d M i*(F₀).coeffSize v:=by
  classical
  have h: (F₀).coeffSize ((F₀).core v)≤(F₀).coeffSize v:=by
    unfold Frame.core Frame.coeffSize
    refine Finset.sum_le_sum fun t _=>?_
    by_cases ht:t=0 <;> simp [ht]
  have cash:0≤(F₀).coeffSize ((F₀).core v):=Finset.sum_nonneg (fun _ _=>norm_nonneg _)
  have βpos (j:ℕ):0≤β₀ j:=zero_le_one.trans (R.family.path.levels.fits.delayed j).le
  have upper:= (WilsonOriginalNullPrimaryFees.slots R d M (i+1) (Nat.le_succ_of_le enrolled) o).2
  have lower:staff₀ i≤M.cost*β₀ i:=(WilsonOriginalNullPrimaryFees.slots R d M i enrolled o).1
  have mass:(B₀ (i+1)).mass ((T₀).footprint o) (w₀ (i+1)*(F₀).coeffSize ((F₀).core v))=
      (B₀ (i+1)).mass ((T₀).footprint o) (w₀ (i+1))*(F₀).coeffSize ((F₀).core v):=by
    unfold BudgetPoint.mass;ring
  have price0:0≤(B₀ (i+1)).mass ((T₀).footprint o) (w₀ (i+1)):=by
    unfold BudgetPoint.mass
    exact mul_nonneg (Real.exp_pos _).le (zero_le_one.trans (price_one_le G _))
  have l0:0≤(l₀ i)^d:=pow_nonneg (zero_le_one.trans (GermGraph.factor_positive R.family i).le) _
  have b0:0≤4*(M.cost*β₀ i)+1:=by have:=M.positive;have:=βpos i;positivity
  rw [mass,charge,mul_assoc ((l₀ i)^d*(4*(M.cost*β₀ i)+1))]
  exact mul_le_mul (mul_le_mul_of_nonneg_left (by linarith only [lower]) l0)
    (mul_le_mul upper h cash (mul_nonneg M.positive.le (βpos _))) (mul_nonneg price0 cash) (mul_nonneg l0 b0)

theorem calendar (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) (M:WilsonMeasuredRankedMenu.Menu R d)
    {ε:ℝ} (small:ε≤1) (i:ℕ):
    charge R d M i*(l₀ i)^ε ≤ (4^(d+1)*(4*M.cost+1)*M.cost)*(β₀ (i+1))^(d+3):=by
  have β1 (j:ℕ):1≤β₀ j:=(R.family.path.levels.fits.delayed j).le
  have mono:β₀ i≤β₀ (i+1):=(Real.log_le_log_iff (zero_lt_one.trans_le (β1 _)) (zero_lt_one.trans_le (β1 _))).1
    (WilsonAdmissionScale.logarithm_monotone R.family.path.levels simple (Nat.le_succ i))
  have mesh:l₀ i≤1+Real.log (2+Real.log (β₀ i)):=by
    change ((R.family.S.block i).val:ℝ)≤_
    exact shop.preMesh i
  have log1:=Real.log_le_sub_one_of_pos (zero_lt_one.trans_le (β1 i))
  have log2:=Real.log_le_sub_one_of_pos (show 0<2+Real.log (β₀ i) by linarith only [Real.log_nonneg (β1 i)])
  have block:l₀ i≤4*β₀ (i+1):=by linarith only [mesh,log1,log2,mono,β1 (i+1)]
  have block1:1≤l₀ i:=(GermGraph.factor_positive R.family i).le
  have small':(l₀ i)^ε≤l₀ i:=by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le block1 small
  have height:0≤4*β₀ (i+1):=by have:=β1 (i+1);positivity
  have M0:=M.positive.le
  have step:4*(M.cost*β₀ i)+1≤(4*M.cost+1)*β₀ (i+1):=by
    nlinarith only [mul_le_mul_of_nonneg_left mono M0,β1 (i+1)]
  have positive:0≤4*(M.cost*β₀ i)+1:=by have:=β1 i;positivity
  have upper:0≤M.cost*β₀ (i+1):=mul_nonneg M0 (zero_le_one.trans (β1 _))
  have f: (l₀ i)^d*(4*(M.cost*β₀ i)+1)≤(4*β₀ (i+1))^d*((4*M.cost+1)*β₀ (i+1)):=
    mul_le_mul (pow_le_pow_left₀ (zero_le_one.trans block1) block d) step positive (pow_nonneg height _)
  calc
    charge R d M i*(l₀ i)^ε ≤
      ((4*β₀ (i+1))^d*((4*M.cost+1)*β₀ (i+1))*(M.cost*β₀ (i+1)))*(4*β₀ (i+1)):=
      mul_le_mul (mul_le_mul_of_nonneg_right f upper) (small'.trans block) (Real.rpow_nonneg (zero_le_one.trans block1) _)
        (mul_nonneg (mul_nonneg (pow_nonneg height _) (by have:=β1 (i+1);positivity)) upper)
    _ = _ :=by simp only [pow_add,mul_pow,pow_one];ring

end YM.Integration.WilsonThermometerSameWalkTariff
end
