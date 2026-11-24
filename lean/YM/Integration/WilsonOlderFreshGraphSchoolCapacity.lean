import YM.Integration.WilsonEmittedOriginalCalendar
import YM.Integration.WilsonOlderFreshGraphFixedFigure

/-! The licensed order and horizon are a *joint* charge of the elected
school. Thus the submitted dictionary already pays for the full original
Waffle at every nonbare receiving date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphSchoolCapacity
open Finset Filter RG Wilson Lattice QuadraticLocal QuadraticLocal.Advent RG.Supply PhysicalNext PhysicalNext.Repeat.Legato
open WilsonLimitConstruction FundedDictionaryPatchPrices WilsonEmittedDictionary AllOrder
open WilsonCoeffUV WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Physical WilsonCoeffUV.Bank.Mosaic
open Comparison.Density Comparison.Density.Mirrors Comparison.Density.Transport
open scoped Topology BigOperators
variable {G:Gauge}(R:Run G){k m:ℕ}(hk:Burn.horizon k+2≤R.alloy.B.a.clock.J m)

include hk in
theorem original (j per h:ℕ)(hm:m≤j)(school:Syl.School k):
    let X:=(R.family.path.levels.clock.op j per).patch
    school.order+school.horizon+1 ≤ capacity X h ∧ school.pieces ≤ capacity X h:=by
  change school.order+school.horizon+1≤h+R.alloy.B.a.clock.J (j+1)+1 ∧
    school.pieces≤h+R.alloy.B.a.clock.J (j+1)+1
  have licensed:Burn.horizon k+2≤R.alloy.B.a.clock.J (j+1):=hk.trans (R.alloy.B.a.fits.mono (hm.trans (Nat.le_succ _)))
  have total:=school.tall.trans licensed
  have pupils:=school.sense.trans licensed
  omega

private theorem doubling (n:ℕ):n≤2^n:=by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have h:0<(2:ℕ)^n:=by positivity
    omega

include hk in
theorem reported (simple:G.Simple)(tube:LinkTube G)(bought:Covered (program tube) R)(h:ℕ):
    let A:=R.family.path.levels
    ∀ᶠ j:ℕ in atTop,∀ _per:ℕ,m≤j → ∀school:Syl.School k,
      let H:=A.clock.hatBeta (j+1)
      let s:=school.order+school.horizon+1
      1<H ∧ (s:ℝ)≤Real.log H ∧ (school.pieces:ℝ)≤Real.log H ∧
      (2:ℝ)^s≤H ∧ (2:ℝ)^s*budgetR R (j+1)≤H^2:=by
  let A:=R.family.path.levels
  have elected:=WilsonEmittedOriginalCalendar.funded tube R simple bought 0 h (cost:=0) (δ:=1) zero_lt_one
  filter_upwards [elected] with j paid
  intro per hm school
  let H:=A.clock.hatBeta (j+1)
  let n:=capacity (A.clock.op j per).patch h
  have pos:0<H:=zero_lt_one.trans (A.fits.delayed (j+1))
  have receipt:=paid per H (by linarith only [pos]) (by linarith only [pos])
  obtain ⟨big,_,_,_,_,_,_,_,_,_,quote,hierarchy,_,wage⟩:=receipt
  have ceiling:(2:ℝ)^n≤Real.log H:=hierarchy.trans quote
  obtain ⟨cohort,seats⟩:=original R hk j per h hm school
  have index_le_two_pow:((n:ℕ):ℝ)≤(2:ℝ)^n:=by exact_mod_cast doubling n
  have spaces:(school.pieces:ℝ)≤n:=by exact_mod_cast seats
  have total:((school.order+school.horizon+1:ℕ):ℝ)≤n:=by exact_mod_cast cohort
  have raised:(2:ℝ)^(school.order+school.horizon+1)≤H:=
    ((pow_le_pow_right₀ (by norm_num :(1:ℝ)≤2) cohort).trans ceiling).trans
      ((Real.log_le_sub_one_of_pos pos).trans (by linarith))
  exact ⟨big,total.trans (index_le_two_pow.trans ceiling),spaces.trans (index_le_two_pow.trans ceiling),raised,
    ((mul_le_mul_of_nonneg_left wage (pow_nonneg (by norm_num :(0:ℝ)≤2) _)).trans (mul_le_mul_of_nonneg_right raised pos.le)).trans_eq (sq H).symm⟩

end YM.Integration.WilsonOlderFreshGraphSchoolCapacity
end
