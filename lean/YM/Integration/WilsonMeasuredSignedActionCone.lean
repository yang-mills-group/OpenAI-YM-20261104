import YM.Integration.WilsonPhysicalStationPrincipalGrade
import YM.Integration.WilsonIndependentUnaryPrincipal
import YM.Integration.WilsonOriginalPublicTrialPhaseFourDictionary
import YM.Integration.WilsonIndependentRegisteredThermalRatios
import YM.FullVolume.Gables.Vendee

/-! The unit transmits exactly. Every original rank-two direction at cap
four has the same positive principal multiplier. On a real invariant
line the error preserves sign through each individual edge. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedActionCone
open Function Filter Finset Labels Wilson Lattice RG Source Extra.Histories Bid
open PhysicalNext.Repeat.Legato
open scoped Topology Classical BigOperators
variable {G:Gauge}(F:Frame G 4)

theorem core (simple:G.Simple)(U:Heading F)(L:Side){hi lo:ℝ}
    (head:WilsonIndependentUnaryPrincipal.Signed U hi lo)(x:F.Coeff):
    F.core (U.leads L x)=(((lo/hi)^2:ℝ):ℂ) • F.core x:=by
  have floor:WilsonPhysicalStationPrincipalGrade.above 4 (F.core x):=by
    intro i low
    by_cases z:i=0
    · subst i;simp [Frame.core]
    · rw [WilsonOriginalPublicTrialPhaseFourDictionary.weight F simple i z] at low
      exact (Nat.lt_irrefl 4 low).elim
  change F.core (U.map (vowel F L x))=_
  rw [← U.core_comm,Work.G08.core_vowel]
  change U.leads L (F.core x)=_
  ext i
  rw [WilsonPhysicalStationPrincipalGrade.one U head.through L floor i (F.bound i)]
  by_cases unit:i=0
  · subst i;simp [Frame.core]
  · rw [WilsonOriginalPublicTrialPhaseFourDictionary.weight F simple i unit]
    simp

private theorem core_sub (x y:F.Coeff):F.core (x-y)=F.core x-F.core y:=by
  funext i
  by_cases z:i=0
  · subst i;simp [Frame.core]
  · simp [Frame.core,z]

theorem size (x:F.Coeff)(a:ℝ):F.coeffSize ((a:ℂ) • x)= |a| * F.coeffSize x:=by
  simp [Frame.coeffSize,Finset.mul_sum,Real.norm_eq_abs]

theorem oriented (simple:G.Simple)(U:Heading F)(L:Side){hi lo:ℝ}
    (head:WilsonIndependentUnaryPrincipal.Signed U hi lo){x y z:F.Coeff}
    (nz:0<F.coeffSize z){a b:ℝ}(fine:F.core x=(a:ℂ) • z)(coarse:F.core y=(b:ℂ) • z)
    (bought:F.coeffSize (y-U.leads L x)≤barunit L*F.coeffSize (F.core x))
    (reserve:barunit L<(lo/hi)^2)(positive:0<a):0<b:=by
  have get: F.coeffSize (F.core (y-U.leads L x)) ≤barunit L*F.coeffSize (F.core x):=
    (Work.G08.size_core F _).trans bought
  rw [core_sub,core F simple U L head x,coarse,fine,smul_smul,← sub_smul] at get
  rw [show (b:ℂ)-↑((lo/hi)^2)*(a:ℂ) = ((b-(lo/hi)^2*a:ℝ):ℂ) by push_cast;ring,
    size,size] at get
  have bounds:|b-(lo/hi)^2*a|≤barunit L*|a|:=by
    apply (mul_le_mul_iff_of_pos_right nz).mp
    simpa only [mul_assoc] using get
  rw [abs_of_pos positive] at bounds
  have tiny:=mul_lt_mul_of_pos_right reserve positive
  linarith only [(neg_le_abs (b-(lo/hi)^2*a)),bounds,tiny]

theorem affordable (R:Run G)(simple:G.Simple):∀ᶠ j:ℕ in atTop,
    barunit (R.family.S.block j)<((R.family.path.levels.budget j).threshold/
      (R.family.path.levels.budget (j+1)).threshold)^2:=by
  filter_upwards [WilsonIndependentRegisteredThermalRatios.appointed R simple] with j pair
  let c:= (R.family.path.levels.budget j).threshold
  let f:= (R.family.path.levels.budget (j+1)).threshold
  have fp:0<f:=(R.family.path.levels.budget (j+1)).threshold_pos
  have near : f ≤ 2*c := pair.2
  have slope: (1/2:ℝ)≤c/f:=(le_div_iff₀ fp).mpr (by linarith only [near])
  let k:=R.w.K (R.family.path.levels.clock.J (j+1)+1)
  let s:=(R.family.path.levels.params (j+1)).columns
  have paid:100000*k^6*(1+s)^2≤puffs (R.family.S.block j):=R.b.clock.bank j
  have kw:1≤k:=R.w.prices _
  have sw : 1 ≤ s :=(R.family.path.levels.params (j+1)).columns_ge
  have big:2≤puffs (R.family.S.block j):=le_trans (by
    have k6:1≤k^6:=one_le_pow₀ kw
    have s2:1≤(1+s)^2:=one_le_pow₀ (by linarith only [sw])
    nlinarith [mul_le_mul_of_nonneg_left s2 (show 0≤k^6 by positivity)]) paid
  have pos:0<puffs (R.family.S.block j):=by linarith only [big]
  have small:(puffs (R.family.S.block j))⁻¹≤(1/2:ℝ):=by
    rw [inv_eq_one_div,div_le_div_iff₀ pos (by norm_num : (0:ℝ)<2)];linarith only [big]
  exact (pow_le_pow_left₀ (inv_nonneg.mpr pos.le) small 3).trans_lt
    (lt_of_lt_of_le (by norm_num:(1/2:ℝ)^3<(1/2:ℝ)^2) (pow_le_pow_left₀ (by norm_num) slope 2))

end YM.Integration.WilsonMeasuredSignedActionCone
end
