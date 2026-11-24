import YM.Integration.WilsonAddressedFiniteGuardHeld
import YM.Integration.WilsonAddressedFiniteGuardCapital
import YM.Integration.WilsonOriginalMicroscopicEntranceHeldHalo
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonAddressedFiniteGuardRefund
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open WilsonReceivedQuietCrownOwner OPE.Therm
open WilsonAddressedFiniteGuardFields (cap gap footprint)
open WilsonOriginalMicroscopicEntranceHeldHalo (spring)
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){N per m k i:ℕ}(π:ℕ → Layout G)(Γ:ℕ → Pace.Coin)
    (Ψ:∀j,Rep G (R.family.side j per))(course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    {K:ℕ}(cut:K ≤ N)(top:Topline (Ψ N) (R.alloy.B.a.clock.forcedAllowance N))
    (simple:G.Simple)(way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (Q:D.Tab R.rolls)(ticket:TicketP R.alloy R.kit D Q){u:ℕ}(floor:m  ≤  u)(ui:u  ≤  i)
    (fixed:WilsonSingleHardRadius.first R simple  ≤  u)(cap:WilsonCenteredCaptureClock.first R simple  ≤  K)
local notation "H" => R.alloy.B.a.clock.hatBeta K
local notation "param" => R.alloy.B.a.budget K
local notation "μ" before:max W:max => WilsonMacroscopicRichFlatPosteriorLaw.law R N per before W


variable {I:Type}[Fintype I](d:I → ℕ)
include course cut top way ticket floor ui fixed cap in
/-- A single booked hot event controls every subword of the true finite
    census after the submitted coordinate norm and the chart costs are restored. -/
theorem original (e p:ℕ){B tol:ℝ}(bp:0 ≤ B)(positive:0<tol)
    (late:(eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple
      (p+WilsonAddressedFiniteGuardCapital.power R d e univ) positive)).choose ≤ K)
    (before:i+1 ≤ K)(o:I → Site (R.family.side K per))(v:∀a,R.family.label (d a))
    (income:∀a,(R.family.labels.level (d a)).coeffSize (v a) ≤ B*H^e)(s:Finset I)
    (W:Config G (R.family.side i per)):
    let law:=WilsonMacroscopicRichFlatPosteriorLaw.law R N per before W
    let event:=gap R d N per K o v s
    let reading:=actualTransport R.family (N:=N) event ((Nat.le_succ i).trans before) W
    reading=(∫U,event U ∂law) ∧ ‖reading‖ ≤ spring R i N per W*
      (WilsonAddressedFiniteGuardCapital.price R d B s*
        ((WilsonAddressedFiniteGuardCapital.count R d s:ℝ)*(4*Real.exp ((param).supportExponent+2))*
          (tol/H^p))):=by
  intro law event reading
  let X:=footprint R d per K o s
  let E:=SelectedCofactorAnchoredRegister.hot (G:=G) (R.family.path.rep N per K).p.threshold X
  let tariff:ℝ:=(WilsonAddressedFiniteGuardCapital.count R d s:ℝ)*(4*Real.exp ((param).supportExponent+2))
  let held:=spring R i N per W
  let wage:=WilsonAddressedFiniteGuardCapital.price R d B s
  let debit:=WilsonAddressedFiniteGuardCapital.power R d e univ
  obtain ⟨same,positiveGap⟩:=WilsonAddressedFiniteGuardHeld.original R d cut before o v s W
  refine ⟨same,?_⟩
  have hp₁:1 ≤ H:=(R.family.path.levels.fits.delayed K).le
  have hp:0<H:=zero_lt_one.trans_le hp₁
  have wp:0 ≤ wage:=WilsonAddressedFiniteGuardCapital.price_nonneg R d bp s
  have hpW:0 ≤ held:=sq_nonneg _
  have area:(X.card:ℝ) ≤ (WilsonAddressedFiniteGuardCapital.count R d s:ℝ):=by
    exact_mod_cast WilsonAddressedFiniteGuardCapital.count_bound R d o s
  have hot:=WilsonOriginalMicroscopicEntranceHeldHalo.original R π Γ Ψ course cut top simple way D Q ticket
    floor ui fixed cap (p+debit) positive late before X W
  have money:law.real E ≤ held*(tariff*(tol/H^(p+debit))):=by
    apply hot.trans
    apply mul_le_mul_of_nonneg_left _ hpW
    apply mul_le_mul_of_nonneg_right _ (div_nonneg positive.le (pow_nonneg hp.le _))
    exact mul_le_mul_of_nonneg_right area (by positivity)
  have subtotal:WilsonAddressedFiniteGuardCapital.power R d e s ≤ debit:=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have actual:=WilsonAddressedFiniteGuardCapital.original R d (p:=per) cut v bp e income s
  have cost:2*(∏a∈s,WilsonAddressedFiniteGuardFields.cap R d N per K v a) ≤ wage*H^debit:=
    actual.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hp₁ subtotal) wp)
  have total:=mul_le_mul cost money measureReal_nonneg (mul_nonneg wp (pow_nonneg hp.le _))
  apply positiveGap.trans (total.trans_eq _)
  dsimp only [wage,held,tariff]
  rw [pow_add]
  field_simp [hp.ne']

end YM.Integration.WilsonAddressedFiniteGuardRefund
end
