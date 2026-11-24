import YM.Integration.WilsonReceivedQuietCrownOwner
import YM.Integration.WilsonMeasuredOwnerIntegrable
import YM.Integration.WilsonThermometerUnitFilingFlatTelescope
import YM.Integration.WilsonThermometerEarlierWallet
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedQuietCrownFlat
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G) {N per m k b:ℕ} (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin)
   (Ψ:∀j,RG.Rep G (R.family.side j per)) (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
   (top:b ≤ N) {d:ℕ} {F:Frame G d} (S:SectionData F) (A:Hol G)
   (y:Site (R.family.side b per)) (q:Coefficient F (R.family.side b per))
   (law:q.Format y A (Ψ b)) {M:ℝ} (income:q.remBound y (Ψ b) (LocalComparison.forcedDivisor R.family b) M)
local notation "κ" => LocalComparison.forcedDivisor R.family b
local notation "β" => R.alloy.B.a.clock.hatBeta b
local notation "vac" => R.family.path.rep N per b
local notation "W" => Ψ b
local notation "J" => Stock.census (Fin 1)
local notation "wallet" => Wallet WilsonMeasuredOwnerReserve.disk
open WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingFlatTelescope
open WilsonReceivedQuietCrownOwner
open WilsonThermometerEarlierWallet
variable (simple:G.Simple) (way:WayStation R.kit)
   (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
   (ticket:TicketP R.alloy R.kit D Q) {u:ℕ} (floor:m ≤ u) (ub:u ≤ b)
   (fixed:WilsonSingleHardRadius.first R simple ≤ u)
   
include way ticket course top floor ub fixed S A in
theorem one {f:Config G (R.family.side b per)→ℂ}{C:ℝ}
    (income:Owned (F:=F) (Ψ b) A y κ C f)
    (p:ℕ) {ε:ℝ}(ep:0<ε)(late:WilsonSingleHardRadius.start R simple p ep≤b):
    Admitted (u:=u) (N:=N) R (le_refl b) f (4*(1+|C|)*ε/(β)^p):=by
  obtain ⟨owner,fit,bill,exactly⟩:=income
  rw [←funext exactly]
  refine ⟨WilsonMeasuredOwnerIntegrable.original R π Γ Ψ course (floor.trans ub) top S A y owner fit bill,?_⟩
  intro j uj jb
  have price:=WilsonMeasuredOwnerFlatCourse.order R π Γ Ψ course top S A y owner fit bill simple way D Q ticket floor ub fixed
    (show 0<1+|C| by positivity) (show C≤1+|C| from (le_abs_self C).trans (le_add_of_nonneg_left zero_le_one)) uj jb p ep late
  let f':=fun U=>((Ψ b).eval U)⁻¹ • account owner (Ψ b) U
  have num: numerator R N per b f'=account owner (Ψ b):=by
    funext U
    have same:(Ψ b).eval=(R.family.path.rep N per b).eval:=(course.1.walk b (floor.trans ub) top).view
    have pos:0<(R.family.path.rep N per b).eval U:=Multi.AxisShift.chosen_positive R.makes.wilson top U
    change ((R.family.path.rep N per b).eval U:ℂ)*(((Ψ b).eval U)⁻¹ • account owner (Ψ b) U)=_
    rw [same,Complex.real_smul,Complex.ofReal_inv,←mul_assoc,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr pos.ne'),one_mul]
  rw [←num]
  have read:=WilsonThermometerUnitFilingPosterior.weighted R (N:=N) f' jb
  change reading R (N:=N) (numerator R N per b f') j jb=actualTransport R.family (N:=N) f' jb 1 at read
  rw [read]
  exact price

theorem sum {G:Gauge}(R:Run G){b u N per:ℕ}{S:Type}[DecidableEq S](roster:Finset S)
    (f : S → Config G (R.family.side b per)→ℂ)(fee:S→ℝ)
    (admitted:∀q∈roster,Admitted (u:=u) (N:=N) R (le_refl b) (f q) (fee q)):
    Admitted (u:=u) (N:=N) R (le_refl b) (∑q∈roster,f q) (∑q∈roster,fee q):=by
  induction roster using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine ⟨integrable_zero _ _ _,?_⟩
    intro j _ jb
    have z:=WilsonThermometerUnitFilingRawSum.scaled R (N:=N) (p:=per) (0:ℂ) (0:Config G (R.family.side b per)→ℂ)
      (integrable_zero ..) jb
    simpa using (congrArg norm z).le
  | insert q roster new ih =>
    rw [Finset.sum_insert new,Finset.sum_insert new]
    exact plus R (admitted q (mem_insert_self ..)) (ih (fun a ha=>admitted a (mem_insert_of_mem ha)))


end YM.Integration.WilsonReceivedQuietCrownFlat
