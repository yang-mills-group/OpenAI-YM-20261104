import YM.Integration.WilsonEmittedProtectedReturn
import YM.Integration.WilsonCenteredCourseKeeper
import YM.Integration.WilsonCapturedPrimarySection
import YM.Integration.WilsonCenteredDividedRoom
import YM.Integration.WilsonOlderSignedOneMarkRate
import YM.Integration.WilsonMeasuredOriginalColumnSigned

/-! The real joined lower field uses the elected course's own Keeper.  Separate its
healthy derivative bill from its polynomial raw group-field bill before applying
the original hard divisor and restoring the measured source size. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredProtectedColumnFare
open Filter Function Finset Lattice RG Wilson Source Labels Push.Local Planned.GuardedAtom
open Push.AbsoluteSums WilsonCenteredCaptureSlots WilsonCenteredFailedHalo WilsonCenteredMountedCapture
open Trace.Physical PhysicalNext Repeat Legato Roost Org Pert.Asymptotics
open Push.PriceCompiler AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Transit AllOrder.Transit.WheelP
open AnalyticBridge VerifiedReset
open scoped Classical Topology BigOperators

variable {G:Gauge} (R:Run G)
local notation "B" => R.family.path.levels
local notation "A" => R.family
local notation "divisor" => LocalComparison.forcedDivisor R.family

theorem original (simple:G.Simple) (d n q:ℕ) {C ε:ℝ} (hc:0<C) (ep:0<ε) :
    ∀ᶠ i:ℕ in atTop, ∀ (m N per k probe:ℕ) (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin)
      (Ψ:(j:ℕ)→Rep G ((A).side j per)),
    Concourse R.alloy R.kit R.T π Γ m N per k Ψ → m ≤ i → i < N → probe ≤ i →
    ∀ (ι:Type) [Countable ι] (T:ι→Support ((A).side i per)) (f:ι → Config G ((A).side i per)→ℂ)
      (e E:ι→ℝ) (a b M:ℝ), 0<M →
    (∀ s,0∈T s) → (∀ s,(Ψ i).p.Regular (T s) (f s)) →
    SumBudget (fun s=>reservedMass (Ψ i).p (T s) (e s)) a →
    SumBudget (fun s=>reservedMass (Ψ i).p (T s) (E s)) b →
    (∀ s,(Ψ i).p.supBounds 0 (T s) (f s) (e s)) → (∀ s U,‖f s U‖≤E s) →
    b≤(C*(B).clock.hatBeta i^n)*M →
    factor (A).params ((A).localSection d) (Ψ i).p.supportExponent ((B).params i).columns*a ≤
      (ε*(regulatorRun (A) N per probe)^q)*M →
    ∃z:Coefficient ((A).labels.level d) ((A).side i per),
      WilsonTrueProjectedDualHistory.Admitted R Ψ i z (3*(ε*(regulatorRun (A) N per probe)^q)*M) ∧
      ((A).labels.level d).coeffSize z.x≤(ε*(regulatorRun (A) N per probe)^q)*M ∧
      ∀U,z.density 0 ((A).localSection d) (Ψ i) U=((Ψ i).eval U:ℂ)*(∑' s,f s U) :=by
  filter_upwards [WilsonOlderSignedOneMarkRate.paid R simple n q hc ep,
    WilsonCenteredDividedRoom.original R simple,eventually_ge_atTop (R.t d)]
    with i flat gap date m N per k probe π Γ Ψ course before cut report ι tall T f e E a b M hM roots regular
      soft hard tested crude gross good
  let W:=Ψ i
  let κ:=divisor i
  let u₀:=(B).clock.forcedAllowance i
  let g:=regulatorRun (A) N per probe
  let bill:=factor (A).params ((A).localSection d) W.p.supportExponent ((B).params i).columns*a
  let toll:=hitWidth W.p*u₀/κ
  let ready:=course.1.walk i before cut.le
  have pt : W.p=(B).budget i:=ready.truep.point
  have clerk:=(WilsonCenteredCourseKeeper.original R course i before cut).some
  have read:=(WilsonCapturedPrimarySection.original R date W pt).1
  have div:0<κ:=Real.sqrt_pos.mpr (allowance_pos (B).clock i)
  have paying:0≤u₀:=(allowance_pos (B).clock i).le
  have reduced:toll≤1:=by
    dsimp only [toll,κ,u₀];rw [pt];exact gap.2
  have actual:hitWidth W.p*u₀≤1:=((div_le_iff₀ div).mp reduced).trans (by simpa using gap.1)
  obtain ⟨z,form,paid,primary,hears⟩:=WilsonEmittedProtectedReturn.funded W 0 T f clerk
    ((A).localSection d) (A).params ready.truep.valid div paying actual read roots regular e E soft hard tested crude
  have bp:0≤b:=(tsum_nonneg hard.1).trans hard.2.2
  have charged:=flat N per cut.le probe report (b/M) (div_nonneg bp hM.le) ((div_le_iff₀ hM).mpr gross)
  have fixed:toll*b≤(ε*g^q)*M:=by
    apply (div_le_iff₀ hM).mp
    dsimp only [toll]
    rw [pt]
    calc
      _=(hitWidth ((B).budget i)*u₀)*(b/M)/κ :=by ring
      _ ≤ ε*g^q :=charged
  have ap:0≤bill:=(Finset.sum_nonneg (fun _ _=>norm_nonneg _)).trans primary
  have cross:toll*bill≤bill:=mul_le_of_le_one_left ap reduced
  have fee:bill+(toll*b+toll*bill) ≤ 3*(ε*g^q)*M:=by linarith only [good,fixed,cross]
  exact ⟨z,⟨form,Extra.Histories.rem_mono paid fee⟩,primary.trans good,hears⟩

end YM.Integration.WilsonMeasuredProtectedColumnFare
end
