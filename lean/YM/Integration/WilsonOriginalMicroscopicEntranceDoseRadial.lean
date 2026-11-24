import YM.Integration.WilsonOriginalMicroscopicEntranceSettledHeld
import YM.Integration.WilsonOriginalRadialBoard

/-! Both original calibrations, all true flags and the held prior price at one radial decoder field. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceDoseRadial
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open WilsonReceivedQuietCrownOwner OPE.Therm
open WilsonOriginalMicroscopicGuardedTrial WilsonOriginalMicroscopicGuardedWallet
open Extra.Histories Extra.Multi Push.AbsoluteSums.Animals
open WilsonOriginalMicroscopicEntranceFiling (units)
open WilsonOriginalMicroscopicEntranceGridBalance (slotFare)
open WilsonOriginalMicroscopicEntranceOpticalUnits (pole rank dye fare)
open WilsonOriginalMicroscopicGuardedFlat (peak count)
open Trace.Physical.Germ Trace.Physical.GermGraph
open scoped BigOperators Classical

open WilsonCoeffUV.Embroider
variable {G:Gauge}(R:Run G)

theorem flags_eq {N per m k u:ℕ}(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)(Ψ:∀j,RG.Rep G (R.family.side j per))
    (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)(lo:m≤u)(hi:u≤N)(W:Config G (R.family.side u per)):
    flags (Ψ u).p.threshold W=flags (R.family.path.rep N per u).p.threshold W:=by
  have a: (Ψ u).p=R.family.path.levels.budget u:=(course.1.walk u lo hi).truep.point
  have b:(R.family.path.rep N per u).p=R.family.path.levels.budget u:=(R.makes.wilson.represents N per u hi).vac
  rw [a,b]

theorem original (simple:G.Simple)(degree target:ℕ):
    ∀ᶠ u in atTop,∀{N per m k D:ℕ}(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)(Ψ:∀j,RG.Rep G (R.family.side j per))
      (_course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)(_floor:m≤u)(_old:u<N)
      (_a:1≤(R.family.path.levels.budget u).supportExponent),∀a∈tests (R.family.labels.level degree),∀t≤D,
      let W:=WilsonCapturedPrimaryWeakTrialRadial.field R degree N per u target D a t
      flags (R.family.path.rep N per u).p.threshold W=∅ ∧ flags (Ψ u).p.threshold W=∅ ∧
        WilsonOriginalMicroscopicEntranceHeldHalo.spring R u N per W≤2:=by
  filter_upwards [WilsonOriginalRadialBoard.original R simple degree target] with u panel
  intro N per m k D π Γ Ψ course floor old a0 a mem t hi W
  obtain ⟨clear,price⟩:=panel (N:=N) (per:=per) (D:=D) old a0 a mem t hi
  exact ⟨clear,(flags_eq R π Γ Ψ course floor old.le W).trans clear,price⟩

end YM.Integration.WilsonOriginalMicroscopicEntranceDoseRadial
end
