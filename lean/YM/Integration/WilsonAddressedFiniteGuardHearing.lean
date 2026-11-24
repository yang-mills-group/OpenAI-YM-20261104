import YM.Integration.WilsonAddressedFiniteGuardEars
import YM.Integration.WilsonAddressedFiniteGuardTrial
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonAddressedFiniteGuardHearing
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
variable {G:Gauge}(R:Run G){N per m k i:ℕ}(π:ℕ   →   Layout G)(Γ:ℕ   →   Pace.Coin)
    (Ψ:∀j,Rep G (R.family.side j per))(course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    {K:ℕ}(cut:K   ≤   N)(top:Topline (Ψ N) (R.alloy.B.a.clock.forcedAllowance N))
    (simple:G.Simple)(way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (Q:D.Tab R.rolls)(ticket:TicketP R.alloy R.kit D Q){u:ℕ}(floor:m    ≤    u)(ui:u    ≤    i)
    (fixed:WilsonSingleHardRadius.first R simple    ≤    u)(cap:WilsonCenteredCaptureClock.first R simple    ≤    K)
local notation "H" => R.alloy.B.a.clock.hatBeta K
local notation "param" => R.alloy.B.a.budget K
local notation "μ" before:max W:max => WilsonMacroscopicRichFlatPosteriorLaw.law R N per before W


variable {I:Type}[Fintype I][DecidableEq I](d:I   →   ℕ)
open WilsonCapturedPrimaryAngles WilsonCapturedPrimaryCollar WilsonCapturedPrimaryPaid
open WilsonFirstReceivedRadialStencil WilsonOriginalRadialRaySpring


open WilsonAddressedFiniteGuardEars (fare)
open WilsonAddressedFiniteGuardTrial (submitted printed)
open Marker QuadraticLocal.Affinity MergeProof.Accent WilsonOriginalAlternativeExtraction

variable (o:I  →  Site (R.family.side K per))(v:∀a:I,R.family.label (d a))(z:I  →  ℂ)
    (x:Wallet (WilsonOriginalAlternativeFiniteSource.disks (V:=I)))(s:(Stock.census I).Mode)

def hearing (before:i+1 ≤ K)(W:Config G (R.family.side i per)):ℂ:=
  actualTransport R.family (N:=N) (printed R d (N:=N) o v z x s) ((Nat.le_succ i).trans before) W-
    actualTransport R.family (N:=N) (WilsonOriginalAlternativeTrialSource.mode R d N per K o v z x s)
      ((Nat.le_succ i).trans before) W

omit [Fintype I] [DecidableEq I] in
private theorem funded (a:I):
    (R.family.labels.level (d a)).coeffSize (submitted R d v z x a) ≤ 
    (R.family.labels.level (d a)).coeffSize (z a • v a):=by
  have scale:(R.family.labels.level (d a)).coeffSize (submitted R d v z x a)=
      ‖(x a).val‖*(R.family.labels.level (d a)).coeffSize (z a • v a):=by
    unfold submitted
    rw [mul_smul]
    simp only [Frame.coeffSize,Pi.smul_apply,norm_smul,Finset.mul_sum]
  have pocket:‖(x a).val‖ ≤ 1:=(x a).property
  rw [scale]
  exact mul_le_of_le_one_left (Finset.sum_nonneg fun _ _=>norm_nonneg _) pocket

include course cut top way ticket floor ui fixed cap in
theorem original (e p:ℕ){B tol:ℝ}(bp:0 ≤ B)(positive:0<tol)
    (late:(eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple
      (p+WilsonAddressedFiniteGuardCapital.power R d e univ) positive)).choose ≤ K)
    (before:i+1 ≤ K)(strength:(param).supportExponent ≤ 100)
    (income:∀a,(R.family.labels.level (d a)).coeffSize (z a • v a) ≤ B*H^e):
    let read:=hearing R d (N:=N) o v z x s before
    let fee:=fare R (K:=K) d B tol p s.val
    (‖read 1‖ ≤ fee) ∧
    ∀dTest target D, (eventually_atTop.mp (WilsonOriginalRadialDecoderSpring.original R simple dTest target)).choose ≤ i  → 
      1 ≤ (R.family.path.levels.budget i).supportExponent  → 
      ∀a∈tests (R.family.labels.level dTest),∀j ≤ D,
      ‖read (WilsonCapturedPrimaryWeakTrialRadial.field R dTest N per i target D a j)‖ ≤ 2*fee:=by
  intro read fee
  let ξ:=submitted R d v z x
  have wage (a:I):(R.family.labels.level (d a)).coeffSize (ξ a) ≤ B*H^e:=
    (funded R d v z x a).trans (income a)
  have ears:=WilsonAddressedFiniteGuardEars.original R π Γ Ψ course cut top simple way D Q ticket floor ui fixed cap d
    e p bp positive late before strength o ξ wage s.val
  have actual (W:Config G (R.family.side i per)):read W=
      actualTransport R.family (N:=N) (gap R d N per K o ξ s.val) ((Nat.le_succ i).trans before) W:=
    WilsonAddressedFiniteGuardTrial.returned R d cut before o v z x s W
  refine ⟨(congrArg norm (actual 1)).le.trans ears.1,?_⟩
  intro target grade depth qualified shell a ha j hj
  exact (congrArg norm (actual _)).le.trans (ears.2 target grade depth qualified shell a ha j hj)

end YM.Integration.WilsonAddressedFiniteGuardHearing
end
