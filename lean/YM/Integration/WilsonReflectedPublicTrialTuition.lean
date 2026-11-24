import YM.Integration.WilsonReflectedPublicTrialCalendar
import YM.Integration.WilsonReflectedPublicTrialRoster
/-! The two original preframe programmes receive their actual finite guarded
columns at the same pair of optical dates before the regulators are read. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicTrialTuition
open Lattice Wilson RG Source Extraction Maxwell Maxwell.Free RG05Readout
open PhysicalNext.Repeat.Legato FVA2 FVA2.Register MS MS.Land
open Function Filter Set Table Spec Climb GapsContact GapsContact.Seams OPE Trace.Pilot
open Next.Rank Next.Rank.Station MergeProof.East Next.UVStress Trace.Terrace Trace.Pilot
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare
open WilsonReflectedOpticalArm WilsonReflectedFullPanel WilsonReflectedFundedHearing
open WilsonOriginalMicroscopicGuardedPage WilsonReflectedRestoredStation
open Source Labels Extra.Histories Extra.Histories.Relay Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open WilsonOriginalNullCorridor MergeProof MergeProof.Accent
open scoped Topology Classical
variable {G : Gauge} {R : Run G} {u : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family u S) {l : Ultrafilter (ℕ×ℕ)} {z : Trace.Terrace.Arch R.family}
    {H : (Bel R.family.book).Hierarchy}
local notation "C₀" => R.family
local notation "levels" => R.family.path.levels
local notation "mesh" => R.family.S.a
local notation "β" => R.family.path.levels.clock.hatBeta

open WilsonReflectedPublicTrialCalendar

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (width:∀i,((levels).budget i).supportExponent ≤ 100)(D d T q:ℕ)(cap:d ≤ D):
    ∃C:ℝ,0<C ∧ ∀ᶠ r in trail,∀{k:ℕ}
      {stock:Bank F l D (WilsonThermometerUnitFilingFourPoolShell.radius z T r)
        (dock (WilsonThermometerUnitFilingFourPoolShell.radius z T r)^T)}
      {W:Vane R.family k}{fits:D ≤ k}{U:Spin.change S d}
      (P:Pair F stock cap W fits U r),W.checked u H k→W.wheel.r=r→
    let m:=max stock.j W.k
    let f:=WilsonInvariantActionPosition.berth R 5 m
    let K:=WilsonInvariantActionPosition.berth R (WilsonReflectedOpticalRate.depth (q+1+2) (2*T+9) D) f
    ∀b:Bool,let j:=station F P b
      ∃ (head:j ≤ K),∀N p (top:K ≤ N)(v:S.Field d)(M:(C₀).label d≃ₗ[ℂ](C₀).label d)(jets:ℕ),
      let Y:=(P.arm b v).source (N,p)
      receipt R d j K N p jets head top (1/32) M Y (mesh j^d*fee F P b v) →
      ∀A:Arm R d N p f K,A.w=M.symm (WilsonOriginalMicroscopicGuardedPage.full R d N p j Y) →
      ∀dose:ℂ,‖dose‖ ≤ 1 →
      ‖dose*(((mesh K:ℂ)^d)⁻¹)‖*((C₀).labels.level d).coeffSize (WilsonReflectedPublicGuardedMotion.coords R A) ≤
        C*(β f)^(span D T q*(d+1)+2)*fee F P b v:=by
  obtain ⟨C,cp,going⟩:=WilsonReflectedPublicTrialCalendar.original F simple bliss slow width D d T q cap
  let Ω:=Extra.Histories.Motion.orbitCost ((C₀).labels.level d)
  have op:0<Ω:=lt_of_lt_of_le (by norm_num:(0:ℝ)<1) (Extra.Histories.Motion.orbitCost_one_le _)
  refine ⟨Ω*(2*C),mul_pos op (mul_pos (by norm_num) cp),?_⟩
  filter_upwards [going] with r sale k stock W fits U P cleared exactR m f K b j
  obtain ⟨early,deep,hp,ratio,non,cash⟩:=sale P cleared exactR b
  refine ⟨early.trans deep.le,?_⟩
  intro N p top v M jets Y receipt A wage dose small
  obtain ⟨_,income⟩:=WilsonReflectedPublicStationFare.original F P cleared b v
  have phys:=income N p ((early.trans_lt deep).trans_le top)
  have nn:0 ≤ Next.UVStress.quota (C₀) d j N p Y:=by unfold Next.UVStress.quota Labels.Frame.coeffSize;positivity
  have vpos:0 ≤ fee F P b v:=
    nonneg_of_mul_nonneg_right (nn.trans phys) (pow_pos ((C₀).S.a_pos j) d)
  have total:=WilsonReflectedPublicTrialCapital.priced R (early.trans deep.le) early top cp.le vpos hp
    ratio non cash receipt (A.s,A.b) small
  simpa only [WilsonReflectedPublicGuardedMotion.coords,wage] using total

end YM.Integration.WilsonReflectedPublicTrialTuition
end
