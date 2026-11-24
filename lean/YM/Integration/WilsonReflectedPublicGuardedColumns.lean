import YM.Integration.WilsonReflectedPublicFiledTrial
/-! The deposited ultraviolet unary and the physically restarted K unary, with
their signed difference on the same numerical forced owners at the reporting site. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicGuardedColumns
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Trace.Physical Trace.Physical.GermGraph Push Push.Local Marker Motion PhysicalNext PhysicalNext.Repeat.Legato
open Trace.Physical.Germ
open Planned.GuardedAtom MergeProof MergeProof.Accent Extra.Multi RG05Readout RG05Readout.Address
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonThermometerReflectedTrajectory
open scoped Topology BigOperators Classical
open WilsonReflectedFundedHearing WilsonReflectedOpticalArm
variable {G:Gauge}(R:Run G){N p f K d:ℕ}
local notation "C₀" => R.family
local notation "F" => R.family.labels.level d
local notation "P₁" => R.family.path.rep N p f

local notation "β" => R.alloy.B.a.clock.hatBeta
open WilsonReflectedPublicSignedFare Extra.Histories.Relay
open WilsonReflectedPublicFiledTrial
structure Joined (A:Arm R d N p f K)(begin:f≤K)(live:K≤N)(dose:ℂ)
    (row:Three G ((C₀).side f p))(wallet head savings:ℝ)
    (Q E:Coefficient (F) ((C₀).side f p)):Prop where
  cash:Q.Format A.o (C₀).params (P₁) ∧ Q.remBound A.o (P₁) (safety (C₀) f) wallet
  coordinate:(F).coeffSize Q.x ≤ head
  regular:row.2.1=Q.exponentialEntry A.o ((C₀).localSection d) (P₁)
  forced:profile (P₁).activities row.2.2=profile (P₁).activities Q.forced
  marked:Q.density A.o ((C₀).localSection d) (P₁) = row.1
  arrived:∀U,Q.density A.o ((C₀).localSection d) (P₁) U=
    dose*((P₁).eval U:ℂ)*WilsonReflectedOriginalTwoDeposit.held R (source R A (begin.trans live)) f U
  difference:Restored R A begin live dose savings E
  onTrial: let D:=trialRow R Q E
    D.Format A.o (C₀).params (P₁) ∧ D.remBound A.o (P₁) (safety (C₀) f) (wallet+savings) ∧
    D.x=Q.x-E.x ∧ (F).coeffSize D.x≤head+savings ∧
    ∀U,D.density A.o ((C₀).localSection d) (P₁) U =
      dose*((P₁).eval U:ℂ)*WilsonReflectedRestartedPair.mean R N (cropped R A begin) f U

theorem deposited (A:Arm R d N p f K)(begin:f≤K)(live:K≤N)(dose:ℂ)
    (row:Three G ((C₀).side f p)){wallet head savings:ℝ}
    (Q E:Coefficient (F) ((C₀).side f p)) (form:Q.Format A.o (C₀).params (P₁))
    (coordinate:(F).coeffSize Q.x≤head)(cash:Q.remBound A.o (P₁) (safety (C₀) f) wallet)
    (r:row.2.1=Q.exponentialEntry A.o ((C₀).localSection d) (P₁))
    (h:profile (P₁).activities row.2.2=profile (P₁).activities Q.forced)
    (report:Q.density A.o ((C₀).localSection d) (P₁)=row.1)
    (field:∀U,row.1 U=dose*((P₁).eval U:ℂ)*WilsonReflectedOriginalTwoDeposit.held R (source R A (begin.trans live)) f U)
    (income:Restored R A begin live dose savings E):
    Joined R A begin live dose row wallet head savings Q E :=by
  have read U:Q.density A.o ((C₀).localSection d) (P₁) U
      = dose*((P₁).eval U:ℂ)*WilsonReflectedOriginalTwoDeposit.held R (source R A (begin.trans live)) f U :=
    (congrFun report U).trans (field U)
  exact ⟨⟨form,cash⟩,coordinate,r,h,report,read,income,
    WilsonReflectedPublicFiledTrial.original R A begin live dose form cash coordinate read income⟩

end YM.Integration.WilsonReflectedPublicGuardedColumns
end
