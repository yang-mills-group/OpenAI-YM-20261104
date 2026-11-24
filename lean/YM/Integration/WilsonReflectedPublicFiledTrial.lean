import YM.Extra.SOURCE_HISTORIES.Beside
import YM.Integration.WilsonReflectedPublicFiledSingle
import YM.Integration.WilsonReflectedPublicOpticalSwaps
/-! The whole native record of the K trial on the original reporting density.
Both original compulsory rosters are retained in the two summands. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicFiledTrial
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
def trialRow {n:Side} (Q E:Coefficient (F) n) : Coefficient (F) n :=
  beside Q (stretch (-1) E)

theorem original (A:Arm R d N p f K)(begin:f≤K)(live:K≤N)(c:ℂ)
    {Q E:Coefficient (F) ((C₀).side f p)} {wallet head fee:ℝ}
    (form:Q.Format A.o (C₀).params (P₁)) (paid:Q.remBound A.o (P₁) (safety (C₀) f) wallet)
    (size:(F).coeffSize Q.x≤head)
    (field:∀U, Q.density A.o ((C₀).localSection d) (P₁) U =
      c*((P₁).eval U:ℂ)*WilsonReflectedOriginalTwoDeposit.held R (source R A (begin.trans live)) f U)
    (error:Restored R A begin live c fee E):
    let D:=trialRow R Q E
    D.Format A.o (C₀).params (P₁) ∧ D.remBound A.o (P₁) (safety (C₀) f) (wallet+fee) ∧
      D.x=Q.x-E.x ∧ (F).coeffSize D.x≤head+fee ∧
      ∀U, D.density A.o ((C₀).localSection d) (P₁) U =
        c*((P₁).eval U:ℂ)*WilsonReflectedRestartedPair.mean R N (cropped R A begin) f U :=by
  intro D
  have neg:(stretch (-1) E).remBound A.o (P₁) (safety (C₀) f) fee :=by
    simpa only [norm_neg,norm_one,one_mul] using stretch_rem (-1) error.paid
  obtain ⟨dfit,dbill⟩:=presentation form paid (stretch_format (-1) error.form) neg
  have old:D.x=Q.x-E.x:=by
    change (beside Q (stretch (-1) E)).x=_
    rw [reckon];change Q.x+(-1:ℂ) • E.x=Q.x-E.x
    simp only [neg_one_smul,sub_eq_add_neg]
  refine ⟨dfit,dbill,old,?_,?_⟩
  · have loss: (F).coeffSize ((-1:ℂ) • E.x) ≤ fee :=by
      simpa only [Size.smul,norm_neg,norm_one,one_mul] using error.primary
    exact ((Size.add (F) _ _).trans (add_le_add size loss) :
      (F).coeffSize (Q.x+(-1:ℂ) • E.x) ≤ _ ) |> (fun good=> by simpa only [old,neg_one_smul,sub_eq_add_neg] using good)
  · intro U
    calc
      _ = Q.density A.o ((C₀).localSection d) (P₁) U + (stretch (-1) E).density A.o ((C₀).localSection d) (P₁) U :=
        congrFun (plus (R.makes.wilson.represents N p f (begin.trans live)).good paid neg ((C₀).localSection d)) U
      _ = _ := by rw [stretch_density,field U,error.field U];ring

end YM.Integration.WilsonReflectedPublicFiledTrial
end
