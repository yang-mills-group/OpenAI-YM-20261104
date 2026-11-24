import YM.Integration.WilsonCapturedPrimaryMasterGridFiling
import YM.Integration.WilsonOriginalMicroscopicGuardedWallet

/-! Site-independent true field salary of the fixed, oriented public trial on the N vacuum. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryMasterGridGross
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories
open PhysicalNext.Repeat.Legato RG16 RG16.Literal WilsonThermometerUnitFilingCoarse
open WilsonThermometerUnitFilingFlatTelescope (numerator)
open WilsonThermometerReflectedTrajectory (anchorAt)
open WilsonReflectedPublicOrientedFaces (displayed)
open WilsonMovingForkMixedSeed WilsonAddressedFiniteGuardTrial WilsonPositionProgramReportedField
open WilsonMeasuredPublicEntrancePanel (Panel Reading charged)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open WilsonPositionProgramBlockedTrialAddBack (uncut)
open WilsonMeasuredPublicEntranceMasterUpper (ReadAt)
open WilsonMeasuredPublicEntranceScreen (Ground)
open PertExtension PertExtension.LatticePT
open MergeProof.Accent Pert.Asymptotics
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Bank.Carp
open WilsonReceivedCanonicalVersePortfolio (Selection weight)
open WilsonReceivedCanonicalVersePosterior (word)
open WilsonThermometerDeclaredSeeds OriginalMarkedSourceComet
open WilsonMeasuredPublicEntranceCellWords (physical submitted)
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)(d:Fin 3→ℕ){N per f K u:ℕ}
local notation "C" => R.family
local notation "H" j:max => R.family.path.levels.clock.hatBeta j
local notation "J" => Stock.census (Fin 3)
variable {requested power t:ℕ}{B:ℝ}{fk:f≤K}{cut:K≤N}

open Extraction WilsonAddressedPhysicalCells


open Motion WilsonOriginalObservedRoseCorrectedWords
open WilsonReceivedCanonicalVersePortfolio (wallet)
variable (A:Panel R d N per f K fk cut requested power t B)(file:Filed R d K)
  (station:A.slot=file.station)(axes:A.axis=file.A N per)
local notation "w" => votes R d (N:=N) (per:=per) file A.names A.turn


open WilsonOriginalMicroscopicGuardedWallet (loss)
open WilsonOriginalMicroscopicGuardedTrial (cap raw unary)
include station axes in
theorem original (s:(J).Mode) (z:Fin 3→Site ((C).side K per))(U:Config G ((C).side K per)):
    ‖submitted R d (N:=N) file (le_refl K) A.names A.turn z s U‖ ≤
      ∏i∈s.val,loss R (d i) K*(B*(H K)^power):=by
  let root:=fun i:Fin 3=>((C).S.toDepth (le_refl K) per).embed (z i)
  change ‖∏i∈s.val,raw R d N per K root w i U‖≤_
  rw [norm_prod]
  apply prod_le_prod (fun _ _=>norm_nonneg _)
  intro i _
  have atField:=((unary R d N per K root w i).2.2 U).2
  have account:=WilsonOriginalMicroscopicGuardedWallet.one R d N per K cut w i
  exact atField.trans (account.trans (mul_le_mul_of_nonneg_left
    (WilsonOriginalObservedRoseFittedPurse.column R d A file station axes i)
    (WilsonOriginalMicroscopicGuardedWallet.nonneg R (d i) K)))

end YM.Integration.WilsonCapturedPrimaryMasterGridGross
end
