import YM.Integration.WilsonOriginalObservedRoseFittedPurse

/-! The public file fixes all fitted coefficients before varying the K-sites or the ordinary subface of the same physical trial. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryMasterGridFiling
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
variable {G:Gauge}(R:Run G){n:ℕ}(d:Fin n→ℕ){N per f K u:ℕ}
local notation "C" => R.family
local notation "H" j:max => R.family.path.levels.clock.hatBeta j
local notation "J" => Stock.census (Fin n)
variable {requested power t:ℕ}{B:ℝ}{fk:f≤K}{cut:K≤N}

open Extraction WilsonAddressedPhysicalCells


open Motion WilsonOriginalObservedRoseCorrectedWords
open WilsonReceivedCanonicalVersePortfolio (wallet)
variable (A:Panel R d N per f K fk cut requested power t B)(file:Filed R d K)
  (station:A.slot=file.station)(axes:A.axis=file.A N per)
local notation "w" => votes R d (N:=N) (per:=per) file A.names A.turn

variable {h:Fin n→ℕ}(κ:(j:Fin n)→Knob (h j))(pt:Fin n→Chamber)

include station axes in
theorem original (s:(J).Mode):
    (∑q:Selection R d s.val,‖weight R d N per K w s.val q‖) ≤
       wallet R d (fun _=>B*(H K)^power) s.val ∧
    ∀z:Fin n→Site ((C).side K per),
      (∀U,submitted R d (N:=N) file (le_refl K) A.names A.turn z s U=
        ∑q:Selection R d s.val,weight R d N per K w s.val q*
          word R d κ pt (regulatorRun C N per K) z s.val q U) ∧
      ∀ b:ℕ,∀ (bk:b≤K)(W:Config G ((C).side b per)),
        actualTransport C (N:=N) (submitted R d (N:=N) file (le_refl K) A.names A.turn z s) bk W=
          ∑q:Selection R d s.val,weight R d N per K w s.val q*
            actualTransport C (N:=N) (word R d κ pt (regulatorRun C N per K) z s.val q) bk W:=by
  refine ⟨WilsonOriginalObservedRoseFittedPurse.original R d A file station axes s,?_⟩
  intro z
  have same:(R.family.S.toDepth (le_refl K) per).embed= id:=by
    funext a
    change (R.family.S.toDepth (le_refl K) per).embed a=a
    rw [Ratio.embed,show (R.family.S.toDepth (le_refl K) per).count.val=1 from by
      simp only [Schedule.toDepth,Nat.sub_self,Schedule.steps]
      rfl,one_smul,wrap_lift]
  constructor
  · intro U
    simpa only [inputs,same,id_eq] using
      WilsonOriginalObservedRoseCorrectedWords.upper R d κ pt file (le_refl K) cut A.names A.turn z s U
  · intro b bk W
    simpa only [inputs,same,id_eq] using
      WilsonOriginalObservedRoseCorrectedWords.sockets R d κ pt file (le_refl K) cut A.names A.turn z s bk W

end YM.Integration.WilsonCapturedPrimaryMasterGridFiling
end
