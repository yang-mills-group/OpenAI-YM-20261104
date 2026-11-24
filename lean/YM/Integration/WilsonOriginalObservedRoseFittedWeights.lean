import YM.Integration.WilsonOriginalObservedRoseFittedPurse
import YM.Integration.WilsonReceivedChronologicalBasis
import YM.Integration.WilsonReceivedChronologicalHeldEntrance

/-! The acquired K stencil carries its engineering factor once, also on its constant source label. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseFittedWeights
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
open WilsonReceivedCanonicalVerseBasis (dose)
open WilsonReceivedChronologicalBasis (fare)
open WilsonOriginalMicroscopicEntranceDoseGrid (mass)
open WilsonThermometerDeclaredSeeds (entry)
open WilsonOriginalStarSceneWords (scalar)

theorem slot (a:Fin n→ℂ)(Y:∀i,(C).label (d i))(i:Fin n)(q:Choice R d i):
    dose R d N per K (fun i=>a i • Y i) i q=a i*dose R d N per K Y i q:=by
  cases q with
  | inl q=>rfl
  | inr q=>
    simp only [dose,WilsonThermometerDeclaredSeeds.entry,WilsonOriginalStarSceneWords.scalar,WilsonOriginalStarLaurentWallet.coefficient]
    simp only [map_smul,Pi.smul_apply,smul_eq_mul]
    ring

theorem scales (a:Fin n→ℂ)(Y:∀i,(C).label (d i))(s:(J).Mode)(q:Selection R d s.val):
    weight R d N per K (fun i=>a i • Y i) s.val q=
      (∏i∈s.val,a i)*weight R d N per K Y s.val q:=by
  unfold WilsonReceivedCanonicalVersePortfolio.weight
  simp_rw [slot R d a Y]
  rw [Finset.prod_mul_distrib,Finset.prod_coe_sort]

theorem filed (d:Fin 3→ℕ){f m N per requested power t:ℕ}{B:ℝ}
    (cut:f+m≤N)(A:Panel R d N per f (f+m) (Nat.le_add_right f m) cut requested power t B)
    (file:Filed R d (f+m))(station:A.slot=file.station)(axes:A.axis=file.A N per)
    (c:Fin 3→ℂ)(s:(Stock.census (Fin 3)).Mode)(q:Selection R d s.val):
    fare R d (WilsonReceivedChronologicalHeldEntrance.coords R d cut A) c N per (f+m) s q=
    mass c s*weight R d N per (f+m) (votes R d (N:=N) (per:=per) file A.names A.turn) s.val q:=by
  let a(i:Fin 3):ℂ:=(((C).S.a (f+m):ℂ)^(d i))⁻¹
  let v:=WilsonReceivedChronologicalHeldEntrance.coords R d cut A
  have same:votes R d (N:=N) (per:=per) file A.names A.turn=fun i=>a i • v i:=by
    funext i
    dsimp only [votes,units,doses,WilsonReceivedChronologicalHeldEntrance.coords,v]
    rw [←station,←axes]
  rw [same,scales R d]
  change (mass c s*(∏i∈s.val,a i))*weight R d N per (f+m) v s.val q=
    mass c s*((∏i∈s.val,a i)*weight R d N per (f+m) v s.val q)
  ring

end YM.Integration.WilsonOriginalObservedRoseFittedWeights
end
