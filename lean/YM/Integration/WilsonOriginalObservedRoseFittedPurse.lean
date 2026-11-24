import YM.Integration.WilsonOriginalObservedRoseCorrectedWords

/-! Cost of the actual complete K-socket sum on the elected optical field. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseFittedPurse
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

include station axes in
theorem column (i:Fin n):((C).labels.level (d i)).coeffSize (w i)≤B*(H K)^power:=by
  let F:=(C).labels.level (d i)
  let ξ:ℂ:=(((C).S.a K:ℂ)^(d i))⁻¹
  let y:=(A.axis i).symm (fitted R (d i) (A.slot i) N per (A.names i))
  change F.coeffSize (ξ • Motion.patch F (A.turn i) (doses R d file.station (N:=N)
    (per:=per) (file.A N per) A.names i))≤_
  rw [←station,←axes]
  change F.coeffSize (ξ • Motion.patch F (A.turn i) y)≤_
  have bought:F.coeffSize (ξ • y)≤A.tuition*(H K)^power:=(A.fixed i).2.1
  have pos:0≤(H K)^power:=pow_nonneg (zero_le_one.trans (R.family.path.levels.fits.delayed K).le) _
  calc
    _≤orbitCost F*F.coeffSize (ξ • y):=by
      rw [Size.smul,Size.smul]
      calc
        _≤‖ξ‖*(orbitCost F*F.coeffSize y):=mul_le_mul_of_nonneg_left (patch_cost F (A.turn i) y) (norm_nonneg _)
        _=_:=by ring
    _≤orbitCost F*(A.tuition*(H K)^power):=
      mul_le_mul_of_nonneg_left bought (zero_le_one.trans (orbitCost_one_le F))
    _≤B*(H K)^power:=by rw [←mul_assoc];exact mul_le_mul_of_nonneg_right (A.priced i) pos

include station axes in
theorem original (s:(J).Mode):
    (∑q:Selection R d s.val,‖weight R d N per K w s.val q‖)≤
       wallet R d (fun _=>B*(H K)^power) s.val:=
  WilsonReceivedCanonicalVersePortfolio.priced R d N per K cut (w) s.val _
    fun j _=>column R d A file station axes j

end YM.Integration.WilsonOriginalObservedRoseFittedPurse
end
