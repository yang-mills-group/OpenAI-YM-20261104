import YM.Integration.WilsonSeparatedPrefixPanelReturn
import YM.Integration.WilsonSeparatedPrefixHeldPanelReturn
import YM.Integration.WilsonSeparatedPrefixScreenedWord

/-! Convert the same Master panel's complete ordinary reading at a screened node into the fixed optical file. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 750000
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixPanelWord
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
open WilsonSeparatedPrefixPanelReturn (trueFace independentFace)
open WilsonMovingForkSeededPoint (seats)
open WilsonOriginalTwoFlatGridCapture (word)
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){n:ℕ}(d:Fin n→ℕ){N per f K u:ℕ}
local notation "C" => R.family
local notation "H" j:max => R.family.path.levels.clock.hatBeta j
local notation "J" => Stock.census (Fin n)
variable {requested power t:ℕ}{B:ℝ}{fk:f≤K}{cut:K≤N}
variable (A:Panel R d N per f K fk cut requested power t B)

variable (site:Fin n → Lattice.Cover) (file:Filed R d K)
variable (trueY:(i:Fin n) → R.family.label (d i))


theorem upper (rows:A.names=trueY)(addresses:A.loc=snap (C) f per site)(still:A.turn=fun _=>(1,false)):
    trueFace R d A (Stock.final (Fin n))=word R d f N per (fk.trans cut) site trueY:=by
  unfold trueFace
  rw [rows,addresses,still]
  exact WilsonSeparatedPrefixScreenedWord.original R (p:=per) d (fk.trans cut) site trueY

theorem lower (rows:A.names=trueY)(addresses:A.loc=snap (C) f per site)(still:A.turn=fun _=>(1,false)):
    independentFace R d A file (Stock.final (Fin n))=
      product R d (N:=N) (seats (R:=R) fk per site) (doses R d file.station (N:=N) (per:=per) (file.A N per) trueY):=by
  have back:(fun a=>Motion.patch ((C).labels.level (d a)) (A.turn a)
      (doses R d file.station (N:=N) (per:=per) (file.A N per) A.names a))=
      doses R d file.station (N:=N) (per:=per) (file.A N per) trueY:=by
    funext a
    rw [rows,still]
    exact Motion.patch_id ..
  unfold independentFace
  rw [back,addresses]
  rfl

theorem original (rows:A.names=trueY)(addresses:A.loc=snap (C) f per site)(still:A.turn=fun _=>(1,false)) {m apron reserve first j:ℕ}(read:ReadAt R d m N per apron requested t reserve power B first)
    (deep:first≤j)(openJ:m≤j)(height:j+2≤f)(berth:K=WilsonInvariantActionPosition.berth R reserve f)
    (allSlots:∀v,first≤file.station v)(roots:((Fin n)→False) ∨ Ground R N per j f apron (snap (C) f per site))
    (top:m≤u)(uj:u≤j)(firstOpen:Trace.Physical.GermGraph.Opened (C) 0 u per)(lastOpen:Trace.Physical.GermGraph.Opened (C) 0 j per)
    (station:A.slot=file.station)(axes:A.axis=file.A N per)
    (one:∀a,1≤A.M a)(E:Fin n→ℕ)(refs:∀a b,b≤d a→(C).ref b≤N)
    (fare:∀a,Next.Rank.Spindle.paid (C) (d a) f N per (A.names a)≤A.M a*(H f)^(E a))
    (desired:ℕ)(exposure:desired+∑a,E a≤requested):
    let pin:=seats (R:=R) fk per site
    let doses_:=doses R d file.station (N:=N) (per:=per) (file.A N per) trueY
    let road: u≤K:=by omega
    ‖reading R (N:=N) (credit (C) N per 0 (word R d f N per (fk.trans cut) site trueY) K cut) u road-
      reading R (N:=N) (numerator R N per K (product R d (N:=N) pin doses_)) u road‖
      ≤(∏a,WilsonAddressedHomeDose.ceiling (R:=R) (d a) (A.M a))*((H f)^desired)⁻¹:=by
  intro pin doses_ road
  have sold:=WilsonSeparatedPrefixPanelReturn.original R d A read deep openJ height berth
    (station ▸ allSlots) (addresses ▸ roots) top uj firstOpen lastOpen file station axes one E refs fare (Stock.final (Fin n)) desired exposure
  rw [upper R d A site trueY rows addresses still,lower R d A site file trueY rows addresses still] at sold
  exact sold

end YM.Integration.WilsonSeparatedPrefixPanelWord
end
