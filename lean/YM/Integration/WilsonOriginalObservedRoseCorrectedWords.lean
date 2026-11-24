import YM.Integration.WilsonMeasuredPublicEntranceCellWords
import YM.Integration.WilsonReceivedCanonicalVersePosterior

/-! The prior in each upper ordinary face is the original cutoff N. Its
actual corrected, measured K entrance is a signed finite sum on that very
law, with the filed axes and the original K sites fixed throughout. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseCorrectedWords
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


variable {h:Fin n→ℕ}(κ:(j:Fin n)→Knob (h j))(pt:Fin n→Chamber)
def votes (file:Filed R d K)(Y:∀i,(C).label (d i))(turn:Fin n→Motion):∀i,(C).label (d i):=
  units R d K fun i=>Motion.patch ((C).labels.level (d i)) (turn i)
    (doses R d file.station (N:=N) (per:=per) (file.A N per) Y i)
def inputs (fk:f≤K)(o:Fin n→Site ((C).side f per))(s:(J).Mode)(q:Selection R d s.val):
    Config G ((C).side K per)→ℂ:=
  word R d κ pt (regulatorRun C N per K) (fun i=>((C).S.toDepth fk per).embed (o i)) s.val q

theorem sockets (file:Filed R d K)(fk:f≤K)(cut:K≤N)(Y:∀i,(C).label (d i))
    (turn:Fin n→Motion)(o:Fin n→Site ((C).side f per))(s:(J).Mode)
    (uk:u≤K)(U:Config G ((C).side u per)):
    let w:=votes R d (N:=N) (per:=per) file Y turn
    actualTransport C (N:=N) (submitted R d (N:=N) file fk Y turn o s) uk U=
      ∑q:Selection R d s.val,weight R d N per K w s.val q*
        actualTransport C (N:=N) (inputs R d (N:=N) κ pt fk o s q) uk U:=by
  intro w
  have used:=WilsonReceivedCanonicalVersePosterior.original R d κ pt N per K cut w
    (fun i=>((C).S.toDepth fk per).embed (o i)) s.val u uk U
  have equal:submitted R d (N:=N) file fk Y turn o s = fun L=>∏i:s.val,uncut R (d i) N per K
      (((C).S.toDepth fk per).embed (o i)) (w i) L:=by
    funext L
    exact (Finset.prod_coe_sort s.val
      (fun i:Fin n=>uncut R (d i) N per K (((C).S.toDepth fk per).embed (o i)) (w i) L)).symm
  rw [equal]
  exact used

theorem upper (file:Filed R d K)(fk:f≤K)(cut:K≤N)(Y:∀i,(C).label (d i))
    (turn:Fin n→Motion)(o:Fin n→Site ((C).side f per))(s:(J).Mode)(U:Config G ((C).side K per)):
    let w:=votes R d (N:=N) (per:=per) file Y turn
    submitted R d (N:=N) file fk Y turn o s U=
      ∑q:Selection R d s.val,weight R d N per K w s.val q*(inputs R d (N:=N) κ pt fk o s q U):=by
  simpa only [actualTransport_base C R.makes cut] using
    sockets R d κ pt file fk cut Y turn o s le_rfl U

theorem paid (A:Panel R d N per f K fk cut requested power t B)(file:Filed R d K)
    (station:A.slot=file.station)(axes:A.axis=file.A N per)(held:u≤f)(sale:Reading R d A held)
    (one:∀i,1≤A.M i)(E:Fin n→ℕ)(refs:∀i j,j≤d i→(C).ref j≤N)
    (fare:∀i,Next.Rank.Spindle.paid (C) (d i) f N per (A.names i)≤A.M i*(H f)^(E i))
    (s:(J).Mode)(desired:ℕ)(room:desired+∑i∈s.val,E i≤requested):
    let w:=votes R d (N:=N) (per:=per) file A.names A.turn
    ‖reading R (N:=N) (credit C N per 0 (physical R d A.names A.turn A.loc s) K cut) u (held.trans fk)-
      ∑q:Selection R d s.val,weight R d N per K w s.val q*reading R (N:=N)
        (numerator R N per K (inputs R d (N:=N) κ pt fk A.loc s q)) u (held.trans fk)‖ ≤
      (∏i∈s.val,WilsonAddressedHomeDose.ceiling (R:=R) (d i) (A.M i))*((H f)^desired)⁻¹:=by
  intro w
  have close:=WilsonMeasuredPublicEntranceCellWords.paid R d A file station axes held sale one E refs fare s desired room
  have point:=sockets R d κ pt file fk cut A.names A.turn A.loc s (held.trans fk) 1
  have base(q:Selection R d s.val):reading R (N:=N)
      (numerator R N per K (inputs R d (N:=N) κ pt fk A.loc s q)) u (held.trans fk)=
      actualTransport C (N:=N) (inputs R d (N:=N) κ pt fk A.loc s q) (held.trans fk) 1:=
    WilsonThermometerUnitFilingPosterior.weighted R _ _
  simp_rw [base]
  rw [←point,←WilsonThermometerUnitFilingPosterior.weighted]
  exact close

end YM.Integration.WilsonOriginalObservedRoseCorrectedWords
