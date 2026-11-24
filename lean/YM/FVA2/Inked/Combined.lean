import YM.FVA2.Inked.TrueF
import YM.FVA2.O.Canon.Give
/-!
# The full rank-budgeted result, no mask or extra tree-jet hypothesis needed

Includes the `Teller`/`TreeT` comparison, which extends the initial
formal-to-formal comparison to keep the stricter demands in the preparation of the
fields. The comparison uses the Taylor jets of the physical stencils at the
inputs (see `Pitch` and `TrueF`). An asymptotic comparison with physical
expectation values requires separate analytic estimates.
 -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Inked
open Function Filter Set Finset MeasureTheory Topology
open scoped ContDiff BigOperators Classical
open Lattice RG Maxwell Gen Press
open MS MS.Koszul MS.Plane MS.Native MS.Native.Sew MS.Native.Draft MS.Cylinder.Taylor MS.Momentum MS.Theater
open MS.Color MS.Arts MS.Motif MS.Landau MS.Landau.Detect MS.Local.Physical MS.Lifting MS.Halo MS.Book MS.Heat MS.Tone MS.Plane.Wire Source
open Position Position.Axes Position.Favors Position.OpenAxis
variable {G:Gauge}
local notation "Γ"=> portDeck G
local notation "ĉ"=> Plot Γ
open MS.Land MS.Menus MS.Motif.Literal
open Register Register.WilsonPrescription Recall Arrival Arrival.Episodic Reg XSpace
open Teller TreeT
variable (U: Land.MS_Data G (Plot (Press.portDeck G))) (N:Register.WilsonPrescription G)(h:G.Simple)
include h
local notation "F"=> Register.WilsonPrescription.scheme N
local notation "K"=> Register.WilsonPrescription.criterion N
local notation "K0"=> (Continuum.Continuation.proofStart h (Reg.supplies F U))
lemma no_top_price (t:Bool): ∃ M:Prescription (Press.portDeck G), M.team=( K0 t ).team ∧ Teller.Homes.Installed F U M true:= by
    apply Homes.spectrum F U h ( Continuum.Continuation.plan ( Reg.supplies F U ) h t |>.taylor.bulk ) (b:=true); intro _ d i; exact TreeT.treeOK (wickInput N.scheme) U i h (inherent N.scheme i) _
-- Replicate strong supplier, this time with nonlinear tree stencil verification to choose strict version.
lemma insured (M:Prescription (Press.portDeck G))(H: Homes.Installed F U M true): Served N U M:= by
    obtain H' : Speed.Quoted F K U M:= Speed.beats_all F K M U h ( Scale.System.promotes F K U M h ⟨ Reg.lifts F K U h M H.toSag, fun n E J p W _ u d P x s=> Episodic.platform F E p u M d P x s, fun n E J p=> candle_eq F E p, fun n E J p=>eraVal F E p ⟩ )
    exact ⟨ ⟨ H', Expense.Stretched.runs N.run,fun i b=> sum_world _ _ _ _, fun {W} x u L d i v y=>Rescaled.on_clock _ _ _ _ _ _ _ _ _ ⟩, H.priced,fun t=> Parity.Clock.measured t F _ U M h H.Taylor H.still H.base ⟩
/-- Comparison incl. `Served` (packaging results through `Scale.System.Contract` etc.). Extend previous
 statement with stricter selection of D. Existing estimates on other Booked conventions wherever expressly
 proved in other files (not claiming OPE works on all other universes). Fix against `OpenAxis.Plot`. -/
theorem strict_establishment (dial:Bool):
      ∃ M:Prescription (Press.portDeck G), M.team=( K0 dial ).team ∧
      Homes.Installed F U M true ∧ Served N U M ∧
      ∀ ν:ℝ,O.Canon.Supplied N U ν
      := by
      obtain ⟨M,hv,H⟩:= no_top_price U N h dial; obtain he:=insured U N h M H;
      exact ⟨M,hv,H,he,O.Canon.provides N he.toPosted.toQuoted.toContract ⟩
omit h
lemma enroll (G:Gauge)(h:G.Simple)(R:Run)(dial:Bool)
      : ∃ (N:Register.WilsonPrescription G)
      (U: Land.MS_Data G (Plot (Press.portDeck G)))
      (M: Land.Prescription ( portDeck G )),
      N.run=R ∧
      M.team=( Continuum.Continuation.proofStart h (Reg.supplies N.scheme U) dial ).team ∧
      Homes.Installed N.scheme U M true ∧ Served N U M ∧ ∀ ν,O.Canon.Supplied N U ν
      := by
    obtain ⟨N,hN,_⟩:= prepared h R ( Initialize.standard G ) 1 one_pos; obtain ⟨T⟩:= MS.Land.bookedMS ( Plot (Press.portDeck G) ); obtain ⟨M,hM,H⟩:= strict_establishment T N h dial; exact ⟨ N,T,M,hN,hM,H⟩
end YM.FVA2.Inked
