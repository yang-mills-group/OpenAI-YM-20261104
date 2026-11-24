import YM.Integration.WilsonThermometerOriginalFilmStep
import YM.Integration.WilsonOriginalThermometerPalette

/-! The (6,4,4) position program files every face and its centered quiet response on a single clock. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerPositionFilmBank
open Exterior Wilson Precision Filter Set Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open RegulatorIR RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.FVAAlt2
open RegulatorIR.FVAAlt2.Period.Field RegulatorIR.FVAAlt2.Pipeline RegulatorIR.Calibration
open WilsonPositionProgramVariableCircuit WilsonThermometerOriginalCoveredRows
open Comparison.RG02 Comparison.RG02.Symmetry Geometry Marker Multi QuadraticLocal
open scoped Classical Topology PowerSeries
variable {G:Gauge} (C:Run G) (D:XSpace.Run) {X:Type} (m j:X→ℕ) (w:X→ℕ→ℕ)
  (blocks:∀ x k,(C.family.S.block (m x+k)).val=D.ratio^(w x k))
  (branch:∀ P:Patch,P.Branches C.family.path.levels.clock.kernel G)
local notation "H" => WilsonPositionProgramInfraredCircuit.history C D m j w blocks
local notation "E" => WilsonPositionProgramInfraredCircuit.circuit C D m j w blocks
local notation "K" => RunFormalChain.fromRun C
local notation "Y" => Oracle.books C.family.path.levels.clock.kernel
local notation "S" => Stock.census Unit
local notation "deg" => WilsonOriginalThermometerPalette.levels

def Reads (s:Finset (Fin 3)) (r:ℕ) (F:Tent j) (T:See.Times (sheet F) r) (per:ℕ)
    (V:Sound.Figure.Activation (I:=↥s) C H per S) : Prop :=
  ∀ (a:(j:↥s)→(C.family.labels.level (deg j.val)).Index) (k:Flap j)
    (x:fieldDir G (C.family.side ((H).vol k.next) per) 1),
    let rows:=V (fun j=>deg j.val) a
    let ker:=(H).readyKin E C.family.path K per k
    let before:=See.before H k (rows k.prev)
    let tree:=Halo.bios ((H).stepData E C.family.path per k)
    let draw:=directive ((H).stepData E C.family.path per k)
    let drift:=-deriv (T.cloth k.prev).rating 0
    let card:=(H).records E C.family.path per k.next
    let q₀:=WilsonThermometerOriginalFilmStep.old K H S () per k (rows k.prev)
    let q₁:=WilsonThermometerOriginalFilmStep.slope K H S () per k (rows k.prev)
    See.noseC S () (T.cloth k.next) (rows k.next) 0 x=q₀ x ∧
    See.noseC S () (T.cloth k.next) (rows k.next) 1 x=q₁ x+fderiv ℝ q₀ x (drift • x) ∧
    See.visible S card.clip card.path (T.cloth k.next) (rows k.next) 0 x=
      Symmetry.price ker tree draw x-Symmetry.price ker tree draw 0 ∧
    See.visible S card.clip card.path (T.cloth k.next) (rows k.next) 1 x=
      (first ker tree draw before x).part (S).quiet+fderiv ℝ (Symmetry.price ker tree draw) x (drift • x)-
      (first ker tree draw before 0).part (S).quiet

theorem original (color:G.ColorIndex) (r:ℕ) (F:Tent j)
    (hF:Notebook E Y G branch color (Rocket.native j) F r) (live : 0 < r) :
    ∃ T:See.Times (sheet F) r, ∀ (s:Finset (Fin 3)) (z : X → ↥s → Cover),
      ∃ V:(per:ℕ)→Sound.Figure.Activation (I:=↥s) C H per S,
        (∀ per, Sound.Figure.Course C H z (sheet F) per () S r T (V per)) ∧
        ∀ per,Reads C D m j w blocks s r F T per (V per) := by
  obtain ⟨T,register⟩:=WilsonPositionProgramDeclaredForest.original C D m j w blocks branch color r F hF
  refine ⟨T,?_⟩
  intro s z
  obtain ⟨V,course,_read,_slope⟩:=register (↥s) z Unit S ()
  refine ⟨V,course,?_⟩
  intro per a k x
  let law:=course per (fun j=>deg j.val) a
  let rows:=V per (fun j=>deg j.val) a
  let fee:=C.family.path.levels.budget ((H).vol k.next)
  have occupied:=WilsonThermometerOriginalFilmStep.marked K H S () (sheet F) per r T k (rows k.prev) (rows k.next)
    (law.walks k) live fee (law.allows k.prev).1 x
  have quiet:=WilsonThermometerOriginalFilmStep.vacuum K H S () (sheet F) per r T k (rows k.prev) (rows k.next)
    (law.walks k) live fee (law.allows k.prev).1 x
  exact ⟨occupied.1,occupied.2,quiet⟩

end YM.Integration.WilsonThermometerPositionFilmBank
