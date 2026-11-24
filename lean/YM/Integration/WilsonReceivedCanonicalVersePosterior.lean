import YM.Integration.WilsonReceivedCanonicalVersePortfolio
import YM.Integration.WilsonThermometerOccupiedLinear

/-! The exact finite socket portfolio is linear on the selected, normalized
original conditional law at every older held field, with all co-owners present. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCanonicalVersePosterior
open Function Finset MeasureTheory Lattice Wilson RG Labels Source
open PhysicalNext.Repeat.Legato WilsonThermometerDeclaredSeeds OriginalMarkedSourceComet
open MergeProof.Accent Pert.Asymptotics
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Bank.Carp
open WilsonReceivedCanonicalVerseBasis (dose restored)
open WilsonReceivedCanonicalVersePortfolio (Selection weight wallet)
open private summed from YM.Integration.WilsonThermometerOccupiedLinear
open scoped Classical BigOperators
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I](R:Run G)(k:I→ℕ){h:I→ℕ}
variable (κ:(j:I)→Knob (h j))(pt:I→Chamber)

def word {n:Side}(g:ℝ)(o:I→Site n)(S:Finset I)(q:Selection R k S)(U:Config G n):ℂ:=
  ∏j:S,restored R k κ pt g j (q j) (o j) U

omit [Fintype I] [DecidableEq I] in
theorem smooth {n:Side}(g:ℝ)(o:I→Site n)(S:Finset I)(q:Selection R k S):
    Continuous (word R k κ pt g o S q):=by
  apply continuous_finsetProd
  intro j _
  exact continuous_const.mul (Complex.continuous_ofReal.comp ((OriginalMarkedSourceComet.colour _ _ _ _).unmasked_cont _))

variable (N p b:ℕ)(live:b≤N)(v:(j:I)→R.family.label (k j))(o:I→Site (R.family.side b p))(S:Finset I)
local notation "C₀" => R.family
local notation "H" => R.family.path
local notation "X" => Config G (R.family.side b p)
local notation "g" => regulatorRun R.family N p b
local notation "face" => fun U:X=>∏j:S,WilsonPositionProgramBlockedTrialAddBack.uncut R (k j) N p b (o j) (v j) U
local notation "ω" => weight R k N p b v S
local notation "row" => word R k κ pt g o S

include live in
theorem original (u:ℕ)(before:u≤b)(W:Config G (R.family.side u p)):
    actualTransport (C₀) (N:=N) (face) before W =
      ∑q:Selection R k S,(ω) q*actualTransport (C₀) (N:=N) ((row) q) before W:=by
  classical
  let density:=fun q U=>((H).rep N p b).eval U • (row) q U
  have rent (q:Selection R k S):Integrable (density q) (prior G _):=by
    have test:=smooth R k κ pt g o S q
    obtain ⟨B,cap⟩:=(isCompact_range test.norm).bddAbove
    have field:∀U,‖(row) q U‖≤B:=fun U=>cap ⟨U,rfl⟩
    have received:=actualTransport_weighted_integrable (C₀) R.makes (N:=N) live test.measurable.aestronglyMeasurable field (le_refl b)
    rwa [actualTransport_base (C₀) R.makes live] at received
  have born:(fun U=>((H).rep N p b).eval U • (face) U)=∑q,(ω) q • density q:=by
    funext U
    change ((H).rep N p b).eval U • (∏j:S,WilsonPositionProgramBlockedTrialAddBack.uncut R (k j) N p b (o j) (v j) U)=_
    rw [WilsonReceivedCanonicalVerseBasis.faces R k κ pt N p b live v o S U,smul_sum]
    simp only [Finset.sum_apply,Pi.smul_apply]
    exact sum_congr rfl fun q _=>smul_comm _ ((ω) q) ((row) q U)
  have pushed:=congrFun (summed R (N:=N) univ (ω) density rent before).2 W
  unfold actualTransport
  rw [born,pushed]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_sum]
  exact sum_congr rfl fun q _=>smul_comm _ ((ω) q) _

end YM.Integration.WilsonReceivedCanonicalVersePosterior
