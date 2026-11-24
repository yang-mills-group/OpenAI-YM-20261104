import YM.Integration.WilsonMarkedIndependentNormalizedElection
import YM.Integration.WilsonThermometerPositionTunedSurvey
/-! Co-elect the literal public bare section and the original marked calendar.
Their partial cutoffs, period, tests and source coordinates are selected later. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerSurveyIncome
open Function Filter Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.PathCost
open WilsonLimitConstruction Labels Source Source.Drops XSpace
open scoped Topology
universe u
variable {G:Gauge}(W:Initialize G)

def chapter (h:ℕ):SectionData ((primes G).F h):=((W.surveys h).prepares ((primes G).F h)).choose
theorem signed (h:ℕ):(W.surveys h).Represents ((primes G).F h) (chapter W h):=
  ((W.surveys h).prepares ((primes G).F h)).choose_spec

def master:Master (hol G):=⟨(primes G).F,chapter W,
  fun h=>(congrArg (fun H=>(chapter W h).Sound H) (WilsonEpochPositionCoefficients.holonomy W.hol (hol G))).mp (signed W h).1,
  fun h=>(signed W h).2.1⟩

theorem prepared (R:Run G)(d:ℕ): (master W).T d=WilsonThermometerPositionTunedSurvey.prepared R W d:=rfl

def prices:FundedCompanySelection.Prediction G:=
  fun {M} {D} {A} _ => horiz (hol G) (master W) (chart G) id M.p.kernel ≤ M.p.floorL ∧
    aperture (hol G) (master W) (chart G) id D ≤ A.delay.betaEntry

theorem purchase:FundedPredictionSupply.AllPrices (@prices G W):=by
  intro s quote targets expenses chartEq programs wages baton valid
  refine ⟨horiz (hol G) (master W) (chart G) id s.kernel,?_⟩
  intro l hl D w U reg post scouts θ stages cost V quarter
  let surveyFees:=aperture (hol G) (master W) (chart G) id D
  let next:Delays θ:={V with betaEntry:=surveyFees ⊔ V.betaEntry}
  refine ⟨next,⟨le_sup_right,le_rfl,le_rfl,le_rfl⟩,?_⟩
  intro W' hW bar wait priced B0
  dsimp only
  intros
  exact ⟨hl,le_sup_left.trans hW.beta⟩

/-- The complete earlier prediction remains attached to this very course. -/
theorem elected (simple:G.Simple){ε:ℝ}(hε:0<ε)(v:ℕ→Gear G→ℝ)
    (P:FundedCompanySelection.Prediction G)(hP:FundedPredictionSupply.AllPrices (@P)):
    ∃(R:Run G)(T:Campaign R)(U:Campaign.Pillars R T),
      FundedMarkedCoverRows.prices v R.kit ∧ prices W R.kit ∧ P R.kit ∧
      NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} simple ε U:=by
  obtain ⟨R,T,U,coin,joint,raw,rest⟩:=FundedMarkedCoverRows.original.{u} simple hε v
    (@FundedPredictionSupply.Both G (@prices G W) (@P))
    (fun s q=>FundedPredictionSupply.both (purchase W s q) (hP s q))
  exact ⟨R,T,U,coin,joint.1,joint.2,raw,rest⟩
end YM.Integration.WilsonMaxwellThermometerSurveyIncome
