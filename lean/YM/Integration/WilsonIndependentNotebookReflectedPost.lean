import YM.Integration.WilsonIndependentNotebookReflectedDose

/-! Jointly appointed real and reflected public stencils on the elected Wilson hierarchy.
The common date tariff and the actual stable field of each returned arm are retained. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 850000
set_option warningAsError true
namespace YM.Integration.WilsonIndependentNotebookReflectedPost
open Function Filter Finset Matrix Lattice Wilson RG RG.Supply Precision Source Labels Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato XSpace PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Power WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.PathCost
open Laurent Bloch WilsonCoeffUV.Fountain WilsonCoeffUV.Wheel
open WilsonPositionProgramTrialHomeDose (publicDose)
open WilsonPositionProgramTrialNativeHome (reporter)
open WilsonIndependentMatchedFiledIncome (charge plate)
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonPositionProgramTrialStationHome (Seated chargeAt)
open WilsonIndependentNotebookReflectedDose (axes)
open WilsonPositionProgramTrialFittedLens (matrix)
open WilsonIndependentFittedMixedCash (embed)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open WilsonOlderFreshSoftCoverScalar (clock)
open scoped BigOperators Topology Classical
variable {G:Gauge}{h D d k u e:ℕ}
local notation "C" => Credit.leanC

def Appointment (R:Run G)(Q:SealR G)(w:Rails Q.h k u e)(m K N:ℕ)(Z B:Credit)
    (Y:TowerS G Q.D)(funds:ℝ)(X:CutsP (hol G) Q.ans Q.path w C C C C):Prop:=
  Seated R Q w m K N Y funds X ∧ ∀a:ℝ,
    (a • X.pt=centralL R.family.path.levels R.metals.O N m K Q
      (PermuteLens R.family.path.levels R.metals.O Q N m (publicDose Q X a))+a • X.springP X.i) ∧
    WilsonPositionProgramTrialStationHome.mass Q e (publicDose Q X a) ≤ chargeAt R.family.path.levels Q e B Z m K*(|a| *funds)

theorem original (R:Run G)(W:Initialize G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)
    (funded:FundedMarkedCoverRows.prices v R.kit)(fit:h<D)(rails:Rails h k u e)
    (d:ℕ)(kind:Bool)(dim:d<D)(cap:d ≤ k):
    let Q:=reporter (G:=G) fit
    let F:=R.family.labels.level d
    let Y:=Shrine (plate (sectionAt R W kind d) dim)
    ∃α:Alma F→ℝ,(∀i,0 ≤ α i) ∧ ∃Z B:Credit,
    ∀ᶠ j:ℕ in atTop,∀m K N,j ≤ m → m ≤ K → K ≤ N →
    ∀(v:Verse F)(b:ℝ)(s:Signed),
    let τ:=paintC F s*ᵥv
    let S:=axes Q.F s
    let M:=Wray R.family.path.levels R.metals.O Q.ans Q.path N m
    ∃X X':CutsP (hol G) Q.ans Q.path rails C C C C,
      Appointment R Q rails m K N Z B (b • Y v) (|b| *charge e v α) X ∧
      Appointment R Q rails m K N Z B (b • Y τ) (|b| *charge e τ α) X' ∧
      ∀a:ℝ,dose X' a=matrix S (dose X a) ∧
        publicDose Q X' a=matrix (M*S*M⁻¹) (publicDose Q X a):=by
  intro Q F Y
  obtain ⟨α,hα,Z,B,sale⟩:=WilsonPositionProgramTrialStationHome.original R W simple v funded fit rails d kind dim cap
  refine ⟨α,hα,Z,B,?_⟩
  filter_upwards [sale] with j booked
  intro m K N jm mk kn v b s τ S M
  obtain ⟨X,l,lp⟩:=booked m K N jm mk kn v b
  obtain ⟨X',r,rp⟩:=booked m K N jm mk kn τ b
  exact ⟨X,X',⟨l,lp⟩,⟨r,rp⟩,WilsonIndependentNotebookReflectedDose.seated R W Q rails kind dim cap s v b X X' _ _ l r⟩

theorem measured (A:Levels G)(O:ChartRatio G)(Q:SealR G)(N m host q:ℕ)
    (earlier:host ≤ m)(t:ℝ)(M:Wall Q.F)(v:Q.Rider):
    let see:=fun c=>cash q t (embed (clock A O N m host c))
    ∀i,see (matrix M v i)=∑j,M i j • see (v j):=by
  intro see i
  simp only [see,WilsonIndependentNotebookDoseCoefficients.actual A O N m host q earlier t,
    matrix,map_sum,map_smul]

end YM.Integration.WilsonIndependentNotebookReflectedPost
