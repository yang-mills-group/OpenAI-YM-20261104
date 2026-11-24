import YM.Integration.WilsonPositionProgramTrialPaidHome

/-! Optical data fixed before both regulators and the dated arm on that original upper law. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPaidPanel
open Function Filter Finset Matrix Lattice Wilson RG RG.Supply Precision Source Labels Next.Foundations
open Extra.Histories Motion PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato XSpace PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Power WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.PathCost
open WilsonPositionProgramTrialHomeDose (publicDose)
open WilsonPositionProgramTrialNativeHome (reporter)
open WilsonPositionProgramTrialStationHome (chargeAt mass Seated)
open WilsonPositionProgramTrialAccrued (home)
open WilsonIndependentMatchedFiledIncome (charge plate)
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentMatchedRosterNativeDose (gross)
open WilsonReflectedMixedSharpAxis (Cash)
open WilsonReflectedFundedHearing (Arm)
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open scoped BigOperators Topology Classical
variable {G:Gauge}{h D d k u e:ℕ}
local notation "C" => Credit.leanC

structure Layout (R:Run G)(K:ℕ) where
  j : ℕ
  f : ℕ
  target : ℕ
  E : ℕ
  η : ℝ
  radius : ℝ
  coupling : ℝ
  phase : ℂ
  test : ℂ →L[ℝ] ℝ
  M : ℝ
  roof : ℝ
  before : j≤f
  up : f≤K
  ep : 0≤η
  small : η≤1
  rp : 0<radius
  gp : 0<coupling
  size : R.family.S.a f≤radius
  mp : 0≤M
  one : 1≤roof
  optical : R.family.path.levels.clock.hatBeta K*coupling^2≤roof

structure Dated (R:Run G)(d K N per:ℕ)(data:Layout R K)(live:K≤N) where
  A : R.family.label d ≃ₗ[ℂ] R.family.label d
  Y : R.family.label d
  allowance : ℝ
  cash : Cash (R:=R) d data.j data.f K N per data.target data.before data.up live data.η A Y allowance
  arm : Arm R d N per data.f K
  received : arm.w=A.symm (fitted R d data.j N per Y)
  positive : 0≤allowance
  card : max 1 (2*(R.family.S.a data.j/R.family.S.a data.f)^(d+1)*allowance) ≤
    data.M*(R.family.path.levels.clock.hatBeta data.f)^data.E

def bill (R:Run G)(d e K:ℕ)(data:Layout R K)(α:Alma (R.family.labels.level d)→ℝ):ℝ:=
  gross (R.family.labels.level d) e α*‖data.test‖*(WilsonOriginalPhysicalFruitClock.salary R d data.E
    data.phase data.M data.roof*data.coupling⁻¹^WilsonOriginalPhysicalFruitClock.power R d data.E*
    (data.radius/R.family.S.a K)^data.η)

def Home (R:Run G)(W:Initialize G)(Q:SealR G)(w:Rails Q.h k u e)(d:ℕ)(kind:Bool)(dim:d<Q.D)
    (α:Alma (R.family.labels.level d)→ℝ)(Z B:Credit)(j:ℕ):Prop:=
  ∀m K N per,j ≤ m → m ≤ K → ∀(live:K ≤ N)(data:Layout R K)(file:Dated R d K N per data live),
  let c:=WilsonPositionProgramTrialPaidHome.source R file.arm data.radius data.phase data.test
  ∃X:CutsP (hol G) Q.ans Q.path w C C C C,
    Seated R Q w m K N (Shrine (plate (sectionAt R W kind d) dim) c) (charge e c α) X ∧
    X.pt=centralL R.family.path.levels R.metals.O N m K Q
      (PermuteLens R.family.path.levels R.metals.O Q N m (home Q X))+X.springP X.i ∧
    mass Q e (home Q X) ≤ |chargeAt R.family.path.levels Q e B Z m K| *bill R d e K data α

theorem original (R:Run G)(W:Initialize G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)
    (funded:FundedMarkedCoverRows.prices v R.kit)(fit:h<D)(w:Rails h k u e)(kind:Bool)
    (dim:d<D)(cap:d≤k):
    ∃α:Alma (R.family.labels.level d)→ℝ,(∀i,0≤α i) ∧ ∃Z B:Credit,
    ∀ᶠ j:ℕ in atTop,Home R W (reporter fit) w d kind dim α Z B j:=by
  obtain ⟨α,nn,Z,B,bought⟩:=WilsonPositionProgramTrialPaidHome.original R W simple v funded fit w kind dim cap
  refine ⟨α,nn,Z,B,?_⟩
  filter_upwards [bought] with j sale
  intro m K N per jm mk live data file
  obtain ⟨X,atSeat,_,all⟩:=sale m data.j data.f K N per data.target data.E jm mk
    data.before data.up live data.ep data.small file.A file.Y file.cash file.arm file.received
    data.radius data.coupling data.rp data.gp data.size data.phase data.test data.M data.roof
    data.mp data.one file.positive file.card data.optical
  obtain ⟨original,paid⟩:=all 1
  refine ⟨X,atSeat,?_,?_⟩
  · simpa only [WilsonPositionProgramTrialHomeDose.scaled,one_smul] using original
  · simpa only [WilsonPositionProgramTrialHomeDose.scaled,one_smul,abs_one,one_mul,bill] using paid

end YM.Integration.WilsonPositionProgramTrialPaidPanel
end
