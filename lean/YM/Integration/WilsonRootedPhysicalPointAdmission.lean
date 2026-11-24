import YM.Integration.WilsonRootedPhysicalOPEDeposit

/-! A common physical preparation and rooted deposit of the prescribed original
OPE on the selected spring. The cutoff precedes the period, source, radii and tests. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedPhysicalPointAdmission
open Filter Function Finset Lattice Wilson RG Source Labels Marker FVA1
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.JointLoad
open Heir Heir.Suite Push.PriceCompiler Supply Push.SectorMeasure Push
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open PhysicalNext.Repeat.Daisy MergeProof Org GapsLocal.Renew
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection WilsonOriginalMarkedExistence
open scoped Classical BigOperators Topology
open private input_leaf from YM.Integration.ActualOriginalQInitialPreparation
universe u
variable {G : Gauge} {V : Type} [decV : DecidableEq V] [Fintype V] [Nonempty V]
    {B : MS.Local.Physical.Deck G} (R : Run G) (hG : G.Simple) (u : V→MS.Rake.Label B)
    (J : Request V) (A : NumericSchedule R.family J) (T : Campaign R)
    (stage : ∀i, i ≤ (R.metals.p.profile i).order ∧ i ≤ (R.metals.p.profile i).power)
    (d : LocalFormal.Datum R.family (Stock.census V)) (Q : MS.Land.Prescription B)
    (o : V → Site (R.family.side (d.level+1) d.period)) (μ : ℝ) (orders : V→ℕ)
local notation "J₀" => ActualOriginalQPointSetup.request R u J
local notation "P₀" => ActualRunSpring.selected R d.cutoff d.period d.level d.below
local notation "D₀" => ActualOriginalQPointSetup.pointDatum R J d.period (d.level+1) o
local notation "source₀" => ActualOriginalQInitialPreparation.input R hG u J A d Q o μ orders
local notation "g₀" => Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)

def RootRate : Prop :=
  ManuscriptQLocalMarkedHeightRun.High (R.kit.expense (R.alloy.B.a.clock.J (d.level+1)) (R.alloy.B.a.clock.J d.level))
      (Mallow.houseS (P₀).spring (P₀).point) (J₀) (Stock.census V) ((2*(g₀))^((J₀).order+1))

def SourcePrice : Prop :=
  ∀ (w : V→ℝ) (_hw : ∀v,0<w v) (x : TestSpace (J₀).tests),
    ∃ rows : Bool × ActualRunFullPages.Index (ActualOriginalQInput.atomPositions (D₀) u) →
      Menu.Hat (Stock.census V) ((P₀).input (P₀).point.val),
      WilsonRootedPhysicalOPEDeposit.Account R (P₀) (Stock.census V) o w ((source₀).leaf x).density rows

def AtPoint : Prop := RootRate R u J d ∧ SourcePrice R hG u J A d Q o μ orders

def Admission : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ (d : LocalFormal.Datum R.family (Stock.census V)), d.level=m →
    ∀ (Q : MS.Land.Prescription B) (o : V→Site (R.family.side (d.level+1) d.period)) (μ : ℝ) (orders : V→ℕ),
    AtPoint R hG u J A d Q o μ orders ∧ ∀ (per : (J₀).physicalPeriodLower ≤ (R.family.S.period d.period).val),
    d.cutoff=d.level+1 → ∃ start : ActualOriginalQInitialInput.start R hG u J A stage ≤ d.level,
      let F := ActualOriginalQInitialInput.input R hG u J A d Q o μ orders stage start per
      ∃ I : FullPreparedInputAt F 0, Retained.NativeIntake I ∧
        I.carrier.rep=R.family.path.rep d.cutoff d.period (d.level+1) ∧
        HEq I.input (ActualOriginalQInitialPreparation.input R hG u J A d Q o μ orders) ∧
        I.regularPrice=0 ∧ I.forcedPrice=0

omit [Nonempty V] in
private theorem rateAt (Γ : Census V) {N p m : ℕ} {below : m<N}
    (P : ActualRunSpring.Packet R N p m below)
    (height : Mallow.RG12.Earned (ManuscriptQLocalMarkedHeightRun.acquisition G J) R.kit.shape R.alloy.delay) :
    ManuscriptQLocalMarkedHeightRun.High (R.kit.expense (R.alloy.B.a.clock.J (m+1)) (R.alloy.B.a.clock.J m))
      (Mallow.houseS P.spring P.point) J Γ ((2*Pert.Asymptotics.regulatorRun R.family N p (m+1))^(J.order+1)) := by
  obtain rfl : decV = (fun a b : V => Classical.propDecidable (a=b)) := Subsingleton.elim _ _
  exact WilsonRootedPhysicalSpring.high R J Γ P height

private theorem sourcePrice {Δ : Daisy.Charity.RG12.Decal G}
    (spring : R2I.Funded ((Mallow.orbitD G).paired Δ) R T)
    (capacity : Fintype.card V ≤ R.alloy.B.a.clock.J d.level)
    (depth : ActualOriginalQLayout.referenceLevel R u ≤ d.level) : SourcePrice R hG u J A d Q o μ orders := by
  let springPoint := ActualRunSpring.selected R d.cutoff d.period d.level d.below
  intro w hw x
  let frame := ActualOriginalQPointSetup.pointDatum R J d.period (d.level+1) o
  let ys := VariableScaling.tests (ActualOriginalQInitialInput.scales R hG u J A d Q o μ orders) x
  have ref := ActualOriginalQLayout.reference_le R u (depth.trans (Nat.le_succ d.level))
  have size : Fintype.card V ≤ R.alloy.B.a.clock.J (d.level+1)+1 :=
    (capacity.trans (R.alloy.B.a.fits.mono (Nat.le_succ d.level))).trans (Nat.le_succ _)
  have out := WilsonRootedPhysicalOPEDeposit.physical R springPoint Q frame u (μ-R.family.S.scale d.cutoff) orders
    hG spring ref size w hw ys
  obtain ⟨rows, receipt⟩ := out
  refine ⟨rows, ?_⟩
  have origin : (ActualOriginalQPackets.positions frame u).origin = o := by
    funext v
    exact ActualOriginalQPointDatum.root_eq R _ _ _ _ _ v
  let value := ((ActualOriginalQInput.input Q frame u (μ-R.family.S.scale d.cutoff) orders hG
    d.cutoff d.below).leaf ys).density
  have transported := congrArg (fun roots : V→Site (R.family.side (d.level+1) d.period) =>
    WilsonRootedPhysicalOPEDeposit.Account R springPoint (Stock.census V) roots w value rows) origin
  rw [input_leaf R hG u J A d Q o μ orders x]
  exact transported.mp receipt

/-- This is a genuine selected OPE datum, evaluated through the original complete
physical spring at every date. At the UV date it is itself the full prepared input. -/
theorem admitted {Δ : Daisy.Charity.RG12.Decal G} (spring : R2I.Funded ((Mallow.orbitD G).paired Δ) R T)
    (height : Mallow.RG12.Earned (ManuscriptQLocalMarkedHeightRun.acquisition G J) R.kit.shape R.alloy.delay) :
    Admission R hG u J A stage := by
  filter_upwards [ActualOriginalQInitialAtTop.eventually_prepared R hG u J A T stage,
    R.alloy.B.a.fits.deep.eventually_ge_atTop (Fintype.card V),
    eventually_ge_atTop (ActualOriginalQLayout.referenceLevel R u)] with m birth capacity depth d hd Q o μ orders
  subst m
  exact ⟨⟨rateAt R (ActualOriginalQPointSetup.request R u J) (Stock.census V)
      (ActualRunSpring.selected R d.cutoff d.period d.level d.below) height,sourcePrice R hG u J A T d Q o μ orders spring capacity depth⟩,
    birth d rfl Q o μ orders⟩

/-- One physical campaign pays its OPE preparation, original comparison, rooted
height and full deposit before choosing the labels, cutoff, tests or their radii. -/
theorem selected (hG : G.Simple) {ε : ℝ} (hε : 0<ε) (J : Request V)
    (extra : Stage→ℕ→ℝ) (γ : ℝ) (hγ : -(1/2:ℝ)<γ) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      ∃ stage : ∀i, i≤(R.metals.p.profile i).order ∧ i≤(R.metals.p.profile i).power,
      QLocalRequestedSectorCalendar.Paid J (WilsonRootedJointCalendar.scheme G J) extra γ R.kit ∧
      WilsonOriginalHighSelection.Salary G R.kit ∧ Stationary.LightPath R.alloy.B.kin Real.log ∧
      NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} hG ε W ∧ Charged R ∧
      ∀ (B : MS.Local.Physical.Deck G) (u : V→MS.Rake.Label B) (A : NumericSchedule R.family J),
        Admission R hG u J A stage := by
  obtain ⟨R,T,W,calendar,stage,spring,height,salary,light,_,_,cors,comparison,charged⟩ :=
    WilsonRootedPhysicalSpringElection.selected.{u} hG hε J extra γ hγ
  exact ⟨R,T,W,stage,calendar,salary,light,cors,comparison,charged,
    fun _ u A=>admitted R hG u J A T stage spring height⟩

end YM.Integration.WilsonRootedPhysicalPointAdmission
end
