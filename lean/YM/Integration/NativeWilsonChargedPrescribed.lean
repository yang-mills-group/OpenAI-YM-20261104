import YM.Integration.WilsonLimitConstruction.FundedWilsonStartupGrade
import YM.Integration.NativeWilsonPrescribedStep
import YM.Integration.ActualOriginalQInitialInput

/-! The true initial Wilson conditional expectation and the original unaltered prescription
for every independently charged tuple of physical Q sources on its actual Run. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.NativeWilsonChargedPrescribed
open Function Filter Finset Lattice Wilson Precision RG Source Labels Tree Exterior Marker Multi
open PhysicalNext.Repeat.Legato LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep Comparison.RG02 Comparison.RG02.Bulk
open PertExtension Series Series.Radial Series.Tested
open WilsonLimitConstruction
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {H : MS.Local.Physical.Deck G} {V : Type} [DecidableEq V] [Fintype V]
    (R : Run G) (camp : Campaign R) (hG : G.Simple) (u : V → MS.Rake.Label H)
    (J : Request V) (A : NumericSchedule R.family J)
    (d : LocalFormal.Datum R.family (Stock.census V)) (Q : MS.Land.Prescription H)
    (o : V → Site (R.family.side (d.level + 1) d.period)) (μ : ℝ) (orders : V → ℕ)
    (hprofile : ∀ j, j ≤ (R.metals.p.profile j).order ∧ j ≤ (R.metals.p.profile j).power)
local notation "J₀" => ActualOriginalQPointSetup.request R u J
local notation "A₀" => ActualOriginalQInitialInput.schedule R hG u J A
variable (hm : ActualOriginalQInitialInput.start R hG u J A hprofile ≤ d.level)
    (hp : (ActualOriginalQPointSetup.request R u J).physicalPeriodLower ≤ (R.family.S.period d.period).val)
    (x : TestSpace (ActualOriginalQPointSetup.request R u J).tests) (B : fieldDir G (R.family.side d.level d.period) 1)
local notation "T" => ActualOriginalQInitialInput.input R hG u J A d Q o μ orders hprofile hm hp
local notation "W" => (T).colors x
local notation "D" => ({d with colors := W,field := B} : LocalFormal.Datum R.family (Stock.census V))
local notation "Y" => RunFormalChain.fromRun R
local notation "Q₁" => NativeWilsonColoredMeasure.colors R d.level d.period W

private theorem frozen : Bare.Starts W := by
  apply NativeWilsonColoredMeasure.frozen W ((T).convention.well x)
  intro i t _ U
  change (ActualOriginalQInitialInput.colors R hG u J A d Q o μ orders x).mark i t U =
    t^(ActualOriginalQInitialInput.colors R hG u J A d Q o μ orders x).power i •
      (ActualOriginalQInitialInput.colors R hG u J A d Q o μ orders x).mark i 1 U
  simp only [ActualOriginalQInitialInput.colors,ActualOriginalQStartupAction.colors,
    NativePaidPacketColors.colors,ActualOriginalQFrozenInput.packets,ActualPacketCouplingFreeze.freeze_read,
    one_pow,one_smul]

include camp

private theorem vacuum : Assembly.GradeAt ((J₀).order+3) (Bulk.projected (fun g U => (Q₁).vac g U - (W).vac g U)) :=
  FundedWilsonStartupGrade.purchase R camp (d.level+1) d.period (J₀).order (J₀).order_ge_two
    ((A₀).inputNorm d.level) ((A₀).inputWidth d.level)

/-- Every original mark, forest choice, independent test and physical field are retained. -/
theorem purchase (hcut : d.cutoff = d.level+1) :
    let f := NativeWilsonPrescribedStep.measured R d.level d.period d.forest d.tag W B
    Laplace.Fleet.Test ((D).ordinary Y (J₀).order) (fun t => Order.unitScale (f t)) ∧
    Laplace.Fleet.Test ((D).markedLog Y (J₀).order) (fun t => Extra.Trajectories.connected (Order.unitScale (f t))) := by
  have he : D = NativeWilsonPrescribedStep.datum R d.level d.period d.forest d.tag W B := by
    cases d with
    | mk N p m hm₀ F j w₀ b₀ =>
      dsimp only at hcut
      subst N
      rfl
  dsimp only
  rw [he]
  exact NativeWilsonPrescribedStep.first R d.level d.period d.forest d.tag W B (J₀).order
    ((T).convention.well x)
    (frozen R hG u J A d Q o μ orders hprofile hm hp x)
    (vacuum R camp hG u J A d Q o μ orders hprofile hm hp x)

/-- The connected normalized integral has exactly the jet of this particular
outgoing prescribed source, including all jointly marked coordinates. -/
theorem output {out : MarkedPackets (J₀).tests G (R.family.side d.level d.period) (Stock.census V)}
    (prescribed : PrescribedPackets Y d (T).colors out (J₀).order) (hcut : d.cutoff = d.level+1)
    (s : (Stock.census V).Mode) :
    Laplace.Trial (fun k => (((k.factorial:ℝ)⁻¹) • iteratedFDeriv ℝ k (fun t : ℝ =>
      prescribed.extension x t B) 0 (fun _ => 1)).part s)
      (fun t => (Extra.Trajectories.connected (Order.unitScale
        (NativeWilsonPrescribedStep.measured R d.level d.period d.forest d.tag W B t))).part s) (J₀).order := by
  have h := (purchase R camp hG u J A d Q o μ orders hprofile hm hp x B hcut).2 s
  refine Laplace.trial_flow h ?_
  intro k hk
  exact congrArg (fun v : Poly (Stock.census V) => v.part s) (prescribed.coefficients x B k hk).symm

end YM.Integration.NativeWilsonChargedPrescribed
end
