import YM.Integration.WilsonCompensatedOpening
import YM.Integration.QLocalNormalizedQBirth
import YM.Integration.WilsonLimitConstruction.FundedWilsonBackgroundPayment

/-! The genuine independently placed, normalized charged Q input is precisely
the full RG02 colored material at the first measured step. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedMatchedPointOpening
open Function Filter Finset MeasureTheory Lattice Wilson RG Precision Marker
open PhysicalNext.Repeat.Legato LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep IterationFour IterationFour.Vacuum
open Comparison.RG02 Pert.Asymptotics ActualPolynomialContraction
open scoped Classical Topology BigOperators

variable {G : Gauge} {B : MS.Local.Physical.Deck G} {V : Type} [DecidableEq V] [Fintype V]
    (R : Run G) (hG : G.Simple) (u : V→MS.Rake.Label B) (J : Request V)
    (A : NumericSchedule R.family J) (d : LocalFormal.Datum R.family (Stock.census V))
    (Q : MS.Land.Prescription B) (o : V→Site (R.family.side (d.level+1) d.period))
    (μ : ℝ) (orders : V→ℕ)
    (profile : ∀k, k≤(R.metals.p.profile k).order ∧ k≤(R.metals.p.profile k).power)
    (hm : ActualOriginalQInitialInput.start R hG u J A profile≤d.level)
    (hp : (ActualOriginalQPointSetup.request R u J).physicalPeriodLower≤(R.family.S.period d.period).val)
local notation "J₀" => ActualOriginalQPointSetup.request R u J
local notation "P₁" => R.family.path.rep d.cutoff d.period (d.level+1)
local notation "g₁" => regulatorRun R.family d.cutoff d.period (d.level+1)
local notation "K₁" => d.kernel (RunFormalChain.fromRun R)
local notation "F₀" => ActualOriginalQInitialInput.input R hG u J A d Q o μ orders profile hm hp
local notation "I₀" => ActualOriginalQInitialPreparation.input R hG u J A d Q o μ orders
local notation "n₁" => R.family.side (d.level+1) d.period

def colors (t : TestSpace (J₀).tests) : Bulk.Colors (Stock.census V) G n₁ :=
  NativeWilsonColoredMeasure.colors R d.level d.period ((F₀).colors t)

local notation "Z" => colors R hG u J A d Q o μ orders profile hm hp

theorem well (t : TestSpace (J₀).tests) : Bulk.Well (Z t) :=
  NativeWilsonColoredMeasure.well R d.level d.period _ ((F₀).convention.well t)

theorem quiet (top : d.cutoff=d.level+1) (t : TestSpace (J₀).tests) (U : Config G n₁) :
    Integral.weight g₁ 0 U (Z t) (P₁).clip (P₁).path=(P₁).eval U := by
  have temp : Integral.temperature g₁=R.family.beta (d.level+1) d.period := by
    rw [top]
    exact FundedWilsonBackgroundPayment.temperature R (d.level+1) d.period
  have rep : (P₁)=R.family.path.rep (d.level+1) d.period (d.level+1) := by rw [top]
  rw [rep]
  calc
    _ = Wilson.bare (Integral.temperature g₁) U :=
      WilsonCompensatedOpening.weight R d.level d.period ((F₀).colors t) g₁ U
    _ = _ := by
      rw [temp]
      exact (congrFun (R.makes.wilson.starts (d.level+1) d.period).2 U).symm

theorem marked (t : TestSpace (J₀).tests) (U : Config G n₁) :
    Integral.markedLog g₁ U (Z t)=
      (ActualOriginalQInitialInput.packets R hG u J A d Q o μ orders).read t g₁ U :=
  (F₀).convention.marks t g₁ (Currency.g_pos R.makes _ _ _ d.below).ne' U

def material (t : TestSpace (J₀).tests) : Config G n₁→Poly (Stock.census V) :=
  Integral.model g₁ 0 (Z t) K₁

local notation "M" => material R hG u J A d Q o μ orders profile hm hp

variable [Nonempty V]

theorem density (top : d.cutoff=d.level+1) (ref : ActualOriginalQLayout.referenceLevel R u≤d.level+1)
    (t : TestSpace (J₀).tests) : ((I₀).leaf t).density=M t := by
  funext U
  change _=(Integral.weight g₁ 0 U (Z t) (P₁).clip (P₁).path:ℂ) • Poly.pass (Integral.markedLog g₁ U (Z t))
  simpa only [quiet R hG u J A d Q o μ orders profile hm hp top t U,
    marked R hG u J A d Q o μ orders profile hm hp t U,Complex.coe_smul] using
    QLocalNormalizedQBirth.source R hG u J A d Q o μ orders ref t U

theorem trajectory (top : d.cutoff=d.level+1) (ref : ActualOriginalQLayout.referenceLevel R u≤d.level+1)
    (t : TestSpace (J₀).tests) {k : ℕ} (hk : k≤d.level+1) :
    actualSignedTransport R.family (N:=d.cutoff) ((I₀).leaf t).density hk=
      actualSignedTransport R.family (N:=d.cutoff) (M t) hk := by
  rw [density R hG u J A d Q o μ orders profile hm hp top ref t]

theorem bounded (top : d.cutoff=d.level+1) (ref : ActualOriginalQLayout.referenceLevel R u≤d.level+1)
    (w : V→ℝ) (hw : ∀v,0<w v) (hu : ∀v,w v≤1) (t : IndependentTests (J₀).tests)
    {k : ℕ} (hk : k≤d.level+1) (U : Config G (R.family.side k d.period)) :
    Poly.price w (actualSignedTransport R.family (N:=d.cutoff) (M (testInclusion _ t)) hk U)≤
      MarkedPackets.uniformModelCost (ActualOriginalQLayout.rankCap R u) (Fintype.card V) 1 := by
  let test := testInclusion (J₀).tests t
  have same := trajectory R hG u J A d Q o μ orders profile hm hp top ref test hk
  have bound := QLocalNormalizedQBirth.transported R hG u J A d Q o μ orders ref w hw hu t hk U
  exact (congrArg (fun f : Config G (R.family.side k d.period) → Poly (Stock.census V) =>
    Poly.price w (f U)) same.symm).le.trans bound

end YM.Integration.WilsonLimitConstruction.FundedMatchedPointOpening
end
