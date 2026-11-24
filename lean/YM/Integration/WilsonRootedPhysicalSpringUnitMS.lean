import YM.Integration.WilsonRootedPhysicalSpringStoredMS
import YM.Integration.WilsonScalarSourceTableDecay

/-! Uniform stored-scalar error on the same paid physical run as the signed MS report. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedPhysicalSpringUnitMS

open Filter Lattice RG FVA2 FVA2.CityHistory FVA2.Both.Passage FVA2.Both.Passage.Cohort
open FormalOPE.RG10.BlockGauge MS MS.Rake MS.Land MS.Tide MS.Orbit MS.Dial MS.Fleet MS.Local.Physical
open PhysicalNext.Repeat.Legato RegulatorIR.FVAAlt2.Lodge WilsonMatrixTicketLanesMirrorClock
open scoped Topology Classical BigOperators
variable {G : Gauge} 

open WilsonMatrixTicketLanesReportedClock
open WilsonMeasuredWindow

open RG.Supply PhysicalNext PhysicalNext.Repeat Progress.DirectedRecipe
open FVA2.Register YM.FVAAlt2 WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open FullQLocal FullQLocal.RenderedStep Org
open WilsonRootedPhysicalSpringAffineRows
universe u


open Function Filter Lattice Wilson RG RG.Shoot Tree Pressure Pressure.Testing Pressure.Tube Pressure.Stores
open Push.SectorMeasure Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open FreeResolvent FreeResolvent.Affine FreeResolvent.TestD FreeResolvent.Mark PhysicalAffineScalarFieldContraction
open Push.PriceCompiler WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open Marker PhysicalNext.JointLoad PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open PhysicalAffineScalarAperture (noHole)
open AnalyticBridge.SectorAffine.Offset (Through)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open ManuscriptQLocalCofinalAffineFields (schedule)

private theorem restrict {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X → ℝ} {j n : ℕ} {C D : ℝ} (H : Through n f 0 C)
    (hj : j ≤ n) (hC : C ≤ D) : Through j f 0 D :=
  ⟨smooth_of_le H.smooth hj, fun k hk => (H.pay k (hk.trans hj)).trans hC⟩

section Field
variable {I : Type} [DecidableEq I] [Fintype I] {Γ : Census I}
variable (R : Run G) (d : LocalFormal.Datum R.family Γ)

local notation "S" => R.family.path.levels.clock.op d.level d.period
local notation "θ" => R.alloy.B.a.clock.hatBeta d.level
local notation "c₀" => R.family.side d.level d.period
local notation "hole" => noHole S
local notation "j₁" => R.alloy.B.a.clock.J (d.level+1)
local notation "j₀" => R.alloy.B.a.clock.J d.level
local notation "Pt" => query R.metals.p R.metals.K j₁ j₀
local notation "P₀" => Clockwork.patch R.rolls (step_paid R.alloy.B.a d.level) (first_le R.alloy.B.valid d.level)
local notation "g₀" => coupling (R.family.path.rep d.cutoff d.period (d.level+1)).beta

/-- All derivatives through the requested order have the original coupling gain, including
the change of the stored defect when the physical forest changes at one specified site. -/
def Fields (table : WilsonScalarSourceTableForecast.Paid schedule schedule R.kit)
    (through power : ℕ) : Prop :=
  ∀ (k : (S).Choices) (q : Chi) (a : ℝ) (z : Site c₀) (U : {U : Forest (S).ratio // changed S d.forest U z})
    (Y : LinkArray G (Frozen hole θ d.forest)) (Z : LinkArray G (Frozen hole θ U.val)) (o : Site c₀),
    let N := j₁
    let r := table.choose j₁ j₀
    let s := ManuscriptQLocalStoredGaussianScalar.cutWidth G P₀ Pt N r
    let κ := ManuscriptQLocalScalarClockPurchase.cutoff Pt (P₀).L/4
    let c := min κ 1/100000
    let C := g₀^power * Real.exp (-c*(radiusB θ:ℝ))
    let K := C * Real.exp (-s*(separation o z:ℝ))
    0<s ∧ 0<c ∧ Through through (ManuscriptQLocalScalarFields.regular R d k q a Y o) 0 C ∧
    Through through (ManuscriptQLocalScalarFields.changedRoot R d k q a z U Y Z o) 0 K ∧
    Through through (ManuscriptQLocalScalarDirections.error R d k d.forest q a Y o) 0 C ∧
    Through through (fun B => ManuscriptQLocalScalarDirections.error R d k U.val q a Z o B-ManuscriptQLocalScalarDirections.error R d k d.forest q a Y o B) 0 K

theorem fields (table : WilsonScalarSourceTableForecast.Paid schedule schedule R.kit)
    (orders : ManuscriptQLocalScalarDirections.PaidOrders schedule schedule R.kit)
    (through power : ℕ) (hd : through ≤ j₁) (hp : power ≤ j₁) :
    Fields R d table through power := by
  intro k q a z U Y Z o N r s κ c C K
  obtain ⟨hs,hc,H,H',J,J'⟩ := WilsonScalarSourceTableDecay.original R d table orders.1.2.2 orders.1.1 k q a z U Y Z o
  have hg := ManuscriptQLocalIdealSquare.fine R d orders.1.1
  have reduced : g₀^N * Real.exp (-c*(radiusB θ:ℝ)) ≤ C :=
    mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hg.1.le hg.2 hp) (Real.exp_pos _).le
  have changed := mul_le_mul_of_nonneg_right reduced (Real.exp_pos (-s*(separation o z:ℝ))).le
  exact ⟨hs,hc,restrict H hd reduced,restrict H' hd changed,restrict J hd reduced,restrict J' hd changed⟩
end Field

/-- Every extraction uses the same lower stage for its signed MS report, the original
charged-to-quiet field budget and all gauge data with arbitrary tested order and coupling power. -/
def Ready (simple : G.Simple)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (R : Run G)
    (paid : ManuscriptQLocalCofinalAffineFields.Paid R) (Q : Prescription (Press.portDeck G))
    (table : WilsonScalarSourceTableForecast.Paid schedule schedule R.kit) : Prop :=
  ∀ (through power : ℕ) (f : Extraction.Order) (rung : ℕ) (hrung : 0 < rung) (c : ℝ) (hc : 1 < c),
    ∀ᶠ b : ℕ in atTop, WilsonRootedPhysicalSpringAffineRows.After R paid (max through power) b ∧
      WilsonRootedPhysicalSpringReportedMS.Filed R M Q f simple rung hrung hc b ∧
      ∀ {I : Type} [DecidableEq I] [Fintype I] {Γ : Census I} (d : LocalFormal.Datum R.family Γ),
        b ≤ d.level → Fields R d table through power

/-- Prepay the derivative forecast, the original signed MS forecast and any independent
physical experiment, then select their single run, pillars and marked prescription. -/
theorem purchasedWith {V : Type} [Fintype V] (simple : G.Simple) {ε : ℝ} (hε : 0 < ε)
    (J : Request V) (extra : Stage → ℕ → ℝ) (γ : ℝ) (hγ : -(1/2:ℝ) < γ)
    (calendar : XSpace.Run) (dial : Bool)
    (prediction : Prediction G) (price : FundedPredictionSupply.AllPrices (@prediction)) :
    ∃ (N : WilsonPrescription G) (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
      (S : Prescription (Press.portDeck G)), N.run = calendar ∧ Main.Match N simple M S dial ∧
      ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T)
        (paid : ManuscriptQLocalCofinalAffineFields.Paid R) (Q : Prescription (Press.portDeck G)),
        ∃ (orders : ManuscriptQLocalScalarDirections.PaidOrders schedule schedule R.kit)
          (table : WilsonScalarSourceTableForecast.Paid schedule schedule R.kit),
          prediction R.kit ∧ WilsonRootedPhysicalSpringReportedMS.Settled.{u} simple ε J extra γ M S R T W paid Q ∧
          WilsonRootedPhysicalSpringStoredMS.Ready simple M R paid Q orders ∧ Ready simple M R paid Q table := by
  let stock := @FundedPredictionSupply.Both G (@WilsonScalarSourceTableForecast.Paid G schedule schedule)
    (@prediction)
  obtain ⟨N,M,S,run,matched,R,T,W,paid,Q,orders,⟨table,receipt⟩,settled,stored⟩ :=
    WilsonRootedPhysicalSpringStoredMS.purchasedWith.{u} simple hε J extra γ hγ calendar dial (@stock)
      (fun s t => FundedPredictionSupply.both (WilsonScalarSourceTableForecast.prices schedule schedule s t)
        (price s t))
  refine ⟨N,M,S,run,matched,R,T,W,paid,Q,orders,table,receipt,settled,stored,?_⟩
  intro through power f rung hrung c hc
  filter_upwards [stored through power f rung hrung c hc] with b offered
  refine ⟨offered.1,offered.2.1,?_⟩
  intro I inst fi Γ d eligible
  have cutoff := (offered.1 d eligible).1
  exact fields R d table orders through power ((le_max_left _ _).trans cutoff) ((le_max_right _ _).trans cutoff)

end YM.Integration.WilsonRootedPhysicalSpringUnitMS
end

