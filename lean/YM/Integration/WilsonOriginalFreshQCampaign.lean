import YM.Integration.WilsonOriginalFreshQWallet
import YM.Integration.WilsonMovingMentorRaffleCourse
import YM.Integration.WilsonOriginalQBirthWallet

/-! Purchase the new operand of an original received marked date on the
same Concourse. The source currency precedes its accuracy and the course
retains the original measured vacuum and physical cutoff parameters. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalFreshQCampaign
open Function Filter Finset Lattice Wilson RG Marker Source Labels
open QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Mentor QuadraticLocal.MintClock
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Transit AllOrder.Transit.WheelP
open Push.PriceCompiler Org ConnectedActivityE6
open LocalComparison ComparisonDensity.Address Comparison.Density.RenderM MergeProof.Accent FVA1
open FullQLocal FullQLocal.RenderedStep
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureLamps
open WilsonOriginalFreshQWallet
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) (hG : G.Simple) {B : MS.Local.Physical.Deck G}
  {V : Type} [DecidableEq V] [Fintype V] (J : Request V) (Q : MS.Land.Prescription B)
  (labels : V → MS.Rake.Label B) (μ : ℝ) (extra : V → ℕ) (w : V → ℝ)
  {ψ : ℕ → ℕ} (root : PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
  (income : WilsonMovingMentorRootRadius.Income (M:=R.metals) root ψ R.alloy.delay)
  (warm : Spill.Raffle.Warm G root R.alloy.delay ψ)
  {E : V → Type} [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
  (A : ∀ i, Set (E i)) (K : ∀ i, Submodule ℝ (E i))
local notation "h" => Fintype.card V
local notation "t" => WilsonOriginalProjectedCurvatureLoan.toll (R:=R) labels
local notation "v" => h*t
local notation "rank" => ActualOriginalQLayout.rankCap R labels
local notation "head" => (rank+v+1)
local notation "β̂" => R.alloy.B.a.clock.hatBeta
local notation "stage" => R.alloy.B.a.clock.J

def Equipped (C : ℝ) (b order : ℕ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ k : ℕ, k ≤ stage m → ∀ Ω : ℝ, 0 < Ω →
    ∀ (N per : ℕ) (o : V → Site (R.family.side m per)) (orders : V → ℕ), (∀ i, orders i ≤ order) →
    ∀ (lo seed : ℕ) (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin)
      (H : (j : ℕ) → Rep G (R.alloy.B.a.S.side j per)),
      Concourse R.alloy R.kit R.T π Γ lo N per seed H → lo ≤ m → m ≤ N →
    let D := ActualOriginalQPointSetup.pointDatum R J per m o
    let η := (μ+R.family.S.scale N-R.family.S.scale m)-R.family.S.scale N
    let σ := Poetry.Agenda.seed root ψ k (stage m)
    let a := C*(β̂ m)^(b+1)
    let wQ := fun i => w i/(a*Ω)
    let price := Spill.Raffle.fundsOne G (R.metals.p.profile (stage m)) σ rank v h (β̂ m)*Ω⁻¹
    let p := (H m).p
    ∀ (oldHome : Passport (R.family.side m per) V) (old fresh : Finset V) (apart : Disjoint old fresh)
      (offer : V → ℝ), (∀ i, 0 < offer i) → (∀ i ∈ fresh, offer i ≤ wQ i) →
    Return Q D labels η orders N σ extra A K oldHome old fresh apart p wQ offer price
        (Spill.allOver p ^ (head)*price) ∧
      (∀ s : (Stock.census V).Mode, Poly.toll wQ s*(a*Ω)^s.val.card = Poly.toll w s) ∧
      Spill.allOver p ^ (head)*price ≤ (β̂ m)^(Spill.Raffle.pad (head))*Willow.haloSlack p.B*Ω⁻¹

include hG income warm
theorem atBirth (order : ℕ) (positive : ∀ i, 0 < w i) {C : ℝ} {b : ℕ}
    (source : WilsonOriginalQBirthWallet.At
      (WilsonOriginalProjectedCurvatureMovingClock.purchased R hG J Q labels μ extra w order positive) C b) :
    Equipped (ψ:=ψ) R J Q labels μ extra w root A K C b order := by
  have deep := R.alloy.B.a.fits.deep.eventually_ge_atTop (rank + v + h)
  filter_upwards [source,deep] with m filed grades
  intro k reached Ω hΩ N per o orders bound lo seed π Γ H course start alive
  dsimp only
  intro oldHome old fresh apart offer pos fits
  let D := ActualOriginalQPointSetup.pointDatum R J per m o
  let η := (μ+R.family.S.scale N-R.family.S.scale m)-R.family.S.scale N
  let σ := Poetry.Agenda.seed root ψ k (stage m)
  let a := C*(β̂ m)^(b+1)
  let wQ := fun i => w i/(a*Ω)
  let X := cohort Q D labels η orders N σ extra
  let g := Pert.Asymptotics.regulatorRun R.family N per m
  have entry := course.1.walk m start alive
  have glaw : g = Coat.gStep (H m).beta := by rw [entry.beta]; rfl
  have raw := WilsonMovingMentorRaffleCourse.measured R warm course start reached
    (show rank ≤ stage m by omega) (show v ≤ stage m by omega) (show h ≤ stage m by omega) alive
  obtain ⟨rawInvoice,gross⟩ := raw
  rw [←glaw] at rawInvoice
  have wide := WilsonMovingMentorRootRadius.at_date (ψ:=ψ) R root income m k reached
  obtain ⟨sourcePos,charges,restore⟩ := filed σ Ω hΩ wide N per m o orders bound alive rawInvoice.1 rawInvoice.2.1
  have census := WilsonOriginalProjectedCurvatureProduction.census R labels
  have book : Scene.Armada X wQ (fun _ => t) σ Ω⁻¹ rank h v :=
    ⟨⟨fun s => (census s).1,fun s => (census s).2⟩,sourcePos,charges,
      WilsonOriginalProjectedCurvatureLamps.issued Q D labels η orders N σ extra,
      fun i => (WilsonOriginalProjectedCurvatureRender.priced Q D labels η orders N i.1 σ
        (extra i.1.1.1) i.2).1⟩
  have native := WilsonOriginalFreshQWallet.original Q D labels η orders N σ extra A K
    oldHome old fresh apart (H m).p alive book pos fits rawInvoice
  have same : Spes.Market.tuning (R.metals.p.profile (stage m)) (H m).p (β̂ m) := by
    rw [entry.truep.point,←params_eq R.alloy.B.valid m]
    exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  have quote := Spill.Raffle.regular G (R.metals.p.profile (stage m)) σ rank v h (H m).p (β̂ m)
    same.2.2 same.2.1
  rw [quote] at native
  refine ⟨native,restore,?_⟩
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right gross (inv_nonneg.mpr hΩ.le)

theorem prepaid (order : ℕ) (positive : ∀ i, 0 < w i) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ b : ℕ, Equipped (ψ:=ψ) R J Q labels μ extra w root A K C b order := by
  obtain ⟨C,hC,b,source⟩ := WilsonOriginalProjectedCurvatureMovingClock.purchased R hG J Q labels μ extra w order positive
  exact ⟨C,hC,b,atBirth R hG J Q labels μ extra w root income warm A K order positive source⟩

end YM.Integration.WilsonOriginalFreshQCampaign
