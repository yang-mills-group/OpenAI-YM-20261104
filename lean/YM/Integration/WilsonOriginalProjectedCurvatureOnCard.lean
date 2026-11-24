import YM.Integration.WilsonOriginalProjectedCurvatureSemesterVoter
import YM.Integration.WilsonMovingMentorItinerary

/-! Register the complete signed curvature input using the actual prior card. -/
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvatureOnCard
open Function Filter Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM MergeProof.Accent FVA1 FullQLocal FullQLocal.RenderedStep
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureSalary
open WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureEnvelope
open QuadraticLocal QuadraticLocal.Earn AllOrder AllOrder.Floe AllOrder.Floe.Step ConnectedActivityE6
open Push.PriceCompiler
open scoped Classical BigOperators
variable {G:Gauge} {V:Type} [DecidableEq V] [Fintype V]

variable (R:Run G) (hG:G.Simple) {B:MS.Local.Physical.Deck G}
  (J:Request V) (Q:MS.Land.Prescription B) (u:V→MS.Rake.Label B) (μ:ℝ) (extra:V→ℕ) (w:V→ℝ)
  {ψ:ℕ→ℕ} (root:PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
  (income:WilsonMovingMentorRootRadius.Income (M:=R.metals) root ψ R.alloy.delay)
local notation "β̂" => R.alloy.B.a.clock.hatBeta
local notation "J₀" => R.alloy.B.a.clock.J
local notation "t" => WilsonOriginalProjectedCurvatureLoan.toll (R:=R) u
local notation "h" => Fintype.card V
local notation "v" => h*t
local notation "rank" => ActualOriginalQLayout.rankCap R u

include hG income
theorem original (K order q:ℕ) (hw:∀i,0<w i) {ε:ℝ} (εpos:0<ε) :
    ∃ C:ℝ,1 ≤ C ∧ ∃ b:ℕ,∀ᶠ m:ℕ in atTop,∀ _:WilsonMovingMentorItinerary.CardAt R root (order+v+h) m,
    ∀ Ω:ℝ,1 ≤ Ω → Ω ≤ (β̂ (m+1))^(Beaming.grain (J₀ m)) →
      ∀ (N p:ℕ) (o:V→Site (R.family.side (m+1) p)) (orders:V→ℕ), (∀i,orders i ≤ K) → m<N →
      let D:=ActualOriginalQPointSetup.pointDatum R J p (m+1) o
      let σ:=Poetry.Agenda.seed root ψ (Burn.horizon (order+v+h)) (J₀ (m+1))
      let η:=(μ+R.family.S.scale N-R.family.S.scale (m+1))-R.family.S.scale N
      let X:=WilsonOriginalProjectedCurvatureLamps.cohort Q D u η orders N σ extra
      let a:=C*(β̂ (m+1))^(b+1)
      let g:=Coat.gStep (R.family.path.rep N p (m+1)).beta
      Mentor.Cruise.Voter X σ order h (order+1) (order+v+h) (J₀ m) ∧
      Scene.Armada X (fun j=>w j/(a*Ω)) (fun _=>t) σ Ω⁻¹ rank h v ∧
      ∀ s:(Stock.census V).Mode,Poly.toll (fun i=>w i/(a*Ω)) s*(a*Ω)^s.val.card=Poly.toll w s ∧
        (a*Ω)^s.val.card*g^(q+2*((b+1)*h)+1) ≤ ε*g^q := by
  obtain ⟨C,hC,b,course⟩:=WilsonOriginalProjectedCurvatureSemesterVoter.original R hG J Q u μ extra w root income K order q hw εpos
  refine ⟨C,hC,b,?_⟩
  let k:=order+v+h
  filter_upwards [course,R.alloy.B.a.fits.deep.eventually_ge_atTop (Burn.horizon k+2),
    R.alloy.B.a.fits.deep.eventually_ge_atTop (h+order+1)] with m ready high room
  intro card
  let r:Mentor.Opportunity (J₀ (m+1)) (J₀ m):=⟨h,order+1,step_paid R.alloy.B.a m,by omega,by omega,by omega⟩
  let E:Mentor.Epoch root R.rolls (J₀ (m+1)) (J₀ m) r:=
    ⟨k,R.alloy.B.a.clock.adm (m+1),high,⟨card⟩⟩
  have horizon:order+v ≤ Burn.horizon k+2:=by unfold Burn.horizon k; omega
  exact ready r E (le_refl _) (le_refl _) horizon

end YM.Integration.WilsonOriginalProjectedCurvatureOnCard
