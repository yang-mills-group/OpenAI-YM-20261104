import YM.Integration.WilsonOriginalProjectedCurvatureMovingArmada
import YM.QuadraticLocal.Campaign.Stencil

/-! Every enrolled club uses its actual jointly occupied Press toll on the
original course. No individual Cartesian color monomial is submitted as a new atom. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvatureSemesterVoter
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

omit [Fintype V] in
theorem admitted {n:Side} {P:Passport n V} {ρ:Marker.Census V} {ι α:Type} {M:ι→Row P ρ G α}
    {w:V→ℝ} {t:V→ℕ} {σ wage:ℝ} {rank height vol order count stage vac ceiling:ℕ}
    (funded:Scene.Armada M w t σ wage rank height vol)
    (read:rank ≤ ceiling) (extent:vol ≤ ceiling) (members:height ≤ count)
    (clock:order+1 ≤ stage) (scope:order+vol ≤ Burn.horizon vac+2) :
    Mentor.Cruise.Voter M σ order count stage vac ceiling := by
  refine ⟨?_,fun k=>(funded.quota k).trans members,clock,?_⟩
  · intro i
    have correct:=funded.purchases.usable i
    exact ⟨funded.honor i,funded.purchases.spend i,correct.1.trans read,
      correct.2 ▸ (funded.crew (M i).mode).trans extent⟩
  · intro club
    rw [Press.tall M club t funded.purchases.usable]
    exact (Nat.add_le_add_left (funded.crew (Club.alliance M club)) order).trans scope

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
    ∃ C:ℝ,1 ≤ C ∧ ∃ b:ℕ,∀ᶠ m:ℕ in atTop,∀ (r:Mentor.Opportunity (J₀ (m+1)) (J₀ m))
      (E:Mentor.Epoch root R.rolls (J₀ (m+1)) (J₀ m) r),
      h ≤ r.count → order+1 ≤ r.stage → order+v ≤ Burn.horizon E.vac+2 →
      ∀ Ω:ℝ,1 ≤ Ω → Ω ≤ (β̂ (m+1))^(Beaming.grain (J₀ m)) →
      ∀ (N p:ℕ) (o:V→Site (R.family.side (m+1) p)) (orders:V→ℕ), (∀i,orders i ≤ K) → m<N →
      let D:=ActualOriginalQPointSetup.pointDatum R J p (m+1) o
      let σ:=Poetry.Agenda.seed root ψ (Burn.horizon E.vac) (J₀ (m+1))
      let η:=(μ+R.family.S.scale N-R.family.S.scale (m+1))-R.family.S.scale N
      let X:=WilsonOriginalProjectedCurvatureLamps.cohort Q D u η orders N σ extra
      let a:=C*(β̂ (m+1))^(b+1)
      let g:=Coat.gStep (R.family.path.rep N p (m+1)).beta
      Mentor.Cruise.Voter X σ order r.count r.stage E.vac (J₀ m) ∧
      Scene.Armada X (fun j=>w j/(a*Ω)) (fun _=>t) σ Ω⁻¹ rank h v ∧
      ∀ s:(Stock.census V).Mode,Poly.toll (fun i=>w i/(a*Ω)) s*(a*Ω)^s.val.card=Poly.toll w s ∧
        (a*Ω)^s.val.card*g^(q+2*((b+1)*h)+1) ≤ ε*g^q := by
  obtain ⟨C,hC,b,paid⟩:=WilsonOriginalProjectedCurvatureMovingArmada.original R hG J Q u μ extra w root income K q hw εpos
  refine ⟨C,hC,b,?_⟩
  filter_upwards [paid,R.alloy.B.a.fits.deep.eventually_ge_atTop (rank+v)] with m purchase large
  intro r E seats stage book Ω one roof N p o orders cap live D σ η X a g
  have height:Burn.horizon E.vac ≤ J₀ (m+1):=
    (Nat.le_trans (Nat.le_add_right ..) E.paid).trans (step_paid R.alloy.B.a m).1
  obtain ⟨file,restore⟩:=purchase (Burn.horizon E.vac) height Ω one roof N p o orders cap live
  exact ⟨admitted file (by omega) (by omega) seats stage book,file,restore⟩

end YM.Integration.WilsonOriginalProjectedCurvatureSemesterVoter
