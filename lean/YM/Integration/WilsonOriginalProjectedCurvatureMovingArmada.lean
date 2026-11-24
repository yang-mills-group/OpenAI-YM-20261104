import YM.Integration.WilsonOriginalProjectedCurvatureArmada
import YM.Integration.WilsonOriginalProjectedCurvatureMovingClock
import YM.Integration.WilsonOriginalProjectedCurvatureReportingRefund

/-! All acquired support exponents and source powers on the same registered
course, before every later finite cutoff and every torus period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvatureMovingArmada
open Function Filter Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM MergeProof.Accent FVA1 FullQLocal FullQLocal.RenderedStep
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureSalary
open WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureEnvelope
open QuadraticLocal QuadraticLocal.Earn AllOrder AllOrder.Floe AllOrder.Floe.Step ConnectedActivityE6
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (hG:G.Simple) {B:MS.Local.Physical.Deck G}
  {V:Type} [DecidableEq V] [Fintype V] (J:Request V) (Q:MS.Land.Prescription B)
  (u:V→MS.Rake.Label B) (μ:ℝ) (extra:V→ℕ) (w:V→ℝ)
  {ψ:ℕ→ℕ} (root:PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
  (income:WilsonMovingMentorRootRadius.Income (M:=R.metals) root ψ R.alloy.delay)
local notation "β̂" => R.alloy.B.a.clock.hatBeta
local notation "J₀" => R.alloy.B.a.clock.J
local notation "t" => WilsonOriginalProjectedCurvatureLoan.toll (R:=R) u

include income hG
theorem original (K q:ℕ) (hw:∀i,0<w i) {ε:ℝ} (εpos:0<ε) :
    ∃ C:ℝ,1≤C ∧ ∃ b:ℕ,∀ᶠ m:ℕ in atTop, ∀ k:ℕ,k≤J₀ (m+1) →
      ∀ Ω:ℝ,1≤Ω → Ω≤(β̂ (m+1))^(Beaming.grain (J₀ m)) →
      ∀ (N p:ℕ) (o:V→Site (R.family.side (m+1) p)) (orders:V→ℕ), (∀i,orders i≤K) → m<N →
      let D:=ActualOriginalQPointSetup.pointDatum R J p (m+1) o
      let σ:=Poetry.Agenda.seed root ψ k (J₀ (m+1))
      let η:=(μ+R.family.S.scale N-R.family.S.scale (m+1))-R.family.S.scale N
      let X:=WilsonOriginalProjectedCurvatureLamps.cohort Q D u η orders N σ extra
      let a:=C*(β̂ (m+1))^(b+1)
      let g:=Coat.gStep (R.family.path.rep N p (m+1)).beta
      Scene.Armada X (fun j=>w j/(a*Ω)) (fun _=>t) σ Ω⁻¹
        (ActualOriginalQLayout.rankCap R u) (Fintype.card V) (Fintype.card V*t) ∧
      ∀ s:(Stock.census V).Mode,
        Poly.toll (fun i=>w i/(a*Ω)) s*(a*Ω)^s.val.card=Poly.toll w s ∧
        (a*Ω)^s.val.card*g^(q+2*((b+1)*Fintype.card V)+1)≤ε*g^q := by
  obtain ⟨C,hC,b,source⟩:=WilsonOriginalProjectedCurvatureMovingClock.purchased R hG J Q u μ extra w K hw
  have fees:=WilsonOriginalProjectedCurvatureReportingRefund.original (V:=V) R hG hC (b+1) q εpos
  have hot:=((Next.Rank.Station.hat_rate R.family.path.levels hG).comp (tendsto_add_atTop_nat 1)).eventually_ge_atTop (2:ℝ)
  refine ⟨C,hC,b,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually source,fees,hot] with m filed sale warm
  intro k reached Ω one roof N p o orders capped live D σ η X a g
  have levy:=WilsonMovingMentorRootRadius.at_date (ψ:=ψ) R root income (m+1) k reached
  have beta:= (R.makes.wilson.represents N p (m+1) (Nat.succ_le_of_lt live)).band.1
  change β̂ (m+1)/2 ≤ (R.family.path.rep N p (m+1)).beta at beta
  change 2 ≤ β̂ (m+1) at warm
  have head:1≤(R.family.path.rep N p (m+1)).beta:=by linarith
  have sqhead:1≤Real.sqrt (R.family.path.rep N p (m+1)).beta:=by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt head
  have pos:0<Pert.Asymptotics.regulatorRun R.family N p (m+1):=inv_pos.mpr (zero_lt_one.trans_le sqhead)
  have unit:Pert.Asymptotics.regulatorRun R.family N p (m+1)≤1:=inv_le_one_of_one_le₀ sqhead
  obtain ⟨pw,paid,restore⟩:=filed σ Ω (zero_lt_one.trans_le one) levy N p (m+1) o orders capped (Nat.succ_le_of_lt live) pos unit
  have members:=WilsonOriginalProjectedCurvatureProduction.census R u
  refine ⟨⟨⟨fun s=>(members s).1,fun s=>(members s).2⟩,pw,paid,
    WilsonOriginalProjectedCurvatureLamps.issued Q D u η orders N σ extra,?_⟩,?_⟩
  · intro i
    exact (WilsonOriginalProjectedCurvatureRender.priced Q D u η orders N i.1 σ (extra i.1.1.1) i.2).1
  · intro s
    exact ⟨restore s,sale Ω one roof N p live s⟩

end YM.Integration.WilsonOriginalProjectedCurvatureMovingArmada
