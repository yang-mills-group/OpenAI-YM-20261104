import YM.Integration.WilsonOriginalProjectedCurvatureAdmission
import YM.QuadraticLocal.Earn.Blend

/-! The assessed entire independent Q is a genuine original financed Armada
on the selected measured run, including its actual source powers at every
occupied mode and the exact restoration along the booked gauges. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvatureArmada
open Function Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM MergeProof.Accent FVA1
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureSalary
open WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureEnvelope
open FullQLocal FullQLocal.RenderedStep
open WilsonOriginalProjectedCurvatureCredits
open scoped Classical BigOperators
variable {G : Gauge} {R : Run G} {B : MS.Local.Physical.Deck G}
  {p L n : ℕ} {hn : n ≤ L} {V : Type} [DecidableEq V] [Fintype V]
  (Q : MS.Land.Prescription B) (D : ActualRunQlocalNativeTuple.Datum R p L n hn V)
  (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ) (N : ℕ)
  (σ : ℝ) (extra : V → ℕ) (w : V→ℝ)
local notation "Group" => Funded Q D u μ orders N σ
local notation "X" => WilsonOriginalProjectedCurvatureLamps.cohort Q D u μ orders N σ extra


variable (run:Run G) (J:Request V)
local notation "t" => WilsonOriginalProjectedCurvatureLoan.toll (R:=run) u
local notation "asked" => WilsonOriginalProjectedCurvatureClock.charge run J u σ σ extra w
theorem original (K:ℕ) (hw:∀i,0<w i) :
    ∃ C : ℝ, 0<C ∧ ∃ b : ℕ, ∀ (N p L:ℕ) (o:V→Site (run.family.side L p)) (orders:V→ℕ),
      (∀i,orders i≤K) → L≤N → 0<Pert.Asymptotics.regulatorRun run.family N p L →
      Pert.Asymptotics.regulatorRun run.family N p L≤1 → ∀ (Ω:ℝ),0<Ω →
    let D₀ := ActualOriginalQPointSetup.pointDatum run J p L o
    let X₀ := WilsonOriginalProjectedCurvatureLamps.cohort Q D₀ u (μ-run.family.S.scale N) orders N σ extra
    let a := max 1 ((C*(1+‖run.family.S.scale N‖)^b)*asked)
    QuadraticLocal.Earn.Scene.Armada X₀ (fun i=>w i/(a*Ω)) (fun _=>t) σ Ω⁻¹
      (ActualOriginalQLayout.rankCap run u) (Fintype.card V) (Fintype.card V*t) ∧
      ∀ k:(Stock.census V).Mode, Poly.toll (fun i=>w i/(a*Ω)) k*(a*Ω)^k.val.card=Poly.toll w k := by
  obtain ⟨C,hC,b,h⟩:=WilsonOriginalProjectedCurvatureAdmission.original (run:=run) (J:=J)
    (Q:=Q) (u:=u) (μ:=μ) (σ:=σ) (extra:=extra) (w:=w) K hw
  obtain ⟨_,_,_,g⟩:=WilsonOriginalProjectedCurvatureProduction.original run J Q u μ σ extra w K hw
  refine ⟨C,hC,b,?_⟩
  intro N p L o orders ho hL hg hx Ω hΩ D₀ X₀ a
  obtain ⟨pos,off,restore⟩:=h N p L o orders ho hL hg hx Ω hΩ
  obtain ⟨_,issues,hon,hms⟩:=g N p L o orders ho hL hg hx
  exact ⟨⟨⟨fun k=>(hms k).1,fun k=>(hms k).2⟩,pos,off,issues,hon⟩,restore⟩

end YM.Integration.WilsonOriginalProjectedCurvatureArmada
