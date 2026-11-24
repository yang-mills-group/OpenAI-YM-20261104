import YM.QuadraticLocal.Fk.Banner
import YM.Integration.WilsonOriginalProjectedCurvatureLamps
import YM.Integration.WilsonNormalizedMarkedSource

/-! The finite roster of submitted Wilson sources and its original normalized material colours. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalClubSourcePackets
open Precision Finset Lattice Wilson RG Tree Source Labels Marker Exterior
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM MergeProof.Accent FVA1
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureSalary
open WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureEnvelope
open WilsonOriginalProjectedCurvatureCredits QuadraticLocal.Earn AllOrder.Floe
open scoped Classical BigOperators
variable {G : Gauge} {R : Run G} {B : MS.Local.Physical.Deck G}
  {p L n : ℕ} {hn : n ≤ L} {V : Type} [DecidableEq V] [Fintype V]
  (Q : MS.Land.Prescription B) (D : ActualRunQlocalNativeTuple.Datum R p L n hn V)
  (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ) (N : ℕ)
  (σ : ℝ) (extra : V → ℕ)
local notation "Group" => Funded Q D u μ orders N σ
local notation "X" => WilsonOriginalProjectedCurvatureLamps.cohort Q D u μ orders N σ extra
local notation "w₀" => (fun _ : V => WilsonOriginalProjectedCurvatureLoan.toll (R:=R) u)
local notation "P₀" => ActualOriginalQPackets.packets Q D u μ orders N

private theorem staff (x : tastes D) :
    ∃ k, Air.Staff X (fun i => (X i).paint x) w₀ 1 k := by
  let d (i : Group) := max (X i).lamp.r (X i).lamp.stamp
  refine ⟨univ.sup d, zero_lt_one, ?_, ?_, ?_, (hasSum_fintype _).summable⟩
  · exact fun i => ((WilsonOriginalProjectedCurvatureLamps.issued Q D u μ orders N σ extra).usable i).2
  · intro i
    exact (le_max_left _ _).trans (Finset.le_sup (f := d) (mem_univ i))
  · intro i
    exact (le_max_right _ _).trans (Finset.le_sup (f := d) (mem_univ i))

variable (layout : Layout G) (tape : Finset Age) (x : tastes D)
local notation "U₀" => Air.craft X (fun i => (X i).paint x) w₀ layout tape
local notation "test" => testInclusion (ActualRunQlocalNativeTuple.orbit D) x

theorem original (point : BudgetPoint) (g : ℝ) (hg : g ≠ 0) (U : Config G (R.family.side L p)) :
    Comparison.RG02.Integral.markedLog g U U₀ = (P₀).read test g U := by
  obtain ⟨_, hs⟩ := staff Q D u μ orders N σ extra x
  have h := Air.liftPassport X (fun i => (X i).paint x) w₀ hs layout tape g hg U
  rw [← h.tsum_eq, tsum_fintype]
  exact (WilsonOriginalProjectedCurvatureLamps.measured Q D u μ orders N σ extra point g x U).trans
    ((WilsonOriginalProjectedCurvatureEnrollment.full Q D u μ orders N σ extra g x U).trans
      (WilsonOriginalProjectedCurvatureProgram.submitted Q D u μ orders N σ g x U))

local notation "W₀" => NativePaidPacketColors.colors P₀ (U₀).vac test
open Comparison.RG02 Comparison.RG02.Bulk

theorem finite {c : Side} {S : StepData c (R.family.side L p)}
    {clip : Clip} {path : PathData G} {chart : ChartRatio G}
    (K : Bulk.Kernel S clip path chart) (F : Forest S.ratio) (tag : S.Choices)
    (b : fieldDir G c 1) (r : ℕ) (hl : Legal tape layout)
    (point : BudgetPoint) (hL : L ≤ N) :
    Bulk.Fk K F tag U₀ b r = Bulk.Fk K F tag W₀ b r := by
  obtain ⟨_, hs⟩ := staff Q D u μ orders N σ extra x
  have paid := ActualOriginalQPackets.packets_paid Q D u μ orders N point (fun _ => 1) 1 zero_lt_one (fun _ => zero_lt_one)
  have h₀ : Pert.Asymptotics.regulatorRun R.family N p L ≠ 0 := (IterationFour.Currency.g_pos R.makes N p L hL).ne'
  have hw := (Air.standard X (fun i => (X i).paint x) w₀ hs layout tape hl).1
  have hv := NativePaidPacketColors.colors_well paid h₀ (U₀).vac hw.suppose_vac hw.natural hw.envelope test
  apply WilsonNormalizedMarkedSource.formal K F U₀ W₀ hw hv _ tag rfl
  intro g hg U
  exact (original Q D u μ orders N σ extra layout tape x point g hg U).trans
    (NativePaidPacketColors.colors_markedLog paid h₀ (U₀).vac test g hg U).symm

end YM.Integration.WilsonOriginalClubSourcePackets
end

