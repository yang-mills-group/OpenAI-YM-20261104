import YM.Integration.WilsonOriginalClubSourcePackets
import YM.Integration.PhysicalWilsonPeriodizedMaterial

/-! The original submitted roster on the same finite periodic Gaussian in both source conventions. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalClubSourceReference
open Finset Lattice Wilson RG Tree Source Labels Marker Exterior
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM MergeProof.Accent FVA1
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureSalary WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureEnvelope
open QuadraticLocal.Earn AllOrder.Floe Comparison.RG02
open private staff from YM.Integration.WilsonOriginalClubSourcePackets
open scoped Classical BigOperators
variable {G : Gauge} {R : Run G} {B : MS.Local.Physical.Deck G}
  {per i n : ℕ} {hn : n ≤ i+1} {V : Type} [DecidableEq V] [Fintype V]
  (Q : MS.Land.Prescription B) (D : ActualRunQlocalNativeTuple.Datum R per (i+1) n hn V)
  (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ) (N : ℕ)
  (σ : ℝ) (extra : V → ℕ) (layout : Layout G) (tape : Finset Age)
  (x : tastes D)

local notation "X" => WilsonOriginalProjectedCurvatureLamps.cohort Q D u μ orders N σ extra
local notation "w₀" => (fun _ : V => WilsonOriginalProjectedCurvatureLoan.toll (R:=R) u)
local notation "Y₀" => Air.craft X (fun a => (X a).paint x) w₀ layout tape
local notation "test" => testInclusion (ActualRunQlocalNativeTuple.orbit D) x
local notation "P₀" => ActualOriginalQPackets.packets Q D u μ orders N
local notation "W₀" => NativePaidPacketColors.colors P₀ (Y₀).vac test

theorem original (below : i < N) (legal : Legal tape layout) (point : BudgetPoint)
    (F : Forest (R.family.path.levels.clock.op i per).ratio) (tag : (R.family.path.levels.clock.op i per).Choices)
    (b : fieldDir G (R.family.side i per) 1) (r : ℕ) :
    (Y₀).Standard ∧ (W₀).Standard ∧
      PhysicalWilsonPeriodizedMaterial.reference R N i per below b Y₀ r =
        PhysicalWilsonPeriodizedMaterial.reference R N i per below b W₀ r := by
  obtain ⟨_, hs⟩ := staff Q D u μ orders N σ extra x
  have hY := Air.standard X (fun a => (X a).paint x) w₀ hs layout tape legal
  have paid := ActualOriginalQPackets.packets_paid Q D u μ orders N point (fun _ => 1) 1 zero_lt_one (fun _ => zero_lt_one)
  have hg := (IterationFour.Currency.g_pos R.makes N per (i+1) below).ne'
  have hW : (W₀).Standard := ⟨NativePaidPacketColors.colors_well paid hg (Y₀).vac hY.1.suppose_vac
    hY.1.natural hY.1.envelope test, hY.2⟩
  have h := WilsonOriginalClubSourcePackets.finite Q D u μ orders N σ extra layout tape x
    ((RunFormalChain.fromRun R).step N i per below) F tag b r legal point below
  exact ⟨hY, hW, (PhysicalWilsonPeriodizedMaterial.original R N i per below b Y₀ r F tag hY.1).symm.trans
    (h.trans (PhysicalWilsonPeriodizedMaterial.original R N i per below b W₀ r F tag hW.1))⟩

end YM.Integration.WilsonOriginalClubSourceReference
end

