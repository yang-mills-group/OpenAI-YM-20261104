import YM.Integration.WilsonPositionProgramWholeBirth
import YM.FVAAlt2.Block.Tables

/-! The whole deposited ordinary field and its own unmarked divisor over every
coarse Wilson chart on the first measured date. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionProgramWholeDeposit
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open PhysicalNext.Repeat.Legato PertExtension.Orb.SlotEvaluation
open Next.SectorChange PertExtension.Series Multi Marker Comparison.RG02
open Comparison.RG02.Cumulants Comparison.RG02.Laplace FormalOPE.RG10 PowerSeries
open RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Kick RegulatorIR.FVAAlt2.Booth
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} (C : Run G) (i per : ℕ)
    {I J : Type} [Fintype I] [LinearOrder I] [Fintype J] [DecidableEq J]
    (R : Census I) (R' : Census J) (s : R.Mode) (j : J)
    (d : I → ℕ) (v : (a : I) → (C.family.labels.level (d a)).Index) (z : I → Cover)
local notation "Γ" => RunFormalChain.fromRun C
local notation "Φ" => C.family.path
local notation "c" => C.family.side i per
local notation "f" => C.family.side (i+1) per
local notation "step₀" => (Φ).levels.clock.op i per
local notation "K" => (Γ).step (i+1) i per (Nat.lt_succ_self i)
local notation "coords" => wrap (f) ∘ z
local notation "W" => YM.FVAAlt2.Block.wardrobe C i per R coords d v
local notation "B" => RegulatorIR.FVAAlt2.Boot.scout C s.val d v z
local notation "W'" => RegulatorIR.FVAAlt2.Boot.ink R' j Φ (i+1) per (B)

omit [Fintype J] in
theorem vacuum (F : Forest (step₀).ratio) (t : (step₀).Choices) (A : fieldDir G c 1) :
    (YM.FVAAlt2.Block.naked K F t).den (YM.FVAAlt2.Block.action K F t A W) =
    (YM.FVAAlt2.Block.naked K F t).den (YM.FVAAlt2.Block.action K F t A W') := rfl

/-- Each full ordinary coefficient is retained as a field on the next date. -/
theorem deposited (F : Forest (step₀).ratio) (t : (step₀).Choices) (A : fieldDir G c 1) :
    (YM.FVAAlt2.Block.naked K F t).step (YM.FVAAlt2.Block.action K F t A W)
        (Word.read s (YM.FVAAlt2.Block.columns K F A W)) =
    (YM.FVAAlt2.Block.naked K F t).step (YM.FVAAlt2.Block.action K F t A W')
        (Word.read (R'.fire j) (YM.FVAAlt2.Block.columns K F A W')) := by
  ext k : 1
  have h := WilsonPositionProgramWholeBirth.original C i per R R' s j d v z F t A k k le_rfl
  change (Order.observe R k (Order.ratio (Bulk.Fk K F t W A k)) k).part s =
    (Order.observe R' k (Order.ratio (Bulk.Fk K F t W' A k)) k).part (R'.fire j) at h
  rw [← YM.FVAAlt2.Block.positive_normalization K F t A W k,
    ← YM.FVAAlt2.Block.positive_normalization K F t A W' k,
    Order.observation R k _ le_rfl, Order.observation R' k _ le_rfl,
    ← Word.unfold_see, ← Word.unfold_see, FlatFeed.close_part, FlatFeed.close_part] at h
  exact h

end YM.Integration.WilsonPositionProgramWholeDeposit
