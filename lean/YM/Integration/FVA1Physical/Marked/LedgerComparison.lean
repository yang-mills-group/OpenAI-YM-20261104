import YM.Integration.FVA1Physical.Marked.LedgerTail

/-! Compare the actual finite low marked catalogue, with its signed rooted remainder,
to the independently normalized Wilson source cumulant on the same measured trajectory. -/
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Filter Function Lattice RG Pressure Tree Wilson
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure ConnectedActivityE6
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato AnalyticBridge VerifiedReset Collection
open Progress.DirectedRecipe Roof Extra.Iteration Time ThroughLaunch Roost JointLoad RGComparison.Core16
open RGComparison01 RGComparison01.Pledge Holdings Merge Qlocal Qlocal.Parabola
open AllOrder Transit WheelP Floe Floe.Step.PlanV Push.PriceCompiler RG.Supply Input Org
open MeasureTheory Canopy Leasing Marker Extra.Trajectories Comparison.RG02.Order
open scoped BigOperators Classical Topology
variable {G : Gauge} {X : Run G} {z N n k m : ℕ} {path : ℕ → Floe.Layout G} {Γ : ℕ → Pace.Coin}
    {x : (i : ℕ) → Rep G (X.alloy.B.a.S.side i n)}
    (track : Metre X.alloy X.kit X.T path Γ z N n k x) (lo : z ≤ m) (hi : m < N)
    (T : Slices X.family.path.levels n)
    {ι : Type} [Fintype ι] (M : ι→Lotus.Leaf (x (m+1))) (g : ι→ℝ)
    (H : Opera.Guide X.alloy.B X.kit.shape N m n (x (m+1)))
    (hH : Opera.Price X.alloy.B X.kit.shape N m n (x (m+1)) H)
    {k₀ j₀ : ℕ} (η : ℕ→ℝ) (B₀ : Bauble G (X.rolls.L (X.alloy.B.a.clock.J (m+1))))
    (funds : Opened X.kit η k₀ j₀ m B₀)
    (regular : Staircase.grows M) (inj : Injective fun i => (M i).turn)
local notation "p" => X.alloy.B.a.budget m
local notation "χ₀" => Chi.canonical
local notation "op" => X.family.path.levels.clock.op m n

local notation "ℬ" => Button.universeP ι
local notation "outD" => traversal T hi.le
local notation "outClock" => line X.family.path n m N

include track lo hi hH funds regular inj in
/-- The finite physical catalogue corrected by the exact omitted signed rows compares
at every unflagged retained field with the independently normalized mixed Wilson
cumulant. The only source-identification error is the discrepancy of each actual
incoming product against the corresponding independent *joint* conditional moment. -/
theorem signed_ledger_wilson {d : ℕ} (ribbon : Ribbon (x (m+1)) d) (s : Finset ι) (hs : s.Nonempty)
    (degree depth : ℕ) (V : Config G (X.family.side m n)) (clear : flags (p).threshold V = ∅)
    (O : ι → Config G (X.family.side N n) → ℂ) (hO : ∀ i, Continuous (O i))
    (w : ι→ℝ) (hw : ∀ i, 0 < w i) (E : Finset ι→ℝ)
    (defect : ∀ t b, ‖(leafProduct M g t b : ℂ) - (traversal T hi).conditioned
      (line X.family.path n (m+1) N) (fullProduct O t) b‖ ≤ E t) :
    let a := commonAperture M (B₀.mass (X.alloy.B.a.clock.hatBeta m))
    let signed := ∏ i∈s, g i/a
    let tail := ∑' z : Baked.Cl M H, masked (p).threshold (Baked.origins M H z)
      (Bridges.balance M (fun _=>a) H ribbon degree depth s (χ:=χ₀) z) V
    let P := Button.mat (Staircase.projection M g (S:=op) V)
    let Q := (outD).moments ℬ outClock O V
    let radius := max (Poly.price w (1-P)) (Poly.price w (1-Q))
    Poly.toll w (Button.tile s) * ‖((Stowe.tale M g H (Drawing.cabinet H ribbon) degree depth s V
      (χ:=χ₀) + signed*tail : ℝ) : ℂ) - ((outD).cumulants ℬ outClock O V).part (Button.tile s)‖ ≤
      repeats (Fintype.card ι) radius * ∑ t:(ℬ).Mode, Poly.toll w t * E t.val := by
  intro a signed tail P Q radius
  have cell := Poly.member hw (Button.tile s) (connected P - (outD).cumulants ℬ outClock O V)
  have total := cell.trans (physical_cumulant_error track lo hi T M g inj O hO w hw E defect V)
  have logs := (signed_low_history track lo hi T M g H hH η B₀ funds regular inj ribbon s hs degree depth V clear).2
  have owned : (connected P).part (Button.tile s) =
      ((Stowe.tale M g H (Drawing.cabinet H ribbon) degree depth s V (χ:=χ₀) + signed*tail : ℝ) : ℂ) := by
    change (connected (Button.mat _)).part _ = _
    rw [Button.matTrans _ (le_refl (Fintype.card ι)) (physical_quiet track lo hi T M g V),Button.mat_reads]
    apply congrArg Complex.ofReal
    exact (congrArg (fun t=> Button.Earmark t (Fintype.card ι) s)
      (funext fun t=> projection_history track lo hi T M g inj t V)).trans logs.symm
  simpa only [part_sub,owned] using total
end YM.Integration.FVA1Physical.Marked
