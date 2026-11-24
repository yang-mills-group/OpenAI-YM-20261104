import YM.Integration.FVA1Physical.Marked.ComplexCell
import YM.Comparison.RG02.Order.Pay

/-! The connected coefficient combines all joint, conditionally normalized
physical moments before extracting the mode. Its finite marker norm keeps
the individual weights and the moment error for every subset. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 950000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Function Filter Lattice RG Wilson Pressure Tree Precision Push PriceCompiler RG.Supply Input Org
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato AnalyticBridge VerifiedReset Collection
open Progress.DirectedRecipe Roof Extra.Iteration Time ThroughLaunch Roost JointLoad RGComparison.Core16
open ConnectedActivityE6 SectorMeasure Extra.Trajectories RG3.Script.Picnic MeasureTheory
open AllOrder Transit WheelP Floe Floe.Step.PlanV Qlocal Qlocal.Parabola RGComparison01 RGComparison01.Pledge
open Marker Canopy Merge Comparison.RG02.Order
open scoped BigOperators Classical Topology

variable {G : Gauge} {X : Run G} {z N n k m : ℕ} {path : ℕ → Floe.Layout G} {Γ : ℕ → Pace.Coin}
    {x : (i : ℕ) → Rep G (X.alloy.B.a.S.side i n)}
    (track : Metre X.alloy X.kit X.T path Γ z N n k x) (lo : z ≤ m) (hi : m < N)
    (T : Slices X.family.path.levels n)
    {ι : Type} [Fintype ι] (M : ι→Lotus.Leaf (x (m+1))) (g : ι→ℝ)
    (inj : Injective fun i => (M i).turn)
local notation "op" => X.family.path.levels.clock.op m n
local notation "outD" => traversal T hi.le
local notation "inD" => traversal T hi
local notation "outClock" => line X.family.path n m N
local notation "inClock" => line X.family.path n (m+1) N
local notation "B" => Button.universeP ι
variable (O : ι → Config G (X.family.side N n) → ℂ) (hO : ∀ i, Continuous (O i))
    (w : ι→ℝ) (hw : ∀ i,0<w i)
    (E : Finset ι→ℝ)
    (defect : ∀ s b, ‖(leafProduct M g s b : ℂ) - (traversal T hi).conditioned (line X.family.path n (m+1) N) (fullProduct O s) b‖ ≤ E s)

omit [Fintype ι] in
include track lo hi T in
theorem physical_quiet (V : Config G (X.family.side m n)) :
    Staircase.projection M g (S:=op) V ∅ = 1 := by
  have hv : 0 < (op).push (x (m+1)).beta (x (m+1)).eval V := by
    rw [(bank_history track lo hi T).2.2]
    exact Descent.positive _ (traversal_ok T hi.le) V
  let A := (x (m+1)).eval
  have hcard (b : Config G (X.alloy.B.a.S.side (m+1) n)) : A b * Staircase.cardTest M g op ∅ b = A b :=
    (congrArg (A b * ·) (Staircase.setModel M g b)).trans (mul_one _)
  exact (congrArg (fun f : Config G (X.alloy.B.a.S.side (m+1) n)→ℝ =>
    (op).push (x (m+1)).beta f V / (op).push (x (m+1)).beta A V) (funext hcard)).trans (div_self hv.ne')

include track lo inj hO hw defect in
/-- The independent terminal observable has its original complex joint moments and
one conditional denominator. The actual/coarse comparison costs one on every
incoming moment before applying the polynomial logarithm. -/
theorem physical_cumulant_error (V : Config G (X.family.side m n)) :
    let P := Button.mat (Staircase.projection M g (S:=op) V)
    let Q := (outD).moments B outClock O V
    let radius := max (Poly.price w (1-P)) (Poly.price w (1-Q))
    Poly.price w (connected P - (outD).cumulants B outClock O V) ≤
      repeats (Fintype.card ι) radius * ∑ s:(B).Mode, Poly.toll w s * E s.val := by
  intro P Q radius
  have pq : P.part (B).quiet=1 := (Button.mat_reads _ ∅).trans (by
    rw [physical_quiet track lo hi T M g V,Complex.ofReal_one])
  have qc : Q.part (B).quiet=1 := Descent.quiet_moment _ _ _ _ _ (traversal_ok T hi.le)
  have cap : Poly.price w (P-Q) ≤ ∑ s:(B).Mode,Poly.toll w s * E s.val := by
    apply Finset.sum_le_sum
    intro s _
    apply mul_le_mul_of_nonneg_left _ (Poly.worth hw s).le
    change ‖P.part s-Q.part s‖ ≤ _
    rw [show P.part s= (Staircase.projection M g (S:=op) V s.val:ℂ) from Button.mat_reads _ s.val]
    exact complex_source_bound track lo hi T M g inj s.val (fullProduct O s.val)
      (continuous_finsetProd _ (fun i _=>hO i)) (defect s.val) V
  have rr : 0≤ radius := (Poly.nonnegative hw (1-P)).trans (le_max_left ..)
  exact (lip P Q w hw pq qc (le_max_left ..) (le_max_right ..) (Fintype.card ι)
    (fun s=> Finset.card_le_univ s.val)).trans (mul_le_mul_of_nonneg_left cap (repeats_pos _ _ rr))

include track lo inj hO hw defect in
/-- A paid actual marked cluster bank at an arbitrary unflagged coarse field
has the preceding quantitative comparison to the independent conditional
Wilson cumulants, simultaneously in every physical marked mode. -/
theorem retained_cumulant_error (H : Opera.Guide X.alloy.B X.kit.shape N m n (x (m+1)))
    (regular : Staircase.grows M)
    (coast : Still.Coastal M g H (χ:=Chi.canonical) (X.alloy.B.a.budget m))
    (V : Config G (X.family.side m n)) (clear : flags (X.alloy.B.a.budget m).threshold V = ∅) :
    let P := Button.mat (Staircase.projection M g (S:=op) V)
    let Q := (outD).moments B outClock O V
    let radius := max (Poly.price w (1-P)) (Poly.price w (1-Q))
    Poly.price w (Button.mat (fun s => Reels.allotV M g H (χ:=Chi.canonical) s V) -
        (outD).cumulants B outClock O V) ≤
      repeats (Fintype.card ι) radius * ∑ s:(B).Mode, Poly.toll w s * E s.val := by
  intro P Q radius
  have bank : Button.mat (fun s=> Reels.allotV M g H (χ:=Chi.canonical) s V) = connected P := by
    rw [Still.coast M g H regular coast V clear (le_refl (Fintype.card ι))]
    exact (Button.matTrans _ (le_refl _) (physical_quiet track lo hi T M g V)).symm
  rw [bank]
  exact physical_cumulant_error track lo hi T M g inj O hO w hw E defect V
end YM.Integration.FVA1Physical.Marked
