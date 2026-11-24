import YM.Integration.FVA1Physical.Marked.LedgerComparison

/-! Transport the actual mixed error in its conditional average norm. This
keeps nonflat incoming fields and their measured posterior weights, allowing
exceptional sets to be charged by their probability. -/
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Function Filter Lattice RG Wilson Pressure Tree Precision Push PriceCompiler RG.Supply Input Org
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato AnalyticBridge VerifiedReset Collection
open Progress.DirectedRecipe Roof Extra.Iteration Time ThroughLaunch Roost JointLoad RGComparison.Core16
open ConnectedActivityE6 SectorMeasure Extra.Trajectories RG3.Script.Picnic MeasureTheory
open AllOrder Transit WheelP Floe Floe.Step.PlanV Qlocal Qlocal.Parabola RGComparison01 RGComparison01.Pledge
open Marker Canopy Merge Comparison.RG02.Order
open scoped BigOperators Classical Topology

open YM.Wilson
section Kernel
variable {G : Gauge} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- Positivity of both actual vacuum factors and the physical block kernel
makes the conditional mean of the entrywise absolute errors a valid price. -/
theorem conditional_mean_norm (A : History G) (selected : A.Selected) {N n m : ℕ} (hi : m<N)
    (F : Config G (A.S.side (m+1) n)→E) (V : Config G (A.S.side m n)) :
    ‖conditionalPush A N n m F V‖ ≤ conditionalPush A N n m (fun v=>‖F v‖) V := by
  let S := A.levels.clock.op m n
  let β := A.β N n (m+1)
  let incoming := (A.rep N n (m+1)).eval
  let μ := prior G (A.S.side (m+1) n)
  have pos := (SectorNext.Vacuum.strictly A selected N n m hi.le V).le
  have nonneg (v) : 0 ≤ incoming v := A.nonnegative selected N n (m+1) hi v
  have ker (v) : 0 ≤ S.density β v V := (A.levels.transition_mass m n β).positive v V
  have triangle := norm_integral_le_integral_norm (μ:=μ) (fun v=> S.density β v V • (incoming v • F v))
  have row (v) : ‖S.density β v V • (incoming v • F v)‖ = S.density β v V * (incoming v * ‖F v‖) := by
    simp only [norm_smul,Real.norm_of_nonneg (ker v),Real.norm_of_nonneg (nonneg v)]
  simp_rw [row] at triangle
  unfold conditionalPush StepData.push
  rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr pos)]
  exact mul_le_mul_of_nonneg_left triangle (inv_nonneg.mpr pos)
end Kernel
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

include track lo inj hO hw in
/-- Price the complete finite marked log by the actual conditional integral
of its distinct incoming product errors. There is no pointwise or supremum
invoice on the interacting inputs. -/
theorem mean_cumulant_error (V : Config G (X.family.side m n)) :
    let P := Button.mat (Staircase.projection M g (S:=op) V)
    let Q := (outD).moments B outClock O V
    let radius := max (Poly.price w (1-P)) (Poly.price w (1-Q))
    let bill := fun (s : Finset ι) => conditionalPush X.family.path N n m (fun v=>
      ‖(leafProduct M g s v : ℂ) - (inD).conditioned inClock (fullProduct O s) v‖) V
    Poly.price w (connected P - (outD).cumulants B outClock O V) ≤
      repeats (Fintype.card ι) radius * ∑ s:(B).Mode, Poly.toll w s * bill s.val := by
  intro P Q radius bill
  have pq : P.part (B).quiet=1 := (Button.mat_reads _ ∅).trans (by
    rw [physical_quiet track lo hi T M g V,Complex.ofReal_one])
  have qc : Q.part (B).quiet=1 := Descent.quiet_moment _ _ _ _ _ (traversal_ok T hi.le)
  have cap : Poly.price w (P-Q) ≤ ∑ s:(B).Mode,Poly.toll w s * bill s.val := by
    apply Finset.sum_le_sum
    intro s _
    apply mul_le_mul_of_nonneg_left _ (Poly.worth hw s).le
    change ‖P.part s-Q.part s‖ ≤ _
    rw [show P.part s= (Staircase.projection M g (S:=op) V s.val:ℂ) from Button.mat_reads _ s.val]
    change ‖(Staircase.projection M g (S:=op) V s.val :ℂ) -(outD).conditioned outClock (fullProduct O s.val) V‖ ≤ _
    rw [complex_source_cell track lo hi T M g inj s.val (fullProduct O s.val) (continuous_finsetProd _ (fun i _=>hO i)) V]
    exact conditional_mean_norm X.family.path X.makes.wilson hi _ V
  have rr : 0≤ radius := (Poly.nonnegative hw (1-P)).trans (le_max_left ..)
  exact (lip P Q w hw pq qc (le_max_left ..) (le_max_right ..) (Fintype.card ι)
    (fun s=> Finset.card_le_univ s.val)).trans (mul_le_mul_of_nonneg_left cap (repeats_pos _ _ rr))
end YM.Integration.FVA1Physical.Marked
