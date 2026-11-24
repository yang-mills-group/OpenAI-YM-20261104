import YM.Integration.FVA1Physical.Marked.RetainedHistory
import YM.Integration.FVA1Physical.ActualPush

/-! The precise mixed-source identification that remains after the actual
representation has been read. This is an equality of functions of a retained
configuration and a unit-cost estimate on their values. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 850000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Function Filter Lattice RG Wilson Pressure Tree Precision Push PriceCompiler RG.Supply Input Org
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato AnalyticBridge VerifiedReset Collection
open Progress.DirectedRecipe Height Roof Extra.Iteration Time ThroughLaunch Roost JointLoad RGComparison.Core16
open ConnectedActivityE6 SectorMeasure Extra.Trajectories RG3.Script.Picnic MeasureTheory
open AllOrder Transit WheelP Floe Floe.Step.PlanV Qlocal Qlocal.Parabola RGComparison01 RGComparison01.Pledge
open scoped BigOperators Classical Topology

variable {G : Gauge} {X : Run G} {z N n k m : ℕ} {path : ℕ → Floe.Layout G} {Γ : ℕ → Pace.Coin}
    {x : (i : ℕ) → Rep G (X.alloy.B.a.S.side i n)}
    (track : Metre X.alloy X.kit X.T path Γ z N n k x) (lo : z ≤ m) (hi : m < N)
    (T : Slices X.family.path.levels n)
local notation "op" => X.family.path.levels.clock.op m n
local notation "outD" => traversal T hi.le
local notation "inD" => traversal T hi
local notation "outClock" => line X.family.path n m N
local notation "inClock" => line X.family.path n (m+1) N

variable {ι : Type} [Fintype ι] (M : ι→Lotus.Leaf (x (m+1))) (g : ι→ℝ)

def leafProduct {f : Side} {R : Rep G f} (L : ι→Lotus.Leaf R) (v : ι→ℝ) (s : Finset ι) (U : Config G f) :=
  (∏ i∈s,v i) * ∏ i∈s,(L i).ingredient U

omit [Fintype ι] in
private theorem leaf_integrable {f : Side} {R : Rep G f} (L : ι→Lotus.Leaf R) (v : ι→ℝ) (s : Finset ι)
    (w : Config G f → ℝ) (hw : Integrable w (prior G f)) :
    Integrable (fun b => w b * leafProduct L v s b) (prior G f) := by
  let B := |∏ i∈s,v i| * ∏ i∈s,(L i).weight
  have meas : Measurable (leafProduct L v s) := measurable_const.mul (Finset.measurable_fun_prod _ (fun i _ => (L i).borel))
  have cap (b : Config G f) : ‖leafProduct L v s b‖ ≤ B := by
    unfold leafProduct B
    rw [norm_mul,Real.norm_eq_abs (∏ i∈s,v i),norm_prod]
    exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun i _=>norm_nonneg _) (fun i _=>(L i).earn b)) (abs_nonneg _)
  change Integrable (w * leafProduct L v s) _
  simpa only [smul_eq_mul,mul_comm] using (hw.bdd_smul B meas.aestronglyMeasurable (Eventually.of_forall cap))

include track lo in
/-- For every marked mode and arbitrary retained field, subtracting the
independent Wilson observable leaves exactly its *incoming* mixed coefficient
error transported by the physical conditional block kernel. -/
theorem source_cell (inj : Injective fun i => (M i).turn) (s : Finset ι)
    (F : Config G (X.family.side N n) → ℝ) (hF : Continuous F) (V : Config G (X.family.side m n)) :
    Staircase.projection M g (S:=op) V s - (outD).conditioned outClock F V =
      conditionalPush X.family.path N n m (fun b => leafProduct M g s b - (inD).conditioned inClock F b) V := by
  let A := X.family.path
  let w := (A.rep N n (m+1)).eval
  let β := A.β N n (m+1)
  let L := leafProduct M g s
  let Y := (inD).weighted inClock F
  have hw : Integrable w (prior G _) := ((A.rep N n (m+1)).envelope (X.makes.wilson.represents N n (m+1) hi).good).integrable _
  have intL := leaf_integrable M g s w hw
  have intY : Integrable Y (prior G _) := weighted_integrable T hi F hF
  have hc (b) : w b * (inD).conditioned inClock F b = Y b := conditional_times T X.makes.wilson hi F b
  have best : Staircase.projection M g (S:=op) V s = ((A.rep N n m).eval V)⁻¹ *
      (op).push β (fun b=>w b*L b) V := by
    rw [projection_history track lo hi T M g inj s V]
    unfold source_path_moment
    rw [vacuum_eq T X.makes.wilson hi,vacuum_eq T X.makes.wilson hi.le,div_eq_inv_mul]
    rfl
  have hv : (outD).conditioned outClock F V = ((A.rep N n m).eval V)⁻¹ * (op).push β Y V := by
    rw [Descent.conditioned,vacuum_eq T X.makes.wilson hi.le,weighted_step T F hi]
    rfl
  rw [best,hv,← mul_sub]
  unfold conditionalPush
  change _ * (_-_) = _ * _
  congr 1
  change (∫ b, (op).density β b V * (w b*L b) ∂prior G _) - (∫ b, (op).density β b V * Y b ∂prior G _) = _
  refine (integral_sub (StepData.push_slice (A.levels.transition_mass m n β) V _ intL)
    (StepData.push_slice (A.levels.transition_mass m n β) V _ intY)).symm.trans ?_
  apply integral_congr_ae
  filter_upwards with b
  change _ - _ * Y b = _ * (w b * (L b - (inD).conditioned inClock F b))
  rw [←hc b]
  ring

include track lo in
/-- The price is one, independent of the volume, the coarse field, the
forest and the number of prior steps. Here the norm is the pointwise readout
after the mixed-mode representation has been evaluated. -/
theorem source_cell_bound (inj : Injective fun i => (M i).turn) (s : Finset ι)
    (F : Config G (X.family.side N n) → ℝ) (hF : Continuous F) {C : ℝ}
    (h : ∀ b, |leafProduct M g s b - (inD).conditioned inClock F b| ≤ C) (V : Config G (X.family.side m n)) :
    |Staircase.projection M g (S:=op) V s - (outD).conditioned outClock F V| ≤ C := by
  rw [source_cell track lo hi T M g inj s F hF V]
  exact conditionalPush_bound X.family.path X.makes.wilson N n m hi
    (fun b => leafProduct M g s b - (inD).conditioned inClock F b) C (fun b=>by simpa only [Real.norm_eq_abs] using h b) V

end YM.Integration.FVA1Physical.Marked
