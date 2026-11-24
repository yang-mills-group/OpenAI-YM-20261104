import YM.Integration.FVA1Physical.Marked.SourceCell
import YM.RGComparison.Core16.Marks

/-! One block takes the actual real wallet slots into the complex physical
moment table, without choosing separate budgets for the real and imaginary
components. -/
set_option autoImplicit false
set_option maxHeartbeats 950000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Function Filter Lattice RG Wilson Pressure Tree Precision Push PriceCompiler RG.Supply Input Org
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato AnalyticBridge VerifiedReset Collection
open Progress.DirectedRecipe Roof Extra.Iteration Time ThroughLaunch Roost JointLoad RGComparison.Core16
open ConnectedActivityE6 SectorMeasure Extra.Trajectories RG3.Script.Picnic MeasureTheory
open AllOrder Transit WheelP Floe Floe.Step.PlanV Qlocal Qlocal.Parabola RGComparison01 RGComparison01.Pledge
open scoped BigOperators Classical Topology

variable {G : Gauge} {X : Run G} {z N n k m : ℕ} {path : ℕ → Floe.Layout G} {Γ : ℕ → Pace.Coin}
    {x : (i : ℕ) → Rep G (X.alloy.B.a.S.side i n)}
    (track : Metre X.alloy X.kit X.T path Γ z N n k x) (lo : z ≤ m) (hi : m < N)
    (T : Slices X.family.path.levels n)
    {ι : Type} [Fintype ι] (M : ι→Lotus.Leaf (x (m+1))) (g : ι→ℝ)
local notation "op" => X.family.path.levels.clock.op m n
local notation "outD" => traversal T hi.le
local notation "inD" => traversal T hi
local notation "outClock" => line X.family.path n m N
local notation "inClock" => line X.family.path n (m+1) N

include track lo in
theorem complex_source_cell (inj : Injective fun i => (M i).turn) (s : Finset ι)
    (F : Config G (X.family.side N n) → ℂ) (hF : Continuous F) (V : Config G (X.family.side m n)) :
    (Staircase.projection M g (S:=op) V s : ℂ) - (outD).conditioned outClock F V =
      conditionalPush X.family.path N n m (fun b => (leafProduct M g s b : ℂ) - (inD).conditioned inClock F b) V := by
  let A := X.family.path
  let β := A.β N n (m+1)
  let w := (A.rep N n (m+1)).eval
  let Z := (A.rep N n m).eval V
  let L : Config G (A.S.side (m+1) n) → ℝ := leafProduct M g s
  let Y := (inD).weighted inClock F
  have hw : Integrable w (prior G _) := ((A.rep N n (m+1)).envelope (X.makes.wilson.represents N n (m+1) hi).good).integrable _
  let bound := |∏ i∈s,g i| * ∏ i∈s,(M i).weight
  have hL : Measurable L := measurable_const.mul (Finset.measurable_fun_prod _ (fun i _ => (M i).borel))
  have hbound (a) : ‖L a‖ ≤ bound := by
    unfold L leafProduct bound
    rw [norm_mul,Real.norm_eq_abs (∏ i∈s,g i),norm_prod]
    exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun i _=>norm_nonneg _) (fun i _=>(M i).earn a)) (abs_nonneg _)
  have hmass : Integrable (fun b => w b*L b) (prior G _) := by
    change Integrable (w * L) _
    simpa only [smul_eq_mul,mul_comm] using hw.bdd_smul bound hL.aestronglyMeasurable (Eventually.of_forall hbound)
  have hY : Integrable Y (prior G _) := weighted_integrable T hi F hF
  have hYeq (b) : w b • (inD).conditioned inClock F b = Y b := conditional_times T X.makes.wilson hi F b
  have ha : Staircase.projection M g (S:=op) V s = Z⁻¹ * (op).push β (fun b => w b*L b) V := by
    rw [projection_history track lo hi T M g inj s V]
    unfold source_path_moment
    rw [vacuum_eq T X.makes.wilson hi,vacuum_eq T X.makes.wilson hi.le,div_eq_inv_mul]
    rfl
  have hb : (outD).conditioned outClock F V = Z⁻¹ • (op).push β Y V := by
    rw [Descent.conditioned,vacuum_eq T X.makes.wilson hi.le,weighted_step T F hi]
  let J := Complex.ofRealCLM
  have hpush : J ((op).push β (fun b => w b*L b) V) = (op).push β (fun b => J (w b*L b)) V := by
    unfold StepData.push
    exact (J.integral_comp_comm (StepData.push_slice (A.levels.transition_mass m n β) V _ hmass)).symm.trans
      (integral_congr_ae (Eventually.of_forall fun b=> J.map_smul _ _))
  have hc : ((Z⁻¹ * (op).push β (fun b=>w b*L b) V:ℝ):ℂ) = Z⁻¹ • (op).push β (fun b=>J (w b*L b)) V :=
    (J.map_smul Z⁻¹ ((op).push β (fun b=>w b*L b) V)).trans (congrArg (Z⁻¹ • ·) hpush)
  rw [ha,hb,hc,← smul_sub]
  unfold conditionalPush
  change Z⁻¹ • (_-_) = Z⁻¹ • _
  apply congrArg (Z⁻¹ • ·)
  unfold StepData.push
  refine (integral_sub (StepData.push_slice (A.levels.transition_mass m n β) V _ (J.integrable_comp hmass))
    (StepData.push_slice (A.levels.transition_mass m n β) V _ hY)).symm.trans ?_
  apply integral_congr_ae
  filter_upwards with b
  change _ • J (w b*L b) - _ • Y b = _ • (w b • (J (L b) - (inD).conditioned inClock F b))
  rw [←hYeq b,smul_sub,smul_sub]
  exact congrArg (· - _) ((congrArg ((op).density β b V • ·) (J.map_smul (w b) (L b))))

include track lo in
theorem complex_source_bound (inj : Injective fun i => (M i).turn) (s : Finset ι)
    (F : Config G (X.family.side N n) → ℂ) (hF : Continuous F) {C : ℝ}
    (h : ∀ b, ‖(leafProduct M g s b : ℂ) - (inD).conditioned inClock F b‖ ≤ C)
    (V : Config G (X.family.side m n)) :
    ‖(Staircase.projection M g (S:=op) V s : ℂ) - (outD).conditioned outClock F V‖ ≤ C := by
  rw [complex_source_cell track lo hi T M g inj s F hF V]
  exact conditionalPush_bound X.family.path X.makes.wilson N n m hi _ C h V
end YM.Integration.FVA1Physical.Marked
