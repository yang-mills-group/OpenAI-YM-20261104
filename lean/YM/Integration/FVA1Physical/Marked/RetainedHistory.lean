import YM.Integration.FVA1Physical.Marked.LinkPrice
import YM.RGComparison.Core16.Trajectory
import YM.Qlocal.Canopy.Still

/-! The retained denominator and the actual square-free source derivatives
on one physical step, with the incoming density independently reconstructed
from the bare Wilson action through the entire preceding kernel history. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Function Filter Lattice RG Wilson Pressure Tree Precision Push PriceCompiler RG.Supply Input Org
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato AnalyticBridge VerifiedReset Collection
open Progress.DirectedRecipe Height Roof Extra.Iteration Time ThroughLaunch Roost JointLoad RGComparison.Core16
open ConnectedActivityE6 SectorMeasure Extra.Trajectories RG3.Script.Picnic
open AllOrder Transit WheelP Floe Floe.Step.PlanV Qlocal Qlocal.Parabola RGComparison01 RGComparison01.Pledge
open Merge
open scoped BigOperators Classical Topology

variable {G : Gauge} {X : Run G} {z N n k m : ℕ} {path : ℕ → Floe.Layout G} {Γ : ℕ → Pace.Coin}
    {x : (i : ℕ) → Rep G (X.alloy.B.a.S.side i n)}
    (track : Metre X.alloy X.kit X.T path Γ z N n k x) (lo : z ≤ m) (hi : m < N)
    (T : Slices X.family.path.levels n)
local notation "U" => x (m+1)
local notation "p" => X.alloy.B.a.budget m
local notation "size" => (X.alloy.B.a.S.oneStep m n).exact_size
local notation "op" => X.family.path.levels.clock.op m n
local notation "tube" => Pane.orchestra X.alloy N size
local notation "price" => X.alloy.B.kin.alpha N m

include track lo in
/-- Incoming density, measured coupling and outgoing denominator all use the
same finite Wilson history at every field, including flagged fields. -/
theorem bank_history :
    (U).eval = (traversal T hi).vacuum (G:=G) (line X.family.path n (m+1) N) ∧
    (U).beta = X.family.path.β N n (m+1) ∧ (op).push (U).beta (U).eval = (traversal T hi.le).vacuum (G:=G) (line X.family.path n m N) := by
  have row := track.1.walk (m+1) (by omega) hi
  have e : (U).eval = (X.family.path.rep N n (m+1)).eval := row.view
  have b : (U).beta = X.family.path.β N n (m+1) := row.beta
  refine ⟨e.trans (vacuum_eq T X.makes.wilson hi).symm,b,?_⟩
  rw [e,b]
  exact (X.makes.wilson.steps N n m hi).1.symm.trans (vacuum_eq T X.makes.wilson hi.le).symm

variable (H : Opera.Guide X.alloy.B X.kit.shape N m n (x (m+1))) {Ω : ℕ→Prop} {q : ℕ} {e : ℝ}
    (wet : Ports.Wet X.kit (X.alloy.B.a.S.oneStep m n).exact_size H q Ω e)
local notation "addr" => Beam.marquee H p
local notation "low" => Coast.kept_out X.kit size H Ω q
local notation "old" => Coast.inherited X.kit size H Ω
local notation "tail" => Coast.weeded X.kit size H Ω q

include track lo wet in
/-- The retained low bank carries the entire physical forced gas. Its only
multiplicative difference from the prescribed full Wilson denominator is the
explicit signed exponential of the inherited and high-order regular rows. -/
theorem retained_history_density (V : Config G (X.family.side m n)) :
    (traversal T hi.le).vacuum (G:=G) (line X.family.path n m N) V =
      earlyValue addr (tube).down (tube).low p low (U).beta (Song.weighty H Chi.canonical (T m)) price V *
      Real.exp (- ((addr).read old).additive p V - ((addr).read tail).additive p V) := by
  rw [← (bank_history track lo hi T).2.2]
  exact (congrFun (wet.unnorm (T m)) V).trans (wet.restores _ V)

variable {ι : Type} [Fintype ι] (M : ι→Lotus.Leaf (x (m+1))) (g : ι→ℝ)

/-- The independently reconstructed input uses the full bare-action history.
Source functions in this formula are the actual leaf ingredients on the
intermediate field. The denominator is the very same full Wilson history. -/
def source_path_moment (s : Finset ι) (V : Config G (X.family.side m n)) : ℝ :=
    (op).push (X.family.path.β N n (m+1)) (fun b : Config G (X.family.side (m+1) n) => (traversal T hi).vacuum (G:=G) (line X.family.path n (m+1) N) b *
        ((∏ i∈s,g i) * ∏ i∈s,(M i).ingredient b)) V / (traversal T hi.le).vacuum (G:=G) (line X.family.path n m N) V

include track lo in
theorem projection_history (inj : Injective fun i => (M i).turn) (s : Finset ι) (V : Config G (X.family.side m n)) :
    Staircase.projection M g (S:=op) V s = source_path_moment hi T M g s V := by
  obtain ⟨income,β,output⟩ := bank_history track lo hi T
  have tests : Staircase.cardTest M g op s = fun b => (∏ i∈s,g i) * ∏ i∈s,(M i).ingredient b :=
    funext fun b => Canopy.Still.fuse g M b op s inj
  have integrand : (U).eval * Staircase.cardTest M g op s = fun b =>
      (traversal T hi).vacuum (G:=G) (line X.family.path n (m+1) N) b * ((∏ i∈s,g i) * ∏ i∈s,(M i).ingredient b) :=
    funext fun b => congrArg₂ (· * ·) (congrFun income b) (congrFun tests b)
  exact congrArg₂ (· / ·) (congrArg₂ (fun θ (f : Config G (X.family.side (m+1) n)→ℝ) =>
    (op).push θ f V) β integrand) (congrFun output V)

include track lo H in
/-- At arbitrary retained fields, the actual multilinear source variation is
the pinned finite-history moment. No unnormalized numerator, arbitrary
zeroth coefficient or reference flat vacuum is substituted. -/
theorem source_jet_history (regular : Staircase.grows M) (inj : Injective fun i => (M i).turn)
    (s : Finset ι) (V : Config G (X.family.side m n)) :
    Switch.jet (fun a b => (op).push (U).beta (Palette.buy M (Palette.ways g a b) op) V /
        (traversal T hi.le).vacuum (G:=G) (line X.family.path n m N) V) s = source_path_moment hi T M g s V := by
  have normed := bank_history track lo hi T
  rw [← normed.2.2, ← projection_history track lo hi T M g inj s V]
  exact Staircase.in_record (S:=op) (T:=tube) (R:=U) M g H regular s V

end YM.Integration.FVA1Physical.Marked
