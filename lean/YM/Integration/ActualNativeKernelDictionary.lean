import YM.Integration.ActualKernelIdentification
import YM.RG08.Supplies.Caps
import YM.RG08.Prism.Shore
import YM.Push.FREE_RESOLVENT.Test

/-!
# Original-Run Gaussian dictionary on the native forest

The covariance is compressed to the literal free tree coordinates, with no
volume factor. The stationary derivative is the native RootField action
minus the copied coarse field. The native finite-period matrices and the
selected formal kernel use the same original Run, clip, path and period.

The canonical forest is explicit. ActualNativeForest separately transports
the same selected model's positive-order ground from its original forest.
This module supplies identities, not a new price or Horizon equality.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualNativeKernelDictionary
open Function Filter Lattice Wilson RG Precision Tree Exterior Matrix
open Stationary RG08 RG08.Line RG08.Cell RG08.Supplies
open Comparison.RG02 PhysicalNext.Repeat.Legato
open scoped Topology ContDiff Classical BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f}

private theorem colour_matrix {j k : ℕ}
    (M : Matrix (Body j c) (Body k f) ℝ) :
    patron G M = FreeResolvent.tensor G M := by
  ext i l
  exact RG08.Line.patron_cell G M (i.1, i.2.1) (l.1, l.2.1)
    i.2.2 l.2.2

private theorem iris_insertion (F : Forest S.ratio) :
    Prism.iris G S F =
      FreeResolvent.insertion (FreeResolvent.plant (G := G) F) := by
  ext i j
  change (if i = FreeResolvent.plant F j then 1 else 0) =
    (if FreeResolvent.plant F j = i then 1 else 0)
  simp only [eq_comm]

private theorem hessian_inverse {B : Bed} {p : Clip} {P : PathData G}
    (F : Forest S.ratio) (t : S.Choices)
    (hP : Bid.Prismatic F p P) (hB : Bid.Comptroller F B p P)
    {Γ : Matrix (Lines G f 1) (Lines G f 1) ℝ}
    (hΓ : Prism.Given F B Γ) :
    (hessian F t p P 0 0)⁻¹ =
      Γ.submatrix (FreeResolvent.plant F) (FreeResolvent.plant F) := by
  have hline : linePrecision G S B =
      FreeResolvent.fullMatrix G S B.metric := colour_matrix _
  have he : hessian F t p P 0 0 =
      (Prism.grace G S F B B).inside := by
    rw [FreeResolvent.Tests.checked_loop F B t p P hP hB]
    change FreeResolvent.treeMatrix G S F B.metric =
      (Prism.iris G S F).transpose *
        (Prism.grace G S F B B).total * Prism.iris G S F
    rw [Prism.totaled, iris_insertion F, hline,
      FreeResolvent.insertion.compress, FreeResolvent.treeMatrix]
  have hi :
      ((Prism.iris G S F).transpose * Γ * Prism.iris G S F) *
        (Prism.grace G S F B B).inside = 1 :=
    Prism.installed G S F B B hΓ
  rw [iris_insertion F, FreeResolvent.insertion.compress] at hi
  rw [he]
  exact Matrix.inv_eq_left_inv hi

private theorem warm_on_step {B : Bed} {σ price : ℝ}
    (h : Warm G S.kernel S.patch B σ price) :
    Prism.Given (green S) B (NativeLine S G B) := by
  cases S with
  | mk P K hs =>
    have hf : f = c * P.L := Subtype.ext hs
    subst f
    exact ⟨(h.invert c).1, (h.invert c).2.1, (h.invert c).2.2⟩

private theorem warm_from_horizon {a : Levels G} {H : Horizon a}
    {Q : MapPrices} (hH : H.Suffices Q) (N m : ℕ) (hm : m < N) :
    Warm G a.clock.kernel (Supplies.stone a m) (H.H N (m + 1))
      (PlanCurve G a.clock.kernel Q (a.clock.J (m + 1)))
      (planSupply G a.clock.kernel Q (a.clock.J (m + 1)) (a.S.block m)) :=
  (planSupply_spec G a.clock.kernel Q _).2 _
    (a.blocks m 0).branches rfl _ (hH.rows N (m + 1) hm).2.1 _ _
    (fun n => hH.all N (m + 1) hm n)

variable (R0 : Run G) (Y : Bulk.Chain R0.family.path)
    (N period m : ℕ) (hm : m < N)

local notation "a₀" => R0.family.path.levels
local notation "S₀" => R0.family.path.levels.clock.op m period
local notation "B₀" => R0.alloy.B.M.H N (m + 1)
local notation "F₀" => green S₀

include hm in
private theorem actual_inverse :
    Prism.Given F₀ B₀ (NativeLine S₀ G B₀) :=
  warm_on_step (S := S₀) (warm_from_horizon R0.alloy.B.plan N m hm)

include hm in
/-- Exact native finite-period matrices of the original covariance/predictor. -/
theorem actual_matrices :
    Pert.Bulk.Matches
      (Cell.sliced (Supplies.stone a₀ m) (a₀).clock.kernel G B₀)
      (NativeLine S₀ G B₀) ∧
    Pert.Bulk.Matches
      (Cell.plotted (Supplies.stone a₀ m) (a₀).clock.kernel G B₀)
      (Cell.RootField (a₀).clock.kernel G S₀ B₀) := by
  have hw := warm_from_horizon R0.alloy.B.plan N m hm
  have hs := plan_hr G (a₀).clock.kernel R0.metals.K ((a₀).clock.J (m + 1))
  exact Cell.viewed hw hs.1.le hs.2.1 (S₀).sizes

/-- The selected inverse Hessian is the free-coordinate native covariance. -/
theorem actual_covariance (t : (S₀).Choices) :
    (Y.step N m period hm).covariance F₀ t =
      (NativeLine S₀ G B₀).submatrix
        (FreeResolvent.plant F₀) (FreeResolvent.plant F₀) := by
  have hh := (CommonConstruction.runAlong R0).home F₀ hm
  have hp : Bid.Prismatic F₀ ((a₀).params (m + 1)).clip
      (R0.family.path.rep N period (m + 1)).path :=
    fun u => ((hh.2.1).2.2 u).1
  rw [ActualKernelIdentification.covariance_path R0 Y N period m hm F₀ t,
    ← CommonConstruction.runAlong_actual_path R0 N (m + 1) period hm]
  exact hessian_inverse F₀ t hp hh.2.2.1
    (actual_inverse R0 N period m hm)

/-- Keep the actual copied coarse field in the stationary chart derivative. -/
theorem actual_stationary (t : (S₀).Choices)
    (x : fieldDir G ((a₀).S.side m period) 1)
    (i : (F₀).Free) (color : G.ColorIndex) :
    (fderiv ℝ ((Y.step N m period hm).b F₀) 0 x) i color =
      (Cell.RootField (a₀).clock.kernel G S₀ B₀ *ᵥ
        FreeResolvent.flatten x) (FreeResolvent.plant F₀ (i, color)) -
      (linearCopy (S₀).ratio (collect G x)) i.val color := by
  have hh := (CommonConstruction.runAlong R0).home F₀ hm
  have hs :
      fderiv ℝ ((CommonConstruction.runAlong R0).V.stationary N m period F₀)
        0 x =
      relative F₀ (Bloch.installed (S₀).ratio
        (R0.alloy.B.M.towers N m).A0) x :=
    (Push.side _ (hh.2.1.2.1.differentiableAt (by simp)) x).unique
      (hh.2.2.2.2.1 x)
  have hr :
      Cell.RootField (a₀).clock.kernel G S₀ B₀ =
      patron G (extracted S₀ F₀
        (Bloch.installed (S₀).ratio (R0.alloy.B.M.towers N m).A0)) :=
    Cell.tree_station (a₀).clock.kernel G rfl F₀ _
      (actual_inverse R0 N period m hm).square
      (R0.alloy.B.plan.crossings N m period hm).trial
  rw [ActualKernelIdentification.stationary_fderiv R0 Y N period m hm F₀ t,
    hs, hr]
  exact congrArg (fun v =>
      v - (linearCopy (S₀).ratio (collect G x)) i.val color)
    (RG08.Line.painted G
      (extracted S₀ F₀
        (Bloch.installed (S₀).ratio (R0.alloy.B.M.towers N m).A0))
      (FreeResolvent.flatten x) color
      (i.val.1, coord i.val.2)).symm

end YM.Integration.ActualNativeKernelDictionary
end
