import YM.Integration.RunFormalChain
import YM.Integration.ActualKernelIdentification
import YM.UVExt.DeliveredK
import YM.WilsonCoeffUV.Flat.Mean

/-! Put the actual finite RG02 Gaussian and its affine background into the
coordinates of the original periodic Wilson heat, for the same prescribed
Run, period, forest and tag. The reference heat uses its original analytic
free form. No equality of chosen beds or full tower predictions is an input. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalMarkedHeatCovariance
open Function Lattice Laurent Wilson RG RG.Supply Precision Tree Exterior Matrix Bloch
open PhysicalNext.Repeat.Legato Comparison.RG02 FreeResolvent WilsonCoeffUV
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} (R : Run G) (N m p : ℕ) (hm : m < N)
local notation "a" => R.family.path.levels
set_option quotPrecheck false in
local notation "op₀" => (a).clock.op m p
local notation "B" => R.alloy.B.M.H N (m+1)
local notation "Y" => RunFormalChain.fromRun R
set_option quotPrecheck false in
local notation "native" => (Y).step N m p hm
local notation "fine" => freeForms (a) N (m+1)
local notation "coarse" => freeForms (a) N m
variable (F : Forest (R.family.path.levels.clock.op m p).ratio)
  (t : (R.family.path.levels.clock.op m p).Choices)

private theorem same_matrix {c f : Side} (op : StepData c f) (tree : Forest op.ratio)
    {U W : FaceRow} (agree : Precision.K (U.acts f)=Precision.K (W.acts f)) :
    treeMatrix G op tree U=treeMatrix G op tree W := by
  unfold treeMatrix fullMatrix baseMatrix
  rw [agree]

private theorem same_inputs {c f : Side} (op : StepData c f) (w : Matrix (Body 1 f) (Body 1 c) ℝ)
    {u₀ u₁ : Matrix (Body 2 f) (Body 2 f) ℝ} {v₀ v₁ : Matrix (Body 2 c) (Body 2 c) ℝ}
    (fineEq : Precision.K u₀=Precision.K u₁) (coarseEq : Precision.K v₀=Precision.K v₁)
    (given : Inputs op w u₀ v₀) : Inputs op w u₁ v₁ := by
  constructor
  · rw [←fineEq,←coarseEq]
    exact given.primal
  · rw [←coarseEq]
    exact given.dual

include hm F t in
theorem precision :
    hessian (S:=R.family.path.levels.clock.op m p) (G:=G) F t (R.family.path.rep N p (m+1)).clip
      (R.family.path.rep N p (m+1)).path 0 0 = treeMatrix G (op₀) F (fine) := by
  have home := (CommonConstruction.runAlong R).home (N:=N) (m:=m) (p:=p) F hm
  have hP : Bid.Prismatic (S:=(op₀)) (G:=G) F ((a).params (m+1)).clip (R.family.path.rep N p (m+1)).path :=
    fun i => (home.2.1.2.2 i).1
  rw [(Y).clips N p (m+1) hm]
  exact (FreeResolvent.Tests.checked_loop (S:=(op₀)) (G:=G) F (B) t _ _ hP home.2.2.1).trans
    (same_matrix (G:=G) (op₀) F (UVExt.horizon_exact (N:=N) (m:=m+1) (p:=p)
      R.alloy.B.M R.alloy.B.plan (Nat.succ_le_of_lt hm)))

/-- All genuine independent free coordinates, including every off-diagonal
contraction and diagonal variance. -/
theorem activeCovariance :
    (native).covariance F t = treeInverse G (op₀) F (fine) 0 := by
  unfold Bulk.Kernel.covariance treeInverse FreeResolvent.resolve
  rw [precision R N m p hm F t, zero_smul, add_zero]

/-- The cover periodic heat matrix is exactly the extension of the original
inverse to the full fine-bond coordinates on this actual forest slice. -/
theorem ambientCovariance :
    insertion (plant (G:=G) F) * (native).covariance F t * reduce G (op₀) F =
      FreeResolvent.covariance G (op₀) F (fine) := by
  rw [activeCovariance R N m p hm F t]
  rfl

set_option quotPrecheck false in
local notation "M₀" => Bloch.installed (op₀).ratio (R.alloy.B.M.towers N m).A0
set_option quotPrecheck false in
local notation "M₁" => Bloch.installed (op₀).ratio (predictionA (a) N m)

def copyCharge (x : fieldDir G ((a).S.side m p) 1) : Precision.Key F G → ℝ :=
  fun i => linearCopy (op₀).ratio (collect G x) i.1.val i.2

private theorem read_relative {c f : Side} (op : StepData c f) (tree : Forest op.ratio)
    (M : Matrix (Body 1 f) (Body 1 c) ℝ) (x : fieldDir G c 1) :
    active tree (relative (S:=op) (G:=G) tree M x) =
      reduce G op tree *ᵥ (tensor G (extracted op tree M) *ᵥ flatten x) -
        (fun i : Key tree G=>linearCopy op.ratio (collect G x) i.1.val i.2) := by
  rw [reduce_actual]
  funext i
  change _ = (component ((tensor G _ *ᵥ _) : Vec G _ 1) i.2) (i.1.val.1,coord i.1.val.2) - _
  rw [component_mul]
  rfl

include hm t in
/-- Both genuine conditional predictions solve the same free Euler equation
on the actual forest. Their components in all fine Lie colours agree. -/
theorem affineMatrix : tensor G (extracted (op₀) F (M₀)) = tensor G (extracted (op₀) F (M₁)) := by
  have hH := UVExt.horizon_exact (N:=N) (m:=m+1) (p:=p) R.alloy.B.M R.alloy.B.plan (Nat.succ_le_of_lt hm)
  have hL := UVExt.horizon_exact (N:=N) (m:=m) (p:=p) R.alloy.B.M R.alloy.B.plan hm.le
  have nativeInput : Inputs (op₀) (M₀) ((fine).acts ((a).S.side (m+1) p)) ((coarse).acts ((a).S.side m p)) :=
    same_inputs (op₀) (M₀) hH hL (R.alloy.B.plan.crossings N m p hm).trial
  have originalInput : Inputs (op₀) (M₁) ((fine).acts _) ((coarse).acts _) :=
    horizon_step (a) m N hm _ _ (op₀).sizes
  have pos := (native).hessian_pos F t
  rw [precision R N m p hm F t] at pos
  have unit := (isUnit_iff_ne_zero.mpr pos.det_pos.ne')
  exact (mean_map G (op₀) F (fine) (coarse) (M₀) nativeInput unit).symm.trans
    (mean_map G (op₀) F (fine) (coarse) (M₁) originalInput unit)

include t in
/-- The coarse-field argument of every original source or quiet vertex,
including its required copy subtraction, in the independent heat coordinates. -/
theorem stationary (x : fieldDir G ((a).S.side m p) 1) :
    active F (fderiv ℝ ((native).b F) 0 x) =
      reduce G (op₀) F *ᵥ (tensor G (extracted (op₀) F (M₁)) *ᵥ flatten x) -
        copyCharge R m p F x := by
  have home := (CommonConstruction.runAlong R).home F hm
  have hs : fderiv ℝ ((CommonConstruction.runAlong R).V.stationary N m p F) 0 x = relative (S:=(op₀)) (G:=G) F (M₀) x :=
    (Push.side _ (home.2.1.2.1.differentiableAt (by simp)) x).unique (home.2.2.2.2.1 x)
  rw [ActualKernelIdentification.stationary_fderiv R (Y) N p m hm F t, hs]
  have hx := read_relative (G:=G) (op₀) F (M₀) x
  rwa [affineMatrix R N m p hm F t] at hx

end YM.Integration.OriginalMarkedHeatCovariance
end
