import YM.Integration.ActualRequestNumericSchedule
import YM.Integration.FullQLocalCostEnlargement

set_option autoImplicit false
noncomputable section
namespace YM.Integration.FullQLocal.PreRun.CostProfile
open Filter Lattice RG
open PhysicalNext.Repeat.Legato
open FullQLocal.RenderedStep
open scoped Topology

/-- A finite polynomial expression in actual selected profile costs.
Every profile and every finite shift is fixed before the physical Run. -/
inductive Polynomial where
  | constant (n : ℕ)
  | profile (W : ProfileWidths)
  | add (a b : Polynomial)
  | mul (a b : Polynomial)
  | pow (a : Polynomial) (n : ℕ)
  | shift (a : Polynomial) (k : ℕ)

variable {G : Gauge}

/-- The profile leaf is exactly the admitted cost of the bounded selected
schedule, independent of its request and calibration cap. -/
def Polynomial.eval (C : Family G) : Polynomial → ℕ → ℝ
  | .constant n, _ => n
  | .profile W, m => 2 * ActualRunComponentAdmission.cost C W m
  | .add a b, m => a.eval C m + b.eval C m
  | .mul a b, m => a.eval C m * b.eval C m
  | .pow a n, m => a.eval C m ^ n
  | .shift a k, m => a.eval C (m + k)

theorem Polynomial.eval_nonnegative (C : Family G) (e : Polynomial) (m : ℕ) :
    0 ≤ e.eval C m := by
  induction e generalizing m with
  | constant n => exact Nat.cast_nonneg n
  | profile W =>
    exact mul_nonneg (by norm_num)
      (zero_le_one.trans (ActualRunComponentAdmission.cost_one C W m))
  | add a b ha hb => exact add_nonneg (ha m) (hb m)
  | mul a b ha hb => exact mul_nonneg (ha m) (hb m)
  | pow a n ha => exact pow_nonneg (ha m) n
  | shift a k ha => exact ha (m + k)

variable {V : Type}

/-- The expression uses the actual selected cost, not an independently
constructed price family. -/
theorem Polynomial.profile_selected (W : ProfileWidths) (R : Run G)
    (hG : G.Simple) (hReadout : RG05Preconstruction.ReadoutPurchase R.b)
    (P : WidthPayment R.family W) (J : Request V)
    (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m)
    (hcap0 : Tendsto cap atTop (𝓝 0)) (m : ℕ) :
    (Polynomial.profile W).eval R.family m =
      (ActualRequestNumericSchedule.selected R hG hReadout W P J
        cap hcap hcap0).admittedCost m := rfl

/-- Keep is a literal identity branch. Enlarge adds a preselected finite
polynomial expression to the original admitted cost. -/
inductive Recipe where
  | keep
  | enlarge (extra : Polynomial)

variable {C : Family G} {J : Request V}

def Recipe.cost (e : Recipe) (A : NumericSchedule C J) (m : ℕ) : ℝ :=
  match e with
  | .keep => A.admittedCost m
  | .enlarge extra => A.admittedCost m + extra.eval C m

theorem Recipe.cost_ge (e : Recipe) (A : NumericSchedule C J) (m : ℕ) :
    A.admittedCost m ≤ e.cost A m := by
  cases e with
  | keep => exact le_rfl
  | enlarge extra => exact le_add_of_nonneg_right (extra.eval_nonnegative C m)

/-- This numerical certificate is proved from the actual purchased delays.
It is not part of the analytic full-q conclusion. -/
def Recipe.Subpower (e : Recipe) (A : NumericSchedule C J) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ start : ℕ, ∀ m : ℕ, start ≤ m → ∀ N period : ℕ, m < N →
      e.cost A m ≤ Pert.Asymptotics.regulatorRun C N period (m + 1) ^ (-epsilon)

theorem Recipe.keep_subpower (A : NumericSchedule C J) :
    Recipe.Subpower .keep A := A.cost_subpower

/-- Only the auxiliary admitted cost is enlarged. All physical data and
all requested norms, widths, radii and path rates are unchanged. -/
def Recipe.schedule (e : Recipe) (A : NumericSchedule C J)
    (hsub : e.Subpower A) : NumericSchedule C J := by
  cases e with
  | keep => exact A
  | enlarge extra =>
    exact FullQLocalCostEnlargement.schedule A
      (Recipe.cost (.enlarge extra) A) (Recipe.cost_ge (.enlarge extra) A) hsub

theorem Recipe.schedule_keep (A : NumericSchedule C J)
    (hsub : Recipe.Subpower .keep A) :
    Recipe.schedule .keep A hsub = A := rfl

theorem Recipe.schedule_data (e : Recipe) (A : NumericSchedule C J)
    (hsub : e.Subpower A) :
    (e.schedule A hsub).inputNorm = A.inputNorm ∧
    (e.schedule A hsub).outputNorm = A.outputNorm ∧
    (e.schedule A hsub).inputWidth = A.inputWidth ∧
    (e.schedule A hsub).outputWidth = A.outputWidth ∧
    (e.schedule A hsub).radiusLoss = A.radiusLoss ∧
    (e.schedule A hsub).calibrationCap = A.calibrationCap ∧
    (e.schedule A hsub).pathRate = A.pathRate ∧
    (e.schedule A hsub).admittedCost = e.cost A := by
  cases e <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end YM.Integration.FullQLocal.PreRun.CostProfile
end
