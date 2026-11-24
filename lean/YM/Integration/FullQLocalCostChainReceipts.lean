import YM.Integration.FullQLocalCostProfileChain
import YM.Integration.FullQLocalCostSubpower

/-!
Build the finite receipt tree before choosing any post-Run Grant. Every profile
leaf uses its actual width payment on the same Run. The selected output record
keeps that payment, the cost certificate, and its dependent rich Grant together.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FullQLocal.PreRun.CostProfile
open Filter Lattice RG RG.Supply Precision Marker
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Profile
open scoped Topology

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    {hG : G.Simple} {B : Census V} {J : Request V}
    {s : Sheet G} {q : MapPrices} {native : NativeComponentRecipe.Choice s}

theorem Chain.receipts (S : Chain hG B J s q native) (r : ℕ) (R : Run G)
    (hReadout : RG05Preconstruction.ReadoutPurchase R.b)
    (P : ∀ n, WidthPayment R.family (S.allocation r n).input)
    (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m)
    (hcap0 : Tendsto cap atTop (𝓝 0)) (n : ℕ) :
    (S.recipe r n).Receipts R := by
  induction n with
  | zero =>
    rw [S.recipe_initial]
    trivial
  | succ n ih =>
    rw [S.recipe_successor]
    exact Recipe.next_receipts R (S.recipe r n) (S.allocation r n).input
      (S.data r n).purchases.constant.degree (S.stage r n).request.order
      (profile_receipt R (S.allocation r n).input
        (ActualRequestNumericSchedule.selected R hG hReadout
          (S.allocation r n).input (P n) (S.stage r n).request cap hcap hcap0)
        (fun _ => rfl)) ih

theorem Chain.subpower (S : Chain hG B J s q native) (r : ℕ) (R : Run G)
    (hReadout : RG05Preconstruction.ReadoutPurchase R.b)
    (P : ∀ n, WidthPayment R.family (S.allocation r n).input)
    (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m)
    (hcap0 : Tendsto cap atTop (𝓝 0)) (n : ℕ) :
    (S.recipe r n).Subpower
      (ActualRequestNumericSchedule.selected R hG hReadout
        (S.allocation r n).input (P n) (S.stage r n).request cap hcap hcap0) :=
  (S.recipe r n).subpower R hG
    (ActualRequestNumericSchedule.selected R hG hReadout
      (S.allocation r n).input (P n) (S.stage r n).request cap hcap hcap0)
    (S.receipts r R hReadout P cap hcap hcap0 n)

abbrev Chain.Grant (S : Chain hG B J s q native) (r n : ℕ) (R : Run G)
    (hReadout : RG05Preconstruction.ReadoutPurchase R.b)
    (P : WidthPayment R.family (S.allocation r n).input)
    (lengths : ℕ → ℕ) (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m)
    (hcap0 : Tendsto cap atTop (𝓝 0))
    (hsub : (S.recipe r n).Subpower
      (ActualRequestNumericSchedule.selected R hG hReadout
        (S.allocation r n).input P (S.stage r n).request cap hcap hcap0)) :=
  { H : Prescribed.Grant (Gamma := B) (S.stage r n).selected.capacities
      (RunFormalChain.fromRun R) (S.stage r n).request
      ((S.recipe r n).schedule
        (ActualRequestNumericSchedule.selected R hG hReadout
          (S.allocation r n).input P (S.stage r n).request cap hcap hcap0) hsub)
      ((S.data r n).purchases.floor (S.stage r n).request s) lengths
      (S.data r n).purchases.constant ((S.allocation r n).target R.family) //
    RawInherited.Receipt H.original.models.prices
      (S.data r n).purchases.rawDegree (S.data r n).purchases.rawCoefficient }

structure Chain.Selected (S : Chain hG B J s q native) (r n : ℕ) (R : Run G)
    (hReadout : RG05Preconstruction.ReadoutPurchase R.b)
    (lengths : ℕ → ℕ) (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m)
    (hcap0 : Tendsto cap atTop (𝓝 0)) where
  payment : WidthPayment R.family (S.allocation r n).input
  subpower : (S.recipe r n).Subpower
    (ActualRequestNumericSchedule.selected R hG hReadout
      (S.allocation r n).input payment (S.stage r n).request cap hcap hcap0)
  grant : S.Grant r n R hReadout payment lengths cap hcap hcap0 subpower

end YM.Integration.FullQLocal.PreRun.CostProfile
end
