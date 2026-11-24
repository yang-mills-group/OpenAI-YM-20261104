import YM.Integration.FullQLocalCostGrowth
import YM.Integration.ActualRunSubpowerShift

/-! Finite polynomial and fixed-shift closure of the actual uniform subpower
predicate. Each profile leaf retains its own numerical receipt on the same Run.
The recipe and its finite exponents precede the tail and every cutoff/period. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FullQLocal.PreRun.CostProfile
open Filter Lattice RG
open PhysicalNext.Repeat.Legato
open FullQLocal.RenderedStep
open scoped Topology

variable {G : Gauge} {V : Type} {J : Request V}

theorem scalar_subpower_of_schedule (R : Run G)
    (A : NumericSchedule R.family J) :
    ActualRunSubpowerShift.Subpower R A.admittedCost := by
  intro epsilon hepsilon
  obtain ⟨start, hstart⟩ := A.cost_subpower epsilon hepsilon
  filter_upwards [eventually_ge_atTop start] with m hm N period hN
  exact hstart m hm N period hN

theorem scalar_subpower_constant (R : Run G) (hG : G.Simple)
    (A : NumericSchedule R.family J) (c : ℝ) :
    ActualRunSubpowerShift.Subpower R (fun _ => c) := by
  intro epsilon hepsilon
  filter_upwards [eventually_cost_ge R hG A c,
    scalar_subpower_of_schedule R A epsilon hepsilon] with m hc hm N period hN
  exact hc.trans (hm N period hN)

theorem scalar_subpower_add (R : Run G) (hG : G.Simple)
    (A : NumericSchedule R.family J) (f g : ℕ → ℝ)
    (hf : ActualRunSubpowerShift.Subpower R f)
    (hg : ActualRunSubpowerShift.Subpower R g) :
    ActualRunSubpowerShift.Subpower R (fun m => f m + g m) := by
  intro epsilon hepsilon
  have hd : 0 < epsilon / 2 := half_pos hepsilon
  filter_upwards [hf (epsilon / 2) hd, hg (epsilon / 2) hd,
    scalar_subpower_constant R hG A 2 (epsilon / 2) hd] with m hfm hgm htwo N period hN
  let u := Pert.Asymptotics.regulatorRun R.family N period (m + 1)
  have hu : 0 < u :=
    IterationFour.Currency.g_pos R.makes N period (m + 1) (by omega)
  have hx : 0 ≤ u ^ (-(epsilon / 2)) := Real.rpow_nonneg hu.le _
  calc
    f m + g m ≤ u ^ (-(epsilon / 2)) + u ^ (-(epsilon / 2)) :=
      add_le_add (hfm N period hN) (hgm N period hN)
    _ = 2 * u ^ (-(epsilon / 2)) := by ring
    _ ≤ u ^ (-(epsilon / 2)) * u ^ (-(epsilon / 2)) :=
      mul_le_mul_of_nonneg_right (htwo N period hN) hx
    _ = u ^ (-epsilon) := by
      rw [← Real.rpow_add hu, show -(epsilon / 2) + -(epsilon / 2) = -epsilon by ring]

theorem scalar_subpower_mul (R : Run G) (f g : ℕ → ℝ)
    (hg0 : ∀ m, 0 ≤ g m)
    (hf : ActualRunSubpowerShift.Subpower R f)
    (hg : ActualRunSubpowerShift.Subpower R g) :
    ActualRunSubpowerShift.Subpower R (fun m => f m * g m) := by
  intro epsilon hepsilon
  have hd : 0 < epsilon / 2 := half_pos hepsilon
  filter_upwards [hf (epsilon / 2) hd, hg (epsilon / 2) hd] with m hfm hgm N period hN
  let u := Pert.Asymptotics.regulatorRun R.family N period (m + 1)
  have hu : 0 < u :=
    IterationFour.Currency.g_pos R.makes N period (m + 1) (by omega)
  calc
    f m * g m ≤ u ^ (-(epsilon / 2)) * u ^ (-(epsilon / 2)) :=
      mul_le_mul (hfm N period hN) (hgm N period hN)
        (hg0 m) (Real.rpow_nonneg hu.le _)
    _ = u ^ (-epsilon) := by
      rw [← Real.rpow_add hu, show -(epsilon / 2) + -(epsilon / 2) = -epsilon by ring]

theorem scalar_subpower_pow (R : Run G) (hG : G.Simple)
    (A : NumericSchedule R.family J) (f : ℕ → ℝ)
    (hf0 : ∀ m, 0 ≤ f m) (hf : ActualRunSubpowerShift.Subpower R f) (n : ℕ) :
    ActualRunSubpowerShift.Subpower R (fun m => f m ^ n) := by
  induction n with
  | zero =>
    simpa only [pow_zero] using scalar_subpower_constant R hG A 1
  | succ n ih =>
    simpa only [pow_succ] using scalar_subpower_mul R (fun m => f m ^ n) f
      hf0 ih hf

/-- Only actual profile leaves need receipts; all other operations are finite
scalar algebra. These receipts share the same original physical Run. -/
def Polynomial.Receipts (R : Run G) : Polynomial → Prop
  | .constant _ => True
  | .profile W => ActualRunSubpowerShift.Subpower R
      (fun m => 2 * ActualRunComponentAdmission.cost R.family W m)
  | .add a b => a.Receipts R ∧ b.Receipts R
  | .mul a b => a.Receipts R ∧ b.Receipts R
  | .pow a _ => a.Receipts R
  | .shift a _ => a.Receipts R

theorem profile_receipt (R : Run G) (W : ProfileWidths)
    (A : NumericSchedule R.family J)
    (hbase : ∀ m, 2 * ActualRunComponentAdmission.cost R.family W m = A.admittedCost m) :
    (Polynomial.profile W).Receipts R := by
  intro epsilon hepsilon
  filter_upwards [scalar_subpower_of_schedule R A epsilon hepsilon] with m hm N period hN
  rw [hbase]
  exact hm N period hN

theorem Polynomial.subpower (R : Run G) (hG : G.Simple)
    (A : NumericSchedule R.family J) (e : Polynomial) :
    e.Receipts R → ActualRunSubpowerShift.Subpower R (e.eval R.family) := by
  induction e with
  | constant n =>
    intro _
    exact scalar_subpower_constant R hG A (n : ℝ)
  | profile W =>
    intro h
    exact h
  | add a b ha hb =>
    intro h
    exact scalar_subpower_add R hG A (a.eval R.family) (b.eval R.family)
      (ha h.1) (hb h.2)
  | mul a b ha hb =>
    intro h
    exact scalar_subpower_mul R (a.eval R.family) (b.eval R.family)
      (b.eval_nonnegative R.family) (ha h.1) (hb h.2)
  | pow a n ha =>
    intro h
    exact scalar_subpower_pow R hG A (a.eval R.family)
      (a.eval_nonnegative R.family) (ha h) n
  | shift a k ha =>
    intro h
    exact ActualRunSubpowerShift.fixed_shift R hG (a.eval R.family)
      (a.eval_nonnegative R.family) (ha h) k

def Recipe.Receipts (R : Run G) : Recipe → Prop
  | .keep => True
  | .enlarge extra => extra.Receipts R

theorem Recipe.subpower (R : Run G) (hG : G.Simple)
    (A : NumericSchedule R.family J) (e : Recipe) (he : e.Receipts R) :
    e.Subpower A := by
  cases e with
  | keep => exact Recipe.keep_subpower A
  | enlarge extra =>
    intro epsilon hepsilon
    exact eventually_atTop.1
      (scalar_subpower_add R hG A A.admittedCost (extra.eval R.family)
        (scalar_subpower_of_schedule R A) (extra.subpower R hG A he) epsilon hepsilon)

theorem Recipe.total_receipts (R : Run G) (e : Recipe) (W : ProfileWidths)
    (hW : (Polynomial.profile W).Receipts R) (he : e.Receipts R) :
    (e.total W).Receipts R := by
  cases e with
  | keep => exact hW
  | enlarge extra => exact ⟨hW, he⟩

theorem Recipe.next_receipts (R : Run G) (e : Recipe) (W : ProfileWidths)
    (degree order : ℕ) (hW : (Polynomial.profile W).Receipts R)
    (he : e.Receipts R) :
    (e.next W degree order).Receipts R :=
  ⟨trivial, ⟨trivial, e.total_receipts R W hW he⟩⟩

theorem Recipe.next_subpower (R : Run G) (hG : G.Simple)
    (A : NumericSchedule R.family J) (e : Recipe) (W : ProfileWidths)
    (degree order : ℕ) (hW : (Polynomial.profile W).Receipts R)
    (he : e.Receipts R) :
    (e.next W degree order).Subpower A :=
  (e.next W degree order).subpower R hG A (e.next_receipts R W degree order hW he)

end YM.Integration.FullQLocal.PreRun.CostProfile
end
