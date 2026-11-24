import YM.Integration.FVA1Physical.Wilson.MovingCoercive
import YM.FVA2.OffsetClock

/-! A finite clock-dependent physical account decomposes into the actual
bare action and the charges of its individual conditional kernels. This
decomposition also controls its Taylor jets on a nonflat retained ray. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Set Lattice RG YM.Wilson Tree RGComparison.Core16 RGComparison.Core16.Descent
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Radial
open FVA2.CityHistory FVA2.RayScatter FormalOPE.RG10
open scoped Classical Topology ContDiff
variable {G : Gauge} {n c : Side} (d : Descent n c)

private theorem account_congr {b e : ℕ → ℝ} (h : ∀ i ≤ d.depth, b i = e i)
    (t : d.Tags) (V : Config G c) (x : Fields G d) :
    d.account b t V x = d.account e t V x := by
  induction d generalizing b e with
  | nil => exact congrArg (· * _) (h 0 le_rfl)
  | push S T d ih =>
    rw [account,account,h 1 (Nat.succ_le_succ (Nat.zero_le _)),ih
      (b:=upβ b) (e:=upβ e) (fun i hi => h (i+1) (Nat.succ_le_succ hi))]

private theorem account_sum (s : Finset ℕ) (w : ℕ → ℝ) (v : ℕ → ℕ → ℝ)
    (t : d.Tags) (V : Config G c) (x : Fields G d) :
    d.account (fun i => ∑ j ∈ s, w j * v j i) t V x =
      ∑ j ∈ s, w j * d.account (v j) t V x := by
  induction d generalizing v with
  | nil =>
    simp only [account,Finset.sum_mul,mul_assoc]
  | push S T d ih =>
    simp only [account,mul_add,Finset.sum_add_distrib,Finset.sum_mul,mul_assoc]
    congr 1
    exact ih (fun j => upβ (v j)) t.2 _ _

def clockAtom (j i : ℕ) : ℝ := if j = i then 1 else 0

theorem split_account (b : ℕ → ℝ) (t : d.Tags) (V : Config G c) (x : Fields G d) :
    d.account b t V x = ∑ j ∈ Finset.range (d.depth+1), b j * d.account (clockAtom j) t V x := by
  rw [← account_sum]
  apply account_congr
  intro i hi
  simp [clockAtom,mul_ite,Finset.mem_range.mpr (Nat.lt_succ_of_le hi)]

variable (t : d.Tags) (u : Pins G c)

def atomAlong (j : ℕ) : ℝ × Coordinates G d → ℝ := consume d t (clockAtom j) ∘ recover u

theorem atom_hot (h : d.OK G) (j : ℕ) : ContDiffAt ℝ ω (atomAlong d t u j) 0 :=
  ((recover (E:=Coordinates G d) u).map_zero.symm ▸ thermal d t h (clockAtom j)).comp
    _ (recover (E:=Coordinates G d) u).contDiff.contDiffAt

theorem atom_stationary (h : d.OK G) (j : ℕ) : Stationary (atomAlong d t u j) := by
  apply Inherit.stable (atom_hot d t u h j)
  · simp [atomAlong,thermal_zero d t h]
  intro y
  apply account_nonnegative
  intro i _
  simp only [clockAtom]
  split <;> norm_num

def clockPhase (z : ℕ → ℝ → ℝ) (y : ℝ × Coordinates G d) :=
  y.1^2 + ∑ i ∈ Finset.range (d.depth+1), z i y.1 * atomAlong d t u i y

theorem clockPhase_exact (z : ℕ → ℝ → ℝ) (y : ℝ × Coordinates G d) :
    clockPhase d t u z y = y.1^2 + consume d t (fun i => z i y.1) (recover u y) :=
  congrArg (y.1^2 + ·) (split_account d _ t _ _).symm

theorem clockPhase_hot (h : d.OK G) {z : ℕ → ℝ → ℝ}
    (hot : ∀ i ≤ d.depth, ContDiffAt ℝ ω (z i) 0) :
    ContDiffAt ℝ ω (clockPhase d t u z) 0 :=
  (contDiffAt_fst.pow 2).add (ContDiffAt.sum fun i hi =>
    ((hot i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))).comp 0 contDiffAt_fst).mul
      (atom_hot d t u h i))

end YM.Integration.FVA1Physical.Wilson
