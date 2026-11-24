import YM.Integration.ActualStartupVacuumPackets

/-!
Actual function-level mass data for the unchanged startup album.
All original Nat rows and their supports are retained. The true cover cost
is explicit; no derivative estimate or admitted-cap purchase is asserted.
The original leading-curvature rank is exactly the stored power plus two.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualStartupPacketInput

open Lattice Wilson RG
open WilsonStartup WilsonStartup.Start WilsonStartup.IterationFour
open ActualStartupVacuumPackets
open scoped Classical BigOperators

variable {G : Gauge} {n : Side}

def rowMass (p : BudgetPoint) (u : ℝ) (k : ℕ) (o : Site n) (i : ℕ) : ℝ :=
  if ((slate G n u (terms G k)).labels i).site = o then
    p.mass ((slate G n u (terms G k)).labels i).support
      (rowAtom G n u k i).magnitude
  else 0

def layerMassCost (G : Gauge) (p : BudgetPoint) (u width : ℝ) (k : ℕ) : ℝ :=
  Real.exp (p.supportExponent * (5 ^ 4 : ℕ)) * layerCost G u width k

def albumMassCost (G : Gauge) (p : BudgetPoint) (S : Stage) (r : ℕ)
    (width : ℝ) : ℝ :=
  Real.exp (p.supportExponent * (5 ^ 4 : ℕ)) * finiteCost G S r width

private theorem budget_dominated {f g : ℕ → ℝ} {b c : ℝ}
    (hf : SumBudget f b) (hc : 0 ≤ c)
    (hg : ∀ i, 0 ≤ g i) (hle : ∀ i, g i ≤ c * f i) :
    SumBudget g (c * b) := by
  have hcf : Summable (fun i => c * f i) := hf.2.1.mul_left c
  have hsum : Summable g := Summable.of_nonneg_of_le hg hle hcf
  refine ⟨hg, hsum, ?_⟩
  calc
    ∑' i, g i ≤ ∑' i, c * f i := hsum.tsum_le_tsum hle hcf
    _ = c * ∑' i, f i := tsum_mul_left
    _ ≤ c * b := mul_le_mul_of_nonneg_left hf.2.2 hc

/-- The original cover multiplier is bounded on nonzero rows; zero rows keep
their arbitrary original support and contribute exactly zero. -/
theorem row_mass_le (p : BudgetPoint) (u : ℝ) (k : ℕ) (i : ℕ) :
    p.mass ((slate G n u (terms G k)).labels i).support
        (rowAtom G n u k i).magnitude ≤
      Real.exp (p.supportExponent * (5 ^ 4 : ℕ)) *
        (rowAtom G n u k i).magnitude := by
  by_cases hz : (rowAtom G n u k i).magnitude = 0
  · simp only [BudgetPoint.mass, hz, mul_zero, le_refl]
  have hm : 0 ≤ (rowAtom G n u k i).magnitude := by
    unfold Atom.magnitude
    positivity
  have hcover : (coverNumber p.B
      ((slate G n u (terms G k)).labels i).support : ℝ) ≤ (5 ^ 4 : ℕ) := by
    exact_mod_cast rowAtom_cover p u k i hz
  exact mul_le_mul_of_nonneg_right
    (Real.exp_monotone (mul_le_mul_of_nonneg_left hcover p.exponent_pos.le)) hm

/-- A genuine per-root absolute sum bound, with the complete cover multiplier.
Nonnegative width pays the passage from magnitude to the original path budget. -/
theorem row_mass_budget (p : BudgetPoint) (u width : ℝ) (hw : 0 ≤ width)
    (k : ℕ) (o : Site n) :
    SumBudget (rowMass (G := G) p u k o) (layerMassCost G p u width k) := by
  let f (i : ℕ) :=
    if ((slate G n u (terms G k)).labels i).site = o then
      (rowAtom G n u k i).magnitude *
        Real.exp (width * (rowAtom G n u k i).length)
    else 0
  have hf : SumBudget f (layerCost G u width k) :=
    rowAtom_exponential u width hw k o
  apply budget_dominated hf (Real.exp_pos _).le
  · intro i
    unfold rowMass
    split
    · unfold BudgetPoint.mass Atom.magnitude
      positivity
    · exact le_rfl
  · intro i
    by_cases hi : ((slate G n u (terms G k)).labels i).site = o
    · simp only [rowMass, f, hi, ↓reduceIte]
      have hm : 0 ≤ (rowAtom G n u k i).magnitude := by
        unfold Atom.magnitude
        positivity
      exact (row_mass_le p u k i).trans
        (mul_le_mul_of_nonneg_left
          (le_mul_of_one_le_right hm
            (Real.one_le_exp (mul_nonneg hw (Nat.cast_nonneg _))))
          (Real.exp_pos _).le)
    · simp only [rowMass, f, hi, ↓reduceIte, mul_zero, le_refl]

/-- The same estimate on each actual original album layer, with no substituted
row enumeration or replacement vacuum representation. -/
theorem album_row_mass_budget (p : BudgetPoint) (S : Stage) (r : ℕ)
    (width : ℝ) (hw : 0 ≤ width)
    (a : YM.IterationFour.Vacuum.Piece G n) (ha : a ∈ album G n p S r)
    (o : Site n) :
    SumBudget
      (fun i => if (a.packet.labels i).site = o then
        p.mass (a.packet.labels i).support
          (rowAtom G n (Start.weight S.clip 1) a.rank i).magnitude else 0)
      (layerMassCost G p (Start.weight S.clip 1) width a.rank) := by
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha
  exact row_mass_budget p (Start.weight S.clip 1) width hw (5 + j) o

/-- The complete finite layer price retains its explicit original cover factor. -/
theorem album_mass_cost (p : BudgetPoint) (S : Stage) (r : ℕ) (width : ℝ) :
    ((album G n p S r).map
      (fun a => layerMassCost G p (Start.weight S.clip 1) width a.rank)).sum =
      albumMassCost G p S r width := by
  have hs (l : List ℕ) :
      (l.map (fun j => Real.exp (p.supportExponent * (5 ^ 4 : ℕ)) *
        layerCost G (Start.weight S.clip 1) width (5 + j))).sum =
      Real.exp (p.supportExponent * (5 ^ 4 : ℕ)) *
        (l.map (fun j => layerCost G (Start.weight S.clip 1) width (5 + j))).sum := by
    induction l with
    | nil => simp only [List.map_nil, List.sum_nil, mul_zero]
    | cons j l ih =>
        simp only [List.map_cons, List.sum_cons, ih, mul_add]
  rw [album, List.map_map]
  change ((List.range (r - 2)).map
      (fun j => Real.exp (p.supportExponent * (5 ^ 4 : ℕ)) *
        layerCost G (Start.weight S.clip 1) width (5 + j))).sum =
    Real.exp (p.supportExponent * (5 ^ 4 : ℕ)) *
      ((List.range (r - 2)).map
        (fun j => layerCost G (Start.weight S.clip 1) width (5 + j))).sum
  exact hs (List.range (r - 2))

/-- Original power and leading-curvature rank, for every layer and hence for
every one of its retained active or padded zero rows. -/
theorem album_rank_power (p : BudgetPoint) (S : Stage) (r : ℕ)
    (a : YM.IterationFour.Vacuum.Piece G n) (ha : a ∈ album G n p S r) :
    a.rank = a.power + 2 := by
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha
  change 5 + j = (3 + j) + 2
  omega

end YM.Integration.ActualStartupPacketInput
end
