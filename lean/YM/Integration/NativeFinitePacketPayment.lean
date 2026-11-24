import YM.Integration.LocalComparisonPackets

/-! Exact finite accounting for the original marked-packet Paid contract.
All token, test, coupling and path factors remain in the displayed costs.
This proves no uniform estimate as the finite packet family varies. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeFinitePacketPayment
open Function Finset Lattice Wilson RG Marker
open LocalComparison Comparison.Density.RenderM
open scoped Classical BigOperators

variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V]
  {R : Census V} {D : V → ComparisonDensity.Address.Orbit}
  (P : MarkedPackets D G n R) (count : ℕ) (w : V → ℝ) (g width : ℝ)

def charge (i : ℕ) : ℝ :=
  match P.packet i with
  | none => 0
  | some T => Poly.toll w (P.mode i) * ‖(g : ℂ) ^ P.power i‖ *
      T.coin * Real.exp (width * T.fall)

def rootCharge (v : V) (i : ℕ) : ℝ :=
  if v ∈ (P.mode i).val then charge P w g width i else 0

def rootCost (v : V) : ℝ := ∑ i ∈ range count, rootCharge P w g width v i

def totalCost : ℝ := ∑ i ∈ range count, charge P w g width i

variable (p : BudgetPoint)

def coverAt (i : ℕ) : ℕ :=
  match P.packet i with
  | none => 0
  | some T => coverNumber p.B T.plot

def coverOffset : ℕ := (range count).sup (coverAt P p)

private theorem charge_nonneg (hw : ∀ v, 0 < w v)
    (hcoin : ∀ i T, P.packet i = some T → 0 ≤ T.coin) (i : ℕ) :
    0 ≤ charge P w g width i := by
  cases hi : P.packet i with
  | none => simp [charge, hi]
  | some T =>
    simp only [charge, hi]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (Poly.worth hw (P.mode i)).le (norm_nonneg _))
        (hcoin i T hi)) (Real.exp_pos _).le

private theorem rootCharge_nonneg (hw : ∀ v, 0 < w v)
    (hcoin : ∀ i T, P.packet i = some T → 0 ≤ T.coin) (v : V) (i : ℕ) :
    0 ≤ rootCharge P w g width v i := by
  unfold rootCharge
  split_ifs
  · exact charge_nonneg P w g width hw hcoin i
  · exact le_rfl

/-- Exact absolute mass at each original marker root, including the
full coupling power and exponential path bill. -/
theorem root_budget (hfinite : ∀ i, count ≤ i → P.packet i = none)
    (hw : ∀ v, 0 < w v)
    (hcoin : ∀ i T, P.packet i = some T → 0 ≤ T.coin) (v : V) :
    SumBudget (rootCharge P w g width v) (rootCost P count w g width v) := by
  have hs : HasSum (rootCharge P w g width v) (rootCost P count w g width v) := by
    apply hasSum_sum_of_ne_finset_zero (s := range count)
    intro i hi
    have hn : ¬ i < count := by simpa only [mem_range] using hi
    simp [rootCharge, charge, hfinite i (Nat.le_of_not_gt hn)]
  exact ⟨rootCharge_nonneg P w g width hw hcoin v, hs.summable, hs.tsum_eq.le⟩

/-- A common finite budget counts each token once, without multiplying by
the number of marker roots. The sharper rootCost remains available. -/
theorem root_cost_le (hw : ∀ v, 0 < w v)
    (hcoin : ∀ i T, P.packet i = some T → 0 ≤ T.coin) (v : V) :
    rootCost P count w g width v ≤ totalCost P count w g width := by
  apply Finset.sum_le_sum
  intro i _
  unfold rootCharge
  split_ifs
  · exact le_rfl
  · exact charge_nonneg P w g width hw hcoin i

/-- The cover offset is the actual maximum of the finite token plots.
No support is shrunk and no period-independent estimate is asserted. -/
theorem cover_bound (hfinite : ∀ i, count ≤ i → P.packet i = none)
    (i : ℕ) (T : Token G n (fun v => (D v).Mood) (P.rank i))
    (hT : P.packet i = some T) :
    coverNumber p.B T.plot ≤ coverOffset P count p := by
  have hi : i < count := by
    by_contra hn
    rw [hfinite i (Nat.le_of_not_gt hn)] at hT
    cases hT
  have h := Finset.le_sup (f := coverAt P p) (mem_range.mpr hi)
  simpa only [coverOffset, coverAt, hT] using h

/-- The existing structural token receipts produce the literal Paid
record with explicit finite costs. Any chosen positive width is paid;
the actual finite cover offset makes the reserved slope exactly zero. -/
theorem paid (hfinite : ∀ i, count ≤ i → P.packet i = none)
    (address : V → Support n)
    (region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n)
    (hwidth : 0 < width) (hw : ∀ v, 0 < w v)
    (hcoefficient : ∀ i T, P.packet i = some T →
      0 ≤ T.coin ∧ ∀ x : IndependentTests D,
        (∑ j, ‖T.gem j (testInclusion D x)‖) ≤ T.coin)
    (hpaths : ∀ i T, P.packet i = some T → ∀ x : TestSpace D,
      (T.re x).length ≤ T.fall ∧ (T.re x).footprint T.root ⊆ T.plot)
    (haddress : ∀ i T, P.packet i = some T → ∀ v ∈ (P.mode i).val,
      address v ⊆ T.plot)
    (hsymmetry : ∀ i T, P.packet i = some T → ∀ x U (k : G.El),
      T.touch x (fun i => G.adjoint k (U i)) = T.touch x U)
    (hreads : ∀ i T, P.packet i = some T → ∀ j,
      Comparison.Density.Testing.Reads region T.plot (P.mode i).val (T.gem j))
    (hlinear : ∀ i T, P.packet i = some T → ∀ j,
      RG3.Held.Letter ℂ (fun v => (D v).Mood) (P.mode i).val (T.gem j)) :
    P.Paid p address region w g width (totalCost P count w g width)
      (coverOffset P count p) 0 := by
  let hcoin : ∀ i T, P.packet i = some T → 0 ≤ T.coin :=
    fun i T hT => (hcoefficient i T hT).1
  refine {
    width_pos := hwidth
    positive := hw
    coefficient := hcoefficient
    paths := hpaths
    addresses := haddress
    symmetry := hsymmetry
    reads := hreads
    multilinear := hlinear
    roots := ?_
    cover := ?_
    width_reserved := ?_ }
  · intro v
    have h := root_budget P count w g width hfinite hw hcoin v
    exact ⟨h.1, h.2.1, h.2.2.trans (root_cost_le P count w g width hw hcoin v)⟩
  · intro i T hT
    have hn : (coverNumber p.B T.plot : ℝ) ≤ (coverOffset P count p : ℝ) :=
      Nat.cast_le.mpr (cover_bound P count p hfinite i T hT)
    calc
      _ ≤ (p.B : ℝ) * (coverOffset P count p : ℝ) :=
        mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg _)
      _ = _ := by simp [mul_comm]
  · simp only [Nat.cast_zero, mul_zero, zero_div]
    exact div_nonneg hwidth.le (by norm_num)

end YM.Integration.NativeFinitePacketPayment
end
