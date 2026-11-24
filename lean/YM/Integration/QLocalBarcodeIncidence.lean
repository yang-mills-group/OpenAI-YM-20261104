import YM.Integration.QLocalPhysicalBirthInvoice

/-! Grouping all original compulsory activities by their true native barcode
preserves the full weighted site bill, including an infinite old label fiber. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalBarcodeIncidence
open Function Finset Lattice Wilson RG Marker FVA1
open Extra.Histories Extra.Trajectories PhysicalNext.Repeat.Legato
open MergeProof MergeProof.Ribbon Packets Push.GridApprox.Nil Push.AbsoluteSums
open QLocalPhysicalBirthInvoice
open scoped BigOperators Classical

variable {G : Gauge} {n : Side} (p : BudgetPoint) (A : Activities G n)

/-- At each site, summing the original weighted compulsory tolls over barcode
fibers leaves their total unchanged. -/
theorem grouped (b : ℕ → ℝ) (hb : ∀ i, 0 ≤ b i) {c : ℝ}
    (h : ∀ x : Site n, SumBudget (fun i => if x ∈ (A.forced i).support then
      p.mass (A.forced i).support (b i) else 0) c) :
    Ac.Hit Prod.fst p.B (barcodePrice A b) p.supportExponent c := by
  intro x
  let f (i : ℕ) := if x ∈ (A.forced i).support then p.mass (A.forced i).support (b i) else 0
  let j (s : Box n) := if x ∈ s.1 then barcodePrice A b s *
    Real.exp (p.supportExponent * coverNumber p.B s.1) else 0
  have hx : SumBudget f c := h x
  have eq (s : Box n) : ∑' i : {i : ℕ // barcode A i = s}, f i.val = j s := by
    have hs (i : {i : ℕ // barcode A i = s}) : (A.forced i.val).support = s.1 :=
      congrArg Prod.fst i.property
    by_cases hit : x ∈ s.1
    · simp only [f,j,hs,if_pos hit,BudgetPoint.mass,barcodePrice]
      rw [tsum_mul_left,mul_comm]
    · simp [f,j,hs,hit]
  change SumBudget j c
  refine ⟨fun s => ?_, Summable.of_finite, ?_⟩
  · dsimp [j]
    split
    · exact mul_nonneg (barcode_nonneg A b hb s) (Real.exp_nonneg _)
    · rfl
  · have hsum := hx.2.1.hasSum.tsum_fiberwise (barcode A)
    calc ∑' s, j s = ∑' s, ∑' i : {i : ℕ // barcode A i = s}, f i.val :=
          tsum_congr fun s => (eq s).symm
      _ = ∑' i, f i := hsum.tsum_eq
      _ ≤ c := hx.2.2

theorem reduce {b : ℕ → ℝ} (hb : ∀ i, 0 ≤ b i) {c e : ℝ}
    (h : Ac.Hit Prod.fst p.B (barcodePrice A b) p.supportExponent c)
    (he : e ≤ p.supportExponent) : Ac.Hit Prod.fst p.B (barcodePrice A b) e c := by
  intro x
  apply budget_mono (h x)
  · intro s
    split
    · exact mul_nonneg (barcode_nonneg A b hb s) (Real.exp_nonneg _)
    · rfl
  · intro s
    split
    · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right he (by positivity))) (barcode_nonneg A b hb s)
    · rfl

theorem physical (R : Run G) (N m L : ℕ) (hL : L ≤ N) :
    ∃ b : ℕ → ℝ, Summable b ∧ (∀ i, 0 ≤ b i) ∧
      (∀ i U, ‖(R.family.path.rep N m L).activities.K i U‖ ≤ b i) ∧
      ∀ e ≤ (R.family.path.rep N m L).p.supportExponent,
        Ac.Hit Prod.fst (R.family.path.rep N m L).p.B
          (barcodePrice (R.family.path.rep N m L).activities b) e (R.family.path.levels.clock.forcedAllowance L) := by
  obtain ⟨b,hb,hinc⟩ := (R.makes.wilson.represents N m L hL).good.labels.boundK
  have hsum := Activities.summable_charge
    (fun i => ((R.family.path.rep N m L).activities.forced i).inventory_ne.mono
      ((R.family.path.rep N m L).activities.forced i).inventory_sup) (fun i => (hb i).1) hinc
  exact ⟨b, hsum, fun i => (hb i).1, fun i => (hb i).2, fun e he =>
    reduce _ _ (fun i => (hb i).1) (grouped _ _ b (fun i => (hb i).1) hinc) he⟩

end YM.Integration.QLocalBarcodeIncidence
end
