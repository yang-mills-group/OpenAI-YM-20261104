import YM.Integration.WilsonFiniteBareHistory

/-! The independently prescribed finite and cover programs make the same
kinetic change of variable. At a fixed output degree this spends just the
absolute coefficients of that scalar series against the incoming invoices. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFiniteCommonKineticReset
open Function Filter Lattice Wilson RG Precision Laurent PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Winding
open scoped Classical BigOperators

variable {G : Gauge}

def fee (b : Cost) (i l : ℕ) (B : ℕ → ℝ) : ℝ :=
  ∑ a ∈ Finset.range (i+1), ‖coeff (i-a) (b^a * (b⁻¹)^l)‖ * B a

theorem retained (A : Levels G) (β : ChartRatio G) {N m : ℕ} (hm : m < N)
    (n : Side) (i r : ℕ) {s : ℝ} (B : ℕ → ℝ)
    (input : ∀ a ≤ i, Sight
      (unripe A β N m (story A β N (m+1)).1 n a (r+1))
      (freshet A β N m a (r+1)) s (B a)) :
    Sight ((story A β N m).1 n i (r+1)) (actionW A β N m i (r+1)) s
      (fee (back (Kstar (freshet A β N m))) i (r+1) B) := by
  let b := back (Kstar (freshet A β N m))
  have rates := Sight.sum (Finset.range (i+1)) (fun a ha =>
    (input a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha))).μ (coeff (i-a) (b^a * (b⁻¹)^(r+1))))
  rw [actionW,story_stride A β hm]
  simpa only [twinkle,Blue.mix,lop,if_neg (Nat.succ_ne_zero r),fee,b,freshet,actionW] using rates

theorem quiet (A : Levels G) (β : ChartRatio G) {N m : ℕ} (hm : m < N)
    (n : Side) (i : ℕ) (s : ℝ) : Sight ((story A β N m).1 n i 0) (actionW A β N m i 0) s 0 := by
  rw [actionW,story_stride A β hm]
  simpa [twinkle,Blue.mix,lop] using
    (Sight.zero (n:=n) (r:=0) (α:=Hooks G) (V:=ℝ) (s:=s))

end YM.Integration.WilsonFiniteCommonKineticReset
