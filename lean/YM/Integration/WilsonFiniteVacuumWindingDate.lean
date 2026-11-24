import YM.Integration.WilsonFiniteVacuumFreeInput
import YM.Integration.WilsonFirstInheritedVacuumIncome

/-! The original finite quiet recursion, compared with its independent cover recursion
on their common measured Wilson step. Only the occupied positive coupling and
angular grades of the incoming quiet vacuum need a separate winding invoice. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonFiniteVacuumWindingDate
open Function Filter Finset Lattice Wilson RG Precision Laurent
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Wheel WilsonCoeffUV.Winding
open scoped Classical BigOperators
variable {G : Gauge} {e m i r : ℕ} {E : Credit}

/-- These are exactly the finitely many possibly nonzero, nonfree quiet slots.
The angular cutoff is the original Wilson shell at each coupling grade. -/
def positive (L : Levels G) (β : ChartRatio G) (e N m : ℕ) (s V : ℝ) : Prop :=
  ∀ (n : Side) a, 0 < a → a ≤ e → ∀ l, l+1 ≤ a+2 →
    Sight ((story L β N m).1 n a (l+1)) (actionW L β N m a (l+1)) s V

theorem prepare (Q : Realm G (e+1) E) (hm : Q.anchor ≤ m) {s : ℝ} (hs : 0 < s) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ N (_ : m < N) (n : Side) (V : ℝ), 1 ≤ V →
      positive Q.draws Q.paid e N (m+1) s V →
      ∀ a ≤ e, ∀ l, Sight ((story Q.draws Q.paid N (m+1)).1 (n*(loose Q.draws m).L) a l)
        (actionW Q.draws Q.paid N (m+1) a l) (holt Q m hm s hs).s (B*V) := by
  obtain ⟨B,hB,free⟩ := WilsonFiniteVacuumFreeInput.original Q hm hs
  refine ⟨B,hB,?_⟩
  intro N cut n V hV issued a ha l
  let q := n*(loose Q.draws m).L
  have more : 0 ≤ B*V := mul_nonneg (zero_le_one.trans hB) (zero_le_one.trans hV)
  cases a with
  | zero => exact (free N cut n l).more (le_mul_of_one_le_right (zero_le_one.trans hB) hV)
  | succ a =>
    let u := (old Q.draws Q.paid Q.hG Q.green N (m+1) cut).basis q
    cases l with
    | zero =>
      have finite := congr_fun (congr_fun u.clear (a+1)) 0
      have cover := congr_fun (congr_fun (catchment Q.draws Q.paid Q.hG Q.green cut).empty (a+1)) 0
      change (0 : Ten ℝ (Site q × Hooks G) 0) = _ at finite
      change (0 : Ten ℝ (Cloth (Hooks G)) 0) = _ at cover
      rw [←finite,←cover]
      exact Sight.zero.more more
    | succ l =>
      by_cases low : l+1 ≤ (a+1)+2
      · apply ((issued q (a+1) (Nat.zero_lt_succ _) ha l low).mono ?_).more
          (le_mul_of_one_le_left (zero_le_one.trans hV) hB)
        exact (min_le_left (s/32) _).trans (by linarith)
      · have high : (a+1)+2 < l+1 := by omega
        rw [u.lamp (a+1) (l+1) (by omega),
          post_end (A:=Q.draws) Q.hG Q.green cut (a+1) (l+1) (by omega)]
        exact Sight.zero.more more

/-- Constants and output width precede the cutoff, period and inlet bill. -/
theorem prior (Q : Realm G (e+1) E) (hm : Q.anchor ≤ m) (hi : i ≤ e) {s : ℝ} (hs : 0 < s) :
    ∃ (d : ℕ) (C σ : ℝ), 0 ≤ C ∧ 0 < σ ∧ ∀ N (_ : m < N) (n : Side) (V : ℝ),
      1 ≤ V → positive Q.draws Q.paid e N (m+1) s V →
      Sight (unripe Q.draws Q.paid N m (story Q.draws Q.paid N (m+1)).1 n i r)
        (freshet Q.draws Q.paid N m i r) σ (C*V^d) := by
  obtain ⟨B,hB,frame⟩ := prepare Q hm hs
  obtain ⟨d,step⟩ := windingVault G e i r hi
  obtain ⟨σ,C,hσ,hC,pay⟩ := step (holt Q m hm s hs)
  refine ⟨d,C*B^d,σ,mul_nonneg hC (pow_nonneg (zero_le_one.trans hB) _),hσ,?_⟩
  intro N cut n V hV issued
  let p : ScrollV e (holt Q m hm s hs) :=
    { cloVent Q m N n hm cut s hs with W := (story Q.draws Q.paid N (m+1)).1
                                       coin := B*V
                                       paid := one_le_mul_of_one_le_of_one_le hB hV
                                       fare := frame N cut n V hV issued }
  have charged := pay p
  change Sight (unripe Q.draws Q.paid N m (story Q.draws Q.paid N (m+1)).1 n i r)
    (freshet Q.draws Q.paid N m i r) σ (C*(B*V)^d) at charged
  simpa only [mul_pow,mul_assoc] using charged

end YM.Integration.WilsonFiniteVacuumWindingDate
end

