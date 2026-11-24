import YM.Integration.WilsonConditionalTaylorBulkPass
import YM.FormalBulk08.Wine.Cab

/-! Convergence of the actual finite spatial Gibbs action under a measured
coupling change, retaining a positive strip for each full coefficient. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorBulkStamp
open Filter PowerSeries Lattice FormalBulk08
open Jets Reef Lava Mesa Lotus Gorge Wine Bank Shore Series Wilson Orb Wick
open scoped Topology BigOperators Classical

def Scalar (H : PowerSeries ℝ) (h : Side→PowerSeries ℝ) :=
  ∀ e,Tendsto (fun n=>coeff e (h n)) atTop (𝓝 (coeff e H))

private theorem times {A B : PowerSeries ℝ} {a b : Side→PowerSeries ℝ}
    (p : Scalar A a) (q : Scalar B b) : Scalar (A*B) (fun n=>a n*b n) := by
  intro e
  simp only [PowerSeries.coeff_mul]
  exact tendsto_finsetSum _ (fun i _=>(p i.1).mul (q i.2))

private theorem powers {A : PowerSeries ℝ} {a : Side→PowerSeries ℝ}
    (p : Scalar A a) (k : ℕ) : Scalar (A^k) (fun n=>a n^k) := by
  induction k with
  | zero => intro e; simp only [pow_zero];exact tendsto_const_nhds
  | succ k ih => simpa only [pow_succ] using times ih p

theorem weight {A B : PowerSeries ℝ} {a b : Side→PowerSeries ℝ}
    (p : Scalar A a) (q : Scalar B b) (e j r : ℕ) :
    Tendsto (fun n=>Wine.bill (a n) (b n) e j r) atTop (𝓝 (Wine.bill A B e j r)) :=
  times (powers p j) (powers q r) (e-j)

theorem variableWeight {I : Type} {r : ℕ} {η b : ℝ} {w : Side→ℝ}
    {T : Tile (Biglot I) r} {U : (n:Side)→ Tile (Tor n I) r}
    (h : Kith η T U) (hw : Tendsto w atTop (𝓝 b)) :
    Kith η (b • T) (fun n=>w n • U n) := by
  obtain ⟨point,C,price⟩:=h
  refine ⟨fun u=>hw.mul (point u),(|b|+1)*C,?_⟩
  have bound : ∀ᶠ n in atTop, abs (w n) < abs b + 1 :=
    hw.abs.eventually (gt_mem_nhds (lt_add_one _))
  filter_upwards [price,bound] with n paid lim
  exact (paid.smul _).mono (mul_le_mul_of_nonneg_right lim.le paid.1)

theorem action {G : Gauge} (W : Pot G) (V : (n:Side)→Pap (wire G n))
    {A B : PowerSeries ℝ} {a b : Side→PowerSeries ℝ} (p : Scalar A a) (q : Scalar B b)
    (e r : ℕ) (income : ∀ j≤e, ∃ s:ℝ, 0<s ∧ Kith s (W j r) (fun n=>rancho (V n) j r)) :
    ∃ η : ℝ,0<η ∧ Kith η (Wine.stamp A B W e r)
      (fun n=>rancho (Wine.canter (a n) (b n) _ (V n)) e r) := by
  simp only [Wine.stamp_book,Wine.stamp]
  apply kith_joint
  intro j hj
  obtain ⟨s,hs,h⟩:=income j (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hj)
  exact ⟨s,hs,variableWeight h (weight p q e j r)⟩

end YM.Integration.WilsonConditionalTaylorBulkStamp

