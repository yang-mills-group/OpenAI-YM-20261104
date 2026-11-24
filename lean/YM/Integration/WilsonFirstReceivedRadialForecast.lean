import YM.Comparison.RG02.Valence.Volume
import YM.Comparison.RG02.Order.Eval
import YM.Comparison.RG02.Assembly.Clipper

/-! The complete finite normalized Wick forecast, at a fixed running coupling,
is one polynomial along each real ray of the original held field. The degree
uses the issued field loads and retains every proper source in the logarithm. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFirstReceivedRadialForecast
open Finset Lattice RG Wilson Marker Precision Tree Exterior
open Comparison.RG02 Comparison.RG02.Order
open scoped Classical BigOperators
variable {G : Gauge} {V : Type} [Fintype V] [DecidableEq V] {I : Census V}
  {c f : Side} {P : Clip} {X : PathData G} {O : ChartRatio G} {S : StepData c f}
  (K : Bulk.Kernel S P X O) (F : Forest S.ratio) (tag : S.Choices) (W : Bulk.Colors I G f)
  (r : ℕ) (s : I.Mode)

def entry (i : ℕ) (a : fieldDir G c 1) : ℂ :=
  (observe I r (logMarked (Bulk.Fk K F tag W a r)) i).part s

def polynomial (D : ℕ) (a : fieldDir G c 1) (g : ℝ) : Polynomial ℂ :=
  ∑ i∈range (r+1),∑ k∈range (D+1),Polynomial.monomial k
    ((g:ℂ)^i * Assembly.jet (entry K F tag W r s i) k a)

theorem bounded (D : ℕ) (a : fieldDir G c 1) (g : ℝ) :
    (polynomial K F tag W r s D a g).natDegree≤D := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  exact (Polynomial.natDegree_monomial_le ..).trans (Nat.le_of_lt_succ (mem_range.mp hk))

theorem evaluated (D : ℕ) (price : V → ℤ) (issued : Valence.Toile W.power s price)
    (room : (r:ℤ)+2+∑ v∈s.val, price v ≤ D) (a : fieldDir G c 1) (g x : ℝ) :
    (polynomial K F tag W r s D a g).eval (x:ℂ)=
      (Order.value (g:ℂ) (logMarked (Bulk.Fk K F tag W (x • a) r))).part s := by
  have fine (i:ℕ) (hi:i≤r) : Valence.Level (D:ℤ) (entry K F tag W r s i) := by
    have h:=Valence.mark_read (r:=r) K F tag W price s i issued
    apply h.promote
    omega
  change (∑ i∈range (r+1),∑ k∈range (D+1),Polynomial.monomial k
    ((g:ℂ)^i * Assembly.jet (entry K F tag W r s i) k a)).eval (x:ℂ)=_
  simp only [Order.value,Poly.part_sum,Poly.part_smul,Polynomial.eval_finsetSum,
    Polynomial.eval_monomial]
  apply sum_congr rfl
  intro i hi
  change _ = (g:ℂ)^i * entry K F tag W r s i (x • a)
  rw [(fine i (Nat.le_of_lt_succ (mem_range.mp hi))).posted (x • a), Finset.mul_sum]
  apply sum_congr rfl
  intro k _
  rw [Assembly.Clipper.weight]
  simp only [Complex.real_smul,Complex.ofReal_pow]
  ring

end YM.Integration.WilsonFirstReceivedRadialForecast
