import YM.Integration.WilsonCapturedPrimaryWickCurve
import YM.Integration.WilsonCapturedPrimaryOrdinaryConvolution

/-! The finite signed ordinary Wilson program on the physical test curve,
including its proper singleton product through exactly the requested grade. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWickFiled
open Finset Lattice RG Wilson Marker Precision Tree Exterior
open Comparison.RG02 Comparison.RG02.Order
open scoped Classical BigOperators
variable {G : Gauge} {V : Type} [Fintype V] [DecidableEq V] {I : Census V}
  {c f : Side} {P : Clip} {X : PathData G} {O : ChartRatio G} {S : StepData c f}
  (K : Bulk.Kernel S P X O) (F : Forest S.ratio) (tag : S.Choices) (W : Bulk.Colors I G f)
  (r D d : ℕ) (v : Fin (d+1) → fieldDir G c 1)

def leaf (s : I.Mode) (j : ℕ) : Polynomial ℂ :=
  WilsonCapturedPrimaryWickCurve.pull (WilsonFirstReceivedRadialForecast.entry K F tag W r s j) D d v

def source (z : ℂ) (s : I.Mode) : Polynomial ℂ :=
  ∑ j∈range (r+1), Polynomial.C (z^j)*leaf K F tag W r D d v s j

def signed (z : ℂ) (a b c₀ : V) (s : I.Mode) : Polynomial ℂ :=
  source K F tag W r D d v z s - source K F tag W r D d v z (I.fire c₀) +
    ∑ j∈range (r+1), Polynomial.C (z^j) *
      ∑ u∈antidiagonal j, leaf K F tag W r D d v (I.fire a) u.1 * leaf K F tag W r D d v (I.fire b) u.2

theorem degree (z : ℂ) (a b c₀ : V) (s : I.Mode) :
    (signed K F tag W r D d v z a b c₀ s).natDegree ≤ 2*(D*d) := by
  have h (t : I.Mode) (j : ℕ) : (leaf K F tag W r D d v t j).natDegree ≤ D*d :=
    WilsonCapturedPrimaryWickCurve.bound .. 
  have con (x : ℂ) (f' : Polynomial ℂ) : (Polynomial.C x*f').natDegree≤f'.natDegree := by
    simpa only [Polynomial.natDegree_C,zero_add] using (show (Polynomial.C x*f').natDegree ≤ (Polynomial.C x).natDegree+f'.natDegree from Polynomial.natDegree_mul_le)
  have ht (t : I.Mode) : (source K F tag W r D d v z t).natDegree ≤ D*d :=
    Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => (con ..).trans (h t j)
  apply (Polynomial.natDegree_add_le ..).trans
  apply max_le
  · exact (Polynomial.natDegree_sub_le ..).trans ((max_le (ht _) (ht _)).trans (by omega))
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro j _
    apply (con ..).trans
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro u _
    exact (Polynomial.natDegree_mul_le ..).trans ((Nat.add_le_add (h _ _) (h _ _)).trans (by omega))

theorem evaluated (price : V → ℤ) (z : ℂ) (a b c₀ : V) (s : I.Mode) (diff : a≠b) (ab : s.val={a,b})
    (issued : ∀ t∈({s,I.fire a,I.fire b,I.fire c₀}:Finset _), Valence.Toile W.power t price)
    (room : ∀ t∈({s,I.fire a,I.fire b,I.fire c₀}:Finset _), (r:ℤ)+2+∑ l∈t.val, price l ≤ D) (y : ℝ) :
    let angle := ∑ j, y^j.val • v j
    let X' := Bulk.Fk K F tag W angle r
    let Z := value z (ratio X')
    (signed K F tag W r D d v z a b c₀ s).eval (y:ℂ) = Z.part s-Z.part (I.fire c₀) := by
  intro angle X' Z
  let e := fun t j => (observe I r (logMarked X') j).part t
  let modes : Finset I.Mode := {s,I.fire a,I.fire b,I.fire c₀}
  have fine (t : I.Mode) (ht : t∈modes) (j : ℕ) (hj : j≤r) :
      (leaf K F tag W r D d v t j).eval (y:ℂ) = e t j := by
    apply WilsonCapturedPrimaryWickCurve.evaluated
    apply (Valence.mark_read (r:=r) K F tag W price t j (issued t ht)).promote
    have paid := room t ht
    omega
  have src (t : I.Mode) (ht : t∈modes) :
      (source K F tag W r D d v z t).eval (y:ℂ) = (value z (logMarked X')).part t := by
    simp only [source,Polynomial.eval_finsetSum,Polynomial.eval_mul,Polynomial.eval_C,
      Order.value,Poly.part_sum,Poly.part_smul]
    exact sum_congr rfl fun j hj => congrArg (z^j*·) (fine t ht j (Nat.le_of_lt_succ (mem_range.mp hj)))
  have hs : s∈modes := by simp [modes]
  have ha : I.fire a∈modes := by simp [modes]
  have hb : I.fire b∈modes := by simp [modes]
  have hc : I.fire c₀∈modes := by simp [modes]
  rw [WilsonCapturedPrimaryOrdinaryConvolution.ordinary X' (Bulk.fk_unit ..) (Bulk.fk_sym ..) z a b c₀ s diff ab]
  simp only [signed,Polynomial.eval_add,Polynomial.eval_sub,Polynomial.eval_finsetSum,
    Polynomial.eval_mul,Polynomial.eval_C,src s hs,src (I.fire c₀) hc,add_right_inj]
  apply sum_congr rfl
  intro j hj
  congr 1
  apply sum_congr rfl
  intro u hu
  have sum : u.1+u.2=j := mem_antidiagonal.mp hu
  have jr : j ≤ r := Nat.le_of_lt_succ (mem_range.mp hj)
  exact congrArg₂ (·*·) (fine _ ha _ (by omega)) (fine _ hb _ (by omega))

end YM.Integration.WilsonCapturedPrimaryWickFiled
