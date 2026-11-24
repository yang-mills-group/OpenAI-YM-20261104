import YM.Integration.WilsonRetainedMarkedInletHard
import YM.Source.Insertion

/-! Enroll an original deposited forced coefficient at its actual owner alongside all prior entries. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalDepositedHard
open Function Finset MeasureTheory Lattice Wilson RG Source Marker Overlay QuadraticLocal Ac
open Push.Corrected Push.AbsoluteSums
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {d : ℕ} {F : Labels.Frame G d} {A : Hol G}
  {P : Rep G n} {V T : Type} [DecidableEq V] {J : Census V} {o : V → Site n}
  (prior : Hard T P.p P.activities.forced P.activities.K o J) (j : V)
  (q : Coefficient F n) (law : q.Format (o j) A P) (t : T → ℂ)

private theorem live : J.quiet ≠ J.fire j := by
  intro h
  have wrong : (∅ : Finset V) = {j} := congrArg Subtype.val h
  simp at wrong

def joined : Hard T P.p P.activities.forced P.activities.K o J where
  hard x i U := prior.hard x i U + Poly.send (J.fire j) (t x * q.forced i U)
  locality x i := by
    have h := prior.locality x i
    refine ⟨fun θ U => congrArg₂ (·+·) (h.gauge θ U)
      (congrArg (fun z : ℂ => Poly.send (J.fire j) (t x * z)) (law.invariant i θ U)), ?_, ?_, ?_⟩
    · exact h.borel.add ((Bands.sends _).measurable.comp (measurable_const.mul (law.borel i)))
    · exact fun U W ha hf => congrArg₂ (·+·) (h.reads U W ha hf)
        (congrArg (fun z : ℂ => Poly.send (J.fire j) (t x*z)) (law.supported i U W ha hf))
    · intro U s nz v hv
      by_cases enter : (prior.hard x i U).part s ≠ 0
      · exact h.carry U s enter v hv
      · rw [Poly.part_plus,not_ne_iff.mp enter,zero_add,Poly.part_send] at nz
        split at nz
        next hs =>
          subst s
          have id : v = j := Finset.mem_singleton.mp hv
          subst v
          exact law.carried i (fun hzero => nz (by simp [hzero]))
        next => exact (nz rfl).elim
  charged x i U nz := by
    by_contra fail
    have priorZero : prior.hard x i U = 0 := not_ne_iff.mp (fun hp => fail (prior.charged x i U hp))
    have forcedZero : q.forced i U = 0 := not_ne_iff.mp (fun hp => fail (law.forcing i U hp))
    exact nz (by simp [priorZero,forcedZero])
  quiet x i U := by rw [Poly.part_plus,prior.quiet,Poly.part_send,if_neg (live j),add_zero]

theorem posted (x : T) (i : ℕ) (U : Config G n) :
    (joined prior j q law t).hard x i U = prior.hard x i U + Poly.send (J.fire j) (t x*q.forced i U) := rfl

open private atom plus from YM.Integration.WilsonRetainedMarkedInletHard

theorem paid [Fintype V] (w : V → ℝ) (hw : ∀ i, 0 < w i) {κ B k : ℝ}
    (base : prior.Paid w P.p.B P.p.supportExponent k) (tested : ∀ x, ‖t x‖ ≤ 1)
    (actual : q.remBound (o j) P κ B) :
    (joined prior j q law t).Paid w P.p.B P.p.supportExponent (k + w j*(κ*B)) := by
  obtain ⟨a,b,ha,hb,total,hκ,_,e,cost,values⟩ := actual
  obtain ⟨f,cap,first⟩ := base.wages
  let s := fun i => (P.activities.forced i).support
  let add := fun i => Poly.send (J.fire j) (e i : ℂ)
  have eb (i : ℕ) : 0 ≤ e i := (values i).1
  have pb (i : ℕ) : Poly.price w (f i + add i) ≤ Poly.price w (f i)+w j*e i := by
    apply (Poly.addition hw _ _).trans_eq
    simp [add,Real.norm_eq_abs,abs_of_nonneg (eb i)]
  refine ⟨fun i => f i + add i,?_,?_⟩
  · intro i x U
    apply plus (cap i x U)
    apply atom
    calc ‖t x*q.forced i U‖ = ‖t x‖*‖q.forced i U‖ := norm_mul _ _
         _ ≤ 1*e i := mul_le_mul (tested x) ((values i).2 U) (norm_nonneg _) zero_le_one
         _ = _ := one_mul _
  · intro z
    have second := budget_scale (hw j).le cost
    apply budget_of_sum
    · intro i
      split
      next => exact mul_nonneg (Poly.nonnegative hw _) (Real.exp_nonneg _)
      next => exact le_rfl
    · intro D
      let g := fun i => if z∈s i then Poly.price w (f i) * Real.exp (P.p.supportExponent*coverNumber P.p.B (s i)) else 0
      have each (i : ℕ) : (if z∈s i then Poly.price w (f i+add i)*Real.exp (P.p.supportExponent*coverNumber P.p.B (s i)) else 0) ≤
          g i+w j*P.p.mass (s i) (e i) := by
        by_cases h : z∈s i
        · simp only [g,if_pos h]
          apply (mul_le_mul_of_nonneg_right (pb i) (Real.exp_nonneg _)).trans_eq
          unfold BudgetPoint.mass
          ring
        · simp only [g,if_neg h,zero_add]
          exact mul_nonneg (hw j).le (mul_nonneg (Real.exp_nonneg _) (eb i))
      calc _ ≤ ∑ i∈D,(g i+w j*P.p.mass (s i) (e i)) := Finset.sum_le_sum fun i _ => each i
           _ ≤ k+w j*(κ*b) := by
             rw [Finset.sum_add_distrib]
             exact add_le_add (budget_sum (first z) D) (budget_sum second D)
           _ ≤ _ := add_le_add (le_refl k) (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (show b ≤ B by linarith) hκ.le) (hw j).le)

end YM.Integration.WilsonOriginalDepositedHard
