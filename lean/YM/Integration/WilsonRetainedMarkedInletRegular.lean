import YM.Integration.WilsonRetainedMarkedInlet
import YM.Push.LOCAL_SPLITTING.Calculus
import YM.Corona.Fit

/-! A single support-exponent unit moves each originally marked regular derivative to every site of its support. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000

noncomputable section
namespace YM.Integration.WilsonRetainedMarkedInletRegular

open Function Finset Lattice Wilson RG Marker Overlay QuadraticLocal Ac Push.AbsoluteSums
open scoped Classical Topology BigOperators

def moving (p : BudgetPoint) (k : ℕ) : ℝ :=
  (1 + ((k*(4*p.B+2)+2*p.B : ℕ):ℝ))^(p.power*p.order)

def cost (p : BudgetPoint) : ℝ :=
  (6*(p.B:ℝ)+3)^(p.power*p.order) * ((p.power*p.order).factorial:ℝ) * Real.exp 1

theorem allowance (p : BudgetPoint) (k : ℕ) :
    moving p k * Real.exp ((p.supportExponent-1)*k) ≤ cost p * Real.exp (p.supportExponent*k) := by
  let K := p.power*p.order
  have r : 1+((k*(4*p.B+2)+2*p.B:ℕ):ℝ) ≤ (6*(p.B:ℝ)+3)*(1+k) := by
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) p.B) (Nat.cast_nonneg (α:=ℝ) k)]
  have poly := pow_le_pow_left₀ (by positivity : 0≤1+((k*(4*p.B+2)+2*p.B:ℕ):ℝ)) r K
  have fac := (div_le_iff₀ (show 0<(K.factorial:ℝ) by positivity)).mp
    (Real.pow_div_factorial_le_exp (1+(k:ℝ)) (by positivity) K)
  have step : moving p k ≤ (6*(p.B:ℝ)+3)^K * (Real.exp (1+k) * K.factorial) := by
    unfold moving
    rw [mul_pow] at poly
    exact poly.trans (mul_le_mul_of_nonneg_left fac (by positivity))
  calc
    _ ≤ ((6*(p.B:ℝ)+3)^K * (Real.exp (1+k) * K.factorial)) *
        Real.exp ((p.supportExponent-1)*k) := mul_le_mul_of_nonneg_right step (Real.exp_pos _).le
    _ = _ := by
      have ex : Real.exp (1+(k:ℝ)) * Real.exp ((p.supportExponent-1)*k) =
          Real.exp 1 * Real.exp (p.supportExponent*k) := by
        rw [←Real.exp_add,←Real.exp_add]
        congr 1
        ring
      unfold cost
      calc
        _ = (6*(p.B:ℝ)+3)^K*K.factorial *
          (Real.exp (1+k)*Real.exp ((p.supportExponent-1)*k)) := by ring
        _ = _ := by rw [ex]; ring

variable {G : Gauge} {n : Side} {V : Type*} [Fintype V] [DecidableEq V]
  {R : Census V} {P : Rep G n} (a : Bands R P) (h : a.Active)
  {w : V → ℝ} {u c d b : ℝ} (t : a.Radial w u c d b)

include t in
theorem purchased : (WilsonRetainedMarkedInlet.lamps a h).Paid w P.p.B (P.p.supportExponent-1)
    (cost P.p * (Fintype.card V * c)) := by
  classical
  obtain ⟨f,hf,bill⟩ := t.bulk
  let k (i : ℕ) := coverNumber P.p.B (a.support i)
  let g (i : ℕ) := Poly.toll w (a.rays i) * P.p.mass (a.support i) (f i)
  have pooled : SumBudget g (Fintype.card V * c) := Overlay.per_system
    (fun i => mul_nonneg (Poly.worth t.pure _).le ((P.p.loMass _ _ (hf i).1).trans' (hf i).1))
    h.proper bill
  have cpos : 0 ≤ cost P.p := by unfold cost; positivity
  refine ⟨fun i=>moving P.p (k i)*f i, fun i=>by
    have := (hf i).1
    unfold moving
    positivity, ?_, ?_⟩
  · intro i _ x hx
    let v := (h.proper i).choose
    have place := (hf i).2 v (h.proper i).choose_spec
    have loc := Corona.extent (a.support i) P.p.B (h.pins i v (h.proper i).choose_spec) hx
    apply Push.Local.bound_weaken (Push.Local.bound_shift place (h.regular i) x)
    apply mul_le_mul_of_nonneg_right _ (hf i).1
    rw [←pow_mul]
    unfold moving
    gcongr
  · intro x
    apply budget_of_sum
    · intro i
      split
      next =>
        have := (hf i).1
        have := (Poly.worth t.pure (a.rays i)).le
        dsimp [WilsonRetainedMarkedInlet.lamps,Lamps.ground,moving]
        positivity
      next => exact le_rfl
    · intro J
      calc
        _ ≤ ∑ i∈J,cost P.p*g i := by
          apply Finset.sum_le_sum
          intro i _
          have h0 := (hf i).1
          have ht := (Poly.worth t.pure (a.rays i)).le
          split
          next =>
            change Poly.toll w (a.rays i) * (moving P.p (k i)*f i) *
              Real.exp ((P.p.supportExponent-1)*k i) ≤ cost P.p*g i
            calc
              _ = (Poly.toll w (a.rays i) * f i) *
                (moving P.p (k i)*Real.exp ((P.p.supportExponent-1)*k i)) := by ring
              _ ≤ _ := by
                have z := mul_le_mul_of_nonneg_left (allowance P.p (k i)) (mul_nonneg ht h0)
                simpa only [g,BudgetPoint.mass,k,mul_assoc,mul_comm,mul_left_comm] using z
          next => exact mul_nonneg cpos (pooled.1 i)
        _ = cost P.p * ∑ i∈J,g i := by rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left (budget_sum pooled J) cpos

end YM.Integration.WilsonRetainedMarkedInletRegular

