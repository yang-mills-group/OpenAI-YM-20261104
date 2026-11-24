import YM.Integration.WilsonOriginalDepositedHardTable

/-! Enroll the masked stable rows of the original deposited source and charge their actual support sizes. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalDepositedRegular
open Function Finset MeasureTheory Lattice Wilson RG Source Marker Overlay QuadraticLocal Ac
open Next.Foundations Push.Local Push.AbsoluteSums WilsonRetainedMarkedInletRegular
open scoped Topology Classical BigOperators
variable {G : Gauge} {n : Side} {d : ℕ} {F : Labels.Frame G d} {A : Hol G}
  {P : Rep G n} {V T : Type} [DecidableEq V] {J : Census V} {o : V → Site n}
  (j : V) (q : Coefficient F n) (law : q.Format (o j) A P) (t : T → ℂ) (keep : ℕ → Prop)

def lamps : Lamps T ℕ G P.p o J where
  mode _ := J.fire j
  live _ := J.fire_hot _
  address i := ⟨o j,q.support i,law.origin i⟩
  roots i v hv := (show v=j from Finset.mem_singleton.mp hv) ▸ law.origin i
  nominal x i := (if keep i then t x else 0) • q.regular i
  legal _ i := regular_smul _ (law.smooth i)
  clear _ := False
  pure _ _ _ no := no.elim

theorem row (x : T) (i : ℕ) (U : Config G n) :
    (lamps (J:=J) j q law t keep).frame i x U =
    Poly.send (J.fire j) ((if keep i then t x else 0) * q.maskedTerm P i U) := by
  unfold Lamps.frame Lamps.light Lamps.ground lamps Coefficient.maskedTerm
  simp only [↓reduceIte]
  by_cases h : Healthy P.p.threshold (q.support i) U
  · rw [masked_eq _ _ _ _ h,masked_eq _ _ _ _ h]
    rfl
  · rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _ h,mul_zero]

theorem paid [Fintype V] (w : V → ℝ) (hw : ∀v, 0<w v) (tested : ∀x, ‖t x‖≤1)
    {κ B a D : ℝ} (actual : q.remBound (o j) P κ B) (hD : 0 ≤ D)
    (width : ∀ i, keep i → Real.exp (a*coverNumber P.p.B (q.support i)) ≤
       D*Real.exp ((P.p.supportExponent-1)*coverNumber P.p.B (q.support i))) :
    (lamps (J:=J) j q law t keep).Paid w P.p.B a (D*cost P.p*(w j*B)) := by
  obtain ⟨b,c,hb,hc,paid,_,⟨e,book,hee⟩,_⟩ := actual
  let k i := coverNumber P.p.B (q.support i)
  let g := fun i => if keep i then moving P.p (k i)*e i else 0
  have he i : 0 ≤ e i := (hee i).1
  have hm i : 0 ≤ moving P.p (k i) := by unfold moving; positivity
  have hg i : 0 ≤ g i := by dsimp [g]; split <;> first | exact mul_nonneg (hm i) (he i) | exact le_rfl
  have hcost : 0 ≤ cost P.p := by unfold cost; positivity
  refine ⟨g,hg,?_,?_⟩
  · intro i x u hu
    change P.p.supBounds u (q.support i) ((if keep i then t x else 0) • q.regular i) (g i)
    have moved : P.p.supBounds u (q.support i) (q.regular i) (moving P.p (k i)*e i) := by
      apply bound_weaken (bound_shift (hee i) (law.smooth i) u)
      apply mul_le_mul_of_nonneg_right _ (he i)
      rw [←pow_mul]
      unfold moving
      have loc := Corona.extent (q.support i) P.p.B (law.origin i) hu
      gcongr
    apply bound_weaken (bound_smul (if keep i then t x else 0) moved)
    by_cases take : keep i
    · simpa only [if_pos take,g] using mul_le_of_le_one_left (mul_nonneg (hm i) (he i)) (tested x)
    · simp [take,g]
  · intro u
    have scaled := budget_scale (mul_nonneg (mul_nonneg hD hcost) (hw j).le) book
    apply budget_of_sum
    · intro i
      split
      next => exact mul_nonneg (mul_nonneg (Poly.worth hw _).le (hg i)) (Real.exp_nonneg _)
      next => exact le_rfl
    · intro S
      have one (i : ℕ) : (if u∈q.support i then Poly.toll w (J.fire j)*g i*Real.exp (a*k i) else 0) ≤
            D*cost P.p*w j*P.p.mass (q.support i) (e i) := by
        have nn : 0 ≤ D*cost P.p*w j*P.p.mass (q.support i) (e i) := mul_nonneg (mul_nonneg (mul_nonneg hD hcost) (hw j).le)
          (mul_nonneg (Real.exp_nonneg _) (he i))
        by_cases hit : u∈q.support i
        · by_cases take : keep i
          · simp only [if_pos hit,g,if_pos take,Poly.solo_toll]
            have width' := width i take
            calc _ ≤ w j*(moving P.p (k i)*e i)*(D*Real.exp ((P.p.supportExponent-1)*k i)) :=
                     mul_le_mul_of_nonneg_left width' (mul_nonneg (hw j).le (mul_nonneg (hm i) (he i)))
                 _ = D*w j*e i * (moving P.p (k i)*Real.exp ((P.p.supportExponent-1)*k i)) := by ring
                 _ ≤ D*w j*e i * (cost P.p*Real.exp (P.p.supportExponent*k i)) :=
                    mul_le_mul_of_nonneg_left (allowance P.p _) (mul_nonneg (mul_nonneg hD (hw j).le) (he i))
                 _ = _ := by unfold BudgetPoint.mass; dsimp only [k]; ring
          · simpa only [if_pos hit,g,if_neg take,mul_zero,zero_mul] using nn
        · simpa only [if_neg hit] using nn
      calc _ ≤ ∑ i∈S,D*cost P.p*w j*P.p.mass (q.support i) (e i) := Finset.sum_le_sum fun i _ => one i
           _ ≤ D*cost P.p*w j*b := budget_sum scaled S
           _ ≤ _ := by
             rw [mul_assoc (D*cost P.p)]
             exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) (hw j).le) (mul_nonneg hD hcost)

end YM.Integration.WilsonOriginalDepositedRegular
