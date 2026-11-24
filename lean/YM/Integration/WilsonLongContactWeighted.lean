import YM.Integration.WilsonLongContactStock
import YM.Integration.WilsonLongContactResponse

/-! The original spatial mass of every regular row of an actual filed coefficient after a
full earlier Wilson history, with the same exponential support weights. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonLongContactWeighted
open Lattice Wilson RG Labels Source MeasureTheory Push.Local Push.Local.Kernel
open PhysicalNext.Repeat.Legato WilsonMacroscopicRichTransitionIncome
open scoped Classical BigOperators
variable {G : Gauge} {d : ℕ} {F : Frame G d}

theorem budget {u v : ℕ → ℝ} {C a : ℝ} (hC : 0 ≤ C) (hv : SumBudget v a)
    (hu : ∀ i, 0 ≤ u i) (h : ∀ i, u i ≤ C * v i) : SumBudget u (C*a) := by
  have full := hv.2.1.mul_left C
  have parts := Summable.of_nonneg_of_le hu h full
  exact ⟨hu,parts,(parts.tsum_le_tsum h full).trans <| by
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hv.2.2 hC⟩

theorem field {n : Side} (Q : Rep G n) (P : Coefficient F n) {z : Site n} {H : Hol G}
    (format : P.Format z H Q) {w : ℝ} (i : ℕ)
    (paid : Q.p.supBounds z (P.support i) (P.regular i) w) :
    Measurable (P.maskedTerm Q i) ∧ ∀ U, ‖P.maskedTerm Q i U‖ ≤ w := by
  refine ⟨masked_measurable _ _ _ (format.smooth i).borel,?_⟩
  intro U
  by_cases h : Healthy Q.p.threshold (P.support i) U
  · rw [Coefficient.maskedTerm,masked_eq _ _ _ _ h]
    exact paid.2 _ h [] (by simp) (by simp)
  · rw [Coefficient.maskedTerm,masked_ne _ _ _ _ h,norm_zero]
    exact paid.1

theorem original (R : Run G) {N per j : ℕ} (hj : j ≤ N)
    (P : Coefficient F (R.family.S.side j per)) (z : Site (R.family.S.side j per))
    {H : Hol G} (format : P.Format z H (R.family.path.rep N per j)) {κ w : ℝ}
    (paid : P.remBound z (R.family.path.rep N per j) κ w) :
    let Q := R.family.path.rep N per j
    ∃ a hard : ℝ, 0 ≤ a ∧ 0 ≤ hard ∧ a+hard ≤ w ∧ 0 < κ ∧
      (∃ e : ℕ → ℝ, SumBudget (fun i => Q.p.mass (Q.activities.forced i).support (e i)) (κ*hard) ∧
        ∀ i, 0 ≤ e i ∧ ∀ U, ‖P.forced i U‖ ≤ e i) ∧
      (∀ b, ∀ hb : b ≤ j, ∀ V : Config G (R.family.S.side b per),
        SumBudget (fun i => Q.p.mass (P.support i)
          ‖actualTransport R.family (N:=N) (P.maskedTerm Q i) hb V‖) a) ∧
      ∀ b, ∀ hb : b < j, ∀ order edges : ℕ, ∀ radius : ℝ, 0 ≤ radius →
        ∀ B : Edges (R.family.side b per), B.card ≤ edges →
        ∀ l : List (Directions G (R.family.S.side b per)), l.length ≤ order →
        (∀ A∈l, Born B radius A) → ∀ V : Config G (R.family.S.side b per),
          SumBudget (fun i => Q.p.mass (P.support i)
            ‖leftDerivs (actualTransport R.family (N:=N) (P.maskedTerm Q i) hb.le) l V‖)
            (WilsonMacroscopicRichHeldProbePrice.price R b order edges radius * a) := by
  intro Q
  obtain ⟨a,hard,ha,hh,total,pos,⟨e,sold,he⟩,force⟩ := paid
  have incoming (i) := field Q P format i (he i)
  refine ⟨a,hard,ha,hh,total,pos,force,?_,?_⟩
  · intro b hb V
    simpa only [BudgetPoint.mass,one_mul] using budget (C:=1) zero_le_one sold
      (fun i => mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
      (fun i => by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_left (actualTransport_norm_le R.family R.makes hj (incoming i).2 hb V)
          (Real.exp_pos _).le)
  · intro b hb order edges radius rad B hB l hl hA V
    let C := WilsonMacroscopicRichHeldProbePrice.price R b order edges radius
    have hc : 0 ≤ C := (WilsonMacroscopicRichHeldMarkedScore.score R b order edges rad).1
    apply budget hc sold (fun i => mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
    intro i
    calc
      _ ≤ Q.p.mass (P.support i) (C*e i) :=
        mul_le_mul_of_nonneg_left
          (WilsonLongContactResponse.original R b order edges rad N per j hj hb _ (incoming i).1
            (e i) (incoming i).2 B hB l hl hA V) (Real.exp_pos _).le
      _ = C * Q.p.mass (P.support i) (e i) := by unfold BudgetPoint.mass; ring

end YM.Integration.WilsonLongContactWeighted
