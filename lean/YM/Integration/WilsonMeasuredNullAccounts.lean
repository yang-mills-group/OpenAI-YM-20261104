import YM.Integration.WilsonMeasuredSectionCorrection
import YM.Extra.SOURCE_HISTORIES.LocalDebt

/-! Individual Ward-null regular rows and their wrapped primary account on the actual carrier. -/
noncomputable section
namespace YM.Integration.WilsonMeasuredNullAccounts
open Labels Lattice Wilson RG Source Trace.Physical Trace.Physical.Germ Extra.Histories
open scoped Classical

variable {G:Gauge} {n:Side} {d:ℕ} (F:Frame G d) (Y:Hol G) (o:Site n)
  (W:Rep G n) (P:Coefficient F n)

theorem atoms {κ b:ℝ} (shape:P.Format o Y W) (paid:P.remBound o W κ b) :
    ∃ (a c:ℝ) (s h:ℕ→ℝ), 0≤a ∧ 0≤c ∧ a+c≤b ∧ 0<κ ∧
      SumBudget (fun i=>W.p.mass (P.support i) (s i)) a ∧
      (∀ i,RegFit W o d Y (P.support i) (P.regular i) ∧
        W.p.supBounds o (P.support i) (P.regular i) (s i)) ∧
      SumBudget (fun i=>W.p.mass (W.activities.forced i).support (h i)) (κ*c) ∧
      ∀ i,0≤h i ∧ ∀ U,‖P.forced i U‖≤h i :=by
  obtain ⟨a,c,ha,hc,total,charge,⟨s,regular,sup⟩,⟨h,hard,whole⟩⟩:=paid
  exact ⟨a,c,s,h,ha,hc,total,charge,regular,fun i=>⟨⟨shape.smooth i,shape.origin i,shape.identity_null i,
    shape.projects i⟩,sup i⟩,hard,whole⟩

theorem wrapped {κ b:ℝ} (shape:P.Format o Y W) (paid:P.remBound o W κ b)
    (order:d≤W.p.order) (power:d≤W.p.power) (null:projection F Y W.p.threshold o P=0) :
    P.x = -(∑' i, if Nonwrapping (P.support i) o then 0 else vector F Y W.p.threshold o (P.regular i)) ∧
    ‖P.x‖ ≤ (germ_close F Y).choose * wraps W.p n * b :=by
  have series: (∑' i,vector F Y W.p.threshold o (P.regular i)) =
      ∑' i, if Nonwrapping (P.support i) o then 0 else vector F Y W.p.threshold o (P.regular i):=by
    apply tsum_congr
    intro i
    by_cases inside:Nonwrapping (P.support i) o
    · simpa only [if_pos inside] using short_vector F Y shape order inside
    · simp only [if_neg inside]
  constructor
  · rw [←series];exact eq_neg_of_add_eq_zero_left null
  · have cost:=(germ_close F Y).choose_spec.2 W P shape paid order power
    simpa only [null,zero_sub,norm_neg] using cost

end YM.Integration.WilsonMeasuredNullAccounts
end
