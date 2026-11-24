import YM.QuadraticLocal.Poetry.Friend
import YM.Integration.WilsonMovingMentorHeader

/-! A single before-period floor on the original registered covariance seeds bounds
the spatial exponent of every subsequently submitted finite original curvature row. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingMentorRootRadius
open RG RG.Supply Push Push.PriceCompiler Precision PhysicalNext PhysicalNext.ThroughLaunch Org Next.Foundations
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato AllOrder.Floe.Step QuadraticLocal Finset
open scoped Classical BigOperators

variable {G : Gauge} {M : Metals G} {D : Rolls M.p} {P : Protection D}
  (r : PlanV.Roots (G:=G) M.p.profile M.K M.p.kernel) (ψ : ℕ → ℕ)

def Income (W : Delays P) : Prop := ∀ j y : ℕ, y ≤ j → ∀ k : ℕ, k ≤ y →
  Real.exp ((y+1:ℝ)*|Poetry.Agenda.seed r ψ k y|) ≤ W.betaEntry j

theorem accrued (W : Delays P) :
    ∃ V : Delays P, DelayLe W V ∧ ∀ Z : Delays P, DelayLe V Z → Income (M:=M) r ψ Z := by
  let cost (y k : ℕ) := Real.exp ((y+1:ℝ)*|Poetry.Agenda.seed r ψ k y|)
  let total (j : ℕ) := ∑ y ∈ range (j+1), ∑ k ∈ range (y+1), cost y k
  have pos (y k : ℕ) : 0 ≤ cost y k := Real.exp_nonneg _
  have member (j y k : ℕ) (hy : y ≤ j) (hk : k ≤ y) : cost y k ≤ total j := by
    have one : cost y k ≤ ∑ a ∈ range (y+1), cost y a :=
      single_le_sum (fun v _ => pos y v) (mem_range.mpr (Nat.lt_succ_of_le hk))
    exact one.trans (single_le_sum (f := fun v : ℕ => ∑ a ∈ range (v+1), cost v a)
      (fun v _=> sum_nonneg (fun a _=> pos v a))
      (mem_range.mpr (Nat.lt_succ_of_le hy)))
  let V : Delays P := {W with betaEntry := fun j=>max (W.betaEntry j) (total j)}
  refine ⟨V,⟨fun j=>le_max_left _ _,le_rfl,le_rfl,le_rfl⟩,?_⟩
  intro Z bought j y hy k hk
  exact (member j y k hy hk).trans ((le_max_right _ _).trans (bought.beta j))

theorem at_date (R : Run G)
    (r' : PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (bought : Income (M:=R.metals) r' ψ R.alloy.delay) (m k : ℕ)
    (filed : k ≤ R.alloy.B.a.clock.J m) :
    Real.exp ((R.alloy.B.a.clock.J m+1:ℝ)*|Poetry.Agenda.seed r' ψ k (R.alloy.B.a.clock.J m)|)
      ≤ R.alloy.B.a.clock.hatBeta m :=
  (bought _ _ (step_paid R.alloy.B.a m).1 k filed).trans (R.alloy.B.valid.pays m)

end YM.Integration.WilsonMovingMentorRootRadius
end
