import YM.Integration.WilsonRegisteredMayerRows
import YM.Integration.LocalComparisonInterface

/-! The original measured and requested norms have identical plaquette masks.
Previously issued directional and derivative estimates remain valid when
the predetermined finite request is reached. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredIntakeNorm
open Filter Lattice RG Pressure Tree Wilson Work.E03 RGLocalTaylor RGLocalTaylor.Insert
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}

theorem restrict {n:Side} {P Q:BudgetPoint} (threshold:Q.threshold=P.threshold)
    (order:Q.order≤P.order) (power:Q.power≤P.power)
    {S:Support n} {o:Site n} {f:Config G n→ℂ} {c:ℝ}
    (reg:P.Regular S f) (income:P.supBounds o S f c) :
    Q.Regular S f ∧ Q.supBounds o S f c:=by
  refine ⟨⟨reg.sites,reg.borel,reg.symmetry,?_,?_⟩,income.1,?_⟩
  · intro U health
    rw [threshold] at health
    exact (reg.smooth U health).of_le (by exact_mod_cast order)
  · intro U health A l short
    rw [threshold] at health
    exact reg.hasDerivs U health A l (short.trans_le order)
  · intro U health l size directions
    rw [threshold] at health
    apply income.2 U health l (size.trans order)
    intro a member e
    have original:=directions a member e
    rw [threshold] at original
    exact original.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (le_add_of_nonneg_right (Nat.cast_nonneg _)) power) P.threshold_pos.le)

theorem dated (R:Legato.Run G) {k N per f p:ℕ} {s:ℝ}
    (live:k≤N) (onset:R.family.ref (max f p)≤k) (Q:BudgetPoint)
    (record:LocalComparison.NormAt R.family k Q f p s):
    let P:=R.family.path.rep N per k
    Q.threshold=P.p.threshold ∧ Q.B=P.p.B ∧ Q.order≤P.p.order ∧ Q.power≤P.p.power:=by
  let P:=R.family.path.rep N per k
  have same:P.p=R.family.path.levels.budget k:=(R.makes.wilson.represents N per k live).vac
  have funded:=(R.makes.stages (max f p)).2 k onset
  refine ⟨record.threshold.trans (congrArg BudgetPoint.threshold same).symm,
    record.block.trans (congrArg BudgetPoint.B same).symm,?_,?_⟩
  · rw [same,record.order]
    exact (le_max_left f p).trans ((Nat.le_succ _).trans funded.1)
  · rw [same,record.distance]
    exact (le_max_right f p).trans funded.2

end YM.Integration.WilsonRegisteredIntakeNorm
