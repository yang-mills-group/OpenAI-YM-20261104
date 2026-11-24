import YM.Integration.WilsonOlderFreshSoftSocketStationDose

/-! Signed physical spending on every purchased face of a public cell. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketStationDosedCells
open Finset
open WilsonPositionThermometerConnected (value)
open WilsonMaxwellThermometerNominatedSecant (bill)
open WilsonOriginalTwoFlatRoseCellSum (Sale cost)
open WilsonOlderFreshSoftSocketStationDose (Mask stamp)
open scoped Classical BigOperators

def residual {O:Mask→ℂ}{read:ℂ}(sale:Sale O read)(amplitude:Fin 3→ℂ)(Q:Mask→ℂ):ℂ:=
  stamp amplitude univ*read-value Q-stamp amplitude univ*∑s:Mask,bill O sale.table s*sale.debit s

theorem node {O:Mask→ℂ}{read:ℂ}(sale:Sale O read)(amplitude:Fin 3→ℂ)(F Q:Mask→ℂ){B:ℝ}
    (issued:∀s:Mask,s.Nonempty→stamp amplitude s*sale.table s=F s)(funded:‖value F-value Q‖ ≤ B):
    ‖residual sale amplitude Q‖ ≤ ‖stamp amplitude univ‖*cost sale+B:=by
  have same:stamp amplitude univ*value sale.table=value F:=
    (WilsonOlderFreshSoftSocketStationDose.homogeneous amplitude sale.table).symm.trans
      (WilsonOlderFreshSoftSocketStationDose.occupied issued)
  have split:residual sale amplitude Q=stamp amplitude univ*
      (read-value sale.table-∑s:Mask,bill O sale.table s*sale.debit s)+(value F-value Q):=by
    unfold residual
    rw [←same];ring
  rw [split]
  apply (norm_add_le ..).trans
  rw [norm_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left sale.bound (norm_nonneg _)) funded

theorem collected {I:Type*}[Fintype I]{O:I→Mask→ℂ}{read:I→ℂ}(sale:∀i,Sale (O i) (read i))
    (amplitude:I→Fin 3→ℂ)(weight:I→ℂ)(F Q:I→Mask→ℂ){B L:ℝ}
    (mass:∑i:I,‖weight i‖ ≤ L)(nonneg:0 ≤ B)
    (issued:∀i s,s.Nonempty→stamp (amplitude i) s*(sale i).table s=F i s)
    (funded:∀i,‖value (F i)-value (Q i)‖ ≤ B):
    ‖∑i:I,weight i*residual (sale i) (amplitude i) (Q i)‖ ≤
      (∑i:I,‖weight i‖*(‖stamp (amplitude i) univ‖*cost (sale i)))+L*B:=by
  calc _ ≤ ∑i:I,‖weight i*residual (sale i) (amplitude i) (Q i)‖:=norm_sum_le ..
       _ ≤ ∑i:I,‖weight i‖*(‖stamp (amplitude i) univ‖*cost (sale i)+B):=by
         apply sum_le_sum;intro i _
         rw [norm_mul]
         exact mul_le_mul_of_nonneg_left (node (sale i) (amplitude i) (F i) (Q i) (issued i) (funded i))
           (norm_nonneg _)
       _ = (∑i:I,‖weight i‖*(‖stamp (amplitude i) univ‖*cost (sale i)))+(∑i:I,‖weight i‖)*B:=by simp only [mul_add,sum_add_distrib,sum_mul]
       _ ≤ _:=add_le_add le_rfl (mul_le_mul_of_nonneg_right mass nonneg)

end YM.Integration.WilsonOlderFreshSoftSocketStationDosedCells
end
