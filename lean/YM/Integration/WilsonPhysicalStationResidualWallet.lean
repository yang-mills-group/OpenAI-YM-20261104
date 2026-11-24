import YM.Integration.WilsonPhysicalStationDirectedRead

/-! A rank-Q physical detector after subtracting the measured lower column.
Only the earlier adjoint Born row of that rank survives in the second sum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationResidualWallet
open Fintype Finset
open scoped Classical BigOperators
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

theorem original (τ:ι→ℕ) (a:ι) (c G:ι→ℂ) (χ y:ℂ) (Q:ℕ)
    {t J g p A E B:ℝ} (gate:0 ≤ t) (live:0 ≤ p) (pos:0 ≤ E) (cash:0 ≤ B)
    (source:t*‖χ‖*p^(τ a) ≤ A*J)
    (coef:∀ i, t*‖c i-χ*(Pi.single a (1:ℂ):ι→ℂ) i‖*p^(τ i) ≤ g*J)
    (physics:‖y-∑ i,c i*G i‖*p^Q ≤ B*E*∑ i,‖c i‖*p^(τ i))
    (foreign:∀ i,τ i≠Q→G i=0) :
    t*‖y-χ*G a‖*p^Q ≤ J*(B*E*(A+(card ι:ℝ)*g)+g*∑ i,‖G i‖) := by
  classical
  let entry:=fun i=>χ*(Pi.single a (1:ℂ):ι→ℂ) i
  let rest:=fun i=>c i-entry i
  have restore (i): rest i+entry i=c i:=sub_add_cancel .. 
  have summand (i):t*‖c i‖*p^(τ i) ≤ g*J+t*‖entry i‖*p^(τ i):=by
    have first:=norm_add_le (rest i) (entry i)
    rw [restore] at first
    have b:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left first gate) (pow_nonneg live (τ i))
    exact b.trans ((le_of_eq (by ring : t*(‖rest i‖+‖entry i‖)*p^(τ i)=
      t*‖rest i‖*p^(τ i)+t*‖entry i‖*p^(τ i))).trans (add_le_add (coef i) le_rfl))
  have bill: t*(∑ i,‖c i‖*p^(τ i))  ≤  ((card ι:ℝ)*g+A)*J:=by
    rw [mul_sum]
    simp_rw [←mul_assoc]
    apply (sum_le_sum (fun i _=>summand i)).trans
    rw [sum_add_distrib,sum_const,card_univ,nsmul_eq_mul]
    have eq:(∑ i,t*‖entry i‖*p^(τ i))=t*‖χ‖*p^(τ a):=by
      rw [Finset.sum_eq_single a]
      · simp [entry]
      · intro i _ hi
        simp [entry,Pi.single_eq_of_ne hi]
      · simp
    rw [eq,add_mul, mul_assoc (card ι:ℝ) g J]
    exact add_le_add le_rfl source
  have unit:(∑ i,entry i*G i)=χ*G a:=by
    rw [Finset.sum_eq_single a]
    · simp [entry]
    · intro i _ hi; simp [entry,Pi.single_eq_of_ne hi]
    · simp
  have turn:(∑ i,c i*G i)-χ*G a=∑ i,rest i*G i:=by
    rw [←unit,←sum_sub_distrib]
    exact sum_congr rfl (fun i _=>by dsimp [rest];ring)
  have band (i):t*‖rest i*G i‖*p^Q ≤ g*J*‖G i‖:=by
    by_cases liveRank:τ i=Q
    · rw [norm_mul,←liveRank]
      calc
        _=t*‖rest i‖*p^(τ i)*‖G i‖:=by ring
        _ ≤ _:=mul_le_mul_of_nonneg_right (coef i) (norm_nonneg _)
    · simp [foreign i liveRank]
  have index:t*‖∑ i,rest i*G i‖*p^Q ≤ g*J*∑ i,‖G i‖:=by
    have sumNorm:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (norm_sum_le (Finset.univ : Finset ι) (fun i=>rest i*G i)) gate) (pow_nonneg live Q)
    apply sumNorm.trans
    rw [mul_sum,sum_mul,mul_sum]
    exact sum_le_sum (fun i _=>band i)
  have size:=add_le_add (mul_le_mul_of_nonneg_left physics gate) index
  have norm:=norm_add_le (y-∑ i,c i*G i) ((∑ i,c i*G i)-χ*G a)
  rw [sub_add_sub_cancel] at norm
  rw [turn] at norm
  calc
    _ ≤ t*(‖y-∑ i,c i*G i‖+‖∑ i,rest i*G i‖)*p^Q:=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left norm gate) (pow_nonneg live Q)
    _=t*(‖y-∑ i,c i*G i‖*p^Q)+t*‖∑ i,rest i*G i‖*p^Q:=by ring
    _ ≤ _:=size.trans (calc
      _=B*E*(t*∑ i,‖c i‖*p^(τ i))+g*J*∑ i,‖G i‖:=by ring
      _ ≤ B*E*(((card ι:ℝ)*g+A)*J)+g*J*∑ i,‖G i‖:=
        add_le_add (mul_le_mul_of_nonneg_left bill (mul_nonneg cash pos)) le_rfl
      _=_:=by ring)

end YM.Integration.WilsonPhysicalStationResidualWallet
end
