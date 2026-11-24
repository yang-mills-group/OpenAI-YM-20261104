import YM.Integration.WilsonPhysicalStationFactoryGerm

/-! The signed entire finite Wilson row tested against one real detector.
The lower thermal legs keep their measured covariance even when the free row
vanishes. The upper legs use their own reported coefficient budget. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationWickFees
open Function RG Labels Source Lattice Wilson Next.Rank Next.Rank.East Next.Rank.Price
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open PhysicalNext.Repeat.Legato Trace.Physical.GermGraph
open WilsonPhysicalStationTableJump (pair)
open scoped BigOperators Classical
variable {I:Type*} [Fintype I]

theorem price (legs:I→ ℕ) (v err:I→ ℂ) (Q:ℕ) (P eps B:ℝ) (hp:1≤ P)
    (he:0≤ eps) (hb:0≤ B) (reserve:1≤ P*eps)
    (low:∀ a,legs a≤ Q→ ‖err a‖*P^Q ≤ B*P^(legs a)*eps)
    (high:∀ a,Q<legs a→ ‖err a‖≤ B) :
    ‖∑ a,v a*err a‖*P^Q ≤ (∑ a,‖v a‖*P^(legs a))*B*eps := by
  have pos : 0≤ P := zero_le_one.trans hp
  have one (a:I) : ‖err a‖*P^Q ≤ B*P^(legs a)*eps := by
    by_cases h:legs a≤ Q
    · exact low a h
    have hq:Q+1≤ legs a:=by omega
    have hP:P^Q≤ P^(legs a)*eps := calc
      P^Q ≤ P^Q*(P*eps) := le_mul_of_one_le_right (pow_nonneg pos _) reserve
      _ = P^(Q+1)*eps := by rw [pow_succ]; ring
      _ ≤ P^(legs a)*eps := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hp hq) he
    calc
      ‖err a‖*P^Q ≤ B*P^Q := mul_le_mul_of_nonneg_right (high a (by omega)) (pow_nonneg pos _)
      _ ≤ B*(P^(legs a)*eps) := mul_le_mul_of_nonneg_left hP hb
      _ = _ := by ring
  calc
    ‖∑ a,v a*err a‖*P^Q ≤ (∑ a,‖v a*err a‖)*P^Q :=
      mul_le_mul_of_nonneg_right (norm_sum_le _ _) (pow_nonneg pos _)
    _ = ∑ a,‖v a‖*(‖err a‖*P^Q) := by simp only [Finset.sum_mul,norm_mul,mul_assoc]
    _ ≤ ∑ a, (‖v a‖*P^(legs a))*B*eps := Finset.sum_le_sum fun a _ => calc
      _ ≤ ‖v a‖*(B*P^(legs a)*eps) := mul_le_mul_of_nonneg_left (one a) (norm_nonneg _)
      _ = _ := by ring
    _ = _ := by simp only [Finset.sum_mul]

variable {G:Gauge}(R:Run G){D:ℕ}(d:Fin (D+1))(N p j:ℕ)(o:Fin 2→ Cover)
variable (peer:R.family.label d) (Y:I→ R.family.label d)

theorem sum_read (v:I→ ℂ) :
    pair R d N p j o (∑ a,v a • Y a) peer =
      ∑ a,v a*pair R d N p j o (Y a) peer := by
  let M:=R.family.ensemble (N:=N) (p:=p) (fun _:Fin 2=>d.val)
    (fun i=>location R.family.S j N p (o i))
  let ear: R.family.label d→ₗ[ℂ]ℂ := M.toLinearMap ![0,peer] 0
  have read (x:R.family.label d) : ear x=pair R d N p j o x peer := by
    change M (Function.update (![0,peer]:Fin 2→ R.family.label d) 0 x)=M ![x,peer]
    congr 1; funext i; fin_cases i <;> simp [Function.update]
  rw [← read,map_sum]
  simp only [map_smul,smul_eq_mul]
  simp_rw [read]

theorem original (legs:I→ ℕ) (v born:I→ ℂ) (q Q:ℕ) (eligible:q≤ Q)
    (P eps A B:ℝ) (hp:1≤ P) (he:0≤ eps) (ha:0≤ A) (hb:0≤ B) (reserve:1≤ P*eps)
    (input:(∑ a,‖v a‖*P^(legs a)) ≤ A*P^q)
    (low:∀a,legs a≤ Q→ ‖pair R d N p j o (Y a) peer-born a‖*P^Q≤ B*P^(legs a)*eps)
    (high:∀a,Q<legs a→ ‖pair R d N p j o (Y a) peer-born a‖≤ B) :
    ‖pair R d N p j o (∑ a,v a • Y a) peer-∑ a,v a*born a‖ ≤ A*B*eps := by
  rw [sum_read,← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  apply le_of_mul_le_mul_right (a:=P^Q) _ (pow_pos (zero_lt_one.trans_le hp) _)
  refine (price legs v _ Q P eps B hp he hb reserve low high).trans ?_
  calc
    _ ≤ (A*P^q)*B*eps := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right input hb) he
    _ ≤ (A*P^Q)*B*eps := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hp eligible) ha) hb) he
    _ = _ := by ring

end YM.Integration.WilsonPhysicalStationWickFees
end
