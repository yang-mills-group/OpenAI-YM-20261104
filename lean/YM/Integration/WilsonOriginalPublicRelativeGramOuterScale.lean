import YM.Integration.WilsonOriginalPublicRelativeGramOuterMesh

/-! The homogeneous factor at a change of ruler acts on the whole measured
column. Each occupied name contributes it once on the normalized finite group. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramOuterScale
open Filter Finset Function Lattice RG Source PhysicalNext.Repeat.Legato
open XSpace XSpace.Expense XSpace.Cirrus Maxwell.Wick PowerSeries
open WilsonOriginalPublicRelativeGramOuterMesh (home move)
open WilsonOriginalPublicPivotReflected (board sampled evaluated)
open WilsonThermometerPositionTunedSlope (paid finite price)
open WilsonPositionProgramTrialThermalGrades (frozen)
open scoped Topology BigOperators Classical

theorem schedule {Z : Type*} {l : Filter Z} (M : Z → Mesh) (prior : Stretched l M)
    (T : Z → ℝ) (positive : ∀i, 0<T i) (b : ℕ)
    (wage : ∀ᶠ i in l, 1 ≤ T i ∧ T i*(M i).spacing^b ≤ 1) :
    Stretched l (fun i=>home (M i) (T i) (positive i)) := by
  constructor
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds prior.endpt
    · exact Eventually.of_forall fun i=>(home (M i) (T i) (positive i)).positive.le
    · filter_upwards [wage] with i h
      exact div_le_self (M i).positive.le h.1
  · intro k
    apply tendsto_atTop_mono' l _ (prior.pay ((b+1)*k))
    filter_upwards [wage] with i h
    have bound : (M i).spacing^(b+1) ≤ (M i).spacing/T i := by
      rw [le_div_iff₀ (positive i),pow_succ]
      have m := mul_le_mul_of_nonneg_right h.2 (M i).positive.le
      linarith only [show (M i).spacing^b*(M i).spacing*T i=
        T i*(M i).spacing^b*(M i).spacing by ring, m]
    change (M i).spacing^((b+1)*k)*sides M i ≤ ((M i).spacing/T i)^k*sides M i
    rw [pow_mul]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (pow_nonneg (M i).positive.le _) bound k)
      (counted M i).le

variable {G:Gauge} {n:ℕ}(R : Run G)(W : Initialize G)(d : Fin n → ℕ)
  (v : (i:Fin n) → (R.family.labels.level (d i)).Coeff)

theorem held (c : Fin n → ℂ)(X : Sample n)(S : Finset (Fin n)) :
    board R W d (fun i=>c i • v i) X S =
      C (∏i:S,c i) * board R W d v X S := by
  classical
  unfold WilsonOriginalPublicPivotReflected.board paid
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro b _
  simp only [price,frozen,Pi.smul_apply,smul_eq_mul,map_mul,Finset.prod_mul_distrib,map_prod,
    mul_assoc]

theorem value (c : ℂ)(q : ℕ)(g : ℝ)(Y : PowerSeries ℂ) :
    evaluated q g (C c * Y)=c*evaluated q g Y := by
  unfold evaluated
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro i _
  rw [coeff_C_mul]
  ring

theorem filed {L:Type*}[Fintype L](X:L → Sample n)(μ:L → ℂ)(T:ℝ)(pos:0<T)
    (c:Fin n → ℂ)(S:Finset (Fin n))(q:ℕ)(u:ℝ) :
    sampled R W d (fun i=>c i • v i) (fun x=>move T pos (X x)) μ S q u =
    (∏i:S,c i)*sampled R W d v X μ S q u := by
  unfold sampled
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro i _
  rw [held R W d v, WilsonOriginalPublicRelativeGramOuterMesh.ordinary, value]
  ring

end YM.Integration.WilsonOriginalPublicRelativeGramOuterScale
end
