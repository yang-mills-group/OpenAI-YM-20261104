import YM.Integration.WilsonMaxwellThermometerNominatedTests

/-! Independent incoming source amplitudes act multiplicatively on each
occupied subset before the exponential or the connected logarithm. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerNominatedAlgebra
open Function Lattice RG Wilson Precision Tree Laurent
open FormalBulk08 Flat Mesa Next.Free Stationary
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open scoped Classical BigOperators

variable {I U E:Type} [DecidableEq I] {D:I→ℕ} {G:Gauge}
def pay (a:I→ℝ) (S:Finset I) : ℝ := ∏i∈S,a i

theorem separate (a:I→ℝ){J S:Finset I}(h:J⊆S) : pay a J*pay a (S\J)=pay a S := by
  unfold pay
  rw [mul_comm,Finset.prod_sdiff h]

private theorem stirred [AddCommGroup E] [Module ℝ E] {r:ℕ} (x:ℝ) (P:Ten E U r) :
    swirl (x • P)=x • swirl P := by
  unfold Blue.swirl
  rw [smul_comm x (Fintype.card (Equiv.Perm (Fin r)):ℝ)⁻¹]
  congr 1
  rw [Finset.smul_sum]
  rfl

private theorem cobbed {J S:Finset I} (h:J⊆S) {i j:ℕ} (c d:ℝ)
    (P:Ten (Pen D J) U i) (Q:Ten (Pen D (S\J)) U j) (r:ℕ) :
    cobT h (c • P) (d • Q) r=(c*d) • cobT h P Q r := by
  funext x
  by_cases join:i+j=r
  · simp only [cobT,dif_pos join,Pi.smul_apply,map_smul,
      smul_apply,smul_smul,mul_comm d c]
  · simp [cobT,join]

private theorem paired {J S:Finset I} (h:J⊆S) (c d:ℝ)
    (P:Gen (Pen D J) U) (Q:Gen (Pen D (S\J)) U) :
    cob h (c • P) (d • Q)=(c*d) • cob h P Q := by
  funext r
  unfold Mark.cob
  rw [Pi.smul_apply]
  rw [←stirred,Finset.smul_sum]
  apply congrArg Blue.swirl
  apply Finset.sum_congr rfl
  intro z _
  exact cobbed h c d (P z.1) (Q z.2) r

private theorem weighted {J S:Finset I} (h:J⊆S) (c d:ℝ)
    (P:Pal (Pen D J) U) (Q:Pal (Pen D (S\J)) U) :
    foam h (c • P) (d • Q)=(c*d) • foam h P Q := by
  funext r
  simp only [foam,Pi.smul_apply,paired,Finset.smul_sum]

theorem joined {J S:Finset I} (h:J⊆S) (c d:ℝ)
    (P:Era G (Pen D J)) (Q:Era G (Pen D (S\J))) :
    waxV h (c • P) (d • Q)=(c*d) • waxV h P Q :=
  Prod.ext (funext fun n=>weighted h c d (P.1 n) (Q.1 n)) (weighted h c d P.2 Q.2)

def scaled (a:I→ℝ) (M:family G D) : family G D := fun S=>pay a S • M S

theorem exponential (a:I→ℝ) (M:family G D) (S:Finset I) :
    levelsO (scaled a M) S=pay a S • levelsO M S := by
  induction S using Finset.strongInductionOn
  case _ S ih =>
    by_cases zero:S=∅
    · subst S; simp [empty_level,pay]
    rw [levelsO,dif_neg zero,levelsO,dif_neg zero,smul_comm (pay a S) (S.card:ℝ)⁻¹]
    congr 1
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro J _
    by_cases hl:J⊆S∧J≠∅
    · rw [dif_pos hl,dif_pos hl,ih _ (sh_k hl.1 hl.2),scaled,joined,separate a hl.1,smul_comm]
    · rw [dif_neg hl,dif_neg hl,smul_zero]

theorem logarithm (a:I→ℝ) (M:family G D) (S:Finset I) :
    reverseO (scaled a M) S=pay a S • reverseO M S := by
  induction S using Finset.strongInductionOn
  case _ S ih =>
    by_cases zero:S=∅
    · subst S; simp [empty_reverse]
    rw [reverseO,dif_neg zero,reverseO,dif_neg zero,smul_sub,scaled,
      smul_comm (pay a S) (S.card:ℝ)⁻¹]
    congr 2
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro J _
    by_cases h:J⊆S∧J≠S
    · rw [dif_pos h,dif_pos h,ih _ (lt_of_le_of_ne h.1 h.2),scaled,joined,separate a h.1,
        smul_comm]
    · rw [dif_neg h,dif_neg h,smul_zero]

end YM.Integration.WilsonMaxwellThermometerNominatedAlgebra
