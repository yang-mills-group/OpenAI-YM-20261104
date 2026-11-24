import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Revenue

/-!
# Arbitrary-occurrence-order reserve for the actual second logarithm

Follow Height.completed from the E construction, but export also the *full*
beacon estimate. This allows cutting at higher internal occurrence order without
asking for any higher-order entrance delay; also useful if scaling grading by a
complex auxiliary parameter. No coupling analyticity of threshold tests (or even
of the unmasked payloads) is involved at this step.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01.Beacon
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Height
open ConnectedActivityE6.Blaze Blaze.March Captain Silica
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {R : RG.Rep G f} {μ q C' d v Y A b r B s α a i : ℝ} {k j : ℕ}
    {χ : Chi} {H : Cash W s μ L Q o α T R}

lemma one_le_beacon (hd : 1 ≤ grow G L s) (z : H.fragrances) : 1 ≤ beacon H z := by
  have hPos : 1 ≤ Real.exp (Q.ε * depth H z) := Real.one_le_exp (mul_nonneg Q.usable.le
    (sum_nonneg fun _ _=> H.positive_volume _))
  have ht : 0 ≤ Q.mark L μ s := H.laws.acquired.marked
  have hM : 1 ≤ Real.exp (Q.mark L μ s * overlap H z) := Real.one_le_exp (mul_nonneg ht
    (Nat.cast_nonneg _))
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hd) hM) hPos

lemma grade_le_beacon (hd : 1 ≤ grow G L s) (z : H.fragrances) :
    grow G L s ^ (Height.degree H z) ≤ beacon H z := by
  have hPos : 1 ≤ Real.exp (Q.ε * depth H z) := Real.one_le_exp (mul_nonneg Q.usable.le
    (sum_nonneg fun _ _=> H.positive_volume _))
  have ht : 0 ≤ Q.mark L μ s := H.laws.acquired.marked
  have hM : 1 ≤ Real.exp (Q.mark L μ s * overlap H z) := Real.one_le_exp (mul_nonneg ht
    (Nat.cast_nonneg _))
  have hz:= pow_nonneg (le_trans zero_le_one hd) (Height.degree H z)
  exact (le_mul_of_one_le_right hz hM).trans (le_mul_of_one_le_right
    (mul_nonneg hz (le_trans zero_le_one hM)) hPos)

variable (N : Captain H j C' d v Y A b r B q k χ)

lemma money_nonneg (z : H.fragrances) (n : ℕ) : 0 ≤ N.markΦ z n :=
  mul_nonneg (pow_nonneg (by unfold shiftG; positivity) _) (N.pvc _)

variable (hd : 1 ≤ grow G L s) (heavy : Heavy N.conduit) (n : ℕ)
    (ht : Armada Q L μ a s i B j k)
    (hs : degreePrice (radiusB s) (grow G L s*(Q.costs L μ 1 s 0).rootHit) Q.δ ≤ 1/2)
    (hp : degreePrice (radiusB s) (grow G L s*salary Q L μ B s j k) i ≤ 1/2)
include N hd heavy n ht hs hp
/-- Strengthen `Height.completed` to the full beacon moment, with the same cost
before withdrawing the 3-grade gain. Hypotheses will be obtained on actual steps
from Height.Rich and the construction's Skill purchase. -/
lemma absolute :
    Ac.Hit (Captain.reachability (H:=H)) (radiusB s) (fun z=>beacon H z * N.markΦ z n) a
        (collars G i s j n*(grow G L s*salary Q L μ B s j k*(1-1/2)⁻¹)) := by
  intro x
  have hy:= log_hit_tail _ _ _ H.testS (Height.stable N hd heavy i a ht.delta ht.little ht.earned hs hp)
    (add_nonneg ht.gain ht.delta.le) 0 x
  simp only [pow_zero,mul_one] at hy
  have he : 0 ≤ shiftG s := by unfold shiftG; positivity
  have hv : 0 ≤ collars G i s j n := by
    unfold collars Reserves.polyPrice
    have hi := ht.delta
    positivity
  have hz (z) : 0 ≤ beacon H z * N.markΦ z n := mul_nonneg
    (le_trans zero_le_one (one_le_beacon hd z)) (money_nonneg N z n)
  have hh := budget_scale hv hy
  refine budget_mono hh (fun z => ?_) fun z=>?_ 
  · dsimp only
    split
    next=> exact mul_nonneg (hz z) (Real.exp_pos _).le
    exact le_rfl
  dsimp only; split
  next hx =>
    rw [if_pos (show 0 ≤ z.fst ∧ x∈unionOf H.smallAt z.snd from ⟨Nat.zero_le _,hx⟩),Height.wield N]
    let c:ℝ:=coverNumber (radiusB s) (reachability (H:=H) z)
    have hg:0 ≤ c:= Nat.cast_nonneg _
    let D:= beacon H z
    have hD : 0 ≤ D := le_trans zero_le_one (one_le_beacon hd z)
    change D * ((shiftG s*(1+c))^(n*j)*N.design z) *Real.exp (a*c) ≤
      collars G i s j n *(D*N.design z*Real.exp ((a+i)*c))
    rw [mul_pow,add_mul a i c,Real.exp_add]
    refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (polynomial_cost ht.delta hg _) (pow_nonneg he _))
        (N.pvc z)) hD) (Real.exp_pos _).le).trans_eq ?_
    unfold collars Reserves.polyPrice; ring
  exact hh.1 z

/-- Pay any exceptional-or-high-order family whose beacon gain was shown,
leaving the same address basis. -/
lemma select (ex : H.fragrances → Prop) (K : ℝ) (hk : 0 < K)
    (gain : ∀ z, ex z → K ≤ beacon H z) :
    Ac.Hit (Captain.reachability (H:=H)) (radiusB s) (fun z => if ex z then N.markΦ z n else 0)
      a (K⁻¹*(collars G i s j n*(grow G L s*salary Q L μ B s j k*(1-1/2)⁻¹))) := by
  intro x
  have hh := budget_scale (inv_pos.mpr hk).le (absolute N hd heavy n ht hs hp x)
  refine budget_mono hh (fun z=>?_) fun z=>?_
  · dsimp only; split
    next hx =>
      split
      next=> exact mul_nonneg (money_nonneg N z n) (Real.exp_pos _).le
      simp
    exact le_rfl
  dsimp only
  split
  next hx =>
    split
    next he =>
      apply le_trans (b := K⁻¹ * (K * N.markΦ z n * Real.exp (a * coverNumber (radiusB s) (reachability z))))
        ?_ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
         (mul_le_mul_of_nonneg_right (gain z he) (money_nonneg N z n))
         (Real.exp_pos _).le) (inv_pos.mpr hk).le)
      apply le_of_eq
      rw [mul_assoc K, inv_mul_cancel_left₀ hk.ne']
    next => rw [zero_mul]; simpa only [if_pos hx] using! hh.1 z
  simp

end YM.RG01.Beacon
