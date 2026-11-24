import YM.MS.Tone.Egal
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
/-!
# Normalization on the momentum torus fundamental domain

Use high cost Domain `Landau`. ∆ identity and alias curvature. Lebesgue Pi.
    Cube closed vs open boundaries irrelevant. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Tone
open Function Filter Set Finset Plane Koszul Cylinder Lab Lattice Native Landau Momentum
open MeasureTheory Real
open Complex (I)
open scoped Topology ContDiff

def μzone : Measure QP := (covMeasure Axis).restrict (firstZone Axis)
lemma inside_i (q:QP): q∈firstZone Axis ↔ ∀ i:Axis, |q i|≤π:= by
   rw [firstZone,Metric.mem_closedBall,dist_zero_right]; exact pi_norm_le_iff_of_nonneg Real.pi_pos.le
def cap : Measure ℝ:= volume.restrict (Set.Icc (-π) π)
instance volcap : IsFiniteMeasure cap:= by unfold cap; constructor; rw [Measure.restrict_apply_univ]; exact isCompact_Icc.measure_lt_top
instance voll : IsFiniteMeasure μzone := by letI : ProperSpace QP:= FiniteDimensional.proper ℝ QP; constructor; rw [μzone,Measure.restrict_apply_univ]; exact (isCompact_closedBall _ _).measure_lt_top
lemma μview : μzone= ENNReal.ofReal ((2*π)^4)⁻¹ • Measure.pi (fun _=> cap) := by
    unfold μzone covMeasure; rw [Measure.restrict_smul]; congr 1
    rw [show firstZone Axis=Set.pi Set.univ (fun _=> Set.Icc (-π) π) by ext x; simp_rw [inside_i,Set.mem_pi,Set.mem_univ,true_imp_iff, abs_le]; rfl]
    exact Measure.restrict_pi_pi ..

def musical (x:ℤ)(z:ℝ): ℂ:= Complex.exp ((x:ℂ)*Complex.I*z)
lemma aria (x:ℤ) : (∫ z,musical x z ∂cap) = if x=0 then 2*(π:ℂ) else 0 := by
    have he (z:ℝ) : (x:ℂ)*I*z=(x*(z:ℝ):ℝ)*(Complex.I:ℂ):= by push_cast; ring
    unfold cap musical; rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -π≤π)]; by_cases hx:x=0; subst x; simp; ring -- simplify
    rw [integral_exp_mul_complex, if_neg hx];
    · simp_rw [he,Complex.exp_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cos]; rw [mul_neg,cos_neg,sin_neg,sin_int_mul_pi]; simp
    exact mul_ne_zero (by exact_mod_cast hx) Complex.I_ne_zero
lemma choir (x:Cover) : (∫ p,bill p (embed x) ∂μzone)= if x=0 then 1 else 0:= by
    have hh (p:QP): bill p (embed x) = ∏ i: Axis,musical (x i) (p i):= by
       unfold bill embed pairing musical; push_cast; simp only [Finset.mul_sum,Complex.exp_sum]; apply Finset.prod_congr rfl; intro j _; congr 1; ring
    simp_rw [hh]; rw [μview,integral_smul_measure, integral_fintype_prod_eq_prod (f:=fun i=>musical (x i))]; simp_rw [aria]; split
    · subst x; rw [ENNReal.toReal_ofReal (by positivity),Complex.real_smul]; simp [Axis]
    rename_i hx; have ht : ∃ i:Axis,x i≠0:= Classical.byContradiction fun h=> hx (funext fun i=> Classical.byContradiction fun he=> h ⟨i,he⟩)
    obtain ⟨i,hi⟩:= ht; rw [Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi),smul_zero]
lemma choir_pair {a b: Atom Axis}(hb:offset a=offset b)(x y:Cover): (∫ p:QP,bill p (embed x+offset a)*bill (-p) (embed y+offset b) ∂μzone)= if x=y then 1 else 0 := by
   have he p:bill p (embed x+offset a)*bill (-p) (embed y+offset b)=bill p (embed (x-y)):= by
      rw [opp,← Tone.inverse,hb, ← rightadd, neg_add, emb_sub]; congr 1; abel
   simp_rw [he]; simp only [choir, sub_eq_zero] -- check
end YM.MS.Tone
