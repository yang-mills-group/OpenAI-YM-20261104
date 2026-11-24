import YM.Integration.WilsonReportSeparatedMoments
import Mathlib.Analysis.PSeries

/-! Uniform chronological summation at the actual Wilson couplings on one
finite regulator. The numerical loss is two powers, with arbitrary slack. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredImpulseCalendar
open Filter Finset Real Lattice Wilson RG Pert.Asymptotics
open PhysicalNext.Repeat.Legato
open scoped Topology BigOperators
variable {G : Gauge}

private def speed (G : Gauge) := G.slopeConstant * Real.log 3

private theorem rising (hG : G.Simple) (A : Levels G) (i : ℕ) :
    A.clock.hatBeta i + speed G ≤ A.clock.hatBeta (i+1) := by
  have step := Real.log_le_log (by norm_num : (0:ℝ)<3) (show (3:ℝ)≤(A.S.block i).val by exact_mod_cast A.S.block_large i)
  have e := mul_le_mul_of_nonneg_left step (Gauge.slopeConstant_pos hG).le
  unfold Calendar.hatBeta speed; rw [show A.clock.schedule.scale (i+1)=A.S.scale i+Real.log (A.S.block i).val from A.S.scale_succ i]; linarith

private theorem monotone (g : G.Simple) (A : Levels G) : Monotone A.clock.hatBeta := by
  have v : 0 < speed G := mul_pos (Gauge.slopeConstant_pos g) (Real.log_pos (by norm_num))
  exact monotone_nat_of_le_succ fun i => by linarith only [rising g A i,v]

private theorem lower (g : G.Simple) (A : Levels G) (i : ℕ) : (i:ℝ)*speed G ≤ A.clock.hatBeta i := by
  induction i with
  | zero => simpa using (zero_lt_one.trans (A.fits.delayed 0)).le
  | succ i ih => rw [Nat.cast_succ,add_mul,one_mul]; linarith only [ih,rising g A i]

private theorem relative {C : Family G} (H : C.Makes) (hg : G.Simple) (N p k j : ℕ) (kj : k≤j) (jn : j≤N) :
    regulatorRun C N p j ≤ 2*regulatorRun C N p k := by
  have k0 := (H.wilson.represents N p k (kj.trans jn)).band
  have j0 := (H.wilson.represents N p j jn).band
  have mono := monotone hg C.path.levels kj
  have ha : 0 < C.path.β N p j := (half_pos (zero_lt_one.trans (C.path.levels.fits.delayed j))).trans_le j0.1
  have hb : 0 < C.path.β N p k := (half_pos (zero_lt_one.trans (C.path.levels.fits.delayed k))).trans_le k0.1
  have h : C.path.β N p k ≤ 4*C.path.β N p j := by linarith only [k0.2,j0.1,mono]
  have sq := Real.sqrt_le_sqrt h
  rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤4),show Real.sqrt 4=2 from by norm_num] at sq
  unfold regulatorRun; have jpos := Real.sqrt_pos.2 ha; have kpos := Real.sqrt_pos.2 hb
  rw [←one_div,← div_eq_mul_inv,(div_le_div_iff₀ jpos kpos)]; simpa using sq

private theorem debit {C : Family G} (H : C.Makes) (g : G.Simple) {t : ℝ} (ht : 0 ≤ t)
    (N p j : ℕ) (jp : 0<j) (jn : j≤N) :
    (regulatorRun C N p j ^ 2 : ℝ) ^ t ≤ (2/speed G)^t * (j:ℝ)^(-t) := by
  have v : 0 < speed G := mul_pos (Gauge.slopeConstant_pos g) (Real.log_pos (by norm_num))
  have j' : 0 < (j:ℝ) := by exact_mod_cast jp
  have band := (H.wilson.represents N p j jn).band.1
  have h := lower g C.path.levels j
  have beta : 0 < C.path.β N p j := (half_pos (zero_lt_one.trans (C.path.levels.fits.delayed j))).trans_le band
  have cost : regulatorRun C N p j^2 ≤ (2/speed G)/(j:ℝ) := by
    rw [regulatorRun,inv_pow,Real.sq_sqrt beta.le,←one_div,div_div,(div_le_div_iff₀ beta (mul_pos v j'))]
    nlinarith only [band,h]
  refine (Real.rpow_le_rpow (sq_nonneg _) cost ht).trans_eq ?_
  rw [Real.div_rpow (div_nonneg (by norm_num) v.le) j'.le,Real.rpow_neg j'.le,div_eq_mul_inv]

theorem purchased {C : Family G} (H : C.Makes) (g : G.Simple) (q : ℕ) {δ ε : ℝ}
    (hd : 0 < δ) (he : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ N p, k≤N →
      ∑ l ∈ range (N+1-k), regulatorRun C N p (k+l)^q * (regulatorRun C N p (k+l))^(2+δ) ≤
        ε * regulatorRun C N p k^q := by
  let t : ℝ := 1+δ/2
  have ht : 1<t := by dsimp [t]; linarith
  let b := fun i : ℕ => (2/speed G)^t * (i:ℝ)^(-t)
  have summ : Summable b := (Real.summable_nat_rpow.mpr (by linarith : -t < -1)).mul_left _
  have two : 0 < (2:ℝ)^q := by positivity
  have v : 0 < speed G := mul_pos (Gauge.slopeConstant_pos g) (Real.log_pos (by norm_num))
  have tails := (tendsto_sum_nat_add b).eventually_le_const (div_pos he two)
  filter_upwards [tails,eventually_gt_atTop 0] with k tail kp N p kn
  have g0 (j : ℕ) : 0≤regulatorRun C N p j := inv_nonneg.mpr (Real.sqrt_nonneg _)
  let c := 2^q * regulatorRun C N p k^q
  have cp : 0≤c := mul_nonneg two.le (pow_nonneg (g0 _) _)
  have step (l : ℕ) (hi : l ∈ range (N+1-k)) :
      regulatorRun C N p (k+l)^q * (regulatorRun C N p (k+l))^(2+δ) ≤ c*b (l+k) := by
    have jn : k+l≤N := by have := mem_range.mp hi; omega
    have h1 := pow_le_pow_left₀ (g0 _) (relative H g N p k (k+l) (by omega) jn) q
    rw [mul_pow] at h1
    apply mul_le_mul h1 _ (Real.rpow_nonneg (g0 _) _) cp
    have e : (regulatorRun C N p (k+l))^(2+δ) = ((regulatorRun C N p (k+l))^2:ℝ)^t := by
      rw [← Real.rpow_natCast (regulatorRun C N p (k+l)) 2,←Real.rpow_mul (g0 _)]; congr 1; dsimp [t]; ring
    rw [e]; simpa [b,Nat.add_comm] using debit H g (zero_lt_one.trans ht).le N p (k+l) (by omega) jn
  calc
    _ ≤ ∑ l ∈ range (N+1-k), c*b (l+k) := sum_le_sum step
    _ = c * ∑ l ∈ range (N+1-k),b (l+k) := (mul_sum ..).symm
    _ ≤ c * ∑' l,b (l+k) := by
      apply mul_le_mul_of_nonneg_left _ cp
      exact (summ.comp_injective (i:=fun i:ℕ => i+k) (by intro i j h; dsimp at h; omega)).sum_le_tsum _
        (fun l _ => mul_nonneg (Real.rpow_nonneg (div_nonneg (by norm_num) v.le) _) (Real.rpow_nonneg (by positivity) _))
    _ ≤ c*(ε/(2:ℝ)^q) := mul_le_mul_of_nonneg_left tail cp
    _ = _ := by dsimp [c]; field_simp

end YM.Integration.WilsonMeasuredImpulseCalendar
