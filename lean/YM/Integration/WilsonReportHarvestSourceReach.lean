import YM.Integration.WilsonMeasuredAdmission
import YM.FullVolume.Cross

/-! Site count of a traversed support at the authentic cutoff, with a separate payment for its earlier date. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportHarvestSourceReach
open Function Filter Real Lattice RG Wilson PhysicalNext.Repeat.Legato WilsonMeasuredAdmission
variable {G:Gauge}

def depth (A:Levels G)(c:ℝ)(p i:ℕ):ℕ:=⌈c*(mast A i)^p⌉₊

theorem cost (A:Levels G)(i p:ℕ){c:ℝ}(cp:0 ≤ c):
    let B:=(A.budget i).B
    ((depth A c p i*(4*B+2)+2*B+1:ℕ):ℝ) ≤ (10*(c+1)+5)*(mast A i)^(p+2):=by
  let x:=mast A i
  let B:=(A.budget i).B
  let D:=depth A c p i
  have one:1 ≤ x:=(mast_gt_one A i).le
  have p1:1 ≤ x^p:=one_le_pow₀ one
  have x2:1 ≤ x^2:=one_le_pow₀ one
  have xp:0 ≤ x^p:=zero_le_one.trans p1
  have l0:0 ≤ Real.log (A.clock.hatBeta i):=Real.log_nonneg (A.fits.delayed i).le
  have lc:Real.log (A.clock.hatBeta i) ≤ x:=by dsimp [x,mast,WilsonAdmissionScale.logarithm];linarith
  have bb:(B:ℝ) ≤ (Real.log (A.clock.hatBeta i))^2+1:=(Nat.ceil_lt_add_one (sq_nonneg _)).le
  have bb':(B:ℝ) ≤ 2*x^2:=by linarith only [bb,pow_le_pow_left₀ l0 lc 2,x2]
  have dd:(D:ℝ) ≤ (c+1)*x^p:=by
    have more:((D:ℕ):ℝ) ≤ c*x^p+1:=(Nat.ceil_lt_add_one (mul_nonneg cp xp)).le
    nlinarith only [more,p1]
  have housing:4*(B:ℝ)+2 ≤ 10*x^2:=by linarith only [bb',x2]
  have product: (D:ℝ)*(4*(B:ℝ)+2) ≤ ((c+1)*x^p)*(10*x^2):=
    mul_le_mul dd housing (by positivity) (mul_nonneg (by linarith only [cp]) xp)
  have extras:2*(B:ℝ)+1 ≤ 5*x^p*x^2:=by
    nlinarith only [bb',x2,mul_nonneg (sub_nonneg.mpr p1) (sq_nonneg x)]
  change ((D*(4*B+2)+2*B+1:ℕ):ℝ) ≤ (10*(c+1)+5)*x^(p+2)
  push_cast
  rw [pow_add x p 2]
  nlinarith only [product,extras]

def elapsed (S:Schedule)(m j:ℕ):ℝ:=S.scale j-S.scale m

theorem mesh (S:Schedule)(m j:ℕ):Real.exp (elapsed S m j)=S.a m/S.a j:=by
  have unit (i:ℕ):Real.exp (S.scale i)=(S.a i)⁻¹:=Real.exp_log (inv_pos.mpr (S.a_pos i))
  rw [elapsed,Real.exp_sub,unit,unit]
  field_simp [(S.a_pos m).ne',(S.a_pos j).ne']

def reach (A:Levels G)(c t:ℝ)(m j:ℕ):ℕ:=depth A c 1 j+depth A (t*elapsed A.S m j) 0 j

end YM.Integration.WilsonReportHarvestSourceReach
