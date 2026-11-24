import YM.WilsonCoeffUV.Vacuum.UV.Relation
import YM.Integration.WilsonLimitConstruction.FundedSpringWinterTensors

/-! Native fine/retuned coarse coupling, separately at every ordered
field tuple. This undoes the genuine chronological coupling change on
all positive-valence cover rows before any periodization or error price. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedSpringCoverRegrade
open Function Finset PowerSeries WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open PhysicalNext.Repeat.Legato Lattice Wilson RG
open scoped BigOperators Classical

def series {X : Type*} (P : Pal ℝ X) (l : ℕ) (z : Fin l → X) : Cost := mk fun i=>P i l z

def pull (B : Cost) (l : ℕ) (F : Cost) := reel B F*(B⁻¹)^l

theorem coefficient (B F : Cost) (l k : ℕ) :
    coeff k (pull B l F)=∑i∈range (k+1),coeff i F * coeff (k-i) (B^i*(B⁻¹)^l) := by
  unfold pull
  have h := filtered (show constantCoeff (reel B X)=0 by rw [reel_X]; simp) (shave F (k+1))
  rw [(h.mul (Equal.refl ((B⁻¹)^l) _)) k k.lt_succ_self,map_sum,Finset.sum_mul,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_mul (reel B),map_pow (reel B),reel_C,reel_X,
    show C (coeff i F)*(B*X)^i*(B⁻¹)^l = (C (coeff i F)*(B^i*(B⁻¹)^l))*X^i by ring,
    coeff_mul_X_pow',if_pos (by have h := mem_range.mp hi; omega),coeff_C_mul]

theorem registered {U : Type*} (B : Cost) (P : Pal ℝ U) (l : ℕ) (z : Fin l→U) :
    series (Blue.mix B P) l z=pull B l (series P l z) := by
  ext1 k
  rw [coefficient]
  simp only [series,coeff_mk,Blue.mix,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem inverse {f : Cost} (unit : constantCoeff f=1) (l : ℕ) (q : Cost) :
    pull (pace f) l (pull (back f) l q)=q := by
  let A := pace f
  let B := back f
  have one : reel A B*A=1 := chart_forward unit
  have hB : constantCoeff B≠0 := by rw [show constantCoeff B=1 from back_cc unit]; exact one_ne_zero
  have hA : constantCoeff A≠0 := by rw [show constantCoeff A=1 from pace_cc unit]; exact one_ne_zero
  have hn : reel A B≠0 := by
    intro h
    rw [h,zero_mul] at one
    exact zero_ne_one one
  have transport : reel A (B⁻¹)=A := by
    apply mul_left_cancel₀ hn
    rw [←map_mul,PowerSeries.mul_inv_cancel B hB,map_one]
    exact one.symm
  have identity : reel A (reel B q)=q := by
    calc
      _ = reel (chartB B A) q := DFunLike.congr_fun (reel_chart B A) q
      _ = q := by rw [show chartB B A=1 from chart_forward unit,reel_one]
  change (reel A (reel B q*(B⁻¹)^l))*(A⁻¹)^l=q
  rw [map_mul,map_pow,transport,identity,mul_assoc,←mul_pow,PowerSeries.mul_inv_cancel A hA,
    one_pow,mul_one]

theorem original {U : Type*} {f : Cost} (unit : constantCoeff f=1) (P : Pal ℝ U) :
    Blue.mix (pace f) (Blue.mix (back f) P)=P := by
  funext k l z
  have e : series (Blue.mix (pace f) (Blue.mix (back f) P)) l z=series P l z := by
    rw [registered,registered,inverse unit]
  simpa only [series,coeff_mk] using congrArg (coeff k) e

/-- The actual positive-valence native fine cover equals its funded
coarse-run tensor family regraded with the true inverse-temperature
series. This includes every cutoff and every grade. -/
theorem physical {G : Gauge} (R : Run G) (hG : G.Simple) (N m : ℕ) (hm : m<N) (k l : ℕ) :
    let A := R.family.path.levels
    let O := R.metals.O
    Blue.mix (pace (pitch A O N m)) (actionW A O N m) k (l+1)=freshet A O N m k (l+1) := by
  intro A O
  rw [conduct A O hm,ratioHigh,original (angle_tilt hG R.alloy.B.ratio hm)]
  simp [lop]

end YM.Integration.WilsonLimitConstruction.FundedSpringCoverRegrade
