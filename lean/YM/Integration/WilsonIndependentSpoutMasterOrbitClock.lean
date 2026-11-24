import YM.Integration.WilsonIndependentSpoutMasterObserved
import YM.Integration.WilsonIndependentSpoutMasterBareClocks
import YM.Integration.WilsonIndependentSpoutMasterOrbit
import YM.FormalBulk08.Series.Level

/-! Restoring the genuine finite inversion output in the measured coupling of its own fresh opening. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutMasterOrbitClock
open Finset PowerSeries PhysicalNext PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Embroider WilsonCoeffUV.Shard
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue WilsonCoeffUV.Power
open WilsonIndependentFittedMixedCash (embed)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open WilsonIndependentSpoutMasterReport (report)
open WilsonIndependentSpoutDoseBoundary (into)
open WilsonIndependentSpoutScalarLedger (ground)
open WilsonIndependentSpoutMasterObserved (observed)
open WilsonCoeffUV.Bank.PathCost
open scoped Classical BigOperators
variable {G:Gauge}

def measure (B:Cost)(Y:PowerSeries ℂ):PowerSeries ℂ:=
  Y.subst (embed B*PowerSeries.X)

theorem shares (B:Cost)(Y:PowerSeries ℂ)(i:ℕ):
  coeff i (measure B Y)=∑j∈range (i+1),coeff j Y*(coeff (R:=ℝ) (i-j) (B^j):ℂ):=by
  have zero:coeff 0 ((embed B)*PowerSeries.X)=0:=by simp [PowerSeries.coeff_zero_eq_constantCoeff]
  rw [measure,YM.FormalBulk08.Series.subst_coeff zero Y i i le_rfl]
  refine sum_congr rfl fun j hj=>?_
  have hit:j ≤ i:=Nat.le_of_lt_succ (mem_range.mp hj)
  rw [mul_pow,PowerSeries.coeff_mul_X_pow',if_pos hit,←map_pow]
  rfl

theorem real (B Y:Cost):measure B (embed Y)=embed (reel B Y):=by
  ext i
  rw [shares]
  change _=(coeff (R:=ℝ) i (reel B Y):ℂ)
  rw [reelQuote,Complex.ofReal_sum]; apply sum_congr rfl
  intro j _
  rw [Complex.ofReal_mul]
  rfl

theorem receipt (B:Cost)(Y Z:PowerSeries ℂ)(q:ℕ)(g w c:ℝ)(small:|g|≤1)
    (words:∀j≤q,‖coeff j Y-coeff j Z‖ ≤ w)
    (clock:∀i≤q,∀j≤q,‖coeff i (B^j)‖ ≤ c):
    ‖cash q g (measure B Y)-cash q g (measure B Z)‖ ≤
      (q+1:ℝ)*((q+1:ℝ)*(w*c)):=by
  have w₀:0≤w:=(norm_nonneg _).trans (words 0 (Nat.zero_le _))
  have c₀:0≤c:=(norm_nonneg _).trans (clock 0 (Nat.zero_le _) 0 (Nat.zero_le _))
  have localFee (i:ℕ)(hq:i ≤ q):‖coeff i (measure B Y)-coeff i (measure B Z)‖ ≤ (q+1:ℝ)*(w*c):=by
    rw [shares,shares,←sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑_j∈range (i+1), w*c:=by
        refine sum_le_sum fun j hj=>?_
        have jq: j ≤ q :=(Nat.le_of_lt_succ (mem_range.mp hj)).trans hq
        rw [←sub_mul,norm_mul,Complex.norm_real]
        exact mul_le_mul (words j jq) (clock (i-j) ((Nat.sub_le ..).trans hq) j jq) (norm_nonneg _) w₀
      _ ≤ _:=by
        simp only [sum_const,card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_succ hq) (mul_nonneg w₀ c₀)
  unfold WilsonPhysicalMarkedDefect.RawBank.cash
  rw [←sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑_i∈range (q+1),(q+1:ℝ)*(w*c):=by
      refine sum_le_sum fun i hi=>?_
      rw [←mul_sub,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right (pow_le_one₀ (abs_nonneg _) small) (norm_nonneg _)).trans
        ((one_mul _).le.trans (localFee i (Nat.le_of_lt_succ (mem_range.mp hi))))
    _ = _:=by simp

theorem posted (R:Run G)(simple:G.Simple)(K m v q:ℕ)(vm:v ≤ m)(mK:m ≤ K)(g w c:ℝ)
    (Z:PowerSeries ℂ)(Y:Era G ℝ)(small:|g|≤1)
    (words:∀i≤q,‖coeff i Z-coeff i (embed (into R.family.path.levels R.metals.O K v (ground Y)))‖≤w)
    (clock:∀i≤q,∀a≤q,‖coeff i ((relativeF R.family.path.levels R.metals.O K m (K-m))^a)‖≤c):
    ‖cash q g (measure (relativeF R.family.path.levels R.metals.O K m (K-m)) Z)-
      observed R.family.path.levels R.metals.O K m v q g Y‖≤(q+1:ℝ)*((q+1:ℝ)*(w*c)):=by
  have h:=receipt _ Z _ q g w c small words clock
  rw [real] at h
  have statement:=WilsonIndependentFittedRelativeClock.reported R.family.path.levels R.metals.O K m (K-m)
    (into R.family.path.levels R.metals.O K v (ground Y))
  rw [show m+(K-m)=K by omega,
    WilsonIndependentSpoutMasterReport.bare R.family.path.levels R.metals.O simple (RunFormalChain.fromRun R).receipt m K v vm mK] at statement
  rw [←statement] at h
  exact h

end YM.Integration.WilsonIndependentSpoutMasterOrbitClock
end
