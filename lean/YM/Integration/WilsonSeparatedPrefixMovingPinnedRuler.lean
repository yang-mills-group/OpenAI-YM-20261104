import YM.Integration.WilsonSeparatedPrefixMovingPinnedContrast
import YM.Integration.WilsonMovingForkSharpPhysicalRuler

/-! The common exterior engineering factor multiplies the full signed cutoff contrast. -/
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingPinnedRuler
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonSeparatedPrefixMovingCalendar (epoch window)
open WilsonSeparatedPrefixMovingLateLaw (whole)
open WilsonSeparatedPrefixMovingWages (coupon)
open WilsonSeparatedPrefixMovingOwnDate (fee)
open WilsonCoeffUV.Cosmos.Polestar
open WilsonIndependentMovingRosterAllFineSeats (Elected Named)
open scoped BigOperators Topology Classical
local notation "C" => Credit.leanC
variable {G:Gauge}{h D k n height seats:ℕ}{H:Hol G}{F:Labels.Frame G h}{T:SectionData F}{p:h<D}

open MeasureTheory
open scoped SchwartzMap ContDiff
open WilsonSeparatedPrefixMovingJointSpectrum (Euclid)
open WilsonSeparatedPrefixMovingJointWaves (sheet)
open WilsonSeparatedPrefixMovingJointExpansion (coefficient angle)
open WilsonSeparatedPrefixMovingJointIntegral (signedRow)
open WilsonSeparatedPrefixMovingJointRows (bill)
open WilsonSeparatedPrefixMovingJointAddress (move)
open WilsonIndependentMatchedCoverProfile (word)
open WilsonMovingForkSharpMaster (Paid)
variable {a u e:ℕ}{v:Rails h k (u+a) e}
open WilsonSeparatedPrefixMovingRelativeMaster (Landed)
open WilsonMovingForkSharpProfile (full projected)
open WilsonMovingForkSharpIncome (gain)
open WilsonMovingForkSharpIntegral (chamber)
open WilsonSeparatedPrefixMovingSpectralSalary (salary)
open WilsonMovingForkSharpAxisIntegral (fare)
open WilsonMovingForkSharpAxisWave (tested)

open WilsonMovingForkSharpActualGram (Priced)
open WilsonSeparatedPrefixMovingCalendar (epoch)
open WilsonMovingForkSharpAxisCash (mass)
open WilsonMovingForkSharpReportClock (atFar)
open WilsonOlderFreshSoftCoverScalar (clock)
open WilsonMovingForkSharpBudget (allowance Earned)
open WilsonIndependentMovingRosterAllFineRead (Heard)
open WilsonMovingForkSharpGrades (row invoice Audited)


def tab (B a b:ℝ):ℝ:=B^4*B^((4:ℝ)+1/4)*(|a|+|b|)

theorem original (e:ℕ)(T L B a b:ℝ)(f:ℕ→ℝ)(measured:1 ≤ T)(exterior:1 ≤ L)(grouped:L/T ≤ B)
    (sold:Heard e 0 T ((T^5)⁻¹*a+T^(-((4:ℝ)+1/4))*b) f):
    let ρ:=L/T
    let contrast:=fun q=>ρ^4*f q
    Heard e 0 L (L^(-((4:ℝ)+1/4))*tab B a b) contrast ∧
      ∀g:ℝ,0 ≤ g → g ≤ 1 → ∀J:ℕ,
        ‖WilsonSeparatedPrefixMovingHighGrades.above J e g contrast‖ ≤
          (e+1:ℕ)*(g^(J+1)*(L^(-(4:ℝ))*tab B a b)):=by
  intro ρ contrast
  have tp:0<T:=lt_of_lt_of_le zero_lt_one measured
  have lp:0<L:=lt_of_lt_of_le zero_lt_one exterior
  have rp:0 ≤ ρ:=(div_pos lp tp).le
  have bp:0 ≤ B:=rp.trans grouped
  let θ:ℝ:=4+1/4
  have dec:(T^5)⁻¹ ≤ T^(-θ):=by
    calc
      (T^5)⁻¹=T^(-(5:ℝ)):=by rw [Real.rpow_neg tp.le];norm_num
      _ ≤ _:=Real.rpow_le_rpow_of_exponent_le measured (by norm_num [θ])
  have cap:T^(-θ) ≤ L^(-θ)*B^θ:=by
    simpa only [Real.one_rpow,mul_one] using WilsonMovingForkSharpPhysicalRuler.rescale T L 1 B θ tp lp zero_le_one (by norm_num [θ]) grouped
  have flat:0 ≤ tab B a b:=by unfold tab;positivity
  have a0:Heard e 0 L (L^(-θ)*tab B a b) contrast:=by
    apply WilsonSeparatedPrefixMovingBeforeRead.heard _ _ _ _ _ lp
    intro q hq
    have old:‖f q‖ ≤ (T^5)⁻¹*a+T^(-θ)*b:=by simpa only [pow_zero,inv_one,one_mul] using sold.1 q hq
    simp only [pow_zero,inv_one,one_mul]
    change ‖ρ^4*f q‖ ≤ _
    rw [norm_mul,Real.norm_of_nonneg (pow_nonneg rp _)]
    calc
      _ ≤ B^4*((T^5)⁻¹*a+T^(-θ)*b):=mul_le_mul (pow_le_pow_left₀ rp grouped _) old (norm_nonneg _) (pow_nonneg bp _)
      _ ≤ B^4*(T^(-θ)*|a|+T^(-θ)*|b|):=by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg bp _)
        apply add_le_add _ (mul_le_mul_of_nonneg_left (le_abs_self _) (Real.rpow_nonneg tp.le _))
        exact ((mul_le_mul_of_nonneg_left (le_abs_self a) (by positivity)).trans
          (mul_le_mul_of_nonneg_right dec (abs_nonneg a)))
      _ ≤ B^4*((L^(-θ)*B^θ)*(|a|+|b|)):=by rw [←mul_add];gcongr
      _= _:=by dsimp only [tab,θ];ring
  refine ⟨a0,?_⟩
  intro g gpos gmax J
  have tail:‖WilsonSeparatedPrefixMovingHighGrades.above J e g contrast‖ ≤
      (e+1:ℕ)*(g^(J+1)*(L^(-θ)*tab B a b)):=by
    simpa only [pow_zero,inv_one,one_mul] using (a0.2 g gpos gmax).2 J
  have dec': L^(-θ) ≤ L^(-(4:ℝ)) := Real.rpow_le_rpow_of_exponent_le exterior (by norm_num [θ])
  exact tail.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right dec' flat) (pow_nonneg gpos _)) (Nat.cast_nonneg _))
end YM.Integration.WilsonSeparatedPrefixMovingPinnedRuler
