import YM.Integration.WilsonMovingForkSharpNamedPlate

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkSharpNearRoom
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
open WilsonSeparatedPrefixMovingTested44 (inner ranks)
open WilsonSeparatedPrefixMovingRelativeMaster (Landed)
open WilsonCoeffUV.Mer.Patrol (BayV)
open WilsonIndependentExactPlate (Requests)
open WilsonIndependentEvenPassport (old count)
open RegulatorIR RegulatorIR.Ledger
variable {D' j extra:ℕ}
open WilsonMovingForkSharpUniform (Earned)
open WilsonSeparatedPrefixMovingSpectralSalary (salary)
open Finset
def fence (arms:Fin (n+1)  →  SealR G)(α:Wilt arms)(U gap:ℝ):ℝ:=
  1+|U|+gap⁻¹+∑i,|(α i).radius|

theorem original (R:Realm G (e+1) C)(m:ℕ)(arms:Fin (n+1)  →  SealR G)(α:Wilt arms)(B:Fin (n+1)  →  ℝ)
    (U gap:ℝ)(price:R.y m  ≤  U)(clear:0<gap)(seats:∀i j,i≠j  →  ClearDay (α i) (α j) gap)
    (stock:∀i,Amplitude (α i) (B i)):
    let Z:=fence arms α U gap
    PadRank R m m Z ∧ Bough arms α (paceT R.draws.S m m) Z B:=by
  intro Z
  have root:0  ≤  ∑i,|(α i).radius|:=sum_nonneg fun _ _=>abs_nonneg _
  have cash:0  ≤  gap⁻¹:=(inv_pos.mpr clear).le
  have room:1  ≤  Z:=by dsimp only [Z,fence];linarith only [abs_nonneg U,cash,root]
  have fit:R.y m  ≤  Z:=by dsimp only [Z,fence];linarith only [price,le_abs_self U,cash,root]
  have inside:gap⁻¹  ≤  Z:=by dsimp only [Z,fence];linarith only [abs_nonneg U,root]
  have zp:0<Z:=zero_lt_one.trans_le room
  have small:Z⁻¹  ≤  gap:=by
    rw [inv_le_comm₀ zp clear]
    exact inside
  have one:paceT R.draws.S m m=1:=by simp [paceT,(R.draws.S.a_pos m).ne']
  refine ⟨⟨?_,?_⟩,⟨room,stock,?_,?_,?_⟩⟩
  · intro i lo hi
    exact (le_antisymm lo hi) ▸ fit
  · rw [Nat.sub_self,Nat.cast_zero];exact zero_le_one.trans room
  · intro i
    have term:|(α i).radius|  ≤  ∑j,|(α j).radius|:=single_le_sum (fun j _=>abs_nonneg ((α j).radius)) (mem_univ i)
    dsimp only [Z,fence];linarith only [abs_nonneg U,cash,term,le_abs_self (α i).radius]
  · rw [one,abs_one];exact room
  · intro i j diff x hx z hz
    exact small.trans (seats i j diff x hx z hz)

end YM.Integration.WilsonMovingForkSharpNearRoom
