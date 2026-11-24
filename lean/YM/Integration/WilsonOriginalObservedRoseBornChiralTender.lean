import YM.Integration.WilsonOriginalObservedRoseBornChiralCoins

/-! One registered court, the measured input, and its surveyed replacement at the actual shared fresh cutoff. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonOriginalObservedRoseBornChiralTender
open Filter Function Finset Matrix Lattice Wilson RG RG.Supply Precision Source Labels Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato XSpace
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Power WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Wheel.Flooring
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentMatchedFiledIncome (plate charge)
open WilsonPositionProgramTrialReverseLens (received)
open WilsonPositionProgramTrialFittedLens (matrix cancel)
open WilsonPositionProgramTrialPublicJointSourceStable (seen)
open WilsonPositionProgramTrialPublicJointSourceVote (port refill)
open WilsonIndependentMatchedFreshWhole (projected)
open WilsonMaxwellThermometerSurveyIncome (prices)
open WilsonMarkedIndependentNormalizedElection (deck)
open scoped BigOperators Classical Topology

open WilsonPositionProgramTrialPublicJointSourceVote (port refill)
open WilsonPositionProgramTrialAccrued (home)
open WilsonIndependentMatchedFreshWhole (projected)
open WilsonIndependentMatchedFiledIncome (plate charge)
open WilsonPositionProgramTrialReverseLens (received)
variable {G:Gauge}{n k u e h D₀:ℕ}(R:Run G)(W:Initialize G)
variable (d D:Fin (n+1)→ℕ)(fit:∀i,d i<D i)
local notation "L" => R.family.path.levels
local notation "O" => R.metals.O
local notation "CC" => Credit.leanC

open WilsonIndependentMatchedFreshInverseIncome (slope measured age)
open WilsonIndependentMatchedProxyIncome (cost)
open WilsonOriginalObservedRoseBornChiralPeer (input)
open PowerSeries WilsonCoeffUV.Bank.Mosaic

def plan {h:ℕ}{F:Labels.Frame G h}(e:ℕ)(A:Alma F→ℝ):ℝ:=
  ∑a,∑t∈Finset.range (e+1),∑_z∈Finset.HasAntidiagonal.antidiagonal t,A a

def size {h:ℕ}(F:Labels.Frame G h)(e:ℕ):ℝ:=∑_q∈Finset.range (e+1),∑_a:Alma F,(1:ℝ)

theorem compact {h:ℕ}{F:Labels.Frame G h}(c:Verse F)(e:ℕ)(A:Alma F→ℝ)(nn:∀a,0≤A a)
    (S:ℝ)(price:∀q ≤ e,∀a,‖coeff q (c a)‖ ≤ S):charge e c A ≤ S*plan e A:=by
  unfold charge WilsonIndependentMatchedFiledIncome.allot plan
  simp only [Finset.mul_sum]
  apply sum_le_sum
  intro a _
  apply sum_le_sum
  intro t ht
  apply sum_le_sum
  intro z hz
  have mass:=Finset.HasAntidiagonal.mem_antidiagonal.mp hz
  have lim:=Finset.mem_range.mp ht
  apply mul_le_mul_of_nonneg_right _ (nn a)
  simpa only [Real.norm_eq_abs] using price z.1 (by omega) a

theorem measuredCost {h:ℕ}{F:Labels.Frame G h}(c:Verse F)(e:ℕ)(S:ℝ)
    (price:∀q ≤ e,∀a,‖coeff q (c a)‖ ≤ S):cost e c ≤ S*size F e:=by
  unfold cost size
  simp only [Finset.mul_sum,mul_one]
  apply sum_le_sum
  intro q hq
  exact sum_le_sum (fun a _=>price q (Nat.le_of_lt_succ (mem_range.mp hq)) a)

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (pub:WilsonMaxwellThermometerSurveyIncome.prices W R.kit)(big:h<D₀)(rails:Rails h k u e)
    (cap:capP (deck (G:=G) d D fit) ≤ k):
    let J:=port R W d D fit false
    ∃A:Fin (n+1)→Bool→Credit,∃B:Fin (n+1)→Credit,∀ᶠ j:ℕ in atTop,∀m K,j ≤ m → m ≤ K →
    ∀i (b:(J i).Rider) side (tariff:Alma (J i).F→ℝ), (∀a,0≤tariff a) →
    let base := (Fintype.card (Alma (J i).F):ℝ)*(B i).buy (zz L m)*cost e b
    cost e (PermuteLens L O (J i) K m b) ≤ base*size (J i).F e ∧
      charge e (input R W d D fit side i m K b) tariff ≤
        ((A i side).buy (age L (zz L) m K)*base)*plan e tariff:=by
  intro J
  obtain ⟨A,B,issued⟩:=WilsonOriginalObservedRoseBornChiralCoins.original R W d D fit simple v funded pub big rails cap
  refine ⟨A,B,?_⟩
  filter_upwards [issued] with j paid
  intro m K floor before i b side tariff nn base
  have both:=paid m K floor before i b side
  exact ⟨measuredCost _ e base (fun q hq a=>(both q hq a).1),
    compact _ e tariff nn _ (fun q hq a=>(both q hq a).2)⟩

end YM.Integration.WilsonOriginalObservedRoseBornChiralTender
