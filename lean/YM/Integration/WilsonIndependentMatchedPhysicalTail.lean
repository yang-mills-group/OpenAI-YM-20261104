import YM.Integration.WilsonIndependentMatchedPhysicalPeerClock
import YM.Integration.WilsonIndependentFittedRosterLedger
/-! Gross reserve for the discarded grades of the real physical dose at the enrolled older stop. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMatchedPhysicalTail
open Function Filter Finset Matrix Lattice Wilson RG RG.Supply Precision Source Labels Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato XSpace PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Power WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.PathCost
open WilsonPositionProgramTrialAccrued (home)
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonMarkedIndependentNormalizedElection (deck)
open scoped BigOperators Classical
variable {G:Gauge}{h D k u e:ℕ}
local notation "CC" => Credit.leanC

open WilsonIndependentFittedRosterFilms (Vote factor)
open WilsonIndependentFittedMixedCash (embed)
open WilsonPhysicalMarkedDefect.RawProduct (belt)
open WilsonOlderFreshSoftCoverScalar (clock)
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonOriginalPublicPlantedStableCredit (span)

def window (V:Realm G (e+1) CC)(s m N:ℕ)(awake:V.anchor ≤ s)(older:s ≤ m)(live:m ≤ N):WindowS G (e+1) CC:=
  ⟨V,s,m-s,N,N,m,awake,by omega,live,live⟩

def capital {F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}{v:Rails h k u e}
    (V:Realm G (e+1) CC)(X:CutsP H T p v CC CC CC CC)(s m N:ℕ)(awake:V.anchor ≤ s)(older:s ≤ m)(live:m ≤ N)
    (J Z:Credit)(q:ℕ)(flag:Bool):ℝ:=
  if flag then 1 else (Fintype.card (Alma F):ℝ)*((q+1:ℕ):ℝ)*
    (Z.buy (window V s m N awake older live).Age*((Real.exp (span X X.i))^h*J.buy X.Age*X.fuel))

theorem original {F:Labels.Frame G h}(H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u e):
    ∃J Z:Credit,∀(V:Realm G (e+1) CC)(X:CutsP H T p v CC CC CC CC)(s m N:ℕ)(awake:V.anchor ≤ s)
    (older:s ≤ m)(live:m ≤ N)(q:ℕ),q ≤ e → ∀flag:Bool,
    (∑i:Vote F flag,belt q (embed (clock V.draws V.paid N m s (factor (dose X 1) flag i)))) ≤
      capital V X s m N awake older live J Z q flag:=by
  obtain ⟨J,issued⟩:=WilsonIndependentFittedReportedWage.original H T p v CC CC CC CC
  obtain ⟨Z,reset⟩:=WilsonIndependentFittedKineticMass.original G h e CC F
  refine ⟨J,Z,?_⟩
  intro V X s m N awake older live q depth flag
  let R:=window V s m N awake older live
  let salary:=(Real.exp (span X X.i))^h*J.buy X.Age*X.fuel
  have nn:0 ≤ salary:=mul_nonneg (mul_nonneg (by positivity) (zero_le_one.trans (J.purchase X.windowC.warm))) X.hf
  have gross (i:ℕ)(d:i ≤ e)(z:Alma F):
      ‖coeff i (clock V.draws V.paid N m s (dose X 1 z))‖ ≤ Z.buy R.Age*salary:=by
    have quote:=reset R (dose X 1) salary nn (fun j hj z=>by simpa [salary] using issued X 1 j hj z) i d z
    have read:=WilsonIndependentFittedRelativeClock.reported V.draws V.paid N s (m-s) (dose X 1 z)
    rw [Nat.add_sub_of_le older] at read
    rw [read]
    exact quote
  cases flag
  · change (∑z:Alma F,belt q (embed (clock V.draws V.paid N m s (dose X 1 z)))) ≤ _
    calc
      _ ≤ ∑_z:Alma F,∑_j∈Finset.range (q+1),Z.buy R.Age*salary:=by
        apply Finset.sum_le_sum
        intro z _
        unfold WilsonPhysicalMarkedDefect.RawProduct.belt
        apply Finset.sum_le_sum
        intro j hj
        rw [embed,coeff_map]
        change ‖((coeff j (clock V.draws V.paid N m s (dose X 1 z)):ℝ):ℂ)‖ ≤ _
        simpa using gross j ((Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans depth) z
      _ = _:=by simp [capital,R,salary,mul_assoc]
  · have fold:=WilsonIndependentFittedRelativeClock.reported V.draws V.paid N s (m-s) 1
    rw [Nat.add_sub_of_le older,map_one] at fold
    change (∑_:Unit,belt q (embed (clock V.draws V.paid N m s 1))) ≤ 1
    simp only [Fintype.sum_unique,fold,(WilsonIndependentFittedRosterLedger.unit q 0).1,le_refl]

end YM.Integration.WilsonIndependentMatchedPhysicalTail
