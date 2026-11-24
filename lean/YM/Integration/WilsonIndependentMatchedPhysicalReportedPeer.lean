import YM.Integration.WilsonIndependentMatchedPhysicalReportedFilm
import YM.Integration.WilsonIndependentMatchedPhysicalTail
/-! Quantitative separation of the measured physical slot and its actual
coefficient reserve on the reporting scale after restoring the old clock. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedPhysicalReportedPeer
open Function Filter Finset Matrix Lattice Wilson RG RG.Supply Precision Source Labels Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato XSpace PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Power WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Wheel.Mark
open WilsonIndependentFittedRosterFilms (Vote factor)
open WilsonIndependentMatchedPhysicalPeer (amount reading)
open WilsonIndependentFittedMixedCash (embed)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open WilsonPhysicalMarkedDefect.RawProduct (belt)
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonOriginalPublicPlantedStableCredit (span)
open WilsonPositionProgramTrialAccrued (home)
open scoped BigOperators Classical
variable {G:Gauge}{h D k u e:ℕ}
local notation "CC" => Credit.leanC

def reserve {F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}{v:Rails h k u e}
    (X:CutsP H T p v CC CC CC CC)(q:ℕ)(J:Credit)(flag:Bool):ℝ:=
  if flag then 1 else (Fintype.card (Alma F):ℝ)*((q+1:ℕ):ℝ)*((Real.exp (span X X.i))^h*J.buy X.Age*X.fuel)

def measured (Q:SealR G){H:Hol G}{v:Rails Q.h k u e}(X:CutsP H Q.ans Q.path v CC CC CC CC)
    (q:ℕ)(g:ℝ)(B:Credit)(m:ℕ)(A:Levels G)(flag:Bool):ℝ:=
  if flag then 1 else (Fintype.card (Alma Q.F):ℝ)*B.buy (zz A m)*amount (Q:=Q) (reading q g) (home Q X)

theorem tail {F:Labels.Frame G h}(H:Hol G)(T:SectionData F)(p:h<D)(rails:Rails h k u e):
    ∃J:Credit,∀(X:CutsP H T p rails CC CC CC CC)(q:ℕ),q ≤ e → ∀flag:Bool,
      (∑a:Vote F flag,belt q (embed (factor (dose X 1) flag a))) ≤ reserve X q J flag:=by
  obtain ⟨J,earned⟩:=WilsonIndependentFittedReportedWage.original H T p rails CC CC CC CC
  refine ⟨J,?_⟩
  intro X q depth flag
  cases flag
  · let salary:=(Real.exp (span X X.i))^h*J.buy X.Age*X.fuel
    change (∑a:Alma F,belt q (embed (dose X 1 a))) ≤ _
    calc
      _ ≤ ∑_a:Alma F,∑_j∈range (q+1),salary:=by
        apply sum_le_sum
        intro a _
        unfold WilsonPhysicalMarkedDefect.RawProduct.belt
        apply sum_le_sum
        intro j hj
        have hj':=earned X 1 j ((Nat.le_of_lt_succ (mem_range.mp hj)).trans depth) a
        simpa [embed,PowerSeries.coeff_map,salary] using hj'
      _ = _:=by simp [reserve,salary,mul_assoc]
  · change (∑_:Unit,belt q (embed (1:Cost))) ≤ 1
    simp only [Fintype.sum_unique,(WilsonIndependentFittedRosterLedger.unit q 0).1,le_refl]

theorem original (R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (fit:h<D)(rails:Rails h k u e):
    let Q:=WilsonPositionProgramTrialNativeHome.reporter (G:=G) fit
    let A:=R.family.path.levels
    ∃B J:Credit,∀ᶠ floor:ℕ in atTop,∀m K N,floor ≤ m → m ≤ K → K ≤ N →
    ∀X:CutsP (hol G) Q.ans Q.path rails CC CC CC CC,X.ax=A → X.tx=R.metals.O → X.N=N → X.m=m →
    ∀(q:ℕ)(g:ℝ),q ≤ e → ∀flag:Bool,
    ((∑a:Vote Q.F flag,‖cash q g (embed (factor (dose X 1) flag a))‖) ≤ measured Q X q g B m A flag) ∧
    ((∑a:Vote Q.F flag,belt q (embed (factor (dose X 1) flag a))) ≤ reserve X q J flag):=by
  intro Q A
  obtain ⟨B,native⟩:=WilsonIndependentMatchedPhysicalPeer.original R simple v funded fit rails
  obtain ⟨J,gross⟩:=tail (hol G) Q.ans Q.path rails
  refine ⟨B,J,?_⟩
  filter_upwards [native] with floor quote
  intro m K N awake prior live X ax tx cap house q g valid flag
  refine ⟨?_,gross X q valid flag⟩
  cases flag
  · change (∑a:Alma Q.F,‖cash q g (embed (dose X 1 a))‖) ≤ _
    have fee:=quote m K N awake prior live X ax tx cap house (reading q g)
    have same (a:Alma Q.F):cash q g (embed (dose X 1 a))=(reading q g (dose X 1 a):ℂ):=by
      simp [WilsonPhysicalMarkedDefect.RawBank.cash,embed,WilsonIndependentMatchedPhysicalPeer.reading,Finset.sum_apply]
    simpa only [same,Complex.norm_real,amount,measured,Bool.false_eq_true,↓reduceIte] using fee
  · change (∑_:Unit,‖cash q g (embed (1:Cost))‖) ≤ 1
    simp only [Fintype.sum_unique,(WilsonIndependentFittedRosterLedger.unit q g).2,norm_one,le_refl]

end YM.Integration.WilsonIndependentMatchedPhysicalReportedPeer
