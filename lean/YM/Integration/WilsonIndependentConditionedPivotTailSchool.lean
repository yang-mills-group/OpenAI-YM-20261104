import YM.Integration.WilsonIndependentConditionedPivotTail
import YM.Integration.WilsonIndependentMovingRosterAllFineSeats
import YM.Integration.WilsonIndependentMatchedPivotSeat

/-! All single-coordinate upper continuations on the very same paid source
realm. Real fitted coefficients may be assembled afterwards by multilinearity. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedPivotTailSchool
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open WilsonCoeffUV.Cosmos.Polestar
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedPivotSeat (axis ticket)
open WilsonIndependentMovingRosterAllFineSeats (Named Elected)
open WilsonIndependentConditionedPivotTailLaw (upper)
open WilsonSeparatedPrefixMovingCalendar (epoch)
open scoped BigOperators Topology Classical
local notation "C₀" => Credit.leanC
variable {G:Gauge}{H:Hol G}{n e height seats:ℕ}

lemma unitFee (Q:SealR G)(v:Alma Q.F)(j:ℕ)(graded:j ≤ e):
    WilsonSeparatedPrefixMovingOwnDate.fee Q e (axis v j)=1:=by
  classical
  calc
    _=WilsonIndependentMatchedProxyIncome.cost e (axis v j):=by
      unfold WilsonSeparatedPrefixMovingOwnDate.fee WilsonIndependentMatchedProxyIncome.cost
      rw [Finset.sum_comm]
      exact Fin.sum_univ_eq_sum_range (fun i=>∑v',‖coeff i (axis v j v')‖) (e+1)
    _=1:=ticket v j graded

theorem original (M:Master H)(Q:Fin (n+1)→SealR G)(gain:ℕ)(surplus:2 ≤ gain)
    (funded:capP Q+gain ≤ seats)(named:∀s,Named M height seats (Q s)):
    ∃C J:Credit,∀(R:Realm G (e+1) C₀),Elected M R height seats →
      ∀(host m K:ℕ),R.anchor ≤ host → host ≤ m → m ≤ K →
      ∀(φ:Wilt Q)(B:Fin (n+1)→ℝ)(y room:ℝ)(o:CellR),Bough Q φ y room B →
      ∀(N:ℕ),K ≤ N → ∀(dir:(s:Fin (n+1))→Alma (Q s).F)(order:Fin (n+1)→ℕ), (∀s,order s ≤ e) →
        let X:Herit Q:=fun s=>axis (dir s) (order s)
        let diff:=upper Q R φ X host m N N y o-upper Q R φ X host m K N y o
        let wages:=2*J.buy (epoch R host K)*(paceT R.draws.S m K)^gain*(C.buy room*∏s,B s)
        Flush e 0 1 diff wages ∧ ∀q ≤ e,∀ω:Fin 0→YForest G,‖diff.2 q 0 ω‖ ≤ wages:=by
  obtain ⟨C,J,test⟩:=WilsonIndependentConditionedPivotTail.original H Q e gain surplus C₀ C₀ C₀ C₀ C₀
  refine ⟨C,J,?_⟩
  intro R sold host m K openAt older cut φ B y room o geo N endAt dir order eligible X diff wages
  have marks:HorizonP H R C₀ C₀ Q:=fun s=>sold.mark _ (named s)
  have cash:=test R marks (sold.spring (capP Q) 0 (capP Q+gain) (Nat.le_add_right _ _) funded (Nat.zero_le _))
    (sold.dorm (capP Q) 0 ((Nat.le_add_right _ gain).trans funded) (Nat.zero_le _))
    host m K N openAt older cut endAt φ X B y room o geo
  have originalFees:WilsonIndependentMovingRosterBirth.charge Q X e B=∏s,B s:=by
    apply Finset.prod_congr rfl
    intro s _
    rw [show WilsonSeparatedPrefixMovingOwnDate.fee (Q s) e (X s)=1 from unitFee (Q s) (dir s) (order s) (eligible s),mul_one]
  simpa only [originalFees] using cash

end YM.Integration.WilsonIndependentConditionedPivotTailSchool

