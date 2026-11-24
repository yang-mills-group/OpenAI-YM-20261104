import YM.Integration.WilsonIndependentConditionedPivotTailDay
import YM.Integration.WilsonIndependentConditionedPivotTailCalendar

/-! The signed microscopic-to-K return, conditional on the complete original
N-history. The full angular cost is uniform through the fine cutoff; in
particular the true marked scalar is among the projections returned. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedPivotTail
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMovingRosterBirth (charge)
open WilsonSeparatedPrefixMovingCalendar (epoch)
open WilsonIndependentConditionedPivotTailLaw (upper deposit)
open scoped BigOperators Topology Classical
variable {G:Gauge}{n:ℕ}

private theorem pile {e u:ℕ}{ι:Type*}(s:Finset ι)(D:ι→Era G ℝ)(w:ι→ℝ)
    (paid:∀i∈s,Flush e u 1 (D i) (w i)):
    Flush e u 1 (∑i∈s,D i) (∑i∈s,w i):=by
  classical
  induction s using Finset.induction_on with
  | empty=>
    simp only [Finset.sum_empty]
    exact ⟨le_rfl,fun _ _ _ _=>Fruit.zero⟩
  | @insert i s fresh earlier=>
    have here:=paid i (Finset.mem_insert_self i s)
    have more:=earlier (fun j hj=>paid j (Finset.mem_insert_of_mem hj))
    rw [Finset.sum_insert fresh,Finset.sum_insert fresh]
    exact ⟨add_nonneg here.1 more.1,fun k hk r hr=>(here.2 k hk r hr).plus (more.2 k hk r hr) zero_le_one⟩

theorem original (H:Hol G)(Q:Fin (n+1)→SealR G)(e gain:ℕ)(surplus:2 ≤ gain)(E W V S U:Credit):
    ∃C J:Credit,∀(R:Realm G (e+1) E),HorizonP H R W V Q →
      SpringD R (capP Q) 0 (capP Q+gain) S → Dormitory R (capP Q) 0 U →
      ∀(host m K N:ℕ),R.anchor ≤ host → host ≤ m → m ≤ K → K ≤ N →
      ∀(φ:Wilt Q)(X:Herit Q)(B:Fin (n+1)→ℝ)(y room:ℝ)(o:CellR),Bough Q φ y room B →
        let diff:=upper Q R φ X host m N N y o-upper Q R φ X host m K N y o
        let wages:=2*J.buy (epoch R host K)*(paceT R.draws.S m K)^gain*(C.buy room*charge Q X e B)
        Flush e 0 1 diff wages ∧ ∀q ≤ e,∀ω:Fin 0→YForest G,‖diff.2 q 0 ω‖ ≤ wages:=by
  obtain ⟨C,localDay⟩:=WilsonIndependentConditionedPivotTailDay.original H Q e gain E W V S U
  let J:=C.finances 1 le_rfl
  refine ⟨C,J,?_⟩
  intro R home spring old host m K N start heard cut width φ X B y room o geo diff wages
  let fields:=fun d=>deposit Q R φ X host m (K+d) N y o
  let amount:=C.buy room*charge Q X e B
  let bills:=fun d=>C.buy (epoch R host (K+d+1))*(paceT R.draws.S m (K+d+1))^gain*amount
  have exactRows:diff=∑d∈Finset.range (N-K),fields d:=WilsonIndependentConditionedPivotTailLaw.original
    Q R home φ X (start.trans heard) heard cut width y o
  have charged:=pile (Finset.range (N-K)) fields bills (e:=e) (u:=0) (by
    intro d hd
    have edge:K+d<N:=by have :=Finset.mem_range.mp hd;omega
    exact (localDay R home spring old host m (K+d) N start heard (by omega) edge φ X B y room o geo).2)
  have nonneg:0 ≤ charge Q X e B:=by
    apply Finset.prod_nonneg
    intro s _
    apply mul_nonneg (geo.lanes s).1
    unfold WilsonSeparatedPrefixMovingOwnDate.fee
    positivity
  have credit:0 ≤ amount:=mul_nonneg (zero_le_one.trans (C.purchase geo.pos)) nonneg
  have all:∑d∈Finset.range (N-K),bills d ≤ wages:=by
    dsimp only [bills,wages,amount,J]
    rw [←Finset.sum_mul]
    apply mul_le_mul_of_nonneg_right _ credit
    exact WilsonIndependentConditionedPivotTailCalendar.original R C host m K (N-K) gain start heard cut surplus
  have consumed:Flush e 0 1 diff wages:=by
    rw [exactRows]
    exact ⟨charged.1.trans all,fun q hq r hr=>(charged.2 q hq r hr).more all⟩
  exact ⟨consumed,WilsonIndependentMatchedCoverJoined.unit consumed⟩

end YM.Integration.WilsonIndependentConditionedPivotTail

