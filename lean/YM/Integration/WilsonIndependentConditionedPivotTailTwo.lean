import YM.Integration.WilsonIndependentConditionedPivotTailTwoEdge
import YM.Integration.WilsonIndependentConditionedPivotTailCalendar
import YM.Integration.WilsonIndependentMatchedCoverJoined

/-! On the same N-born vacuum, compare the full normalized roster with the
actual product of the individually returned K-fields at either an older
receiver or the near report. The distant field retains its own scale. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedPivotTailTwo
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMovingRosterStableSale (homes centers)
open WilsonIndependentConditionedPivotTailTwoEdge (amount)
open WilsonIndependentConditionedPivotTailHomes (received deposit)
open WilsonSeparatedPrefixMovingCalendar (epoch window)
open scoped BigOperators Topology Classical
variable {G:Gauge}{n:ℕ}
local notation "I" => Fin ((n+1)+1)

private theorem combine {e k:ℕ}{ι:Type*}(s:Finset ι)(D:ι→Era G ℝ)(w:ι→ℝ)
    (paid:∀i∈s,Auth k (D i) ∧ Flush e 0 1 (D i) (w i)):
    Auth k (∑i∈s,D i) ∧ Flush e 0 1 (∑i∈s,D i) (∑i∈s,w i):=by
  refine ⟨Auth.sum fun i hi=>(paid i hi).1,?_⟩
  induction s using Finset.induction_on with
  | empty=>simp only [Finset.sum_empty];exact ⟨le_rfl,fun _ _ _ _=>Fruit.zero⟩
  | @insert i s new earlier=>
    have item:=(paid i (Finset.mem_insert_self i s)).2
    have rest:=earlier (fun j hj=>paid j (Finset.mem_insert_of_mem hj))
    rw [Finset.sum_insert new,Finset.sum_insert new]
    exact ⟨add_nonneg item.1 rest.1,fun q hq l hl=>(item.2 q hq l hl).plus (rest.2 q hq l hl) zero_le_one⟩

theorem original (H:Hol G)(Q:I→SealR G)(e gain:ℕ)(surplus:2 ≤ gain)(E W V:Credit):
    ∃J U:Credit,∀(R:Realm G (e+1) E)(_roster:HorizonP H R W V Q)
    (_spring:SpringD R (capP Q) 0 (capP Q+gain) W)(_older:Dormitory R (capP Q) 0 V)
    (host t m K N:ℕ),R.anchor ≤ host → R.anchor ≤ t → host ≤ m → t ≤ m → m ≤ K → K ≤ N →
    ∀(φ:Wilt Q)(X:Herit Q)(B:I→ℝ)(y z gap:ℝ)(o:CellR),
    let T:=paceT R.draws.S m t
    let diff:=received R Q φ X (homes t m) (centers y T) (fun _=>o) host N N-
      received R Q φ X (homes t m) (centers y T) (fun _=>o) host K N
    let pay:=2*J.buy (epoch R t K)*(paceT R.draws.S m K)^gain*
      (U.buy (epoch R host m)*amount Q X B e (capP Q+gain) T gap z)
    0 < gap → (∀s,Amplitude (φ s) (B s)) → (∀s,radiusH (φ s) 1 (centers y T s) ≤ z) →
    (∀s s':Fin (n+1),s≠s'→ClearDay (φ s.succ) (φ s'.succ) gap) →
    (∀s:Fin (n+1),∀p∈tsupport (φ s.succ).ψ.val,∀q∈tsupport (φ 0).ψ.val,gap ≤ dist p (T • q)) →
      Auth (capP Q) diff ∧ Flush e 0 1 diff pay ∧ ∀q ≤ e,∀ω:Fin 0→YForest G,‖diff.2 q 0 ω‖ ≤ pay:=by
  obtain ⟨C,edge⟩:=WilsonIndependentConditionedPivotTailTwoEdge.original H Q e gain E W V
  obtain ⟨U,send⟩:=waveSeen G (capP Q) e 0 E V
  refine ⟨C.finances 1 le_rfl,U,?_⟩
  intro R roster spring older host t m K N first start held away cut top φ X B y z gap o T diff pay pos amp caps clear between
  let M:=amount Q X B e (capP Q+gain) T gap z
  let heldAge:=epoch R host m
  let trials:=fun d=>deposit R Q φ X (homes t m) (centers y T) (fun _=>o) host (K+d) N
  let bills:=fun d=>C.buy (epoch R t (K+d+1))*(paceT R.draws.S m (K+d+1))^gain*(U.buy heldAge*M)
  have appointments (i:I):R.anchor ≤ homes t m i:=Fin.cases start (fun _=>start.trans away) i
  have homesCut (i:I):homes t m i ≤ K:=Fin.cases (away.trans cut) (fun _=>cut) i
  have rosterLaw:diff=∑d∈Finset.range (N-K),trials d:=WilsonIndependentConditionedPivotTailHomes.original
    R Q roster φ X (homes t m) (centers y T) (fun _=>o) host K N appointments (held.trans cut) homesCut top
  have enough:=window R host host m first le_rfl held
  have read:Escort R host m (fun _=>1):=by
    refine ⟨first,held,fun _ _ _=>zero_le_one,fun _ _ _=>le_rfl,?_⟩
    intro j _ _
    exact div_le_self zero_le_one (by exact_mod_cast (R.draws.S.block j).pos)
  have entire:=combine (Finset.range (N-K)) trials bills (e:=e) (k:=capP Q) (by
    intro d hd
    let j:=K+d
    have jOld:m ≤ j:=cut.trans (Nat.le_add_right ..)
    have jNew:j<N:=by have off:=Finset.mem_range.mp hd;dsimp only [j];omega
    let Y:=deposit R Q φ X (homes t m) (centers y T) (fun _=>o) m j N
    have ear:=edge R roster spring older t m j N start away jOld jNew φ X B y z gap o pos amp caps clear between
    have order:m ≤ N:=cut.trans top
    have ship:=send R older host m (fun _=>1) m N N _ (max 0 (R.tempC m m)) heldAge read enough.2.2.2
      le_rfl order order (le_max_right _ _) Y Y (Fringed.same ear.2 ear.1 (le_max_left _ _))
    have mark:trials d=cruises R.draws R.paid N (capP Q) m host Y:=cruisesMore R.draws R.paid _ held jOld
    rw [mark]
    refine ⟨ship.inkV,?_⟩
    convert ship.f_l using 1
    dsimp only [bills,j,M,heldAge];ring)
  have M0:0 ≤ M:=by
    have zp:0 ≤ z:=(zero_le_one.trans (fieldCap ..)).trans (caps 0)
    have tp:0 ≤ T:=(pace_pos ..).le
    have co:0 ≤ coinMat (capP Q) e+1:=by linarith only [coinMat_nn (capP Q) e]
    have bp (s:I):0 ≤ B s:=(amp s).1
    have fp (s:I):0 ≤ WilsonSeparatedPrefixMovingOwnDate.fee (Q s) e (X s):=Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>norm_nonneg _
    have product:0 ≤ ∏s,WilsonIndependentMatchedRosterTariff.factor 0 (capP Q+gain) z*(B s*WilsonSeparatedPrefixMovingOwnDate.fee (Q s) e (X s)):=by
      apply Finset.prod_nonneg
      intro s _
      exact mul_nonneg (by unfold WilsonIndependentMatchedRosterTariff.factor;positivity) (mul_nonneg (bp s) (fp s))
    dsimp only [M,amount,WilsonIndependentMatchedRosterPowers.profiles];positivity
  have gross:0 ≤ U.buy heldAge*M:=mul_nonneg (zero_le_one.trans (U.purchase enough.1)) M0
  have close:∑d∈Finset.range (N-K),bills d ≤ pay:=by
    unfold bills pay
    rw [←Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (WilsonIndependentConditionedPivotTailCalendar.original R C t m K (N-K) gain start away cut surplus) gross
  rw [←rosterLaw] at entire
  have done:Flush e 0 1 diff pay:=⟨entire.2.1.trans close,fun q hq a ha=>(entire.2.2 q hq a ha).more close⟩
  exact ⟨entire.1,done,WilsonIndependentMatchedCoverJoined.unit done⟩

end YM.Integration.WilsonIndependentConditionedPivotTailTwo

