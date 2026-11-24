import YM.Integration.WilsonIndependentMatchedRosterMasks
import YM.Integration.WilsonIndependentMatchedRosterCuts

/-! The complete connected and disconnected terms are carried through
the same original allotted conditional program before testing its scalar. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedRosterSigned
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical

open WilsonIndependentMatchedCoverProfile
variable {G:Gauge}{n e:ℕ}{C:Credit}

open WilsonIndependentMatchedRosterMasks (Bits quiet choose placed)
open WilsonIndependentMatchedRosterSlots (degree)
open WilsonIndependentMatchedRosterCuts (ranks)

private lemma addition {R:Realm G (e+1) C}{k m s N:ℕ}(before:s ≤ m)(top:m ≤ N)
    (P Q:Era G ℝ)(hp:Auth k P)(hq:Auth k Q):
    cruises R.draws R.paid N k m s (P+Q)=cruises R.draws R.paid N k m s P+cruises R.draws R.paid N k m s Q:=by
  have δ:=cruisePlus R.draws before R.hG R.green top (hp.add hq) hq
  rw [add_sub_cancel_right] at δ
  exact sub_eq_iff_eq_add.mp δ.symm

private lemma summing {R:Realm G (e+1) C}{k m s N:ℕ}(before:s ≤ m)(top:m ≤ N)
    {ι:Type*}(f:Finset ι)(P:ι→Era G ℝ)(hp:∀i∈f,Auth k (P i)):
    cruises R.draws R.paid N k m s (∑i∈f,P i)=∑i∈f,cruises R.draws R.paid N k m s (P i):=by
  classical
  induction f using Finset.induction_on with
  | empty=>
    simp only [Finset.sum_empty]
    have hz:Auth k (0:Era G ℝ):=by let Z:Unit→Era G ℝ:=fun _=>0;simpa using Auth.sum (P:=Z) (S:=∅) (by simp)
    simpa only [sub_self] using (cruisePlus R.draws before R.hG R.green top hz hz)
  | @insert a f ha ih=>
    have sold (i:ι)(hi:i∈f):Auth k (P i):=hp i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha,Finset.sum_insert ha,addition before top _ _ (hp a (Finset.mem_insert_self ..)) (Auth.sum sold),ih sold]

/-- The actual complete raw-minus-fitted word, on one vacuum through every
post-capture date, consists exactly of the contributions with a signed
slot. Each summand uses its own authentic rank horizon. -/
theorem original {R:Realm G (e+1) C}{n k h m s N:ℕ}(before:s ≤ m)(top:m ≤ N)(order:h ≤ k)
    (P Q:Fin (n+1)→Era G ℝ)(hp:∀i,Auth k (P i))(hq:∀i,Auth h (Q i)):
    cruises R.draws R.paid N ((n+1)*k) m s (MassP G ℝ n (fun i=>P i+Q i))-
      cruises R.draws R.paid N ((n+1)*k) m s (MassP G ℝ n Q)=
    ∑j∈Finset.univ.erase (quiet n),
      cruises R.draws R.paid N (ranks (choose n j) k h) m s (placed P Q j):=by
  classical
  have form (j:Bits n):Auth (ranks (choose n j) k h) (placed P Q j):=by
    apply manCo _ (fun i=>degree (choose n j i) k h)
    intro i
    cases ok:choose n j i <;> simp only [degree,Bool.false_eq_true,if_false,if_true] <;> first | exact hp i | exact hq i
  have less (j:Bits n):ranks (choose n j) k h ≤ (n+1)*k:=by
    have pt (i:Fin (n+1)):degree (choose n j i) k h ≤ k:=by cases choose n j i <;> simp [degree,order]
    simpa [ranks] using Finset.sum_le_sum (s:=Finset.univ) (fun i _=>pt i)
  let L:=fun j:Bits n=>cruises R.draws R.paid N ((n+1)*k) m s (placed P Q j)
  rw [WilsonIndependentMatchedRosterMasks.deposited,summing before top _ _ (fun j _=>(form j).tall (less j))]
  change (∑ j:Bits n,L j)-cruises R.draws R.paid N ((n+1)*k) m s (MassP G ℝ n Q)=_
  have no:L (quiet n)=cruises R.draws R.paid N ((n+1)*k) m s (MassP G ℝ n Q):=by
    dsimp only [L];rw [WilsonIndependentMatchedRosterMasks.fitted]
  rw [←no,←Finset.sum_erase_add _ L (Finset.mem_univ (quiet n)),add_sub_cancel_right]
  apply Finset.sum_congr rfl
  intro j _
  exact (WilsonIndependentMatchedCoverGrade.carried R.draws R.paid R.hG R.green before top _ (form j) (less j)).symm

end YM.Integration.WilsonIndependentMatchedRosterSigned
