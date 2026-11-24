import YM.Integration.WilsonSeparatedPrefixMovingSecondBirth
import YM.Integration.WilsonOriginalPublicPlantedFirstJoinScale

/-! Sum the genuine fine dates with the declared exterior/near time gap.
The highest-order credits contribute a polynomial only at the fixed home
and a summable spatial factor through every higher original cutoff. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingCalendar
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open Finset
open private tape from YM.Integration.WilsonOriginalPublicPlantedStableCredit
open scoped BigOperators Topology Classical

variable {G:Gauge}{e t m i j:ℕ}{E:Credit}

def epoch (R:Realm G e E)(t j:ℕ):ℝ:=R.y t+2*(R.draws.S.scale j-R.draws.S.scale t)

lemma days (S:Schedule)(i j:ℕ)(apart:i ≤ j): ((j-i:ℕ):ℝ) ≤ S.scale j-S.scale i:=by
  have three:1≤Real.log 3:=by rw [←Real.exp_le_exp,Real.exp_log (by norm_num:0<(3:ℝ))];exact Real.exp_one_lt_three.le
  have h:=tape S i (j-i)
  rw [Nat.add_sub_of_le apart] at h
  exact ((le_mul_of_one_le_right (Nat.cast_nonneg _) three).trans h)

theorem window (R:Realm G e E)(t i j:ℕ)(live:R.anchor ≤ t)(left:t ≤ i)(order:i ≤ j):
    1≤epoch R t j ∧ R.y i ≤ epoch R t j ∧
      Compar R.draws.S R.y i j ≤ epoch R t j ∧ PadRank R i j (epoch R t j):=by
  have de:=R.depth t live
  have lt':=scales R.draws.S left
  have top:=scales R.draws.S order
  have dur:=days R.draws.S i j order
  have adj:=R.age t i live left
  have far:Compar R.draws.S R.y i j ≤ epoch R t j:=by
    unfold epoch Compar;linarith only [lt',adj,dur]
  have pad:=PadRank.frugal R (live.trans left) order
  refine ⟨?_,?_,far,⟨fun v lo hi=>(pad.year v lo hi).trans far,pad.lengthS.trans far⟩⟩ <;>
    unfold epoch <;> linarith only [top,lt',adj,de]

/-- Two surplus native mesh powers absorb every fixed-order chronological
credit and still leave one full summable mesh power. -/
theorem credit (R:Realm G e E)(C:Credit)(t m j:ℕ)(live:R.anchor ≤ t)(tm:t ≤ m)(mj:m ≤ j):
    C.buy (epoch R t j)*(paceT R.draws.S m j)^2 ≤
      (C.finances 1 le_rfl).buy (epoch R t m)*paceT R.draws.S m j:=by
  let d:=R.draws.S.scale j-R.draws.S.scale m
  have hd:0≤d:=sub_nonneg.mpr (scales R.draws.S mj)
  have a:1≤epoch R t m:=(window R t m m live tm le_rfl).1
  have b:1≤epoch R t j:=(window R t m j live tm mj).1
  have cost:epoch R t j ≤ epoch R t m+2*d:=by unfold epoch d;linarith
  have sold:=Credit.rag_fee C a b cost (show 0≤2*d by positivity)
  have pp:paceT R.draws.S m j=Real.exp (-d):=pace_rep ..
  have even:-(2*d)/2= -d:=by ring
  rw [even] at sold
  rw [pp,pow_two,←mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact sold.trans (mul_le_of_le_one_right
    (zero_le_one.trans (Credit.purchase _ a)) (Real.exp_le_one_iff.mpr (by linarith)))

theorem light (S:Schedule)(m n:ℕ): (∑d∈range n,paceT S m (m+d))≤2:=by
  have ce:=WilsonOriginalPublicPlantedFirstJoinScale.pay S m n 1 one_pos 1 0 0 (by norm_num)
  simpa only [Nat.cast_zero,zero_div,sub_zero,Real.rpow_one,Real.rpow_zero,mul_one,
    WilsonOriginalPublicPlantedFirstJoinScale.radius,pace_rep] using ce

/-- Summation over the original ordered double births i≤j. The remaining
coefficients carry the actual jointly signed root valuation in each cell. -/
theorem triangular {V:Type*}[SeminormedAddCommGroup V](R:Realm G e E)(C:Credit)(t m N:ℕ)
    (live:R.anchor ≤ t)(tm:t ≤ m)(amount:ℝ)(pa:0≤amount)(D:ℕ→ℕ→V)
    (fee:∀i<N,∀j∈range N,i≤j → ‖D i j‖≤amount*C.buy (epoch R t (m+j))*
      (paceT R.draws.S m (m+i)*(paceT R.draws.S m (m+j))^2)):
    ‖∑i∈range N,∑j ∈ (range N).filter (fun j=>i≤j),D i j‖ ≤
      4*amount*(C.finances 1 le_rfl).buy (epoch R t m):=by
  let x:=fun d=>paceT R.draws.S m (m+d)
  let gross:=amount*(C.finances 1 le_rfl).buy (epoch R t m)
  have nonneg:0≤gross:=mul_nonneg pa (zero_le_one.trans (Credit.purchase _ (window R t m m live tm le_rfl).1))
  have one (i:ℕ)(hi:i<N)(j:ℕ)(hj:j∈range N)(order:i≤j): ‖D i j‖≤gross*x i*x j:=by
    have earned:=credit R C t m (m+j) live tm (Nat.le_add_right ..)
    have spread:=mul_le_mul_of_nonneg_left earned (mul_nonneg pa (pace_pos R.draws.S m (m+i)).le)
    dsimp only [gross,x]
    exact (fee i hi j hj order).trans (by convert spread using 1 <;> ring)
  have row (i:ℕ)(hi:i∈range N):‖∑j∈(range N).filter (fun j=>i≤j),D i j‖≤2*gross*x i:=by
    calc
      _≤∑j∈(range N).filter (fun j=>i≤j),‖D i j‖:=norm_sum_le ..
      _≤∑j∈(range N).filter (fun j=>i≤j),gross*x i*x j:=sum_le_sum fun j hj=>
        one i (mem_range.mp hi) j (mem_filter.mp hj).1 (mem_filter.mp hj).2
      _≤∑j∈range N,gross*x i*x j:=sum_le_sum_of_subset_of_nonneg (filter_subset ..)
        (fun j _ _=>mul_nonneg (mul_nonneg nonneg (pace_pos ..).le) (pace_pos ..).le)
      _=(gross*x i)*∑j∈range N,x j:=by rw [mul_sum]
      _≤2*gross*x i:=by have h:=mul_le_mul_of_nonneg_left (light R.draws.S m N)
                               (mul_nonneg nonneg (pace_pos R.draws.S m (m+i)).le)
                        exact h.trans_eq (by ring)
  calc
    _≤∑i∈range N,‖∑j∈(range N).filter (fun j=>i≤j),D i j‖:=norm_sum_le ..
    _≤∑i∈range N,2*gross*x i:=sum_le_sum row
    _=(2*gross)*∑i∈range N,x i:=by rw [mul_sum]
    _≤_:=by have h:=mul_le_mul_of_nonneg_left (light R.draws.S m N)
                       (show 0≤2*gross by positivity)
            exact h.trans_eq (by dsimp only [gross];ring)

end YM.Integration.WilsonSeparatedPrefixMovingCalendar
