import YM.Integration.WilsonSeparatedPrefixMovingCalendar

/-! Ordered births at the incoming child i+1 of each true edge. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingNextCalendar
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open Finset
open WilsonSeparatedPrefixMovingCalendar
open scoped BigOperators Topology Classical

variable {G:Gauge}{e:ℕ}{E:Credit}

lemma selected (S:Schedule)(m N:ℕ):∑j∈range N,paceT S m (m+j+1)≤2:=by
  have all:=light S m (N+1)
  rw [sum_range_succ' (fun j=>paceT S m (m+j))] at all
  simp only [add_zero,←Nat.add_assoc] at all
  linarith only [all,(pace_pos S m m).le]

theorem original {V:Type*}[SeminormedAddCommGroup V](R:Realm G e E)(C:Credit)(t m N:ℕ)
    (live:R.anchor ≤ t)(tm:t ≤ m)(amount:ℝ)(pa:0≤amount)(D:ℕ→ℕ→V)
    (fee:∀i<N,∀j∈range N,i≤j → ‖D i j‖≤amount*C.buy (epoch R t (m+j+1))*
      (paceT R.draws.S m (m+i+1)*(paceT R.draws.S m (m+j+1))^2)):
    ‖∑i∈range N,∑j ∈ (range N).filter (fun j=>i≤j),D i j‖ ≤
      4*amount*(C.finances 1 le_rfl).buy (epoch R t m):=by
  let x:=fun d=>paceT R.draws.S m (m+d+1)
  let gross:=amount*(C.finances 1 le_rfl).buy (epoch R t m)
  have nonneg:0≤gross:=mul_nonneg pa (zero_le_one.trans (Credit.purchase _ (window R t m m live tm le_rfl).1))
  have one (i:ℕ)(hi:i<N)(j:ℕ)(hj:j∈range N)(order:i≤j): ‖D i j‖≤gross*x i*x j:=by
    have earned:=credit R C t m (m+j+1) live tm (by omega)
    have spread:=mul_le_mul_of_nonneg_left earned (mul_nonneg pa (pace_pos R.draws.S m (m+i+1)).le)
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
      _≤2*gross*x i:=by have h:=mul_le_mul_of_nonneg_left (selected R.draws.S m N)
                               (mul_nonneg nonneg (pace_pos R.draws.S m (m+i+1)).le)
                        exact h.trans_eq (by ring)
  calc
    _≤∑i∈range N,‖∑j∈(range N).filter (fun j=>i≤j),D i j‖:=norm_sum_le ..
    _≤∑i∈range N,2*gross*x i:=sum_le_sum row
    _=(2*gross)*∑i∈range N,x i:=by rw [mul_sum]
    _≤_:=by have h:=mul_le_mul_of_nonneg_left (selected R.draws.S m N)
                       (show 0≤2*gross by positivity)
            exact h.trans_eq (by dsimp only [gross];ring)

end YM.Integration.WilsonSeparatedPrefixMovingNextCalendar
