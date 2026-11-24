import YM.Integration.WilsonSeparatedPrefixMovingCalendar

/-! The growing upper age is charged inside the summation. Two relative
powers above K suffice, while the entire optical power up to K is retained. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedPivotTailCalendar
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonSeparatedPrefixMovingCalendar (epoch window credit light)
open scoped BigOperators Topology Classical
variable {G:Gauge}{e:ℕ}{E:Credit}

theorem original (R:Realm G e E)(C:Credit)(host m K count gain:ℕ)(live:R.anchor ≤ host)
    (heard:host ≤ m)(cut:m ≤ K)(surplus:2 ≤ gain):
    ∑d∈Finset.range count,C.buy (epoch R host (K+d+1))*(paceT R.draws.S m (K+d+1))^gain ≤
      2*((C.finances 1 le_rfl).buy (epoch R host K))*(paceT R.draws.S m K)^gain:=by
  let S:=R.draws.S
  let δ:=paceT S m K
  let A:=(C.finances 1 le_rfl).buy (epoch R host K)
  have Apos:0 ≤ A:=zero_le_one.trans ((C.finances 1 le_rfl).purchase (window R host K K live (heard.trans cut) le_rfl).1)
  have dp:0 ≤ δ^gain:=pow_nonneg (pace_pos ..).le _
  have one (d:ℕ):
      C.buy (epoch R host (K+d+1))*(paceT S m (K+d+1))^gain ≤
        (A*δ^gain)*paceT S K (K+d):=by
    let j:=K+d+1
    let mesh:=paceT S K j
    have later:K ≤ j:=by dsimp only [j];omega
    have positive:0 ≤ mesh:=(pace_pos ..).le
    have short:mesh ≤ 1:=pace_le S later
    have split:paceT S m j=δ*mesh:=by
      unfold δ mesh paceT
      field_simp [(S.a_pos K).ne',(S.a_pos m).ne']
    have cmp:mesh^gain ≤ mesh^2:=by
      calc
        _=mesh^(2+(gain-2)):=by rw [Nat.add_sub_of_le surplus]
        _=mesh^2*mesh^(gain-2):=pow_add .. 
        _ ≤ mesh^2:=mul_le_of_le_one_right (sq_nonneg _) (pow_le_one₀ positive short)
    have sale:=credit R C host K j live (heard.trans cut) later
    have eligible:0 ≤ C.buy (epoch R host j):=zero_le_one.trans
      (C.purchase (window R host K j live (heard.trans cut) later).1)
    have step:mesh ≤ paceT S K (K+d):=by
      exact div_le_div_of_nonneg_right (S.strictAnti.antitone (Nat.le_succ _)) (S.a_pos K).le
    change C.buy (epoch R host j)*(paceT S m j)^gain ≤ _
    rw [split,mul_pow]
    calc
      _=δ^gain*(C.buy (epoch R host j)*mesh^gain):=by ring
      _≤δ^gain*(A*mesh):=mul_le_mul_of_nonneg_left
        ((mul_le_mul_of_nonneg_left cmp eligible).trans sale) dp
      _≤δ^gain*(A*paceT S K (K+d)):=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left step Apos) dp
      _=_:=by ring
  calc
    _≤∑d∈Finset.range count,(A*δ^gain)*paceT S K (K+d):=Finset.sum_le_sum fun d _=>one d
    _=(A*δ^gain)*(∑d∈Finset.range count,paceT S K (K+d)):=by rw [Finset.mul_sum]
    _≤(A*δ^gain)*2:=mul_le_mul_of_nonneg_left (light S K count) (mul_nonneg Apos dp)
    _=_:=by dsimp only [A,δ,S];ring

end YM.Integration.WilsonIndependentConditionedPivotTailCalendar

