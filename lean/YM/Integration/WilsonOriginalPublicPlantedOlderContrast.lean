import YM.Integration.WilsonOriginalPublicPlantedOlderJoin
import YM.WilsonCoeffUV.Product.Report.Shapes

/-! The difference heard at the fitted report and the difference of the two
original top words reach the same older receiver on its own normalized
Wilson course. The input cost is on the signed field after cancellation. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalPublicPlantedOlderContrast
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentEvenPassport (old count)
open scoped BigOperators Topology Classical

theorem original (G:Gauge)(k e u:ℕ)(E W:Credit)(V:XSpace.Run)(a:ℕ)(B η:ℝ)
    (positive:0≤B)(small:0<η):
    ∀ᶠ i:ℕ in atTop,∀(R:Realm G (e+1) E),Dormitory R k u W →
      ∀ s:ℕ,R.anchor=s → (∀ t ≤ old V a i,R.y (s+t)≤B) →
      ∀ m c t:ℕ,m ≤ c → c ≤ old V a i → c ≤ t → t ≤ count V a i →
        let N:=s+count V a i
        let read:=fun (l:ℕ)(P:Era G ℝ)=>cruises R.draws R.paid N k (s+t) (s+l) P
        ∀P Q:Era G ℝ,Auth k P → Auth k Q → ∀ wage:ℝ,Flush e u 1 (read c P-read c Q) wage →
          let fee:=(V.step i).spacing^(-η)*wage
          Flush e u 1 (read m P-read m Q) fee ∧
            ∀j ≤ e,∀z:Fin 0→YForest G,‖(read m P).2 j 0 z-(read m Q).2 j 0 z‖≤fee:=by
  filter_upwards [WilsonOriginalPublicPlantedOlderJoin.original G k e u E W V a B η positive small] with
    i pay R licensed s start budget m c t before span fine top N read P Q hp hq wage funded fee
  have early:s+c ≤ s+t:=Nat.add_le_add_left fine s
  have older:s+m ≤ s+c:=Nat.add_le_add_left before s
  have cap:s+t ≤ N:=Nat.add_le_add_left top s
  have valid (X:Era G ℝ)(h:Auth k X):Auth k (read c X):=
    cruising R.draws R.hG R.green early cap h
  have bound:=pay R licensed s start budget m c before span (read c P-read c Q)
    ((valid P hp).sub (valid Q hq)) wage funded
  have joint:cruises R.draws R.paid N k (s+c) (s+m) (read c P-read c Q)=read m P-read m Q:=by
    rw [cruisePlus R.draws older R.hG R.green (early.trans cap) (valid P hp) (valid Q hq)]
    change cruises _ _ _ _ _ _ (cruises _ _ _ _ _ _ P)-
      cruises _ _ _ _ _ _ (cruises _ _ _ _ _ _ Q)=_
    rw [←cruisesMore R.draws R.paid P older early,←cruisesMore R.draws R.paid Q older early]
  dsimp only at bound
  rw [joint] at bound
  exact bound

end YM.Integration.WilsonOriginalPublicPlantedOlderContrast
