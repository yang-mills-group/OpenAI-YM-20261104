import YM.Integration.WilsonMovingForkSharpFineWindow
import YM.Integration.WilsonMovingForkSharpGramBirth

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingForkSharpFineGram
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile WilsonSeparatedPrefixMovingCalendar
open WilsonSeparatedPrefixMovingPairSector (current)
open WilsonSeparatedPrefixMovingFineFare (unitFee)
open Finset
open scoped BigOperators Topology Classical
variable {G:Gauge}{e n:ℕ}{E:Credit}

open WilsonSeparatedPrefixMovingUnformedSector (fresh invoice)
open WilsonMovingForkSharpGramBirth (pair)

theorem original (H:Hol G)(A B:SealR G)(k e u target:ℕ)(E W V Wo:Credit):
    let a:=B.h+A.h+(u+target+2)
    ∃C:Credit,∀(R:Realm G (e+1) E),SpringD R k u a W → Dormitory R (A.h+B.h) u Wo →
      PassportC H R A W V → PassportC H R B W V →
      ∀(older t b N:ℕ),R.anchor ≤ older → older ≤ t → t ≤ b → b ≤ N → A.h+B.h ≤ k →
      ∀(φ:Rarity A.D)(ψ:Rarity B.D)(X:A.Rider)(Z:B.Rider)(o:CellR)(y gap r U V':ℝ),
      0<gap → Amplitude φ U → Amplitude ψ V' → ClearDay φ ψ gap →
      φ.radius+|y|+1 ≤ r → ψ.radius+|y|+1 ≤ r → ∀q ≤ e,∀w:Fin 0→YForest G,
        let fee:=invoice (fun _:Fin 1=>B) A (fun _=>Z) X e k u a r gap U (fun _=>V')
        ‖(pair R A B φ ψ X Z o y t N older N).2 q 0 w-(pair R A B φ ψ X Z o y t b older N).2 q 0 w‖
          ≤ 2*(fee*(paceT R.draws.S t b)^target)*C.buy (epoch R older b):=by
  intro a
  let arms:=fun _:Fin 1=>B
  obtain ⟨C,pay⟩:=WilsonMovingForkSharpFineWindow.original H arms A k e u target E W V Wo
  refine ⟨C,?_⟩
  intro R spring stop left right older t b N gate ear live cut rank φ ψ X Z o y gap r U V' small ha hb clear near far q retained w fee
  let α:Wilt arms:=fun _=>ψ
  let c:Herit arms:=fun _=>Z
  have unit:paceT R.draws.S t t=1:=div_self (R.draws.S.a_pos _).ne'
  have grades:(∑j,(arms j).h)=B.h:=by simp [arms]
  have income:HorizonP H R W V arms:=fun _=>⟨right⟩
  have online:=pay R (by simpa only [grades] using spring) (by simpa only [grades] using stop)
    income left older t t N gate ear le_rfl (live.trans cut) (by simpa only [grades] using rank)
    α φ c X o y gap r U (fun _=>V') small (fun _=>hb) ha
    (fun _ z hz x hx=>by simpa only [unit,one_mul,one_smul,dist_comm z] using clear x hx z hz)
    (fun _=>far) (by simpa only [unit,div_one] using near) b live cut q retained w
  rw [WilsonMovingForkSharpGramBirth.original R A B left right φ ψ X Z o y t b older N q w (gate.trans ear) live (ear.trans live) cut]
  apply (norm_sum_le ..).trans
  simpa only [grades,unit,one_pow,inv_one,one_mul] using online
end YM.Integration.WilsonMovingForkSharpFineGram
