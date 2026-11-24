import YM.Integration.WilsonSeparatedPrefixMovingLiveDeposit
import YM.WilsonCoeffUV.Product.Report.Capture
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingMiddleIncome
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical

open WilsonSeparatedPrefixMovingOwnDate (fee)
open scoped Classical

theorem own {G:Gauge}(Q:SealR G)(e:ℕ)(X:Q.Rider)(δ:ℝ)(hd:0≤δ):
    Terms e Q (fee Q e X) δ X X:=by
  intro j hj v
  have cash:‖coeff j (X v)‖≤fee Q e X:=
    (Finset.single_le_sum (f:=fun n:Fin (e+1)=>‖coeff n.val (X v)‖)
      (fun _ _=>norm_nonneg _) (Finset.mem_univ (⟨j,by omega⟩:Fin (e+1)))).trans
      (Finset.single_le_sum (f:=fun v:Alma Q.F=>∑n:Fin (e+1),‖coeff n.val (X v)‖)
        (fun _ _=>Finset.sum_nonneg fun _ _=>norm_nonneg _) (Finset.mem_univ v))
  exact twain.one _ _ hd cash

theorem original {G:Gauge}{H:Hol G}{n:ℕ}(Q:Fin (n+1)→SealR G)(e w:ℕ)(E W V S D:Credit):
    ∃C:Credit,∀(R:Realm G (e+1) E)(_home:HorizonP H R W V Q)
      (_spring:SpringD R (capP Q) w (capP Q+2) S)(_dorm:Dormitory R (capP Q) w D)
      (m j N:ℕ)(F:Wilt Q)(X:Herit Q)(B:Fin (n+1)→ℝ)(Z y:ℝ)(o:CellR),
      R.anchor ≤ j → j ≤ m → m ≤ N → PadRank R j m Z → Bough Q F y Z B →
        let full:=locale o (LodeStar R.draws R.paid F X m j N y)
        Auth (capP Q) full ∧ Flush e w 1 full (C.buy Z*∏v,B v*fee (Q v) e (X v)):=by
  obtain ⟨C,received⟩:=Captures H Q E W V S D e w
  refine ⟨C,?_⟩
  intro R fields spring dorm m j N F X B Z y o live old top room profile full
  let A:=fun v=>fee (Q v) e (X v)
  let δ:=max 0 (R.tempC m m)
  have paid:Sitting Q A e δ X X:=⟨fun _=>Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>norm_nonneg _,
    fun v=>own (Q v) e (X v) δ (le_max_left _ _)⟩
  have ear:=received R fields spring dorm m m j N N F X X A B Z y δ o live old le_rfl top top room
    profile (le_max_right _ _) paid
  exact ⟨ear.inkV,ear.f_l⟩

end YM.Integration.WilsonSeparatedPrefixMovingMiddleIncome
