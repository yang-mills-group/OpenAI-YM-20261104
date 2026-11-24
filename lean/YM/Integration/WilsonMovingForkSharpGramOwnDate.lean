import YM.Integration.WilsonMovingForkSharpFineGram
import YM.Integration.WilsonSeparatedPrefixMovingUnjoined

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingForkSharpGramOwnDate
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical

variable {G:Gauge}{h D k e u:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}

private theorem own {δ:ℝ}(Q:SealR G)(X:Q.Rider)(e:ℕ)(hd:0≤δ):
    0≤WilsonSeparatedPrefixMovingOwnDate.fee Q e X ∧
    Terms e Q (WilsonSeparatedPrefixMovingOwnDate.fee Q e X) δ X X:=by
  refine ⟨Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>norm_nonneg _,?_⟩
  intro j hj v
  apply twain.one _ _ hd
  exact (Finset.single_le_sum (f:=fun n:Fin (e+1)=>‖coeff n.val (X v)‖)
    (fun _ _=>norm_nonneg _) (Finset.mem_univ (⟨j,by omega⟩:Fin (e+1)))).trans
    (Finset.single_le_sum (f:=fun v:Alma Q.F=>∑n:Fin (e+1),‖coeff n.val (X v)‖)
      (fun _ _=>Finset.sum_nonneg fun _ _=>norm_nonneg _) (Finset.mem_univ v))

open WilsonSeparatedPrefixMovingCalendar (epoch window)
open WilsonSeparatedPrefixMovingPairSector (current)
open WilsonMovingForkSharpGramBirth (pair)
open WilsonSeparatedPrefixMovingOwnDate (fee)
def tariff (H:Hol G)(A:SealR G)(E W V:Credit)(e u:ℕ)(Z B:ℝ)(X:A.Rider):ℝ:=
  (hardCash e u E W V H A).buy Z*(B*fee A e X)
theorem fund {E W V:Credit}(H:Hol G)(R:Realm G (e+1) E)(A:SealR G)
    (ticket:PassportC H R A W V)(t N:ℕ)(live:R.anchor ≤ t)(top:t ≤ N)(Z:ℝ)(clock:Compar R.draws.S R.y t t ≤ Z)
    (φ:Rarity A.D)(X:A.Rider)(y B:ℝ)(o:CellR)(radius:φ.radius ≤ Z)(shift:|y| ≤ Z)(paid:Amplitude φ B):
    let A':=current R A φ X t t N y o
    let δ:=max 0 (R.tempC t t)
    Fringed A.h e u 1 (tariff H A E W V e u Z B X) δ A' A':=by
  intro A' δ
  have hd:0 ≤ δ:=le_max_left ..
  have hp:=own A X e hd
  have stage:=(capLife ticket live le_rfl le_rfl top top clock hp.1 (le_max_right _ _) X X hp.2
    φ radius u o shift paid).1
  simpa only [tariff, A',δ,WilsonSeparatedPrefixMovingPairSector.current,pace_self,one_pow,inv_one,mul_one] using stage
theorem original (H:Hol G)(A B:SealR G)(e u:ℕ)(E W V L:Credit):
    ∃C:Credit,∀(R:Realm G (e+1) E),PassportC H R A W V → PassportC H R B W V →
      Dormitory R (A.h+B.h) u L → ∀(older t N:ℕ),R.anchor ≤ older → older ≤ t → t ≤ N →
      ∀(φ:Rarity A.D)(ψ:Rarity B.D)(X:A.Rider)(Y:B.Rider)(y r a b:ℝ)(o:CellR),
      |y| ≤ r → φ.radius ≤ r → ψ.radius ≤ r → Amplitude φ a → Amplitude ψ b →
      let Z:=epoch R older t
      let z:=max Z r
      let cost:=C.buy Z*(coinMat (A.h+B.h) e*tariff H A E W V e u z a X*tariff H B E W V e u z b Y)
      ∀q ≤ e,∀w:Fin 0→YForest G,‖(pair R A B φ ψ X Y o y t t older N).2 q 0 w‖ ≤ cost:=by
  obtain ⟨C,seen⟩:=waveSeen G (A.h+B.h) e u E L
  refine ⟨C,?_⟩
  intro R ha hb dorm older t N gate ear cap φ ψ X Y y r a b o shift rad rad' fa fb Z z cost q hq w
  let δ:=max 0 (R.tempC t t)
  have clock:Compar R.draws.S R.y t t ≤ z:=(window R older t t gate ear le_rfl).2.2.1.trans (le_max_left ..)
  have left:=fund H R A ha t N (gate.trans ear) cap z clock φ X y a o (rad.trans (le_max_right ..)) (shift.trans (le_max_right ..)) fa (u:=u)
  have right:=fund H R B hb t N (gate.trans ear) cap z clock ψ Y y b o (rad'.trans (le_max_right ..)) (shift.trans (le_max_right ..)) fb (u:=u)
  have joint:=fringedMat left right zero_le_one (le_refl (A.h+B.h))
  have arrived:=(seen R dorm older t (fun _=>1) t N N _ δ Z (oldGuard gate ear)
    (window R older older t gate le_rfl ear).2.2.2 le_rfl cap cap (le_max_right _ _) _ _ joint).f_l
  exact WilsonIndependentMatchedCoverJoined.unit arrived q hq w

end YM.Integration.WilsonMovingForkSharpGramOwnDate
