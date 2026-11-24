import YM.Integration.WilsonIndependentMatchedInheritedOrdinary
import YM.Integration.WilsonIndependentMatchedAccruedFaces
import YM.Integration.WilsonIndependentMatchedRestartPower

/-! The genuine inherited K word at the older receiver and the reenrolled
K-born film on a second vacuum. The two errors have distinct signed payers. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMatchedInheritedComparison
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonIndependentMatchedReportedProxy (passport sectionSeal)
open WilsonIndependentMatchedFittedSeat (receiving)
open WilsonIndependentMatchedCoverProfile (word)
open WilsonIndependentMatchedRosterPlanted (response)
open WilsonIndependentMatchedAccruedFaces (paidVector product)
open WilsonIndependentMatchedBufferedVacuum (Receipt)
open WilsonPositionProgramNormalizedMaster (fee)
open scoped BigOperators Classical
variable {G:Gauge}{h D k e u₀ u n:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}
    {p:h<D}{v:Rails h k u₀ e}{E W U V:Credit}
local notation "Cuts" => CutsP H T p v E W U V
local notation "Q" => fun _:Fin (n+1)=>sectionSeal T p

def heard (X:Fin (n+1)→Cuts)(a:Fin (n+1)→ℝ)(φ:Fin (n+1)→Rarity D)
    (stem:Fin (n+1)→TowerS G D)(stop:ℕ)(y:ℝ)(o:CellR):Era G ℝ:=
  cruises (X 0).ax (X 0).tx (X 0).N ((n+1)*k) (X 0).ceilC stop
    (MassP G ℝ n (fun s=>word (a s • stem s) (φ s) (paceT (X s).ax.S (X s).m (X s).ceilC) y o h))

def refund (X:Fin (n+1)→Cuts)(a amp:Fin (n+1)→ℝ)(φ:Fin (n+1)→Rarity D)
    (N' stop:ℕ)(y:ℝ)(o:CellR):Era G ℝ:=
  WilsonIndependentMatchedBufferedVacuum.stopped (X 0).ax (X 0).tx Q φ
    (paidVector X (fun s=>a s/amp s)) (X 0).m (X 0).ceilC N' stop y o

def wage (X:Fin (n+1)→Cuts)(a amp B:Fin (n+1)→ℝ)(C wallet:Credit)(clock:ℕ→ℝ)
    (Z:ℝ)(upper:ℕ):ℝ:=
  C.buy Z*(∏s,B s*(wallet.buy (clock (X 0).m)*fee (paidVector X (fun s=>a s/amp s)) e s))*
    trailC (X 0).ax.S (X 0).m upper

theorem scalar {Y Z:Era G ℝ}{rent δ:ℝ}(bill:Fringed k e u 1 rent δ Y Z)
    (j:ℕ)(hj:j ≤ e)(x:Fin 0→YForest G):‖Y.2 j 0 x-Z.2 j 0 x‖ ≤ rent*δ:=by
  have h:Fruit 0 1 u (Y.2 j 0-Z.2 j 0) (rent*δ):=(bill.heapS j 0 hj).toll
  have at₀:hedge 0 1 u x*‖(Y.2 j 0-Z.2 j 0) x‖ ≤ _:=
    (h.2.1.le_tsum x (fun y _=>h.1 y)).trans h.2.2
  rw [autumn_empty G 1 0 u x] at at₀
  simpa only [hedge,autumn,zero_mul,add_zero,one_pow,one_mul,Pi.sub_apply] using at₀

theorem joined (X:Fin (n+1)→Cuts)(a amp B:Fin (n+1)→ℝ)(φ:Fin (n+1)→Rarity D)
    (stem:Fin (n+1)→TowerS G D)(stop upper N':ℕ)(fare Z y:ℝ)(o:CellR)
    (clock:ℕ→ℝ)(start:ℕ)(C wallet:Credit)
    (issued:Receipt Q (X 0).ax (X 0).tx clock start e u C wallet)
    (course:∀s,(X s).vesselsC=(X 0).vesselsC)
    (bottom:∀s,(X s).m=(X 0).m)(birth:∀s,(X s).ceilC=(X 0).ceilC)(prior:∀s,(X s).N=(X 0).N)
    (awake:start ≤ stop)(older:stop ≤ (X 0).m)(buffer:(X 0).ceilC ≤ upper)
    (fine:upper ≤ (X 0).N)(other:upper ≤ N')(room:Compar (X 0).ax.S clock stop (X 0).m ≤ Z)
    (shape:Bough Q φ y Z B)
    (residual:response e u (heard X a φ stem stop y o-
      cruises (X 0).ax (X 0).tx (X 0).N ((n+1)*k) (X 0).ceilC stop
        (product X (fun s=>a s/amp s) φ y o)) fare):
    ∀j ≤ e,∀x:Fin 0→YForest G,
      ‖(heard X a φ stem stop y o).2 j 0 x-(refund X a amp φ N' stop y o).2 j 0 x‖ ≤
        fare+wage X a amp B C wallet clock Z upper:=by
  have fresh:=issued (X 0).m (X 0).ceilC upper (X 0).N N' stop (paidVector X (fun s=>a s/amp s))
    φ B Z y o awake older (Nat.le_add_right _ _) buffer fine other room shape
  rw [WilsonIndependentMatchedAccruedFaces.original X _ φ y o stop older course bottom birth prior] at fresh
  intro j hj x
  have old:=residual.2 j hj x
  have new:=scalar fresh j hj x
  let middle:=(cruises (X 0).ax (X 0).tx (X 0).N ((n+1)*k) (X 0).ceilC stop
    (product X (fun s=>a s/amp s) φ y o)).2 j 0 x
  have tri:=dist_triangle ((heard X a φ stem stop y o).2 j 0 x) middle ((refund X a amp φ N' stop y o).2 j 0 x)
  simp only [dist_eq_norm] at tri
  exact tri.trans (add_le_add old new)
end YM.Integration.WilsonIndependentMatchedInheritedComparison
