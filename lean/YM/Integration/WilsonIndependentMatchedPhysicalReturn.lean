import YM.Integration.WilsonIndependentMatchedPhysicalSector
import YM.Integration.WilsonIndependentMatchedTotalTop
import YM.Integration.WilsonPositionProgramTrialHomeFaces
/-! The actual unprojected ordinary word and the refilled public row on their two original vacua. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedPhysicalReturn
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile WilsonIndependentMatchedRosterLane WilsonIndependentMatchedCoverPairBudget
open scoped BigOperators Topology Classical
open WilsonIndependentMatchedRosterSlots (entry wallet degree count)
open WilsonIndependentMatchedPhysicalComponent (volume price)
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonIndependentMatchedRosterPlanted (response)
open WilsonIndependentMatchedPhysicalMasks (ranksV)
variable {G:Gauge}{n k e u₀:ℕ}{H:Hol G}{Q:Fin (n+1)→SealR G}{v:∀i,Rails (Q i).h k u₀ e}
local notation "C" => Credit.leanC
abbrev Courts:=(i:Fin (n+1))→CutsP H (Q i).ans (Q i).path (v i) C C C C

open WilsonIndependentMatchedPhysicalSector (stamp field)
open WilsonIndependentMatchedCoverProfile (word)
open WilsonIndependentMatchedFittedSeat (receiving)
open WilsonIndependentMatchedCoveredSeats (seat traced)
open WilsonIndependentMatchedRosterMasks (Bits quiet choose placed)
open WilsonIndependentMatchedBufferedVacuum (stopped)
open WilsonPositionProgramTrialAccrued (home)
open private summed from YM.Integration.WilsonIndependentMatchedRosterPlanted

def ordinary (L:Levels G)(X:Courts (H:=H) (v:=v))(F:Wilt Q)(m K:ℕ)(y:ℝ)(o:CellR):Era G ℝ:=
  MassP G ℝ n fun i=>word (X i).pt (F i) (paceT L.S m K) y o (Q i).h

theorem exactRows (V:Realm G (e+1) C)(X:Courts (H:=H) (v:=v))(F:Wilt Q)(B:Fin (n+1)→ℝ)(host m K N:ℕ)(y:ℝ)(o:CellR)
    (filed:stamp V X m K N)(older:host ≤ m)(start:m ≤ K)(live:K ≤ N)
    (good:∀s,On (Q s).h (X s).pt)(test:∀s,Amplitude (F s) (B s)):
    cruises V.draws V.paid N (capP Q) K host (ordinary V.draws X F m K y o)-
    stopped V.draws V.paid Q F (fun s=>home (Q s) (X s)) m K N host y o=
    ∑j∈Finset.univ.erase (quiet n),cruises V.draws V.paid N
      (ranksV (choose n j) k fun i=>(Q i).h) K host (field (choose n j) X F y o):=by
  let rem:=fun i=>seat (X i) 1 (F i) y o (X i).i
  let proj:=fun i=>receiving (X i) 1 (F i) y o (X i).i
  let raw:=fun i=>word (X i).pt (F i) (paceT V.draws.S m K) y o (Q i).h
  have lev s: (X s).ax=V.draws:=(filed s).1
  have clock s: (X s).tx=V.paid:=(filed s).2.1
  have bottom s: (X s).m=m:=(filed s).2.2.1
  have top s: (X s).ceilC=K:=(filed s).2.2.2.1
  have prior s: (X s).N=N:=(filed s).2.2.2.2
  have pitch s:paceT (X s).ax.S (X s).m ((X s).m+(X s).i)=paceT V.draws.S m K:=by
    change paceT (X s).ax.S (X s).m (X s).ceilC=_
    rw [lev s,bottom s,top s]
  have split:raw=fun s=>rem s+proj s:=by
    funext s
    simpa only [one_smul,pitch s] using WilsonIndependentMatchedTotalTop.placed (X s) 1 (F s) y o
  have stable s:Auth k (rem s):=(traced (X s) 1 (F s) y o).1 _ le_rfl
  have written s:Auth (Q s).h (proj s):=(WilsonIndependentMatchedFittedSeat.funds (X s) 1 (F s) y o
    1 (B s) (test s) 0 0).head _ le_rfl
  have auth s:Auth (Q s).h (raw s):=locale_val _ (WilsonCoeffUV.Mer.placed (Q s).h (F s) (good s) _ _) _
  have less:capP Q ≤ (n+1)*k:=by
    simpa only [capP,asp,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] using
      Finset.sum_le_sum (s:=Finset.univ) (fun i _=>(v i).hk)
  have strong:=WilsonIndependentMatchedPhysicalMasks.original (R:=V) (older.trans start) live
    (fun s=>(Q s).h) (fun s=>(v s).hk) rem proj stable written
  have born:=WilsonIndependentMatchedAccruedRestart.first V.draws V.paid X F m K N host y o lev clock bottom top prior
  unfold WilsonIndependentMatchedAccruedRestart.fitted at born
  rw [←cruisesMore _ _ _ older start] at born
  have fitted: (fun s=>word ((X s).pt-(X s).springP (X s).i) (F s) (paceT V.draws.S m K) y o (Q s).h)=proj:=by
    funext s
    rw [show proj s=receiving (X s) 1 (F s) y o (X s).i from rfl,
      WilsonIndependentMatchedFittedSeat.inlet,one_smul,pitch s,(X s).carve1]
    congr 1
    abel
  rw [fitted] at born
  have a₁:=WilsonIndependentMatchedCoverGrade.carried V.draws V.paid V.hG V.green
    (older.trans start) live _ (manCo _ (fun i=>(Q i).h) auth) less
  have a₂:=WilsonIndependentMatchedCoverGrade.carried V.draws V.paid V.hG V.green
    (older.trans start) live _ (manCo _ (fun i=>(Q i).h) written) less
  change cruises V.draws V.paid N (capP Q) K host (MassP G ℝ n proj)=
    stopped V.draws V.paid Q F (fun s=>home (Q s) (X s)) m K N host y o at born
  rw [←born]
  change cruises _ _ _ _ _ _ (MassP G ℝ n raw)-_ = _
  rw [a₁,a₂,split,strong]
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (cruises V.draws V.paid N _ K host)
  apply congrArg (MassP G ℝ n)
  funext s
  change (if choose n j s then rem s else proj s)=
    WilsonIndependentMatchedRosterSlots.entry (choose n j s) (X s) 1
      (WilsonIndependentMatchedFittedSeat.dose (X s) 1) (F s) y o (X s).i
  cases choose n j s <;> rfl

end YM.Integration.WilsonIndependentMatchedPhysicalReturn
