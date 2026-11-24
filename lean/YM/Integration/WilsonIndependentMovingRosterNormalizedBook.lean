import YM.Integration.WilsonIndependentMovingRosterNormalizedInputs
import YM.Integration.WilsonIndependentMovingRosterRawReturn

/-! Exact common-board balance for a prescribed normalized stable-corrected product. -/
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterNormalizedBook

open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedRosterTariff (factor)
open WilsonIndependentMovingRosterStableSale (homes centers)
open WilsonIndependentMovingRosterLaneFilm (Licensed)
open WilsonIndependentMatchedRosterPowers (profiles)
open WilsonIndependentMatchedRosterSlots (degree count entry wallet)
open WilsonIndependentMatchedRosterMasks (Bits choose placed)
open WilsonIndependentMatchedRosterCuts (counts ranks)
open WilsonIndependentMovingRosterTopFields (stable fitted)
open WilsonIndependentMatchedFittedSeat (dose)
open scoped BigOperators Topology Classical
open WilsonIndependentMatchedRosterMasks (quiet present)
open WilsonIndependentMatchedCoverDate (age)
variable {G:Gauge}{H:Hol G}{n e h D k u₀:ℕ}{F:Labels.Frame G h}{T:SectionData F}
    {p:h<D}{v:Rails h k u₀ e}{E W K U:Credit}

open WilsonIndependentMatchedReportedProxy (sectionSeal)
open WilsonIndependentMovingRosterCut (parcel residual)
open WilsonSeparatedPrefixMovingPairSector (current)
open WilsonIndependentMovingRosterTopFields (offered)
open WilsonIndependentMovingRosterStablePortfolio (rate returned)
local notation "Qₙ" => (fun _:Fin (n+1)=>sectionSeal T p)
local notation "Q₀" => sectionSeal T p
local notation "near" φ:max => (fun i:Fin (n+1)=>φ (Fin.succ i))

def raw (R:Realm G (e+1) E)(X:Fin ((n+1)+1)→CutsP H T p v E W K U)
    (a:Fin ((n+1)+1)→ℝ)(col:Fin ((n+1)+1)→Verse F)(φ:Fin ((n+1)+1)→Rarity D)(y:ℝ)(o:CellR)(t m older N:ℕ):Era G ℝ:=
  let zoom:=paceT R.draws.S m t
  cruises R.draws R.paid N ((n+2)*k) N older (MassP G ℝ (n+1) (WilsonIndependentMovingRosterNormalizedInputs.submitted R X a col φ (centers y zoom) (fun _=>o) N))-
    cruises R.draws R.paid N (h+capP Qₙ) m older
      (agateV (current R Q₀ (φ 0) (col 0) t m N (y/zoom) o)
        (parcel R Qₙ (near φ) (Fin.tail col) o y m m N))

def prescribed (R:Realm G (e+1) E)(_X:Fin ((n+1)+1)→CutsP H T p v E W K U)
    (col:Fin ((n+1)+1)→Verse F)(φ:Fin ((n+1)+1)→Rarity D)(y:ℝ)(o:CellR)(t m older N:ℕ):Era G ℝ:=
  residual R Qₙ Q₀ (near φ) (φ 0) (Fin.tail col) (col 0) o y t m older N


open WilsonIndependentMovingRosterNormalizedInputs (submitted pupil exact_source)

def cut (mask:Bits (n+1))(R:Realm G (e+1) E)(X:Fin ((n+1)+1)→CutsP H T p v E W K U)
    (a:Fin ((n+1)+1)→ℝ)(col:Fin ((n+1)+1)→Verse F)(φ:Fin ((n+1)+1)→Rarity D)(y:ℝ)(o:CellR)(t m older N:ℕ):Era G ℝ:=
  let c:=centers y (paceT R.draws.S m t)
  cruises R.draws R.paid N (ranks (choose (n+1) mask) k h) N older
    (placed (stable X a φ c (fun _=>o)) (pupil R X col φ c (fun _=>o) N) mask)

theorem original (R:Realm G (e+1) E)(X:Fin ((n+1)+1)→CutsP H T p v E W K U)
    {older t m N:ℕ}(before:older ≤ N)(cap:h ≤ k)(same:∀s,(X s).vesselsC=R)
    (last:∀s,(X s).N=N)(times:∀s,(X s).m+(X s).i=N)(starts:∀s,(X s).m=homes t m s)
    (a:Fin ((n+1)+1)→ℝ)(col:Fin ((n+1)+1)→Verse F)(φ:Fin ((n+1)+1)→Rarity D)(y:ℝ)(o:CellR):
    raw R X a col φ y o t m older N=prescribed (H:=H) (T:=T) (p:=p) (v:=v) (W:=W) (K:=K) (U:=U) R X col φ y o t m older N+
      ∑j∈Finset.univ.erase (quiet (n+1)),cut j R X a col φ y o t m older N:=by
  let law:ℕ→Era G ℝ→Era G ℝ:=fun l=>cruises R.draws R.paid N l N older
  let zoom:=paceT R.draws.S m t
  let c:Fin ((n+1)+1)→ℝ:=centers y zoom
  let sites:=fun _:Fin ((n+1)+1)=>o
  let P:=stable X a φ c sites
  let Fw:=pupil R X col φ c sites N
  let dst:=submitted R X a col φ c sites N
  let sz:=h+capP Qₙ
  have all:dst=fun i=>P i+Fw i:=funext (exact_source R X same last times a col φ c sites)
  have grade:=WilsonIndependentMovingRosterNormalizedInputs.grades R X same last times a col φ c sites
  have split:=WilsonIndependentMatchedRosterSigned.original (R:=R) before le_rfl cap P Fw
    (fun s=>(grade s).1) (fun s=>(grade s).2)
  rw [←all] at split
  have fits:sz≤(n+2)*k:=by
    have near':capP Qₙ≤(n+1)*k:=by
      simpa only [capP,asp,sectionSeal,Finset.sum_const,Finset.card_univ,Fintype.card_fin,Nat.nsmul_eq_mul] using
        (Finset.sum_le_sum (s:=(Finset.univ:Finset (Fin (n+1)))) (f:=fun _=>h) (g:=fun _=>k) (fun _ _=>cap))
    change h+capP Qₙ≤(n+1+1)*k
    rw [Nat.succ_mul]
    omega
  have base:Auth sz (MassP G ℝ (n+1) Fw):=
    (grade 0).2.manor (manCo (Fin.tail Fw) (fun _=>h) (fun i=>(grade i.succ).2))
  have small:=WilsonIndependentMatchedCoverGrade.carried R.draws R.paid R.hG R.green before le_rfl _ base fits
  have atFar:Fw 0=current R Q₀ (φ 0) (col 0) t N N (y/zoom) o:=by
    dsimp only [Fw,WilsonIndependentMovingRosterNormalizedInputs.pupil,c,WilsonIndependentMovingRosterStableSale.centers,Fin.cons_zero,current,sites]
    rw [starts 0]
    rfl
  have atNear:Fin.tail Fw=awaken Qₙ R.draws R.paid (near φ) (Fin.tail col) m N N y o:=by
    funext i
    dsimp only [Fw,Fin.tail,WilsonIndependentMovingRosterNormalizedInputs.pupil,c,WilsonIndependentMovingRosterStableSale.centers,Fin.cons_succ,awaken,sites]
    rw [starts i.succ]
    rfl
  have combined:=congrArg₂ agateV atFar (congrArg (MassP G ℝ n) atNear)
  change MassP G ℝ (n+1) Fw=agateV _ (Ashore Qₙ R.draws R.paid (near φ) (Fin.tail col) m N N y o) at combined
  unfold raw prescribed WilsonIndependentMovingRosterCut.residual
  dsimp only
  rw [←combined]
  change law ((n+2)*k) (MassP G ℝ (n+1) dst)-_= (law sz (MassP G ℝ (n+1) Fw)-_)+_
  change law sz (MassP G ℝ (n+1) Fw)=law ((n+2)*k) (MassP G ℝ (n+1) Fw) at small
  change law ((n+2)*k) (MassP G ℝ (n+1) dst)-law ((n+2)*k) (MassP G ℝ (n+1) Fw)=
    ∑j∈Finset.univ.erase (quiet (n+1)),cut j R X a col φ y o t m older N at split
  rw [small,←split]
  abel

end YM.Integration.WilsonIndependentMovingRosterNormalizedBook
